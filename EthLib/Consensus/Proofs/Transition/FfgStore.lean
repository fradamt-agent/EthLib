module

public import EthLib.Consensus.Proofs.ForkChoice.Runs
public import EthLib.Consensus.Proofs.ForkChoice.StoreConflict
public import EthLib.Consensus.Proofs.Transition.FfgHistories
public import EthLib.Consensus.Proofs.Transition.GenesisHeader

/-!
# Proofs: accountable safety for the checkpoints of a fork-choice store

A store keeps a justified and a finalized checkpoint.

Suppose the store starts at genesis and every handler uses one choice of signature checks.

Then each of the two checkpoints comes from a state that a chain from genesis reached.

It is one of that state's checkpoints, or one that a call on it wrote, the pulled-up tip.

That call is a call of `processJustificationAndFinalization`.

So each lies in the two-history refinement of the chains to those two states.

`store_accountable_safety` then applies the finalized-versus-justified theorem.

Suppose the two checkpoints conflict as epoch-boundary pairs.

Then there are validators with a third of the reference stake, less twice the drift bound.

Each of them signed two attestation data that the beacon chain slashes.

Both data were checked in blocks of the two chains.

Otherwise a state or a block header of those chains has the zero root.

The pair conflict comes from the store's failed descent check, through the fork-choice proofs.

Its alternatives are hash evidence too:

- two block headers with one root;
- a block whose root is zero, which is a SHA-256 output of zero.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg Serialization.Ssz SszType

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Base.Fork}

/-- At genesis the current epoch is the genesis epoch. -/
theorem genesis_currentEpoch {anchorState : BeaconState preset fork}
    (genesis : Genesis config checks ⟨fork, anchorState⟩) :
    getCurrentEpoch anchorState = GENESIS_EPOCH := by
  have slot := (genesis_state genesis).1
  simp only at slot
  simp [getCurrentEpoch, computeEpochAtSlot, slot, GENESIS_SLOT, GENESIS_EPOCH]

/-- Take a store checkpoint of a current justified field, not at the genesis epoch.

It is justified on the chain to some state that genesis reaches. -/
theorem justified_of_checkpointFromRuns {anchorState : BeaconState preset fork}
    {anchor : Checkpoint}
    (genesis : Genesis config checks ⟨fork, anchorState⟩)
    (anchorEpoch : anchor.epoch = getCurrentEpoch anchorState) {c : Checkpoint}
    (notGenesis : c.epoch ≠ GENESIS_EPOCH)
    (origin : Store.CheckpointFromRuns config checks anchorState anchor
      (·.currentJustifiedCheckpoint) c) :
    ∃ s : BeaconState preset fork, Reaches config checks ⟨fork, anchorState⟩ ⟨fork, s⟩ ∧
      (JustifiedOrStart config checks ⟨fork, anchorState⟩ ⟨fork, s⟩ c ∨
        JustifiedByCall config checks ⟨fork, anchorState⟩ ⟨fork, s⟩ c) := by
  rcases origin with rfl | ⟨s, head, rfl⟩ | ⟨s, t, head, weighedOk, rfl⟩
  · exact absurd (anchorEpoch.trans (genesis_currentEpoch genesis)) notGenesis
  · exact ⟨s, head, .inl head.checkpoints.2.2⟩
  · dsimp only
    rcases processJustificationAndFinalization_current head weighedOk with same | ⟨voters, call⟩
    · rw [same]
      exact ⟨s, head, .inl head.checkpoints.2.2⟩
    · exact ⟨s, head, .inr ⟨fork, s, s, t, voters, call⟩⟩

/-- Take a store checkpoint of a finalized field, not at the genesis epoch.

It is finalized on the chain to some state that genesis reaches.

It is the state's own finalized checkpoint, or a call on the state finalized it. -/
theorem finalized_of_checkpointFromRuns {anchorState : BeaconState preset fork}
    {anchor : Checkpoint}
    (genesis : Genesis config checks ⟨fork, anchorState⟩)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorEpoch : anchor.epoch = getCurrentEpoch anchorState) {c : Checkpoint}
    (notGenesis : c.epoch ≠ GENESIS_EPOCH)
    (origin : Store.CheckpointFromRuns config checks anchorState anchor
      (·.finalizedCheckpoint) c) :
    ∃ s : BeaconState preset fork, Reaches config checks ⟨fork, anchorState⟩ ⟨fork, s⟩ ∧
      (c = s.finalizedCheckpoint ∨
        KFinalizedByCall config checks ⟨fork, anchorState⟩ ⟨fork, s⟩ c) := by
  rcases origin with rfl | ⟨s, head, rfl⟩ | ⟨s, t, head, weighedOk, rfl⟩
  · exact absurd (anchorEpoch.trans (genesis_currentEpoch genesis)) notGenesis
  · exact ⟨s, head, .inl rfl⟩
  · dsimp only at notGenesis ⊢
    rcases processJustificationAndFinalization_finalized_rule wide4 genesis head weighedOk with
      same | atGenesis | byCall
    · exact ⟨s, head, .inl same⟩
    · exact absurd (by rw [atGenesis]) notGenesis
    · exact ⟨s, head, .inr byCall⟩

/-- The epoch of a checkpoint that a call weighs, times the slots of an epoch, fits in 64 bits.

It is at most the slot of the call's state. -/
theorem CallRecord.epoch_fits {start after : ForkedBeaconState preset}
    {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
    {c : Checkpoint}
    (call : CallRecord config checks start after fork state cached weighed voters c) :
    c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
  have current : c.epoch.toNat ≤ (getCurrentEpoch cached).toNat := by
    rcases call.recent with h | h
    · rw [h]
      exact UInt64.le_iff_toNat_le.mp (getPreviousEpoch_le cached)
    · rw [h]
  have slotBound := cached.slot.toNat_lt
  have epochSlot : (getCurrentEpoch cached).toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      cached.slot.toNat := by
    simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_mul_le_self _ _
  calc c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat
      ≤ (getCurrentEpoch cached).toNat * preset.SLOTS_PER_EPOCH.toNat :=
        Nat.mul_le_mul_right _ current
    _ < 2 ^ 64 := lt_of_le_of_lt epochSlot slotBound

/-- What the store bridge needs of a checkpoint justified on a chain from genesis.

The checkpoint is off the genesis epoch, and the bridge needs:

- a nonzero root;
- a header at or before the first slot of its epoch;
- an epoch that fits.

Each holds, or a state or a cached header of the chain has the zero root. -/
theorem justified_root_facts {g x : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {c : Checkpoint}
    (notGenesis : c.epoch ≠ GENESIS_EPOCH)
    (justified : JustifiedOrStart config checks g x c ∨ JustifiedByCall config checks g x c) :
    (c.root ≠ Vector.replicate 32 0 ∨ ZeroHeaderFound config checks g x) ∧
      ((∃ header : BeaconBlockHeader, hashTreeRoot header = .ok c.root ∧
        header.slot.toNat ≤ c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) ∨
        ZeroRootFound config checks g x) ∧
      c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64 := by
  obtain ⟨startSlot, previous, current, finalized⟩ := genesis_state genesis
  have fromStart : g.state.slot.toNat ≤ c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [startSlot]
    exact Nat.zero_le _
  have record : ∃ (fork : Base.Fork) (state cached weighed : BeaconState preset fork)
      (voters : List ValidatorIndex),
      CallRecord config checks g x fork state cached weighed voters c := by
    rcases justified with (rfl | rfl | rfl | ⟨fork, state, cached, weighed, next, voters, call⟩) |
      ⟨fork, state, cached, weighed, voters, call⟩
    · exact absurd (by rw [finalized]) notGenesis
    · exact absurd (by rw [previous]) notGenesis
    · exact absurd (by rw [current]) notGenesis
    · exact ⟨fork, state, cached, weighed, voters, call.record⟩
    · exact ⟨fork, state, cached, weighed, voters, call⟩
  obtain ⟨fork, state, cached, weighed, voters, call⟩ := record
  refine ⟨call.target_nonzero wide fromStart, ?_, call.epoch_fits⟩
  rcases call.root_block wide fromStart with ⟨p, slot, block, below⟩ | ⟨stateRoot, rootOk⟩ |
    found
  · obtain ⟨header, rootOk, -, slotEq⟩ := block.header
    exact .inl ⟨header, rootOk, by rw [slotEq]; exact below⟩
  · refine .inl ⟨_, rootOk, ?_⟩
    simp only [genesis_latestBlockHeader_slot genesis, GENESIS_SLOT]
    exact Nat.zero_le _
  · exact .inr found

/-- Hash evidence that the store bridge can find, one of:

- two block headers with one root;
- a stored block at the zero root;
- a block of the chains whose root is zero. -/
def StoreEvidence (store : Store preset fork) (links : Root → Root → ℕ → Prop) : Prop :=
  HeaderCollision ∨ (∃ block, store.blocks[(Vector.replicate 32 0 : Root)]? = some block) ∨
    ∃ parentRoot slot, links parentRoot (Vector.replicate 32 0) slot

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

open scoped Classical in
/-- Accountable safety for the checkpoints of a fork-choice store that starts at genesis.

The store's finalized checkpoint `F` is not at the genesis epoch.

The epoch of `F` is at most that of the store's justified checkpoint `J`.

Its head computes, and its justified block does not descend from `F` at the epoch of `F`.

Then chains from genesis reached two states `a` and `b`, such that the following holds.

`J` is justified on the chain to `a`, and `F` is finalized on the chain to `b`.

Take a reference weighing `ω₀`, and a bound `D` on the drift of the calls between the two epochs.

Then there are validators active in `ω₀` with a third of its stake, less `2 * D`.

Each of them signed two attestation data that the beacon chain slashes.

Both data were checked in blocks of the chains.

Otherwise there is hash evidence, one of:

- a state or a block header of the chains with the zero root;
- two block headers with one root;
- a block whose root is zero. -/
theorem store_accountable_safety {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (genesis : Genesis config checks ⟨fork, anchorState⟩)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (within : ∀ (fork' : Base.Fork) (state : BeaconState preset fork'),
      Reaches config checks ⟨fork, anchorState⟩ ⟨fork', state⟩ → state.RegistryWithinLimit)
    (reachable : Store.ReachableWith config checks anchorState anchorBlock store)
    (notDue : ∀ state : BeaconState preset fork, upgradeDue config ⟨fork, state⟩ = false)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (anchorParent : anchorBlock.parentRoot = Vector.replicate 32 0)
    {head : ForkChoiceNode} (headOk : store.getHead config = .ok head)
    (notGenesis : store.finalizedCheckpoint.epoch ≠ GENESIS_EPOCH)
    (hle : store.finalizedCheckpoint.epoch.toNat ≤ store.justifiedCheckpoint.epoch.toNat)
    (notDescends : store.getCheckpointBlock store.justifiedCheckpoint.root
      store.finalizedCheckpoint.epoch ≠ .ok store.finalizedCheckpoint.root) :
    ∃ a b : ForkedBeaconState preset,
      OnEither config checks ⟨fork, anchorState⟩ a b a ∧
      OnEither config checks ⟨fork, anchorState⟩ a b b ∧
      ∀ (ω₀ : Weighing ValidatorIndex) {D : ℕ},
        (∀ r ∈ (historyRefinement (a := a) (b := b) genesis wide4 lookahead within).records,
          store.finalizedCheckpoint.epoch.toNat ≤ r.target.epoch.toNat →
          r.target.epoch.toNat ≤ store.justifiedCheckpoint.epoch.toNat →
          Weighing.drift ω₀ r.weighing ≤ D) →
        stake ω₀.stake ω₀.active ≤
          3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2,
            (i, data1) ∈
              (historyRefinement (a := a) (b := b) genesis wide4 lookahead within).signed ∧
            (i, data2) ∈
              (historyRefinement (a := a) (b := b) genesis wide4 lookahead within).signed ∧
            isSlashableAttestationData data1 data2 = true} + 2 * D ∨
          historyEvidence config checks ⟨fork, anchorState⟩ a b ∨
          StoreEvidence store (historyLinks config checks ⟨fork, anchorState⟩ a b) := by
  have wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    omega
  obtain ⟨anchorRoot, -, -, justifiedOrigin, finalizedOrigin, -, -⟩ :=
    reachable.checkpointsFromRuns notDue
  have justifiedNotGenesis : store.justifiedCheckpoint.epoch ≠ GENESIS_EPOCH := by
    intro atGenesis
    apply notGenesis
    rw [atGenesis] at hle
    exact UInt64.toNat_inj.mp (Nat.le_zero.mp (by simpa [GENESIS_EPOCH] using hle))
  obtain ⟨sJ, headJ, justified⟩ :=
    justified_of_checkpointFromRuns genesis rfl justifiedNotGenesis justifiedOrigin
  obtain ⟨sF, headF, finalized⟩ :=
    finalized_of_checkpointFromRuns genesis wide4 rfl notGenesis finalizedOrigin
  let a : ForkedBeaconState preset := ⟨fork, sJ⟩
  let b : ForkedBeaconState preset := ⟨fork, sF⟩
  have onA : OnEither config checks ⟨fork, anchorState⟩ a b a := ⟨headJ, .inl (.refl _)⟩
  have onB : OnEither config checks ⟨fork, anchorState⟩ a b b := ⟨headF, .inr (.refl _)⟩
  -- The finalized checkpoint is justified on the chain to `b` too.
  have finalizedJustified :
      JustifiedOrStart config checks ⟨fork, anchorState⟩ b store.finalizedCheckpoint ∨
        JustifiedByCall config checks ⟨fork, anchorState⟩ b store.finalizedCheckpoint := by
    rcases finalized with same | ⟨k, hk, -, cs, h0, -, justifiedAt, -⟩
    · rw [same]
      exact .inl headF.checkpoints.1
    · rw [← h0]
      exact justifiedAt 0 hk
  obtain ⟨fNonzero, fHeader, fFits⟩ :=
    justified_root_facts genesis wide notGenesis finalizedJustified
  obtain ⟨jNonzero, -, -⟩ :=
    justified_root_facts genesis wide justifiedNotGenesis justified
  refine ⟨a, b, onA, onB, fun ω₀ D hD => ?_⟩
  -- Hash evidence on either chain ends the proof.
  rcases fNonzero with fNonzero | zero
  swap
  · exact .inr (.inl ⟨b, onB, .inr zero⟩)
  rcases jNonzero with jNonzero | zero
  swap
  · exact .inr (.inl ⟨a, onA, .inr zero⟩)
  rcases fHeader with fHeader | found
  swap
  · exact .inr (.inl ⟨b, onB, .inl found⟩)
  rcases reachable.reachable.conflicting_of_not_descends
      (links := historyLinks config checks ⟨fork, anchorState⟩ a b) anchorSlot anchorParent
      headOk (fun ⟨_, _, s, block, slotEq⟩ => by
        obtain ⟨header, rootOk, parent, headerSlot⟩ := block.header
        exact ⟨header, rootOk, parent, by rw [headerSlot, slotEq]⟩)
      fFits hle fNonzero jNonzero fHeader notDescends with
    conflicting | zeroLink | collision | zeroBlock
  · exact (historyRefinement genesis wide4 lookahead within).accountable_safety_justified
      ⟨b, onB, finalized⟩ ⟨a, onA, justified⟩ hle conflicting ω₀ hD |>.imp_right .inl
  · exact .inr (.inr (.inr (.inr zeroLink)))
  · exact .inr (.inr (.inl collision))
  · exact .inr (.inr (.inr (.inl zeroBlock)))

end EthLib.Consensus
