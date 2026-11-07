module

public import EthLib.Consensus.Proofs.ForkChoice.Runs
public import EthLib.Consensus.Proofs.Transition.FfgHistories

/-!
# Proofs: accountable safety for the checkpoints of a fork-choice store

A store keeps a justified and a finalized checkpoint.

When the store starts at genesis and every handler uses one choice of signature checks, each comes
from a state that a chain from genesis reached: one of its checkpoints, or one that a call of
`processJustificationAndFinalization` on it wrote, the pulled-up tip.

So each lies in the two-history refinement of the chains to those two states.

`store_accountable_safety` then applies the finalized-versus-justified theorem.

Suppose the two checkpoints conflict as epoch-boundary pairs.

Then validators with a third of the reference stake, less twice the drift bound, signed two
attestation data that the beacon chain slashes, both checked in blocks of the two chains.

Otherwise a state or a block header of those chains has the zero root.

The conflict itself is a hypothesis here.

The store's descent check gives it, or hash evidence, through the fork-choice proofs.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Base.Fork}

/-- At genesis the current epoch is the genesis epoch. -/
theorem genesis_currentEpoch {anchorState : BeaconState preset fork}
    (genesis : Genesis config checks ⟨fork, anchorState⟩) :
    getCurrentEpoch anchorState = GENESIS_EPOCH := by
  have slot := (genesis_state genesis).1
  simp only at slot
  simp [getCurrentEpoch, computeEpochAtSlot, slot, GENESIS_SLOT, GENESIS_EPOCH]

/-- A store checkpoint of a current justified field, not at the genesis epoch, is justified on the
chain to some state that genesis reaches. -/
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

/-- A store checkpoint of a finalized field, not at the genesis epoch, is finalized on the chain to
some state that genesis reaches: the state's own, or by a call on it. -/
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

open scoped Classical in
/-- Accountable safety for the checkpoints of a fork-choice store that starts at genesis.

The store's finalized checkpoint `F` is not at the genesis epoch, and its epoch is at most that of
its justified checkpoint `J`.

Then there are two states `a` and `b` that chains from genesis reached, with `J` justified on the
chain to `a` and `F` finalized on the chain to `b`, such that the following holds.

If `F` and `J` conflict as epoch-boundary pairs over the parent links of the two chains, then
validators active in a reference weighing with a third of its stake, less twice the drift bound,
signed two attestation data that the beacon chain slashes, both checked in blocks of the chains.

Otherwise a state or a block header of the chains has the zero root. -/
theorem store_accountable_safety {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (genesis : Genesis config checks ⟨fork, anchorState⟩)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (within : ∀ (fork' : Base.Fork) (state : BeaconState preset fork'),
      Reaches config checks ⟨fork, anchorState⟩ ⟨fork', state⟩ → state.RegistryWithinLimit)
    (reachable : Store.ReachableWith config checks anchorState anchorBlock store)
    (notDue : ∀ state : BeaconState preset fork, upgradeDue config ⟨fork, state⟩ = false)
    (notGenesis : store.finalizedCheckpoint.epoch ≠ GENESIS_EPOCH)
    (hle : store.finalizedCheckpoint.epoch.toNat ≤ store.justifiedCheckpoint.epoch.toNat) :
    ∃ a b : ForkedBeaconState preset,
      OnEither config checks ⟨fork, anchorState⟩ a b a ∧
      OnEither config checks ⟨fork, anchorState⟩ a b b ∧
      ∀ (ω₀ : Weighing ValidatorIndex) {D : ℕ},
        (∀ r ∈ (historyRefinement (a := a) (b := b) genesis wide4 lookahead within).records,
          store.finalizedCheckpoint.epoch.toNat ≤ r.target.epoch.toNat →
          r.target.epoch.toNat ≤ store.justifiedCheckpoint.epoch.toNat →
          Weighing.drift ω₀ r.weighing ≤ D) →
        Conflicting
          (EpochBlock.ofCheckpoint (links := historyLinks config checks ⟨fork, anchorState⟩ a b)
            (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat) store.finalizedCheckpoint)
          (EpochBlock.ofCheckpoint store.justifiedCheckpoint) →
        stake ω₀.stake ω₀.active ≤
          3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2,
            (i, data1) ∈
              (historyRefinement (a := a) (b := b) genesis wide4 lookahead within).signed ∧
            (i, data2) ∈
              (historyRefinement (a := a) (b := b) genesis wide4 lookahead within).signed ∧
            isSlashableAttestationData data1 data2 = true} + 2 * D ∨
          historyEvidence config checks ⟨fork, anchorState⟩ a b := by
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
  refine ⟨⟨fork, sJ⟩, ⟨fork, sF⟩, ⟨headJ, .inl (.refl _)⟩, ⟨headF, .inr (.refl _)⟩,
    fun ω₀ D hD conflicting => ?_⟩
  exact (historyRefinement genesis wide4 lookahead within).accountable_safety_justified
    ⟨⟨fork, sF⟩, ⟨headF, .inr (.refl _)⟩, finalized⟩
    ⟨⟨fork, sJ⟩, ⟨headJ, .inl (.refl _)⟩, justified⟩ hle conflicting ω₀ hD

end EthLib.Consensus
