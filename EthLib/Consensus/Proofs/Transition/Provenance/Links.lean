module

public import EthLib.Consensus.Proofs.Transition.Provenance.Settled

/-!
# Proofs: the source block of a weighing call is an ancestor of its target block

A weighing call reads its target root from the block roots, for the first slot of the target's
epoch.

Its source is a checkpoint that an earlier call justified, with a root read the same way.

Along one chain, a root read for an earlier slot is an ancestor of a root read for a later one,
following the parent links of the blocks of the chain.

So the source block is an ancestor of the target block.

The source may instead be the checkpoint of genesis, whose root is zero by convention.

A state of the chain may also have the zero root, which the statement keeps as evidence.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- A genesis state is at slot 0, and its three checkpoints are the genesis checkpoint.

That checkpoint has epoch 0 and the zero root. -/
theorem genesis_state {forked : ForkedBeaconState preset} (genesis : Genesis config checks forked) :
    forked.state.slot = GENESIS_SLOT ∧
      forked.state.previousJustifiedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∧
      forked.state.currentJustifiedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∧
      forked.state.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ := by
  obtain ⟨⟨_, _, _, computed⟩, _⟩ := genesis
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, same⟩ :=
    computed
  have frame := (Frame.foldlM (fun _ _ _ ok => frame_genesisDeposit ok) depositedOk).trans
    (Frame.foldlM (fun _ _ _ ok => frame_activateAtGenesis ok) activatedOk)
  rw [← same]
  exact ⟨frame.slot, frame.previousJustified, frame.currentJustified, frame.finalized⟩

/-- The caching of a slot keeps the slot, the registry and the balances.

So a weighing call weighs the validators and balances of the state of the chain before it. -/
theorem processSlot_keeps {cached : BeaconState preset fork}
    (cachedOk : processSlot state = .ok cached) :
    cached.slot = state.slot ∧ cached.validators = state.validators ∧
      cached.balances = state.balances := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  exact ⟨rfl, rfl, rfl⟩

/-- From Altair, the voters a call counts for an epoch are active in that epoch. -/
theorem TargetVoters.active (altair : .altair ≤ fork) {epoch : Epoch}
    {voters : List ValidatorIndex} (counted : TargetVoters state epoch voters) :
    ∀ index ∈ voters, index ∈ getActiveValidatorIndices state epoch := by
  simp only [TargetVoters, altair, ↓reduceDIte] at counted
  exact fun index member => (mem_getUnslashedParticipatingIndices counted index member).1

/-- A root that a weighing call reads is the root its state held before the caching.

The call reads the first slot of the previous or the current epoch.

The buffer of roots must span two epochs, so the caching wrote another entry. -/
theorem processSlot_read
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {cached : BeaconState preset fork} (cachedOk : processSlot state = .ok cached)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch cached) {epoch : Epoch} {root : Root}
    (recent : epoch = getPreviousEpoch cached ∨ epoch = getCurrentEpoch cached)
    (rootOk : getBlockRoot cached epoch = .ok root) :
    ∃ slot : Slot, slot.toNat = epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ∧
      slot.toNat < state.slot.toNat ∧
      state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ∧
      readCircular state.blockRoots.elements slot = .ok root := by
  obtain ⟨slot, slotEq, below, near, read⟩ := getBlockRoot_ok rootOk
  have sameSlot : cached.slot = state.slot := processSlot_slot cachedOk
  obtain ⟨_, blockRoot, _, _, _, _, blockWrite, _⟩ := processSlot_roots cachedOk
  have epochs : (getCurrentEpoch cached).toNat ≤ epoch.toNat + 1 := by
    have := getPreviousEpoch_toNat cached
    rcases recent with same | same <;> rw [same] <;> omega
  have epochNat := getCurrentEpoch_toNat cached
  rw [sameSlot] at epochNat near below
  have spe : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    -- With no slot in an epoch, every epoch is the genesis epoch, which weighs nothing.
    rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
    · rw [zero, Nat.div_zero] at epochNat
      have weighs := UInt64.lt_iff_toNat_lt.mp later
      rw [epochNat] at weighs
      simp [GENESIS_EPOCH] at weighs
    · exact positive
  -- The state is in the epoch or the one after, so at most two epochs past the slot.
  have other : state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
      slot % preset.SLOTS_PER_HISTORICAL_ROOT := by
    refine mod_ne_of_lt below ?_
    have inEpoch : state.slot.toNat < preset.SLOTS_PER_EPOCH.toNat *
        (state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) := Nat.lt_mul_div_succ _ spe
    have bound : preset.SLOTS_PER_EPOCH.toNat *
          (state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) ≤
        preset.SLOTS_PER_EPOCH.toNat * (epoch.toNat + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have expand : preset.SLOTS_PER_EPOCH.toNat * (epoch.toNat + 2) =
        epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + 2 * preset.SLOTS_PER_EPOCH.toNat := by
      rw [Nat.mul_add, Nat.mul_comm]
      omega
    omega
  refine ⟨slot, slotEq, below, near, ?_⟩
  rw [← readCircular_writeCircular_of_ne blockWrite other]
  exact read

/-- The source block of a weighing call is an ancestor of its target block.

Take a chain from genesis, and a call of it at `state`, whose caching gives `cached`.

The buffer of roots must span two epochs.

The call's source for the checkpoint's epoch has the zero root of genesis.

Or its root is an ancestor of the checkpoint's root, along the parent links of the chain's
blocks.

The source's root is the root of the latest block at or before the first slot of its epoch.

So each block on the way is past that slot.

Or a state of the chain has the zero root. -/
theorem WeighingCall.source_pastAncestor {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed next : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start)
    (call : WeighingCall config checks start after fork state cached weighed next voters checkpoint) :
    (recordSource cached checkpoint.epoch).root = Vector.replicate 32 0 ∨
      PastAncestor config checks start after
        ((recordSource cached checkpoint.epoch).epoch.toNat * preset.SLOTS_PER_EPOCH.toNat)
        (recordSource cached checkpoint.epoch).root checkpoint.root ∨
      ZeroRootFound config checks start after := by
  have toAfter := call.toAfter
  obtain ⟨head, _, _, _, _, cachedOk, _, later, recent, _, _, rootOk⟩ := call
  obtain ⟨startSlot, startPrevious, startCurrent, startFinalized⟩ := genesis_state genesis
  have cachedSame : cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
      cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
      getCurrentEpoch cached = getCurrentEpoch state := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl, rfl⟩
  -- The source is one of the state's justified checkpoints, so the start's or a call's.
  have sourceIs : JustifiedOrStart config checks start ⟨fork, state⟩
      (recordSource cached checkpoint.epoch) := by
    obtain ⟨-, previous, current⟩ := head.checkpoints
    unfold recordSource
    rw [cachedSame.1, cachedSame.2.1]
    split
    · exact current
    · exact previous
  rcases sourceIs with same | same | same | ⟨fork', state', cached', _, next', voters', head',
    notDue', nextOk', tail', _, cachedOk', _, later', recent', _, _, rootOk'⟩
  · exact .inl (by rw [same, startFinalized])
  · exact .inl (by rw [same, startPrevious])
  · exact .inl (by rw [same, startCurrent])
  -- The source root and the target root are reads of the chain, for slots in order.
  right
  obtain ⟨slot', slotEq', below', near', read'⟩ :=
    processSlot_read wide cachedOk' later' recent' rootOk'
  obtain ⟨slot, slotEq, below, near, read⟩ := processSlot_read wide cachedOk later recent rootOk
  have sourceBefore := recordSource_epoch_lt (forked := ⟨fork, state⟩)
    (reachable := ⟨start, genesis, head⟩) cachedOk later recent
  -- The source's slot is before the target's, and from genesis on.
  have ordered : slot'.toNat ≤ slot.toNat := by
    rw [slotEq', slotEq]
    exact Nat.mul_le_mul_right _ (Nat.le_of_lt sourceBefore)
  have toState : Reaches config checks ⟨fork', state'⟩ ⟨fork, state⟩ :=
    ((Reaches.refl _).step (.slot notDue' nextOk')).trans tail'
  rcases head'.reads_pastAncestor toState (by rw [startSlot]; exact Nat.zero_le _) ordered
    read' below' near' read below near with ancestor | zero
  · rw [slotEq'] at ancestor
    exact .inl (ancestor.extendChain toAfter)
  · exact .inr (zero.extendChain toAfter)

/-- `WeighingCall.source_pastAncestor`, as ancestry along any blocks of the chain. -/
theorem WeighingCall.source_ancestor {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed next : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start)
    (call : WeighingCall config checks start after fork state cached weighed next voters checkpoint) :
    (recordSource cached checkpoint.epoch).root = Vector.replicate 32 0 ∨
      ChainAncestor config checks start after (recordSource cached checkpoint.epoch).root
        checkpoint.root ∨
      ZeroRootFound config checks start after :=
  (call.source_pastAncestor wide genesis).imp_right (Or.imp_left (·.chainAncestor))

/-- `WeighingCall.source_ancestor` for a call that `JustifiedBy` names. -/
theorem JustifiedBy.source_ancestor {start after : ForkedBeaconState preset}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start)
    (justified : JustifiedBy config checks start after checkpoint) :
    ∃ (fork : Fork) (state cached : BeaconState preset fork),
      Reaches config checks start ⟨fork, state⟩ ∧
      Reaches config checks ⟨fork, state⟩ after ∧ processSlot state = .ok cached ∧
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
      ((recordSource cached checkpoint.epoch).root = Vector.replicate 32 0 ∨
        ChainAncestor config checks start after (recordSource cached checkpoint.epoch).root
          checkpoint.root ∨
        ZeroRootFound config checks start after) := by
  obtain ⟨fork, state, cached, _, _, _, call⟩ := justified
  exact ⟨fork, state, cached, call.head, call.toAfter, call.cachedOk, call.recent,
    call.source_ancestor wide genesis⟩

/-- A checkpoint that a call justified is read again at the end of the chain, while still in
the buffer. -/
theorem JustifiedBy.read_at_end {start after : ForkedBeaconState preset} {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (justified : JustifiedBy config checks start after checkpoint)
    (recentEnd : after.state.slot.toNat ≤
      checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ∃ slot : Slot, slot.toNat = checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ∧
      slot.toNat < after.state.slot.toNat ∧
      readCircular after.state.blockRoots.elements slot = .ok checkpoint.root := by
  obtain ⟨fork, state, cached, _, next, _, _, notDue, nextOk, tail, _, cachedOk, _, later,
    recent, _, _, rootOk⟩ := justified
  obtain ⟨slot, slotEq, below, _, read⟩ := processSlot_read wide cachedOk later recent rootOk
  have toAfter : Reaches config checks ⟨fork, state⟩ after :=
    ((Reaches.refl _).step (.slot notDue nextOk)).trans tail
  have stateLe := toAfter.slot_le
  simp only at stateLe
  have stable := (toAfter.roots_stable (slot := slot) below (by rw [slotEq]; exact recentEnd)).1
  rw [read] at stable
  exact ⟨slot, slotEq, by omega, stable⟩

/-- Two checkpoints that calls of one chain justified: the earlier block is an ancestor.

The chain starts at genesis, and both checkpoints are still in the buffer at its end.

The buffer of roots must span two epochs.

The earlier checkpoint's root is an ancestor of the later one's, along the parent links of the
blocks of a chain from genesis to the end.

Each of those blocks is past the first slot of the earlier checkpoint's epoch.

Or a state of that chain has the zero root. -/
theorem JustifiedBy.pastAncestor {start after : ForkedBeaconState preset} {first second : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start)
    (firstJustified : JustifiedBy config checks start after first)
    (secondJustified : JustifiedBy config checks start after second)
    (ordered : first.epoch.toNat ≤ second.epoch.toNat)
    (recentEnd : after.state.slot.toNat ≤
      first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    PastAncestor config checks start after (first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat)
        first.root second.root ∨
      ZeroRootFound config checks start after := by
  obtain ⟨slot, slotEq, below, read⟩ := firstJustified.read_at_end wide recentEnd
  have slotOrder : first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      second.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := Nat.mul_le_mul_right _ ordered
  obtain ⟨slot', slotEq', below', read'⟩ := secondJustified.read_at_end wide (by omega)
  have chain : Reaches config checks start after := by
    obtain ⟨_, _, _, _, _, _, head, notDue, nextOk, tail, _⟩ := firstJustified
    exact head.trans (((Reaches.refl _).step (.slot notDue nextOk)).trans tail)
  have startSlot := (genesis_state genesis).1
  rcases Nat.lt_or_ge slot.toNat slot'.toNat with before | same
  · rcases chain.blockRoots_pastAncestor (by rw [startSlot]; exact Nat.zero_le _) before below'
      (by omega) read read' with ⟨_, _, _, ⟨_, _, _, _, _, head, _⟩, ancestor | zero⟩
    · rw [slotEq] at ancestor
      exact .inl (ancestor.prefix head)
    · exact .inr (zero.prefix head)
  · have sameSlot : slot = slot' := UInt64.toNat_inj.mp (by omega)
    subst sameSlot
    rw [read] at read'
    rw [Except.ok.inj read']
    exact .inl .refl

/-- `JustifiedBy.pastAncestor`, as ancestry along any blocks of the chain. -/
theorem JustifiedBy.ancestor {start after : ForkedBeaconState preset} {first second : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start)
    (firstJustified : JustifiedBy config checks start after first)
    (secondJustified : JustifiedBy config checks start after second)
    (ordered : first.epoch.toNat ≤ second.epoch.toNat)
    (recentEnd : after.state.slot.toNat ≤
      first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ChainAncestor config checks start after first.root second.root ∨
      ZeroRootFound config checks start after :=
  (firstJustified.pastAncestor wide genesis secondJustified ordered recentEnd).imp_left
    (·.chainAncestor)

/-- A slot step of a chain cached a header whose root is zero.

That header is the latest block's, with its state root filled, so its root is that block's root.

A zero root is a preimage of zero under the hash, which no one is known to find.

This records the cryptographic event instead of assuming it cannot happen. -/
def ZeroHeaderFound (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) : Prop :=
  ∃ (slot : Slot) (fork : Fork) (state cached : BeaconState preset fork),
    CachesSlot config checks start after slot state cached ∧
    SszType.hashTreeRoot cached.latestBlockHeader = .ok (Vector.replicate 32 0)

/-- The target root of a weighing call is not zero, or a header of the chain has the zero root.

The call reads the root of the first slot of the checkpoint's epoch.

That slot is from the start of the chain on, for example from genesis, whose slot is zero.

A slot step of the chain cached that slot, and the root is the root of the header it cached.

The buffer of roots must span two epochs. -/
theorem JustifiedBy.target_nonzero {start after : ForkedBeaconState preset}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (justified : JustifiedBy config checks start after checkpoint)
    (fromStart : start.state.slot.toNat ≤
      checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    checkpoint.root ≠ Vector.replicate 32 0 ∨ ZeroHeaderFound config checks start after := by
  obtain ⟨fork, state, cached, _, next, _, head, notDue, nextOk, tail, _, cachedOk, _, later,
    recent, _, _, rootOk⟩ := justified
  obtain ⟨slot, slotEq, below, near, read⟩ := processSlot_read wide cachedOk later recent rootOk
  -- A slot step before the call cached that slot, and wrote the root of its header.
  obtain ⟨fork', state', cached', ⟨atSlot, cachedOk', next', nextOk', notDue', head', tail'⟩,
    ⟨root, rootOk', written⟩, -⟩ :=
    head.roots_written (by rw [slotEq]; exact fromStart) below near
  rw [read] at written
  cases written
  by_cases zero : checkpoint.root = Vector.replicate 32 0
  · have toAfter : Reaches config checks ⟨fork', next'⟩ after :=
      tail'.trans (((Reaches.refl _).step (.slot notDue nextOk)).trans tail)
    exact .inr ⟨slot, fork', state', cached', ⟨atSlot, cachedOk', next', nextOk', notDue', head',
      toAfter⟩, zero ▸ rootOk'⟩
  · exact .inl zero

/-- `JustifiedBy.target_nonzero` for one named call. -/
theorem WeighingCall.target_nonzero {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed next : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (call : WeighingCall config checks start after fork state cached weighed next voters checkpoint)
    (fromStart : start.state.slot.toNat ≤
      checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    checkpoint.root ≠ Vector.replicate 32 0 ∨ ZeroHeaderFound config checks start after :=
  call.justifiedBy.target_nonzero wide fromStart

end EthLib.Consensus
