module

public import EthLib.Consensus.Proofs.Transition.Provenance.Sources

/-!
# Proofs: the source of a weighing call is justified, and earlier than its target

Casper FFG links a source checkpoint to a later target checkpoint.

A weighing call of the beacon chain links the justified checkpoint of the target's epoch to it.

This file shows that the source is justified, and that its epoch is below the target's.

The second fact needs a property of every state reached from genesis.

The previous justified checkpoint is at least two epochs back, from epoch 2 on.

In epochs 0 and 1 it is the genesis checkpoint, as is the current justified one.

The call at the end of an epoch makes the old current justified checkpoint the previous one.

The current one is at most the previous epoch.

The first two epochs weigh nothing, so their checkpoints stay those of genesis.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The previous justified checkpoint is two epochs back from epoch 2 on.

Before epoch 2 both justified checkpoints are one checkpoint of epoch 0. -/
def PreviousSettled (state : BeaconState preset fork) : Prop :=
  ((getCurrentEpoch state).toNat ≤ 1 →
      state.previousJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
        state.previousJustifiedCheckpoint.epoch.toNat = 0) ∧
    (2 ≤ (getCurrentEpoch state).toNat →
      state.previousJustifiedCheckpoint.epoch.toNat + 2 ≤ (getCurrentEpoch state).toNat)

/-- A genesis state is at epoch 0, with both justified checkpoints at epoch 0. -/
theorem genesis_previousSettled {forked : ForkedBeaconState preset}
    (genesis : Genesis config checks forked) : PreviousSettled forked.state := by
  obtain ⟨⟨_, _, _, computed⟩, _⟩ := genesis
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  rename_i altair
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, same⟩ :=
    computed
  have frame := (Frame.foldlM (fun _ _ _ ok => frame_genesisDeposit ok) depositedOk).trans
    (Frame.foldlM (fun _ _ _ ok => frame_activateAtGenesis ok) activatedOk)
  have slot : forked.state.slot = GENESIS_SLOT := by rw [← same]; exact frame.slot
  have previous :
      forked.state.previousJustifiedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ := by
    rw [← same]; exact frame.previousJustified
  have current :
      forked.state.currentJustifiedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ := by
    rw [← same]; exact frame.currentJustified
  have epoch : (getCurrentEpoch forked.state).toNat = 0 := by
    rw [getCurrentEpoch_toNat, slot]
    simp [GENESIS_SLOT]
  refine ⟨fun _ => ⟨previous.trans current.symm, by rw [previous]; rfl⟩, fun two => ?_⟩
  omega

/-- Each step from a state with the invariant keeps the previous justified checkpoint settled. -/
theorem previousSettled_step {before after : ForkedBeaconState preset}
    (holds : Invariant before.state) (settled : PreviousSettled before.state)
    (step : Step config checks before after) : PreviousSettled after.state := by
  cases step with
  | @slot fork state next notDue computed =>
    obtain ⟨cached, cachedOk, stepSlot, -, -, -, closing⟩ := advanceSlot_history computed
    have cachedSame : cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
        cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
        getCurrentEpoch cached = getCurrentEpoch state := by
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
      exact ⟨rfl, rfl, rfl⟩
    split at closing
    · next closes =>
      obtain ⟨weighed, weighedOk, -, previousSame, currentSame, -⟩ := closing
      have nextEpoch := epoch_of_closes stepSlot closes
      simp only at settled ⊢
      unfold PreviousSettled at settled ⊢
      rw [previousSame, currentSame, nextEpoch]
      rcases processJustificationAndFinalization_weighs weighedOk with ⟨early, rfl⟩ |
        ⟨later, _, _, _, _, _, _, _, _, _, _, weighs⟩
      · -- The first two epochs weigh nothing: the checkpoints of genesis stay.
        rw [cachedSame.1, cachedSame.2.1]
        have earlyNat := UInt64.le_iff_toNat_le.mp early
        rw [cachedSame.2.2] at earlyNat
        change _ ≤ 0 + 1 at earlyNat
        obtain ⟨same, zero⟩ := settled.1 (by omega)
        exact ⟨fun _ => ⟨same, zero⟩, fun _ => by omega⟩
      · -- The call makes the current justified checkpoint the previous one.
        have moved := (weighJustificationAndFinalization_checkpoints weighs).1
        rw [moved, cachedSame.2.1]
        have laterNat := UInt64.lt_iff_toNat_lt.mp later
        rw [cachedSame.2.2] at laterNat
        change 0 + 1 < _ at laterNat
        have justifiedLe := UInt64.le_iff_toNat_le.mp holds.settled
        have previousEpoch := getPreviousEpoch_toNat state
        simp only at justifiedLe
        exact ⟨fun _ => by omega, fun _ => by omega⟩
    · next notClosing =>
      obtain ⟨-, previousSame, currentSame, -⟩ := closing
      have sameEpoch := epoch_of_open stepSlot notClosing
      unfold PreviousSettled at settled ⊢
      simp only at settled ⊢
      rw [previousSame, currentSame, sameEpoch]
      exact settled
  | @upgrade _ post due computed =>
    have same := upgradeNext_history computed
    simp only [BeaconState.history, Prod.mk.injEq] at same
    have epoch : getCurrentEpoch post.val.state = getCurrentEpoch before.state := by
      simp only [getCurrentEpoch, same.1]
    unfold PreviousSettled at settled ⊢
    rw [epoch, same.2.2.2.2.2.1, same.2.2.2.2.2.2.1]
    exact settled
  | @block fork engine signed validateResult state post notDue computed =>
    have frame := frame_processBlock (applySignedBlock_ok computed).2.1
    have epoch : getCurrentEpoch post = getCurrentEpoch state := by
      simp only [getCurrentEpoch, frame.slot]
    unfold PreviousSettled at settled ⊢
    simp only at settled ⊢
    rw [epoch, frame.previousJustified, frame.currentJustified]
    exact settled

/-- Every state reached from genesis has its previous justified checkpoint settled. -/
theorem Reachable.previousSettled {forked : ForkedBeaconState preset}
    (reachable : Reachable config checks forked) : PreviousSettled forked.state :=
  Reachable.induction (fun _ genesis => genesis_previousSettled genesis)
    (fun reachableBefore settled step =>
      previousSettled_step reachableBefore.invariant settled step) reachable

/-- Up to epoch 2, a chain keeps its justified checkpoints: the first two epochs weigh nothing. -/
theorem Reaches.justified_of_early {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after)
    (early : (getCurrentEpoch after.state).toNat ≤ 2) :
    after.state.previousJustifiedCheckpoint = start.state.previousJustifiedCheckpoint ∧
      after.state.currentJustifiedCheckpoint = start.state.currentJustifiedCheckpoint := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | @snoc middle last run step more =>
    have stepLe := ((Reaches.refl (config := config) (checks := checks) middle).step step).epoch_le
    obtain ⟨previous, current⟩ := more (by omega)
    rw [← previous, ← current]
    cases step with
    | @slot fork state next notDue computed =>
      obtain ⟨cached, cachedOk, stepSlot, -, -, -, closing⟩ := advanceSlot_history computed
      split at closing
      · next closes =>
        obtain ⟨weighed, weighedOk, -, previousSame, currentSame, -⟩ := closing
        have nextEpoch := epoch_of_closes stepSlot closes
        simp only at early nextEpoch ⊢
        rw [previousSame, currentSame]
        have cachedSame : cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
            cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
            getCurrentEpoch cached = getCurrentEpoch state := by
          obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
          exact ⟨rfl, rfl, rfl⟩
        rcases processJustificationAndFinalization_weighs weighedOk with ⟨_, rfl⟩ |
          ⟨later, _, _, _, _, _, _, _, _, _, _, _⟩
        · exact ⟨cachedSame.1, cachedSame.2.1⟩
        · have laterNat := UInt64.lt_iff_toNat_lt.mp later
          rw [cachedSame.2.2] at laterNat
          change 0 + 1 < _ at laterNat
          omega
      · exact ⟨closing.2.1, closing.2.2.1⟩
    | upgrade due computed =>
      have same := upgradeNext_history computed
      simp only [BeaconState.history, Prod.mk.injEq] at same
      exact ⟨same.2.2.2.2.2.1, same.2.2.2.2.2.2.1⟩
    | block engine signed validateResult notDue computed =>
      have frame := frame_processBlock (applySignedBlock_ok computed).2.1
      exact ⟨frame.previousJustified, frame.currentJustified⟩

theorem JustifiedOrStart.extendChain {start middle after : ForkedBeaconState preset}
    {checkpoint : Checkpoint} (justified : JustifiedOrStart config checks start middle checkpoint)
    (chain : Reaches config checks middle after) :
    JustifiedOrStart config checks start after checkpoint := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact justified
  | snoc _ step more => exact more.extend step

/-- The source that a weighing call gives an epoch is earlier than that epoch.

The call reads a state reached from genesis, after its caching. -/
theorem recordSource_epoch_lt {forked : ForkedBeaconState preset}
    (reachable : Reachable config checks forked) {cached : BeaconState preset forked.fork}
    (readsFrom : ReadsFrom forked.state cached)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch cached) {epoch : Epoch}
    (recent : epoch = getPreviousEpoch cached ∨ epoch = getCurrentEpoch cached) :
    (recordSource cached epoch).epoch.toNat < epoch.toNat := by
  have holds : Invariant forked.state := reachable.invariant
  have settled : PreviousSettled forked.state := reachable.previousSettled
  have cachedSame : cached.previousJustifiedCheckpoint =
        forked.state.previousJustifiedCheckpoint ∧
      cached.currentJustifiedCheckpoint = forked.state.currentJustifiedCheckpoint ∧
      getCurrentEpoch cached = getCurrentEpoch forked.state := by
    obtain ⟨_, _, _, _, rfl⟩ := readsFrom.eq
    exact ⟨rfl, rfl, rfl⟩
  have cachedPrevious : getPreviousEpoch cached = getPreviousEpoch forked.state := by
    unfold getPreviousEpoch
    rw [cachedSame.2.2]
  unfold recordSource
  rw [cachedSame.1, cachedSame.2.1, cachedSame.2.2]
  rw [cachedSame.2.2, cachedPrevious] at recent
  rw [cachedSame.2.2] at later
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  change 0 + 1 < _ at laterNat
  have previousNat := getPreviousEpoch_toNat forked.state
  split
  · next isCurrent =>
    -- The current justified epoch is at most the previous epoch.
    have justifiedLe := UInt64.le_iff_toNat_le.mp holds.settled
    rw [isCurrent]
    omega
  · next notCurrent =>
    -- The previous justified checkpoint is two epochs back.
    have previousLe := settled.2 (by omega)
    have isPrevious := recent.resolve_right notCurrent
    rw [isPrevious]
    omega

/-- The source of a weighing call is justified, and earlier than its target.

Take a chain from a state reached from genesis, and a call of it that justified a checkpoint.

The call's source for the checkpoint's epoch is one of the start's checkpoints.

Or a call of the chain justified it.

Its epoch is below the checkpoint's. -/
theorem CallRecord.source {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint} (reachable : Reachable config checks start)
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    JustifiedOrStart config checks start after (recordSource cached checkpoint.epoch) ∧
      (recordSource cached checkpoint.epoch).epoch.toNat < checkpoint.epoch.toNat := by
  have head := call.head
  have toAfter := call.toAfter
  have readsFrom := call.reads
  have stateReachable : Reachable config checks ⟨fork, state⟩ := reachable.reaches head
  have cachedSame : cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
      cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint := by
    obtain ⟨_, _, _, _, rfl⟩ := readsFrom.eq
    exact ⟨rfl, rfl⟩
  obtain ⟨-, previousJustified, currentJustified⟩ := head.checkpoints
  refine ⟨?_, recordSource_epoch_lt stateReachable readsFrom call.later call.recent⟩
  unfold recordSource
  rw [cachedSame.1, cachedSame.2]
  split
  · exact currentJustified.extendChain toAfter
  · exact previousJustified.extendChain toAfter

/-- `CallRecord.source` for a weighing call at an epoch boundary. -/
theorem WeighingCall.source {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed next : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint} (reachable : Reachable config checks start)
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    JustifiedOrStart config checks start after (recordSource cached checkpoint.epoch) ∧
      (recordSource cached checkpoint.epoch).epoch.toNat < checkpoint.epoch.toNat :=
  call.record.source reachable

/-- The source of a weighing call is justified, and earlier than its target, for some call.

This is `WeighingCall.source` for a call that `JustifiedBy` names. -/
theorem JustifiedBy.source {start after : ForkedBeaconState preset} {checkpoint : Checkpoint}
    (reachable : Reachable config checks start)
    (justified : JustifiedBy config checks start after checkpoint) :
    ∃ (fork : Fork) (state cached : BeaconState preset fork),
      Reaches config checks start ⟨fork, state⟩ ∧
      Reaches config checks ⟨fork, state⟩ after ∧ processSlot state = .ok cached ∧
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
      JustifiedOrStart config checks start after (recordSource cached checkpoint.epoch) ∧
      (recordSource cached checkpoint.epoch).epoch.toNat < checkpoint.epoch.toNat := by
  obtain ⟨fork, state, cached, _, _, _, call⟩ := justified
  exact ⟨fork, state, cached, call.head, call.toAfter, call.cachedOk, call.recent,
    call.source reachable⟩

/-- The source that a vote of epoch 1 read is the call's source, on a chain from genesis.

In epoch 1 both justified checkpoints are those of genesis, and they stay to epoch 2. -/
theorem recordSource_of_epochOne {start : ForkedBeaconState preset} {fork : Fork}
    {state cached : BeaconState preset fork} {checkpoint voteSource : Checkpoint}
    (reachable : Reachable config checks start) (readsFrom : ReadsFrom state cached)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch cached)
    (recent : checkpoint.epoch = getPreviousEpoch cached ∨
      checkpoint.epoch = getCurrentEpoch cached)
    (exception : checkpoint.epoch.toNat = 1 ∧
      ∃ (fork' : Fork) (epochOne : BeaconState preset fork'),
        Reaches config checks start ⟨fork', epochOne⟩ ∧
        Reaches config checks ⟨fork', epochOne⟩ ⟨fork, state⟩ ∧
        (getCurrentEpoch epochOne).toNat = 1 ∧ voteSource = epochOne.currentJustifiedCheckpoint) :
    voteSource = recordSource cached checkpoint.epoch := by
  obtain ⟨first, fork', epochOne, headOne, chain, epoch, source⟩ := exception
  -- In epoch 1 both justified checkpoints are the same, and they stay to epoch 2.
  have settled : PreviousSettled epochOne :=
    Reachable.previousSettled (forked := ⟨fork', epochOne⟩) (reachable.reaches headOne)
  obtain ⟨sameOne, -⟩ := settled.1 (by omega)
  have cachedSame : cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
      getCurrentEpoch cached = getCurrentEpoch state := by
    obtain ⟨_, _, _, _, rfl⟩ := readsFrom.eq
    exact ⟨rfl, rfl⟩
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  change 0 + 1 < _ at laterNat
  have previousNat := getPreviousEpoch_toNat cached
  -- The call is at epoch 2, and its target is the previous epoch.
  have notCurrent : checkpoint.epoch ≠ getCurrentEpoch cached := by
    intro same
    rw [same] at first
    omega
  have callEpoch : (getCurrentEpoch state).toNat ≤ 2 := by
    rw [← cachedSame.2]
    rcases recent with same | same
    · rw [same] at first
      omega
    · exact absurd same notCurrent
  obtain ⟨previous, -⟩ := chain.justified_of_early callEpoch
  unfold recordSource
  rw [ite_eq_right_of_eq_false _ _ (eq_false notCurrent), cachedSame.1, source]
  simp only at previous
  rw [previous, sameOne]

/-- From genesis, a counted voter of a weighing call signed the call's link, with no exception.

The voter's data has the checkpoint as target and the call's source as source.

Its flag may still come from the upgrade to Altair, or from the start of the chain. -/
theorem CallRecord.voters_signed_of_reachable {start after : ForkedBeaconState preset}
    {fork : Fork} {state cached weighed : BeaconState preset fork}
    {voters : List ValidatorIndex} {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (reachable : Reachable config checks start)
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    .altair ≤ fork → ∀ index ∈ voters,
      FlagAtStart start index.toNat TIMELY_TARGET_FLAG_INDEX ∨
      FlagFromAltairUpgrade config checks start ⟨fork, state⟩ index.toNat
        TIMELY_TARGET_FLAG_INDEX checkpoint.epoch ∨
      ∃ data, data.target = checkpoint ∧
        SignedTarget config checks start ⟨fork, state⟩ index data ∧
        data.source = recordSource cached checkpoint.epoch := by
  intro altair index member
  rcases call.voters_signed wide altair index member with atStart | upgraded |
    ⟨data, target, signed, source⟩
  · exact .inl atStart
  · exact .inr (.inl upgraded)
  refine .inr (.inr ⟨data, target, signed, ?_⟩)
  rcases source with same | exception
  · exact same
  · exact recordSource_of_epochOne reachable call.reads call.later call.recent exception

/-- `CallRecord.voters_signed_of_reachable` for a weighing call at an epoch boundary. -/
theorem WeighingCall.voters_signed_of_reachable {start after : ForkedBeaconState preset}
    {fork : Fork} {state cached weighed next : BeaconState preset fork}
    {voters : List ValidatorIndex} {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (reachable : Reachable config checks start)
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    .altair ≤ fork → ∀ index ∈ voters,
      FlagAtStart start index.toNat TIMELY_TARGET_FLAG_INDEX ∨
      FlagFromAltairUpgrade config checks start ⟨fork, state⟩ index.toNat
        TIMELY_TARGET_FLAG_INDEX checkpoint.epoch ∨
      ∃ data, data.target = checkpoint ∧
        SignedTarget config checks start ⟨fork, state⟩ index data ∧
        data.source = recordSource cached checkpoint.epoch :=
  call.record.voters_signed_of_reachable wide reachable

/-- `WeighingCall.voters_signed_of_reachable` for a call that `JustifiedBy` names. -/
theorem JustifiedBy.voters_signed_of_reachable {start after : ForkedBeaconState preset}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (reachable : Reachable config checks start)
    (justified : JustifiedBy config checks start after checkpoint) :
    ∃ (fork : Fork) (state cached : BeaconState preset fork) (voters : List ValidatorIndex),
      Reaches config checks start ⟨fork, state⟩ ∧
      Reaches config checks ⟨fork, state⟩ after ∧ processSlot state = .ok cached ∧
      GENESIS_EPOCH + 1 < getCurrentEpoch cached ∧
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
      TargetVoters cached checkpoint.epoch voters ∧ PassesThreshold cached voters ∧
      getBlockRoot cached checkpoint.epoch = .ok checkpoint.root ∧
      (.altair ≤ fork → ∀ index ∈ voters,
        FlagAtStart start index.toNat TIMELY_TARGET_FLAG_INDEX ∨
        FlagFromAltairUpgrade config checks start ⟨fork, state⟩ index.toNat
          TIMELY_TARGET_FLAG_INDEX checkpoint.epoch ∨
        ∃ data, data.target = checkpoint ∧
          SignedTarget config checks start ⟨fork, state⟩ index data ∧
          data.source = recordSource cached checkpoint.epoch) := by
  obtain ⟨fork, state, cached, _, _, voters, call⟩ := justified
  exact ⟨fork, state, cached, voters, call.head, call.toAfter, call.cachedOk, call.later,
    call.recent, call.counted, call.passes, call.rootOk,
    call.voters_signed_of_reachable wide reachable⟩

end EthLib.Consensus
