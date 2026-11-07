module

public import EthLib.Consensus.Proofs.Transition.Provenance.Justification
public import EthLib.Consensus.Proofs.Transition.Provenance.Roots

/-!
# Proofs: the weighing calls of a chain, and the checkpoints they justified

A chain weighs votes once per epoch, in the slot step that closes the epoch.

That step caches the slot, then runs justification and finalization on the cached state.

This file names such a call, and the checkpoints it justified.

A call can justify two checkpoints: that of the previous epoch and that of the current one.

When both pass, the state keeps only the current one.

The previous one still counts as justified: its bit is set, and finalization reads it.

So a justified checkpoint here is one that a call justified, kept or not.

Every justified checkpoint of a state of a chain is one of the start's, or one a call justified.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## One slot step -/

/-- A slot step closes its epoch when the slot after it starts a new epoch. -/
def ClosesEpoch (preset : Preset) (state : BeaconState preset fork) : Prop :=
  (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0

instance : Decidable (ClosesEpoch preset state) := by
  unfold ClosesEpoch
  infer_instance

/-- What one slot step does to the history.

It caches the slot.

If it closes the epoch, it then weighs the votes, and the checkpoints and bits are the weighed ones.

Otherwise the checkpoints and the bits stay. -/
theorem advanceSlot_history (computed : advanceSlot config checks state = .ok after) :
    ∃ cached, processSlot state = .ok cached ∧ after.slot.toNat = state.slot.toNat + 1 ∧
      after.latestBlockHeader = cached.latestBlockHeader ∧
      after.blockRoots = cached.blockRoots ∧ after.stateRoots = cached.stateRoots ∧
      if ClosesEpoch preset state then
        ∃ weighed, processJustificationAndFinalization cached = .ok weighed ∧
          after.justificationBits = weighed.justificationBits ∧
          after.previousJustifiedCheckpoint = weighed.previousJustifiedCheckpoint ∧
          after.currentJustifiedCheckpoint = weighed.currentJustifiedCheckpoint ∧
          after.finalizedCheckpoint = weighed.finalizedCheckpoint
      else
        after.justificationBits = state.justificationBits ∧
          after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
          after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
          after.finalizedCheckpoint = state.finalizedCheckpoint := by
  have slot := advanceSlot_slot computed
  obtain ⟨cached', cachedOk', -, header, blockRoots, stateRoots⟩ := advanceSlot_roots computed
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨fits, nextEq⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have sameCached := Except.ok.inj (cachedOk.symm.trans cachedOk')
  subst sameCached
  -- The caching keeps the bits and the checkpoints.
  have cachedSame : cached.justificationBits = state.justificationBits ∧
      cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
      cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
      cached.finalizedCheckpoint = state.finalizedCheckpoint := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl, rfl, rfl⟩
  have nextIs : next = state.slot + 1 := by
    apply UInt64.toNat_inj.mp
    rw [nextEq, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  refine ⟨cached, cachedOk, slot, header, blockRoots, stateRoots, ?_⟩
  unfold epochIfLast at epochedOk
  rw [nextIs] at epochedOk
  by_cases closes : ClosesEpoch preset state
  · have last : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := closes
    simp only [last, ↓reduceIte] at epochedOk
    simp only [closes, ↓reduceIte]
    obtain ⟨weighed, weighedOk, kept⟩ := processEpoch_kept epochedOk
    exact ⟨weighed, weighedOk, kept.justificationBits, kept.previousJustifiedCheckpoint,
      kept.currentJustifiedCheckpoint, kept.finalizedCheckpoint⟩
  · have notLast : ¬(state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := closes
    simp only [notLast, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
    simp only [closes, ↓reduceIte]
    subst epochedOk
    exact cachedSame

/-! ## Weighing calls and justified checkpoints -/

/-- The state a weighing call reads, from a state of a chain.

At an epoch boundary the call reads the caching of the state's slot.

A store may also call the weighing directly on a state, which it then reads as it is.

Either way the read state differs from the state at most in a few fields.

They are the two buffers of roots, the latest header and the availability of payloads. -/
def ReadsFrom (state cached : BeaconState preset fork) : Prop :=
  processSlot state = .ok cached ∨ cached = state

theorem ReadsFrom.eq {state cached : BeaconState preset fork} (reads : ReadsFrom state cached) :
    ∃ (stateRoots blockRoots : RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
      (header : BeaconBlockHeader)
      (availability : Since .glamsterdam fork (ExecutionPayloadAvailability preset)),
      cached = { state with
        stateRoots := stateRoots
        blockRoots := blockRoots
        latestBlockHeader := header
        executionPayloadAvailability := availability } := by
  rcases reads with cachedOk | rfl
  · exact processSlot_ok cachedOk
  · exact ⟨_, _, _, _, rfl⟩

theorem ReadsFrom.slot {state cached : BeaconState preset fork} (reads : ReadsFrom state cached) :
    cached.slot = state.slot := by
  obtain ⟨_, _, _, _, rfl⟩ := reads.eq
  rfl

/-- One weighing call of a chain, which justified a checkpoint.

The call ran in a slot step of the chain that closed an epoch.

The step starts at `state` and ends at `next`, and the chain goes on from `next` to `after`.

`cached` is the state after the caching of that slot, which the call read.

`weighed` is the state after the call.

The checkpoint's epoch is the previous or the current epoch of `cached`.

`voters` are the voters the call counted for it, and they passed the test.

Its root is the root `cached` held for the epoch's first slot.

The first two epochs weigh nothing, so the current epoch of `cached` is at least two.

Naming the call lets several facts speak about the same `cached` and `voters`. -/
def WeighingCall (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset)
    (fork : Fork) (state cached weighed next : BeaconState preset fork)
    (voters : List ValidatorIndex) (checkpoint : Checkpoint) : Prop :=
  Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
    advanceSlot config checks state = .ok next ∧ Reaches config checks ⟨fork, next⟩ after ∧
    ClosesEpoch preset state ∧ processSlot state = .ok cached ∧
    processJustificationAndFinalization cached = .ok weighed ∧
    GENESIS_EPOCH + 1 < getCurrentEpoch cached ∧
    (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
    TargetVoters cached checkpoint.epoch voters ∧ PassesThreshold cached voters ∧
    getBlockRoot cached checkpoint.epoch = .ok checkpoint.root

/-- A weighing call of a chain justified a checkpoint. -/
def JustifiedBy (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset)
    (checkpoint : Checkpoint) : Prop :=
  ∃ (fork : Fork) (state cached weighed next : BeaconState preset fork)
    (voters : List ValidatorIndex),
    WeighingCall config checks start after fork state cached weighed next voters checkpoint

namespace WeighingCall

variable {start after : ForkedBeaconState preset} {fork : Fork}
  {state cached weighed next : BeaconState preset fork} {voters : List ValidatorIndex}
  {checkpoint : Checkpoint}

theorem justifiedBy
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    JustifiedBy config checks start after checkpoint :=
  ⟨fork, state, cached, weighed, next, voters, call⟩

theorem head
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    Reaches config checks start ⟨fork, state⟩ :=
  call.1

/-- The chain runs from the call's state to the end. -/
theorem toAfter
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    Reaches config checks ⟨fork, state⟩ after :=
  ((Reaches.refl _).step (.slot call.2.1 call.2.2.1)).trans call.2.2.2.1

theorem cachedOk
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    processSlot state = .ok cached :=
  call.2.2.2.2.2.1

theorem later
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    GENESIS_EPOCH + 1 < getCurrentEpoch cached :=
  call.2.2.2.2.2.2.2.1

theorem recent
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached :=
  call.2.2.2.2.2.2.2.2.1

theorem counted
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    TargetVoters cached checkpoint.epoch voters :=
  call.2.2.2.2.2.2.2.2.2.1

theorem passes
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    PassesThreshold cached voters :=
  call.2.2.2.2.2.2.2.2.2.2.1

theorem rootOk
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    getBlockRoot cached checkpoint.epoch = .ok checkpoint.root :=
  call.2.2.2.2.2.2.2.2.2.2.2

theorem extend {last : ForkedBeaconState preset}
    (call : WeighingCall config checks start after fork state cached weighed next voters checkpoint)
    (step : Step config checks after last) :
    WeighingCall config checks start last fork state cached weighed next voters checkpoint :=
  have ⟨head, notDue, nextOk, tail, rest⟩ := call
  ⟨head, notDue, nextOk, tail.step step, rest⟩

end WeighingCall

theorem JustifiedBy.extend {start middle after : ForkedBeaconState preset} {checkpoint : Checkpoint}
    (justified : JustifiedBy config checks start middle checkpoint)
    (step : Step config checks middle after) : JustifiedBy config checks start after checkpoint :=
  have ⟨fork, state, cached, weighed, next, voters, head, notDue, nextOk, tail, rest⟩ := justified
  ⟨fork, state, cached, weighed, next, voters, head, notDue, nextOk, tail.step step, rest⟩

/-- A call of the weighing on a state of a chain, which justified a checkpoint.

It reads `cached`, from `state`, as `ReadsFrom` says, and its result is `weighed`.

The chain goes on from `state` to `after`.

A `WeighingCall` at an epoch boundary is one, and so is a call that a store makes on a state.

The facts that a weighing call gives hold for each such call. -/
def CallRecord (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset)
    (fork : Fork) (state cached weighed : BeaconState preset fork)
    (voters : List ValidatorIndex) (checkpoint : Checkpoint) : Prop :=
  Reaches config checks start ⟨fork, state⟩ ∧ Reaches config checks ⟨fork, state⟩ after ∧
    ReadsFrom state cached ∧ processJustificationAndFinalization cached = .ok weighed ∧
    GENESIS_EPOCH + 1 < getCurrentEpoch cached ∧
    (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
    TargetVoters cached checkpoint.epoch voters ∧ PassesThreshold cached voters ∧
    getBlockRoot cached checkpoint.epoch = .ok checkpoint.root

namespace CallRecord

variable {start after : ForkedBeaconState preset} {fork : Fork}
  {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
  {checkpoint : Checkpoint}

theorem head (call : CallRecord config checks start after fork state cached weighed voters
  checkpoint) :
    Reaches config checks start ⟨fork, state⟩ :=
  call.1

theorem toAfter
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    Reaches config checks ⟨fork, state⟩ after :=
  call.2.1

theorem reads
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    ReadsFrom state cached :=
  call.2.2.1

theorem weighedOk
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    processJustificationAndFinalization cached = .ok weighed :=
  call.2.2.2.1

theorem later
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    GENESIS_EPOCH + 1 < getCurrentEpoch cached :=
  call.2.2.2.2.1

theorem recent
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached :=
  call.2.2.2.2.2.1

theorem counted
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    TargetVoters cached checkpoint.epoch voters :=
  call.2.2.2.2.2.2.1

theorem passes
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    PassesThreshold cached voters :=
  call.2.2.2.2.2.2.2.1

theorem rootOk
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    getBlockRoot cached checkpoint.epoch = .ok checkpoint.root :=
  call.2.2.2.2.2.2.2.2

theorem extendChain {last : ForkedBeaconState preset}
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint)
    (chain : Reaches config checks after last) :
    CallRecord config checks start last fork state cached weighed voters checkpoint :=
  have ⟨head, tail, rest⟩ := call
  ⟨head, tail.trans chain, rest⟩

end CallRecord

/-- A weighing call at an epoch boundary is a call of the weighing on the state before the step.

It reads that state after the caching. -/
theorem WeighingCall.record {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed next : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    CallRecord config checks start after fork state cached weighed voters checkpoint :=
  have ⟨head, _, _, _, _, cachedOk, weighedOk, rest⟩ := call
  ⟨head, call.toAfter, .inl cachedOk, weighedOk, rest⟩

/-- A checkpoint is one of the start's three, or a weighing call of the chain justified it. -/
def JustifiedOrStart (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) (checkpoint : Checkpoint) : Prop :=
  checkpoint = start.state.finalizedCheckpoint ∨
    checkpoint = start.state.previousJustifiedCheckpoint ∨
    checkpoint = start.state.currentJustifiedCheckpoint ∨
    JustifiedBy config checks start after checkpoint

theorem JustifiedOrStart.extend {start middle after : ForkedBeaconState preset}
    {checkpoint : Checkpoint} (justified : JustifiedOrStart config checks start middle checkpoint)
    (step : Step config checks middle after) :
    JustifiedOrStart config checks start after checkpoint :=
  justified.imp_right (Or.imp_right (Or.imp_right (·.extend step)))

/-- The three checkpoints of a state. -/
def AllCheckpoints (holds : Checkpoint → Prop) (state : BeaconState preset fork) : Prop :=
  holds state.finalizedCheckpoint ∧ holds state.previousJustifiedCheckpoint ∧
    holds state.currentJustifiedCheckpoint

/-- Where the checkpoints of a chain's end come from.

Each of the finalized, previous justified and current justified checkpoints is one of the start's.

Or a weighing call of the chain justified it. -/
theorem Reaches.checkpoints {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) :
    AllCheckpoints (JustifiedOrStart config checks start after) after.state := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact ⟨.inl rfl, .inr (.inl rfl), .inr (.inr (.inl rfl))⟩
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    -- What held at the state before the step still holds after it.
    have kept : AllCheckpoints (JustifiedOrStart config checks start last) middle.state :=
      ⟨more.1.extend step, more.2.1.extend step, more.2.2.extend step⟩
    cases step with
    | @slot fork state next notDue computed =>
      obtain ⟨cached, cachedOk, -, -, -, -, closing⟩ := advanceSlot_history computed
      have cachedSame : cached.finalizedCheckpoint = state.finalizedCheckpoint ∧
          cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
          cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint := by
        obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
        exact ⟨rfl, rfl, rfl⟩
      split at closing
      · next closes =>
        obtain ⟨weighed, weighedOk, -, previousSame, currentSame, finalizedSame⟩ := closing
        unfold AllCheckpoints at kept ⊢
        simp only at kept ⊢
        rw [finalizedSame, previousSame, currentSame]
        rw [← cachedSame.1, ← cachedSame.2.1, ← cachedSame.2.2] at kept
        rcases processJustificationAndFinalization_weighs weighedOk with ⟨_, rfl⟩ |
          ⟨later, _, _, _, _, _, _, _, _, _, _, weighs⟩
        · exact kept
        obtain ⟨moved, -, finalized, -⟩ := weighJustificationAndFinalization_checkpoints weighs
        refine ⟨?_, by rw [moved]; exact kept.2.2, ?_⟩
        · rcases finalized with same | same | same <;> rw [same]
          · exact kept.1
          · exact kept.2.1
          · exact kept.2.2
        · rcases processJustificationAndFinalization_justified weighedOk with same |
            ⟨epoch, voters, root, recent, votersAre, passes, rootOk, justified⟩
          · rw [same]
            exact kept.2.2
          · rw [justified]
            exact .inr (.inr (.inr ⟨fork, state, cached, weighed, next, voters, middleChain, notDue,
              computed, .refl _, closes, cachedOk, weighedOk, later, recent, votersAre, passes,
              rootOk⟩))
      · obtain ⟨-, previousSame, currentSame, finalizedSame⟩ := closing
        unfold AllCheckpoints at kept ⊢
        simp only at kept ⊢
        rw [finalizedSame, previousSame, currentSame]
        exact kept
    | upgrade due computed =>
      have same := upgradeNext_history computed
      simp only [BeaconState.history, Prod.mk.injEq] at same
      unfold AllCheckpoints at kept ⊢
      rw [same.2.2.2.2.2.1, same.2.2.2.2.2.2.1, same.2.2.2.2.2.2.2]
      exact kept
    | block engine signed validateResult notDue computed =>
      have frame := frame_processBlock (applySignedBlock_ok computed).2.1
      unfold AllCheckpoints at kept ⊢
      simp only at kept ⊢
      rw [frame.finalized, frame.previousJustified, frame.currentJustified]
      exact kept

end EthLib.Consensus
