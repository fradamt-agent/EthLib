module

public import EthLib.Consensus.Proofs.Transition.Provenance.DirectCalls

/-!
# Proofs: provenance along a given run

The theorems of provenance take a chain and name the weighing calls of it.

A chain is `Reaches`, which says only that some run exists.

Two runs may reach the same state, so a call that a theorem names need not be on a given run.

The proofs find each call by induction on one run, so the calls they name are on that run.

This file states them for a given run.

Each call it names ran on a prefix of the run.

A prefix is a run from the start to the call's state whose states begin the run's states.

So two runs that share their first states share the calls on those states.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-! ## Prefixes of a run -/

namespace Run

variable {start : ForkedBeaconState preset}

/-- A run is a prefix of another: its states begin the other's states. -/
def Prefix {middle after : ForkedBeaconState preset} (pre : Run config checks start middle)
    (run : Run config checks start after) : Prop :=
  pre.states <+: run.states

theorem Prefix.refl {after : ForkedBeaconState preset} (run : Run config checks start after) :
    run.Prefix run :=
  List.prefix_refl _

theorem Prefix.trans {first second after : ForkedBeaconState preset}
    {one : Run config checks start first} {two : Run config checks start second}
    {run : Run config checks start after} (oneTwo : one.Prefix two) (twoRun : two.Prefix run) :
    one.Prefix run :=
  List.IsPrefix.trans oneTwo twoRun

theorem Prefix.snoc {middle last after : ForkedBeaconState preset}
    {pre : Run config checks start middle} {run : Run config checks start last}
    (onRun : pre.Prefix run) (step : Step config checks last after) :
    pre.Prefix (run.snoc step) :=
  List.IsPrefix.trans onRun (List.prefix_append _ _)

theorem Prefix.self_snoc {last after : ForkedBeaconState preset}
    (run : Run config checks start last) (step : Step config checks last after) :
    run.Prefix (run.snoc step) :=
  (Prefix.refl run).snoc step

/-- The end of a prefix is a state of the run. -/
theorem Prefix.mem {middle after : ForkedBeaconState preset}
    {pre : Run config checks start middle} {run : Run config checks start after}
    (onRun : pre.Prefix run) : middle ∈ run.states :=
  onRun.subset (end_mem_states pre)

end Run

/-! ## Calls on a run -/

/-- A weighing call at an epoch boundary justified a checkpoint, on a prefix of a run. -/
def JustifiedByOn {start after : ForkedBeaconState preset} (run : Run config checks start after)
    (checkpoint : Checkpoint) : Prop :=
  ∃ (fork : Fork) (state cached weighed next : BeaconState preset fork)
    (voters : List ValidatorIndex) (pre : Run config checks start ⟨fork, state⟩),
    WeighingCall config checks start after fork state cached weighed next voters checkpoint ∧
      pre.Prefix run

/-- A checkpoint is one of the start's three, or a call on a prefix of a run justified it. -/
def JustifiedOrStartOn {start after : ForkedBeaconState preset}
    (run : Run config checks start after) (checkpoint : Checkpoint) : Prop :=
  checkpoint = start.state.finalizedCheckpoint ∨
    checkpoint = start.state.previousJustifiedCheckpoint ∨
    checkpoint = start.state.currentJustifiedCheckpoint ∨
    JustifiedByOn run checkpoint

/-- A call of the weighing of either kind, on a prefix of a run. -/
def CallRecordOn {start after : ForkedBeaconState preset} (run : Run config checks start after)
    (fork : Fork) (state cached weighed : BeaconState preset fork)
    (voters : List ValidatorIndex) (checkpoint : Checkpoint) : Prop :=
  ∃ pre : Run config checks start ⟨fork, state⟩,
    CallRecord config checks start after fork state cached weighed voters checkpoint ∧
      pre.Prefix run

section

variable {start after : ForkedBeaconState preset} {run : Run config checks start after}
  {checkpoint : Checkpoint}

theorem JustifiedByOn.justifiedBy (justified : JustifiedByOn run checkpoint) :
    JustifiedBy config checks start after checkpoint :=
  have ⟨_, _, _, _, _, _, _, call, _⟩ := justified
  call.justifiedBy

theorem JustifiedByOn.snoc {last : ForkedBeaconState preset}
    (justified : JustifiedByOn run checkpoint)
    (step : Step config checks after last) : JustifiedByOn (run.snoc step) checkpoint :=
  have ⟨fork, state, cached, weighed, next, voters, pre, call, onRun⟩ := justified
  ⟨fork, state, cached, weighed, next, voters, pre, call.extend step, onRun.snoc step⟩

/-- A call on a prefix of a run is on the run. -/
theorem JustifiedByOn.mono {middle : ForkedBeaconState preset}
    {pre : Run config checks start middle} (justified : JustifiedByOn pre checkpoint)
    (onRun : pre.Prefix run) (tail : Reaches config checks middle after) :
    JustifiedByOn run checkpoint :=
  have ⟨fork, state, cached, weighed, next, voters, pre', call, onRun'⟩ := justified
  ⟨fork, state, cached, weighed, next, voters, pre', call.extendChain tail, onRun'.trans onRun⟩

/-- The call's state is a state of the run. -/
theorem JustifiedByOn.mem (justified : JustifiedByOn run checkpoint) :
    ∃ (fork : Fork) (state cached weighed next : BeaconState preset fork)
      (voters : List ValidatorIndex),
      WeighingCall config checks start after fork state cached weighed next voters checkpoint ∧
        (⟨fork, state⟩ : ForkedBeaconState preset) ∈ run.states :=
  have ⟨fork, state, cached, weighed, next, voters, _, call, onRun⟩ := justified
  ⟨fork, state, cached, weighed, next, voters, call, onRun.mem⟩

theorem JustifiedOrStartOn.justifiedOrStart (justified : JustifiedOrStartOn run checkpoint) :
    JustifiedOrStart config checks start after checkpoint :=
  justified.imp_right (Or.imp_right (Or.imp_right (·.justifiedBy)))

theorem JustifiedOrStartOn.snoc {last : ForkedBeaconState preset}
    (justified : JustifiedOrStartOn run checkpoint) (step : Step config checks after last) :
    JustifiedOrStartOn (run.snoc step) checkpoint :=
  justified.imp_right (Or.imp_right (Or.imp_right (·.snoc step)))

theorem JustifiedOrStartOn.mono {middle : ForkedBeaconState preset}
    {pre : Run config checks start middle} (justified : JustifiedOrStartOn pre checkpoint)
    (onRun : pre.Prefix run) (tail : Reaches config checks middle after) :
    JustifiedOrStartOn run checkpoint :=
  justified.imp_right (Or.imp_right (Or.imp_right (·.mono onRun tail)))

theorem CallRecordOn.record {fork : Fork} {state cached weighed : BeaconState preset fork}
    {voters : List ValidatorIndex}
    (call : CallRecordOn run fork state cached weighed voters checkpoint) :
    CallRecord config checks start after fork state cached weighed voters checkpoint :=
  have ⟨_, record, _⟩ := call
  record

theorem CallRecordOn.mem {fork : Fork} {state cached weighed : BeaconState preset fork}
    {voters : List ValidatorIndex}
    (call : CallRecordOn run fork state cached weighed voters checkpoint) :
    (⟨fork, state⟩ : ForkedBeaconState preset) ∈ run.states :=
  have ⟨_, _, onRun⟩ := call
  onRun.mem

end

/-! ## Checkpoints, bits and finalization along a run -/

/-- `Reaches.checkpoints` along a given run: each call it names ran on a prefix of the run. -/
theorem Run.checkpointsOn {start after : ForkedBeaconState preset}
    (run : Run config checks start after) :
    AllCheckpoints (JustifiedOrStartOn run) after.state := by
  induction run with
  | nil => exact ⟨.inl rfl, .inr (.inl rfl), .inr (.inr (.inl rfl))⟩
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    -- What held at the state before the step still holds after it.
    have kept : AllCheckpoints (JustifiedOrStartOn (run.snoc step)) middle.state :=
      ⟨more.1.snoc step, more.2.1.snoc step, more.2.2.snoc step⟩
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
            exact .inr (.inr (.inr ⟨fork, state, cached, weighed, next, voters, run,
              ⟨middleChain, notDue, computed, .refl _, closes, cachedOk, weighedOk, later, recent,
                votersAre, passes, rootOk⟩, Run.Prefix.self_snoc _ _⟩))
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

/-- `Reaches.justificationBit` along a given run. -/
theorem Run.justificationBitOn {start after : ForkedBeaconState preset}
    (run : Run config checks start after) (index : Nat)
    (inside : index < JUSTIFICATION_BITS_LENGTH.toNat)
    (set : after.state.justificationBits.bits[index] = true) :
    (∃ (other : Nat) (inside : other < JUSTIFICATION_BITS_LENGTH.toNat),
        start.state.justificationBits.bits[other] = true) ∨
      ∃ checkpoint : Checkpoint,
        checkpoint.epoch.toNat + index = (getPreviousEpoch after.state).toNat ∧
        JustifiedByOn run checkpoint := by
  induction run generalizing index with
  | nil => exact .inl ⟨index, inside, set⟩
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    cases step with
    | @slot fork state next notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, next⟩ := .slot notDue computed
      obtain ⟨cached, cachedOk, stepSlot, -, -, -, closing⟩ := advanceSlot_history computed
      have cachedSame : cached.justificationBits = state.justificationBits ∧
          getCurrentEpoch cached = getCurrentEpoch state := by
        obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
        exact ⟨rfl, rfl⟩
      split at closing
      · next closes =>
        obtain ⟨weighed, weighedOk, bitsSame, -, -, -⟩ := closing
        simp only at set ⊢
        rw [bitsSame] at set
        have previousNext := getPreviousEpoch_of_closes stepSlot closes
        rcases processJustificationAndFinalization_bits weighedOk with ⟨early, rfl⟩ |
          ⟨later, bit0, bit1, bit2, bit3⟩
        · -- The first two epochs keep the bits; no call ran before them.
          rw [cachedSame.1] at set
          rcases more index inside set with atStart | ⟨checkpoint, -, justified⟩
          · exact .inl atStart
          · exfalso
            have := justified.justifiedBy.late
            have earlyNat := UInt64.le_iff_toNat_le.mp early
            rw [cachedSame.2] at earlyNat
            change _ ≤ 0 + 1 at earlyNat
            simp only at this
            omega
        · rw [cachedSame.2] at later
          have laterNat := UInt64.lt_iff_toNat_lt.mp later
          change 0 + 1 < _ at laterNat
          have previousMiddle := getPreviousEpoch_toNat state
          rw [previousNext]
          -- A bit the call set stands for a checkpoint it justified.
          have record : ∀ {epoch : Epoch} {voters root},
              (epoch = getPreviousEpoch cached ∨ epoch = getCurrentEpoch cached) →
              TargetVoters cached epoch voters → PassesThreshold cached voters →
              getBlockRoot cached epoch = .ok root →
              JustifiedByOn (run.snoc (.slot notDue computed)) ⟨epoch, root⟩ :=
            fun recent votersAre passes rootOk =>
              ⟨fork, state, cached, weighed, next, _, run, ⟨middleChain, notDue, computed, .refl _,
                closes, cachedOk, weighedOk, by rw [cachedSame.2]; exact later, recent, votersAre,
                passes, rootOk⟩, Run.Prefix.self_snoc _ _⟩
          have cachedPrevious : getPreviousEpoch cached = getPreviousEpoch state := by
            unfold getPreviousEpoch
            rw [cachedSame.2]
          -- A bit moved from before stands for the same epoch, one place further back.
          have moved : ∀ (older : Nat) (olderInside : older < JUSTIFICATION_BITS_LENGTH.toNat),
              state.justificationBits.bits[older] = true →
              (∃ (other : Nat) (inside : other < JUSTIFICATION_BITS_LENGTH.toNat),
                  start.state.justificationBits.bits[other] = true) ∨
                ∃ checkpoint : Checkpoint,
                  checkpoint.epoch.toNat + (older + 1) = (getCurrentEpoch state).toNat ∧
                  JustifiedByOn (run.snoc (.slot notDue computed)) checkpoint := by
            intro older olderInside old
            rcases more older olderInside old with atStart | ⟨checkpoint, epoch, justified⟩
            · exact .inl atStart
            · exact .inr ⟨checkpoint, by simp only at epoch; omega, justified.snoc _⟩
          rcases index with _ | _ | _ | _ | index
          · obtain ⟨voters, root, votersAre, passes, rootOk⟩ := bit0 set
            exact .inr ⟨⟨_, root⟩, by simp only [cachedSame.2, Nat.add_zero],
              record (.inr rfl) votersAre passes rootOk⟩
          · rcases bit1 set with ⟨voters, root, votersAre, passes, rootOk⟩ | old
            · refine .inr ⟨⟨_, root⟩, ?_, record (.inl rfl) votersAre passes rootOk⟩
              simp only
              rw [cachedPrevious, previousMiddle]
              omega
            · exact moved 0 (by decide) (cachedSame.1 ▸ old)
          · rw [bit2] at set
            exact moved 1 (by decide) (cachedSame.1 ▸ set)
          · rw [bit3] at set
            exact moved 2 (by decide) (cachedSame.1 ▸ set)
          · exact absurd inside (by simp [JUSTIFICATION_BITS_LENGTH])
      · next notClosing =>
        obtain ⟨bitsSame, -, -, -⟩ := closing
        simp only at set ⊢
        rw [bitsSame] at set
        have sameEpoch := epoch_of_open stepSlot notClosing
        have previousSame : getPreviousEpoch next = getPreviousEpoch state := by
          unfold getPreviousEpoch
          rw [sameEpoch]
        rw [previousSame]
        rcases more index inside set with atStart | ⟨checkpoint, epoch, justified⟩
        · exact .inl atStart
        · exact .inr ⟨checkpoint, epoch, justified.snoc _⟩
    | @upgrade _ post due computed =>
      have theStep : Step config checks middle post.val := .upgrade due computed
      have same := upgradeNext_history computed
      simp only [BeaconState.history, Prod.mk.injEq] at same
      have previousSame : getPreviousEpoch post.val.state = getPreviousEpoch middle.state := by
        simp only [getPreviousEpoch, getCurrentEpoch, same.1]
      rw [same.2.2.2.2.1] at set
      rw [previousSame]
      rcases more index inside set with atStart | ⟨checkpoint, epoch, justified⟩
      · exact .inl atStart
      · exact .inr ⟨checkpoint, epoch, justified.snoc _⟩
    | @block fork engine signed validateResult state post notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, post⟩ :=
        .block engine signed validateResult notDue computed
      have postSlot := processBlock_slot (applySignedBlock_ok computed).2.1
      have previousSame : getPreviousEpoch post = getPreviousEpoch state := by
        simp only [getPreviousEpoch, getCurrentEpoch, postSlot]
      simp only at set ⊢
      rw [applySignedBlock_bits computed] at set
      rw [previousSame]
      rcases more index inside set with atStart | ⟨checkpoint, epoch, justified⟩
      · exact .inl atStart
      · exact .inr ⟨checkpoint, epoch, justified.snoc _⟩

/-- `Reaches.newestBit` along a given run: the call ran on a prefix of the run. -/
theorem Run.newestBitOn {start after : ForkedBeaconState preset}
    (run : Run config checks start after)
    (set : after.state.justificationBits.bits[0] = true) :
    (∃ (other : Nat) (inside : other < JUSTIFICATION_BITS_LENGTH.toNat),
        start.state.justificationBits.bits[other] = true) ∨
      ∃ (fork : Fork) (state cached weighed next : BeaconState preset fork)
        (voters : List ValidatorIndex) (root : Root) (pre : Run config checks start ⟨fork, state⟩),
        WeighingCall config checks start after fork state cached weighed next voters
          ⟨getCurrentEpoch cached, root⟩ ∧ pre.Prefix run ∧
        (getCurrentEpoch cached).toNat + 1 = (getCurrentEpoch after.state).toNat ∧
        after.state.previousJustifiedCheckpoint = cached.currentJustifiedCheckpoint := by
  induction run with
  | nil => exact .inl ⟨0, by decide, set⟩
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    cases step with
    | @slot fork state next notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, next⟩ := .slot notDue computed
      obtain ⟨cached, cachedOk, stepSlot, -, -, -, closing⟩ := advanceSlot_history computed
      have cachedSame : cached.justificationBits = state.justificationBits ∧
          getCurrentEpoch cached = getCurrentEpoch state := by
        obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
        exact ⟨rfl, rfl⟩
      split at closing
      · next closes =>
        obtain ⟨weighed, weighedOk, bitsSame, previousSame, -, -⟩ := closing
        simp only at set ⊢
        rw [bitsSame] at set
        have nextEpoch := epoch_of_closes stepSlot closes
        rcases processJustificationAndFinalization_weighs weighedOk with ⟨early, rfl⟩ |
          ⟨later, _, _, _, _, _, _, _, _, _, _, weighs⟩
        · -- The first two epochs keep the bits, and no call ran before them.
          rw [cachedSame.1] at set
          rcases more set with atStart | ⟨_, _, cached', _, _, _, _, _, call, _, epochs, _⟩
          · exact .inl atStart
          · exfalso
            have callLater := UInt64.lt_iff_toNat_lt.mp call.later
            have earlyNat := UInt64.le_iff_toNat_le.mp early
            rw [cachedSame.2] at earlyNat
            change _ ≤ 0 + 1 at earlyNat
            change 0 + 1 < _ at callLater
            simp only at epochs
            omega
        · rcases processJustificationAndFinalization_bits weighedOk with ⟨early, -⟩ |
            ⟨-, bit0, -⟩
          · exact absurd later (UInt64.not_lt.mpr early)
          obtain ⟨voters, root, counted, passes, rootOk⟩ := bit0 set
          refine .inr ⟨fork, state, cached, weighed, next, voters, root, run,
            ⟨middleChain, notDue, computed, .refl _, closes, cachedOk, weighedOk, later, .inr rfl,
              counted, passes, rootOk⟩, Run.Prefix.self_snoc _ _, ?_, ?_⟩
          · rw [nextEpoch, cachedSame.2]
          · rw [previousSame, (weighJustificationAndFinalization_checkpoints weighs).1]
      · next notClosing =>
        obtain ⟨bitsSame, previousSame, -, -⟩ := closing
        simp only at set ⊢
        rw [bitsSame] at set
        have sameEpoch := epoch_of_open stepSlot notClosing
        rcases more set with atStart | ⟨fork', state', cached', weighed', next', voters', root',
          pre, call, onRun, epochs, previous⟩
        · exact .inl atStart
        · refine .inr ⟨fork', state', cached', weighed', next', voters', root', pre,
            call.extend theStep, onRun.snoc _,
            ?_, ?_⟩
          · rw [sameEpoch]
            exact epochs
          · rw [previousSame]
            exact previous
    | @upgrade _ post due computed =>
      have theStep : Step config checks middle post.val := .upgrade due computed
      have same := upgradeNext_history computed
      simp only [BeaconState.history, Prod.mk.injEq] at same
      have epochSame : getCurrentEpoch post.val.state = getCurrentEpoch middle.state := by
        simp only [getCurrentEpoch, same.1]
      rw [same.2.2.2.2.1] at set
      rcases more set with atStart | ⟨fork', state', cached', weighed', next', voters', root',
        pre, call, onRun, epochs, previous⟩
      · exact .inl atStart
      · refine .inr ⟨fork', state', cached', weighed', next', voters', root', pre,
          call.extend theStep, onRun.snoc _,
          ?_, ?_⟩
        · rw [epochSame]
          exact epochs
        · rw [same.2.2.2.2.2.1]
          exact previous
    | @block fork engine signed validateResult state post notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, post⟩ :=
        .block engine signed validateResult notDue computed
      have frame := frame_processBlock (applySignedBlock_ok computed).2.1
      have epochSame : getCurrentEpoch post = getCurrentEpoch state := by
        simp only [getCurrentEpoch, frame.slot]
      simp only at set ⊢
      rw [applySignedBlock_bits computed] at set
      rcases more set with atStart | ⟨fork', state', cached', weighed', next', voters', root',
        pre, call, onRun, epochs, previous⟩
      · exact .inl atStart
      · refine .inr ⟨fork', state', cached', weighed', next', voters', root', pre,
          call.extend theStep, onRun.snoc _,
          ?_, ?_⟩
        · simp only at epochs ⊢
          rw [epochSame]
          exact epochs
        · simp only at previous ⊢
          rw [frame.previousJustified]
          exact previous


/-- `FinalizedBy` along a given run.

The call's state and the state after its slot step are both ends of prefixes of the run. -/
def FinalizedByOn {start after : ForkedBeaconState preset} (run : Run config checks start after)
    (checkpoint : Checkpoint) : Prop :=
  ∃ (fork : Fork) (state cached weighed next : BeaconState preset fork)
    (pre : Run config checks start ⟨fork, state⟩) (toNext : Run config checks start ⟨fork, next⟩),
    pre.Prefix run ∧ toNext.Prefix run ∧
    Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
    advanceSlot config checks state = .ok next ∧ Reaches config checks ⟨fork, next⟩ after ∧
    ClosesEpoch preset state ∧ processSlot state = .ok cached ∧
    processJustificationAndFinalization cached = .ok weighed ∧
    GENESIS_EPOCH + 1 < getCurrentEpoch cached ∧
    next.justificationBits = weighed.justificationBits ∧
    ((checkpoint = cached.currentJustifiedCheckpoint ∧
        ((next.justificationBits.bits[0] && next.justificationBits.bits[1] &&
            next.justificationBits.bits[2] &&
            decide (cached.currentJustifiedCheckpoint.epoch.toNat + 2 =
              (getCurrentEpoch cached).toNat)) ||
          (next.justificationBits.bits[0] && next.justificationBits.bits[1] &&
            decide (cached.currentJustifiedCheckpoint.epoch.toNat + 1 =
              (getCurrentEpoch cached).toNat))) = true) ∨
      (checkpoint = cached.previousJustifiedCheckpoint ∧
        ((next.justificationBits.bits[1] && next.justificationBits.bits[2] &&
            next.justificationBits.bits[3] &&
            decide (cached.previousJustifiedCheckpoint.epoch.toNat + 3 =
              (getCurrentEpoch cached).toNat)) ||
          (next.justificationBits.bits[1] && next.justificationBits.bits[2] &&
            decide (cached.previousJustifiedCheckpoint.epoch.toNat + 2 =
              (getCurrentEpoch cached).toNat))) = true))

theorem FinalizedByOn.snoc {start after last : ForkedBeaconState preset}
    {run : Run config checks start after} {checkpoint : Checkpoint}
    (finalized : FinalizedByOn run checkpoint) (step : Step config checks after last) :
    FinalizedByOn (run.snoc step) checkpoint :=
  have ⟨fork, state, cached, weighed, next, pre, toNext, prePrefix, nextPrefix, head, notDue,
    nextOk, tail, rest⟩ := finalized
  ⟨fork, state, cached, weighed, next, pre, toNext, prePrefix.snoc step, nextPrefix.snoc step,
    head, notDue, nextOk, tail.step step, rest⟩

/-- `Reaches.finalized` along a given run: the call ran on a prefix of the run. -/
theorem Run.finalizedOn {start after : ForkedBeaconState preset}
    (run : Run config checks start after) :
    after.state.finalizedCheckpoint = start.state.finalizedCheckpoint ∨
      FinalizedByOn run after.state.finalizedCheckpoint := by
  induction run with
  | nil => exact .inl rfl
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    cases step with
    | @slot fork state next notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, next⟩ := .slot notDue computed
      obtain ⟨cached, cachedOk, -, -, -, -, closing⟩ := advanceSlot_history computed
      have cachedSame : cached.finalizedCheckpoint = state.finalizedCheckpoint := by
        obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
        rfl
      split at closing
      · next closes =>
        obtain ⟨weighed, weighedOk, bitsSame, -, -, finalizedSame⟩ := closing
        simp only at more ⊢
        rw [finalizedSame]
        rcases processJustificationAndFinalization_weighs weighedOk with ⟨_, rfl⟩ |
          ⟨later, _, _, _, _, _, _, _, _, _, _, weighs⟩
        · rw [cachedSame]
          exact more.imp id (·.snoc _)
        obtain ⟨_, _, _, _, _, _, _, _, _, finalizedRule, -⟩ :=
          weighJustificationAndFinalization_eq weighs
        rw [← bitsSame] at finalizedRule
        split at finalizedRule
        · next byCurrent =>
          exact .inr ⟨fork, state, cached, weighed, next, run, run.snoc _, Run.Prefix.self_snoc _ _,
            Run.Prefix.refl _, middleChain, notDue, computed, .refl _,
            closes, cachedOk, weighedOk, later, bitsSame, .inl ⟨finalizedRule, byCurrent⟩⟩
        · split at finalizedRule
          · next byPrevious =>
            exact .inr ⟨fork, state, cached, weighed, next, run, run.snoc _,
              Run.Prefix.self_snoc _ _, Run.Prefix.refl _, middleChain, notDue, computed, .refl _,
              closes, cachedOk, weighedOk, later, bitsSame,
              .inr ⟨finalizedRule, byPrevious⟩⟩
          · rw [finalizedRule, cachedSame]
            exact more.imp id (·.snoc _)
      · obtain ⟨-, -, -, finalizedSame⟩ := closing
        simp only at more ⊢
        rw [finalizedSame]
        exact more.imp id (·.snoc _)
    | @upgrade _ post due computed =>
      have same := upgradeNext_history computed
      simp only [BeaconState.history, Prod.mk.injEq] at same
      rw [same.2.2.2.2.2.2.2]
      exact more.imp id (·.snoc _)
    | @block fork engine signed validateResult state post notDue computed =>
      have frame := frame_processBlock (applySignedBlock_ok computed).2.1
      simp only at more ⊢
      rw [frame.finalized]
      exact more.imp id (·.snoc _)

/-- `KFinalizedBy` along a given run.

The justified checkpoints are the start's, or justified by calls on prefixes of the run.

The link is a call on a prefix of the run. -/
def KFinalizedByOn {start after : ForkedBeaconState preset} (run : Run config checks start after)
    (c : Checkpoint) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ 2 ∧ ∃ cs : ℕ → Checkpoint, cs 0 = c ∧
    (∀ i ≤ k, (cs i).epoch.toNat = c.epoch.toNat + i) ∧
    (∀ i < k, JustifiedOrStartOn run (cs i)) ∧
    (∀ i < k, PastAncestor config checks start after
        ((cs i).epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) (cs i).root (cs (i + 1)).root ∨
      ZeroRootFound config checks start after) ∧
    (∀ i ≤ k, 1 ≤ i → (cs i).root ≠ Vector.replicate 32 0 ∨
      ZeroHeaderFound config checks start after) ∧
    ∃ (fork : Fork) (state cached weighed next : BeaconState preset fork)
      (voters : List ValidatorIndex) (pre : Run config checks start ⟨fork, state⟩),
      WeighingCall config checks start after fork state cached weighed next voters (cs k) ∧
      pre.Prefix run ∧ recordSource cached (cs k).epoch = c

/-- Along a run, `k`-finalization gives `k`-finalization of its chain. -/
theorem KFinalizedByOn.kFinalizedBy {start after : ForkedBeaconState preset}
    {run : Run config checks start after} {c : Checkpoint} (finalized : KFinalizedByOn run c) :
    KFinalizedBy config checks start after c :=
  have ⟨k, one, two, cs, first, epochs, justified, ancestry, nonzero, fork, state, cached, weighed,
    next, voters, _, call, _, source⟩ := finalized
  ⟨k, one, two, cs, first, epochs, fun i below => (justified i below).justifiedOrStart, ancestry,
    nonzero, fork, state, cached, weighed, next, voters, call, source⟩

/-- `kFinalizedBy_one` along a run.

It is `1`-finalization from a justified `c` and a link from it to the next epoch. -/
theorem kFinalizedByOn_one {start middle after : ForkedBeaconState preset} {c : Checkpoint}
    {run : Run config checks start after}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start) (tail : Reaches config checks middle after)
    (cJustified : JustifiedBy config checks start middle c) (cOn : JustifiedOrStartOn run c)
    {fork : Fork} {state cached weighed next : BeaconState preset fork}
    {voters : List ValidatorIndex} {d : Checkpoint}
    (link : WeighingCall config checks start middle fork state cached weighed next voters d)
    (linkPre : Run config checks start ⟨fork, state⟩) (linkOn : linkPre.Prefix run)
    (source : recordSource cached d.epoch = c) (epoch : d.epoch.toNat = c.epoch.toNat + 1)
    (recentEnd : middle.state.slot.toNat ≤
      c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    KFinalizedByOn run c := by
  refine ⟨1, Nat.le_refl _, by decide, fun i => if i = 0 then c else d, rfl, ?_, ?_, ?_, ?_,
    fork, state, cached, weighed, next, voters, linkPre, link.extendChain tail, linkOn,
    source⟩
  · intro i below
    rcases i with _ | _ | i
    · simp
    · simp [epoch]
    · omega
  · intro i below
    rcases i with _ | i
    · exact cOn
    · omega
  · intro i below
    rcases i with _ | i
    · exact JustifiedBy.pastAncestor_at wide genesis tail cJustified link.justifiedBy
        (by simp [epoch]) recentEnd
    · omega
  · intro i below one
    rcases i with _ | _ | i
    · omega
    · exact JustifiedBy.nonzero_at wide genesis tail link.justifiedBy
    · omega

/-- `kFinalizedBy_two` along a run.

It is `2`-finalization from a justified `c` and a justified checkpoint of the next epoch.

A link goes from `c` to the epoch after that. -/
theorem kFinalizedByOn_two {start middle after : ForkedBeaconState preset} {c d : Checkpoint}
    {run : Run config checks start after}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start) (tail : Reaches config checks middle after)
    (cJustified : JustifiedBy config checks start middle c) (cOn : JustifiedOrStartOn run c)
    (dJustified : JustifiedBy config checks start middle d) (dOn : JustifiedOrStartOn run d)
    (dEpoch : d.epoch.toNat = c.epoch.toNat + 1)
    {fork : Fork} {state cached weighed next : BeaconState preset fork}
    {voters : List ValidatorIndex} {e : Checkpoint}
    (link : WeighingCall config checks start middle fork state cached weighed next voters e)
    (linkPre : Run config checks start ⟨fork, state⟩) (linkOn : linkPre.Prefix run)
    (source : recordSource cached e.epoch = c) (eEpoch : e.epoch.toNat = c.epoch.toNat + 2)
    (recentEnd : middle.state.slot.toNat ≤
      c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    KFinalizedByOn run c := by
  refine ⟨2, by decide, Nat.le_refl _, fun i => if i = 0 then c else if i = 1 then d else e, rfl,
    ?_, ?_, ?_, ?_, fork, state, cached, weighed, next, voters, linkPre, link.extendChain tail,
    linkOn,
    source⟩
  · intro i below
    rcases i with _ | _ | _ | i
    · simp
    · simp [dEpoch]
    · simp [eEpoch]
    · omega
  · intro i below
    rcases i with _ | _ | i
    · exact cOn
    · exact dOn
    · omega
  · intro i below
    rcases i with _ | _ | i
    · exact JustifiedBy.pastAncestor_at wide genesis tail cJustified dJustified
        (by simp [dEpoch]) recentEnd
    · refine JustifiedBy.pastAncestor_at wide genesis tail dJustified link.justifiedBy
        (by simp [dEpoch, eEpoch])
        ?_
      show _ ≤ d.epoch.toNat * _ + _
      rw [dEpoch, Nat.add_mul, Nat.one_mul]
      omega
    · omega
  · intro i below one
    rcases i with _ | _ | _ | i
    · omega
    · exact JustifiedBy.nonzero_at wide genesis tail dJustified
    · exact JustifiedBy.nonzero_at wide genesis tail link.justifiedBy
    · omega


/-! ## The four rules along a run -/

/-- `Reaches.finalized_rule` along a given run.

Each call it names ran on a prefix of the run. -/
theorem Run.finalized_ruleOn {start after : ForkedBeaconState preset}
    (wide : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start) (run : Run config checks start after) :
    after.state.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      KFinalizedByOn run after.state.finalizedCheckpoint := by
  have wide2 : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    omega
  obtain ⟨-, startPrevious, startCurrent, startFinalized⟩ := genesis_state genesis
  have noStartBit : ¬∃ (other : Nat) (inside : other < JUSTIFICATION_BITS_LENGTH.toNat),
      start.state.justificationBits.bits[other] = true := by
    rintro ⟨other, inside, set⟩
    rw [genesis_bits genesis other inside] at set
    cases set
  rcases run.finalizedOn with same | ⟨fork, state, cached, weighed, next, pre, toNextRun, preOn,
    nextOn, head, notDue, nextOk, tail, closes, cachedOk, weighedOk, later, bitsSame, rule⟩
  · exact .inl (same.trans startFinalized)
  generalize after.state.finalizedCheckpoint = c at rule ⊢
  have theStep : Step config checks ⟨fork, state⟩ ⟨fork, next⟩ := .slot notDue nextOk
  have toNext : Reaches config checks start ⟨fork, next⟩ := head.step theStep
  have stepSlot := advanceSlot_slot nextOk
  have nextEpoch := epoch_of_closes stepSlot closes
  have cachedSame : cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
      cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
      cached.justificationBits = state.justificationBits ∧
      getCurrentEpoch cached = getCurrentEpoch state := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl, rfl, rfl⟩
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  change 0 + 1 < _ at laterNat
  rw [← cachedSame.2.2.2] at nextEpoch
  -- The slot after the call is the first of the next epoch.
  have slotEq : next.slot.toNat =
      ((getCurrentEpoch cached).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    have fits : state.slot.toNat + 1 < 2 ^ 64 := stepSlot ▸ UInt64.toNat_lt next.slot
    have divides := (closesEpoch_iff fits).mp closes
    have epochIs := getCurrentEpoch_toNat next
    rw [stepSlot] at epochIs ⊢
    rw [← nextEpoch, epochIs, Nat.div_mul_cancel divides]
  -- The roots of checkpoints up to three epochs back are still in the buffer.
  have recent : ∀ (checkpoint : Checkpoint) (back : Nat), back ≤ 3 →
      checkpoint.epoch.toNat + back = (getCurrentEpoch cached).toNat →
      (⟨fork, next⟩ : ForkedBeaconState preset).state.slot.toNat ≤
        checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat +
          preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    intro checkpoint back few epochs
    show next.slot.toNat ≤ _
    rw [slotEq, ← epochs, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat few
    omega
  -- An old justified checkpoint is genesis, or a call of the chain justified it.
  have toAfter : Reaches config checks ⟨fork, state⟩ after :=
    ((Reaches.refl _).step theStep).trans tail
  have old : ∀ checkpoint, JustifiedOrStartOn pre checkpoint →
      checkpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        (JustifiedBy config checks start ⟨fork, next⟩ checkpoint ∧
          JustifiedOrStartOn run checkpoint) := by
    intro checkpoint justified
    rcases justified with same | same | same | justified
    · exact .inl (same.trans startFinalized)
    · exact .inl (same.trans startPrevious)
    · exact .inl (same.trans startCurrent)
    · exact .inr ⟨justified.justifiedBy.extend theStep,
        .inr (.inr (.inr (justified.mono preOn toAfter)))⟩
  obtain ⟨-, previousOld, currentOld⟩ := pre.checkpointsOn
  rw [← cachedSame.1] at currentOld
  rw [← cachedSame.2.1] at previousOld
  -- What the new bits stand for.
  rcases processJustificationAndFinalization_bits weighedOk with ⟨early, -⟩ |
    ⟨-, bit0, bit1, -, -⟩
  · exact absurd later (UInt64.not_lt.mpr early)
  rw [← bitsSame] at bit0 bit1
  have link0 : next.justificationBits.bits[0] = true →
      ∃ (voters : List ValidatorIndex) (root : Root),
        WeighingCall config checks start ⟨fork, next⟩ fork state cached weighed next voters
          ⟨getCurrentEpoch cached, root⟩ ∧ pre.Prefix run := by
    intro set
    obtain ⟨voters, root, counted, passes, rootOk⟩ := bit0 set
    exact ⟨voters, root, ⟨head, notDue, nextOk, .refl _, closes, cachedOk, weighedOk, later,
      .inr rfl, counted, passes, rootOk⟩, preOn⟩
  have link1 : next.justificationBits.bits[1] = true →
      ∃ (fork' : Fork) (state' cached' weighed' next' : BeaconState preset fork')
        (voters : List ValidatorIndex) (d : Checkpoint)
        (pre' : Run config checks start ⟨fork', state'⟩),
        WeighingCall config checks start ⟨fork, next⟩ fork' state' cached' weighed' next' voters d ∧
        pre'.Prefix run ∧ d.epoch.toNat + 1 = (getCurrentEpoch cached).toNat ∧
        recordSource cached' d.epoch = cached.previousJustifiedCheckpoint := by
    intro set
    rcases bit1 set with ⟨voters, root, counted, passes, rootOk⟩ | older
    · -- This call justified the previous epoch, from its old previous justified checkpoint.
      have previousNat := getPreviousEpoch_toNat cached
      have notCurrent : getPreviousEpoch cached ≠ getCurrentEpoch cached := fun same => by
        rw [same] at previousNat
        omega
      refine ⟨fork, state, cached, weighed, next, voters, ⟨getPreviousEpoch cached, root⟩, pre,
        ⟨head, notDue, nextOk, .refl _, closes, cachedOk, weighedOk, later, .inl rfl, counted,
          passes, rootOk⟩, preOn, by simp only; omega, ?_⟩
      unfold recordSource
      exact ite_eq_right_of_eq_false _ _ (eq_false notCurrent)
    · -- The call before justified it as its current epoch, from this call's old previous one.
      rw [cachedSame.2.2.1] at older
      rcases pre.newestBitOn older with atStart | ⟨fork', state', cached', weighed', next', voters,
        root, pre', call, onPre, epochs, previous⟩
      · exact absurd atStart noStartBit
      refine ⟨fork', state', cached', weighed', next', voters, ⟨getCurrentEpoch cached', root⟩,
        pre', call.extend theStep, onPre.trans preOn,
        by simp only; rw [cachedSame.2.2.2]; exact epochs, ?_⟩
      unfold recordSource
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), cachedSame.2.1]
      exact previous.symm
  have justifiedBit : ∀ (index : Nat) (inside : index < JUSTIFICATION_BITS_LENGTH.toNat),
      next.justificationBits.bits[index] = true →
      ∃ d : Checkpoint, d.epoch.toNat + index = (getCurrentEpoch cached).toNat ∧
        JustifiedBy config checks start ⟨fork, next⟩ d ∧ JustifiedOrStartOn run d := by
    intro index inside set
    rcases toNextRun.justificationBitOn index inside set with atStart | ⟨d, epoch, justified⟩
    · exact absurd atStart noStartBit
    refine ⟨d, ?_, justified.justifiedBy, .inr (.inr (.inr (justified.mono nextOn tail)))⟩
    have previousNat := getPreviousEpoch_toNat next
    simp only at epoch
    omega
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at rule
  rcases rule with ⟨rfl, ⟨⟨⟨b0, b1⟩, b2⟩, back⟩ | ⟨⟨b0, b1⟩, back⟩⟩ |
    ⟨rfl, ⟨⟨⟨b1, b2⟩, b3⟩, back⟩ | ⟨⟨b1, b2⟩, back⟩⟩
  · -- Old current justified, two epochs back.
    rcases old _ currentOld with genesisCheckpoint | ⟨cJustified, cOn⟩
    · exact .inl genesisCheckpoint
    right
    obtain ⟨d, dEpoch, dJustified, dOn⟩ := justifiedBit 1 (by decide) b1
    obtain ⟨voters, root, link, linkOn⟩ := link0 b0
    refine kFinalizedByOn_two wide2 genesis tail cJustified cOn dJustified dOn (by omega) link pre
      linkOn ?_
      (by simp only; omega) (recent _ 2 (by decide) back)
    unfold recordSource
    exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
  · -- Old current justified, one epoch back.
    rcases old _ currentOld with genesisCheckpoint | ⟨cJustified, cOn⟩
    · exact .inl genesisCheckpoint
    right
    obtain ⟨voters, root, link, linkOn⟩ := link0 b0
    refine kFinalizedByOn_one wide2 genesis tail cJustified cOn link pre linkOn ?_
      (by simp only; omega)
      (recent _ 1 (by decide) back)
    unfold recordSource
    exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
  · -- Old previous justified, three epochs back.
    rcases old _ previousOld with genesisCheckpoint | ⟨cJustified, cOn⟩
    · exact .inl genesisCheckpoint
    right
    obtain ⟨d, dEpoch, dJustified, dOn⟩ := justifiedBit 2 (by decide) b2
    obtain ⟨fork', state', cached', weighed', next', voters, e, pre', link, linkOn, eEpoch,
      source⟩ :=
      link1 b1
    exact kFinalizedByOn_two wide2 genesis tail cJustified cOn dJustified dOn (by omega) link pre'
      linkOn source
      (by omega) (recent _ 3 (by decide) back)
  · -- Old previous justified, two epochs back.
    rcases old _ previousOld with genesisCheckpoint | ⟨cJustified, cOn⟩
    · exact .inl genesisCheckpoint
    right
    obtain ⟨fork', state', cached', weighed', next', voters, e, pre', link, linkOn, eEpoch,
      source⟩ :=
      link1 b1
    exact kFinalizedByOn_one wide2 genesis tail cJustified cOn link pre' linkOn source (by omega)
      (recent _ 2 (by decide) back)

/-! ## The source of a call along a run -/

/-- The source of a call on a prefix `pre` of a run is justified on `pre`, before the call.

It is earlier than its target.

So the source's call ran on the run, at or before the call's state. -/
theorem CallRecord.sourceOn {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint} (reachable : Reachable config checks start)
    (pre : Run config checks start ⟨fork, state⟩)
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    JustifiedOrStartOn pre (recordSource cached checkpoint.epoch) ∧
      (recordSource cached checkpoint.epoch).epoch.toNat < checkpoint.epoch.toNat := by
  have stateReachable : Reachable config checks ⟨fork, state⟩ := reachable.reaches call.head
  have cachedSame : cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
      cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint := by
    obtain ⟨_, _, _, _, rfl⟩ := call.reads.eq
    exact ⟨rfl, rfl⟩
  obtain ⟨-, previousJustified, currentJustified⟩ := pre.checkpointsOn
  refine ⟨?_, recordSource_epoch_lt stateReachable call.reads call.later call.recent⟩
  unfold recordSource
  rw [cachedSame.1, cachedSame.2]
  split
  · exact currentJustified
  · exact previousJustified

/-- `CallRecord.sourceOn` for a call on a prefix of a run: the source is justified on the run. -/
theorem CallRecordOn.source {start after : ForkedBeaconState preset}
    {run : Run config checks start after} {fork : Fork}
    {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint} (reachable : Reachable config checks start)
    (call : CallRecordOn run fork state cached weighed voters checkpoint) :
    ∃ pre : Run config checks start ⟨fork, state⟩, pre.Prefix run ∧
      JustifiedOrStartOn pre (recordSource cached checkpoint.epoch) ∧
      JustifiedOrStartOn run (recordSource cached checkpoint.epoch) ∧
      (recordSource cached checkpoint.epoch).epoch.toNat < checkpoint.epoch.toNat := by
  obtain ⟨pre, record, onRun⟩ := call
  obtain ⟨justified, before⟩ := record.sourceOn reachable pre
  exact ⟨pre, onRun, justified, justified.mono onRun record.toAfter, before⟩

/-- A call on a prefix of a run at an epoch boundary is a call record on the run. -/
theorem JustifiedByOn.callRecordOn {start after : ForkedBeaconState preset}
    {run : Run config checks start after} {checkpoint : Checkpoint}
    (justified : JustifiedByOn run checkpoint) :
    ∃ (fork : Fork) (state cached weighed : BeaconState preset fork)
      (voters : List ValidatorIndex),
      CallRecordOn run fork state cached weighed voters checkpoint :=
  have ⟨fork, state, cached, weighed, _, voters, pre, call, onRun⟩ := justified
  ⟨fork, state, cached, weighed, voters, pre, call.record, onRun⟩

end EthLib.Consensus
