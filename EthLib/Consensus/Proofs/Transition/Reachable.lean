module

public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.Genesis

/-!
# Proofs: runs, reachable states, and lifting a step property to whole chains

A chain runs three kinds of step on a beacon state.

- One slot: `advanceSlot`, which caches the slot and closes the epoch at its last slot.
- One upgrade: `upgradeNext`, run by `processUpgrades` when the next fork is due.
- One block: `applySignedBlock`, run by `stateTransitionAcross` once the state is at its slot.

`Step` is one such step, with its inputs, and `Run` is a sequence of steps.

A run is data: it lists the blocks and the states that the chain passes through.

`Reaches` says that a run exists from one state to another.

A slot or a block runs only when no upgrade is due, so due upgrades always run first.

From a state with no upgrade due, `processSlotsAcross` and `stateTransitionAcross` give runs.

Take a relation between two states that is reflexive and transitive.

When every step satisfies it, it holds between the two ends of every run.

That is the one lemma behind every invariant of the state transition.

A property of one state is the relation "if it holds before, it holds after".

A relation may need a property of the state before each step, such as an invariant.

It then carries that property along.

`ReachableFrom` starts the runs at any state of a set of anchors.

`Reachable` takes the genesis states that launch the chain as the anchors.

Induction over reachable states may assume, at each step, that the state before it is reachable.

So each invariant already proved is a free premise for the next one.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A relation between two forked states that every step of a chain satisfies.

It is reflexive and transitive, so it then holds between the two ends of a chain.

An upgrade is a step only when it is due, as `processUpgrades` runs it.

A block is a step for every execution engine, signed block and choice of result validation. -/
structure StepRelation (config : Config) (checks : SignatureChecks)
    (relates : ForkedBeaconState preset → ForkedBeaconState preset → Prop) : Prop where
  refl : ∀ forked, relates forked forked
  trans : ∀ {first second third}, relates first second → relates second third →
    relates first third
  advanceSlot : ∀ {fork : Fork} {state after : BeaconState preset fork},
    advanceSlot config checks state = .ok after → relates ⟨fork, state⟩ ⟨fork, after⟩
  upgradeNext : ∀ {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}},
    upgradeDue config pre = true → upgradeNext config checks pre = .ok post →
    relates pre post.val
  applySignedBlock : ∀ {fork : Fork} {engine : ExecutionEngine preset fork}
    {state after : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool},
    applySignedBlock config checks engine state signed validateResult = .ok after →
    relates ⟨fork, state⟩ ⟨fork, after⟩

namespace StepRelation

variable {relates : ForkedBeaconState preset → ForkedBeaconState preset → Prop}

/-! ## Lifting through the chain functions -/

/-- The upgrades due at a slot are steps, one after another. -/
theorem processUpgrades (steps : StepRelation config checks relates)
    {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) : relates forked after := by
  fun_induction EthLib.Consensus.processUpgrades config checks forked generalizing after with
  | case1 forked due more =>
    obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    exact steps.trans (steps.upgradeNext due stepOk) (more step rest)
  | case2 forked _ =>
    cases computed
    exact steps.refl _

/-- One slot, then the upgrades due at the slot it reaches. -/
theorem advanceSlotAcross (steps : StepRelation config checks relates)
    {forked after : ForkedBeaconState preset}
    (computed : advanceSlotAcross config checks forked = .ok after) : relates forked after := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  exact steps.trans (steps.advanceSlot advancedOk) (steps.processUpgrades upgraded)

theorem advanceSlotsAcross (steps : StepRelation config checks relates) :
    ∀ {count : Nat} {forked after : ForkedBeaconState preset},
      advanceSlotsAcross config checks count forked = .ok after → relates forked after
  | 0, forked, after, computed => by
    simp only [EthLib.Consensus.advanceSlotsAcross, pure, Except.pure,
      Except.ok.injEq] at computed
    subst computed
    exact steps.refl _
  | count + 1, forked, after, computed => by
    simp only [EthLib.Consensus.advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact steps.trans (steps.advanceSlotAcross nextOk) (steps.advanceSlotsAcross rest)

/-- Advancing to a later slot, with the upgrades on the way. -/
theorem processSlotsAcross (steps : StepRelation config checks relates)
    {forked after : ForkedBeaconState preset} {slot : Slot}
    (computed : processSlotsAcross config checks forked slot = .ok after) :
    relates forked after := by
  simp only [EthLib.Consensus.processSlotsAcross, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact steps.advanceSlotsAcross advanced

/-- A valid block, from a state that may be of an earlier fork. -/
theorem stateTransitionAcross (steps : StepRelation config checks relates) {fork : Fork}
    {engine : ExecutionEngine preset fork} {forked : ForkedBeaconState preset}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    {after : BeaconState preset fork}
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after) :
    relates forked ⟨fork, after⟩ := by
  obtain ⟨advanced, slotsOk, applied⟩ := stateTransitionAcross_ok computed
  exact steps.trans (steps.processSlotsAcross slotsOk) (steps.applySignedBlock applied)

/-! ## Lifting within one fork -/

theorem advanceSlots (steps : StepRelation config checks relates) {fork : Fork} :
    ∀ {count : Nat} {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      relates ⟨fork, state⟩ ⟨fork, after⟩
  | 0, state, after, computed => by
    simp only [EthLib.Consensus.advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact steps.refl _
  | count + 1, state, after, computed => by
    simp only [EthLib.Consensus.advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact steps.trans (steps.advanceSlot nextOk) (steps.advanceSlots rest)

theorem processSlots (steps : StepRelation config checks relates) {fork : Fork}
    {state after : BeaconState preset fork} {slot : Slot}
    (computed : processSlots config checks state slot = .ok after) :
    relates ⟨fork, state⟩ ⟨fork, after⟩ := by
  simp only [EthLib.Consensus.processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact steps.advanceSlots advanced

/-- A valid block, from a state of its own fork. -/
theorem stateTransition (steps : StepRelation config checks relates) {fork : Fork}
    {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    relates ⟨fork, state⟩ ⟨fork, after⟩ := by
  simp only [EthLib.Consensus.stateTransition, bind_ok_iff] at computed
  obtain ⟨advanced, slotsOk, applied⟩ := computed
  exact steps.trans (steps.processSlots slotsOk) (steps.applySignedBlock applied)

/-! ## Building a step relation -/

/-- A property of one state that every step keeps.

The relation is "if the property holds before, it holds after". -/
theorem ofPreserves {holds : ForkedBeaconState preset → Prop}
    (advanceSlot : ∀ {fork : Fork} {state after : BeaconState preset fork},
      holds ⟨fork, state⟩ → EthLib.Consensus.advanceSlot config checks state = .ok after →
      holds ⟨fork, after⟩)
    (upgradeNext : ∀ {pre : ForkedBeaconState preset}
      {post : {post : ForkedBeaconState preset // pre.fork < post.fork}},
      holds pre → upgradeDue config pre = true →
      EthLib.Consensus.upgradeNext config checks pre = .ok post → holds post.val)
    (applySignedBlock : ∀ {fork : Fork} {engine : ExecutionEngine preset fork}
      {state after : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
      {validateResult : Bool}, holds ⟨fork, state⟩ →
      EthLib.Consensus.applySignedBlock config checks engine state signed validateResult =
        .ok after →
      holds ⟨fork, after⟩) :
    StepRelation config checks fun forked after => holds forked → holds after where
  refl _ := id
  trans first second := second ∘ first
  advanceSlot computed before := advanceSlot before computed
  upgradeNext due computed before := upgradeNext before due computed
  applySignedBlock computed before := applySignedBlock before computed

/-- A relation that each step satisfies when a property holds before it.

Each step also keeps the property.

Along a chain from a state with the property, every state has it, so the relation holds. -/
theorem ofGuarded {holds : ForkedBeaconState preset → Prop}
    (refl : ∀ forked, relates forked forked)
    (trans : ∀ {first second third}, relates first second → relates second third →
      relates first third)
    (advanceSlot : ∀ {fork : Fork} {state after : BeaconState preset fork},
      holds ⟨fork, state⟩ → EthLib.Consensus.advanceSlot config checks state = .ok after →
      holds ⟨fork, after⟩ ∧ relates ⟨fork, state⟩ ⟨fork, after⟩)
    (upgradeNext : ∀ {pre : ForkedBeaconState preset}
      {post : {post : ForkedBeaconState preset // pre.fork < post.fork}},
      holds pre → upgradeDue config pre = true →
      EthLib.Consensus.upgradeNext config checks pre = .ok post →
      holds post.val ∧ relates pre post.val)
    (applySignedBlock : ∀ {fork : Fork} {engine : ExecutionEngine preset fork}
      {state after : BeaconState preset fork} {signed : SignedBeaconBlock preset fork}
      {validateResult : Bool}, holds ⟨fork, state⟩ →
      EthLib.Consensus.applySignedBlock config checks engine state signed validateResult =
        .ok after →
      holds ⟨fork, after⟩ ∧ relates ⟨fork, state⟩ ⟨fork, after⟩) :
    StepRelation config checks fun forked after =>
      holds forked → holds after ∧ relates forked after where
  refl forked before := ⟨before, refl forked⟩
  trans first second before :=
    -- The property reaches the middle state, which starts the second part.
    have ⟨middle, firstRelates⟩ := first before
    have ⟨last, secondRelates⟩ := second middle
    ⟨last, trans firstRelates secondRelates⟩
  advanceSlot computed before := advanceSlot before computed
  upgradeNext due computed before := upgradeNext before due computed
  applySignedBlock computed before := applySignedBlock before computed

end StepRelation

/-! ## Steps and runs -/

/-- One step of a chain: one slot, one due upgrade, or one block on a state of its own fork.

A block step keeps its execution engine, its signed block and whether it validated the result.

A slot or a block runs only at a state at which no upgrade is due, so due upgrades run first.

The chain functions run them first too, except at their own start.

So a chain function gives a run when no upgrade is due at the state it starts from. -/
inductive Step (config : Config) (checks : SignatureChecks) :
    ForkedBeaconState preset → ForkedBeaconState preset → Type where
  | slot {fork : Fork} {state after : BeaconState preset fork} :
    upgradeDue config ⟨fork, state⟩ = false →
    EthLib.Consensus.advanceSlot config checks state = .ok after →
    Step config checks ⟨fork, state⟩ ⟨fork, after⟩
  | upgrade {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}} :
    upgradeDue config pre = true → EthLib.Consensus.upgradeNext config checks pre = .ok post →
    Step config checks pre post.val
  | block {fork : Fork} (engine : ExecutionEngine preset fork)
    (signed : SignedBeaconBlock preset fork) (validateResult : Bool)
    {state after : BeaconState preset fork} :
    upgradeDue config ⟨fork, state⟩ = false →
    EthLib.Consensus.applySignedBlock config checks engine state signed validateResult =
      .ok after →
    Step config checks ⟨fork, state⟩ ⟨fork, after⟩

/-- A sequence of steps from one forked state to another, the last step at the end. -/
inductive Run (config : Config) (checks : SignatureChecks) (start : ForkedBeaconState preset) :
    ForkedBeaconState preset → Type where
  | nil : Run config checks start start
  | snoc {middle after : ForkedBeaconState preset} :
    Run config checks start middle → Step config checks middle after →
    Run config checks start after

namespace Run

variable {start : ForkedBeaconState preset}

/-- The states that a run passes through, in order, from its start to its end. -/
def states : {after : ForkedBeaconState preset} → Run config checks start after →
    List (ForkedBeaconState preset)
  | _, .nil => [start]
  | after, .snoc run _ => run.states ++ [after]

/-- The number of steps of a run. -/
def length : {after : ForkedBeaconState preset} → Run config checks start after → Nat
  | _, .nil => 0
  | _, .snoc run _ => run.length + 1

/-- A run followed by another run. -/
def append {middle : ForkedBeaconState preset} (head : Run config checks start middle) :
    {after : ForkedBeaconState preset} → Run config checks middle after →
    Run config checks start after
  | _, .nil => head
  | _, .snoc tail step => .snoc (head.append tail) step

theorem start_mem_states {after : ForkedBeaconState preset} :
    ∀ run : Run config checks start after, start ∈ run.states
  | .nil => List.mem_singleton_self _
  | .snoc run _ => List.mem_append_left _ (start_mem_states run)

theorem end_mem_states {after : ForkedBeaconState preset} :
    ∀ run : Run config checks start after, after ∈ run.states
  | .nil => List.mem_singleton_self _
  | .snoc _ _ => List.mem_append_right _ (List.mem_singleton_self _)

theorem length_states {after : ForkedBeaconState preset} :
    ∀ run : Run config checks start after, run.states.length = run.length + 1
  | .nil => rfl
  | .snoc run _ => by simp [states, length, length_states run]

end Run

namespace StepRelation

variable {relates : ForkedBeaconState preset → ForkedBeaconState preset → Prop}

/-- Each step satisfies a step relation. -/
theorem step (steps : StepRelation config checks relates) {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : relates before after := by
  cases step with
  | slot _ computed => exact steps.advanceSlot computed
  | upgrade due computed => exact steps.upgradeNext due computed
  | block _ _ _ _ computed => exact steps.applySignedBlock computed

/-- A step relation holds between the two ends of a run. -/
theorem run (steps : StepRelation config checks relates) {start : ForkedBeaconState preset} :
    ∀ {after : ForkedBeaconState preset}, Run config checks start after → relates start after
  | _, .nil => steps.refl _
  | _, .snoc run last => steps.trans (steps.run run) (steps.step last)

/-- A step relation holds from the start of a run to every state it passes through. -/
theorem run_states (steps : StepRelation config checks relates) {start : ForkedBeaconState preset} :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      ∀ state ∈ run.states, relates start state
  | _, .nil, state, member => by
    rw [List.mem_singleton.mp member]
    exact steps.refl _
  | _, .snoc run last, state, member => by
    rcases List.mem_append.mp member with earlier | now
    · exact steps.run_states run state earlier
    · rw [List.mem_singleton.mp now]
      exact steps.trans (steps.run run) (steps.step last)

end StepRelation

/-! ## Chains -/

/-- One forked state leads to another by a run of steps.

The steps are slots, due upgrades and valid blocks.

A block may run with any execution engine and with or without validating the result. -/
def Reaches (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset) :
    Prop :=
  Nonempty (Run config checks start after)

theorem Reaches.refl (start : ForkedBeaconState preset) : Reaches config checks start start :=
  ⟨.nil⟩

/-- A chain followed by another chain is a chain. -/
theorem Reaches.trans {first second third : ForkedBeaconState preset}
    (head : Reaches config checks first second) (tail : Reaches config checks second third) :
    Reaches config checks first third :=
  have ⟨head⟩ := head
  have ⟨tail⟩ := tail
  ⟨head.append tail⟩

theorem Reaches.step {start before after : ForkedBeaconState preset}
    (chain : Reaches config checks start before) (step : Step config checks before after) :
    Reaches config checks start after :=
  have ⟨run⟩ := chain
  ⟨.snoc run step⟩

/-- A property that fails at the start of a chain and holds at its end starts to hold at one step.

The chain splits there into a chain to the state before the step, the step, and a chain after it.
-/
theorem Reaches.split {holds : ForkedBeaconState preset → Prop}
    {start after : ForkedBeaconState preset} (chain : Reaches config checks start after)
    (notStart : ¬holds start) (atEnd : holds after) :
    ∃ before next, Reaches config checks start before ∧ ¬holds before ∧
      Nonempty (Step config checks before next) ∧ holds next ∧
      Reaches config checks next after := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact absurd atEnd notStart
  | @snoc middle last run step more =>
    by_cases earlier : holds middle
    · obtain ⟨before, next, head, notBefore, one, holdsNext, tail⟩ := more earlier
      exact ⟨before, next, head, notBefore, one, holdsNext, tail.step step⟩
    · exact ⟨middle, last, ⟨run⟩, earlier, ⟨step⟩, atEnd, .refl _⟩

/-! ## Chains of the chain functions -/

/-- Whether an upgrade is due depends only on the fork and the slot. -/
theorem upgradeDue_of_slot {fork : Fork} {state after : BeaconState preset fork}
    (slot : after.slot = state.slot) :
    upgradeDue config ⟨fork, after⟩ = upgradeDue config ⟨fork, state⟩ := by
  simp [upgradeDue, slot]

/-- The upgrades due at a slot are a chain, and leave no upgrade due. -/
theorem Reaches.processUpgrades {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    Reaches config checks forked after ∧ upgradeDue config after = false := by
  fun_induction EthLib.Consensus.processUpgrades config checks forked generalizing after with
  | case1 forked due more =>
    obtain ⟨step, stepOk, rest⟩ := bind_ok_iff.mp computed
    obtain ⟨chain, notDue⟩ := more step rest
    exact ⟨((Reaches.refl _).step (.upgrade due stepOk)).trans chain, notDue⟩
  | case2 forked notDue =>
    cases computed
    exact ⟨.refl _, by simpa using notDue⟩

/-- One slot, then the upgrades due at the slot it reaches, from a state with no upgrade due. -/
theorem Reaches.advanceSlotAcross {forked after : ForkedBeaconState preset}
    (notDue : upgradeDue config forked = false)
    (computed : advanceSlotAcross config checks forked = .ok after) :
    Reaches config checks forked after ∧ upgradeDue config after = false := by
  obtain ⟨fork, state⟩ := forked
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  obtain ⟨chain, afterNotDue⟩ := Reaches.processUpgrades upgraded
  exact ⟨((Reaches.refl _).step (.slot notDue advancedOk)).trans chain, afterNotDue⟩

theorem Reaches.advanceSlotsAcross :
    ∀ {count : Nat} {forked after : ForkedBeaconState preset},
      upgradeDue config forked = false →
      advanceSlotsAcross config checks count forked = .ok after →
      Reaches config checks forked after ∧ upgradeDue config after = false
  | 0, forked, after, notDue, computed => by
    simp only [EthLib.Consensus.advanceSlotsAcross, pure, Except.pure,
      Except.ok.injEq] at computed
    subst computed
    exact ⟨.refl _, notDue⟩
  | count + 1, forked, after, notDue, computed => by
    rw [EthLib.Consensus.advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    obtain ⟨head, nextNotDue⟩ := Reaches.advanceSlotAcross notDue nextOk
    obtain ⟨tail, afterNotDue⟩ := Reaches.advanceSlotsAcross nextNotDue rest
    exact ⟨head.trans tail, afterNotDue⟩

/-- Advancing to a later slot, with the upgrades on the way, from a state with no upgrade due. -/
theorem Reaches.processSlotsAcross {forked after : ForkedBeaconState preset} {slot : Slot}
    (notDue : upgradeDue config forked = false)
    (computed : processSlotsAcross config checks forked slot = .ok after) :
    Reaches config checks forked after ∧ upgradeDue config after = false := by
  simp only [EthLib.Consensus.processSlotsAcross, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact Reaches.advanceSlotsAcross notDue advanced

/-- A valid block, from a state with no upgrade due that may be of an earlier fork.

The block runs on the state at its slot, at which no upgrade is due. -/
theorem Reaches.of_stateTransitionAcross {fork : Fork} {engine : ExecutionEngine preset fork}
    {forked : ForkedBeaconState preset} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {after : BeaconState preset fork}
    (notDue : upgradeDue config forked = false)
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after) :
    ∃ advanced : BeaconState preset fork,
      Reaches config checks forked ⟨fork, advanced⟩ ∧
      upgradeDue config ⟨fork, advanced⟩ = false ∧
      applySignedBlock config checks engine advanced signed validateResult = .ok after := by
  obtain ⟨advanced, slotsOk, applied⟩ := stateTransitionAcross_ok computed
  obtain ⟨chain, advancedNotDue⟩ := Reaches.processSlotsAcross notDue slotsOk
  exact ⟨advanced, chain, advancedNotDue, applied⟩

/-- A valid block from a state with no upgrade due is a chain, after which none is due. -/
theorem Reaches.stateTransitionAcross {fork : Fork} {engine : ExecutionEngine preset fork}
    {forked : ForkedBeaconState preset} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {after : BeaconState preset fork}
    (notDue : upgradeDue config forked = false)
    (computed :
      stateTransitionAcross config checks engine forked signed validateResult = .ok after) :
    Reaches config checks forked ⟨fork, after⟩ ∧ upgradeDue config ⟨fork, after⟩ = false := by
  obtain ⟨advanced, chain, advancedNotDue, applied⟩ :=
    Reaches.of_stateTransitionAcross notDue computed
  -- The block keeps the slot, so no upgrade is due after it either.
  have slot := (frame_processBlock (applySignedBlock_ok applied).2.1).slot
  exact ⟨chain.step (.block _ _ _ advancedNotDue applied),
    (upgradeDue_of_slot slot).trans advancedNotDue⟩

/-- A chain followed by empty slots, with the upgrades on the way, is a chain.

No upgrade may be due where the slots start. -/
theorem Reaches.slots {start forked after : ForkedBeaconState preset} {slot : Slot}
    (chain : Reaches config checks start forked) (notDue : upgradeDue config forked = false)
    (computed : EthLib.Consensus.processSlotsAcross config checks forked slot = .ok after) :
    Reaches config checks start after :=
  chain.trans (Reaches.processSlotsAcross notDue computed).1

/-- A chain followed by a valid block, from a state that may be of an earlier fork, is a chain.

No upgrade may be due where the block's slots start. -/
theorem Reaches.block {start forked : ForkedBeaconState preset} {fork : Fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {after : BeaconState preset fork}
    (chain : Reaches config checks start forked) (notDue : upgradeDue config forked = false)
    (computed : EthLib.Consensus.stateTransitionAcross config checks engine forked signed
      validateResult = .ok after) :
    Reaches config checks start ⟨fork, after⟩ :=
  chain.trans (Reaches.stateTransitionAcross notDue computed).1

/-- The upgrades due at a slot leave no upgrade due. -/
theorem processUpgrades_not_due {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    upgradeDue config after = false := by
  fun_induction processUpgrades config checks forked generalizing after with
  | case1 forked _ more =>
    obtain ⟨step, _, rest⟩ := bind_ok_iff.mp computed
    exact more step rest
  | case2 forked notDue =>
    cases computed
    simpa using notDue

/-- After at least one slot with the upgrades on the way, no upgrade is due. -/
theorem advanceSlotsAcross_not_due :
    ∀ {count : Nat} {forked after : ForkedBeaconState preset},
      advanceSlotsAcross config checks (count + 1) forked = .ok after →
      upgradeDue config after = false
  | 0, forked, after, computed => by
    simp only [advanceSlotsAcross, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨next, nextOk, rfl⟩ := computed
    obtain ⟨_, _, upgraded⟩ := bind_ok_iff.mp nextOk
    exact processUpgrades_not_due upgraded
  | count + 1, forked, after, computed => by
    rw [advanceSlotsAcross, bind_ok_iff] at computed
    obtain ⟨_, _, rest⟩ := computed
    exact advanceSlotsAcross_not_due rest

/-- A step relation holds between the two ends of every chain. -/
theorem StepRelation.reaches {relates : ForkedBeaconState preset → ForkedBeaconState preset → Prop}
    (steps : StepRelation config checks relates) {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) : relates start after :=
  have ⟨run⟩ := chain
  steps.run run

/-! ## Reachable states -/

/-- A state that a chain reaches from one of a set of anchor states.

The anchors may be genesis states, the first states of a later fork, or checkpoint states. -/
def ReachableFrom (config : Config) (checks : SignatureChecks)
    (anchor : ForkedBeaconState preset → Prop) (forked : ForkedBeaconState preset) : Prop :=
  ∃ start, anchor start ∧ Reaches config checks start forked

namespace ReachableFrom

variable {anchor : ForkedBeaconState preset → Prop}

theorem of_anchor {forked : ForkedBeaconState preset} (anchored : anchor forked) :
    ReachableFrom config checks anchor forked :=
  ⟨forked, anchored, .refl _⟩

theorem step {before after : ForkedBeaconState preset}
    (reachable : ReachableFrom config checks anchor before)
    (step : Step config checks before after) : ReachableFrom config checks anchor after :=
  have ⟨start, anchored, chain⟩ := reachable
  ⟨start, anchored, chain.step step⟩

theorem reaches {before after : ForkedBeaconState preset}
    (reachable : ReachableFrom config checks anchor before)
    (chain : Reaches config checks before after) : ReachableFrom config checks anchor after :=
  have ⟨start, anchored, head⟩ := reachable
  ⟨start, anchored, head.trans chain⟩

/-- Induction over reachable states.

The step may assume that the state before it is reachable.

So every invariant already proved holds there. -/
theorem induction {holds : ForkedBeaconState preset → Prop}
    (anchors : ∀ forked, anchor forked → holds forked)
    (step : ∀ {before after : ForkedBeaconState preset},
      ReachableFrom config checks anchor before → holds before →
      Step config checks before after → holds after)
    {forked : ForkedBeaconState preset} (reachable : ReachableFrom config checks anchor forked) :
    holds forked := by
  obtain ⟨start, anchored, ⟨run⟩⟩ := reachable
  induction run with
  | nil => exact anchors start anchored
  | snoc run last more => exact step ⟨start, anchored, ⟨run⟩⟩ more last

end ReachableFrom

/-- A genesis state that launches the chain.

It is the candidate state of a proof-of-work block.

Its genesis time is late enough, and enough validators are active. -/
def Genesis (config : Config) (checks : SignatureChecks) (forked : ForkedBeaconState preset) :
    Prop :=
  (∃ eth1BlockHash eth1Timestamp deposits,
    initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok forked.state) ∧
    isValidGenesisState config forked.state = true

/-- A state that a chain from a genesis state reaches. -/
def Reachable (config : Config) (checks : SignatureChecks) (forked : ForkedBeaconState preset) :
    Prop :=
  ReachableFrom config checks (Genesis config checks) forked

/-- Induction over the states that a chain from genesis reaches.

The step may assume that the state before it is reachable. -/
theorem Reachable.induction {holds : ForkedBeaconState preset → Prop}
    (genesis : ∀ forked, Genesis config checks forked → holds forked)
    (step : ∀ {before after : ForkedBeaconState preset},
      Reachable config checks before → holds before →
      Step config checks before after → holds after)
    {forked : ForkedBeaconState preset} (reachable : Reachable config checks forked) :
    holds forked :=
  ReachableFrom.induction genesis step reachable

/-- A property that holds at genesis and that every step keeps holds in every reachable state. -/
theorem Reachable.of_preserves {holds : ForkedBeaconState preset → Prop}
    (steps : StepRelation config checks fun forked after => holds forked → holds after)
    (genesis : ∀ forked, Genesis config checks forked → holds forked)
    {forked : ForkedBeaconState preset} (reachable : Reachable config checks forked) :
    holds forked :=
  have ⟨start, launched, chain⟩ := reachable
  steps.reaches chain (genesis start launched)

/-- A proof-of-work block with no deposits gives a genesis state that launches the chain.

The configuration must ask for no genesis validators.

The time of the block must be late enough.

The genesis state has no validators.

With deposits, the Merkle proof and the signature of each deposit must check.

This theorem does not attempt that.

The preset needs the nonzero sizes that give the empty block body a root. -/
theorem genesis_of_no_deposits [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    (checks : SignatureChecks) (eth1BlockHash : Hash32) (eth1Timestamp : UInt64)
    (noValidators : config.MIN_GENESIS_ACTIVE_VALIDATOR_COUNT = 0)
    (fits : eth1Timestamp.toNat + config.GENESIS_DELAY.toNat < 2 ^ 64)
    (late : config.MIN_GENESIS_TIME ≤ eth1Timestamp + config.GENESIS_DELAY) :
    ∃ state : BeaconState preset .phase0, Genesis config checks ⟨.phase0, state⟩ := by
  obtain ⟨bodyRoot, bodyOk⟩ := Serialization.Ssz.SszType.hashTreeRoot_total
    (emptyBody (preset := preset) (fork := .phase0) (by decide))
  let empty := emptyGenesisState (preset := preset) config (by decide : Fork.phase0 < .altair)
    (eth1Timestamp + config.GENESIS_DELAY) eth1BlockHash 0 bodyRoot
  obtain ⟨validatorsRoot, validatorsOk⟩ :=
    Serialization.Ssz.SszType.hashTreeRoot_total empty.validators
  have added : Uint64.addChecked eth1Timestamp config.GENESIS_DELAY =
      .ok (eth1Timestamp + config.GENESIS_DELAY) := by
    simp [Uint64.addChecked, fits]
  refine ⟨{ empty with genesisValidatorsRoot := validatorsRoot },
    ⟨eth1BlockHash, eth1Timestamp, #[], ?_⟩, ?_⟩
  · have noValidator : (List.range empty.validators.data.size).foldlM activateAtGenesis empty =
        .ok empty := rfl
    simp only [initializeBeaconStateFromEth1, show ¬Fork.altair ≤ Fork.phase0 by decide,
      ↓reduceDIte, liftAccessor, liftArith, liftSsz, added, bodyOk, Except.mapError, bind,
      Except.bind, ensure, Array.size_empty, Nat.toUInt64_eq, pure, Except.pure]
    simp only [show (0 : Nat) < 2 ^ 64 by decide, ↓reduceIte, List.zipIdx_nil,
      List.foldlM_nil, pure, Except.pure]
    rw [show UInt64.ofNat 0 = 0 from rfl]
    erw [noValidator]
    simp only [validatorsOk, empty]
  · simp [isValidGenesisState, empty, emptyGenesisState, noValidators, late]

/-- A genesis state exists for some configuration.

That configuration is mainnet with no minimum count of genesis validators. -/
theorem genesis_exists [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat]
    [NeZero preset.SYNC_COMMITTEE_SIZE.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
    [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]
    (checks : SignatureChecks) :
    ∃ (config : Config) (forked : ForkedBeaconState preset), Genesis config checks forked :=
  have ⟨state, launched⟩ := genesis_of_no_deposits
    (config := { Config.mainnet with MIN_GENESIS_ACTIVE_VALIDATOR_COUNT := 0 }) checks
    (Vector.replicate 32 0) 1606219200 rfl (by decide) (by decide)
  ⟨_, _, launched⟩

/-! ## The invariant of the state transition -/

/-- Each step keeps the invariant of the state transition, and never lowers the finalized epoch.

So both hold along every chain from a state that satisfies the invariant. -/
theorem stepRelation_invariant :
    StepRelation config checks fun (forked after : ForkedBeaconState preset) =>
      Invariant forked.state → Invariant after.state ∧
        forked.state.finalizedCheckpoint.epoch ≤ after.state.finalizedCheckpoint.epoch :=
  StepRelation.ofGuarded (holds := fun forked => Invariant forked.state)
    (relates := fun forked after =>
      forked.state.finalizedCheckpoint.epoch ≤ after.state.finalizedCheckpoint.epoch)
    (fun _ => UInt64.le_refl _) UInt64.le_trans
    (fun holds computed => advanceSlot_invariant holds computed)
    (fun holds _ computed =>
      have ⟨after, same⟩ := upgradeNext_invariant holds computed
      ⟨after, same ▸ UInt64.le_refl _⟩)
    (fun holds computed =>
      -- The block is a frame, which keeps the checkpoints.
      have frame := frame_processBlock (applySignedBlock_ok computed).2.1
      ⟨frame.invariant holds, frame.finalized ▸ UInt64.le_refl _⟩)

/-- Every state reachable from anchors that satisfy the invariant satisfies it. -/
theorem ReachableFrom.invariant {anchor : ForkedBeaconState preset → Prop}
    (anchors : ∀ forked, anchor forked → Invariant forked.state)
    {forked : ForkedBeaconState preset} (reachable : ReachableFrom config checks anchor forked) :
    Invariant forked.state :=
  have ⟨start, anchored, chain⟩ := reachable
  (stepRelation_invariant.reaches chain (anchors start anchored)).1

/-- Every reachable state satisfies the invariant of the state transition. -/
theorem Reachable.invariant {forked : ForkedBeaconState preset}
    (reachable : Reachable config checks forked) : Invariant forked.state :=
  ReachableFrom.invariant (fun _ ⟨⟨_, _, _, initialized⟩, _⟩ =>
    (initializeBeaconStateFromEth1_invariant initialized).2) reachable

/-- Along a chain from a state that satisfies the invariant, the finalized epoch never decreases.
-/
theorem Reaches.finalized_le {start after : ForkedBeaconState preset}
    (holds : Invariant start.state) (chain : Reaches config checks start after) :
    start.state.finalizedCheckpoint.epoch ≤ after.state.finalizedCheckpoint.epoch :=
  (stepRelation_invariant.reaches chain holds).2

end EthLib.Consensus
