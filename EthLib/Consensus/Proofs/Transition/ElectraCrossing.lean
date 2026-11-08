module

public import EthLib.Consensus.Proofs.Transition.ExitLoss
public import EthLib.Consensus.Proofs.Transition.ChurnWindows
public import EthLib.Consensus.Proofs.Transition.DepositChurn

/-!
# Proofs: the stake that leaves the active set across the upgrade to Electra

Before Electra, exits are limited by count.

From Electra, they are limited by balance.

[EIP-7251] specifies both the new churn and the upgrade between the two.

A run that starts before Electra and ends from Electra on has exactly one upgrade to Electra.

It splits there into a run before Electra, the upgrade, and a run from Electra on.

The upgrade keeps the slot, and the activation and exit epochs of every validator.

It also keeps the effective balance of every validator that has an activation epoch.

So the stake that leaves over the whole run is that of four groups.

```text
  E_x            E_p = E_q           L            E_s
   |---- count ----|                                      leave before the upgrade
                   |-- queued before Electra --|          leave after it, by count
                                               |- churn -| exits from Electra, by balance
```

`L` is the latest exit epoch that the upgrade finds, or its activation exit epoch.

The upgrade opens the Electra queue of exits at `L + 1`, with a full churn.

So the exits from Electra never take an epoch of the queue before Electra.

A fourth amount is what each exit from Electra lost before its churn was charged.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## What the upgrade keeps of each validator -/

/-- A later state keeps the slot, the size of the registry and part of each validator.

Each validator keeps its activation and exit epochs.

A validator with an activation epoch also keeps its effective balance. -/
structure UpgradeKeeps {fork fork' : Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') : Prop where
  slot : after.slot = state.slot
  size : after.validators.data.size = state.validators.data.size
  validator : ∀ (position : Nat) (validator : Validator),
    state.validators.data[position]? = some validator → ∃ later,
      after.validators.data[position]? = some later ∧
        later.activationEpoch = validator.activationEpoch ∧
        later.exitEpoch = validator.exitEpoch ∧
        (validator.activationEpoch ≠ FAR_FUTURE_EPOCH →
          later.effectiveBalance = validator.effectiveBalance)

namespace UpgradeKeeps

variable {fork fork' fork'' : Fork} {state : BeaconState preset fork}
  {after : BeaconState preset fork'} {third : BeaconState preset fork''}

theorem of_data (slot : after.slot = state.slot)
    (data : after.validators.data = state.validators.data) : UpgradeKeeps state after :=
  ⟨slot, by rw [data], fun _ validator found =>
    ⟨validator, by rw [data]; exact found, rfl, rfl, fun _ => rfl⟩⟩

theorem trans (one : UpgradeKeeps state after) (two : UpgradeKeeps after third) :
    UpgradeKeeps state third :=
  ⟨two.slot.trans one.slot, two.size.trans one.size, fun position validator found => by
    obtain ⟨middle, middleFound, activation, exit, effective⟩ :=
      one.validator position validator found
    obtain ⟨later, laterFound, activation', exit', effective'⟩ :=
      two.validator position middle middleFound
    refine ⟨later, laterFound, activation'.trans activation, exit'.trans exit, fun set => ?_⟩
    exact (effective' (activation ▸ set)).trans (effective set)⟩

/-- The validator at a position is active at an epoch in both states, or in neither. -/
theorem activeAt_eq (keeps : UpgradeKeeps state after) (epoch : Epoch) (position : Nat) :
    activeAt after epoch position = activeAt state epoch position := by
  cases found : state.validators.data[position]? with
  | none =>
    have : after.validators.data[position]? = none := by
      rw [Array.getElem?_eq_none_iff] at found ⊢
      rw [keeps.size]
      exact found
    simp [activeAt, found, this]
  | some validator =>
    obtain ⟨later, laterFound, activation, exit, -⟩ := keeps.validator position validator found
    simp [activeAt, found, laterFound, isActiveValidator, activation, exit]

end UpgradeKeeps

/-- A validator with no activation epoch is active at no epoch. -/
theorem isActiveValidator_of_far {validator : Validator}
    (far : validator.activationEpoch = FAR_FUTURE_EPOCH) (epoch : Epoch) :
    isActiveValidator validator epoch = false := by
  simp only [isActiveValidator, far, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  by_cases top : FAR_FUTURE_EPOCH ≤ epoch
  · right
    have := validator.exitEpoch.toNat_lt
    have := UInt64.le_iff_toNat_le.mp top
    have := epoch.toNat_lt
    rw [UInt64.not_lt, UInt64.le_iff_toNat_le]
    simp only [FAR_FUTURE_EPOCH] at *
    simp at *
    omega
  · left
    exact top

/-- Queueing a validator with no activation epoch as a deposit keeps what `UpgradeKeeps` names.
-/
theorem upgradeKeeps_queuePreActivation {fork : Fork} {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (far : ∀ validator, state.validators.data[index.toNat]? = some validator →
      validator.activationEpoch = FAR_FUTURE_EPOCH)
    (computed : queuePreActivation state electra index = .ok after) : UpgradeKeeps state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, got, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  have found : state.validators.data[index.toNat]? = some validator := by
    unfold getValidator at got
    split at got <;> simp_all
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  obtain ⟨inside, rfl⟩ := setValidator_ok set₂
  refine ⟨rfl, by simp [BeaconState.putValidator, BeaconState.putBalance],
    fun position other otherFound => ?_⟩
  simp only [BeaconState.putValidator, BeaconState.putBalance, RootedForkList.data_set,
    Array.getElem?_set]
  split
  · rename_i same
    subst same
    rw [found] at otherFound
    cases otherFound
    exact ⟨_, rfl, rfl, rfl, fun set => absurd (far validator found) set⟩
  · exact ⟨other, otherFound, rfl, rfl, fun _ => rfl⟩

/-- Queueing the excess balance of a validator keeps the whole registry. -/
theorem upgradeKeeps_queueCompoundingExcess {fork : Fork} {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    UpgradeKeeps state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · have queued := liftAccessor_ok.mp computed
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨_, _, queued⟩ := queued
      split at queued
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
        obtain ⟨_, rfl⟩ := setBalance_ok set
        exact .of_data rfl rfl
      · cases queued
        exact .of_data rfl rfl
    · cases computed
      exact .of_data rfl rfl
  · cases computed
    exact .of_data rfl rfl

/-! ## The total active balance across the upgrade -/

/-- A mark set by marking some indices is at one of them, or was set before. -/
theorem foldl_setIfInBounds_true (indices : List ValidatorIndex) :
    ∀ (marks : Array Bool) (position : Nat),
      (indices.foldl (fun marked index => marked.setIfInBounds index.toNat true) marks)[position]? =
          some true →
        marks[position]? = some true ∨ ∃ index ∈ indices, index.toNat = position := by
  induction indices with
  | nil => exact fun _ _ marked => .inl marked
  | cons index rest more =>
    intro marks position marked
    rcases more _ position marked with earlier | later
    · simp only [Array.getElem?_setIfInBounds] at earlier
      split at earlier
      · exact .inr ⟨index, List.mem_cons_self, by omega⟩
      · exact .inl earlier
    · obtain ⟨other, member, same⟩ := later
      exact .inr ⟨other, List.mem_cons_of_mem _ member, same⟩

/-- Each mark of `markIndices` is at one of the indices. -/
theorem markIndices_true {size position : Nat} {indices : List ValidatorIndex}
    (marked : (markIndices size indices)[position]? = some true) :
    ∃ index ∈ indices, index.toNat = position := by
  rcases foldl_setIfInBounds_true indices _ position marked with start | found
  · simp [Array.getElem?_replicate] at start
  · exact found

/-- A sum of marked effective balances reads only the balances at the marks. -/
theorem foldl_zip_marked {init : Nat} :
    ∀ (first second : List Validator) (marks : List Bool), first.length = second.length →
      (∀ (position : Nat) (inFirst : position < first.length)
          (inSecond : position < second.length), marks[position]? = some true →
        first[position].effectiveBalance = second[position].effectiveBalance) →
      (first.zip marks).foldl (fun sum (validator, mark) =>
          if mark then sum + validator.effectiveBalance.toNat else sum) init =
        (second.zip marks).foldl (fun sum (validator, mark) =>
          if mark then sum + validator.effectiveBalance.toNat else sum) init := by
  intro first
  induction first generalizing init with
  | nil =>
    intro second marks lengths _
    cases second with
    | nil => rfl
    | cons _ _ => simp at lengths
  | cons head rest more =>
    intro second marks lengths same
    cases second with
    | nil => simp at lengths
    | cons head' rest' =>
      cases marks with
      | nil => rfl
      | cons mark marks =>
        simp only [List.zip_cons_cons, List.foldl_cons]
        have heads : mark = true → head.effectiveBalance = head'.effectiveBalance :=
          fun set => same 0 (by simp) (by simp) (by simp [set])
        have tails := @more (if mark then init + head.effectiveBalance.toNat else init) rest'
          marks (by simpa using lengths) fun position inFirst inSecond marked =>
            same (position + 1) (by simp; omega) (by simp; omega) (by simpa using marked)
        rw [tails]
        cases mark
        · rfl
        · rw [heads rfl]

/-- The positions of the active validators, read from their flags. -/
theorem getActiveValidatorIndices_flags {fork : Fork} (state : BeaconState preset fork)
    (epoch : Epoch) :
    getActiveValidatorIndices state epoch =
      (activeFlags state epoch).zipIdx.filterMap fun (flag, index) =>
        if flag then some index.toUInt64 else none := by
  simp only [getActiveValidatorIndices, activeFlags, List.zipIdx_map, List.filterMap_map]
  rfl

/-- What `UpgradeKeeps` keeps keeps the total active balance.

The registry must be below `2^64`, so that each position is its own index. -/
theorem UpgradeKeeps.getTotalActiveBalance_eq {fork fork' : Fork}
    {state : BeaconState preset fork} {after : BeaconState preset fork'}
    (keeps : UpgradeKeeps state after) (small : state.validators.data.size < 2 ^ 64) :
    getTotalActiveBalance after = getTotalActiveBalance state := by
  have epoch : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, keeps.slot]
  have flags : activeFlags after (getCurrentEpoch state) =
      activeFlags state (getCurrentEpoch state) := by
    apply List.ext_getElem (by simp [activeFlags, keeps.size])
    intro position first second
    simp only [activeFlags, List.length_map, Array.length_toList] at first second
    have := keeps.activeAt_eq (getCurrentEpoch state) position
    simp only [activeAt, Array.getElem?_eq_getElem first, Array.getElem?_eq_getElem second,
      Option.any_some] at this
    simpa [activeFlags] using this
  have indices : getActiveValidatorIndices after (getCurrentEpoch state) =
      getActiveValidatorIndices state (getCurrentEpoch state) := by
    rw [getActiveValidatorIndices_flags, getActiveValidatorIndices_flags, flags]
  -- Each marked validator is active, so it has an activation epoch and keeps its balance.
  have sums : sumMarked after.validators.data (markIndices state.validators.data.size
        (getActiveValidatorIndices state (getCurrentEpoch state))) =
      sumMarked state.validators.data (markIndices state.validators.data.size
        (getActiveValidatorIndices state (getCurrentEpoch state))) := by
    simp only [sumMarked, ← Array.foldl_toList, Array.toList_zip]
    refine foldl_zip_marked _ _ _ (by simp [keeps.size]) fun position inFirst inSecond marked => ?_
    simp only [Array.length_toList] at inFirst inSecond
    obtain ⟨index, member, same⟩ := markIndices_true (by simpa using marked)
    simp only [getActiveValidatorIndices, List.mem_filterMap, Option.ite_none_right_eq_some,
      Option.some.injEq, Prod.exists, List.mem_zipIdx_iff_getElem?] at member
    obtain ⟨validator, at', read, active, rfl⟩ := member
    simp only [Array.getElem?_toList] at read
    have below : at' < 2 ^ 64 :=
      Nat.lt_trans (Array.getElem?_eq_some_iff.mp read).1 small
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' below] at same
    subst same
    obtain ⟨later, laterFound, -, -, effective⟩ := keeps.validator _ validator read
    have set : validator.activationEpoch ≠ FAR_FUTURE_EPOCH := fun far =>
      absurd active (by rw [isActiveValidator_of_far far]; decide)
    rw [Array.getElem?_eq_getElem inSecond] at read
    rw [Array.getElem?_eq_getElem inFirst] at laterFound
    simp only [Array.getElem_toList, Option.some.injEq] at read laterFound ⊢
    rw [laterFound, read]
    exact effective set
  simp only [getTotalActiveBalance, getTotalBalance, epoch, indices, keeps.size, sums]

/-! ## The upgrade to Electra -/

/-- Queueing validators with no activation epoch, one after another, keeps `UpgradeKeeps`.

They had no activation epoch at the start of the queueing. -/
theorem foldlM_queuePreActivation_keeps {fork : Fork} {electra : .pectra ≤ fork}
    {start : BeaconState preset fork} (small : start.validators.data.size < 2 ^ 64) :
    ∀ {indices : List ValidatorIndex} {current after : BeaconState preset fork},
      (members : ∀ index ∈ indices, index ∈ preActivationIndices start) →
      (keeps : UpgradeKeeps start current) →
      (computed : indices.foldlM (fun state index => queuePreActivation state electra index)
        current = .ok after) →
      UpgradeKeeps start after
  | [], current, after, _, keeps, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ keeps
  | index :: rest, current, after, members, keeps, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    -- The validator had no activation epoch at the start, and the queueing keeps every one.
    obtain ⟨original, originalFound, far⟩ :=
      mem_preActivationIndices small (members index List.mem_cons_self)
    obtain ⟨now, nowFound, activation, -, -⟩ := keeps.validator _ original originalFound
    have step := upgradeKeeps_queuePreActivation (fun validator found => by
      rw [nowFound] at found
      cases found
      exact activation.trans far) first
    exact foldlM_queuePreActivation_keeps small
      (fun other member => members other (List.mem_cons_of_mem _ member)) (keeps.trans step) tail

theorem le_max_left' (first second : UInt64) : first ≤ max first second := by
  rw [UInt64.max_def]
  split
  · assumption
  · exact UInt64.le_refl _

theorem le_max_right' (first second : UInt64) : second ≤ max first second := by
  rw [UInt64.max_def]
  split
  · exact UInt64.le_refl _
  · exact UInt64.le_of_lt (UInt64.not_le.mp ‹_›)

/-- The latest exit epoch of a registry, from a first epoch, is at least each exit epoch set. -/
theorem le_latestExit (validators : List Validator) :
    ∀ (init : Epoch), init ≤ validators.foldl (init := init) (fun latest validator =>
        if validator.exitEpoch = FAR_FUTURE_EPOCH then latest
        else max latest validator.exitEpoch) ∧
      ∀ validator ∈ validators, validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
        validator.exitEpoch ≤ validators.foldl (init := init) (fun latest validator =>
          if validator.exitEpoch = FAR_FUTURE_EPOCH then latest
          else max latest validator.exitEpoch) := by
  induction validators with
  | nil => exact fun init => ⟨UInt64.le_refl _, fun _ member => absurd member (by simp)⟩
  | cons head rest more =>
    intro init
    simp only [List.foldl_cons]
    have next : init ≤ (if head.exitEpoch = FAR_FUTURE_EPOCH then init
        else max init head.exitEpoch) := by
      split
      · exact UInt64.le_refl _
      · exact le_max_left' _ _
    obtain ⟨atLeast, each⟩ := more (if head.exitEpoch = FAR_FUTURE_EPOCH then init
      else max init head.exitEpoch)
    refine ⟨UInt64.le_trans next atLeast, fun validator member set => ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · refine UInt64.le_trans ?_ atLeast
      simp only [set, ↓reduceIte]
      exact le_max_right' _ _
    · exact each validator member set

/-- The upgrade to Electra, as the churn of exits and of consolidations sees it.

- It keeps the slot, and what `UpgradeKeeps` names of each validator.
- Each exit epoch set before it is before the earliest exit epoch it opens.
- It starts both churns full: each churn left is the churn of the upgraded state.

[EIP-7251] specifies these steps.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1 -/
theorem upgradeToElectra_crossing {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok post) :
    UpgradeKeeps pre post ∧
      (∀ (position : Nat) (validator : Validator), pre.validators.data[position]? = some validator →
        validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
          validator.exitEpoch.toNat < (post.earliestExitEpoch (by decide)).toNat) ∧
      exitChurnLimit config post = .ok (post.exitBalanceToConsume (by decide)) ∧
      getConsolidationChurnLimit config post =
        .ok (post.consolidationBalanceToConsume (by decide)) := by
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨activationExit, -, earliest, earliestOk, exitChurn, exitChurnOk, consolidationChurn,
    consolidationChurnOk, middle, queued, compounded⟩ := computed
  have small : pre.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (pre.validators.bound (by decide)) (UInt64.toNat_lt _)
  -- The registry of the carried state is that of the Deneb state.
  have folded := foldlM_queuePreActivation_keeps (computed := queued) (by exact small)
    (fun _ member => member) (UpgradeKeeps.of_data rfl rfl)
  have queuedKeeps : UpgradeKeeps pre middle :=
    UpgradeKeeps.trans (by exact .of_data rfl rfl) folded
  have compoundedKeeps := foldlM_ok_invariant (UpgradeKeeps _)
    (fun _ _ _ before step => before.trans (upgradeKeeps_queueCompoundingExcess step))
    queuedKeeps compounded
  have queuedQueues := foldlM_ok_invariant (fun current => churnQueues current =
      churnQueues ({ carryFields config .pectra pre (by decide) (by decide) with
        earliestExitEpoch := fun _ => earliest
        earliestConsolidationEpoch := fun _ => activationExit
        exitBalanceToConsume := fun _ => exitChurn
        consolidationBalanceToConsume := fun _ => consolidationChurn } :
          BeaconState preset .pectra))
    (fun _ _ _ before step => (churnQueues_queuePreActivation step).trans before) rfl queued
  have queues := foldlM_ok_invariant (fun current => churnQueues current =
      churnQueues ({ carryFields config .pectra pre (by decide) (by decide) with
        earliestExitEpoch := fun _ => earliest
        earliestConsolidationEpoch := fun _ => activationExit
        exitBalanceToConsume := fun _ => exitChurn
        consolidationBalanceToConsume := fun _ => consolidationChurn } :
          BeaconState preset .pectra))
    (fun _ _ _ before step => (churnQueues_queueCompoundingExcess step).trans before) queuedQueues
    compounded
  have exitEpoch := congrArg (fun queues => (queues (by decide)).1) queues
  have exitLeft := congrArg (fun queues => (queues (by decide)).2.1) queues
  have consolidationLeft := congrArg (fun queues => (queues (by decide)).2.2.2) queues
  simp only [churnQueues] at exitEpoch exitLeft consolidationLeft
  -- The total active balance, and so each churn, is that of the Deneb state.
  have total := compoundedKeeps.getTotalActiveBalance_eq small
  refine ⟨compoundedKeeps, fun position validator found set => ?_, ?_, ?_⟩
  · rw [exitEpoch]
    obtain ⟨-, each⟩ := le_latestExit pre.validators.data.toList activationExit
    have le := UInt64.le_iff_toNat_le.mp (each validator
      (by simpa using Array.mem_of_getElem? found) set)
    have := (addChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp earliestOk))).2
    rw [← Array.foldl_toList] at this
    simp only [UInt64.toNat_one] at this
    omega
  · rw [exitLeft]
    simp only [exitChurnLimit, show ¬ (Fork.glamsterdam ≤ Fork.pectra) by decide, ↓reduceIte]
    rw [← liftAccessor_ok.mp exitChurnOk]
    simp only [getActivationExitChurnLimit, getBalanceChurnLimit, total]
    rfl
  · rw [consolidationLeft, ← liftAccessor_ok.mp consolidationChurnOk]
    simp only [getConsolidationChurnLimit, show ¬ (Fork.glamsterdam ≤ Fork.pectra) by decide,
      ↓reduceIte, getActivationExitChurnLimit, getBalanceChurnLimit, total]
    rfl

/-! ## The step that upgrades to Electra -/

/-- A step from a state before Electra to one from Electra on is the upgrade to Electra. -/
theorem Step.toElectra {before after : ForkedBeaconState preset}
    (step : Step config checks before after) (early : before.fork < .pectra)
    (late : .pectra ≤ after.fork) :
    ∃ (pre : BeaconState preset .dencun) (post : BeaconState preset .pectra),
      before = ⟨.dencun, pre⟩ ∧ after = ⟨.pectra, post⟩ ∧
        upgradeToElectra config pre = .ok post := by
  cases step with
  | slot _ _ => exact absurd (Nat.lt_of_lt_of_le early late) (Nat.lt_irrefl _)
  | block _ _ _ _ _ => exact absurd (Nat.lt_of_lt_of_le early late) (Nat.lt_irrefl _)
  | upgrade _ computed =>
    obtain ⟨fork, state⟩ := before
    cases fork <;>
      simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
        throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
    all_goals first
      | (obtain ⟨_, _, rfl⟩ := computed; simp only at late; exact absurd late (by decide))
      | (simp only at early; exact absurd early (by decide))
      | (obtain ⟨post, upgraded, rfl⟩ := computed; exact ⟨state, post, rfl, rfl, upgraded⟩)

/-- A run from before Electra to Electra or later splits at its one upgrade to Electra.

It is a run before Electra, the upgrade step, and a run from Electra on. -/
theorem Run.splitAtElectra {start : ForkedBeaconState preset} (early : start.fork < .pectra) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      .pectra ≤ after.fork →
      ∃ (before next : ForkedBeaconState preset) (head : Run config checks start before)
        (step : Step config checks before next) (tail : Run config checks next after),
        before.fork < .pectra ∧ .pectra ≤ next.fork ∧ (head.snoc step).append tail = run
  | _, .nil, late => absurd (Nat.lt_of_lt_of_le early late) (Nat.lt_irrefl _)
  | _, .snoc (middle := middle) run step, late => by
    by_cases middleLate : .pectra ≤ middle.fork
    · obtain ⟨before, next, head, upgrade, tail, beforeEarly, nextLate, same⟩ :=
        Run.splitAtElectra early run middleLate
      exact ⟨before, next, head, upgrade, tail.snoc step, beforeEarly, nextLate, by
        rw [← same]
        rfl⟩
    · exact ⟨middle, _, run, step, .nil, Nat.lt_of_not_le middleLate, late, rfl⟩

/-! ## The churn charged from the earliest exit epoch -/

/-- A queue whose churn left is within its cap has spent every epoch before both bounds.

They are the first epoch a new request may take, and the earliest epoch of the queue. -/
theorem max_le_queuePotential {cap first : Nat} {earliestEpoch : Epoch} {churnLeft : Gwei}
    (leftLe : churnLeft.toNat ≤ cap) :
    max first earliestEpoch.toNat * cap ≤ queuePotential cap first earliestEpoch churnLeft := by
  unfold queuePotential
  split
  · rw [Nat.max_eq_left (by omega)]
  · rw [Nat.max_eq_right (by omega)]
    omega

/-- The churn that the exits started over a run from Electra spend, up to an epoch.

It is the balance each such exit was charged.

The queue of exits spends at most one cap per epoch from its earliest epoch at the start.

That is, unless the first epoch a new exit may take is later.

The queue of consolidations spends at most one cap per epoch from that first epoch.

The caps bound the churns of every state of the run, and the churn left at its start. -/
theorem Run.chargedStake_le {capExit capConsolidation largest : Nat}
    {start after : ForkedBeaconState preset} (electra : .pectra ≤ start.fork)
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    (churns : ∀ forked ∈ run.states, ChurnsBounded config capExit capConsolidation largest forked)
    (lefts : LeftBounded capExit capConsolidation start) (upTo : Nat) :
    ∑ position ∈ exitsBetween start.state after.state 0 upTo, run.chargedBalance position ≤
      (upTo + 1 - max (firstExitEpoch preset start.state)
          (start.state.earliestExitEpoch electra).toNat) * capExit +
        (upTo + 1 - firstExitEpoch preset start.state) * capConsolidation := by
  obtain ⟨forkLe, _, _, rises⟩ := Run.exitCharge_charged electra run small churns lefts
  have rise := rises 0 upTo
  have electra' : .pectra ≤ after.fork := Nat.le_trans electra forkLe
  simp only [forkedPotential, electra, electra', ↓reduceDIte, statePotential,
    windowPotential_zero] at rise
  -- At the start each queue has spent every epoch before its own first epoch.
  have exitStart := max_le_queuePotential (first := firstExitEpoch preset start.state)
    (earliestEpoch := start.state.earliestExitEpoch electra) (lefts electra).1
  have consolidationStart := le_queuePotential (first := firstExitEpoch preset start.state)
    (earliestEpoch := start.state.earliestConsolidationEpoch electra) (lefts electra).2
  -- From there to the end of the range, each queue spends at most one cap per epoch.
  have exitRange : (upTo + 1) * capExit -
      min (max (firstExitEpoch preset start.state)
        (start.state.earliestExitEpoch electra).toNat * capExit) ((upTo + 1) * capExit) ≤
        (upTo + 1 - max (firstExitEpoch preset start.state)
          (start.state.earliestExitEpoch electra).toNat) * capExit := by
    rw [Nat.sub_mul]
    omega
  have consolidationRange : (upTo + 1) * capConsolidation -
      min (firstExitEpoch preset start.state * capConsolidation)
        ((upTo + 1) * capConsolidation) ≤
        (upTo + 1 - firstExitEpoch preset start.state) * capConsolidation := by
    rw [Nat.sub_mul]
    omega
  omega

/-! ## The stake that leaves across the upgrade -/

/-- Each state of the second of two runs is a state of both together. -/
theorem Run.mem_states_append {first start : ForkedBeaconState preset}
    (head : Run config checks first start) :
    ∀ {after : ForkedBeaconState preset} (tail : Run config checks start after),
      ∀ forked ∈ tail.states, forked ∈ (head.append tail).states
  | _, .nil, forked, member => by
    rw [List.mem_singleton.mp member]
    exact Run.end_mem_states head
  | _, .snoc tail _, forked, member => by
    rcases List.mem_append.mp member with earlier | now
    · exact List.mem_append_left _ (Run.mem_states_append head tail forked earlier)
    · exact List.mem_append_right _ now

/-- The stake of a state that a later upgraded state has queued to leave by an epoch.

Take the validators active at the current epoch of the first state.

Keep those active at the current epoch of the upgraded state, with an exit epoch up to the epoch.

Their effective balance is read from the first state. -/
def queuedAtUpgrade {fork fork' : Fork} (state : BeaconState preset fork)
    (upgraded : BeaconState preset fork') (upTo : Epoch) : Nat :=
  ∑ position ∈ (Finset.range state.validators.data.size).filter (fun position =>
      activeAt state (getCurrentEpoch state) position = true ∧
        (upgraded.validators.data[position]?).any (fun validator =>
          isActiveValidator validator (getCurrentEpoch upgraded) &&
            decide (validator.exitEpoch ≤ upTo)) = true),
    effectiveAt state position

/-- The stake that leaves the active set over a run from before Electra to Electra or later.

The run starts at a reachable state.

It splits at its upgrade from Deneb to Electra, which keeps the current epoch.

The stake is measured at the effective balances of the first state.

It is at most five parts.

- The stake that leaves before the upgrade.
- The stake queued to leave by the last epoch at the upgrade, read from the upgraded state.
- The churn of exits from the earliest exit epoch that the upgrade opens, to the last epoch.
- The churn of consolidations from the first epoch an exit may take at the upgrade.
- For each exit started from Electra on, its slack at the start, its step budgets and the rounding.

The upgrade opens the queue of exits after every exit epoch set before it.

So the second and the third parts never count the same epoch.

Take caps on the churns of every state of the run.

The upgrade starts both churns full, so they also cap the churn left at the upgrade.

A validator active in the first state must keep its activation epoch, as the lifecycle gives.

The last epoch must be at least the first and below the far future epoch.

Each state of the run must be ready for a ledger. -/
theorem Run.leavingStake_le_acrossElectra (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {capExit capConsolidation largest : Nat} {start after : ForkedBeaconState preset}
    (early : start.fork < .pectra) (late : .pectra ≤ after.fork)
    (reachable : Reachable config checks start) (run : Run config checks start after)
    (ready : ∀ forked ∈ run.states, LedgerReady forked)
    (churns : ∀ forked ∈ run.states, ChurnsBounded config capExit capConsolidation largest forked)
    (epochs : getCurrentEpoch start.state ≤ getCurrentEpoch after.state)
    (finite : getCurrentEpoch after.state < FAR_FUTURE_EPOCH)
    (activations : ∀ (position : Nat) (validator later : Validator),
      start.state.validators.data[position]? = some validator →
        after.state.validators.data[position]? = some later →
        isActiveValidator validator (getCurrentEpoch start.state) = true →
          later.activationEpoch = validator.activationEpoch) :
    ∃ (pre : BeaconState preset .dencun) (post : BeaconState preset .pectra)
      (budgets : Nat → List (BalanceFlow → Nat)),
      Reaches config checks start ⟨.dencun, pre⟩ ∧
      Nonempty (Step config checks ⟨.dencun, pre⟩ ⟨.pectra, post⟩) ∧
      Reaches config checks ⟨.pectra, post⟩ after ∧
      upgradeToElectra config pre = .ok post ∧
      getCurrentEpoch post = getCurrentEpoch pre ∧
      (∀ position, run.Budgets position (budgets position)) ∧
      leavingStake start.state after.state ≤
        leavingStake start.state pre +
          queuedAtUpgrade start.state post (getCurrentEpoch after.state) +
          ((getCurrentEpoch after.state).toNat + 1 -
            (post.earliestExitEpoch (by decide)).toNat) * capExit +
          ((getCurrentEpoch after.state).toNat + 1 - firstExitEpoch preset post) *
            capConsolidation +
          ∑ position ∈ (leavingExits post after.state).filter (fun position =>
              activeAt start.state (getCurrentEpoch start.state) position = true),
            ((effectiveAt start.state position - balanceAt start.state position) +
              (BalanceFlow.all.map fun flow => ((budgets position).map (· flow)).sum).sum +
              (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)) := by
  obtain ⟨before, next, head, step, tail, beforeEarly, nextLate, rfl⟩ :=
    Run.splitAtElectra early run late
  obtain ⟨pre, post, rfl, rfl, upgraded⟩ := step.toElectra beforeEarly nextLate
  obtain ⟨keeps, exitsBefore, exitChurn, consolidationChurn⟩ := upgradeToElectra_crossing upgraded
  have small : ∀ forked ∈ ((head.snoc step).append tail).states,
      forked.state.validators.data.size < 2 ^ 64 := fun forked member => (ready forked member).small
  have tailIn := Run.mem_states_append (head.snoc step) tail
  have nextIn := tailIn _ (Run.start_mem_states tail)
  have afterSmall := small after (Run.end_mem_states _)
  have epochSame : getCurrentEpoch post = getCurrentEpoch pre := by
    simp only [getCurrentEpoch, keeps.slot]
  -- The upgrade starts both churns full, so the caps bound the churn left at it.
  have lefts : LeftBounded capExit capConsolidation ⟨.pectra, post⟩ := fun electra =>
    ⟨(churns _ nextIn electra).1 _ exitChurn, (churns _ nextIn electra).2.1 _ consolidationChurn⟩
  have electraNext : Fork.pectra ≤ (⟨.pectra, post⟩ : ForkedBeaconState preset).fork :=
    Nat.le_refl _
  have kept := Run.exitsKept electraNext tail afterSmall
  have charged := Run.chargedStake_le electraNext tail afterSmall
    (fun forked member => churns forked (tailIn forked member)) lefts
    (getCurrentEpoch after.state).toNat
  replace charged : ∑ position ∈ exitsBetween post after.state 0
        (getCurrentEpoch after.state).toNat, tail.chargedBalance position ≤
      ((getCurrentEpoch after.state).toNat + 1 - max (firstExitEpoch preset post)
          (post.earliestExitEpoch (by decide)).toNat) * capExit +
        ((getCurrentEpoch after.state).toNat + 1 - firstExitEpoch preset post) *
          capConsolidation := charged
  have chosen := fun position => ((head.snoc step).append tail).fallen_le_stepBudgets position ready
  refine ⟨pre, post, fun position => (chosen position).choose, ⟨head⟩, ⟨step⟩, ⟨tail⟩, upgraded,
    epochSame, fun position => (chosen position).choose_spec.1, ?_⟩
  set upTo := getCurrentEpoch after.state
  set exits := exitsBetween post after.state 0 upTo.toNat
  set activeFirst : Nat → Prop := fun position =>
    activeAt start.state (getCurrentEpoch start.state) position = true
  set early' := (Finset.range start.state.validators.data.size).filter (fun position =>
    (activeAt start.state (getCurrentEpoch start.state) position &&
      !activeAt pre (getCurrentEpoch pre) position) = true)
  set queued := (Finset.range start.state.validators.data.size).filter (fun position =>
    activeAt start.state (getCurrentEpoch start.state) position = true ∧
      (post.validators.data[position]?).any (fun validator =>
        isActiveValidator validator (getCurrentEpoch post) &&
          decide (validator.exitEpoch ≤ upTo)) = true)
  set started := (leavingExits post after.state).filter activeFirst
  -- Each leaving validator leaves before the upgrade, is queued at it, or exits after it.
  have split : (Finset.range start.state.validators.data.size).filter (fun position =>
        (activeAt start.state (getCurrentEpoch start.state) position &&
          !activeAt after.state upTo position) = true) ⊆ early' ∪ queued ∪ started := by
    intro position member
    obtain ⟨inside, leaves⟩ := Finset.mem_filter.mp member
    have leavesBool := leaves
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at leaves
    obtain ⟨activeStart, inactiveAfter⟩ := leaves
    by_cases activePre : activeAt pre (getCurrentEpoch pre) position = true
    · have activePost : activeAt post (getCurrentEpoch post) position = true := by
        rw [keeps.activeAt_eq, epochSame]
        exact activePre
      obtain ⟨current, currentFound⟩ : ∃ current,
          post.validators.data[position]? = some current := by
        cases read : post.validators.data[position]? with
        | none => simp [activeAt, read] at activePost
        | some current => exact ⟨current, rfl⟩
      obtain ⟨validator, found⟩ : ∃ validator,
          start.state.validators.data[position]? = some validator :=
        ⟨_, Array.getElem?_eq_getElem (Finset.mem_range.mp inside)⟩
      obtain ⟨later, laterFound, exitsSame⟩ := kept.exits afterSmall position current currentFound
      have activeValidator : isActiveValidator validator (getCurrentEpoch start.state) = true := by
        simpa [activeAt, found] using activeStart
      have currentActive : isActiveValidator current (getCurrentEpoch post) = true := by
        simpa [activeAt, currentFound] using activePost
      have laterInactive : isActiveValidator later upTo = false := by
        simpa [activeAt, laterFound] using inactiveAfter
      have same := activations position validator later found laterFound activeValidator
      -- The validator is active then not, with the same activation epoch, so it left by then.
      have left : later.exitEpoch ≤ upTo := by
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
          decide_eq_false_iff_not] at activeValidator laterInactive
        rcases laterInactive with notActivated | notBefore
        · exact absurd (same ▸ UInt64.le_trans activeValidator.1 epochs) notActivated
        · exact UInt64.not_lt.mp notBefore
      rcases exitsSame with sameExit | far
      · refine Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨inside, activeStart, ?_⟩))
        simp [currentFound, currentActive, sameExit ▸ left]
      · have postInside : position < post.validators.data.size :=
          (Array.getElem?_eq_some_iff.mp currentFound).1
        have set : later.exitEpoch ≠ FAR_FUTURE_EPOCH := fun top =>
          absurd (top ▸ left) (UInt64.not_le.mpr finite)
        refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨mem_exitsBetween.mpr ⟨postInside, ?_⟩, activePost, inactiveAfter⟩, activeStart⟩)
        have leftNat : later.exitEpoch.toNat ≤ (getCurrentEpoch after.state).toNat :=
          UInt64.le_iff_toNat_le.mp left
        simp [currentFound, laterFound, startsExit, far, set, leftNat]
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨inside, ?_⟩))
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨activeStart, by simpa using activePre⟩
  -- The validators that exit from Electra on cost their charge and what they lost before it.
  have startedSplit : ∑ position ∈ started, effectiveAt start.state position ≤
      ∑ position ∈ started, tail.chargedBalance position +
        ∑ position ∈ started,
          (effectiveAt start.state position - tail.chargedBalance position) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun _ _ => by omega
  have startedCharged : ∑ position ∈ started, tail.chargedBalance position ≤
      ∑ position ∈ exits, tail.chargedBalance position :=
    Finset.sum_le_sum_of_subset ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
  have losses : ∑ position ∈ started,
        (effectiveAt start.state position - tail.chargedBalance position) ≤
      ∑ position ∈ started,
        ((effectiveAt start.state position - balanceAt start.state position) +
          (BalanceFlow.all.map fun flow =>
            (((chosen position).choose).map (· flow)).sum).sum +
          (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)) := by
    refine Finset.sum_le_sum fun position member => ?_
    obtain ⟨inLeaving, active⟩ := Finset.mem_filter.mp member
    obtain ⟨inExits, -⟩ := Finset.mem_filter.mp inLeaving
    obtain ⟨_, starts⟩ := mem_exitsBetween.mp inExits
    obtain ⟨validator, later, found, found', far, set⟩ := startsExit_eq_true starts
    have loss := Run.charged_loss_le_append caps increment electraNext reachable (head.snoc step)
      active tail small validator later found far found' set
    have budget := (chosen position).choose_spec.2
    omega
  have exitFrom : (upTo.toNat + 1 - max (firstExitEpoch preset post)
        (post.earliestExitEpoch (by decide)).toNat) * capExit ≤
      (upTo.toNat + 1 - (post.earliestExitEpoch (by decide)).toNat) * capExit :=
    Nat.mul_le_mul_right _ (Nat.sub_le_sub_left (Nat.le_max_right _ _) _)
  have leaving : leavingStake start.state after.state =
      ∑ position ∈ (Finset.range start.state.validators.data.size).filter (fun position =>
        (activeAt start.state (getCurrentEpoch start.state) position &&
          !activeAt after.state upTo position) = true),
        effectiveAt start.state position :=
    sum_map_filter_range _ _ _
  have before : leavingStake start.state pre =
      ∑ position ∈ early', effectiveAt start.state position :=
    sum_map_filter_range _ _ _
  have subset := Finset.sum_le_sum_of_subset (f := effectiveAt start.state) split
  have union₁ := Nat.le.intro (Finset.sum_union_inter (s₁ := early' ∪ queued) (s₂ := started)
    (f := effectiveAt start.state))
  have union₂ := Nat.le.intro (Finset.sum_union_inter (s₁ := early') (s₂ := queued)
    (f := effectiveAt start.state))
  have queuedEq : queuedAtUpgrade start.state post upTo =
      ∑ position ∈ queued, effectiveAt start.state position := rfl
  dsimp only
  rw [leaving, before, queuedEq]
  omega

/-- The stake queued to leave at the upgrade to Electra, in closed form.

Before Electra each exit epoch has at most `max 1 cap` validators, for the cap of its registry.

The queued validators leave after the epoch of the upgrade, and before the queue it opens.

Each has an effective balance of at most `MAX_EFFECTIVE_BALANCE` in the first state.

The first state is reachable and before Electra, and the run from it reaches the Deneb state. -/
theorem queuedAtUpgrade_le (caps : EffectiveBalanceCaps preset) {start : ForkedBeaconState preset}
    (early : start.fork < .pectra) (reachable : Reachable config checks start)
    {pre : BeaconState preset .dencun} {post : BeaconState preset .pectra}
    (chain : Reaches config checks start ⟨.dencun, pre⟩)
    (upgraded : upgradeToElectra config pre = .ok post) {upTo : Epoch}
    (below : getCurrentEpoch post ≤ upTo) (finite : upTo < FAR_FUTURE_EPOCH) :
    queuedAtUpgrade start.state post upTo ≤
      (min ((post.earliestExitEpoch (by decide)).toNat - 1) upTo.toNat -
          (getCurrentEpoch post).toNat) *
        max 1 (churnCap config pre.validators.data.size) * preset.MAX_EFFECTIVE_BALANCE.toNat := by
  obtain ⟨keeps, exitsBefore, -, -⟩ := upgradeToElectra_crossing upgraded
  have preReachable := ReachableFrom.reaches reachable chain
  have cohorts := (Reachable.cohorts preReachable (show Fork.dencun < Fork.pectra by decide)).1
  have capped := reachable.effectiveBalancesCapped caps
  have finiteNat : upTo.toNat < 2 ^ 64 - 1 := UInt64.lt_iff_toNat_lt.mp finite
  have belowNat := UInt64.le_iff_toNat_le.mp below
  set first := (getCurrentEpoch post).toNat
  set window := min ((post.earliestExitEpoch (by decide)).toNat - 1) upTo.toNat - first
  set inWindow : Validator → Bool := fun validator =>
    decide (first < validator.exitEpoch.toNat ∧ validator.exitEpoch.toNat ≤ first + window)
  -- Each queued validator has, before the upgrade, an exit epoch in the window.
  have subset : (Finset.range start.state.validators.data.size).filter (fun position =>
        activeAt start.state (getCurrentEpoch start.state) position = true ∧
          (post.validators.data[position]?).any (fun validator =>
            isActiveValidator validator (getCurrentEpoch post) &&
              decide (validator.exitEpoch ≤ upTo)) = true) ⊆
      (Finset.range pre.validators.data.size).filter (fun position =>
        (pre.validators.data[position]?).any inWindow = true) := by
    intro position member
    obtain ⟨-, -, queued⟩ := Finset.mem_filter.mp member
    obtain ⟨current, currentFound⟩ : ∃ current,
        post.validators.data[position]? = some current := by
      cases read : post.validators.data[position]? with
      | none => simp [read] at queued
      | some current => exact ⟨current, rfl⟩
    have inside : position < pre.validators.data.size :=
      keeps.size ▸ (Array.getElem?_eq_some_iff.mp currentFound).1
    obtain ⟨validator, found⟩ : ∃ validator, pre.validators.data[position]? = some validator :=
      ⟨_, Array.getElem?_eq_getElem inside⟩
    obtain ⟨later, laterFound, -, exitSame, -⟩ := keeps.validator position validator found
    rw [currentFound] at laterFound
    cases laterFound
    simp only [currentFound, Option.any_some, Bool.and_eq_true, decide_eq_true_eq,
      isActiveValidator] at queued
    obtain ⟨⟨-, after⟩, byEnd⟩ := queued
    have afterNat := UInt64.lt_iff_toNat_lt.mp after
    have byEndNat := UInt64.le_iff_toNat_le.mp byEnd
    have set : validator.exitEpoch ≠ FAR_FUTURE_EPOCH := fun top => by
      rw [exitSame, top] at byEnd
      exact absurd byEnd (UInt64.not_le.mpr finite)
    have beforeQueue := exitsBefore position validator found set
    rw [exitSame] at afterNat byEndNat
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr inside, ?_⟩
    simp only [found, Option.any_some, inWindow, decide_eq_true_eq]
    omega
  have count : ((Finset.range pre.validators.data.size).filter (fun position =>
        (pre.validators.data[position]?).any inWindow = true)).card =
      pre.validators.data.toList.countP inWindow := by
    rw [countP_eq_range inWindow pre.validators.data.toList]
    simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range,
      Multiset.filter_coe, Multiset.coe_card, List.countP_eq_length_filter, Array.length_toList,
      Array.getElem?_toList, Bool.decide_eq_true]
  have windowed := countP_window_le (·.exitEpoch) pre.validators.data.toList first
    (max 1 (churnCap config pre.validators.data.size)) (fun epoch _ below =>
      cohorts epoch fun far => by rw [far, toNat_farFutureEpoch] at below; omega) window
    (by omega)
  have cards := Finset.card_le_card subset
  unfold queuedAtUpgrade
  refine Nat.le_trans (Finset.sum_le_card_nsmul _ _ preset.MAX_EFFECTIVE_BALANCE.toNat
    fun position _ => effectiveAt_le_max capped early position) ?_
  replace windowed : pre.validators.data.toList.countP inWindow ≤
      window * max 1 (churnCap config pre.validators.data.size) := windowed
  exact Nat.mul_le_mul_right _ (Nat.le_trans cards (Nat.le_trans (Nat.le_of_eq count) windowed))

/-- The stake that leaves the active set across the upgrade to Electra, in closed form.

It is `Run.leavingStake_le_acrossElectra` with both parts before Electra bounded by count.

- Before the upgrade, at most `max 1 cap` validators leave per epoch.
- The queue before Electra holds the same per epoch, up to the earliest exit epoch less one.

Each of those validators counts `MAX_EFFECTIVE_BALANCE`.

The cap is that of the registry at the upgrade.

The churn and the losses of the exits from Electra are as there. -/
theorem Run.leavingStake_le_acrossElectra_closed (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {capExit capConsolidation largest : Nat} {start after : ForkedBeaconState preset}
    (early : start.fork < .pectra) (late : .pectra ≤ after.fork)
    (reachable : Reachable config checks start) (run : Run config checks start after)
    (ready : ∀ forked ∈ run.states, LedgerReady forked)
    (churns : ∀ forked ∈ run.states, ChurnsBounded config capExit capConsolidation largest forked)
    (epochs : getCurrentEpoch start.state ≤ getCurrentEpoch after.state)
    (finite : getCurrentEpoch after.state < FAR_FUTURE_EPOCH)
    (activations : ∀ (position : Nat) (validator later : Validator),
      start.state.validators.data[position]? = some validator →
        after.state.validators.data[position]? = some later →
        isActiveValidator validator (getCurrentEpoch start.state) = true →
          later.activationEpoch = validator.activationEpoch) :
    ∃ (pre : BeaconState preset .dencun) (post : BeaconState preset .pectra)
      (budgets : Nat → List (BalanceFlow → Nat)),
      Reaches config checks start ⟨.dencun, pre⟩ ∧
      Nonempty (Step config checks ⟨.dencun, pre⟩ ⟨.pectra, post⟩) ∧
      Reaches config checks ⟨.pectra, post⟩ after ∧
      upgradeToElectra config pre = .ok post ∧
      getCurrentEpoch post = getCurrentEpoch pre ∧
      (∀ position, run.Budgets position (budgets position)) ∧
      leavingStake start.state after.state ≤
        ((getCurrentEpoch pre).toNat - (getCurrentEpoch start.state).toNat) *
            max 1 (churnCap config pre.validators.data.size) *
            preset.MAX_EFFECTIVE_BALANCE.toNat +
          (min ((post.earliestExitEpoch (by decide)).toNat - 1)
              (getCurrentEpoch after.state).toNat - (getCurrentEpoch post).toNat) *
            max 1 (churnCap config pre.validators.data.size) *
            preset.MAX_EFFECTIVE_BALANCE.toNat +
          ((getCurrentEpoch after.state).toNat + 1 -
            (post.earliestExitEpoch (by decide)).toNat) * capExit +
          ((getCurrentEpoch after.state).toNat + 1 - firstExitEpoch preset post) *
            capConsolidation +
          ∑ position ∈ (leavingExits post after.state).filter (fun position =>
              activeAt start.state (getCurrentEpoch start.state) position = true),
            ((effectiveAt start.state position - balanceAt start.state position) +
              (BalanceFlow.all.map fun flow => ((budgets position).map (· flow)).sum).sum +
              (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)) := by
  obtain ⟨pre, post, budgets, chain, step, tailChain, upgraded, epochSame, budgetsOk, bound⟩ :=
    Run.leavingStake_le_acrossElectra caps increment early late reachable run ready churns epochs
      finite activations
  refine ⟨pre, post, budgets, chain, step, tailChain, upgraded, epochSame, budgetsOk, ?_⟩
  obtain ⟨tail⟩ := tailChain
  -- The epoch of the upgrade is at most the last one, so it is below the far future epoch.
  have moves := Run.epochTransitions_eq (Nat.le_refl _) tail
  have finiteNat := UInt64.lt_iff_toNat_lt.mp finite
  have far := toNat_farFutureEpoch
  have preFinite : (getCurrentEpoch pre).toNat < 2 ^ 64 - 1 := by
    rw [← epochSame]
    simp only at moves
    omega
  have before : leavingStake start.state pre ≤
      ((getCurrentEpoch pre).toNat - (getCurrentEpoch start.state).toNat) *
        max 1 (churnCap config pre.validators.data.size) * preset.MAX_EFFECTIVE_BALANCE.toNat :=
    Reaches.leavingStake_le (after := ⟨.dencun, pre⟩) caps reachable chain
      (show Fork.dencun < Fork.pectra by decide) preFinite
  have postBelow : getCurrentEpoch post ≤ getCurrentEpoch after.state := by
    simp only at moves
    exact UInt64.le_iff_toNat_le.mpr (by omega)
  have queued := queuedAtUpgrade_le caps early reachable chain upgraded postBelow finite
  exact Nat.le_trans bound (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.add_le_add before queued) _) _) _)

end EthLib.Consensus
