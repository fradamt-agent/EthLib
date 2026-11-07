module

public import EthLib.Consensus.Proofs.Transition.Cohorts
public import EthLib.Consensus.WeakSubjectivity

/-!
# Proofs: how much the active set changes over a range of epochs, before Electra

The weak subjectivity period rests on a bound on how fast the validator set changes.

Take a state, and a later state that a chain reaches from it, both before Electra.

Let `E` and `E'` be their current epochs, and `n = E' - E`.

- Leaving: at most `n * max 1 cap` validators active at `E` are not active at `E'`.
- Joining: at most `n * cap` validators active at `E'` were not active at `E`.

Here `cap` is the churn cap of the later registry, `churnCap config size`.

So within a weak subjectivity period of `p` epochs, at most `p * max 1 cap` validators leave.

At most `p * cap` join.

Two facts give the bound.

A validator that leaves has its exit epoch in `(E, E']`, and one that joins its activation epoch.

An epoch set after the first state is at least its next activation epoch, which is after `E`.

So each one sits in a cohort between `E` and `E'`, and each cohort is within its cap.

The analysis of the period instead takes the churn limit of the first state.

That limit counts only the validators active then.

The cap here counts the whole later registry, since later churn limits may be larger.

The bound counts validators, not stake.

The last epoch `E'` must be below the far future epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork fork' : Base.Fork} {config : Config} {checks : SignatureChecks}

/-! ## Counting -/

/-- A list has at most the count of a list at least as long that passes its tests at each position.
-/
theorem countP_le_of_getElem {α : Type} {test test' : α → Bool} :
    ∀ {first second : List α}, first.length ≤ second.length →
      (∀ index (inside : index < first.length) (inside' : index < second.length),
        test first[index] = true → test' second[index] = true) →
      first.countP test ≤ second.countP test'
  | [], _, _, _ => Nat.zero_le _
  | _ :: _, [], longer, _ => by simp at longer
  | head :: rest, head' :: rest', longer, implied => by
    have tail := countP_le_of_getElem (first := rest) (second := rest')
      (by simpa using longer) (fun index inside inside' holds => by
        have := implied (index + 1) (by simpa using inside) (by simpa using inside')
          (by rw [List.getElem_cons_succ]; exact holds)
        rwa [List.getElem_cons_succ] at this)
    have first := implied 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at first
    simp only [List.countP_cons]
    split <;> split <;> first | omega | simp_all

/-- As above, with one more position where only the second test holds. -/
theorem countP_lt_of_getElem {α : Type} {test test' : α → Bool} :
    ∀ {first second : List α}, first.length ≤ second.length →
      (∀ index (inside : index < first.length) (inside' : index < second.length),
        test first[index] = true → test' second[index] = true) →
      (∃ index, ∃ inside' : index < second.length, test' second[index] = true ∧
        ∀ inside : index < first.length, test first[index] = false) →
      first.countP test < second.countP test'
  | [], second, _, _, ⟨index, inside', holds, _⟩ =>
    List.countP_pos_iff.mpr ⟨second[index], List.getElem_mem inside', holds⟩
  | _ :: _, [], longer, _, _ => by simp at longer
  | head :: rest, head' :: rest', longer, implied, ⟨index, inside', holds, fails⟩ => by
    have restImplied : ∀ index (inside : index < rest.length) (inside' : index < rest'.length),
        test rest[index] = true → test' rest'[index] = true := fun index inside inside' h => by
      have := implied (index + 1) (by simpa using inside) (by simpa using inside')
        (by rw [List.getElem_cons_succ]; exact h)
      rwa [List.getElem_cons_succ] at this
    have first := implied 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at first
    simp only [List.countP_cons]
    cases index with
    | zero =>
      have tail := countP_le_of_getElem (first := rest) (second := rest')
        (by simpa using longer) restImplied
      simp only [List.getElem_cons_zero] at holds
      have headFails := fails (by simp)
      simp only [List.getElem_cons_zero] at headFails
      simp only [holds, headFails, Bool.false_eq_true, ↓reduceIte]
      omega
    | succ index =>
      have tail := countP_lt_of_getElem (first := rest) (second := rest')
        (by simpa using longer) restImplied
        ⟨index, by simpa using inside', by rwa [List.getElem_cons_succ] at holds,
          fun inside => by
            have := fails (by simpa using inside)
            rwa [List.getElem_cons_succ] at this⟩
      split <;> split <;> first | omega | simp_all

/-- The count of a list is the count of its positions. -/
theorem countP_eq_range {α : Type} (test : α → Bool) :
    ∀ list : List α,
      list.countP test = (List.range list.length).countP fun index => (list[index]?).any test
  | [] => rfl
  | head :: rest => by
    have more := countP_eq_range test rest
    simp only [List.countP_cons, List.length_cons, List.range_succ_eq_map, List.countP_map,
      more, List.getElem?_cons_zero, Option.any_some]
    simp [Function.comp_def]

/-- A count of positions below `n` is at most one of positions below a larger `m`. -/
theorem countP_range_le {test test' : Nat → Bool} {n m : Nat} (le : n ≤ m)
    (implied : ∀ index, index < n → test index = true → test' index = true) :
    (List.range n).countP test ≤ (List.range m).countP test' := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le le
  rw [List.range_add, List.countP_append]
  refine Nat.le_trans ?_ (Nat.le_add_right _ _)
  exact List.countP_mono_left fun index member holds =>
    implied index (List.mem_range.mp member) holds

theorem countP_or_le {α : Type} (test test' : α → Bool) :
    ∀ list : List α,
      list.countP (fun item => test item || test' item) ≤ list.countP test + list.countP test'
  | [] => Nat.zero_le _
  | head :: rest => by
    have := countP_or_le test test' rest
    simp only [List.countP_cons]
    cases test head <;> cases test' head <;> simp <;> omega

/-! ## Windows of epochs -/

/-- The validators with an epoch in a window, when each epoch of the window has a capped cohort.
-/
theorem countP_window_le (epochOf : Validator → Epoch) (validators : List Validator)
    (start : Nat) (cap : Nat)
    (bounded : ∀ epoch : Epoch, start < epoch.toNat → epoch.toNat < 2 ^ 64 - 1 →
      validators.countP (epochOf · == epoch) ≤ cap) :
    ∀ count, start + count < 2 ^ 64 - 1 →
      validators.countP (fun validator =>
        decide (start < (epochOf validator).toNat ∧ (epochOf validator).toNat ≤ start + count)) ≤
        count * cap
  | 0, _ => by
    rw [List.countP_eq_zero.mpr fun validator _ inside => by simp at inside; omega]
    simp
  | count + 1, fits => by
    have earlier := countP_window_le epochOf validators start cap bounded count (by omega)
    -- The epoch at the end of the window, which fits in 64 bits.
    have last := bounded (start + count + 1).toUInt64 (by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)]
      omega) (by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)]
      omega)
    have split := countP_or_le
      (fun validator =>
        decide (start < (epochOf validator).toNat ∧ (epochOf validator).toNat ≤ start + count))
      (epochOf · == (start + count + 1).toUInt64) validators
    refine Nat.le_trans (List.countP_mono_left fun validator _ inside => ?_)
      (Nat.le_trans split ?_)
    · simp only [decide_eq_true_eq] at inside
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
      by_cases atEnd : (epochOf validator).toNat = start + count + 1
      · refine .inr (UInt64.toNat_inj.mp ?_)
        have size : UInt64.size = 2 ^ 64 := rfl
        rw [atEnd, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by omega)]
      · exact .inl ⟨inside.1, by omega⟩
    · rw [Nat.succ_mul]
      omega

/-! ## Active validators at an epoch -/

/-- Whether the validator at a position of the registry is active at an epoch. -/
def activeAt (state : BeaconState preset fork) (epoch : Epoch) (index : Nat) : Bool :=
  (state.validators.data[index]?).any (isActiveValidator · epoch)

/-- The validators active at the current epoch of a state, and not at that of a later state. -/
def leavingCount (state : BeaconState preset fork) (after : BeaconState preset fork') : Nat :=
  (List.range state.validators.data.size).countP fun index =>
    activeAt state (getCurrentEpoch state) index && !activeAt after (getCurrentEpoch after) index

/-- The validators active at the current epoch of a later state, and not at that of a state. -/
def joiningCount (state : BeaconState preset fork) (after : BeaconState preset fork') : Nat :=
  (List.range after.validators.data.size).countP fun index =>
    activeAt after (getCurrentEpoch after) index && !activeAt state (getCurrentEpoch state) index

theorem isActiveValidator_iff {validator : Validator} {epoch : Epoch} :
    isActiveValidator validator epoch = true ↔
      validator.activationEpoch.toNat ≤ epoch.toNat ∧ epoch.toNat < validator.exitEpoch.toNat := by
  simp [isActiveValidator, UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt]

theorem toNat_farFutureEpoch : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl

/-! ## Epochs set after a state -/

/-- A later state may set an exit epoch at a position that the first state did not.

That epoch is at least the next activation epoch of the first state.

Otherwise its cohort would have one more validator than in the first state. -/
theorem nextActivationEpoch_le_of_exitEpoch_set {state : BeaconState preset fork}
    {after : BeaconState preset fork'} (lifecycle : RegistryLifecycle state after)
    (small : after.validators.data.size < 2 ^ 64) (past : PastCohortsKept state after)
    {index : Nat} {later : Validator} (found : after.validators.data[index]? = some later)
    (finite : later.exitEpoch ≠ FAR_FUTURE_EPOCH)
    (unset : ∀ validator, state.validators.data[index]? = some validator →
      validator.exitEpoch = FAR_FUTURE_EPOCH) :
    nextActivationEpoch state ≤ later.exitEpoch.toNat := by
  refine Nat.le_of_not_lt fun before => ?_
  have same := (past.2 later.exitEpoch finite before).1
  have more : exitCohort state later.exitEpoch < exitCohort after later.exitEpoch := by
    refine countP_lt_of_getElem (by simpa using lifecycle.size_le) (fun position inside inside' =>
      ?_) ⟨index, by simpa using (Array.getElem?_eq_some_iff.mp found).1, ?_, fun inside => ?_⟩
    · -- An exit epoch that is set stays.
      simp only [Array.getElem_toList, beq_iff_eq]
      intro equal
      obtain ⟨kept, keptFound, step⟩ := lifecycle.validators small position
        state.validators.data[position] (Array.getElem?_eq_getElem (by simpa using inside))
      rw [Array.getElem?_eq_getElem (by simpa using inside')] at keptFound
      cases keptFound
      rw [step.exitEpoch (by rw [equal]; exact finite), equal]
    · have := (Array.getElem?_eq_some_iff.mp found).2
      simp [this]
    · have := unset _ (Array.getElem?_eq_getElem (by simpa using inside))
      simp only [Array.getElem_toList, this]
      exact beq_eq_false_iff_ne.mpr (Ne.symm finite)
  omega

/-- A later state may set an activation epoch at a position that the first state did not.

That epoch is at least the next activation epoch of the first state. -/
theorem nextActivationEpoch_le_of_activationEpoch_set {state : BeaconState preset fork}
    {after : BeaconState preset fork'} (lifecycle : RegistryLifecycle state after)
    (small : after.validators.data.size < 2 ^ 64) (past : PastCohortsKept state after)
    {index : Nat} {later : Validator} (found : after.validators.data[index]? = some later)
    (finite : later.activationEpoch ≠ FAR_FUTURE_EPOCH)
    (unset : ∀ validator, state.validators.data[index]? = some validator →
      validator.activationEpoch = FAR_FUTURE_EPOCH) :
    nextActivationEpoch state ≤ later.activationEpoch.toNat := by
  refine Nat.le_of_not_lt fun before => ?_
  have same := (past.2 later.activationEpoch finite before).2
  have more : activationCohort state later.activationEpoch <
      activationCohort after later.activationEpoch := by
    refine countP_lt_of_getElem (by simpa using lifecycle.size_le) (fun position inside inside' =>
      ?_) ⟨index, by simpa using (Array.getElem?_eq_some_iff.mp found).1, ?_, fun inside => ?_⟩
    · simp only [Array.getElem_toList, beq_iff_eq]
      intro equal
      obtain ⟨kept, keptFound, step⟩ := lifecycle.validators small position
        state.validators.data[position] (Array.getElem?_eq_getElem (by simpa using inside))
      rw [Array.getElem?_eq_getElem (by simpa using inside')] at keptFound
      cases keptFound
      rw [step.activationEpoch (by rw [equal]; exact finite), equal]
    · have := (Array.getElem?_eq_some_iff.mp found).2
      simp [this]
    · have := unset _ (Array.getElem?_eq_getElem (by simpa using inside))
      simp only [Array.getElem_toList, this]
      exact beq_eq_false_iff_ne.mpr (Ne.symm finite)
  omega

/-! ## Leaving and joining -/

/-- A next activation epoch no later than that of another state gives a current epoch no later.
-/
theorem currentEpoch_le_of_next {state : BeaconState preset fork}
    {after : BeaconState preset fork'}
    (le : nextActivationEpoch state ≤ nextActivationEpoch after) :
    (getCurrentEpoch state).toNat ≤ (getCurrentEpoch after).toNat := by
  unfold nextActivationEpoch at le
  omega

/-- At most `n * max 1 cap` validators leave the active set over `n` epochs, before Electra. -/
theorem leavingCount_le {state : BeaconState preset fork} {after : BeaconState preset fork'}
    (lifecycle : RegistryLifecycle state after) (small : after.validators.data.size < 2 ^ 64)
    (past : PastCohortsKept state after) (bounded : ExitCohortsBounded config after)
    (finite : (getCurrentEpoch after).toNat < 2 ^ 64 - 1) :
    leavingCount state after ≤
      ((getCurrentEpoch after).toNat - (getCurrentEpoch state).toNat) *
        max 1 (churnCap config after.validators.data.size) := by
  have ordered := currentEpoch_le_of_next past.1
  set start := (getCurrentEpoch state).toNat
  set last := (getCurrentEpoch after).toNat
  have window := countP_window_le (·.exitEpoch) after.validators.data.toList start
    (max 1 (churnCap config after.validators.data.size)) (fun epoch _ below =>
      bounded epoch fun far => by rw [far, toNat_farFutureEpoch] at below; omega)
      (last - start) (by omega)
  refine Nat.le_trans ?_ window
  rw [countP_eq_range _ after.validators.data.toList, Array.length_toList]
  refine countP_range_le lifecycle.size_le fun index inside holds => ?_
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at holds
  obtain ⟨wasActive, notActive⟩ := holds
  unfold activeAt at wasActive notActive
  obtain ⟨validator, found⟩ : ∃ validator, state.validators.data[index]? = some validator :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨later, laterFound, step⟩ := lifecycle.validators small index validator found
  rw [found, Option.any_some, isActiveValidator_iff] at wasActive
  rw [laterFound, Option.any_some] at notActive
  simp only [Array.getElem?_toList, laterFound, Option.any_some, decide_eq_true_eq]
  -- The validator was activated by the first epoch, so not later, and has exited since.
  have activationSet : validator.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro far
    rw [far, toNat_farFutureEpoch] at wasActive
    have := UInt64.toNat_lt validator.exitEpoch
    omega
  have activationSame := step.activationEpoch activationSet
  have exited : later.exitEpoch.toNat ≤ last := by
    by_contra notExited
    have : isActiveValidator later (getCurrentEpoch after) = true := by
      rw [isActiveValidator_iff, activationSame]
      omega
    rw [this] at notActive
    cases notActive
  refine ⟨?_, by omega⟩
  by_cases exitSet : validator.exitEpoch = FAR_FUTURE_EPOCH
  · have fresh := nextActivationEpoch_le_of_exitEpoch_set lifecycle small past laterFound
      (fun far => by rw [far, toNat_farFutureEpoch] at exited; omega)
      (fun other otherFound => by
        rw [found] at otherFound
        cases otherFound
        exact exitSet)
    unfold nextActivationEpoch at fresh
    omega
  · rw [step.exitEpoch exitSet]
    exact wasActive.2

/-- At most `n * cap` validators join the active set over `n` epochs, before Electra. -/
theorem joiningCount_le {state : BeaconState preset fork} {after : BeaconState preset fork'}
    (lifecycle : RegistryLifecycle state after) (small : after.validators.data.size < 2 ^ 64)
    (past : PastCohortsKept state after) (activations : ActivationCohorts config after)
    (finite : (getCurrentEpoch after).toNat < 2 ^ 64 - 1) :
    joiningCount state after ≤
      ((getCurrentEpoch after).toNat - (getCurrentEpoch state).toNat) *
        churnCap config after.validators.data.size := by
  have ordered := currentEpoch_le_of_next past.1
  set start := (getCurrentEpoch state).toNat
  set last := (getCurrentEpoch after).toNat
  have window := countP_window_le (·.activationEpoch) after.validators.data.toList start
    (churnCap config after.validators.data.size) (fun epoch late below =>
      activations.bounded epoch (fun far => by rw [far, toNat_farFutureEpoch] at below; omega)
        (fun genesis => by rw [genesis] at late; simp [GENESIS_EPOCH] at late))
      (last - start) (by omega)
  refine Nat.le_trans ?_ window
  rw [countP_eq_range _ after.validators.data.toList, Array.length_toList]
  refine countP_range_le (Nat.le_refl _) fun index inside holds => ?_
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at holds
  obtain ⟨isActive, wasNotActive⟩ := holds
  unfold activeAt at isActive wasNotActive
  obtain ⟨later, laterFound⟩ : ∃ later, after.validators.data[index]? = some later :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  rw [laterFound, Option.any_some, isActiveValidator_iff] at isActive
  simp only [Array.getElem?_toList, laterFound, Option.any_some, decide_eq_true_eq]
  refine ⟨?_, by omega⟩
  have activationFinite : later.activationEpoch ≠ FAR_FUTURE_EPOCH := by
    intro far
    rw [far, toNat_farFutureEpoch] at isActive
    omega
  -- The activation epoch is after the first epoch: set before and kept, or set since.
  cases found : state.validators.data[index]? with
  | none =>
    have fresh := nextActivationEpoch_le_of_activationEpoch_set lifecycle small past laterFound
      activationFinite (fun _ absent => by rw [found] at absent; cases absent)
    unfold nextActivationEpoch at fresh
    omega
  | some validator =>
    obtain ⟨kept, keptFound, step⟩ := lifecycle.validators small index validator found
    rw [laterFound] at keptFound
    cases keptFound
    rw [found, Option.any_some] at wasNotActive
    by_cases activationSet : validator.activationEpoch = FAR_FUTURE_EPOCH
    · have fresh := nextActivationEpoch_le_of_activationEpoch_set lifecycle small past
        laterFound activationFinite (fun other otherFound => by
          rw [found] at otherFound
          cases otherFound
          exact activationSet)
      unfold nextActivationEpoch at fresh
      omega
    · have same := step.activationEpoch activationSet
      rw [same]
      by_contra early
      -- Active at the first epoch would need it not to have exited by then.
      have exitLate : (getCurrentEpoch state).toNat < validator.exitEpoch.toNat := by
        by_contra exitedEarly
        have exitSet : validator.exitEpoch ≠ FAR_FUTURE_EPOCH := fun far => by
          rw [far, toNat_farFutureEpoch] at exitedEarly
          omega
        rw [step.exitEpoch exitSet] at isActive
        omega
      have : isActiveValidator validator (getCurrentEpoch state) = true := by
        rw [isActiveValidator_iff]
        omega
      rw [this] at wasNotActive
      cases wasNotActive

/-! ## Along chains, and within the weak subjectivity period -/

/-- Along a chain from a reachable state, at most `n * max 1 cap` validators leave in `n` epochs.

The chain must stay before Electra. -/
theorem Reaches.leavingCount_le {start after : ForkedBeaconState preset}
    (reachable : Reachable config checks start) (chain : Reaches config checks start after)
    (early : after.fork < .pectra) (finite : (getCurrentEpoch after.state).toNat < 2 ^ 64 - 1) :
    leavingCount start.state after.state ≤
      ((getCurrentEpoch after.state).toNat - (getCurrentEpoch start.state).toNat) *
        max 1 (churnCap config after.state.validators.data.size) :=
  EthLib.Consensus.leavingCount_le chain.registryLifecycle
    (Nat.lt_of_le_of_lt (after.state.validators.bound (Nat.lt_trans early (by decide)))
      (UInt64.toNat_lt _))
    ((chain.pastCohorts reachable.cohorts).2 early)
    ((Reachable.cohorts (ReachableFrom.reaches reachable chain) early).1) finite

/-- Along a chain from a reachable state, at most `n * cap` validators join in `n` epochs.

The chain must stay before Electra. -/
theorem Reaches.joiningCount_le {start after : ForkedBeaconState preset}
    (reachable : Reachable config checks start) (chain : Reaches config checks start after)
    (early : after.fork < .pectra) (finite : (getCurrentEpoch after.state).toNat < 2 ^ 64 - 1) :
    joiningCount start.state after.state ≤
      ((getCurrentEpoch after.state).toNat - (getCurrentEpoch start.state).toNat) *
        churnCap config after.state.validators.data.size :=
  EthLib.Consensus.joiningCount_le chain.registryLifecycle
    (Nat.lt_of_le_of_lt (after.state.validators.bound (Nat.lt_trans early (by decide)))
      (UInt64.toNat_lt _))
    ((chain.pastCohorts reachable.cohorts).2 early)
    ((Reachable.cohorts (ReachableFrom.reaches reachable chain) early).2) finite

/-- Within some epochs of a reachable state, the active set changes by at most that many caps.

Each way is counted apart, and the chain must stay before Electra.

For the weak subjectivity period, the epochs are what `computeWeakSubjectivityPeriod` gives.

The cap is that of the later registry, which is at least the churn limit of the first state. -/
theorem Reaches.churn_le_of_epochs_le {start after : ForkedBeaconState preset} {epochs : Nat}
    (reachable : Reachable config checks start) (chain : Reaches config checks start after)
    (early : after.fork < .pectra) (finite : (getCurrentEpoch after.state).toNat < 2 ^ 64 - 1)
    (within : (getCurrentEpoch after.state).toNat ≤ (getCurrentEpoch start.state).toNat + epochs) :
    leavingCount start.state after.state ≤
        epochs * max 1 (churnCap config after.state.validators.data.size) ∧
      joiningCount start.state after.state ≤
        epochs * churnCap config after.state.validators.data.size := by
  have span : (getCurrentEpoch after.state).toNat - (getCurrentEpoch start.state).toNat ≤
      epochs := by omega
  exact ⟨Nat.le_trans (chain.leavingCount_le reachable early finite)
      (Nat.mul_le_mul_right _ span),
    Nat.le_trans (chain.joiningCount_le reachable early finite) (Nat.mul_le_mul_right _ span)⟩

/-! ## The churn limit of the first state does not bound a window

The analysis of the period bounds each epoch by the churn limit of the first state.

Each cohort is instead filled up to the churn limit of the state that fills it.

That limit grows with the number of active validators, so it can exceed that of the first state.

The theorems below give the exact amounts, and the minimal configuration shows the limit moving.

They do not build a chain that reaches such a state.
-/

/-- Before Electra, the registry updates fill the cohort of the next activation epoch.

They add the first validators of the queue, as many as the limit of the state they run on allows.

That state is the one after the pass of eligibility and ejections. -/
theorem activationCohort_processRegistryUpdates {state after : BeaconState preset fork}
    (early : fork < .pectra) (computed : processRegistryUpdates config state = .ok after) :
    ∃ updated, (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state =
        .ok updated ∧
      ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch.toNat = nextActivationEpoch state →
        activationCohort after epoch = activationCohort state epoch +
          ((activationQueue updated).take
            (if Fork.dencun ≤ fork then getValidatorActivationChurnLimit config updated
              else getValidatorChurnLimit config updated).toNat).length := by
  unfold processRegistryUpdates at computed
  split at computed
  · rename_i electra
    exact absurd electra (Nat.not_le_of_lt early)
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  have updatedKept := CohortStep.foldlM (config := config)
    (fun _ _ _ ok => cohortStep_updateRegistryEntry early ok) updatedOk
  have small : updated.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (updated.validators.bound (Nat.lt_trans early (by decide)))
      (UInt64.toNat_lt _)
  obtain ⟨_, _, _, activations⟩ := foldActivateValidator_cohorts
    (List.Nodup.sublist (List.take_sublist _ _) (activationQueue_nodup small))
    (fun index member => by
      obtain ⟨position, validator, equal, found, eligible⟩ :=
        mem_activationQueue (List.mem_of_mem_take member)
      refine ⟨validator, ?_, activationEpoch_of_isEligibleForActivation eligible⟩
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have size : UInt64.size = 2 ^ 64 := rfl
      have exact : index.toNat = position := by
        rw [← equal, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by omega)]
      simp [getValidator, exact, found]) activated
  have next : nextActivationEpoch updated = nextActivationEpoch state := by
    simp [nextActivationEpoch, getCurrentEpoch, updatedKept.slot]
  refine ⟨updated, updatedOk, fun epoch finite atNext => ?_⟩
  simp only [activations epoch finite, next, atNext, ↓reduceIte,
    updatedKept.activations epoch finite]

/-- Before Electra, an exit goes to the latest exit epoch while its cohort has room.

The room is below the churn limit of the state that adds the exit.

So each exit cohort fills up to the churn limit of the states that add to it. -/
theorem exitQueueEpoch_of_room {state : BeaconState preset fork} {earliest : Epoch}
    (earliestOk : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok earliest)
    (room : (state.validators.data.toList.filter (·.exitEpoch ==
        (state.validators.data.toList.filter (·.exitEpoch != FAR_FUTURE_EPOCH)).foldl
          (fun latest validator => max latest validator.exitEpoch) earliest)).length <
      (getValidatorChurnLimit config state).toNat) :
    exitQueueEpoch config state =
      .ok ((state.validators.data.toList.filter (·.exitEpoch != FAR_FUTURE_EPOCH)).foldl
        (fun latest validator => max latest validator.exitEpoch) earliest) := by
  simp only [exitQueueEpoch, liftArith, earliestOk, Except.mapError, bind, Except.bind, pure,
    Except.pure]
  simp only [Nat.not_le_of_lt room, ↓reduceIte]

/-- Before Deneb, a pass with a long enough queue fills an empty cohort to exactly its churn limit.

In a reachable state the cohort of the next activation epoch is empty. -/
theorem activationCohort_processRegistryUpdates_eq_limit {state after : BeaconState preset fork}
    (early : fork < .dencun) (computed : processRegistryUpdates config state = .ok after)
    {epoch : Epoch} (finite : epoch ≠ FAR_FUTURE_EPOCH)
    (atNext : epoch.toNat = nextActivationEpoch state)
    (empty : activationCohort state epoch = 0) :
    ∃ updated, (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state =
        .ok updated ∧
      ((getValidatorChurnLimit config updated).toNat ≤ (activationQueue updated).length →
        activationCohort after epoch = (getValidatorChurnLimit config updated).toNat) := by
  obtain ⟨updated, updatedOk, cohort⟩ :=
    activationCohort_processRegistryUpdates (Nat.lt_trans early (by decide)) computed
  refine ⟨updated, updatedOk, fun long => ?_⟩
  have notDeneb : ¬Fork.dencun ≤ fork := Nat.not_le_of_lt early
  rw [cohort epoch finite atNext, empty, Nat.zero_add]
  simp only [notDeneb, ↓reduceIte, List.length_take]
  exact Nat.min_eq_left long

/-- In the minimal configuration, the churn limit is 2 with 64 active validators and 3 with 96.

So 32 more active validators raise the limit by one. -/
theorem getValidatorChurnLimit_minimal {state after : BeaconState preset fork}
    (first : (getActiveValidatorIndices state (getCurrentEpoch state)).length = 64)
    (second : (getActiveValidatorIndices after (getCurrentEpoch after)).length = 96) :
    getValidatorChurnLimit Config.minimal state = 2 ∧
      getValidatorChurnLimit Config.minimal after = 3 := by
  unfold getValidatorChurnLimit
  rw [first, second]
  decide

end EthLib.Consensus
