module

public import EthLib.Consensus.Proofs.Transition.Finality.Churn

/-!
# Realized activation weight

New active weight lies in activation cohorts strictly after the reference epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {p : Preset}

/-- Activity at a later epoch but not a preserved earlier epoch locates activation. -/
theorem finality_activation_window {s : FinalityState p} {v : Validator}
    {earlier : Epoch}
    (later : earlier ≤ getCurrentEpoch s)
    (active : isActiveValidator v (getCurrentEpoch s) = true)
    (absent : isActiveValidator v earlier = false) :
    earlier.toNat < v.activationEpoch.toNat ∧
      v.activationEpoch.toNat ≤ (getCurrentEpoch s).toNat := by
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  have upper := UInt64.le_iff_toNat_le.mp active.1
  have exit := UInt64.lt_iff_toNat_lt.mp active.2
  have order := UInt64.le_iff_toNat_le.mp later
  have lower : ¬v.activationEpoch ≤ earlier := by
    intro h
    have live : isActiveValidator v earlier = true := by
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h, UInt64.lt_iff_toNat_lt.mpr (by omega)⟩
    rw [absent] at live
    contradiction
  have := UInt64.not_le.mp lower
  exact ⟨UInt64.lt_iff_toNat_lt.mp this, upper⟩

/-- Each observed non-reference active position activates inside the observed epoch window. -/
theorem finality_observed_activation_window {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c s : FinalityState p}
    {bs : List (FinalityBlock p)} {i : Nat} {v : Validator}
    (inv : Invariant c) (member : s ∈ finalityObservations cfg checks eng c bs)
    (found : s.validators.data[i]? = some v)
    (active : finalityActive s i = true) (absent : finalityActive c i = false) :
    (getCurrentEpoch c).toNat < v.activationEpoch.toNat ∧
      v.activationEpoch.toNat ≤ (getCurrentEpoch s).toNat := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exactIndex : i.toUInt64.toNat = i :=
    toNat_toUInt64_of_lt (s.validators.bound (by decide)) inside
  have kept := finality_observations_active_indices inv (UInt64.le_refl _) member
  have notEarlier : isActiveValidator v (getCurrentEpoch c) = false := by
    cases flag : isActiveValidator v (getCurrentEpoch c) with
    | false => rfl
    | true =>
      have inS : i.toUInt64 ∈ getActiveValidatorIndices s (getCurrentEpoch c) :=
        (mem_getActiveValidatorIndices (s.validators.bound (by decide))).mpr
          ⟨v, by simpa only [exactIndex] using found, flag⟩
      rw [kept] at inS
      obtain ⟨old, read, live⟩ :=
        (mem_getActiveValidatorIndices (c.validators.bound (by decide))).mp inS
      rw [exactIndex] at read
      have yes : finalityActive c i = true := by
        simpa only [finalityActive, read] using live
      rw [absent] at yes
      contradiction
  apply finality_activation_window
    (UInt64.le_iff_toNat_le.mpr (finality_observations_epoch_ge member))
    (by simpa only [finalityActive, found] using active) notEarlier

/-- The added weight at one observation is bounded by its realized activation cohorts.

The cohort premise is restricted to non-reference active positions, not scheduling calls. -/
theorem finality_observed_additions_weight {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c s after : FinalityState p}
    {bs : List (FinalityBlock p)} {n cap : Nat}
    (inv : Invariant c) (holds : Invariant s)
    (ran : finalityRuns cfg checks eng c bs after)
    (horizon : (getCurrentEpoch after).toNat - (getCurrentEpoch c).toNat ≤ n)
    (member : s ∈ finalityObservations cfg checks eng c bs)
    (cohorts : ∀ e, (getCurrentEpoch c).toNat < e →
      e ≤ (getCurrentEpoch c).toNat + n →
      ((List.range s.validators.data.size).filter (fun i =>
        !finalityActive c i && finalityActive s i &&
        ((s.validators.data[i]?.map (fun v => v.activationEpoch.toNat)).getD 0 == e))).length
        ≤ cap) :
    ((List.range s.validators.data.size).map fun i =>
      if finalityActive c i then 0 else
        if finalityActive s i then finalityEffective s i else 0).sum ≤
      n * cap * p.MAX_EFFECTIVE_BALANCE.toNat := by
  let added := (List.range s.validators.data.size).filter
    (fun i => !finalityActive c i && finalityActive s i)
  have observedUpper := Nat.div_le_div_right (c := p.SLOTS_PER_EPOCH.toNat)
    (finality_observations_slot_le ran member)
  rw [← getCurrentEpoch_toNat, ← getCurrentEpoch_toNat] at observedUpper
  have weighted := finality_weighted_cohort_window added
    (fun i => (s.validators.data[i]?.map (fun v => v.activationEpoch.toNat)).getD 0)
    (finalityEffective s) (getCurrentEpoch c).toNat n cap p.MAX_EFFECTIVE_BALANCE.toNat
  have bound : (added.map (finalityEffective s)).sum ≤
      n * cap * p.MAX_EFFECTIVE_BALANCE.toNat := by
    apply weighted
    · intro i listed
      obtain ⟨inside, flags⟩ := List.mem_filter.mp listed
      have index := List.mem_range.mp inside
      have found : s.validators.data[i]? = some s.validators.data[i] :=
        Array.getElem?_eq_some_iff.mpr ⟨index, rfl⟩
      have flags : finalityActive c i = false ∧ finalityActive s i = true := by
        simpa only [Bool.and_eq_true, Bool.not_eq_true'] using flags
      have window := finality_observed_activation_window inv member found flags.2 flags.1
      simp only [found, Option.map_some, Option.getD_some]
      omega
    · intro i listed
      have index := List.mem_range.mp (List.mem_filter.mp listed).1
      unfold finalityEffective
      simp only [Array.getElem?_eq_getElem index]
      exact UInt64.le_iff_toNat_le.mp
        (holds.effectiveBalancesBounded _ (Array.getElem_mem index))
    · intro e lower upper
      simpa only [added, List.filter_filter, Bool.and_assoc, Bool.and_comm,
        Bool.and_left_comm] using cohorts e lower upper
  have sums : ∀ indices : List Nat,
      (indices.map fun i => if finalityActive c i then 0 else
        if finalityActive s i then finalityEffective s i else 0).sum =
      ((indices.filter (fun i => !finalityActive c i && finalityActive s i)).map
        (finalityEffective s)).sum := by
    intro indices
    induction indices with
    | nil => rfl
    | cons i rest ih =>
      cases hc : finalityActive c i <;> cases hs : finalityActive s i <;>
        simp [hc, hs, ih]
  rw [sums]
  exact bound

/-- One activation assignment adds at most one member to any activation cohort. -/
theorem finality_activateValidator_activationCohort_le {s t : FinalityState p}
    {i : ValidatorIndex} (ran : activateValidator s i = .ok t) (epoch : Epoch) :
    (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length + 1 := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨v, _, assigned, _, rfl⟩ := ran
  simp only [BeaconState.setValidator, Array.toList_set!]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  by_cases inside : i.toNat < s.validators.data.toList.length
  · rw [List.countP_set inside]
    split <;> split <;> omega
  · rw [List.set_eq_of_length_le (by omega)]
    omega

/-- A complete activation fold adds at most its length to a fixed epoch's cohort. -/
theorem finality_fold_activateValidator_activationCohort_le {s t : FinalityState p}
    {indices : List ValidatorIndex}
    (ran : indices.foldlM activateValidator s = .ok t) (epoch : Epoch) :
    (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length + indices.length := by
  induction indices generalizing s with
  | nil => cases ran; omega
  | cons i rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    have one := finality_activateValidator_activationCohort_le first epoch
    have remaining := ih tail
    simp only [List.length_cons]
    omega

/-- A registry pass fills an initially empty activation cohort within its scheduling budget.

The emptiness premise concerns the state after the eligibility and ejection pass.

History must establish it before this lemma can bound a realized cohort. -/
theorem finality_registry_activationCohort_budget {cfg : Config}
    {s t updated : FinalityState p} {epoch : Epoch}
    (ran : processRegistryUpdates cfg s = .ok t)
    (pass : (List.range s.validators.data.size).foldlM (updateRegistryEntry cfg) s =
      .ok updated)
    (empty : (updated.validators.data.toList.filter (·.activationEpoch == epoch)).length = 0) :
    (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤
      (getValidatorChurnLimit cfg updated).toNat := by
  obtain ⟨middle, indices, first, _, budget, activated⟩ :=
    processRegistryUpdates_activation_budget (by decide) ran
  have equal := Except.ok.inj (first.symm.trans pass)
  subst middle
  have counted := finality_fold_activateValidator_activationCohort_le activated epoch
  omega

/-- Replacing a validator without changing activation preserves all activation epochs. -/
theorem finality_activationEpochs_setValidator {s : FinalityState p} {i : Nat}
    {v : Validator} (found : s.validators.data[i]? = some v)
    (w : Validator) (same : w.activationEpoch = v.activationEpoch) :
    (s.setValidator i w).validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch) := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have read := (Array.getElem?_eq_some_iff.mp found).2
  have mappedInside : i < (s.validators.data.toList.map (·.activationEpoch)).length := by
    simpa only [List.length_map, Array.length_toList] using inside
  simp only [BeaconState.setValidator, Array.toList_set!, List.map_set]
  rw [show w.activationEpoch = (s.validators.data.toList.map (·.activationEpoch))[i] by
    simp only [List.getElem_map, Array.getElem_toList, same, read]]
  exact List.set_getElem_self (by simpa using inside)

/-- Starting an exit does not change the list of activation epochs. -/
theorem finality_initiateValidatorExit_activationEpochs {cfg : Config}
    {s t : FinalityState p} {i : ValidatorIndex}
    (ran : initiateValidatorExit cfg s i = .ok t) :
    t.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch) := by
  obtain ⟨old, read, ⟨_, rfl⟩ | ⟨_, queued, allocated, withdrawable, queue, _, rfl⟩⟩ :=
    initiateValidatorExit_ok ran
  · rfl
  have same := exitQueue_state (by decide : Fork.phase0 < .pectra) queue
  subst queued
  have found : s.validators.data[i.toNat]? = some old := by
    unfold getValidator at read
    split at read
    · cases read; assumption
    · cases read
  exact finality_activationEpochs_setValidator found
    { old with exitEpoch := allocated, withdrawableEpoch := withdrawable } rfl

/-- Queue eligibility and ejection do not change the list of activation epochs. -/
theorem finality_updateRegistryEntry_activationEpochs {cfg : Config}
    {s t : FinalityState p} {i : Nat} (inside : i < s.validators.data.size)
    (ran : updateRegistryEntry cfg s i = .ok t) :
    t.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch) := by
  have exactIndex := toNat_toUInt64_of_lt (s.validators.bound (by decide)) inside
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ran
  obtain ⟨v, read, w, queued, rest⟩ := ran
  have same : w.activationEpoch = v.activationEpoch := by
    unfold queueForActivation at queued
    split at queued
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
      obtain ⟨_, _, rfl⟩ := queued
      rfl
    · cases queued; rfl
  have found : s.validators.data[i]? = some v := by
    unfold getValidator at read
    rw [exactIndex] at read
    split at read
    · cases read; assumption
    · cases read
  have kept := finality_activationEpochs_setValidator found w same
  split at rest
  · exact (finality_initiateValidatorExit_activationEpochs
      (liftAccessor_ok.mp rest)).trans kept
  · cases rest; exact kept

/-- The full eligibility pass leaves the activation epochs unchanged. -/
theorem finality_fold_updateRegistryEntry_activationEpochs {cfg : Config}
    {s t : FinalityState p} {indices : List Nat}
    (inside : ∀ i ∈ indices, i < s.validators.data.size)
    (ran : indices.foldlM (updateRegistryEntry cfg) s = .ok t) :
    t.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch) := by
  induction indices generalizing s with
  | nil => cases ran; rfl
  | cons i rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    have sizes := (sameSizes_updateRegistryEntry first).1
    exact (ih (fun j member => by
      rw [sizes]
      exact inside j (List.mem_cons_of_mem _ member)) tail).trans
        (finality_updateRegistryEntry_activationEpochs (inside i List.mem_cons_self) first)

/-- An activation fold preserves cohorts other than the epoch it assigns.

Assignments are checked additions, so their natural-number epoch is exact. -/
theorem finality_fold_activateValidator_otherCohort {s t : FinalityState p}
    {indices : List ValidatorIndex} {epoch : Epoch}
    (other : epoch.toNat ≠ (getCurrentEpoch s).toNat + 1 + p.MAX_SEED_LOOKAHEAD.toNat)
    (finite : epoch ≠ FAR_FUTURE_EPOCH)
    (eligible : ∀ i ∈ indices, ∃ v, getValidator s i = .ok v ∧
      isEligibleForActivation s v = true)
    (distinct : indices.Nodup)
    (ran : indices.foldlM activateValidator s = .ok t) :
    (t.validators.data.toList.filter (·.activationEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length := by
  induction indices generalizing s with
  | nil => cases ran; rfl
  | cons i rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨v, read, allowed⟩ := eligible i List.mem_cons_self
    have fresh : v.activationEpoch = FAR_FUTURE_EPOCH := by
      exact (by simpa only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq]
        using allowed : _ ∧ _).2
    obtain ⟨old, assigned, oldRead, assignedRead, schedule, shape⟩ :=
      activateValidator_scheduled first
    have equal := Except.ok.inj (read.symm.trans oldRead)
    subst old
    have found : s.validators.data[i.toNat]? = some v := by
      unfold getValidator at read
      split at read
      · cases read; assumption
      · cases read
    have one : (middle.validators.data.toList.filter (·.activationEpoch == epoch)).length =
        (s.validators.data.toList.filter (·.activationEpoch == epoch)).length := by
      simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at first
      obtain ⟨old, oldRead, e, computed, rfl⟩ := first
      have oldEq := Except.ok.inj (oldRead.symm.trans read)
      subst old
      have assignedEq : e = assigned.activationEpoch := by
        have readNew := getValidator_setValidator_self read { v with activationEpoch := e }
        have := Except.ok.inj (readNew.symm.trans assignedRead)
        exact congrArg Validator.activationEpoch this
      have notAssigned : e ≠ epoch := by
        intro h
        rw [← assignedEq, h] at schedule
        exact other schedule
      simp only [BeaconState.setValidator, Array.toList_set!]
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
        List.countP_set (by simpa using (Array.getElem?_eq_some_iff.mp found).1)]
      simp only [Array.getElem_toList, (Array.getElem?_eq_some_iff.mp found).2,
        fresh, beq_iff_eq, Ne.symm finite, notAssigned, ↓reduceIte,
        Nat.sub_zero, Nat.add_zero]
    have frame := frame_activateValidator first
    have remaining : ∀ j ∈ rest, ∃ v, getValidator middle j = .ok v ∧
        isEligibleForActivation middle v = true := by
      intro j listed
      obtain ⟨w, found, ok⟩ := eligible j (List.mem_cons_of_mem _ listed)
      have ne : j ≠ i := by
        intro h
        subst j
        exact (List.nodup_cons.mp distinct).1 listed
      have sameFinalized := frame.finalized
      refine ⟨w, ?_, ?_⟩
      · simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
          Except.ok.injEq] at first
        obtain ⟨_, _, _, _, rfl⟩ := first
        exact (getValidator_setValidator_of_ne ne _).trans found
      · simpa only [isEligibleForActivation, sameFinalized] using ok
    exact (ih (by simpa only [getCurrentEpoch, frame.slot] using other)
      remaining distinct.tail tail).trans one

/-- Equal lists of activation epochs give equal cohort counts. -/
theorem finality_activationCohort_of_epochs {s t : FinalityState p}
    (same : t.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch)) (epoch : Epoch) :
    (t.validators.data.toList.filter (·.activationEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length := by
  have count (vs : List Validator) :
      (vs.filter (·.activationEpoch == epoch)).length =
        ((vs.map (·.activationEpoch)).filter (· == epoch)).length := by
    induction vs with
    | nil => rfl
    | cons v vs ih =>
      by_cases h : v.activationEpoch = epoch <;> simp [h, ih]
  rw [count, count, same]

/-- A registry pass can fill only its fresh scheduled activation epoch.

History must show that epoch was empty, rather than merely bound the pass length. -/
theorem finality_processRegistryUpdates_activationCohort {cfg : Config}
    {s t : FinalityState p} {cap : Nat}
    (bounded : ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap)
    (fresh : ∀ epoch, epoch.toNat = (getCurrentEpoch s).toNat + 1 +
      p.MAX_SEED_LOOKAHEAD.toNat → epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length = 0)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : processRegistryUpdates cfg s = .ok t) :
    ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap := by
  obtain ⟨updated, indices, pass, indicesEq, budget, activated⟩ :=
    processRegistryUpdates_activation_budget (by decide) ran
  have kept := finality_fold_updateRegistryEntry_activationEpochs
    (fun _ member => List.mem_range.mp member) pass
  have frame := Frame.foldlM (fun _ _ _ ok => frame_updateRegistryEntry ok) pass
  have equalSize : updated.validators.data.size = s.validators.data.size := by
    simpa only [List.length_map, Array.length_toList] using congrArg List.length kept
  intro epoch nonzero finite
  by_cases assigned : epoch.toNat = (getCurrentEpoch s).toNat + 1 +
      p.MAX_SEED_LOOKAHEAD.toNat
  · have empty := (finality_activationCohort_of_epochs kept epoch).trans
      (fresh epoch assigned finite)
    exact Nat.le_trans (finality_registry_activationCohort_budget ran pass empty)
      (limit updated equalSize)
  · have others := finality_fold_activateValidator_otherCohort
      (by simpa only [getCurrentEpoch, frame.slot] using assigned) finite
      (fun i member => getValidator_of_mem_activationQueue (updated.validators.bound (by decide))
        (List.mem_of_mem_take (indicesEq ▸ member)))
      (indicesEq ▸ (activationQueue_nodup (updated.validators.bound (by decide))).take) activated
    rw [others, finality_activationCohort_of_epochs kept epoch]
    exact bounded epoch nonzero finite

/-- No finite activation is scheduled beyond the largest epoch assigned so far. -/
def FinalityActivationFrontier (s : FinalityState p) (last : Nat) : Prop :=
  ∀ v ∈ s.validators.data, v.activationEpoch ≠ FAR_FUTURE_EPOCH →
    v.activationEpoch.toNat ≤ last

/-- The activation frontier proves that every later finite cohort is empty. -/
theorem FinalityActivationFrontier.empty {s : FinalityState p} {last : Nat}
    (frontier : FinalityActivationFrontier s last) {epoch : Epoch}
    (finite : epoch ≠ FAR_FUTURE_EPOCH) (later : last < epoch.toNat) :
    (s.validators.data.toList.filter (·.activationEpoch == epoch)).length = 0 := by
  have empty : s.validators.data.toList.filter (·.activationEpoch == epoch) = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v member
    obtain ⟨inside, same⟩ := List.mem_filter.mp member
    have equal := beq_iff_eq.mp same
    have bound := frontier v (by simpa using inside) (equal ▸ finite)
    rw [equal] at bound
    omega
  rw [empty]
  rfl

/-- Lists with the same activation epochs have the same frontier. -/
theorem FinalityActivationFrontier.of_epochs {s t : FinalityState p} {last : Nat}
    (frontier : FinalityActivationFrontier s last)
    (same : t.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch)) :
    FinalityActivationFrontier t last := by
  intro v inside finite
  have member : v.activationEpoch ∈ t.validators.data.toList.map (·.activationEpoch) :=
    List.mem_map.mpr ⟨v, by simpa using inside, rfl⟩
  rw [same] at member
  obtain ⟨w, found, equal⟩ := List.mem_map.mp member
  have bound := frontier w (by simpa using found) (equal ▸ finite)
  rwa [equal] at bound

/-- One activation assignment advances the frontier to its checked assigned epoch. -/
theorem finality_activateValidator_frontier {s t : FinalityState p}
    {i : ValidatorIndex} {last : Nat}
    (frontier : FinalityActivationFrontier s last)
    (assigned : (getCurrentEpoch s).toNat + 1 + p.MAX_SEED_LOOKAHEAD.toNat ≤ last)
    (ran : activateValidator s i = .ok t) : FinalityActivationFrontier t last := by
  obtain ⟨_, v, _, found, scheduled, _⟩ := activateValidator_scheduled ran
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨old, read, epoch, _, rfl⟩ := ran
  have readNew := getValidator_setValidator_self read { old with activationEpoch := epoch }
  have equal := Except.ok.inj (readNew.symm.trans found)
  have schedule : epoch.toNat = (getCurrentEpoch s).toNat + 1 + p.MAX_SEED_LOOKAHEAD.toNat := by
    simpa only [← equal] using scheduled
  intro w member finite
  simp only [BeaconState.setValidator, Array.mem_def, Array.toList_set!] at member
  obtain original | replaced := List.mem_or_eq_of_mem_set member
  · exact frontier w (by simpa using original) finite
  · subst w
    change epoch.toNat ≤ last
    omega

/-- An activation fold cannot schedule beyond the pass's assigned epoch. -/
theorem finality_fold_activateValidator_frontier {s t : FinalityState p}
    {indices : List ValidatorIndex} {last : Nat}
    (frontier : FinalityActivationFrontier s last)
    (assigned : (getCurrentEpoch s).toNat + 1 + p.MAX_SEED_LOOKAHEAD.toNat ≤ last)
    (ran : indices.foldlM activateValidator s = .ok t) : FinalityActivationFrontier t last := by
  induction indices generalizing s with
  | nil => cases ran; exact frontier
  | cons i rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    exact ih (finality_activateValidator_frontier frontier assigned first)
      (by simpa only [getCurrentEpoch, activateValidator_slot first] using assigned) tail

/-- A registry pass advances the finite activation frontier by its checked scheduling delay. -/
theorem finality_processRegistryUpdates_frontier {cfg : Config} {s t : FinalityState p}
    {last : Nat} (frontier : FinalityActivationFrontier s last)
    (assigned : (getCurrentEpoch s).toNat + 1 + p.MAX_SEED_LOOKAHEAD.toNat ≤ last)
    (ran : processRegistryUpdates cfg s = .ok t) : FinalityActivationFrontier t last := by
  obtain ⟨updated, _, pass, _, _, activated⟩ :=
    processRegistryUpdates_activation_budget (by decide) ran
  have kept := finality_fold_updateRegistryEntry_activationEpochs
    (fun _ member => List.mem_range.mp member) pass
  have frame := Frame.foldlM (fun _ _ _ ok => frame_updateRegistryEntry ok) pass
  exact finality_fold_activateValidator_frontier (frontier.of_epochs kept)
    (by simpa only [getCurrentEpoch, frame.slot] using assigned) activated

/-- A registry pass creates one bounded cohort beyond the old finite frontier.

Genesis epoch zero is exempt because genesis activates its entire initial set. -/
theorem finality_processRegistryUpdates_activation_history {cfg : Config}
    {s t : FinalityState p} {cap : Nat}
    (frontier : FinalityActivationFrontier s
      ((getCurrentEpoch s).toNat + p.MAX_SEED_LOOKAHEAD.toNat))
    (bounded : ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : processRegistryUpdates cfg s = .ok t) :
    FinalityActivationFrontier t
      ((getCurrentEpoch s).toNat + 1 + p.MAX_SEED_LOOKAHEAD.toNat) ∧
    ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap := by
  refine ⟨finality_processRegistryUpdates_frontier ?_ (Nat.le_refl _) ran,
    finality_processRegistryUpdates_activationCohort bounded ?_ limit ran⟩
  · intro v member finite
    have := frontier v member finite
    omega
  · intro epoch assigned finite
    exact frontier.empty finite (by omega)

end EthLib.Consensus
