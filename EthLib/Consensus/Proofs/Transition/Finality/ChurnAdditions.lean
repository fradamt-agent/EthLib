module

public import EthLib.Consensus.Proofs.Transition.Finality.Churn

/-!
# Realized activation weight

New active weight lies in activation cohorts strictly after the reference epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

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

/-- Effective-balance hysteresis leaves the activation epochs unchanged. -/
theorem finality_processEffectiveBalanceUpdates_activationEpochs {s t : FinalityState p}
    (ran : processEffectiveBalanceUpdates s = .ok t) :
    t.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch) := by
  simp only [processEffectiveBalanceUpdates, show ¬Fork.pectra ≤ Fork.phase0 by decide,
    ↓reduceIte] at ran
  have step : ∀ (a b : FinalityState p) i, i < a.validators.data.size →
      updateEffectiveBalance a i = .ok b →
      b.validators.data.toList.map (·.activationEpoch) =
        a.validators.data.toList.map (·.activationEpoch) := by
    intro a b i inside ok
    have exactIndex := toNat_toUInt64_of_lt (a.validators.bound (by decide)) inside
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at ok
    obtain ⟨v, read, _, _, balance, _, rfl⟩ := ok
    have found : a.validators.data[i]? = some v := by
      unfold getValidator at read
      rw [exactIndex] at read
      split at read
      · cases read; assumption
      · cases read
    exact finality_activationEpochs_setValidator found { v with effectiveBalance := balance } rfl
  have pass : ∀ (indices : List Nat) (a b : FinalityState p),
      (∀ i ∈ indices, i < a.validators.data.size) →
      indices.foldlM updateEffectiveBalance a = .ok b →
      b.validators.data.toList.map (·.activationEpoch) =
        a.validators.data.toList.map (·.activationEpoch) := by
    intro indices
    induction indices with
    | nil => intro a b _ ok; cases ok; rfl
    | cons i rest ih =>
      intro a b inside ok
      obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ok
      have sizes := (sameSizes_updateEffectiveBalance first).1
      exact (ih middle b (fun j member => by
        rw [sizes]
        exact inside j (List.mem_cons_of_mem _ member)) tail).trans
          (step a middle i (inside i List.mem_cons_self) first)
  exact pass _ s t (fun _ member => List.mem_range.mp member) ran

/-- Epoch processing creates a bounded activation cohort and advances its finite frontier. -/
theorem finality_processEpoch_activation_history {cfg : Config}
    {s t : FinalityState p} {cap : Nat} (inv : Invariant s)
    (frontier : FinalityActivationFrontier s
      ((getCurrentEpoch s).toNat + p.MAX_SEED_LOOKAHEAD.toNat))
    (bounded : ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : processEpoch cfg s = .ok t) :
    FinalityActivationFrontier t
      ((getCurrentEpoch s).toNat + 1 + p.MAX_SEED_LOOKAHEAD.toNat) ∧
    ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap := by
  simp only [processEpoch, show ¬Fork.altair ≤ Fork.phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at ran
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := ran
  obtain ⟨_, _, _, justifiedSlot, justifiedRegistry, _⟩ :=
    processJustificationAndFinalization_invariant inv.ordered inv.settled justifiedOk
  have rewardedRegistry :=
    (processRewardsAndPenalties_validators rewardedOk).trans justifiedRegistry
  have rewardedSlot := (frame_processRewardsAndPenalties rewardedOk).slot.trans justifiedSlot
  have history := finality_processRegistryUpdates_activation_history
    (s := rewarded) (by
      simpa only [FinalityActivationFrontier, getCurrentEpoch, rewardedSlot, rewardedRegistry]
        using frontier)
    (by simpa only [rewardedRegistry] using bounded)
    (fun u same => limit u (by simpa only [rewardedRegistry] using same)) registeredOk
  have clearedRegistry : cleared.validators = balanced.validators := by
    obtain ⟨_, _, rfl⟩ := processSlashingsReset_eq clearedOk
    rfl
  have mixedRegistry : mixed.validators = cleared.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    rfl
  have same : t.validators.data.toList.map (·.activationEpoch) =
      registered.validators.data.toList.map (·.activationEpoch) := by
    rw [processParticipationRecordUpdates_validators rotated,
      processHistoricalRootsUpdate_validators rootedOk, mixedRegistry, clearedRegistry,
      finality_processEffectiveBalanceUpdates_activationEpochs balancedOk,
      processEth1DataReset_validators resetOk, processSlashings_validators slashedOk]
  refine ⟨?_, ?_⟩
  · have front := history.1.of_epochs same
    simpa only [getCurrentEpoch, rewardedSlot] using front
  · intro epoch nonzero finite
    rw [finality_activationCohort_of_epochs same epoch]
    exact history.2 epoch nonzero finite

/-- Slashing changes exit and withdrawal data but not activation epochs. -/
theorem finality_slashValidator_activationEpochs {cfg : Config}
    {s t : FinalityState p} {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ran : slashValidator cfg s i whistleblower = .ok t) :
    t.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch) := by
  unfold slashValidator at ran
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at ran
  obtain ⟨exited, exitedOk, validator, found, withdrawable, _, _, _, _, _, _, lowered,
    _, _, _, _, _, raised, _, final, done⟩ := ran
  have same := (slashValidator_last done).1.trans ((increaseBalance_validators final).trans
    ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered)))
  have read : exited.validators.data[i.toNat]? = some validator := by
    unfold getValidator at found
    split at found
    · cases found; assumption
    · cases found
  let marked := { validator with
    slashed := true
    withdrawableEpoch := max validator.withdrawableEpoch withdrawable }
  rw [same, finality_activationEpochs_setValidator read marked rfl]
  exact finality_initiateValidatorExit_activationEpochs exitedOk

/-- A proposer-slashing operation preserves activation epochs. -/
theorem finality_processProposerSlashing_activationEpochs {cfg : Config}
    {checks : SignatureChecks} {s t : FinalityState p} {slashing : ProposerSlashing}
    (ran : processProposerSlashing cfg checks s slashing = .ok t) :
    t.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch) := by
  unfold processProposerSlashing at ran
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ran
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ran
  exact finality_slashValidator_activationEpochs slashed

/-- Conditional slashing preserves activation epochs. -/
theorem finality_slashIfSlashable_activationEpochs {cfg : Config}
    {s t : FinalityState p × Bool} {i : ValidatorIndex}
    (ran : slashIfSlashable cfg s i = .ok t) :
    t.1.validators.data.toList.map (·.activationEpoch) =
      s.1.validators.data.toList.map (·.activationEpoch) := by
  obtain ⟨s, flag⟩ := s
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ran
  obtain ⟨v, _, rest⟩ := ran
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨_, slashed, rfl⟩ := rest
    exact finality_slashValidator_activationEpochs slashed
  · cases rest; rfl

/-- An attester slashing preserves activation epochs through its actual index fold. -/
theorem finality_processAttesterSlashing_activationEpochs {cfg : Config}
    {checks : SignatureChecks} {s t : FinalityState p} {a : AttesterSlashing p .phase0}
    (ran : processAttesterSlashing cfg checks s a = .ok t) :
    t.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch) := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ran
  exact foldlM_ok_invariant
    (fun u : FinalityState p × Bool => u.1.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch))
    (fun _ _ _ previous ok => (finality_slashIfSlashable_activationEpochs ok).trans previous)
    rfl folded

/-- A voluntary exit preserves activation epochs. -/
theorem finality_processVoluntaryExit_activationEpochs {cfg : Config}
    {checks : SignatureChecks} {s t : FinalityState p} {a : SignedVoluntaryExit}
    (ran : processVoluntaryExit cfg checks s a = .ok t) :
    t.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch) := by
  simp only [processVoluntaryExit, show ¬Fork.pectra ≤ Fork.phase0 by decide,
    ↓reduceIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ran
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ran
  exact finality_initiateValidatorExit_activationEpochs exited

/-- Deposits preserve finite activation cohorts. -/
theorem finality_applyDeposit_activation_history {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {key : BLSPubkey} {credentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (ran : applyDeposit cfg checks s key credentials amount signature = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length =
        (s.validators.data.toList.filter (·.activationEpoch == epoch)).length := by
  simp only [applyDeposit, show ¬Fork.pectra ≤ Fork.phase0 by decide, ↓reduceDIte,
    applyPendingDeposit] at ran
  split at ran
  · simp only [bind_ok_iff] at ran
    obtain ⟨_, _, ran⟩ := ran
    split at ran
    · simp only [addValidatorToRegistry, show ¬Fork.altair ≤ Fork.phase0 by decide,
        ↓reduceDIte] at ran
      split at ran
      · cases ran
        intro epoch finite
        simp [Array.toList_push, getValidatorFromDeposit, Ne.symm finite]
      · cases ran
    · cases ran
      intro _ _; rfl
  · rw [increaseBalance_validators (liftAccessor_ok.mp ran)]
    intro _ _; rfl

/-- Preserving every finite activation cohort preserves the finite frontier. -/
theorem FinalityActivationFrontier.of_cohorts {s t : FinalityState p} {last : Nat}
    (frontier : FinalityActivationFrontier s last)
    (same : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length =
        (s.validators.data.toList.filter (·.activationEpoch == epoch)).length) :
    FinalityActivationFrontier t last := by
  intro v member finite
  by_contra h
  have empty := frontier.empty finite (by omega)
  have present : v ∈ t.validators.data.toList.filter
      (·.activationEpoch == v.activationEpoch) := by
    simp only [List.mem_filter, beq_self_eq_true, and_true]
    simpa using member
  have positive := List.length_pos_of_mem present
  rw [same _ finite, empty] at positive
  omega

/-- A checked deposit preserves all finite activation cohorts. -/
theorem finality_processDeposit_activationCohort {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {deposit : Deposit}
    (ran : processDeposit cfg checks (by decide) s deposit = .ok t)
    {epoch : Epoch} (finite : epoch ≠ FAR_FUTURE_EPOCH) :
    (t.validators.data.toList.filter (·.activationEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok ran
  exact finality_applyDeposit_activation_history applied epoch finite

/-- Phase 0 block operations preserve every finite activation cohort. -/
theorem finality_processOperations_activationCohort {cfg : Config}
    {checks : SignatureChecks} {s t : FinalityState p} {body : BeaconBlockBody p .phase0}
    (ran : processOperations cfg checks s body = .ok t)
    {epoch : Epoch} (finite : epoch ≠ FAR_FUTURE_EPOCH) :
    (t.validators.data.toList.filter (·.activationEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length := by
  unfold processOperations at ran
  split at ran
  · cases ran
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ran
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := ran
  simp only [show ¬Fork.shapella ≤ Fork.phase0 by decide, ↓reduceDIte,
    pure, Except.pure, Except.ok.injEq] at changesOk
  subst t
  have one := foldlM_ok_invariant
    (fun u : FinalityState p => u.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch))
    (fun _ _ _ prior ok => (finality_processProposerSlashing_activationEpochs ok).trans prior)
    rfl proposersOk
  have two := foldlM_ok_invariant
    (fun u : FinalityState p => u.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch))
    (fun _ _ _ prior ok => (finality_processAttesterSlashing_activationEpochs ok).trans prior)
    one attestersOk
  have three := foldlM_ok_invariant
    (fun u : FinalityState p => u.validators.data.toList.map (·.activationEpoch) =
      s.validators.data.toList.map (·.activationEpoch))
    (fun before a _ prior ok => by
      obtain ⟨_, _, _, _, _, recorded, _, _, _⟩ := processAttestation_records (by decide) ok
      cases current : a.data.target.epoch == getCurrentEpoch before <;>
        simp only [recordPendingAttestation, current, Bool.false_eq_true,
          ↓reduceIte] at recorded <;>
        split at recorded <;> cases recorded <;> exact prior) two attestedOk
  have four := foldlM_ok_invariant
    (fun u : FinalityState p =>
      (u.validators.data.toList.filter (·.activationEpoch == epoch)).length =
        (s.validators.data.toList.filter (·.activationEpoch == epoch)).length)
    (fun _ _ _ prior ok => (finality_processDeposit_activationCohort ok finite).trans prior)
    (finality_activationCohort_of_epochs three epoch) depositedOk
  have five := foldlM_ok_invariant
    (fun u : FinalityState p => u.validators.data.toList.map (·.activationEpoch) =
      deposited.validators.data.toList.map (·.activationEpoch))
    (fun _ _ _ prior ok => (finality_processVoluntaryExit_activationEpochs ok).trans prior)
    rfl exitsOk
  exact (finality_activationCohort_of_epochs five epoch).trans four

/-- A Phase 0 block preserves all finite activation cohorts. -/
theorem finality_processBlock_activationCohort {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {b : BeaconBlock p .phase0}
    (ran : processBlock cfg checks eng s b = .ok t)
    {epoch : Epoch} (finite : epoch ≠ FAR_FUTURE_EPOCH) :
    (t.validators.data.toList.filter (·.activationEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length := by
  simp only [processBlock, show ¬Fork.altair ≤ Fork.phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at ran
  obtain ⟨header, headerOk, randao, randaoOk, eth1, eth1Ok, operationsOk⟩ := ran
  have headerRegistry : header.validators = s.validators := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    rfl
  have randaoRegistry : randao.validators = header.validators := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
    rfl
  have eth1Registry : eth1.validators = randao.validators :=
    congrArg (fun u => u.validators) (processEth1Data_eq eth1Ok).2.2
  simpa only [eth1Registry, randaoRegistry, headerRegistry] using
    finality_processOperations_activationCohort operationsOk finite

/-- Positive slots make the last-slot epoch step advance the epoch by exactly one. -/
theorem finality_epoch_boundary {s : FinalityState p} {next : Slot}
    (_positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (step : next.toNat = s.slot.toNat + 1)
    (boundary : next % p.SLOTS_PER_EPOCH = 0) :
    (computeEpochAtSlot p next).toNat = (getCurrentEpoch s).toNat + 1 := by
  have modulo : next.toNat % p.SLOTS_PER_EPOCH.toNat = 0 := by
    simpa only [UInt64.toNat_mod, UInt64.toNat_zero] using congrArg UInt64.toNat boundary
  rw [getCurrentEpoch_toNat]
  simp only [computeEpochAtSlot, UInt64.toNat_div]
  rw [step] at modulo ⊢
  exact Nat.succ_div_of_mod_eq_zero modulo

/-- One slot preserves the activation history bound after moving to its next epoch. -/
theorem finality_advanceSlot_activation_history {cfg : Config}
    {s t : FinalityState p} {cap : Nat} (inv : Invariant s)
    (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (frontier : FinalityActivationFrontier s
      ((getCurrentEpoch s).toNat + p.MAX_SEED_LOOKAHEAD.toNat))
    (bounded : ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : advanceSlot cfg s = .ok t) :
    FinalityActivationFrontier t
      ((getCurrentEpoch t).toNat + p.MAX_SEED_LOOKAHEAD.toNat) ∧
    ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap := by
  have step := advanceSlot_slot ran
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ran
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := ran
  change next.toNat = s.slot.toNat + 1 at step
  have cacheRegistry : cached.validators = s.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have cacheSlot := (frame_processSlot cachedOk).slot
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have boundaryEpoch := finality_epoch_boundary (s := s) positive step boundary
    have history := finality_processEpoch_activation_history
      ((frame_processSlot cachedOk).invariant inv)
      (by simpa only [FinalityActivationFrontier, getCurrentEpoch, cacheSlot, cacheRegistry]
        using frontier)
      (by simpa only [cacheRegistry] using bounded)
      (fun u same => limit u (by simpa only [cacheRegistry] using same)) epochedOk
    refine ⟨?_, history.2⟩
    simpa only [FinalityActivationFrontier, getCurrentEpoch, cacheSlot, boundaryEpoch,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using history.1
  · cases epochedOk
    refine ⟨?_, ?_⟩
    · have epochLe := Nat.div_le_div_right (c := p.SLOTS_PER_EPOCH.toNat)
        (show s.slot.toNat ≤ next.toNat by omega)
      intro v member finite
      have oldMember : v ∈ s.validators.data := by
        simpa only [cacheRegistry] using member
      have bound := frontier v oldMember finite
      change v.activationEpoch.toNat ≤
        (computeEpochAtSlot p next).toNat + p.MAX_SEED_LOOKAHEAD.toNat
      simp only [computeEpochAtSlot, UInt64.toNat_div] at *
      rw [getCurrentEpoch_toNat] at bound
      omega
    · simpa only [cacheRegistry] using bounded

/-- Empty-slot advancement preserves bounded historical activation cohorts. -/
theorem finality_advanceSlots_activation_history {cfg : Config}
    {s t : FinalityState p} {count cap : Nat} (inv : Invariant s)
    (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (frontier : FinalityActivationFrontier s
      ((getCurrentEpoch s).toNat + p.MAX_SEED_LOOKAHEAD.toNat))
    (bounded : ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : advanceSlots cfg count s = .ok t) :
    FinalityActivationFrontier t
      ((getCurrentEpoch t).toNat + p.MAX_SEED_LOOKAHEAD.toNat) ∧
    ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap := by
  induction count generalizing s with
  | zero => cases ran; exact ⟨frontier, bounded⟩
  | succ count ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    have next := finality_advanceSlot_activation_history inv positive frontier bounded limit first
    have sizes := finality_advanceSlots_size (count := 1) (by simpa [advanceSlots] using first)
    exact ih (advanceSlot_invariant (by decide) inv first).1 next.1 next.2
      (fun u same => limit u (same.trans sizes)) tail

/-- A validated block transition preserves the finite activation history. -/
theorem finality_stateTransition_activation_history {cfg : Config}
    {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {s t : FinalityState p} {b : FinalityBlock p} {population cap : Nat}
    (inv : Invariant s) (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (frontier : FinalityActivationFrontier s
      ((getCurrentEpoch s).toNat + p.MAX_SEED_LOOKAHEAD.toNat))
    (bounded : ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap)
    (size : t.validators.data.size ≤ population)
    (limit : ∀ u : FinalityState p, u.validators.data.size ≤ population →
      (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : stateTransition cfg checks eng s b true = .ok t) :
    FinalityActivationFrontier t
      ((getCurrentEpoch t).toNat + p.MAX_SEED_LOOKAHEAD.toNat) ∧
    ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap := by
  have startSize := Nat.le_trans (finality_stateTransition_registry inv ran).1 size
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok ran
  have slots := slotsOk
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slots
  obtain ⟨_, _, advancedOk⟩ := slots
  have history := finality_advanceSlots_activation_history inv positive frontier bounded
    (fun u same => limit u (same ▸ startSize)) advancedOk
  have blockSlot := (frame_processBlock (by decide) blockOk).slot
  refine ⟨?_, ?_⟩
  · have kept := history.1.of_cohorts (fun _ finite =>
      finality_processBlock_activationCohort blockOk finite)
    simpa only [getCurrentEpoch, blockSlot] using kept
  · intro epoch nonzero finite
    rw [finality_processBlock_activationCohort blockOk finite]
    exact history.2 epoch nonzero finite

/-- A validated chain preserves nonzero finite activation-cohort caps. -/
theorem finality_runs_activation_history {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p}
    {bs : List (FinalityBlock p)} {population cap : Nat}
    (inv : Invariant s) (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (frontier : FinalityActivationFrontier s
      ((getCurrentEpoch s).toNat + p.MAX_SEED_LOOKAHEAD.toNat))
    (bounded : ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap)
    (size : t.validators.data.size ≤ population)
    (limit : ∀ u : FinalityState p, u.validators.data.size ≤ population →
      (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : finalityRuns cfg checks eng s bs t) :
    FinalityActivationFrontier t
      ((getCurrentEpoch t).toNat + p.MAX_SEED_LOOKAHEAD.toNat) ∧
    ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap := by
  induction bs generalizing s with
  | nil => cases ran; exact ⟨frontier, bounded⟩
  | cons b bs ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    have middleInv := finality_runs_invariant inv (bs := [b])
      (by simpa [finalityRuns] using first)
    have middleSize := Nat.le_trans (finality_runs_registry middleInv tail).1 size
    have history := finality_stateTransition_activation_history inv positive frontier bounded
      middleSize limit first
    exact ih middleInv history.1 history.2 tail

/-- Genesis activation cannot create a nonzero finite activation cohort. -/
theorem finality_activateAtGenesis_activationCohort {s t : FinalityState p} {i : Nat}
    {epoch : Epoch} (nonzero : epoch ≠ 0) (_finite : epoch ≠ FAR_FUTURE_EPOCH)
    (ran : activateAtGenesis s i = .ok t)
    (empty : (s.validators.data.toList.filter (·.activationEpoch == epoch)).length = 0) :
    (t.validators.data.toList.filter (·.activationEpoch == epoch)).length = 0 := by
  simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨v, read, balance, _, rfl⟩ := ran
  by_cases inside : i < s.validators.data.size
  · have exactIndex := toNat_toUInt64_of_lt (s.validators.bound (by decide)) inside
    have found : s.validators.data[i]? = some v := by
      unfold getValidator at read
      rw [exactIndex] at read
      split at read
      · cases read; assumption
      · cases read
    split
    · simp only [BeaconState.setValidator, Array.toList_set!]
      rw [← List.countP_eq_length_filter, List.countP_set (by simpa using inside)]
      have zeroCount : s.validators.data.toList.countP (·.activationEpoch == epoch) = 0 := by
        simpa only [List.countP_eq_length_filter] using empty
      simp only [zeroCount, GENESIS_EPOCH, beq_iff_eq, Ne.symm nonzero, ↓reduceIte,
        Nat.zero_sub, Nat.add_zero]
    · let effective := min (balance - balance % p.EFFECTIVE_BALANCE_INCREMENT)
        p.MAX_EFFECTIVE_BALANCE
      rw [finality_activationCohort_of_epochs
        (finality_activationEpochs_setValidator found
          { v with effectiveBalance := effective } rfl) epoch]
      exact empty
  · simp only [BeaconState.setValidator, Array.toList_set!]
    rw [List.set_eq_of_length_le (by simpa using Nat.le_of_not_gt inside)]
    exact empty

/-- Genesis has no nonzero finite activation cohorts.

The full initial active set belongs to epoch zero, which is excluded. -/
theorem finality_initialized_activationCohort {cfg : Config} {checks : SignatureChecks}
    {g : FinalityState p} (initialized : finalityInitialized cfg checks g)
    {epoch : Epoch} (nonzero : epoch ≠ 0) (finite : epoch ≠ FAR_FUTURE_EPOCH) :
    (g.validators.data.toList.filter (·.activationEpoch == epoch)).length = 0 := by
  obtain ⟨⟨hash, time, deposits, ran⟩, _⟩ := initialized
  simp only [initializeBeaconStateFromEth1, show ¬Fork.altair ≤ Fork.phase0 by decide,
    ↓reduceDIte, bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, _, _, rfl⟩ := ran
  have initial : ∀ (a b : FinalityState p) entry,
      genesisDeposit cfg checks (by decide) (deposits.map (·.data)) a entry = .ok b →
      (b.validators.data.toList.filter (·.activationEpoch == epoch)).length =
        (a.validators.data.toList.filter (·.activationEpoch == epoch)).length := by
    intro a b entry ok
    simp only [genesisDeposit, bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    exact finality_processDeposit_activationCohort applied finite
  have depositedZero := foldlM_ok_invariant
    (fun u : FinalityState p =>
      (u.validators.data.toList.filter (·.activationEpoch == epoch)).length = 0)
    (fun _ _ _ previous ok => (initial _ _ _ ok).trans previous)
    (by simp [emptyGenesisState]) depositedOk
  change (activated.validators.data.toList.filter (·.activationEpoch == epoch)).length = 0
  exact foldlM_ok_invariant
    (fun u : FinalityState p =>
      (u.validators.data.toList.filter (·.activationEpoch == epoch)).length = 0)
    (fun _ _ _ previous ok =>
      finality_activateAtGenesis_activationCohort nonzero finite ok previous)
    depositedZero activatedOk

/-- All finite genesis activation epochs are zero. -/
theorem finality_initialized_activation_frontier {cfg : Config} {checks : SignatureChecks}
    {g : FinalityState p} (initialized : finalityInitialized cfg checks g) :
    FinalityActivationFrontier g ((getCurrentEpoch g).toNat + p.MAX_SEED_LOOKAHEAD.toNat) := by
  intro v member finite
  by_cases zero : v.activationEpoch = 0
  · simp [zero]
  · have empty := finality_initialized_activationCohort initialized zero finite
    have present : v ∈ g.validators.data.toList.filter
        (·.activationEpoch == v.activationEpoch) := by
      simp only [List.mem_filter, beq_self_eq_true, and_true]
      simpa using member
    have positive := List.length_pos_of_mem present
    omega

/-- Reachability from genesis bounds every nonzero finite activation cohort. -/
theorem finality_reachable_activation_history {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {g t : FinalityState p}
    {bs : List (FinalityBlock p)} {population cap : Nat}
    (initialized : finalityInitialized cfg checks g)
    (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (ran : finalityRuns cfg checks eng g bs t)
    (size : t.validators.data.size ≤ population)
    (limit : ∀ u : FinalityState p, u.validators.data.size ≤ population →
      (getValidatorChurnLimit cfg u).toNat ≤ cap) :
    FinalityActivationFrontier t
      ((getCurrentEpoch t).toNat + p.MAX_SEED_LOOKAHEAD.toNat) ∧
    ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap := by
  obtain ⟨_, _, _, genesis⟩ := initialized.1
  exact finality_runs_activation_history (initializeBeaconStateFromEth1_invariant genesis).2
    positive (finality_initialized_activation_frontier initialized)
    (fun epoch nonzero finite => by
      rw [finality_initialized_activationCohort initialized nonzero finite]
      omega) size limit ran

/-- Every collected weighing state inherits the bounded activation history. -/
theorem finality_observations_activation_history {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t : FinalityState p} {bs : List (FinalityBlock p)}
    {population cap : Nat} (inv : Invariant c)
    (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (frontier : FinalityActivationFrontier c
      ((getCurrentEpoch c).toNat + p.MAX_SEED_LOOKAHEAD.toNat))
    (bounded : ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (c.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap)
    (size : t.validators.data.size ≤ population)
    (limit : ∀ u : FinalityState p, u.validators.data.size ≤ population →
      (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (member : t ∈ finalityObservations cfg checks eng c bs) :
    ∀ epoch, epoch ≠ 0 → epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.activationEpoch == epoch)).length ≤ cap := by
  simp only [finalityObservations, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨⟨b, i⟩, _, member⟩
  · exact bounded
  cases prefixOk : (bs.take i).foldlM (fun s b => stateTransition cfg checks eng s b true) c with
  | error e => simp [prefixOk] at member
  | ok before =>
    simp only [prefixOk, List.mem_append, List.mem_cons, List.mem_flatMap] at member
    have holds := finality_runs_invariant inv prefixOk
    rcases member with output | rfl | ⟨count, _, member⟩
    · cases block : stateTransition cfg checks eng before b true with
      | error e => simp [block, Except.toOption] at output
      | ok after =>
        simp only [block, Except.toOption, Option.toList, List.mem_singleton] at output
        subst t
        have beforeSize := Nat.le_trans (finality_stateTransition_registry holds block).1 size
        have previous := finality_runs_activation_history inv positive frontier bounded
          beforeSize limit prefixOk
        exact (finality_stateTransition_activation_history holds positive previous.1 previous.2
          size limit block).2
    · exact (finality_runs_activation_history inv positive frontier bounded size limit prefixOk).2
    · cases slots : advanceSlots cfg count before with
      | error e => simp [slots] at member
      | ok atStep =>
        simp only [slots, List.mem_cons] at member
        have sameSize := finality_advanceSlots_size slots
        rcases member with rfl | member
        · have beforeSize : before.validators.data.size ≤ population := by
            rwa [sameSize] at size
          have previous := finality_runs_activation_history inv positive frontier bounded
            beforeSize limit prefixOk
          exact (finality_advanceSlots_activation_history holds positive previous.1 previous.2
            (fun u same => limit u (same ▸ beforeSize)) slots).2
        · cases cache : processSlot atStep with
          | error e => simp [cache, Except.toOption] at member
          | ok cached =>
            simp only [cache, Except.toOption, Option.toList, List.mem_singleton] at member
            subst t
            have sameRegistry : cached.validators = atStep.validators := by
              obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
              rfl
            have beforeSize : before.validators.data.size ≤ population := by
              simpa only [sameRegistry, sameSize] using size
            have previous := finality_runs_activation_history inv positive frontier bounded
              beforeSize limit prefixOk
            have advanced := (finality_advanceSlots_activation_history holds positive
              previous.1 previous.2 (fun u same => limit u (same ▸ beforeSize)) slots).2
            simpa only [sameRegistry] using advanced

end EthLib.Consensus
