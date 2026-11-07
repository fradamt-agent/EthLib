module

public import EthLib.Consensus.Proofs.Transition.Finality.Registry

/-!
# Indexed effective-stake comparison for Phase 0 finality

The comparison reads reference activity and effective balances directly from beacon states.

The maximum loss is taken per validator before summing, as in the requested safety bound.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {p : Preset}

/-- The Phase 0 cap bounds indexed effective balances, including absent entries. -/
theorem finality_effective_le_cap {s : FinalityState p} (bounded : EffectiveBalancesBounded s)
    (i : Nat) : finalityEffective s i ≤ p.MAX_EFFECTIVE_BALANCE.toNat := by
  cases found : s.validators.data[i]? with
  | none => simp [finalityEffective, found]
  | some v =>
    simpa only [finalityEffective, found] using
      UInt64.le_iff_toNat_le.mp (bounded v (Array.mem_of_getElem? found))

/-- The indexed comparison charges the deficit twice and the largest observed loss three times.

Marks are restricted to the current-active denominator at each weighing state.

An index absent from either denominator contributes its reference stake to one shared exit charge.

This is the stake calculation in Casper FFG §2, with the Phase 0 cap and changing denominators. -/
theorem finality_index_stake_comparison (c s t : FinalityState p) (i : Nat)
    (leftMarked rightMarked : Bool) (cBound : EffectiveBalancesBounded c)
    (sBound : EffectiveBalancesBounded s) (tBound : EffectiveBalancesBounded t) :
    (if finalityActive c i then finalityEffective c i else 0) +
        3 * (if finalityActive c i && finalityActive s i && leftMarked
          then finalityEffective s i else 0) +
        3 * (if finalityActive c i && finalityActive t i && rightMarked
          then finalityEffective t i else 0) ≤
      3 * (if finalityActive c i && finalityActive s i && leftMarked &&
          finalityActive t i && rightMarked then finalityEffective c i else 0) +
        3 * (if finalityActive c i then
          max (finalityEffective c i - finalityEffective s i)
            (finalityEffective c i - finalityEffective t i) else 0) +
        2 * (if finalityActive c i then
          p.MAX_EFFECTIVE_BALANCE.toNat - finalityEffective c i else 0) +
        2 * (if finalityActive c i && finalityActive s i then finalityEffective s i else 0) +
        2 * (if finalityActive c i && finalityActive t i then finalityEffective t i else 0) +
        2 * (if finalityActive c i && !(finalityActive s i && finalityActive t i)
          then finalityEffective c i else 0) := by
  have cb := finality_effective_le_cap cBound i
  have sb := finality_effective_le_cap sBound i
  have tb := finality_effective_le_cap tBound i
  cases finalityActive c i <;> cases finalityActive s i <;> cases finalityActive t i <;>
    cases leftMarked <;> cases rightMarked <;>
    simp only [Bool.and_false, Bool.and_true, Bool.not_false,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Sum the indexed comparison over C's own registry, with marks read at those same indices. -/
theorem finality_reference_stake_comparison (c s t : FinalityState p)
    (leftMarked rightMarked : Nat → Bool) (cBound : EffectiveBalancesBounded c)
    (sBound : EffectiveBalancesBounded s) (tBound : EffectiveBalancesBounded t) :
    let indices := List.range c.validators.data.size
    let leftWeight := fun i => if finalityActive c i && finalityActive s i && leftMarked i
      then finalityEffective s i else 0
    let rightWeight := fun i => if finalityActive c i && finalityActive t i && rightMarked i
      then finalityEffective t i else 0
    let overlap := fun i => if finalityActive c i && finalityActive s i && leftMarked i &&
      finalityActive t i && rightMarked i then finalityEffective c i else 0
    let losses := fun i => if finalityActive c i then
      max (finalityEffective c i - finalityEffective s i)
        (finalityEffective c i - finalityEffective t i) else 0
    let leftActive := fun i => if finalityActive c i && finalityActive s i
      then finalityEffective s i else 0
    let rightActive := fun i => if finalityActive c i && finalityActive t i
      then finalityEffective t i else 0
    let absent := fun i => if finalityActive c i && !(finalityActive s i && finalityActive t i)
      then finalityEffective c i else 0
    finalityStake c + 3 * (indices.map leftWeight).sum + 3 * (indices.map rightWeight).sum ≤
      3 * (indices.map overlap).sum + 3 * (indices.map losses).sum + 2 * finalityDeficit c +
        2 * (indices.map leftActive).sum + 2 * (indices.map rightActive).sum +
        2 * (indices.map absent).sum := by
  dsimp only
  unfold finalityStake finalityDeficit
  generalize List.range c.validators.data.size = indices
  induction indices with
  | nil => simp
  | cons i rest ih =>
    have one := finality_index_stake_comparison c s t i (leftMarked i) (rightMarked i)
      cBound sBound tBound
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- Every observation is bounded by the history maximum used for per-validator losses. -/
theorem finality_le_maxOn {ss : List (FinalityState p)} {s : FinalityState p}
    (member : s ∈ ss) (f : FinalityState p → Nat) : f s ≤ finalityMaxOn ss f := by
  have bound : ∀ (xs : List Nat) (start x : Nat), x ∈ xs → x ≤ xs.foldl max start := by
    intro xs
    induction xs with
    | nil => simp
    | cons a rest ih =>
      intro start x member
      rcases List.mem_cons.mp member with equal | tail
      · have initial : ∀ (ys : List Nat) (z : Nat), z ≤ ys.foldl max z := by
          intro ys
          induction ys with
          | nil => intro z; exact Nat.le_refl _
          | cons b ys ih => intro z; exact Nat.le_trans (Nat.le_max_left z b) (ih (max z b))
        subst x
        exact Nat.le_trans (Nat.le_max_right start a) (initial rest (max start a))
      · exact ih (max start a) x tail
  exact bound (ss.map f) 0 (f s) (List.mem_map.mpr ⟨s, member, rfl⟩)

/-- Taking the maximum drop per validator covers losses at both selected weighing states. -/
theorem finality_pair_losses_le {c s t : FinalityState p} {ss : List (FinalityState p)}
    (left : s ∈ ss) (right : t ∈ ss) :
    ((List.range c.validators.data.size).map fun i => if finalityActive c i then
      max (finalityEffective c i - finalityEffective s i)
        (finalityEffective c i - finalityEffective t i) else 0).sum ≤ finalityLoss c ss := by
  unfold finalityLoss
  generalize List.range c.validators.data.size = indices
  induction indices with
  | nil => simp
  | cons i rest ih =>
    have one : (if finalityActive c i then
        max (finalityEffective c i - finalityEffective s i)
          (finalityEffective c i - finalityEffective t i) else 0) ≤
        (if finalityActive c i then finalityMaxOn ss
          (fun s => finalityEffective c i - finalityEffective s i) else 0) := by
      split
      · exact Nat.max_le.mpr
          ⟨finality_le_maxOn left (fun u => finalityEffective c i - finalityEffective u i),
            finality_le_maxOn right (fun u => finalityEffective c i - finalityEffective u i)⟩
      · exact Nat.le_refl _
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Absence from either selected denominator is covered by the history's union exit charge. -/
theorem finality_pair_exits_le {c s t : FinalityState p} {ss : List (FinalityState p)}
    (left : s ∈ ss) (right : t ∈ ss) :
    ((List.range c.validators.data.size).map fun i =>
      if finalityActive c i && !(finalityActive s i && finalityActive t i)
      then finalityEffective c i else 0).sum ≤ finalityExits c ss := by
  unfold finalityExits
  generalize List.range c.validators.data.size = indices
  induction indices with
  | nil => simp
  | cons i rest ih =>
    have absent : !(finalityActive s i && finalityActive t i) = true →
        ss.any (fun u => !(finalityActive u i)) = true := by
      intro outside
      cases ls : finalityActive s i with
      | false => exact List.any_eq_true.mpr ⟨s, left, by simp [ls]⟩
      | true =>
        have rt : finalityActive t i = false := by simpa [ls] using outside
        exact List.any_eq_true.mpr ⟨t, right, by simp [rt]⟩
    have one : (if finalityActive c i && !(finalityActive s i && finalityActive t i)
        then finalityEffective c i else 0) ≤
        (if finalityActive c i && ss.any (fun u => !(finalityActive u i))
        then finalityEffective c i else 0) := by
      split
      · rename_i counted
        simp only [Bool.and_eq_true] at counted
        obtain ⟨active, outside⟩ := counted
        rw [active, absent outside]
        exact Nat.le_refl _
      · exact Nat.zero_le _
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Cancel two corrected thresholds on C-active indices without increasing either correction.

This lemma isolates the arithmetic from extraction of actual attestation thresholds. -/
theorem finality_reference_threshold_drift (c s t : FinalityState p)
    (leftMarked rightMarked : Nat → Bool) (cBound : EffectiveBalancesBounded c)
    (sBound : EffectiveBalancesBounded s) (tBound : EffectiveBalancesBounded t)
    (ss : List (FinalityState p)) (left : s ∈ ss) (right : t ∈ ss)
    (leftCorrection rightCorrection : Nat)
    (leftEnough :
      2 * ((List.range c.validators.data.size).map fun i =>
        if finalityActive c i && finalityActive s i then finalityEffective s i else 0).sum ≤
      3 * ((List.range c.validators.data.size).map fun i =>
        if finalityActive c i && finalityActive s i && leftMarked i
        then finalityEffective s i else 0).sum + leftCorrection)
    (rightEnough :
      2 * ((List.range c.validators.data.size).map fun i =>
        if finalityActive c i && finalityActive t i then finalityEffective t i else 0).sum ≤
      3 * ((List.range c.validators.data.size).map fun i =>
        if finalityActive c i && finalityActive t i && rightMarked i
        then finalityEffective t i else 0).sum + rightCorrection) :
    finalityStake c ≤
      3 * ((List.range c.validators.data.size).map fun i =>
        if finalityActive c i && finalityActive s i && leftMarked i &&
          finalityActive t i && rightMarked i then finalityEffective c i else 0).sum +
        3 * finalityLoss c ss + 2 * finalityDeficit c + 2 * finalityExits c ss +
        leftCorrection + rightCorrection := by
  have compared := finality_reference_stake_comparison c s t leftMarked rightMarked
    cBound sBound tBound
  have losses := finality_pair_losses_le (c := c) left right
  have exits := finality_pair_exits_le (c := c) left right
  dsimp only at compared
  omega

/-- Removing non-reference voters costs their active weight once, not three times.

Their contribution to the denominator cancels two of the three participation coefficients.

Marked voters outside that denominator remain an explicit correction. -/
theorem finality_threshold_reference (c s : FinalityState p) (marked : Nat → Bool)
    (size : c.validators.data.size ≤ s.validators.data.size) (correction : Nat)
    (enough :
      2 * ((List.range s.validators.data.size).map fun i =>
        if finalityActive s i then finalityEffective s i else 0).sum ≤
      3 * ((List.range s.validators.data.size).map fun i =>
        if marked i then finalityEffective s i else 0).sum + correction) :
    2 * ((List.range c.validators.data.size).map fun i =>
      if finalityActive c i && finalityActive s i then finalityEffective s i else 0).sum ≤
      3 * ((List.range c.validators.data.size).map fun i =>
        if finalityActive c i && finalityActive s i && marked i
        then finalityEffective s i else 0).sum +
      ((List.range s.validators.data.size).map fun i =>
        if !finalityActive c i && finalityActive s i then finalityEffective s i else 0).sum +
      3 * ((List.range s.validators.data.size).map fun i =>
        if !finalityActive s i && marked i then finalityEffective s i else 0).sum + correction := by
  have compare : ∀ indices : List Nat,
      3 * (indices.map fun i => if marked i then finalityEffective s i else 0).sum +
        2 * (indices.map fun i => if finalityActive c i && finalityActive s i
          then finalityEffective s i else 0).sum ≤
      3 * (indices.map fun i => if finalityActive c i && finalityActive s i && marked i
        then finalityEffective s i else 0).sum +
      2 * (indices.map fun i => if finalityActive s i then finalityEffective s i else 0).sum +
      (indices.map fun i => if !finalityActive c i && finalityActive s i
        then finalityEffective s i else 0).sum +
      3 * (indices.map fun i => if !finalityActive s i && marked i
        then finalityEffective s i else 0).sum := by
    intro indices
    induction indices with
    | nil => simp
    | cons i rest ih =>
      have one : 3 * (if marked i then finalityEffective s i else 0) +
          2 * (if finalityActive c i && finalityActive s i then finalityEffective s i else 0) ≤
        3 * (if finalityActive c i && finalityActive s i && marked i
          then finalityEffective s i else 0) +
        2 * (if finalityActive s i then finalityEffective s i else 0) +
        (if !finalityActive c i && finalityActive s i then finalityEffective s i else 0) +
        3 * (if !finalityActive s i && marked i then finalityEffective s i else 0) := by
        cases finalityActive c i <;> cases finalityActive s i <;> cases marked i <;>
          simp only [Bool.and_false, Bool.and_true, Bool.not_false, Bool.not_true,
            Bool.false_eq_true, ↓reduceIte] <;> omega
      simp only [List.map_cons, List.sum_cons, Nat.mul_add]
      omega
  have compared := compare (List.range s.validators.data.size)
  have denominator := finality_active_sum_prefix c s
    (fun i => if finalityActive s i then finalityEffective s i else 0) size
  have voters := finality_active_sum_prefix c s
    (fun i => if finalityActive s i && marked i then finalityEffective s i else 0) size
  simp only [Bool.and_eq_true, ite_and] at compared denominator voters ⊢
  rw [denominator, voters] at compared
  omega

/-- The active-index marks agree with the spec's activity test at every registry position. -/
theorem finality_active_mark (s : FinalityState p) (i : Nat)
    (inside : i < s.validators.data.size) :
    ((markIndices s.validators.data.size
      (getActiveValidatorIndices s (getCurrentEpoch s)))[i]?).getD false =
        finalityActive s i := by
  rw [getElem?_markIndices, ite_eq_left inside]
  simp only [Option.getD_some]
  have within : s.RegistryWithinLimit := s.validators.bound (by decide)
  have convertIndex := toNat_toUInt64_of_lt within inside
  cases found : s.validators.data[i]? with
  | none => have outside := Array.getElem?_eq_none_iff.mp found; omega
  | some v =>
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, finalityActive, found]
    constructor
    · rintro ⟨index, member, equal⟩
      have indexEq : index.toNat = i := of_decide_eq_true equal
      obtain ⟨w, read, active⟩ := (mem_getActiveValidatorIndices within).mp member
      rw [indexEq, found] at read
      cases read
      exact active
    · intro active
      refine ⟨i.toUInt64, (mem_getActiveValidatorIndices within).mpr ?_, ?_⟩
      · exact ⟨v, by simpa only [convertIndex] using found, active⟩
      · simp [convertIndex]

/-- The concrete query threshold has the indexed current-active denominator used above. -/
theorem finality_threshold_indexed {s : FinalityState p} {e : Epoch}
    {indices : List ValidatorIndex} (threshold : FinalityThreshold s e indices) :
    2 * ((List.range s.validators.data.size).map fun i =>
      if finalityActive s i then finalityEffective s i else 0).sum ≤
    3 * ((List.range s.validators.data.size).map fun i =>
      if (markIndices s.validators.data.size indices)[i]?.getD false
      then finalityEffective s i else 0).sum + 3 * totalBalanceFloor s indices := by
  obtain ⟨_, _, _, enough⟩ := threshold
  rw [sumMarked_eq_index_sum, sumMarked_eq_index_sum] at enough
  have activeEq :
      ((List.range s.validators.data.size).map fun i =>
        if (markIndices s.validators.data.size
          (getActiveValidatorIndices s (getCurrentEpoch s)))[i]?.getD false
        then (s.validators.data[i]?.map (fun v => v.effectiveBalance.toNat)).getD 0 else 0) =
      ((List.range s.validators.data.size).map fun i =>
        if finalityActive s i then finalityEffective s i else 0) := by
    apply List.map_congr_left
    intro i member
    rw [finality_active_mark s i (List.mem_range.mp member)]
    cases found : s.validators.data[i]? <;> simp [finalityEffective, found]
  rw [activeEq] at enough
  have effectiveEq : ∀ i, (s.validators.data[i]?.map
      (fun v => v.effectiveBalance.toNat)).getD 0 = finalityEffective s i := by
    intro i
    cases found : s.validators.data[i]? <;> simp [finalityEffective, found]
  simpa only [effectiveEq] using enough

/-- A mark at a registry position supplies the exact validator index counted by the query. -/
theorem finality_marked_index {s : FinalityState p} {indices : List ValidatorIndex} {i : Nat}
    (marked : (markIndices s.validators.data.size indices)[i]?.getD false = true) :
    i.toUInt64 ∈ indices := by
  rw [getElem?_markIndices] at marked
  split at marked
  · simp only [Option.getD_some, List.any_eq_true] at marked
    obtain ⟨index, member, same⟩ := marked
    have equal : index = i.toUInt64 := by
      rw [← of_decide_eq_true same]
      exact UInt64.ofNat_toNat.symm
    exact equal ▸ member
  · simp at marked

/-- A target signer outside the current denominator is active in the previous epoch.

The successful query restricts its epoch to current or previous through the pending invariant. -/
theorem finality_marked_outside_previous {s : FinalityState p} {e : Epoch}
    {indices : List ValidatorIndex} {i : Nat} {v : Validator}
    (holds : PendingEpochsMatch s (by decide)) (threshold : FinalityThreshold s e indices)
    (found : s.validators.data[i]? = some v)
    (marked : (markIndices s.validators.data.size indices)[i]?.getD false = true)
    (outside : finalityActive s i = false) :
    isActiveValidator v (getPreviousEpoch s) = true := by
  obtain ⟨attestations, matching, computed, _⟩ := threshold
  have within : s.RegistryWithinLimit := s.validators.bound (by decide)
  have inside : i < s.validators.data.size := (Array.getElem?_eq_some_iff.mp found).1
  have natural := toNat_toUInt64_of_lt within inside
  have active := mem_getActiveValidatorIndices_of_target holds matching computed
    (finality_marked_index marked)
  obtain ⟨w, read, active⟩ := (mem_getActiveValidatorIndices within).mp active
  rw [natural, found] at read
  cases read
  obtain ⟨⟨pending, included, _, _, _⟩, _⟩ :=
    mem_getUnslashedAttestingIndices computed (finality_marked_index marked)
  obtain ⟨sources, _, sourceOk, _, _, _⟩ :=
    getMatchingTargetAttestations_mem matching included
  have recent := getMatchingSourceAttestations_epoch sourceOk
  rcases recent with previous | current
  · simpa only [previous] using active
  · have no : isActiveValidator v (getCurrentEpoch s) = false := by
      simpa only [finalityActive, found] using outside
    rw [current, no] at active
    cases active

/-- Summing registry values agrees with summing their successful natural-number lookups. -/
theorem finality_registry_sum_index (vs : Array Validator) (f : Validator → Nat) :
    (vs.toList.map f).sum =
      ((List.range vs.size).map fun i => (vs[i]?.map f).getD 0).sum := by
  have lists : ∀ xs : List Validator, (xs.map f).sum =
      ((List.range xs.length).map fun i => (xs[i]?.map f).getD 0).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons v xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, List.range_succ_eq_map,
        List.map_map, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.map_some,
        Option.getD_some, Function.comp_def]
      rw [ih]
  simpa only [Array.length_toList, Array.getElem?_toList] using lists vs.toList

/-- The previous-voter discrepancy bounds all marked weight outside the current denominator. -/
theorem finality_threshold_gap_le {s : FinalityState p} {e : Epoch}
    {indices : List ValidatorIndex} {ss : List (FinalityState p)}
    (observed : s ∈ ss) (holds : PendingEpochsMatch s (by decide))
    (threshold : FinalityThreshold s e indices) :
    ((List.range s.validators.data.size).map fun i =>
      if !finalityActive s i && (markIndices s.validators.data.size indices)[i]?.getD false
      then finalityEffective s i else 0).sum ≤ finalityPreviousGap ss := by
  have maximum := finality_le_maxOn observed (fun u =>
    (u.validators.data.toList.map fun v =>
      if isActiveValidator v (getPreviousEpoch u) && !isActiveValidator v (getCurrentEpoch u)
      then v.effectiveBalance.toNat else 0).sum)
  rw [finality_registry_sum_index] at maximum
  have one : ∀ i, (if !finalityActive s i &&
      (markIndices s.validators.data.size indices)[i]?.getD false
      then finalityEffective s i else 0) ≤
      (s.validators.data[i]?.map (fun v =>
        if isActiveValidator v (getPreviousEpoch s) && !isActiveValidator v (getCurrentEpoch s)
        then v.effectiveBalance.toNat else 0)).getD 0 := by
    intro i
    cases found : s.validators.data[i]? with
    | none => simp [finalityEffective, found]
    | some v =>
      split
      · rename_i counted
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at counted
        have previous := finality_marked_outside_previous holds threshold found
          counted.2 counted.1
        have current : isActiveValidator v (getCurrentEpoch s) = false := by
          simpa only [finalityActive, found] using counted.1
        simp [found, previous, current, finalityEffective]
      · exact Nat.zero_le _
  have summed : ∀ xs : List Nat,
      (xs.map fun i => if !finalityActive s i &&
        (markIndices s.validators.data.size indices)[i]?.getD false
        then finalityEffective s i else 0).sum ≤
      (xs.map fun i => (s.validators.data[i]?.map (fun v =>
        if isActiveValidator v (getPreviousEpoch s) && !isActiveValidator v (getCurrentEpoch s)
        then v.effectiveBalance.toNat else 0)).getD 0).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons i xs ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (one i) ih
  exact Nat.le_trans (summed _) maximum

/-- Each concrete threshold induces a C-active threshold with one addition charge. -/
theorem finality_threshold_reference_bound {c s : FinalityState p} {e : Epoch}
    {indices : List ValidatorIndex} {ss : List (FinalityState p)}
    (observed : s ∈ ss) (size : c.validators.data.size ≤ s.validators.data.size)
    (holds : PendingEpochsMatch s (by decide)) (threshold : FinalityThreshold s e indices) :
    2 * ((List.range c.validators.data.size).map fun i =>
      if finalityActive c i && finalityActive s i then finalityEffective s i else 0).sum ≤
    3 * ((List.range c.validators.data.size).map fun i =>
      if finalityActive c i && finalityActive s i &&
        (markIndices s.validators.data.size indices)[i]?.getD false
      then finalityEffective s i else 0).sum +
      finalityAdditions c ss + 3 * finalityPreviousGap ss +
        3 * p.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have enough := finality_threshold_reference c s
    (fun i => (markIndices s.validators.data.size indices)[i]?.getD false) size
    (3 * totalBalanceFloor s indices) (finality_threshold_indexed threshold)
  have added := finality_le_maxOn observed (fun u =>
    ((List.range u.validators.data.size).map fun i =>
      if finalityActive c i then 0 else if finalityActive u i
      then finalityEffective u i else 0).sum)
  have addedEq : ∀ xs : List Nat,
      (xs.map fun i => if !finalityActive c i && finalityActive s i
        then finalityEffective s i else 0).sum =
      (xs.map fun i => if finalityActive c i then 0 else if finalityActive s i
        then finalityEffective s i else 0).sum := by
    intro xs
    apply congrArg List.sum
    apply List.map_congr_left
    intro i _
    cases finalityActive c i <;> cases finalityActive s i <;> rfl
  rw [← addedEq] at added
  change ((List.range s.validators.data.size).map fun i =>
    if !finalityActive c i && finalityActive s i then finalityEffective s i else 0).sum ≤
      finalityAdditions c ss at added
  have gap := finality_threshold_gap_le observed holds threshold
  have floor : totalBalanceFloor s indices ≤ p.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    Nat.sub_le _ _
  omega

/-- Common marked indices with checked slashable evidence contribute at most slashable C-stake. -/
theorem finality_threshold_overlap_le {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c s t : FinalityState p}
    {a b : List (FinalityBlock p)} {indices other : List ValidatorIndex}
    (intersection : ∀ i, i ∈ indices → i ∈ other → FinalitySlashable cfg checks eng c a b i) :
    ((List.range c.validators.data.size).map fun i =>
      if finalityActive c i && finalityActive s i &&
        (markIndices s.validators.data.size indices)[i]?.getD false && finalityActive t i &&
        (markIndices t.validators.data.size other)[i]?.getD false
      then finalityEffective c i else 0).sum ≤ finalitySlashableStake cfg checks eng c a b := by
  classical
  unfold finalitySlashableStake
  generalize List.range c.validators.data.size = positions
  induction positions with
  | nil => simp
  | cons i rest ih =>
    have one : (if finalityActive c i && finalityActive s i &&
        (markIndices s.validators.data.size indices)[i]?.getD false && finalityActive t i &&
        (markIndices t.validators.data.size other)[i]?.getD false
        then finalityEffective c i else 0) ≤
        (if finalityActive c i ∧ FinalitySlashable cfg checks eng c a b i.toUInt64
        then finalityEffective c i else 0) := by
      split
      · rename_i counted
        simp only [Bool.and_eq_true] at counted
        have slashable := intersection i.toUInt64
          (finality_marked_index counted.1.1.2) (finality_marked_index counted.2)
        rw [ite_eq_left ⟨counted.1.1.1.1, slashable⟩]
        exact Nat.le_refl _
      · exact Nat.zero_le _
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add one ih

/-- Concrete threshold queries give the requested stake bound once their execution invariants hold.

The hypotheses expose bounded balances, prefix alignment and pending-epoch facts.

The final safety theorem must recover these facts from the histories. -/
theorem finality_threshold_stake_bound_of_invariants
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {c s t : FinalityState p} {a b : List (FinalityBlock p)} {ss : List (FinalityState p)}
    {e f : Epoch} {indices other : List ValidatorIndex}
    (cBound : EffectiveBalancesBounded c) (sBound : EffectiveBalancesBounded s)
    (tBound : EffectiveBalancesBounded t)
    (sSize : c.validators.data.size ≤ s.validators.data.size)
    (tSize : c.validators.data.size ≤ t.validators.data.size)
    (sEpochs : PendingEpochsMatch s (by decide)) (tEpochs : PendingEpochsMatch t (by decide))
    (left : s ∈ ss) (right : t ∈ ss)
    (sThreshold : FinalityThreshold s e indices) (tThreshold : FinalityThreshold t f other)
    (intersection : ∀ i, i ∈ indices → i ∈ other → FinalitySlashable cfg checks eng c a b i) :
    finalityStake c ≤ 3 * (finalitySlashableStake cfg checks eng c a b + finalityLoss c ss) +
      2 * finalityDeficit c + 2 * finalityAdditions c ss + 2 * finalityExits c ss +
      6 * finalityPreviousGap ss + 6 * p.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have compared := finality_reference_threshold_drift c s t
    (fun i => (markIndices s.validators.data.size indices)[i]?.getD false)
    (fun i => (markIndices t.validators.data.size other)[i]?.getD false)
    cBound sBound tBound ss left right
    (finalityAdditions c ss + 3 * finalityPreviousGap ss +
      3 * p.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (finalityAdditions c ss + 3 * finalityPreviousGap ss +
      3 * p.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (by simpa only [Nat.add_assoc] using
      finality_threshold_reference_bound left sSize sEpochs sThreshold)
    (by simpa only [Nat.add_assoc] using
      finality_threshold_reference_bound right tSize tEpochs tThreshold)
  have overlap := finality_threshold_overlap_le (s := s) (t := t) intersection
  omega

/-- Collected execution states retain bounded balances and checked pending epochs.

Only successful prefixes are used, including when a later block fails. -/
theorem finality_observations_invariants {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t : FinalityState p} {bs : List (FinalityBlock p)}
    (inv : Invariant c) (epochs : PendingEpochsMatch c (by decide))
    (member : t ∈ finalityObservations cfg checks eng c bs) :
    Invariant t ∧ PendingEpochsMatch t (by decide) := by
  simp only [finalityObservations, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨⟨b, i⟩, _, member⟩
  · exact ⟨inv, epochs⟩
  cases prefixOk : (bs.take i).foldlM (fun s b => stateTransition cfg checks eng s b true) c with
  | error e => simp [prefixOk] at member
  | ok before =>
    simp only [prefixOk, List.mem_append, List.mem_cons, List.mem_flatMap] at member
    have holds := finality_runs_invariant inv prefixOk
    have pending := foldlM_ok_invariant (fun s => PendingEpochsMatch s (by decide))
      (fun _ _ _ h ok => stateTransition_pending_epochs (by decide) h ok) epochs prefixOk
    rcases member with output | rfl | ⟨n, _, member⟩
    · cases block : stateTransition cfg checks eng before b true with
      | error e => simp [block, Except.toOption] at output
      | ok after =>
        simp only [block, Except.toOption, Option.toList, List.mem_singleton] at output
        subst t
        exact ⟨(stateTransition_invariant (by decide) holds block).1,
          stateTransition_pending_epochs (by decide) pending block⟩
    · exact ⟨holds, pending⟩
    · cases slots : advanceSlots cfg n before with
      | error e => simp [slots] at member
      | ok atStep =>
        simp only [slots, List.mem_cons] at member
        have step := (advanceSlots_invariant (by decide) holds slots).1
        have stepPending := advanceSlots_pending_epochs (by decide) n pending slots
        rcases member with rfl | member
        · exact ⟨step, stepPending⟩
        · cases cache : processSlot atStep with
          | error e => simp [cache, Except.toOption] at member
          | ok cached =>
            simp only [cache, Except.toOption, Option.toList, List.mem_singleton] at member
            subst t
            have frame := frame_processSlot cache
            exact ⟨frame.invariant step,
              (pendingUnchanged_processSlot cache).epochs frame stepPending⟩

/-- Two observed threshold queries yield the concrete correction from initialized execution.

The remaining extraction obligation is to supply the queries and their slashable intersection. -/
theorem finality_threshold_stake_bound
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g c s t : FinalityState p} {common a b : List (FinalityBlock p)}
    {e f : Epoch} {indices other : List ValidatorIndex}
    (initialized : finalityInitialized cfg checks g)
    (shared : finalityRuns cfg checks eng g common c)
    (left : s ∈ finalityObservations cfg checks eng c a ++
      finalityObservations cfg checks eng c b)
    (right : t ∈ finalityObservations cfg checks eng c a ++
      finalityObservations cfg checks eng c b)
    (sThreshold : FinalityThreshold s e indices) (tThreshold : FinalityThreshold t f other)
    (intersection : ∀ i, i ∈ indices → i ∈ other → FinalitySlashable cfg checks eng c a b i) :
    let ss := finalityObservations cfg checks eng c a ++ finalityObservations cfg checks eng c b
    finalityStake c ≤ 3 * (finalitySlashableStake cfg checks eng c a b + finalityLoss c ss) +
      2 * finalityDeficit c + 2 * finalityAdditions c ss + 2 * finalityExits c ss +
      6 * finalityPreviousGap ss + 6 * p.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  obtain ⟨h, timestamp, deposits, genesis⟩ := initialized.1
  have inv := finality_runs_invariant (initializeBeaconStateFromEth1_invariant genesis).2 shared
  have epochs := pendingEpochsMatch_of_initialized_chain (by decide) genesis shared
  have observed : ∀ u, u ∈ finalityObservations cfg checks eng c a ++
      finalityObservations cfg checks eng c b →
      (Invariant u ∧ PendingEpochsMatch u (by decide)) ∧ FinalityRegistryExtends c u := by
    intro u member
    rcases List.mem_append.mp member with member | member
    · exact ⟨finality_observations_invariants inv epochs member,
        finality_observations_registry inv member⟩
    · exact ⟨finality_observations_invariants inv epochs member,
        finality_observations_registry inv member⟩
  have sh := observed s left
  have th := observed t right
  exact finality_threshold_stake_bound_of_invariants inv.effectiveBalancesBounded
    sh.1.1.effectiveBalancesBounded th.1.1.effectiveBalancesBounded
    sh.2.1 th.2.1 sh.1.2 th.1.2 left right sThreshold tThreshold intersection

end EthLib.Consensus
