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

end EthLib.Consensus
