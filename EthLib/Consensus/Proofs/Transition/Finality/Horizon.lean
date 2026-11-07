module

public import EthLib.Consensus.Proofs.Transition.Finality.Definitions

/-!
# Phase 0 finality within an epoch horizon

The correction combines the two suffixes' actual activation and exit cohorts.

Exits count the union of missing C-active indices, so both suffix bounds are needed.

The zero horizon uses checkpoint preservation instead of a churn estimate.
-/

@[expose] public section

namespace EthLib.Consensus

variable {p : Preset}

/-- Bounding each observation bounds their maximum, including an empty history. -/
theorem finalityMaxOn_le_iff (ss : List (FinalityState p)) (f : FinalityState p → Nat)
    (bound : Nat) : finalityMaxOn ss f ≤ bound ↔ ∀ s ∈ ss, f s ≤ bound := by
  have fold (xs : List Nat) (start : Nat) :
      xs.foldl max start ≤ bound ↔ start ≤ bound ∧ ∀ x ∈ xs, x ≤ bound := by
    induction xs generalizing start with
    | nil => simp
    | cons x xs ih => simp [List.foldl_cons, ih, Nat.max_le, and_assoc]
  simp [finalityMaxOn, fold]

/-- An observation maximum on two suffixes is the maximum of their separate bounds. -/
theorem finalityMaxOn_append_le {a b : List (FinalityState p)}
    {f : FinalityState p → Nat} {bound : Nat}
    (left : finalityMaxOn a f ≤ bound) (right : finalityMaxOn b f ≤ bound) :
    finalityMaxOn (a ++ b) f ≤ bound := by
  simp only [finalityMaxOn_le_iff, List.mem_append, or_imp, forall_and] at *
  exact ⟨left, right⟩

/-- The reference-weight union of exits costs at most the sum of the suffix costs. -/
theorem finalityExits_append_le (c : FinalityState p) (a b : List (FinalityState p)) :
    finalityExits c (a ++ b) ≤ finalityExits c a + finalityExits c b := by
  unfold finalityExits
  generalize List.range c.validators.data.size = indices
  induction indices with
  | nil => simp
  | cons i indices ih =>
    simp only [List.map_cons, List.sum_cons, List.any_append] at *
    cases finalityActive c i <;> cases a.any (fun s => !finalityActive s i) <;>
      cases b.any (fun s => !finalityActive s i) <;> simp_all <;> omega

/-- The two-fork churn costs fit the frozen correction at every positive horizon.

The exit bound is twice a single suffix's bound, not once.
-/
theorem finality_horizon_arithmetic {cfg : Config} {c : FinalityState p} {n : Nat}
    {additions exits previousGap : Nat} (positive : 0 < n)
    (added : additions ≤ n * finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat)
    (exited : exits ≤ 2 * (n * finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat))
    (gap : previousGap ≤ finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat) :
    2 * additions + 2 * exits + 6 * previousGap +
      6 * p.EFFECTIVE_BALANCE_INCREMENT.toNat ≤
        finalityHorizonCorrection cfg c n - 2 * finalityDeficit c := by
  rw [finalityHorizonCorrection, ite_eq_right (by omega)]
  -- Expand the extra epoch before linear arithmetic; all products are natural numbers.
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
  simp only [Nat.mul_assoc] at *
  omega

/-- Successful zero-horizon suffixes cannot finalize conflicting checkpoints.

The underlying preservation theorem also covers a zero slots-per-epoch preset.
-/
theorem finality_not_conflicting_zero_horizon {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c left right : FinalityState p}
    {common a b : List (FinalityBlock p)}
    (leftRun : finalityRuns cfg checks eng c a left)
    (rightRun : finalityRuns cfg checks eng c b right)
    (leftHorizon : (getCurrentEpoch left).toNat - (getCurrentEpoch c).toNat ≤ 0)
    (rightHorizon : (getCurrentEpoch right).toNat - (getCurrentEpoch c).toNat ≤ 0) :
    ¬FinalityConflicting (common ++ a ++ b) left.finalizedCheckpoint
      right.finalizedCheckpoint := by
  have same := stateTransition_chains_finalized_eq_of_zero_epochs (by decide)
    leftRun rightRun leftHorizon rightHorizon
  intro conflict
  apply conflict.2.2.1
  rw [same]
  exact Relation.ReflTransGen.refl

/-- Compose the core safety inequality and the realized churn theorem.

The two premises are the conclusions of those theorems at this execution.

They impose no new condition on a successful chain.

Collision and zero-root sentinel evidence pass through on the same frozen observation pool.
-/
theorem finality_phase0_safety_horizon_of_main_and_churn
    (cfg : Config) (checks : SignatureChecks) (eng : ExecutionEngine p .phase0)
    (g c left right : FinalityState p) (common a b : List (FinalityBlock p)) (n : Nat)
    (leftRun : finalityRuns cfg checks eng c a left)
    (rightRun : finalityRuns cfg checks eng c b right)
    (leftHorizon : (getCurrentEpoch left).toNat - (getCurrentEpoch c).toNat ≤ n)
    (rightHorizon : (getCurrentEpoch right).toNat - (getCurrentEpoch c).toNat ≤ n)
    (conflict : FinalityConflicting (common ++ a ++ b)
      left.finalizedCheckpoint right.finalizedCheckpoint)
    (main : let ss := finalityObservations cfg checks eng c a ++
        finalityObservations cfg checks eng c b
      (finalityStake c ≤
        3 * (finalitySlashableStake cfg checks eng c a b + finalityLoss c ss) +
        2 * finalityDeficit c + 2 * finalityAdditions c ss + 2 * finalityExits c ss +
        6 * finalityPreviousGap ss + 6 * p.EFFECTIVE_BALANCE_INCREMENT.toNat) ∨
      FinalityCollisionFound (finalityObservations cfg checks eng g common ++ ss)
        (common ++ a ++ b) ∨
      FinalityZeroRootFound (finalityObservations cfg checks eng g common ++ ss)
        (common ++ a ++ b))
    (churn : ∀ (after : FinalityState p) (bs : List (FinalityBlock p)),
      finalityRuns cfg checks eng c bs after →
      (getCurrentEpoch after).toNat - (getCurrentEpoch c).toNat ≤ n →
      let ss := finalityObservations cfg checks eng c bs
      finalityAdditions c ss ≤ n * finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat ∧
      finalityExits c ss ≤ n * finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat ∧
      finalityPreviousGap ss ≤ finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat) :
    let ss := finalityObservations cfg checks eng c a ++
      finalityObservations cfg checks eng c b
    (finalityStake c ≤
      3 * (finalitySlashableStake cfg checks eng c a b + finalityLoss c ss) +
        finalityHorizonCorrection cfg c n) ∨
    FinalityCollisionFound (finalityObservations cfg checks eng g common ++ ss)
      (common ++ a ++ b) ∨
    FinalityZeroRootFound (finalityObservations cfg checks eng g common ++ ss)
      (common ++ a ++ b) := by
  by_cases zero : n = 0
  · subst n
    exact False.elim (finality_not_conflicting_zero_horizon
      leftRun rightRun leftHorizon rightHorizon conflict)
  obtain bound | evidence := main
  · left
    obtain ⟨addedLeft, exitedLeft, gapLeft⟩ := churn left a leftRun leftHorizon
    obtain ⟨addedRight, exitedRight, gapRight⟩ := churn right b rightRun rightHorizon
    have added := finalityMaxOn_append_le addedLeft addedRight
    have gap := finalityMaxOn_append_le gapLeft gapRight
    -- Keep the same stake expressions as the core inequality for arithmetic cancellation.
    change finalityAdditions c (finalityObservations cfg checks eng c a ++
      finalityObservations cfg checks eng c b) ≤
      n * finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat at added
    change finalityPreviousGap (finalityObservations cfg checks eng c a ++
      finalityObservations cfg checks eng c b) ≤
      finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat at gap
    have exited := finalityExits_append_le c
      (finalityObservations cfg checks eng c a) (finalityObservations cfg checks eng c b)
    have exitBound : finalityExits c (finalityObservations cfg checks eng c a ++
        finalityObservations cfg checks eng c b) ≤
        2 * (n * finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat) := by omega
    have correction := finality_horizon_arithmetic (by omega) added exitBound gap
    -- Natural subtraction can be cancelled because the positive-horizon formula includes deficit.
    have deficit : 2 * finalityDeficit c ≤ finalityHorizonCorrection cfg c n := by
      simp only [finalityHorizonCorrection, ite_eq_right zero]
      omega
    omega
  · exact Or.inr evidence

end EthLib.Consensus
