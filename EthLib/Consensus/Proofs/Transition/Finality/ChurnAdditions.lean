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

end EthLib.Consensus
