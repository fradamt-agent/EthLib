module

public import EthLib.Consensus.Proofs.Transition.Finality.Churn

/-!
# Reference exits on one Phase 0 suffix

Past-epoch activity at an observation agrees with the endpoint registry.

Thus the union of absent reference indices can be charged to endpoint exit cohorts.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {p : Preset}

/-- The endpoint retains an observation's active-index query at its own epoch. -/
theorem finality_observation_endpoint_active_indices {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t after : FinalityState p}
    {bs : List (FinalityBlock p)} (inv : Invariant c)
    (ran : finalityRuns cfg checks eng c bs after)
    (member : t ∈ finalityObservations cfg checks eng c bs) :
    getActiveValidatorIndices after (getCurrentEpoch t) =
      getActiveValidatorIndices t (getCurrentEpoch t) := by
  simp only [finalityObservations, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨⟨b, i⟩, listed, member⟩
  · exact stateTransition_chain_active_indices (by decide) inv (UInt64.le_refl _) ran
  obtain ⟨inside, equal⟩ := List.getElem?_eq_some_iff.mp
    (List.mk_mem_zipIdx_iff_getElem?.mp listed)
  have split : bs = bs.take i ++ b :: bs.drop (i + 1) := by
    rw [← equal, ← List.drop_eq_getElem_cons inside, List.take_append_drop]
  cases prefixOk : (bs.take i).foldlM
      (fun s b => stateTransition cfg checks eng s b true) c with
  | error e => simp [prefixOk] at member
  | ok before =>
    have remaining := ran
    unfold finalityRuns at remaining
    rw [split, List.foldlM_append, prefixOk] at remaining
    change (b :: bs.drop (i + 1)).foldlM
      (fun s b => stateTransition cfg checks eng s b true) before = .ok after at remaining
    have holds := finality_runs_invariant inv prefixOk
    obtain ⟨middle, blockOk, tailOk⟩ := bind_ok_iff.mp remaining
    have middleInv := (stateTransition_invariant (by decide) holds blockOk).1
    obtain ⟨advanced, slotsOk, advancedSlot, _, processed, _⟩ := stateTransition_ok blockOk
    simp only [prefixOk, List.mem_append, List.mem_cons, List.mem_flatMap] at member
    rcases member with output | rfl | ⟨n, count, member⟩
    · simp only [blockOk, Except.toOption, Option.toList, List.mem_singleton] at output
      subst t
      exact stateTransition_chain_active_indices (by decide) middleInv
        (UInt64.le_refl _) tailOk
    · exact stateTransition_chain_active_indices (by decide) holds
        (UInt64.le_refl _) remaining
    · have within := List.mem_range.mp count
      have full : advanceSlots cfg (b.message.slot.toNat - before.slot.toNat) before =
          .ok advanced := by
        simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
        exact slotsOk.choose_spec.2
      obtain ⟨atStep, stepOk, restOk⟩ := advanceSlots_add (first := n)
        (rest := b.message.slot.toNat - before.slot.toNat - n)
        (by simpa only [Nat.add_sub_of_le (Nat.le_of_lt within)] using full)
      have stepInv := (advanceSlots_invariant (by decide) holds stepOk).1
      have stepSlot := advanceSlots_slot n stepOk
      have advancedNat := congrArg UInt64.toNat advancedSlot
      have middleSlot := (frame_processBlock (by decide) processed).slot
      have later : getCurrentEpoch atStep ≤ getCurrentEpoch middle := by
        apply UInt64.le_iff_toNat_le.mpr
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, middleSlot]
        exact Nat.div_le_div_right (by omega)
      have advancedPast : getCurrentEpoch atStep ≤ getCurrentEpoch advanced := by
        simpa only [getCurrentEpoch, middleSlot] using later
      have kept := (stateTransition_chain_active_indices (by decide) middleInv later tailOk).trans
        ((processBlock_active_indices (by decide) advancedPast processed).trans
          (advanceSlots_active_indices (by decide) _ stepInv (UInt64.le_refl _) restOk))
      rw [stepOk] at member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact kept
      · cases cache : processSlot atStep with
        | error e => simp [cache, Except.toOption] at member
        | ok cached =>
          simp only [cache, Except.toOption, Option.toList, List.mem_singleton] at member
          subst t
          obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
          exact kept

/-- An absent reference index belongs to an endpoint exit cohort inside the horizon. -/
theorem finality_exit_window {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t after : FinalityState p}
    {bs : List (FinalityBlock p)} {i : Nat} (inv : Invariant c)
    (ran : finalityRuns cfg checks eng c bs after)
    (member : t ∈ finalityObservations cfg checks eng c bs)
    (active : finalityActive c i = true) (absent : finalityActive t i = false) :
    ∃ v, after.validators.data[i]? = some v ∧
      (getCurrentEpoch c).toNat < v.exitEpoch.toNat ∧
      v.exitEpoch.toNat ≤ (getCurrentEpoch after).toNat := by
  have present : ∃ v, c.validators.data[i]? = some v := by
    cases read : c.validators.data[i]? with
    | none => simp [finalityActive, read] at active
    | some v => exact ⟨v, rfl⟩
  obtain ⟨v, read⟩ := present
  have inside := (Array.getElem?_eq_some_iff.mp read).1
  have exactIndex := toNat_toUInt64_of_lt (c.validators.bound (by decide)) inside
  have found : getValidator c i.toUInt64 = .ok v := by
    simp [getValidator, exactIndex, inside, (Array.getElem?_eq_some_iff.mp read).2]
  have oldActive : isActiveValidator v (getCurrentEpoch c) = true := by
    simpa only [finalityActive, read] using active
  have oldMember := (mem_getActiveValidatorIndices (index := i.toUInt64)
    (c.validators.bound (by decide))).mpr
    ⟨v, by simpa only [exactIndex] using read, oldActive⟩
  have endpoint := stateTransition_chain_active_indices (by decide) inv (UInt64.le_refl _) ran
  have endpointMember : i.toUInt64 ∈ getActiveValidatorIndices after (getCurrentEpoch c) := by
    rwa [endpoint]
  obtain ⟨w, wread, wactive⟩ :=
    (mem_getActiveValidatorIndices (after.validators.bound (by decide))).mp endpointMember
  have wread' : after.validators.data[i]? = some w := by simpa only [exactIndex] using wread
  have notMember : i.toUInt64 ∉ getActiveValidatorIndices t (getCurrentEpoch t) := by
    intro yes
    obtain ⟨x, xread, xactive⟩ :=
      (mem_getActiveValidatorIndices (t.validators.bound (by decide))).mp yes
    have xread' : t.validators.data[i]? = some x := by simpa only [exactIndex] using xread
    simp only [finalityActive, xread', xactive] at absent
    contradiction
  have inactive : isActiveValidator w (getCurrentEpoch t) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    apply notMember
    rw [← finality_observation_endpoint_active_indices inv ran member]
    exact (mem_getActiveValidatorIndices (after.validators.bound (by decide))).mpr
      ⟨w, wread, yes⟩
  have lower := finality_observations_epoch_ge member
  have upper := Nat.div_le_div_right (c := p.SLOTS_PER_EPOCH.toNat)
    (finality_observations_slot_le ran member)
  rw [← getCurrentEpoch_toNat, ← getCurrentEpoch_toNat] at upper
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at wactive
  have activation := UInt64.le_iff_toNat_le.mp wactive.1
  have exits := UInt64.lt_iff_toNat_lt.mp wactive.2
  have ended : w.exitEpoch.toNat ≤ (getCurrentEpoch t).toNat := by
    by_contra h
    have yes : isActiveValidator w (getCurrentEpoch t) = true := by
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨UInt64.le_iff_toNat_le.mpr (by omega), UInt64.lt_iff_toNat_lt.mpr (by omega)⟩
    simp [yes] at inactive
  exact ⟨w, wread', exits, by omega⟩

/-- Counting indexed array entries counts occurrences, including equal validator values. -/
private theorem exits_index_count (vs : Array Validator) (test : Validator → Bool) :
    ((List.range vs.size).filter (fun i => (vs[i]?.map test).getD false)).length =
      (vs.toList.filter test).length := by
  have general : ∀ xs : List Validator,
      ((List.range xs.length).filter (fun i => (xs[i]?.map test).getD false)).length =
        (xs.filter test).length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.length_cons, List.range_succ_eq_map, List.filter_cons,
        List.getElem?_cons_zero, Option.map_some, Option.getD_some,
        List.filter_map, Function.comp_def, List.getElem?_cons_succ]
      split <;> simp_all
  simpa only [Array.length_toList, Array.getElem?_toList] using general vs.toList

/-- The union of absent reference indices fits the endpoint's finite exit cohorts. -/
theorem finality_exits_le_of_positive {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {g c after : FinalityState p}
    {common bs : List (FinalityBlock p)} {n : Nat}
    (initialized : finalityInitialized cfg checks g)
    (shared : finalityRuns cfg checks eng g common c)
    (ran : finalityRuns cfg checks eng c bs after)
    (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (horizon : (getCurrentEpoch after).toNat - (getCurrentEpoch c).toNat ≤ n) :
    finalityExits c (finalityObservations cfg checks eng c bs) ≤
      n * finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat := by
  obtain ⟨_, _, _, genesis⟩ := initialized.1
  have inv := finality_runs_invariant (initializeBeaconStateFromEth1_invariant genesis).2 shared
  let selected := fun i => finalityActive c i &&
    (finalityObservations cfg checks eng c bs).any (fun s => !(finalityActive s i))
  let items := (List.range c.validators.data.size).filter selected
  let epoch := fun (i : Nat) =>
    (after.validators.data[i]?.map (fun v => v.exitEpoch.toNat)).getD 0
  have window : ∀ i ∈ items, (getCurrentEpoch c).toNat < epoch i ∧
      epoch i ≤ (getCurrentEpoch c).toNat + n := by
    intro i member
    obtain ⟨_, flags⟩ := List.mem_filter.mp member
    have flags' : finalityActive c i = true ∧
        (finalityObservations cfg checks eng c bs).any (fun s => !(finalityActive s i)) = true :=
      by simpa only [selected, Bool.and_eq_true] using flags
    obtain ⟨active, missing⟩ := flags'
    obtain ⟨t, observed, absent⟩ := List.any_eq_true.mp missing
    have absent' : finalityActive t i = false := by simpa using absent
    obtain ⟨v, read, lower, upper⟩ := finality_exit_window inv ran observed active absent'
    simp only [epoch, read, Option.map_some, Option.getD_some]
    exact ⟨lower, by omega⟩
  have bounded : ∀ i ∈ items, finalityEffective c i ≤ p.MAX_EFFECTIVE_BALANCE.toNat := by
    intro i _
    cases read : c.validators.data[i]? with
    | none => simp [finalityEffective, read]
    | some v =>
      simpa only [finalityEffective, read] using
        UInt64.le_iff_toNat_le.mp (inv.effectiveBalancesBounded v (Array.mem_of_getElem? read))
  have size := finality_runs_size_horizon positive ran horizon
  have cohorts := finality_reachable_exitCohort initialized
    (show finalityRuns cfg checks eng g (common ++ bs) after by
      simp only [finalityRuns, List.foldlM_append]
      rw [show common.foldlM (fun s b => stateTransition cfg checks eng s b true) g =
        .ok c from shared]
      exact ran) size
  have finalFinite := finality_runs_epoch_finite
    (finality_runs_epoch_finite (by rw [finality_initialized_epoch initialized]; decide) shared) ran
  have count : ∀ e, (getCurrentEpoch c).toNat < e →
      e ≤ (getCurrentEpoch c).toNat + n →
      (items.filter (fun i => epoch i == e)).length ≤ finalityChurnCap cfg c n := by
    intro e lower upper
    by_cases endBound : e ≤ (getCurrentEpoch after).toNat
    · have fits : e < 2 ^ 64 := Nat.lt_of_le_of_lt endBound (getCurrentEpoch after).toNat_lt
      have exactEpoch : e.toUInt64.toNat = e := by
        rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
      have finite : e.toUInt64 ≠ FAR_FUTURE_EPOCH := by
        intro far
        have endTop := (getCurrentEpoch after).toNat_lt
        have top := congrArg UInt64.toNat far
        rw [exactEpoch] at top
        have same : getCurrentEpoch after = FAR_FUTURE_EPOCH := by
          apply UInt64.toNat_inj.mp
          change (getCurrentEpoch after).toNat = 18446744073709551615
          change e = 18446744073709551615 at top
          omega
        exact finalFinite same
      have subset : List.Sublist (items.filter (fun i => epoch i == e))
          ((List.range after.validators.data.size).filter
            (fun i => (after.validators.data[i]?.map (fun v => v.exitEpoch == e.toUInt64)).getD
              false)) := by
        apply List.sublist_filter_iff.mpr
        refine ⟨items.filter (fun i => epoch i == e),
          (List.filter_sublist.trans List.filter_sublist).trans
            (List.range_sublist.mpr (finality_runs_registry inv ran).1), ?_⟩
        symm
        apply List.filter_eq_self.mpr
        intro i member
        obtain ⟨selectedMember, yes⟩ := List.mem_filter.mp member
        have inside := List.mem_range.mp (List.mem_filter.mp selectedMember).1
        have enlarged := (finality_runs_registry inv ran).1
        have read : ∃ v, after.validators.data[i]? = some v :=
          ⟨after.validators.data[i]'(by omega), Array.getElem?_eq_getElem (by omega)⟩
        obtain ⟨v, read⟩ := read
        simp only [epoch, read, Option.map_some, Option.getD_some, beq_iff_eq] at yes ⊢
        exact UInt64.toNat_inj.mp (yes.trans exactEpoch.symm)
      have countBound := subset.length_le
      rw [exits_index_count] at countBound
      exact Nat.le_trans countBound (cohorts _ finite)
    · have empty : items.filter (fun i => epoch i == e) = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro i member
        obtain ⟨inside, same⟩ := List.mem_filter.mp member
        obtain ⟨_, flags⟩ := List.mem_filter.mp inside
        have flags' : finalityActive c i = true ∧
            (finalityObservations cfg checks eng c bs).any
              (fun s => !(finalityActive s i)) = true := by
          simpa only [selected, Bool.and_eq_true] using flags
        obtain ⟨active, missing⟩ := flags'
        obtain ⟨t, observed, absent⟩ := List.any_eq_true.mp missing
        obtain ⟨v, read, _, ended⟩ := finality_exit_window inv ran observed active
          (by simpa using absent)
        simp only [epoch, read, Option.map_some, Option.getD_some, beq_iff_eq] at same
        omega
      simp [empty]
  have total := finality_weighted_cohort_window items epoch (finalityEffective c)
    (getCurrentEpoch c).toNat n (finalityChurnCap cfg c n) p.MAX_EFFECTIVE_BALANCE.toNat
    window bounded count
  have sum : finalityExits c (finalityObservations cfg checks eng c bs) =
      (items.map (finalityEffective c)).sum := by
    have general : ∀ xs : List Nat,
        (xs.map (fun i => if selected i then finalityEffective c i else 0)).sum =
          ((xs.filter selected).map (finalityEffective c)).sum := by
      intro xs
      induction xs with
      | nil => rfl
      | cons x xs ih => cases h : selected x <;> simp [h, ih]
    exact general _
  rwa [sum]

/-- Reference exits on one suffix are bounded without positivity premises. -/
theorem finality_exits_le {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {g c after : FinalityState p}
    {common bs : List (FinalityBlock p)} {n : Nat}
    (initialized : finalityInitialized cfg checks g)
    (shared : finalityRuns cfg checks eng g common c)
    (ran : finalityRuns cfg checks eng c bs after)
    (horizon : (getCurrentEpoch after).toNat - (getCurrentEpoch c).toNat ≤ n) :
    finalityExits c (finalityObservations cfg checks eng c bs) ≤
      n * finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat := by
  obtain ⟨_, _, _, genesis⟩ := initialized.1
  have inv := finality_runs_invariant (initializeBeaconStateFromEth1_invariant genesis).2 shared
  by_cases zero : p.SLOTS_PER_EPOCH = 0
  · rw [(finality_realized_churn_zero_slots zero inv).2.1]
    exact Nat.zero_le _
  by_cases same : (getCurrentEpoch after).toNat - (getCurrentEpoch c).toNat = 0
  · rw [(finality_realized_churn_zero_horizon inv ran same).2]
    exact Nat.zero_le _
  have positive : 0 < p.SLOTS_PER_EPOCH.toNat := by
    have nonzero : p.SLOTS_PER_EPOCH.toNat ≠ 0 := by
      intro h
      exact zero (UInt64.toNat_inj.mp (by simpa using h))
    omega
  exact finality_exits_le_of_positive initialized shared ran positive horizon

end EthLib.Consensus
