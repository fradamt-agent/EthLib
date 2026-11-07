module

public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.EpochRewards

/-!
# Proofs: rewards and penalties

Adding a delta changes the entry at its index only.

A validator whose vote does not match earns nothing for that kind of vote.

It pays the base reward instead.

So a validator absent from the unslashed signers earns no reward for that kind of vote.

From Altair, a validator that did not set a flag earns no reward for it.

A validator that set it pays no penalty for it, and nobody pays one for the head flag.

The inactivity deltas hold no reward.

From Altair, a validator with a timely target pays no inactivity penalty.

The first epoch has no rewards, and the step keeps one balance for each validator.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- Adding a delta keeps the entries at the other indices. -/
theorem addDelta_getD_of_ne {deltas result : Array Gwei} {index : ValidatorIndex}
    {amount : Gwei} (computed : addDelta deltas index amount = .ok result) {j : Nat}
    (other : j ≠ index.toNat) : result.getD j 0 = deltas.getD j 0 := by
  unfold addDelta at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    simp [Array.getD_eq_getD_getElem?, Ne.symm other]
  · cases computed

/-- Adding nothing keeps the deltas. -/
theorem addDelta_zero {deltas result : Array Gwei} {index : ValidatorIndex}
    (computed : addDelta deltas index 0 = .ok result) : result = deltas := by
  unfold addDelta at computed
  split at computed
  · rename_i inside
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff,
      pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨sum, ⟨_, value⟩, rfl⟩ := computed
    have same : sum = deltas[index.toNat] := UInt64.toNat_inj.mp (by simpa using value)
    subst same
    simp
  · cases computed

/-- A validator whose vote does not match earns nothing for that kind of vote.

It pays the base reward instead. -/
theorem componentDelta_unmatched (state : BeaconState preset fork)
    (base attestingBalance totalActiveBalance : Gwei) :
    componentDelta state false base attestingBalance totalActiveBalance = .ok (0, base) := rfl

/-- A validator absent from the unslashed signers of some attestations earns nothing for them.

This holds in a leak and outside one. -/
theorem getAttestationComponentDeltas_absent {attestations : Array (PendingAttestation preset)}
    {rewards penalties : Array Gwei}
    (computed : getAttestationComponentDeltas state attestations = .ok (rewards, penalties))
    {attesters : List ValidatorIndex}
    (signers : getUnslashedAttestingIndices state attestations = .ok attesters) {index : Nat}
    (absent : ∀ attester ∈ attesters, attester.toNat ≠ index) : rewards.getD index 0 = 0 := by
  simp only [getAttestationComponentDeltas, bind_ok_iff, liftAccessor_ok, signers] at computed
  obtain ⟨_, _, _, found, _, _, eligible, _, folded⟩ := computed
  cases found
  have unmarked : (markIndices state.validators.data.size attesters).getD index false = false := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    split
    · simp only [Option.getD_some, List.any_eq_false, beq_iff_eq]
      exact fun attester member => absent attester member
    · rfl
  let P : Array Gwei × Array Gwei → Prop := fun deltas =>
    ∀ j, (markIndices state.validators.data.size attesters).getD j false = false →
      deltas.1.getD j 0 = 0
  have start : P (Array.replicate state.validators.data.size 0,
      Array.replicate state.validators.data.size 0) := by
    intro j _
    simp [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  have holds := foldlM_ok_invariant P (fun deltas index next before step => by
    obtain ⟨rewards, penalties⟩ := deltas
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at step
    obtain ⟨_, _, ⟨reward, penalty⟩, delta, newRewards, rewardsOk, _, _, rfl⟩ := step
    intro j unmarkedJ
    by_cases same : j = index.toNat
    · subst same
      rw [unmarkedJ] at delta
      rw [componentDelta_unmatched] at delta
      cases delta
      rw [addDelta_zero rewardsOk]
      exact before _ unmarkedJ
    · rw [addDelta_getD_of_ne rewardsOk same]
      exact before j unmarkedJ) start folded
  exact holds index unmarked

/-- A fold of steps that keep one entry of the deltas, from zeros, leaves that entry zero. -/
private theorem foldlM_getD_zero {step : Array Gwei × Array Gwei → ValidatorIndex →
      Except TransitionError (Array Gwei × Array Gwei)}
    (pick : Array Gwei × Array Gwei → Array Gwei) {j : Nat}
    (keeps : ∀ deltas index next, step deltas index = .ok next →
      (pick next).getD j 0 = (pick deltas).getD j 0)
    {indices : List ValidatorIndex} {start result : Array Gwei × Array Gwei}
    (zero : (pick start).getD j 0 = 0) (computed : indices.foldlM step start = .ok result) :
    (pick result).getD j 0 = 0 :=
  foldlM_ok_invariant (fun deltas => (pick deltas).getD j 0 = 0)
    (fun deltas index next before done => (keeps deltas index next done).trans before) zero computed

/-- An array of zeros is zero at every index. -/
private theorem replicate_getD_zero (size j : Nat) :
    (Array.replicate size (0 : Gwei)).getD j 0 = 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
  split <;> rfl

/-- One step of the flag deltas keeps the reward of a validator that did not set the flag. -/
theorem addFlagDelta_reward {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements : Gwei}
    {deltas next : Array Gwei × Array Gwei} {index : ValidatorIndex}
    (computed : addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements deltas index = .ok next)
    {j : Nat} (unset : participated.getD j false = false) :
    next.1.getD j 0 = deltas.1.getD j 0 := by
  obtain ⟨rewards, penalties⟩ := deltas
  simp only [addFlagDelta, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · rename_i set
    have other : j ≠ index.toNat := fun same => by rw [same, set] at unset; cases unset
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, _, _, _, _, ok, rfl⟩ := computed
      exact addDelta_getD_of_ne ok other
  · split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, _, rfl⟩ := computed
      rfl

/-- One step of the flag deltas keeps the penalty of a validator that set the flag.

It keeps every penalty for the head flag. -/
theorem addFlagDelta_penalty {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length}
    {participated : Array Bool} {total participatingIncrements activeIncrements : Gwei}
    {deltas next : Array Gwei × Array Gwei} {index : ValidatorIndex}
    (computed : addFlagDelta state flagIndex participated total participatingIncrements
      activeIncrements deltas index = .ok next)
    {j : Nat} (exempt : participated.getD j false = true ∨
      flagIndex.val.toUInt64 = TIMELY_HEAD_FLAG_INDEX) :
    next.2.getD j 0 = deltas.2.getD j 0 := by
  obtain ⟨rewards, penalties⟩ := deltas
  simp only [addFlagDelta, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := computed
      rfl
  · rename_i unset
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · rename_i notHead
      simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, ok, rfl⟩ := computed
      refine addDelta_getD_of_ne ok fun same => ?_
      rcases exempt with set | head
      · rw [same] at set
        exact unset set
      · exact notHead head

/-- From Altair, a validator that did not set a flag in the previous epoch earns no reward for it.

This holds in a leak and outside one. -/
theorem getFlagIndexDeltas_absent {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties))
    {participating : List ValidatorIndex}
    (flagged : getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
      (getPreviousEpoch state) = .ok participating)
    {index : Nat} (absent : ∀ participant ∈ participating, participant.toNat ≠ index) :
    rewards.getD index 0 = 0 := by
  simp only [getFlagIndexDeltas, bind_ok_iff, liftAccessor_ok, flagged] at computed
  obtain ⟨_, found, _, _, _, _, _, _, folded⟩ := computed
  cases found
  have unset : (markIndices state.validators.data.size participating).getD index false = false := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    split
    · simp only [Option.getD_some, List.any_eq_false, beq_iff_eq]
      exact fun participant member => absent participant member
    · rfl
  exact foldlM_getD_zero Prod.fst (fun _ _ _ step => addFlagDelta_reward step unset)
    (replicate_getD_zero _ _) folded

/-- From Altair, a validator that set a flag in the previous epoch pays no penalty for it. -/
theorem getFlagIndexDeltas_present {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties))
    {participating : List ValidatorIndex}
    (flagged : getUnslashedParticipatingIndices state altair flagIndex.val.toUInt64
      (getPreviousEpoch state) = .ok participating)
    {index : ValidatorIndex} (present : index ∈ participating)
    (inside : index.toNat < state.validators.data.size) :
    penalties.getD index.toNat 0 = 0 := by
  simp only [getFlagIndexDeltas, bind_ok_iff, liftAccessor_ok, flagged] at computed
  obtain ⟨_, found, _, _, _, _, _, _, folded⟩ := computed
  cases found
  have set : (markIndices state.validators.data.size participating).getD index.toNat false =
      true := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    simpa [inside] using ⟨index, present, rfl⟩
  exact foldlM_getD_zero Prod.snd (fun _ _ _ step => addFlagDelta_penalty step (.inl set))
    (replicate_getD_zero _ _) folded

/-- From Altair, the head flag has no penalties. -/
theorem getFlagIndexDeltas_head {altair : .altair ≤ fork}
    {flagIndex : Fin PARTICIPATION_FLAG_WEIGHTS.length} {rewards penalties : Array Gwei}
    (computed : getFlagIndexDeltas state altair flagIndex = .ok (rewards, penalties))
    (head : flagIndex.val.toUInt64 = TIMELY_HEAD_FLAG_INDEX) (j : Nat) :
    penalties.getD j 0 = 0 := by
  simp only [getFlagIndexDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, folded⟩ := computed
  exact foldlM_getD_zero Prod.snd (fun _ _ _ step => addFlagDelta_penalty step (.inr head))
    (replicate_getD_zero _ _) folded

/-- The inactivity deltas hold no reward, at every fork. -/
theorem getInactivityPenaltyDeltas_rewards {config : Config} {rewards penalties : Array Gwei}
    (computed : getInactivityPenaltyDeltas config state = .ok (rewards, penalties)) (j : Nat) :
    rewards.getD j 0 = 0 := by
  unfold getInactivityPenaltyDeltas at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact replicate_getD_zero _ _
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl, _⟩ := computed
      exact replicate_getD_zero _ _
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
      obtain ⟨rfl, _⟩ := computed
      exact replicate_getD_zero _ _

/-- One step of the inactivity penalties keeps the penalty of a validator with a timely target. -/
theorem addInactivityScorePenalty_matched {config : Config} {altair : .altair ≤ fork}
    {targetMatched : Array Bool} {penalties next : Array Gwei} {index : ValidatorIndex}
    (computed : addInactivityScorePenalty config state altair targetMatched penalties index =
      .ok next)
    {j : Nat} (matched : targetMatched.getD j false = true) :
    next.getD j 0 = penalties.getD j 0 := by
  unfold addInactivityScorePenalty at computed
  split at computed
  · cases computed
    rfl
  · rename_i unmatched
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, _, _, ok⟩ := computed
      exact addDelta_getD_of_ne ok fun same => unmatched (same ▸ matched)
    · cases computed

/-- From Altair, a validator with a timely target in the previous epoch pays no inactivity penalty.

This holds in a leak and outside one. -/
theorem getInactivityPenaltyDeltas_target {config : Config} (altair : .altair ≤ fork)
    {rewards penalties : Array Gwei}
    (computed : getInactivityPenaltyDeltas config state = .ok (rewards, penalties))
    {matching : List ValidatorIndex}
    (timely : getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX
      (getPreviousEpoch state) = .ok matching)
    {index : ValidatorIndex} (present : index ∈ matching)
    (inside : index.toNat < state.validators.data.size) :
    penalties.getD index.toNat 0 = 0 := by
  unfold getInactivityPenaltyDeltas at computed
  dsimp only at computed
  simp only [altair, ↓reduceDIte, bind_ok_iff, liftAccessor_ok, timely, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at computed
  obtain ⟨_, found, _, _, _, folded, _, rfl⟩ := computed
  cases found
  have set : (markIndices state.validators.data.size matching).getD index.toNat false = true := by
    rw [Array.getD_eq_getD_getElem?, getElem?_markIndices]
    simpa [inside] using ⟨index, present, rfl⟩
  exact foldlM_ok_invariant (fun deltas : Array Gwei => deltas.getD index.toNat 0 = 0)
    (fun _ _ _ before step => (addInactivityScorePenalty_matched step set).trans before)
    (replicate_getD_zero _ _) folded

/-- In the first epoch, rewards and penalties change nothing. -/
theorem processRewardsAndPenalties_genesis (config : Config)
    (genesis : getCurrentEpoch state = GENESIS_EPOCH) :
    processRewardsAndPenalties config state = .ok state := by
  simp [processRewardsAndPenalties, genesis, pure, Except.pure]

/-- Applying the deltas of one validator keeps the sizes. -/
theorem sameSizes_applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) : SameSizes state after := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨raised, raisedOk, lowered⟩ := computed
  exact (sameSizes_increaseBalance raisedOk).trans (sameSizes_decreaseBalance lowered)

/-- Applying some deltas to every validator keeps the sizes. -/
theorem sameSizes_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : SameSizes state after :=
  foldlM_ok_invariant (SameSizes state) (fun _ _ _ sizes step =>
    sizes.trans (sameSizes_applyDeltas step)) (SameSizes.refl state) computed

/-- Rewards and penalties keep the sizes, at every fork. -/
theorem processRewardsAndPenalties_sameSizes {config : Config}
    (computed : processRewardsAndPenalties config state = .ok after) : SameSizes state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ SameSizes.refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact foldlM_ok_invariant (SameSizes state) (fun before _ _ sizes step =>
      sizes.trans (sameSizes_applyAllDeltas step)) (SameSizes.refl state) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact sameSizes_applyAllDeltas applied

/-- A successful reward addition fits in 64 bits, before the penalty saturates at zero.

The subtraction in the conclusion is on natural numbers. -/
theorem balance_applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) :
    ∃ balance : Gwei, getBalance state index.toUInt64 = .ok balance ∧
      balance.toNat + (rewards.getD index 0).toNat < 2 ^ 64 ∧
      getBalance after index.toUInt64 =
        .ok (saturatingSub (balance + rewards.getD index 0) (penalties.getD index 0)) ∧
      (saturatingSub (balance + rewards.getD index 0) (penalties.getD index 0)).toNat =
        balance.toNat + (rewards.getD index 0).toNat - (penalties.getD index 0).toNat := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨raised, raisedOk, lowered⟩ := computed
  simp only [increaseBalance, bind_ok_iff, liftArith, mapError_ok_iff,
    addChecked_ok_iff] at raisedOk
  obtain ⟨balance, found, sum, ⟨fits, summed⟩, set⟩ := raisedOk
  have sum_eq : sum = balance + rewards.getD index 0 :=
    UInt64.toNat_inj.mp (summed.trans (toNat_add_of_lt fits).symm)
  subst sum_eq
  have read := getBalance_setBalance_self set
  simp only [decreaseBalance, read, bind, Except.bind] at lowered
  exact ⟨balance, found, fits, getBalance_setBalance_self lowered, by
    rw [toNat_saturatingSub, toNat_add_of_lt fits]⟩

/-- Applying another validator's deltas leaves this balance unchanged. -/
private theorem getBalance_applyDeltas_of_ne {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after)
    {j : ValidatorIndex} (other : j.toNat ≠ index.toUInt64.toNat) :
    getBalance after j = getBalance state j := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨raised, raisedOk, lowered⟩ := computed
  obtain ⟨_, set⟩ := increaseBalance_ok raisedOk
  obtain ⟨_, rfl⟩ := setBalance_ok set
  obtain ⟨_, set⟩ := decreaseBalance_ok lowered
  obtain ⟨_, rfl⟩ := setBalance_ok set
  simp only [getBalance, BeaconState.putBalance, Array.getElem?_set,
    ite_eq_right (Ne.symm other)]

/-- A sequence of updates at other indices keeps the selected balance. -/
private theorem getBalance_fold_applyDeltas_of_not_mem
    {rewards penalties : Array Gwei} {indices : List Nat} {j : ValidatorIndex}
    (other : ∀ i ∈ indices, j.toNat ≠ i.toUInt64.toNat)
    (computed : indices.foldlM (applyDeltas rewards penalties) state = .ok after) :
    getBalance after j = getBalance state j := by
  induction indices generalizing state with
  | nil => cases computed; rfl
  | cons i indices ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨next, step, rest⟩ := computed
    exact (ih (fun i hi => other i (by simp [hi])) rest).trans
      (getBalance_applyDeltas_of_ne step (other i (by simp)))

/-- A pass applies each validator's reward before its penalty, with no wrapping addition.

Validator indices are 64-bit values.

The index bound prevents distinct registry positions from naming the same validator.

Before Gloas the registry type supplies this bound.

From Gloas the progressive registry has no type-level bound. -/
theorem balance_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (bounded : state.validators.data.size ≤ 2 ^ 64)
    (computed : applyAllDeltas state deltas = .ok after)
    {j : Nat} (inside : j < state.validators.data.size) :
    ∃ beforeBalance afterBalance : Gwei,
      getBalance state j.toUInt64 = .ok beforeBalance ∧
      getBalance after j.toUInt64 = .ok afterBalance ∧
      beforeBalance.toNat + (deltas.1.getD j 0).toNat < 2 ^ 64 ∧
      afterBalance.toNat = beforeBalance.toNat + (deltas.1.getD j 0).toNat -
        (deltas.2.getD j 0).toNat := by
  have jbound : j < 2 ^ 64 := Nat.lt_of_lt_of_le inside bounded
  have convert : ∀ i, i < 2 ^ 64 → i.toUInt64.toNat = i := by
    intro i hi
    exact Nat.mod_eq_of_lt hi
  have walk : ∀ (indices : List Nat) (pre post : BeaconState preset fork),
      indices.Nodup → (∀ i ∈ indices, i < 2 ^ 64) → j ∈ indices →
      indices.foldlM (applyDeltas deltas.1 deltas.2) pre = .ok post →
      ∃ b a : Gwei, getBalance pre j.toUInt64 = .ok b ∧
        getBalance post j.toUInt64 = .ok a ∧
        b.toNat + (deltas.1.getD j 0).toNat < 2 ^ 64 ∧
        a.toNat = b.toNat + (deltas.1.getD j 0).toNat - (deltas.2.getD j 0).toNat := by
    intro indices
    induction indices with
    | nil => simp
    | cons i indices ih =>
      intro pre post unique bounds member folded
      rw [List.foldlM_cons, bind_ok_iff] at folded
      obtain ⟨next, step, rest⟩ := folded
      rcases List.mem_cons.mp member with same | member
      · subst i
        obtain ⟨b, found, fits, read, value⟩ := balance_applyDeltas step
        have kept := getBalance_fold_applyDeltas_of_not_mem (j := j.toUInt64)
          (fun i hi => by
            rw [convert j jbound, convert i (bounds i (by simp [hi]))]
            exact fun eq => (List.nodup_cons.mp unique).1 (eq ▸ hi)) rest
        exact ⟨b, _, found, kept.trans read, fits, value⟩
      · obtain ⟨b, a, found, read, fits, value⟩ := ih next post
          (List.nodup_cons.mp unique).2 (fun i hi => bounds i (by simp [hi])) member rest
        have other : j ≠ i := by
          exact fun eq => (List.nodup_cons.mp unique).1 (eq ▸ member)
        have kept := getBalance_applyDeltas_of_ne step (j := j.toUInt64)
          (by simpa [convert j jbound, convert i (bounds i (by simp))] using other)
        exact ⟨b, a, kept ▸ found, read, fits, value⟩
  exact walk (List.range state.validators.data.size) state after List.nodup_range
    (fun i hi => Nat.lt_of_lt_of_le (List.mem_range.mp hi) bounded)
    (List.mem_range.mpr inside) computed

/-- Each pass saturates separately, in list order.

Successful execution supplies the checked addition at every pass. -/
theorem balance_fold_applyAllDeltas {passes : List (Array Gwei × Array Gwei)}
    (bounded : state.validators.data.size ≤ 2 ^ 64)
    (computed : passes.foldlM applyAllDeltas state = .ok after)
    {j : Nat} (inside : j < state.validators.data.size) {balance : Gwei}
    (found : getBalance state j.toUInt64 = .ok balance) :
    ∃ finalBalance : Gwei, getBalance after j.toUInt64 = .ok finalBalance ∧
      finalBalance.toNat = passes.foldl
        (fun b d => b + (d.1.getD j 0).toNat - (d.2.getD j 0).toNat) balance.toNat := by
  induction passes generalizing state balance with
  | nil => cases computed; exact ⟨balance, found, rfl⟩
  | cons delta passes ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨next, step, rest⟩ := computed
    obtain ⟨b, a, read, nextRead, _, value⟩ := balance_applyAllDeltas bounded step inside
    have same : b = balance := Except.ok.inj (read.symm.trans found)
    subst same
    have sizes := sameSizes_applyAllDeltas step
    obtain ⟨finalBalance, finalRead, finalValue⟩ := ih (by simpa [sizes.1] using bounded) rest
      (by simpa [sizes.1] using inside) nextRead
    exact ⟨finalBalance, finalRead, by simpa [List.foldl_cons, value] using finalValue⟩

/-- Before Altair, the attestation deltas are applied in one saturating pass. -/
theorem balance_processRewardsAndPenalties_before_altair {config : Config}
    (before : fork < .altair) (notGenesis : getCurrentEpoch state ≠ GENESIS_EPOCH)
    (computed : processRewardsAndPenalties config state = .ok after)
    {j : Nat} (inside : j < state.validators.data.size) :
    ∃ deltas : Array Gwei × Array Gwei,
      getAttestationDeltas config state before = .ok deltas ∧
      ∃ b a : Gwei, getBalance state j.toUInt64 = .ok b ∧
        getBalance after j.toUInt64 = .ok a ∧
        b.toNat + (deltas.1.getD j 0).toNat < 2 ^ 64 ∧
        a.toNat = b.toNat + (deltas.1.getD j 0).toNat - (deltas.2.getD j 0).toNat := by
  have notAltair : ¬Fork.altair ≤ fork := fun le =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simp only [processRewardsAndPenalties, notGenesis, ↓reduceIte,
    notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨deltas, calculated, applied⟩ := computed
  have bound := state.validators.bound (show fork < .glamsterdam from by
    exact Nat.lt_trans before (by decide))
  have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  have bounded : state.validators.data.size ≤ 2 ^ 64 := by omega
  exact ⟨deltas, calculated, balance_applyAllDeltas bounded applied inside⟩

/-- From Altair, apply the flags in index order, then inactivity, saturating after each pass.

All deltas are computed from the state before any pass. -/
theorem balance_processRewardsAndPenalties_from_altair {config : Config}
    (altair : .altair ≤ fork) (notGenesis : getCurrentEpoch state ≠ GENESIS_EPOCH)
    (bounded : state.validators.data.size ≤ 2 ^ 64)
    (computed : processRewardsAndPenalties config state = .ok after)
    {j : Nat} (inside : j < state.validators.data.size) {balance : Gwei}
    (found : getBalance state j.toUInt64 = .ok balance) :
    ∃ flags inactivity,
      (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
        (getFlagIndexDeltas state altair) = .ok flags ∧
      getInactivityPenaltyDeltas config state = .ok inactivity ∧
      ∃ finalBalance : Gwei, getBalance after j.toUInt64 = .ok finalBalance ∧
        finalBalance.toNat = (flags ++ [inactivity]).foldl
          (fun b d => b + (d.1.getD j 0).toNat - (d.2.getD j 0).toNat) balance.toNat := by
  simp only [processRewardsAndPenalties, notGenesis, ↓reduceIte, altair,
    ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨flags, calculated, inactivity, inactive, applied⟩ := computed
  exact ⟨flags, inactivity, calculated, inactive,
    balance_fold_applyAllDeltas bounded applied inside found⟩

/-- Before Gloas, the registry type supplies the bound for the ordered flag passes. -/
theorem balance_processRewardsAndPenalties_altair_before_gloas {config : Config}
    (altair : .altair ≤ fork) (before : fork < .glamsterdam)
    (notGenesis : getCurrentEpoch state ≠ GENESIS_EPOCH)
    (computed : processRewardsAndPenalties config state = .ok after)
    {j : Nat} (inside : j < state.validators.data.size) {balance : Gwei}
    (found : getBalance state j.toUInt64 = .ok balance) :
    ∃ flags inactivity,
      (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
        (getFlagIndexDeltas state altair) = .ok flags ∧
      getInactivityPenaltyDeltas config state = .ok inactivity ∧
      ∃ finalBalance : Gwei, getBalance after j.toUInt64 = .ok finalBalance ∧
        finalBalance.toNat = (flags ++ [inactivity]).foldl
          (fun b d => b + (d.1.getD j 0).toNat - (d.2.getD j 0).toNat) balance.toNat := by
  have bound := state.validators.bound before
  have limit := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
  exact balance_processRewardsAndPenalties_from_altair altair notGenesis
    (by omega) computed inside found

end EthLib.Consensus
