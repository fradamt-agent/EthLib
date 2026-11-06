module

public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Transition.EpochUpdates

/-!
# Proofs: the other steps of the epoch transition

An updated effective balance is the old one, or the balance rounded down to an increment and capped.

The effective balances are aligned when each is a whole number of increments, at most the largest.

When the largest is itself a whole number of increments, the update keeps them aligned.

The registry updates, the slashings and the update of the effective balances keep the sizes.

The slashings reset clears the slashed balance of the next epoch.

The RANDAO reset copies the mix of the current epoch to the next.

The rotation of the pending attestations moves those of the current epoch to the previous one.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-! ## Effective balances -/

/-- Every validator's effective balance is at most the Phase 0 voting-weight cap. -/
def EffectiveBalancesBounded (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data, validator.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE

/-- A bounded later effective balance can exceed its reference only by the initial deficit. -/
theorem effectiveBalance_growth_le_initial_deficit {reference : Gwei} {validator : Validator}
    (bounded : EffectiveBalancesBounded state) (member : validator ∈ state.validators.data) :
    validator.effectiveBalance.toNat - reference.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE.toNat - reference.toNat := by
  have bound := UInt64.le_iff_toNat_le.mp (bounded validator member)
  omega

/-- A registry replacement preserves the cap when the replacement satisfies it. -/
theorem effectiveBalancesBounded_setValidator {index : Nat} {validator : Validator}
    (bounded : EffectiveBalancesBounded state)
    (bound : validator.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE) :
    EffectiveBalancesBounded (state.setValidator index validator) := by
  intro other member
  rcases Array.mem_or_eq_of_mem_setIfInBounds member with old | rfl
  · exact bounded other old
  · exact bound

/-- Stored balance that can fund an effective-balance increase without new rewards.

The update rounds down and caps the balance, so this is an upper bound on its headroom. -/
def effectiveBalanceHeadroom (balance effectiveBalance : Gwei) : Nat :=
  balance.toNat - effectiveBalance.toNat

/-- Stored balance can fund growth only up to the Phase 0 effective-balance cap.

Balance above the cap cannot increase justification weight. -/
def cappedEffectiveBalanceHeadroom (preset : Preset) (balance effectiveBalance : Gwei) : Nat :=
  min (effectiveBalanceHeadroom balance effectiveBalance)
    (preset.MAX_EFFECTIVE_BALANCE.toNat - effectiveBalance.toNat)

/-- A deposit can supply at most one Phase 0 effective-balance cap of voting weight.

The balance credit itself is not capped. -/
def cappedDepositCredit (preset : Preset) (amount : Gwei) : Nat :=
  min amount.toNat preset.MAX_EFFECTIVE_BALANCE.toNat

/-- Capping each deposit bounds the charge by the number of deposits times the cap. -/
theorem sum_cappedDepositCredit_le (preset : Preset) (amounts : List Gwei) :
    (amounts.map (cappedDepositCredit preset)).sum ≤
      amounts.length * preset.MAX_EFFECTIVE_BALANCE.toNat := by
  induction amounts with
  | nil => simp
  | cons amount amounts ih =>
    have capped : cappedDepositCredit preset amount ≤ preset.MAX_EFFECTIVE_BALANCE.toNat :=
      Nat.min_le_right _ _
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

/-- Stored headroom and deposit credits share the same remaining effective-balance capacity.

This caps their combined contribution instead of charging the same available capacity twice. -/
theorem cappedEffectiveBalanceHeadroom_add_deposit (preset : Preset)
    (balance effectiveBalance amount : Gwei) :
    min (balance.toNat + amount.toNat - effectiveBalance.toNat)
        (preset.MAX_EFFECTIVE_BALANCE.toNat - effectiveBalance.toNat) ≤
      min (cappedEffectiveBalanceHeadroom preset balance effectiveBalance +
          cappedDepositCredit preset amount)
        (preset.MAX_EFFECTIVE_BALANCE.toNat - effectiveBalance.toNat) := by
  unfold cappedEffectiveBalanceHeadroom effectiveBalanceHeadroom cappedDepositCredit
  omega

/-- An updated effective balance is the old one, or the balance rounded down and capped. -/
theorem updatedEffectiveBalance_cases {balance effectiveBalance result : Gwei}
    (computed : updatedEffectiveBalance preset balance effectiveBalance = .ok result) :
    result = effectiveBalance ∨
      result = min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
        preset.MAX_EFFECTIVE_BALANCE := by
  simp only [updatedEffectiveBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, leaves, _, rfl⟩ := computed
  cases leaves
  · exact .inl rfl
  · exact .inr rfl

/-- The update preserves the effective-balance cap without an alignment assumption. -/
theorem updatedEffectiveBalance_le_max {balance effectiveBalance result : Gwei}
    (bounded : effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (computed : updatedEffectiveBalance preset balance effectiveBalance = .ok result) :
    result ≤ preset.MAX_EFFECTIVE_BALANCE := by
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact bounded
  · exact Std.min_le_right

/-- Updating one effective balance preserves the registry-wide cap. -/
theorem updateEffectiveBalance_bounded {index : Nat}
    (bounded : EffectiveBalancesBounded state)
    (computed : updateEffectiveBalance state index = .ok after) :
    EffectiveBalancesBounded after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, _, effectiveBalance, updated, rfl⟩ := computed
  apply effectiveBalancesBounded_setValidator bounded
  apply updatedEffectiveBalance_le_max _ updated
  unfold getValidator at found
  split at found
  · rename_i read
    cases found
    exact bounded _ (Array.mem_of_getElem? read)
  · cases found

/-- Updating every effective balance preserves the cap. -/
theorem processEffectiveBalanceUpdates_bounded
    (bounded : EffectiveBalancesBounded state)
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    EffectiveBalancesBounded after := by
  unfold processEffectiveBalanceUpdates at computed
  split at computed
  · cases computed
  exact foldlM_ok_invariant EffectiveBalancesBounded
    (fun _ _ _ before step => updateEffectiveBalance_bounded before step) bounded computed

/-- An effective-balance increase cannot exceed the balance's excess over the old value.

This bound includes stored balance below the next hysteresis threshold.

A bound from rewards alone must also account for that stored balance. -/
theorem updatedEffectiveBalance_increase_le {balance effectiveBalance result : Gwei}
    (computed : updatedEffectiveBalance preset balance effectiveBalance = .ok result) :
    result.toNat - effectiveBalance.toNat ≤ balance.toNat - effectiveBalance.toNat := by
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · omega
  · have remainder : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
    have capped : min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
        preset.MAX_EFFECTIVE_BALANCE ≤
        balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT := Std.min_le_left
    have bound := UInt64.le_iff_toNat_le.mp capped
    rw [UInt64.toNat_sub_of_le _ _ remainder, UInt64.toNat_mod] at bound
    omega

/-- Updating an effective balance preserves every indexed committee activity query.

Committee assignment uses activation and exit epochs, not effective balance. -/
theorem updateEffectiveBalance_active {index : Nat} {epoch : Epoch}
    (exactIndex : index.toUInt64.toNat = index)
    (computed : updateEffectiveBalance state index = .ok after) (other : ValidatorIndex) :
    (getValidator after other).map (isActiveValidator · epoch) =
      (getValidator state other).map (isActiveValidator · epoch) := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, _, effectiveBalance, _, rfl⟩ := computed
  by_cases equal : other = index.toUInt64
  · subst other
    have read := getValidator_setValidator_self found
      { validator with effectiveBalance }
    rw [exactIndex] at read
    rw [read, found]
    rfl
  · have same := getValidator_setValidator_of_ne (state := state) equal
      { validator with effectiveBalance }
    rw [exactIndex] at same
    rw [same]

/-- The complete effective-balance pass preserves every indexed activity query. -/
theorem processEffectiveBalanceUpdates_active {epoch : Epoch}
    (within : state.RegistryWithinLimit)
    (computed : processEffectiveBalanceUpdates state = .ok after) (other : ValidatorIndex) :
    (getValidator after other).map (isActiveValidator · epoch) =
      (getValidator state other).map (isActiveValidator · epoch) := by
  unfold processEffectiveBalanceUpdates at computed
  split at computed
  · cases computed
  have preserve : ∀ (indices : List Nat) (s s' : BeaconState preset fork),
      s.RegistryWithinLimit → (∀ i ∈ indices, i < s.validators.data.size) →
      indices.foldlM updateEffectiveBalance s = .ok s' →
      (getValidator s' other).map (isActiveValidator · epoch) =
        (getValidator s other).map (isActiveValidator · epoch) := by
    intro indices
    induction indices with
    | nil =>
      intro s s' _ _ ok
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at ok
      subst s'
      rfl
    | cons index rest ih =>
      intro s s' bound inside ok
      rw [List.foldlM_cons, bind_ok_iff] at ok
      obtain ⟨middle, first, tail⟩ := ok
      have sizes : middle.validators.data.size = s.validators.data.size := by
        simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
          Except.ok.injEq] at first
        obtain ⟨_, _, _, _, _, _, rfl⟩ := first
        simp only [BeaconState.setValidator, Array.size_set!]
      have middleBound : middle.RegistryWithinLimit := by
        unfold BeaconState.RegistryWithinLimit at bound ⊢
        rw [sizes]
        exact bound
      have kept := updateEffectiveBalance_active (epoch := epoch)
        (toNat_toUInt64_of_lt bound (inside index List.mem_cons_self)) first other
      exact (ih middle s' middleBound (fun i member => by
        rw [sizes]
        exact inside i (List.mem_cons_of_mem _ member)) tail).trans kept
  exact preserve _ state after within (fun _ member => List.mem_range.mp member) computed

/-- A single update cannot use stored balance above the effective-balance cap. -/
theorem updatedEffectiveBalance_increase_le_capped_headroom
    {balance effectiveBalance result : Gwei}
    (computed : updatedEffectiveBalance preset balance effectiveBalance = .ok result) :
    result.toNat - effectiveBalance.toNat ≤
      cappedEffectiveBalanceHeadroom preset balance effectiveBalance := by
  have balanceBound := updatedEffectiveBalance_increase_le computed
  have capBound : result.toNat - effectiveBalance.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE.toNat - effectiveBalance.toNat := by
    rcases updatedEffectiveBalance_cases computed with rfl | rfl
    · omega
    · have capped := UInt64.le_iff_toNat_le.mp
        (Std.min_le_right (a := balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
          (b := preset.MAX_EFFECTIVE_BALANCE))
      omega
  exact Nat.le_min.mpr ⟨balanceBound, capBound⟩

/-- Credits after the reference state and its stored headroom cover an effective-balance increase.

The caller must bound credits from deposits and rewards separately.

Penalties can only reduce the balance bound in the hypothesis. -/
theorem updatedEffectiveBalance_increase_le_headroom_add
    {referenceBalance referenceEffective balance effectiveBalance result : Gwei} {credits : Nat}
    (balanceBound : balance.toNat ≤ referenceBalance.toNat + credits)
    (computed : updatedEffectiveBalance preset balance effectiveBalance = .ok result) :
    result.toNat - referenceEffective.toNat ≤
      effectiveBalanceHeadroom referenceBalance referenceEffective + credits +
        (effectiveBalance.toNat - referenceEffective.toNat) := by
  unfold effectiveBalanceHeadroom
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · omega
  · have remainder : balance % preset.EFFECTIVE_BALANCE_INCREMENT ≤ balance := by
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
      exact Nat.mod_le _ _
    have capped : min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
        preset.MAX_EFFECTIVE_BALANCE ≤
        balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT := Std.min_le_left
    have bound := UInt64.le_iff_toNat_le.mp capped
    rw [UInt64.toNat_sub_of_le _ _ remainder, UInt64.toNat_mod] at bound
    omega

/-- Reference headroom is capped even when later deposits or rewards supply more credits.

The separate old-effective-balance term permits an update after earlier growth. -/
theorem updatedEffectiveBalance_increase_le_capped_headroom_add
    {referenceBalance referenceEffective balance effectiveBalance result : Gwei} {credits : Nat}
    (balanceBound : balance.toNat ≤ referenceBalance.toNat + credits)
    (computed : updatedEffectiveBalance preset balance effectiveBalance = .ok result) :
    result.toNat - referenceEffective.toNat ≤
      cappedEffectiveBalanceHeadroom preset referenceBalance referenceEffective + credits +
        (effectiveBalance.toNat - referenceEffective.toNat) := by
  have uncapped := updatedEffectiveBalance_increase_le_headroom_add
    (referenceEffective := referenceEffective) balanceBound computed
  unfold cappedEffectiveBalanceHeadroom effectiveBalanceHeadroom at *
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · omega
  · have capped := UInt64.le_iff_toNat_le.mp
      (Std.min_le_right (a := balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT)
        (b := preset.MAX_EFFECTIVE_BALANCE))
    omega

/-- Every effective balance is a whole number of increments, and at most the largest. -/
def EffectiveBalancesAligned (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data.toList,
    validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
      validator.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE

/-- A balance rounded down to an increment is a whole number of increments. -/
theorem sub_mod_mod_self (balance increment : Gwei) :
    (balance - balance % increment) % increment = 0 := by
  have le : balance % increment ≤ balance := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
    exact Nat.mod_le _ _
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ le, UInt64.toNat_mod]
  simpa using Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm

/-- An updated effective balance is aligned when the old one and the largest are. -/
theorem updatedEffectiveBalance_aligned {balance effectiveBalance result : Gwei}
    (maxAligned : preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (old : effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
      effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (computed : updatedEffectiveBalance preset balance effectiveBalance = .ok result) :
    result % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧ result ≤ preset.MAX_EFFECTIVE_BALANCE := by
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact old
  · rw [UInt64.min_def]
    split
    · exact ⟨sub_mod_mod_self _ _, by assumption⟩
    · exact ⟨maxAligned, UInt64.le_refl _⟩

/-- Replacing a validator by an aligned one keeps the effective balances aligned. -/
theorem effectiveBalancesAligned_setValidator {index : Nat} {validator : Validator}
    (holds : EffectiveBalancesAligned state)
    (good : validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
      validator.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE) :
    EffectiveBalancesAligned (state.setValidator index validator) := by
  intro other member
  simp only [BeaconState.setValidator, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
    at member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact holds other old
  · exact good

/-- The update of one effective balance keeps them aligned, when the largest is aligned. -/
theorem updateEffectiveBalance_aligned {index : Nat}
    (maxAligned : preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (holds : EffectiveBalancesAligned state)
    (computed : updateEffectiveBalance state index = .ok after) :
    EffectiveBalancesAligned after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, _, effectiveBalance, updated, rfl⟩ := computed
  apply effectiveBalancesAligned_setValidator holds
  apply updatedEffectiveBalance_aligned maxAligned _ updated
  unfold getValidator at found
  split at found
  · rename_i read
    cases found
    exact holds _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? read))
  · cases found

/-- The update of the effective balances keeps them aligned.

The largest effective balance must be a whole number of increments. -/
theorem processEffectiveBalanceUpdates_aligned
    (maxAligned : preset.MAX_EFFECTIVE_BALANCE % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (holds : EffectiveBalancesAligned state)
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    EffectiveBalancesAligned after := by
  unfold processEffectiveBalanceUpdates at computed
  split at computed
  · cases computed
  exact foldlM_ok_invariant EffectiveBalancesAligned
    (fun _ _ _ before step => updateEffectiveBalance_aligned maxAligned before step) holds
    computed

/-- The update of one effective balance keeps the sizes. -/
theorem sameSizes_updateEffectiveBalance {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) : SameSizes state after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, rfl⟩ := computed
  exact sameSizes_setValidator _ _ _

theorem sameSizes_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : SameSizes state after := by
  unfold processEffectiveBalanceUpdates at computed
  split at computed
  · cases computed
  exact foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ sizes step => sizes.trans (sameSizes_updateEffectiveBalance step))
    (SameSizes.refl state) computed

/-! ## Registry updates and slashings -/

theorem sameSizes_updateRegistryEntry {config : Config} {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) : SameSizes state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · rw [liftAccessor_ok] at computed
    exact (sameSizes_setValidator _ _ _).trans (sameSizes_initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ sameSizes_setValidator _ _ _

theorem sameSizes_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : SameSizes state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact sameSizes_setValidator _ _ _

/-- The eligibility pass does not advance the slot. -/
theorem updateRegistryEntry_slot {config : Config} {index : Nat}
    (before : fork < .pectra)
    (computed : updateRegistryEntry config state index = .ok after) :
    after.slot = state.slot := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, queued, _, rest⟩ := computed
  split at rest
  · exact initiateValidatorExit_slot (state := state.setValidator index queued)
      before (liftAccessor_ok.mp rest)
  · simp only [pure, Except.pure, Except.ok.injEq] at rest
    subst after
    rfl

/-- Scheduling an activation does not advance the slot. -/
theorem activateValidator_slot {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : after.slot = state.slot := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  rfl

/-- Eligibility-queue updates leave activation and exit epochs unchanged. -/
theorem queueForActivation_active {validator queued : Validator} (epoch : Epoch)
    (computed : queueForActivation state validator = .ok queued) :
    isActiveValidator queued epoch = isActiveValidator validator epoch := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl
  · cases computed
    rfl

/-- Every index in the activation queue names a validator eligible in that state.

Sorting the queue changes order, not eligibility or registry identity. -/
theorem mem_activationQueue {index : ValidatorIndex}
    (member : index ∈ activationQueue state) :
    ∃ (position : Nat) (validator : Validator), position.toUInt64 = index ∧
      state.validators.data[position]? = some validator ∧
      isEligibleForActivation state validator = true := by
  simp only [activationQueue, List.mem_map, List.mem_mergeSort] at member
  obtain ⟨⟨eligibleEpoch, queuedIndex⟩, member, equal⟩ := member
  simp only [List.mem_filterMap] at member
  obtain ⟨⟨validator, position⟩, positionOk, selected⟩ := member
  split at selected
  · rename_i eligible
    simp only [Option.some.injEq, Prod.mk.injEq] at selected
    obtain ⟨_, rfl⟩ := selected
    refine ⟨position, validator, equal, ?_, eligible⟩
    simpa only [Array.getElem?_toList] using
      (List.mem_zipIdx_iff_getElem?.mp positionOk)
  · cases selected

/-- Updating an eligibility epoch and scheduling an ejection preserve past activity.

The registry pass cannot change committees for an epoch at or before its current epoch. -/
theorem updateRegistryEntry_active_of_past {config : Config} {index : Nat} {epoch : Epoch}
    {validator : Validator}
    (before : fork < .pectra) (found : getValidator state index.toUInt64 = .ok validator)
    (exactIndex : index.toUInt64.toNat = index)
    (past : epoch ≤ getCurrentEpoch state)
    (computed : updateRegistryEntry config state index = .ok after) :
    ∃ updated, getValidator after index.toUInt64 = .ok updated ∧
      isActiveValidator updated epoch = isActiveValidator validator epoch := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨old, oldOk, queued, queueOk, rest⟩ := computed
  have equal : old = validator := Except.ok.inj (oldOk.symm.trans found)
  subst old
  have queuedFound : getValidator (state.setValidator index queued) index.toUInt64 =
      .ok queued := by
    simpa only [exactIndex] using getValidator_setValidator_self found queued
  have active := queueForActivation_active epoch queueOk
  split at rest
  · obtain ⟨exited, exitedOk, same⟩ :=
      initiateValidatorExit_active_of_past before queuedFound past (liftAccessor_ok.mp rest)
    exact ⟨exited, exitedOk, same.trans active⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at rest
    subst after
    exact ⟨queued, queuedFound, active⟩

/-- One registry pass preserves all activity queries for a past epoch. -/
theorem updateRegistryEntry_active {config : Config} {index : Nat} {epoch : Epoch}
    (before : fork < .pectra) (exactIndex : index.toUInt64.toNat = index)
    (past : epoch ≤ getCurrentEpoch state)
    (computed : updateRegistryEntry config state index = .ok after) (other : ValidatorIndex) :
    (getValidator after other).map (isActiveValidator · epoch) =
      (getValidator state other).map (isActiveValidator · epoch) := by
  by_cases equal : other = index.toUInt64
  · subst other
    have read : ∃ validator, getValidator state index.toUInt64 = .ok validator := by
      simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨validator, found, _⟩ := computed
      exact ⟨validator, found⟩
    obtain ⟨validator, found⟩ := read
    obtain ⟨updated, updatedOk, active⟩ :=
      updateRegistryEntry_active_of_past before found exactIndex past computed
    rw [found, updatedOk]
    exact congrArg Except.ok active
  · simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨validator, _, queued, _, rest⟩ := computed
    have unchanged : getValidator (state.setValidator index queued) other =
        getValidator state other := by
      simpa only [exactIndex] using
        getValidator_setValidator_of_ne (state := state) equal queued
    split at rest
    · exact (initiateValidatorExit_active (state := state.setValidator index queued)
        before past (liftAccessor_ok.mp rest) other).trans
        (congrArg (fun read => read.map (isActiveValidator · epoch)) unchanged)
    · simp only [pure, Except.pure, Except.ok.injEq] at rest
      subst after
      rw [unchanged]

/-- A queued index reads back an eligible validator when registry indices fit in 64 bits. -/
theorem getValidator_of_mem_activationQueue {index : ValidatorIndex}
    (within : state.RegistryWithinLimit) (member : index ∈ activationQueue state) :
    ∃ validator, getValidator state index = .ok validator ∧
      isEligibleForActivation state validator = true := by
  obtain ⟨position, validator, equal, found, eligible⟩ := mem_activationQueue member
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exactIndex := toNat_toUInt64_of_lt within inside
  refine ⟨validator, ?_, eligible⟩
  unfold getValidator
  rw [← equal, exactIndex]
  simp only [found]

/-- The eligibility pass over a registry prefix preserves all past activity queries.

The prefix carries its registry bound so its natural-number indices cannot truncate. -/
theorem fold_updateRegistryEntry_active {config : Config} {indices : List Nat} {epoch : Epoch}
    (before : fork < .pectra) (within : state.RegistryWithinLimit)
    (inside : ∀ index ∈ indices, index < state.validators.data.size)
    (past : epoch ≤ getCurrentEpoch state)
    (computed : indices.foldlM (updateRegistryEntry config) state = .ok after)
    (other : ValidatorIndex) :
    (getValidator after other).map (isActiveValidator · epoch) =
      (getValidator state other).map (isActiveValidator · epoch) := by
  induction indices generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst after
    rfl
  | cons index rest ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    have sizes := sameSizes_updateRegistryEntry first
    have slot := updateRegistryEntry_slot before first
    have middleWithin : middle.RegistryWithinLimit := by
      unfold BeaconState.RegistryWithinLimit at within ⊢
      rw [sizes.1]
      exact within
    have middlePast : epoch ≤ getCurrentEpoch middle := by
      simpa only [getCurrentEpoch, slot] using past
    have kept := updateRegistryEntry_active before
      (toNat_toUInt64_of_lt within (inside index List.mem_cons_self)) past first other
    exact (ih middleWithin (fun i member => by
      rw [sizes.1]
      exact inside i (List.mem_cons_of_mem _ member)) middlePast tail).trans kept

/-- Each validator occurs only once in the activation queue.

Sorting reorders distinct registry positions without creating an additional occurrence. -/
theorem activationQueue_nodup (within : state.RegistryWithinLimit) :
    (activationQueue state).Nodup := by
  let entries := state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
    if isEligibleForActivation state validator then
      some (validator.activationEligibilityEpoch, index.toUInt64)
    else none
  have base : state.validators.data.toList.zipIdx.Pairwise (fun a b => a.2 < b.2) := by
    have := List.pairwise_lt_range' (s := 0) (n := state.validators.data.toList.length)
    rw [← List.zipIdx_map_snd 0] at this
    exact List.pairwise_map.mp this
  have distinct : entries.Pairwise (fun a b => a.2 ≠ b.2) := by
    apply List.Pairwise.filterMap _ ?_ (List.Pairwise.and_mem.mp base)
    rintro ⟨v, i⟩ ⟨w, j⟩ ⟨mi, mj, lt⟩ a ha b hb
    simp only [Option.ite_none_right_eq_some, Option.some.injEq] at ha hb
    obtain ⟨_, rfl⟩ := ha
    obtain ⟨_, rfl⟩ := hb
    have hi : i < state.validators.data.size := by simpa using (List.mem_zipIdx' mi).1
    have hj : j < state.validators.data.size := by simpa using (List.mem_zipIdx' mj).1
    intro equal
    have equalNat := congrArg UInt64.toNat equal
    rw [toNat_toUInt64_of_lt within hi, toNat_toUInt64_of_lt within hj] at equalNat
    omega
  have unique : (entries.map (·.2)).Nodup := List.pairwise_map.mpr distinct
  exact ((List.mergeSort_perm entries _).map (·.2)).nodup_iff.mpr unique

/-- An activation is scheduled strictly after the epoch that schedules it.

Its checked epoch calculation is exact, so activation cannot alter a current committee. -/
theorem activateValidator_scheduled {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) :
    ∃ validator activated,
      getValidator state index = .ok validator ∧
      getValidator after index = .ok activated ∧
      activated.activationEpoch.toNat = (getCurrentEpoch state).toNat + 1 +
        preset.MAX_SEED_LOOKAHEAD.toNat ∧
      activated = { validator with activationEpoch := activated.activationEpoch } := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, epoch, epochOk, rfl⟩ := computed
  simp only [computeActivationExitEpoch, bind_ok_iff, addChecked_ok_iff] at epochOk
  obtain ⟨next, nextOk, epochOk⟩ := epochOk
  refine ⟨validator, { validator with activationEpoch := epoch }, found,
    getValidator_setValidator_self found _, ?_, rfl⟩
  change epoch.toNat = (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat
  simp only [UInt64.toNat_one] at nextOk
  omega

/-- Scheduling an eligible validator does not change whether it is active in a past epoch.

The queue admits only validators with the far-future activation epoch. -/
theorem activateValidator_active_of_eligible {index : ValidatorIndex} {epoch : Epoch}
    {validator : Validator}
    (found : getValidator state index = .ok validator)
    (eligible : isEligibleForActivation state validator = true)
    (past : epoch ≤ getCurrentEpoch state)
    (computed : activateValidator state index = .ok after) :
    ∃ activated, getValidator after index = .ok activated ∧
      isActiveValidator activated epoch = isActiveValidator validator epoch := by
  obtain ⟨old, activated, oldOk, activatedOk, scheduled, fields⟩ :=
    activateValidator_scheduled computed
  have equal : old = validator := Except.ok.inj (oldOk.symm.trans found)
  subst old
  refine ⟨activated, activatedOk, ?_⟩
  have inactiveBefore : isActiveValidator validator epoch = false := by
    simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
    simp only [isActiveValidator, eligible.2, Bool.and_eq_false_iff]
    apply Or.inl
    apply Bool.eq_false_iff.mpr
    intro active
    have top : epoch ≤ FAR_FUTURE_EPOCH := UInt64.le_iff_toNat_le.mpr
      (by have := epoch.toNat_lt; change epoch.toNat ≤ 18446744073709551615; omega)
    have epochEq : epoch = FAR_FUTURE_EPOCH :=
      UInt64.le_antisymm top (of_decide_eq_true active)
    have pastNat := UInt64.le_iff_toNat_le.mp past
    have activatedBound := activated.activationEpoch.toNat_lt
    rw [epochEq] at pastNat
    change 18446744073709551615 ≤ (getCurrentEpoch state).toNat at pastNat
    omega
  have inactiveAfter : isActiveValidator activated epoch = false := by
    have pastNat := UInt64.le_iff_toNat_le.mp past
    have later : ¬activated.activationEpoch ≤ epoch := by
      rw [UInt64.le_iff_toNat_le]
      omega
    simp [isActiveValidator, later]
  exact inactiveAfter.trans inactiveBefore.symm

/-- Scheduling an eligible activation preserves every indexed activity query in a past epoch. -/
theorem activateValidator_active {index : ValidatorIndex} {epoch : Epoch} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (eligible : isEligibleForActivation state validator = true)
    (past : epoch ≤ getCurrentEpoch state)
    (computed : activateValidator state index = .ok after) (other : ValidatorIndex) :
    (getValidator after other).map (isActiveValidator · epoch) =
      (getValidator state other).map (isActiveValidator · epoch) := by
  by_cases equal : other = index
  · subst other
    obtain ⟨activated, activatedOk, active⟩ :=
      activateValidator_active_of_eligible found eligible past computed
    rw [found, activatedOk]
    exact congrArg Except.ok active
  · simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    rw [getValidator_setValidator_of_ne equal]

/-- Scheduling distinct eligible validators preserves activity in every past epoch. -/
theorem fold_activateValidator_active {indices : List ValidatorIndex} {epoch : Epoch}
    (unique : indices.Nodup)
    (eligible : ∀ index ∈ indices, ∃ validator,
      getValidator state index = .ok validator ∧ isEligibleForActivation state validator = true)
    (past : epoch ≤ getCurrentEpoch state)
    (computed : indices.foldlM activateValidator state = .ok after) (other : ValidatorIndex) :
    (getValidator after other).map (isActiveValidator · epoch) =
      (getValidator state other).map (isActiveValidator · epoch) := by
  induction indices generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst after
    rfl
  | cons index rest ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    obtain ⟨validator, found, allowed⟩ := eligible index List.mem_cons_self
    have kept := activateValidator_active found allowed past first other
    have slot := activateValidator_slot first
    have remaining : ∀ i ∈ rest, getValidator middle i = getValidator state i := by
      intro i member
      have distinct : i ≠ index := fun equal => (List.nodup_cons.mp unique).1 (equal ▸ member)
      simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at first
      obtain ⟨_, _, _, _, rfl⟩ := first
      exact getValidator_setValidator_of_ne distinct _
    have finalized : middle.finalizedCheckpoint = state.finalizedCheckpoint := by
      simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at first
      obtain ⟨_, _, _, _, rfl⟩ := first
      rfl
    have middleEligible : ∀ i ∈ rest, ∃ validator,
        getValidator middle i = .ok validator ∧
          isEligibleForActivation middle validator = true := by
      intro i member
      obtain ⟨v, read, allowed⟩ := eligible i (List.mem_cons_of_mem _ member)
      refine ⟨v, (remaining i member).trans read, ?_⟩
      simpa only [isEligibleForActivation, finalized] using allowed
    have middlePast : epoch ≤ getCurrentEpoch middle := by
      simpa only [getCurrentEpoch, slot] using past
    exact (ih (List.nodup_cons.mp unique).2 middleEligible middlePast tail).trans kept

/-- Registry processing preserves the active indices for every epoch at or before its own.

Activations and exits are scheduled later, so neither can change a counted committee. -/
theorem processRegistryUpdates_active {config : Config} {epoch : Epoch}
    (before : fork < .pectra) (within : state.RegistryWithinLimit)
    (past : epoch ≤ getCurrentEpoch state)
    (computed : processRegistryUpdates config state = .ok after) (other : ValidatorIndex) :
    (getValidator after other).map (isActiveValidator · epoch) =
      (getValidator state other).map (isActiveValidator · epoch) := by
  unfold processRegistryUpdates at computed
  split at computed
  · exact False.elim ((Nat.not_le_of_lt before) ‹_›)
  simp only [bind_ok_iff] at computed
  obtain ⟨middle, updated, activated⟩ := computed
  have kept := fold_updateRegistryEntry_active before within
    (fun _ member => List.mem_range.mp member) past updated other
  have sizes := foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ same step => same.trans (sameSizes_updateRegistryEntry step))
    (SameSizes.refl state) updated
  have slots := foldlM_ok_invariant (fun s => s.slot = state.slot)
    (fun _ _ _ same step => (updateRegistryEntry_slot before step).trans same) rfl updated
  have middleWithin : middle.RegistryWithinLimit := by
    unfold BeaconState.RegistryWithinLimit at within ⊢
    rw [sizes.1]
    exact within
  have middlePast : epoch ≤ getCurrentEpoch middle := by
    simpa only [getCurrentEpoch, slots] using past
  apply Eq.trans (fold_activateValidator_active
    (activationQueue_nodup middleWithin).take
    (fun index member => getValidator_of_mem_activationQueue middleWithin
      (List.mem_of_mem_take member)) middlePast activated other) kept

/-- From Deneb, an epoch activates at most the maximum, and at most the churn limit. -/
theorem getValidatorActivationChurnLimit_le {config : Config} :
    getValidatorActivationChurnLimit config state ≤ config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT ∧
      getValidatorActivationChurnLimit config state ≤ getValidatorChurnLimit config state :=
  ⟨Std.min_le_left, Std.min_le_right⟩

/-- A successful Phase 0 registry pass schedules at most its computed validator churn limit.

The limit is read after eligibility updates and ejections, as in the transition.

These are scheduled activations, not validators whose activation epoch is reached now. -/
theorem processRegistryUpdates_activation_budget {config : Config}
    (before : fork < .altair)
    (computed : processRegistryUpdates config state = .ok after) :
    ∃ updated indices,
      (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state =
        .ok updated ∧
      indices = (activationQueue updated).take (getValidatorChurnLimit config updated).toNat ∧
      indices.length ≤ (getValidatorChurnLimit config updated).toNat ∧
      indices.foldlM activateValidator updated = .ok after := by
  have notElectra : ¬Fork.pectra ≤ fork := fun le =>
    Nat.not_lt_of_ge le (Nat.lt_trans before (by decide))
  have notDeneb : ¬Fork.dencun ≤ fork := fun le =>
    Nat.not_lt_of_ge le (Nat.lt_trans before (by decide))
  simp only [processRegistryUpdates, notElectra, notDeneb, ↓reduceIte, bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  exact ⟨updated, _, updatedOk, rfl, List.length_take_le _ _, activated⟩

/-- The registry updates succeed only before Electra, and keep the sizes. -/
theorem processRegistryUpdates_ok {config : Config}
    (computed : processRegistryUpdates config state = .ok after) :
    fork < .pectra ∧ SameSizes state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · cases computed
  rename_i electra
  refine ⟨Nat.lt_of_not_le electra, ?_⟩
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  have first := foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ sizes step => sizes.trans (sameSizes_updateRegistryEntry step))
    (SameSizes.refl state) updatedOk
  exact foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ sizes step => sizes.trans (sameSizes_activateValidator step)) first activated

/-- Successful registry processing leaves the same ordered active indices for a past epoch. -/
theorem processRegistryUpdates_active_indices {config : Config} {epoch : Epoch}
    (before : fork < .pectra) (within : state.RegistryWithinLimit)
    (past : epoch ≤ getCurrentEpoch state)
    (computed : processRegistryUpdates config state = .ok after) :
    getActiveValidatorIndices after epoch = getActiveValidatorIndices state epoch := by
  have sizes := (processRegistryUpdates_ok computed).2
  have afterWithin : after.RegistryWithinLimit := by
    unfold BeaconState.RegistryWithinLimit at within ⊢
    rw [sizes.1]
    exact within
  apply getActiveValidatorIndices_congr within afterWithin
  intro index
  have equal := processRegistryUpdates_active before within past computed index
  simp only [getValidator] at equal
  cases old : state.validators.data[index.toNat]? <;>
    cases new : after.validators.data[index.toNat]? <;>
    simp only [old, new, Except.map] at equal <;>
    simp_all

theorem sameSizes_applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    SameSizes state after := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact sameSizes_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ SameSizes.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ SameSizes.refl _

/-- The delayed slashing penalty changes balances, not committee assignments. -/
theorem applySlashingPenalty_validators {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    after.validators = state.validators := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, rest⟩ := computed
  split at rest
  · simp only [bind_ok_iff] at rest
    obtain ⟨_, _, rest⟩ := rest
    split at rest
    · simp only [bind_ok_iff, liftAccessor_ok] at rest
      obtain ⟨_, _, _, _, lowered⟩ := rest
      exact decreaseBalance_validators lowered
    · cases rest
      rfl
  · cases rest
    rfl

/-- Applying all delayed slashing penalties leaves the validator registry unchanged. -/
theorem processSlashings_validators
    (computed : processSlashings state = .ok after) : after.validators = state.validators := by
  unfold processSlashings at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, applied⟩ := computed
  exact foldlM_ok_invariant (fun s => s.validators = state.validators)
    (fun _ _ _ same ok => (applySlashingPenalty_validators ok).trans same) rfl applied

/-- The slashings succeed only before Electra, and keep the sizes. -/
theorem processSlashings_ok (computed : processSlashings state = .ok after) :
    fork < .pectra ∧ SameSizes state after := by
  unfold processSlashings at computed
  split at computed
  · cases computed
  rename_i electra
  refine ⟨Nat.lt_of_not_le electra, ?_⟩
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, applied⟩ := computed
  exact foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ sizes step => sizes.trans (sameSizes_applySlashingPenalty step))
    (SameSizes.refl state) applied

/-! ## Resets and rotations -/

/-- The slashings reset clears the slashed balance of the next epoch, and nothing else. -/
theorem processSlashingsReset_eq (computed : processSlashingsReset state = .ok after) :
    ∃ nextEpoch : Epoch, nextEpoch.toNat = (getCurrentEpoch state).toNat + 1 ∧
      after = { state with
        slashings :=
          state.slashings.set! (nextEpoch % preset.EPOCHS_PER_SLASHINGS_VECTOR).toNat 0 } := by
  simp only [processSlashingsReset, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, ⟨_, sum⟩, rfl⟩ := computed
  exact ⟨nextEpoch, by simpa using sum, rfl⟩

/-- The RANDAO reset copies the mix of the current epoch to the next epoch, and nothing else. -/
theorem processRandaoMixesReset_eq (computed : processRandaoMixesReset state = .ok after) :
    ∃ (nextEpoch : Epoch) (mix : Bytes32), nextEpoch.toNat = (getCurrentEpoch state).toNat + 1 ∧
      getRandaoMix state (getCurrentEpoch state) = .ok mix ∧
      after = { state with
        randaoMixes :=
          state.randaoMixes.set! (nextEpoch % preset.EPOCHS_PER_HISTORICAL_VECTOR).toNat mix } := by
  simp only [processRandaoMixesReset, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, ⟨_, sum⟩, mix, mixOk, rfl⟩ := computed
  exact ⟨nextEpoch, mix, by simpa using sum, mixOk, rfl⟩

/-- Resetting the next mix preserves positions different from the next epoch's position.

The checked increment identifies the next epoch without modular wraparound. -/
theorem processRandaoMixesReset_mix_of_ne {epoch : Epoch}
    (computed : processRandaoMixesReset state = .ok after)
    (distinct : ∀ next : Epoch, next.toNat = (getCurrentEpoch state).toNat + 1 →
      (epoch % preset.EPOCHS_PER_HISTORICAL_VECTOR).toNat ≠
        (next % preset.EPOCHS_PER_HISTORICAL_VECTOR).toNat) :
    getRandaoMix after epoch = getRandaoMix state epoch := by
  obtain ⟨next, mix, nextEq, _, rfl⟩ := processRandaoMixesReset_eq computed
  simp only [getRandaoMix, readCircular]
  split
  · rfl
  · congr 1
    exact Vector.getElem_set!_ne (toNat_mod_lt ‹_›) (Ne.symm (distinct next nextEq))

/-- Epoch rotation preserves recent attester seeds when the lookahead separates mix writes. -/
theorem processRandaoMixesReset_attester_seed {epoch : Epoch}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (computed : processRandaoMixesReset state = .ok after)
    (recent : epoch = getCurrentEpoch state ∨ epoch.toNat + 1 = (getCurrentEpoch state).toNat) :
    getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
  apply getSeed_congr
  intro shifted shiftedOk
  exact processRandaoMixesReset_mix_of_ne computed
    (attester_seed_positions positive history recent shiftedOk).2

/-- Mainnet epoch rotation preserves the attester seed of the current or previous epoch. -/
theorem processRandaoMixesReset_mainnet_attester_seed
    {state after : BeaconState Preset.mainnet fork} {epoch : Epoch}
    (computed : processRandaoMixesReset state = .ok after)
    (recent : epoch = getCurrentEpoch state ∨ epoch.toNat + 1 = (getCurrentEpoch state).toNat) :
    getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
  apply getSeed_congr
  intro shifted shiftedOk
  exact processRandaoMixesReset_mix_of_ne computed
    (mainnet_attester_seed_positions recent shiftedOk).2

/-- Before Altair, the rotation moves the pending attestations of the current epoch to the previous.

The current ones then start empty. -/
theorem processParticipationRecordUpdates_eq (before : fork < .altair) :
    ∃ after, processParticipationRecordUpdates state = .ok after ∧
      after.previousEpochAttestations before = state.currentEpochAttestations before ∧
      (after.currentEpochAttestations before).data = #[] ∧
      { after with
        previousEpochAttestations := state.previousEpochAttestations,
        currentEpochAttestations := state.currentEpochAttestations } = state := by
  have notAltair : ¬Fork.altair ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  refine ⟨{ state with
    previousEpochAttestations := state.currentEpochAttestations
    currentEpochAttestations := fun _ => ⟨#[], by simp⟩ }, ?_, rfl, rfl, rfl⟩
  simp only [processParticipationRecordUpdates, notAltair, ↓reduceIte]
  try rfl

/-- Rotation restores source matching when the new previous checkpoint names the old source.

Justification changes the current checkpoint before this rotation.

Only the previous checkpoint must still equal the source of the current pending list. -/
theorem processParticipationRecordUpdates_sources (before : fork < .altair)
    (sources : ∀ pending ∈ (state.currentEpochAttestations before).data,
      pending.data.source = state.previousJustifiedCheckpoint)
    (computed : processParticipationRecordUpdates state = .ok after) :
    PendingSourcesMatch after before := by
  obtain ⟨rotated, rotatedOk, previous, current, unchanged⟩ :=
    processParticipationRecordUpdates_eq (state := state) before
  rw [rotatedOk] at computed
  cases computed
  have previousCheckpoint := congrArg BeaconState.previousJustifiedCheckpoint unchanged
  constructor
  · intro pending member
    rw [current] at member
    simp at member
  · intro pending member
    rw [previous] at member
    rw [previousCheckpoint]
    exact sources pending member

end EthLib.Consensus
