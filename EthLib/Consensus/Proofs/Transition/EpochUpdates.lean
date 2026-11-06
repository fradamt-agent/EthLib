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
