module

public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Transition.EpochUpdates

/-!
# Proofs: the other steps of the epoch transition

An updated effective balance is the old one, or the balance rounded down to an increment and capped.

The effective balances are aligned when each is a whole number of increments, at most its largest.

When each largest value is itself a whole number of increments, the update keeps them aligned.

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

/-- An updated effective balance is the old one, or the balance rounded down and capped. -/
theorem updatedEffectiveBalance_cases {largest balance effectiveBalance result : Gwei}
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result = effectiveBalance ∨
      result = min (balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT) largest := by
  simp only [updatedEffectiveBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, leaves, _, rfl⟩ := computed
  cases leaves
  · exact .inl rfl
  · exact .inr rfl

/-- Every effective balance is a whole number of increments, and at most its largest at the fork.
-/
def EffectiveBalancesAligned (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data.toList,
    validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator

/-- An updated effective balance is aligned when the old one and the largest are. -/
theorem updatedEffectiveBalance_aligned {largest balance effectiveBalance result : Gwei}
    (maxAligned : largest % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (old : effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧ effectiveBalance ≤ largest)
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧ result ≤ largest := by
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact old
  · rw [UInt64.min_def]
    split
    · exact ⟨sub_mod_mod_self _ _, by assumption⟩
    · exact ⟨maxAligned, UInt64.le_refl _⟩

/-- Replacing a validator by an aligned one keeps the effective balances aligned. -/
theorem effectiveBalancesAligned_setValidator {index : ValidatorIndex} {validator : Validator}
    (holds : EffectiveBalancesAligned state)
    (good : validator.effectiveBalance % preset.EFFECTIVE_BALANCE_INCREMENT = 0 ∧
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator)
    (set : state.setValidator index validator = .ok after) :
    EffectiveBalancesAligned after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  intro other member
  simp only [BeaconState.putValidator, RootedForkList.data_set, Array.toList_set] at member
  rcases List.mem_or_eq_of_mem_set member with old | rfl
  · exact holds other old
  · exact good

/-- The update of one effective balance keeps them aligned, when each largest is aligned. -/
theorem updateEffectiveBalance_aligned {index : Nat}
    (maxAligned : ∀ validator,
      withdrawalMaxEffectiveBalance preset fork validator % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (holds : EffectiveBalancesAligned state)
    (computed : updateEffectiveBalance state index = .ok after) :
    EffectiveBalancesAligned after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, effectiveBalance, updated, set⟩ := computed
  refine effectiveBalancesAligned_setValidator holds ?_ set
  apply updatedEffectiveBalance_aligned (maxAligned validator) _ updated
  unfold getValidator at found
  split at found
  · rename_i read
    cases found
    exact holds _ (Array.mem_toList_iff.mpr (Array.mem_of_getElem? read))
  · cases found

/-- The update of the effective balances keeps them aligned.

The largest effective balance of each validator must be a whole number of increments. -/
theorem processEffectiveBalanceUpdates_aligned
    (maxAligned : ∀ validator,
      withdrawalMaxEffectiveBalance preset fork validator % preset.EFFECTIVE_BALANCE_INCREMENT = 0)
    (holds : EffectiveBalancesAligned state)
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    EffectiveBalancesAligned after := by
  unfold processEffectiveBalanceUpdates at computed
  exact foldlM_ok_invariant EffectiveBalancesAligned
    (fun _ _ _ before step => updateEffectiveBalance_aligned maxAligned before step) holds
    computed

/-- The update of one effective balance keeps the sizes. -/
theorem sameSizes_updateEffectiveBalance {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) : SameSizes state after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, set⟩ := computed
  exact sameSizes_setValidator set

theorem sameSizes_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : SameSizes state after := by
  unfold processEffectiveBalanceUpdates at computed
  exact foldlM_ok_invariant (SameSizes state)
    (fun _ _ _ sizes step => sizes.trans (sameSizes_updateEffectiveBalance step))
    (SameSizes.refl state) computed

/-! ## Registry updates and slashings -/

theorem sameSizes_updateRegistryEntry {config : Config} {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) : SameSizes state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, set, computed⟩ := computed
  split at computed
  · rw [liftAccessor_ok] at computed
    exact (sameSizes_setValidator set).trans (sameSizes_initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ sameSizes_setValidator set

theorem sameSizes_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : SameSizes state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, set⟩ := computed
  exact sameSizes_setValidator set

/-- The activation churn limit is at most the configured maximum and the validator churn limit. -/
theorem getValidatorActivationChurnLimit_le {config : Config} :
    getValidatorActivationChurnLimit config state ≤ config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT ∧
      getValidatorActivationChurnLimit config state ≤ getValidatorChurnLimit config state :=
  ⟨Std.min_le_left, Std.min_le_right⟩

/-- The activation epoch at an index, or the accessor error outside the registry. -/
def activationEpochAt (state : BeaconState preset fork) (index : ValidatorIndex) :
    Except AccessorError Epoch :=
  (getValidator state index).map (·.activationEpoch)

/-- A write of one validator leaves every other activation epoch unchanged. -/
theorem activationEpochAt_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) (other : ValidatorIndex) :
    activationEpochAt after other =
      if other = index then .ok validator.activationEpoch else activationEpochAt state other := by
  by_cases equal : other = index
  · subst other
    simp [activationEpochAt, getValidator_setValidator_self set, Except.map]
  · simp [activationEpochAt, getValidator_setValidator_of_ne set equal, equal]

/-- Before Electra, starting an exit keeps the slot and all activation epochs. -/
theorem initiateValidatorExit_activationEpochs {config : Config} {index : ValidatorIndex}
    (before : fork < .pectra)
    (computed : initiateValidatorExit config state index = .ok after) :
    after.slot = state.slot ∧
      ∀ other, activationEpochAt after other = activationEpochAt state other := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact ⟨rfl, fun _ => rfl⟩
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt before
  -- Before Electra the exit queue changes no state field.
  simp only [exitQueue, notElectra, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at queue
  obtain ⟨_, _, rfl, _⟩ := queue
  refine ⟨setValidator_slot set, fun other => ?_⟩
  rw [activationEpochAt_setValidator set]
  split
  · rename_i equal
    subst other
    simp [activationEpochAt, found, Except.map]
  · rfl

/-- The first registry pass keeps the slot and all activation epochs. -/
theorem updateRegistryEntry_activationEpochs {config : Config} {index : Nat}
    (before : fork < .pectra)
    (computed : updateRegistryEntry config state index = .ok after) :
    after.slot = state.slot ∧
      ∀ other, activationEpochAt after other = activationEpochAt state other := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, joined, middle, set, rest⟩ := computed
  -- Joining the queue changes eligibility, not the activation epoch.
  have kept : queued.activationEpoch = validator.activationEpoch := by
    unfold queueForActivation at joined
    split at joined
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at joined
      obtain ⟨_, _, rfl⟩ := joined
      rfl
    · cases joined
      rfl
  have first : ∀ other, activationEpochAt middle other = activationEpochAt state other := by
    intro other
    rw [activationEpochAt_setValidator set]
    split
    · rename_i equal
      subst other
      simp [activationEpochAt, found, kept, Except.map]
    · rfl
  split at rest
  · rw [liftAccessor_ok] at rest
    obtain ⟨slot, epochs⟩ := initiateValidatorExit_activationEpochs before rest
    exact ⟨slot.trans (setValidator_slot set), fun other => (epochs other).trans (first other)⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at rest
    subst after
    exact ⟨setValidator_slot set, first⟩

/-- Activating one validator writes the computed epoch and leaves every other activation epoch. -/
theorem activateValidator_activationEpochs {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) :
    ∃ epoch, computeActivationExitEpoch preset (getCurrentEpoch state) = .ok epoch ∧
      after.slot = state.slot ∧
      ∀ other, activationEpochAt after other =
        if other = index then .ok epoch else activationEpochAt state other := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff] at computed
  obtain ⟨_, _, epoch, calculated, set⟩ := computed
  exact ⟨epoch, calculated, setValidator_slot set, activationEpochAt_setValidator set⟩

/-- A successful activation pass writes the computed epoch at its selected indices.

With no selected index the computation need not succeed, since the pass never calls it. -/
theorem foldlM_activateValidator_activationEpochs {indices : List ValidatorIndex}
    (computed : indices.foldlM activateValidator state = .ok after) :
    after.slot = state.slot ∧
      (∀ other, other ∉ indices → activationEpochAt after other = activationEpochAt state other) ∧
      (∀ other, other ∈ indices → ∃ epoch,
        computeActivationExitEpoch preset (getCurrentEpoch state) = .ok epoch ∧
          activationEpochAt after other = .ok epoch) := by
  induction indices generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst after
    exact ⟨rfl, fun _ _ => rfl, by simp⟩
  | cons index indices ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, rest⟩ := computed
    obtain ⟨epoch, calculated, slot, epochs⟩ := activateValidator_activationEpochs step
    obtain ⟨lastSlot, unchanged, selected⟩ := ih rest
    have current : getCurrentEpoch middle = getCurrentEpoch state := by
      simp [getCurrentEpoch, slot]
    refine ⟨lastSlot.trans slot, ?_, ?_⟩
    · intro other outside
      have ne : other ≠ index := fun equal => outside (by simp [equal])
      rw [unchanged other (fun member => outside (by simp [member])), epochs other,
        ite_eq_right ne]
    · intro other member
      -- A later write wins, and the unchanged slot makes its computed epoch the same.
      by_cases tail : other ∈ indices
      · obtain ⟨value, valueOk, written⟩ := selected other tail
        exact ⟨value, current ▸ valueOk, written⟩
      · have equal : other = index := (List.mem_cons.mp member).resolve_right tail
        subst other
        exact ⟨epoch, calculated, by rw [unchanged index tail, epochs index, ite_eq_left rfl]⟩

/-- Before Electra, the registry writes activation epochs only in a bounded queue prefix.

The queue of the first pass orders eligibility epochs, then validator indices.

Phase 0 uses validator churn, and Deneb caps it as [EIP-7514] specifies.

A write need not change its old value for an arbitrary preset.

At epoch 0 with MAX_SEED_LOOKAHEAD = 2^64 - 2, the computed epoch is FAR_FUTURE_EPOCH.

A selected validator with that activation epoch therefore keeps its value.

With an empty prefix, the step does not compute an activation epoch at all.

[EIP-7514]: https://eips.ethereum.org/EIPS/eip-7514#specification
-/
theorem processRegistryUpdates_activationEpochs {config : Config}
    (before : fork < .pectra)
    (computed : processRegistryUpdates config state = .ok after) :
    ∃ updated : BeaconState preset fork,
      (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state =
        .ok updated ∧
      let limit := if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
        else getValidatorChurnLimit config updated
      let selected := (activationQueue updated).take limit.toNat
      selected.length ≤ limit.toNat ∧
      limit ≤ getValidatorChurnLimit config updated ∧
      (.dencun ≤ fork → limit ≤ config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT) ∧
      (∀ index, index ∉ selected →
        activationEpochAt after index = activationEpochAt state index) ∧
      (∀ index, index ∈ selected → ∃ epoch,
        computeActivationExitEpoch preset (getCurrentEpoch state) = .ok epoch ∧
          activationEpochAt after index = .ok epoch) := by
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt before
  simp only [processRegistryUpdates, notElectra, ↓reduceIte, bind_ok_iff] at computed
  obtain ⟨updated, first, last⟩ := computed
  -- The first pass leaves every input activation epoch and the current epoch unchanged.
  have kept := foldlM_ok_invariant
    (fun next : BeaconState preset fork => next.slot = state.slot ∧
      ∀ index, activationEpochAt next index = activationEpochAt state index)
    (fun _ _ _ holds step => by
      obtain ⟨slot, epochs⟩ := updateRegistryEntry_activationEpochs before step
      exact ⟨slot.trans holds.1, fun index => (epochs index).trans (holds.2 index)⟩)
    ⟨rfl, fun _ => rfl⟩ first
  obtain ⟨_, unchanged, written⟩ := foldlM_activateValidator_activationEpochs last
  refine ⟨updated, first, List.length_take_le .., ?_, ?_, ?_, ?_⟩
  · split
    · exact (getValidatorActivationChurnLimit_le).2
    · exact UInt64.le_refl _
  · intro deneb
    simp only [deneb, ↓reduceIte]
    exact (getValidatorActivationChurnLimit_le).1
  · intro index outside
    exact (unchanged index outside).trans (kept.2 index)
  · intro index member
    obtain ⟨epoch, calculated, value⟩ := written index member
    refine ⟨epoch, ?_, value⟩
    simpa only [getCurrentEpoch, kept.1] using calculated

/-- If the computed epoch differs from every selected old value, exactly the prefix changes. -/
theorem processRegistryUpdates_changedActivationEpochs_exact {config : Config}
    (before : fork < .pectra)
    (computed : processRegistryUpdates config state = .ok after) :
    ∃ updated : BeaconState preset fork,
      (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state =
        .ok updated ∧
      let limit := if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
        else getValidatorChurnLimit config updated
      let selected := (activationQueue updated).take limit.toNat
      ∀ epoch, computeActivationExitEpoch preset (getCurrentEpoch state) = .ok epoch →
        (∀ index ∈ selected, activationEpochAt state index ≠ .ok epoch) →
        ∀ index, activationEpochAt after index ≠ activationEpochAt state index ↔
          index ∈ selected := by
  obtain ⟨updated, first, _, _, _, unchanged, written⟩ :=
    processRegistryUpdates_activationEpochs before computed
  refine ⟨updated, first, ?_⟩
  dsimp only
  intro epoch calculated selectedOldValuesDiffer index
  constructor
  · intro changed
    by_cases member : index ∈ (activationQueue updated).take
        (if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
          else getValidatorChurnLimit config updated).toNat
    · exact member
    · exact False.elim (changed (unchanged index member))
  · intro member
    obtain ⟨value, valueOk, atIndex⟩ := written index member
    have equal : value = epoch := Except.ok.inj (valueOk.symm.trans calculated)
    rw [atIndex, equal]
    exact Ne.symm (selectedOldValuesDiffer index member)

theorem sameSizes_updateRegistryEntryElectra {config : Config} {activationEpoch : Epoch}
    {index : Nat}
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    SameSizes state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact sameSizes_setValidator set
  split at computed
  · rw [liftAccessor_ok] at computed
    exact sameSizes_initiateValidatorExit computed
  split at computed
  · rw [liftAccessor_ok] at computed
    exact sameSizes_setValidator computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ SameSizes.refl _

/-- The registry updates keep the sizes. -/
theorem sameSizes_processRegistryUpdates {config : Config}
    (computed : processRegistryUpdates config state = .ok after) : SameSizes state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact foldlM_ok_invariant (SameSizes state)
      (fun _ _ _ sizes step => sizes.trans (sameSizes_updateRegistryEntryElectra step))
      (SameSizes.refl state) computed
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

theorem sameSizes_applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (computed : applySlashingPenaltyElectra state perIncrement index = .ok after) :
    SameSizes state after := by
  simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, lowered⟩ := computed
      exact sameSizes_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ SameSizes.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ SameSizes.refl _

/-- The slashings keep the sizes. -/
theorem sameSizes_processSlashings (computed : processSlashings state = .ok after) :
    SameSizes state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact foldlM_ok_invariant (SameSizes state)
      (fun _ _ _ sizes step => sizes.trans (sameSizes_applySlashingPenaltyElectra step))
      (SameSizes.refl state) applied
  · exact foldlM_ok_invariant (SameSizes state)
      (fun _ _ _ sizes step => sizes.trans (sameSizes_applySlashingPenalty step))
      (SameSizes.refl state) computed

/-! ## Resets and rotations -/

/-- The slashings reset clears the slashed balance of the next epoch, and nothing else. -/
theorem processSlashingsReset_eq (computed : processSlashingsReset state = .ok after) :
    ∃ (nextEpoch : Epoch) (slashings : RootedVector Gwei preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat),
      nextEpoch.toNat = (getCurrentEpoch state).toNat + 1 ∧
      writeCircularRooted state.slashings nextEpoch 0 = .ok slashings ∧
      after = { state with slashings } := by
  simp only [processSlashingsReset, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, ⟨_, sum⟩, slashings, written, rfl⟩ := computed
  exact ⟨nextEpoch, slashings, by simpa using sum, written, rfl⟩

/-- The RANDAO reset copies the mix of the current epoch to the next epoch, and nothing else. -/
theorem processRandaoMixesReset_eq (computed : processRandaoMixesReset state = .ok after) :
    ∃ (nextEpoch : Epoch) (mix : Bytes32)
      (randaoMixes : RootedVector Bytes32 preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat),
      nextEpoch.toNat = (getCurrentEpoch state).toNat + 1 ∧
      getRandaoMix state (getCurrentEpoch state) = .ok mix ∧
      writeCircularRooted state.randaoMixes nextEpoch mix = .ok randaoMixes ∧
      after = { state with randaoMixes } := by
  simp only [processRandaoMixesReset, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, ⟨_, sum⟩, mix, mixOk, randaoMixes, written, rfl⟩ := computed
  exact ⟨nextEpoch, mix, randaoMixes, by simpa using sum, mixOk, written, rfl⟩

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

end EthLib.Consensus
