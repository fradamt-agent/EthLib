module

public import EthLib.Consensus.Proofs.Transition.Invariants

/-!
# Proofs: the balance effects of a slashing, at every fork

A slashed validator pays two penalties, and the proposer that includes the slashing gets a reward.

The first penalty comes in `slashValidator`, when the validator is slashed.

It is the effective balance over `MIN_SLASHING_PENALTY_QUOTIENT` of the fork.

The same call pays the reward: the effective balance over the whistleblower quotient of the fork.

The proposer is the whistleblower by default, so the proposer gets the whole reward.

The reward splits into a proposer part and a whistleblower part.

Before Altair the proposer part is the reward over `PROPOSER_REWARD_QUOTIENT`.

From Altair it is `PROPOSER_WEIGHT / WEIGHT_DENOMINATOR` of the reward.

The second penalty comes in `processSlashings`, halfway through the time before it may withdraw.

It is proportional to the slashed balance of the recent epochs, times a multiplier of the fork.

Each theorem here gives the balances after the step at every index, in natural numbers.

A penalty saturates at zero, since a balance cannot go below zero.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config}

/-- Starting an exit keeps the balances. -/
theorem initiateValidatorExit_balances {state after : BeaconState preset fork}
    {index : ValidatorIndex} (computed : initiateValidatorExit config state index = .ok after) :
    after.balances = state.balances := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · rfl
  · obtain ⟨_, rfl⟩ := setValidator_ok set
    exact (exitQueue_validators queue).2

/-! ## The payout of one slashing -/

/-- The reward of a slashing: the effective balance over the whistleblower quotient of the fork. -/
def whistleblowerReward (preset : Preset) (fork : Base.Fork) (validator : Validator) : Gwei :=
  validator.effectiveBalance / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT

/-- The proposer part of a reward is at most the reward.

So the whistleblower part, the reward minus the proposer part, does not wrap. -/
theorem proposerShare_le {reward share : Gwei}
    (computed : proposerShare preset fork reward = .ok share) : share ≤ reward := by
  unfold proposerShare at computed
  split at computed
  · simp only [bind_ok_iff, liftArith, mapError_ok_iff, mulChecked_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨product, ⟨_, exact⟩, rfl⟩ := computed
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_div, exact]
    -- `PROPOSER_WEIGHT / WEIGHT_DENOMINATOR` is `8 / 64`, below one.
    simp only [PROPOSER_WEIGHT, WEIGHT_DENOMINATOR, UInt64.reduceToNat]
    omega
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_div]
    exact Nat.div_le_self _ _

/-- Starting an exit keeps the effective balance of the validator. -/
theorem initiateValidatorExit_effectiveBalance {state after : BeaconState preset fork}
    {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (computed : initiateValidatorExit config state index = .ok after) :
    ∃ exiting, getValidator after index = .ok exiting ∧
      exiting.effectiveBalance = validator.effectiveBalance := by
  obtain ⟨read, readOk, ⟨_, rfl⟩ | ⟨_, _, _, _, _, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact ⟨validator, found, rfl⟩
  · have same : read = validator := Except.ok.inj (readOk.symm.trans found)
    subst same
    exact ⟨_, getValidator_setValidator_self set, rfl⟩

/-- A slashing pays its whole reward to the proposer.

`penalized` is the state just before the reward.

The validator has started to exit, is slashed, and has paid the first penalty.

The proposer of that state gets the reward in two parts.

It gets its own part, then the whistleblower part, since it is the whistleblower too.

No other balance changes, and the sum does not overflow, since the call succeeded.

`penalized` has the balances of the state before the call, with the first penalty at the index.
-/
theorem slashValidator_payout {state after : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} (found : getValidator state index = .ok validator)
    (computed : slashValidator config state index = .ok after) :
    ∃ (penalized : BeaconState preset fork) (proposer : ValidatorIndex) (share : Gwei)
      (inside : proposer.toNat < penalized.balances.data.size),
      getBeaconProposerIndex penalized = .ok proposer ∧
      proposerShare preset fork (whistleblowerReward preset fork validator) = .ok share ∧
      share ≤ whistleblowerReward preset fork validator ∧
      after.validators = penalized.validators ∧
      penalized.balances.data[proposer.toNat].toNat +
        (whistleblowerReward preset fork validator).toNat < 2 ^ 64 ∧
      after.balances.data = penalized.balances.data.set proposer.toNat
        (penalized.balances.data[proposer.toNat] + whistleblowerReward preset fork validator)
        inside ∧
      ∃ slashedInside : index.toNat < state.balances.data.size,
        penalized.balances.data = state.balances.data.set index.toNat
          (saturatingSub state.balances.data[index.toNat]
            (validator.effectiveBalance /
              (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT)) slashedInside := by
  unfold slashValidator at computed
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, read, readOk, _, _, marked, markedOk, _, _, _, _, _, _,
    penalized, penalizedOk, proposer, proposerOk, share, shareOk, raised, raisedOk, paid, paidOk,
    done⟩ := computed
  -- The reward reads the validator after its exit starts, which keeps its effective balance.
  obtain ⟨exiting, exitingOk, sameBalance⟩ := initiateValidatorExit_effectiveBalance found exitedOk
  have same : read = exiting := Except.ok.inj (readOk.symm.trans exitingOk)
  subst same
  have reward : read.effectiveBalance / (parameters preset fork).WHISTLEBLOWER_REWARD_QUOTIENT =
      whistleblowerReward preset fork validator := by
    rw [whistleblowerReward, sameBalance]
  rw [reward] at shareOk paidOk
  have below := proposerShare_le shareOk
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp raisedOk
  obtain ⟨_, fitsPaid, rfl⟩ := increaseBalance_eq_ok_iff.mp paidOk
  have last := slashValidator_last done
  -- Before the penalty, the exit and the slashed flag keep the balances.
  have markedBalances : marked.balances = state.balances := by
    have exitedBalances := initiateValidatorExit_balances exitedOk
    obtain ⟨_, rfl⟩ := setValidator_ok markedOk
    exact exitedBalances
  have penalty : read.effectiveBalance / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT =
      validator.effectiveBalance / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT := by
    rw [sameBalance]
  rw [penalty] at penalizedOk
  obtain ⟨slashedInside, penalizedEq⟩ := decreaseBalance_eq_ok_iff.mp penalizedOk
  refine ⟨penalized, proposer, share, inside, proposerOk, shareOk, below, last.1, ?_, ?_,
    ?_⟩
  · -- The two parts add up to the reward, since the proposer part is at most the reward.
    have partsNat := UInt64.le_iff_toNat_le.mp below
    simp only [BeaconState.putBalance, Option.getD_none, Array.getElem_set_self] at fitsPaid
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ below, Nat.mod_eq_of_lt fits] at fitsPaid
    omega
  · rw [last.2]
    simp only [BeaconState.putBalance, Option.getD_none, Array.getElem_set_self, Array.set_set]
    congr 1
    -- In arithmetic modulo `2^64` the two parts add up to the reward.
    rw [UInt64.add_assoc, UInt64.add_comm share, UInt64.sub_add_cancel]
  · refine ⟨by simpa [markedBalances] using slashedInside, ?_⟩
    rw [penalizedEq]
    simp only [BeaconState.putBalance, markedBalances]

/-! ## The balances after a slashing -/

/-- The first penalty of a slashed validator: its effective balance over the quotient of the fork.
-/
def initialSlashingPenalty (preset : Preset) (fork : Base.Fork) (validator : Validator) : Nat :=
  validator.effectiveBalance.toNat / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT.toNat

/-- The balances after a slashing, at every index.

The slashed validator pays `initialSlashingPenalty`, saturating at zero.

Then the proposer gets the whole reward, as both proposer and whistleblower.

The proposer is that of `penalized`, the state just before the reward.

No other balance changes. -/
theorem slashValidator_balances {state after : BeaconState preset fork} {index : ValidatorIndex}
    {validator : Validator} (found : getValidator state index = .ok validator)
    (computed : slashValidator config state index = .ok after) :
    ∃ (penalized : BeaconState preset fork) (proposer : ValidatorIndex),
      getBeaconProposerIndex penalized = .ok proposer ∧
      ∀ position, (after.balances.data[position]?).map UInt64.toNat =
        (state.balances.data[position]?).map fun balance =>
          balance.toNat -
              (if position = index.toNat then initialSlashingPenalty preset fork validator
                else 0) +
            (if position = proposer.toNat then (whistleblowerReward preset fork validator).toNat
              else 0) := by
  obtain ⟨penalized, proposer, _, inside, proposerOk, _, _, _, fits, paid, slashedInside,
    lowered⟩ := slashValidator_payout found computed
  refine ⟨penalized, proposer, proposerOk, fun position => ?_⟩
  have penaltyNat : (validator.effectiveBalance /
      (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT).toNat =
      initialSlashingPenalty preset fork validator := UInt64.toNat_div _ _
  -- The balances before the reward: the penalty at the index of the slashed validator.
  have before : ∀ other, penalized.balances.data[other]? =
      if index.toNat = other then
        some (saturatingSub state.balances.data[index.toNat]
          (validator.effectiveBalance / (parameters preset fork).MIN_SLASHING_PENALTY_QUOTIENT))
      else state.balances.data[other]? := by
    intro other
    rw [lowered, Array.getElem?_set]
  have slashedRead : state.balances.data[index.toNat]? = some state.balances.data[index.toNat] :=
    Array.getElem?_eq_getElem slashedInside
  -- The reward does not overflow, so it adds to the balance in natural numbers.
  have rewardNat : (penalized.balances.data[proposer.toNat] +
      whistleblowerReward preset fork validator).toNat =
      penalized.balances.data[proposer.toNat].toNat +
        (whistleblowerReward preset fork validator).toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have proposerRead := before proposer.toNat
  rw [Array.getElem?_eq_getElem inside] at proposerRead
  rw [paid, Array.getElem?_set]
  by_cases atProposer : proposer.toNat = position
  · subst atProposer
    simp only [↓reduceIte, Option.map_some, rewardNat]
    by_cases atSlashed : index.toNat = proposer.toNat
    · simp only [atSlashed, ↓reduceIte, Option.some.injEq] at proposerRead
      have read : state.balances.data[proposer.toNat]? =
          some state.balances.data[index.toNat] := atSlashed ▸ slashedRead
      rw [proposerRead, read]
      simp [toNat_saturatingSub, penaltyNat, atSlashed.symm]
    · simp only [atSlashed, ↓reduceIte] at proposerRead
      rw [← proposerRead]
      simp [Ne.symm atSlashed]
  · simp only [atProposer, ↓reduceIte]
    rw [before position]
    by_cases atSlashed : index.toNat = position
    · subst atSlashed
      simp [slashedRead, toNat_saturatingSub, penaltyNat, Ne.symm atProposer]
    · simp [atSlashed, Ne.symm atSlashed, Ne.symm atProposer]

/-! ## The penalty at the end of the slashing period -/

/-- An amount that a slashed validator pays at the epoch when it is due, and zero otherwise.

It is due half the vector of slashings before the withdrawable epoch of the validator. -/
def dueSlashingAmount (preset : Preset) (epoch : Epoch) (validator : Validator) (amount : Nat) :
    Nat :=
  if validator.slashed = true ∧ epoch.toNat + preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 =
      validator.withdrawableEpoch.toNat then amount
  else 0

/-- The penalty of `processSlashings` on one validator, in Gwei.

`total` is the total active balance.

`adjusted` is the slashed balance of the recent epochs times the multiplier of the fork.

It is at most `total`.

Before Electra the penalty is the increments of the validator times `adjusted / total`.

It is rounded down to a whole increment.

From Electra it is the increments times a penalty per increment.

That penalty per increment is `adjusted` over the increments of `total`. -/
def epochSlashingPenalty (preset : Preset) (fork : Base.Fork) (epoch : Epoch)
    (total adjusted : Nat) : Option Validator → Nat
  | none => 0
  | some validator =>
    let increment := preset.EFFECTIVE_BALANCE_INCREMENT.toNat
    let increments := validator.effectiveBalance.toNat / increment
    dueSlashingAmount preset epoch validator
      (if .pectra ≤ fork then adjusted / (total / increment) * increments
        else increments * adjusted / total * increment)

/-- One step of `processSlashings` lowers one balance by the amount that it computes, if due.

It keeps the validators and the slot, and every other balance. -/
private theorem slashingStep {state after : BeaconState preset fork} {index : Nat}
    {validator : Validator} (found : state.validators.data[index]? = some validator)
    (small : state.validators.data.size < 2 ^ 64)
    (compute : Validator → Except TransitionError Gwei) (amount : Nat)
    (exact : ∀ penalty, compute validator = .ok penalty → penalty.toNat = amount)
    (computed : (do
      let validator ← liftAccessor (getValidator state index.toUInt64)
      if validator.slashed then
        let due ← liftAccessor (liftArith
          (addChecked (getCurrentEpoch state) (preset.EPOCHS_PER_SLASHINGS_VECTOR / 2)))
        if due = validator.withdrawableEpoch then
          let penalty ← compute validator
          liftAccessor (decreaseBalance state index.toUInt64 penalty)
        else pure state
      else pure state : Except TransitionError (BeaconState preset fork)) = .ok after) :
    after.validators = state.validators ∧ after.slot = state.slot ∧
      ∀ position, (after.balances.data[position]?).map UInt64.toNat =
        (state.balances.data[position]?).map fun balance => balance.toNat -
          if position = index then dueSlashingAmount preset (getCurrentEpoch state) validator amount
          else 0 := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exactIndex : index.toUInt64.toNat = index := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
  have read : getValidator state index.toUInt64 = .ok validator := by
    simp [getValidator, exactIndex, found]
  -- When nothing is due, the state stays, and the amount is zero.
  have unchanged : ¬(validator.slashed = true ∧ (getCurrentEpoch state).toNat +
      preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 = validator.withdrawableEpoch.toNat) →
      after = state →
      after.validators = state.validators ∧ after.slot = state.slot ∧
      ∀ position, (after.balances.data[position]?).map UInt64.toNat =
        (state.balances.data[position]?).map fun balance => balance.toNat -
          if position = index then dueSlashingAmount preset (getCurrentEpoch state) validator amount
          else 0 := by
    rintro notDue rfl
    refine ⟨rfl, rfl, fun position => ?_⟩
    simp [dueSlashingAmount, notDue]
  simp only [bind_ok_iff, liftAccessor_ok, read, Except.ok.injEq, exists_eq_left'] at computed
  split at computed
  · rename_i slashed
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff]
      at computed
    obtain ⟨due, ⟨_, dueNat⟩, computed⟩ := computed
    rw [UInt64.toNat_div] at dueNat
    split at computed
    · rename_i atDue
      simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨penalty, penaltyOk, lowered⟩ := computed
      obtain ⟨balanceInside, rfl⟩ := decreaseBalance_eq_ok_iff.mp lowered
      have isDue : validator.slashed = true ∧ (getCurrentEpoch state).toNat +
          preset.EPOCHS_PER_SLASHINGS_VECTOR.toNat / 2 = validator.withdrawableEpoch.toNat :=
        ⟨slashed, by rw [← atDue, dueNat]; rfl⟩
      refine ⟨rfl, rfl, fun position => ?_⟩
      simp only [BeaconState.putBalance, Array.getElem?_set, exactIndex]
      by_cases same : index = position
      · subst same
        simp [Array.getElem?_eq_getElem (exactIndex ▸ balanceInside), toNat_saturatingSub,
          exact penalty penaltyOk, dueSlashingAmount, isDue]
      · simp [same, Ne.symm same]
    · rename_i notAtDue
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      refine unchanged (fun ⟨_, equal⟩ => notAtDue ?_) computed.symm
      apply UInt64.toNat_inj.mp
      rw [dueNat]
      exact equal
  · rename_i notSlashed
    simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact unchanged (fun ⟨slashed, _⟩ => notSlashed slashed) computed.symm

/-- A fold whose steps each lower one balance, at distinct indices, lowers each balance once.

The steps keep the validators and the slot. -/
private theorem foldlM_slashingSteps {α : Type} {state : BeaconState preset fork}
    {step : BeaconState preset fork → Nat → Except α (BeaconState preset fork)}
    (penalty : Nat → Nat) (indices : List Nat)
    (each : ∀ current next index, index ∈ indices → current.validators = state.validators →
      current.slot = state.slot → step current index = .ok next →
      next.validators = current.validators ∧ next.slot = current.slot ∧
      ∀ position, (next.balances.data[position]?).map UInt64.toNat =
        ((current.balances.data[position]?).map UInt64.toNat).map fun balance =>
          balance - if position = index then penalty index else 0) :
    ∀ {current after : BeaconState preset fork}, indices.Nodup →
      current.validators = state.validators → current.slot = state.slot →
      indices.foldlM step current = .ok after →
      after.validators = state.validators ∧ after.slot = state.slot ∧
      ∀ position, (after.balances.data[position]?).map UInt64.toNat =
        ((current.balances.data[position]?).map UInt64.toNat).map fun balance =>
          balance - if position ∈ indices then penalty position else 0 := by
  induction indices with
  | nil =>
    intro current after _ validators slot computed
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨validators, slot, fun position => by simp [Option.map_map]; rfl⟩
  | cons index rest more =>
    intro current after unique validators slot computed
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    obtain ⟨middleValidators, middleSlot, middleBalances⟩ :=
      each current middle index List.mem_cons_self validators slot first
    obtain ⟨afterValidators, afterSlot, afterBalances⟩ :=
      more (fun current next index member => each current next index
        (List.mem_cons_of_mem _ member)) restUnique (middleValidators.trans validators)
        (middleSlot.trans slot) tail
    refine ⟨afterValidators, afterSlot, fun position => ?_⟩
    rw [afterBalances, middleBalances, Option.map_map]
    congr 1
    funext balance
    -- The index of this step is not in the rest, so at most one step lowers each balance.
    by_cases same : position = index
    · subst same
      simp [absent]
    · by_cases later : position ∈ rest
      · simp [same, later]
      · simp [same, later]

/-- The balances after the slashing penalties of an epoch, at every index.

Each validator pays `epochSlashingPenalty`, saturating at zero.

`total` is the total active balance, and `slashedSum` the slashed balance of the recent epochs.

The registry must be below `2^64`, so that each position is its own index of 64 bits.

Before Gloas that holds by the limit of the registry, see `validators_size_lt_of_before`. -/
theorem processSlashings_balances {state after : BeaconState preset fork}
    (small : state.validators.data.size < 2 ^ 64)
    (computed : processSlashings state = .ok after) :
    ∃ total slashedSum : Gwei,
      getTotalActiveBalance state = .ok total ∧ slashingsSum state = .ok slashedSum ∧
      after.validators = state.validators ∧
      ∀ position : Nat, (after.balances.data[position]?).map UInt64.toNat =
        (state.balances.data[position]?).map fun balance => balance.toNat -
          epochSlashingPenalty preset fork (getCurrentEpoch state) total.toNat
            (min (slashedSum.toNat *
              (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat) total.toNat)
            state.validators.data[position]? := by
  unfold processSlashings at computed
  simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff] at computed
  obtain ⟨total, totalOk, slashedSum, sumOk, slashed, slashedOk, computed⟩ := computed
  have slashedNat := (mulChecked_ok_iff.mp slashedOk).2
  -- The adjusted slashed balance, at most the total, in natural numbers.
  have adjustedNat : (min slashed total).toNat = min (slashedSum.toNat *
      (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat) total.toNat := by
    rw [← slashedNat, UInt64.min_def]
    split
    · rename_i le
      exact (Nat.min_eq_left (UInt64.le_iff_toNat_le.mp le)).symm
    · rename_i notLe
      exact (Nat.min_eq_right (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp
        (UInt64.not_le.mp notLe)))).symm
  refine ⟨total, slashedSum, totalOk, sumOk, ?_⟩
  -- The penalty of each position, read from the validators before the step.
  let penalty := fun position : Nat => epochSlashingPenalty preset fork (getCurrentEpoch state)
    total.toNat (min (slashedSum.toNat *
      (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat) total.toNat)
    state.validators.data[position]?
  -- Each step lowers the balance at its position by that penalty.
  have conclude : ∀ (step : BeaconState preset fork → Nat → Except TransitionError _),
      (∀ current next index, index ∈ List.range state.validators.data.size →
        current.validators = state.validators → current.slot = state.slot →
        step current index = .ok next →
        next.validators = current.validators ∧ next.slot = current.slot ∧
        ∀ position, (next.balances.data[position]?).map UInt64.toNat =
          ((current.balances.data[position]?).map UInt64.toNat).map fun balance =>
            balance - if position = index then penalty index else 0) →
      (List.range state.validators.data.size).foldlM step state = .ok after →
      after.validators = state.validators ∧
      ∀ position : Nat, (after.balances.data[position]?).map UInt64.toNat =
        (state.balances.data[position]?).map fun balance => balance.toNat - penalty position := by
    intro step each folded
    obtain ⟨validators, _, balances⟩ :=
      foldlM_slashingSteps penalty _ each List.nodup_range rfl rfl folded
    refine ⟨validators, fun position => ?_⟩
    rw [balances, Option.map_map]
    congr 1
    funext balance
    -- Past the registry no validator pays, so its penalty is zero.
    by_cases inside : position < state.validators.data.size
    · simp [List.mem_range, inside]
    · simp [List.mem_range, inside, penalty, epochSlashingPenalty]
  -- A step reads the validator at its position, the same as before the steps.
  have reading : ∀ (current : BeaconState preset fork) (index : Nat),
      index ∈ List.range state.validators.data.size → current.validators = state.validators →
      ∃ validator, current.validators.data[index]? = some validator ∧
        state.validators.data[index]? = some validator ∧
        current.validators.data.size < 2 ^ 64 := by
    intro current index member same
    rw [List.mem_range] at member
    exact ⟨_, by rw [same]; exact Array.getElem?_eq_getElem member,
      Array.getElem?_eq_getElem member, by rw [same]; exact small⟩
  have epochSame : ∀ current : BeaconState preset fork, current.slot = state.slot →
      getCurrentEpoch current = getCurrentEpoch state := by
    intro current slot
    simp [getCurrentEpoch, slot]
  split at computed
  · rename_i electra
    simp only [bind_ok_iff, liftAccessor_ok, mapError_ok_iff] at computed
    obtain ⟨perIncrement, perOk, folded⟩ := computed
    obtain ⟨increments, incrementsOk, perOk⟩ := perOk
    obtain ⟨_, incrementsNat⟩ := divChecked_ok_iff.mp incrementsOk
    obtain ⟨_, perNat⟩ := divChecked_ok_iff.mp perOk
    refine conclude _ (fun current next index member validators slot ok => ?_) folded
    obtain ⟨validator, found, original, currentSmall⟩ := reading current index member validators
    unfold applySlashingPenaltyElectra at ok
    have stepped := slashingStep found currentSmall
      (fun validator => liftAccessor (liftArith (mulChecked perIncrement
        (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT))))
      (perIncrement.toNat * (validator.effectiveBalance.toNat /
        preset.EFFECTIVE_BALANCE_INCREMENT.toNat))
      (fun penalty penaltyOk => by
        simp only [liftAccessor_ok, liftArith, mapError_ok_iff, mulChecked_ok_iff] at penaltyOk
        rw [penaltyOk.2, UInt64.toNat_div])
      ok
    obtain ⟨nextValidators, nextSlot, balances⟩ := stepped
    refine ⟨nextValidators, nextSlot, fun position => ?_⟩
    rw [balances, Option.map_map]
    congr 1
    funext balance
    simp only [Function.comp, epochSlashingPenalty, penalty, original, epochSame current slot,
      electra, ↓reduceIte]
    rw [perNat, adjustedNat, incrementsNat]
  · rename_i notElectra
    refine conclude _ (fun current next index member validators slot ok => ?_) computed
    obtain ⟨validator, found, original, currentSmall⟩ := reading current index member validators
    unfold applySlashingPenalty at ok
    have stepped := slashingStep found currentSmall
      (fun validator => do
        let numerator ← liftAccessor (liftArith (mulChecked
          (validator.effectiveBalance / preset.EFFECTIVE_BALANCE_INCREMENT) (min slashed total)))
        liftAccessor (liftArith (mulChecked (numerator / total)
          preset.EFFECTIVE_BALANCE_INCREMENT)))
      (validator.effectiveBalance.toNat / preset.EFFECTIVE_BALANCE_INCREMENT.toNat *
        (min slashed total).toNat / total.toNat * preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
      (fun penalty penaltyOk => by
        simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
          mulChecked_ok_iff] at penaltyOk
        obtain ⟨numerator, ⟨_, numeratorNat⟩, _, penaltyNat⟩ := penaltyOk
        rw [penaltyNat, UInt64.toNat_div, numeratorNat, UInt64.toNat_div])
      (by simpa only [bind_assoc] using ok)
    obtain ⟨nextValidators, nextSlot, balances⟩ := stepped
    refine ⟨nextValidators, nextSlot, fun position => ?_⟩
    rw [balances, Option.map_map]
    congr 1
    funext balance
    simp only [Function.comp, epochSlashingPenalty, penalty, original, epochSame current slot,
      notElectra, ↓reduceIte, adjustedNat]

/-- Before Gloas the limit of the registry keeps it below `2^64` validators.

So `processSlashings_balances` applies to every state of those forks. -/
theorem validators_size_lt_of_before {state : BeaconState preset fork}
    (before : fork < .glamsterdam) : state.validators.data.size < 2 ^ 64 :=
  Nat.lt_of_le_of_lt (state.validators.bound before) (UInt64.toNat_lt _)

end EthLib.Consensus
