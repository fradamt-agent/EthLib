module

public import EthLib.Consensus.Proofs.Transition.EffectiveBalanceCap
public import EthLib.Consensus.Proofs.Transition.Lifecycle

/-!
# Proofs: how far an effective balance can fall, at every fork

An effective balance falls in one place: the update at the end of an epoch.

It falls only when the balance leaves the band of the hysteresis below it.

It then becomes the balance, rounded down to an increment.

So it never falls below the lowest balance, rounded down, that it is updated from.

Every other step keeps the effective balance of a validator with an activation epoch.

The upgrade to Electra sets to zero the effective balance of a validator with none.

Along a run, an effective balance is then at least the smaller of two values.

- Its value at the start.
- The lowest balance at a state of the run, rounded down to an increment.

So it falls below its start at most as far as the balance does, plus less than one increment.

The start must be reachable, so that every effective balance is under its cap.

From Gloas the registry at the end must be below `2^64`, as in `Lifecycle`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- A position below `2^64` is its own index of 64 bits. -/
private theorem toNat_toUInt64_of_lt_pow {position : Nat} (small : position < 2 ^ 64) :
    position.toUInt64.toNat = position := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]

/-- One validator, later in its life.

If it has an activation epoch, it keeps it, and its effective balance does not fall. -/
def HeldStep (validator later : Validator) : Prop :=
  validator.activationEpoch ≠ FAR_FUTURE_EPOCH →
    later.activationEpoch = validator.activationEpoch ∧
      validator.effectiveBalance ≤ later.effectiveBalance

theorem HeldStep.refl (validator : Validator) : HeldStep validator validator :=
  fun _ => ⟨rfl, UInt64.le_refl _⟩

theorem HeldStep.trans {first second third : Validator} (one : HeldStep first second)
    (two : HeldStep second third) : HeldStep first third := fun set =>
  have ⟨sameOne, leOne⟩ := one set
  have ⟨sameTwo, leTwo⟩ := two (sameOne ▸ set)
  ⟨sameTwo.trans sameOne, UInt64.le_trans leOne leTwo⟩

/-- The registry of a later state, which may be of a later fork.

It is at least as long.

While it has fewer than `2^64` validators, each validator is at its index.

If it had an activation epoch, it keeps it, and its effective balance does not fall. -/
structure EffectiveHeld {fork' : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') : Prop where
  size_le : state.validators.data.size ≤ after.validators.data.size
  validators : after.validators.data.size < 2 ^ 64 →
    ∀ (index : Nat) (validator : Validator), state.validators.data[index]? = some validator →
      ∃ later, after.validators.data[index]? = some later ∧ HeldStep validator later

namespace EffectiveHeld

theorem refl (state : BeaconState preset fork) : EffectiveHeld state state :=
  ⟨Nat.le_refl _, fun _ _ validator found => ⟨validator, found, .refl validator⟩⟩

theorem trans {fork' fork'' : Base.Fork} {first : BeaconState preset fork}
    {second : BeaconState preset fork'} {third : BeaconState preset fork''}
    (one : EffectiveHeld first second) (two : EffectiveHeld second third) :
    EffectiveHeld first third where
  size_le := Nat.le_trans one.size_le two.size_le
  validators small index validator found := by
    -- The middle registry is at most as long as the last one, so it is below `2^64` too.
    obtain ⟨middle, middleFound, oneStep⟩ :=
      one.validators (Nat.lt_of_le_of_lt two.size_le small) index validator found
    obtain ⟨later, laterFound, twoStep⟩ := two.validators small index middle middleFound
    exact ⟨later, laterFound, oneStep.trans twoStep⟩

/-- A state with the same validators, of any fork. -/
theorem of_data {fork' : Base.Fork} {after : BeaconState preset fork'}
    (same : after.validators.data = state.validators.data) : EffectiveHeld state after :=
  ⟨Nat.le_of_eq (by rw [same]), fun _ index validator found =>
    ⟨validator, by rw [same]; exact found, .refl _⟩⟩

/-- A step that keeps the validators at the indices of the registry, while it stays small.

Each index of the registry has a validator after it. -/
theorem of_read {after : BeaconState preset fork}
    (present : ∀ index, index < state.validators.data.size →
      (after.validators.data[index]?).isSome)
    (read : after.validators.data.size < 2 ^ 64 → ∀ index, index < state.validators.data.size →
      after.validators.data[index]? = state.validators.data[index]?) :
    EffectiveHeld state after where
  size_le := by
    refine Nat.le_of_not_lt fun shorter => ?_
    have := present _ shorter
    simp at this
  validators small index validator found := by
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨validator, (read small index inside).trans found, .refl _⟩

/-- A fold whose every step keeps the lifecycle keeps it. -/
theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → EffectiveHeld s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : EffectiveHeld state after :=
  foldlM_ok_invariant (EffectiveHeld state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

/-- Replacing a validator by itself later in its life. -/
theorem putValidator {index : Nat} {validator : Validator}
    (inside : index < state.validators.data.size)
    (step : HeldStep state.validators.data[index] validator) :
    EffectiveHeld state (state.putValidator index inside validator) where
  size_le := by simp [BeaconState.putValidator]
  validators _ other old found := by
    simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set]
    split
    · rename_i same
      subst same
      have equal : state.validators.data[index] = old := by
        rw [Array.getElem?_eq_getElem inside] at found
        exact Option.some.inj found
      exact ⟨validator, by simp, equal ▸ step⟩
    · exact ⟨old, found, .refl _⟩

theorem setValidator {index : ValidatorIndex} {old validator : Validator}
    (found : getValidator state index = .ok old)
    (set : state.setValidator index validator = .ok after)
    (step : HeldStep old validator) : EffectiveHeld state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine putValidator inside ?_
  have read : state.validators.data[index.toNat]? = some old := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      exact read
    · cases found
  rw [Array.getElem?_eq_getElem inside] at read
  exact Option.some.inj read ▸ step

/-- Replacing the validator at a position of the registry, given by its index of 64 bits.

The position is below `2^64` while the registry is. -/
theorem setValidator_position {position : Nat} {old validator : Validator}
    (found : state.validators.data[position]? = some old)
    (set : state.setValidator position.toUInt64 validator = .ok after)
    (step : HeldStep old validator) :
    EffectiveHeld state after := by
  have sizes := sameSizes_setValidator set
  refine ⟨Nat.le_of_eq sizes.1.symm, fun small => ?_⟩
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exact : position.toUInt64.toNat = position :=
    toNat_toUInt64_of_lt_pow (by rw [sizes.1] at small; omega)
  refine (setValidator (old := old) ?_ set step).validators small
  simp [getValidator, exact, found]

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : EffectiveHeld state after :=
  of_data (by rw [increaseBalance_validators computed])

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : EffectiveHeld state after :=
  of_data (by rw [decreaseBalance_validators computed])

end EffectiveHeld

/-- Below Gloas the registry is within its limit, so the condition on its size holds. -/
theorem EffectiveHeld.validators_of_before {fork' : Base.Fork}
    {after : BeaconState preset fork'} (lifecycle : EffectiveHeld state after)
    (before : fork' < .glamsterdam) (index : Nat)
    {validator : Validator} (found : state.validators.data[index]? = some validator) :
    ∃ later, after.validators.data[index]? = some later ∧ HeldStep validator later :=
  lifecycle.validators
    (Nat.lt_of_le_of_lt (after.validators.bound before) (UInt64.toNat_lt _)) index validator found

/-! ## Mutators -/

theorem effectiveHeld_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    EffectiveHeld state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _
  · have same := (exitQueue_validators queue).1
    -- Only a validator with no exit epoch gets one.
    exact (EffectiveHeld.of_data (by rw [same])).trans <|
      .setValidator ((getValidator_of_validators_eq same index).trans found) set
        (fun _ => ⟨rfl, UInt64.le_refl _⟩)

theorem effectiveHeld_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    EffectiveHeld state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  -- The slashed validator keeps its key and its epochs, and is now slashed.
  exact (effectiveHeld_initiateValidatorExit exitedOk).trans <|
    ((EffectiveHeld.setValidator found markedOk
      (fun _ => ⟨rfl, UInt64.le_refl _⟩)).trans (by exact .of_data rfl)).trans <|
    (EffectiveHeld.decreaseBalance loweredOk).trans <|
    (EffectiveHeld.increaseBalance raisedOk).trans <|
    (EffectiveHeld.increaseBalance lastOk).trans
      (.of_data (by rw [(slashValidator_last done).1]))

/-! ## The steps of a block -/

theorem effectiveHeld_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : EffectiveHeld state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_data rfl

theorem effectiveHeld_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    EffectiveHeld state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_data rfl

theorem effectiveHeld_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : EffectiveHeld state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_data (by rw [← rest])

theorem effectiveHeld_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    EffectiveHeld state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact effectiveHeld_slashValidator slashed

theorem effectiveHeld_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    EffectiveHeld step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact effectiveHeld_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem effectiveHeld_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    EffectiveHeld state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => EffectiveHeld state step.1)
    (fun _ _ _ before ok => before.trans (effectiveHeld_slashIfSlashable ok))
    (show EffectiveHeld state (state, false).1 from .refl state) folded

theorem effectiveHeld_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    EffectiveHeld state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : EffectiveHeld raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_data rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        EffectiveHeld state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_data rfl
    exact (flagged _ _).trans ((EffectiveHeld.increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact .of_data (by rw [← rest])

/-- A new validator goes to the index for a new validator, which is the size of the registry.

While the registry is below `2^64`, that index is past every validator, so it replaces none. -/
theorem effectiveHeld_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    EffectiveHeld state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨validators, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
    have read := setOrAppendRooted_getElem? validatorsOk
    refine .of_read (fun index inside => ?_) (fun small index inside => ?_)
    · rw [read]
      split <;> simp [inside]
    · rw [read]
      -- Below `2^64` the index for a new validator is the size, past every index.
      have sizeLe : state.validators.data.size ≤ validators.data.size := by
        refine Nat.le_of_not_lt fun shorter => ?_
        have := read validators.data.size
        split at this
        · simp at this
        · rw [Array.getElem?_eq_getElem shorter] at this
          simp at this
      have exact : (getIndexForNewValidator state).toNat = state.validators.data.size := by
        dsimp only at small
        exact toNat_toUInt64_of_lt_pow (by omega)
      simp [exact, Nat.ne_of_lt inside]
  · split at computed
    · cases computed
      refine .of_read (fun index inside => ?_) (fun _ index inside => ?_)
      · simp [RootedForkList.data_push, Nat.lt_succ_of_lt inside]
      · simp [RootedForkList.data_push, Array.getElem?_push, Nat.ne_of_lt inside]
    · cases computed

theorem effectiveHeld_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    EffectiveHeld state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact effectiveHeld_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · rw [liftAccessor_ok] at computed
    exact .increaseBalance computed

theorem effectiveHeld_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    EffectiveHeld state after := by
  unfold applyDeposit at computed
  split at computed
  · unfold applyDepositElectra at computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, added, pushed⟩ := computed
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (effectiveHeld_addValidatorToRegistry added).trans (.of_data rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_data rfl
  · exact effectiveHeld_applyPendingDeposit computed

theorem effectiveHeld_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    EffectiveHeld state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (EffectiveHeld.of_data (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (effectiveHeld_applyDeposit applied)

theorem effectiveHeld_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    EffectiveHeld state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact effectiveHeld_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem effectiveHeld_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    EffectiveHeld state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_data rfl

theorem effectiveHeld_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    EffectiveHeld state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

theorem effectiveHeld_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    EffectiveHeld state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

theorem effectiveHeld_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    EffectiveHeld state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (effectiveHeld_computeExitEpochAndUpdateChurn churned).trans (.of_data rfl)
  · cases computed
    exact .refl _

theorem effectiveHeld_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    EffectiveHeld state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact effectiveHeld_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact effectiveHeld_requestPartialWithdrawal computed

theorem effectiveHeld_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    EffectiveHeld state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_data rfl
  · cases computed
    exact .refl _

/-- A switch to compounding changes only the withdrawal credentials of the validator. -/
theorem effectiveHeld_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    EffectiveHeld state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (EffectiveHeld.setValidator found set (fun _ => ⟨rfl, UInt64.le_refl _⟩)).trans
    (effectiveHeld_queueExcessActiveBalance queued)

/-- The source of a consolidation gets an exit epoch, which it did not have. -/
theorem effectiveHeld_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourcePosition]? = some source)
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    EffectiveHeld state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, _, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have churnedKept := effectiveHeld_computeConsolidationEpochAndUpdateChurn churned
  have same : churnedState.validators.data = state.validators.data := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    rfl
  exact churnedKept.trans <|
    (EffectiveHeld.setValidator_position (old := source) (by rw [same]; exact found) set
      (fun _ => ⟨rfl, UInt64.le_refl _⟩)).trans (.of_data rfl)

theorem effectiveHeld_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    EffectiveHeld state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact effectiveHeld_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact effectiveHeld_queueConsolidation (Array.getElem?_eq_getElem _) computed

theorem effectiveHeld_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    EffectiveHeld state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processDepositRequest ok)
      depositsOk).trans <|
    (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processConsolidationRequest ok)
      consolidationsOk

/-! ## Withdrawals -/

theorem effectiveHeld_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : EffectiveHeld state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl
  · exact .decreaseBalance computed

theorem effectiveHeld_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    EffectiveHeld state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : EffectiveHeld state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_applyWithdrawal ok) appliedOk
  have two : EffectiveHeld applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_data rfl
    · cases indexedOk
      exact .refl _
  have queued : ∀ kept : BeaconState preset fork,
      EffectiveHeld kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl
    · exact .refl _
  have partials : ∀ kept : BeaconState preset fork,
      EffectiveHeld kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl
    · exact .refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → EffectiveHeld kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact .of_data rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  have lastKept : EffectiveHeld finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact .of_data rfl
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

theorem effectiveHeld_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    EffectiveHeld state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact effectiveHeld_applyExpectedWithdrawals applied
    · cases computed
      exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact effectiveHeld_applyExpectedWithdrawals applied

/-- A change to an execution address changes only the withdrawal credentials of the validator. -/
theorem effectiveHeld_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    EffectiveHeld state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact .setValidator found set (fun _ => ⟨rfl, UInt64.le_refl _⟩)

/-! ## The parent payload and the execution part of a block -/

theorem effectiveHeld_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    EffectiveHeld state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_data rfl

theorem effectiveHeld_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    EffectiveHeld state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .of_data rfl)

theorem effectiveHeld_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    EffectiveHeld state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl

theorem effectiveHeld_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : EffectiveHeld state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact .of_data rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;> exact .of_data rfl

theorem effectiveHeld_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    EffectiveHeld state after := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact .refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  unfold applyParentExecutionPayload at applied
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    applied
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, buildersOk, exitsOk⟩ :=
    requestedOk
  exact (effectiveHeld_settleParentPayment settledOk).trans <|
    (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processDepositRequest ok)
      depositsOk).trans <|
    (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processConsolidationRequest ok)
      consolidationsOk).trans <|
    (EffectiveHeld.foldlM
      (fun _ _ _ ok => effectiveHeld_processBuilderDepositRequest ok) buildersOk).trans <|
    (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processBuilderExitRequest ok)
      exitsOk).trans (.of_data rfl)

theorem effectiveHeld_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    EffectiveHeld state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_data rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_data rfl

theorem effectiveHeld_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    EffectiveHeld state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (effectiveHeld_processWithdrawals withdrawnOk).trans
      (effectiveHeld_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (effectiveHeld_processWithdrawals withdrawnOk).trans
      (effectiveHeld_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact effectiveHeld_processExecutionPayload computed
    · cases computed
      exact .refl _

/-! ## The sync aggregate -/

theorem effectiveHeld_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    EffectiveHeld state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine EffectiveHeld.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (EffectiveHeld.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

/-! ## Blocks -/

theorem effectiveHeld_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    EffectiveHeld state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processProposerSlashing ok)
        proposersOk).trans <|
      (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processAttesterSlashing ok)
        attestersOk).trans <|
      (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processAttestation ok)
        attestedOk).trans <|
      (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processVoluntaryExit ok)
        exitsOk).trans <|
      (EffectiveHeld.foldlM
        (fun _ _ _ ok => effectiveHeld_processBlsToExecutionChange ok) changesOk).trans <|
      EffectiveHeld.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : EffectiveHeld exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact EffectiveHeld.foldlM
        (fun _ _ _ ok => effectiveHeld_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : EffectiveHeld changed after := by
    split at requestsOk
    · exact effectiveHeld_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  exact (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processProposerSlashing ok)
      proposersOk).trans <|
    (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processAttesterSlashing ok)
      attestersOk).trans <|
    (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processAttestation ok)
      attestedOk).trans <|
    (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processDeposit ok)
      depositedOk).trans <|
    (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_processVoluntaryExit ok)
      exitsOk).trans <|
    changes.trans requests

theorem effectiveHeld_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    EffectiveHeld state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidKept : EffectiveHeld state paid := by
      split at paidOk
      · exact effectiveHeld_processParentExecutionPayload paidOk
      · cases paidOk
        exact .refl _
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedKept : EffectiveHeld headed executed := by
      split at executedOk
      · exact effectiveHeld_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    -- Heze drops the vote on the deposit contract.
    have votedKept : EffectiveHeld revealed voted := by
      split at votedOk
      · exact effectiveHeld_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    exact paidKept.trans <| (effectiveHeld_processBlockHeader headedOk).trans <|
      executedKept.trans <| (effectiveHeld_processRandao revealedOk).trans <|
      votedKept.trans <| (effectiveHeld_processOperations operatedOk).trans
        (effectiveHeld_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (effectiveHeld_processBlockHeader headerOk).trans <|
    (effectiveHeld_processRandao randaoOk).trans <|
    (effectiveHeld_processEth1Data eth1Ok).trans
      (effectiveHeld_processOperations operationsOk)

/-! ## The steps of an epoch -/

theorem effectiveHeld_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    EffectiveHeld state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_data (by rw [← rest])

theorem effectiveHeld_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : EffectiveHeld state after :=
  EffectiveHeld.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (EffectiveHeld.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem effectiveHeld_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    EffectiveHeld state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact effectiveHeld_applyAllDeltas applied

/-- Joining the activation queue changes only the eligibility epoch. -/
theorem heldStep_queueForActivation {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    HeldStep validator queued := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact (fun _ => ⟨rfl, UInt64.le_refl _⟩)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem effectiveHeld_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    EffectiveHeld state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set := EffectiveHeld.setValidator found markedOk
    (heldStep_queueForActivation queuedOk)
  split at computed
  · exact set.trans (effectiveHeld_initiateValidatorExit (liftAccessor_ok.mp computed))
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

/-- Activating a validator that has no activation epoch yet. -/
theorem effectiveHeld_activateValidator {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (far : validator.activationEpoch = FAR_FUTURE_EPOCH)
    (computed : activateValidator state index = .ok after) : EffectiveHeld state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨old, oldFound, _, _, set⟩ := computed
  have same := Except.ok.inj (oldFound.symm.trans found)
  subst same
  exact .setValidator oldFound set (fun set => absurd far set)

/-- Activating distinct validators, each eligible for activation at the start. -/
theorem effectiveHeld_foldActivateValidator :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      indices.Nodup →
      (∀ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
        validator.activationEpoch = FAR_FUTURE_EPOCH) →
      indices.foldlM activateValidator state = .ok after → EffectiveHeld state after
  | [], state, after, _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  | index :: rest, state, after, unique, eligible, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    obtain ⟨validator, found, far⟩ := eligible index List.mem_cons_self
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    refine (effectiveHeld_activateValidator found far first).trans
      (effectiveHeld_foldActivateValidator restUnique (fun other member => ?_) tail)
    -- The other validators of the queue are not touched by this activation.
    have distinct : other ≠ index := fun same => absent (same ▸ member)
    obtain ⟨otherValidator, otherFound, otherFar⟩ := eligible other (List.mem_cons_of_mem _ member)
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at first
    obtain ⟨_, _, _, _, set⟩ := first
    exact ⟨otherValidator, (getValidator_setValidator_of_ne set distinct).trans otherFound,
      otherFar⟩

theorem effectiveHeld_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    EffectiveHeld state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine EffectiveHeld.foldlM (fun state _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact .setValidator found set (fun _ => ⟨rfl, UInt64.le_refl _⟩)
    split at ok
    · exact effectiveHeld_initiateValidatorExit (liftAccessor_ok.mp ok)
    split at ok
    · rename_i eligible
      rw [liftAccessor_ok] at ok
      have far := activationEpoch_of_isEligibleForActivation eligible
      exact .setValidator found ok (fun set => absurd far set)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  rename_i notElectra
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  -- Before Electra the registry is within its limit, far below `2^64`.
  have before : fork < .glamsterdam := Nat.lt_trans (Nat.lt_of_not_le notElectra) (by decide)
  have small : updated.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (updated.validators.bound before) (UInt64.toNat_lt _)
  refine (EffectiveHeld.foldlM (fun _ _ _ ok => effectiveHeld_updateRegistryEntry ok)
    updatedOk).trans (effectiveHeld_foldActivateValidator
      (List.Nodup.sublist (List.take_sublist _ _) (activationQueue_nodup small))
      (fun index member => ?_) activated)
  obtain ⟨position, validator, equal, found, eligible⟩ :=
    mem_activationQueue (List.mem_of_mem_take member)
  refine ⟨validator, ?_, activationEpoch_of_isEligibleForActivation eligible⟩
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exact : index.toNat = position := by
    rw [← equal, toNat_toUInt64_of_lt_pow (by omega)]
  simp [getValidator, exact, found]

theorem effectiveHeld_processSlashings (computed : processSlashings state = .ok after) :
    EffectiveHeld state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine EffectiveHeld.foldlM (fun _ _ _ ok => ?_) applied
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, lowered⟩ := ok
        exact .decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ .refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  · refine EffectiveHeld.foldlM (fun _ _ _ ok => ?_) computed
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact .decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ .refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _

theorem effectiveHeld_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    EffectiveHeld state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_data rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- The balance at a position, rounded down to an increment, as a natural number.

It is zero past the end of the balances. -/
def balanceFloorAt (state : BeaconState preset fork) (position : Nat) : Nat :=
  match state.balances.data[position]? with
  | some balance => balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  | none => 0

/-- An updated effective balance is at least the old one or the balance rounded down.

The old one must be at most the largest, which holds under the cap. -/
theorem updatedEffectiveBalance_ge {largest balance effectiveBalance result : Gwei}
    (old : effectiveBalance ≤ largest)
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    min effectiveBalance.toNat
        (balance.toNat - balance.toNat % preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ≤
      result.toNat := by
  have oldNat := UInt64.le_iff_toNat_le.mp old
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact Nat.min_le_left _ _
  · -- The new value is the rounded balance, or the largest, which is at least the old one.
    rw [UInt64.min_def]
    split
    · rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr
        (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)), UInt64.toNat_mod]
      exact Nat.min_le_right _ _
    · exact Nat.le_trans (Nat.min_le_left _ _) oldNat

/-- The update of the effective balances, at distinct positions of the registry.

Each updated validator keeps its activation epoch.

Its effective balance is at least the old one or its balance rounded down.

The balances and the other validators stay. -/
private theorem foldlM_updateEffectiveBalance_floor :
    ∀ {positions : List Nat} {state after : BeaconState preset fork},
      positions.Nodup → (∀ position ∈ positions, position < state.validators.data.size) →
      state.validators.data.size < 2 ^ 64 → EffectiveBalancesCapped state →
      positions.foldlM updateEffectiveBalance state = .ok after →
      after.balances = state.balances ∧
      after.validators.data.size = state.validators.data.size ∧
      ∀ position validator, state.validators.data[position]? = some validator →
        ∃ later, after.validators.data[position]? = some later ∧
          later.activationEpoch = validator.activationEpoch ∧
          if position ∈ positions then
            min validator.effectiveBalance.toNat (balanceFloorAt state position) ≤
              later.effectiveBalance.toNat
          else later = validator
  | [], state, after, _, _, _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl, fun _ validator found => ⟨validator, found, rfl, by simp⟩⟩
  | position :: rest, state, after, unique, inside, small, capped, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    have here := inside position List.mem_cons_self
    have exactIndex : position.toUInt64.toNat = position :=
      toNat_toUInt64_of_lt_pow (by omega)
    have step := first
    simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨validator, found, balance, balanceOk, updated, updatedOk, set⟩ := step
    obtain ⟨setInside, rfl⟩ := setValidator_ok set
    have read : state.validators.data[position]? = some validator := by
      unfold getValidator at found
      rw [exactIndex] at found
      split at found
      · rename_i read
        cases found
        exact read
      · cases found
    have balanceRead : state.balances.data[position]? = some balance := by
      unfold getBalance at balanceOk
      rw [exactIndex] at balanceOk
      split at balanceOk
      · rename_i read
        cases balanceOk
        exact read
      · cases balanceOk
    -- The update is under the cap, so the new effective balance is at least the smaller one.
    have grown := updatedEffectiveBalance_ge (capped.get found) updatedOk
    have middleCapped : EffectiveBalancesCapped
        (state.putValidator position.toUInt64.toNat setInside
          { validator with effectiveBalance := updated }) :=
      (CapKept.setValidator set fun capped => by
        have bound := updatedEffectiveBalance_le (capped.get found) updatedOk
        rw [withdrawalMaxEffectiveBalance_congr rfl]
        exact bound).kept capped
    obtain ⟨balances, sizes, rest⟩ := foldlM_updateEffectiveBalance_floor restUnique
      (fun other member => by
        simp only [BeaconState.putValidator, RootedForkList.data_set, Array.size_set]
        exact inside other (List.mem_cons_of_mem _ member))
      (by simpa [BeaconState.putValidator] using small) middleCapped tail
    refine ⟨balances, by simpa [BeaconState.putValidator] using sizes,
      fun other old oldFound => ?_⟩
    by_cases same : other = position
    · subst same
      have equal : old = validator := Option.some.inj (oldFound.symm.trans read)
      subst equal
      obtain ⟨later, laterFound, activation, kept⟩ :=
        rest other { old with effectiveBalance := updated }
        (by simp [BeaconState.putValidator, exactIndex])
      simp only [absent, ↓reduceIte] at kept
      subst kept
      refine ⟨_, laterFound, activation, ?_⟩
      simp only [List.mem_cons_self, ↓reduceIte, balanceFloorAt, balanceRead]
      exact grown
    · obtain ⟨later, laterFound, activation, kept⟩ := rest other old
        (by simp [BeaconState.putValidator, exactIndex, Ne.symm same, oldFound])
      refine ⟨later, laterFound, activation, ?_⟩
      simp only [List.mem_cons, same, false_or]
      split at kept
      · rename_i member
        simp only [member, ↓reduceIte]
        simpa [balanceFloorAt, BeaconState.putValidator] using kept
      · rename_i notMember
        simp only [notMember, ↓reduceIte]
        exact kept

theorem effectiveHeld_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    EffectiveHeld state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_data rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem effectiveHeld_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    EffectiveHeld state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_data rfl

/-! ## The steps of an epoch from Altair -/

theorem effectiveHeld_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    EffectiveHeld state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_data rfl

theorem effectiveHeld_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      EffectiveHeld state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact .refl _
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (effectiveHeld_applyPendingDeposit credited).trans
        (effectiveHeld_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact effectiveHeld_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact .refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (effectiveHeld_applyPendingDeposit credited).trans
      (effectiveHeld_passPendingDeposits (deposits := rest) ‹_›)

theorem effectiveHeld_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    EffectiveHeld state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (effectiveHeld_passPendingDeposits ‹_›).trans (.of_data rfl)

theorem effectiveHeld_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      EffectiveHeld state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact effectiveHeld_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (EffectiveHeld.decreaseBalance loweredOk).trans <|
      (EffectiveHeld.increaseBalance raisedOk).trans
        (effectiveHeld_passPendingConsolidations (result := (passed, read)) passedOk)

theorem effectiveHeld_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    EffectiveHeld state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine (effectiveHeld_processPendingDeposits deposited).trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (effectiveHeld_passPendingConsolidations ‹_›).trans (.of_data rfl)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-! ## The epoch transition -/

/-- A step that keeps the validators and the balances. -/
private def Untouched (state after : BeaconState preset fork) : Prop :=
  after.validators.data = state.validators.data ∧ after.balances = state.balances

private theorem Untouched.trans {first second third : BeaconState preset fork}
    (one : Untouched first second) (two : Untouched second third) : Untouched first third :=
  ⟨two.1.trans one.1, two.2.trans one.2⟩

/-- The steps that close an epoch from Altair, after the history, touch no validator or balance.
-/
private theorem untouched_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : Untouched rooted after := by
  have syncedKept : Untouched rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact ⟨rfl, rfl⟩
  have lookedKept : Untouched synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact ⟨rfl, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ ⟨rfl, rfl⟩
  have windowedKept : Untouched looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact ⟨rfl, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ ⟨rfl, rfl⟩
  exact syncedKept.trans (lookedKept.trans windowedKept)

private theorem untouched_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : Untouched state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ ⟨rfl, rfl⟩

/-- The effective balances after the update, against those of the state that it starts from.

The registry after the epoch is below `2^64`, so each position is its own index of 64 bits. -/
private theorem floor_of_update {paid balanced : BeaconState preset fork}
    (prefixHeld : EffectiveHeld state paid) (capped : EffectiveBalancesCapped paid)
    (balancedOk : processEffectiveBalanceUpdates paid = .ok balanced)
    (suffix : Untouched balanced after) (small : after.validators.data.size < 2 ^ 64)
    {position : Nat} {validator : Validator}
    (found : state.validators.data[position]? = some validator)
    (set : validator.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ later, after.validators.data[position]? = some later ∧
      later.activationEpoch = validator.activationEpoch ∧
      min validator.effectiveBalance.toNat (balanceFloorAt after position) ≤
        later.effectiveBalance.toNat := by
  have paidSmall : paid.validators.data.size < 2 ^ 64 := by
    have sizes := congrArg Array.size suffix.1
    have updateSizes := (sameSizes_processEffectiveBalanceUpdates balancedOk).1
    omega
  unfold processEffectiveBalanceUpdates at balancedOk
  obtain ⟨balances, _, updated⟩ := foldlM_updateEffectiveBalance_floor List.nodup_range
    (fun other member => List.mem_range.mp member) paidSmall capped balancedOk
  obtain ⟨middle, middleFound, middleStep⟩ :=
    prefixHeld.validators paidSmall position validator found
  obtain ⟨sameActivation, grown⟩ := middleStep set
  have inside : position < paid.validators.data.size :=
    (Array.getElem?_eq_some_iff.mp middleFound).1
  obtain ⟨later, laterFound, activation, bound⟩ := updated position middle middleFound
  simp only [List.mem_range, inside, ↓reduceIte] at bound
  refine ⟨later, by rw [suffix.1]; exact laterFound, activation.trans sameActivation, ?_⟩
  have floorSame : balanceFloorAt after position = balanceFloorAt paid position := by
    simp only [balanceFloorAt, suffix.2, balances]
  rw [floorSame]
  have grownNat := UInt64.le_iff_toNat_le.mp grown
  omega


/-- The floor on the effective balances, between two states.

While the later registry is below `2^64`, take a validator with an activation epoch.

Later it keeps that epoch, and its effective balance is at least the smaller of two values.

One is its effective balance before, the other its balance after, rounded down. -/
def FloorStep {fork' : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') : Prop :=
  after.validators.data.size < 2 ^ 64 → ∀ (position : Nat) (validator : Validator),
    state.validators.data[position]? = some validator →
    validator.activationEpoch ≠ FAR_FUTURE_EPOCH →
    ∃ later, after.validators.data[position]? = some later ∧
      later.activationEpoch = validator.activationEpoch ∧
      min validator.effectiveBalance.toNat (balanceFloorAt after position) ≤
        later.effectiveBalance.toNat

/-- From Altair, the epoch transition keeps each effective balance above its floor.

It is at least the old one or the balance after the epoch, rounded down.

The state must be under the cap, as every reachable state is. -/
theorem floorStep_processEpochAltair {altair : .altair ≤ fork}
    (capped : EffectiveBalancesCapped state)
    (computed : processEpochAltair config checks state altair = .ok after) :
    FloorStep state after := by
  intro small position validator found set
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetHeld : EffectiveHeld slashed reset := by
    split at resetOk
    · exact effectiveHeld_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ .refl _
  have resetCapped : CapKept slashed reset := by
    split at resetOk
    · exact capKept_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ .refl _
  have paidUntouched : Untouched pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact ⟨rfl, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ ⟨rfl, rfl⟩
  -- The steps before the update keep the effective balances and the cap.
  have prefixHeld : EffectiveHeld state paid :=
    (effectiveHeld_processJustificationAndFinalization justifiedOk).trans <|
    (effectiveHeld_processInactivityUpdates scoredOk).trans <|
    (effectiveHeld_processRewardsAndPenalties rewardedOk).trans <|
    (effectiveHeld_processRegistryUpdates registeredOk).trans <|
    (effectiveHeld_processSlashings slashedOk).trans <|
    resetHeld.trans <|
    (effectiveHeld_processPendingBalances pendingOk).trans (.of_data paidUntouched.1)
  have prefixCapped : CapKept state paid :=
    (capKept_processJustificationAndFinalization justifiedOk).trans <|
    (capKept_processInactivityUpdates scoredOk).trans <|
    (capKept_processRewardsAndPenalties rewardedOk).trans <|
    (capKept_processRegistryUpdates registeredOk).trans <|
    (capKept_processSlashings slashedOk).trans <|
    resetCapped.trans <|
    (capKept_processPendingBalances pendingOk).trans (.of_data paidUntouched.1)
  -- The steps after the update touch no validator and no balance.
  have clearedUntouched : Untouched balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact ⟨rfl, rfl⟩
  have mixedUntouched : Untouched cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact ⟨rfl, rfl⟩
  have suffix : Untouched balanced after := by
    split at computed <;> simp only [bind_ok_iff] at computed <;>
      obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
    · have rootedUntouched : Untouched mixed rooted := by
        unfold processHistoricalSummariesUpdate at rootedOk
        simp only [bind, Except.bind, pure, Except.pure] at rootedOk
        repeat' (split at rootedOk <;> try cases rootedOk)
        all_goals exact ⟨rfl, rfl⟩
      exact clearedUntouched.trans <| mixedUntouched.trans <| rootedUntouched.trans
        (untouched_epochEnd syncedOk lookedOk windowed)
    · exact clearedUntouched.trans <| mixedUntouched.trans <|
        (untouched_processHistoricalRootsUpdate rootedOk).trans
          (untouched_epochEnd syncedOk lookedOk windowed)
  exact floor_of_update prefixHeld (prefixCapped.kept capped) balancedOk suffix small found set

/-- The epoch transition keeps each effective balance above its floor, at every fork. -/
theorem floorStep_processEpoch (capped : EffectiveBalancesCapped state)
    (computed : processEpoch config checks state = .ok after) : FloorStep state after := by
  unfold processEpoch at computed
  split at computed
  · exact floorStep_processEpochAltair capped computed
  intro small position validator found set
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have prefixHeld : EffectiveHeld state reset :=
    (effectiveHeld_processJustificationAndFinalization justifiedOk).trans <|
    (effectiveHeld_processRewardsAndPenalties rewardedOk).trans <|
    (effectiveHeld_processRegistryUpdates registeredOk).trans <|
    (effectiveHeld_processSlashings slashedOk).trans
      (effectiveHeld_processEth1DataReset resetOk)
  have prefixCapped : CapKept state reset :=
    (capKept_processJustificationAndFinalization justifiedOk).trans <|
    (capKept_processRewardsAndPenalties rewardedOk).trans <|
    (capKept_processRegistryUpdates registeredOk).trans <|
    (capKept_processSlashings slashedOk).trans (capKept_processEth1DataReset resetOk)
  have clearedUntouched : Untouched balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact ⟨rfl, rfl⟩
  have mixedUntouched : Untouched cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact ⟨rfl, rfl⟩
  have rotatedUntouched : Untouched rooted after := by
    unfold processParticipationRecordUpdates at rotated
    split at rotated
    · cases rotated
    simp only [pure, Except.pure, Except.ok.injEq] at rotated
    subst rotated
    exact ⟨rfl, rfl⟩
  exact floor_of_update prefixHeld (prefixCapped.kept capped) balancedOk
    (clearedUntouched.trans <| mixedUntouched.trans <|
      (untouched_processHistoricalRootsUpdate rootedOk).trans rotatedUntouched)
    small found set

/-- A step that keeps the effective balances keeps them above the floor. -/
theorem EffectiveHeld.floorStep {fork' : Base.Fork} {after : BeaconState preset fork'}
    (held : EffectiveHeld state after) : FloorStep state after := by
  intro small position validator found set
  obtain ⟨later, laterFound, step⟩ := held.validators small position validator found
  obtain ⟨activation, grown⟩ := step set
  exact ⟨later, laterFound, activation,
    Nat.le_trans (Nat.min_le_left _ _) (UInt64.le_iff_toNat_le.mp grown)⟩

/-! ## Slots, upgrades and chains -/

/-- One slot keeps each effective balance above its floor.

The epoch transition at the last slot of an epoch updates it from the balance after the epoch.

The slot then moves on, which keeps the balances. -/
theorem floorStep_advanceSlot (capped : EffectiveBalancesCapped state)
    (computed : advanceSlot config checks state = .ok after) : FloorStep state after := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, afterEq⟩ := computed
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  have cachedValidators : cached.validators.data = state.validators.data := by
    rw [cachedEq]
  have afterValidators : after.validators.data = epoched.validators.data := by
    rw [← afterEq]
  have afterBalances : after.balances = epoched.balances := by
    rw [← afterEq]
  have cachedCapped : EffectiveBalancesCapped cached :=
    (CapKept.of_data cachedValidators).kept capped
  have epochStep : FloorStep cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact floorStep_processEpoch cachedCapped epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact (EffectiveHeld.refl cached).floorStep
  intro small position validator found set
  obtain ⟨later, laterFound, activation, bound⟩ := epochStep (afterValidators ▸ small) position
    validator (cachedValidators ▸ found) set
  refine ⟨later, afterValidators ▸ laterFound, activation, ?_⟩
  simp only [balanceFloorAt, afterBalances] at bound ⊢
  exact bound

/-- Each index among those not yet active is that of a validator with no activation epoch.

The registry must be below `2^64`, so that each position is its own index of 64 bits. -/
theorem mem_preActivationIndices {state : BeaconState preset fork} {index : ValidatorIndex}
    (small : state.validators.data.size < 2 ^ 64) (member : index ∈ preActivationIndices state) :
    ∃ validator, state.validators.data[index.toNat]? = some validator ∧
      validator.activationEpoch = FAR_FUTURE_EPOCH := by
  simp only [preActivationIndices, List.mem_map, List.mem_mergeSort, List.mem_filter,
    decide_eq_true_eq] at member
  obtain ⟨⟨validator, position⟩, ⟨entry, far⟩, rfl⟩ := member
  have read := List.mem_zipIdx_iff_getElem?.mp entry
  simp only [Array.getElem?_toList] at read
  have inside := (Array.getElem?_eq_some_iff.mp read).1
  refine ⟨validator, ?_, far⟩
  rw [toNat_toUInt64_of_lt_pow (by omega)]
  exact read

/-- Queueing a validator that is not yet active keeps every activation epoch.

It keeps every other effective balance, and that of a validator with an activation epoch. -/
theorem effectiveHeld_queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} (found : getValidator state index = .ok validator)
    (far : validator.activationEpoch = FAR_FUTURE_EPOCH)
    (computed : queuePreActivation state electra index = .ok after) :
    EffectiveHeld state after ∧ ∀ position : Nat, (after.validators.data[position]?).map
      (fun later : Validator => later.activationEpoch) =
        (state.validators.data[position]?).map (fun earlier : Validator => earlier.activationEpoch)
      := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨read, readOk, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  have same : read = validator := Except.ok.inj (readOk.symm.trans found)
  subst same
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  refine ⟨EffectiveHeld.trans (by exact .of_data rfl)
    ((EffectiveHeld.setValidator (old := read) (by exact readOk) set₂
      (fun set => absurd far set)).trans (.of_data rfl)), fun position => ?_⟩
  obtain ⟨inside, rfl⟩ := setValidator_ok set₂
  simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set]
  split
  · rename_i equal
    subst equal
    have read' : state.validators.data[index.toNat]? = some read := by
      unfold getValidator at readOk
      split at readOk
      · rename_i got
        cases readOk
        exact got
      · cases readOk
    simp [read']
  · rfl


/-- Queueing validators that had no activation epoch at the start, one after another. -/
private theorem foldlM_queuePreActivation {electra : .pectra ≤ fork}
    {start : BeaconState preset fork} (before : fork < .glamsterdam) :
    ∀ {indices : List ValidatorIndex} {current after : BeaconState preset fork},
      (∀ index ∈ indices, index ∈ preActivationIndices start) →
      EffectiveHeld start current →
      (∀ position : Nat, (current.validators.data[position]?).map
        (fun later : Validator => later.activationEpoch) =
          (start.validators.data[position]?).map
            (fun earlier : Validator => earlier.activationEpoch)) →
      indices.foldlM (fun state index => queuePreActivation state electra index) current =
        .ok after →
      EffectiveHeld start after
  | [], current, after, _, held, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ held
  | index :: rest, current, after, members, held, activations, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    -- The validator had no activation epoch at the start, and the queue keeps every one.
    have small : start.validators.data.size < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (start.validators.bound before) (UInt64.toNat_lt _)
    obtain ⟨original, originalFound, far⟩ :=
      mem_preActivationIndices small (members index List.mem_cons_self)
    have now := activations index.toNat
    rw [originalFound] at now
    obtain ⟨validator, found, sameActivation⟩ : ∃ validator,
        current.validators.data[index.toNat]? = some validator ∧
          validator.activationEpoch = original.activationEpoch := by
      cases read : current.validators.data[index.toNat]? with
      | none => simp [read] at now
      | some validator =>
        simp only [read, Option.map_some, Option.some.injEq] at now
        exact ⟨validator, rfl, now⟩
    have readOk : getValidator current index = .ok validator := by
      simp [getValidator, found]
    obtain ⟨stepHeld, stepActivations⟩ :=
      effectiveHeld_queuePreActivation readOk (sameActivation.trans far) first
    exact foldlM_queuePreActivation before
      (fun other member => members other (List.mem_cons_of_mem _ member)) (held.trans stepHeld)
      (fun position => (stepActivations position).trans (activations position)) tail

/-- An upgrade keeps each effective balance of a validator with an activation epoch. -/
theorem effectiveHeld_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    EffectiveHeld pre.state post.val.state := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToAltair_spec upgraded).1
  · subst computed
    exact .of_data rfl
  · subst computed
    exact .of_data rfl
  · subst computed
    exact .of_data rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, _, queued, compounded⟩ := upgraded
    have compoundedHeld := EffectiveHeld.foldlM (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · exact effectiveHeld_queueExcessActiveBalance (liftAccessor_ok.mp ok)
        · cases ok
          exact .refl _
      · cases ok
        exact .refl _) compounded
    have queuedHeld := foldlM_queuePreActivation (by decide) (fun _ member => member) (.refl _)
      (fun _ => rfl) queued
    exact EffectiveHeld.trans (by exact .of_data rfl) (queuedHeld.trans compoundedHeld)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact .of_data (upgradeHezeFields_lists _).1

/-- Each step keeps each effective balance above its floor, from a state under the cap. -/
theorem Step.floorStep {before after : ForkedBeaconState preset}
    (step : Step config checks before after) (capped : EffectiveBalancesCapped before.state) :
    FloorStep before.state after.state := by
  cases step with
  | slot _ computed => exact floorStep_advanceSlot capped computed
  | upgrade _ computed => exact (effectiveHeld_upgradeNext computed).floorStep
  | block _ _ _ _ computed =>
    exact (effectiveHeld_processBlock (applySignedBlock_ok computed).2.1).floorStep

/-- Along a run from a reachable state, an effective balance stays above any common floor.

Take a validator with an activation epoch at the start, and a bound.

Its effective balance at the start is at least the bound.

At every state of the run, its balance rounded down to an increment is at least the bound.

Then at the end it keeps its activation epoch, and its effective balance is at least the bound.

The preset must order its largest effective balances as `EffectiveBalanceCaps` says.

From Gloas the registry at the end must be below `2^64`. -/
theorem Run.effectiveBalance_floor (caps : EffectiveBalanceCaps preset)
    {start : ForkedBeaconState preset} (reachable : Reachable config checks start) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      after.state.validators.data.size < 2 ^ 64 →
      ∀ (position : Nat) (validator : Validator),
        start.state.validators.data[position]? = some validator →
        validator.activationEpoch ≠ FAR_FUTURE_EPOCH →
        ∀ bound : Nat, bound ≤ validator.effectiveBalance.toNat →
        (∀ state ∈ run.states, bound ≤ balanceFloorAt state.state position) →
        ∃ later, after.state.validators.data[position]? = some later ∧
          later.activationEpoch = validator.activationEpoch ∧
          bound ≤ later.effectiveBalance.toNat
  | _, .nil, _, _, validator, found, _, _, startBound, _ =>
    ⟨validator, found, rfl, startBound⟩
  | _, .snoc run step, small, position, validator, found, set, bound, startBound, floors => by
    have middleSmall :=
      Nat.lt_of_le_of_lt (stepRelation_registryLifecycle.step step).size_le small
    obtain ⟨middle, middleFound, middleActivation, middleBound⟩ :=
      run.effectiveBalance_floor caps reachable middleSmall position validator found set bound
        startBound (fun state member => floors state (List.mem_append_left _ member))
    -- The state before the step is reachable, so it is under the cap.
    have capped := Reachable.effectiveBalancesCapped caps (reachable.reaches ⟨run⟩)
    obtain ⟨later, laterFound, activation, stepBound⟩ := step.floorStep capped small position
      middle middleFound (middleActivation ▸ set)
    have lastFloor := floors _ (List.mem_append_right _ (List.mem_singleton_self _))
    exact ⟨later, laterFound, activation.trans middleActivation, by omega⟩

end EthLib.Consensus
