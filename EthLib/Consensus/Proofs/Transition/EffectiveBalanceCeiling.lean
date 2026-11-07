module

public import EthLib.Consensus.Proofs.Transition.EffectiveBalanceCap
public import EthLib.Consensus.Proofs.Transition.Lifecycle

/-!
# Proofs: how far an effective balance can rise, at every fork

An effective balance rises in one place: the update at the end of an epoch.

There it becomes at most the balance, rounded down and capped.

That balance is the one after every step of the epoch that changes balances.

Every other step keeps it, or sets it to zero.

The upgrade to Electra sets it to zero for a validator that is not yet active.

So along a run each effective balance is at most the larger of two values.

- Its value at the start.
- The largest balance at a state of the run.

The bound is for the validators at the start.

From Gloas the registry at the end must be below `2^64`, so that no new validator replaces one.
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

/-- One validator, later: its effective balance has not risen. -/
def NotRaised (validator later : Validator) : Prop :=
  later.effectiveBalance ≤ validator.effectiveBalance

theorem NotRaised.refl (validator : Validator) : NotRaised validator validator :=
  UInt64.le_refl _

theorem NotRaised.trans {first second third : Validator} (one : NotRaised first second)
    (two : NotRaised second third) : NotRaised first third :=
  UInt64.le_trans two one

/-- The registry of a later state, which may be of a later fork.

It is at least as long.

While it has fewer than `2^64` validators, each validator is at its index.

Its effective balance has not risen. -/
structure EffectiveCapped {fork' : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') : Prop where
  size_le : state.validators.data.size ≤ after.validators.data.size
  validators : after.validators.data.size < 2 ^ 64 →
    ∀ (index : Nat) (validator : Validator), state.validators.data[index]? = some validator →
      ∃ later, after.validators.data[index]? = some later ∧ NotRaised validator later

namespace EffectiveCapped

theorem refl (state : BeaconState preset fork) : EffectiveCapped state state :=
  ⟨Nat.le_refl _, fun _ _ validator found => ⟨validator, found, .refl validator⟩⟩

theorem trans {fork' fork'' : Base.Fork} {first : BeaconState preset fork}
    {second : BeaconState preset fork'} {third : BeaconState preset fork''}
    (one : EffectiveCapped first second) (two : EffectiveCapped second third) :
    EffectiveCapped first third where
  size_le := Nat.le_trans one.size_le two.size_le
  validators small index validator found := by
    -- The middle registry is at most as long as the last one, so it is below `2^64` too.
    obtain ⟨middle, middleFound, oneStep⟩ :=
      one.validators (Nat.lt_of_le_of_lt two.size_le small) index validator found
    obtain ⟨later, laterFound, twoStep⟩ := two.validators small index middle middleFound
    exact ⟨later, laterFound, oneStep.trans twoStep⟩

/-- A state with the same validators, of any fork. -/
theorem of_data {fork' : Base.Fork} {after : BeaconState preset fork'}
    (same : after.validators.data = state.validators.data) : EffectiveCapped state after :=
  ⟨Nat.le_of_eq (by rw [same]), fun _ index validator found =>
    ⟨validator, by rw [same]; exact found, .refl _⟩⟩

/-- A step that keeps the validators at the indices of the registry, while it stays small.

Each index of the registry has a validator after it. -/
theorem of_read {after : BeaconState preset fork}
    (present : ∀ index, index < state.validators.data.size →
      (after.validators.data[index]?).isSome)
    (read : after.validators.data.size < 2 ^ 64 → ∀ index, index < state.validators.data.size →
      after.validators.data[index]? = state.validators.data[index]?) :
    EffectiveCapped state after where
  size_le := by
    refine Nat.le_of_not_lt fun shorter => ?_
    have := present _ shorter
    simp at this
  validators small index validator found := by
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨validator, (read small index inside).trans found, .refl _⟩

/-- A fold whose every step keeps the lifecycle keeps it. -/
theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → EffectiveCapped s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : EffectiveCapped state after :=
  foldlM_ok_invariant (EffectiveCapped state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

/-- Replacing a validator by one whose effective balance is not higher. -/
theorem putValidator {index : Nat} {validator : Validator}
    (inside : index < state.validators.data.size)
    (step : NotRaised state.validators.data[index] validator) :
    EffectiveCapped state (state.putValidator index inside validator) where
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
    (step : NotRaised old validator) : EffectiveCapped state after := by
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
    (step : NotRaised old validator) :
    EffectiveCapped state after := by
  have sizes := sameSizes_setValidator set
  refine ⟨Nat.le_of_eq sizes.1.symm, fun small => ?_⟩
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exact : position.toUInt64.toNat = position :=
    toNat_toUInt64_of_lt_pow (by rw [sizes.1] at small; omega)
  refine (setValidator (old := old) ?_ set step).validators small
  simp [getValidator, exact, found]

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : EffectiveCapped state after :=
  of_data (by rw [increaseBalance_validators computed])

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : EffectiveCapped state after :=
  of_data (by rw [decreaseBalance_validators computed])

end EffectiveCapped

/-- Below Gloas the registry is within its limit, so the condition on its size holds. -/
theorem EffectiveCapped.validators_of_before {fork' : Base.Fork}
    {after : BeaconState preset fork'} (lifecycle : EffectiveCapped state after)
    (before : fork' < .glamsterdam) (index : Nat)
    {validator : Validator} (found : state.validators.data[index]? = some validator) :
    ∃ later, after.validators.data[index]? = some later ∧ NotRaised validator later :=
  lifecycle.validators
    (Nat.lt_of_le_of_lt (after.validators.bound before) (UInt64.toNat_lt _)) index validator found

/-! ## Mutators -/

theorem effectiveCapped_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    EffectiveCapped state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _
  · have same := (exitQueue_validators queue).1
    -- Only a validator with no exit epoch gets one.
    exact (EffectiveCapped.of_data (by rw [same])).trans <|
      .setValidator ((getValidator_of_validators_eq same index).trans found) set
        (UInt64.le_refl _)

theorem effectiveCapped_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    EffectiveCapped state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  -- The slashed validator keeps its key and its epochs, and is now slashed.
  exact (effectiveCapped_initiateValidatorExit exitedOk).trans <|
    ((EffectiveCapped.setValidator found markedOk
      (UInt64.le_refl _)).trans (by exact .of_data rfl)).trans <|
    (EffectiveCapped.decreaseBalance loweredOk).trans <|
    (EffectiveCapped.increaseBalance raisedOk).trans <|
    (EffectiveCapped.increaseBalance lastOk).trans
      (.of_data (by rw [(slashValidator_last done).1]))

/-! ## The steps of a block -/

theorem effectiveCapped_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : EffectiveCapped state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_data rfl

theorem effectiveCapped_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    EffectiveCapped state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_data rfl

theorem effectiveCapped_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : EffectiveCapped state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_data (by rw [← rest])

theorem effectiveCapped_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    EffectiveCapped state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact effectiveCapped_slashValidator slashed

theorem effectiveCapped_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    EffectiveCapped step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact effectiveCapped_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem effectiveCapped_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    EffectiveCapped state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => EffectiveCapped state step.1)
    (fun _ _ _ before ok => before.trans (effectiveCapped_slashIfSlashable ok))
    (show EffectiveCapped state (state, false).1 from .refl state) folded

theorem effectiveCapped_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    EffectiveCapped state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : EffectiveCapped raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_data rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        EffectiveCapped state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_data rfl
    exact (flagged _ _).trans ((EffectiveCapped.increaseBalance raisedOk).trans last)
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
theorem effectiveCapped_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    EffectiveCapped state after := by
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

theorem effectiveCapped_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    EffectiveCapped state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact effectiveCapped_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · rw [liftAccessor_ok] at computed
    exact .increaseBalance computed

theorem effectiveCapped_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    EffectiveCapped state after := by
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
        exact (effectiveCapped_addValidatorToRegistry added).trans (.of_data rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_data rfl
  · exact effectiveCapped_applyPendingDeposit computed

theorem effectiveCapped_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    EffectiveCapped state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (EffectiveCapped.of_data (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (effectiveCapped_applyDeposit applied)

theorem effectiveCapped_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    EffectiveCapped state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact effectiveCapped_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem effectiveCapped_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    EffectiveCapped state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_data rfl

theorem effectiveCapped_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    EffectiveCapped state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

theorem effectiveCapped_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    EffectiveCapped state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

theorem effectiveCapped_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    EffectiveCapped state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (effectiveCapped_computeExitEpochAndUpdateChurn churned).trans (.of_data rfl)
  · cases computed
    exact .refl _

theorem effectiveCapped_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    EffectiveCapped state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact effectiveCapped_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact effectiveCapped_requestPartialWithdrawal computed

theorem effectiveCapped_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    EffectiveCapped state after := by
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
theorem effectiveCapped_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    EffectiveCapped state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (EffectiveCapped.setValidator found set (UInt64.le_refl _)).trans
    (effectiveCapped_queueExcessActiveBalance queued)

/-- The source of a consolidation gets an exit epoch, which it did not have. -/
theorem effectiveCapped_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourcePosition]? = some source)
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    EffectiveCapped state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, _, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have churnedKept := effectiveCapped_computeConsolidationEpochAndUpdateChurn churned
  have same : churnedState.validators.data = state.validators.data := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    rfl
  exact churnedKept.trans <|
    (EffectiveCapped.setValidator_position (old := source) (by rw [same]; exact found) set
      (UInt64.le_refl _)).trans (.of_data rfl)

theorem effectiveCapped_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    EffectiveCapped state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact effectiveCapped_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact effectiveCapped_queueConsolidation (Array.getElem?_eq_getElem _) computed

theorem effectiveCapped_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    EffectiveCapped state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processDepositRequest ok)
      depositsOk).trans <|
    (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processConsolidationRequest ok)
      consolidationsOk

/-! ## Withdrawals -/

theorem effectiveCapped_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : EffectiveCapped state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl
  · exact .decreaseBalance computed

theorem effectiveCapped_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    EffectiveCapped state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : EffectiveCapped state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_applyWithdrawal ok) appliedOk
  have two : EffectiveCapped applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_data rfl
    · cases indexedOk
      exact .refl _
  have queued : ∀ kept : BeaconState preset fork,
      EffectiveCapped kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl
    · exact .refl _
  have partials : ∀ kept : BeaconState preset fork,
      EffectiveCapped kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl
    · exact .refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → EffectiveCapped kept finished := by
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
  have lastKept : EffectiveCapped finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact .of_data rfl
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

theorem effectiveCapped_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    EffectiveCapped state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact effectiveCapped_applyExpectedWithdrawals applied
    · cases computed
      exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact effectiveCapped_applyExpectedWithdrawals applied

/-- A change to an execution address changes only the withdrawal credentials of the validator. -/
theorem effectiveCapped_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    EffectiveCapped state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact .setValidator found set (UInt64.le_refl _)

/-! ## The parent payload and the execution part of a block -/

theorem effectiveCapped_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    EffectiveCapped state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_data rfl

theorem effectiveCapped_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    EffectiveCapped state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .of_data rfl)

theorem effectiveCapped_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    EffectiveCapped state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl

theorem effectiveCapped_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : EffectiveCapped state after := by
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

theorem effectiveCapped_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    EffectiveCapped state after := by
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
  exact (effectiveCapped_settleParentPayment settledOk).trans <|
    (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processDepositRequest ok)
      depositsOk).trans <|
    (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processConsolidationRequest ok)
      consolidationsOk).trans <|
    (EffectiveCapped.foldlM
      (fun _ _ _ ok => effectiveCapped_processBuilderDepositRequest ok) buildersOk).trans <|
    (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processBuilderExitRequest ok)
      exitsOk).trans (.of_data rfl)

theorem effectiveCapped_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    EffectiveCapped state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_data rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_data rfl

theorem effectiveCapped_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    EffectiveCapped state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (effectiveCapped_processWithdrawals withdrawnOk).trans
      (effectiveCapped_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (effectiveCapped_processWithdrawals withdrawnOk).trans
      (effectiveCapped_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact effectiveCapped_processExecutionPayload computed
    · cases computed
      exact .refl _

/-! ## The sync aggregate -/

theorem effectiveCapped_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    EffectiveCapped state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine EffectiveCapped.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (EffectiveCapped.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

/-! ## Blocks -/

theorem effectiveCapped_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    EffectiveCapped state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processProposerSlashing ok)
        proposersOk).trans <|
      (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processAttesterSlashing ok)
        attestersOk).trans <|
      (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processAttestation ok)
        attestedOk).trans <|
      (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processVoluntaryExit ok)
        exitsOk).trans <|
      (EffectiveCapped.foldlM
        (fun _ _ _ ok => effectiveCapped_processBlsToExecutionChange ok) changesOk).trans <|
      EffectiveCapped.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : EffectiveCapped exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact EffectiveCapped.foldlM
        (fun _ _ _ ok => effectiveCapped_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : EffectiveCapped changed after := by
    split at requestsOk
    · exact effectiveCapped_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  exact (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processProposerSlashing ok)
      proposersOk).trans <|
    (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processAttesterSlashing ok)
      attestersOk).trans <|
    (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processAttestation ok)
      attestedOk).trans <|
    (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processDeposit ok)
      depositedOk).trans <|
    (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_processVoluntaryExit ok)
      exitsOk).trans <|
    changes.trans requests

theorem effectiveCapped_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    EffectiveCapped state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidKept : EffectiveCapped state paid := by
      split at paidOk
      · exact effectiveCapped_processParentExecutionPayload paidOk
      · cases paidOk
        exact .refl _
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedKept : EffectiveCapped headed executed := by
      split at executedOk
      · exact effectiveCapped_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    -- Heze drops the vote on the deposit contract.
    have votedKept : EffectiveCapped revealed voted := by
      split at votedOk
      · exact effectiveCapped_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    exact paidKept.trans <| (effectiveCapped_processBlockHeader headedOk).trans <|
      executedKept.trans <| (effectiveCapped_processRandao revealedOk).trans <|
      votedKept.trans <| (effectiveCapped_processOperations operatedOk).trans
        (effectiveCapped_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (effectiveCapped_processBlockHeader headerOk).trans <|
    (effectiveCapped_processRandao randaoOk).trans <|
    (effectiveCapped_processEth1Data eth1Ok).trans
      (effectiveCapped_processOperations operationsOk)

/-! ## The steps of an epoch -/

theorem effectiveCapped_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    EffectiveCapped state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_data (by rw [← rest])

theorem effectiveCapped_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : EffectiveCapped state after :=
  EffectiveCapped.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (EffectiveCapped.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem effectiveCapped_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    EffectiveCapped state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact effectiveCapped_applyAllDeltas applied

/-- Joining the activation queue changes only the eligibility epoch. -/
theorem notRaised_queueForActivation {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    NotRaised validator queued := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact (UInt64.le_refl _)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem effectiveCapped_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    EffectiveCapped state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set := EffectiveCapped.setValidator found markedOk
    (notRaised_queueForActivation queuedOk)
  split at computed
  · exact set.trans (effectiveCapped_initiateValidatorExit (liftAccessor_ok.mp computed))
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

/-- Activating a validator changes only its activation epoch. -/
theorem effectiveCapped_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : EffectiveCapped state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨old, oldFound, _, _, set⟩ := computed
  exact .setValidator oldFound set (UInt64.le_refl _)

theorem effectiveCapped_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    EffectiveCapped state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine EffectiveCapped.foldlM (fun state _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact .setValidator found set (UInt64.le_refl _)
    split at ok
    · exact effectiveCapped_initiateValidatorExit (liftAccessor_ok.mp ok)
    split at ok
    · rw [liftAccessor_ok] at ok
      exact .setValidator found ok (UInt64.le_refl _)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  exact (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_updateRegistryEntry ok)
    updatedOk).trans
    (EffectiveCapped.foldlM (fun _ _ _ ok => effectiveCapped_activateValidator ok) activated)

theorem effectiveCapped_processSlashings (computed : processSlashings state = .ok after) :
    EffectiveCapped state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine EffectiveCapped.foldlM (fun _ _ _ ok => ?_) applied
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
  · refine EffectiveCapped.foldlM (fun _ _ _ ok => ?_) computed
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

theorem effectiveCapped_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    EffectiveCapped state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_data rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem effectiveCapped_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    EffectiveCapped state after := by
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

theorem effectiveCapped_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    EffectiveCapped state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_data rfl

/-! ## The steps of an epoch from Altair -/

theorem effectiveCapped_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    EffectiveCapped state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_data rfl

theorem effectiveCapped_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      EffectiveCapped state pass.1.state
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
      exact (effectiveCapped_applyPendingDeposit credited).trans
        (effectiveCapped_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact effectiveCapped_passPendingDeposits (deposits := rest) ‹_›
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
    exact (effectiveCapped_applyPendingDeposit credited).trans
      (effectiveCapped_passPendingDeposits (deposits := rest) ‹_›)

theorem effectiveCapped_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    EffectiveCapped state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (effectiveCapped_passPendingDeposits ‹_›).trans (.of_data rfl)

theorem effectiveCapped_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      EffectiveCapped state result.1
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
      exact effectiveCapped_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (EffectiveCapped.decreaseBalance loweredOk).trans <|
      (EffectiveCapped.increaseBalance raisedOk).trans
        (effectiveCapped_passPendingConsolidations (result := (passed, read)) passedOk)

theorem effectiveCapped_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    EffectiveCapped state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine (effectiveCapped_processPendingDeposits deposited).trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (effectiveCapped_passPendingConsolidations ‹_›).trans (.of_data rfl)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- The balance at a position, as a natural number, and zero past the end of the balances. -/
def balanceAt (state : BeaconState preset fork) (position : Nat) : Nat :=
  ((state.balances.data[position]?).map UInt64.toNat).getD 0

/-- The update of the effective balances, at distinct positions of the registry.

Each updated effective balance is at most the old one or the balance.

The balances and the other validators stay. -/
private theorem foldlM_updateEffectiveBalance_ceiling :
    ∀ {positions : List Nat} {state after : BeaconState preset fork},
      positions.Nodup → (∀ position ∈ positions, position < state.validators.data.size) →
      state.validators.data.size < 2 ^ 64 →
      positions.foldlM updateEffectiveBalance state = .ok after →
      after.balances = state.balances ∧
      after.validators.data.size = state.validators.data.size ∧
      ∀ position validator, state.validators.data[position]? = some validator →
        ∃ later, after.validators.data[position]? = some later ∧
          if position ∈ positions then
            later.effectiveBalance.toNat ≤
              max validator.effectiveBalance.toNat (balanceAt state position)
          else later = validator
  | [], state, after, _, _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl, fun _ validator found => ⟨validator, found, by simp⟩⟩
  | position :: rest, state, after, unique, inside, small, computed => by
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
    have grown := updatedEffectiveBalance_le_max updatedOk
    obtain ⟨balances, sizes, rest⟩ := foldlM_updateEffectiveBalance_ceiling restUnique
      (fun other member => by
        simp only [BeaconState.putValidator, RootedForkList.data_set, Array.size_set]
        exact inside other (List.mem_cons_of_mem _ member))
      (by simpa [BeaconState.putValidator] using small) tail
    refine ⟨balances, by simpa [BeaconState.putValidator] using sizes,
      fun other old oldFound => ?_⟩
    by_cases same : other = position
    · subst same
      have equal : old = validator := Option.some.inj (oldFound.symm.trans read)
      subst equal
      obtain ⟨later, laterFound, kept⟩ :=
        rest other { old with effectiveBalance := updated }
          (by simp [BeaconState.putValidator, exactIndex])
      simp only [absent, ↓reduceIte] at kept
      subst kept
      refine ⟨_, laterFound, ?_⟩
      simp only [List.mem_cons_self, ↓reduceIte, balanceAt, balanceRead, Option.map_some,
        Option.getD_some]
      exact grown
    · obtain ⟨later, laterFound, kept⟩ := rest other old
        (by simp [BeaconState.putValidator, exactIndex, Ne.symm same, oldFound])
      refine ⟨later, laterFound, ?_⟩
      simp only [List.mem_cons, same, false_or]
      split at kept
      · rename_i member
        simp only [member, ↓reduceIte]
        simpa [balanceAt, BeaconState.putValidator] using kept
      · rename_i notMember
        simp only [notMember, ↓reduceIte]
        exact kept

/-! ## The epoch transition -/

/-- A step that keeps the validators and the balances. -/
def Untouched (state after : BeaconState preset fork) : Prop :=
  after.validators.data = state.validators.data ∧ after.balances = state.balances

theorem Untouched.trans {first second third : BeaconState preset fork}
    (one : Untouched first second) (two : Untouched second third) : Untouched first third :=
  ⟨two.1.trans one.1, two.2.trans one.2⟩

/-- The steps that close an epoch from Altair, after the history, touch no validator or balance.
-/
theorem untouched_epochEnd {altair : .altair ≤ fork}
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

theorem untouched_processHistoricalRootsUpdate
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

/-- The ceiling on the effective balances, between two states.

While the later registry is below `2^64`, take a validator of the earlier state.

Later its effective balance is at most the larger of its value before and its balance after. -/
def CeilingStep {fork' : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') : Prop :=
  after.validators.data.size < 2 ^ 64 → ∀ (position : Nat) (validator : Validator),
    state.validators.data[position]? = some validator →
    ∃ later, after.validators.data[position]? = some later ∧
      later.effectiveBalance.toNat ≤ max validator.effectiveBalance.toNat (balanceAt after position)

/-- A step that raises no effective balance keeps them under the ceiling. -/
theorem EffectiveCapped.ceilingStep {fork' : Base.Fork} {after : BeaconState preset fork'}
    (held : EffectiveCapped state after) : CeilingStep state after := by
  intro small position validator found
  obtain ⟨later, laterFound, step⟩ := held.validators small position validator found
  exact ⟨later, laterFound,
    Nat.le_trans (UInt64.le_iff_toNat_le.mp step) (Nat.le_max_left _ _)⟩

/-- The effective balances after the update, against those of the state the epoch starts from. -/
theorem ceiling_of_update {paid balanced : BeaconState preset fork}
    (prefixHeld : EffectiveCapped state paid)
    (balancedOk : processEffectiveBalanceUpdates paid = .ok balanced)
    (suffix : Untouched balanced after) : CeilingStep state after := by
  intro small position validator found
  have paidSmall : paid.validators.data.size < 2 ^ 64 := by
    have sizes := congrArg Array.size suffix.1
    have updateSizes := (sameSizes_processEffectiveBalanceUpdates balancedOk).1
    omega
  unfold processEffectiveBalanceUpdates at balancedOk
  obtain ⟨balances, _, updated⟩ := foldlM_updateEffectiveBalance_ceiling List.nodup_range
    (fun other member => List.mem_range.mp member) paidSmall balancedOk
  obtain ⟨middle, middleFound, middleStep⟩ :=
    prefixHeld.validators paidSmall position validator found
  have inside : position < paid.validators.data.size :=
    (Array.getElem?_eq_some_iff.mp middleFound).1
  obtain ⟨later, laterFound, bound⟩ := updated position middle middleFound
  simp only [List.mem_range, inside, ↓reduceIte] at bound
  refine ⟨later, by rw [suffix.1]; exact laterFound, ?_⟩
  have balanceSame : balanceAt after position = balanceAt paid position := by
    simp only [balanceAt, suffix.2, balances]
  rw [balanceSame]
  have middleNat := UInt64.le_iff_toNat_le.mp middleStep
  omega

/-- From Altair, the epoch transition keeps each effective balance under its ceiling. -/
theorem ceilingStep_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    CeilingStep state after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetHeld : EffectiveCapped slashed reset := by
    split at resetOk
    · exact effectiveCapped_processEth1DataReset resetOk
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
  -- The steps before the update raise no effective balance.
  have prefixHeld : EffectiveCapped state paid :=
    (effectiveCapped_processJustificationAndFinalization justifiedOk).trans <|
    (effectiveCapped_processInactivityUpdates scoredOk).trans <|
    (effectiveCapped_processRewardsAndPenalties rewardedOk).trans <|
    (effectiveCapped_processRegistryUpdates registeredOk).trans <|
    (effectiveCapped_processSlashings slashedOk).trans <|
    resetHeld.trans <|
    (effectiveCapped_processPendingBalances pendingOk).trans (.of_data paidUntouched.1)
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
  exact ceiling_of_update prefixHeld balancedOk suffix

/-- The epoch transition keeps each effective balance under its ceiling, at every fork. -/
theorem ceilingStep_processEpoch (computed : processEpoch config checks state = .ok after) :
    CeilingStep state after := by
  unfold processEpoch at computed
  split at computed
  · exact ceilingStep_processEpochAltair computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have prefixHeld : EffectiveCapped state reset :=
    (effectiveCapped_processJustificationAndFinalization justifiedOk).trans <|
    (effectiveCapped_processRewardsAndPenalties rewardedOk).trans <|
    (effectiveCapped_processRegistryUpdates registeredOk).trans <|
    (effectiveCapped_processSlashings slashedOk).trans
      (effectiveCapped_processEth1DataReset resetOk)
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
  exact ceiling_of_update prefixHeld balancedOk
    (clearedUntouched.trans <| mixedUntouched.trans <|
      (untouched_processHistoricalRootsUpdate rootedOk).trans rotatedUntouched)

/-! ## Slots, upgrades and chains -/

/-- One slot keeps each effective balance under its ceiling. -/
theorem ceilingStep_advanceSlot (computed : advanceSlot config checks state = .ok after) :
    CeilingStep state after := by
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
  have epochStep : CeilingStep cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact ceilingStep_processEpoch epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact (EffectiveCapped.refl cached).ceilingStep
  intro small position validator found
  obtain ⟨later, laterFound, bound⟩ := epochStep (afterValidators ▸ small) position
    validator (cachedValidators ▸ found)
  refine ⟨later, afterValidators ▸ laterFound, ?_⟩
  simp only [balanceAt, afterBalances] at bound ⊢
  exact bound

/-- Queueing a validator that is not yet active sets its effective balance to zero. -/
theorem effectiveCapped_queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    EffectiveCapped state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact EffectiveCapped.trans (by exact .of_data rfl)
    ((EffectiveCapped.setValidator (old := validator) (by exact found) set₂
      UInt64.zero_le).trans (.of_data rfl))

/-- An upgrade raises no effective balance. -/
theorem effectiveCapped_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    EffectiveCapped pre.state post.val.state := by
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
    have compoundedHeld := EffectiveCapped.foldlM (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · exact effectiveCapped_queueExcessActiveBalance (liftAccessor_ok.mp ok)
        · cases ok
          exact .refl _
      · cases ok
        exact .refl _) compounded
    have queuedHeld := EffectiveCapped.foldlM
      (fun _ _ _ ok => effectiveCapped_queuePreActivation ok) queued
    exact EffectiveCapped.trans (by exact .of_data rfl) (queuedHeld.trans compoundedHeld)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact .of_data (upgradeHezeFields_lists _).1

/-- Each step keeps each effective balance under its ceiling. -/
theorem Step.ceilingStep {before after : ForkedBeaconState preset}
    (step : Step config checks before after) : CeilingStep before.state after.state := by
  cases step with
  | slot _ computed => exact ceilingStep_advanceSlot computed
  | upgrade _ computed => exact (effectiveCapped_upgradeNext computed).ceilingStep
  | block _ _ _ _ computed =>
    exact (effectiveCapped_processBlock (applySignedBlock_ok computed).2.1).ceilingStep

/-- Along a run, the effective balance of a validator of the start stays under any common ceiling.

Take a validator of the start, and a bound at least its effective balance at the start.

Let its balance at every state of the run be at most the bound.

Then at the end its effective balance is at most the bound.

From Gloas the registry at the end must be below `2^64`. -/
theorem Run.effectiveBalance_ceiling {start : ForkedBeaconState preset} :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      after.state.validators.data.size < 2 ^ 64 →
      ∀ (position : Nat) (validator : Validator),
        start.state.validators.data[position]? = some validator →
        ∀ bound : Nat, validator.effectiveBalance.toNat ≤ bound →
        (∀ state ∈ run.states, balanceAt state.state position ≤ bound) →
        ∃ later, after.state.validators.data[position]? = some later ∧
          later.effectiveBalance.toNat ≤ bound
  | _, .nil, _, _, validator, found, _, startBound, _ => ⟨validator, found, startBound⟩
  | _, .snoc run step, small, position, validator, found, bound, startBound, balances => by
    have middleSmall :=
      Nat.lt_of_le_of_lt (stepRelation_registryLifecycle.step step).size_le small
    obtain ⟨middle, middleFound, middleBound⟩ :=
      run.effectiveBalance_ceiling middleSmall position validator found bound startBound
        (fun state member => balances state (List.mem_append_left _ member))
    obtain ⟨later, laterFound, stepBound⟩ := step.ceilingStep small position middle middleFound
    have lastBalance := balances _ (List.mem_append_right _ (List.mem_singleton_self _))
    exact ⟨later, laterFound, by omega⟩

end EthLib.Consensus
