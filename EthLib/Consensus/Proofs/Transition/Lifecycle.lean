module

public import EthLib.Consensus.Proofs.Transition.Reachable

/-!
# Proofs: the lifecycle of a validator, at every fork

A validator keeps its index in the registry for the life of the chain.

At that index, four of its fields only move one way.

- Its public key never changes.
- Once its activation epoch is set, it never changes.
- Once its exit epoch is set, it never changes.
- Once it is slashed, it stays slashed.

Its withdrawal credentials may change.

From Capella a BLS key may move to an execution address.

From Electra an execution address may switch to compounding.

The registry also never shrinks.

From Gloas the registry is a progressive list with no limit.

A new validator then goes to the index `size.toUInt64`, which wraps at `2^64`.

With `2^64` validators or more, that index is an existing one, and the deposit replaces it.

So the facts above hold while the registry has fewer than `2^64` validators.

Before Gloas the type of the registry bounds it by the preset limit, which is below `2^64`.

Each step of the chain keeps these facts, at every fork, and so does every chain.
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

The public key is the same.

An activation or exit epoch that was set is the same, and a slashed validator stays slashed. -/
structure ValidatorLifecycle (validator later : Validator) : Prop where
  pubkey : later.pubkey = validator.pubkey
  activationEpoch : validator.activationEpoch ≠ FAR_FUTURE_EPOCH →
    later.activationEpoch = validator.activationEpoch
  exitEpoch : validator.exitEpoch ≠ FAR_FUTURE_EPOCH → later.exitEpoch = validator.exitEpoch
  slashed : validator.slashed = true → later.slashed = true

theorem ValidatorLifecycle.refl (validator : Validator) : ValidatorLifecycle validator validator :=
  ⟨rfl, fun _ => rfl, fun _ => rfl, id⟩

theorem ValidatorLifecycle.trans {first second third : Validator}
    (one : ValidatorLifecycle first second) (two : ValidatorLifecycle second third) :
    ValidatorLifecycle first third where
  pubkey := two.pubkey.trans one.pubkey
  activationEpoch set := by
    have same := one.activationEpoch set
    exact (two.activationEpoch (same ▸ set)).trans same
  exitEpoch set := by
    have same := one.exitEpoch set
    exact (two.exitEpoch (same ▸ set)).trans same
  slashed := two.slashed ∘ one.slashed

/-- The registry of a later state, which may be of a later fork.

It is at least as long.

While it has fewer than `2^64` validators, each validator is at its index, later in its life. -/
structure RegistryLifecycle {fork' : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') : Prop where
  size_le : state.validators.data.size ≤ after.validators.data.size
  validators : after.validators.data.size < 2 ^ 64 →
    ∀ (index : Nat) (validator : Validator), state.validators.data[index]? = some validator →
      ∃ later, after.validators.data[index]? = some later ∧ ValidatorLifecycle validator later

namespace RegistryLifecycle

theorem refl (state : BeaconState preset fork) : RegistryLifecycle state state :=
  ⟨Nat.le_refl _, fun _ _ validator found => ⟨validator, found, .refl validator⟩⟩

theorem trans {fork' fork'' : Base.Fork} {first : BeaconState preset fork}
    {second : BeaconState preset fork'} {third : BeaconState preset fork''}
    (one : RegistryLifecycle first second) (two : RegistryLifecycle second third) :
    RegistryLifecycle first third where
  size_le := Nat.le_trans one.size_le two.size_le
  validators small index validator found := by
    -- The middle registry is at most as long as the last one, so it is below `2^64` too.
    obtain ⟨middle, middleFound, oneStep⟩ :=
      one.validators (Nat.lt_of_le_of_lt two.size_le small) index validator found
    obtain ⟨later, laterFound, twoStep⟩ := two.validators small index middle middleFound
    exact ⟨later, laterFound, oneStep.trans twoStep⟩

/-- A state with the same validators, of any fork. -/
theorem of_data {fork' : Base.Fork} {after : BeaconState preset fork'}
    (same : after.validators.data = state.validators.data) : RegistryLifecycle state after :=
  ⟨Nat.le_of_eq (by rw [same]), fun _ index validator found =>
    ⟨validator, by rw [same]; exact found, .refl _⟩⟩

/-- A step that keeps the validators at the indices of the registry, while it stays small.

Each index of the registry has a validator after it. -/
theorem of_read {after : BeaconState preset fork}
    (present : ∀ index, index < state.validators.data.size →
      (after.validators.data[index]?).isSome)
    (read : after.validators.data.size < 2 ^ 64 → ∀ index, index < state.validators.data.size →
      after.validators.data[index]? = state.validators.data[index]?) :
    RegistryLifecycle state after where
  size_le := by
    refine Nat.le_of_not_lt fun shorter => ?_
    have := present _ shorter
    simp at this
  validators small index validator found := by
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    exact ⟨validator, (read small index inside).trans found, .refl _⟩

/-- A fold whose every step keeps the lifecycle keeps it. -/
theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → RegistryLifecycle s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : RegistryLifecycle state after :=
  foldlM_ok_invariant (RegistryLifecycle state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

/-- Replacing a validator by itself later in its life. -/
theorem putValidator {index : Nat} {validator : Validator}
    (inside : index < state.validators.data.size)
    (step : ValidatorLifecycle state.validators.data[index] validator) :
    RegistryLifecycle state (state.putValidator index inside validator) where
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
    (step : ValidatorLifecycle old validator) : RegistryLifecycle state after := by
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
    (step : ValidatorLifecycle old validator) :
    RegistryLifecycle state after := by
  have sizes := sameSizes_setValidator set
  refine ⟨Nat.le_of_eq sizes.1.symm, fun small => ?_⟩
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exact : position.toUInt64.toNat = position :=
    toNat_toUInt64_of_lt_pow (by rw [sizes.1] at small; omega)
  refine (setValidator (old := old) ?_ set step).validators small
  simp [getValidator, exact, found]

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : RegistryLifecycle state after :=
  of_data (by rw [increaseBalance_validators computed])

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : RegistryLifecycle state after :=
  of_data (by rw [decreaseBalance_validators computed])

end RegistryLifecycle

/-- Below Gloas the registry is within its limit, so the condition on its size holds. -/
theorem RegistryLifecycle.validators_of_before {fork' : Base.Fork}
    {after : BeaconState preset fork'} (lifecycle : RegistryLifecycle state after)
    (before : fork' < .glamsterdam) (index : Nat)
    {validator : Validator} (found : state.validators.data[index]? = some validator) :
    ∃ later, after.validators.data[index]? = some later ∧ ValidatorLifecycle validator later :=
  lifecycle.validators
    (Nat.lt_of_le_of_lt (after.validators.bound before) (UInt64.toNat_lt _)) index validator found

/-! ## Mutators -/

theorem registryLifecycle_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨far, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _
  · have same := (exitQueue_validators queue).1
    -- Only a validator with no exit epoch gets one.
    exact (RegistryLifecycle.of_data (by rw [same])).trans <|
      .setValidator ((getValidator_of_validators_eq same index).trans found) set
        ⟨rfl, fun _ => rfl, fun set => absurd far set, id⟩

theorem registryLifecycle_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    RegistryLifecycle state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  -- The slashed validator keeps its key and its epochs, and is now slashed.
  exact (registryLifecycle_initiateValidatorExit exitedOk).trans <|
    ((RegistryLifecycle.setValidator found markedOk
      ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩).trans (by exact .of_data rfl)).trans <|
    (RegistryLifecycle.decreaseBalance loweredOk).trans <|
    (RegistryLifecycle.increaseBalance raisedOk).trans <|
    (RegistryLifecycle.increaseBalance lastOk).trans
      (.of_data (by rw [(slashValidator_last done).1]))

/-! ## The steps of a block -/

theorem registryLifecycle_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : RegistryLifecycle state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_data rfl

theorem registryLifecycle_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_data rfl

theorem registryLifecycle_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : RegistryLifecycle state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_data (by rw [← rest])

theorem registryLifecycle_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    RegistryLifecycle state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact registryLifecycle_slashValidator slashed

theorem registryLifecycle_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    RegistryLifecycle step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact registryLifecycle_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem registryLifecycle_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    RegistryLifecycle state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => RegistryLifecycle state step.1)
    (fun _ _ _ before ok => before.trans (registryLifecycle_slashIfSlashable ok))
    (show RegistryLifecycle state (state, false).1 from .refl state) folded

theorem registryLifecycle_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    RegistryLifecycle state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : RegistryLifecycle raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_data rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        RegistryLifecycle state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_data rfl
    exact (flagged _ _).trans ((RegistryLifecycle.increaseBalance raisedOk).trans last)
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
theorem registryLifecycle_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    RegistryLifecycle state after := by
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

theorem registryLifecycle_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    RegistryLifecycle state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact registryLifecycle_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · rw [liftAccessor_ok] at computed
    exact .increaseBalance computed

theorem registryLifecycle_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    RegistryLifecycle state after := by
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
        exact (registryLifecycle_addValidatorToRegistry added).trans (.of_data rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_data rfl
  · exact registryLifecycle_applyPendingDeposit computed

theorem registryLifecycle_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (RegistryLifecycle.of_data (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (registryLifecycle_applyDeposit applied)

theorem registryLifecycle_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    RegistryLifecycle state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact registryLifecycle_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem registryLifecycle_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_data rfl

theorem registryLifecycle_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    RegistryLifecycle state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

theorem registryLifecycle_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    RegistryLifecycle state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

theorem registryLifecycle_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    RegistryLifecycle state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (registryLifecycle_computeExitEpochAndUpdateChurn churned).trans (.of_data rfl)
  · cases computed
    exact .refl _

theorem registryLifecycle_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    RegistryLifecycle state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact registryLifecycle_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact registryLifecycle_requestPartialWithdrawal computed

theorem registryLifecycle_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    RegistryLifecycle state after := by
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
theorem registryLifecycle_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    RegistryLifecycle state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (RegistryLifecycle.setValidator found set ⟨rfl, fun _ => rfl, fun _ => rfl, id⟩).trans
    (registryLifecycle_queueExcessActiveBalance queued)

/-- The source of a consolidation gets an exit epoch, which it did not have. -/
theorem registryLifecycle_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourcePosition]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    RegistryLifecycle state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, _, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have churnedKept := registryLifecycle_computeConsolidationEpochAndUpdateChurn churned
  have same : churnedState.validators.data = state.validators.data := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    rfl
  exact churnedKept.trans <|
    (RegistryLifecycle.setValidator_position (old := source) (by rw [same]; exact found) set
      ⟨rfl, fun _ => rfl, fun set => absurd far set, id⟩).trans (.of_data rfl)

theorem registryLifecycle_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    RegistryLifecycle state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact registryLifecycle_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact registryLifecycle_queueConsolidation (Array.getElem?_eq_getElem _)
        (by clear computed; simp_all) computed

theorem registryLifecycle_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    RegistryLifecycle state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processDepositRequest ok)
      depositsOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processConsolidationRequest ok)
      consolidationsOk

/-! ## Withdrawals -/

theorem registryLifecycle_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : RegistryLifecycle state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl
  · exact .decreaseBalance computed

theorem registryLifecycle_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    RegistryLifecycle state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : RegistryLifecycle state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_applyWithdrawal ok) appliedOk
  have two : RegistryLifecycle applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_data rfl
    · cases indexedOk
      exact .refl _
  have queued : ∀ kept : BeaconState preset fork,
      RegistryLifecycle kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl
    · exact .refl _
  have partials : ∀ kept : BeaconState preset fork,
      RegistryLifecycle kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl
    · exact .refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → RegistryLifecycle kept finished := by
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
  have lastKept : RegistryLifecycle finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact .of_data rfl
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

theorem registryLifecycle_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    RegistryLifecycle state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact registryLifecycle_applyExpectedWithdrawals applied
    · cases computed
      exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact registryLifecycle_applyExpectedWithdrawals applied

/-- A change to an execution address changes only the withdrawal credentials of the validator. -/
theorem registryLifecycle_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact .setValidator found set ⟨rfl, fun _ => rfl, fun _ => rfl, id⟩

/-! ## The parent payload and the execution part of a block -/

theorem registryLifecycle_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_data rfl

theorem registryLifecycle_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    RegistryLifecycle state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .of_data rfl)

theorem registryLifecycle_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    RegistryLifecycle state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl

theorem registryLifecycle_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : RegistryLifecycle state after := by
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

theorem registryLifecycle_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    RegistryLifecycle state after := by
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
  exact (registryLifecycle_settleParentPayment settledOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processDepositRequest ok)
      depositsOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processConsolidationRequest ok)
      consolidationsOk).trans <|
    (RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_processBuilderDepositRequest ok) buildersOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processBuilderExitRequest ok)
      exitsOk).trans (.of_data rfl)

theorem registryLifecycle_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    RegistryLifecycle state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_data rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_data rfl

theorem registryLifecycle_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    RegistryLifecycle state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (registryLifecycle_processWithdrawals withdrawnOk).trans
      (registryLifecycle_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (registryLifecycle_processWithdrawals withdrawnOk).trans
      (registryLifecycle_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact registryLifecycle_processExecutionPayload computed
    · cases computed
      exact .refl _

/-! ## The sync aggregate -/

theorem registryLifecycle_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    RegistryLifecycle state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine RegistryLifecycle.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (RegistryLifecycle.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

/-! ## Blocks -/

theorem registryLifecycle_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    RegistryLifecycle state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok)
        proposersOk).trans <|
      (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok)
        attestersOk).trans <|
      (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttestation ok)
        attestedOk).trans <|
      (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok)
        exitsOk).trans <|
      (RegistryLifecycle.foldlM
        (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changesOk).trans <|
      RegistryLifecycle.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : RegistryLifecycle exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact RegistryLifecycle.foldlM
        (fun _ _ _ ok => registryLifecycle_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : RegistryLifecycle changed after := by
    split at requestsOk
    · exact registryLifecycle_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  exact (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processProposerSlashing ok)
      proposersOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttesterSlashing ok)
      attestersOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processAttestation ok)
      attestedOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processDeposit ok)
      depositedOk).trans <|
    (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_processVoluntaryExit ok)
      exitsOk).trans <|
    changes.trans requests

theorem registryLifecycle_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    RegistryLifecycle state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidKept : RegistryLifecycle state paid := by
      split at paidOk
      · exact registryLifecycle_processParentExecutionPayload paidOk
      · cases paidOk
        exact .refl _
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedKept : RegistryLifecycle headed executed := by
      split at executedOk
      · exact registryLifecycle_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    -- Heze drops the vote on the deposit contract.
    have votedKept : RegistryLifecycle revealed voted := by
      split at votedOk
      · exact registryLifecycle_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    exact paidKept.trans <| (registryLifecycle_processBlockHeader headedOk).trans <|
      executedKept.trans <| (registryLifecycle_processRandao revealedOk).trans <|
      votedKept.trans <| (registryLifecycle_processOperations operatedOk).trans
        (registryLifecycle_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (registryLifecycle_processBlockHeader headerOk).trans <|
    (registryLifecycle_processRandao randaoOk).trans <|
    (registryLifecycle_processEth1Data eth1Ok).trans
      (registryLifecycle_processOperations operationsOk)

/-! ## The steps of an epoch -/

theorem registryLifecycle_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    RegistryLifecycle state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_data (by rw [← rest])

theorem registryLifecycle_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : RegistryLifecycle state after :=
  RegistryLifecycle.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (RegistryLifecycle.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem registryLifecycle_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    RegistryLifecycle state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact registryLifecycle_applyAllDeltas applied

/-- Joining the activation queue changes only the eligibility epoch. -/
theorem validatorLifecycle_queueForActivation {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    ValidatorLifecycle validator queued := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨rfl, fun _ => rfl, fun _ => rfl, id⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem registryLifecycle_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    RegistryLifecycle state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set := RegistryLifecycle.setValidator found markedOk
    (validatorLifecycle_queueForActivation queuedOk)
  split at computed
  · exact set.trans (registryLifecycle_initiateValidatorExit (liftAccessor_ok.mp computed))
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

/-- A validator eligible for activation has no activation epoch yet. -/
theorem activationEpoch_of_isEligibleForActivation {validator : Validator}
    (eligible : isEligibleForActivation state validator = true) :
    validator.activationEpoch = FAR_FUTURE_EPOCH := by
  simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
  exact eligible.2

/-- Activating a validator that has no activation epoch yet. -/
theorem registryLifecycle_activateValidator {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (far : validator.activationEpoch = FAR_FUTURE_EPOCH)
    (computed : activateValidator state index = .ok after) : RegistryLifecycle state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨old, oldFound, _, _, set⟩ := computed
  have same := Except.ok.inj (oldFound.symm.trans found)
  subst same
  exact .setValidator oldFound set ⟨rfl, fun set => absurd far set, fun _ => rfl, id⟩

/-- Each index in the activation queue is that of a validator eligible for activation. -/
theorem mem_activationQueue {index : ValidatorIndex} (member : index ∈ activationQueue state) :
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
    simpa only [Array.getElem?_toList] using (List.mem_zipIdx_iff_getElem?.mp positionOk)
  · cases selected

/-- The activation queue holds each index at most once, while the registry is below `2^64`. -/
theorem activationQueue_nodup (small : state.validators.data.size < 2 ^ 64) :
    (activationQueue state).Nodup := by
  let entries := state.validators.data.toList.zipIdx.filterMap fun (validator, index) =>
    if isEligibleForActivation state validator then
      some (validator.activationEligibilityEpoch, index.toUInt64)
    else none
  -- The positions of the registry increase, and below `2^64` their indices of 64 bits differ.
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
    dsimp only at equal lt
    have equalNat := congrArg UInt64.toNat equal
    rw [toNat_toUInt64_of_lt_pow (by omega), toNat_toUInt64_of_lt_pow (by omega)] at equalNat
    omega
  have unique : (entries.map (·.2)).Nodup := List.pairwise_map.mpr distinct
  exact ((List.mergeSort_perm entries _).map (·.2)).nodup_iff.mpr unique

/-- Activating distinct validators, each eligible for activation at the start. -/
theorem registryLifecycle_foldActivateValidator :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      indices.Nodup →
      (∀ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
        validator.activationEpoch = FAR_FUTURE_EPOCH) →
      indices.foldlM activateValidator state = .ok after → RegistryLifecycle state after
  | [], state, after, _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  | index :: rest, state, after, unique, eligible, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    obtain ⟨validator, found, far⟩ := eligible index List.mem_cons_self
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    refine (registryLifecycle_activateValidator found far first).trans
      (registryLifecycle_foldActivateValidator restUnique (fun other member => ?_) tail)
    -- The other validators of the queue are not touched by this activation.
    have distinct : other ≠ index := fun same => absent (same ▸ member)
    obtain ⟨otherValidator, otherFound, otherFar⟩ := eligible other (List.mem_cons_of_mem _ member)
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at first
    obtain ⟨_, _, _, _, set⟩ := first
    exact ⟨otherValidator, (getValidator_setValidator_of_ne set distinct).trans otherFound,
      otherFar⟩

theorem registryLifecycle_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    RegistryLifecycle state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine RegistryLifecycle.foldlM (fun state _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact .setValidator found set ⟨rfl, fun _ => rfl, fun _ => rfl, id⟩
    split at ok
    · exact registryLifecycle_initiateValidatorExit (liftAccessor_ok.mp ok)
    split at ok
    · rename_i eligible
      rw [liftAccessor_ok] at ok
      have far := activationEpoch_of_isEligibleForActivation eligible
      exact .setValidator found ok ⟨rfl, fun set => absurd far set, fun _ => rfl, id⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  rename_i notElectra
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  -- Before Electra the registry is within its limit, far below `2^64`.
  have before : fork < .glamsterdam := Nat.lt_trans (Nat.lt_of_not_le notElectra) (by decide)
  have small : updated.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (updated.validators.bound before) (UInt64.toNat_lt _)
  refine (RegistryLifecycle.foldlM (fun _ _ _ ok => registryLifecycle_updateRegistryEntry ok)
    updatedOk).trans (registryLifecycle_foldActivateValidator
      (List.Nodup.sublist (List.take_sublist _ _) (activationQueue_nodup small))
      (fun index member => ?_) activated)
  obtain ⟨position, validator, equal, found, eligible⟩ :=
    mem_activationQueue (List.mem_of_mem_take member)
  refine ⟨validator, ?_, activationEpoch_of_isEligibleForActivation eligible⟩
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have exact : index.toNat = position := by
    rw [← equal, toNat_toUInt64_of_lt_pow (by omega)]
  simp [getValidator, exact, found]

theorem registryLifecycle_processSlashings (computed : processSlashings state = .ok after) :
    RegistryLifecycle state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine RegistryLifecycle.foldlM (fun _ _ _ ok => ?_) applied
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
  · refine RegistryLifecycle.foldlM (fun _ _ _ ok => ?_) computed
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

theorem registryLifecycle_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    RegistryLifecycle state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_data rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- An update of effective balances changes only the effective balances. -/
theorem registryLifecycle_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    RegistryLifecycle state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine RegistryLifecycle.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, _, _, _, _, set⟩ := ok
  exact .setValidator found set ⟨rfl, fun _ => rfl, fun _ => rfl, id⟩

theorem registryLifecycle_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    RegistryLifecycle state after := by
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

theorem registryLifecycle_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    RegistryLifecycle state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_data rfl

/-! ## The steps of an epoch from Altair -/

theorem registryLifecycle_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    RegistryLifecycle state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_data rfl

theorem registryLifecycle_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      RegistryLifecycle state pass.1.state
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
      exact (registryLifecycle_applyPendingDeposit credited).trans
        (registryLifecycle_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact registryLifecycle_passPendingDeposits (deposits := rest) ‹_›
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
    exact (registryLifecycle_applyPendingDeposit credited).trans
      (registryLifecycle_passPendingDeposits (deposits := rest) ‹_›)

theorem registryLifecycle_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    RegistryLifecycle state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (registryLifecycle_passPendingDeposits ‹_›).trans (.of_data rfl)

theorem registryLifecycle_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      RegistryLifecycle state result.1
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
      exact registryLifecycle_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (RegistryLifecycle.decreaseBalance loweredOk).trans <|
      (RegistryLifecycle.increaseBalance raisedOk).trans
        (registryLifecycle_passPendingConsolidations (result := (passed, read)) passedOk)

theorem registryLifecycle_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    RegistryLifecycle state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine (registryLifecycle_processPendingDeposits deposited).trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (registryLifecycle_passPendingConsolidations ‹_›).trans (.of_data rfl)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- The steps that close an epoch from Altair, after the history. -/
private theorem registryLifecycle_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : RegistryLifecycle rooted after := by
  have syncedKept : RegistryLifecycle rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact .of_data rfl
  have lookedKept : RegistryLifecycle synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedKept : RegistryLifecycle looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedKept.trans (lookedKept.trans windowedKept)

theorem registryLifecycle_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    RegistryLifecycle state after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetKept : RegistryLifecycle slashed reset := by
    split at resetOk
    · exact registryLifecycle_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ .refl _
  have paidKept : RegistryLifecycle pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ .refl _
  have clearedKept : RegistryLifecycle balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_data rfl
  have mixedKept : RegistryLifecycle cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_data rfl
  have head : RegistryLifecycle state mixed :=
    (registryLifecycle_processJustificationAndFinalization justifiedOk).trans <|
    (registryLifecycle_processInactivityUpdates scoredOk).trans <|
    (registryLifecycle_processRewardsAndPenalties rewardedOk).trans <|
    (registryLifecycle_processRegistryUpdates registeredOk).trans <|
    (registryLifecycle_processSlashings slashedOk).trans <|
    resetKept.trans <|
    (registryLifecycle_processPendingBalances pendingOk).trans <|
    paidKept.trans <|
    (registryLifecycle_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans mixedKept
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · have rootedKept : RegistryLifecycle mixed rooted := by
      unfold processHistoricalSummariesUpdate at rootedOk
      simp only [bind, Except.bind, pure, Except.pure] at rootedOk
      repeat' (split at rootedOk <;> try cases rootedOk)
      all_goals first
        | exact .refl _
        | exact .of_data rfl
    exact head.trans <| rootedKept.trans (registryLifecycle_epochEnd syncedOk lookedOk windowed)
  · exact head.trans <| (registryLifecycle_processHistoricalRootsUpdate rootedOk).trans
      (registryLifecycle_epochEnd syncedOk lookedOk windowed)

theorem registryLifecycle_processEpoch
    (computed : processEpoch config checks state = .ok after) : RegistryLifecycle state after := by
  unfold processEpoch at computed
  split at computed
  · exact registryLifecycle_processEpochAltair computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have clearedKept : RegistryLifecycle balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_data rfl
  have mixedKept : RegistryLifecycle cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_data rfl
  exact (registryLifecycle_processJustificationAndFinalization justifiedOk).trans <|
    (registryLifecycle_processRewardsAndPenalties rewardedOk).trans <|
    (registryLifecycle_processRegistryUpdates registeredOk).trans <|
    (registryLifecycle_processSlashings slashedOk).trans <|
    (registryLifecycle_processEth1DataReset resetOk).trans <|
    (registryLifecycle_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans <| mixedKept.trans <|
    (registryLifecycle_processHistoricalRootsUpdate rootedOk).trans
      (registryLifecycle_processParticipationRecordUpdates rotated)

/-! ## Slots, upgrades and chains -/

theorem registryLifecycle_advanceSlot (computed : advanceSlot config checks state = .ok after) :
    RegistryLifecycle state after := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedKept : RegistryLifecycle state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact .of_data rfl
  have epochedKept : RegistryLifecycle cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact registryLifecycle_processEpoch epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ .refl _
  exact cachedKept.trans (epochedKept.trans (.of_data rfl))

/-- Queueing a validator that is not yet active changes its eligibility and effective balance. -/
theorem registryLifecycle_queuePreActivation {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    RegistryLifecycle state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  have reset := RegistryLifecycle.setValidator (old := validator) (by exact found) set₂
    ⟨rfl, fun _ => rfl, fun _ => rfl, id⟩
  exact RegistryLifecycle.trans (by exact .of_data rfl) (reset.trans (.of_data rfl))

theorem registryLifecycle_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    RegistryLifecycle pre.state post.val.state := by
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
    have compoundedKept := RegistryLifecycle.foldlM (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · exact registryLifecycle_queueExcessActiveBalance (liftAccessor_ok.mp ok)
        · cases ok
          exact .refl _
      · cases ok
        exact .refl _) compounded
    have queuedKept := RegistryLifecycle.foldlM
      (fun _ _ _ ok => registryLifecycle_queuePreActivation ok) queued
    exact RegistryLifecycle.trans (by exact .of_data rfl) (queuedKept.trans compoundedKept)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToFulu_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact .of_data (upgradeToGloas_spec upgraded).1
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact .of_data (upgradeHezeFields_lists _).1

/-- Every step of a chain keeps the lifecycle of the validators. -/
theorem stepRelation_registryLifecycle :
    StepRelation config checks fun (forked after : ForkedBeaconState preset) =>
      RegistryLifecycle forked.state after.state where
  refl forked := .refl forked.state
  trans one two := one.trans two
  advanceSlot computed := registryLifecycle_advanceSlot computed
  upgradeNext _ computed := registryLifecycle_upgradeNext computed
  applySignedBlock computed := registryLifecycle_processBlock (applySignedBlock_ok computed).2.1

/-- Along every chain, each validator keeps its index, its key, its set epochs and its slashing.

From Gloas this holds while the registry has fewer than `2^64` validators. -/
theorem Reaches.registryLifecycle {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) : RegistryLifecycle start.state after.state :=
  stepRelation_registryLifecycle.reaches chain

end EthLib.Consensus
