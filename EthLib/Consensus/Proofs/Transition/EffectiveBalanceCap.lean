module

public import EthLib.Consensus.Proofs.Transition.Reachable

/-!
# Proofs: the cap on effective balances, at every fork

An effective balance is at most the largest effective balance of its validator at the fork.

Before Electra that largest value is `MAX_EFFECTIVE_BALANCE` for every validator.

From Electra it depends on the credentials, as [EIP-7251] specifies.

With compounding credentials it is `MAX_EFFECTIVE_BALANCE_ELECTRA`.

Otherwise it is `MIN_ACTIVATION_BALANCE`.

Three kinds of step set an effective balance.

- A new validator gets its deposit, rounded down to an increment, and at most its largest value.
- The update at the end of an epoch moves it to the balance, rounded down and capped, or leaves it.
- The upgrade to Electra sets the effective balance of a validator that is not yet active to zero.

Two kinds of step change the credentials, and so the largest value.

- A change of BLS credentials gives an execution address, which does not compound.
- A switch to compounding raises the largest value from Electra.

So the cap holds in every state that a chain reaches, with two conditions on the preset.

- `MAX_EFFECTIVE_BALANCE ≤ MIN_ACTIVATION_BALANCE` keeps the cap at the upgrade to Electra.
- `MIN_ACTIVATION_BALANCE ≤ MAX_EFFECTIVE_BALANCE_ELECTRA` keeps it at a switch to compounding.

Mainnet and the minimal preset satisfy both, with `32 ETH ≤ 32 ETH ≤ 2048 ETH`.

The first condition is needed.

Without it, an effective balance before Electra may be above `MIN_ACTIVATION_BALANCE`.

The upgrade keeps it, so a validator without compounding credentials is then above its cap.

An effective balance can then exceed any earlier value by at most the gap to its cap.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- Each effective balance is at most the largest effective balance of its validator at the fork.
-/
def EffectiveBalancesCapped (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data,
    validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator

/-- The order of the largest effective balances that the cap needs.

Mainnet and the minimal preset satisfy it. -/
structure EffectiveBalanceCaps (preset : Preset) : Prop where
  max_le_activation : preset.MAX_EFFECTIVE_BALANCE ≤ preset.MIN_ACTIVATION_BALANCE
  activation_le_electra : preset.MIN_ACTIVATION_BALANCE ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA

theorem effectiveBalanceCaps_mainnet : EffectiveBalanceCaps Preset.mainnet where
  max_le_activation := by decide
  activation_le_electra := by decide

theorem effectiveBalanceCaps_minimal : EffectiveBalanceCaps Preset.minimal where
  max_le_activation := by decide
  activation_le_electra := by decide

/-- The smaller of two values is at most the second. -/
private theorem uint64_min_le_right (first second : UInt64) : min first second ≤ second := by
  rw [UInt64.min_def]
  split
  · assumption
  · exact UInt64.le_refl _

/-- A remainder is at most the value it divides. -/
private theorem uint64_mod_le (value divisor : UInt64) : value % divisor ≤ value :=
  UInt64.le_iff_toNat_le.mpr (by rw [UInt64.toNat_mod]; exact Nat.mod_le _ _)

/-- A new validator from a deposit is under the cap. -/
theorem getValidatorFromDeposit_capped {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} :
    (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount).effectiveBalance ≤
      withdrawalMaxEffectiveBalance preset fork
        (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount) :=
  uint64_min_le_right _ _

/-- A step that keeps the cap on effective balances. -/
structure CapKept (state after : BeaconState preset fork) : Prop where
  kept : EffectiveBalancesCapped state → EffectiveBalancesCapped after

namespace CapKept

theorem refl (state : BeaconState preset fork) : CapKept state state := ⟨id⟩

theorem trans {first second third : BeaconState preset fork} (one : CapKept first second)
    (two : CapKept second third) : CapKept first third :=
  ⟨two.kept ∘ one.kept⟩

/-- A state with the same validators. -/
theorem of_data (same : after.validators.data = state.validators.data) : CapKept state after :=
  ⟨fun capped validator member => capped validator (same ▸ member)⟩

theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → CapKept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : CapKept state after :=
  foldlM_ok_invariant (CapKept state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

/-- Replacing a validator by one under the cap, when the state is. -/
theorem putValidator {index : Nat} {validator : Validator}
    (inside : index < state.validators.data.size)
    (good : EffectiveBalancesCapped state →
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator) :
    CapKept state (state.putValidator index inside validator) := by
  refine ⟨fun capped other member => ?_⟩
  simp only [BeaconState.putValidator, RootedForkList.data_set] at member
  rcases Array.mem_or_eq_of_mem_set member with old | rfl
  · exact capped other old
  · exact good capped

theorem setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after)
    (good : EffectiveBalancesCapped state →
      validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator) :
    CapKept state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  exact putValidator inside good

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : CapKept state after :=
  of_data (by rw [increaseBalance_validators computed])

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : CapKept state after :=
  of_data (by rw [decreaseBalance_validators computed])

end CapKept

/-- A validator of a state under the cap is under the cap. -/
theorem EffectiveBalancesCapped.get {index : ValidatorIndex} {validator : Validator}
    (capped : EffectiveBalancesCapped state) (found : getValidator state index = .ok validator) :
    validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator :=
  capped validator (mem_of_getValidator found)

/-- The largest effective balance depends only on the credentials. -/
theorem withdrawalMaxEffectiveBalance_congr {validator other : Validator}
    (same : other.withdrawalCredentials = validator.withdrawalCredentials) :
    withdrawalMaxEffectiveBalance preset fork other =
      withdrawalMaxEffectiveBalance preset fork validator := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance hasCompoundingWithdrawalCredential
  rw [same]

/-- A validator with the effective balance and the credentials of one under the cap. -/
theorem EffectiveBalancesCapped.keep {index : ValidatorIndex} {validator other : Validator}
    (capped : EffectiveBalancesCapped state) (found : getValidator state index = .ok validator)
    (balance : other.effectiveBalance = validator.effectiveBalance)
    (credentials : other.withdrawalCredentials = validator.withdrawalCredentials) :
    other.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork other := by
  rw [balance, withdrawalMaxEffectiveBalance_congr credentials]
  exact capped.get found

theorem EffectiveBalancesCapped.getElem? {position : Nat} {validator : Validator}
    (capped : EffectiveBalancesCapped state)
    (found : state.validators.data[position]? = some validator) :
    validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator :=
  capped validator (Array.mem_of_getElem? found)

theorem EffectiveBalancesCapped.keepElem? {position : Nat} {validator other : Validator}
    (capped : EffectiveBalancesCapped state)
    (found : state.validators.data[position]? = some validator)
    (balance : other.effectiveBalance = validator.effectiveBalance)
    (credentials : other.withdrawalCredentials = validator.withdrawalCredentials) :
    other.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork other := by
  rw [balance, withdrawalMaxEffectiveBalance_congr credentials]
  exact capped.getElem? found

/-! ## Mutators -/

theorem capKept_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    CapKept state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _
  · have same := (exitQueue_validators queue).1
    -- The exit sets two epochs, and keeps the effective balance and the credentials.
    exact (CapKept.of_data (by rw [same])).trans <|
      .setValidator set fun capped =>
        capped.keep ((getValidator_of_validators_eq same index).trans found) rfl rfl

theorem capKept_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    CapKept state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  -- The slashed validator keeps its effective balance and its credentials.
  exact (capKept_initiateValidatorExit exitedOk).trans <|
    ((CapKept.setValidator markedOk (fun capped => capped.keep found rfl rfl)).trans
      (by exact .of_data rfl)).trans <|
    (CapKept.decreaseBalance loweredOk).trans <|
    (CapKept.increaseBalance raisedOk).trans <|
    (CapKept.increaseBalance lastOk).trans
      (.of_data (by rw [(slashValidator_last done).1]))

/-! ## The steps of a block -/

theorem capKept_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : CapKept state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_data rfl

theorem capKept_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    CapKept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_data rfl

theorem capKept_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : CapKept state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_data (by rw [← rest])

theorem capKept_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    CapKept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact capKept_slashValidator slashed

theorem capKept_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    CapKept step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact capKept_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem capKept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    CapKept state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => CapKept state step.1)
    (fun _ _ _ before ok => before.trans (capKept_slashIfSlashable ok))
    (show CapKept state (state, false).1 from .refl state) folded

theorem capKept_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    CapKept state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : CapKept raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_data rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        CapKept state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_data rfl
    exact (flagged _ _).trans ((CapKept.increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact .of_data (by rw [← rest])

/-- A new validator has its deposit, rounded down to an increment, and at most its largest value.

It may replace a validator, from Gloas with `2^64` validators, but the new one is under the cap.
-/
theorem capKept_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    CapKept state after := by
  have fresh := getValidatorFromDeposit_capped (preset := preset) (fork := fork) (pubkey := pubkey)
    (withdrawalCredentials := withdrawalCredentials) (amount := amount)
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨validators, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
    have read := setOrAppendRooted_getElem? validatorsOk
    -- Each validator after it is the new one, or one that was there.
    refine ⟨fun capped validator member => ?_⟩
    obtain ⟨position, found⟩ := Array.getElem?_of_mem member
    rw [read] at found
    split at found
    · cases found
      exact fresh
    · exact capped.getElem? found
  · split at computed
    · cases computed
      refine ⟨fun capped validator member => ?_⟩
      simp only [RootedForkList.data_push, Array.mem_push] at member
      rcases member with old | rfl
      · exact capped validator old
      · exact fresh
    · cases computed

theorem capKept_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    CapKept state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact capKept_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · rw [liftAccessor_ok] at computed
    exact .increaseBalance computed

theorem capKept_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    CapKept state after := by
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
        exact (capKept_addValidatorToRegistry added).trans (.of_data rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_data rfl
  · exact capKept_applyPendingDeposit computed

theorem capKept_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    CapKept state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (CapKept.of_data (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (capKept_applyDeposit applied)

theorem capKept_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    CapKept state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact capKept_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem capKept_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    CapKept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_data rfl

theorem capKept_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    CapKept state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

theorem capKept_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    CapKept state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_data rfl

theorem capKept_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    CapKept state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (capKept_computeExitEpochAndUpdateChurn churned).trans (.of_data rfl)
  · cases computed
    exact .refl _

theorem capKept_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    CapKept state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact capKept_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact capKept_requestPartialWithdrawal computed

theorem capKept_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    CapKept state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_data rfl
  · cases computed
    exact .refl _

/-- A switch to compounding raises the largest effective balance of the validator. -/
theorem capKept_switchToCompoundingValidator (caps : EffectiveBalanceCaps preset)
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    CapKept state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  refine (CapKept.setValidator set fun capped => ?_).trans
    (capKept_queueExcessActiveBalance queued)
  have bound := capped.get found
  -- The new credentials compound, so the largest value becomes the largest of Electra.
  simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte, getMaxEffectiveBalance,
    hasCompoundingWithdrawalCredential, isCompoundingWithdrawalCredential] at bound ⊢
  simp only [Vector.getElem_set_self, beq_self_eq_true, ↓reduceIte]
  by_cases compounding :
      (validator.withdrawalCredentials[0] == COMPOUNDING_WITHDRAWAL_PREFIX[0]) = true
  · simp only [compounding, ↓reduceIte] at bound
    exact bound
  · simp only [compounding, Bool.false_eq_true, ↓reduceIte] at bound
    exact UInt64.le_trans bound caps.activation_le_electra

/-- The source of a consolidation gets an exit epoch, and keeps its effective balance. -/
theorem capKept_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourcePosition]? = some source)
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    CapKept state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, _, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have churnedKept := capKept_computeConsolidationEpochAndUpdateChurn churned
  have same : churnedState.validators.data = state.validators.data := by
    simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at churned
    obtain ⟨_, _, _, _, _, _, churned⟩ := churned
    cases churned
    rfl
  exact churnedKept.trans <|
    (CapKept.setValidator set
      (fun capped => capped.keepElem? (position := sourcePosition) (validator := source)
        (by rw [same]; exact found) rfl rfl)).trans (.of_data rfl)

theorem capKept_processConsolidationRequest (caps : EffectiveBalanceCaps preset)
    {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    CapKept state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact capKept_switchToCompoundingValidator caps (liftAccessor_ok.mp computed)
    | exact capKept_queueConsolidation (Array.getElem?_eq_getElem _) computed

theorem capKept_processExecutionRequests (caps : EffectiveBalanceCaps preset)
    {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    CapKept state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (CapKept.foldlM (fun _ _ _ ok => capKept_processDepositRequest ok)
      depositsOk).trans <|
    (CapKept.foldlM (fun _ _ _ ok => capKept_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    CapKept.foldlM (fun _ _ _ ok => capKept_processConsolidationRequest caps ok)
      consolidationsOk

/-! ## Withdrawals -/

theorem capKept_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : CapKept state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl
  · exact .decreaseBalance computed

theorem capKept_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    CapKept state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : CapKept state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact CapKept.foldlM (fun _ _ _ ok => capKept_applyWithdrawal ok) appliedOk
  have two : CapKept applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_data rfl
    · cases indexedOk
      exact .refl _
  have queued : ∀ kept : BeaconState preset fork,
      CapKept kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl
    · exact .refl _
  have partials : ∀ kept : BeaconState preset fork,
      CapKept kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl
    · exact .refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → CapKept kept finished := by
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
  have lastKept : CapKept finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact .of_data rfl
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

theorem capKept_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    CapKept state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact capKept_applyExpectedWithdrawals applied
    · cases computed
      exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact capKept_applyExpectedWithdrawals applied

/-- A change to an execution address keeps the largest effective balance of the validator. -/
theorem capKept_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    CapKept state after := by
  obtain ⟨validator, found, bls, _, _, set⟩ := processBlsToExecutionChange_ok computed
  refine .setValidator set fun capped => ?_
  have bound := capped.get found
  -- Neither the BLS prefix nor the execution address prefix compounds.
  have old : isCompoundingWithdrawalCredential validator.withdrawalCredentials = false := by
    simp [isCompoundingWithdrawalCredential, bls, BLS_WITHDRAWAL_PREFIX,
      COMPOUNDING_WITHDRAWAL_PREFIX]
  have new : isCompoundingWithdrawalCredential
      (executionCredentials signed.message.toExecutionAddress) = false := by
    simp [isCompoundingWithdrawalCredential, executionCredentials,
      ETH1_ADDRESS_WITHDRAWAL_PREFIX, COMPOUNDING_WITHDRAWAL_PREFIX]
  simp only [withdrawalMaxEffectiveBalance, getMaxEffectiveBalance,
    hasCompoundingWithdrawalCredential, old, new] at bound ⊢
  exact bound

/-! ## The parent payload and the execution part of a block -/

theorem capKept_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    CapKept state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_data rfl

theorem capKept_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    CapKept state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .of_data rfl)

theorem capKept_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    CapKept state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl

theorem capKept_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : CapKept state after := by
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

theorem capKept_processParentExecutionPayload (caps : EffectiveBalanceCaps preset)
    {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    CapKept state after := by
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
  exact (capKept_settleParentPayment settledOk).trans <|
    (CapKept.foldlM (fun _ _ _ ok => capKept_processDepositRequest ok)
      depositsOk).trans <|
    (CapKept.foldlM (fun _ _ _ ok => capKept_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    (CapKept.foldlM (fun _ _ _ ok => capKept_processConsolidationRequest caps ok)
      consolidationsOk).trans <|
    (CapKept.foldlM
      (fun _ _ _ ok => capKept_processBuilderDepositRequest ok) buildersOk).trans <|
    (CapKept.foldlM (fun _ _ _ ok => capKept_processBuilderExitRequest ok)
      exitsOk).trans (.of_data rfl)

theorem capKept_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    CapKept state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_data rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_data rfl

theorem capKept_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    CapKept state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (capKept_processWithdrawals withdrawnOk).trans
      (capKept_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (capKept_processWithdrawals withdrawnOk).trans
      (capKept_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact capKept_processExecutionPayload computed
    · cases computed
      exact .refl _

/-! ## The sync aggregate -/

theorem capKept_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    CapKept state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine CapKept.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (CapKept.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

/-! ## Blocks -/

theorem capKept_processOperations (caps : EffectiveBalanceCaps preset)
    {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    CapKept state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (CapKept.foldlM (fun _ _ _ ok => capKept_processProposerSlashing ok)
        proposersOk).trans <|
      (CapKept.foldlM (fun _ _ _ ok => capKept_processAttesterSlashing ok)
        attestersOk).trans <|
      (CapKept.foldlM (fun _ _ _ ok => capKept_processAttestation ok)
        attestedOk).trans <|
      (CapKept.foldlM (fun _ _ _ ok => capKept_processVoluntaryExit ok)
        exitsOk).trans <|
      (CapKept.foldlM
        (fun _ _ _ ok => capKept_processBlsToExecutionChange ok) changesOk).trans <|
      CapKept.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : CapKept exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact CapKept.foldlM
        (fun _ _ _ ok => capKept_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : CapKept changed after := by
    split at requestsOk
    · exact capKept_processExecutionRequests caps requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  exact (CapKept.foldlM (fun _ _ _ ok => capKept_processProposerSlashing ok)
      proposersOk).trans <|
    (CapKept.foldlM (fun _ _ _ ok => capKept_processAttesterSlashing ok)
      attestersOk).trans <|
    (CapKept.foldlM (fun _ _ _ ok => capKept_processAttestation ok)
      attestedOk).trans <|
    (CapKept.foldlM (fun _ _ _ ok => capKept_processDeposit ok)
      depositedOk).trans <|
    (CapKept.foldlM (fun _ _ _ ok => capKept_processVoluntaryExit ok)
      exitsOk).trans <|
    changes.trans requests

theorem capKept_processBlock (caps : EffectiveBalanceCaps preset)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    CapKept state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidKept : CapKept state paid := by
      split at paidOk
      · exact capKept_processParentExecutionPayload caps paidOk
      · cases paidOk
        exact .refl _
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedKept : CapKept headed executed := by
      split at executedOk
      · exact capKept_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    -- Heze drops the vote on the deposit contract.
    have votedKept : CapKept revealed voted := by
      split at votedOk
      · exact capKept_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    exact paidKept.trans <| (capKept_processBlockHeader headedOk).trans <|
      executedKept.trans <| (capKept_processRandao revealedOk).trans <|
      votedKept.trans <| (capKept_processOperations caps operatedOk).trans
        (capKept_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (capKept_processBlockHeader headerOk).trans <|
    (capKept_processRandao randaoOk).trans <|
    (capKept_processEth1Data eth1Ok).trans
      (capKept_processOperations caps operationsOk)

/-! ## The steps of an epoch -/

theorem capKept_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    CapKept state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_data (by rw [← rest])

theorem capKept_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : CapKept state after :=
  CapKept.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (CapKept.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem capKept_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    CapKept state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact CapKept.foldlM (fun _ _ _ ok => capKept_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact capKept_applyAllDeltas applied

/-- Joining the activation queue changes only the eligibility epoch. -/
theorem queueForActivation_capped {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued)
    (bound : validator.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork validator) :
    queued.effectiveBalance ≤ withdrawalMaxEffectiveBalance preset fork queued := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact bound
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ bound

theorem capKept_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    CapKept state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set := CapKept.setValidator markedOk
    (fun capped => by
      have queuedBound := queueForActivation_capped queuedOk (capped.get found)
      exact queuedBound)
  split at computed
  · exact set.trans (capKept_initiateValidatorExit (liftAccessor_ok.mp computed))
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

/-- Activating a validator changes only its activation epoch. -/
theorem capKept_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : CapKept state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨old, oldFound, _, _, set⟩ := computed
  exact .setValidator set (fun capped => capped.keep oldFound rfl rfl)

theorem capKept_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    CapKept state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine CapKept.foldlM (fun state _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact .setValidator set (fun capped => capped.keep found rfl rfl)
    split at ok
    · exact capKept_initiateValidatorExit (liftAccessor_ok.mp ok)
    split at ok
    · rw [liftAccessor_ok] at ok
      exact .setValidator ok (fun capped => capped.keep found rfl rfl)
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  exact (CapKept.foldlM (fun _ _ _ ok => capKept_updateRegistryEntry ok) updatedOk).trans
    (CapKept.foldlM (fun _ _ _ ok => capKept_activateValidator ok) activated)

theorem capKept_processSlashings (computed : processSlashings state = .ok after) :
    CapKept state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine CapKept.foldlM (fun _ _ _ ok => ?_) applied
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
  · refine CapKept.foldlM (fun _ _ _ ok => ?_) computed
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

theorem capKept_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    CapKept state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_data rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- An updated effective balance is at most the largest, if the old one is. -/
theorem updatedEffectiveBalance_le {largest balance effectiveBalance result : Gwei}
    (old : effectiveBalance ≤ largest)
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result ≤ largest := by
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact old
  · exact uint64_min_le_right _ _

/-- The update of an effective balance raises it only up to the balance.

The hysteresis moves it only when the balance leaves a band around it.

It then becomes the balance rounded down to an increment, so it never exceeds the balance. -/
theorem updatedEffectiveBalance_le_max {largest balance effectiveBalance result : Gwei}
    (computed : updatedEffectiveBalance preset largest balance effectiveBalance = .ok result) :
    result.toNat ≤ max effectiveBalance.toNat balance.toNat := by
  rcases updatedEffectiveBalance_cases computed with rfl | rfl
  · exact Nat.le_max_left _ _
  · refine Nat.le_trans ?_ (Nat.le_max_right _ _)
    rw [UInt64.min_def]
    split
    · rw [UInt64.toNat_sub_of_le _ _ (uint64_mod_le _ _)]
      exact Nat.sub_le _ _
    · rename_i above
      rw [UInt64.not_le] at above
      have below := UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt above)
      rw [UInt64.toNat_sub_of_le _ _ (uint64_mod_le _ _)] at below
      exact Nat.le_trans below (Nat.sub_le _ _)

/-- A new validator from a deposit has an effective balance of at most the deposit. -/
theorem getValidatorFromDeposit_le_amount {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} :
    (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount).effectiveBalance.toNat
      ≤ amount.toNat := by
  simp only [getValidatorFromDeposit]
  rw [UInt64.min_def]
  split
  · rw [UInt64.toNat_sub_of_le _ _ (uint64_mod_le _ _)]
    exact Nat.sub_le _ _
  · rename_i above
    rw [UInt64.not_le] at above
    have below := UInt64.le_iff_toNat_le.mp (UInt64.le_of_lt above)
    rw [UInt64.toNat_sub_of_le _ _ (uint64_mod_le _ _)] at below
    exact Nat.le_trans below (Nat.sub_le _ _)

/-- The update of the effective balances caps each one at its largest value. -/
theorem capKept_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    CapKept state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine CapKept.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, _, _, _, updated, set⟩ := ok
  refine .setValidator set fun capped => ?_
  have bound := updatedEffectiveBalance_le (capped.get found) updated
  rw [withdrawalMaxEffectiveBalance_congr rfl]
  exact bound

theorem capKept_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    CapKept state after := by
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

theorem capKept_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    CapKept state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_data rfl

/-! ## The steps of an epoch from Altair -/

theorem capKept_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    CapKept state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_data rfl

theorem capKept_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      CapKept state pass.1.state
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
      exact (capKept_applyPendingDeposit credited).trans
        (capKept_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact capKept_passPendingDeposits (deposits := rest) ‹_›
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
    exact (capKept_applyPendingDeposit credited).trans
      (capKept_passPendingDeposits (deposits := rest) ‹_›)

theorem capKept_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    CapKept state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (capKept_passPendingDeposits ‹_›).trans (.of_data rfl)

theorem capKept_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      CapKept state result.1
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
      exact capKept_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (CapKept.decreaseBalance loweredOk).trans <|
      (CapKept.increaseBalance raisedOk).trans
        (capKept_passPendingConsolidations (result := (passed, read)) passedOk)

theorem capKept_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    CapKept state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine (capKept_processPendingDeposits deposited).trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (capKept_passPendingConsolidations ‹_›).trans (.of_data rfl)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- The steps that close an epoch from Altair, after the history. -/
private theorem capKept_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : CapKept rooted after := by
  have syncedKept : CapKept rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact .of_data rfl
  have lookedKept : CapKept synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedKept : CapKept looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedKept.trans (lookedKept.trans windowedKept)

theorem capKept_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    CapKept state after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetKept : CapKept slashed reset := by
    split at resetOk
    · exact capKept_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ .refl _
  have paidKept : CapKept pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ .refl _
  have clearedKept : CapKept balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_data rfl
  have mixedKept : CapKept cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_data rfl
  have head : CapKept state mixed :=
    (capKept_processJustificationAndFinalization justifiedOk).trans <|
    (capKept_processInactivityUpdates scoredOk).trans <|
    (capKept_processRewardsAndPenalties rewardedOk).trans <|
    (capKept_processRegistryUpdates registeredOk).trans <|
    (capKept_processSlashings slashedOk).trans <|
    resetKept.trans <|
    (capKept_processPendingBalances pendingOk).trans <|
    paidKept.trans <|
    (capKept_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans mixedKept
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · have rootedKept : CapKept mixed rooted := by
      unfold processHistoricalSummariesUpdate at rootedOk
      simp only [bind, Except.bind, pure, Except.pure] at rootedOk
      repeat' (split at rootedOk <;> try cases rootedOk)
      all_goals first
        | exact .refl _
        | exact .of_data rfl
    exact head.trans <| rootedKept.trans (capKept_epochEnd syncedOk lookedOk windowed)
  · exact head.trans <| (capKept_processHistoricalRootsUpdate rootedOk).trans
      (capKept_epochEnd syncedOk lookedOk windowed)

theorem capKept_processEpoch
    (computed : processEpoch config checks state = .ok after) : CapKept state after := by
  unfold processEpoch at computed
  split at computed
  · exact capKept_processEpochAltair computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have clearedKept : CapKept balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_data rfl
  have mixedKept : CapKept cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_data rfl
  exact (capKept_processJustificationAndFinalization justifiedOk).trans <|
    (capKept_processRewardsAndPenalties rewardedOk).trans <|
    (capKept_processRegistryUpdates registeredOk).trans <|
    (capKept_processSlashings slashedOk).trans <|
    (capKept_processEth1DataReset resetOk).trans <|
    (capKept_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans <| mixedKept.trans <|
    (capKept_processHistoricalRootsUpdate rootedOk).trans
      (capKept_processParticipationRecordUpdates rotated)

/-! ## Slots, upgrades and chains -/

theorem capKept_advanceSlot (computed : advanceSlot config checks state = .ok after) :
    CapKept state after := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedKept : CapKept state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact .of_data rfl
  have epochedKept : CapKept cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact capKept_processEpoch epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ .refl _
  exact cachedKept.trans (epochedKept.trans (.of_data rfl))

/-- Queueing a validator that is not yet active sets its effective balance to zero. -/
theorem capKept_queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) : CapKept state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact CapKept.trans (by exact .of_data rfl)
    ((CapKept.setValidator set₂ fun _ => UInt64.zero_le).trans (.of_data rfl))

/-- The largest effective balance of a validator never falls at a later fork. -/
theorem withdrawalMaxEffectiveBalance_mono (caps : EffectiveBalanceCaps preset)
    {earlier later : Base.Fork} (le : earlier ≤ later) (validator : Validator) :
    withdrawalMaxEffectiveBalance preset earlier validator ≤
      withdrawalMaxEffectiveBalance preset later validator := by
  unfold withdrawalMaxEffectiveBalance getMaxEffectiveBalance
  by_cases laterElectra : Base.Fork.pectra ≤ later
  · by_cases earlierElectra : Base.Fork.pectra ≤ earlier
    · simp only [earlierElectra, laterElectra, ↓reduceIte]
      exact UInt64.le_refl _
    · -- Before Electra the largest is `MAX_EFFECTIVE_BALANCE`, at most either largest of Electra.
      simp only [earlierElectra, laterElectra, ↓reduceIte]
      split
      · exact UInt64.le_trans caps.max_le_activation caps.activation_le_electra
      · exact caps.max_le_activation
  · have earlierBefore : ¬Base.Fork.pectra ≤ earlier := fun earlierElectra =>
      laterElectra (Nat.le_trans earlierElectra le)
    simp only [earlierBefore, laterElectra, ↓reduceIte]
    exact UInt64.le_refl _

/-- A state of a later fork with the same validators keeps the cap. -/
theorem effectiveBalancesCapped_of_data (caps : EffectiveBalanceCaps preset)
    {later : Base.Fork} {after : BeaconState preset later} (le : fork ≤ later)
    (same : after.validators.data = state.validators.data)
    (capped : EffectiveBalancesCapped state) : EffectiveBalancesCapped after :=
  fun validator member => UInt64.le_trans (capped validator (same ▸ member))
    (withdrawalMaxEffectiveBalance_mono caps le validator)

theorem effectiveBalancesCapped_upgradeNext (caps : EffectiveBalanceCaps preset)
    {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post)
    (capped : EffectiveBalancesCapped pre.state) : EffectiveBalancesCapped post.val.state := by
  have le : pre.fork ≤ post.val.fork := Nat.le_of_lt post.property
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact effectiveBalancesCapped_of_data caps le (upgradeToAltair_spec upgraded).1 capped
  · subst computed
    exact effectiveBalancesCapped_of_data caps le rfl capped
  · subst computed
    exact effectiveBalancesCapped_of_data caps le rfl capped
  · subst computed
    exact effectiveBalancesCapped_of_data caps le rfl capped
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, _, queued, compounded⟩ := upgraded
    have compoundedKept := CapKept.foldlM (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · exact capKept_queueExcessActiveBalance (liftAccessor_ok.mp ok)
        · cases ok
          exact .refl _
      · cases ok
        exact .refl _) compounded
    have queuedKept := CapKept.foldlM (fun _ _ _ ok => capKept_queuePreActivation ok) queued
    exact (queuedKept.trans compoundedKept).kept
      (effectiveBalancesCapped_of_data caps le rfl capped)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact effectiveBalancesCapped_of_data caps le (upgradeToFulu_spec upgraded).1 capped
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact effectiveBalancesCapped_of_data caps le (upgradeToGloas_spec upgraded).1 capped
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact effectiveBalancesCapped_of_data caps le (upgradeHezeFields_lists _).1 capped

/-- Every step of a chain keeps the cap on effective balances. -/
theorem stepRelation_effectiveBalancesCapped (caps : EffectiveBalanceCaps preset) :
    StepRelation config checks fun (forked after : ForkedBeaconState preset) =>
      EffectiveBalancesCapped forked.state → EffectiveBalancesCapped after.state :=
  StepRelation.ofPreserves (holds := fun forked => EffectiveBalancesCapped forked.state)
    (fun capped computed => (capKept_advanceSlot computed).kept capped)
    (fun capped _ computed => effectiveBalancesCapped_upgradeNext caps computed capped)
    (fun capped computed =>
      (capKept_processBlock caps (applySignedBlock_ok computed).2.1).kept capped)

/-! ## Genesis -/

/-- Each validator at genesis has its balance, rounded down and capped. -/
theorem capKept_activateAtGenesis (before : fork < .pectra) {index : Nat}
    (computed : activateAtGenesis state index = .ok after) : CapKept state after := by
  simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, set⟩ := computed
  refine .setValidator set fun _ => ?_
  -- Before Electra the largest effective balance is `MAX_EFFECTIVE_BALANCE`.
  have notElectra : ¬Base.Fork.pectra ≤ fork := Nat.not_le_of_lt before
  split <;>
    simp only [withdrawalMaxEffectiveBalance, notElectra, ↓reduceIte] <;>
    exact uint64_min_le_right _ _

/-- A candidate genesis state is under the cap. -/
theorem initializeBeaconStateFromEth1_capped {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    EffectiveBalancesCapped after := by
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  rename_i altair
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, rfl⟩ :=
    computed
  have before : fork < .pectra := Nat.lt_trans (Nat.lt_of_not_le altair) (by decide)
  have beforeHeze : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le altair) (by decide)
  have kept := (CapKept.foldlM (fun state _ _ ok => by
      simp only [genesisDeposit, bind_ok_iff] at ok
      obtain ⟨depositRoot, _, deposited⟩ := ok
      exact (CapKept.of_data (state := state) (after := { state with
        eth1Data := fun _ => { state.eth1Data beforeHeze with depositRoot } }) rfl).trans
        (capKept_processDeposit deposited)) depositedOk).trans
    (CapKept.foldlM (fun _ _ _ ok => capKept_activateAtGenesis before ok) activatedOk)
  have rooted : CapKept activated { activated with genesisValidatorsRoot := root } :=
    .of_data rfl
  -- The empty state has no validator.
  exact (kept.trans rooted).kept fun _ member => by simp [emptyGenesisState] at member

/-! ## Reachable states -/

/-- In every state that a chain from genesis reaches, each effective balance is at most its cap.

The preset must order its largest effective balances as `EffectiveBalanceCaps` says. -/
theorem Reachable.effectiveBalancesCapped (caps : EffectiveBalanceCaps preset)
    {forked : ForkedBeaconState preset} (reachable : Reachable config checks forked) :
    EffectiveBalancesCapped forked.state :=
  Reachable.of_preserves (stepRelation_effectiveBalancesCapped caps)
    (fun _ launched =>
      have ⟨⟨_, _, _, initialized⟩, _⟩ := launched
      initializeBeaconStateFromEth1_capped initialized)
    reachable

/-- Before Electra every effective balance is at most `MAX_EFFECTIVE_BALANCE`. -/
theorem EffectiveBalancesCapped.le_max (capped : EffectiveBalancesCapped state)
    (before : fork < .pectra) {validator : Validator} (member : validator ∈ state.validators.data) :
    validator.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE := by
  have bound := capped validator member
  have notElectra : ¬Base.Fork.pectra ≤ fork := Nat.not_le_of_lt before
  simp only [withdrawalMaxEffectiveBalance, notElectra, ↓reduceIte] at bound
  exact bound

/-- From Electra every effective balance is at most `MAX_EFFECTIVE_BALANCE_ELECTRA`. -/
theorem EffectiveBalancesCapped.le_max_electra (caps : EffectiveBalanceCaps preset)
    (capped : EffectiveBalancesCapped state) (electra : .pectra ≤ fork) {validator : Validator}
    (member : validator ∈ state.validators.data) :
    validator.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE_ELECTRA := by
  have bound := capped validator member
  simp only [withdrawalMaxEffectiveBalance, electra, ↓reduceIte, getMaxEffectiveBalance] at bound
  split at bound
  · exact bound
  · exact UInt64.le_trans bound caps.activation_le_electra

/-- An effective balance grows by at most the gap to its cap.

Take any reference, such as the effective balance of the same validator at an earlier state.

A later effective balance exceeds it by at most the cap minus the reference. -/
theorem EffectiveBalancesCapped.growth_le (capped : EffectiveBalancesCapped state)
    {validator : Validator} (member : validator ∈ state.validators.data) (reference : Gwei) :
    validator.effectiveBalance.toNat - reference.toNat ≤
      (withdrawalMaxEffectiveBalance preset fork validator).toNat - reference.toNat := by
  have bound := UInt64.le_iff_toNat_le.mp (capped validator member)
  omega

/-- In a reachable state, an effective balance exceeds any reference by at most the gap to its cap.

The reference may be the effective balance of the same validator at an earlier state.

The gap is to its cap in the later state, which from Electra depends on its credentials then. -/
theorem Reachable.effectiveBalance_growth_le (caps : EffectiveBalanceCaps preset)
    {forked : ForkedBeaconState preset} (reachable : Reachable config checks forked)
    {validator : Validator} (member : validator ∈ forked.state.validators.data)
    (reference : Gwei) :
    validator.effectiveBalance.toNat - reference.toNat ≤
      (withdrawalMaxEffectiveBalance preset forked.fork validator).toNat - reference.toNat :=
  (Reachable.effectiveBalancesCapped caps reachable).growth_le member reference

end EthLib.Consensus
