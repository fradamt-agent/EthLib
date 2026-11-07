module

public import EthLib.Consensus.Proofs.Transition.Lifecycle

/-!
# Proofs: the growth of inactivity scores, at every fork

From Altair each validator has an inactivity score.

Its inactivity penalty in an epoch is its effective balance times its score, over a fixed quotient.

So a bound on the score bounds the penalty.

The score changes in one place: `processInactivityUpdates`, once per epoch.

There it grows by at most `INACTIVITY_SCORE_BIAS`.

A new validator starts at zero, and an upgrade carries the scores or starts them at zero.

So along a chain each score grows by at most `INACTIVITY_SCORE_BIAS` per epoch that passes.

Before Altair there are no scores, and the score of a validator here reads as zero.

The update runs over the eligible validators.

Each comes at most once while the registry is below `2^64`.

From Gloas the bound needs that condition, as in `Lifecycle`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- The inactivity score at a position of the registry, as a natural number.

It is zero before Altair and past the end of the scores. -/
def inactivityScoreAt (state : BeaconState preset fork) (position : Nat) : Nat :=
  if altair : .altair ≤ fork then
    (((state.inactivityScores altair).data[position]?).map UInt64.toNat).getD 0
  else 0

/-- A step that raises no inactivity score. -/
structure ScoresKept (state after : BeaconState preset fork) : Prop where
  le : ∀ position, inactivityScoreAt after position ≤ inactivityScoreAt state position

namespace ScoresKept

theorem refl (state : BeaconState preset fork) : ScoresKept state state :=
  ⟨fun _ => Nat.le_refl _⟩

theorem trans {first second third : BeaconState preset fork} (one : ScoresKept first second)
    (two : ScoresKept second third) : ScoresKept first third :=
  ⟨fun position => Nat.le_trans (two.le position) (one.le position)⟩

/-- A state with the same scores. -/
theorem of_scores (same : after.inactivityScores = state.inactivityScores) :
    ScoresKept state after :=
  ⟨fun position => by simp [inactivityScoreAt, same]⟩

theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → ScoresKept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : ScoresKept state after :=
  foldlM_ok_invariant (ScoresKept state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

theorem setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : ScoresKept state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact of_scores rfl

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : ScoresKept state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact of_scores rfl

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : ScoresKept state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact of_scores rfl

end ScoresKept

/-! ## Mutators -/

/-- The exit queue keeps the scores. -/
theorem exitQueue_scores {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    after.inactivityScores = state.inactivityScores := by
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
      Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    rfl

theorem scoresKept_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    ScoresKept state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _
  · exact (ScoresKept.of_scores (exitQueue_scores queue)).trans (.setValidator set)

theorem scoresKept_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    ScoresKept state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  exact (scoresKept_initiateValidatorExit exitedOk).trans <|
    ((ScoresKept.setValidator markedOk).trans
      (by exact .of_scores rfl)).trans <|
    (ScoresKept.decreaseBalance loweredOk).trans <|
    (ScoresKept.increaseBalance raisedOk).trans <|
    (ScoresKept.increaseBalance lastOk).trans (by
      simp only [pure, Except.pure, Except.ok.injEq] at done
      subst done
      split <;> exact .of_scores rfl)

/-! ## The steps of a block -/

theorem scoresKept_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : ScoresKept state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_scores rfl

theorem scoresKept_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    ScoresKept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_scores rfl

theorem scoresKept_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : ScoresKept state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_scores (by rw [← rest])

theorem scoresKept_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    ScoresKept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact scoresKept_slashValidator slashed

theorem scoresKept_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    ScoresKept step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact scoresKept_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem scoresKept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    ScoresKept state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => ScoresKept state step.1)
    (fun _ _ _ before ok => before.trans (scoresKept_slashIfSlashable ok))
    (show ScoresKept state (state, false).1 from .refl state) folded

theorem scoresKept_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ScoresKept state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : ScoresKept raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_scores rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        ScoresKept state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_scores rfl
    exact (flagged _ _).trans ((ScoresKept.increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact .of_scores (by rw [← rest])

/-- A new validator starts with a score of zero.

It may replace a validator, from Gloas with `2^64` validators, whose score it then lowers. -/
theorem scoresKept_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    ScoresKept state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · rename_i altair
    unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, scores, scoresOk, rfl⟩ := computed
    have read := setOrAppendList_getElem? scoresOk
    refine ⟨fun position => ?_⟩
    simp only [inactivityScoreAt, altair, ↓reduceDIte]
    rw [read]
    split
    · simp
    · exact Nat.le_refl _
  · split at computed
    · cases computed
      exact .of_scores rfl
    · cases computed

theorem scoresKept_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    ScoresKept state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact scoresKept_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · rw [liftAccessor_ok] at computed
    exact .increaseBalance computed

theorem scoresKept_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    ScoresKept state after := by
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
        exact (scoresKept_addValidatorToRegistry added).trans (.of_scores rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_scores rfl
  · exact scoresKept_applyPendingDeposit computed

theorem scoresKept_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    ScoresKept state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (ScoresKept.of_scores (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (scoresKept_applyDeposit applied)

theorem scoresKept_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    ScoresKept state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact scoresKept_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem scoresKept_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    ScoresKept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_scores rfl

theorem scoresKept_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    ScoresKept state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_scores rfl

theorem scoresKept_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    ScoresKept state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_scores rfl

theorem scoresKept_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    ScoresKept state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (scoresKept_computeExitEpochAndUpdateChurn churned).trans (.of_scores rfl)
  · cases computed
    exact .refl _

theorem scoresKept_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    ScoresKept state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact scoresKept_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact scoresKept_requestPartialWithdrawal computed

theorem scoresKept_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    ScoresKept state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_scores rfl
  · cases computed
    exact .refl _

/-- A switch to compounding changes only the credentials and the balances. -/
theorem scoresKept_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    ScoresKept state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  exact (ScoresKept.setValidator set).trans (scoresKept_queueExcessActiveBalance queued)

/-- The source of a consolidation gets an exit epoch. -/
theorem scoresKept_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    ScoresKept state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, _, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  have churnedKept := scoresKept_computeConsolidationEpochAndUpdateChurn churned
  exact churnedKept.trans <| (ScoresKept.setValidator set).trans (.of_scores rfl)

theorem scoresKept_processConsolidationRequest
    {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    ScoresKept state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact scoresKept_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact scoresKept_queueConsolidation computed

theorem scoresKept_processExecutionRequests
    {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    ScoresKept state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processDepositRequest ok)
      depositsOk).trans <|
    (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processConsolidationRequest ok)
      consolidationsOk

/-! ## Withdrawals -/

theorem scoresKept_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : ScoresKept state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_scores rfl
  · exact .decreaseBalance computed

theorem scoresKept_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    ScoresKept state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : ScoresKept state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact ScoresKept.foldlM (fun _ _ _ ok => scoresKept_applyWithdrawal ok) appliedOk
  have two : ScoresKept applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_scores rfl
    · cases indexedOk
      exact .refl _
  have queued : ∀ kept : BeaconState preset fork,
      ScoresKept kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_scores rfl
    · exact .refl _
  have partials : ∀ kept : BeaconState preset fork,
      ScoresKept kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_scores rfl
    · exact .refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → ScoresKept kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact .of_scores rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact .of_scores rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  have lastKept : ScoresKept finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact .of_scores rfl
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

theorem scoresKept_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    ScoresKept state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact scoresKept_applyExpectedWithdrawals applied
    · cases computed
      exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact scoresKept_applyExpectedWithdrawals applied

/-- A change to an execution address changes only the credentials. -/
theorem scoresKept_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    ScoresKept state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact .setValidator set

/-! ## The parent payload and the execution part of a block -/

theorem scoresKept_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    ScoresKept state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_scores rfl

theorem scoresKept_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    ScoresKept state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .of_scores rfl)

theorem scoresKept_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    ScoresKept state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_scores rfl

theorem scoresKept_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : ScoresKept state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact .of_scores rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;> exact .of_scores rfl

theorem scoresKept_processParentExecutionPayload
    {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    ScoresKept state after := by
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
  exact (scoresKept_settleParentPayment settledOk).trans <|
    (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processDepositRequest ok)
      depositsOk).trans <|
    (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processConsolidationRequest ok)
      consolidationsOk).trans <|
    (ScoresKept.foldlM
      (fun _ _ _ ok => scoresKept_processBuilderDepositRequest ok) buildersOk).trans <|
    (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processBuilderExitRequest ok)
      exitsOk).trans (.of_scores rfl)

theorem scoresKept_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    ScoresKept state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_scores rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_scores rfl

theorem scoresKept_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    ScoresKept state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (scoresKept_processWithdrawals withdrawnOk).trans
      (scoresKept_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (scoresKept_processWithdrawals withdrawnOk).trans
      (scoresKept_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact scoresKept_processExecutionPayload computed
    · cases computed
      exact .refl _

/-! ## The sync aggregate -/

theorem scoresKept_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    ScoresKept state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine ScoresKept.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (ScoresKept.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

/-! ## Blocks -/

theorem scoresKept_processOperations
    {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ScoresKept state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processProposerSlashing ok)
        proposersOk).trans <|
      (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processAttesterSlashing ok)
        attestersOk).trans <|
      (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processAttestation ok)
        attestedOk).trans <|
      (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processVoluntaryExit ok)
        exitsOk).trans <|
      (ScoresKept.foldlM
        (fun _ _ _ ok => scoresKept_processBlsToExecutionChange ok) changesOk).trans <|
      ScoresKept.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : ScoresKept exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact ScoresKept.foldlM
        (fun _ _ _ ok => scoresKept_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : ScoresKept changed after := by
    split at requestsOk
    · exact scoresKept_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  exact (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processProposerSlashing ok)
      proposersOk).trans <|
    (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processAttesterSlashing ok)
      attestersOk).trans <|
    (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processAttestation ok)
      attestedOk).trans <|
    (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processDeposit ok)
      depositedOk).trans <|
    (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_processVoluntaryExit ok)
      exitsOk).trans <|
    changes.trans requests

theorem scoresKept_processBlock
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ScoresKept state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidKept : ScoresKept state paid := by
      split at paidOk
      · exact scoresKept_processParentExecutionPayload paidOk
      · cases paidOk
        exact .refl _
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedKept : ScoresKept headed executed := by
      split at executedOk
      · exact scoresKept_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    -- Heze drops the vote on the deposit contract.
    have votedKept : ScoresKept revealed voted := by
      split at votedOk
      · exact scoresKept_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    exact paidKept.trans <| (scoresKept_processBlockHeader headedOk).trans <|
      executedKept.trans <| (scoresKept_processRandao revealedOk).trans <|
      votedKept.trans <| (scoresKept_processOperations operatedOk).trans
        (scoresKept_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (scoresKept_processBlockHeader headerOk).trans <|
    (scoresKept_processRandao randaoOk).trans <|
    (scoresKept_processEth1Data eth1Ok).trans
      (scoresKept_processOperations operationsOk)

/-! ## The steps of an epoch -/

theorem scoresKept_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    ScoresKept state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_scores (by rw [← rest])

theorem scoresKept_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : ScoresKept state after :=
  ScoresKept.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (ScoresKept.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem scoresKept_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    ScoresKept state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact ScoresKept.foldlM (fun _ _ _ ok => scoresKept_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact scoresKept_applyAllDeltas applied

theorem scoresKept_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    ScoresKept state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set := ScoresKept.setValidator markedOk
  split at computed
  · exact set.trans (scoresKept_initiateValidatorExit (liftAccessor_ok.mp computed))
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

/-- Activating a validator changes only its activation epoch. -/
theorem scoresKept_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : ScoresKept state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨old, oldFound, _, _, set⟩ := computed
  exact .setValidator set

theorem scoresKept_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    ScoresKept state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine ScoresKept.foldlM (fun state _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨validator, found, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact .setValidator set
    split at ok
    · exact scoresKept_initiateValidatorExit (liftAccessor_ok.mp ok)
    split at ok
    · rw [liftAccessor_ok] at ok
      exact .setValidator ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  exact (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_updateRegistryEntry ok) updatedOk).trans
    (ScoresKept.foldlM (fun _ _ _ ok => scoresKept_activateValidator ok) activated)

theorem scoresKept_processSlashings (computed : processSlashings state = .ok after) :
    ScoresKept state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine ScoresKept.foldlM (fun _ _ _ ok => ?_) applied
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
  · refine ScoresKept.foldlM (fun _ _ _ ok => ?_) computed
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

theorem scoresKept_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    ScoresKept state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_scores rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- The update of the effective balances changes only the validators. -/
theorem scoresKept_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    ScoresKept state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine ScoresKept.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, set⟩ := ok
  exact .setValidator set

theorem scoresKept_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    ScoresKept state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_scores rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem scoresKept_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    ScoresKept state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_scores rfl

/-! ## The steps of an epoch from Altair -/

/-- An updated score is at most the old one plus the score bias. -/
theorem nextInactivityScore_le {hit : Bool} {leaking : Except TransitionError Bool}
    {score next : UInt64}
    (computed : nextInactivityScore config hit leaking score = .ok next) :
    next.toNat ≤ score.toNat + config.INACTIVITY_SCORE_BIAS.toNat := by
  -- The first change lowers the score by one, or raises it by the bias.
  --
  -- Outside a leak the score then falls by the recovery rate.
  cases hit
  · simp only [nextInactivityScore, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, liftAccessor_ok,
      liftArith, mapError_ok_iff, addChecked_ok_iff, pure, Except.pure] at computed
    obtain ⟨changed, ⟨_, changedNat⟩, leak, _, done⟩ := computed
    cases done
    split
    · omega
    · rw [toNat_saturatingSub]
      omega
  · simp only [nextInactivityScore, ↓reduceIte, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨changed, rfl, leak, _, done⟩ := computed
    cases done
    split
    · rw [toNat_saturatingSub]
      omega
    · rw [toNat_saturatingSub, toNat_saturatingSub]
      omega

/-- The score at a position of a list of scores, as a natural number. -/
private def scoreOf (scores : InactivityScores preset fork) (position : Nat) : Nat :=
  ((scores.data[position]?).map UInt64.toNat).getD 0

/-- One update raises only the score at its index, by at most the score bias. -/
private theorem updateInactivityScore_le {hit : Except TransitionError (Array Bool)}
    {leaking : Except TransitionError Bool} {scores next : InactivityScores preset fork}
    {index : ValidatorIndex}
    (computed : updateInactivityScore config hit leaking scores index = .ok next)
    (position : Nat) :
    scoreOf next position ≤ scoreOf scores position +
      if position = index.toNat then config.INACTIVITY_SCORE_BIAS.toNat else 0 := by
  unfold updateInactivityScore at computed
  obtain ⟨_, _, computed⟩ := bind_ok_iff.mp computed
  split at computed
  · rename_i inside
    obtain ⟨score, scoreOk, computed⟩ := bind_ok_iff.mp computed
    simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    have grown := nextInactivityScore_le scoreOk
    simp only [scoreOf, Array.getElem?_set]
    by_cases same : index.toNat = position
    · subst same
      simp [Array.getElem?_eq_getElem inside, grown]
    · simp [same, Ne.symm same]
  · cases computed

/-- Updates at distinct indices raise each score by at most the score bias. -/
private theorem foldlM_updateInactivityScore_le {hit : Except TransitionError (Array Bool)}
    {leaking : Except TransitionError Bool} :
    ∀ {indices : List ValidatorIndex} {scores next : InactivityScores preset fork},
      indices.Nodup →
      indices.foldlM (updateInactivityScore config hit leaking) scores = .ok next →
      ∀ position, scoreOf next position ≤ scoreOf scores position +
        if position ∈ indices.map UInt64.toNat then config.INACTIVITY_SCORE_BIAS.toNat else 0
  | [], scores, next, _, computed, position => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | index :: rest, scores, next, unique, computed, position => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    have one := updateInactivityScore_le first position
    have two := foldlM_updateInactivityScore_le restUnique tail position
    -- The index of the first update is not in the rest, so at most one update raises the score.
    by_cases same : position = index.toNat
    · subst same
      have notLater : index.toNat ∉ rest.map UInt64.toNat := by
        rw [List.mem_map]
        rintro ⟨other, member, equal⟩
        exact absent (UInt64.toNat_inj.mp equal ▸ member)
      simp only [↓reduceIte] at one
      simp only [notLater, ↓reduceIte, Nat.add_zero] at two
      have first : index.toNat ∈ (index :: rest).map UInt64.toNat := by simp
      simp only [first, ↓reduceIte]
      omega
    · simp only [same, ↓reduceIte, Nat.add_zero] at one
      simp only [List.map_cons, List.mem_cons, same, false_or]
      omega

/-- The output of a monadic filter has no duplicate when the keys of the input have none.

Each output is the key of the input that gives it. -/
private theorem filterMapM_nodup {α β ε : Type} {f : α → Except ε (Option β)} (key : α → β)
    (keyed : ∀ a b, f a = .ok (some b) → b = key a) :
    ∀ {items : List α} {out : List β}, (items.map key).Nodup →
      items.filterMapM f = .ok out → out.Nodup ∧ ∀ b ∈ out, ∃ a ∈ items, b = key a
  | [], out, _, computed => by
    simp only [List.filterMapM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | item :: rest, out, unique, computed => by
    rw [List.filterMapM_cons, bind_ok_iff] at computed
    obtain ⟨image, first, computed⟩ := computed
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp (List.map_cons ▸ unique)
    cases image with
    | none =>
      obtain ⟨nodup, members⟩ := filterMapM_nodup key keyed restUnique computed
      exact ⟨nodup, fun b member =>
        have ⟨a, mem, equal⟩ := members b member
        ⟨a, List.mem_cons_of_mem _ mem, equal⟩⟩
    | some b =>
      simp only at computed
      obtain ⟨tail, tailOk, computed⟩ := bind_ok_iff.mp computed
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      obtain ⟨nodup, members⟩ := filterMapM_nodup key keyed restUnique tailOk
      have equal := keyed _ _ first
      refine ⟨List.nodup_cons.mpr ⟨fun member => ?_, nodup⟩, fun c member => ?_⟩
      · obtain ⟨a, mem, same⟩ := members b member
        exact absent (List.mem_map.mpr ⟨a, mem, same.symm.trans equal⟩)
      · rcases List.mem_cons.mp member with rfl | member
        · exact ⟨item, List.mem_cons_self, equal⟩
        · obtain ⟨a, mem, same⟩ := members c member
          exact ⟨a, List.mem_cons_of_mem _ mem, same⟩

/-- The eligible validators have distinct indices, while the registry is below `2^64`. -/
theorem getEligibleValidatorIndices_nodup {eligible : List ValidatorIndex}
    (small : state.validators.data.size < 2 ^ 64)
    (computed : getEligibleValidatorIndices state = .ok eligible) : eligible.Nodup := by
  unfold getEligibleValidatorIndices at computed
  refine (filterMapM_nodup (fun entry => entry.2.toUInt64) (fun entry index ok => ?_) ?_
    computed).1
  · obtain ⟨eligibleFlag, _, ok⟩ := bind_ok_iff.mp ok
    simp only [pure, Except.pure, Except.ok.injEq] at ok
    split at ok
    · exact (Option.some.inj ok).symm
    · cases ok
  · -- The positions of the registry differ, and below `2^64` their indices of 64 bits do too.
    rw [show (fun entry : Validator × Nat => entry.2.toUInt64) =
      Nat.toUInt64 ∘ (·.2) from rfl, ← List.map_map, List.zipIdx_map_snd]
    have increasing := List.pairwise_lt_range' (s := 0)
      (n := state.validators.data.toList.length)
    refine (List.Pairwise.and_mem.mp increasing).map _ ?_
    rintro first second ⟨firstMember, secondMember, lt⟩ equal
    rw [List.mem_range'] at firstMember secondMember
    simp only [Array.length_toList] at firstMember secondMember
    have equalNat := congrArg UInt64.toNat equal
    rw [Nat.toUInt64_eq, Nat.toUInt64_eq, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at equalNat
    omega

/-- The update of the inactivity scores raises each by at most the score bias.

The registry must be below `2^64`, so that each eligible validator is updated once. -/
theorem processInactivityUpdates_le {altair : .altair ≤ fork}
    (small : state.validators.data.size < 2 ^ 64)
    (computed : processInactivityUpdates config state altair = .ok after) (position : Nat) :
    inactivityScoreAt after position ≤
      inactivityScoreAt state position + config.INACTIVITY_SCORE_BIAS.toNat := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    omega
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨eligible, eligibleOk, scores, scoresOk, rfl⟩ := computed
    have grown := foldlM_updateInactivityScore_le
      (getEligibleValidatorIndices_nodup small eligibleOk) scoresOk position
    simp only [inactivityScoreAt, altair, ↓reduceDIte]
    simp only [scoreOf] at grown
    split at grown <;> omega

theorem scoresKept_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      ScoresKept state pass.1.state
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
      exact (scoresKept_applyPendingDeposit credited).trans
        (scoresKept_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact scoresKept_passPendingDeposits (deposits := rest) ‹_›
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
    exact (scoresKept_applyPendingDeposit credited).trans
      (scoresKept_passPendingDeposits (deposits := rest) ‹_›)

theorem scoresKept_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ScoresKept state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (scoresKept_passPendingDeposits ‹_›).trans (.of_scores rfl)

theorem scoresKept_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      ScoresKept state result.1
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
      exact scoresKept_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (ScoresKept.decreaseBalance loweredOk).trans <|
      (ScoresKept.increaseBalance raisedOk).trans
        (scoresKept_passPendingConsolidations (result := (passed, read)) passedOk)

theorem scoresKept_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    ScoresKept state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine (scoresKept_processPendingDeposits deposited).trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (scoresKept_passPendingConsolidations ‹_›).trans (.of_scores rfl)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- The steps that close an epoch from Altair, after the history. -/
private theorem scoresKept_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : ScoresKept rooted after := by
  have syncedKept : ScoresKept rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact .of_scores rfl
  have lookedKept : ScoresKept synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_scores rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedKept : ScoresKept looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_scores rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedKept.trans (lookedKept.trans windowedKept)

/-- From Altair, the epoch transition raises each score by at most the score bias.

The registry must be below `2^64`, so that each eligible validator is updated once. -/
theorem processEpochAltair_scores_le {altair : .altair ≤ fork}
    (small : state.validators.data.size < 2 ^ 64)
    (computed : processEpochAltair config checks state altair = .ok after) (position : Nat) :
    inactivityScoreAt after position ≤
      inactivityScoreAt state position + config.INACTIVITY_SCORE_BIAS.toNat := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetKept : ScoresKept slashed reset := by
    split at resetOk
    · exact scoresKept_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ .refl _
  have paidKept : ScoresKept pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact .of_scores rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ .refl _
  have clearedKept : ScoresKept balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_scores rfl
  have mixedKept : ScoresKept cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_scores rfl
  -- The justification keeps the registry and the scores, and the update raises each score.
  have justifiedValidators : justified.validators = state.validators := by
    obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok justifiedOk
    · rw [same]
    · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
      rw [← rest]
  have grown := processInactivityUpdates_le (by rw [justifiedValidators]; exact small) scoredOk
    position
  have justifiedKept := (scoresKept_processJustificationAndFinalization justifiedOk).le position
  -- Every later step keeps the scores.
  have finish : ScoresKept scored after →
      inactivityScoreAt after position ≤
        inactivityScoreAt state position + config.INACTIVITY_SCORE_BIAS.toNat :=
    fun kept => by have := kept.le position; omega
  have head : ScoresKept scored mixed :=
    (scoresKept_processRewardsAndPenalties rewardedOk).trans <|
    (scoresKept_processRegistryUpdates registeredOk).trans <|
    (scoresKept_processSlashings slashedOk).trans <|
    resetKept.trans <|
    (scoresKept_processPendingBalances pendingOk).trans <|
    paidKept.trans <|
    (scoresKept_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans mixedKept
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · have rootedKept : ScoresKept mixed rooted := by
      unfold processHistoricalSummariesUpdate at rootedOk
      simp only [bind, Except.bind, pure, Except.pure] at rootedOk
      repeat' (split at rootedOk <;> try cases rootedOk)
      all_goals first
        | exact .refl _
        | exact .of_scores rfl
    exact finish (head.trans <| rootedKept.trans (scoresKept_epochEnd syncedOk lookedOk windowed))
  · exact finish (head.trans <| (scoresKept_processHistoricalRootsUpdate rootedOk).trans
      (scoresKept_epochEnd syncedOk lookedOk windowed))

/-- The epoch transition raises each score by at most the score bias.

Before Altair there are no scores, so each reads as zero before and after. -/
theorem processEpoch_scores_le (small : state.validators.data.size < 2 ^ 64)
    (computed : processEpoch config checks state = .ok after) (position : Nat) :
    inactivityScoreAt after position ≤
      inactivityScoreAt state position + config.INACTIVITY_SCORE_BIAS.toNat := by
  by_cases altair : Base.Fork.altair ≤ fork
  · unfold processEpoch at computed
    simp only [altair, ↓reduceDIte] at computed
    exact processEpochAltair_scores_le small computed position
  · simp [inactivityScoreAt, altair]

/-! ## Slots, upgrades and chains -/

/-- One slot raises each score by the score bias at most once, when it ends an epoch.

The epoch of the state then moves on by one, so the bound is the bias per epoch. -/
theorem advanceSlot_scores_le (computed : advanceSlot config checks state = .ok after)
    (small : after.validators.data.size < 2 ^ 64) (position : Nat) :
    inactivityScoreAt after position ≤ inactivityScoreAt state position +
      config.INACTIVITY_SCORE_BIAS.toNat *
        ((getCurrentEpoch after).toNat - (getCurrentEpoch state).toNat) := by
  have lifecycle := registryLifecycle_advanceSlot computed
  have slotNext := advanceSlot_slot computed
  have smallState : state.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt lifecycle.size_le small
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slotNext]
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, nextNat⟩, cached, cachedOk, epoched, epochedOk, afterEq⟩ := computed
  have nextValue : next.toNat = state.slot.toNat + 1 := by simpa using nextNat
  obtain ⟨_, _, _, _, cachedEq⟩ := processSlot_ok cachedOk
  -- The scores after the slot are those after the epoch, if it ran.
  have afterScores : inactivityScoreAt after position = inactivityScoreAt epoched position := by
    rw [← afterEq]
    rfl
  have cachedScores : inactivityScoreAt cached position = inactivityScoreAt state position := by
    rw [cachedEq]
    rfl
  have cachedSmall : cached.validators.data.size < 2 ^ 64 := by
    rw [cachedEq]
    exact smallState
  rw [afterScores, ← cachedScores]
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    -- The next slot starts an epoch, so the epoch moves on by one.
    have boundaryNat : (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      rw [← nextValue, ← UInt64.toNat_mod, boundary]
      rfl
    have moved : (state.slot.toNat + 1) / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
      rw [Nat.succ_div]
      simp [Nat.dvd_of_mod_eq_zero boundaryNat]
    have grown := processEpoch_scores_le cachedSmall epochedOk position
    rw [moved, Nat.add_sub_cancel_left, Nat.mul_one]
    exact grown
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact Nat.le_add_right _ _

/-- Queueing a validator that is not yet active keeps the scores. -/
theorem scoresKept_queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) : ScoresKept state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  exact ScoresKept.trans (by exact .of_scores rfl)
    ((ScoresKept.setValidator set₂).trans (.of_scores rfl))

/-- Queueing a validator that is not yet active keeps the slot. -/
theorem queuePreActivation_slot {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) : after.slot = state.slot := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  exact (setValidator_slot set₂).trans (setBalance_slot set₁)

/-- Queueing the excess balance of a compounding validator keeps the slot. -/
theorem queueCompoundingExcess_slot {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    after.slot = state.slot := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · have queued := liftAccessor_ok.mp computed
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨_, _, queued⟩ := queued
      split at queued
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
        have slot := setBalance_slot set
        exact slot
      · cases queued
        rfl
    · cases computed
      rfl
  · cases computed
    rfl

theorem scoresKept_queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    ScoresKept state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · exact scoresKept_queueExcessActiveBalance (liftAccessor_ok.mp computed)
    · cases computed
      exact .refl _
  · cases computed
    exact .refl _

/-- An upgrade keeps the slot, and raises no score.

The upgrade to Altair starts every score at zero, and the later ones carry the scores. -/
theorem upgradeNext_scores {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.slot = pre.state.slot ∧ ∀ position,
      inactivityScoreAt post.val.state position ≤ inactivityScoreAt pre.state position := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToAltair, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at upgraded
    obtain ⟨translated, translatedOk, _, _, rfl⟩ := upgraded
    rw [← Array.foldlM_toList] at translatedOk
    obtain ⟨_, rfl, _⟩ := foldlM_translateAttestation translatedOk
    have zeros := (carryFields_of_lt_altair (config := config) (post := .altair) state (by decide)
      (by decide) (by decide) (by decide)).2.2
    refine ⟨rfl, fun position => ?_⟩
    -- Every score starts at zero.
    simp only [inactivityScoreAt, zeros, Array.getElem?_replicate]
    split <;> split <;> simp_all
  -- The upgrades to Bellatrix, Capella and Deneb carry the slot and the scores.
  · subst computed
    exact ⟨rfl, fun position => by
      simp (config := { decide := true }) [inactivityScoreAt, carryFields, carryList]⟩
  · subst computed
    exact ⟨rfl, fun position => by
      simp (config := { decide := true }) [inactivityScoreAt, carryFields, carryList]⟩
  · subst computed
    exact ⟨rfl, fun position => by
      simp (config := { decide := true }) [inactivityScoreAt, carryFields, carryList]⟩
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := upgraded
    -- Each queue step keeps the slot and raises no score.
    have queuedKept := foldlM_ok_invariant
      (fun current : BeaconState preset .pectra => current.slot = state.slot ∧
        ∀ position, inactivityScoreAt current position ≤ inactivityScoreAt state position)
      (fun _ _ _ ⟨slot, kept⟩ step => ⟨(queuePreActivation_slot step).trans slot,
        fun position => Nat.le_trans ((scoresKept_queuePreActivation step).le position)
          (kept position)⟩)
      ⟨rfl, fun position => by
        simp (config := { decide := true }) [inactivityScoreAt, carryFields, carryList]⟩ queued
    exact foldlM_ok_invariant
      (fun current : BeaconState preset .pectra => current.slot = state.slot ∧
        ∀ position, inactivityScoreAt current position ≤ inactivityScoreAt state position)
      (fun _ _ _ ⟨slot, kept⟩ step => ⟨(queueCompoundingExcess_slot step).trans slot,
        fun position => Nat.le_trans ((scoresKept_queueCompoundingExcess step).le position)
          (kept position)⟩) queuedKept compounded
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    exact ⟨rfl, fun position => by
      simp (config := { decide := true }) [inactivityScoreAt, carryFields, carryList]⟩
  · obtain ⟨_, upgraded, rfl⟩ := computed
    unfold upgradeToGloas at upgraded
    obtain ⟨_, -, rest⟩ := bind_ok_iff.mp upgraded
    obtain ⟨_, -, onboarded⟩ := bind_ok_iff.mp rest
    obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    exact ⟨rfl, fun position => by
      simp (config := { decide := true }) [inactivityScoreAt, upgradeFields, toGloasList]⟩
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact ⟨rfl, fun position => by
      simp (config := { decide := true }) [inactivityScoreAt, upgradeHezeFields,
      toHezeList]⟩

/-- The inactivity scores at the end of a part of a chain, against those at its start.

The validators keep their lifecycle, and the slot does not go back.

While the last registry is below `2^64`, each score is bounded.

It is at most its value at the start plus the score bias for each epoch between. -/
def ScoresGrowth (config : Config) (start after : ForkedBeaconState preset) : Prop :=
  RegistryLifecycle start.state after.state ∧ start.state.slot.toNat ≤ after.state.slot.toNat ∧
    (after.state.validators.data.size < 2 ^ 64 → ∀ position,
      inactivityScoreAt after.state position ≤ inactivityScoreAt start.state position +
        config.INACTIVITY_SCORE_BIAS.toNat *
          ((getCurrentEpoch after.state).toNat - (getCurrentEpoch start.state).toNat))

/-- Every step of a chain satisfies the growth of the scores. -/
theorem stepRelation_scoresGrowth :
    StepRelation config checks (ScoresGrowth (preset := preset) config) where
  refl _ := ⟨.refl _, Nat.le_refl _, fun _ _ => by simp⟩
  trans {first second third} one two := by
    obtain ⟨firstLifecycle, firstSlot, firstScores⟩ := one
    obtain ⟨secondLifecycle, secondSlot, secondScores⟩ := two
    refine ⟨firstLifecycle.trans secondLifecycle, Nat.le_trans firstSlot secondSlot,
      fun small position => ?_⟩
    have middle := firstScores (Nat.lt_of_le_of_lt secondLifecycle.size_le small) position
    have last := secondScores small position
    -- The epochs do not go back, so the epochs of the two parts add up.
    have firstEpochs := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat) firstSlot
    have secondEpochs := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat) secondSlot
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat] at middle last
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    generalize first.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = firstEpoch at *
    generalize second.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = secondEpoch at *
    generalize third.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat = thirdEpoch at *
    have parts : thirdEpoch - firstEpoch =
        (secondEpoch - firstEpoch) + (thirdEpoch - secondEpoch) := by omega
    rw [parts, Nat.mul_add]
    omega
  advanceSlot computed := ⟨registryLifecycle_advanceSlot computed,
    by have slot := advanceSlot_slot computed; dsimp only; omega, advanceSlot_scores_le computed⟩
  upgradeNext _ computed := by
    obtain ⟨slot, scores⟩ := upgradeNext_scores computed
    exact ⟨registryLifecycle_upgradeNext computed, by rw [slot]; exact Nat.le_refl _,
      fun _ position => Nat.le_trans (scores position) (Nat.le_add_right _ _)⟩
  applySignedBlock computed := by
    have block := (applySignedBlock_ok computed).2.1
    exact ⟨registryLifecycle_processBlock block,
      by dsimp only; rw [(frame_processBlock block).slot]; exact Nat.le_refl _,
      fun _ position => Nat.le_trans ((scoresKept_processBlock block).le position)
        (Nat.le_add_right _ _)⟩

/-- Along every chain, each inactivity score grows by at most the score bias per epoch.

A validator that is new since the start counts from zero.

From Gloas the registry at the end must be below `2^64`. -/
theorem Reaches.inactivityScore_le {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after)
    (small : after.state.validators.data.size < 2 ^ 64) (position : Nat) :
    inactivityScoreAt after.state position ≤ inactivityScoreAt start.state position +
      config.INACTIVITY_SCORE_BIAS.toNat *
        ((getCurrentEpoch after.state).toNat - (getCurrentEpoch start.state).toNat) :=
  (stepRelation_scoresGrowth.reaches chain).2.2 small position

end EthLib.Consensus
