module

public import EthLib.Consensus.Proofs.Transition.ForkBoundary

/-!
# Proofs: the steps that keep the record of history

Eight fields of a state record its history.

- The slot.
- The latest block header.
- The circular buffer of block roots.
- The circular buffer of state roots.
- The justification bits.
- The previous justified, current justified and finalized checkpoints.

Only five functions write them.

- `advanceSlot` moves the slot on.
- `processSlot` writes the two buffers, and fills the state root of the header.
- `processBlockHeader` writes the header of a new block.
- `weighJustificationAndFinalization` writes the justification bits and the checkpoints.
- The upgrades copy all eight fields.

This file proves that every other step of a block or an epoch keeps the eight fields.

That is what lets a value in a buffer be traced back to the step that wrote it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- The fields that record history.

They are the slot, the latest header, the two buffers of roots, the bits and the checkpoints. -/
def BeaconState.history (state : BeaconState preset fork) :
    Slot × BeaconBlockHeader × RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat ×
      RootedVector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat ×
      Bitvector JUSTIFICATION_BITS_LENGTH.toNat × Checkpoint × Checkpoint × Checkpoint :=
  (state.slot, state.latestBlockHeader, state.blockRoots, state.stateRoots,
    state.justificationBits, state.previousJustifiedCheckpoint, state.currentJustifiedCheckpoint,
    state.finalizedCheckpoint)

/-- A step that keeps every field of the history. -/
def Kept (state after : BeaconState preset fork) : Prop :=
  after.history = state.history

theorem Kept.refl (state : BeaconState preset fork) : Kept state state := rfl

theorem Kept.trans {first second third : BeaconState preset fork} (one : Kept first second)
    (two : Kept second third) : Kept first third :=
  Eq.trans two one

theorem Kept.slot (kept : Kept state after) : after.slot = state.slot :=
  congrArg Prod.fst kept

theorem Kept.latestBlockHeader (kept : Kept state after) :
    after.latestBlockHeader = state.latestBlockHeader :=
  congrArg (·.2.1) kept

theorem Kept.blockRoots (kept : Kept state after) : after.blockRoots = state.blockRoots :=
  congrArg (·.2.2.1) kept

theorem Kept.stateRoots (kept : Kept state after) : after.stateRoots = state.stateRoots :=
  congrArg (·.2.2.2.1) kept

theorem Kept.justificationBits (kept : Kept state after) :
    after.justificationBits = state.justificationBits :=
  congrArg (·.2.2.2.2.1) kept

theorem Kept.previousJustifiedCheckpoint (kept : Kept state after) :
    after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint :=
  congrArg (·.2.2.2.2.2.1) kept

theorem Kept.currentJustifiedCheckpoint (kept : Kept state after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint :=
  congrArg (·.2.2.2.2.2.2.1) kept

theorem Kept.finalizedCheckpoint (kept : Kept state after) :
    after.finalizedCheckpoint = state.finalizedCheckpoint :=
  congrArg (·.2.2.2.2.2.2.2) kept

/-- A fold whose every step keeps the history keeps it. -/
theorem Kept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → Kept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Kept state after :=
  foldlM_ok_invariant (Kept state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (Kept.refl state) computed

/-! ## Mutators -/

theorem kept_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : Kept state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

theorem kept_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : Kept state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact rfl

theorem kept_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : Kept state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact rfl

theorem kept_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    Kept state after := by
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact Kept.refl _

theorem kept_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : Kept state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, exitEpoch, withdrawableEpoch, queue, summed, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Kept.refl _
  · exact (kept_exitQueue queue).trans (kept_setValidator set)

theorem kept_slashings (state : BeaconState preset fork) (slashings : RootedVector Gwei _) :
    Kept state { state with slashings } :=
  rfl

/-- The last step of a slashing, which from Gloas cancels builder payments, keeps the history. -/
theorem kept_slashValidatorLast {last : BeaconState preset fork} {index : ValidatorIndex}
    (done : (pure (if gloas : .glamsterdam ≤ fork then cancelProposerPayments last gloas index
      else last) : Except AccessorError (BeaconState preset fork)) = .ok after) :
    Kept last after := by
  simp only [pure, Except.pure, Except.ok.injEq] at done
  subst done
  split
  · exact rfl
  · exact Kept.refl _

theorem kept_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    Kept state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  refine (kept_initiateValidatorExit exitedOk).trans <|
    ((kept_setValidator markedOk).trans
      (kept_slashings _ _)).trans <|
    (kept_decreaseBalance loweredOk).trans <| (kept_increaseBalance raisedOk).trans <|
    (kept_increaseBalance lastOk).trans (kept_slashValidatorLast done)

/-! ## The steps of a block -/

theorem kept_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : Kept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact rfl

theorem kept_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : Kept state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact (congrArg BeaconState.history rest :)

theorem kept_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    Kept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact kept_slashValidator slashed

theorem kept_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    Kept step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact kept_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _

theorem kept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    Kept state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => Kept state step.1)
    (fun _ _ _ before ok => before.trans (kept_slashIfSlashable ok))
    (show Kept state (state, false).1 from Kept.refl state) folded

theorem kept_setEpochParticipation (current : Bool)
    (participation : EpochParticipation preset fork) :
    Kept state (setEpochParticipation state current participation) := by
  unfold setEpochParticipation
  split <;> exact rfl

/-- From Altair, an attestation sets flags, pays the proposer, and from Gloas weighs a payment. -/
theorem kept_processAttestationAltair {attestation : Attestation preset fork}
    {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed :
      processAttestationAltair config checks state attestation altair parentSlot = .ok after) :
    Kept state after := by
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, raised, raisedOk, final⟩ := computed
  have last : Kept raised after := by
    split at final
    · rw [recordPaymentWeight_eq final]
      exact rfl
    · cases final
      exact Kept.refl _
  exact (kept_setEpochParticipation _ _).trans ((kept_increaseBalance raisedOk).trans last)

theorem kept_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    Kept state after := by
  unfold processAttestation at computed
  split at computed
  · exact kept_processAttestationAltair computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept
  · obtain ⟨_, rest⟩ := kept
    exact (congrArg BeaconState.history rest :)
  · obtain ⟨_, rest⟩ := kept
    exact (congrArg BeaconState.history rest :)

theorem kept_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    Kept state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact rfl
  split at computed
  · cases computed
    exact rfl
  · cases computed

theorem kept_applyDepositElectra {electra : .pectra ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials
      amount signature = .ok after) :
    Kept state after := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, added, pushed⟩ := computed
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact (kept_addValidatorToRegistry added).trans
        (rfl)
    · cases computed
      exact Kept.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    exact rfl

theorem kept_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    Kept state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact Kept.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact kept_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Kept.refl _
  · rw [liftAccessor_ok] at computed
    exact kept_increaseBalance computed

theorem kept_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    Kept state after := by
  unfold applyDeposit at computed
  split at computed
  · exact kept_applyDepositElectra computed
  · exact kept_applyPendingDeposit computed

theorem kept_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    Kept state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (show Kept state { state with eth1DepositIndex := fun _ => next } from rfl).trans
    (kept_applyDeposit applied)

theorem kept_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    Kept state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact kept_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem kept_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) : Kept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact rfl

theorem kept_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    Kept state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact rfl

theorem kept_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    Kept state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact rfl

theorem kept_requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    Kept state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (kept_computeExitEpochAndUpdateChurn churned).trans
      (rfl)
  · cases computed
    exact Kept.refl _

theorem kept_processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    Kept state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Kept.refl _)
    | exact kept_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact kept_requestPartialWithdrawal computed

theorem kept_queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) : Kept state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact rfl
  · cases computed
    exact Kept.refl _

theorem kept_switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    Kept state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (kept_setValidator set).trans
    (kept_queueExcessActiveBalance queued)

theorem kept_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    Kept state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, ⟨_, sum⟩, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  exact (kept_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (kept_setValidator (state := churnedState) set).trans rfl

theorem kept_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    Kept state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact Kept.refl _)
    | exact kept_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact kept_queueConsolidation computed

theorem kept_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    Kept state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (Kept.foldlM (fun _ _ _ ok => kept_processDepositRequest ok) depositsOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processWithdrawalRequest ok) withdrawalsOk).trans <|
    Kept.foldlM (fun _ _ _ ok => kept_processConsolidationRequest ok) consolidationsOk

/-! ## Withdrawals -/

theorem kept_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : Kept state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact rfl
  · exact kept_decreaseBalance computed

theorem kept_updateNextWithdrawalIndex {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalIndex state withdrawals = .ok after) : Kept state after := by
  unfold updateNextWithdrawalIndex at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact rfl
  · cases computed
    exact Kept.refl _

theorem kept_updateNextWithdrawalValidatorIndex {capella : .shapella ≤ fork}
    {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalValidatorIndex state capella withdrawals = .ok after) :
    Kept state after := by
  unfold updateNextWithdrawalValidatorIndex at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · cases computed
  · cases computed
    exact rfl

theorem kept_updateNextWithdrawalBuilderIndex {gloas : .glamsterdam ≤ fork} {count : Nat}
    (computed : updateNextWithdrawalBuilderIndex state gloas count = .ok after) :
    Kept state after := by
  unfold updateNextWithdrawalBuilderIndex at computed
  dsimp only at computed
  split at computed
  · cases computed
    exact rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact rfl

theorem kept_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    Kept state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : Kept state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact Kept.foldlM (fun _ _ _ ok => kept_applyWithdrawal ok) appliedOk
  have queued : ∀ kept : BeaconState preset fork,
      Kept kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact rfl
  have partials : ∀ kept : BeaconState preset fork,
      Kept kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact rfl
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → Kept kept finished := by
    intro kept ok
    split at ok
    · exact kept_updateNextWithdrawalBuilderIndex ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ Kept.refl _
  exact one.trans <| (kept_updateNextWithdrawalIndex indexedOk).trans <| (queued _).trans <|
    (partials _).trans <| (swept _ sweptOk).trans (kept_updateNextWithdrawalValidatorIndex last)

theorem kept_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : Kept state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact kept_applyExpectedWithdrawals applied
    · cases computed
      exact Kept.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact kept_applyExpectedWithdrawals applied

theorem kept_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    Kept state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact kept_setValidator set

/-! ## The parent payload and the execution part of a block -/

theorem kept_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    Kept state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact rfl

theorem kept_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    Kept state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact rfl)

theorem kept_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    Kept state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact Kept.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact rfl

theorem kept_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : Kept state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;>
      exact rfl

theorem kept_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    Kept state after := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact Kept.refl _
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
  exact (kept_settleParentPayment settledOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processDepositRequest ok) depositsOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processWithdrawalRequest ok) withdrawalsOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processConsolidationRequest ok) consolidationsOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processBuilderDepositRequest ok) buildersOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processBuilderExitRequest ok) exitsOk).trans
      (rfl)

theorem kept_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    Kept state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact rfl

theorem kept_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    Kept state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (kept_processWithdrawals withdrawnOk).trans (kept_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (kept_processWithdrawals withdrawnOk).trans (kept_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact kept_processExecutionPayload computed
    · cases computed
      exact Kept.refl _

/-! ## The sync aggregate -/

theorem kept_applySyncReward {reward proposerReward : Gwei}
    {proposer : Except AccessorError ValidatorIndex} {member : ValidatorIndex × Bool}
    (computed : applySyncReward reward proposerReward proposer state member = .ok after) :
    Kept state after := by
  unfold applySyncReward at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, raised, _, _, paid⟩ := computed
    exact (kept_increaseBalance raised).trans (kept_increaseBalance paid)
  · exact kept_decreaseBalance (liftAccessor_ok.mp computed)

theorem kept_processSyncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    Kept state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  exact Kept.foldlM (fun _ _ _ ok => kept_applySyncReward ok) folded

/-! ## Blocks -/

/-- The operations of a block keep the history. -/
theorem kept_processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    Kept state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (Kept.foldlM (fun _ _ _ ok => kept_processProposerSlashing ok) proposersOk).trans <|
      (Kept.foldlM (fun _ _ _ ok => kept_processAttesterSlashing ok) attestersOk).trans <|
      (Kept.foldlM (fun _ _ _ ok => kept_processAttestation ok) attestedOk).trans <|
      (Kept.foldlM (fun _ _ _ ok => kept_processVoluntaryExit ok) exitsOk).trans <|
      (Kept.foldlM (fun _ _ _ ok => kept_processBlsToExecutionChange ok) changesOk).trans <|
      Kept.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact Kept.refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : Kept exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact Kept.foldlM (fun _ _ _ ok => kept_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ Kept.refl _
  have requests : Kept changed after := by
    split at requestsOk
    · exact kept_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ Kept.refl _
  exact (Kept.foldlM (fun _ _ _ ok => kept_processProposerSlashing ok) proposersOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processAttesterSlashing ok) attestersOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processAttestation ok) attestedOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processDeposit ok) depositedOk).trans <|
    (Kept.foldlM (fun _ _ _ ok => kept_processVoluntaryExit ok) exitsOk).trans <|
    changes.trans requests

/-- A block keeps the history, except at its header.

From Gloas the payload of the parent block runs first, and keeps it.

The header step then writes the header of the block, and every later step keeps it. -/
theorem processBlock_kept {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ paid headed, Kept state paid ∧ processBlockHeader paid block = .ok headed ∧
      Kept headed after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidKept : Kept state paid := by
      split at paidOk
      · exact kept_processParentExecutionPayload paidOk
      · cases paidOk
        exact Kept.refl _
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedKept : Kept headed executed := by
      split at executedOk
      · exact kept_processBlockExecution executedOk
      · cases executedOk
        exact Kept.refl _
    -- Heze drops the vote on the deposit contract.
    have votedKept : Kept revealed voted := by
      split at votedOk
      · exact kept_processEth1Data votedOk
      · cases votedOk
        exact Kept.refl _
    exact ⟨paid, headed, paidKept, headedOk, executedKept.trans <|
      (kept_processRandao revealedOk).trans <| votedKept.trans <|
      (kept_processOperations operatedOk).trans (kept_processSyncAggregate synced)⟩
  simp only [bind_ok_iff] at computed
  obtain ⟨headed, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact ⟨state, headed, Kept.refl _, headerOk, (kept_processRandao randaoOk).trans <|
    (kept_processEth1Data eth1Ok).trans (kept_processOperations operationsOk)⟩

/-! ## The steps of an epoch -/

theorem kept_applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) : Kept state after := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, raised, lowered⟩ := computed
  exact (kept_increaseBalance raised).trans (kept_decreaseBalance lowered)

theorem kept_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : Kept state after :=
  Kept.foldlM (fun _ _ _ ok => kept_applyDeltas ok) computed

theorem kept_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) : Kept state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact Kept.foldlM (fun _ _ _ ok => kept_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact kept_applyAllDeltas applied

theorem kept_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) : Kept state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set : Kept state marked := kept_setValidator markedOk
  split at computed
  · rw [liftAccessor_ok] at computed
    exact set.trans (kept_initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

theorem kept_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : Kept state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, set⟩ := computed
  exact kept_setValidator set

theorem kept_updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    Kept state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact kept_setValidator set
  split at computed
  · rw [liftAccessor_ok] at computed
    exact kept_initiateValidatorExit computed
  split at computed
  · rw [liftAccessor_ok] at computed
    exact kept_setValidator computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _

theorem kept_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : Kept state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact Kept.foldlM (fun _ _ _ ok => kept_updateRegistryEntryElectra ok) computed
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  exact (Kept.foldlM (fun _ _ _ ok => kept_updateRegistryEntry ok) updatedOk).trans
    (Kept.foldlM (fun _ _ _ ok => kept_activateValidator ok) activated)

theorem kept_applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    Kept state after := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact kept_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Kept.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _

theorem kept_applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (computed : applySlashingPenaltyElectra state perIncrement index = .ok after) :
    Kept state after := by
  simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, lowered⟩ := computed
      exact kept_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Kept.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _

theorem kept_processSlashings (computed : processSlashings state = .ok after) :
    Kept state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact Kept.foldlM (fun _ _ _ ok => kept_applySlashingPenaltyElectra ok) applied
  · exact Kept.foldlM (fun _ _ _ ok => kept_applySlashingPenalty ok) computed

theorem kept_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) : Kept state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _

theorem kept_updateEffectiveBalance {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) : Kept state after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, _, _, set⟩ := computed
  exact kept_setValidator set

theorem kept_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : Kept state after := by
  unfold processEffectiveBalanceUpdates at computed
  exact Kept.foldlM (fun _ _ _ ok => kept_updateEffectiveBalance ok) computed

theorem kept_processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    Kept state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq computed
  exact kept_slashings _ _

theorem kept_processRandaoMixesReset (computed : processRandaoMixesReset state = .ok after) :
    Kept state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq computed
  exact rfl

theorem kept_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : Kept state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _

theorem kept_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) : Kept state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact rfl

/-! ## The steps of an epoch from Altair -/

theorem kept_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) : Kept state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact rfl

theorem kept_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      Kept state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Kept.refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact Kept.refl _
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (kept_applyPendingDeposit credited).trans
        (kept_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact kept_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact Kept.refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (kept_applyPendingDeposit credited).trans
      (kept_passPendingDeposits (deposits := rest) ‹_›)

theorem kept_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    Kept state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals
    exact (kept_passPendingDeposits ‹_›).trans
      (rfl)

theorem kept_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      Kept state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Kept.refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact kept_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact Kept.refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (kept_decreaseBalance loweredOk).trans <|
      (kept_increaseBalance raisedOk).trans
        (kept_passPendingConsolidations (result := (passed, read)) passedOk)

theorem kept_processPendingConsolidations {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) : Kept state after := by
  unfold processPendingConsolidations at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals
    exact (kept_passPendingConsolidations ‹_›).trans
      (rfl)

theorem kept_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) : Kept state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    exact (kept_processPendingDeposits deposited).trans
      (kept_processPendingConsolidations consolidated)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Kept.refl _

theorem kept_processBuilderPendingPayments {gloas : .glamsterdam ≤ fork}
    (computed : processBuilderPendingPayments state gloas = .ok after) : Kept state after := by
  simp only [processBuilderPendingPayments, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact rfl

theorem kept_processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (computed : processHistoricalSummariesUpdate state capella = .ok after) :
    Kept state after := by
  unfold processHistoricalSummariesUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals first
    | exact Kept.refl _
    | exact rfl

theorem kept_processParticipationFlagUpdates (state : BeaconState preset fork)
    (altair : .altair ≤ fork) : Kept state (processParticipationFlagUpdates state altair) :=
  rfl

theorem kept_processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (computed : processSyncCommitteeUpdates state altair = .ok after) : Kept state after := by
  unfold processSyncCommitteeUpdates at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals first
    | exact Kept.refl _
    | exact rfl

theorem kept_processProposerLookahead {fulu : .fusaka ≤ fork}
    (computed : processProposerLookahead state fulu = .ok after) : Kept state after := by
  simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact rfl

theorem kept_processPtcWindow {gloas : .glamsterdam ≤ fork}
    (computed : processPtcWindow state gloas = .ok after) : Kept state after := by
  simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact rfl

/-- The steps that close an epoch from Altair, after the history. -/
private theorem kept_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : Kept rooted after := by
  have lookedKept : Kept synced looked := by
    split at lookedOk
    · exact kept_processProposerLookahead (liftAccessor_ok.mp lookedOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ Kept.refl _
  have windowedKept : Kept looked after := by
    split at windowed
    · exact kept_processPtcWindow (liftAccessor_ok.mp windowed)
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ Kept.refl _
  exact (kept_processParticipationFlagUpdates rooted altair).trans <|
    (kept_processSyncCommitteeUpdates syncedOk).trans (lookedKept.trans windowedKept)

/-- From Altair, the epoch transition is justification, then steps that keep the history. -/
theorem processEpochAltair_kept {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    ∃ justified, processJustificationAndFinalization state = .ok justified ∧
      Kept justified after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetKept : Kept slashed reset := by
    split at resetOk
    · exact kept_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ Kept.refl _
  have paidKept : Kept pending paid := by
    split at paidOk
    · exact kept_processBuilderPendingPayments (liftAccessor_ok.mp paidOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ Kept.refl _
  have head : Kept justified mixed :=
    (kept_processInactivityUpdates scoredOk).trans <|
    (kept_processRewardsAndPenalties rewardedOk).trans <|
    (kept_processRegistryUpdates registeredOk).trans <|
    (kept_processSlashings slashedOk).trans <|
    resetKept.trans <|
    (kept_processPendingBalances pendingOk).trans <|
    paidKept.trans <|
    (kept_processEffectiveBalanceUpdates balancedOk).trans <|
    (kept_processSlashingsReset clearedOk).trans <|
    (kept_processRandaoMixesReset mixedOk)
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · exact ⟨justified, justifiedOk, head.trans <|
      (kept_processHistoricalSummariesUpdate rootedOk).trans
        (kept_epochEnd syncedOk lookedOk windowed)⟩
  · exact ⟨justified, justifiedOk, head.trans <|
      (kept_processHistoricalRootsUpdate rootedOk).trans
        (kept_epochEnd syncedOk lookedOk windowed)⟩


/-- The epoch transition is justification, then steps that keep the history, at every fork. -/
theorem processEpoch_kept (computed : processEpoch config checks state = .ok after) :
    ∃ justified, processJustificationAndFinalization state = .ok justified ∧
      Kept justified after := by
  unfold processEpoch at computed
  split at computed
  · exact processEpochAltair_kept computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  exact ⟨justified, justifiedOk,
    (kept_processRewardsAndPenalties rewardedOk).trans <|
    (kept_processRegistryUpdates registeredOk).trans <|
    (kept_processSlashings slashedOk).trans <|
    (kept_processEth1DataReset resetOk).trans <|
    (kept_processEffectiveBalanceUpdates balancedOk).trans <|
    (kept_processSlashingsReset clearedOk).trans <|
    (kept_processRandaoMixesReset mixedOk).trans <|
    (kept_processHistoricalRootsUpdate rootedOk).trans <|
    kept_processParticipationRecordUpdates rotated⟩

/-- Justification and finalization keep the latest header and the two buffers of roots.

They write only the justification bits and the checkpoints. -/
theorem processJustificationAndFinalization_roots
    (computed : processJustificationAndFinalization state = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader ∧ after.blockRoots = state.blockRoots ∧
      after.stateRoots = state.stateRoots := by
  rcases processJustificationAndFinalization_ok computed with rfl | ⟨_, _, _, weighed⟩
  · exact ⟨rfl, rfl, rfl⟩
  · have rest := (weighJustificationAndFinalization_checkpoints weighed).2.2.2
    rw [← rest]
    exact ⟨rfl, rfl, rfl⟩

/-! ## Upgrades -/

theorem kept_queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) : Kept state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, -, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  obtain ⟨_, rfl⟩ := setValidator_ok set₂
  rfl

theorem kept_queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) : Kept state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · exact kept_queueExcessActiveBalance (liftAccessor_ok.mp computed)
    · cases computed
      rfl
  · cases computed
    rfl

/-- An upgrade copies every field of the history.

The fields have the same type at every fork, so the statement compares them directly. -/
theorem upgradeNext_history {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.history = pre.state.history := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToAltair, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, folded, _, -, rfl⟩ := upgraded
    rw [← Array.foldlM_toList] at folded
    obtain ⟨_, rfl, -⟩ := foldlM_translateAttestation folded
    rfl
  · subst computed
    rfl
  · subst computed
    rfl
  · subst computed
    rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := upgraded
    have first := Kept.foldlM (fun _ _ _ ok => kept_queuePreActivation ok) queued
    exact (first.trans (Kept.foldlM (fun _ _ _ ok => kept_queueCompoundingExcess ok) compounded) :)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    unfold upgradeToGloas at upgraded
    obtain ⟨_, -, rest⟩ := bind_ok_iff.mp upgraded
    obtain ⟨_, -, onboarded⟩ := bind_ok_iff.mp rest
    obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    rfl

end EthLib.Consensus
