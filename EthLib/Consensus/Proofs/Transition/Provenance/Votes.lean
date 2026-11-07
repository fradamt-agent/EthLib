module

public import EthLib.Consensus.Proofs.Transition.Provenance.Kept

/-!
# Proofs: the steps that add no vote

Four fields of a state record the votes of the last two epochs.

- Before Altair, the pending attestations of the previous and of the current epoch.
- From Altair, the participation flags of the previous and of the current epoch.

A vote here is a pending attestation, or one flag of one validator.

Only three kinds of step add a vote.

- An attestation of a block adds a pending attestation, or sets flags of its attesters.
- The end of an epoch moves the votes of the current epoch to the previous one.
- The upgrade to Altair turns the pending attestations of the previous epoch into flags.

This file proves that every other step of a block or an epoch adds no vote.

A new validator gets no flag, and other steps keep the four fields.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- The flags of one epoch after a step are among those before it, validator by validator.

A validator may lose flags, or be new with none, but gains no flag. -/
def FlagsWithin (before after : Array ParticipationFlags) : Prop :=
  ∀ (index : Nat) (flags : ParticipationFlags) (flagIndex : UInt64), after[index]? = some flags →
    hasFlag flags flagIndex = true →
      ∃ old, before[index]? = some old ∧ hasFlag old flagIndex = true

theorem FlagsWithin.refl (flags : Array ParticipationFlags) : FlagsWithin flags flags :=
  fun _ _ _ found set => ⟨_, found, set⟩

theorem FlagsWithin.trans {first second third : Array ParticipationFlags}
    (one : FlagsWithin first second) (two : FlagsWithin second third) :
    FlagsWithin first third := fun index flags flagIndex found set =>
  have ⟨middle, middleFound, middleSet⟩ := two index flags flagIndex found set
  one index middle flagIndex middleFound middleSet

theorem flagBit_ne_zero (flagIndex : UInt64) : flagBit flagIndex ≠ 0 := by
  unfold flagBit
  rw [UInt8.shiftLeft_eq_shiftLeft_mod]
  -- A shift by less than eight keeps the one bit inside the byte.
  have shifted : ∀ k : Fin 8, (1 : UInt8) <<< (UInt8.ofNat k.val) ≠ 0 := by decide
  have lt : (flagIndex.toUInt8 % 8).toNat < 8 := by
    rw [UInt8.toNat_mod]
    exact Nat.mod_lt _ (by decide)
  simpa only [UInt8.ofNat_toNat] using shifted ⟨_, lt⟩

/-- No flag is set in the empty flags. -/
theorem hasFlag_zero (flagIndex : UInt64) : hasFlag 0 flagIndex = false := by
  simp only [hasFlag, UInt8.zero_and, beq_eq_false_iff_ne, ne_eq]
  exact fun same => flagBit_ne_zero _ same.symm

/-- Writing empty flags at one index adds no flag. -/
theorem flagsWithin_setOrAppendList {switch : Base.Fork} {limit : Nat}
    {list list' : ForkList switch fork ParticipationFlags limit} {index : UInt64}
    (computed : setOrAppendList list index 0 = .ok list') : FlagsWithin list.data list'.data := by
  intro i flags flagIndex found set
  rw [setOrAppendList_getElem? computed] at found
  split at found
  · cases found
    rw [hasFlag_zero] at set
    cases set
  · exact ⟨flags, found, set⟩

/-- The four fields that record votes. -/
def BeaconState.votes (state : BeaconState preset fork) :=
  (state.previousEpochAttestations, state.currentEpochAttestations,
    state.previousEpochParticipation, state.currentEpochParticipation)

/-- A step that adds no vote.

It keeps the pending attestations, and every flag after it was set before it. -/
structure VotesKept (state after : BeaconState preset fork) : Prop where
  previousEpochAttestations : after.previousEpochAttestations = state.previousEpochAttestations
  currentEpochAttestations : after.currentEpochAttestations = state.currentEpochAttestations
  previousEpochParticipation : ∀ altair : .altair ≤ fork,
    FlagsWithin (state.previousEpochParticipation altair).data
      (after.previousEpochParticipation altair).data
  currentEpochParticipation : ∀ altair : .altair ≤ fork,
    FlagsWithin (state.currentEpochParticipation altair).data
      (after.currentEpochParticipation altair).data

theorem VotesKept.of_votes (same : after.votes = state.votes) : VotesKept state after := by
  simp only [BeaconState.votes, Prod.mk.injEq] at same
  obtain ⟨previous, current, previousFlags, currentFlags⟩ := same
  exact ⟨previous, current, fun _ => previousFlags ▸ .refl _, fun _ => currentFlags ▸ .refl _⟩

theorem VotesKept.refl (state : BeaconState preset fork) : VotesKept state state :=
  .of_votes rfl

theorem VotesKept.trans {first second third : BeaconState preset fork}
    (one : VotesKept first second) (two : VotesKept second third) : VotesKept first third :=
  ⟨two.previousEpochAttestations.trans one.previousEpochAttestations,
    two.currentEpochAttestations.trans one.currentEpochAttestations,
    fun altair => (one.previousEpochParticipation altair).trans
      (two.previousEpochParticipation altair),
    fun altair => (one.currentEpochParticipation altair).trans
      (two.currentEpochParticipation altair)⟩

/-- A fold whose every step adds no vote adds none. -/
theorem VotesKept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → VotesKept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : VotesKept state after :=
  foldlM_ok_invariant (VotesKept state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (VotesKept.refl state) computed

/-! ## Mutators -/

theorem votesKept_setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : VotesKept state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact .of_votes rfl

theorem votesKept_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : VotesKept state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact .of_votes rfl

theorem votesKept_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : VotesKept state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact .of_votes rfl

theorem votesKept_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    VotesKept state after := by
  unfold exitQueue at computed
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact .of_votes rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact VotesKept.refl _

theorem votesKept_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : VotesKept state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, exitEpoch, withdrawableEpoch, queue, summed, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact VotesKept.refl _
  · exact (votesKept_exitQueue queue).trans (votesKept_setValidator set)

theorem votesKept_slashings (state : BeaconState preset fork) (slashings : RootedVector Gwei _) :
    VotesKept state { state with slashings } :=
  .of_votes rfl

/-- The last step of a slashing, which from Gloas cancels builder payments, keeps the history. -/
theorem votesKept_slashValidatorLast {last : BeaconState preset fork} {index : ValidatorIndex}
    (done : (pure (if gloas : .glamsterdam ≤ fork then cancelProposerPayments last gloas index
      else last) : Except AccessorError (BeaconState preset fork)) = .ok after) :
    VotesKept last after := by
  simp only [pure, Except.pure, Except.ok.injEq] at done
  subst done
  split
  · exact .of_votes rfl
  · exact VotesKept.refl _

theorem votesKept_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    VotesKept state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  refine (votesKept_initiateValidatorExit exitedOk).trans <|
    ((votesKept_setValidator markedOk).trans
      (votesKept_slashings _ _)).trans <|
    (votesKept_decreaseBalance loweredOk).trans <| (votesKept_increaseBalance raisedOk).trans <|
    (votesKept_increaseBalance lastOk).trans (votesKept_slashValidatorLast done)

/-! ## The steps of a block -/

theorem votesKept_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : VotesKept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_votes rfl

theorem votesKept_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : VotesKept state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_votes (congrArg BeaconState.votes rest :)

theorem votesKept_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    VotesKept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact votesKept_slashValidator slashed

theorem votesKept_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    VotesKept step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact votesKept_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ VotesKept.refl _

theorem votesKept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    VotesKept state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => VotesKept state step.1)
    (fun _ _ _ before ok => before.trans (votesKept_slashIfSlashable ok))
    (show VotesKept state (state, false).1 from VotesKept.refl state) folded

theorem votesKept_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    VotesKept state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · simp only [addValidatorToRegistryAltair, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, previous, previousOk, current, currentOk, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl, fun _ => flagsWithin_setOrAppendList previousOk,
      fun _ => flagsWithin_setOrAppendList currentOk⟩
  split at computed
  · cases computed
    exact .of_votes rfl
  · cases computed

theorem votesKept_applyDepositElectra {electra : .pectra ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials
      amount signature = .ok after) :
    VotesKept state after := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, added, pushed⟩ := computed
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
      exact (votesKept_addValidatorToRegistry added).trans
        (.of_votes rfl)
    · cases computed
      exact VotesKept.refl _
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    exact .of_votes rfl

theorem votesKept_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    VotesKept state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact VotesKept.refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact votesKept_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ VotesKept.refl _
  · rw [liftAccessor_ok] at computed
    exact votesKept_increaseBalance computed

theorem votesKept_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    VotesKept state after := by
  unfold applyDeposit at computed
  split at computed
  · exact votesKept_applyDepositElectra computed
  · exact votesKept_applyPendingDeposit computed

theorem votesKept_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    VotesKept state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (show VotesKept state { state with eth1DepositIndex := fun _ => next } from .of_votes rfl).trans
    (votesKept_applyDeposit applied)

theorem votesKept_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    VotesKept state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact votesKept_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem votesKept_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) : VotesKept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_votes rfl

theorem votesKept_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    VotesKept state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_votes rfl

theorem votesKept_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    VotesKept state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  cases computed
  exact .of_votes rfl

theorem votesKept_requestPartialWithdrawal {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    VotesKept state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (votesKept_computeExitEpochAndUpdateChurn churned).trans
      (.of_votes rfl)
  · cases computed
    exact VotesKept.refl _

theorem votesKept_processWithdrawalRequest {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    VotesKept state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact VotesKept.refl _)
    | exact votesKept_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact votesKept_requestPartialWithdrawal computed

theorem votesKept_queueExcessActiveBalance {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) : VotesKept state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_votes rfl
  · cases computed
    exact VotesKept.refl _

theorem votesKept_switchToCompoundingValidator {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    VotesKept state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨validator, found, _, set, queued⟩ := computed
  exact (votesKept_setValidator set).trans
    (votesKept_queueExcessActiveBalance queued)

theorem votesKept_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    VotesKept state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨churnedState, exitEpoch⟩, churned, withdrawable, ⟨_, sum⟩, _, set, _, _, computed⟩ :=
    computed
  simp only [Except.ok.injEq] at computed
  subst computed
  exact (votesKept_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (votesKept_setValidator (state := churnedState) set).trans (.of_votes rfl)

theorem votesKept_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    VotesKept state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact VotesKept.refl _)
    | exact votesKept_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact votesKept_queueConsolidation computed

theorem votesKept_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    VotesKept state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (VotesKept.foldlM (fun _ _ _ ok => votesKept_processDepositRequest ok) depositsOk).trans <|
    (VotesKept.foldlM (fun _ _ _ ok => votesKept_processWithdrawalRequest ok) withdrawalsOk).trans <|
    VotesKept.foldlM (fun _ _ _ ok => votesKept_processConsolidationRequest ok) consolidationsOk

/-! ## Withdrawals -/

theorem votesKept_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : VotesKept state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_votes rfl
  · exact votesKept_decreaseBalance computed

theorem votesKept_updateNextWithdrawalIndex {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalIndex state withdrawals = .ok after) : VotesKept state after := by
  unfold updateNextWithdrawalIndex at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact .of_votes rfl
  · cases computed
    exact VotesKept.refl _

theorem votesKept_updateNextWithdrawalValidatorIndex {capella : .shapella ≤ fork}
    {withdrawals : Array Withdrawal}
    (computed : updateNextWithdrawalValidatorIndex state capella withdrawals = .ok after) :
    VotesKept state after := by
  unfold updateNextWithdrawalValidatorIndex at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · cases computed
  · cases computed
    exact .of_votes rfl

theorem votesKept_updateNextWithdrawalBuilderIndex {gloas : .glamsterdam ≤ fork} {count : Nat}
    (computed : updateNextWithdrawalBuilderIndex state gloas count = .ok after) :
    VotesKept state after := by
  unfold updateNextWithdrawalBuilderIndex at computed
  dsimp only at computed
  split at computed
  · cases computed
    exact .of_votes rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact .of_votes rfl

theorem votesKept_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    VotesKept state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : VotesKept state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact VotesKept.foldlM (fun _ _ _ ok => votesKept_applyWithdrawal ok) appliedOk
  have queued : ∀ kept : BeaconState preset fork,
      VotesKept kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact .of_votes rfl
  have partials : ∀ kept : BeaconState preset fork,
      VotesKept kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact .of_votes rfl
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → VotesKept kept finished := by
    intro kept ok
    split at ok
    · exact votesKept_updateNextWithdrawalBuilderIndex ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ VotesKept.refl _
  exact one.trans <| (votesKept_updateNextWithdrawalIndex indexedOk).trans <| (queued _).trans <|
    (partials _).trans <| (swept _ sweptOk).trans (votesKept_updateNextWithdrawalValidatorIndex last)

theorem votesKept_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : VotesKept state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact votesKept_applyExpectedWithdrawals applied
    · cases computed
      exact VotesKept.refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact votesKept_applyExpectedWithdrawals applied

theorem votesKept_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    VotesKept state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact votesKept_setValidator set

/-! ## The parent payload and the execution part of a block -/

theorem votesKept_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    VotesKept state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_votes rfl

theorem votesKept_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    VotesKept state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .of_votes rfl)

theorem votesKept_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    VotesKept state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact VotesKept.refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_votes rfl

theorem votesKept_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : VotesKept state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact .of_votes rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;>
      exact .of_votes rfl

theorem votesKept_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    VotesKept state after := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact VotesKept.refl _
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
  exact (votesKept_settleParentPayment settledOk).trans <|
    (VotesKept.foldlM (fun _ _ _ ok => votesKept_processDepositRequest ok) depositsOk).trans <|
    (VotesKept.foldlM (fun _ _ _ ok => votesKept_processWithdrawalRequest ok) withdrawalsOk).trans <|
    (VotesKept.foldlM (fun _ _ _ ok => votesKept_processConsolidationRequest ok) consolidationsOk).trans <|
    (VotesKept.foldlM (fun _ _ _ ok => votesKept_processBuilderDepositRequest ok) buildersOk).trans <|
    (VotesKept.foldlM (fun _ _ _ ok => votesKept_processBuilderExitRequest ok) exitsOk).trans
      (.of_votes rfl)

theorem votesKept_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    VotesKept state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_votes rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_votes rfl

theorem votesKept_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    VotesKept state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (votesKept_processWithdrawals withdrawnOk).trans (votesKept_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (votesKept_processWithdrawals withdrawnOk).trans (votesKept_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact votesKept_processExecutionPayload computed
    · cases computed
      exact VotesKept.refl _

/-! ## The sync aggregate -/

theorem votesKept_applySyncReward {reward proposerReward : Gwei}
    {proposer : Except AccessorError ValidatorIndex} {member : ValidatorIndex × Bool}
    (computed : applySyncReward reward proposerReward proposer state member = .ok after) :
    VotesKept state after := by
  unfold applySyncReward at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, raised, _, _, paid⟩ := computed
    exact (votesKept_increaseBalance raised).trans (votesKept_increaseBalance paid)
  · exact votesKept_decreaseBalance (liftAccessor_ok.mp computed)

theorem votesKept_processSyncAggregate {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    VotesKept state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  exact VotesKept.foldlM (fun _ _ _ ok => votesKept_applySyncReward ok) folded

/-! ## Blocks -/

/-- Two states agree on what an attestation and a weighing read of history.

That is the slot, the block roots, and the two justified checkpoints. -/
structure SameReads (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  blockRoots : after.blockRoots = state.blockRoots
  previousJustifiedCheckpoint :
    after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint
  currentJustifiedCheckpoint : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint

theorem SameReads.trans {first second third : BeaconState preset fork}
    (one : SameReads first second) (two : SameReads second third) : SameReads first third :=
  ⟨two.slot.trans one.slot, two.blockRoots.trans one.blockRoots,
    two.previousJustifiedCheckpoint.trans one.previousJustifiedCheckpoint,
    two.currentJustifiedCheckpoint.trans one.currentJustifiedCheckpoint⟩

theorem Kept.sameReads (kept : Kept state after) : SameReads state after :=
  ⟨kept.slot, kept.blockRoots, kept.previousJustifiedCheckpoint, kept.currentJustifiedCheckpoint⟩

theorem sameReads_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : SameReads state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The operations of a block add votes only in their attestations.

The steps before the attestations and the steps after them add none. -/
theorem processOperations_votes {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ∃ before attested, VotesKept state before ∧ Kept state before ∧
      body.attestations.data.toList.foldlM (processAttestation config checks · parentSlot ·)
        before = .ok attested ∧
      VotesKept attested after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact ⟨_, _,
      (VotesKept.foldlM (fun _ _ _ ok => votesKept_processProposerSlashing ok) proposersOk).trans
        (VotesKept.foldlM (fun _ _ _ ok => votesKept_processAttesterSlashing ok) attestersOk),
      (Kept.foldlM (fun _ _ _ ok => kept_processProposerSlashing ok) proposersOk).trans
        (Kept.foldlM (fun _ _ _ ok => kept_processAttesterSlashing ok) attestersOk),
      attestedOk,
      (VotesKept.foldlM (fun _ _ _ ok => votesKept_processVoluntaryExit ok) exitsOk).trans <|
      (VotesKept.foldlM (fun _ _ _ ok => votesKept_processBlsToExecutionChange ok) changesOk).trans <|
      VotesKept.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact VotesKept.refl _) paid⟩
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : VotesKept exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact VotesKept.foldlM (fun _ _ _ ok => votesKept_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ VotesKept.refl _
  have requests : VotesKept changed after := by
    split at requestsOk
    · exact votesKept_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ VotesKept.refl _
  exact ⟨_, _,
    (VotesKept.foldlM (fun _ _ _ ok => votesKept_processProposerSlashing ok) proposersOk).trans
      (VotesKept.foldlM (fun _ _ _ ok => votesKept_processAttesterSlashing ok) attestersOk),
    (Kept.foldlM (fun _ _ _ ok => kept_processProposerSlashing ok) proposersOk).trans
      (Kept.foldlM (fun _ _ _ ok => kept_processAttesterSlashing ok) attestersOk),
    attestedOk,
    (VotesKept.foldlM (fun _ _ _ ok => votesKept_processDeposit ok) depositedOk).trans <|
    (VotesKept.foldlM (fun _ _ _ ok => votesKept_processVoluntaryExit ok) exitsOk).trans <|
    changes.trans requests⟩

/-- A block adds votes only in its attestations.

They run with the slot of the latest block before this one. -/
theorem processBlock_votes {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ∃ before attested, VotesKept state before ∧ SameReads state before ∧
      block.body.attestations.data.toList.foldlM
        (processAttestation config checks · state.latestBlockHeader.slot ·) before = .ok attested ∧
      VotesKept attested after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidVotes : VotesKept state paid := by
      split at paidOk
      · exact votesKept_processParentExecutionPayload paidOk
      · cases paidOk
        exact VotesKept.refl _
    have headedVotes : VotesKept paid headed := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
      exact .of_votes rfl
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedVotes : VotesKept headed executed := by
      split at executedOk
      · exact votesKept_processBlockExecution executedOk
      · cases executedOk
        exact VotesKept.refl _
    -- Heze drops the vote on the deposit contract.
    have votedVotes : VotesKept revealed voted := by
      split at votedOk
      · exact votesKept_processEth1Data votedOk
      · cases votedOk
        exact VotesKept.refl _
    obtain ⟨before, attested, head, headKept, folded, tail⟩ := processOperations_votes operatedOk
    -- Every step before the attestations keeps what they read.
    have reads : SameReads state voted := by
      have paidKept : Kept state paid := by
        split at paidOk
        · exact kept_processParentExecutionPayload paidOk
        · cases paidOk
          exact Kept.refl _
      have executedKept : Kept headed executed := by
        split at executedOk
        · exact kept_processBlockExecution executedOk
        · cases executedOk
          exact Kept.refl _
      have votedKept : Kept revealed voted := by
        split at votedOk
        · exact kept_processEth1Data votedOk
        · cases votedOk
          exact Kept.refl _
      exact paidKept.sameReads.trans <| (sameReads_processBlockHeader headedOk).trans <|
        (executedKept.trans <| (kept_processRandao revealedOk).trans votedKept).sameReads
    exact ⟨before, attested, paidVotes.trans <| headedVotes.trans <| executedVotes.trans <|
      (votesKept_processRandao revealedOk).trans <| votedVotes.trans head,
      reads.trans headKept.sameReads, folded, tail.trans (votesKept_processSyncAggregate synced)⟩
  simp only [bind_ok_iff] at computed
  obtain ⟨headed, headerOk, revealed, randaoOk, voted, eth1Ok, operationsOk⟩ := computed
  have headedVotes : VotesKept state headed := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    exact .of_votes rfl
  obtain ⟨before, attested, head, headKept, folded, tail⟩ := processOperations_votes operationsOk
  have reads : SameReads state voted := (sameReads_processBlockHeader headerOk).trans
    ((kept_processRandao randaoOk).trans (kept_processEth1Data eth1Ok)).sameReads
  exact ⟨before, attested, headedVotes.trans <| (votesKept_processRandao randaoOk).trans <|
    (votesKept_processEth1Data eth1Ok).trans head, reads.trans headKept.sameReads, folded, tail⟩

/-! ## The steps of an epoch -/

theorem votesKept_applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) : VotesKept state after := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, raised, lowered⟩ := computed
  exact (votesKept_increaseBalance raised).trans (votesKept_decreaseBalance lowered)

theorem votesKept_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : VotesKept state after :=
  VotesKept.foldlM (fun _ _ _ ok => votesKept_applyDeltas ok) computed

theorem votesKept_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) : VotesKept state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ VotesKept.refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact VotesKept.foldlM (fun _ _ _ ok => votesKept_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact votesKept_applyAllDeltas applied

theorem votesKept_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) : VotesKept state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set : VotesKept state marked := votesKept_setValidator markedOk
  split at computed
  · rw [liftAccessor_ok] at computed
    exact set.trans (votesKept_initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

theorem votesKept_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : VotesKept state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, set⟩ := computed
  exact votesKept_setValidator set

theorem votesKept_updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    VotesKept state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact votesKept_setValidator set
  split at computed
  · rw [liftAccessor_ok] at computed
    exact votesKept_initiateValidatorExit computed
  split at computed
  · rw [liftAccessor_ok] at computed
    exact votesKept_setValidator computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ VotesKept.refl _

theorem votesKept_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : VotesKept state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact VotesKept.foldlM (fun _ _ _ ok => votesKept_updateRegistryEntryElectra ok) computed
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  exact (VotesKept.foldlM (fun _ _ _ ok => votesKept_updateRegistryEntry ok) updatedOk).trans
    (VotesKept.foldlM (fun _ _ _ ok => votesKept_activateValidator ok) activated)

theorem votesKept_applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    VotesKept state after := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact votesKept_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ VotesKept.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ VotesKept.refl _

theorem votesKept_applySlashingPenaltyElectra {perIncrement : Gwei} {index : Nat}
    (computed : applySlashingPenaltyElectra state perIncrement index = .ok after) :
    VotesKept state after := by
  simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, lowered⟩ := computed
      exact votesKept_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ VotesKept.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ VotesKept.refl _

theorem votesKept_processSlashings (computed : processSlashings state = .ok after) :
    VotesKept state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact VotesKept.foldlM (fun _ _ _ ok => votesKept_applySlashingPenaltyElectra ok) applied
  · exact VotesKept.foldlM (fun _ _ _ ok => votesKept_applySlashingPenalty ok) computed

theorem votesKept_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) : VotesKept state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_votes rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ VotesKept.refl _

theorem votesKept_updateEffectiveBalance {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) : VotesKept state after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, _, _, _, _, set⟩ := computed
  exact votesKept_setValidator set

theorem votesKept_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : VotesKept state after := by
  unfold processEffectiveBalanceUpdates at computed
  exact VotesKept.foldlM (fun _ _ _ ok => votesKept_updateEffectiveBalance ok) computed

theorem votesKept_processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    VotesKept state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq computed
  exact votesKept_slashings _ _

theorem votesKept_processRandaoMixesReset (computed : processRandaoMixesReset state = .ok after) :
    VotesKept state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq computed
  exact .of_votes rfl

theorem votesKept_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : VotesKept state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_votes rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ VotesKept.refl _

/-- The end of an epoch moves the votes of the current epoch to the previous one.

The current epoch then has no vote: no pending attestation, and no flag. -/
structure RotatesVotes (state after : BeaconState preset fork) : Prop where
  previousEpochAttestations : ∀ before : fork < .altair,
    after.previousEpochAttestations before = state.currentEpochAttestations before
  currentEpochAttestations : ∀ before : fork < .altair,
    (after.currentEpochAttestations before).data = #[]
  previousEpochParticipation : ∀ altair : .altair ≤ fork,
    after.previousEpochParticipation altair = state.currentEpochParticipation altair
  currentEpochParticipation : ∀ altair : .altair ≤ fork,
    ∀ (index : Nat) (flags : ParticipationFlags),
      (after.currentEpochParticipation altair).data[index]? = some flags →
      flags = 0

theorem rotatesVotes_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    RotatesVotes state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact ⟨fun _ => rfl, fun _ => rfl, fun altair => absurd altair ‹_›,
    fun altair => absurd altair ‹_›⟩

/-! ## The steps of an epoch from Altair -/

theorem votesKept_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) : VotesKept state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ VotesKept.refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_votes rfl

theorem votesKept_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      VotesKept state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact VotesKept.refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact VotesKept.refl _
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (votesKept_applyPendingDeposit credited).trans
        (votesKept_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact votesKept_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact VotesKept.refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (votesKept_applyPendingDeposit credited).trans
      (votesKept_passPendingDeposits (deposits := rest) ‹_›)

theorem votesKept_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    VotesKept state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals
    exact (votesKept_passPendingDeposits ‹_›).trans
      (.of_votes rfl)

theorem votesKept_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      VotesKept state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact VotesKept.refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact votesKept_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact VotesKept.refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (votesKept_decreaseBalance loweredOk).trans <|
      (votesKept_increaseBalance raisedOk).trans
        (votesKept_passPendingConsolidations (result := (passed, read)) passedOk)

theorem votesKept_processPendingConsolidations {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) : VotesKept state after := by
  unfold processPendingConsolidations at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals
    exact (votesKept_passPendingConsolidations ‹_›).trans
      (.of_votes rfl)

theorem votesKept_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) : VotesKept state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    exact (votesKept_processPendingDeposits deposited).trans
      (votesKept_processPendingConsolidations consolidated)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ VotesKept.refl _

theorem votesKept_processBuilderPendingPayments {gloas : .glamsterdam ≤ fork}
    (computed : processBuilderPendingPayments state gloas = .ok after) : VotesKept state after := by
  simp only [processBuilderPendingPayments, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_votes rfl

theorem votesKept_processHistoricalSummariesUpdate {capella : .shapella ≤ fork}
    (computed : processHistoricalSummariesUpdate state capella = .ok after) :
    VotesKept state after := by
  unfold processHistoricalSummariesUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals first
    | exact VotesKept.refl _
    | exact .of_votes rfl

theorem rotatesVotes_processParticipationFlagUpdates (state : BeaconState preset fork)
    (altair : .altair ≤ fork) :
    RotatesVotes state (processParticipationFlagUpdates state altair) := by
  refine ⟨fun before => absurd altair (Nat.not_le_of_lt before),
    fun before => absurd altair (Nat.not_le_of_lt before), fun _ => rfl, ?_⟩
  intro _ index flags found
  simp only [processParticipationFlagUpdates, Array.getElem?_replicate] at found
  split at found
  · exact (Option.some.inj found).symm
  · cases found

theorem votesKept_processSyncCommitteeUpdates {altair : .altair ≤ fork}
    (computed : processSyncCommitteeUpdates state altair = .ok after) : VotesKept state after := by
  unfold processSyncCommitteeUpdates at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals first
    | exact VotesKept.refl _
    | exact .of_votes rfl

theorem votesKept_processProposerLookahead {fulu : .fusaka ≤ fork}
    (computed : processProposerLookahead state fulu = .ok after) : VotesKept state after := by
  simp only [processProposerLookahead, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact .of_votes rfl

theorem votesKept_processPtcWindow {gloas : .glamsterdam ≤ fork}
    (computed : processPtcWindow state gloas = .ok after) : VotesKept state after := by
  simp only [processPtcWindow, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact .of_votes rfl

/-- The steps that close an epoch from Altair, after the history. -/
private theorem votesKept_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) :
    VotesKept (processParticipationFlagUpdates rooted altair) after := by
  have lookedVotesKept : VotesKept synced looked := by
    split at lookedOk
    · exact votesKept_processProposerLookahead (liftAccessor_ok.mp lookedOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ VotesKept.refl _
  have windowedVotesKept : VotesKept looked after := by
    split at windowed
    · exact votesKept_processPtcWindow (liftAccessor_ok.mp windowed)
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ VotesKept.refl _
  exact (votesKept_processSyncCommitteeUpdates syncedOk).trans
    (lookedVotesKept.trans windowedVotesKept)

/-- Justification and finalization add no vote: they write only the bits and the checkpoints. -/
theorem votesKept_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) : VotesKept state after := by
  rcases processJustificationAndFinalization_ok computed with rfl | ⟨_, _, _, weighed⟩
  · exact VotesKept.refl _
  · have rest := (weighJustificationAndFinalization_checkpoints weighed).2.2.2
    exact .of_votes (congrArg BeaconState.votes rest :)

/-- From Altair, the epoch transition adds votes only when it rotates the flags. -/
theorem processEpochAltair_votes {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    ∃ before rotated, VotesKept state before ∧ RotatesVotes before rotated ∧
      VotesKept rotated after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetVotesKept : VotesKept slashed reset := by
    split at resetOk
    · exact votesKept_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ VotesKept.refl _
  have paidVotesKept : VotesKept pending paid := by
    split at paidOk
    · exact votesKept_processBuilderPendingPayments (liftAccessor_ok.mp paidOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ VotesKept.refl _
  have justifiedVotes : VotesKept state justified :=
    votesKept_processJustificationAndFinalization justifiedOk
  have head : VotesKept justified mixed :=
    (votesKept_processInactivityUpdates scoredOk).trans <|
    (votesKept_processRewardsAndPenalties rewardedOk).trans <|
    (votesKept_processRegistryUpdates registeredOk).trans <|
    (votesKept_processSlashings slashedOk).trans <|
    resetVotesKept.trans <|
    (votesKept_processPendingBalances pendingOk).trans <|
    paidVotesKept.trans <|
    (votesKept_processEffectiveBalanceUpdates balancedOk).trans <|
    (votesKept_processSlashingsReset clearedOk).trans <|
    (votesKept_processRandaoMixesReset mixedOk)
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · exact ⟨rooted, _, justifiedVotes.trans <| head.trans
        (votesKept_processHistoricalSummariesUpdate rootedOk),
      rotatesVotes_processParticipationFlagUpdates rooted altair,
      votesKept_epochEnd syncedOk lookedOk windowed⟩
  · exact ⟨rooted, _, justifiedVotes.trans <| head.trans
        (votesKept_processHistoricalRootsUpdate rootedOk),
      rotatesVotes_processParticipationFlagUpdates rooted altair,
      votesKept_epochEnd syncedOk lookedOk windowed⟩


/-- The epoch transition adds votes only when it rotates them, at every fork. -/
theorem processEpoch_votes (computed : processEpoch config checks state = .ok after) :
    ∃ before rotated, VotesKept state before ∧ RotatesVotes before rotated ∧
      VotesKept rotated after := by
  unfold processEpoch at computed
  split at computed
  · exact processEpochAltair_votes computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  exact ⟨rooted, after, (votesKept_processJustificationAndFinalization justifiedOk).trans <|
    (votesKept_processRewardsAndPenalties rewardedOk).trans <|
    (votesKept_processRegistryUpdates registeredOk).trans <|
    (votesKept_processSlashings slashedOk).trans <|
    (votesKept_processEth1DataReset resetOk).trans <|
    (votesKept_processEffectiveBalanceUpdates balancedOk).trans <|
    (votesKept_processSlashingsReset clearedOk).trans <|
    (votesKept_processRandaoMixesReset mixedOk).trans <|
    (votesKept_processHistoricalRootsUpdate rootedOk),
    rotatesVotes_processParticipationRecordUpdates rotated, VotesKept.refl _⟩

/-! ## Upgrades -/

theorem votesKept_queuePreActivation {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) : VotesKept state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, -, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  obtain ⟨_, rfl⟩ := setValidator_ok set₂
  exact .of_votes rfl

theorem votesKept_queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) : VotesKept state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · exact votesKept_queueExcessActiveBalance (liftAccessor_ok.mp computed)
    · cases computed
      exact VotesKept.refl _
  · cases computed
    exact VotesKept.refl _

/-- An upgrade from Altair on adds no flag: each list of flags carries over.

The upgrade from Phase 0 is the one that turns pending attestations into flags. -/
theorem upgradeNext_flags {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) (altair : .altair ≤ pre.fork) :
    FlagsWithin (pre.state.previousEpochParticipation altair).data
        (post.val.state.previousEpochParticipation (Nat.le_trans altair (Nat.le_of_lt post.2))).data ∧
      FlagsWithin (pre.state.currentEpochParticipation altair).data
        (post.val.state.currentEpochParticipation (Nat.le_trans altair (Nat.le_of_lt post.2))).data := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · exact absurd (show Fork.altair ≤ Fork.phase0 from altair) (by decide)
  · subst computed
    exact ⟨.refl _, .refl _⟩
  · subst computed
    exact ⟨.refl _, .refl _⟩
  · subst computed
    exact ⟨.refl _, .refl _⟩
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := upgraded
    have kept := (VotesKept.foldlM (fun _ _ _ ok => votesKept_queuePreActivation ok) queued).trans
      (VotesKept.foldlM (fun _ _ _ ok => votesKept_queueCompoundingExcess ok) compounded)
    exact ⟨kept.previousEpochParticipation _, kept.currentEpochParticipation _⟩
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    exact ⟨.refl _, .refl _⟩
  · obtain ⟨_, upgraded, rfl⟩ := computed
    unfold upgradeToGloas at upgraded
    obtain ⟨_, -, rest⟩ := bind_ok_iff.mp upgraded
    obtain ⟨_, -, onboarded⟩ := bind_ok_iff.mp rest
    obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    exact ⟨.refl _, .refl _⟩
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact ⟨.refl _, .refl _⟩

end EthLib.Consensus
