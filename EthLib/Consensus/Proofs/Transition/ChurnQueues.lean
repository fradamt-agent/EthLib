module

public import EthLib.Consensus.Proofs.Churn
public import EthLib.Consensus.Proofs.Transition.Reachable

/-!
# Proofs: the queues of exits and of consolidations, along every chain

From Electra a state holds two queues of balance, as [EIP-7251] specifies.

Exits wait in one, and consolidations in the other.

Each queue holds its earliest open epoch and the churn left at that epoch.

Only a request to the queue changes them, apart from the upgrade to Electra, which opens both.

So along every chain each queue's earliest open epoch never moves back.

The churn left is the part of an epoch's churn that later requests may still take.

It stays at most a cap whenever every churn of the fork is at most that cap.

Before Gloas the churn of exits is at most `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`.

The upgrade to Electra starts the churn left of exits at a churn of the state, also below it.

So in every reachable state before Gloas, the churn left of exits is at most that maximum.

Every run of exits from such a state then places at most that maximum per epoch.

The first exit of a range of epochs may also take churn from epochs before the range.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- The four fields of the two queues, from Electra. -/
def churnQueues (state : BeaconState preset fork) :
    Since .pectra fork (Epoch × Gwei × Epoch × Gwei) := fun electra =>
  (state.earliestExitEpoch electra, state.exitBalanceToConsume electra,
    state.earliestConsolidationEpoch electra, state.consolidationBalanceToConsume electra)

/-- Every churn of exits that a state of the fork computes is at most a cap. -/
def ExitChurnAtMost (config : Config) (preset : Preset) (fork : Base.Fork) (cap : Gwei) : Prop :=
  ∀ (state : BeaconState preset fork) (churn : Gwei),
    exitChurnLimit config state = .ok churn → churn ≤ cap

/-- Every churn of consolidations that a state of the fork computes is at most a cap. -/
def ConsolidationChurnAtMost (config : Config) (preset : Preset) (fork : Base.Fork) (cap : Gwei) :
    Prop :=
  ∀ (state : BeaconState preset fork) (churn : Gwei),
    getConsolidationChurnLimit config state = .ok churn → churn ≤ cap

/-- The queues of a later state of the same fork.

Each earliest open epoch is the same or later.

A churn left at most a cap stays at most the cap, when every churn of the fork is. -/
structure ChurnQueuesAdvance (config : Config) (state after : BeaconState preset fork) :
    Prop where
  exitEpoch : ∀ electra, state.earliestExitEpoch electra ≤ after.earliestExitEpoch electra
  consolidationEpoch : ∀ electra,
    state.earliestConsolidationEpoch electra ≤ after.earliestConsolidationEpoch electra
  exitLeft : ∀ cap, ExitChurnAtMost config preset fork cap → ∀ electra,
    state.exitBalanceToConsume electra ≤ cap → after.exitBalanceToConsume electra ≤ cap
  consolidationLeft : ∀ cap, ConsolidationChurnAtMost config preset fork cap → ∀ electra,
    state.consolidationBalanceToConsume electra ≤ cap →
      after.consolidationBalanceToConsume electra ≤ cap

namespace ChurnQueuesAdvance

theorem refl (state : BeaconState preset fork) : ChurnQueuesAdvance config state state :=
  ⟨fun _ => UInt64.le_refl _, fun _ => UInt64.le_refl _, fun _ _ _ => id, fun _ _ _ => id⟩

theorem trans {first second third : BeaconState preset fork}
    (one : ChurnQueuesAdvance config first second) (two : ChurnQueuesAdvance config second third) :
    ChurnQueuesAdvance config first third where
  exitEpoch electra := UInt64.le_trans (one.exitEpoch electra) (two.exitEpoch electra)
  consolidationEpoch electra :=
    UInt64.le_trans (one.consolidationEpoch electra) (two.consolidationEpoch electra)
  exitLeft cap bounded electra :=
    two.exitLeft cap bounded electra ∘ one.exitLeft cap bounded electra
  consolidationLeft cap bounded electra :=
    two.consolidationLeft cap bounded electra ∘ one.consolidationLeft cap bounded electra

/-- A step that keeps both queues. -/
theorem of_eq (same : churnQueues after = churnQueues state) : ChurnQueuesAdvance config state after
    := by
  have field := congrFun same
  simp only [churnQueues, Prod.mk.injEq] at field
  exact ⟨fun electra => (field electra).1 ▸ UInt64.le_refl _,
    fun electra => (field electra).2.2.1 ▸ UInt64.le_refl _,
    fun _ _ electra => (field electra).2.1 ▸ id,
    fun _ _ electra => (field electra).2.2.2 ▸ id⟩

/-- A fold whose every step advances the queues advances them. -/
theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → ChurnQueuesAdvance config s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : ChurnQueuesAdvance config state after :=
  foldlM_ok_invariant (ChurnQueuesAdvance config state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

theorem setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : ChurnQueuesAdvance config state after
    := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact .of_eq rfl

theorem setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : ChurnQueuesAdvance config state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact .of_eq rfl

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    ChurnQueuesAdvance config state after :=
  have ⟨_, set⟩ := increaseBalance_ok computed
  .setBalance set

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) :
    ChurnQueuesAdvance config state after :=
  have ⟨_, set⟩ := decreaseBalance_ok computed
  .setBalance set

end ChurnQueuesAdvance

/-! ## The two requests to a queue -/

/-- An exit moves the queue of exits to the epoch it gets, or keeps it there.

The churn left after it is at most a cap that bounds the churn left before and the churn. -/
theorem churnQueuesAdvance_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨_, churn, _, _, churnOk, queued, rfl⟩ := computeExitEpochAndUpdateChurn_eq computed
  have moved := (churnQueue_cap (cap := 2 ^ 64) (Nat.le_of_lt (UInt64.toNat_lt _))
    (Nat.le_of_lt (UInt64.toNat_lt _)) queued).2.1
  refine ⟨fun _ => moved, fun _ => UInt64.le_refl _, fun cap bounded _ leftLe => ?_,
    fun _ _ _ => id⟩
  have churnLe := UInt64.le_iff_toNat_le.mp (bounded state churn churnOk)
  exact UInt64.le_iff_toNat_le.mpr
    (churnQueue_cap (UInt64.le_iff_toNat_le.mp leftLe) churnLe queued).1

/-- A consolidation moves the queue of consolidations to the epoch it gets, or keeps it there.

The churn left after it is at most a cap that bounds the churn left before and the churn. -/
theorem churnQueuesAdvance_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨_, churn, _, _, churnOk, queued, rfl⟩ :=
    computeConsolidationEpochAndUpdateChurn_eq computed
  have moved := (churnQueue_cap (cap := 2 ^ 64) (Nat.le_of_lt (UInt64.toNat_lt _))
    (Nat.le_of_lt (UInt64.toNat_lt _)) queued).2.1
  refine ⟨fun _ => UInt64.le_refl _, fun _ => moved, fun _ _ _ => id,
    fun cap bounded _ leftLe => ?_⟩
  have churnLe := UInt64.le_iff_toNat_le.mp (bounded state churn churnOk)
  exact UInt64.le_iff_toNat_le.mpr
    (churnQueue_cap (UInt64.le_iff_toNat_le.mp leftLe) churnLe queued).1

/-! ## Mutators -/

theorem churnQueuesAdvance_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    ChurnQueuesAdvance config state after := by
  unfold exitQueue at computed
  split at computed
  · exact churnQueuesAdvance_computeExitEpochAndUpdateChurn computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact .refl _

theorem churnQueuesAdvance_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact .refl _
  · exact (churnQueuesAdvance_exitQueue queue).trans (.setValidator set)

theorem churnQueuesAdvance_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  have final : ChurnQueuesAdvance config last after := by
    simp only [pure, Except.pure, Except.ok.injEq] at done
    subst done
    split
    · exact .of_eq rfl
    · exact .refl _
  exact (churnQueuesAdvance_initiateValidatorExit exitedOk).trans <|
    ((ChurnQueuesAdvance.setValidator markedOk).trans (by exact .of_eq rfl)).trans <|
    (ChurnQueuesAdvance.decreaseBalance loweredOk).trans <|
    (ChurnQueuesAdvance.increaseBalance raisedOk).trans <|
    (ChurnQueuesAdvance.increaseBalance lastOk).trans final

/-! ## The steps of a block -/

theorem churnQueuesAdvance_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_eq rfl

theorem churnQueuesAdvance_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_eq rfl

theorem churnQueuesAdvance_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_eq (by rw [← rest]; rfl)

theorem churnQueuesAdvance_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact churnQueuesAdvance_slashValidator slashed

theorem churnQueuesAdvance_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    ChurnQueuesAdvance config step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact churnQueuesAdvance_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem churnQueuesAdvance_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => ChurnQueuesAdvance config state step.1)
    (fun _ _ _ before ok => before.trans (churnQueuesAdvance_slashIfSlashable ok))
    (show ChurnQueuesAdvance config state (state, false).1 from .refl state) folded

theorem churnQueuesAdvance_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : ChurnQueuesAdvance config raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_eq rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        ChurnQueuesAdvance config state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_eq rfl
    exact (flagged _ _).trans ((ChurnQueuesAdvance.increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact .of_eq (by rw [← rest]; rfl)

theorem churnQueuesAdvance_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact .of_eq rfl
  · split at computed
    · cases computed
      exact .of_eq rfl
    · cases computed

theorem churnQueuesAdvance_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact churnQueuesAdvance_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · rw [liftAccessor_ok] at computed
    exact .increaseBalance computed

theorem churnQueuesAdvance_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    ChurnQueuesAdvance config state after := by
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
        exact (churnQueuesAdvance_addValidatorToRegistry added).trans (.of_eq rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_eq rfl
  · exact churnQueuesAdvance_applyPendingDeposit computed

theorem churnQueuesAdvance_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (ChurnQueuesAdvance.of_eq (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (churnQueuesAdvance_applyDeposit applied)

theorem churnQueuesAdvance_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact churnQueuesAdvance_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem churnQueuesAdvance_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_eq rfl

theorem churnQueuesAdvance_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (churnQueuesAdvance_computeExitEpochAndUpdateChurn churned).trans (.of_eq rfl)
  · cases computed
    exact .refl _

theorem churnQueuesAdvance_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact churnQueuesAdvance_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact churnQueuesAdvance_requestPartialWithdrawal computed

theorem churnQueuesAdvance_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_eq rfl
  · cases computed
    exact .refl _

theorem churnQueuesAdvance_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  exact (ChurnQueuesAdvance.setValidator set).trans
    (churnQueuesAdvance_queueExcessActiveBalance queued)

theorem churnQueuesAdvance_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  exact (churnQueuesAdvance_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (ChurnQueuesAdvance.setValidator set).trans (.of_eq rfl)

theorem churnQueuesAdvance_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact churnQueuesAdvance_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact churnQueuesAdvance_queueConsolidation computed

theorem churnQueuesAdvance_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_processDepositRequest ok)
      depositsOk).trans <|
    (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    ChurnQueuesAdvance.foldlM
      (fun _ _ _ ok => churnQueuesAdvance_processConsolidationRequest ok) consolidationsOk

/-! ## Withdrawals -/

theorem churnQueuesAdvance_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_eq rfl
  · exact .decreaseBalance computed

theorem churnQueuesAdvance_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : ChurnQueuesAdvance config state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_applyWithdrawal ok)
      appliedOk
  have two : ChurnQueuesAdvance config applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_eq rfl
    · cases indexedOk
      exact .refl _
  have queued : ∀ kept : BeaconState preset fork,
      ChurnQueuesAdvance config kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_eq rfl
    · exact .refl _
  have partials : ∀ kept : BeaconState preset fork,
      ChurnQueuesAdvance config kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_eq rfl
    · exact .refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → ChurnQueuesAdvance config kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact .of_eq rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  have lastKept : ChurnQueuesAdvance config finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact .of_eq rfl
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

theorem churnQueuesAdvance_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact churnQueuesAdvance_applyExpectedWithdrawals applied
    · cases computed
      exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact churnQueuesAdvance_applyExpectedWithdrawals applied

theorem churnQueuesAdvance_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact .setValidator set

/-! ## The parent payload and the execution part of a block -/

theorem churnQueuesAdvance_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_eq rfl

theorem churnQueuesAdvance_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .of_eq rfl)

theorem churnQueuesAdvance_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    ChurnQueuesAdvance config state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_eq rfl

theorem churnQueuesAdvance_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact .of_eq rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;> exact .of_eq rfl

theorem churnQueuesAdvance_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    ChurnQueuesAdvance config state after := by
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
  exact (churnQueuesAdvance_settleParentPayment settledOk).trans <|
    (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_processDepositRequest ok)
      depositsOk).trans <|
    (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    (ChurnQueuesAdvance.foldlM
      (fun _ _ _ ok => churnQueuesAdvance_processConsolidationRequest ok) consolidationsOk).trans <|
    (ChurnQueuesAdvance.foldlM
      (fun _ _ _ ok => churnQueuesAdvance_processBuilderDepositRequest ok) buildersOk).trans <|
    (ChurnQueuesAdvance.foldlM
      (fun _ _ _ ok => churnQueuesAdvance_processBuilderExitRequest ok) exitsOk).trans
      (.of_eq rfl)

theorem churnQueuesAdvance_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    ChurnQueuesAdvance config state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_eq rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_eq rfl

theorem churnQueuesAdvance_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (churnQueuesAdvance_processWithdrawals withdrawnOk).trans
      (churnQueuesAdvance_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (churnQueuesAdvance_processWithdrawals withdrawnOk).trans
      (churnQueuesAdvance_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact churnQueuesAdvance_processExecutionPayload computed
    · cases computed
      exact .refl _

/-! ## The sync aggregate -/

theorem churnQueuesAdvance_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine ChurnQueuesAdvance.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (ChurnQueuesAdvance.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

/-! ## Blocks -/

theorem churnQueuesAdvance_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (ChurnQueuesAdvance.foldlM
        (fun _ _ _ ok => churnQueuesAdvance_processProposerSlashing ok) proposersOk).trans <|
      (ChurnQueuesAdvance.foldlM
        (fun _ _ _ ok => churnQueuesAdvance_processAttesterSlashing ok) attestersOk).trans <|
      (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_processAttestation ok)
        attestedOk).trans <|
      (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_processVoluntaryExit ok)
        exitsOk).trans <|
      (ChurnQueuesAdvance.foldlM
        (fun _ _ _ ok => churnQueuesAdvance_processBlsToExecutionChange ok) changesOk).trans <|
      ChurnQueuesAdvance.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : ChurnQueuesAdvance config exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact ChurnQueuesAdvance.foldlM
        (fun _ _ _ ok => churnQueuesAdvance_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : ChurnQueuesAdvance config changed after := by
    split at requestsOk
    · exact churnQueuesAdvance_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  exact (ChurnQueuesAdvance.foldlM
      (fun _ _ _ ok => churnQueuesAdvance_processProposerSlashing ok) proposersOk).trans <|
    (ChurnQueuesAdvance.foldlM
      (fun _ _ _ ok => churnQueuesAdvance_processAttesterSlashing ok) attestersOk).trans <|
    (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_processAttestation ok)
      attestedOk).trans <|
    (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_processDeposit ok)
      depositedOk).trans <|
    (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_processVoluntaryExit ok)
      exitsOk).trans <|
    changes.trans requests

theorem churnQueuesAdvance_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    have paidKept : ChurnQueuesAdvance config state paid := by
      split at paidOk
      · exact churnQueuesAdvance_processParentExecutionPayload paidOk
      · cases paidOk
        exact .refl _
    have executedKept : ChurnQueuesAdvance config headed executed := by
      split at executedOk
      · exact churnQueuesAdvance_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    have votedKept : ChurnQueuesAdvance config revealed voted := by
      split at votedOk
      · exact churnQueuesAdvance_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    exact paidKept.trans <| (churnQueuesAdvance_processBlockHeader headedOk).trans <|
      executedKept.trans <| (churnQueuesAdvance_processRandao revealedOk).trans <|
      votedKept.trans <| (churnQueuesAdvance_processOperations operatedOk).trans
        (churnQueuesAdvance_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (churnQueuesAdvance_processBlockHeader headerOk).trans <|
    (churnQueuesAdvance_processRandao randaoOk).trans <|
    (churnQueuesAdvance_processEth1Data eth1Ok).trans
      (churnQueuesAdvance_processOperations operationsOk)

/-! ## The steps of an epoch -/

theorem churnQueuesAdvance_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    ChurnQueuesAdvance config state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_eq (by rw [← rest]; rfl)

theorem churnQueuesAdvance_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : ChurnQueuesAdvance config state after :=
  ChurnQueuesAdvance.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (ChurnQueuesAdvance.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem churnQueuesAdvance_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact churnQueuesAdvance_applyAllDeltas applied

theorem churnQueuesAdvance_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, marked, markedOk, computed⟩ := computed
  have set := ChurnQueuesAdvance.setValidator (config := config) markedOk
  split at computed
  · exact set.trans (churnQueuesAdvance_initiateValidatorExit (liftAccessor_ok.mp computed))
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

theorem churnQueuesAdvance_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, set⟩ := computed
  exact .setValidator set

theorem churnQueuesAdvance_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine ChurnQueuesAdvance.foldlM (fun state _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact .setValidator set
    split at ok
    · exact churnQueuesAdvance_initiateValidatorExit (liftAccessor_ok.mp ok)
    split at ok
    · rw [liftAccessor_ok] at ok
      exact .setValidator ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, updatedOk, activated⟩ := computed
  exact (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_updateRegistryEntry ok)
    updatedOk).trans
    (ChurnQueuesAdvance.foldlM (fun _ _ _ ok => churnQueuesAdvance_activateValidator ok)
      activated)

theorem churnQueuesAdvance_processSlashings (computed : processSlashings state = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine ChurnQueuesAdvance.foldlM (fun _ _ _ ok => ?_) applied
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
  · refine ChurnQueuesAdvance.foldlM (fun _ _ _ ok => ?_) computed
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

theorem churnQueuesAdvance_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_eq rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem churnQueuesAdvance_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine ChurnQueuesAdvance.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, set⟩ := ok
  exact .setValidator set

theorem churnQueuesAdvance_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_eq rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem churnQueuesAdvance_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_eq rfl

/-! ## The steps of an epoch from Altair -/

theorem churnQueuesAdvance_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_eq rfl

theorem churnQueuesAdvance_passPendingDeposits {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      ChurnQueuesAdvance config state pass.1.state
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
      exact (churnQueuesAdvance_applyPendingDeposit credited).trans
        (churnQueuesAdvance_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact churnQueuesAdvance_passPendingDeposits (deposits := rest) ‹_›
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
    exact (churnQueuesAdvance_applyPendingDeposit credited).trans
      (churnQueuesAdvance_passPendingDeposits (deposits := rest) ‹_›)

theorem churnQueuesAdvance_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (churnQueuesAdvance_passPendingDeposits ‹_›).trans (.of_eq rfl)

theorem churnQueuesAdvance_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      ChurnQueuesAdvance config state result.1
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
      exact churnQueuesAdvance_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (ChurnQueuesAdvance.decreaseBalance loweredOk).trans <|
      (ChurnQueuesAdvance.increaseBalance raisedOk).trans
        (churnQueuesAdvance_passPendingConsolidations (result := (passed, read)) passedOk)

theorem churnQueuesAdvance_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine (churnQueuesAdvance_processPendingDeposits deposited).trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (churnQueuesAdvance_passPendingConsolidations ‹_›).trans (.of_eq rfl)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- The steps that close an epoch from Altair, after the history. -/
private theorem churnQueuesAdvance_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : ChurnQueuesAdvance config rooted after := by
  have syncedKept : ChurnQueuesAdvance config rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact .of_eq rfl
  have lookedKept : ChurnQueuesAdvance config synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedKept : ChurnQueuesAdvance config looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedKept.trans (lookedKept.trans windowedKept)

theorem churnQueuesAdvance_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetKept : ChurnQueuesAdvance config slashed reset := by
    split at resetOk
    · exact churnQueuesAdvance_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ .refl _
  have paidKept : ChurnQueuesAdvance config pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ .refl _
  have clearedKept : ChurnQueuesAdvance config balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_eq rfl
  have mixedKept : ChurnQueuesAdvance config cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_eq rfl
  have head : ChurnQueuesAdvance config state mixed :=
    (churnQueuesAdvance_processJustificationAndFinalization justifiedOk).trans <|
    (churnQueuesAdvance_processInactivityUpdates scoredOk).trans <|
    (churnQueuesAdvance_processRewardsAndPenalties rewardedOk).trans <|
    (churnQueuesAdvance_processRegistryUpdates registeredOk).trans <|
    (churnQueuesAdvance_processSlashings slashedOk).trans <|
    resetKept.trans <|
    (churnQueuesAdvance_processPendingBalances pendingOk).trans <|
    paidKept.trans <|
    (churnQueuesAdvance_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans mixedKept
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · have rootedKept : ChurnQueuesAdvance config mixed rooted := by
      unfold processHistoricalSummariesUpdate at rootedOk
      simp only [bind, Except.bind, pure, Except.pure] at rootedOk
      repeat' (split at rootedOk <;> try cases rootedOk)
      all_goals first
        | exact .refl _
        | exact .of_eq rfl
    exact head.trans <| rootedKept.trans (churnQueuesAdvance_epochEnd syncedOk lookedOk windowed)
  · exact head.trans <| (churnQueuesAdvance_processHistoricalRootsUpdate rootedOk).trans
      (churnQueuesAdvance_epochEnd syncedOk lookedOk windowed)

theorem churnQueuesAdvance_processEpoch
    (computed : processEpoch config checks state = .ok after) :
    ChurnQueuesAdvance config state after := by
  unfold processEpoch at computed
  split at computed
  · exact churnQueuesAdvance_processEpochAltair computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have clearedKept : ChurnQueuesAdvance config balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_eq rfl
  have mixedKept : ChurnQueuesAdvance config cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_eq rfl
  exact (churnQueuesAdvance_processJustificationAndFinalization justifiedOk).trans <|
    (churnQueuesAdvance_processRewardsAndPenalties rewardedOk).trans <|
    (churnQueuesAdvance_processRegistryUpdates registeredOk).trans <|
    (churnQueuesAdvance_processSlashings slashedOk).trans <|
    (churnQueuesAdvance_processEth1DataReset resetOk).trans <|
    (churnQueuesAdvance_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans <| mixedKept.trans <|
    (churnQueuesAdvance_processHistoricalRootsUpdate rootedOk).trans
      (churnQueuesAdvance_processParticipationRecordUpdates rotated)

theorem churnQueuesAdvance_advanceSlot
    (computed : advanceSlot config checks state = .ok after) :
    ChurnQueuesAdvance config state after := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedKept : ChurnQueuesAdvance config state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact .of_eq rfl
  have epochedKept : ChurnQueuesAdvance config cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact churnQueuesAdvance_processEpoch epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ .refl _
  exact cachedKept.trans (epochedKept.trans (.of_eq rfl))

/-! ## Upgrades and chains -/

/-- Queueing a validator that is not yet active keeps both queues. -/
theorem churnQueues_queuePreActivation {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    churnQueues after = churnQueues state := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  obtain ⟨_, rfl⟩ := setValidator_ok set₂
  rfl

/-- Queueing the excess balance of a compounding validator keeps both queues. -/
theorem churnQueues_queueCompoundingExcess {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    churnQueues after = churnQueues state := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · simp only [queueExcessActiveBalance, liftAccessor_ok, bind_ok_iff] at computed
      obtain ⟨_, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
        obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
        obtain ⟨_, rfl⟩ := setBalance_ok set
        rfl
      · cases computed
        rfl
    · cases computed
      rfl
  · cases computed
    rfl

/-- A fold whose every step keeps both queues keeps them. -/
private theorem churnQueues_foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → churnQueues s' = churnQueues s) {items : List α}
    (computed : items.foldlM step state = .ok after) : churnQueues after = churnQueues state :=
  foldlM_ok_invariant (fun current => churnQueues current = churnQueues state)
    (fun _ _ _ before ok => (kept _ _ _ ok).trans before) rfl computed

/-- The upgrade to Electra opens the queue of exits with the churn of exits of a state.

So its churn left is at most the configured maximum of activations and exits. -/
theorem upgradeToElectra_exitBalanceToConsume_le {pre : BeaconState preset .dencun}
    {post : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok post) :
    post.exitBalanceToConsume (by decide) ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT := by
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨_, -, _, -, exitChurn, exitChurnOk, _, -, _, queued, compounded⟩ := computed
  have queuedKept := churnQueues_foldlM (fun _ _ _ ok => churnQueues_queuePreActivation ok) queued
  have compoundedKept :=
    churnQueues_foldlM (fun _ _ _ ok => churnQueues_queueCompoundingExcess ok) compounded
  have same := congrArg (fun queues => (queues (by decide)).2.1)
    (compoundedKept.trans queuedKept)
  simp only [churnQueues] at same
  rw [same]
  exact getActivationExitChurnLimit_le (liftAccessor_ok.mp exitChurnOk)

/-- Before Gloas, the churn left of exits is at most the maximum of activations and exits.

Earlier forks have no queue, so they satisfy it vacuously. -/
def ExitLeftBounded (config : Config) (forked : ForkedBeaconState preset) : Prop :=
  forked.fork < .glamsterdam → ∀ electra,
    forked.state.exitBalanceToConsume electra ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT

/-- The queues of a later state, which may be of a later fork.

Each earliest open epoch is the same or later, once both states have the queue.

Before Gloas, the churn left of exits stays at most the maximum of activations and exits. -/
structure ForkedChurnQueues (config : Config) (forked after : ForkedBeaconState preset) :
    Prop where
  fork_le : forked.fork ≤ after.fork
  exitEpoch : ∀ electra electra',
    forked.state.earliestExitEpoch electra ≤ after.state.earliestExitEpoch electra'
  consolidationEpoch : ∀ electra electra',
    forked.state.earliestConsolidationEpoch electra ≤
      after.state.earliestConsolidationEpoch electra'
  exitLeft : ExitLeftBounded config forked → ExitLeftBounded config after

/-- A step within one fork. -/
theorem ChurnQueuesAdvance.forked {fork : Base.Fork} {state after : BeaconState preset fork}
    (advance : ChurnQueuesAdvance config state after) :
    ForkedChurnQueues config ⟨fork, state⟩ ⟨fork, after⟩ where
  fork_le := Nat.le_refl _
  exitEpoch electra _ := advance.exitEpoch electra
  consolidationEpoch electra _ := advance.consolidationEpoch electra
  exitLeft bounded before electra :=
    advance.exitLeft _ (fun _ _ computed => exitChurnLimit_le_of_lt before computed) electra
      (bounded before electra)

/-- An upgrade from a fork before Electra, to a state whose churn left of exits is bounded. -/
private theorem forkedChurnQueues_of_before {fork' : Base.Fork} {state : BeaconState preset fork}
    {post : BeaconState preset fork'} (early : fork < .pectra) (upgrade : fork < fork')
    (bounded : ExitLeftBounded config ⟨fork', post⟩) :
    ForkedChurnQueues config ⟨fork, state⟩ ⟨fork', post⟩ :=
  ⟨Nat.le_of_lt upgrade, fun electra => absurd electra (Nat.not_le_of_lt early),
    fun electra => absurd electra (Nat.not_le_of_lt early), fun _ => bounded⟩

/-- An upgrade that carries both queues. -/
private theorem forkedChurnQueues_of_carried {fork' : Base.Fork} {state : BeaconState preset fork}
    {post : BeaconState preset fork'} (electra : .pectra ≤ fork) (upgrade : fork ≤ fork')
    (exits : ∀ electra electra', post.earliestExitEpoch electra' = state.earliestExitEpoch electra)
    (consolidations : ∀ electra electra',
      post.earliestConsolidationEpoch electra' = state.earliestConsolidationEpoch electra)
    (left : fork' < .glamsterdam → ∀ electra electra',
      post.exitBalanceToConsume electra' = state.exitBalanceToConsume electra) :
    ForkedChurnQueues config ⟨fork, state⟩ ⟨fork', post⟩ where
  fork_le := upgrade
  exitEpoch electra electra' := (exits electra electra').symm ▸ UInt64.le_refl _
  consolidationEpoch electra electra' := (consolidations electra electra').symm ▸ UInt64.le_refl _
  exitLeft bounded later electra' := by
    rw [left later electra electra']
    exact bounded (Nat.lt_of_le_of_lt upgrade later) electra

/-- An upgrade carries both queues, or opens them at Electra.

The upgrade to Electra opens the queue of exits with a churn of the new state. -/
theorem forkedChurnQueues_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    ForkedChurnQueues config pre post.val := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  -- Before Electra no state has the queues.
  · obtain ⟨_, _, rfl⟩ := computed
    exact forkedChurnQueues_of_before (by decide) (by decide)
      fun _ electra => absurd electra (by simp only; decide)
  · subst computed
    exact forkedChurnQueues_of_before (by decide) (by decide)
      fun _ electra => absurd electra (by simp only; decide)
  · subst computed
    exact forkedChurnQueues_of_before (by decide) (by decide)
      fun _ electra => absurd electra (by simp only; decide)
  · subst computed
    exact forkedChurnQueues_of_before (by decide) (by decide)
      fun _ electra => absurd electra (by simp only; decide)
  -- The upgrade to Electra opens the queues.
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact forkedChurnQueues_of_before (by decide) (by decide)
      fun _ _ => upgradeToElectra_exitBalanceToConsume_le upgraded
  -- Later upgrades carry both queues.
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    exact forkedChurnQueues_of_carried (by decide) (by decide) (fun _ _ => rfl) (fun _ _ => rfl)
      fun _ _ _ => rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToGloas, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, onboarded⟩ := upgraded
    obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    exact forkedChurnQueues_of_carried (by decide) (by decide) (fun _ _ => rfl) (fun _ _ => rfl)
      fun later => absurd later (by decide)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact forkedChurnQueues_of_carried (by decide) (by decide) (fun _ _ => rfl) (fun _ _ => rfl)
      fun later => absurd later (by decide)

/-- Every step of a chain advances both queues. -/
theorem stepRelation_churnQueues :
    StepRelation config checks fun (forked after : ForkedBeaconState preset) =>
      ForkedChurnQueues config forked after where
  refl forked := (ChurnQueuesAdvance.refl forked.state).forked
  trans one two := {
    fork_le := Nat.le_trans one.fork_le two.fork_le
    exitEpoch := fun electra electra' =>
      UInt64.le_trans (one.exitEpoch electra (Nat.le_trans electra one.fork_le))
        (two.exitEpoch _ electra')
    consolidationEpoch := fun electra electra' =>
      UInt64.le_trans (one.consolidationEpoch electra (Nat.le_trans electra one.fork_le))
        (two.consolidationEpoch _ electra')
    exitLeft := two.exitLeft ∘ one.exitLeft }
  advanceSlot computed := (churnQueuesAdvance_advanceSlot computed).forked
  upgradeNext _ computed := forkedChurnQueues_upgradeNext computed
  applySignedBlock computed :=
    (churnQueuesAdvance_processBlock (applySignedBlock_ok computed).2.1).forked

/-- Along every chain, the earliest exit epoch never moves back, once the queue exists. -/
theorem Reaches.earliestExitEpoch_le {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) (electra : .pectra ≤ start.fork)
    (electra' : .pectra ≤ after.fork) :
    start.state.earliestExitEpoch electra ≤ after.state.earliestExitEpoch electra' :=
  (stepRelation_churnQueues.reaches chain).exitEpoch electra electra'

/-- Along every chain, the earliest consolidation epoch never moves back, once the queue exists.
-/
theorem Reaches.earliestConsolidationEpoch_le {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) (electra : .pectra ≤ start.fork)
    (electra' : .pectra ≤ after.fork) :
    start.state.earliestConsolidationEpoch electra ≤
      after.state.earliestConsolidationEpoch electra' :=
  (stepRelation_churnQueues.reaches chain).consolidationEpoch electra electra'

/-- In every reachable state before Gloas, the churn left of exits is within the maximum.

The maximum is `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`, which caps the churn of exits.

A genesis state is of Phase 0, which has no queue. -/
theorem Reachable.exitBalanceToConsume_le {forked : ForkedBeaconState preset}
    (reachable : Reachable config checks forked) (electra : .pectra ≤ forked.fork)
    (before : forked.fork < .glamsterdam) :
    forked.state.exitBalanceToConsume electra ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT
    := by
  obtain ⟨start, ⟨⟨_, _, _, initialized⟩, _⟩, chain⟩ := reachable
  -- Genesis runs only at Phase 0, so the genesis state has no queue.
  have early : start.fork < .altair := by
    unfold initializeBeaconStateFromEth1 at initialized
    split at initialized
    · cases initialized
    · exact Nat.lt_of_not_le ‹_›
  have genesis : ExitLeftBounded config start :=
    fun _ electra => absurd (Nat.lt_of_le_of_lt electra early) (by decide)
  exact (stepRelation_churnQueues.reaches chain).exitLeft genesis before electra

/-- Exits in turn from a reachable state before Gloas.

Take a range of `stop - start` epochs, and every exit placed in it but the first.

Those exits take at most `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` per epoch of the range.

The first exit in the range may also take churn from epochs before the range.

Each request must have a churn of exits of a state of the same fork, as every exit does. -/
theorem Reachable.exitTrace_window {forked : ForkedBeaconState preset}
    (reachable : Reachable config checks forked) (electra : .pectra ≤ forked.fork)
    (before : forked.fork < .glamsterdam) {placements : List (ChurnRequest × Epoch)}
    {lastEpoch lastLeft : Epoch}
    (trace : ChurnTrace (forked.state.earliestExitEpoch electra)
      (forked.state.exitBalanceToConsume electra) placements lastEpoch lastLeft)
    (churns : ∀ placement ∈ placements, ∃ other : BeaconState preset forked.fork,
      exitChurnLimit config other = .ok placement.1.perEpochChurn)
    (start stop : Epoch) :
    (((placements.filter fun placement =>
        decide (start < placement.2) && decide (placement.2 ≤ stop)).tail).map
      fun placement => placement.1.amount.toNat).sum ≤
      (stop.toNat - start.toNat) * config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat :=
  trace.window_tail_le
    (UInt64.le_iff_toNat_le.mp (reachable.exitBalanceToConsume_le electra before))
    (fun placement member =>
      have ⟨_, churn⟩ := churns placement member
      UInt64.le_iff_toNat_le.mp (exitChurnLimit_le_of_lt before churn))
    start stop

end EthLib.Consensus
