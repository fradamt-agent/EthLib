module

public import EthLib.Consensus.Proofs.Transition.Cohorts
public import EthLib.Consensus.Proofs.Transition.EpochParticipation
public import EthLib.Consensus.Proofs.Transition.EpochPending
public import EthLib.Consensus.Proofs.Transition.Provenance.Kept
public import EthLib.Consensus.Proofs.Transition.SyncAggregate

/-!
# Proofs: how fast the registry grows, at every fork

Only one function adds a validator to the registry, `addValidatorToRegistry`.

It adds at most one, and three kinds of step call it.

- A deposit of a block, before Fulu, for a key that no validator has.
- From Electra, a pending deposit that the epoch applies, for a key that no validator has.
- Nothing else: a deposit request only queues a pending deposit, as [EIP-6110] specifies.

So each step adds at most this many validators.

- A block: `MAX_DEPOSITS` before Fulu, and none from Fulu.
- An epoch: none before Electra, and `MAX_PENDING_DEPOSITS_PER_EPOCH` from Electra ([EIP-7251]).
- An empty slot without the end of an epoch, and an upgrade: none.

A chain applies at most one block per slot, since a block must be later than the latest header.

It may apply one more at the slot of its first state.

Over `n` epochs, blocks add at most `(n + 1) * SLOTS_PER_EPOCH * MAX_DEPOSITS` validators.

Epochs from Electra add at most `n * MAX_PENDING_DEPOSITS_PER_EPOCH`.

That bounds the churn cap of every state that a chain reaches within `n` epochs.

`Reaches.churnCap_le` states it.

[EIP-6110]: https://eips.ethereum.org/EIPS/eip-6110#consensus-layer
[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- A step that adds at most `count` validators to the registry. -/
def Grows (count : Nat) (state after : BeaconState preset fork) : Prop :=
  after.validators.data.size ≤ state.validators.data.size + count

namespace Grows

theorem refl (state : BeaconState preset fork) : Grows 0 state state :=
  Nat.le_refl _

theorem trans {first second third : BeaconState preset fork} {one two : Nat}
    (head : Grows one first second) (tail : Grows two second third) :
    Grows (one + two) first third := by
  unfold Grows at *
  omega

theorem mono {small large : Nat} (le : small ≤ large) (grows : Grows small state after) :
    Grows large state after := by
  unfold Grows at *
  omega

theorem of_data (same : after.validators.data = state.validators.data) : Grows 0 state after := by
  unfold Grows
  rw [same]
  omega

theorem of_sameSizes (sizes : SameSizes state after) : Grows 0 state after := by
  unfold Grows
  rw [sizes.1]
  omega

/-- A fold whose steps add none adds none. -/
theorem foldlM_zero {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ s x s', step s x = .ok s' → Grows 0 s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Grows 0 state after :=
  foldlM_ok_invariant (Grows 0 state)
    (fun _ _ _ before ok => before.trans (each _ _ _ ok)) (.refl state) computed

/-- A fold whose steps add at most one each adds at most its length. -/
theorem foldlM_one {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (each : ∀ s x s', step s x = .ok s' → Grows 1 s s') :
    ∀ {items : List α} {state after : BeaconState preset fork},
      items.foldlM step state = .ok after → Grows items.length state after
  | [], _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | _ :: rest, _, _, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, others⟩ := computed
    have tail := foldlM_one each (items := rest) others
    simpa [Nat.add_comm] using (each _ _ _ first).trans tail

end Grows

/-! ## Deposits -/

/-- A new validator takes one index: the end of the registry, or from Gloas an index it reuses.
-/
theorem grows_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    Grows 1 state after := by
  unfold Grows
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨validators, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
    have size := setOrAppendRooted_size validatorsOk
    dsimp only
    split at size <;> omega
  · split at computed
    · cases computed
      simp
    · cases computed

theorem grows_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    Grows 1 state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact (Grows.refl _).mono (Nat.zero_le _)
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact grows_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ (Grows.refl _).mono (Nat.zero_le _)
  · rw [liftAccessor_ok] at computed
    exact (Grows.of_sameSizes (sameSizes_increaseBalance computed)).mono (Nat.zero_le _)

theorem grows_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    Grows 1 state after := by
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
        exact (grows_addValidatorToRegistry added).trans (Grows.of_data rfl)
      · cases computed
        exact (Grows.refl _).mono (Nat.zero_le _)
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact (Grows.of_data rfl).mono (Nat.zero_le _)
  · exact grows_applyPendingDeposit computed

theorem grows_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    Grows 1 state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (Grows.of_data (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (grows_applyDeposit applied)

/-- A deposit request only queues a pending deposit. -/
theorem grows_processDepositRequest {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    Grows 0 state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_data rfl

/-! ## Blocks -/

/-- The most validators that the deposits of one block add: `MAX_DEPOSITS` before Fulu.

From Fulu a block carries no deposits, so it adds none. -/
def blockGrowth (preset : Preset) (fork : Base.Fork) : Nat :=
  if fork < .fusaka then preset.MAX_DEPOSITS.toNat else 0

theorem blockGrowth_le (preset : Preset) (fork : Base.Fork) :
    blockGrowth preset fork ≤ preset.MAX_DEPOSITS.toNat := by
  unfold blockGrowth
  split <;> omega

theorem grows_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    Grows 0 state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .of_data rfl)

theorem grows_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    Grows 0 state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl

theorem grows_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) : Grows 0 state after := by
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

/-- From Gloas the payload of the parent applies its requests, which queue or go to builders. -/
theorem grows_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    Grows 0 state after := by
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
  exact (grows_settleParentPayment settledOk).trans <|
    (Grows.foldlM_zero (fun _ _ _ ok => grows_processDepositRequest ok) depositsOk).trans <|
    (Grows.foldlM_zero (fun _ _ _ ok => .of_sameSizes (sameSizes_processWithdrawalRequest ok))
      withdrawalsOk).trans <|
    (Grows.foldlM_zero (fun _ _ _ ok => .of_sameSizes (sameSizes_processConsolidationRequest ok))
      consolidationsOk).trans <|
    (Grows.foldlM_zero (fun _ _ _ ok => grows_processBuilderDepositRequest ok)
      buildersOk).trans <|
    (Grows.foldlM_zero (fun _ _ _ ok => grows_processBuilderExitRequest ok) exitsOk).trans
      (.of_data rfl)

theorem grows_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    Grows 0 state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_data rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_data rfl

theorem grows_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    Grows 0 state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_data rfl

theorem grows_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    Grows 0 state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (Grows.of_sameSizes (sameSizes_processWithdrawals withdrawnOk)).trans
      (grows_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (Grows.of_sameSizes (sameSizes_processWithdrawals withdrawnOk)).trans
      (grows_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact grows_processExecutionPayload computed
    · cases computed
      exact .refl _

/-- The operations of a block add a validator only by a deposit, one per deposit. -/
theorem grows_processOperations {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    Grows (blockGrowth preset fork) state after := by
  have fuluCase : Fork.fusaka ≤ fork → ∀ before : fork < .hegota,
      (body.deposits before).data.size = 0 :=
    fun fulu => processOperations_no_deposit fulu computed
  unfold processOperations at computed
  split at computed
  · exact (Grows.of_sameSizes (sameSizes_processOperationsGloas computed)).mono
      (Nat.zero_le _)
  rename_i notGloas
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, deposited, depositedOk,
    exited, exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : Grows 0 exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact Grows.foldlM_zero
        (fun _ _ _ ok => .of_sameSizes (sameSizes_processBlsToExecutionChange ok)) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : Grows 0 changed after := by
    split at requestsOk
    · exact .of_sameSizes (sameSizes_processExecutionRequests requestsOk)
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  have deposits := Grows.foldlM_one (fun _ _ _ ok => grows_processDeposit ok) depositedOk
  -- The deposits of a block are at most `MAX_DEPOSITS`, and none from Fulu.
  have before : fork < .hegota := Nat.lt_trans (Nat.lt_of_not_le notGloas) (by decide)
  have count : (body.deposits before).data.toList.length ≤ blockGrowth preset fork := by
    rw [Array.length_toList]
    unfold blockGrowth
    split
    · exact (body.deposits before).bound (Nat.lt_of_not_le notGloas)
    · exact Nat.le_of_eq (fuluCase (Nat.le_of_not_lt ‹_›) before)
  have total := (Grows.foldlM_zero
      (fun _ _ _ ok => .of_sameSizes (sameSizes_processProposerSlashing ok)) proposersOk).trans <|
    (Grows.foldlM_zero (fun _ _ _ ok => .of_sameSizes (sameSizes_processAttesterSlashing ok))
      attestersOk).trans <|
    (Grows.foldlM_zero (fun _ _ _ ok => .of_sameSizes (sameSizes_processAttestation ok))
      attestedOk).trans <|
    (deposits.mono count).trans <|
    (Grows.foldlM_zero (fun _ _ _ ok => .of_sameSizes (sameSizes_processVoluntaryExit ok))
      exitsOk).trans <|
    changes.trans requests
  exact total.mono (by omega)

/-- A block adds at most `blockGrowth` validators. -/
theorem grows_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    Grows (blockGrowth preset fork) state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    have paidGrows : Grows 0 state paid := by
      split at paidOk
      · exact grows_processParentExecutionPayload paidOk
      · cases paidOk
        exact .refl _
    have executedGrows : Grows 0 headed executed := by
      split at executedOk
      · exact grows_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    have votedGrows : Grows 0 revealed voted := by
      split at votedOk
      · exact .of_sameSizes (sameSizes_processEth1Data votedOk)
      · cases votedOk
        exact .refl _
    have total := paidGrows.trans <|
      (Grows.of_sameSizes (sameSizes_processBlockHeader headedOk)).trans <|
      executedGrows.trans <| (Grows.of_sameSizes (sameSizes_processRandao revealedOk)).trans <|
      votedGrows.trans <| (grows_processOperations operatedOk).trans
        (Grows.of_sameSizes (sameSizes_processSyncAggregate synced))
    exact total.mono (by omega)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  have total := (Grows.of_sameSizes (sameSizes_processBlockHeader headerOk)).trans <|
    (Grows.of_sameSizes (sameSizes_processRandao randaoOk)).trans <|
    (Grows.of_sameSizes (sameSizes_processEth1Data eth1Ok)).trans
      (grows_processOperations operationsOk)
  exact total.mono (by omega)

/-! ## Epochs -/

/-- The most validators that one epoch adds: none before Electra.

From Electra each pending deposit that an epoch applies adds at most one.

An epoch applies at most `MAX_PENDING_DEPOSITS_PER_EPOCH` of them. -/
def epochGrowth (preset : Preset) (fork : Base.Fork) : Nat :=
  if .pectra ≤ fork then preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat else 0

theorem epochGrowth_mono (preset : Preset) {earlier later : Base.Fork} (le : earlier ≤ later) :
    epochGrowth preset earlier ≤ epochGrowth preset later := by
  unfold epochGrowth
  by_cases electra : Base.Fork.pectra ≤ earlier
  · simp [electra, show Base.Fork.pectra ≤ later from Nat.le_trans electra le]
  · simp only [electra, ↓reduceIte]
    exact Nat.zero_le _

theorem grows_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    Grows preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat state after := by
  obtain ⟨read, _, applied, _, next, _, _, _, _, length, inRead, _, _, later, rfl⟩ :=
    processPendingDeposits_applied computed
  have each := Grows.foldlM_one (fun _ _ _ ok => grows_applyPendingDeposit ok) later
  exact (each.trans (Grows.of_data (state := next) rfl)).mono
    (by have := inRead.length_le; omega)

theorem grows_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      Grows 0 state result.1
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
      exact grows_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (Grows.of_sameSizes (sameSizes_decreaseBalance loweredOk)).trans <|
      (Grows.of_sameSizes (sameSizes_increaseBalance raisedOk)).trans
        (grows_passPendingConsolidations (result := (passed, read)) passedOk)

theorem grows_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    Grows (epochGrowth preset fork) state after := by
  unfold processPendingBalances at computed
  split at computed
  · rename_i electra
    simp only [bind_ok_iff] at computed
    obtain ⟨deposits, deposited, consolidated⟩ := computed
    have consolidations : Grows 0 deposits after := by
      unfold processPendingConsolidations at consolidated
      simp only [bind, Except.bind, pure, Except.pure] at consolidated
      repeat' (split at consolidated <;> try cases consolidated)
      all_goals exact (grows_passPendingConsolidations ‹_›).trans (.of_data rfl)
    have total := (grows_processPendingDeposits deposited).trans consolidations
    simpa [epochGrowth, electra] using total
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ (Grows.refl _).mono (Nat.zero_le _)

theorem grows_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) : Grows 0 state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_data rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem grows_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    Grows 0 state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_data rfl

theorem grows_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : Grows 0 state after := by
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

theorem grows_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) : Grows 0 state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_data rfl

/-- The steps that close an epoch from Altair, after the history. -/
private theorem grows_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : Grows 0 rooted after := by
  have syncedGrows : Grows 0 rooted synced :=
    (Grows.of_sameSizes (sameSizes_processParticipationFlagUpdates altair)).trans
      (Grows.of_sameSizes (sameSizes_processSyncCommitteeUpdates syncedOk))
  have lookedGrows : Grows 0 synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedGrows : Grows 0 looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedGrows.trans (lookedGrows.trans windowedGrows)

theorem grows_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    Grows (epochGrowth preset fork) state after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetGrows : Grows 0 slashed reset := by
    split at resetOk
    · exact grows_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ .refl _
  have paidGrows : Grows 0 pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact .of_data rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ .refl _
  have clearedGrows : Grows 0 balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_data rfl
  have mixedGrows : Grows 0 cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_data rfl
  have justifiedGrows :=
    Grows.of_sameSizes (sameSizes_processJustificationAndFinalization justifiedOk)
  have head := justifiedGrows.trans <| (grows_processInactivityUpdates scoredOk).trans <|
    (Grows.of_sameSizes (processRewardsAndPenalties_sameSizes rewardedOk)).trans <|
    (Grows.of_sameSizes (sameSizes_processRegistryUpdates registeredOk)).trans <|
    (Grows.of_sameSizes (sameSizes_processSlashings slashedOk)).trans <|
    resetGrows.trans <|
    (grows_processPendingBalances pendingOk).trans <|
    paidGrows.trans <|
    (Grows.of_sameSizes (sameSizes_processEffectiveBalanceUpdates balancedOk)).trans <|
    clearedGrows.trans mixedGrows
  have head' : Grows (epochGrowth preset fork) state mixed := head.mono (by omega)
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · have rootedGrows : Grows 0 mixed rooted := by
      unfold processHistoricalSummariesUpdate at rootedOk
      simp only [bind, Except.bind, pure, Except.pure] at rootedOk
      repeat' (split at rootedOk <;> try cases rootedOk)
      all_goals exact .refl _
    exact (head'.trans (rootedGrows.trans (grows_epochEnd syncedOk lookedOk windowed))).mono
      (by omega)
  · exact (head'.trans ((grows_processHistoricalRootsUpdate rootedOk).trans
      (grows_epochEnd syncedOk lookedOk windowed))).mono (by omega)

/-- An epoch adds at most `epochGrowth` validators: none before Electra. -/
theorem grows_processEpoch (computed : processEpoch config checks state = .ok after) :
    Grows (epochGrowth preset fork) state after := by
  unfold processEpoch at computed
  split at computed
  · exact grows_processEpochAltair computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have clearedGrows : Grows 0 balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_data rfl
  have mixedGrows : Grows 0 cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_data rfl
  have justifiedGrows :=
    Grows.of_sameSizes (sameSizes_processJustificationAndFinalization justifiedOk)
  have total := justifiedGrows.trans <|
    (Grows.of_sameSizes (processRewardsAndPenalties_sameSizes rewardedOk)).trans <|
    (Grows.of_sameSizes (sameSizes_processRegistryUpdates registeredOk)).trans <|
    (Grows.of_sameSizes (sameSizes_processSlashings slashedOk)).trans <|
    (grows_processEth1DataReset resetOk).trans <|
    (Grows.of_sameSizes (sameSizes_processEffectiveBalanceUpdates balancedOk)).trans <|
    clearedGrows.trans <| mixedGrows.trans <|
    (grows_processHistoricalRootsUpdate rootedOk).trans
      (grows_processParticipationRecordUpdates rotated)
  exact total.mono (Nat.zero_le _)

/-! ## Slots and upgrades -/

/-- The caching of a slot keeps the registry and the slot of the latest header. -/
theorem processSlot_keeps_header (computed : processSlot state = .ok after) :
    after.validators = state.validators ∧
      after.latestBlockHeader.slot = state.latestBlockHeader.slot := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, computed⟩ := computed
  split at computed
  · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
    refine ⟨rfl, ?_⟩
    dsimp only
    split <;> rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    refine ⟨rfl, ?_⟩
    dsimp only
    split <;> rfl

/-- One slot step adds validators only at the end of an epoch, and keeps the latest header's slot.
-/
theorem advanceSlot_growth (computed : advanceSlot config checks state = .ok after) :
    after.slot.toNat = state.slot.toNat + 1 ∧
      after.latestBlockHeader.slot = state.latestBlockHeader.slot ∧
      Grows (if after.slot % preset.SLOTS_PER_EPOCH = 0 then epochGrowth preset fork else 0)
        state after := by
  have slot := advanceSlot_slot computed
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  obtain ⟨cachedValidators, cachedHeader⟩ := processSlot_keeps_header cachedOk
  have cachedGrows : Grows 0 state cached := .of_data (by rw [cachedValidators])
  refine ⟨slot, ?_, ?_⟩
  · unfold epochIfLast at epochedOk
    split at epochedOk
    · obtain ⟨justified, justifiedOk, kept⟩ := processEpoch_kept epochedOk
      have header := (processJustificationAndFinalization_roots justifiedOk).1
      change epoched.latestBlockHeader.slot = _
      rw [kept.latestBlockHeader, header, cachedHeader]
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact cachedHeader
  · unfold epochIfLast at epochedOk
    dsimp only
    split at epochedOk
    · rename_i last
      simp only [last, ↓reduceIte]
      exact (cachedGrows.trans ((grows_processEpoch epochedOk).trans
        (Grows.of_data (state := epoched) rfl))).mono (by omega)
    · rename_i notLast
      simp only [notLast, ↓reduceIte]
      simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      subst epochedOk
      exact cachedGrows.trans (Grows.of_data (state := cached) rfl)

/-- An upgrade adds no validator. -/
theorem upgradeNext_size {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.validators.data.size ≤ pre.state.validators.data.size := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact Nat.le_of_eq (congrArg Array.size (upgradeToAltair_spec upgraded).1)
  · subst computed
    exact Nat.le_refl _
  · subst computed
    exact Nat.le_refl _
  · subst computed
    exact Nat.le_refl _
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, _, queued, compounded⟩ := upgraded
    have compoundedGrows := Grows.foldlM_zero (fun _ _ _ ok => by
      unfold queueCompoundingExcess at ok
      split at ok
      · split at ok
        · exact .of_sameSizes (sameSizes_queueExcessActiveBalance (liftAccessor_ok.mp ok))
        · cases ok
          exact .refl _
      · cases ok
        exact .refl _) compounded
    have queuedGrows := Grows.foldlM_zero (fun _ _ _ ok => by
      simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at ok
      obtain ⟨_, _, _, -, _, -, _, set₁, _, set₂, rfl⟩ := ok
      obtain ⟨_, rfl⟩ := setBalance_ok set₁
      exact (Grows.of_sameSizes (sameSizes_setValidator set₂)).trans (.of_data rfl)) queued
    exact queuedGrows.trans compoundedGrows
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact Nat.le_of_eq (congrArg Array.size (upgradeToFulu_spec upgraded).1)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact Nat.le_of_eq (congrArg Array.size (upgradeToGloas_spec upgraded).1)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact Nat.le_of_eq (congrArg Array.size (upgradeHezeFields_lists _).1)

/-! ## Chains -/

/-- The slots that blocks have used: that of the latest header, or the slot before the state's.

A block at the slot of a state moves it up by one, and no other step moves it down. -/
def blockMark (state : BeaconState preset fork) : Nat :=
  max state.latestBlockHeader.slot.toNat (state.slot.toNat - 1)

/-- Along a chain the registry grows only by blocks and, from Electra, by epochs.

The relation also keeps the order of forks and slots, and bounds how far `blockMark` moves. -/
def GrowthBounded (forked after : ForkedBeaconState preset) : Prop :=
  forked.fork ≤ after.fork ∧ forked.state.slot.toNat ≤ after.state.slot.toNat ∧
    blockMark forked.state ≤ blockMark after.state ∧
    blockMark after.state ≤ max (blockMark forked.state) after.state.slot.toNat ∧
    after.state.validators.data.size ≤ forked.state.validators.data.size +
      (blockMark after.state - blockMark forked.state) * preset.MAX_DEPOSITS.toNat +
      ((getCurrentEpoch after.state).toNat - (getCurrentEpoch forked.state).toNat) *
        epochGrowth preset after.fork

theorem epoch_le_of_slot_le {fork' : Base.Fork} {state : BeaconState preset fork}
    {after : BeaconState preset fork'} (le : state.slot.toNat ≤ after.slot.toNat) :
    (getCurrentEpoch state).toNat ≤ (getCurrentEpoch after).toNat := by
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
  exact Nat.div_le_div_right le

theorem stepRelation_growthBounded :
    StepRelation config checks (GrowthBounded (preset := preset)) where
  refl forked := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _, by simp⟩
  trans := by
    intro first second third ⟨fork₁, slot₁, mark₁, markMax₁, size₁⟩
      ⟨fork₂, slot₂, mark₂, markMax₂, size₂⟩
    have epochs₁ := epoch_le_of_slot_le slot₁
    have epochs₂ := epoch_le_of_slot_le slot₂
    have growth := epochGrowth_mono preset fork₂
    refine ⟨Nat.le_trans fork₁ fork₂, Nat.le_trans slot₁ slot₂, Nat.le_trans mark₁ mark₂,
      ?_, ?_⟩
    · exact Nat.le_trans markMax₂ (Nat.max_le.mpr ⟨Nat.le_trans markMax₁
        (Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans slot₂ (Nat.le_max_right _ _)⟩),
        Nat.le_max_right _ _⟩)
    · have epochTerm := Nat.mul_le_mul_left
        ((getCurrentEpoch second.state).toNat - (getCurrentEpoch first.state).toNat) growth
      have marks : blockMark third.state - blockMark first.state =
          (blockMark second.state - blockMark first.state) +
            (blockMark third.state - blockMark second.state) := by omega
      have epochs : (getCurrentEpoch third.state).toNat - (getCurrentEpoch first.state).toNat =
          ((getCurrentEpoch second.state).toNat - (getCurrentEpoch first.state).toNat) +
            ((getCurrentEpoch third.state).toNat - (getCurrentEpoch second.state).toNat) := by
        omega
      rw [marks, epochs, Nat.add_mul, Nat.add_mul]
      omega
  advanceSlot := by
    intro fork state after computed
    obtain ⟨slot, header, grows⟩ := advanceSlot_growth computed
    unfold GrowthBounded blockMark
    dsimp only
    rw [header, slot]
    refine ⟨Nat.le_refl _, by omega, by omega, by omega, ?_⟩
    unfold Grows at grows
    split at grows
    · rename_i last
      -- The slot step that ends an epoch moves the epoch on by one.
      have positive : 0 < preset.SLOTS_PER_EPOCH.toNat := by
        rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
        · have zero' : preset.SLOTS_PER_EPOCH = 0 := UInt64.toNat_inj.mp (by simpa using zero)
          rw [zero', UInt64.mod_zero] at last
          have := congrArg UInt64.toNat last
          simp only [UInt64.toNat_zero] at this
          omega
        · exact positive
      have divides : preset.SLOTS_PER_EPOCH.toNat ∣ after.slot.toNat := by
        have := congrArg UInt64.toNat last
        rw [UInt64.toNat_mod, UInt64.toNat_zero] at this
        exact Nat.dvd_of_mod_eq_zero this
      have moved : (getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat + 1 := by
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slot, Nat.succ_div]
        rw [slot] at divides
        simp [divides]
      rw [moved]
      simp only [Nat.add_sub_cancel_left, Nat.one_mul]
      omega
    · omega
  upgradeNext := by
    intro pre post _ computed
    have same := upgradeNext_history computed
    simp only [BeaconState.history, Prod.mk.injEq] at same
    obtain ⟨slot, header, _⟩ := same
    have size := upgradeNext_size computed
    have epochs : (getCurrentEpoch post.val.state).toNat = (getCurrentEpoch pre.state).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slot]
    unfold GrowthBounded blockMark
    rw [slot, header, epochs]
    exact ⟨Nat.le_of_lt post.property, Nat.le_refl _, Nat.le_refl _, Nat.le_max_left _ _,
      by simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]; exact size⟩
  applySignedBlock := by
    intro fork engine state after signed validateResult computed
    have processed := (applySignedBlock_ok computed).2.1
    have grows := grows_processBlock processed
    obtain ⟨paid, headed, paidKept, headedOk, headedKept⟩ := processBlock_kept processed
    obtain ⟨slot, newer, -⟩ := processBlockHeader_checks headedOk
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
    have afterSlot : after.slot = state.slot := headedKept.slot.trans paidKept.slot
    have afterHeader : after.latestBlockHeader.slot = state.slot := by
      rw [headedKept.latestBlockHeader, slot, paidKept.slot]
    rw [paidKept.slot] at slot
    have newer' := UInt64.lt_iff_toNat_lt.mp (slot ▸ newer)
    rw [paidKept.latestBlockHeader] at newer'
    have limit := blockGrowth_le preset fork
    have epochs : (getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, afterSlot]
    unfold Grows at grows
    unfold GrowthBounded blockMark
    dsimp only
    rw [afterSlot, afterHeader, epochs]
    refine ⟨Nat.le_refl _, Nat.le_refl _, by omega, by omega, ?_⟩
    have one : max state.slot.toNat (state.slot.toNat - 1) -
        max state.latestBlockHeader.slot.toNat (state.slot.toNat - 1) = 1 := by omega
    rw [one, Nat.sub_self, Nat.one_mul, Nat.zero_mul]
    omega

/-- Along a chain the registry grows by at most `MAX_DEPOSITS` for each slot, and one slot more.

From Electra it also grows by at most `MAX_PENDING_DEPOSITS_PER_EPOCH` for each epoch.

The slots and epochs are those between the two states. -/
theorem Reaches.size_le {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) :
    after.state.validators.data.size ≤ start.state.validators.data.size +
      (after.state.slot.toNat + 1 - start.state.slot.toNat) * preset.MAX_DEPOSITS.toNat +
      ((getCurrentEpoch after.state).toNat - (getCurrentEpoch start.state).toNat) *
        epochGrowth preset after.fork := by
  obtain ⟨_, slots, _, markMax, size⟩ := stepRelation_growthBounded.reaches chain
  have marks : blockMark after.state - blockMark start.state ≤
      after.state.slot.toNat + 1 - start.state.slot.toNat := by
    have : start.state.slot.toNat - 1 ≤ blockMark start.state := Nat.le_max_right _ _
    have := Nat.max_le.mp (Nat.le_refl (max (blockMark start.state) after.state.slot.toNat))
    omega
  have := Nat.mul_le_mul_right preset.MAX_DEPOSITS.toNat marks
  omega

/-- The slots from a state to a later one, plus one, fit in the epochs between them, plus one.

Each epoch has `SLOTS_PER_EPOCH` slots. -/
theorem slots_le_epochs {fork' : Base.Fork} {state : BeaconState preset fork}
    {after : BeaconState preset fork'} (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) :
    after.slot.toNat + 1 - state.slot.toNat ≤
      ((getCurrentEpoch after).toNat - (getCurrentEpoch state).toNat + 1) *
        preset.SLOTS_PER_EPOCH.toNat := by
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
  have upper := Nat.lt_mul_div_succ after.slot.toNat positive
  have lower := Nat.div_mul_le_self state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
  by_cases order : state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      after.slot.toNat / preset.SLOTS_PER_EPOCH.toNat
  · rw [← Nat.sub_add_comm order, Nat.sub_mul, Nat.mul_comm _ preset.SLOTS_PER_EPOCH.toNat]
    generalize preset.SLOTS_PER_EPOCH.toNat * (after.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1)
      = whole at upper ⊢
    generalize state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat
      = start at lower ⊢
    omega
  · -- A later epoch at the first state means a later slot, so there are no slots between.
    have earlier : after.slot.toNat < state.slot.toNat := by
      by_contra later
      exact order (Nat.div_le_div_right (Nat.le_of_not_lt later))
    omega

theorem epochGrowth_le (preset : Preset) (fork : Base.Fork) :
    epochGrowth preset fork ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
  unfold epochGrowth
  split <;> omega

theorem epochGrowth_of_lt (preset : Preset) {fork : Base.Fork} (before : fork < .pectra) :
    epochGrowth preset fork = 0 := by
  unfold epochGrowth
  split
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  · rfl

/-- The most validators that a chain has within `epochs` epochs of its start.

It adds three parts.

- The registry of the start.
- `MAX_DEPOSITS` for each slot of `epochs + 1` epochs.
- `MAX_PENDING_DEPOSITS_PER_EPOCH` for each epoch. -/
def sizeWithin (start : ForkedBeaconState preset) (epochs : Nat) : Nat :=
  start.state.validators.data.size +
    (epochs + 1) * preset.SLOTS_PER_EPOCH.toNat * preset.MAX_DEPOSITS.toNat +
    epochs * preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat

/-- The churn cap of a registry of `sizeWithin` validators.

It bounds the churn cap of every state that a chain reaches within `epochs` epochs. -/
def churnCapWithin (config : Config) (start : ForkedBeaconState preset) (epochs : Nat) : Nat :=
  churnCap config (sizeWithin start epochs)

theorem sizeWithin_mono (start : ForkedBeaconState preset) {epochs more : Nat}
    (le : epochs ≤ more) : sizeWithin start epochs ≤ sizeWithin start more := by
  unfold sizeWithin
  have blocks := Nat.mul_le_mul_right preset.MAX_DEPOSITS.toNat
    (Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat (Nat.add_le_add_right le 1))
  have epochTerm := Nat.mul_le_mul_right preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat le
  omega

theorem churnCapWithin_mono (config : Config) (start : ForkedBeaconState preset)
    {epochs more : Nat} (le : epochs ≤ more) :
    churnCapWithin config start epochs ≤ churnCapWithin config start more :=
  churnCap_mono (sizeWithin_mono start le)

/-- Along a chain, the registry is within `sizeWithin` of the epochs between its ends.

That needs at least one slot per epoch, as mainnet and the minimal preset have. -/
theorem Reaches.size_le_within {start after : ForkedBeaconState preset}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (chain : Reaches config checks start after) :
    after.state.validators.data.size ≤ sizeWithin start
      ((getCurrentEpoch after.state).toNat - (getCurrentEpoch start.state).toNat) := by
  have size := chain.size_le
  have slots := Nat.mul_le_mul_right preset.MAX_DEPOSITS.toNat
    (slots_le_epochs (state := start.state) (after := after.state) positive)
  have epochTerm := Nat.mul_le_mul_left
    ((getCurrentEpoch after.state).toNat - (getCurrentEpoch start.state).toNat)
    (epochGrowth_le preset after.fork)
  unfold sizeWithin
  omega

/-- Along a chain, the churn cap of the end is at most `churnCapWithin` of the epochs between.

That needs at least one slot per epoch, as mainnet and the minimal preset have. -/
theorem Reaches.churnCap_le {start after : ForkedBeaconState preset}
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat) (chain : Reaches config checks start after) :
    max 1 (churnCap config after.state.validators.data.size) ≤
      max 1 (churnCapWithin config start
        ((getCurrentEpoch after.state).toNat - (getCurrentEpoch start.state).toNat)) := by
  have capped := churnCap_mono (config := config) (chain.size_le_within positive)
  exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans capped (Nat.le_max_right _ _)⟩

end EthLib.Consensus
