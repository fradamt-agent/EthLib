module

public import EthLib.Consensus.Proofs.Transition.BlockLedger
public import EthLib.Consensus.Proofs.Transition.StakeLoss
public import EthLib.Consensus.Proofs.Transition.WithdrawalAmounts

/-!
# Proofs: what a block debits, flow by flow

The ledger of a block names the kind of each change.

To bound how far a balance falls, the debits also need their amounts.

A block debits a balance in four ways.

- Withdrawals, from Capella: a debit of each withdrawal amount that names it.
- The sync aggregate, from Altair: a debit of the participant reward for each miss.
  A miss is a seat of the committee held by the validator whose bit is not set.
- Slashings: the initial penalty of a slashed validator.
- From Electra, a switch to compounding credentials: the excess queued back as a deposit.

This file keeps the withdrawals and the sync changes exact, with the step that computes them.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Debits of one kind -/

/-- Changes debit nothing of a kind when none of them is a debit of that kind. -/
theorem BalanceChange.debited_eq_zero {flow : BalanceFlow} :
    ∀ {changes : List BalanceChange}, (∀ change ∈ changes, ∀ amount, change ≠ .debit flow amount) →
      BalanceChange.debited flow changes = 0
  | [], _ => rfl
  | change :: rest, absent => by
    have later := BalanceChange.debited_eq_zero fun other member =>
      absent other (List.mem_cons_of_mem _ member)
    simp only [BalanceChange.debited, List.map_cons, List.sum_cons] at later ⊢
    rw [later]
    cases change with
    | credit => rfl
    | debit kind amount =>
      by_cases same : kind = flow
      · exact absurd (by rw [same]) (absent _ List.mem_cons_self amount)
      · simp [same]

/-- What changes in turn debit of a kind is the sum over the parts. -/
theorem BalanceChange.debited_append (flow : BalanceFlow) (first second : List BalanceChange) :
    BalanceChange.debited flow (first ++ second) =
      BalanceChange.debited flow first + BalanceChange.debited flow second := by
  simp [BalanceChange.debited]

/-- The number of seats of a committee held by a validator whose bit is not set. -/
def syncMisses (members : List (ValidatorIndex × Bool)) (i : Nat) : Nat :=
  members.countP fun member => !member.2 && member.1.toNat == i

/-- The sync changes debit a validator the participant reward for each of its misses. -/
theorem debited_syncChanges (proposer : ValidatorIndex) (reward proposerReward i : Nat) :
    ∀ members : List (ValidatorIndex × Bool),
      BalanceChange.debited .blockReward (syncChanges members proposer reward proposerReward i) =
        reward * syncMisses members i
  | [] => by simp [syncChanges, syncMisses, BalanceChange.debited]
  | (index, signed) :: rest => by
    have later := debited_syncChanges proposer reward proposerReward i rest
    simp only [syncChanges, syncMisses, List.flatMap_cons] at later ⊢
    rw [BalanceChange.debited_append, later, List.countP_cons]
    cases signed <;> by_cases one : index.toNat = i <;> by_cases two : proposer.toNat = i <;>
      simp [one, two, BalanceChange.debited, Nat.mul_add] <;> omega

/-- Withdrawals debit a balance only as withdrawals. -/
theorem debited_withdrawalChanges_of_ne {flow : BalanceFlow} (other : flow ≠ .withdrawal)
    (withdrawals : List Withdrawal) (i : Nat) :
    BalanceChange.debited flow (withdrawalChanges fork withdrawals i) = 0 := by
  refine BalanceChange.debited_eq_zero fun change member amount same => ?_
  simp only [withdrawalChanges, List.mem_flatMap] at member
  obtain ⟨_, _, member⟩ := member
  split at member
  · rw [List.mem_singleton.mp member] at same
    cases same
    exact other rfl
  · cases member

/-- The sync changes debit a balance only as block rewards. -/
theorem debited_syncChanges_of_ne {flow : BalanceFlow} (other : flow ≠ .blockReward)
    {members : List (ValidatorIndex × Bool)} {proposer : ValidatorIndex}
    {reward proposerReward i : Nat} :
    BalanceChange.debited flow (syncChanges members proposer reward proposerReward i) = 0 :=
  BalanceChange.debited_eq_zero fun change member amount same => by
    have := syncChanges_isSyncReward member
    rw [same] at this
    exact other this

/-! ## The debits of a block -/

/-- The withdrawals that a block applies: none, or those of its withdrawal step.

That step runs from a state inside the block, and `AppliedWithdrawals` names them. -/
def BlockWithdrawals (preset : Preset) (fork : Base.Fork) (withdrawals : List Withdrawal) :
    Prop :=
  withdrawals = [] ∨ ∃ (capella : .shapella ≤ fork) (pre post : BeaconState preset fork)
    (payload : Until .glamsterdam fork (ExecutionPayload preset fork)) (applied : Array Withdrawal),
    processWithdrawals pre capella payload = .ok post ∧
      AppliedWithdrawals pre post capella payload applied ∧ withdrawals = applied.toList

/-- The sync changes of a block: none before Altair, or those of its sync aggregate.

The aggregate runs on a state inside the block, the last before the end. -/
def BlockSync (config : Config) (checks : SignatureChecks) (fork : Base.Fork)
    (sync : Nat → List BalanceChange) : Prop :=
  (∀ i, sync i = []) ∨ ∃ (altair : .altair ≤ fork) (pre post : BeaconState preset fork)
    (aggregate : SyncAggregate preset) (reward proposerReward : Gwei)
    (members : Array ValidatorIndex) (proposer : ValidatorIndex),
    processSyncAggregate config checks pre altair aggregate = .ok post ∧
      syncParticipantReward pre = .ok reward ∧
      (pre.currentSyncCommittee altair).value.pubkeys.toArray.mapM
        (validatorIndexOfPubkey pre) = .ok members ∧
      ∀ i, sync i = if i < pre.balances.data.size then
        syncChanges (members.zip aggregate.syncCommitteeBits.bits.toArray).toList proposer
          reward.toNat proposerReward.toNat i else []

/-- The ledger of a block, with its withdrawals and its sync changes exact.

It is `BlockLedger`, with the withdrawals and the sync changes named by the steps that make them.
-/
def BlockDebits (config : Config) (checks : SignatureChecks)
    (state after : BeaconState preset fork) : Prop :=
  ∃ (excess slashings credits deposits requests sync : Nat → List BalanceChange)
    (withdrawals : List Withdrawal),
    BalanceLedger state after (fun i => excess i ++ withdrawalChanges fork withdrawals i ++
      slashings i ++ credits i ++ deposits i ++ requests i ++ sync i) ∧
    (∀ i, ∀ change ∈ excess i, IsExcessQueued change) ∧
    (∀ i, ∀ change ∈ slashings i, IsSlashing change) ∧
    (∀ i, ∀ change ∈ credits i, IsProposerCredit change) ∧
    (∀ i, ∀ change ∈ deposits i, IsDeposit change) ∧
    (∀ i, ∀ change ∈ requests i, IsExcessQueued change) ∧
    BlockWithdrawals preset fork withdrawals ∧
    BlockSync (preset := preset) config checks fork sync

/-- The ledger of a block, at every fork, with its withdrawals and sync changes exact.

That needs one balance for each validator. -/
theorem processBlock_debits {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (holds : BalancesMatch state) : BlockDebits config checks state after := by
  unfold processBlock at computed
  split at computed
  · rename_i altair
    unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨s1, s1Ok, s2, s2Ok, s3, s3Ok, s4, s4Ok, s5, s5Ok, s6, s6Ok, last⟩ := computed
    -- The payload of the parent block.
    obtain ⟨excess, excessLedger, excessKind⟩ : LedgerOf IsExcessQueued state s1 := by
      split at s1Ok
      · exact processParentExecutionPayload_ledgerOf s1Ok
      · cases s1Ok
        exact LedgerOf.of_balances rfl
    have header := processBlockHeader_balances s2Ok
    -- The withdrawals, then the payload or the bid.
    obtain ⟨withdrawals, withdrawalSpec, withdrawalLedger⟩ : ∃ withdrawals,
        BlockWithdrawals preset fork withdrawals ∧
          BalanceLedger s2 s3 (withdrawalChanges fork withdrawals) := by
      split at s3Ok
      · unfold processBlockExecution at s3Ok
        dsimp only at s3Ok
        split at s3Ok
        · simp only [bind_ok_iff] at s3Ok
          obtain ⟨withdrawn, withdrawnOk, bid⟩ := s3Ok
          obtain ⟨applied, named, ledger⟩ := processWithdrawals_ledger withdrawnOk
          exact ⟨applied.toList, .inr ⟨_, _, _, _, _, withdrawnOk, named, rfl⟩,
            (ledger.trans (BalanceLedger.of_balances
              (processExecutionPayloadBid_balances bid))).congr fun i => by simp⟩
        · split at s3Ok
          · simp only [bind_ok_iff] at s3Ok
            obtain ⟨withdrawn, withdrawnOk, paid⟩ := s3Ok
            obtain ⟨applied, named, ledger⟩ := processWithdrawals_ledger withdrawnOk
            exact ⟨applied.toList, .inr ⟨_, _, _, _, _, withdrawnOk, named, rfl⟩,
              (ledger.trans (BalanceLedger.of_balances
                (processExecutionPayload_balances paid))).congr fun i => by simp⟩
          · split at s3Ok
            · exact ⟨[], .inl rfl, (BalanceLedger.of_balances
                (processExecutionPayload_balances s3Ok)).congr fun i => by simp [withdrawalChanges]⟩
            · cases s3Ok
              exact ⟨[], .inl rfl,
                (BalanceLedger.refl _).congr fun i => by simp [withdrawalChanges]⟩
      · cases s3Ok
        exact ⟨[], .inl rfl, (BalanceLedger.refl _).congr fun i => by simp [withdrawalChanges]⟩
    have randao := processRandao_balances s4Ok
    have eth1 : s5.balances = s4.balances := by
      split at s5Ok
      · exact processEth1Data_balances s5Ok
      · cases s5Ok
        rfl
    -- Before Gloas the sizes stay up to the operations.
    have matched : fork < .glamsterdam → BalancesMatch s5 := by
      intro before
      have noGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
      have one : s1 = state := by
        simp only [noGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at s1Ok
        exact s1Ok.symm
      subst one
      have three : SameSizes s2 s3 := by
        split at s3Ok
        · unfold processBlockExecution at s3Ok
          simp only [noGloas, ↓reduceDIte] at s3Ok
          split at s3Ok
          · simp only [bind_ok_iff] at s3Ok
            obtain ⟨withdrawn, withdrawnOk, paid⟩ := s3Ok
            exact (sameSizes_processWithdrawals withdrawnOk).trans
              (sameSizes_processExecutionPayload paid)
          · split at s3Ok
            · exact sameSizes_processExecutionPayload s3Ok
            · cases s3Ok
              exact SameSizes.refl _
        · cases s3Ok
          exact SameSizes.refl _
      have five : SameSizes s4 s5 := by
        split at s5Ok
        · exact sameSizes_processEth1Data s5Ok
        · cases s5Ok
          exact SameSizes.refl _
      exact balancesMatch_of_sameSizes ((((sameSizes_processBlockHeader s2Ok).trans three).trans
        (sameSizes_processRandao s4Ok)).trans five) holds
    obtain ⟨slashings, credits, deposits, requests, operationsLedger, slashingKind, creditKind,
      depositKind, requestKind⟩ := processOperations_ledger s6Ok matched
    obtain ⟨reward, proposerReward, members, proposer, rewardOk, _, membersOk, _, syncLedger⟩ :=
      processSyncAggregate_ledger last
    refine ⟨excess, slashings, credits, deposits, requests,
      fun i => if i < s6.balances.data.size then syncChanges
          (members.zip (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray).toList
          proposer reward.toNat proposerReward.toNat i else [], withdrawals, ?_, excessKind,
      slashingKind, creditKind, depositKind, requestKind, withdrawalSpec,
      .inr ⟨altair, s6, after, _, reward, proposerReward, members, proposer, last, rewardOk,
        membersOk, fun _ => rfl⟩⟩
    refine (((((excessLedger.trans (BalanceLedger.of_balances header)).trans withdrawalLedger).trans
      (BalanceLedger.of_balances (eth1.trans randao))).trans operationsLedger).trans
        syncLedger).congr fun i => by simp
  · rename_i notAltair
    have before : fork < .glamsterdam := Nat.lt_trans (Nat.lt_of_not_le notAltair) (by decide)
    simp only [bind_ok_iff] at computed
    obtain ⟨s1, s1Ok, s2, s2Ok, s3, s3Ok, last⟩ := computed
    have sizes : SameSizes state s3 :=
      ((sameSizes_processBlockHeader s1Ok).trans (sameSizes_processRandao s2Ok)).trans
        (sameSizes_processEth1Data s3Ok)
    obtain ⟨slashings, credits, deposits, requests, operationsLedger, slashingKind, creditKind,
      depositKind, requestKind⟩ :=
      processOperations_ledger last fun _ => balancesMatch_of_sameSizes sizes holds
    refine ⟨fun _ => [], slashings, credits, deposits, requests, fun _ => [], [], ?_,
      fun _ _ absent => absurd absent List.not_mem_nil, slashingKind, creditKind,
      depositKind, requestKind, .inl rfl, .inl fun _ => rfl⟩
    have frame : s3.balances = state.balances := (processEth1Data_balances s3Ok).trans
      ((processRandao_balances s2Ok).trans (processBlockHeader_balances s1Ok))
    exact ((BalanceLedger.of_balances frame).trans operationsLedger).congr fun i => by
      simp [withdrawalChanges]

/-- Changes all of one kind debit nothing of another flow. -/
theorem BalanceChange.debited_of_kind {allowed : BalanceChange → Prop} {flow : BalanceFlow}
    (excluded : ∀ amount, ¬ allowed (.debit flow amount)) {changes : List BalanceChange}
    (kind : ∀ change ∈ changes, allowed change) : BalanceChange.debited flow changes = 0 :=
  BalanceChange.debited_eq_zero fun change member amount same =>
    excluded amount (same ▸ kind change member)

/-- The debits of a block to one balance, flow by flow.

The withdrawals debit their amounts, and the sync changes the participant reward per miss.

The slashings debit as slashing, and the excess queued back as such.

No step of a block debits as rewards, deposits or consolidations. -/
theorem BlockDebits.debited (debits : BlockDebits config checks state after) :
    ∃ (excess slashings sync : Nat → List BalanceChange) (withdrawals : List Withdrawal)
      (changes : Nat → List BalanceChange),
      BalanceLedger state after changes ∧
      BlockWithdrawals preset fork withdrawals ∧
      BlockSync (preset := preset) config checks fork sync ∧
      (∀ i, ∀ change ∈ slashings i, IsSlashing change) ∧
      (∀ i, ∀ change ∈ excess i, IsExcessQueued change) ∧
      ∀ i flow, BalanceChange.debited flow (changes i) =
        match flow with
        | BalanceFlow.withdrawal =>
          BalanceChange.debited .withdrawal (withdrawalChanges fork withdrawals i)
        | BalanceFlow.blockReward => BalanceChange.debited .blockReward (sync i)
        | BalanceFlow.slashing => BalanceChange.debited .slashing (slashings i)
        | BalanceFlow.excessQueued => BalanceChange.debited .excessQueued (excess i)
        | _ => 0 := by
  obtain ⟨excess, slashings, credits, deposits, requests, sync, withdrawals, ledger, excessKind,
    slashingKind, creditKind, depositKind, requestKind, withdrawalSpec, syncSpec⟩ := debits
  -- The excess queued by the parent payload and by the requests are one kind.
  refine ⟨fun i => excess i ++ requests i, slashings, sync, withdrawals, _, ledger,
    withdrawalSpec, syncSpec, slashingKind, fun i change member => ?_, fun i flow => ?_⟩
  · rcases List.mem_append.mp member with member | member
    · exact excessKind i change member
    · exact requestKind i change member
  -- The sync changes are sync rewards, whether there are any or not.
  have syncKind : ∀ i, ∀ change ∈ sync i, IsSyncReward change := by
    rcases syncSpec with none | ⟨_, _, _, _, _, _, _, _, _, _, _, named⟩
    · intro i change member
      rw [none i] at member
      cases member
    · intro i change member
      rw [named i] at member
      split at member
      · exact syncChanges_isSyncReward member
      · cases member
  simp only [BalanceChange.debited_append]
  have e := fun (flow : BalanceFlow) (other : flow ≠ .excessQueued) => BalanceChange.debited_of_kind
    (allowed := IsExcessQueued) (flow := flow) (by intro _ h; exact other h) (excessKind i)
  have r := fun (flow : BalanceFlow) (other : flow ≠ .excessQueued) => BalanceChange.debited_of_kind
    (allowed := IsExcessQueued) (flow := flow) (by intro _ h; exact other h) (requestKind i)
  have l := fun (flow : BalanceFlow) (other : flow ≠ .slashing) => BalanceChange.debited_of_kind
    (allowed := IsSlashing) (flow := flow) (by intro _ h; exact other h) (slashingKind i)
  have c := fun (flow : BalanceFlow) =>
    BalanceChange.debited_of_kind (allowed := IsProposerCredit) (flow := flow)
    (by intro _ h; exact h) (creditKind i)
  have d := fun (flow : BalanceFlow) =>
    BalanceChange.debited_of_kind (allowed := IsDeposit) (flow := flow)
    (by intro _ h; exact h) (depositKind i)
  have s := fun (flow : BalanceFlow) (other : flow ≠ .blockReward) => BalanceChange.debited_of_kind
    (allowed := IsSyncReward) (flow := flow) (by intro _ h; exact other h) (syncKind i)
  have w := fun (flow : BalanceFlow) (other : flow ≠ .withdrawal) =>
    debited_withdrawalChanges_of_ne (fork := fork) other withdrawals i
  cases flow <;> simp (disch := decide) only [e, r, l, c, d, s, w] <;> omega

end EthLib.Consensus
