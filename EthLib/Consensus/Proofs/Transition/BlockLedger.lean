module

public import EthLib.Consensus.Proofs.Transition.BalanceLedger
public import EthLib.Consensus.Proofs.Transition.BlockRewards
public import EthLib.Consensus.Proofs.Transition.ParentPayload

/-!
# Proofs: the ledger of a block

The steps of a block that change balances, and those that keep them.

From Gloas the payload of the parent block may queue the excess of balances back as deposits.

From Capella the withdrawals debit each balance they name, in turn.

The slashings debit the slashed validators and credit the proposer.

From Altair each attestation credits the proposer.

Before Heze the deposits credit balances, and from Electra the requests may queue excess.

From Altair the sync rewards credit the members that signed and the proposer.

They debit the members that did not sign.

Every other step of a block keeps the balances.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

/-- Peels the steps of a successful `do` block, down to its last equation. -/
local macro "peel" h:ident : tactic =>
  `(tactic| repeat obtain ⟨_, _, $h:ident⟩ := $h:ident)

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## The steps of a block that keep the balances -/

/-- The block header keeps the balances. -/
theorem processBlockHeader_balances {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : after.balances = state.balances := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  rfl

/-- The RANDAO reveal keeps the balances. -/
theorem processRandao_balances {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    after.balances = state.balances := by
  simp only [processRandao, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  peel computed
  rfl

/-- The vote on the deposit contract keeps the balances. -/
theorem processEth1Data_balances {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) :
    after.balances = state.balances := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]

/-- The execution payload keeps the balances. -/
theorem processExecutionPayload_balances {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    after.balances = state.balances := by
  simp only [processExecutionPayload, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  peel computed
  rfl

/-- From Gloas, the bid for the payload keeps the balances. -/
theorem processExecutionPayloadBid_balances {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    after.balances = state.balances := by
  simp only [processExecutionPayloadBid, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, recorded, recordedOk, rfl⟩ := computed
  unfold recordBidPayment at recordedOk
  split at recordedOk
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at recordedOk
    obtain ⟨_, _, _, _, rfl⟩ := recordedOk
    rfl
  · cases recordedOk
    rfl

/-- A voluntary exit keeps the balances. -/
theorem processVoluntaryExit_balances {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    after.balances = state.balances := by
  simp only [processVoluntaryExit, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  peel computed
  exact initiateValidatorExit_balances computed

/-- A change of BLS credentials keeps the balances. -/
theorem processBlsToExecutionChange_balances {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    after.balances = state.balances := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact setValidator_balances set

/-- From Gloas, a payload attestation keeps the state. -/
theorem processPayloadAttestation_balances {gloas : .glamsterdam ≤ fork}
    {attestation : PayloadAttestation preset}
    (computed : processPayloadAttestation config checks state gloas attestation = .ok after) :
    after.balances = state.balances := by
  simp only [processPayloadAttestation, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  peel computed
  rfl

/-- From Electra, a deposit request only queues a deposit. -/
theorem processDepositRequest_balances {electra : .pectra ≤ fork} {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    after.balances = state.balances := by
  simp only [processDepositRequest, liftAccessor_ok, addPendingDeposit, bind_ok_iff, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  unfold recordDepositRequestsStart
  split
  · split <;> rfl
  · rfl

/-- From Electra, a partial withdrawal request only queues a withdrawal. -/
theorem requestPartialWithdrawal_balances {electra : .pectra ≤ fork} {index : ValidatorIndex}
    {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) : after.balances = state.balances := by
  unfold requestPartialWithdrawal at computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  all_goals first
    | (cases computed; rfl)
    | (simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
       obtain ⟨⟨churned, _⟩, churnedOk, _, _, _, _, rfl⟩ := computed
       exact (computeExitEpochAndUpdateChurn_earliest churnedOk).2.2)

/-- From Electra, a withdrawal request keeps the balances. -/
theorem processWithdrawalRequest_balances {electra : .pectra ≤ fork} {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    after.balances = state.balances := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)
    | exact initiateValidatorExit_balances (liftAccessor_ok.mp computed)
    | exact requestPartialWithdrawal_balances computed

/-- From Gloas, a builder deposit request changes only the builders. -/
theorem processBuilderDepositRequest_balances {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    after.balances = state.balances := by
  unfold processBuilderDepositRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)
    | (simp only [Except.ok.injEq] at computed; rw [← computed]; rfl)
    | (simp only [addBuilderToRegistry, Except.ok.injEq] at computed
       rw [← computed]
       split <;> rfl)

/-- From Gloas, starting the exit of a builder changes only the builders. -/
theorem initiateBuilderExit_balances {gloas : .glamsterdam ≤ fork} {index : BuilderIndex}
    (computed : initiateBuilderExit config state gloas index = .ok after) :
    after.balances = state.balances := by
  unfold initiateBuilderExit at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, set⟩ := computed
  obtain ⟨_, rfl⟩ := setBuilder_ok set
  rfl

/-- From Gloas, a builder exit request changes only the builders. -/
theorem processBuilderExitRequest_balances {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    after.balances = state.balances := by
  unfold processBuilderExitRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; rfl)
    | exact initiateBuilderExit_balances (liftAccessor_ok.mp computed)

/-- From Gloas, settling the payment of the parent block changes only the builder queues. -/
theorem settleParentPayment_balances {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) :
    after.balances = state.balances := by
  unfold settleParentPayment at computed
  dsimp only at computed
  split at computed
  · rw [liftAccessor_ok] at computed
    unfold settleBuilderPayment at computed
    split at computed
    · cases computed
      rfl
    · cases computed
  · split at computed <;> (cases computed; rfl)

/-! ## Switching to compounding credentials -/

/-- The change of the balance above the activation balance, queued back as a deposit. -/
def excessChanges (index : ValidatorIndex) (excess : Nat) (i : Nat) : List BalanceChange :=
  if index.toNat = i then [.debit .excessQueued excess] else []

/-- From Electra, queuing the excess of a balance lowers it to the activation balance.

A balance at most the activation balance stays.

The excess joins the pending deposits. -/
theorem queueExcessActiveBalance_ledger {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    ∃ balance : Gwei, getBalance state index = .ok balance ∧
      after.validators = state.validators ∧
      BalanceLedger state after (excessChanges index
        (balance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat)) := by
  unfold queueExcessActiveBalance at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨balance, balanceOk, computed⟩ := computed
  have read : state.balances.data[index.toNat]? = some balance := by
    unfold getBalance at balanceOk
    split at balanceOk
    · rename_i found
      cases balanceOk
      exact found
    · cases balanceOk
  refine ⟨balance, balanceOk, ?_⟩
  split at computed
  · rename_i above
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, set, setOk, rfl⟩ := computed
    obtain ⟨inside, rfl⟩ := setBalance_ok setOk
    refine ⟨rfl, fun i => ?_⟩
    unfold balanceNat excessChanges
    have lt := UInt64.lt_iff_toNat_lt.mp above
    by_cases same : index.toNat = i
    · subst same
      have value : state.balances.data[index.toNat] = balance := by
        rw [Array.getElem?_eq_getElem inside] at read
        exact Option.some.inj read
      simp [BeaconState.putBalance, value, inside, BalanceChange.apply]
      omega
    · simp [BeaconState.putBalance, same]
  · rename_i atMost
    cases computed
    refine ⟨rfl, fun i => ?_⟩
    unfold balanceNat excessChanges
    have le := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp atMost)
    by_cases same : index.toNat = i
    · subst same
      simp [read, BalanceChange.apply]
      omega
    · simp [same]

/-- From Electra, a switch to compounding credentials queues the excess of the balance. -/
theorem switchToCompoundingValidator_ledger {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    ∃ balance : Gwei, getBalance state index = .ok balance ∧
      BalanceLedger state after (excessChanges index
        (balance.toNat - preset.MIN_ACTIVATION_BALANCE.toNat)) := by
  unfold switchToCompoundingValidator at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, set, setOk, queued⟩ := computed
  obtain ⟨balance, balanceOk, _, ledger⟩ := queueExcessActiveBalance_ledger queued
  obtain ⟨_, rfl⟩ := setValidator_ok setOk
  exact ⟨balance, balanceOk, ledger⟩

/-! ## Slashings -/

/-- A step that maps each balance by a function of its position has a ledger.

Its changes act as that function at each position that holds a balance. -/
theorem BalanceLedger.of_map {changes : Nat → List BalanceChange} {f : Nat → Nat → Nat}
    (mapped : ∀ i, (after.balances.data[i]?).map UInt64.toNat =
      (state.balances.data[i]?).map fun balance => f i balance.toNat)
    (acts : ∀ i balance, (changes i).foldl BalanceChange.apply balance = f i balance) :
    BalanceLedger state after fun i =>
      if i < state.balances.data.size then changes i else [] := by
  intro i
  unfold balanceNat
  rw [mapped i]
  dsimp only
  split
  · rename_i inside
    rw [Array.getElem?_eq_getElem inside]
    simp [acts]
  · rename_i outside
    rw [Array.getElem?_eq_none (by omega)]
    rfl

/-- The changes of one slashing: a debit of the slashed validator, then a credit of the proposer.
-/
def slashChanges (index proposer : ValidatorIndex) (penalty reward : Nat) (i : Nat) :
    List BalanceChange :=
  (if i = index.toNat then [.debit .slashing penalty] else []) ++
    (if i = proposer.toNat then [.credit .slashing reward] else [])

/-- The ledger of one slashing: the slashed validator pays its initial penalty.

The proposer, of the state just before the reward, then gets the whole whistleblower reward. -/
theorem slashValidator_ledger {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (computed : slashValidator config state index = .ok after) :
    ∃ (penalized : BeaconState preset fork) (proposer : ValidatorIndex),
      getBeaconProposerIndex penalized = .ok proposer ∧
      BalanceLedger state after fun i => if i < state.balances.data.size then
        slashChanges index proposer (initialSlashingPenalty preset fork validator)
          (whistleblowerReward preset fork validator).toNat i else [] := by
  obtain ⟨penalized, proposer, proposerOk, mapped⟩ := slashValidator_balances found computed
  refine ⟨penalized, proposer, proposerOk, BalanceLedger.of_map (f := fun i balance =>
    balance - (if i = index.toNat then initialSlashingPenalty preset fork validator else 0) +
      (if i = proposer.toNat then (whistleblowerReward preset fork validator).toNat else 0))
    mapped fun i balance => ?_⟩
  unfold slashChanges
  split <;> split <;> rfl

/-! ## Withdrawals -/

/-- The changes of some withdrawals to one balance: a debit for each that names it.

From Gloas a withdrawal of a builder names no balance of a validator. -/
def withdrawalChanges (fork : Base.Fork) (withdrawals : List Withdrawal) (i : Nat) :
    List BalanceChange :=
  withdrawals.flatMap fun withdrawal =>
    if ¬(.glamsterdam ≤ fork ∧ isBuilderIndex withdrawal.validatorIndex = true) ∧
        withdrawal.validatorIndex.toNat = i then
      [.debit .withdrawal withdrawal.amount.toNat]
    else []

/-- Withdrawals applied in turn debit each balance they name, in turn. -/
theorem foldlM_applyWithdrawal_ledger :
    ∀ {withdrawals : List Withdrawal} {state after : BeaconState preset fork},
      withdrawals.foldlM applyWithdrawal state = .ok after →
      BalanceLedger state after (withdrawalChanges fork withdrawals)
  | [], state, after, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    intro i
    rfl
  | withdrawal :: rest, state, after, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, folded⟩ := computed
    have first : BalanceLedger state middle (withdrawalChanges fork [withdrawal]) := by
      unfold applyWithdrawal at step
      split at step
      · rename_i builder
        simp only [bind_ok_iff] at step
        obtain ⟨_, _, set⟩ := step
        obtain ⟨_, rfl⟩ := setBuilder_ok set
        intro i
        simp [withdrawalChanges, builder, balanceNat, BeaconState.putBuilder]
      · rename_i notBuilder
        refine (decreaseBalance_ledger .withdrawal step).congr fun i => ?_
        have free : ¬(.glamsterdam ≤ fork ∧ isBuilderIndex withdrawal.validatorIndex = true) :=
          notBuilder
        simp only [withdrawalChanges, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          free, not_false_eq_true, true_and]
    refine (first.trans (foldlM_applyWithdrawal_ledger folded)).congr fun i => ?_
    simp [withdrawalChanges, List.foldl_append]

/-- The withdrawal step debits each balance by each withdrawal that names it, in turn.

The withdrawals are those that `AppliedWithdrawals` names. -/
theorem processWithdrawals_ledger {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    ∃ withdrawals, AppliedWithdrawals state after capella payload withdrawals ∧
      BalanceLedger state after (withdrawalChanges fork withdrawals.toList) := by
  obtain ⟨withdrawals, applied, named, -, applyOk, balances, -⟩ :=
    processWithdrawals_applied computed
  unfold applyWithdrawals at applyOk
  rw [← Array.foldlM_toList] at applyOk
  have ledger := foldlM_applyWithdrawal_ledger applyOk
  refine ⟨withdrawals, named, fun i => ?_⟩
  rw [← ledger i]
  simp [balanceNat, balances]

/-! ## Rewards paid inside a block -/

/-- A step that keeps the number of balances and maps each one by a function has a ledger.

Its changes act as that function at each position that holds a balance. -/
theorem BalanceLedger.of_some {changes : Nat → List BalanceChange} {f : Nat → Nat → Nat}
    (sizes : after.balances.data.size = state.balances.data.size)
    (sent : ∀ i balance, state.balances.data[i]? = some balance → ∃ final,
      after.balances.data[i]? = some final ∧ final.toNat = f i balance.toNat)
    (acts : ∀ i balance, (changes i).foldl BalanceChange.apply balance = f i balance) :
    BalanceLedger state after fun i =>
      if i < state.balances.data.size then changes i else [] := by
  intro i
  unfold balanceNat
  dsimp only
  split
  · rename_i inside
    obtain ⟨final, found, value⟩ := sent i _ (Array.getElem?_eq_getElem inside)
    rw [found, Array.getElem?_eq_getElem inside]
    simp [value, acts]
  · rename_i outside
    rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
    rfl

/-- From Altair, the ledger of an attestation: one credit to the proposer of the slot.

The credit is the numerator of the newly set flags over 448.

`processAttestationAltair_balance` gives that numerator. -/
theorem processAttestationAltair_ledger {attestation : Attestation preset fork}
    {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed : processAttestationAltair config checks state attestation altair parentSlot =
      .ok after) :
    ∃ (proposer : ValidatorIndex) (reward : Nat), getBeaconProposerIndex state = .ok proposer ∧
      BalanceLedger state after fun i => if i < state.balances.data.size then
        (if proposer.toNat = i then [.credit .blockReward reward] else []) else [] := by
  obtain ⟨earned, total, attesters, proposer, _, _, _, proposerOk, shares, _, _, sent⟩ :=
    processAttestationAltair_balance computed
  let reward := (shares.map fun share => newFlagsNumerator earned share.2.1 share.2.2).sum /
    ((WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) * WEIGHT_DENOMINATOR.toNat /
      PROPOSER_WEIGHT.toNat)
  refine ⟨proposer, reward, proposerOk, BalanceLedger.of_some
    (f := fun i balance => balance + if proposer.toNat = i then reward else 0)
    (sameSizes_processAttestationAltair computed).2 sent fun i balance => ?_⟩
  split <;> simp [BalanceChange.apply, *]

/-- The changes of the sync rewards to one balance, member by member in committee order. -/
def syncChanges (members : List (ValidatorIndex × Bool)) (proposer : ValidatorIndex)
    (reward proposerReward : Nat) (i : Nat) : List BalanceChange :=
  members.flatMap fun member =>
    if member.2 then
      (if member.1.toNat = i then [.credit .blockReward reward] else []) ++
        (if proposer.toNat = i then [.credit .blockReward proposerReward] else [])
    else if member.1.toNat = i then [.debit .blockReward reward] else []

/-- The sync changes act on a balance as the steps of the sync rewards do. -/
theorem foldl_syncChanges (proposer : ValidatorIndex) (reward proposerReward : Nat) (i : Nat) :
    ∀ (members : List (ValidatorIndex × Bool)) (balance : Nat),
      (syncChanges members proposer reward proposerReward i).foldl BalanceChange.apply balance =
        members.foldl (fun balance member =>
          if member.2 then balance + (if member.1.toNat = i then reward else 0) +
            (if proposer.toNat = i then proposerReward else 0)
          else if member.1.toNat = i then balance - reward else balance) balance
  | [], _ => rfl
  | (index, signed) :: rest, balance => by
    rw [List.foldl_cons, ← foldl_syncChanges proposer reward proposerReward i rest]
    simp only [syncChanges, List.flatMap_cons, List.foldl_append]
    congr 1
    cases signed <;> by_cases one : index.toNat = i <;> by_cases two : proposer.toNat = i <;>
      simp [one, two, BalanceChange.apply]

/-- From Altair, the ledger of the sync aggregate, member by member in committee order.

A member that signed is credited the participant reward, and the proposer its share.

A member that did not sign is debited the participant reward. -/
theorem processSyncAggregate_ledger {altair : .altair ≤ fork} {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    ∃ (reward proposerReward : Gwei) (members : Array ValidatorIndex) (proposer : ValidatorIndex),
      syncParticipantReward state = .ok reward ∧
      proposerReward.toNat =
        reward.toNat * PROPOSER_WEIGHT.toNat / (WEIGHT_DENOMINATOR.toNat - PROPOSER_WEIGHT.toNat) ∧
      (state.currentSyncCommittee altair).value.pubkeys.toArray.mapM
        (validatorIndexOfPubkey state) = .ok members ∧
      ((∃ member ∈ (members.zip aggregate.syncCommitteeBits.bits.toArray).toList,
        member.2 = true) → getBeaconProposerIndex state = .ok proposer) ∧
      BalanceLedger state after fun i => if i < state.balances.data.size then
        syncChanges (members.zip aggregate.syncCommitteeBits.bits.toArray).toList proposer
          reward.toNat proposerReward.toNat i else [] := by
  obtain ⟨reward, proposerReward, members, proposer, rewardOk, share, membersOk, read, sent⟩ :=
    processSyncAggregate_balance computed
  exact ⟨reward, proposerReward, members, proposer, rewardOk, share, membersOk, read,
    BalanceLedger.of_some (sameSizes_processSyncAggregate computed).2 sent
      (foldl_syncChanges proposer _ _ · _ ·)⟩

/-! ## Ledgers by kind of change -/

/-- A step has a ledger whose changes are all of one kind. -/
def LedgerOf (allowed : BalanceChange → Prop) (state after : BeaconState preset fork) : Prop :=
  ∃ changes : Nat → List BalanceChange, BalanceLedger state after changes ∧
    ∀ i, ∀ change ∈ changes i, allowed change

/-- A step that keeps the balances has a ledger of any kind. -/
theorem LedgerOf.of_balances {allowed : BalanceChange → Prop}
    (same : after.balances = state.balances) : LedgerOf allowed state after :=
  ⟨fun _ => [], BalanceLedger.of_balances same, fun _ _ absent => absurd absent List.not_mem_nil⟩

/-- Two steps of one kind make a step of that kind. -/
theorem LedgerOf.trans {allowed : BalanceChange → Prop} {middle : BeaconState preset fork}
    (one : LedgerOf allowed state middle) (two : LedgerOf allowed middle after) :
    LedgerOf allowed state after := by
  obtain ⟨first, firstLedger, firstAllowed⟩ := one
  obtain ⟨second, secondLedger, secondAllowed⟩ := two
  refine ⟨fun i => first i ++ second i, firstLedger.trans secondLedger, fun i change member => ?_⟩
  rcases List.mem_append.mp member with member | member
  · exact firstAllowed i change member
  · exact secondAllowed i change member

/-- A fold whose every step is of one kind is of that kind. -/
theorem LedgerOf.foldlM {α ε : Type} {allowed : BalanceChange → Prop}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (each : ∀ last x next, step last x = .ok next → LedgerOf allowed last next) :
    ∀ {xs : List α} {state after : BeaconState preset fork},
      xs.foldlM step state = .ok after → LedgerOf allowed state after
  | [], state, after, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact LedgerOf.of_balances rfl
  | x :: rest, state, after, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepped, folded⟩ := computed
    exact (each _ _ _ stepped).trans (LedgerOf.foldlM each folded)

/-- A change of slashing: a penalty or a reward for reporting. -/
def IsSlashing : BalanceChange → Prop
  | .credit flow _ => flow = .slashing
  | .debit flow _ => flow = .slashing

/-- A slashing of a validator is a step of slashing changes. -/
theorem slashValidator_ledgerOf {index : ValidatorIndex}
    (computed : slashValidator config state index = .ok after) :
    LedgerOf IsSlashing state after := by
  -- The step reads the validator first, so it exists.
  obtain ⟨validator, found⟩ : ∃ validator, getValidator state index = .ok validator := by
    unfold slashValidator at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨_, exitedOk, _⟩ := computed
    obtain ⟨validator, found, _⟩ := initiateValidatorExit_ok exitedOk
    exact ⟨validator, found⟩
  obtain ⟨_, proposer, _, ledger⟩ := slashValidator_ledger found computed
  refine ⟨_, ledger, fun i change member => ?_⟩
  split at member
  · simp only [slashChanges, List.mem_append] at member
    rcases member with member | member <;> split at member <;>
      simp_all [IsSlashing]
  · cases member

/-- A proposer slashing is a step of slashing changes. -/
theorem processProposerSlashing_ledgerOf {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    LedgerOf IsSlashing state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  peel computed
  exact slashValidator_ledgerOf computed

/-- An attester slashing is a step of slashing changes. -/
theorem processAttesterSlashing_ledgerOf {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    LedgerOf IsSlashing state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  peel computed
  have each : ∀ (last : BeaconState preset fork × Bool) (index : ValidatorIndex) next,
      slashIfSlashable config last index = .ok next → LedgerOf IsSlashing last.1 next.1 := by
    intro ⟨last, slashedAny⟩ index next step
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨_, _, step⟩ := step
    split at step
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at step
      obtain ⟨_, slashedOk, rfl⟩ := step
      exact slashValidator_ledgerOf slashedOk
    · cases step
      exact LedgerOf.of_balances rfl
  -- The fold carries a flag beside the state, so it is read on the first component.
  have folds : ∀ (indices : List ValidatorIndex) (start result : BeaconState preset fork × Bool),
      indices.foldlM (slashIfSlashable config) start = .ok result →
      LedgerOf IsSlashing start.1 result.1 := by
    intro indices
    induction indices with
    | nil =>
      intro start result computed
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact LedgerOf.of_balances rfl
    | cons index rest ih =>
      intro start result computed
      rw [List.foldlM_cons, bind_ok_iff] at computed
      obtain ⟨middle, stepped, folded⟩ := computed
      exact (each _ _ _ stepped).trans (ih _ _ folded)
  exact folds _ (state, false) _ ‹_›

/-- A fold whose every step is of one kind, where a property holds, is of that kind.

The property must hold at the start and be kept by each step. -/
theorem LedgerOf.foldlM_of {α ε : Type} {allowed : BalanceChange → Prop}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (Keep : BeaconState preset fork → Prop)
    (each : ∀ last x next, Keep last → step last x = .ok next →
      Keep next ∧ LedgerOf allowed last next) :
    ∀ {xs : List α} {state after : BeaconState preset fork}, Keep state →
      xs.foldlM step state = .ok after → LedgerOf allowed state after
  | [], state, after, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact LedgerOf.of_balances rfl
  | x :: rest, state, after, kept, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepped, folded⟩ := computed
    obtain ⟨kept', ledger⟩ := each _ _ _ kept stepped
    exact ledger.trans (LedgerOf.foldlM_of Keep each kept' folded)

/-- A credit of a deposit. -/
def IsDeposit : BalanceChange → Prop
  | .credit flow _ => flow = .deposit
  | .debit _ _ => False

/-- A deposit of a block, before Heze, is a step of deposit credits.

Before Electra it credits the validator of its key, or a new one.

From Electra it only queues the deposit, and a new validator starts with no balance.

That needs one balance for each validator, and a registry below `2^64`. -/
theorem processDeposit_ledgerOf {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after)
    (holds : BalancesMatch state) (small : state.validators.data.size < 2 ^ 64) :
    LedgerOf IsDeposit state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  -- Moving the deposit index keeps the balances and the registry.
  let moved : BeaconState preset fork := { state with eth1DepositIndex := fun _ => next }
  have first : LedgerOf IsDeposit state moved := LedgerOf.of_balances rfl
  refine first.trans ?_
  have holds' : BalancesMatch moved := holds
  unfold applyDeposit at applied
  split at applied
  · -- From Electra a new validator starts with no balance, and the deposit waits in the queue.
    unfold applyDepositElectra at applied
    split at applied
    · simp only [bind, Except.bind] at applied
      split at applied
      · cases applied
      split at applied
      · split at applied
        · cases applied
        rename_i added addedOk
        obtain ⟨_, balances⟩ := addValidatorToRegistry_push addedOk holds' small
        simp only [liftAccessor_ok, addPendingDeposit, bind_ok_iff, pure, Except.pure,
          Except.ok.injEq] at applied
        obtain ⟨_, _, rfl⟩ := applied
        refine ⟨fun _ => [], fun i => ?_, fun _ _ absent => absurd absent List.not_mem_nil⟩
        simp only [balanceNat, balances, Array.getElem?_push, List.foldl_nil]
        split
        · rename_i same
          subst same
          show 0 = ((state.balances.data[state.balances.data.size]?).map UInt64.toNat).getD 0
          simp
        · rfl
      · cases applied
        exact LedgerOf.of_balances rfl
    · simp only [liftAccessor_ok, addPendingDeposit, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at applied
      obtain ⟨_, _, rfl⟩ := applied
      exact LedgerOf.of_balances rfl
  · obtain ⟨target, _, _, _, ledger⟩ := applyPendingDeposit_ledger applied holds' small
    refine ⟨_, ledger, fun i change member => ?_⟩
    simp only [depositChanges] at member
    split at member
    · simp only [List.mem_singleton] at member
      subst member
      rfl
    · cases member

/-! ## Requests of the execution layer -/

/-- A debit of the excess of a balance, queued back as a deposit. -/
def IsExcessQueued : BalanceChange → Prop
  | .credit _ _ => False
  | .debit flow _ => flow = .excessQueued

/-- From Electra, queuing a consolidation keeps the balances. -/
theorem queueConsolidation_balances {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed : queueConsolidation config state electra sourcePosition source targetIndex =
      .ok after) : after.balances = state.balances := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨⟨churned, _⟩, churnedOk, _, _, set, setOk, _, _, rfl⟩ := computed
  exact (setValidator_balances setOk).trans
    (computeConsolidationEpochAndUpdateChurn_earliest churnedOk).2.2

/-- From Electra, a consolidation request debits at most the excess of one balance.

A switch to compounding credentials queues that excess back as a deposit.

A consolidation between two validators only joins the queue. -/
theorem processConsolidationRequest_ledgerOf {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    LedgerOf IsExcessQueued state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact LedgerOf.of_balances rfl)
    | exact LedgerOf.of_balances (queueConsolidation_balances computed)
    | (obtain ⟨_, _, ledger⟩ := switchToCompoundingValidator_ledger (liftAccessor_ok.mp computed)
       exact ⟨_, ledger, fun i change member => by
         simp only [excessChanges] at member
         split at member
         · simp only [List.mem_singleton] at member
           subst member
           rfl
         · cases member⟩)

/-- From Electra, the requests of a payload are a step of excess debits. -/
theorem requests_ledgerOf {electra : .pectra ≤ fork} {requests : ExecutionRequests preset fork}
    {middle withdrawn : BeaconState preset fork}
    (deposited : requests.deposits.data.foldlM (processDepositRequest · electra ·) state =
      .ok middle)
    (exited : requests.withdrawals.data.foldlM (processWithdrawalRequest config · electra ·)
      middle = .ok withdrawn)
    (consolidated : requests.consolidations.data.foldlM
      (processConsolidationRequest config · electra ·) withdrawn = .ok after) :
    LedgerOf IsExcessQueued state after := by
  rw [← Array.foldlM_toList] at deposited exited consolidated
  exact ((LedgerOf.foldlM (fun _ _ _ step =>
      LedgerOf.of_balances (processDepositRequest_balances step)) deposited).trans
    (LedgerOf.foldlM (fun _ _ _ step =>
      LedgerOf.of_balances (processWithdrawalRequest_balances step)) exited)).trans
    (LedgerOf.foldlM (fun _ _ _ step => processConsolidationRequest_ledgerOf step) consolidated)

/-- In Electra and Fulu, the requests of a block are a step of excess debits. -/
theorem processExecutionRequests_ledgerOf {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    LedgerOf IsExcessQueued state after := by
  simp only [processExecutionRequests, bind_ok_iff] at computed
  obtain ⟨middle, deposited, withdrawn, exited, consolidated⟩ := computed
  exact requests_ledgerOf deposited exited consolidated

/-- From Gloas, the requests of the parent payload are a step of excess debits. -/
theorem processParentRequests_ledgerOf {gloas : .glamsterdam ≤ fork}
    {requests : ExecutionRequests preset fork}
    (computed : processParentRequests config checks state gloas requests = .ok after) :
    LedgerOf IsExcessQueued state after := by
  simp only [processParentRequests, bind_ok_iff] at computed
  obtain ⟨middle, deposited, withdrawn, exited, consolidated, consolidatedOk, built, builtOk,
    exitedBuilders⟩ := computed
  rw [← Array.foldlM_toList] at builtOk exitedBuilders
  exact ((requests_ledgerOf deposited exited consolidatedOk).trans
    (LedgerOf.foldlM (fun _ _ _ step =>
      LedgerOf.of_balances (processBuilderDepositRequest_balances step)) builtOk)).trans
    (LedgerOf.foldlM (fun _ _ _ step =>
      LedgerOf.of_balances (processBuilderExitRequest_balances step)) exitedBuilders)

/-- From Gloas, the payload of the parent block is a step of excess debits.

Its requests may switch validators to compounding credentials.

Its payment to the builder, and its builder requests, change no balance of a validator. -/
theorem processParentExecutionPayload_ledgerOf {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    LedgerOf IsExcessQueued state after := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact LedgerOf.of_balances rfl
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  unfold applyParentExecutionPayload at applied
  simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at applied
  peel applied
  rename_i settled settledOk requested requestedOk _ _
  refine ((LedgerOf.of_balances (settleParentPayment_balances settledOk)).trans
    (processParentRequests_ledgerOf requestedOk)).trans (LedgerOf.of_balances rfl)

/-! ## The operations of a block -/

/-- A credit of a reward to the proposer of a block. -/
def IsProposerCredit : BalanceChange → Prop
  | .credit flow _ => flow = .blockReward
  | .debit _ _ => False

/-- An attestation is a step of credits to the proposer.

Before Altair it only joins the pending attestations. -/
theorem processAttestation_ledgerOf {parentSlot : Slot} {attestation : Attestation preset fork}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    LedgerOf IsProposerCredit state after := by
  by_cases altair : .altair ≤ fork
  · rw [processAttestation_of_altair altair] at computed
    obtain ⟨proposer, reward, _, ledger⟩ := processAttestationAltair_ledger computed
    refine ⟨_, ledger, fun i change member => ?_⟩
    repeat' split at member
    all_goals simp_all [IsProposerCredit]
  · obtain ⟨_, _, _, _, _, recorded, _⟩ :=
      processAttestation_records (Nat.lt_of_not_le altair) computed
    refine LedgerOf.of_balances ?_
    unfold recordPendingAttestation at recorded
    dsimp only at recorded
    repeat' split at recorded
    all_goals first
      | (cases recorded; done)
      | (cases recorded; rfl)
      | (simp only [Except.ok.injEq] at recorded; rw [← recorded])

/-- A change of the sync rewards: a credit, or a debit of a member that did not sign. -/
def IsSyncReward : BalanceChange → Prop
  | .credit flow _ => flow = .blockReward
  | .debit flow _ => flow = .blockReward

/-- A debit of a withdrawal. -/
def IsWithdrawal : BalanceChange → Prop
  | .credit _ _ => False
  | .debit flow _ => flow = .withdrawal

/-- The withdrawal step is a step of withdrawal debits. -/
theorem processWithdrawals_ledgerOf {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    LedgerOf IsWithdrawal state after := by
  obtain ⟨withdrawals, _, ledger⟩ := processWithdrawals_ledger computed
  refine ⟨_, ledger, fun i change member => ?_⟩
  simp only [withdrawalChanges, List.mem_flatMap] at member
  obtain ⟨_, _, member⟩ := member
  split at member
  · simp only [List.mem_singleton] at member
    subst member
    rfl
  · cases member

/-- The sync changes are all sync rewards. -/
theorem syncChanges_isSyncReward {members : List (ValidatorIndex × Bool)}
    {proposer : ValidatorIndex} {reward proposerReward i : Nat} {change : BalanceChange}
    (member : change ∈ syncChanges members proposer reward proposerReward i) :
    IsSyncReward change := by
  simp only [syncChanges, List.mem_flatMap] at member
  obtain ⟨_, _, member⟩ := member
  split at member
  · rcases List.mem_append.mp member with member | member
    · split at member
      · rw [List.mem_singleton.mp member]
        rfl
      · cases member
    · split at member
      · rw [List.mem_singleton.mp member]
        rfl
      · cases member
  · split at member
    · rw [List.mem_singleton.mp member]
      rfl
    · cases member

/-- From Altair, the sync aggregate is a step of sync rewards. -/
theorem processSyncAggregate_ledgerOf {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    LedgerOf IsSyncReward state after := by
  obtain ⟨_, _, _, _, _, _, _, _, ledger⟩ := processSyncAggregate_ledger computed
  refine ⟨_, ledger, fun i change member => ?_⟩
  split at member
  · exact syncChanges_isSyncReward member
  · cases member

/-- Sizes kept along a fold, for a step that keeps them. -/
theorem SameSizes.foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (each : ∀ last x next, step last x = .ok next → SameSizes last next)
    {xs : List α} (computed : xs.foldlM step state = .ok after) : SameSizes state after :=
  foldlM_ok_invariant (SameSizes state) (fun _ _ _ sizes step => sizes.trans (each _ _ _ step))
    (SameSizes.refl state) computed

/-- The operations of a block, as four parts in turn.

The slashings come first, then the credits of the attestations to the proposer.

Before Heze the deposits follow, and from Electra to Gloas the requests of the payload.

The exits, the changes of credentials and the payload attestations keep the balances.

Before Gloas that needs one balance for each validator. -/
theorem processOperations_ledger {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after)
    (holds : fork < .glamsterdam → BalancesMatch state) :
    ∃ slashings credits deposits requests : Nat → List BalanceChange,
      BalanceLedger state after
        (fun i => slashings i ++ credits i ++ deposits i ++ requests i) ∧
      (∀ i, ∀ change ∈ slashings i, IsSlashing change) ∧
      (∀ i, ∀ change ∈ credits i, IsProposerCredit change) ∧
      (∀ i, ∀ change ∈ deposits i, IsDeposit change) ∧
      (∀ i, ∀ change ∈ requests i, IsExcessQueued change) := by
  unfold processOperations at computed
  split at computed
  · rename_i gloas
    unfold processOperationsGloas at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, proposed, proposedOk, attested, attestedOk,
      included, includedOk, exited, exitedOk, changed, changedOk, last⟩ := computed
    rw [← Array.foldlM_toList] at proposedOk attestedOk includedOk exitedOk changedOk last
    obtain ⟨one, oneLedger, oneKind⟩ := (LedgerOf.foldlM (fun _ _ _ step =>
      processProposerSlashing_ledgerOf step) proposedOk).trans
        (LedgerOf.foldlM (fun _ _ _ step => processAttesterSlashing_ledgerOf step) attestedOk)
    obtain ⟨two, twoLedger, twoKind⟩ := LedgerOf.foldlM (fun _ _ _ step =>
      processAttestation_ledgerOf step) includedOk
    have rest : after.balances = included.balances := by
      rw [foldlM_balances (fun _ _ _ step => processPayloadAttestation_balances step) last,
        foldlM_balances (fun _ _ _ step => processBlsToExecutionChange_balances step) changedOk,
        foldlM_balances (fun _ _ _ step => processVoluntaryExit_balances step) exitedOk]
    refine ⟨one, two, fun _ => [], fun _ => [], ?_, oneKind, twoKind,
      fun _ _ absent => absurd absent List.not_mem_nil,
      fun _ _ absent => absurd absent List.not_mem_nil⟩
    refine ((oneLedger.trans twoLedger).trans (BalanceLedger.of_balances rest)).congr
      fun i => by simp
  · rename_i notGloas
    have before : fork < .glamsterdam := Nat.lt_of_not_le notGloas
    simp only [bind_ok_iff, ensure_ok_iff] at computed
    obtain ⟨_, _, _, _, proposed, proposedOk, attested, attestedOk, included, includedOk,
      deposited, depositedOk, exited, exitedOk, changed, changedOk, last⟩ := computed
    rw [← Array.foldlM_toList] at proposedOk attestedOk includedOk depositedOk exitedOk
    obtain ⟨one, oneLedger, oneKind⟩ := (LedgerOf.foldlM (fun _ _ _ step =>
      processProposerSlashing_ledgerOf step) proposedOk).trans
        (LedgerOf.foldlM (fun _ _ _ step => processAttesterSlashing_ledgerOf step) attestedOk)
    obtain ⟨two, twoLedger, twoKind⟩ := LedgerOf.foldlM (fun _ _ _ step =>
      processAttestation_ledgerOf step) includedOk
    -- The slashings and the attestations keep the sizes, so the deposits start matched.
    have sizes : SameSizes state included :=
      ((SameSizes.foldlM (fun _ _ _ step => sameSizes_processProposerSlashing step)
        proposedOk).trans (SameSizes.foldlM (fun _ _ _ step =>
          sameSizes_processAttesterSlashing step) attestedOk)).trans
        (SameSizes.foldlM (fun _ _ _ step => sameSizes_processAttestation step) includedOk)
    obtain ⟨three, threeLedger, threeKind⟩ := LedgerOf.foldlM_of (allowed := IsDeposit)
      (fun s => BalancesMatch s) (fun last _ next kept step =>
        ⟨balancesMatch_processDeposit step kept, processDeposit_ledgerOf step kept
          (Nat.lt_of_le_of_lt (last.validators.bound before)
            preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt)⟩)
      (balancesMatch_of_sameSizes sizes (holds before)) depositedOk
    have exits : exited.balances = deposited.balances :=
      foldlM_balances (fun _ _ _ step => processVoluntaryExit_balances step) exitedOk
    have changes : changed.balances = exited.balances := by
      unfold processBlsToExecutionChanges at changedOk
      split at changedOk
      · rw [← Array.foldlM_toList] at changedOk
        exact foldlM_balances (fun _ _ _ step => processBlsToExecutionChange_balances step)
          changedOk
      · cases changedOk
        rfl
    obtain ⟨four, fourLedger, fourKind⟩ : LedgerOf IsExcessQueued changed after := by
      split at last
      · exact processExecutionRequests_ledgerOf last
      · cases last
        exact LedgerOf.of_balances rfl
    refine ⟨one, two, three, four, ?_, oneKind, twoKind, threeKind, fourKind⟩
    refine ((((oneLedger.trans twoLedger).trans threeLedger).trans
      (BalanceLedger.of_balances (changes.trans exits))).trans fourLedger).congr fun i => by simp

/-! ## The block -/

/-- The execution payload keeps the sizes. -/
theorem sameSizes_processExecutionPayload {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    SameSizes state after := by
  simp only [processExecutionPayload, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  peel computed
  exact ⟨rfl, rfl⟩

/-- The kinds of change of a block, part by part, in turn.

From Gloas the payload of the parent block may queue the excess of balances.

From Capella the withdrawals debit balances.

The slashings, the credits of the attestations, the deposits and the requests follow.

From Altair the sync rewards come last. -/
def BlockLedger (state after : BeaconState preset fork) : Prop :=
  ∃ excess withdrawals slashings credits deposits requests sync : Nat → List BalanceChange,
    BalanceLedger state after (fun i => excess i ++ withdrawals i ++ slashings i ++ credits i ++
      deposits i ++ requests i ++ sync i) ∧
    (∀ i, ∀ change ∈ excess i, IsExcessQueued change) ∧
    (∀ i, ∀ change ∈ withdrawals i, IsWithdrawal change) ∧
    (∀ i, ∀ change ∈ slashings i, IsSlashing change) ∧
    (∀ i, ∀ change ∈ credits i, IsProposerCredit change) ∧
    (∀ i, ∀ change ∈ deposits i, IsDeposit change) ∧
    (∀ i, ∀ change ∈ requests i, IsExcessQueued change) ∧
    (∀ i, ∀ change ∈ sync i, IsSyncReward change)

/-- The ledger of a block, at every fork.

Each balance takes the parts of `BlockLedger` in turn.

They are the excess queued by the parent payload, the withdrawals and the slashings.

Then come the credits of the attestations, the deposits, the requests and the sync rewards.

Every other step of a block keeps the balances.

That needs one balance for each validator. -/
theorem processBlock_ledger {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (holds : BalancesMatch state) : BlockLedger state after := by
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
    obtain ⟨withdrawals, withdrawalLedger, withdrawalKind⟩ : LedgerOf IsWithdrawal s2 s3 := by
      split at s3Ok
      · unfold processBlockExecution at s3Ok
        dsimp only at s3Ok
        split at s3Ok
        · simp only [bind_ok_iff] at s3Ok
          obtain ⟨withdrawn, withdrawnOk, bid⟩ := s3Ok
          exact (processWithdrawals_ledgerOf withdrawnOk).trans
            (LedgerOf.of_balances (processExecutionPayloadBid_balances bid))
        · split at s3Ok
          · simp only [bind_ok_iff] at s3Ok
            obtain ⟨withdrawn, withdrawnOk, paid⟩ := s3Ok
            exact (processWithdrawals_ledgerOf withdrawnOk).trans
              (LedgerOf.of_balances (processExecutionPayload_balances paid))
          · split at s3Ok
            · exact LedgerOf.of_balances (processExecutionPayload_balances s3Ok)
            · cases s3Ok
              exact LedgerOf.of_balances rfl
      · cases s3Ok
        exact LedgerOf.of_balances rfl
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
    obtain ⟨sync, syncLedger, syncKind⟩ := processSyncAggregate_ledgerOf last
    refine ⟨excess, withdrawals, slashings, credits, deposits, requests, sync, ?_, excessKind,
      withdrawalKind, slashingKind, creditKind, depositKind, requestKind, syncKind⟩
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
    refine ⟨fun _ => [], fun _ => [], slashings, credits, deposits, requests, fun _ => [], ?_,
      fun _ _ absent => absurd absent List.not_mem_nil,
      fun _ _ absent => absurd absent List.not_mem_nil, slashingKind, creditKind,
      depositKind, requestKind, fun _ _ absent => absurd absent List.not_mem_nil⟩
    have frame : s3.balances = state.balances := (processEth1Data_balances s3Ok).trans
      ((processRandao_balances s2Ok).trans (processBlockHeader_balances s1Ok))
    exact ((BalanceLedger.of_balances frame).trans operationsLedger).congr fun i => by simp

end EthLib.Consensus
