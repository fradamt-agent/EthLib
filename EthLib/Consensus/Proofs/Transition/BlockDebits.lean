module

public import EthLib.Consensus.Proofs.Transition.BlockLedger
public import EthLib.Consensus.Proofs.Transition.SlashingPayouts
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

/-! ## The slashings of a block -/

/-- The initial penalties of the payouts that slash the validator at a position. -/
def payoutPenalties (payouts : List (SlashingPayout preset)) (i : Nat) : Nat :=
  ((payouts.filter fun payout => payout.index.toNat == i).map fun payout =>
    initialSlashingPenalty preset payout.fork payout.validator).sum

theorem payoutPenalties_append (first second : List (SlashingPayout preset)) (i : Nat) :
    payoutPenalties (first ++ second) i = payoutPenalties first i + payoutPenalties second i := by
  simp [payoutPenalties, List.filter_append]

/-- A step of slashings, with the payouts it makes.

Its changes are all of slashing.

They debit each balance at most the initial penalties of the payouts that slash it. -/
def SlashingDebits (state after : BeaconState preset fork)
    (payouts : List (SlashingPayout preset)) : Prop :=
  ∃ changes : Nat → List BalanceChange, BalanceLedger state after changes ∧
    (∀ i, ∀ change ∈ changes i, IsSlashing change) ∧
    ∀ i, BalanceChange.debited .slashing (changes i) ≤ payoutPenalties payouts i

theorem SlashingDebits.of_balances (same : after.balances = state.balances) :
    SlashingDebits state after [] :=
  ⟨fun _ => [], BalanceLedger.of_balances same, fun _ _ absent => absurd absent List.not_mem_nil,
    fun _ => by simp [BalanceChange.debited]⟩

theorem SlashingDebits.trans {middle : BeaconState preset fork}
    {first second : List (SlashingPayout preset)} (one : SlashingDebits state middle first)
    (two : SlashingDebits middle after second) : SlashingDebits state after (first ++ second) := by
  obtain ⟨firstChanges, firstLedger, firstKind, firstBound⟩ := one
  obtain ⟨secondChanges, secondLedger, secondKind, secondBound⟩ := two
  refine ⟨fun i => firstChanges i ++ secondChanges i, firstLedger.trans secondLedger,
    fun i change member => ?_, fun i => ?_⟩
  · rcases List.mem_append.mp member with member | member
    · exact firstKind i change member
    · exact secondKind i change member
  · rw [BalanceChange.debited_append, payoutPenalties_append]
    exact Nat.add_le_add (firstBound i) (secondBound i)

/-- A slashing of a validator debits it its initial penalty, and credits the proposer. -/
theorem slashValidator_slashingDebits {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (computed : slashValidator config state index = .ok after) :
    SlashingDebits state after [⟨fork, state, after, index, validator⟩] := by
  obtain ⟨_, proposer, _, ledger⟩ := slashValidator_ledger found computed
  refine ⟨_, ledger, fun i change member => ?_, fun i => ?_⟩
  · split at member
    · simp only [slashChanges, List.mem_append] at member
      rcases member with member | member <;> split at member <;>
        simp_all [IsSlashing]
    · cases member
  · -- Only the debit at the slashed index is of slashing; the credit to the proposer is not.
    have credit : ∀ amount, BalanceChange.debited .slashing
        (if i = proposer.toNat then [.credit .slashing amount] else []) = 0 := by
      intro amount
      split <;> simp [BalanceChange.debited]
    split
    · simp only [slashChanges, BalanceChange.debited_append, credit, Nat.add_zero]
      by_cases here : i = index.toNat
      · subst here
        simp [payoutPenalties, BalanceChange.debited]
      · simp [here, BalanceChange.debited]
    · simp [BalanceChange.debited]

/-- The proposer slashings of a block debit at most the penalties of their payouts. -/
theorem proposerSlashingPayouts_debits (slashings : List ProposerSlashing)
    {state after : BeaconState preset fork}
    (computed : slashings.foldlM (processProposerSlashing config checks) state = .ok after) :
    ∃ payouts, proposerSlashingPayouts config checks slashings state = .ok (after, payouts) ∧
      SlashingDebits state after payouts := by
  induction slashings generalizing state with
  | nil =>
    cases computed
    exact ⟨[], rfl, .of_balances rfl⟩
  | cons slashing rest more =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp computed
    obtain ⟨payouts, collected, debits⟩ := more tail
    obtain ⟨_, _, _, validator, found, _, _⟩ := processProposerSlashing_checks first
    have called := first
    simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at called
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, called⟩ := called
    refine ⟨_ :: payouts, ?_, (slashValidator_slashingDebits found called).trans debits⟩
    simp [proposerSlashingPayouts, first, slashingPayout, found, liftAccessor, Except.mapError,
      collected, bind, Except.bind, pure, Except.pure]

/-- The steps of an attester slashing debit at most the penalties of their payouts. -/
theorem indexSlashingPayouts_debits (indices : List ValidatorIndex)
    {step after : BeaconState preset fork × Bool}
    (computed : indices.foldlM (slashIfSlashable config) step = .ok after) :
    ∃ payouts, indexSlashingPayouts config indices step = .ok (after, payouts) ∧
      SlashingDebits step.1 after.1 payouts := by
  induction indices generalizing step with
  | nil =>
    cases computed
    exact ⟨[], rfl, .of_balances rfl⟩
  | cons index rest more =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp computed
    obtain ⟨payouts, collected, debits⟩ := more tail
    have read := first
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at read
    obtain ⟨validator, found, action⟩ := read
    by_cases slashable : isSlashableValidator validator (getCurrentEpoch step.1) = true
    · simp only [slashable, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at action
      obtain ⟨slashed, called, rfl⟩ := action
      refine ⟨_ :: payouts, ?_, (slashValidator_slashingDebits found called).trans debits⟩
      simp [indexSlashingPayouts, first, found, liftAccessor, Except.mapError, collected,
        slashable, slashingPayout, bind, Except.bind, pure, Except.pure]
    · have same : middle = step := by
        simpa [slashable, pure, Except.pure] using action.symm
      subst same
      refine ⟨payouts, ?_, debits⟩
      simp [indexSlashingPayouts, first, found, liftAccessor, Except.mapError, collected,
        slashable, bind, Except.bind, pure, Except.pure]

/-- The attester slashings of a block debit at most the penalties of their payouts. -/
theorem attesterSlashingPayouts_debits (slashings : List (AttesterSlashing preset fork))
    {state after : BeaconState preset fork}
    (computed : slashings.foldlM (processAttesterSlashing config checks) state = .ok after) :
    ∃ payouts, attesterSlashingPayouts config checks slashings state = .ok (after, payouts) ∧
      SlashingDebits state after payouts := by
  induction slashings generalizing state with
  | nil =>
    cases computed
    exact ⟨[], rfl, .of_balances rfl⟩
  | cons slashing rest more =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp computed
    obtain ⟨payouts, collected, debits⟩ := more tail
    have read := first
    simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at read
    obtain ⟨_, _, _, _, _, _, _, _, _, _, folded, foldOk, done⟩ := read
    simp only [pure, Except.pure, Except.ok.injEq] at done
    obtain ⟨_, _, rfl⟩ := done
    obtain ⟨paid, paidOk, paidDebits⟩ := indexSlashingPayouts_debits _ foldOk
    refine ⟨paid ++ payouts, ?_, paidDebits.trans debits⟩
    simp [attesterSlashingPayouts, first, paidOk, collected, bind, Except.bind, pure,
      Except.pure]

/-- The operations of a block, as four parts in turn, with the payouts of its slashings.

It is `processOperations_ledger`, with the slashing debits bounded by the payouts.

Before Gloas that needs one balance for each validator. -/
theorem processOperations_debits {body : BeaconBlockBody preset fork} {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after)
    (holds : fork < .glamsterdam → BalancesMatch state) :
    ∃ (proposed : BeaconState preset fork) (first : List (SlashingPayout preset))
      (attested : BeaconState preset fork) (second : List (SlashingPayout preset))
      (slashings credits deposits requests : Nat → List BalanceChange),
      proposerSlashingPayouts config checks body.proposerSlashings.data.toList state =
        .ok (proposed, first) ∧
      attesterSlashingPayouts config checks body.attesterSlashings.data.toList proposed =
        .ok (attested, second) ∧
      BalanceLedger state after
        (fun i => slashings i ++ credits i ++ deposits i ++ requests i) ∧
      (∀ i, ∀ change ∈ slashings i, IsSlashing change) ∧
      (∀ i, ∀ change ∈ credits i, IsProposerCredit change) ∧
      (∀ i, ∀ change ∈ deposits i, IsDeposit change) ∧
      (∀ i, ∀ change ∈ requests i, IsExcessQueued change) ∧
      ∀ i, BalanceChange.debited .slashing (slashings i) ≤ payoutPenalties (first ++ second) i := by
  unfold processOperations at computed
  split at computed
  · rename_i gloas
    unfold processOperationsGloas at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, proposed, proposedOk, attested, attestedOk,
      included, includedOk, exited, exitedOk, changed, changedOk, last⟩ := computed
    rw [← Array.foldlM_toList] at proposedOk attestedOk includedOk exitedOk changedOk last
    obtain ⟨first, firstOk, firstDebits⟩ := proposerSlashingPayouts_debits _ proposedOk
    obtain ⟨second, secondOk, secondDebits⟩ := attesterSlashingPayouts_debits _ attestedOk
    obtain ⟨one, oneLedger, oneKind, oneBound⟩ := firstDebits.trans secondDebits
    obtain ⟨two, twoLedger, twoKind⟩ := LedgerOf.foldlM (fun _ _ _ step =>
      processAttestation_ledgerOf step) includedOk
    have rest : after.balances = included.balances := by
      rw [foldlM_balances (fun _ _ _ step => processPayloadAttestation_balances step) last,
        foldlM_balances (fun _ _ _ step => processBlsToExecutionChange_balances step) changedOk,
        foldlM_balances (fun _ _ _ step => processVoluntaryExit_balances step) exitedOk]
    refine ⟨proposed, first, attested, second, one, two, fun _ => [], fun _ => [], firstOk,
      secondOk, ?_, oneKind, twoKind,
      fun _ _ absent => absurd absent List.not_mem_nil,
      fun _ _ absent => absurd absent List.not_mem_nil, oneBound⟩
    refine ((oneLedger.trans twoLedger).trans (BalanceLedger.of_balances rest)).congr
      fun i => by simp
  · rename_i notGloas
    have before : fork < .glamsterdam := Nat.lt_of_not_le notGloas
    simp only [bind_ok_iff, ensure_ok_iff] at computed
    obtain ⟨_, _, _, _, proposed, proposedOk, attested, attestedOk, included, includedOk,
      deposited, depositedOk, exited, exitedOk, changed, changedOk, last⟩ := computed
    rw [← Array.foldlM_toList] at proposedOk attestedOk includedOk depositedOk exitedOk
    obtain ⟨first, firstOk, firstDebits⟩ := proposerSlashingPayouts_debits _ proposedOk
    obtain ⟨second, secondOk, secondDebits⟩ := attesterSlashingPayouts_debits _ attestedOk
    obtain ⟨one, oneLedger, oneKind, oneBound⟩ := firstDebits.trans secondDebits
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
    refine ⟨proposed, first, attested, second, one, two, three, four, firstOk, secondOk, ?_,
      oneKind, twoKind, threeKind, fourKind, oneBound⟩
    refine ((((oneLedger.trans twoLedger).trans threeLedger).trans
      (BalanceLedger.of_balances (changes.trans exits))).trans fourLedger).congr fun i => by simp

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

/-- The ledger of a block, with its withdrawals, slashings and sync changes exact.

It is `BlockLedger`, with the withdrawals and the sync changes named by the steps that make them.

The slashings debit at most the initial penalties of the payouts of the block.
-/
def BlockDebits (config : Config) (checks : SignatureChecks)
    (engine : ExecutionEngine preset fork) (state : BeaconState preset fork)
    (block : BeaconBlock preset fork) (after : BeaconState preset fork) : Prop :=
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
    BlockSync (preset := preset) config checks fork sync ∧
    ∃ payouts, blockSlashingPayouts config checks engine state block = .ok payouts ∧
      ∀ i, BalanceChange.debited .slashing (slashings i) ≤ payoutPenalties payouts i

/-- The ledger of a block, at every fork, with its withdrawals and sync changes exact.

That needs one balance for each validator. -/
theorem processBlock_debits {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (holds : BalancesMatch state) : BlockDebits config checks engine state block after := by
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
    obtain ⟨_, first, _, second, slashings, credits, deposits, requests, firstOk, secondOk,
      operationsLedger, slashingKind, creditKind, depositKind, requestKind, slashingBound⟩ :=
      processOperations_debits s6Ok matched
    have inputOk : operationsInput config checks engine state block = .ok s5 := by
      simp only [operationsInput, altair, ↓reduceDIte, bind_ok_iff]
      exact ⟨s1, s1Ok, s2, s2Ok, s3, s3Ok, s4, s4Ok, s5Ok⟩
    obtain ⟨reward, proposerReward, members, proposer, rewardOk, _, membersOk, _, syncLedger⟩ :=
      processSyncAggregate_ledger last
    refine ⟨excess, slashings, credits, deposits, requests,
      fun i => if i < s6.balances.data.size then syncChanges
          (members.zip (block.body.syncAggregate altair).syncCommitteeBits.bits.toArray).toList
          proposer reward.toNat proposerReward.toNat i else [], withdrawals, ?_, excessKind,
      slashingKind, creditKind, depositKind, requestKind, withdrawalSpec,
      .inr ⟨altair, s6, after, _, reward, proposerReward, members, proposer, last, rewardOk,
        membersOk, fun _ => rfl⟩, first ++ second, ?_, slashingBound⟩
    swap
    · simp [blockSlashingPayouts, inputOk, firstOk, secondOk, bind, Except.bind, pure,
        Except.pure]
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
    obtain ⟨_, first, _, second, slashings, credits, deposits, requests, firstOk, secondOk,
      operationsLedger, slashingKind, creditKind, depositKind, requestKind, slashingBound⟩ :=
      processOperations_debits last fun _ => balancesMatch_of_sameSizes sizes holds
    have inputOk : operationsInput config checks engine state block = .ok s3 := by
      simp only [operationsInput, notAltair, ↓reduceDIte, bind_ok_iff]
      exact ⟨s1, s1Ok, s2, s2Ok, s3Ok⟩
    refine ⟨fun _ => [], slashings, credits, deposits, requests, fun _ => [], [], ?_,
      fun _ _ absent => absurd absent List.not_mem_nil, slashingKind, creditKind,
      depositKind, requestKind, .inl rfl, .inl fun _ => rfl, first ++ second, ?_, slashingBound⟩
    swap
    · simp [blockSlashingPayouts, inputOk, firstOk, secondOk, bind, Except.bind, pure,
        Except.pure]
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
theorem BlockDebits.debited {engine : ExecutionEngine preset fork} {block : BeaconBlock preset fork}
    (debits : BlockDebits config checks engine state block after) :
    ∃ (excess slashings sync : Nat → List BalanceChange) (withdrawals : List Withdrawal)
      (changes : Nat → List BalanceChange),
      BalanceLedger state after changes ∧
      BlockWithdrawals preset fork withdrawals ∧
      BlockSync (preset := preset) config checks fork sync ∧
      (∃ payouts, blockSlashingPayouts config checks engine state block = .ok payouts ∧
        ∀ i, BalanceChange.debited .slashing (slashings i) ≤ payoutPenalties payouts i) ∧
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
    slashingKind, creditKind, depositKind, requestKind, withdrawalSpec, syncSpec, payoutSpec⟩ :=
    debits
  -- The excess queued by the parent payload and by the requests are one kind.
  refine ⟨fun i => excess i ++ requests i, slashings, sync, withdrawals, _, ledger,
    withdrawalSpec, syncSpec, payoutSpec, fun i change member => ?_, fun i flow => ?_⟩
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
