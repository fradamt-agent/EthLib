module

public import EthLib.Consensus.Proofs.Transition.BuilderPayments
public import EthLib.Consensus.Proofs.Transition.EpochPending
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Proofs.Transition.Requests
public import EthLib.Consensus.Proofs.Transition.SlashingBalances
public import EthLib.Consensus.Proofs.Transition.WithdrawalAmounts

/-!
# Proofs: a ledger of the balances

A ledger lists, for each position of the registry, the changes that a step makes to its balance.

Each change is a credit, or a debit that stops at zero, and it names the kind of flow it is.

A balance past the end of the registry reads as zero, so a new validator starts from zero.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Ledgers -/

/-- The kinds of flow that change a balance. -/
inductive BalanceFlow where
  /-- The rewards and penalties of an epoch, by participation. -/
  | rewards
  /-- The penalties of slashing, and the rewards for reporting it. -/
  | slashing
  /-- A deposit credited. -/
  | deposit
  /-- A balance moved by a consolidation, from its source to its target. -/
  | consolidation
  /-- A withdrawal paid out. -/
  | withdrawal
  /-- A reward paid inside a block: to its proposer or to the members of the sync committee. -/
  | blockReward
  deriving DecidableEq, Repr

/-- One change to a balance: a credit, or a debit that stops at zero. -/
inductive BalanceChange where
  | credit (flow : BalanceFlow) (amount : Nat)
  | debit (flow : BalanceFlow) (amount : Nat)
  deriving DecidableEq, Repr

/-- The balance after one change. -/
def BalanceChange.apply (balance : Nat) : BalanceChange → Nat
  | .credit _ amount => balance + amount
  | .debit _ amount => balance - amount

/-- The balance at a position, on natural numbers, or zero past the end. -/
def balanceNat (state : BeaconState preset fork) (i : Nat) : Nat :=
  ((state.balances.data[i]?).map UInt64.toNat).getD 0

/-- A ledger of a step: each balance after it is the one before, with its changes applied. -/
def BalanceLedger (state after : BeaconState preset fork) (changes : Nat → List BalanceChange) :
    Prop :=
  ∀ i, balanceNat after i = (changes i).foldl BalanceChange.apply (balanceNat state i)

/-- A step that keeps the balances has the empty ledger. -/
theorem BalanceLedger.of_balances (same : after.balances = state.balances) :
    BalanceLedger state after fun _ => [] := by
  intro i
  simp [balanceNat, same]

/-- The empty ledger of a state to itself. -/
theorem BalanceLedger.refl (state : BeaconState preset fork) :
    BalanceLedger state state fun _ => [] :=
  BalanceLedger.of_balances rfl

/-- Two steps in turn have the ledger of the first, then that of the second. -/
theorem BalanceLedger.trans {middle : BeaconState preset fork}
    {first second : Nat → List BalanceChange} (one : BalanceLedger state middle first)
    (two : BalanceLedger middle after second) :
    BalanceLedger state after fun i => first i ++ second i := by
  intro i
  rw [two i, one i, List.foldl_append]

/-- A ledger holds for any changes that act the same on each balance. -/
theorem BalanceLedger.congr {first second : Nat → List BalanceChange}
    (holds : BalanceLedger state after first)
    (same : ∀ i, (first i).foldl BalanceChange.apply (balanceNat state i) =
      (second i).foldl BalanceChange.apply (balanceNat state i)) :
    BalanceLedger state after second :=
  fun i => (holds i).trans (same i)

/-- The total that some changes of one kind credit. -/
def BalanceChange.credited (flow : BalanceFlow) (changes : List BalanceChange) : Nat :=
  (changes.map fun
    | .credit kind amount => if kind = flow then amount else 0
    | .debit _ _ => 0).sum

/-- The total that some changes of one kind ask to debit, before any stop at zero. -/
def BalanceChange.debited (flow : BalanceFlow) (changes : List BalanceChange) : Nat :=
  (changes.map fun
    | .credit _ _ => 0
    | .debit kind amount => if kind = flow then amount else 0).sum

/-! ## The steps of an epoch that keep the balances -/

/-- Replacing a validator keeps the balances. -/
theorem setValidator_balances {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : after.balances = state.balances := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  rfl

/-- A fold whose every step keeps the balances keeps them. -/
theorem foldlM_balances {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (keeps : ∀ last x next, step last x = .ok next → next.balances = last.balances)
    {xs : List α} (computed : xs.foldlM step state = .ok after) :
    after.balances = state.balances :=
  foldlM_ok_invariant (fun middle => middle.balances = state.balances)
    (fun _ _ _ same ok => (keeps _ _ _ ok).trans same) rfl computed

/-- Justification and finalization keep the balances. -/
theorem processJustificationAndFinalization_balances
    (computed : processJustificationAndFinalization state = .ok after) :
    after.balances = state.balances := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · rw [same]
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]

/-- The inactivity updates keep the balances. -/
theorem processInactivityUpdates_balances {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    after.balances = state.balances := by
  unfold processInactivityUpdates at computed
  split at computed
  · cases computed
    rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    rfl

/-- The registry updates keep the balances. -/
theorem processRegistryUpdates_balances
    (computed : processRegistryUpdates config state = .ok after) :
    after.balances = state.balances := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, folded⟩ := computed
    refine foldlM_balances (fun last index next step => ?_) folded
    unfold updateRegistryEntryElectra at step
    simp only [bind_ok_iff, liftAccessor_ok] at step
    obtain ⟨_, _, step⟩ := step
    split at step
    · simp only [bind_ok_iff, liftAccessor_ok] at step
      obtain ⟨_, _, set⟩ := step
      exact setValidator_balances set
    · split at step
      · exact initiateValidatorExit_balances (liftAccessor_ok.mp step)
      · split at step
        · exact setValidator_balances (liftAccessor_ok.mp step)
        · cases step
          rfl
  · simp only [bind_ok_iff] at computed
    obtain ⟨middle, folded, activated⟩ := computed
    rw [foldlM_balances (fun last index next step => ?_) activated,
      foldlM_balances (fun last index next step => ?_) folded]
    · unfold updateRegistryEntry at step
      simp only [bind_ok_iff, liftAccessor_ok] at step
      obtain ⟨_, _, _, _, set', set, step⟩ := step
      rw [← setValidator_balances set]
      split at step
      · exact initiateValidatorExit_balances (liftAccessor_ok.mp step)
      · cases step
        rfl
    · unfold activateValidator at step
      simp only [bind_ok_iff, liftAccessor_ok] at step
      obtain ⟨_, _, _, _, set⟩ := step
      exact setValidator_balances set

/-- The reset of the deposit votes keeps the balances. -/
theorem processEth1DataReset_balances {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    after.balances = state.balances := by
  unfold processEth1DataReset at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed <;> (cases computed; rfl)

/-- The effective balance updates keep the balances. -/
theorem processEffectiveBalanceUpdates_balances
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    after.balances = state.balances := by
  refine foldlM_balances (fun last index next step => ?_) computed
  unfold updateEffectiveBalance at step
  simp only [bind_ok_iff, liftAccessor_ok] at step
  obtain ⟨_, _, _, _, _, _, set⟩ := step
  exact setValidator_balances set

/-- The reset of the slashings keeps the balances. -/
theorem processSlashingsReset_balances (computed : processSlashingsReset state = .ok after) :
    after.balances = state.balances := by
  unfold processSlashingsReset at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  rfl

/-- The reset of the RANDAO mixes keeps the balances. -/
theorem processRandaoMixesReset_balances (computed : processRandaoMixesReset state = .ok after) :
    after.balances = state.balances := by
  unfold processRandaoMixesReset at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, rfl⟩ := computed
  rfl

/-- The update of the historical summaries keeps the balances. -/
theorem processHistoricalSummariesUpdate_balances {capella : .shapella ≤ fork}
    (computed : processHistoricalSummariesUpdate state capella = .ok after) :
    after.balances = state.balances := by
  unfold processHistoricalSummariesUpdate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, computed⟩ := computed
    split at computed
    · cases computed
      rfl
    · cases computed
  · cases computed
    rfl

/-- The update of the historical roots keeps the balances. -/
theorem processHistoricalRootsUpdate_balances
    (computed : processHistoricalRootsUpdate state = .ok after) :
    after.balances = state.balances := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨_, _, _, _, rfl⟩ := computed
      rfl
    · cases computed
      rfl

/-- The update of the sync committees keeps the balances. -/
theorem processSyncCommitteeUpdates_balances {altair : .altair ≤ fork}
    (computed : processSyncCommitteeUpdates state altair = .ok after) :
    after.balances = state.balances := by
  unfold processSyncCommitteeUpdates at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl
  · cases computed
    rfl

/-- The move of the proposer lookahead keeps the balances. -/
theorem processProposerLookahead_balances {fulu : .fusaka ≤ fork}
    (computed : processProposerLookahead state fulu = .ok after) :
    after.balances = state.balances := by
  unfold processProposerLookahead at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  rfl

/-- The move of the window of payload committees keeps the balances. -/
theorem processPtcWindow_balances {gloas : .glamsterdam ≤ fork}
    (computed : processPtcWindow state gloas = .ok after) :
    after.balances = state.balances := by
  unfold processPtcWindow at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  rfl

/-- The settlement of the builder payments keeps the balances of the validators. -/
theorem processBuilderPendingPayments_balances {gloas : .glamsterdam ≤ fork}
    (computed : processBuilderPendingPayments state gloas = .ok after) :
    after.balances = state.balances := by
  unfold processBuilderPendingPayments at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  rfl

/-! ## Rewards and penalties -/

/-- The changes of some passes of deltas to one balance: each pass credits, then debits. -/
def deltaChanges (deltas : List (Array Gwei × Array Gwei)) (i : Nat) : List BalanceChange :=
  deltas.flatMap fun delta =>
    [.credit .rewards (delta.1.getD i 0).toNat, .debit .rewards (delta.2.getD i 0).toNat]

/-- Passes of deltas whose checked additions succeed act on the balance as their changes say. -/
theorem toNat_foldl_deltas {i : Nat} :
    ∀ (deltas : List (Array Gwei × Array Gwei)) (balance : Gwei),
      deltas.foldlM (fun balance delta => (addChecked balance (delta.1.getD i 0)).map
          fun raised => saturatingSub raised (delta.2.getD i 0)) balance =
        .ok (deltas.foldl (fun balance delta =>
          saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) balance) →
      (deltas.foldl (fun balance delta =>
          saturatingSub (balance + delta.1.getD i 0) (delta.2.getD i 0)) balance).toNat =
        (deltaChanges deltas i).foldl BalanceChange.apply balance.toNat
  | [], _, _ => rfl
  | delta :: rest, balance, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, folded⟩ := computed
    cases raisedOk : addChecked balance (delta.1.getD i 0) with
    | error _ =>
      rw [raisedOk] at step
      cases step
    | ok raised =>
    rw [raisedOk] at step
    simp only [Except.map, Except.ok.injEq] at step
    subst step
    obtain ⟨fits, value⟩ := addChecked_ok_iff.mp raisedOk
    have same : raised = balance + delta.1.getD i 0 :=
      UInt64.toNat_inj.mp (by rw [value, toNat_add_of_lt fits])
    subst same
    simp only [List.foldl_cons, deltaChanges, List.flatMap_cons, List.foldl_append]
    rw [toNat_foldl_deltas rest _ folded]
    simp only [List.foldl_nil, BalanceChange.apply, toNat_saturatingSub,
      toNat_add_of_lt fits]
    rfl

/-- The ledger of the rewards and penalties, at every fork, for a registry within its limit.

Each position of the registry with a balance takes each pass of deltas in turn.

A pass credits the reward of the position, then debits its penalty, stopping at zero.

Before Altair there is one pass, of the attestation deltas.

From Altair there is a pass for each flag, then one of the inactivity deltas.

The first epoch has no pass. -/
theorem processRewardsAndPenalties_ledger (within : state.RegistryWithinLimit)
    (computed : processRewardsAndPenalties config state = .ok after) :
    ∃ deltas : List (Array Gwei × Array Gwei),
      (getCurrentEpoch state = GENESIS_EPOCH → deltas = []) ∧
      (∀ before : fork < .altair, getCurrentEpoch state ≠ GENESIS_EPOCH →
        ∃ attestation, getAttestationDeltas config state before = .ok attestation ∧
          deltas = [attestation]) ∧
      (∀ altair : .altair ≤ fork, getCurrentEpoch state ≠ GENESIS_EPOCH →
        ∃ flags inactivity, (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
            (getFlagIndexDeltas state altair) = .ok flags ∧
          getInactivityPenaltyDeltas config state = .ok inactivity ∧
          deltas = flags ++ [inactivity]) ∧
      BalanceLedger state after fun i =>
        if i < state.validators.data.size ∧ i < state.balances.data.size then
          deltaChanges deltas i else [] := by
  by_cases genesis : getCurrentEpoch state = GENESIS_EPOCH
  · rw [processRewardsAndPenalties_genesis config genesis, Except.ok.injEq] at computed
    subst computed
    refine ⟨[], fun _ => rfl, fun _ later => absurd genesis later,
      fun _ later => absurd genesis later, fun i => ?_⟩
    dsimp only
    split <;> rfl
  by_cases altair : .altair ≤ fork
  · obtain ⟨flags, inactivity, flagsOk, inactivityOk, holds⟩ :=
      processRewardsAndPenalties_balances_of_altair altair within genesis computed
    refine ⟨flags ++ [inactivity], fun later => absurd later genesis,
      fun before => absurd altair (Nat.not_le_of_lt before),
      fun _ _ => ⟨flags, inactivity, flagsOk, inactivityOk, rfl⟩, fun i => ?_⟩
    obtain ⟨changed, checked, past⟩ := holds i
    unfold balanceNat
    dsimp only
    split
    · rename_i inside
      obtain ⟨balance, found⟩ : ∃ balance, state.balances.data[i]? = some balance :=
        ⟨_, Array.getElem?_eq_getElem inside.2⟩
      rw [changed inside.1, found]
      simp only [Option.map_some, Option.getD_some]
      exact toNat_foldl_deltas _ _ (checked inside.1 balance found)
    · rename_i outside
      by_cases registry : i < state.validators.data.size
      · have none : state.balances.data[i]? = none :=
          Array.getElem?_eq_none (by omega)
        rw [changed registry, none]
        rfl
      · rw [past (by omega)]
        rfl
  · have before : fork < .altair := Nat.lt_of_not_le altair
    obtain ⟨rewards, penalties, found, holds⟩ :=
      processRewardsAndPenalties_balances_of_lt_altair before genesis computed
    refine ⟨[(rewards, penalties)], fun later => absurd later genesis,
      fun _ _ => ⟨(rewards, penalties), found, rfl⟩, fun altair' => absurd altair' altair,
      fun i => ?_⟩
    obtain ⟨changed, past⟩ := holds i
    unfold balanceNat
    dsimp only
    split
    · rename_i inside
      obtain ⟨balance, read, fits, raised⟩ := changed inside.1
      rw [raised, read]
      simp only [Option.map_some, Option.getD_some, deltaChanges, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.foldl_cons, List.foldl_nil, BalanceChange.apply,
        toNat_saturatingSub, toNat_add_of_lt fits]
    · rename_i outside
      by_cases registry : i < state.validators.data.size
      · obtain ⟨balance, read, _, _⟩ := changed registry
        have := (Array.getElem?_eq_some_iff.mp read).1
        omega
      · rw [past (by omega)]
        rfl

/-! ## Deposits -/

/-- The changes of a deposit credited at a position, if any. -/
def depositChanges (deposit : PendingDeposit) (target : Option Nat) (i : Nat) :
    List BalanceChange :=
  if target = some i then [.credit .deposit deposit.amount.toNat] else []

/-- The ledger of one deposit credited.

A key that a validator has credits the first such validator.

A new key with a valid signature credits a new validator, at the end of the registry.

Otherwise the deposit credits nothing.

The registry then stays, or grows by that new validator.

That needs one balance for each validator, and an index that fits 64 bits. -/
theorem applyPendingDeposit_ledger {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (holds : BalancesMatch state) (small : state.validators.data.size < 2 ^ 64) :
    ∃ target : Option Nat,
      (∀ j, state.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some j →
        target = some j) ∧
      (state.validators.data.findIdx? (·.pubkey == deposit.pubkey) = none →
        target = none ∨ target = some state.validators.data.size) ∧
      (after.validators.data = state.validators.data ∨ ∃ validator,
        after.validators.data = state.validators.data.push validator ∧
          validator.pubkey = deposit.pubkey) ∧
      BalanceLedger state after (depositChanges deposit target) := by
  cases known : state.validators.data.findIdx? (·.pubkey == deposit.pubkey) with
  | some j =>
    obtain ⟨⟨balance, raised, found, raisedFound, value⟩, others⟩ :=
      applyPendingDeposit_known_balances known computed small
    have registry : after.validators = state.validators := by
      simp only [applyPendingDeposit, known, liftAccessor_ok] at computed
      exact increaseBalance_validators computed
    refine ⟨some j, fun _ same => Option.some.inj same ▸ rfl, fun absent => (by cases absent),
      .inl (by rw [registry]), fun i => ?_⟩
    unfold balanceNat depositChanges
    by_cases same : some j = some i
    · obtain rfl := Option.some.inj same
      simp [raisedFound, found, value, BalanceChange.apply]
    · have other : i ≠ j := fun h => same (h ▸ rfl)
      simp [same, others i other]
  | none =>
    unfold applyPendingDeposit at computed
    rw [known] at computed
    dsimp only at computed
    split at computed
    · cases computed
      exact ⟨none, fun _ absent => (by cases absent), fun _ => .inl rfl, .inl rfl,
        fun i => by simp [depositChanges]⟩
    rename_i notBls
    simp only [bind_ok_iff] at computed
    obtain ⟨valid, validOk, computed⟩ := computed
    cases valid with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact ⟨none, fun _ absent => (by cases absent), fun _ => .inl rfl, .inl rfl,
        fun i => by simp [depositChanges]⟩
    | true =>
      have pushed := applyPendingDeposit_new_valid known notBls validOk
        (by simp only [applyPendingDeposit, known, notBls, ↓reduceIte, bind, Except.bind,
          validOk]; exact computed) holds small
      simp only [↓reduceIte] at computed
      obtain ⟨validators, balances⟩ := addValidatorToRegistry_push computed holds small
      refine ⟨some state.validators.data.size, fun _ absent => (by cases absent),
        fun _ => .inr rfl, .inr ⟨_, validators, ?_⟩, fun i => ?_⟩
      · simp [getValidatorFromDeposit]
      · unfold balanceNat depositChanges
        rw [balances, Array.getElem?_push]
        have sizes : state.balances.data.size = state.validators.data.size := holds
        by_cases same : i = state.validators.data.size
        · subst same
          simp [sizes, BalanceChange.apply]
        · have other : some state.validators.data.size ≠ some i := fun h =>
            same (Option.some.inj h).symm
          simp [sizes, same, other]

/-- What a deposit credits, read against a registry: the first validator with its key, if any.

Otherwise it credits nothing, or a new validator past the end of that registry. -/
def CreditsFirst (validators : Array Validator) (deposit : PendingDeposit) (target : Option Nat) :
    Prop :=
  (∀ j, validators.findIdx? (·.pubkey == deposit.pubkey) = some j → target = some j) ∧
  (validators.findIdx? (·.pubkey == deposit.pubkey) = none →
    target = none ∨ ∃ m, validators.size ≤ m ∧ target = some m)

/-- What a deposit credits against a registry, it credits against the registry before a push. -/
private theorem CreditsFirst.of_push {validators : Array Validator} {added : Validator}
    {deposit : PendingDeposit} {target : Option Nat}
    (credits : CreditsFirst (validators.push added) deposit target) :
    CreditsFirst validators deposit target := by
  obtain ⟨known, new⟩ := credits
  refine ⟨fun j found => known j (by rw [Array.findIdx?_push, found]; rfl), fun absent => ?_⟩
  rw [Array.findIdx?_push, absent] at known new
  split at known
  · rename_i same
    exact .inr ⟨validators.size, Nat.le_refl _, known _ (by simp)⟩
  · rcases new (by simp [*]) with none | ⟨m, above, rfl⟩
    · exact .inl none
    · exact .inr ⟨m, by simp at above; omega, rfl⟩

/-- The ledger of some deposits credited in turn.

Each credits, against the registry before them all, the first validator with its key.

Otherwise it credits nothing, or a new validator past the end of that registry.

That needs one balance for each validator, and room in 64 bits for the new validators. -/
theorem foldlM_applyPendingDeposit_ledger :
    ∀ {deposits : List PendingDeposit} {state after : BeaconState preset fork},
      deposits.foldlM (applyPendingDeposit config checks) state = .ok after →
      BalancesMatch state →
      state.validators.data.size + deposits.length < 2 ^ 64 →
      ∃ targets : List (Option Nat), targets.length = deposits.length ∧
        (∀ pair ∈ deposits.zip targets, CreditsFirst state.validators.data pair.1 pair.2) ∧
        BalanceLedger state after fun i =>
          (deposits.zip targets).flatMap fun pair => depositChanges pair.1 pair.2 i
  | [], state, after, computed, _, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨[], rfl, fun _ absent => absurd absent List.not_mem_nil,
      fun i => by simp⟩
  | deposit :: rest, state, after, computed, holds, room => by
    simp only [List.length_cons] at room
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepped, folded⟩ := computed
    obtain ⟨target, known, new, grown, first⟩ := applyPendingDeposit_ledger stepped holds (by omega)
    have holds' := (applyPendingDeposit_kept stepped).1 holds
    have size : middle.validators.data.size ≤ state.validators.data.size + 1 := by
      rcases grown with same | ⟨_, pushed, _⟩
      · rw [same]; omega
      · rw [pushed, Array.size_push]
        exact Nat.le_refl _
    obtain ⟨targets, length, credits, later⟩ :=
      foldlM_applyPendingDeposit_ledger folded holds' (by omega)
    refine ⟨target :: targets, by simp [length], fun pair member => ?_, fun i => ?_⟩
    · rcases List.mem_cons.mp member with rfl | member
      · refine ⟨known, fun absent => ?_⟩
        rcases new absent with none | some
        · exact .inl none
        · exact .inr ⟨_, Nat.le_refl _, some⟩
      · have := credits pair member
        rcases grown with same | ⟨_, pushed, _⟩
        · rwa [same] at this
        · rw [pushed] at this
          exact this.of_push
    · rw [(first.trans later) i]
      simp

/-- From Electra, the ledger of the pending deposits of an epoch.

The deposits read are a prefix of the queue, and those applied are some of them, in order.

Each credits, against the registry before, the first validator with its key.

Otherwise it credits nothing, or a new validator past the end of the registry.

That needs one balance for each validator, and room in 64 bits for the new validators. -/
theorem processPendingDeposits_ledger {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ (read rest applied postponed : List PendingDeposit) (targets : List (Option Nat)),
      (state.pendingDeposits electra).data.toList = read ++ rest ∧
      (after.pendingDeposits electra).data.toList = rest ++ postponed ∧
      applied.Sublist read ∧ (applied ++ postponed).Perm read ∧
      targets.length = applied.length ∧
      (∀ pair ∈ applied.zip targets, CreditsFirst state.validators.data pair.1 pair.2) ∧
      BalanceLedger state after fun i =>
        (applied.zip targets).flatMap fun pair => depositChanges pair.1 pair.2 i := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, length, inRead, _,
    perm, folded, rfl⟩ := processPendingDeposits_applied computed
  obtain ⟨targets, lengths, credits, ledger⟩ :=
    foldlM_applyPendingDeposit_ledger folded holds (by have := inRead.length_le; omega)
  exact ⟨read, rest, applied, postponed, targets, queue, kept, inRead, perm, lengths, credits,
    ledger⟩

/-! ## Consolidations -/

/-- One balance moved by a consolidation: from a source, to a target, by an amount. -/
structure Transfer where
  source : ValidatorIndex
  target : ValidatorIndex
  amount : Nat

/-- The changes of some transfers to one balance, in turn.

Each transfer debits its source, then credits its target. -/
def transferChanges (transfers : List Transfer) (i : Nat) : List BalanceChange :=
  transfers.flatMap fun transfer =>
    (if transfer.source.toNat = i then [.debit .consolidation transfer.amount] else []) ++
      (if transfer.target.toNat = i then [.credit .consolidation transfer.amount] else [])

/-- The changes of transfers in turn are those of each in turn. -/
theorem transferChanges_cons (transfer : Transfer) (rest : List Transfer) (i : Nat) :
    transferChanges (transfer :: rest) i =
      transferChanges [transfer] i ++ transferChanges rest i := by
  simp [transferChanges]

/-- Raising a balance is a ledger of one credit at its position. -/
theorem increaseBalance_ledger (flow : BalanceFlow) {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    BalanceLedger state after fun i =>
      if index.toNat = i then [.credit flow delta.toNat] else [] := by
  obtain ⟨inside, fits, rfl⟩ := increaseBalance_eq_ok_iff.mp computed
  intro i
  unfold balanceNat
  by_cases same : index.toNat = i
  · subst same
    simp [BeaconState.putBalance, inside, BalanceChange.apply, toNat_add_of_lt fits]
  · simp [BeaconState.putBalance, same]

/-- Lowering a balance is a ledger of one debit at its position. -/
theorem decreaseBalance_ledger (flow : BalanceFlow) {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) :
    BalanceLedger state after fun i =>
      if index.toNat = i then [.debit flow delta.toNat] else [] := by
  obtain ⟨inside, rfl⟩ := decreaseBalance_eq_ok_iff.mp computed
  intro i
  unfold balanceNat
  by_cases same : index.toNat = i
  · subst same
    simp [BeaconState.putBalance, inside, BalanceChange.apply, toNat_saturatingSub]
  · simp [BeaconState.putBalance, same]

/-- The smaller of two 64-bit integers has the smaller value. -/
theorem toNat_min (a b : UInt64) : (min a b).toNat = min a.toNat b.toNat := by
  rw [UInt64.min_def, Nat.min_def]
  by_cases h : a ≤ b
  · simp [h, UInt64.le_iff_toNat_le.mp h]
  · simp [h, mt UInt64.le_iff_toNat_le.mpr h]

/-- Two states with the same registry read the same validators. -/
theorem getValidator_of_validators {other : BeaconState preset fork}
    (same : other.validators = state.validators) (index : ValidatorIndex) :
    getValidator other index = getValidator state index := by
  unfold getValidator
  rw [same]

/-- What one transfer of a pass over the pending consolidations is, after the transfers before it.

It comes from a consolidation of the queue whose source is not slashed and can withdraw.

It moves the effective balance of the source, or all its balance left if that is less. -/
def TransferMade (state : BeaconState preset fork) (nextEpoch : Epoch)
    (queue : List PendingConsolidation) (before : List Transfer) (transfer : Transfer) : Prop :=
  ∃ consolidation ∈ queue, ∃ source : Validator,
    consolidation.sourceIndex = transfer.source ∧ consolidation.targetIndex = transfer.target ∧
    getValidator state transfer.source = .ok source ∧ source.slashed = false ∧
    source.withdrawableEpoch ≤ nextEpoch ∧
    transfer.amount = min ((transferChanges before transfer.source.toNat).foldl
      BalanceChange.apply (balanceNat state transfer.source.toNat))
        source.effectiveBalance.toNat

/-- A pass over the pending consolidations keeps the registry. -/
theorem passPendingConsolidations_validators {nextEpoch : Epoch} :
    ∀ {queue : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state queue = .ok result →
      result.1.validators = state.validators
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨⟨later, _⟩, laterOk, rfl⟩ := computed
      have kept := passPendingConsolidations_validators laterOk
      exact kept
    split at computed
    · cases computed
      rfl
    simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨later, _⟩, laterOk, rfl⟩ := computed
    have kept := passPendingConsolidations_validators laterOk
    exact kept.trans ((increaseBalance_validators raisedOk).trans
      (decreaseBalance_validators loweredOk))

/-- The ledger of a pass over the pending consolidations: the transfers it makes, in turn.

Each transfer is as `TransferMade` says, after the transfers before it. -/
theorem passPendingConsolidations_ledger {nextEpoch : Epoch}
    {whole : List PendingConsolidation} :
    ∀ {queue : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      (∀ consolidation ∈ queue, consolidation ∈ whole) →
      passPendingConsolidations nextEpoch state queue = .ok result →
      ∃ transfers : List Transfer,
        (∀ k (inside : k < transfers.length),
          TransferMade state nextEpoch whole (transfers.take k) transfers[k]) ∧
        BalanceLedger state result.1 (transferChanges transfers)
  | [], _, _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨[], fun _ inside => absurd inside (by simp), fun i => by simp [transferChanges]⟩
  | consolidation :: rest, state, result, within, computed => by
    have rest' : ∀ other ∈ rest, other ∈ whole :=
      fun other member => within other (List.mem_cons_of_mem _ member)
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, sourceOk, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨⟨later, _⟩, laterOk, rfl⟩ := computed
      have ledger := passPendingConsolidations_ledger rest' laterOk
      exact ledger
    rename_i notSlashed
    split at computed
    · cases computed
      exact ⟨[], fun _ inside => absurd inside (by simp), fun i => by simp [transferChanges]⟩
    rename_i withdrawable
    simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨balance, balanceOk, lowered, loweredOk, raised, raisedOk, ⟨later, _⟩, laterOk,
      rfl⟩ := computed
    obtain ⟨transfers, made, ledger⟩ := passPendingConsolidations_ledger rest' laterOk
    let first : Transfer := ⟨consolidation.sourceIndex, consolidation.targetIndex,
      (min balance source.effectiveBalance).toNat⟩
    -- The transfer moves one amount out of the source, then into the target.
    have moved : BalanceLedger state raised (transferChanges [first]) :=
      ((decreaseBalance_ledger .consolidation loweredOk).trans
        (increaseBalance_ledger .consolidation raisedOk)).congr fun i => by
          simp [transferChanges, first]
    have registry : raised.validators = state.validators :=
      (increaseBalance_validators raisedOk).trans (decreaseBalance_validators loweredOk)
    have read : balanceNat state consolidation.sourceIndex.toNat = balance.toNat := by
      unfold getBalance at balanceOk
      split at balanceOk
      · rename_i found
        cases balanceOk
        simp [balanceNat, found]
      · cases balanceOk
    refine ⟨first :: transfers, fun k inside => ?_, ?_⟩
    · cases k with
      | zero =>
        refine ⟨consolidation, within _ List.mem_cons_self, source, rfl, rfl, sourceOk,
          by simpa using notSlashed, UInt64.not_lt.mp withdrawable, ?_⟩
        simp only [List.take_zero, transferChanges, List.flatMap_nil, List.foldl_nil, read,
          List.getElem_cons_zero, first]
        rw [toNat_min]
      | succ k =>
        obtain ⟨original, member, validator, sourceSame, targetSame, validatorOk, slashed, ready,
          amount⟩ := made k (by simpa using inside)
        refine ⟨original, member, validator, sourceSame, targetSame, ?_, slashed, ready, ?_⟩
        · simpa [getValidator_of_validators registry] using validatorOk
        · simp only [List.getElem_cons_succ, List.take_succ_cons]
          rw [amount, moved, transferChanges_cons first (List.take k transfers),
            List.foldl_append]
    · exact (moved.trans ledger).congr fun i => by
        rw [transferChanges_cons first transfers, List.foldl_append]

/-- From Electra, the ledger of the pending consolidations of an epoch: the transfers they make.

Each transfer is as `TransferMade` says, from a consolidation of the queue before. -/
theorem processPendingConsolidations_ledger {electra : .pectra ≤ fork}
    (computed : processPendingConsolidations state electra = .ok after) :
    ∃ (nextEpoch : Epoch) (transfers : List Transfer),
      nextEpoch.toNat = (getCurrentEpoch state).toNat + 1 ∧
      (∀ k (inside : k < transfers.length),
        TransferMade state nextEpoch (state.pendingConsolidations electra).data.toList
          (transfers.take k) transfers[k]) ∧
      BalanceLedger state after (transferChanges transfers) := by
  unfold processPendingConsolidations at computed
  simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextEpoch, ⟨_, next⟩, ⟨passed, _⟩, passedOk, rfl⟩ := computed
  obtain ⟨transfers, made, ledger⟩ :=
    passPendingConsolidations_ledger (fun _ member => member) passedOk
  exact ⟨nextEpoch, transfers, by simpa using next, made, fun i => ledger i⟩

/-- From Electra, the ledger of the pending balances of an epoch.

The pending deposits credit first, as `processPendingDeposits_ledger` says.

Then the pending consolidations move balances, as `processPendingConsolidations_ledger` says.

Before Electra nothing changes. -/
theorem processPendingBalances_ledger
    (computed : processPendingBalances config checks state = .ok after)
    (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ (deposited : BeaconState preset fork) (deposits : Nat → List BalanceChange)
      (transfers : Nat → List BalanceChange),
      BalanceLedger state deposited deposits ∧ BalanceLedger deposited after transfers ∧
      BalanceLedger state after (fun i => deposits i ++ transfers i) ∧
      (fork < .pectra → deposited = state ∧ (∀ i, deposits i = []) ∧ ∀ i, transfers i = []) ∧
      (∀ electra : .pectra ≤ fork, processPendingDeposits config checks state electra =
          .ok deposited ∧ processPendingConsolidations deposited electra = .ok after) := by
  unfold processPendingBalances at computed
  split at computed
  · rename_i electra
    simp only [bind_ok_iff] at computed
    obtain ⟨deposited, depositedOk, consolidated⟩ := computed
    obtain ⟨_, _, applied, _, targets, _, _, _, _, _, _, depositLedger⟩ :=
      processPendingDeposits_ledger depositedOk holds room
    obtain ⟨_, transfers, _, _, transferLedger⟩ :=
      processPendingConsolidations_ledger consolidated
    exact ⟨deposited, _, _, depositLedger, transferLedger, depositLedger.trans transferLedger,
      fun before => absurd electra (Nat.not_le_of_lt before),
      fun _ => ⟨depositedOk, consolidated⟩⟩
  · rename_i electra
    cases computed
    exact ⟨state, fun _ => [], fun _ => [], BalanceLedger.refl state, BalanceLedger.refl state,
      fun i => rfl, fun _ => ⟨rfl, fun _ => rfl, fun _ => rfl⟩,
      fun electra' => absurd electra' electra⟩

/-! ## The epoch -/

/-- A registry of the same size stays within its limit. -/
theorem SameSizes.registryWithinLimit (sizes : SameSizes state after)
    (within : state.RegistryWithinLimit) : after.RegistryWithinLimit := by
  unfold BeaconState.RegistryWithinLimit at within ⊢
  rw [sizes.1]
  exact within

/-- The inactivity updates keep the sizes. -/
theorem sameSizes_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    SameSizes state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · cases computed
    exact SameSizes.refl state
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩

/-- The reset of the deposit votes keeps the sizes. -/
theorem sameSizes_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) : SameSizes state after := by
  unfold processEth1DataReset at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed <;> (cases computed; exact ⟨rfl, rfl⟩)

/-- What the slashings of an epoch do to the balances: one debit at each position.

`slashingsLedger` proves it from the balances that the slashings leave. -/
def SlashingsLedger (preset : Preset) (fork : Base.Fork) : Prop :=
  ∀ state after : BeaconState preset fork, state.RegistryWithinLimit →
    processSlashings state = .ok after →
    ∃ penalty : Nat → Nat, BalanceLedger state after fun i => [.debit .slashing (penalty i)]

/-- From Altair, the ledger of an epoch, given the ledger of its slashings.

The registry must be within its limit, with one balance for each validator.

It also needs room in 64 bits for the new validators of the pending deposits.

Each balance takes the rewards and penalties of the epoch first.

It then takes the penalty of the slashings, then the deposits credited, then the consolidations.

The rewards are those of the state that the rewards step reads.

That state comes after justification and the inactivity scores.

The deposits and consolidations are those of the state that the pending balances step reads.

No other step of the epoch changes a balance. -/
theorem processEpochAltair_ledger_of_slashings (slashings : SlashingsLedger preset fork)
    {altair : .altair ≤ fork} (within : state.RegistryWithinLimit) (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64)
    (computed : processEpochAltair config checks state altair = .ok after) :
    ∃ (justified rewarded pending : BeaconState preset fork)
      (deltas : List (Array Gwei × Array Gwei)) (penalty : Nat → Nat)
      (deposits transfers : Nat → List BalanceChange),
      (∃ middle, processJustificationAndFinalization state = .ok middle ∧
        processInactivityUpdates config middle altair = .ok justified) ∧
      processRewardsAndPenalties config justified = .ok rewarded ∧
      (getCurrentEpoch justified ≠ GENESIS_EPOCH →
        ∃ flags inactivity, (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
            (getFlagIndexDeltas justified altair) = .ok flags ∧
          getInactivityPenaltyDeltas config justified = .ok inactivity ∧
          deltas = flags ++ [inactivity]) ∧
      (getCurrentEpoch justified = GENESIS_EPOCH → deltas = []) ∧
      (∃ deposited, processPendingBalances config checks pending = .ok deposited ∧
        (∀ electra : .pectra ≤ fork, ∃ middle,
          processPendingDeposits config checks pending electra = .ok middle ∧
          processPendingConsolidations middle electra = .ok deposited ∧
          BalanceLedger pending middle deposits ∧ BalanceLedger middle deposited transfers) ∧
        (fork < .pectra → (∀ i, deposits i = []) ∧ ∀ i, transfers i = [])) ∧
      BalanceLedger state after fun i =>
        (if i < state.validators.data.size ∧ i < state.balances.data.size then
          deltaChanges deltas i else []) ++
        [.debit .slashing (penalty i)] ++ deposits i ++ transfers i := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨s1, s1Ok, s2, s2Ok, s3, s3Ok, s4, s4Ok, s5, s5Ok, s6, s6Ok, s7, s7Ok, s8, s8Ok,
    s9, s9Ok, s10, s10Ok, s11, s11Ok, computed⟩ := computed
  -- The sizes stay the same up to the pending balances.
  have size1 := sameSizes_processJustificationAndFinalization s1Ok
  have size2 := size1.trans (sameSizes_processInactivityUpdates s2Ok)
  have size3 := size2.trans (processRewardsAndPenalties_sameSizes s3Ok)
  have size4 := size3.trans (sameSizes_processRegistryUpdates s4Ok)
  have size5 := size4.trans (sameSizes_processSlashings s5Ok)
  have size6 : SameSizes state s6 := by
    split at s6Ok
    · exact size5.trans (sameSizes_processEth1DataReset s6Ok)
    · cases s6Ok
      exact size5
  -- The ledgers of the steps that change balances.
  obtain ⟨deltas, genesis, -, fromAltair, rewards⟩ :=
    processRewardsAndPenalties_ledger (size2.registryWithinLimit within) s3Ok
  obtain ⟨penalty, slashed⟩ := slashings s4 s5 (size4.registryWithinLimit within) s5Ok
  obtain ⟨deposited, deposits, transfers, depositLedger, transferLedger, pendingLedger, early,
    late⟩ := processPendingBalances_ledger s7Ok (balancesMatch_of_sameSizes size6 holds)
      (by rw [size6.1]; exact room)
  -- Every other step keeps the balances.
  have one := (BalanceLedger.of_balances (processJustificationAndFinalization_balances s1Ok)).trans
    (BalanceLedger.of_balances (processInactivityUpdates_balances s2Ok))
  have four := BalanceLedger.of_balances (processRegistryUpdates_balances s4Ok)
  have six : BalanceLedger s5 s6 fun _ => [] := by
    split at s6Ok
    · exact BalanceLedger.of_balances (processEth1DataReset_balances s6Ok)
    · cases s6Ok
      exact BalanceLedger.refl _
  -- The steps after the pending balances keep the balances.
  have b8 : s8.balances = s7.balances := by
    split at s8Ok
    · exact processBuilderPendingPayments_balances (liftAccessor_ok.mp s8Ok)
    · cases s8Ok
      rfl
  have b11 : s11.balances = s8.balances :=
    (processRandaoMixesReset_balances s11Ok).trans ((processSlashingsReset_balances s10Ok).trans
      (processEffectiveBalanceUpdates_balances s9Ok))
  have later : ∀ s12 : BeaconState preset fork, s12.balances = s11.balances →
      (∃ s13, processSyncCommitteeUpdates (processParticipationFlagUpdates s12 altair) altair =
          .ok s13 ∧ ∃ s14, (if fulu : Fork.fusaka ≤ fork then
              liftAccessor (processProposerLookahead s13 fulu) else pure s13) = .ok s14 ∧
            (if gloas : Fork.glamsterdam ≤ fork then liftAccessor (processPtcWindow s14 gloas)
              else pure s14) = .ok after) → after.balances = s11.balances := by
    intro s12 b12 rest
    obtain ⟨s13, s13Ok, s14, s14Ok, last⟩ := rest
    have b14 : s14.balances = s13.balances := by
      split at s14Ok
      · exact processProposerLookahead_balances (liftAccessor_ok.mp s14Ok)
      · cases s14Ok
        rfl
    have final : after.balances = s14.balances := by
      split at last
      · exact processPtcWindow_balances (liftAccessor_ok.mp last)
      · cases last
        rfl
    rw [final, b14, processSyncCommitteeUpdates_balances s13Ok]
    exact b12
  have rest : after.balances = s7.balances := by
    rw [← b8, ← b11]
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨s12, s12Ok, computed⟩ := computed
      exact later s12 (processHistoricalSummariesUpdate_balances s12Ok) computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨s12, s12Ok, computed⟩ := computed
      exact later s12 (processHistoricalRootsUpdate_balances s12Ok) computed
  have tail := BalanceLedger.of_balances rest
  refine ⟨s2, s3, s6, deltas, penalty, deposits, transfers, ⟨s1, s1Ok, s2Ok⟩, s3Ok,
    fun later => ?_, genesis, ⟨s7, s7Ok, fun electra => ?_,
      fun before => ⟨(early before).2.1, (early before).2.2⟩⟩, ?_⟩
  · obtain ⟨flags, inactivity, flagsOk, inactivityOk, same⟩ := fromAltair altair later
    exact ⟨flags, inactivity, flagsOk, inactivityOk, same⟩
  · obtain ⟨depositedOk, consolidatedOk⟩ := late electra
    exact ⟨deposited, depositedOk, consolidatedOk, depositLedger, transferLedger⟩
  · refine ((((((one.trans rewards).trans four).trans slashed).trans six).trans
      pendingLedger).trans tail).congr fun i => ?_
    simp only [size2.1, size2.2, List.nil_append, List.append_nil, List.foldl_append]

/-- Before Altair, the rotation of the pending attestations keeps the balances. -/
theorem processParticipationRecordUpdates_balances
    (computed : processParticipationRecordUpdates state = .ok after) :
    after.balances = state.balances := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  · cases computed
    rfl

/-- Before Altair, the ledger of an epoch, given the ledger of its slashings.

Each balance takes the rewards and penalties of the epoch, then the penalty of the slashings.

The rewards are those of the state after justification.

No other step of the epoch changes a balance. -/
theorem processEpoch_ledger_of_lt_altair_of_slashings (slashings : SlashingsLedger preset fork)
    (before : fork < .altair) (computed : processEpoch config checks state = .ok after) :
    ∃ (justified : BeaconState preset fork) (deltas : List (Array Gwei × Array Gwei))
      (penalty : Nat → Nat),
      processJustificationAndFinalization state = .ok justified ∧
      (getCurrentEpoch justified ≠ GENESIS_EPOCH →
        ∃ attestation, getAttestationDeltas config justified before = .ok attestation ∧
          deltas = [attestation]) ∧
      (getCurrentEpoch justified = GENESIS_EPOCH → deltas = []) ∧
      BalanceLedger state after fun i =>
        (if i < state.validators.data.size ∧ i < state.balances.data.size then
          deltaChanges deltas i else []) ++ [.debit .slashing (penalty i)] := by
  have notAltair : ¬ .altair ≤ fork := Nat.not_le_of_lt before
  have within : state.RegistryWithinLimit :=
    state.validators.bound (Nat.lt_trans before (by decide))
  unfold processEpoch at computed
  simp only [notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨s1, s1Ok, s2, s2Ok, s3, s3Ok, s4, s4Ok, s5, s5Ok, s6, s6Ok, s7, s7Ok, s8, s8Ok,
    s9, s9Ok, last⟩ := computed
  have size1 := sameSizes_processJustificationAndFinalization s1Ok
  have size3 := (size1.trans (processRewardsAndPenalties_sameSizes s2Ok)).trans
    (sameSizes_processRegistryUpdates s3Ok)
  obtain ⟨deltas, genesis, fromPhase0, -, rewards⟩ :=
    processRewardsAndPenalties_ledger (size1.registryWithinLimit within) s2Ok
  obtain ⟨penalty, slashed⟩ := slashings s3 s4 (size3.registryWithinLimit within) s4Ok
  have one := BalanceLedger.of_balances (processJustificationAndFinalization_balances s1Ok)
  have three := BalanceLedger.of_balances (processRegistryUpdates_balances s3Ok)
  have rest : after.balances = s4.balances := by
    rw [processParticipationRecordUpdates_balances last, processHistoricalRootsUpdate_balances s9Ok,
      processRandaoMixesReset_balances s8Ok, processSlashingsReset_balances s7Ok,
      processEffectiveBalanceUpdates_balances s6Ok, processEth1DataReset_balances s5Ok]
  refine ⟨s1, deltas, penalty, s1Ok, fromPhase0 before, genesis, ?_⟩
  refine ((((one.trans rewards).trans three).trans slashed).trans
    (BalanceLedger.of_balances rest)).congr fun i => ?_
  simp only [size1.1, size1.2, List.nil_append, List.append_nil, List.foldl_append]

/-! ## The slashings of an epoch -/

/-- For a registry within its limit, the slashings of an epoch debit each balance by its penalty.

The penalty is the one of `processSlashings_balances`. -/
theorem slashingsLedger : SlashingsLedger preset fork := by
  intro state after within computed
  have small : state.validators.data.size < 2 ^ 64 := by
    have bound : state.validators.data.size ≤ _ := within
    have := preset.VALIDATOR_REGISTRY_LIMIT.toNat_lt
    omega
  obtain ⟨total, slashedSum, _, _, _, balances⟩ := processSlashings_balances small computed
  refine ⟨fun i => epochSlashingPenalty preset fork (getCurrentEpoch state) total.toNat
    (min (slashedSum.toNat * (parameters preset fork).PROPORTIONAL_SLASHING_MULTIPLIER.toNat)
      total.toNat) state.validators.data[i]?, fun i => ?_⟩
  unfold balanceNat
  rw [balances i]
  cases state.balances.data[i]? <;> simp [BalanceChange.apply]

/-- From Altair, the ledger of an epoch.

The registry must be within its limit, with one balance for each validator.

It also needs room in 64 bits for the new validators of the pending deposits.

Each balance takes the rewards and penalties of the epoch first, then its slashing penalty.

It then takes the deposits credited, then the consolidation transfers.

No other step of the epoch changes a balance. -/
theorem processEpochAltair_ledger {altair : .altair ≤ fork} (within : state.RegistryWithinLimit)
    (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64)
    (computed : processEpochAltair config checks state altair = .ok after) :
    ∃ (justified rewarded pending : BeaconState preset fork)
      (deltas : List (Array Gwei × Array Gwei)) (penalty : Nat → Nat)
      (deposits transfers : Nat → List BalanceChange),
      (∃ middle, processJustificationAndFinalization state = .ok middle ∧
        processInactivityUpdates config middle altair = .ok justified) ∧
      processRewardsAndPenalties config justified = .ok rewarded ∧
      (getCurrentEpoch justified ≠ GENESIS_EPOCH →
        ∃ flags inactivity, (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
            (getFlagIndexDeltas justified altair) = .ok flags ∧
          getInactivityPenaltyDeltas config justified = .ok inactivity ∧
          deltas = flags ++ [inactivity]) ∧
      (getCurrentEpoch justified = GENESIS_EPOCH → deltas = []) ∧
      (∃ deposited, processPendingBalances config checks pending = .ok deposited ∧
        (∀ electra : .pectra ≤ fork, ∃ middle,
          processPendingDeposits config checks pending electra = .ok middle ∧
          processPendingConsolidations middle electra = .ok deposited ∧
          BalanceLedger pending middle deposits ∧ BalanceLedger middle deposited transfers) ∧
        (fork < .pectra → (∀ i, deposits i = []) ∧ ∀ i, transfers i = [])) ∧
      BalanceLedger state after fun i =>
        (if i < state.validators.data.size ∧ i < state.balances.data.size then
          deltaChanges deltas i else []) ++
        [.debit .slashing (penalty i)] ++ deposits i ++ transfers i :=
  processEpochAltair_ledger_of_slashings slashingsLedger within holds room computed

/-- Before Altair, the ledger of an epoch.

Each balance takes the rewards and penalties of the epoch, then its slashing penalty.

The rewards are those of the state after justification.

No other step of the epoch changes a balance. -/
theorem processEpoch_ledger_of_lt_altair (before : fork < .altair)
    (computed : processEpoch config checks state = .ok after) :
    ∃ (justified : BeaconState preset fork) (deltas : List (Array Gwei × Array Gwei))
      (penalty : Nat → Nat),
      processJustificationAndFinalization state = .ok justified ∧
      (getCurrentEpoch justified ≠ GENESIS_EPOCH →
        ∃ attestation, getAttestationDeltas config justified before = .ok attestation ∧
          deltas = [attestation]) ∧
      (getCurrentEpoch justified = GENESIS_EPOCH → deltas = []) ∧
      BalanceLedger state after fun i =>
        (if i < state.validators.data.size ∧ i < state.balances.data.size then
          deltaChanges deltas i else []) ++ [.debit .slashing (penalty i)] :=
  processEpoch_ledger_of_lt_altair_of_slashings slashingsLedger before computed

end EthLib.Consensus
