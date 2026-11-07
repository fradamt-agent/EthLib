module

public import EthLib.Consensus.Proofs.Transition.BuilderPayments
public import EthLib.Consensus.Proofs.Transition.EpochPending
public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Proofs.Transition.Requests
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

/-- A ledger of a step: each balance after it is the one before, with its changes applied in order.
-/
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

/-- Starting the exit of a validator keeps the balances. -/
theorem initiateValidatorExit_balances {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    after.balances = state.balances := by
  unfold initiateValidatorExit at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · cases computed
    rfl
  · simp only [bind_ok_iff] at computed
    obtain ⟨⟨queued, _⟩, queuedOk, _, _, set⟩ := computed
    rw [setValidator_balances set, (exitQueue_validators queuedOk).2]

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

end EthLib.Consensus
