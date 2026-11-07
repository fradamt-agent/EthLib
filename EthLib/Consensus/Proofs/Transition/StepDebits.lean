module

public import EthLib.Consensus.Proofs.Transition.BlockDebits

/-!
# Proofs: what each step debits, flow by flow

A step of a chain is a slot, a block or an upgrade.

Each lowers a balance only by debits of a few kinds.

- An epoch, at the end of a slot, debits the penalties of its rewards pass.
  It also debits the penalty of the slashings, and the consolidations move balance from sources.
- A block debits withdrawals, slashings, sync penalties, and the excess queued back as a deposit.
- The upgrade to Electra moves balances to the pending deposits, as excess queued.
  Every other upgrade keeps the balances.

This file names the amount of each debit, with the computation it comes from.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## The debits of an epoch -/

/-- The passes of rewards and penalties of an epoch, read from the state the rewards step reads.

That state, `justified`, comes from the state of the epoch by justification.

From Altair the inactivity scores are updated in between.

From Altair the passes are those of the three flags, then that of inactivity.

Before Altair there is one pass, of the attestations.

At the genesis epoch there is none. -/
def EpochDeltas (config : Config) (state justified : BeaconState preset fork)
    (deltas : List (Array Gwei × Array Gwei)) : Prop :=
  (∀ altair : .altair ≤ fork,
    (∃ middle, processJustificationAndFinalization state = .ok middle ∧
      processInactivityUpdates config middle altair = .ok justified) ∧
    (getCurrentEpoch justified ≠ GENESIS_EPOCH →
      ∃ flags inactivity, (List.finRange PARTICIPATION_FLAG_WEIGHTS.length).mapM
          (getFlagIndexDeltas justified altair) = .ok flags ∧
        getInactivityPenaltyDeltas config justified = .ok inactivity ∧
        deltas = flags ++ [inactivity])) ∧
  (∀ before : fork < .altair, processJustificationAndFinalization state = .ok justified ∧
    (getCurrentEpoch justified ≠ GENESIS_EPOCH →
      ∃ attestation, getAttestationDeltas config justified before = .ok attestation ∧
        deltas = [attestation])) ∧
  (getCurrentEpoch justified = GENESIS_EPOCH → deltas = [])

/-- The penalties of the slashings of an epoch, from the state the rewards step reads.

The rewards step and the registry updates run first, then the slashings. -/
def EpochSlashing (config : Config) (justified : BeaconState preset fork)
    (penalty : Nat → Nat) : Prop :=
  ∃ rewarded registered slashedOut : BeaconState preset fork,
    processRewardsAndPenalties config justified = .ok rewarded ∧
    processRegistryUpdates config rewarded = .ok registered ∧
    processSlashings registered = .ok slashedOut ∧ SlashingPenaltyAt registered penalty

/-- The debits of an epoch to each balance, flow by flow.

The rewards pass debits the penalties of its deltas, at each position of a validator.

The slashings debit their penalty, and the consolidations what they move from a source.

No other flow debits. -/
def EpochDebits (config : Config) (state after : BeaconState preset fork) : Prop :=
  ∃ (justified : BeaconState preset fork) (deltas : List (Array Gwei × Array Gwei))
    (penalty : Nat → Nat) (transfers changes : Nat → List BalanceChange),
    BalanceLedger state after changes ∧
    EpochDeltas config state justified deltas ∧ EpochSlashing config justified penalty ∧
    ∀ i flow, BalanceChange.debited flow (changes i) =
      match flow with
      | BalanceFlow.rewards =>
        if i < state.validators.data.size ∧ i < state.balances.data.size then
          BalanceChange.debited .rewards (deltaChanges deltas i) else 0
      | BalanceFlow.slashing => penalty i
      | BalanceFlow.consolidation => BalanceChange.debited .consolidation (transfers i)
      | _ => 0

/-- One debit debits its amount of its own kind, and nothing of another. -/
theorem BalanceChange.debited_debit (flow kind : BalanceFlow) (amount : Nat) :
    BalanceChange.debited flow [.debit kind amount] = if kind = flow then amount else 0 := by
  simp [BalanceChange.debited]

/-- Nothing debits nothing. -/
theorem BalanceChange.debited_nil (flow : BalanceFlow) : BalanceChange.debited flow [] = 0 := rfl

/-- The passes of deltas debit only as rewards. -/
theorem debited_deltaChanges_of_ne {flow : BalanceFlow} (other : flow ≠ .rewards)
    (deltas : List (Array Gwei × Array Gwei)) (i : Nat) :
    BalanceChange.debited flow (deltaChanges deltas i) = 0 := by
  refine BalanceChange.debited_eq_zero fun change member amount same => ?_
  simp only [deltaChanges, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain ⟨_, _, member⟩ := member
  rcases member with rfl | rfl
  · cases same
  · cases same
    exact other rfl

/-- The debits of an epoch, at every fork.

From Altair the registry must be within its limit, with one balance for each validator.

It also needs room in 64 bits for the new validators of the pending deposits. -/
theorem processEpoch_debits (computed : processEpoch config checks state = .ok after)
    (within : state.RegistryWithinLimit) (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    EpochDebits config state after := by
  -- How the four parts of an epoch ledger debit, given what the deposits and transfers debit.
  have flows : ∀ (deltas : List (Array Gwei × Array Gwei)) (penalty : Nat → Nat)
      (deposits transfers : Nat → List BalanceChange),
      (∀ i flow, BalanceChange.debited flow (deposits i) = 0 ∧
        (flow ≠ .consolidation → BalanceChange.debited flow (transfers i) = 0)) →
      ∀ i flow, BalanceChange.debited flow
        ((if i < state.validators.data.size ∧ i < state.balances.data.size then
          deltaChanges deltas i else []) ++ [.debit .slashing (penalty i)] ++ deposits i ++
            transfers i) =
        match flow with
        | BalanceFlow.rewards =>
          if i < state.validators.data.size ∧ i < state.balances.data.size then
            BalanceChange.debited .rewards (deltaChanges deltas i) else 0
        | BalanceFlow.slashing => penalty i
        | BalanceFlow.consolidation => BalanceChange.debited .consolidation (transfers i)
        | _ => 0 := by
    intro deltas penalty deposits transfers kinds i flow
    have d := fun (flow : BalanceFlow) (other : flow ≠ .rewards) =>
      debited_deltaChanges_of_ne other deltas i
    have p := fun (flow : BalanceFlow) (other : flow ≠ .consolidation) => (kinds i flow).2 other
    simp only [BalanceChange.debited_append, (kinds i _).1]
    split <;> cases flow <;>
      simp (disch := decide) only [d, p, BalanceChange.debited_debit, BalanceChange.debited_nil,
        ite_true, ite_false, reduceCtorEq, Nat.add_zero, Nat.zero_add]
  by_cases altair : .altair ≤ fork
  · unfold processEpoch at computed
    simp only [altair, ↓reduceDIte] at computed
    obtain ⟨justified, rewarded, _, deltas, penalty, deposits, transfers, justifiedOk, rewardedOk,
      fromAltair, genesis, _, kinds, ⟨registered, slashedOut, registeredOk, slashedOk, penaltyAt⟩,
      ledger⟩ := processEpochAltair_ledger within holds room computed
    refine ⟨justified, deltas, penalty, transfers, _, ledger,
      ⟨fun _ => ⟨justifiedOk, fromAltair⟩, fun before => absurd altair (Nat.not_le_of_lt before),
        genesis⟩,
      ⟨rewarded, registered, slashedOut, rewardedOk, registeredOk, slashedOk, penaltyAt⟩,
      flows deltas penalty deposits transfers kinds⟩
  · have before : fork < .altair := Nat.lt_of_not_le altair
    obtain ⟨justified, deltas, penalty, justifiedOk, fromPhase0, genesis,
      ⟨rewarded, registered, slashedOut, rewardedOk, registeredOk, slashedOk, penaltyAt⟩,
      ledger⟩ := processEpoch_ledger_of_lt_altair before computed
    refine ⟨justified, deltas, penalty, fun _ => [], _, ledger,
      ⟨fun altair' => absurd altair' altair,
        fun _ => ⟨justifiedOk, fromPhase0⟩, genesis⟩,
      ⟨rewarded, registered, slashedOut, rewardedOk, registeredOk, slashedOk, penaltyAt⟩,
      fun i flow => ?_⟩
    have := flows deltas penalty (fun _ => []) (fun _ => [])
      (fun _ _ => ⟨rfl, fun _ => rfl⟩) i flow
    simp only [List.append_nil] at this
    exact this

/-! ## The budget of each step -/

/-- The debits of an epoch to one balance, as a budget by flow. -/
def epochBudget (state : BeaconState preset fork) (deltas : List (Array Gwei × Array Gwei))
    (penalty : Nat → Nat) (transfers : Nat → List BalanceChange) (i : Nat) :
    BalanceFlow → Nat
  | BalanceFlow.rewards =>
    if i < state.validators.data.size ∧ i < state.balances.data.size then
      BalanceChange.debited .rewards (deltaChanges deltas i) else 0
  | BalanceFlow.slashing => penalty i
  | BalanceFlow.consolidation => BalanceChange.debited .consolidation (transfers i)
  | _ => 0

/-- The debits of a block to one balance, as a budget by flow. -/
def blockBudget (fork : Base.Fork) (withdrawals : List Withdrawal)
    (sync excess : Nat → List BalanceChange) (payouts : List (SlashingPayout preset)) (i : Nat) :
    BalanceFlow → Nat
  | BalanceFlow.withdrawal =>
    BalanceChange.debited .withdrawal (withdrawalChanges fork withdrawals i)
  | BalanceFlow.blockReward => BalanceChange.debited .blockReward (sync i)
  | BalanceFlow.slashing => payoutPenalties payouts i
  | BalanceFlow.excessQueued => BalanceChange.debited .excessQueued (excess i)
  | _ => 0

/-- What a step may debit one balance, flow by flow, with where each amount comes from.

A slot that ends no epoch debits nothing.

A slot that ends an epoch debits as `epochBudget`, for the state after the slot is cached.

A block debits as `blockBudget`.

Its withdrawals, sync changes and slashing payouts are those the block computes.

An upgrade debits only the excess queued, and only the upgrade to Electra does. -/
def StepBudget (i : Nat) : {pre post : ForkedBeaconState preset} →
    Step config checks pre post → (BalanceFlow → Nat) → Prop
  | _, _, .slot (fork := fork) (state := state) _ _, budget =>
    budget = (fun _ => 0) ∨
      ∃ (cached epoched justified : BeaconState preset fork)
        (deltas : List (Array Gwei × Array Gwei)) (penalty : Nat → Nat)
        (transfers : Nat → List BalanceChange),
        processSlot state = .ok cached ∧ processEpoch config checks cached = .ok epoched ∧
        EpochDeltas config cached justified deltas ∧ EpochSlashing config justified penalty ∧
        budget = epochBudget cached deltas penalty transfers i
  | _, _, .block (fork := fork) (state := state) engine signed _ _ _, budget =>
    ∃ (withdrawals : List Withdrawal) (sync excess : Nat → List BalanceChange)
      (payouts : List (SlashingPayout preset)),
      BlockWithdrawals preset fork withdrawals ∧
      BlockSync (preset := preset) config checks fork sync ∧
      blockSlashingPayouts config checks engine state signed.message = .ok payouts ∧
      (∀ i, ∀ change ∈ excess i, IsExcessQueued change) ∧
      budget = blockBudget fork withdrawals sync excess payouts i
  | _, _, .upgrade _ _, budget => ∀ flow, flow ≠ .excessQueued → budget flow = 0

/-- Every step from a state ready for a ledger debits within a budget of `StepBudget`. -/
theorem Step.debitsWithin {pre post : ForkedBeaconState preset}
    (step : Step config checks pre post) (ready : LedgerReady pre) (i : Nat) :
    ∃ budget, DebitsWithin pre post i budget ∧ StepBudget i step budget := by
  cases step with
  | slot _ computed =>
    rename_i fork state after
    simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    unfold epochIfLast at epochedOk
    split at epochedOk
    · obtain ⟨justified, deltas, penalty, transfers, changes, ledger, deltasSpec, slashingSpec,
        flows⟩ := processEpoch_debits epochedOk ready.within ready.holds ready.room
      refine ⟨epochBudget _ deltas penalty transfers i, ⟨changes i, ledger i, fun flow => ?_⟩,
        Or.inr ⟨_, epoched, justified, deltas, penalty, transfers, cachedOk, epochedOk,
          deltasSpec, slashingSpec, rfl⟩⟩
      rw [flows i flow]
      cases flow <;> exact Nat.le_refl _
    · cases epochedOk
      exact ⟨fun _ => 0, ⟨[], rfl, fun _ => Nat.le_refl _⟩, Or.inl rfl⟩
  | block engine signed _ _ computed =>
    obtain ⟨excess, slashings, sync, withdrawals, changes, ledger, withdrawalSpec, syncSpec,
      ⟨payouts, payoutsOk, slashingBound⟩, excessKind, flows⟩ :=
      (processBlock_debits (applySignedBlock_ok computed).2.1 ready.holds).debited
    refine ⟨blockBudget _ withdrawals sync excess payouts i,
      ⟨changes i, ledger i, fun flow => ?_⟩,
      withdrawals, sync, excess, payouts, withdrawalSpec, syncSpec, payoutsOk, excessKind, rfl⟩
    rw [flows i flow]
    cases flow
    · exact Nat.le_refl _
    · exact slashingBound i
    all_goals exact Nat.le_refl _
  | upgrade due computed =>
    rename_i upgraded
    obtain ⟨fork, state⟩ := pre
    -- Each upgrade but that to Electra keeps the balances.
    suffices kept : upgraded.val.state.balances.data = state.balances.data ∨
        ∃ changes : Nat → List BalanceChange,
          (∀ i, balanceAt upgraded.val.state i =
            (changes i).foldl BalanceChange.apply (balanceAt state i)) ∧
          ∀ i, ∀ change ∈ changes i, IsQueuedDebit change by
      rcases kept with same | ⟨changes, ledger, queued⟩
      · exact ⟨fun _ => 0, ⟨[], by simp [balanceAt, same], fun _ => Nat.le_refl _⟩,
          fun _ _ => rfl⟩
      · refine ⟨fun flow => BalanceChange.debited flow (changes i),
          ⟨changes i, ledger i, fun _ => Nat.le_refl _⟩, fun flow other => ?_⟩
        exact BalanceChange.debited_eq_zero fun change member amount same => by
          have := queued i change member
          rw [same] at this
          exact other this
    cases fork <;>
      simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
        throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
    · obtain ⟨_, upgradedOk, rfl⟩ := computed
      exact .inl (upgradeToAltair_spec upgradedOk).2.1
    · subst computed
      exact .inl rfl
    · subst computed
      exact .inl rfl
    · subst computed
      exact .inl rfl
    · obtain ⟨_, upgradedOk, rfl⟩ := computed
      obtain ⟨changes, ledger, queued⟩ := upgradeToElectra_ledgerOf upgradedOk
      exact .inr ⟨changes, ledger, queued⟩
    · obtain ⟨_, upgradedOk, rfl⟩ := computed
      exact .inl (upgradeToFulu_spec upgradedOk).2.1
    · obtain ⟨_, upgradedOk, rfl⟩ := computed
      exact .inl (upgradeToGloas_spec upgradedOk).2.1
    · obtain ⟨_, upgradedOk, rfl⟩ := computed
      obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgradedOk
      exact .inl (upgradeHezeFields_lists _).2.1

/-! ## The budgets of a run -/

namespace Run

variable {start : ForkedBeaconState preset}

/-- A budget of `StepBudget` for each step of a run, in order. -/
def Budgets (i : Nat) : {after : ForkedBeaconState preset} → Run config checks start after →
    List (BalanceFlow → Nat) → Prop
  | _, .nil, budgets => budgets = []
  | _, .snoc run step, budgets =>
    ∃ earlier budget, budgets = earlier ++ [budget] ∧ run.Budgets i earlier ∧
      StepBudget i step budget

/-- What a run debits a balance is at most the sum of the budgets of its steps, flow by flow.

Each budget is of `StepBudget`: it names the debits of its step and where they come from.

Each state of the run before the last must be ready for a ledger. -/
theorem fallen_le_stepBudgets (i : Nat) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      (∀ state ∈ run.states, LedgerReady state) →
      ∃ budgets, run.Budgets i budgets ∧
        run.fallen i ≤ (BalanceFlow.all.map fun flow => (budgets.map (· flow)).sum).sum
  | _, .nil, _ => ⟨[], rfl, by simp [fallen, BalanceFlow.all]⟩
  | _, .snoc (middle := middle) run step, ready => by
    obtain ⟨earlier, earlierOk, bound⟩ :=
      fallen_le_stepBudgets i run fun state member => ready state (List.mem_append_left _ member)
    obtain ⟨budget, within, spec⟩ :=
      step.debitsWithin (ready middle (List.mem_append_left _ (end_mem_states run))) i
    refine ⟨earlier ++ [budget], ⟨earlier, budget, rfl, earlierOk, spec⟩, ?_⟩
    have here := within.fall_le
    simp only [fallen, BalanceFlow.all, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil] at bound here ⊢
    omega

end Run

/-- Along a run from a reachable state, the effective balance lost by an active validator.

The validator is active at the start, at some epoch.

It loses at most its slack at the start, plus less than one increment.

It also loses at most the sum of the budgets of the steps, flow by flow.

Each budget is of `StepBudget`, which names its amounts and where they come from.

Each state of the run before the last must be ready for a ledger.

The increment must be positive, and from Gloas the registry at the end below `2^64`. -/
theorem Run.effectiveAt_fall_le_stepBudgets (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {start after : ForkedBeaconState preset} (reachable : Reachable config checks start)
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    (ready : ∀ state ∈ run.states, LedgerReady state)
    {position : Nat} {epoch : Epoch} (active : activeAt start.state epoch position = true) :
    ∃ budgets, run.Budgets position budgets ∧
      effectiveAt start.state position - effectiveAt after.state position ≤
        (effectiveAt start.state position - balanceAt start.state position) +
          (BalanceFlow.all.map fun flow => (budgets.map (· flow)).sum).sum +
          (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  obtain ⟨budgets, budgetsOk, bound⟩ := run.fallen_le_stepBudgets position ready
  have fall := run.effectiveAt_fall_le caps increment reachable small active
  exact ⟨budgets, budgetsOk, by omega⟩

/-! ## Slashing penalties along a run -/

/-- Payouts of distinct validators pay at most one initial penalty at a position.

That is the penalty of the one payout that slashes the validator there, if any. -/
theorem payoutPenalties_of_nodup {payouts : List (SlashingPayout preset)}
    (nodup : (payouts.map (·.index)).Nodup) (i : Nat) :
    payoutPenalties payouts i = 0 ∨ ∃ payout ∈ payouts, payout.index.toNat = i ∧
      payoutPenalties payouts i = initialSlashingPenalty preset payout.fork payout.validator := by
  induction payouts with
  | nil => exact .inl rfl
  | cons payout rest more =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at nodup
    obtain ⟨fresh, nodup⟩ := nodup
    by_cases here : payout.index.toNat = i
    · -- No later payout slashes the same position, since the indices differ.
      have none : payoutPenalties rest i = 0 := by
        simp only [payoutPenalties, List.sum_eq_zero_iff, List.mem_map, List.mem_filter,
          beq_iff_eq]
        rintro _ ⟨other, ⟨member, same⟩, rfl⟩
        exact absurd ⟨other, member, UInt64.toNat_inj.mp (same.trans here.symm)⟩ fresh
      refine .inr ⟨payout, List.mem_cons_self, here, ?_⟩
      have split := payoutPenalties_append [payout] rest i
      simp only [List.singleton_append] at split
      rw [split, none]
      simp [payoutPenalties, here]
    · have split := payoutPenalties_append [payout] rest i
      simp only [List.singleton_append] at split
      have first : payoutPenalties [payout] i = 0 := by simp [payoutPenalties, here]
      rw [split, first, Nat.zero_add]
      rcases more nodup with zero | ⟨other, member, named, value⟩
      · exact .inl zero
      · exact .inr ⟨other, List.mem_cons_of_mem _ member, named, value⟩

/-- Along a run, the initial slashing penalties at a position are at most one penalty.

It is the penalty of the one payout of the run that slashes the validator there, if any.

The registry at the end of the run must be below `2^64`. -/
theorem Run.payoutPenalties_slashingPayouts {start after : ForkedBeaconState preset}
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    (i : Nat) :
    payoutPenalties run.slashingPayouts i = 0 ∨ ∃ payout ∈ run.slashingPayouts,
      payout.index.toNat = i ∧ payout.Valid config ∧
      payoutPenalties run.slashingPayouts i =
        initialSlashingPenalty preset payout.fork payout.validator := by
  have ledger := run.slashingLedger small
  rcases payoutPenalties_of_nodup ledger.nodup i with zero | ⟨payout, member, named, value⟩
  · exact .inl zero
  · exact .inr ⟨payout, member, named, ledger.valid payout member, value⟩

/-- The slashing budget of a block is the initial penalties of the payouts of that block. -/
theorem StepBudget.slashing_block {fork : Base.Fork} {state after : BeaconState preset fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {due : upgradeDue config ⟨fork, state⟩ = false}
    {computed : applySignedBlock config checks engine state signed validateResult = .ok after}
    {i : Nat} {budget : BalanceFlow → Nat}
    (spec : StepBudget i (Step.block engine signed validateResult due computed) budget) :
    budget .slashing = payoutPenalties (Step.block engine signed validateResult due computed
      ).slashingPayouts i := by
  obtain ⟨_, _, _, payouts, _, _, payoutsOk, _, rfl⟩ := spec
  simp [blockBudget, Step.slashingPayouts, payoutsOk]

end EthLib.Consensus
