module

public import EthLib.Consensus.Proofs.Transition.ExitStake
public import EthLib.Consensus.Proofs.Transition.StepDebits

/-!
# Proofs: the effective balance an exit loses before its churn is charged

From Electra an exit spends churn equal to the effective balance of its validator then.

[EIP-7251] specifies it.

`Run.exitingStake_le` bounds the stake of the validators that start to exit over a run.

That stake is their effective balance at the start of the run.

It is the churn of the epochs they reach, plus what each lost before its exit was charged.

That loss is a fall of effective balance from the start of the run to the step of the exit.

`Run.effectiveAt_fall_le_stepBudgets` bounds such a fall by three amounts.

They are the slack at the start, the budgets of the steps flow by flow, and less than one increment.

This file puts the two together.

So the stake that starts to exit is at most the churn plus three amounts per validator.

They are its slack, its step budgets and the rounding.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The effective balance at a position is the same, read either way. -/
theorem effectiveBalanceAtPosition_eq_effectiveAt {fork : Base.Fork}
    (state : BeaconState preset fork) (position : Nat) :
    effectiveBalanceAtPosition state position = effectiveAt state position := by
  unfold effectiveBalanceAtPosition effectiveAt
  cases state.validators.data[position]? <;> rfl

/-- A registry ready for a ledger is below `2^64`. -/
theorem LedgerReady.small {forked : ForkedBeaconState preset} (ready : LedgerReady forked) :
    forked.state.validators.data.size < 2 ^ 64 :=
  Nat.lt_of_le_of_lt ready.within (UInt64.toNat_lt _)

/-- Along a run from a reachable state from Electra, what an exit lost before its charge.

The validator is active at the start at some epoch, and has no exit epoch then.

It has one at the end.

Take the effective balance it lost, from the start to the step that set its exit.

It is at most three amounts.

They are its slack at the start, what the run debits its balance, and less than one increment.

Every registry of the run must be below `2^64`. -/
theorem Run.charged_loss_le (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {start : ForkedBeaconState preset} (electra : .pectra ≤ start.fork)
    (reachable : Reachable config checks start) {position : Nat} {epoch : Epoch}
    (active : activeAt start.state epoch position = true) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      (∀ forked ∈ run.states, forked.state.validators.data.size < 2 ^ 64) →
      ∀ (validator later : Validator), start.state.validators.data[position]? = some validator →
        validator.exitEpoch = FAR_FUTURE_EPOCH →
        after.state.validators.data[position]? = some later →
        later.exitEpoch ≠ FAR_FUTURE_EPOCH →
        effectiveAt start.state position - run.chargedBalance position ≤
          (effectiveAt start.state position - balanceAt start.state position) +
            run.fallen position + (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)
  | _, .nil, _, validator, later, found, far, found', set => by
    rw [found] at found'
    cases found'
    exact absurd far set
  | after, .snoc (middle := middle) run step, small, validator, later, found, far, found', set => by
    have earlier : ∀ forked ∈ run.states, forked ∈ (Run.snoc run step).states :=
      fun _ member => List.mem_append_left _ member
    have middleSmall := small middle (earlier _ (Run.end_mem_states run))
    have grows : run.fallen position ≤ (Run.snoc run step).fallen position := by
      simp only [Run.fallen]
      omega
    unfold Run.chargedBalance
    split
    · -- The last step set the exit, from the effective balance of the state before it.
      rw [effectiveBalanceAtPosition_eq_effectiveAt]
      have fall := run.effectiveAt_fall_le caps increment reachable middleSmall active
      omega
    · -- The exit was set earlier, and the validator is still there before the last step.
      rename_i notStarted
      have kept := Run.exitsKept electra run middleSmall
      obtain ⟨current, currentFound, -⟩ := kept.exits middleSmall position validator found
      have currentSet : current.exitEpoch ≠ FAR_FUTURE_EPOCH := by
        intro currentFar
        apply notStarted
        simp [startedExit, currentFound, found', currentFar, set]
      have := Run.charged_loss_le caps increment electra reachable active run
        (fun forked member => small forked (earlier forked member)) validator current found far
        currentFound currentSet
      omega

/-- The stake that starts to exit over a run from a reachable state from Electra.

Take caps on the churns of every state of the run, and on the churn left at its start.

Count the validators that start to exit, with an exit epoch up to some epoch.

Each must be active at the start, at some epoch.

Their effective balance at the start is at most a churn plus three amounts per validator.

The churn is that of the epochs from the first one a new exit may take.

The amounts are the slack at the start, the budgets of the steps for it, and the rounding.

The rounding is less than one increment.

Each budget is of `StepBudget`, which names its debits flow by flow.

Each state of the run must be ready for a ledger. -/
theorem Run.exitingStake_le_budgets (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {capExit capConsolidation largest : Nat} {start after : ForkedBeaconState preset}
    (electra : .pectra ≤ start.fork) (reachable : Reachable config checks start)
    (run : Run config checks start after) (ready : ∀ forked ∈ run.states, LedgerReady forked)
    (churns : ∀ forked ∈ run.states, ChurnsBounded config capExit capConsolidation largest forked)
    (lefts : LeftBounded capExit capConsolidation start) (upTo : Nat)
    (active : ∀ position ∈ exitsBetween start.state after.state 0 upTo,
      ∃ epoch, activeAt start.state epoch position = true) :
    ∃ budgets : Nat → List (BalanceFlow → Nat),
      (∀ position, run.Budgets position (budgets position)) ∧
      ∑ position ∈ exitsBetween start.state after.state 0 upTo, effectiveAt start.state position ≤
        (upTo + 1 - firstExitEpoch preset start.state) * (capExit + capConsolidation) +
          ∑ position ∈ exitsBetween start.state after.state 0 upTo,
            ((effectiveAt start.state position - balanceAt start.state position) +
              (BalanceFlow.all.map fun flow => ((budgets position).map (· flow)).sum).sum +
              (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)) := by
  have small : ∀ forked ∈ run.states, forked.state.validators.data.size < 2 ^ 64 :=
    fun forked member => (ready forked member).small
  have afterSmall := small after (Run.end_mem_states run)
  -- One list of budgets per position, each of the run.
  have chosen := fun position => run.fallen_le_stepBudgets position ready
  refine ⟨fun position => (chosen position).choose,
    fun position => (chosen position).choose_spec.1, ?_⟩
  have bound := Run.exitingStake_le electra run afterSmall churns lefts upTo
  simp only [effectiveBalanceAtPosition_eq_effectiveAt] at bound
  refine Nat.le_trans bound (Nat.add_le_add_left (Finset.sum_le_sum fun position member => ?_) _)
  -- Each exiting validator had no exit epoch at the start and has one at the end.
  obtain ⟨_, starts⟩ := mem_exitsBetween.mp member
  obtain ⟨validator, later, found, found', far, set⟩ := startsExit_eq_true starts
  obtain ⟨epoch, isActive⟩ := active position member
  have loss := Run.charged_loss_le caps increment electra reachable isActive run small validator
    later found far found' set
  have budget := (chosen position).choose_spec.2
  dsimp only
  omega

end EthLib.Consensus
