module

public import EthLib.Consensus.Proofs.Transition.EffectiveBalanceDrift
public import EthLib.Consensus.Proofs.Transition.GainedBound

/-!
# Proofs: the stake lost along a run

Fix a reachable state `x` and a run from `x` to a state `s`.

The stake lost by the validators active at `x` is the sum of their falls in effective balance:

```text
    lost(x, s) = sum_{i in A} (eff_x i - eff_s i)
```

Here `A` is a set of validators active at `x`, and `-` stops at zero.

Each fall is at most three amounts.

- The slack at `x`: `eff_x i - bal_x i`, read exactly from `x`.
- What the run debits the balance: `fallen i`, the sum of the fall of the balance at each step.
- The rounding: less than one increment.

A ledger of each step bounds its fall by the debits of that step.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

namespace Run

variable {start : ForkedBeaconState preset}

/-- The drop of a balance along a run is at most what the run debits it. -/
theorem balanceDrop_le_fallen {after : ForkedBeaconState preset}
    (run : Run config checks start after) (position : Nat) :
    run.balanceDrop position ≤ run.fallen position := by
  unfold balanceDrop largest
  have below := balanceAt_ge_fallen position run
  generalize run.states = states at below ⊢
  induction states with
  | nil => simp
  | cons first rest more =>
    have here := below first List.mem_cons_self
    have later := more fun state member => below state (List.mem_cons_of_mem _ member)
    simp only [List.foldr_cons] at later ⊢
    omega

/-- A validator active at an epoch has an activation epoch. -/
theorem activationEpoch_ne_of_activeAt {fork : Base.Fork} {state : BeaconState preset fork}
    {epoch : Epoch} {position : Nat} (active : activeAt state epoch position = true)
    {validator : Validator} (found : state.validators.data[position]? = some validator) :
    validator.activationEpoch ≠ FAR_FUTURE_EPOCH := by
  simp only [activeAt, found, Option.any_some, isActiveValidator, Bool.and_eq_true,
    decide_eq_true_eq] at active
  intro far
  -- The exit epoch would be above the largest epoch.
  have := active.2
  have bounded := validator.exitEpoch.toNat_lt
  simp only [far, FAR_FUTURE_EPOCH] at active
  have := UInt64.le_iff_toNat_le.mp active.1
  have := UInt64.lt_iff_toNat_lt.mp active.2
  simp at *
  omega

/-- Along a run from a reachable state, an active validator loses at most three amounts.

It is a validator active at the start, and the loss is of effective balance.

They are the slack at the start, what the run debits the balance, and less than one increment.

The increment must be positive, and from Gloas the registry at the end below `2^64`. -/
theorem effectiveAt_fall_le (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {after : ForkedBeaconState preset} (reachable : Reachable config checks start)
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    {position : Nat} {epoch : Epoch} (active : activeAt start.state epoch position = true) :
    effectiveAt start.state position - effectiveAt after.state position ≤
      (effectiveAt start.state position - balanceAt start.state position) +
        run.fallen position + (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  -- An active validator is present at the start.
  obtain ⟨validator, found⟩ : ∃ validator,
      start.state.validators.data[position]? = some validator := by
    cases present : start.state.validators.data[position]? with
    | none => simp [activeAt, present] at active
    | some validator => exact ⟨validator, rfl⟩
  obtain ⟨later, laterFound, fall⟩ := run.effectiveBalance_fall_le caps increment reachable small
    found (activationEpoch_ne_of_activeAt active found)
  have dropped := run.balanceDrop_le_fallen position
  simp only [effectiveAt, found, laterFound, Option.map_some, Option.getD_some]
  omega

/-- Along a run from a reachable state, the stake lost by validators active at the start.

Each loses at most its slack at the start, what the run debits it, and the rounding.

The increment must be positive, and from Gloas the registry at the end below `2^64`. -/
theorem lost_le (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {after : ForkedBeaconState preset} (reachable : Reachable config checks start)
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    (positions : Finset Nat) {epoch : Epoch}
    (active : ∀ position ∈ positions, activeAt start.state epoch position = true) :
    ∑ position ∈ positions, (effectiveAt start.state position - effectiveAt after.state position) ≤
      ∑ position ∈ positions,
        ((effectiveAt start.state position - balanceAt start.state position) +
          run.fallen position + (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)) :=
  Finset.sum_le_sum fun position member =>
    run.effectiveAt_fall_le caps increment reachable small (active position member)

end Run

/-! ## What a run debits, by flow -/

/-- Every kind of balance change. -/
def BalanceFlow.all : List BalanceFlow :=
  [.rewards, .slashing, .deposit, .consolidation, .withdrawal, .blockReward, .excessQueued]

/-- What some changes debit, of every kind, is the sum of what they debit of each kind. -/
theorem BalanceChange.debitedAll_eq_sum :
    ∀ changes : List BalanceChange, BalanceChange.debitedAll changes =
      (BalanceFlow.all.map fun flow => BalanceChange.debited flow changes).sum
  | [] => by simp [BalanceChange.debitedAll, BalanceChange.debited, BalanceFlow.all]
  | change :: rest => by
    have later := BalanceChange.debitedAll_eq_sum rest
    simp only [BalanceChange.debitedAll, BalanceChange.debited, BalanceFlow.all, List.map_cons,
      List.sum_cons, List.map_nil, List.sum_nil] at later ⊢
    cases change with
    | credit => simp only [later]; omega
    | debit flow amount =>
      cases flow <;> simp only [later, ite_true, reduceCtorEq, ite_false] <;> omega

/-- A move of one balance, from one state to another, debits at most a budget of each kind.

Some changes take the balance from the first state to the second.

What they debit of each kind is at most the budget of that kind. -/
def DebitsWithin (pre post : ForkedBeaconState preset) (position : Nat)
    (budget : BalanceFlow → Nat) : Prop :=
  ∃ changes : List BalanceChange,
    balanceAt post.state position =
      changes.foldl BalanceChange.apply (balanceAt pre.state position) ∧
    ∀ flow, BalanceChange.debited flow changes ≤ budget flow

/-- A balance falls by at most the sum of the budgets of the changes that move it. -/
theorem DebitsWithin.fall_le {pre post : ForkedBeaconState preset} {position : Nat}
    {budget : BalanceFlow → Nat} (within : DebitsWithin pre post position budget) :
    balanceAt pre.state position - balanceAt post.state position ≤
      (BalanceFlow.all.map budget).sum := by
  obtain ⟨changes, ledger, bounded⟩ := within
  have fall := BalanceChange.le_foldl_apply changes (balanceAt pre.state position)
  rw [← ledger, BalanceChange.debitedAll_eq_sum] at fall
  have sums : (BalanceFlow.all.map fun flow => BalanceChange.debited flow changes).sum ≤
      (BalanceFlow.all.map budget).sum :=
    List.sum_le_sum fun flow _ => bounded flow
  omega

namespace Run

variable {start : ForkedBeaconState preset}

/-- The sum over the steps of a run of a cost of each step. -/
def sumSteps (cost : ∀ {pre post : ForkedBeaconState preset}, Step config checks pre post → Nat) :
    {after : ForkedBeaconState preset} → Run config checks start after → Nat
  | _, .nil => 0
  | _, .snoc run step => run.sumSteps cost + cost step

/-- What a run debits a balance is at most what its steps may debit, flow by flow.

The budget of each step need only hold for a step from a state reached from the start.

The sum is over the kinds of change, of the budgets of that kind over the steps. -/
theorem fallen_le_budgets (position : Nat)
    (budget : ∀ {pre post : ForkedBeaconState preset}, Step config checks pre post →
      BalanceFlow → Nat)
    (within : ∀ {pre post : ForkedBeaconState preset} (step : Step config checks pre post),
      Reaches config checks start pre → DebitsWithin pre post position (budget step)) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      run.fallen position ≤
        (BalanceFlow.all.map fun flow => run.sumSteps fun step => budget step flow).sum
  | _, .nil => by simp [fallen, sumSteps, BalanceFlow.all]
  | _, .snoc run step => by
    have earlier := fallen_le_budgets position budget within run
    have here := (within step ⟨run⟩).fall_le
    simp only [fallen, sumSteps, BalanceFlow.all, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at earlier here ⊢
    omega

/-- Along a run from a reachable state, the stake lost by active validators, flow by flow.

They are the validators active at the start.

Each validator loses at most its slack at the start, plus the rounding.

It also loses at most what the steps of the run may debit its balance, of each kind.

The increment must be positive, and from Gloas the registry at the end below `2^64`. -/
theorem lost_le_budgets (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {after : ForkedBeaconState preset} (reachable : Reachable config checks start)
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    (positions : Finset Nat) {epoch : Epoch}
    (active : ∀ position ∈ positions, activeAt start.state epoch position = true)
    (budget : Nat → ∀ {pre post : ForkedBeaconState preset}, Step config checks pre post →
      BalanceFlow → Nat)
    (within : ∀ position ∈ positions, ∀ {pre post : ForkedBeaconState preset}
      (step : Step config checks pre post),
      Reaches config checks start pre → DebitsWithin pre post position (budget position step)) :
    ∑ position ∈ positions, (effectiveAt start.state position - effectiveAt after.state position) ≤
      ∑ position ∈ positions,
        ((effectiveAt start.state position - balanceAt start.state position) +
          (BalanceFlow.all.map fun flow =>
            run.sumSteps fun step => budget position step flow).sum +
          (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)) :=
  Finset.sum_le_sum fun position member => by
    have fall := run.effectiveAt_fall_le caps increment reachable small (active position member)
    have debits := run.fallen_le_budgets position (budget position) (within position member)
    omega

end Run

end EthLib.Consensus
