module

public import EthLib.Consensus.Proofs.Transition.FfgStoreRuns
public import EthLib.Consensus.Proofs.Transition.ExitLoss
public import EthLib.Consensus.Proofs.Transition.DepositChurn
public import EthLib.Consensus.Proofs.Transition.DepositCredits

/-!
# Proofs: the drift of the weighing along a run from Electra

The drift from the weighing of a state `x` to a weighing of a later state `s` has four terms.

They are the stake that leaves, the stake lost, the stake gained and the stake that joins.

Before Electra, `drift_ofState_le` bounds the gain by the room below `MAX_EFFECTIVE_BALANCE`.

From Electra the cap is `MAX_EFFECTIVE_BALANCE_ELECTRA`, so that bound is too weak to use.

[EIP-7251] raises the cap, and adds the churn of exits, consolidations and deposits by balance.

`drift_ofState_le_gained` keeps the gain as a sum, at every fork.

`Run.drift_le_electra` bounds each term along a run from a reachable state from Electra:

- leaving, by the exits queued at `x`, the churn of exits and consolidations, and step budgets;
- lost, by `lossBudget` of step budgets;
- gained, by the excess of balance at `x`, the deposit churn and the gains after deposits;
- joining, by the stake waiting at `x`, the growth of joiners and the stake of new validators.

The gains after deposits, the growth of joiners and the stake of new validators stay as sums.

They are rewards and consolidations, which no churn limits.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork fork' : Base.Fork}

/-- The drift from the weighing of `x` to a weighing of `s`, at every fork, term by term.

The gain of the validators active at `x` that vote at `s` stays a sum. -/
theorem drift_ofState_le_gained {x : BeaconState preset fork} {s : BeaconState preset fork'}
    (withinX : x.RegistryWithinLimit) (withinS : s.RegistryWithinLimit)
    (votersX votersS : Finset ValidatorIndex)
    (voting : ∀ i ∈ votersS, activeAt s (getPreviousEpoch s) i.toNat = true ∨
      activeAt s (getCurrentEpoch s) i.toNat = true) :
    Weighing.drift (Weighing.ofState x votersX) (Weighing.ofState s votersS) ≤
      2 * leavingStake x s + 2 * lostStake x s +
        3 * ∑ v ∈ (Weighing.ofState x votersX).active ∩ (Weighing.ofState s votersS).voters,
          ((Weighing.ofState s votersS).stake v - (Weighing.ofState x votersX).stake v) +
        3 * joiningStakePrev x s + 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have e₁ := exited_le withinX withinS votersX votersS
  have e₂ := lost_le (s := s) withinX votersX votersS
  have e₄ := entered_le (x := x) withinX votersX votersS voting
  unfold Weighing.drift
  have floor : (Weighing.ofState s votersS).floor = preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    rfl
  omega

/-- The positions of the validators active at the current epoch of a state. -/
def activePositions (x : BeaconState preset fork) : Finset Nat :=
  (Finset.range x.validators.data.size).filter (activeAt x (getCurrentEpoch x) · = true)

/-- The balance above the effective balance of the validators active at `x`. -/
def excessStake (x : BeaconState preset fork) : Nat :=
  ∑ j ∈ activePositions x, (balanceAt x j - effectiveAt x j)

/-- Whether a validator joins the active set from `x` to `s`, as `joiningStakePrev` counts. -/
def joinsAt (x : BeaconState preset fork) (s : BeaconState preset fork') (j : Nat) : Bool :=
  (activeAt s (getPreviousEpoch s) j || activeAt s (getCurrentEpoch s) j) &&
    !activeAt x (getCurrentEpoch x) j

theorem effectiveBalanceAtPosition_eq (state : BeaconState preset fork) (j : Nat) :
    effectiveBalanceAtPosition state j = effectiveAt state j := by
  unfold effectiveBalanceAtPosition effectiveAt
  cases state.validators.data[j]? <;> rfl

/-- A voter at `s` has an exit epoch at least the current epoch of `s`. -/
theorem exitEpoch_of_voting {s : BeaconState preset fork'} {j : Nat} {validator : Validator}
    (found : s.validators.data[j]? = some validator)
    (voting : activeAt s (getPreviousEpoch s) j = true ∨ activeAt s (getCurrentEpoch s) j = true) :
    (getCurrentEpoch s).toNat ≤ validator.exitEpoch.toNat := by
  have previous := getPreviousEpoch_toNat s
  rcases voting with active | active <;>
  · simp only [activeAt, found, Option.any_some, isActiveValidator, Bool.and_eq_true,
      decide_eq_true_eq] at active
    have := UInt64.lt_iff_toNat_lt.mp active.2
    omega

/-- Along a run from a reachable state from Electra, the gain of the voters active at the start.

It is at most the sum of three terms, over the validators active at the start:

- the excess of balance at the start;
- the deposits that the churn charges;
- the gains after deposits.

Every state of the run must be ready for a ledger. -/
theorem Run.gainedVoters_le {x s : ForkedBeaconState preset} (electra : .pectra ≤ x.fork)
    (reachable : Reachable config checks x) (run : Run config checks x s)
    (ready : ∀ y ∈ run.states, LedgerReady y) (votersX votersS : Finset ValidatorIndex)
    (voting : ∀ i ∈ votersS, activeAt s.state (getPreviousEpoch s.state) i.toNat = true ∨
      activeAt s.state (getCurrentEpoch s.state) i.toNat = true) :
    ∑ v ∈ (Weighing.ofState x.state votersX).active ∩ (Weighing.ofState s.state votersS).voters,
        ((Weighing.ofState s.state votersS).stake v - (Weighing.ofState x.state votersX).stake v) ≤
      excessStake x.state + run.depositsCharged +
        ∑ j ∈ activePositions x.state, run.gainsAfterDeposit j := by
  have withinX := (ready x (Run.start_mem_states run)).within
  have small := (ready s (Run.end_mem_states run)).small
  simp only [Weighing.ofState, effectiveBalanceAt_eq]
  rw [sum_toNat _ fun j => effectiveAt s.state j - effectiveAt x.state j]
  set P := ((getActiveValidatorIndices x.state (getCurrentEpoch x.state)).toFinset ∩
    votersS).image UInt64.toNat
  have sub : P ⊆ activePositions x.state := by
    intro j member
    obtain ⟨i, inter, rfl⟩ := Finset.mem_image.mp member
    have active := (mem_active_iff withinX).mp (List.mem_toFinset.mp (Finset.mem_inter.mp inter).1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (activeAt_lt active), active⟩
  have present : ∀ j ∈ P, j < x.state.validators.data.size := fun j member =>
    Finset.mem_range.mp (Finset.mem_filter.mp (sub member)).1
  have staying : ∀ j ∈ P, ∀ validator, s.state.validators.data[j]? = some validator →
      (getCurrentEpoch s.state).toNat ≤ validator.exitEpoch.toNat := by
    intro j member validator found
    obtain ⟨i, inter, rfl⟩ := Finset.mem_image.mp member
    exact exitEpoch_of_voting found (voting i (Finset.mem_inter.mp inter).2)
  have gained := run.gained_le small P present
  have credits := Run.depositCredits_le electra reachable run small
    (fun y member => (ready y member).room) P staying
  have split : ∑ j ∈ P, run.credited j ≤
      ∑ j ∈ P, run.depositCredits j + ∑ j ∈ P, run.gainsAfterDeposit j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => Run.credited_le j run
  have excess : ∑ j ∈ P, (balanceAt x.state j - effectiveAt x.state j) ≤ excessStake x.state :=
    Finset.sum_le_sum_of_subset sub
  have gains : ∑ j ∈ P, run.gainsAfterDeposit j ≤
      ∑ j ∈ activePositions x.state, run.gainsAfterDeposit j :=
    Finset.sum_le_sum_of_subset sub
  rw [Finset.sum_add_distrib] at gained
  omega

/-- The drift along a run from a reachable state from Electra, to a state before Gloas.

`capExit`, `capConsolidation` and `capDeposit` cap the churns of every state of the run.

`largest` caps its effective balances.

The churn left at the start is within the caps, and the end is before the far future epoch.

The validators active at the start keep their activation epoch.

Then there are step budgets of the run for each validator, two families, such that:

- leaving: the exits queued at the start, the churn of exits and consolidations, and budgets;
- lost: `lossBudget` of the start;
- gained: the excess of balance at the start, the deposit churn, and the gains after deposits;
- joining: the stake waiting at the start, the growth of old joiners, and new joiners' stake. -/
theorem Run.drift_le_electra (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (room : preset.VALIDATOR_REGISTRY_LIMIT.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat <
      2 ^ 64)
    {capExit capConsolidation capDeposit largest : Nat} {x s : ForkedBeaconState preset}
    (electra : .pectra ≤ x.fork) (reachable : Reachable config checks x)
    (run : Run config checks x s) (early : s.fork < .glamsterdam)
    (churns : ∀ y ∈ run.states, ChurnsBounded config capExit capConsolidation largest y)
    (lefts : LeftBounded capExit capConsolidation x)
    (deposits : ∀ y ∈ run.states, ∀ churn,
      depositChurnLimit config y.state = .ok churn → churn.toNat ≤ capDeposit)
    (finite : getCurrentEpoch s.state < FAR_FUTURE_EPOCH)
    (activations : ∀ (position : Nat) (validator later : Validator),
      x.state.validators.data[position]? = some validator →
        s.state.validators.data[position]? = some later →
        isActiveValidator validator (getCurrentEpoch x.state) = true →
          later.activationEpoch = validator.activationEpoch)
    (votersX votersS : Finset ValidatorIndex)
    (voting : ∀ i ∈ votersS, activeAt s.state (getPreviousEpoch s.state) i.toNat = true ∨
      activeAt s.state (getCurrentEpoch s.state) i.toNat = true) :
    ∃ budgetsLeaving budgetsLost : Nat → List (BalanceFlow → Nat),
      (∀ j, run.Budgets j (budgetsLeaving j)) ∧ (∀ j, run.Budgets j (budgetsLost j)) ∧
      Weighing.drift (Weighing.ofState x.state votersX) (Weighing.ofState s.state votersS) ≤
        2 * ((((List.range x.state.validators.data.size).filter fun position =>
              (x.state.validators.data[position]?).any fun validator =>
                isActiveValidator validator (getCurrentEpoch x.state) &&
                  decide (validator.exitEpoch ≤ getCurrentEpoch s.state)).map
              (effectiveAt x.state)).sum +
            ((getCurrentEpoch s.state).toNat + 1 - firstExitEpoch preset x.state) *
              (capExit + capConsolidation) +
            ∑ j ∈ leavingExits x.state s.state,
              ((effectiveAt x.state j - balanceAt x.state j) +
                (BalanceFlow.all.map fun flow => ((budgetsLeaving j).map (· flow)).sum).sum +
                (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1))) +
          2 * lossBudget x.state budgetsLost +
          3 * (excessStake x.state + forkedDepositCarry x +
            ((getCurrentEpoch s.state).toNat - (getCurrentEpoch x.state).toNat) * capDeposit +
            ∑ j ∈ activePositions x.state, run.gainsAfterDeposit j) +
          3 * (pendingActivationStake x.state +
            ∑ j ∈ (Finset.range s.state.validators.data.size).filter (fun j =>
                joinsAt x.state s.state j = true ∧ j < x.state.validators.data.size),
              (effectiveAt s.state j - effectiveAt x.state j) +
            ∑ j ∈ (Finset.range s.state.validators.data.size).filter (fun j =>
                joinsAt x.state s.state j = true ∧ ¬ j < x.state.validators.data.size),
              effectiveAt s.state j) +
          3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have ready := run.ledgerReady room reachable early
  have withinX := (ready x (Run.start_mem_states run)).within
  have withinS := (ready s (Run.end_mem_states run)).within
  have small := (ready s (Run.end_mem_states run)).small
  have transitions := Run.epochTransitions_eq electra run
  have epochs : getCurrentEpoch x.state ≤ getCurrentEpoch s.state :=
    UInt64.le_iff_toNat_le.mpr (by omega)
  obtain ⟨budgetsLeaving, okLeaving, leaving⟩ := run.leavingStake_le_budgets caps increment
    electra reachable ready churns lefts epochs finite activations
  obtain ⟨budgetsLost, okLost, lostAll⟩ := run.lostStake_le_budgets caps increment room reachable
    early
  refine ⟨budgetsLeaving, budgetsLost, okLeaving, okLost, ?_⟩
  have lost := lostAll s (Run.end_mem_states run)
  have gained := run.gainedVoters_le electra reachable ready votersX votersS voting
  have charged := Run.depositsCharged_le electra run small deposits
  have joining := Run.joiningStakePrev_le electra run small epochs
  simp only [effectiveBalanceAtPosition_eq] at joining
  have joining' : joiningStakePrev x.state s.state ≤ pendingActivationStake x.state +
      ∑ j ∈ (Finset.range s.state.validators.data.size).filter (fun j =>
          joinsAt x.state s.state j = true ∧ j < x.state.validators.data.size),
        (effectiveAt s.state j - effectiveAt x.state j) +
      ∑ j ∈ (Finset.range s.state.validators.data.size).filter (fun j =>
          joinsAt x.state s.state j = true ∧ ¬ j < x.state.validators.data.size),
        effectiveAt s.state j := joining
  have drift := drift_ofState_le_gained withinX withinS votersX votersS voting
  have carry := Nat.zero_le (forkedDepositCarry s)
  refine drift.trans ?_
  have chargedLe : run.depositsCharged ≤ forkedDepositCarry x +
      ((getCurrentEpoch s.state).toNat - (getCurrentEpoch x.state).toNat) * capDeposit := by
    have count : (getCurrentEpoch s.state).toNat - (getCurrentEpoch x.state).toNat =
        run.epochTransitions := by omega
    rw [count]
    omega
  have := Nat.mul_le_mul_left 2 leaving
  have := Nat.mul_le_mul_left 2 lost
  have gainedLe : ∑ v ∈ (Weighing.ofState x.state votersX).active ∩
        (Weighing.ofState s.state votersS).voters,
      ((Weighing.ofState s.state votersS).stake v - (Weighing.ofState x.state votersX).stake v) ≤
      excessStake x.state + forkedDepositCarry x +
        ((getCurrentEpoch s.state).toNat - (getCurrentEpoch x.state).toNat) * capDeposit +
        ∑ j ∈ activePositions x.state, run.gainsAfterDeposit j := by
    omega
  have := Nat.mul_le_mul_left 3 gainedLe
  have := Nat.mul_le_mul_left 3 joining'
  omega

end EthLib.Consensus
