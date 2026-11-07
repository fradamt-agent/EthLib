module

public import EthLib.Consensus.Proofs.Transition.EffectiveBalanceCap
public import EthLib.Consensus.Proofs.Transition.InactivityScores
public import EthLib.Consensus.Proofs.Transition.RewardDeltas

/-!
# Proofs: the size of an inactivity penalty, from Altair

From Altair the inactivity penalty of a validator in an epoch is a product over a divisor.

The product is its effective balance times its inactivity score.

The divisor is `INACTIVITY_SCORE_BIAS` times the inactivity quotient of the fork.

Along a chain the score grows by at most the bias per epoch.

The effective balance stays under its cap.

So the penalty at an epoch `k` epochs after a state `x` is bounded by a closed form.

It is the cap times the score at `x` plus `k` times the bias, over the divisor.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- The inactivity penalty of a validator is at most its effective balance times its score.

That product is divided by the score bias times the inactivity quotient. -/
theorem getInactivityPenaltyDeltas_le {state : BeaconState preset fork} (altair : .altair ≤ fork)
    {rewards penalties : Array Gwei} (within : state.RegistryWithinLimit)
    (computed : getInactivityPenaltyDeltas config state = .ok (rewards, penalties))
    {position : Nat} (inside : position < state.validators.data.size) :
    (penalties.getD position 0).toNat ≤
      state.validators.data[position].effectiveBalance.toNat *
        inactivityScoreAt state position /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  obtain ⟨matching, _, each⟩ := getInactivityPenaltyDeltas_getD_of_altair altair within computed
  obtain ⟨eligible, _, _, none, some⟩ := each position inside
  by_cases paid : eligible = true ∧ position.toUInt64 ∉ matching
  · obtain ⟨score, scoreRead, amount⟩ := some paid.1 paid.2
    rw [amount]
    simp [inactivityScoreAt, altair, scoreRead]
  · have zero : penalties.getD position 0 = 0 := by
      apply none
      cases eligible <;> simp_all
    rw [zero]
    exact Nat.zero_le _

/-- Along a chain, the inactivity penalty at a later epoch has a closed bound.

The state `x` starts the chain, and `state` is where the penalty is computed.

The validator is at its position in both.

The bound is its largest effective balance times its score at `x` plus the bias for each epoch.

That product is divided by the score bias times the inactivity quotient. -/
theorem Reaches.inactivityPenalty_le {start : ForkedBeaconState preset}
    {state : BeaconState preset fork} (altair : .altair ≤ fork)
    (chain : Reaches config checks start ⟨fork, state⟩)
    (capped : EffectiveBalancesCapped state)
    {rewards penalties : Array Gwei} (within : state.RegistryWithinLimit)
    (computed : getInactivityPenaltyDeltas config state = .ok (rewards, penalties))
    {position : Nat} (inside : position < state.validators.data.size) :
    (penalties.getD position 0).toNat ≤
      (withdrawalMaxEffectiveBalance preset fork state.validators.data[position]).toNat *
        (inactivityScoreAt start.state position + config.INACTIVITY_SCORE_BIAS.toNat *
          ((getCurrentEpoch state).toNat - (getCurrentEpoch start.state).toNat)) /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) := by
  have small : state.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt within (UInt64.toNat_lt _)
  have scores := chain.inactivityScore_le small position
  have cap := UInt64.le_iff_toNat_le.mp (capped _ (Array.getElem_mem inside))
  refine Nat.le_trans (getInactivityPenaltyDeltas_le altair within computed inside) ?_
  exact Nat.div_le_div_right (Nat.mul_le_mul cap scores)

/-- The same bound along a chain from a reachable state, which is then under the cap.

The preset must order its largest effective balances as `EffectiveBalanceCaps` says. -/
theorem Reachable.inactivityPenalty_le (caps : EffectiveBalanceCaps preset)
    {start : ForkedBeaconState preset} {state : BeaconState preset fork}
    (altair : .altair ≤ fork) (reachable : Reachable config checks start)
    (chain : Reaches config checks start ⟨fork, state⟩)
    {rewards penalties : Array Gwei} (within : state.RegistryWithinLimit)
    (computed : getInactivityPenaltyDeltas config state = .ok (rewards, penalties))
    {position : Nat} (inside : position < state.validators.data.size) :
    (penalties.getD position 0).toNat ≤
      (withdrawalMaxEffectiveBalance preset fork state.validators.data[position]).toNat *
        (inactivityScoreAt start.state position + config.INACTIVITY_SCORE_BIAS.toNat *
          ((getCurrentEpoch state).toNat - (getCurrentEpoch start.state).toNat)) /
          (config.INACTIVITY_SCORE_BIAS.toNat *
            (parameters preset fork).INACTIVITY_PENALTY_QUOTIENT.toNat) :=
  chain.inactivityPenalty_le altair
    (Reachable.effectiveBalancesCapped caps (reachable.reaches chain)) within computed inside

end EthLib.Consensus
