module

public import EthLib.Consensus.Proofs.Transition.EffectiveBalanceCeiling
public import EthLib.Consensus.Proofs.Transition.EffectiveBalanceFloor

/-!
# Proofs: how far an effective balance drifts along a run

Along a run from `x` to `s`, an effective balance moves with the balance, and lags it.

It falls below its value at `x` by at most three amounts.

- The slack at `x`: how far the effective balance at `x` is above the balance at `x`.
- The drop: how far the balance falls below its value at `x`, at the worst state of the run.
- The rounding: less than one increment, since an update rounds the balance down.

It rises above its value at `x` by at most the rise.

The rise is how far the balance climbs above that value, at the best state of the run.

The slack and the drop are explicit, so a bound on the drop by penalties and withdrawals plugs in.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The largest value of a function on the states of a run, and zero for no state. -/
def Run.largest {start after : ForkedBeaconState preset} (run : Run config checks start after)
    (value : ForkedBeaconState preset → Nat) : Nat :=
  run.states.foldr (fun state best => max (value state) best) 0

theorem Run.le_largest {start after : ForkedBeaconState preset}
    (run : Run config checks start after) (value : ForkedBeaconState preset → Nat)
    {state : ForkedBeaconState preset} (member : state ∈ run.states) :
    value state ≤ run.largest value := by
  unfold Run.largest
  generalize run.states = states at member ⊢
  induction states with
  | nil => exact absurd member List.not_mem_nil
  | cons first rest more =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp member with rfl | member
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (more member) (Nat.le_max_right _ _)

/-- The drop of a balance along a run: how far it falls below its value at the start.

It is the largest fall at a state of the run, and zero if it never falls. -/
def Run.balanceDrop {start after : ForkedBeaconState preset} (run : Run config checks start after)
    (position : Nat) : Nat :=
  run.largest fun state => balanceAt start.state position - balanceAt state.state position

/-- The rise of a balance along a run, above a reference.

The reference may be the effective balance at the start.

It is the largest excess at a state of the run, and zero if there is none. -/
def Run.balanceRise {start after : ForkedBeaconState preset} (run : Run config checks start after)
    (position reference : Nat) : Nat :=
  run.largest fun state => balanceAt state.state position - reference

/-- Along a run from a reachable state, an effective balance falls by at most three amounts.

They are the slack at the start, the drop of the balance, and less than one increment.

The validator has an activation epoch at the start, as every active one does.

The increment must be positive, and from Gloas the registry at the end below `2^64`. -/
theorem Run.effectiveBalance_fall_le (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {start after : ForkedBeaconState preset} (reachable : Reachable config checks start)
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    {position : Nat} {validator : Validator}
    (found : start.state.validators.data[position]? = some validator)
    (set : validator.activationEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ later, after.state.validators.data[position]? = some later ∧
      validator.effectiveBalance.toNat - later.effectiveBalance.toNat ≤
        (validator.effectiveBalance.toNat - balanceAt start.state position) +
          run.balanceDrop position + (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) := by
  -- Every balance of the run, rounded down, is at least this bound.
  let bound := validator.effectiveBalance.toNat -
    ((validator.effectiveBalance.toNat - balanceAt start.state position) +
      run.balanceDrop position + (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1))
  have floors : ∀ state ∈ run.states, bound ≤ balanceFloorAt state.state position := by
    intro state member
    have dropped := run.le_largest
      (fun state => balanceAt start.state position - balanceAt state.state position) member
    -- The floor rounds the balance down by less than one increment.
    have rounding : ∀ balance : Nat, balance - (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1) ≤
        balance - balance % preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
      intro balance
      have := Nat.mod_lt balance increment
      omega
    have floorAt : balanceAt state.state position - (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)
        ≤ balanceFloorAt state.state position := by
      unfold balanceFloorAt balanceAt
      cases state.state.balances.data[position]? with
      | none => simp
      | some balance => simpa using rounding balance.toNat
    have dropEq : run.balanceDrop position = run.largest
        (fun state => balanceAt start.state position - balanceAt state.state position) := rfl
    omega
  obtain ⟨later, laterFound, _, laterBound⟩ := run.effectiveBalance_floor caps reachable small
    position validator found set bound (Nat.sub_le _ _) floors
  exact ⟨later, laterFound, by omega⟩

/-- Along a run, an effective balance rises above its value at the start by at most the rise.

The rise is how far the balance climbs above that value, at the best state of the run.

From Gloas the registry at the end must be below `2^64`. -/
theorem Run.effectiveBalance_rise_le {start after : ForkedBeaconState preset}
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    {position : Nat} {validator : Validator}
    (found : start.state.validators.data[position]? = some validator) :
    ∃ later, after.state.validators.data[position]? = some later ∧
      later.effectiveBalance.toNat - validator.effectiveBalance.toNat ≤
        run.balanceRise position validator.effectiveBalance.toNat := by
  let bound := validator.effectiveBalance.toNat +
    run.balanceRise position validator.effectiveBalance.toNat
  have balances : ∀ state ∈ run.states, balanceAt state.state position ≤ bound := by
    intro state member
    have risen := run.le_largest
      (fun state => balanceAt state.state position - validator.effectiveBalance.toNat) member
    have riseEq : run.balanceRise position validator.effectiveBalance.toNat = run.largest
        (fun state => balanceAt state.state position - validator.effectiveBalance.toNat) := rfl
    omega
  obtain ⟨later, laterFound, laterBound⟩ := run.effectiveBalance_ceiling small position
    validator found bound (Nat.le_add_right _ _) balances
  exact ⟨later, laterFound, by omega⟩

end EthLib.Consensus
