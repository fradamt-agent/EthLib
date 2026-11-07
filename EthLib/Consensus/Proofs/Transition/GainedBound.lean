module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import EthLib.Consensus.Proofs.Transition.BlockLedger
public import EthLib.Consensus.Proofs.Transition.ChurnWindows
public import EthLib.Consensus.Proofs.Transition.EffectiveBalanceCeiling

/-!
# Proofs: what a balance can gain along a run

The rise of a balance along a run sums, step by step, how much the step raised it.

Every balance of the run is at most the balance at the start plus that rise.

The ledger of each step bounds its rise by what the step credits.

From Electra an upgrade keeps the balances, and a slot or a block has a ledger.

Before Gloas the registry is within its limit by its type, and from Gloas that is a premise.

The room in 64 bits for the new validators of the pending deposits is a premise at every fork.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- `balanceAt` is the balance that ledgers read. -/
theorem balanceAt_eq_balanceNat {fork : Base.Fork} (state : BeaconState preset fork)
    (index : Nat) : balanceAt state index = balanceNat state index := rfl

/-! ## The ledger of each kind of step -/

/-- The epoch at the end of a slot, if it is due, has a ledger.

From Altair it needs the registry within its limit and one balance for each validator.

It also needs room in 64 bits for the new validators of the pending deposits. -/
theorem epochIfLast_ledger {fork : Base.Fork} {state after : BeaconState preset fork}
    {next : Slot} (computed : epochIfLast config checks next state = .ok after)
    (within : state.RegistryWithinLimit) (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ changes, BalanceLedger state after changes := by
  unfold epochIfLast at computed
  split at computed
  · by_cases altair : .altair ≤ fork
    · unfold processEpoch at computed
      simp only [altair, ↓reduceDIte] at computed
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, ledger⟩ :=
        processEpochAltair_ledger within holds room computed
      exact ⟨_, ledger⟩
    · obtain ⟨_, _, _, _, _, _, ledger⟩ :=
        processEpoch_ledger_of_lt_altair (Nat.lt_of_not_le altair) computed
      exact ⟨_, ledger⟩
  · cases computed
    exact ⟨_, BalanceLedger.refl state⟩

/-- A slot has a ledger: that of its epoch, if the slot ends one.

The premises are those of `epochIfLast_ledger`. -/
theorem advanceSlot_ledger {fork : Base.Fork} {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after)
    (within : state.RegistryWithinLimit) (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ changes, BalanceLedger state after changes := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  obtain ⟨changes, ledger⟩ := epochIfLast_ledger epochedOk within holds room
  exact ⟨changes, fun i => ledger i⟩

/-- Every step of a chain from Electra raises each balance by at most what a ledger credits it.

An upgrade from Electra keeps the balances.

A slot needs the premises of `epochIfLast_ledger`, and a block one balance for each validator.

Before Gloas the registry is within its limit by its type.

From Gloas nothing bounds the registry, so that is a premise.

The room in 64 bits for the new validators of the pending deposits is a premise at every fork. -/
theorem Step.balanceAt_le_credited {pre post : ForkedBeaconState preset}
    (step : Step config checks pre post) (electra : .pectra ≤ pre.fork)
    (within : pre.state.RegistryWithinLimit) (holds : BalancesMatch pre.state)
    (room : pre.state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ changes : Nat → List BalanceChange, ∀ i,
      balanceAt post.state i ≤ balanceAt pre.state i + BalanceChange.creditedAll (changes i) := by
  cases step with
  | slot _ computed =>
    obtain ⟨changes, ledger⟩ := advanceSlot_ledger computed within holds room
    exact ⟨changes, ledger.le_credited⟩
  | block _ _ _ _ computed =>
    obtain ⟨_, _, _, _, _, _, _, ledger, _⟩ :=
      processBlock_ledger (applySignedBlock_ok computed).2.1 holds
    exact ⟨_, ledger.le_credited⟩
  | upgrade due computed =>
    rename_i upgraded
    obtain ⟨fork, state⟩ := pre
    refine ⟨fun _ => [], fun i => ?_⟩
    simp only [BalanceChange.creditedAll, List.map_nil, List.sum_nil, Nat.add_zero]
    -- From Electra each upgrade keeps the balances.
    have same : upgraded.val.state.balances.data = state.balances.data := by
      cases fork
      all_goals dsimp only at electra
      all_goals first
        | exact absurd electra (by decide)
        | simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
            throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
      · obtain ⟨_, upgradedOk, rfl⟩ := computed
        exact (upgradeToFulu_spec upgradedOk).2.1
      · obtain ⟨_, upgradedOk, rfl⟩ := computed
        exact (upgradeToGloas_spec upgradedOk).2.1
      · obtain ⟨_, upgradedOk, rfl⟩ := computed
        obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgradedOk
        exact (upgradeHezeFields_lists _).2.1
    simp [balanceAt, same]

namespace Run

variable {start : ForkedBeaconState preset}

/-- How much a run credits the balance at a position: the sum of the rise of each step.

A step that lowers the balance counts zero. -/
def credited (index : Nat) : {after : ForkedBeaconState preset} → Run config checks start after → Nat
  | _, .nil => 0
  | after, .snoc (middle := middle) run _ =>
    run.credited index + (balanceAt after.state index - balanceAt middle.state index)

/-- Every balance of a run is at most the balance at the start plus what the run credits. -/
theorem balanceAt_le_credited (index : Nat) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      ∀ state ∈ run.states,
        balanceAt state.state index ≤ balanceAt start.state index + run.credited index
  | _, .nil, state, member => by
    rw [List.mem_singleton.mp member]
    simp [credited]
  | after, .snoc (middle := middle) run _, state, member => by
    have earlier := balanceAt_le_credited index run
    have here := earlier middle (end_mem_states run)
    rcases List.mem_append.mp member with member | member
    · have := earlier state member
      simp only [credited]
      omega
    · rw [List.mem_singleton.mp member]
      simp only [credited]
      omega

/-- An effective balance at the end of a run is at most the larger of the effective balance and
the balance at the start, plus what the run credits the balance.

It is for a position that holds a validator at the start.

It needs a registry of fewer than `2^64` validators at the end, which holds before Gloas. -/
theorem effectiveAt_le_credited {after : ForkedBeaconState preset}
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    (index : Nat) (present : index < start.state.validators.data.size) :
    effectiveAt after.state index ≤
      max (effectiveAt start.state index) (balanceAt start.state index) + run.credited index := by
  obtain ⟨later, found, bound⟩ := run.effectiveBalance_ceiling small index
    start.state.validators.data[index] (Array.getElem?_eq_getElem present)
    (max (effectiveAt start.state index) (balanceAt start.state index) + run.credited index)
    (by simp [effectiveAt, Array.getElem?_eq_getElem present]; omega)
    (fun state member => by have := balanceAt_le_credited index run state member; omega)
  simpa [effectiveAt, found] using bound

/-- What the validators at some positions gain in effective balance along a run.

It is at most what their balance exceeds their effective balance at the start, plus what the run
credits them.

Each position must hold a validator at the start.

It needs a registry of fewer than `2^64` validators at the end, which holds before Gloas. -/
theorem gained_le {after : ForkedBeaconState preset} (run : Run config checks start after)
    (small : after.state.validators.data.size < 2 ^ 64) (positions : Finset Nat)
    (present : ∀ index ∈ positions, index < start.state.validators.data.size) :
    ∑ index ∈ positions, (effectiveAt after.state index - effectiveAt start.state index) ≤
      ∑ index ∈ positions,
        (balanceAt start.state index - effectiveAt start.state index + run.credited index) := by
  apply Finset.sum_le_sum
  intro index member
  have := run.effectiveAt_le_credited small index (present index member)
  omega

end Run

end EthLib.Consensus
