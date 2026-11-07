module

public import EthLib.Consensus.Proofs.Containers.State
public import EthLib.Consensus.Proofs.Transition.ChurnWindows
public import EthLib.Consensus.Proofs.Transition.CommonState
public import EthLib.Consensus.Proofs.Transition.FfgRefinement

/-!
# Proofs: accountable safety before Electra, from a state two histories share

`FfgRefinement.accountable_safety` measures slashable stake in a reference weighing.

It loses twice a bound on the drift of each weighing between the two finalized epochs.

Here the reference is the weighing of a state `x` that both histories share.

Each weighing is that of a later state `s` of one history, before Electra.

The drift then splits into five terms, each a sum over the registry:

```text
  drift ≤ 2 * leavingStake x s + 2 * lostStake x s + 3 * deficit x + 3 * joiningStakePrev x s
            + 3 * EFFECTIVE_BALANCE_INCREMENT
```

- `leavingStake`: validators active at `x` and not at `s`, at their stake at `x`.
  Churn bounds it, through the activation and exit cohorts.
- `lostStake`: what validators active at `x` lose in effective balance.
  Penalties bound it; the inactivity leak dominates.
- `deficit`: the room below `MAX_EFFECTIVE_BALANCE` of validators active at `x`.
  The cap on effective balances before Electra bounds their gains by it.
- `joiningStakePrev`: voters at `s` not active at `x`, at their stake at `s`.
  Churn bounds it, through the activation cohorts.
- one increment: the floor of the balances that the beacon chain weighs.

`accountable_safety_preElectra` assembles them.

The churn bounds on `leavingStake` and `joiningStakePrev`, and the cap, are proved.

The bound on `lostStake` and the facts that place each weighing call are hypotheses.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {fork fork' : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- The effective-balance loss of the validators active at `x`, by the time of a later state. -/
def lostStake (x : BeaconState preset fork) (s : BeaconState preset fork') : ℕ :=
  (((List.range x.validators.data.size).filter fun j => activeAt x (getCurrentEpoch x) j).map
    fun j => effectiveAt x j - effectiveAt s j).sum

/-- The room below `MAX_EFFECTIVE_BALANCE` of the validators active at `x`. -/
def deficit (x : BeaconState preset fork) : ℕ :=
  (((List.range x.validators.data.size).filter fun j => activeAt x (getCurrentEpoch x) j).map
    fun j => preset.MAX_EFFECTIVE_BALANCE.toNat - effectiveAt x j).sum

/-! ## From registry sums to sums over sets of indices -/

theorem list_sum_filter_range (n : ℕ) (p : ℕ → Bool) (g : ℕ → ℕ) :
    (((List.range n).filter p).map g).sum = ∑ j ∈ (Finset.range n).filter (p · = true), g j := by
  rw [Finset.sum_filter]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    simp only [List.range_succ, List.filter_append, List.map_append, List.sum_append]
    cases h : p n <;> simp [h]

theorem effectiveBalanceAt_eq (state : BeaconState preset fork) (index : ValidatorIndex) :
    effectiveBalanceAt state index = effectiveAt state index.toNat := by
  unfold effectiveBalanceAt effectiveAt
  cases state.validators.data[index.toNat]? <;> rfl

theorem sum_toNat (A : Finset ValidatorIndex) (g : ℕ → ℕ) :
    ∑ i ∈ A, g i.toNat = ∑ j ∈ A.image UInt64.toNat, g j :=
  (Finset.sum_image fun _ _ _ _ h => UInt64.toNat_inj.mp h).symm

theorem activeAt_lt {state : BeaconState preset fork} {epoch : Epoch} {j : ℕ}
    (active : activeAt state epoch j = true) : j < state.validators.data.size := by
  unfold activeAt at active
  cases found : state.validators.data[j]? with
  | none => simp [found] at active
  | some _ => exact (Array.getElem?_eq_some_iff.mp found).1

theorem mem_active_iff {state : BeaconState preset fork} (within : state.RegistryWithinLimit)
    {epoch : Epoch} {index : ValidatorIndex} :
    index ∈ getActiveValidatorIndices state epoch ↔ activeAt state epoch index.toNat = true := by
  rw [mem_getActiveValidatorIndices within]
  unfold activeAt
  cases state.validators.data[index.toNat]? <;> simp

/-- The active indices of a state, as positions of its registry. -/
theorem image_active {state : BeaconState preset fork} (within : state.RegistryWithinLimit)
    (epoch : Epoch) :
    (getActiveValidatorIndices state epoch).toFinset.image UInt64.toNat =
      (Finset.range state.validators.data.size).filter (activeAt state epoch · = true) := by
  ext j
  simp only [Finset.mem_image, List.mem_toFinset, Finset.mem_filter, Finset.mem_range,
    mem_active_iff within]
  constructor
  · rintro ⟨i, active, rfl⟩
    exact ⟨activeAt_lt active, active⟩
  · rintro ⟨lt, active⟩
    exact ⟨j.toUInt64, by rwa [toNat_toUInt64_of_lt within lt], toNat_toUInt64_of_lt within lt⟩

/-- A sum over the active indices of a state is the sum over the active positions. -/
theorem sum_active {state : BeaconState preset fork} (within : state.RegistryWithinLimit)
    (epoch : Epoch) (g : ℕ → ℕ) :
    ∑ i ∈ (getActiveValidatorIndices state epoch).toFinset, g i.toNat =
      (((List.range state.validators.data.size).filter (activeAt state epoch)).map g).sum := by
  rw [sum_toNat, image_active within, list_sum_filter_range]

/-! ## The five terms of the drift -/

section Terms

variable {x : BeaconState preset fork} {s : BeaconState preset fork'}
  (withinX : x.RegistryWithinLimit) (withinS : s.RegistryWithinLimit)
  (votersX votersS : Finset ValidatorIndex)

include withinX withinS in
/-- The reference stake of the validators that leave is the leaving stake. -/
theorem exited_le :
    stake (Weighing.ofState x votersX).stake
        ((Weighing.ofState x votersX).active \ (Weighing.ofState s votersS).active) ≤
      leavingStake x s := by
  simp only [Weighing.ofState, stake]
  simp only [effectiveBalanceAt_eq]
  rw [sum_toNat, leavingStake, list_sum_filter_range]
  refine Finset.sum_le_sum_of_subset fun j hj => ?_
  simp only [Finset.mem_image, Finset.mem_sdiff, List.mem_toFinset, mem_active_iff withinX,
    mem_active_iff withinS] at hj
  obtain ⟨i, ⟨active, notActive⟩, rfl⟩ := hj
  simp [activeAt_lt active, active, notActive]

include withinX in
/-- The loss term of the drift is at most the lost stake. -/
theorem lost_le :
    ∑ v ∈ (Weighing.ofState x votersX).active ∩ (Weighing.ofState s votersS).active,
        ((Weighing.ofState x votersX).stake v - (Weighing.ofState s votersS).stake v) ≤
      lostStake x s := by
  refine (Finset.sum_le_sum_of_subset Finset.inter_subset_left).trans (le_of_eq ?_)
  simp only [Weighing.ofState, effectiveBalanceAt_eq]
  exact sum_active withinX _ fun j => effectiveAt x j - effectiveAt s j

include withinX in
/-- Before Electra, the validators active at `x` gain at most their room below the cap. -/
theorem gained_le (capped : EffectiveBalancesCapped s) (before : fork' < .pectra) :
    ∑ v ∈ (Weighing.ofState x votersX).active ∩ (Weighing.ofState s votersS).voters,
        ((Weighing.ofState s votersS).stake v - (Weighing.ofState x votersX).stake v) ≤
      deficit (preset := preset) x := by
  refine (Finset.sum_le_sum_of_subset Finset.inter_subset_left).trans ?_
  simp only [Weighing.ofState, effectiveBalanceAt_eq]
  rw [deficit, ← sum_active withinX]
  refine Finset.sum_le_sum fun i _ => ?_
  have := effectiveAt_le_max capped before i.toNat
  omega

include withinX in
/-- Voters at `s` that were not active at `x` hold at most the entering stake. -/
theorem entered_le
    (voting : ∀ i ∈ votersS, activeAt s (getPreviousEpoch s) i.toNat = true ∨
      activeAt s (getCurrentEpoch s) i.toNat = true) :
    stake (Weighing.ofState s votersS).stake
        ((Weighing.ofState s votersS).voters \ (Weighing.ofState x votersX).active) ≤
      joiningStakePrev x s := by
  simp only [Weighing.ofState, stake, effectiveBalanceAt_eq]
  rw [sum_toNat, joiningStakePrev, list_sum_filter_range]
  refine Finset.sum_le_sum_of_subset fun j hj => ?_
  simp only [Finset.mem_image, Finset.mem_sdiff, List.mem_toFinset, mem_active_iff withinX] at hj
  obtain ⟨i, ⟨voter, notActive⟩, rfl⟩ := hj
  have lt : i.toNat < s.validators.data.size := by
    rcases voting i voter with h | h <;> exact activeAt_lt h
  simp only [Finset.mem_filter, Finset.mem_range, lt, true_and, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true']
  exact ⟨voting i voter, by simpa using notActive⟩

include withinX withinS in
/-- The drift from the weighing of `x` to a weighing of `s`, before Electra, term by term. -/
theorem drift_ofState_le (capped : EffectiveBalancesCapped s) (before : fork' < .pectra)
    (voting : ∀ i ∈ votersS, activeAt s (getPreviousEpoch s) i.toNat = true ∨
      activeAt s (getCurrentEpoch s) i.toNat = true) :
    Weighing.drift (Weighing.ofState x votersX) (Weighing.ofState s votersS) ≤
      2 * leavingStake x s + 2 * lostStake x s + 3 * deficit (preset := preset) x +
        3 * joiningStakePrev x s + 3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  have e₁ := exited_le withinX withinS votersX votersS
  have e₂ := lost_le (s := s) withinX votersX votersS
  have e₃ := gained_le withinX votersX votersS capped before
  have e₄ := entered_le (x := x) withinX votersX votersS voting
  unfold Weighing.drift
  have floor : (Weighing.ofState s votersS).floor = preset.EFFECTIVE_BALANCE_INCREMENT.toNat :=
    rfl
  omega

end Terms

/-! ## Accountable safety -/

open scoped Classical in
/-- Accountable safety before Electra, measured in a state that both histories share.

`X` is a state of both histories after a common start: its run, then each history's own run.

Take two finalized checkpoints of the histories whose blocks conflict.

The hypothesis `placed` is for L5.

It says that each weighing call with a target between the two finalized epochs weighs a state `s`.

That state `s` is on one history, after `X` in slot and before Electra.

Its voters were active in the previous or the current epoch of `s`.

Its epoch is at most `n` after that of `X`, and `K` bounds its churn cap.

`lost` bounds the loss from `X` to every such state.

The churn windows of L1 bound the leaving and the joining stake.

Then, measured at `X`, the validators active at `X` hold at most the sum of:

- three times the stake of those that signed slashable attestation data;
- twice the drift bound.

Otherwise there is hash evidence. -/
theorem FfgRefinement.accountable_safety_preElectra {β : Type*} [Preorder β]
    (R : FfgRefinement β) (caps : EffectiveBalanceCaps preset)
    {start left right : ForkedBeaconState preset}
    (X : CommonState config checks start left right)
    (reachable : Reachable config checks X.common) (early : X.common.fork < .pectra)
    {c₁ c₂ : Checkpoint} (h₁ : c₁ ∈ R.finalized) (h₂ : c₂ ∈ R.finalized)
    (conflicting : Conflicting (R.block c₁) (R.block c₂)) {n K L : ℕ}
    (placed : ∀ r ∈ R.records, min c₁.epoch.toNat c₂.epoch.toNat ≤ r.target.epoch.toNat →
      r.target.epoch.toNat ≤ max c₁.epoch.toNat c₂.epoch.toNat →
      ∃ (s : ForkedBeaconState preset) (voters : Finset ValidatorIndex),
        (s ∈ X.leftRun.states ∨ s ∈ X.rightRun.states) ∧
        X.common.state.slot.toNat < s.state.slot.toNat ∧ s.fork < .pectra ∧
        (getCurrentEpoch s.state).toNat < 2 ^ 64 - 1 ∧
        (getCurrentEpoch s.state).toNat ≤ (getCurrentEpoch X.common.state).toNat + n ∧
        max 1 (churnCap config s.state.validators.data.size) ≤ K ∧
        r.weighing = Weighing.ofState s.state voters ∧
        ∀ i ∈ voters, activeAt s.state (getPreviousEpoch s.state) i.toNat = true ∨
          activeAt s.state (getCurrentEpoch s.state) i.toNat = true)
    (lost : ∀ s, Reaches config checks X.common s → s.fork < .pectra →
      lostStake X.common.state s.state ≤ L) :
    let ω₀ := Weighing.ofState X.common.state
      (getActiveValidatorIndices X.common.state (getCurrentEpoch X.common.state)).toFinset
    stake ω₀.stake ω₀.active ≤
      3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2, (i, data1) ∈ R.signed ∧
        (i, data2) ∈ R.signed ∧ isSlashableAttestationData data1 data2 = true} +
        2 * (2 * (n * K * preset.MAX_EFFECTIVE_BALANCE.toNat) + 2 * L +
          3 * deficit (preset := preset) X.common.state +
          3 * ((n + 1) * K * preset.MAX_EFFECTIVE_BALANCE.toNat) +
          3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∨
      R.evidence := by
  intro ω₀
  refine R.accountable_safety h₁ h₂ conflicting ω₀ fun r hr lo hi => ?_
  obtain ⟨s, voters, member, later, before, finite, epochs, cap, weighing, voting⟩ :=
    placed r hr lo hi
  obtain ⟨-, chain⟩ := X.reaches_of_slot_lt member later
  have withinX := BeaconState.registryWithinLimit_of_lt
    (Nat.lt_of_lt_of_le early (by decide)) X.common.state
  have withinS := BeaconState.registryWithinLimit_of_lt
    (Nat.lt_of_lt_of_le before (by decide)) s.state
  have capped := Reachable.effectiveBalancesCapped caps (ReachableFrom.reaches reachable chain)
  have drift := drift_ofState_le withinX withinS
    (getActiveValidatorIndices X.common.state (getCurrentEpoch X.common.state)).toFinset voters
    capped before voting
  have leaving := chain.leavingStake_le caps reachable before finite
  have window : ((getCurrentEpoch s.state).toNat - (getCurrentEpoch X.common.state).toNat) *
      max 1 (churnCap config s.state.validators.data.size) *
        preset.MAX_EFFECTIVE_BALANCE.toNat ≤ n * K * preset.MAX_EFFECTIVE_BALANCE.toNat :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) cap)
  rw [weighing]
  have := lost s chain before
  have joining := chain.joiningStakePrev_le_add caps reachable before finite
  have joinWindow : (((getCurrentEpoch s.state).toNat - (getCurrentEpoch X.common.state).toNat) *
      churnCap config s.state.validators.data.size +
        max 1 (churnCap config s.state.validators.data.size)) *
        preset.MAX_EFFECTIVE_BALANCE.toNat ≤ (n + 1) * K * preset.MAX_EFFECTIVE_BALANCE.toNat := by
    refine Nat.mul_le_mul_right _ ?_
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add (Nat.mul_le_mul (by omega) ((le_max_right _ _).trans cap)) cap
  refine drift.trans ?_
  omega

end EthLib.Consensus
