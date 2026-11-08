module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import EthLib.Consensus.Proofs.Time
public import EthLib.Consensus.Proofs.Transition.ChurnQueues

/-!
# Proofs: the effective stake that starts to exit, from Electra

From Electra a validator exits through one of two queues of balance, as [EIP-7251] specifies.

An exit spends churn of the queue of exits.

A consolidation spends churn of the queue of consolidations.

Each spends the effective balance of the validator when it starts.

Within one slot or one block, that is its effective balance at the start of the step.

A block changes no effective balance.

An epoch changes them only in its effective-balance updates, after its exits.

The potential of a queue is the churn it has spent, one cap per epoch.

It counts every epoch up to the earliest open one, less the churn left there.

It also counts every epoch before the first one a new exit may take.

Each exit raises the potential of its queue by at least the balance it spends.

So, over a run, the stake that starts to exit up to an epoch is at most the rise in potential.

`Run.exitingStake_le` states it for validators of the first state:

```text
  sum of effectiveBalance(start, i)
    <= (upTo + 1 - firstExitEpoch(start)) * (capExit + capConsolidation)
     + sum of (effectiveBalance(start, i) - chargedBalance(i))
```

The sums run over the validators with no exit epoch at the start, and one up to `upTo` at the end.

`firstExitEpoch(start)` is the current epoch plus one, plus `MAX_SEED_LOOKAHEAD`.

`chargedBalance(i)` is the effective balance that the exit of `i` spent.

The last sum is the effective balance that a validator lost before its exit started.

The churn does not see it.

The caps bound the churns of every state of the run.

Before Gloas, `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` bounds the churn of exits.

The churn of consolidations, and from Gloas that of exits, grows with the total active balance.

A range of exit epochs that starts later is bounded the same way.

There the potential is clamped to the range.

The one exit that crosses into the range from before it may spend churn of earlier epochs.

That costs at most `largest`, a bound on every effective balance, once per queue.

The facts on the registry hold while it has fewer than `2^64` validators.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-! ## The potential of a queue -/

/-- The churn that a queue has spent, in a cap per epoch.

It counts one cap for each epoch up to the earliest open one, less the churn left there.

An earliest open epoch before the first epoch a new request may take counts as that first epoch.

There the queue would open a fresh epoch, so no churn is left from before. -/
def queuePotential (cap first : Nat) (earliestEpoch : Epoch) (churnLeft : Gwei) : Nat :=
  if earliestEpoch.toNat < first then first * cap
  else earliestEpoch.toNat * cap + cap - churnLeft.toNat

/-- The larger of two 64-bit numbers, as a natural number. -/
private theorem toNat_max (a b : UInt64) : (max a b).toNat = max a.toNat b.toNat := by
  rw [UInt64.max_def, Nat.max_def]
  split <;> split <;> rename_i first second
  · rfl
  · exact absurd (UInt64.le_iff_toNat_le.mp first) second
  · exact absurd (UInt64.le_iff_toNat_le.mpr second) first
  · rfl

/-- A request raises the potential of its queue by at least its amount.

The first epoch of the request is `first`, and a cap bounds the churn and the churn left. -/
theorem churnQueue_potential {earliestEpoch firstEpoch perEpochChurn churnLeft amount epoch left :
    UInt64} {cap : Nat} (leftLe : churnLeft.toNat ≤ cap) (churnLe : perEpochChurn.toNat ≤ cap)
    (computed :
      churnQueue earliestEpoch firstEpoch perEpochChurn churnLeft amount = .ok (epoch, left)) :
    left.toNat ≤ cap ∧ firstEpoch ≤ epoch ∧
      amount.toNat + queuePotential cap firstEpoch.toNat earliestEpoch churnLeft ≤
        queuePotential cap firstEpoch.toNat epoch left := by
  obtain ⟨leftAfter, _, _⟩ := churnQueue_cap leftLe churnLe computed
  obtain ⟨placed, spent, _⟩ := churnQueue_spend computed
  have opened := toNat_max earliestEpoch firstEpoch
  have epochNat := UInt64.le_iff_toNat_le.mp placed
  generalize max earliestEpoch firstEpoch = first at placed spent epochNat opened
  have firstNat : firstEpoch.toNat ≤ epoch.toNat := by omega
  refine ⟨leftAfter, UInt64.le_iff_toNat_le.mpr firstNat, ?_⟩
  -- After the request the queue is open at its epoch, no earlier than the first one.
  have notStale : ¬ epoch.toNat < firstEpoch.toNat := Nat.not_lt.mpr firstNat
  simp only [queuePotential, notStale, ↓reduceIte]
  have added := Nat.mul_le_mul_left (epoch.toNat - first.toNat) churnLe
  have whole : first.toNat * cap + (epoch.toNat - first.toNat) * cap = epoch.toNat * cap := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' epochNat]
  by_cases stale : earliestEpoch.toNat < firstEpoch.toNat
  · -- A stale queue opens the first epoch with a fresh churn.
    have isFirst : first.toNat = firstEpoch.toNat := by omega
    have opens : earliestEpoch < first := UInt64.lt_iff_toNat_lt.mpr (by omega)
    simp only [opens, ↓reduceIte, stale] at spent ⊢
    rw [isFirst] at added whole spent
    omega
  · -- An open queue keeps its earliest epoch and the churn left there.
    have isEarliest : first.toNat = earliestEpoch.toNat := by omega
    have notOpens : ¬ earliestEpoch < first := fun lt => by
      have := UInt64.lt_iff_toNat_lt.mp lt
      omega
    simp only [notOpens, ↓reduceIte, stale] at spent ⊢
    rw [isEarliest] at added whole spent
    omega

/-- A later first epoch never lowers the potential, while the churn left is within the cap. -/
theorem queuePotential_mono {cap first first' : Nat} {earliestEpoch : Epoch} {churnLeft : Gwei}
    (leftLe : churnLeft.toNat ≤ cap) (later : first ≤ first') :
    queuePotential cap first earliestEpoch churnLeft ≤
      queuePotential cap first' earliestEpoch churnLeft := by
  unfold queuePotential
  have := Nat.mul_le_mul_right cap later
  split <;> split
  · exact this
  · omega
  · -- The queue becomes stale: its open epoch is before the new first epoch.
    rename_i open_ stale
    have := Nat.mul_le_mul_right cap (Nat.succ_le_of_lt stale)
    rw [Nat.succ_mul] at this
    omega
  · exact Nat.le_refl _

/-- The churn spent on a range of epochs, from `lower` to `upTo`, in caps.

It is the potential clamped to that range.

Once the potential reaches the range, it also counts `largest`, the most that one exit spends.

That covers the one request that may cross into the range: it spends churn from before it.

So it is at most `upTo + 1 - lower` caps, plus `largest`. -/
def windowPotential (cap largest lower upTo potential : Nat) : Nat :=
  min (max potential (lower * cap)) ((upTo + 1) * cap) - lower * cap +
    if lower * cap ≤ potential then largest else 0

/-- A larger potential never spends less on a range. -/
theorem windowPotential_mono {cap largest lower upTo potential potential' : Nat}
    (le : potential ≤ potential') :
    windowPotential cap largest lower upTo potential ≤
      windowPotential cap largest lower upTo potential' := by
  unfold windowPotential
  split <;> split <;> omega

/-- The spend on a range is at most one cap per epoch of the range, plus `largest`. -/
theorem windowPotential_le (cap largest lower upTo potential : Nat) :
    windowPotential cap largest lower upTo potential ≤ (upTo + 1 - lower) * cap + largest := by
  unfold windowPotential
  have : (upTo + 1) * cap - lower * cap ≤ (upTo + 1 - lower) * cap := by
    rw [← Nat.sub_mul]
  have := Nat.min_le_right (max potential (lower * cap)) ((upTo + 1) * cap)
  split <;> omega

/-- A request raises the spend on a range by its amount, if its epoch lies in the range.

The amount must be at most `largest`.

A request that crosses into the range from before it is paid by `largest`. -/
theorem churnQueue_windowPotential {earliestEpoch firstEpoch perEpochChurn churnLeft amount epoch
    left : UInt64} {cap largest : Nat} (leftLe : churnLeft.toNat ≤ cap)
    (churnLe : perEpochChurn.toNat ≤ cap)
    (computed :
      churnQueue earliestEpoch firstEpoch perEpochChurn churnLeft amount = .ok (epoch, left))
    (lower upTo : Nat) (amountLe : amount.toNat ≤ largest) :
    (if lower ≤ epoch.toNat ∧ epoch.toNat ≤ upTo then amount.toNat else 0) +
        windowPotential cap largest lower upTo
          (queuePotential cap firstEpoch.toNat earliestEpoch churnLeft) ≤
      windowPotential cap largest lower upTo (queuePotential cap firstEpoch.toNat epoch left) := by
  obtain ⟨leftAfter, firstLe, rises⟩ := churnQueue_potential leftLe churnLe computed
  have firstNat := UInt64.le_iff_toNat_le.mp firstLe
  have notStale : ¬ epoch.toNat < firstEpoch.toNat := Nat.not_lt.mpr firstNat
  -- After the request the potential lies within the cap of its epoch.
  have after : queuePotential cap firstEpoch.toNat epoch left =
      epoch.toNat * cap + cap - left.toNat := by
    simp only [queuePotential, notStale, ↓reduceIte]
  generalize queuePotential cap firstEpoch.toNat earliestEpoch churnLeft = before at rises ⊢
  rw [after] at rises ⊢
  split
  · rename_i within
    have low := Nat.mul_le_mul_right cap (show lower ≤ epoch.toNat from within.1)
    have high := Nat.mul_le_mul_right cap (show epoch.toNat + 1 ≤ upTo + 1 by omega)
    rw [Nat.succ_mul] at high
    unfold windowPotential
    split <;> split <;> omega
  · simp only [Nat.zero_add]
    exact windowPotential_mono (by omega)

/-! ## The first epoch of a state, and its potentials -/

/-- The first epoch an exit or a consolidation started in a state may take. -/
def firstExitEpoch (preset : Preset) (state : BeaconState preset fork) : Nat :=
  (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat

/-- The churn that both queues of a state have spent on a range of epochs, with a cap for each.
-/
def statePotential (capExit capConsolidation largest lower upTo : Nat)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork) : Nat :=
  windowPotential capExit largest lower upTo (queuePotential capExit (firstExitEpoch preset state)
      (state.earliestExitEpoch electra) (state.exitBalanceToConsume electra)) +
    windowPotential capConsolidation largest lower upTo (queuePotential capConsolidation
      (firstExitEpoch preset state) (state.earliestConsolidationEpoch electra)
      (state.consolidationBalanceToConsume electra))

/-- The churns and the churn left of a state are within the caps.

Every effective balance is at most `largest`. -/
structure ChurnsWithin (config : Config) (capExit capConsolidation largest : Nat)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork) : Prop where
  exitChurn : ∀ churn, exitChurnLimit config state = .ok churn → churn.toNat ≤ capExit
  consolidationChurn : ∀ churn,
    getConsolidationChurnLimit config state = .ok churn → churn.toNat ≤ capConsolidation
  exitLeft : (state.exitBalanceToConsume electra).toNat ≤ capExit
  consolidationLeft : (state.consolidationBalanceToConsume electra).toNat ≤ capConsolidation
  effective : ∀ (position : Nat) (validator : Validator),
    state.validators.data[position]? = some validator → validator.effectiveBalance.toNat ≤ largest

/-- The potentials after a request to the queue of exits. -/
theorem statePotential_exitQueue {capExit capConsolidation largest lower upTo : Nat}
    {electra : .pectra ≤ fork} (epoch : Epoch) (left : Gwei) :
    statePotential capExit capConsolidation largest lower upTo
        ({ state with exitBalanceToConsume := fun _ => left, earliestExitEpoch := fun _ => epoch } :
          BeaconState preset fork) electra =
      windowPotential capExit largest lower upTo
          (queuePotential capExit (firstExitEpoch preset state) epoch left) +
        windowPotential capConsolidation largest lower upTo (queuePotential capConsolidation
          (firstExitEpoch preset state) (state.earliestConsolidationEpoch electra)
          (state.consolidationBalanceToConsume electra)) := rfl

/-- The potentials after a request to the queue of consolidations. -/
theorem statePotential_consolidationQueue {capExit capConsolidation largest lower upTo : Nat}
    {electra : .pectra ≤ fork} (epoch : Epoch) (left : Gwei) :
    statePotential capExit capConsolidation largest lower upTo
        ({ state with
          consolidationBalanceToConsume := fun _ => left
          earliestConsolidationEpoch := fun _ => epoch } : BeaconState preset fork) electra =
      windowPotential capExit largest lower upTo (queuePotential capExit
          (firstExitEpoch preset state) (state.earliestExitEpoch electra)
          (state.exitBalanceToConsume electra)) +
        windowPotential capConsolidation largest lower upTo
          (queuePotential capConsolidation (firstExitEpoch preset state) epoch left) := rfl

/-! ## The validators that start to exit -/

/-- Whether a validator has no exit epoch in one state, and one in a range in another.

The range runs from `lower` to `upTo`, both included. -/
def startsExit (before later : Option Validator) (lower upTo : Nat) : Bool :=
  match before, later with
  | some validator, some later =>
    validator.exitEpoch == FAR_FUTURE_EPOCH && later.exitEpoch != FAR_FUTURE_EPOCH &&
      decide (lower ≤ later.exitEpoch.toNat) && decide (later.exitEpoch.toNat ≤ upTo)
  | _, _ => false

/-- The positions of the validators of a state that start to exit by a later state.

Their exit epochs lie from `lower` to `upTo`, both included. -/
def exitsBetween {fork' : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') (lower upTo : Nat) : Finset Nat :=
  (Finset.range state.validators.data.size).filter fun position =>
    startsExit state.validators.data[position]? after.validators.data[position]? lower upTo

/-- The effective balance at a position of the registry, and zero past its end. -/
def effectiveBalanceAtPosition (state : BeaconState preset fork) (position : Nat) : Nat :=
  match state.validators.data[position]? with
  | some validator => validator.effectiveBalance.toNat
  | none => 0

/-! ## The total active balance within a step -/

/-- Whether each validator of a registry is active in an epoch, in registry order. -/
def activeFlags (state : BeaconState preset fork) (epoch : Epoch) : List Bool :=
  state.validators.data.toList.map (isActiveValidator · epoch)

/-- The effective balances of a registry, in registry order. -/
def effectiveBalances (state : BeaconState preset fork) : List Nat :=
  state.validators.data.toList.map (·.effectiveBalance.toNat)

/-- The positions of the set flags of a list, as indices of 64 bits. -/
private def flagIndices (flags : List Bool) : List ValidatorIndex :=
  flags.zipIdx.filterMap fun (flag, index) => if flag then some index.toUInt64 else none

/-- The marked effective balances, summed in order. -/
private def sumFlags (balances : List Nat) (marks : List Bool) : Nat :=
  (balances.zip marks).foldl (fun sum (balance, mark) => if mark then sum + balance else sum) 0

private theorem getActiveValidatorIndices_eq (state : BeaconState preset fork) (epoch : Epoch) :
    getActiveValidatorIndices state epoch = flagIndices (activeFlags state epoch) := by
  simp only [getActiveValidatorIndices, flagIndices, activeFlags, List.zipIdx_map,
    List.filterMap_map]
  rfl

private theorem sumMarked_eq (validators : Array Validator) (marks : Array Bool) :
    sumMarked validators marks =
      sumFlags (validators.toList.map (·.effectiveBalance.toNat)) marks.toList := by
  simp only [sumMarked, sumFlags, ← Array.foldl_toList, Array.toList_zip, List.zip_map_left,
    List.foldl_map]
  rfl

/-- The total active balance reads only three things of the registry.

They are its size, whether each validator is active, and each effective balance. -/
theorem getTotalActiveBalance_congr {fork' : Base.Fork} {after : BeaconState preset fork'}
    (slot : after.slot = state.slot)
    (size : after.validators.data.size = state.validators.data.size)
    (flags : activeFlags after (getCurrentEpoch state) = activeFlags state (getCurrentEpoch state))
    (balances : effectiveBalances after = effectiveBalances state) :
    getTotalActiveBalance after = getTotalActiveBalance state := by
  have epoch : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  simp only [getTotalActiveBalance, getTotalBalance, getActiveValidatorIndices_eq, epoch, flags,
    sumMarked_eq, size]
  simp only [effectiveBalances] at balances
  rw [balances]

/-- The flags of a list with one clear flag at its end mark the same positions. -/
private theorem flagIndices_append_false (flags : List Bool) :
    flagIndices (flags ++ [false]) = flagIndices flags := by
  unfold flagIndices
  rw [List.zipIdx_append, List.filterMap_append]
  simp

/-- Each position that a list of flags marks is below its length, while that is below `2^64`. -/
private theorem toNat_lt_of_mem_flagIndices {flags : List Bool} (small : flags.length < 2 ^ 64)
    {index : ValidatorIndex} (member : index ∈ flagIndices flags) : index.toNat < flags.length := by
  simp only [flagIndices, List.mem_filterMap, Option.ite_none_right_eq_some, Option.some.injEq,
    Prod.exists] at member
  obtain ⟨_, position, inside, _, rfl⟩ := member
  have below : position < flags.length := by
    have := (List.mem_zipIdx inside).2.1
    omega
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (show position < 2 ^ 64 by omega)]
  exact below

/-- Marking indices keeps the size of the array of marks. -/
private theorem size_foldl_setIfInBounds (indices : List ValidatorIndex) (marks : Array Bool) :
    (indices.foldl (fun marked index => marked.setIfInBounds index.toNat true) marks).size =
      marks.size := by
  induction indices generalizing marks with
  | nil => rfl
  | cons index rest more => simp [more]

/-- Marking indices below a size, in a longer array, marks the same positions. -/
private theorem markIndices_succ {size : Nat} {indices : List ValidatorIndex}
    (inside : ∀ index ∈ indices, index.toNat < size) :
    markIndices (size + 1) indices = (markIndices size indices).push false := by
  unfold markIndices
  rw [show Array.replicate (size + 1) false = (Array.replicate size false).push false from by
    apply Array.ext'
    simp [List.replicate_succ']]
  have sized : (Array.replicate size false).size = size := by simp
  generalize Array.replicate size false = marks at sized
  induction indices generalizing marks with
  | nil => rfl
  | cons index rest more =>
    simp only [List.foldl_cons]
    have below := inside index List.mem_cons_self
    rw [← more (fun i m => inside i (List.mem_cons_of_mem _ m)) _ (by simp [sized])]
    congr 1
    apply Array.ext'
    simp only [Array.toList_setIfInBounds, Array.toList_push]
    rw [List.set_append_left _ _ (by simp; omega)]

/-- A sum of marked balances with one unmarked balance at its end is the same sum. -/
private theorem sumFlags_append {balances : List Nat} {marks : List Bool}
    (lengths : balances.length = marks.length) (balance : Nat) :
    sumFlags (balances ++ [balance]) (marks ++ [false]) = sumFlags balances marks := by
  simp [sumFlags, List.zip_append lengths]

/-- A new validator that is not active in the current epoch leaves the total active balance.

The registry stays below `2^64`. -/
theorem getTotalActiveBalance_push {fork' : Base.Fork} {after : BeaconState preset fork'}
    {validator : Validator} (slot : after.slot = state.slot)
    (pushed : after.validators.data = state.validators.data.push validator)
    (inactive : isActiveValidator validator (getCurrentEpoch state) = false)
    (small : after.validators.data.size < 2 ^ 64) :
    getTotalActiveBalance after = getTotalActiveBalance state := by
  have epoch : getCurrentEpoch after = getCurrentEpoch state := by
    simp only [getCurrentEpoch, slot]
  have flags : activeFlags after (getCurrentEpoch state) =
      activeFlags state (getCurrentEpoch state) ++ [false] := by
    simp [activeFlags, pushed, inactive]
  have sizeEq : after.validators.data.size = state.validators.data.size + 1 := by
    simp [pushed]
  have inside : ∀ index ∈ getActiveValidatorIndices state (getCurrentEpoch state),
      index.toNat < state.validators.data.size := by
    intro index member
    rw [getActiveValidatorIndices_eq] at member
    have := toNat_lt_of_mem_flagIndices (by simp [activeFlags]; omega) member
    simpa [activeFlags] using this
  simp only [getTotalActiveBalance, getTotalBalance, getActiveValidatorIndices_eq, epoch, flags,
    flagIndices_append_false, sumMarked_eq, sizeEq]
  rw [← getActiveValidatorIndices_eq, markIndices_succ inside, pushed]
  simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, Array.toList_push]
  rw [sumFlags_append (by simp [markIndices, size_foldl_setIfInBounds])]
  -- Every active index is below the old size, so the bounds checks agree.
  have same : (getActiveValidatorIndices state (getCurrentEpoch state)).find?
        (fun index => decide (state.validators.data.size + 1 ≤ index.toNat)) =
      (getActiveValidatorIndices state (getCurrentEpoch state)).find?
        (fun index => decide (state.validators.data.size ≤ index.toNat)) := by
    rw [List.find?_eq_none.mpr, List.find?_eq_none.mpr] <;> intro index member <;>
      have := inside index member <;> simp <;> omega
  rw [same]

/-- The churn limits read the state only through its total active balance. -/
theorem churnLimits_of_total {fork : Base.Fork} {state after : BeaconState preset fork}
    (total : getTotalActiveBalance after = getTotalActiveBalance state) :
    exitChurnLimit config after = exitChurnLimit config state ∧
      getConsolidationChurnLimit config after = getConsolidationChurnLimit config state := by
  constructor <;> simp only [exitChurnLimit, getExitChurnLimit, getActivationExitChurnLimit,
    getBalanceChurnLimit, getConsolidationChurnLimit, total]

/-! ## The steps within a slot or a block -/

/-- One validator later in a step that changes no effective balance.

Its effective balance and its activity in an epoch are the same.

It keeps its exit epoch, unless it had none. -/
structure KeepsStake (epoch : Epoch) (validator later : Validator) : Prop where
  effectiveBalance : later.effectiveBalance = validator.effectiveBalance
  active : isActiveValidator later epoch = isActiveValidator validator epoch
  exitEpoch : later.exitEpoch = validator.exitEpoch ∨ validator.exitEpoch = FAR_FUTURE_EPOCH

theorem KeepsStake.refl (epoch : Epoch) (validator : Validator) :
    KeepsStake epoch validator validator :=
  ⟨rfl, rfl, .inl rfl⟩

theorem KeepsStake.trans {epoch : Epoch} {first second third : Validator}
    (one : KeepsStake epoch first second) (two : KeepsStake epoch second third) :
    KeepsStake epoch first third where
  effectiveBalance := two.effectiveBalance.trans one.effectiveBalance
  active := two.active.trans one.active
  exitEpoch := by
    rcases one.exitEpoch with same | none
    · rcases two.exitEpoch with same' | none'
      · exact .inl (same'.trans same)
      · exact .inr (same ▸ none')
    · exact .inr none

/-- A later state within one slot or block, before any effective balance changes.

Every validator keeps its stake, as `KeepsStake` says, and a new one is not yet active.

So the total active balance is the same.

This holds while the registry has fewer than `2^64` validators. -/
structure FrozenStep (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  size_le : state.validators.data.size ≤ after.validators.data.size
  kept : after.validators.data.size < 2 ^ 64 → ∀ (position : Nat) (validator : Validator),
    state.validators.data[position]? = some validator → ∃ later,
      after.validators.data[position]? = some later ∧
        KeepsStake (getCurrentEpoch state) validator later
  total : after.validators.data.size < 2 ^ 64 →
    getTotalActiveBalance after = getTotalActiveBalance state
  fresh : after.validators.data.size < 2 ^ 64 → ∀ (position : Nat) (later : Validator),
    state.validators.data.size ≤ position → after.validators.data[position]? = some later →
      later.effectiveBalance = 0
  deposit : after.depositBalanceToConsume = state.depositBalanceToConsume

theorem FrozenStep.refl (state : BeaconState preset fork) : FrozenStep state state :=
  ⟨rfl, Nat.le_refl _, fun _ _ validator found => ⟨validator, found, .refl _ _⟩, fun _ => rfl,
    fun _ _ _ outside found => absurd (Array.getElem?_eq_some_iff.mp found).1 (by omega), rfl⟩

theorem FrozenStep.trans {first second third : BeaconState preset fork}
    (one : FrozenStep first second) (two : FrozenStep second third) :
    FrozenStep first third where
  slot := two.slot.trans one.slot
  size_le := Nat.le_trans one.size_le two.size_le
  kept small position validator found := by
    have middleSmall := Nat.lt_of_le_of_lt two.size_le small
    obtain ⟨middle, middleFound, oneKeeps⟩ := one.kept middleSmall position validator found
    obtain ⟨later, laterFound, twoKeeps⟩ := two.kept small position middle middleFound
    have epoch : getCurrentEpoch second = getCurrentEpoch first := by
      simp only [getCurrentEpoch, one.slot]
    exact ⟨later, laterFound, oneKeeps.trans (epoch ▸ twoKeeps)⟩
  total small := (two.total small).trans (one.total (Nat.lt_of_le_of_lt two.size_le small))
  fresh small position later outside found := by
    have middleSmall := Nat.lt_of_le_of_lt two.size_le small
    -- A validator new in the first step keeps its zero balance in the second.
    by_cases middleInside : position < second.validators.data.size
    · obtain ⟨middle, middleFound⟩ : ∃ middle, second.validators.data[position]? = some middle :=
        ⟨_, Array.getElem?_eq_getElem middleInside⟩
      obtain ⟨last, lastFound, keep⟩ := two.kept small position middle middleFound
      rw [lastFound] at found
      cases found
      rw [keep.effectiveBalance]
      exact one.fresh middleSmall position middle outside middleFound
    · exact two.fresh small position later (by omega) found
  deposit := two.deposit.trans one.deposit

/-- The validators that start to exit over two frozen steps in turn.

Each starts in the first step or in the second, with the same effective balance. -/
theorem FrozenStep.sum_exitsBetween_le {first second third : BeaconState preset fork}
    (one : FrozenStep first second) (two : FrozenStep second third)
    (small : third.validators.data.size < 2 ^ 64) (lower upTo : Nat) :
    ∑ position ∈ exitsBetween first third lower upTo, effectiveBalanceAtPosition first position ≤
      ∑ position ∈ exitsBetween first second lower upTo, effectiveBalanceAtPosition first position +
        ∑ position ∈ exitsBetween second third lower upTo,
          effectiveBalanceAtPosition second position := by
  have middleSmall := Nat.lt_of_le_of_lt two.size_le small
  set later := (exitsBetween second third lower upTo).filter (· < first.validators.data.size)
    with laterDef
  -- Each validator that starts to exit has no exit epoch at the middle state, or already one.
  have cover : exitsBetween first third lower upTo ⊆
      exitsBetween first second lower upTo ∪ later := by
    intro position member
    simp only [exitsBetween, Finset.mem_filter, Finset.mem_range] at member
    obtain ⟨inside, starts⟩ := member
    obtain ⟨validator, found⟩ : ∃ validator,
        first.validators.data[position]? = some validator :=
      ⟨_, Array.getElem?_eq_getElem inside⟩
    obtain ⟨middle, middleFound, oneKeeps⟩ := one.kept middleSmall position validator found
    obtain ⟨last, lastFound, twoKeeps⟩ := two.kept small position middle middleFound
    simp only [found, lastFound, startsExit, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at starts
    obtain ⟨⟨⟨far, set⟩, low⟩, within⟩ := starts
    by_cases started : middle.exitEpoch = FAR_FUTURE_EPOCH
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, inside⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_of_lt_of_le inside one.size_le), ?_⟩
      simp [middleFound, lastFound, startsExit, started, set, low, within]
    · have same : last.exitEpoch = middle.exitEpoch := twoKeeps.exitEpoch.resolve_right started
      refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr inside, ?_⟩)
      simp [found, middleFound, startsExit, far, started, same ▸ low, same ▸ within]
  -- On those that start in the second step, the effective balance is the same as at the first.
  have equal : ∑ position ∈ later, effectiveBalanceAtPosition first position =
      ∑ position ∈ later, effectiveBalanceAtPosition second position := by
    refine Finset.sum_congr rfl fun position member => ?_
    have inside := (Finset.mem_filter.mp member).2
    obtain ⟨middle, middleFound, keeps⟩ :=
      one.kept middleSmall position _ (Array.getElem?_eq_getElem inside)
    simp only [effectiveBalanceAtPosition, Array.getElem?_eq_getElem inside, middleFound,
      keeps.effectiveBalance]
  have union := Finset.sum_union_inter (s₁ := exitsBetween first second lower upTo) (s₂ := later)
    (f := effectiveBalanceAtPosition first)
  have covered := Finset.sum_le_sum_of_subset (f := effectiveBalanceAtPosition first) cover
  have filtered := Finset.sum_le_sum_of_subset (f := effectiveBalanceAtPosition second)
    (Finset.filter_subset (· < first.validators.data.size) (exitsBetween second third lower upTo))
  rw [← laterDef, ← equal] at filtered
  calc _ ≤ _ := covered
    _ ≤ _ := Nat.le.intro union
    _ ≤ _ := Nat.add_le_add_left filtered _

/-- No validator starts to exit from a state to itself. -/
theorem exitsBetween_self (state : BeaconState preset fork) (lower upTo : Nat) :
    exitsBetween state state lower upTo = ∅ := by
  refine Finset.filter_eq_empty_iff.mpr fun position _ => ?_
  cases state.validators.data[position]? <;> simp [startsExit]

/-- A frozen step that keeps the size of the registry adds no validator. -/
theorem FrozenStep.of_size (slot : after.slot = state.slot)
    (size : after.validators.data.size = state.validators.data.size)
    (kept : after.validators.data.size < 2 ^ 64 → ∀ (position : Nat) (validator : Validator),
      state.validators.data[position]? = some validator → ∃ later,
        after.validators.data[position]? = some later ∧
          KeepsStake (getCurrentEpoch state) validator later)
    (total : after.validators.data.size < 2 ^ 64 →
      getTotalActiveBalance after = getTotalActiveBalance state)
    (deposit : after.depositBalanceToConsume = state.depositBalanceToConsume) :
    FrozenStep state after :=
  ⟨slot, Nat.le_of_eq size.symm, kept, total, fun _ _ _ outside found =>
    absurd (Array.getElem?_eq_some_iff.mp found).1 (by omega), deposit⟩

/-- A frozen step keeps the churns and every effective balance within its bounds.

The churn left of each queue must stay within its cap. -/
theorem ChurnsWithin.of_frozen {capExit capConsolidation largest : Nat}
    {electra : .pectra ≤ fork} (frozen : FrozenStep state after)
    (small : after.validators.data.size < 2 ^ 64)
    (within : ChurnsWithin config capExit capConsolidation largest state electra)
    (exitLeft : (after.exitBalanceToConsume electra).toNat ≤ capExit)
    (consolidationLeft : (after.consolidationBalanceToConsume electra).toNat ≤ capConsolidation) :
    ChurnsWithin config capExit capConsolidation largest after electra := by
  have limits := churnLimits_of_total (config := config) (frozen.total small)
  refine ⟨fun churn ok => within.exitChurn churn (limits.1 ▸ ok),
    fun churn ok => within.consolidationChurn churn (limits.2 ▸ ok), exitLeft, consolidationLeft,
    fun position later found => ?_⟩
  by_cases inside : position < state.validators.data.size
  · obtain ⟨other, otherFound, keep⟩ :=
      frozen.kept small position _ (Array.getElem?_eq_getElem inside)
    rw [otherFound] at found
    cases found
    rw [keep.effectiveBalance]
    exact within.effective position _ (Array.getElem?_eq_getElem inside)
  · rw [frozen.fresh small position later (by omega) found]
    exact Nat.zero_le _

/-- A step within one slot or block that spends churn.

Each validator that starts to exit spends its effective balance from one of the two queues.

So with churns within two caps, the potentials rise by at least that stake.

The churn left stays within the caps.

The caps must bound the churns of the state, and the step keeps those churns. -/
structure ChargedStep (config : Config) (capExit capConsolidation largest : Nat)
    (electra : .pectra ≤ fork) (state after : BeaconState preset fork) : Prop where
  frozen : FrozenStep state after
  charged : after.validators.data.size < 2 ^ 64 →
    ChurnsWithin config capExit capConsolidation largest state electra →
      ChurnsWithin config capExit capConsolidation largest after electra ∧ ∀ lower upTo,
        ∑ position ∈ exitsBetween state after lower upTo,
            effectiveBalanceAtPosition state position +
            statePotential capExit capConsolidation largest lower upTo state electra ≤
          statePotential capExit capConsolidation largest lower upTo after electra

namespace ChargedStep

variable {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}

theorem refl (state : BeaconState preset fork) :
    ChargedStep config capExit capConsolidation largest electra state state :=
  ⟨.refl state, fun _ within => ⟨within, fun lower upTo => by simp [exitsBetween_self]⟩⟩

theorem trans {first second third : BeaconState preset fork}
    (one : ChargedStep config capExit capConsolidation largest electra first second)
    (two : ChargedStep config capExit capConsolidation largest electra second third) :
    ChargedStep config capExit capConsolidation largest electra first third where
  frozen := one.frozen.trans two.frozen
  charged small within := by
    have middleSmall := Nat.lt_of_le_of_lt two.frozen.size_le small
    obtain ⟨middleWithin, oneCharged⟩ := one.charged middleSmall within
    obtain ⟨lastWithin, twoCharged⟩ := two.charged small middleWithin
    refine ⟨lastWithin, fun lower upTo => ?_⟩
    have split := one.frozen.sum_exitsBetween_le two.frozen small lower upTo
    have := oneCharged lower upTo
    have := twoCharged lower upTo
    omega

/-- A step that keeps the slot, the registry and both queues. -/
theorem of_eq (same : (after.slot, after.validators, churnQueues after,
        after.depositBalanceToConsume) =
      (state.slot, state.validators, churnQueues state, state.depositBalanceToConsume)) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [Prod.mk.injEq] at same
  obtain ⟨slot, validators, queues, deposit⟩ := same
  have exits : exitsBetween state after = exitsBetween state state := by
    funext lower upTo
    simp only [exitsBetween, validators]
  have total : getTotalActiveBalance after = getTotalActiveBalance state := by
    unfold getTotalActiveBalance getTotalBalance getActiveValidatorIndices getCurrentEpoch
    rw [slot, validators]
  have field := congrFun queues electra
  simp only [churnQueues, Prod.mk.injEq] at field
  obtain ⟨exitEpoch, exitLeft, consolidationEpoch, consolidationLeft⟩ := field
  have first : firstExitEpoch preset after = firstExitEpoch preset state := by
    simp only [firstExitEpoch, getCurrentEpoch, slot]
  have frozen : FrozenStep state after := .of_size slot (by rw [validators])
    (fun _ _ validator found => ⟨validator, by rw [validators]; exact found, .refl _ _⟩)
    (fun _ => total) deposit
  refine ⟨frozen, fun small within => ⟨.of_frozen frozen small within
    (exitLeft ▸ within.exitLeft) (consolidationLeft ▸ within.consolidationLeft),
    fun lower upTo => ?_⟩⟩
  · simp only [exits, exitsBetween_self, Finset.sum_empty, Nat.zero_add, statePotential, first,
      exitEpoch, exitLeft, consolidationEpoch, consolidationLeft, Nat.le_refl]

end ChargedStep

/-- A registry of the same size whose validators keep their stake keeps the total active balance.
-/
theorem getTotalActiveBalance_of_keeps (slot : after.slot = state.slot)
    (size : after.validators.data.size = state.validators.data.size)
    (keeps : ∀ (position : Nat) (validator : Validator),
      state.validators.data[position]? = some validator → ∃ later,
        after.validators.data[position]? = some later ∧
          KeepsStake (getCurrentEpoch state) validator later) :
    getTotalActiveBalance after = getTotalActiveBalance state := by
  -- Read both registries position by position.
  have pointwise : ∀ (position : Nat) (inside : position < state.validators.data.size),
      KeepsStake (getCurrentEpoch state) state.validators.data[position]
        (after.validators.data[position]'(size ▸ inside)) := by
    intro position inside
    obtain ⟨later, found, keep⟩ := keeps position _ (Array.getElem?_eq_getElem inside)
    rw [Array.getElem?_eq_getElem (size ▸ inside)] at found
    exact Option.some.inj found ▸ keep
  refine getTotalActiveBalance_congr slot size ?_ ?_
  · apply List.ext_getElem (by simp [activeFlags, size])
    intro position first second
    simp only [activeFlags, List.length_map, Array.length_toList] at first second
    simp only [activeFlags, List.getElem_map, Array.getElem_toList]
    exact (pointwise position second).active
  · apply List.ext_getElem (by simp [effectiveBalances, size])
    intro position first second
    simp only [effectiveBalances, List.length_map, Array.length_toList] at first second
    simp only [effectiveBalances, List.getElem_map, Array.getElem_toList]
    rw [(pointwise position second).effectiveBalance]

namespace ChargedStep

variable {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}

/-- A step that keeps the slot, both queues, the size of the registry and every exit epoch.

Each validator keeps its stake. -/
theorem of_keeps (slot : after.slot = state.slot) (queues : churnQueues after = churnQueues state)
    (deposit : after.depositBalanceToConsume = state.depositBalanceToConsume)
    (size : after.validators.data.size = state.validators.data.size)
    (keeps : ∀ (position : Nat) (validator : Validator),
      state.validators.data[position]? = some validator → ∃ later,
        after.validators.data[position]? = some later ∧
          KeepsStake (getCurrentEpoch state) validator later ∧
          later.exitEpoch = validator.exitEpoch) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  have total := getTotalActiveBalance_of_keeps slot size fun position validator found =>
    have ⟨later, laterFound, keep, _⟩ := keeps position validator found
    ⟨later, laterFound, keep⟩
  have none : ∀ lower upTo, exitsBetween state after lower upTo = ∅ := by
    intro lower upTo
    refine Finset.filter_eq_empty_iff.mpr fun position member => ?_
    have inside := Finset.mem_range.mp member
    obtain ⟨later, laterFound, _, same⟩ :=
      keeps position _ (Array.getElem?_eq_getElem inside)
    simp [Array.getElem?_eq_getElem inside, laterFound, startsExit, same]
  have field := congrFun queues electra
  simp only [churnQueues, Prod.mk.injEq] at field
  obtain ⟨exitEpoch, exitLeft, consolidationEpoch, consolidationLeft⟩ := field
  have first : firstExitEpoch preset after = firstExitEpoch preset state := by
    simp only [firstExitEpoch, getCurrentEpoch, slot]
  have frozen : FrozenStep state after := .of_size slot size
    (fun _ position validator found =>
      have ⟨later, laterFound, keep, _⟩ := keeps position validator found
      ⟨later, laterFound, keep⟩) (fun _ => total) deposit
  refine ⟨frozen, fun small within => ⟨.of_frozen frozen small within
    (exitLeft ▸ within.exitLeft) (consolidationLeft ▸ within.consolidationLeft),
    fun lower upTo => ?_⟩⟩
  · simp only [none, Finset.sum_empty, Nat.zero_add, statePotential, first, exitEpoch,
      exitLeft, consolidationEpoch, consolidationLeft, Nat.le_refl]

/-- Replacing a validator by one that keeps its stake and its exit epoch. -/
theorem setValidator {index : ValidatorIndex} {old validator : Validator}
    (found : getValidator state index = .ok old)
    (set : state.setValidator index validator = .ok after)
    (keep : KeepsStake (getCurrentEpoch state) old validator)
    (same : validator.exitEpoch = old.exitEpoch) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read : state.validators.data[index.toNat]? = some old := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      exact read
    · cases found
  refine of_keeps rfl rfl rfl (by simp [BeaconState.putValidator])
    fun position other otherFound => ?_
  simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set]
  split
  · rename_i equal
    subst equal
    rw [read] at otherFound
    cases otherFound
    exact ⟨validator, by simp, keep, same⟩
  · exact ⟨other, otherFound, .refl _ _, rfl⟩

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : EthLib.Consensus.increaseBalance state index delta = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact .of_eq rfl

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : EthLib.Consensus.decreaseBalance state index delta = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact .of_eq rfl

/-- A fold whose every step is a charged step is a charged step. -/
theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' →
      ChargedStep config capExit capConsolidation largest electra s s') {items : List α}
    (computed : items.foldlM step state = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after :=
  foldlM_ok_invariant (ChargedStep config capExit capConsolidation largest electra state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

end ChargedStep

/-- Replacing one validator starts at most its exit, with its effective balance. -/
theorem sum_exitsBetween_putValidator {index : Nat} {old validator : Validator}
    (inside : index < state.validators.data.size)
    (found : state.validators.data[index]? = some old) (lower upTo : Nat) :
    ∑ position ∈ exitsBetween state (state.putValidator index inside validator) lower upTo,
        effectiveBalanceAtPosition state position ≤
      if startsExit (some old) (some validator) lower upTo then old.effectiveBalance.toNat
      else 0 := by
  have subset : exitsBetween state (state.putValidator index inside validator) lower upTo ⊆
      if startsExit (some old) (some validator) lower upTo then {index} else ∅ := by
    intro position member
    simp only [exitsBetween, Finset.mem_filter, Finset.mem_range, BeaconState.putValidator,
      RootedForkList.data_set, Array.getElem?_set] at member
    obtain ⟨_, starts⟩ := member
    split at starts
    · rename_i equal
      subst equal
      rw [found] at starts
      simp [starts]
    · cases h : state.validators.data[position]? <;> simp [h, startsExit] at starts
  have bound := Finset.sum_le_sum_of_subset (f := effectiveBalanceAtPosition state) subset
  split at bound <;> rename_i starts <;> simp only [starts, ↓reduceIte] <;>
    simp_all [effectiveBalanceAtPosition]

/-- A request that spends churn, then starts the exit of one validator.

The request leaves the registry and the slot, and raises the potentials by the balance it spends.

The validator had no exit epoch, and keeps its stake. -/
theorem ChargedStep.of_put {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}
    {mid : BeaconState preset fork} {index : Nat} {old validator : Validator}
    (validators : mid.validators = state.validators) (slot : mid.slot = state.slot)
    (deposit : mid.depositBalanceToConsume = state.depositBalanceToConsume)
    (inside : index < mid.validators.data.size)
    (found : state.validators.data[index]? = some old)
    (keep : KeepsStake (getCurrentEpoch state) old validator)
    (far : old.exitEpoch = FAR_FUTURE_EPOCH)
    (spent : ChurnsWithin config capExit capConsolidation largest state electra →
      (mid.exitBalanceToConsume electra).toNat ≤ capExit ∧
        (mid.consolidationBalanceToConsume electra).toNat ≤ capConsolidation ∧
        ∀ lower upTo, (if lower ≤ validator.exitEpoch.toNat ∧ validator.exitEpoch.toNat ≤ upTo
            then old.effectiveBalance.toNat else 0) +
            statePotential capExit capConsolidation largest lower upTo state electra ≤
          statePotential capExit capConsolidation largest lower upTo mid electra) :
    ChargedStep config capExit capConsolidation largest electra state
      (mid.putValidator index inside validator) := by
  have midFound : mid.validators.data[index]? = some old := by rw [validators]; exact found
  have keeps : ∀ (position : Nat) (other : Validator),
      state.validators.data[position]? = some other → ∃ later,
        (mid.putValidator index inside validator).validators.data[position]? = some later ∧
          KeepsStake (getCurrentEpoch state) other later := by
    intro position other otherFound
    simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set, validators]
    split
    · rename_i equal
      subst equal
      rw [found] at otherFound
      cases otherFound
      exact ⟨validator, by simp, keep⟩
    · exact ⟨other, otherFound, .refl _ _⟩
  have total : getTotalActiveBalance (mid.putValidator index inside validator) =
      getTotalActiveBalance state :=
    getTotalActiveBalance_of_keeps slot (by simp [BeaconState.putValidator, validators]) keeps
  have frozen : FrozenStep state (mid.putValidator index inside validator) :=
    .of_size slot (by simp [BeaconState.putValidator, validators]) (fun _ => keeps)
      (fun _ => total) deposit
  refine ⟨frozen, fun small within => ?_⟩
  obtain ⟨exitLeft, consolidationLeft, rises⟩ := spent within
  refine ⟨.of_frozen frozen small within exitLeft consolidationLeft, fun lower upTo => ?_⟩
  -- Only the replaced validator can start to exit, with its balance.
  have exits := sum_exitsBetween_putValidator (validator := validator) inside midFound lower upTo
  have sameExits : exitsBetween state (mid.putValidator index inside validator) lower upTo =
      exitsBetween mid (mid.putValidator index inside validator) lower upTo := by
    simp only [exitsBetween, validators]
  have sameBalances : ∀ position, effectiveBalanceAtPosition state position =
      effectiveBalanceAtPosition mid position := by
    intro position
    simp only [effectiveBalanceAtPosition, validators]
  have potential : statePotential capExit capConsolidation largest lower upTo
      (mid.putValidator index inside validator) electra =
      statePotential capExit capConsolidation largest lower upTo mid electra := rfl
  simp only [sameExits, sameBalances, potential]
  have := rises lower upTo
  simp only [startsExit, far, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, bne_iff_ne,
    ne_eq, decide_eq_true_eq] at exits
  split at exits <;> rename_i starts
  · have within : lower ≤ validator.exitEpoch.toNat ∧ validator.exitEpoch.toNat ≤ upTo :=
      ⟨starts.1.2, starts.2⟩
    simp only [within, and_self, ↓reduceIte] at this
    omega
  · split at this <;> omega

/-- An exit from Electra spends the effective balance of the validator from the queue of exits.

The validator was active or not in the current epoch, and stays so, since it leaves later. -/
theorem ChargedStep.initiateValidatorExit {capExit capConsolidation largest : Nat}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : EthLib.Consensus.initiateValidatorExit config state index = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨far, queued, exitEpoch, withdrawable, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _
  simp only [exitQueue, electra, ↓reduceDIte] at queue
  obtain ⟨firstEpoch, churn, left, firstOk, churnOk, placed, rfl⟩ :=
    computeExitEpochAndUpdateChurn_eq queue
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read : state.validators.data[index.toNat]? = some validator := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      exact read
    · cases found
  obtain ⟨-, firstValue⟩ := computeActivationExitEpoch_ok_iff.mp firstOk
  have firstIs : firstEpoch.toNat = firstExitEpoch preset state := firstValue
  have exitLater : (getCurrentEpoch state).toNat < exitEpoch.toNat := by
    obtain ⟨_, firstLe, _⟩ := churnQueue_potential (cap := 2 ^ 64)
      (Nat.le_of_lt (UInt64.toNat_lt _)) (Nat.le_of_lt (UInt64.toNat_lt _)) placed
    have := UInt64.le_iff_toNat_le.mp firstLe
    unfold firstExitEpoch at firstIs
    omega
  refine ChargedStep.of_put (state := state) (mid := { state with
    exitBalanceToConsume := fun _ => left, earliestExitEpoch := fun _ => exitEpoch })
    rfl rfl rfl inside read ?_ far fun within => ?_
  · -- The validator leaves after the current epoch, so its activity now is the same.
    refine ⟨rfl, ?_, .inr far⟩
    have below := exitEpoch.toNat_lt
    simp only [isActiveValidator, far, FAR_FUTURE_EPOCH]
    by_cases active : validator.activationEpoch ≤ getCurrentEpoch state
    · simp only [active, decide_true, Bool.true_and, UInt64.lt_iff_toNat_lt]
      simp
      omega
    · simp [active]
  · have churnLe := within.exitChurn churn churnOk
    obtain ⟨leftLe, _, _⟩ := churnQueue_potential within.exitLeft churnLe placed
    refine ⟨leftLe, within.consolidationLeft, fun lower upTo => ?_⟩
    have rises := churnQueue_windowPotential within.exitLeft churnLe placed lower upTo
      (within.effective _ _ read)
    rw [firstIs] at rises
    rw [statePotential_exitQueue]
    unfold statePotential
    dsimp only
    split at rises <;> split <;> omega

/-- With `2^64` validators or more, every step of the same slot and size is a charged step.

All its facts hold only below `2^64`. -/
theorem ChargedStep.of_big {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}
    (big : 2 ^ 64 ≤ state.validators.data.size) (slot : after.slot = state.slot)
    (size : state.validators.data.size ≤ after.validators.data.size)
    (deposit : after.depositBalanceToConsume = state.depositBalanceToConsume) :
    ChargedStep config capExit capConsolidation largest electra state after :=
  ⟨⟨slot, size, fun small => absurd small (by omega), fun small => absurd small (by omega),
    fun small => absurd small (by omega), deposit⟩, fun small => absurd small (by omega)⟩

/-- A request that spends churn and starts no exit, such as a partial withdrawal. -/
theorem ChargedStep.of_rise {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}
    (validators : after.validators = state.validators) (slot : after.slot = state.slot)
    (deposit : after.depositBalanceToConsume = state.depositBalanceToConsume)
    (spent : ChurnsWithin config capExit capConsolidation largest state electra →
      (after.exitBalanceToConsume electra).toNat ≤ capExit ∧
        (after.consolidationBalanceToConsume electra).toNat ≤ capConsolidation ∧
        ∀ lower upTo, statePotential capExit capConsolidation largest lower upTo state electra ≤
          statePotential capExit capConsolidation largest lower upTo after electra) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  have total : getTotalActiveBalance after = getTotalActiveBalance state := by
    unfold getTotalActiveBalance getTotalBalance getActiveValidatorIndices getCurrentEpoch
    rw [slot, validators]
  have none : ∀ lower upTo, exitsBetween state after lower upTo = ∅ := by
    intro lower upTo
    simp only [exitsBetween, validators]
    exact exitsBetween_self state lower upTo
  have frozen : FrozenStep state after := .of_size slot (by rw [validators])
    (fun _ _ validator found => ⟨validator, by rw [validators]; exact found, .refl _ _⟩)
    (fun _ => total) deposit
  refine ⟨frozen, fun small within => ?_⟩
  obtain ⟨exitLeft, consolidationLeft, rises⟩ := spent within
  exact ⟨.of_frozen frozen small within exitLeft consolidationLeft, fun lower upTo => by
    simp only [none, Finset.sum_empty, Nat.zero_add]
    exact rises lower upTo⟩

theorem ChargedStep.requestPartialWithdrawal {capExit capConsolidation largest : Nat}
    {electra : .pectra ≤ fork} {index : ValidatorIndex} {validator : Validator}
    {amount owed : Gwei}
    (computed : EthLib.Consensus.requestPartialWithdrawal config state electra index validator
      amount owed = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [EthLib.Consensus.requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure,
    Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, exitEpoch⟩, churned, _, _, _, _, rfl⟩ := computed
    obtain ⟨firstEpoch, churn, left, firstOk, churnOk, placed, rfl⟩ :=
      computeExitEpochAndUpdateChurn_eq churned
    obtain ⟨-, firstValue⟩ := computeActivationExitEpoch_ok_iff.mp firstOk
    have firstIs : firstEpoch.toNat = firstExitEpoch preset state := firstValue
    refine ChargedStep.of_rise rfl rfl rfl fun within => ?_
    have churnLe := within.exitChurn churn churnOk
    obtain ⟨leftLe, _, rises⟩ := churnQueue_potential within.exitLeft churnLe placed
    refine ⟨leftLe, within.consolidationLeft, fun lower upTo => ?_⟩
    -- A partial withdrawal starts no exit, and never lowers the spend on a range.
    have mono := windowPotential_mono (cap := capExit) (largest := largest) (lower := lower)
      (upTo := upTo) (show _ ≤ _ from Nat.le_of_add_left_le rises)
    rw [firstIs] at mono
    show _ ≤ windowPotential capExit largest lower upTo
        (queuePotential capExit (firstExitEpoch preset state) exitEpoch left) +
      windowPotential capConsolidation largest lower upTo (queuePotential capConsolidation
        (firstExitEpoch preset state) (state.earliestConsolidationEpoch electra)
        (state.consolidationBalanceToConsume electra))
    unfold statePotential
    omega
  · cases computed
    exact .refl _

/-- A consolidation spends the effective balance of its source from the queue of consolidations.

The source starts to exit then, after the current epoch. -/
theorem ChargedStep.queueConsolidation {capExit capConsolidation largest : Nat}
    {electra : .pectra ≤ fork} {sourcePosition : Nat} {source : Validator}
    {targetIndex : ValidatorIndex}
    (found : state.validators.data[sourcePosition]? = some source)
    (far : source.exitEpoch = FAR_FUTURE_EPOCH)
    (computed : EthLib.Consensus.queueConsolidation config state electra sourcePosition source
      targetIndex = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [EthLib.Consensus.queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, pure, Except.pure] at computed
  obtain ⟨⟨_, exitEpoch⟩, churned, withdrawable, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  obtain ⟨firstEpoch, churn, left, firstOk, churnOk, placed, rfl⟩ :=
    computeConsolidationEpochAndUpdateChurn_eq churned
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have lastStep : ∀ {fork' : Base.Fork} (middle : BeaconState preset fork),
      ChargedStep config capExit capConsolidation largest electra middle
        { middle with pendingConsolidations := fun _ => ‹_› } := fun _ => .of_eq rfl
  refine ChargedStep.trans ?_ (lastStep (fork' := fork) _)
  by_cases big : 2 ^ 64 ≤ state.validators.data.size
  · exact .of_big big rfl (by simp [BeaconState.putValidator]) rfl
  have exact : sourcePosition.toUInt64.toNat = sourcePosition := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (show sourcePosition < 2 ^ 64 by
      have := (Array.getElem?_eq_some_iff.mp found).1
      omega)]
  have read : state.validators.data[sourcePosition.toUInt64.toNat]? = some source := by
    rw [exact]
    exact found
  obtain ⟨-, firstValue⟩ := computeActivationExitEpoch_ok_iff.mp firstOk
  have firstIs : firstEpoch.toNat = firstExitEpoch preset state := firstValue
  have exitLater : (getCurrentEpoch state).toNat < exitEpoch.toNat := by
    obtain ⟨_, firstLe, _⟩ := churnQueue_potential (cap := 2 ^ 64)
      (Nat.le_of_lt (UInt64.toNat_lt _)) (Nat.le_of_lt (UInt64.toNat_lt _)) placed
    have := UInt64.le_iff_toNat_le.mp firstLe
    unfold firstExitEpoch at firstIs
    omega
  refine ChargedStep.of_put (state := state) (mid := { state with
    consolidationBalanceToConsume := fun _ => left,
    earliestConsolidationEpoch := fun _ => exitEpoch })
    rfl rfl rfl inside read ?_ far fun within => ?_
  · -- The source leaves after the current epoch, so its activity now is the same.
    refine ⟨rfl, ?_, .inr far⟩
    have below := exitEpoch.toNat_lt
    simp only [isActiveValidator, far, FAR_FUTURE_EPOCH]
    by_cases active : source.activationEpoch ≤ getCurrentEpoch state
    · simp only [active, decide_true, Bool.true_and, UInt64.lt_iff_toNat_lt]
      simp
      omega
    · simp [active]
  · have churnLe := within.consolidationChurn churn churnOk
    obtain ⟨leftLe, _, _⟩ := churnQueue_potential within.consolidationLeft churnLe placed
    refine ⟨within.exitLeft, leftLe, fun lower upTo => ?_⟩
    have rises := churnQueue_windowPotential within.consolidationLeft churnLe placed lower upTo
      (within.effective _ _ found)
    rw [firstIs] at rises
    rw [statePotential_consolidationQueue]
    unfold statePotential
    dsimp only
    split at rises <;> split <;> omega

/-- A new validator at the end of the registry, not yet active. -/
theorem ChargedStep.of_push {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}
    {validator : Validator}
    (pushed : after.validators.data = state.validators.data.push validator)
    (inactive : isActiveValidator validator (getCurrentEpoch state) = false)
    (zero : validator.effectiveBalance = 0)
    (slot : after.slot = state.slot) (queues : churnQueues after = churnQueues state)
    (deposit : after.depositBalanceToConsume = state.depositBalanceToConsume) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  have keeps : ∀ (position : Nat) (other : Validator),
      state.validators.data[position]? = some other →
        after.validators.data[position]? = some other := by
    intro position other found
    rw [pushed, Array.getElem?_push]
    have := (Array.getElem?_eq_some_iff.mp found).1
    simp only [Nat.ne_of_lt this, ↓reduceIte, found]
  have none : ∀ lower upTo, exitsBetween state after lower upTo = ∅ := by
    intro lower upTo
    refine Finset.filter_eq_empty_iff.mpr fun position member => ?_
    have inside := Finset.mem_range.mp member
    rw [keeps position _ (Array.getElem?_eq_getElem inside), Array.getElem?_eq_getElem inside]
    simp [startsExit]
  have field := congrFun queues electra
  simp only [churnQueues, Prod.mk.injEq] at field
  obtain ⟨exitEpoch, exitLeft, consolidationEpoch, consolidationLeft⟩ := field
  have first : firstExitEpoch preset after = firstExitEpoch preset state := by
    simp only [firstExitEpoch, getCurrentEpoch, slot]
  -- The only new validator is the pushed one, with no effective balance.
  have frozen : FrozenStep state after := ⟨slot, by simp [pushed], fun _ position other found =>
    ⟨other, keeps position other found, .refl _ _⟩,
    fun small => getTotalActiveBalance_push slot pushed inactive small,
    fun _ position later outside found => by
      rw [pushed, Array.getElem?_push] at found
      split at found
      · cases found
        exact zero
      · exact absurd (Array.getElem?_eq_some_iff.mp found).1 (by omega), deposit⟩
  refine ⟨frozen, fun small within => ⟨.of_frozen frozen small within
    (exitLeft ▸ within.exitLeft) (consolidationLeft ▸ within.consolidationLeft),
    fun lower upTo => ?_⟩⟩
  · simp only [none, Finset.sum_empty, Nat.zero_add, statePotential, first, exitEpoch,
      exitLeft, consolidationEpoch, consolidationLeft, Nat.le_refl]

/-- An append at the end of a list that is below `2^64` long. -/
private theorem setOrAppendRooted_push {switch : Base.Fork} {α : Type} [SszType α] {limit : Nat}
    {list list' : RootedForkList switch fork α limit} {value : α}
    (small : list.data.size < 2 ^ 64)
    (computed : setOrAppendRooted list list.data.size.toUInt64 value = .ok list') :
    list'.data = list.data.push value := by
  have atEnd : list.data.size.toUInt64.toNat = list.data.size := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (show list.data.size < 2 ^ 64 from small)]
  unfold setOrAppendRooted at computed
  simp only [atEnd, ↓reduceIte] at computed
  split at computed
  · cases computed
    rfl
  · cases computed

/-- A validator that comes from a deposit is not yet active. -/
theorem isActiveValidator_getValidatorFromDeposit {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} (epoch : Epoch) :
    isActiveValidator (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount)
      epoch = false := by
  simp only [isActiveValidator, getValidatorFromDeposit, Bool.and_eq_false_iff]
  -- An epoch at or past the far future epoch is not before it.
  by_cases far : FAR_FUTURE_EPOCH ≤ epoch
  · exact .inr (decide_eq_false (UInt64.not_lt.mpr far))
  · exact .inl (decide_eq_false far)

/-! ## The charged steps of a block -/

section Block

variable {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}

theorem chargedStep_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  have final : ChargedStep config capExit capConsolidation largest electra last after := by
    simp only [pure, Except.pure, Except.ok.injEq] at done
    subst done
    split
    · exact .of_eq rfl
    · exact .refl _
  -- Slashing keeps the effective balance and the epochs that decide activity.
  exact (ChargedStep.initiateValidatorExit exitedOk).trans <|
    ((ChargedStep.setValidator found markedOk ⟨rfl, rfl, .inl rfl⟩ rfl).trans
      (by exact .of_eq rfl)).trans <|
    (ChargedStep.decreaseBalance loweredOk).trans <|
    (ChargedStep.increaseBalance raisedOk).trans <|
    (ChargedStep.increaseBalance lastOk).trans final

theorem chargedStep_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_eq rfl

theorem chargedStep_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_eq rfl

theorem chargedStep_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_eq (by rw [← rest]; rfl)

theorem chargedStep_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact chargedStep_slashValidator slashed

theorem chargedStep_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    ChargedStep config capExit capConsolidation largest electra step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact chargedStep_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem chargedStep_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant
    (fun step => ChargedStep config capExit capConsolidation largest electra state step.1)
    (fun _ _ _ before ok => before.trans (chargedStep_slashIfSlashable ok))
    (show ChargedStep config capExit capConsolidation largest electra state (state, false).1 from
      .refl state) folded

theorem chargedStep_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : ChargedStep config capExit capConsolidation largest electra raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_eq rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        ChargedStep config capExit capConsolidation largest electra state
          (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_eq rfl
    exact (flagged _ _).trans ((ChargedStep.increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact .of_eq (by rw [← rest]; rfl)

theorem chargedStep_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} (zero : amount = 0)
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨validators, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
    by_cases big : 2 ^ 64 ≤ state.validators.data.size
    · refine .of_big big rfl ?_ rfl
      have := setOrAppendRooted_size validatorsOk
      simp only at this ⊢
      split at this <;> omega
    · exact .of_push (setOrAppendRooted_push (by omega) validatorsOk)
        (isActiveValidator_getValidatorFromDeposit _) (by
          subst zero
          simp only [getValidatorFromDeposit, UInt64.zero_mod, UInt64.sub_self, UInt64.min_def,
            UInt64.zero_le, ↓reduceIte])
        rfl rfl rfl
  · rename_i notAltair
    exact absurd (Nat.le_trans (by decide) electra) notAltair

theorem chargedStep_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold applyDeposit at computed
  split at computed
  · unfold applyDepositElectra at computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, added, pushed⟩ := computed
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (chargedStep_addValidatorToRegistry rfl added).trans (.of_eq rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_eq rfl
  · rename_i notElectra
    exact absurd electra notElectra

theorem chargedStep_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (ChargedStep.of_eq (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (chargedStep_applyDeposit applied)

theorem chargedStep_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact ChargedStep.initiateValidatorExit exited

theorem chargedStep_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_eq rfl

theorem chargedStep_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact ChargedStep.initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact ChargedStep.requestPartialWithdrawal computed

theorem chargedStep_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_eq rfl
  · cases computed
    exact .refl _

theorem chargedStep_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, found, _, set, queued⟩ := computed
  exact (ChargedStep.setValidator found set ⟨rfl, rfl, .inl rfl⟩ rfl).trans
    (chargedStep_queueExcessActiveBalance queued)

theorem chargedStep_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact chargedStep_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact ChargedStep.queueConsolidation (Array.getElem?_eq_getElem _)
        (by clear computed; simp_all) computed

theorem chargedStep_processExecutionRequests {body : BeaconBlockBody preset fork}
    {during : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body during = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (ChargedStep.foldlM (fun _ _ _ ok => chargedStep_processDepositRequest ok)
      depositsOk).trans <|
    (ChargedStep.foldlM (fun _ _ _ ok => chargedStep_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    ChargedStep.foldlM
      (fun _ _ _ ok => chargedStep_processConsolidationRequest ok) consolidationsOk

/-! ## Withdrawals -/

theorem chargedStep_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_eq rfl
  · exact .decreaseBalance computed

theorem chargedStep_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : ChargedStep config capExit capConsolidation largest electra state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact ChargedStep.foldlM (fun _ _ _ ok => chargedStep_applyWithdrawal ok)
      appliedOk
  have two : ChargedStep config capExit capConsolidation largest electra applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_eq rfl
    · cases indexedOk
      exact .refl _
  have queued : ∀ kept : BeaconState preset fork,
      ChargedStep config capExit capConsolidation largest electra kept
        (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_eq rfl
    · exact .refl _
  have partials : ∀ kept : BeaconState preset fork,
      ChargedStep config capExit capConsolidation largest electra kept
        (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split <;> exact .of_eq rfl
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished →
        ChargedStep config capExit capConsolidation largest electra kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact .of_eq rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  have lastKept : ChargedStep config capExit capConsolidation largest electra finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact .of_eq rfl
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

theorem chargedStep_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact chargedStep_applyExpectedWithdrawals applied
    · cases computed
      exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact chargedStep_applyExpectedWithdrawals applied

theorem chargedStep_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨old, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  have keep : KeepsStake (getCurrentEpoch state) old { old with
      withdrawalCredentials := executionCredentials signed.message.toExecutionAddress } :=
    ⟨rfl, by simp only [isActiveValidator], .inl rfl⟩
  exact .setValidator found set keep rfl

/-! ## The parent payload and the execution part of a block -/

theorem chargedStep_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_eq rfl

theorem chargedStep_processBuilderDepositRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processBuilderDepositRequest addBuilderToRegistry at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .of_eq rfl)

theorem chargedStep_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · simp only [initiateBuilderExit, bind_ok_iff] at exited
    obtain ⟨_, _, _, _, set⟩ := exited
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_eq rfl

theorem chargedStep_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact .of_eq rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;> exact .of_eq rfl

theorem chargedStep_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact .refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  unfold applyParentExecutionPayload at applied
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    applied
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, buildersOk, exitsOk⟩ :=
    requestedOk
  exact (chargedStep_settleParentPayment settledOk).trans <|
    (ChargedStep.foldlM (fun _ _ _ ok => chargedStep_processDepositRequest ok)
      depositsOk).trans <|
    (ChargedStep.foldlM (fun _ _ _ ok => chargedStep_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    (ChargedStep.foldlM
      (fun _ _ _ ok => chargedStep_processConsolidationRequest ok) consolidationsOk).trans <|
    (ChargedStep.foldlM
      (fun _ _ _ ok => chargedStep_processBuilderDepositRequest ok) buildersOk).trans <|
    (ChargedStep.foldlM
      (fun _ _ _ ok => chargedStep_processBuilderExitRequest ok) exitsOk).trans
      (.of_eq rfl)

theorem chargedStep_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_eq rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_eq rfl

theorem chargedStep_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (chargedStep_processWithdrawals withdrawnOk).trans
      (chargedStep_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (chargedStep_processWithdrawals withdrawnOk).trans
      (chargedStep_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact chargedStep_processExecutionPayload computed
    · cases computed
      exact .refl _

/-! ## The sync aggregate -/

theorem chargedStep_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine ChargedStep.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (ChargedStep.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

/-! ## Blocks -/

theorem chargedStep_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (ChargedStep.foldlM
        (fun _ _ _ ok => chargedStep_processProposerSlashing ok) proposersOk).trans <|
      (ChargedStep.foldlM
        (fun _ _ _ ok => chargedStep_processAttesterSlashing ok) attestersOk).trans <|
      (ChargedStep.foldlM (fun _ _ _ ok => chargedStep_processAttestation ok)
        attestedOk).trans <|
      (ChargedStep.foldlM (fun _ _ _ ok => chargedStep_processVoluntaryExit ok)
        exitsOk).trans <|
      (ChargedStep.foldlM
        (fun _ _ _ ok => chargedStep_processBlsToExecutionChange ok) changesOk).trans <|
      ChargedStep.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : ChargedStep config capExit capConsolidation largest electra exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact ChargedStep.foldlM
        (fun _ _ _ ok => chargedStep_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : ChargedStep config capExit capConsolidation largest electra changed after :=
    chargedStep_processExecutionRequests requestsOk
  exact (ChargedStep.foldlM
      (fun _ _ _ ok => chargedStep_processProposerSlashing ok) proposersOk).trans <|
    (ChargedStep.foldlM
      (fun _ _ _ ok => chargedStep_processAttesterSlashing ok) attestersOk).trans <|
    (ChargedStep.foldlM (fun _ _ _ ok => chargedStep_processAttestation ok)
      attestedOk).trans <|
    (ChargedStep.foldlM (fun _ _ _ ok => chargedStep_processDeposit ok)
      depositedOk).trans <|
    (ChargedStep.foldlM (fun _ _ _ ok => chargedStep_processVoluntaryExit ok)
      exitsOk).trans <|
    changes.trans requests

theorem chargedStep_processBlock {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    have paidKept : ChargedStep config capExit capConsolidation largest electra state paid := by
      split at paidOk
      · exact chargedStep_processParentExecutionPayload paidOk
      · cases paidOk
        exact .refl _
    have executedKept :
        ChargedStep config capExit capConsolidation largest electra headed executed := by
      split at executedOk
      · exact chargedStep_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    have votedKept :
        ChargedStep config capExit capConsolidation largest electra revealed voted := by
      split at votedOk
      · exact chargedStep_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    exact paidKept.trans <| (chargedStep_processBlockHeader headedOk).trans <|
      executedKept.trans <| (chargedStep_processRandao revealedOk).trans <|
      votedKept.trans <| (chargedStep_processOperations operatedOk).trans
        (chargedStep_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (chargedStep_processBlockHeader headerOk).trans <|
    (chargedStep_processRandao randaoOk).trans <|
    (chargedStep_processEth1Data eth1Ok).trans
      (chargedStep_processOperations operationsOk)

end Block

/-! ## The charged steps of an epoch: up to the slashings -/

section EpochCharged

variable {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}

theorem chargedStep_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_eq (by rw [← rest]; rfl)

theorem chargedStep_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_eq rfl

theorem chargedStep_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after :=
  ChargedStep.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (ChargedStep.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem chargedStep_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact ChargedStep.foldlM (fun _ _ _ ok => chargedStep_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact chargedStep_applyAllDeltas applied

/-- One validator in the registry updates from Electra.

An activation sets an activation epoch after the current one, so the validator stays inactive. -/
theorem chargedStep_updateRegistryEntryElectra {activationEpoch : Epoch} {index : Nat}
    (later : (getCurrentEpoch state).toNat < activationEpoch.toNat)
    (computed : updateRegistryEntryElectra config activationEpoch state index = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, set⟩ := computed
    exact .setValidator found set ⟨rfl, by simp only [isActiveValidator], .inl rfl⟩ rfl
  split at computed
  · exact ChargedStep.initiateValidatorExit (liftAccessor_ok.mp computed)
  split at computed
  · rename_i eligible
    rw [liftAccessor_ok] at computed
    have far : validator.activationEpoch = FAR_FUTURE_EPOCH := by
      simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
      exact eligible.2
    -- Neither the old nor the new activation epoch is at or before the current epoch.
    refine .setValidator found computed ⟨rfl, ?_, .inl rfl⟩ rfl
    simp only [isActiveValidator, far]
    have notYet : ¬ activationEpoch ≤ getCurrentEpoch state := fun le => by
      have := UInt64.le_iff_toNat_le.mp le
      omega
    by_cases farLe : FAR_FUTURE_EPOCH ≤ getCurrentEpoch state
    · have notBefore : ¬ getCurrentEpoch state < validator.exitEpoch := fun lt => by
        have farValue : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
        have := UInt64.le_iff_toNat_le.mp farLe
        have := UInt64.lt_iff_toNat_lt.mp lt
        have := validator.exitEpoch.toNat_lt
        omega
      simp [notYet, farLe, notBefore]
    · simp [notYet, farLe]
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem chargedStep_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨activationEpoch, activationOk, computed⟩ := computed
    obtain ⟨-, value⟩ := computeActivationExitEpoch_ok_iff.mp (by
      simpa [liftArith, mapError_ok_iff] using activationOk)
    -- Each step of the fold keeps the slot, so the activation epoch stays after the current one.
    refine foldlM_ok_invariant (ChargedStep config capExit capConsolidation largest electra state)
      (fun current _ next before ok => before.trans
        (chargedStep_updateRegistryEntryElectra ?_ ok)) (.refl state) computed
    have epoch : getCurrentEpoch current = getCurrentEpoch state := by
      simp only [getCurrentEpoch, before.frozen.slot]
    rw [epoch]
    omega
  · rename_i notElectra
    exact absurd electra notElectra

theorem chargedStep_processSlashings (computed : processSlashings state = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff, electra, ↓reduceIte] at computed
  obtain ⟨_, _, _, _, _, _, _, _, applied⟩ := computed
  refine ChargedStep.foldlM (fun _ _ _ ok => ?_) applied
  simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, lowered⟩ := ok
      exact .decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ .refl _

theorem chargedStep_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    ChargedStep config capExit capConsolidation largest electra state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_eq rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

end EpochCharged

/-! ## The quiet steps of an epoch: after the slashings -/

/-- A later state in which no validator starts to exit and both queues stay.

Effective balances may change, and new validators may join.

The slot may move on.

The facts on the registry hold while it has fewer than `2^64` validators. -/
structure QuietStep (state after : BeaconState preset fork) : Prop where
  slot : state.slot ≤ after.slot
  size_le : state.validators.data.size ≤ after.validators.data.size
  exits : after.validators.data.size < 2 ^ 64 → ∀ (position : Nat) (validator : Validator),
    state.validators.data[position]? = some validator → ∃ later,
      after.validators.data[position]? = some later ∧ later.exitEpoch = validator.exitEpoch
  queues : churnQueues after = churnQueues state

namespace QuietStep

theorem refl (state : BeaconState preset fork) : QuietStep state state :=
  ⟨UInt64.le_refl _, Nat.le_refl _, fun _ _ validator found => ⟨validator, found, rfl⟩, rfl⟩

theorem trans {first second third : BeaconState preset fork} (one : QuietStep first second)
    (two : QuietStep second third) : QuietStep first third where
  slot := UInt64.le_trans one.slot two.slot
  size_le := Nat.le_trans one.size_le two.size_le
  exits small position validator found := by
    obtain ⟨middle, middleFound, same⟩ :=
      one.exits (Nat.lt_of_le_of_lt two.size_le small) position validator found
    obtain ⟨later, laterFound, same'⟩ := two.exits small position middle middleFound
    exact ⟨later, laterFound, same'.trans same⟩
  queues := two.queues.trans one.queues

theorem of_eq (same : (after.slot, after.validators, churnQueues after) =
      (state.slot, state.validators, churnQueues state)) : QuietStep state after := by
  simp only [Prod.mk.injEq] at same
  obtain ⟨slot, validators, queues⟩ := same
  exact ⟨slot ▸ UInt64.le_refl _, by rw [validators], fun _ _ validator found =>
    ⟨validator, by rw [validators]; exact found, rfl⟩, queues⟩

theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → QuietStep s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : QuietStep state after :=
  foldlM_ok_invariant (QuietStep state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (.refl state) computed

theorem setValidator {index : ValidatorIndex} {old validator : Validator}
    (found : getValidator state index = .ok old)
    (set : state.setValidator index validator = .ok after)
    (same : validator.exitEpoch = old.exitEpoch) : QuietStep state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read : state.validators.data[index.toNat]? = some old := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      exact read
    · cases found
  refine ⟨UInt64.le_refl _, by simp [BeaconState.putValidator],
    fun _ position other otherFound => ?_,
    rfl⟩
  simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem?_set]
  split
  · rename_i equal
    subst equal
    rw [read] at otherFound
    cases otherFound
    exact ⟨validator, by simp, same⟩
  · exact ⟨other, otherFound, rfl⟩

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : EthLib.Consensus.increaseBalance state index delta = .ok after) :
    QuietStep state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact .of_eq rfl

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : EthLib.Consensus.decreaseBalance state index delta = .ok after) :
    QuietStep state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact .of_eq rfl

end QuietStep

theorem quietStep_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    QuietStep state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨validators, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
    have read := setOrAppendRooted_getElem? validatorsOk
    have size := setOrAppendRooted_size validatorsOk
    refine ⟨UInt64.le_refl _, by simp only at size ⊢; split at size <;> omega,
      fun small position validator found => ⟨validator, ?_, rfl⟩, rfl⟩
    -- Below `2^64` the index for a new validator is the size, past every position.
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have exact : (getIndexForNewValidator state).toNat = state.validators.data.size := by
      simp only at small size
      unfold getIndexForNewValidator
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt'
        (show state.validators.data.size < 2 ^ 64 by split at size <;> omega)]
    simp only
    rw [read, exact]
    simp [Nat.ne_of_lt inside, found]
  · split at computed
    · cases computed
      refine ⟨UInt64.le_refl _, by simp [RootedForkList.data_push],
        fun _ position validator found =>
        ⟨validator, ?_, rfl⟩, rfl⟩
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      simp [RootedForkList.data_push, Array.getElem?_push, Nat.ne_of_lt inside, found]
    · cases computed

theorem quietStep_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    QuietStep state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact quietStep_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · rw [liftAccessor_ok] at computed
    exact .increaseBalance computed

theorem quietStep_processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    QuietStep state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq computed
  exact .of_eq rfl

theorem quietStep_processRandaoMixesReset (computed : processRandaoMixesReset state = .ok after) :
    QuietStep state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq computed
  exact .of_eq rfl

theorem quietStep_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : QuietStep state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_eq rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem quietStep_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    QuietStep state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine QuietStep.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, found, _, _, _, _, set⟩ := ok
  exact .setValidator found set rfl

theorem quietStep_passPendingDeposits {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      QuietStep state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact .refl _
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (quietStep_applyPendingDeposit credited).trans
        (quietStep_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact quietStep_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact .refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (quietStep_applyPendingDeposit credited).trans
      (quietStep_passPendingDeposits (deposits := rest) ‹_›)

theorem quietStep_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    QuietStep state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (quietStep_passPendingDeposits ‹_›).trans (.of_eq rfl)

theorem quietStep_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      QuietStep state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact quietStep_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (QuietStep.decreaseBalance loweredOk).trans <|
      (QuietStep.increaseBalance raisedOk).trans
        (quietStep_passPendingConsolidations (result := (passed, read)) passedOk)

theorem quietStep_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    QuietStep state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine (quietStep_processPendingDeposits deposited).trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (quietStep_passPendingConsolidations ‹_›).trans (.of_eq rfl)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- The steps that close an epoch from Altair, after the history. -/
theorem quietStep_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : QuietStep rooted after := by
  have syncedKept : QuietStep rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact .of_eq rfl
  have lookedKept : QuietStep synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedKept : QuietStep looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedKept.trans (lookedKept.trans windowedKept)


/-! ## One slot or one block -/

/-- A later state after one slot or one block of the same fork.

Each validator keeps its exit epoch, unless it had none.

Take churns within two caps, and a range of exit epochs.

The potentials on the range then rise by at least the effective stake that starts to exit in it.

The churn left stays within the caps.

The facts hold while the registry has fewer than `2^64` validators. -/
structure StepCharge (config : Config) (capExit capConsolidation largest : Nat)
    (electra : .pectra ≤ fork) (state after : BeaconState preset fork) : Prop where
  size_le : state.validators.data.size ≤ after.validators.data.size
  exits : after.validators.data.size < 2 ^ 64 → ∀ (position : Nat) (validator : Validator),
    state.validators.data[position]? = some validator → ∃ later,
      after.validators.data[position]? = some later ∧
        (later.exitEpoch = validator.exitEpoch ∨ validator.exitEpoch = FAR_FUTURE_EPOCH)
  charged : after.validators.data.size < 2 ^ 64 →
    ChurnsWithin config capExit capConsolidation largest state electra →
      (after.exitBalanceToConsume electra).toNat ≤ capExit ∧
        (after.consolidationBalanceToConsume electra).toNat ≤ capConsolidation ∧
        ∀ lower upTo,
          ∑ position ∈ exitsBetween state after lower upTo,
              effectiveBalanceAtPosition state position +
              statePotential capExit capConsolidation largest lower upTo state electra ≤
            statePotential capExit capConsolidation largest lower upTo after electra

/-- A charged step, then a quiet one. -/
theorem ChargedStep.quiet {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}
    {middle : BeaconState preset fork}
    (charged : ChargedStep config capExit capConsolidation largest electra state middle)
    (quiet : QuietStep middle after) :
    StepCharge config capExit capConsolidation largest electra state after := by
  have middleSmall : after.validators.data.size < 2 ^ 64 →
      middle.validators.data.size < 2 ^ 64 := fun small => Nat.lt_of_le_of_lt quiet.size_le small
  have field := congrFun quiet.queues electra
  simp only [churnQueues, Prod.mk.injEq] at field
  obtain ⟨exitEpoch, exitLeft, consolidationEpoch, consolidationLeft⟩ := field
  refine ⟨Nat.le_trans charged.frozen.size_le quiet.size_le,
    fun small position validator found => ?_,
    fun small within => ?_⟩
  · obtain ⟨middleValidator, middleFound, keep⟩ :=
      charged.frozen.kept (middleSmall small) position validator found
    obtain ⟨later, laterFound, same⟩ := quiet.exits small position middleValidator middleFound
    exact ⟨later, laterFound, by rw [same]; exact keep.exitEpoch⟩
  obtain ⟨middleWithin, rises⟩ := charged.charged (middleSmall small) within
  refine ⟨exitLeft ▸ middleWithin.exitLeft, consolidationLeft ▸ middleWithin.consolidationLeft,
    fun lower upTo => ?_⟩
  -- No validator starts to exit in the quiet step.
  have sameExits : exitsBetween state after lower upTo ⊆ exitsBetween state middle lower upTo := by
    intro position member
    simp only [exitsBetween, Finset.mem_filter, Finset.mem_range] at member ⊢
    obtain ⟨inside, starts⟩ := member
    refine ⟨inside, ?_⟩
    obtain ⟨middleValidator, middleFound, _⟩ := charged.frozen.kept (middleSmall small) position _
      (Array.getElem?_eq_getElem inside)
    obtain ⟨later, laterFound, same⟩ := quiet.exits small position middleValidator middleFound
    rw [laterFound] at starts
    rw [middleFound]
    revert starts
    cases state.validators.data[position]? <;> simp [startsExit, same]
  have fewer := Finset.sum_le_sum_of_subset (f := effectiveBalanceAtPosition state) sameExits
  -- A later slot only moves the first epoch on, which never lowers the potentials.
  have first : firstExitEpoch preset middle ≤ firstExitEpoch preset after := by
    unfold firstExitEpoch getCurrentEpoch computeEpochAtSlot
    have := UInt64.le_iff_toNat_le.mp quiet.slot
    rw [UInt64.toNat_div, UInt64.toNat_div]
    have := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat) this
    omega
  have exitMono := windowPotential_mono (cap := capExit) (largest := largest) (lower := lower)
    (upTo := upTo) (queuePotential_mono (earliestEpoch := middle.earliestExitEpoch electra)
      middleWithin.exitLeft first)
  have consolidationMono := windowPotential_mono (cap := capConsolidation) (largest := largest)
    (lower := lower) (upTo := upTo)
    (queuePotential_mono (earliestEpoch := middle.earliestConsolidationEpoch electra)
      middleWithin.consolidationLeft first)
  have := rises lower upTo
  simp only [statePotential, exitEpoch, exitLeft, consolidationEpoch,
    consolidationLeft] at this ⊢
  omega

theorem stepCharge_advanceSlot {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}
    (computed : advanceSlot config checks state = .ok after) :
    StepCharge config capExit capConsolidation largest electra state after := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, nextValue⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedKept : ChargedStep config capExit capConsolidation largest electra state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact .of_eq rfl
  -- The slot moves on by one at the end.
  have one : (1 : UInt64).toNat = 1 := rfl
  have bump : ∀ {middle : BeaconState preset fork}, middle.slot = state.slot →
      QuietStep middle epoched → QuietStep middle { epoched with slot := next } :=
    fun slot quiet => ⟨show _ ≤ next from slot ▸ UInt64.le_iff_toNat_le.mpr (by omega),
      quiet.size_le, quiet.exits, quiet.queues⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · unfold processEpoch at epochedOk
    split at epochedOk
    · rename_i altair
      unfold processEpochAltair at epochedOk
      simp only [bind_ok_iff] at epochedOk
      obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
        registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk,
        balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := epochedOk
      have resetKept :
          ChargedStep config capExit capConsolidation largest electra slashed reset := by
        split at resetOk
        · exact chargedStep_processEth1DataReset resetOk
        · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
          exact resetOk ▸ .refl _
      have paidKept : QuietStep pending paid := by
        split at paidOk
        · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure,
            Except.pure, Except.ok.injEq] at paidOk
          obtain ⟨_, _, rfl⟩ := paidOk
          exact .of_eq rfl
        · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
          exact paidOk ▸ .refl _
      have charged : ChargedStep config capExit capConsolidation largest electra state slashed :=
        cachedKept.trans <|
        (chargedStep_processJustificationAndFinalization justifiedOk).trans <|
        (chargedStep_processInactivityUpdates scoredOk).trans <|
        (chargedStep_processRewardsAndPenalties rewardedOk).trans <|
        (chargedStep_processRegistryUpdates registeredOk).trans
          (chargedStep_processSlashings slashedOk)
      have head : QuietStep reset mixed :=
        (quietStep_processPendingBalances pendingOk).trans <| paidKept.trans <|
        (quietStep_processEffectiveBalanceUpdates balancedOk).trans <|
        (quietStep_processSlashingsReset clearedOk).trans
          (quietStep_processRandaoMixesReset mixedOk)
      split at computed <;> simp only [bind_ok_iff] at computed <;>
        obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
      · have rootedKept : QuietStep mixed rooted := by
          unfold processHistoricalSummariesUpdate at rootedOk
          simp only [bind, Except.bind, pure, Except.pure] at rootedOk
          repeat' (split at rootedOk <;> try cases rootedOk)
          all_goals first
            | exact .refl _
            | exact .of_eq rfl
        exact (charged.trans resetKept).quiet <| bump (charged.trans resetKept).frozen.slot <|
          head.trans <| rootedKept.trans (quietStep_epochEnd syncedOk lookedOk windowed)
      · exact (charged.trans resetKept).quiet <| bump (charged.trans resetKept).frozen.slot <|
          head.trans <| (quietStep_processHistoricalRootsUpdate rootedOk).trans
            (quietStep_epochEnd syncedOk lookedOk windowed)
    · rename_i notAltair
      exact absurd (Nat.le_trans (by decide) electra) notAltair
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact cachedKept.quiet (bump cachedKept.frozen.slot (.refl _))

theorem stepCharge_applySignedBlock {capExit capConsolidation largest : Nat}
    {electra : .pectra ≤ fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : applySignedBlock config checks engine state signed validateResult = .ok after) :
    StepCharge config capExit capConsolidation largest electra state after :=
  (chargedStep_processBlock (applySignedBlock_ok computed).2.1).quiet (.refl _)

/-! ## Runs -/

/-- A later state, maybe of a later fork, whose registry is at least as long.

While it has fewer than `2^64` validators, each validator keeps its exit epoch, unless it had none.
-/
structure ExitsKept {fork' : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') : Prop where
  size_le : state.validators.data.size ≤ after.validators.data.size
  exits : after.validators.data.size < 2 ^ 64 → ∀ (position : Nat) (validator : Validator),
    state.validators.data[position]? = some validator → ∃ later,
      after.validators.data[position]? = some later ∧
        (later.exitEpoch = validator.exitEpoch ∨ validator.exitEpoch = FAR_FUTURE_EPOCH)

theorem ExitsKept.refl (state : BeaconState preset fork) : ExitsKept state state :=
  ⟨Nat.le_refl _, fun _ _ validator found => ⟨validator, found, .inl rfl⟩⟩

theorem ExitsKept.trans {fork' fork'' : Base.Fork} {first : BeaconState preset fork}
    {second : BeaconState preset fork'} {third : BeaconState preset fork''}
    (one : ExitsKept first second) (two : ExitsKept second third) : ExitsKept first third where
  size_le := Nat.le_trans one.size_le two.size_le
  exits small position validator found := by
    obtain ⟨middle, middleFound, oneKeeps⟩ :=
      one.exits (Nat.lt_of_le_of_lt two.size_le small) position validator found
    obtain ⟨later, laterFound, twoKeeps⟩ := two.exits small position middle middleFound
    refine ⟨later, laterFound, ?_⟩
    rcases oneKeeps with same | far
    · rcases twoKeeps with same' | far'
      · exact .inl (same'.trans same)
      · exact .inr (same ▸ far')
    · exact .inr far

/-- The validators that start to exit over two parts of a run.

Each starts in the first part, or in the second with a position of the first state. -/
theorem ExitsKept.sum_exitsBetween_le {fork' fork'' : Base.Fork} {first : BeaconState preset fork}
    {second : BeaconState preset fork'} {third : BeaconState preset fork''}
    (one : ExitsKept first second) (two : ExitsKept second third)
    (small : third.validators.data.size < 2 ^ 64) (weight : Nat → Nat) (lower upTo : Nat) :
    ∑ position ∈ exitsBetween first third lower upTo, weight position ≤
      ∑ position ∈ exitsBetween first second lower upTo, weight position +
        ∑ position ∈ (exitsBetween second third lower upTo).filter (· < first.validators.data.size),
          weight position := by
  have middleSmall := Nat.lt_of_le_of_lt two.size_le small
  have cover : exitsBetween first third lower upTo ⊆ exitsBetween first second lower upTo ∪
      (exitsBetween second third lower upTo).filter (· < first.validators.data.size) := by
    intro position member
    simp only [exitsBetween, Finset.mem_filter, Finset.mem_range] at member
    obtain ⟨inside, starts⟩ := member
    obtain ⟨validator, found⟩ : ∃ validator,
        first.validators.data[position]? = some validator :=
      ⟨_, Array.getElem?_eq_getElem inside⟩
    obtain ⟨middle, middleFound, oneKeeps⟩ := one.exits middleSmall position validator found
    obtain ⟨last, lastFound, twoKeeps⟩ := two.exits small position middle middleFound
    simp only [found, lastFound, startsExit, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at starts
    obtain ⟨⟨⟨far, set⟩, low⟩, within⟩ := starts
    by_cases started : middle.exitEpoch = FAR_FUTURE_EPOCH
    · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, inside⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_of_lt_of_le inside one.size_le), ?_⟩
      simp [middleFound, lastFound, startsExit, started, set, low, within]
    · have same : last.exitEpoch = middle.exitEpoch := twoKeeps.resolve_right started
      refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr inside, ?_⟩)
      simp [found, middleFound, startsExit, far, started, same ▸ low, same ▸ within]
  have union := Finset.sum_union_inter (s₁ := exitsBetween first second lower upTo)
    (s₂ := (exitsBetween second third lower upTo).filter (· < first.validators.data.size))
    (f := weight)
  calc _ ≤ _ := Finset.sum_le_sum_of_subset cover
    _ ≤ _ := Nat.le.intro union

theorem StepCharge.exitsKept {capExit capConsolidation largest : Nat} {electra : .pectra ≤ fork}
    (charge : StepCharge config capExit capConsolidation largest electra state after) :
    ExitsKept state after :=
  ⟨charge.size_le, charge.exits⟩

/-- The potentials of a forked state from Electra, and zero before it. -/
def forkedPotential (capExit capConsolidation largest lower upTo : Nat)
    (forked : ForkedBeaconState preset) :
    Nat :=
  if electra : .pectra ≤ forked.fork then
    statePotential capExit capConsolidation largest lower upTo forked.state electra
  else 0

/-- The churns of a forked state from Electra are within the caps.

Every effective balance is at most `largest`. -/
def ChurnsBounded (config : Config) (capExit capConsolidation largest : Nat)
    (forked : ForkedBeaconState preset) : Prop :=
  .pectra ≤ forked.fork →
    (∀ churn, exitChurnLimit config forked.state = .ok churn → churn.toNat ≤ capExit) ∧
      (∀ churn, getConsolidationChurnLimit config forked.state = .ok churn →
        churn.toNat ≤ capConsolidation) ∧
      ∀ (position : Nat) (validator : Validator),
        forked.state.validators.data[position]? = some validator →
          validator.effectiveBalance.toNat ≤ largest

/-- The churn left of both queues of a forked state is within the caps. -/
def LeftBounded (capExit capConsolidation : Nat) (forked : ForkedBeaconState preset) : Prop :=
  ∀ electra : .pectra ≤ forked.fork,
    (forked.state.exitBalanceToConsume electra).toNat ≤ capExit ∧
      (forked.state.consolidationBalanceToConsume electra).toNat ≤ capConsolidation

/-- A cap on every churn of exits, from a bound on the total active balance.

It takes the larger of two shares, one for the forks before Gloas and one for those from Gloas.

The quotients are `CHURN_LIMIT_QUOTIENT` and `CHURN_LIMIT_QUOTIENT_GLOAS`. -/
def exitCapOfTotal (config : Config) (total : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
    (max (total / config.CHURN_LIMIT_QUOTIENT.toNat)
      (total / config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat))

/-- A cap on every churn of consolidations, from a bound on the total active balance.

Before Gloas the churn of consolidations is a part of the whole churn.

From Gloas it is the share `CONSOLIDATION_CHURN_LIMIT_QUOTIENT`. -/
def consolidationCapOfTotal (config : Config) (total : Nat) : Nat :=
  max (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
      (total / config.CHURN_LIMIT_QUOTIENT.toNat))
    (total / config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat)

/-- A bound on the total active balance of a state bounds both of its churns, at every fork. -/
theorem ChurnsBounded.of_total {largest total : Nat} {forked : ForkedBeaconState preset}
    (totalLe : ∀ balance, getTotalActiveBalance forked.state = .ok balance →
      balance.toNat ≤ total)
    (effective : ∀ (position : Nat) (validator : Validator),
      forked.state.validators.data[position]? = some validator →
        validator.effectiveBalance.toNat ≤ largest) :
    ChurnsBounded config (exitCapOfTotal config total) (consolidationCapOfTotal config total)
      largest forked := by
  intro _
  refine ⟨fun churn computed => ?_, fun churn computed => ?_, effective⟩
  · obtain ⟨balance, balanceOk⟩ := exitChurnLimit_total computed
    have le := exitChurnLimit_le_total balanceOk computed
    have share := totalLe balance balanceOk
    -- A share of a smaller balance is no larger.
    have one := Nat.div_le_div_right (c := config.CHURN_LIMIT_QUOTIENT.toNat) share
    have two := Nat.div_le_div_right (c := config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat) share
    unfold exitCapOfTotal
    split at le <;> omega
  · obtain ⟨balance, balanceOk⟩ := getConsolidationChurnLimit_total computed
    have le := getConsolidationChurnLimit_le_total balanceOk computed
    have share := totalLe balance balanceOk
    have one := Nat.div_le_div_right (c := config.CHURN_LIMIT_QUOTIENT.toNat) share
    have two := Nat.div_le_div_right (c := config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat) share
    unfold consolidationCapOfTotal
    split at le <;> omega

/-- An upgrade from Electra on keeps the registry, the slot and both queues. -/
theorem upgradeNext_keeps {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork) (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.validators.data = pre.state.validators.data ∧
      post.val.state.slot = pre.state.slot ∧
      ∀ electra' : .pectra ≤ post.val.fork,
        post.val.state.earliestExitEpoch electra' = pre.state.earliestExitEpoch electra ∧
          post.val.state.exitBalanceToConsume electra' = pre.state.exitBalanceToConsume electra ∧
          post.val.state.earliestConsolidationEpoch electra' =
            pre.state.earliestConsolidationEpoch electra ∧
          post.val.state.consolidationBalanceToConsume electra' =
            pre.state.consolidationBalanceToConsume electra := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  all_goals try exact absurd electra (by simp only; decide)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    exact ⟨rfl, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨_, upgraded, rfl⟩ := computed
    have lists := (upgradeToGloas_spec upgraded).1
    simp only [upgradeToGloas, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, onboarded⟩ := upgraded
    obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    exact ⟨lists, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact ⟨(upgradeHezeFields_lists _).1, rfl, fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

/-- The fork of a run's end is at least that of its start. -/
theorem Run.fork_le {start : ForkedBeaconState preset} :
    ∀ {after : ForkedBeaconState preset}, Run config checks start after → start.fork ≤ after.fork
  | _, .nil => Nat.le_refl _
  | _, .snoc run step => by
    have before := Run.fork_le run
    cases step with
    | slot _ _ => exact before
    | @upgrade _ post _ _ => exact Nat.le_trans before (Nat.le_of_lt post.property)
    | block _ _ _ _ _ => exact before

/-- The facts of `Run.exitCharge` for a run, at its end. -/
def ExitChargeAt (capExit capConsolidation largest : Nat) (weight : Nat → Nat)
    (start after : ForkedBeaconState preset) : Prop :=
  start.fork ≤ after.fork ∧ ExitsKept start.state after.state ∧
    LeftBounded capExit capConsolidation after ∧ ∀ lower upTo,
      ∑ position ∈ exitsBetween start.state after.state lower upTo, weight position +
          forkedPotential capExit capConsolidation largest lower upTo start ≤
        forkedPotential capExit capConsolidation largest lower upTo after

/-- One more slot or block after a run. -/
private theorem ExitChargeAt.charge {capExit capConsolidation largest : Nat} {weight : Nat → Nat}
    {start : ForkedBeaconState preset} {middle after : BeaconState preset fork}
    (electra : .pectra ≤ fork)
    (before : ExitChargeAt capExit capConsolidation largest weight start ⟨fork, middle⟩)
    (charge : StepCharge config capExit capConsolidation largest electra middle after)
    (small : after.validators.data.size < 2 ^ 64)
    (churns : ChurnsBounded config capExit capConsolidation largest ⟨fork, middle⟩)
    (weightLe : ∀ position < start.state.validators.data.size,
      weight position ≤ effectiveBalanceAtPosition middle position) :
    ExitChargeAt capExit capConsolidation largest weight start ⟨fork, after⟩ := by
  obtain ⟨forkLe, kept, lefts, rises⟩ := before
  have within : ChurnsWithin config capExit capConsolidation largest middle electra :=
    ⟨(churns electra).1, (churns electra).2.1, (lefts electra).1, (lefts electra).2,
      (churns electra).2.2⟩
  obtain ⟨exitLeft, consolidationLeft, charged⟩ := charge.charged small within
  refine ⟨forkLe, kept.trans charge.exitsKept, fun _ => ⟨exitLeft, consolidationLeft⟩,
    fun lower upTo => ?_⟩
  have split := kept.sum_exitsBetween_le charge.exitsKept small weight lower upTo
  -- Each validator of the start that starts to exit in this step weighs at most its balance.
  have weighed : ∑ position ∈ (exitsBetween middle after lower upTo).filter
        (· < start.state.validators.data.size), weight position ≤
      ∑ position ∈ exitsBetween middle after lower upTo,
        effectiveBalanceAtPosition middle position :=
    (Finset.sum_le_sum fun position member =>
      weightLe position (Finset.mem_filter.mp member).2).trans
      (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
  have step := charged lower upTo
  have rise := rises lower upTo
  simp only [forkedPotential, electra, ↓reduceDIte] at rise ⊢
  dsimp only at split rise weighed ⊢
  omega

/-- One more upgrade after a run from Electra on. -/
private theorem ExitChargeAt.upgrade {capExit capConsolidation largest : Nat} {weight : Nat → Nat}
    {start pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork)
    (before : ExitChargeAt capExit capConsolidation largest weight start pre)
    (computed : upgradeNext config checks pre = .ok post) :
    ExitChargeAt capExit capConsolidation largest weight start post.val := by
  obtain ⟨forkLe, kept, lefts, rises⟩ := before
  obtain ⟨validators, slot, queues⟩ := upgradeNext_keeps electra computed
  have electra' : .pectra ≤ post.val.fork := Nat.le_trans electra (Nat.le_of_lt post.property)
  obtain ⟨exitEpoch, exitLeft, consolidationEpoch, consolidationLeft⟩ := queues electra'
  refine ⟨Nat.le_trans forkLe (Nat.le_of_lt post.property),
    ⟨by rw [validators]; exact kept.size_le, by rw [validators]; exact kept.exits⟩,
    fun _ => ⟨exitLeft ▸ (lefts electra).1, consolidationLeft ▸ (lefts electra).2⟩,
    fun lower upTo => ?_⟩
  have exits : exitsBetween start.state post.val.state lower upTo =
      exitsBetween start.state pre.state lower upTo := by
    simp only [exitsBetween, validators]
  have first : firstExitEpoch preset post.val.state = firstExitEpoch preset pre.state := by
    simp only [firstExitEpoch, getCurrentEpoch, slot]
  have rise := rises lower upTo
  simp only [forkedPotential, electra, electra', ↓reduceDIte, statePotential, first,
    exitEpoch, exitLeft, consolidationEpoch, consolidationLeft, exits] at rise ⊢
  exact rise

/-- The stake that starts to exit over a run from Electra on, bounded by the rise in potential.

Take caps on the churns of every state of the run, and on the churn left at its start.

Weigh each validator of the first state by at most its effective balance in every state of the run.

Count those that start to exit, with an exit epoch up to some epoch.

Their weight, plus the potentials up to that epoch at the start, is at most those at the end.

The churn left stays within the caps.

This holds while the registry has fewer than `2^64` validators. -/
theorem Run.exitCharge {capExit capConsolidation largest : Nat} {start : ForkedBeaconState preset}
    (electra : .pectra ≤ start.fork) (weight : Nat → Nat) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      after.state.validators.data.size < 2 ^ 64 →
      (∀ forked ∈ run.states, ChurnsBounded config capExit capConsolidation largest forked) →
      LeftBounded capExit capConsolidation start →
      (∀ forked ∈ run.states, ∀ position < start.state.validators.data.size,
        weight position ≤ effectiveBalanceAtPosition forked.state position) →
      ExitChargeAt capExit capConsolidation largest weight start after
  | _, .nil, _, _, lefts, _ =>
    ⟨Nat.le_refl _, .refl _, lefts, fun lower upTo => by simp [exitsBetween_self]⟩
  | _, .snoc (middle := middle) run step, small, churns, lefts, weightLe => by
    have electraMiddle : .pectra ≤ middle.fork := Nat.le_trans electra (Run.fork_le run)
    have middleIn : middle ∈ (Run.snoc run step).states :=
      List.mem_append_left _ (Run.end_mem_states run)
    have earlier : ∀ forked ∈ run.states, forked ∈ (Run.snoc run step).states :=
      fun _ member => List.mem_append_left _ member
    -- The run up to the middle state, whose registry is at most as long as the last one.
    have before := fun (middleSmall : middle.state.validators.data.size < 2 ^ 64) =>
      Run.exitCharge electra weight run middleSmall (fun forked member => churns forked
        (earlier forked member)) lefts
        (fun forked member => weightLe forked (earlier forked member))
    cases step with
    | slot _ computed =>
      have charge := stepCharge_advanceSlot (capExit := capExit)
        (capConsolidation := capConsolidation) (largest := largest) (electra := electraMiddle)
        computed
      exact (before (Nat.lt_of_le_of_lt charge.size_le small)).charge electraMiddle charge small
        (churns _ middleIn) (weightLe _ middleIn)
    | block _ _ _ _ computed =>
      have charge := stepCharge_applySignedBlock (capExit := capExit)
        (capConsolidation := capConsolidation) (largest := largest) (electra := electraMiddle)
        computed
      exact (before (Nat.lt_of_le_of_lt charge.size_le small)).charge electraMiddle charge small
        (churns _ middleIn) (weightLe _ middleIn)
    | upgrade _ computed =>
      have same := (upgradeNext_keeps electraMiddle computed).1
      exact (before (by rw [← same]; exact small)).upgrade electraMiddle computed

/-! ## The balance each exit spends -/

/-- Whether a validator has no exit epoch in one state and has one in another. -/
def startedExit (before later : Option Validator) : Bool :=
  match before, later with
  | some validator, some later =>
    validator.exitEpoch == FAR_FUTURE_EPOCH && later.exitEpoch != FAR_FUTURE_EPOCH
  | _, _ => false

/-- The effective balance with which a validator started to exit over a run, and zero otherwise.

It is the balance at the start of the step that set its exit epoch.

Within a slot or a block no effective balance changes before an exit, so the exit spent it. -/
def Run.chargedBalance {start : ForkedBeaconState preset} :
    {after : ForkedBeaconState preset} → Run config checks start after → Nat → Nat
  | _, .nil, _ => 0
  | after, .snoc (middle := middle) run _, position =>
    if startedExit middle.state.validators.data[position]? after.state.validators.data[position]?
    then effectiveBalanceAtPosition middle.state position
    else run.chargedBalance position

/-- A validator that starts to exit has no exit epoch in the first state and one in the second. -/
theorem startsExit_eq_true {before later : Option Validator} {lower upTo : Nat}
    (starts : startsExit before later lower upTo = true) :
    ∃ validator later', before = some validator ∧ later = some later' ∧
      validator.exitEpoch = FAR_FUTURE_EPOCH ∧ later'.exitEpoch ≠ FAR_FUTURE_EPOCH := by
  cases before <;> cases later <;> simp_all [startsExit]

theorem mem_exitsBetween {fork' : Base.Fork} {state : BeaconState preset fork}
    {after : BeaconState preset fork'} {lower upTo position : Nat} :
    position ∈ exitsBetween state after lower upTo ↔
      position < state.validators.data.size ∧
        startsExit state.validators.data[position]? after.validators.data[position]? lower upTo =
          true := by
  simp [exitsBetween]

/-- One more slot or block after a run, with a new weight for the validators it starts to exit.

The weight stays the same on validators that already have an exit epoch.

On the others it is at most the effective balance at the start of the step. -/
private theorem ExitChargeAt.charge_with {capExit capConsolidation largest : Nat}
    {weight weight' : Nat → Nat} {start : ForkedBeaconState preset}
    {middle after : BeaconState preset fork} (electra : .pectra ≤ fork)
    (before : ExitChargeAt capExit capConsolidation largest weight start ⟨fork, middle⟩)
    (charge : StepCharge config capExit capConsolidation largest electra middle after)
    (small : after.validators.data.size < 2 ^ 64)
    (churns : ChurnsBounded config capExit capConsolidation largest ⟨fork, middle⟩)
    (same : ∀ (position : Nat) (validator : Validator),
      middle.validators.data[position]? = some validator →
        validator.exitEpoch ≠ FAR_FUTURE_EPOCH → weight' position = weight position)
    (fresh : ∀ (position : Nat) (validator later : Validator),
      middle.validators.data[position]? = some validator →
        after.validators.data[position]? = some later →
        validator.exitEpoch = FAR_FUTURE_EPOCH → later.exitEpoch ≠ FAR_FUTURE_EPOCH →
          weight' position ≤ effectiveBalanceAtPosition middle position) :
    ExitChargeAt capExit capConsolidation largest weight' start ⟨fork, after⟩ := by
  obtain ⟨forkLe, kept, lefts, rises⟩ := before
  have within : ChurnsWithin config capExit capConsolidation largest middle electra :=
    ⟨(churns electra).1, (churns electra).2.1, (lefts electra).1, (lefts electra).2,
      (churns electra).2.2⟩
  obtain ⟨exitLeft, consolidationLeft, charged⟩ := charge.charged small within
  refine ⟨forkLe, kept.trans charge.exitsKept, fun _ => ⟨exitLeft, consolidationLeft⟩,
    fun lower upTo => ?_⟩
  have split := kept.sum_exitsBetween_le charge.exitsKept small weight' lower upTo
  -- Those that started to exit before this step keep their weight.
  have earlier : ∑ position ∈ exitsBetween start.state middle lower upTo, weight' position =
      ∑ position ∈ exitsBetween start.state middle lower upTo, weight position := by
    refine Finset.sum_congr rfl fun position member => ?_
    obtain ⟨_, starts⟩ := mem_exitsBetween.mp member
    obtain ⟨_, later, _, found, _, set⟩ := startsExit_eq_true starts
    exact same position later found set
  -- Those that start in this step weigh at most their balance at its start.
  have weighed : ∑ position ∈ (exitsBetween middle after lower upTo).filter
        (· < start.state.validators.data.size), weight' position ≤
      ∑ position ∈ exitsBetween middle after lower upTo,
        effectiveBalanceAtPosition middle position := by
    refine (Finset.sum_le_sum fun position member => ?_).trans
      (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    obtain ⟨_, starts⟩ := mem_exitsBetween.mp (Finset.mem_filter.mp member).1
    obtain ⟨validator, later, found, laterFound, far, set⟩ := startsExit_eq_true starts
    exact fresh position validator later found laterFound far set
  have step := charged lower upTo
  have rise := rises lower upTo
  simp only [forkedPotential, electra, ↓reduceDIte] at rise ⊢
  dsimp only at split rise weighed earlier ⊢
  omega

/-- The weights that a run gives its exits, along the run.

Each validator that starts to exit, by the end of a run, weighs the balance it spent. -/
theorem Run.exitCharge_charged {capExit capConsolidation largest : Nat}
    {start : ForkedBeaconState preset} (electra : .pectra ≤ start.fork) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      after.state.validators.data.size < 2 ^ 64 →
      (∀ forked ∈ run.states, ChurnsBounded config capExit capConsolidation largest forked) →
      LeftBounded capExit capConsolidation start →
      ExitChargeAt capExit capConsolidation largest run.chargedBalance start after
  | _, .nil, _, _, lefts =>
    ⟨Nat.le_refl _, .refl _, lefts, fun lower upTo => by simp [exitsBetween_self]⟩
  | after, .snoc (middle := middle) run step, small, churns, lefts => by
    have electraMiddle : .pectra ≤ middle.fork := Nat.le_trans electra (Run.fork_le run)
    have middleIn : middle ∈ (Run.snoc run step).states :=
      List.mem_append_left _ (Run.end_mem_states run)
    have earlier : ∀ forked ∈ run.states, forked ∈ (Run.snoc run step).states :=
      fun _ member => List.mem_append_left _ member
    have before := fun (middleSmall : middle.state.validators.data.size < 2 ^ 64) =>
      Run.exitCharge_charged electra run middleSmall
        (fun forked member => churns forked (earlier forked member)) lefts
    -- The new weight reads the step: a validator it starts to exit weighs its balance before it.
    have same : ∀ (position : Nat) (validator : Validator),
        middle.state.validators.data[position]? = some validator →
          validator.exitEpoch ≠ FAR_FUTURE_EPOCH →
            (Run.snoc run step).chargedBalance position = run.chargedBalance position := by
      intro position validator found set
      simp only [Run.chargedBalance, found]
      split
      · rename_i started
        unfold startedExit at started
        split at started <;> simp_all
      · rfl
    have fresh : ∀ (position : Nat) (validator later : Validator),
        middle.state.validators.data[position]? = some validator →
          after.state.validators.data[position]? = some later →
          validator.exitEpoch = FAR_FUTURE_EPOCH → later.exitEpoch ≠ FAR_FUTURE_EPOCH →
            (Run.snoc run step).chargedBalance position ≤
              effectiveBalanceAtPosition middle.state position := by
      intro position validator later found laterFound far set
      simp [Run.chargedBalance, found, laterFound, startedExit, far, set]
    cases step with
    | slot _ computed =>
      have charge := stepCharge_advanceSlot (capExit := capExit)
        (capConsolidation := capConsolidation) (largest := largest) (electra := electraMiddle)
        computed
      exact (before (Nat.lt_of_le_of_lt charge.size_le small)).charge_with electraMiddle charge
        small (churns _ middleIn) same fresh
    | block _ _ _ _ computed =>
      have charge := stepCharge_applySignedBlock (capExit := capExit)
        (capConsolidation := capConsolidation) (largest := largest) (electra := electraMiddle)
        computed
      exact (before (Nat.lt_of_le_of_lt charge.size_le small)).charge_with electraMiddle charge
        small (churns _ middleIn) same fresh
    | upgrade _ computed =>
      have keeps := upgradeNext_keeps electraMiddle computed
      -- An upgrade starts no exit, so the weights stay.
      have weights : (Run.snoc run (.upgrade ‹_› computed)).chargedBalance =
          run.chargedBalance := by
        funext position
        simp only [Run.chargedBalance, keeps.1]
        cases middle.state.validators.data[position]? <;> simp [startedExit]
      rw [weights]
      exact (before (by rw [← keeps.1]; exact small)).upgrade electraMiddle computed

/-- A queue's potential counts at least every epoch before the first one a new request may take.
-/
theorem le_queuePotential {cap first : Nat} {earliestEpoch : Epoch} {churnLeft : Gwei}
    (leftLe : churnLeft.toNat ≤ cap) :
    first * cap ≤ queuePotential cap first earliestEpoch churnLeft := by
  unfold queuePotential
  split
  · exact Nat.le_refl _
  · have := Nat.mul_le_mul_right cap (Nat.le_of_not_lt ‹_›)
    omega

/-- The spend from epoch zero is the potential up to the range's end, plus `largest`. -/
theorem windowPotential_zero (cap largest upTo potential : Nat) :
    windowPotential cap largest 0 upTo potential = min potential ((upTo + 1) * cap) + largest := by
  simp [windowPotential]

/-- The effective stake that starts to exit over a run from Electra on, up to an epoch.

Each such exit leaves at `upTo` or before.

Each queue takes at most one cap per epoch, up to `upTo`.

The count starts at the first epoch a new exit may take at the start of the run.

The rest is the effective balance at the start above the balance each exit spent.

That part is a loss of effective balance before the exit started, which the churn does not see.

The caps bound the churns of every state of the run, and the churn left at its start.

`largest` bounds every effective balance of the run.

This holds while the registry has fewer than `2^64` validators. -/
theorem Run.exitingStake_le {capExit capConsolidation largest : Nat}
    {start after : ForkedBeaconState preset} (electra : .pectra ≤ start.fork)
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    (churns : ∀ forked ∈ run.states, ChurnsBounded config capExit capConsolidation largest forked)
    (lefts : LeftBounded capExit capConsolidation start) (upTo : Nat) :
    ∑ position ∈ exitsBetween start.state after.state 0 upTo,
        effectiveBalanceAtPosition start.state position ≤
      (upTo + 1 - firstExitEpoch preset start.state) * (capExit + capConsolidation) +
        ∑ position ∈ exitsBetween start.state after.state 0 upTo,
          (effectiveBalanceAtPosition start.state position - run.chargedBalance position) := by
  obtain ⟨forkLe, _, _, rises⟩ := Run.exitCharge_charged electra run small churns lefts
  have rise := rises 0 upTo
  have electra' : .pectra ≤ after.fork := Nat.le_trans electra forkLe
  simp only [forkedPotential, electra, electra', ↓reduceDIte, statePotential,
    windowPotential_zero] at rise
  -- At the start each queue has spent every epoch before the first one a new exit may take.
  have exitStart := le_queuePotential (first := firstExitEpoch preset start.state)
    (earliestEpoch := start.state.earliestExitEpoch electra) (lefts electra).1
  have consolidationStart := le_queuePotential (first := firstExitEpoch preset start.state)
    (earliestEpoch := start.state.earliestConsolidationEpoch electra) (lefts electra).2
  -- From there to the end of the range, each queue spends at most one cap per epoch.
  have exitRange : (upTo + 1) * capExit -
      min (firstExitEpoch preset start.state * capExit) ((upTo + 1) * capExit) ≤
        (upTo + 1 - firstExitEpoch preset start.state) * capExit := by
    rw [Nat.sub_mul]
    omega
  have consolidationRange : (upTo + 1) * capConsolidation -
      min (firstExitEpoch preset start.state * capConsolidation)
        ((upTo + 1) * capConsolidation) ≤
        (upTo + 1 - firstExitEpoch preset start.state) * capConsolidation := by
    rw [Nat.sub_mul]
    omega
  have split : ∑ position ∈ exitsBetween start.state after.state 0 upTo,
        effectiveBalanceAtPosition start.state position ≤
      ∑ position ∈ exitsBetween start.state after.state 0 upTo, run.chargedBalance position +
        ∑ position ∈ exitsBetween start.state after.state 0 upTo,
          (effectiveBalanceAtPosition start.state position - run.chargedBalance position) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun _ _ => by omega
  rw [Nat.mul_add]
  omega

/-- Along a run from Electra on, a validator keeps its exit epoch once it has one.

The registry only grows.

This holds while the registry has fewer than `2^64` validators. -/
theorem Run.exitsKept {start after : ForkedBeaconState preset} (electra : .pectra ≤ start.fork)
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64) :
    ExitsKept start.state after.state := by
  -- Caps of `2^64` bound every churn, churn left and effective balance.
  refine (Run.exitCharge_charged (capExit := 2 ^ 64) (capConsolidation := 2 ^ 64)
    (largest := 2 ^ 64) electra run small (fun _ _ _ => ⟨fun churn _ => Nat.le_of_lt churn.toNat_lt,
      fun churn _ => Nat.le_of_lt churn.toNat_lt,
      fun _ validator _ => Nat.le_of_lt validator.effectiveBalance.toNat_lt⟩)
    (fun _ => ⟨Nat.le_of_lt (UInt64.toNat_lt _), Nat.le_of_lt (UInt64.toNat_lt _)⟩)).2.1

/-! ## The stake that leaves the active set -/

/-- A sum over the positions of a list filter is a sum over the matching finite set. -/
theorem sum_map_filter_range (size : Nat) (test : Nat → Bool) (value : Nat → Nat) :
    (((List.range size).filter test).map value).sum =
      ∑ position ∈ (Finset.range size).filter (fun position => test position = true),
        value position := by
  simp only [Finset.sum, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.map_coe, Multiset.sum_coe, Bool.decide_eq_true]

/-- The stake that leaves the active set over a run from Electra on.

Take the validators active at the current epoch of the first state, and not at that of the last.

Their effective balance in the first state is at most that of two groups.

- Those that already have an exit epoch in the first state, up to the last state's epoch.
- Those that start to exit over the run, up to the last state's epoch.

The first group is read from the first state.

`Run.exitingStake_le` bounds the second.

A validator active in the first state must keep its activation epoch.

The lifecycle of validators gives that.

The last state's epoch must be at least the first's and below the far future epoch.

This holds while the registry has fewer than `2^64` validators. -/
theorem Run.leavingStake_le {start after : ForkedBeaconState preset}
    (electra : .pectra ≤ start.fork) (run : Run config checks start after)
    (small : after.state.validators.data.size < 2 ^ 64)
    (epochs : getCurrentEpoch start.state ≤ getCurrentEpoch after.state)
    (finite : getCurrentEpoch after.state < FAR_FUTURE_EPOCH)
    (activations : ∀ (position : Nat) (validator later : Validator),
      start.state.validators.data[position]? = some validator →
        after.state.validators.data[position]? = some later →
        isActiveValidator validator (getCurrentEpoch start.state) = true →
          later.activationEpoch = validator.activationEpoch) :
    (((List.range start.state.validators.data.size).filter fun position =>
        (start.state.validators.data[position]?).any
            (isActiveValidator · (getCurrentEpoch start.state)) &&
          !(after.state.validators.data[position]?).any
            (isActiveValidator · (getCurrentEpoch after.state))).map
        fun position => effectiveBalanceAtPosition start.state position).sum ≤
      (((List.range start.state.validators.data.size).filter fun position =>
          (start.state.validators.data[position]?).any fun validator =>
            isActiveValidator validator (getCurrentEpoch start.state) &&
              decide (validator.exitEpoch ≤ getCurrentEpoch after.state)).map
          fun position => effectiveBalanceAtPosition start.state position).sum +
        ∑ position ∈ exitsBetween start.state after.state 0 (getCurrentEpoch after.state).toNat,
          effectiveBalanceAtPosition start.state position := by
  rw [sum_map_filter_range, sum_map_filter_range]
  have kept := Run.exitsKept electra run small
  -- Each leaving validator is queued at the start, or starts to exit over the run.
  refine (Finset.sum_le_sum_of_subset (fun position member => ?_)).trans
    (Nat.le.intro Finset.sum_union_inter)
  obtain ⟨inside, leaves⟩ := Finset.mem_filter.mp member
  have inside := Finset.mem_range.mp inside
  obtain ⟨validator, found⟩ : ∃ validator,
      start.state.validators.data[position]? = some validator :=
    ⟨_, Array.getElem?_eq_getElem inside⟩
  obtain ⟨later, laterFound, exits⟩ := kept.exits small position validator found
  simp only [found, laterFound, Option.any_some, Bool.and_eq_true, Bool.not_eq_true'] at leaves
  obtain ⟨active, inactive⟩ := leaves
  have same := activations position validator later found laterFound active
  -- The validator is active then not, with the same activation epoch, so it left by then.
  have left : later.exitEpoch ≤ getCurrentEpoch after.state := by
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at active inactive
    rcases inactive with notActivated | notBefore
    · exact absurd (same ▸ UInt64.le_trans active.1 epochs) notActivated
    · exact UInt64.not_lt.mp notBefore
  rcases exits with sameExit | far
  · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr inside, ?_⟩)
    simp [found, active, sameExit ▸ left]
  · refine Finset.mem_union_right _ (mem_exitsBetween.mpr ⟨inside, ?_⟩)
    have set : later.exitEpoch ≠ FAR_FUTURE_EPOCH := fun same =>
      absurd (same ▸ left) (UInt64.not_le.mpr finite)
    simp [found, laterFound, startsExit, far, set, UInt64.le_iff_toNat_le.mp left]

end EthLib.Consensus
