module

public import EthLib.Consensus.Proofs.Transition.EpochJustification

/-!
# Proofs: where the justification bits and checkpoints come from

Casper FFG justifies a checkpoint when a supermajority link reaches it.

The beacon chain approximates that rule once per epoch, in one weighing call.

The call compares two balances: the target balance of an epoch and the total active balance.

```text
    justified  iff  2 * total <= 3 * target
```

This file states exactly what one call does, without rounding the test to "two thirds".

Two details of the concrete rule matter for any model built on top of it.

- Each balance is at least one increment, `EFFECTIVE_BALANCE_INCREMENT`.
  A sum below it counts as one increment.
- The two balances sum over different sets of validators.
  The total sums the validators active in the current epoch.
  The target sums the unslashed voters, who need not be active in the current epoch.

So each statement gives the two index sets and the two raw sums, and the floor, separately.

The new bits are the old ones moved one place, with the newest two set by the test.

The finalized checkpoint changes only by one of four rules, each reading three or two bits.

Casper FFG is the paper by Buterin and Griffith, arXiv:1710.09437.

Gasper, arXiv:2003.03052 §4, describes the epoch-boundary rule that this call implements.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-! ## One weighing call -/

/-- A rule of finalization fires when its bits are set and its source is `gap` epochs back. -/
theorem finalizes_ok {justified : Bool} {source gap currentEpoch : Epoch} {result : Bool}
    (computed : finalizes justified source gap currentEpoch = .ok result) :
    result = (justified && decide (source.toNat + gap.toNat = currentEpoch.toNat)) := by
  cases justified
  · simp only [finalizes, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at computed
    subst computed
    rfl
  · simp only [finalizes, ↓reduceIte, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨sum, ⟨_, sumEq⟩, rfl⟩ := computed
    rw [Bool.true_and, ← sumEq, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff,
      UInt64.toNat_inj]

/-- A justified epoch gets the checkpoint of its first block, read from the block roots. -/
theorem justifyCheckpoint_eq {justified : Bool} {epoch : Epoch} {checkpoint result : Checkpoint}
    (computed : justifyCheckpoint state justified epoch checkpoint = .ok result) :
    if justified then ∃ root, getBlockRoot state epoch = .ok root ∧ result = ⟨epoch, root⟩
    else result = checkpoint := by
  cases justified
  · simp only [justifyCheckpoint, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at computed ⊢
    exact computed.symm
  · simp only [justifyCheckpoint, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at computed ⊢
    obtain ⟨root, rootOk, rfl⟩ := computed
    exact ⟨root, rootOk, rfl⟩

/-- What one weighing call does, bit by bit and checkpoint by checkpoint.

The tests compare natural numbers: the products cannot overflow, or the call fails.

- The newest bit says whether the current epoch passed the test.
- The next bit says whether the previous epoch passed it now, or had passed it a call ago.
- The two oldest bits are the old bits moved one place.

The new current justified checkpoint is that of the current epoch if it passed the test.

Otherwise it is that of the previous epoch if it passed, and otherwise it stays.

Its root is the root that the state holds for the first slot of its epoch.

The finalized checkpoint follows the four rules, read on the new bits.

Nothing else in the state changes. -/
theorem weighJustificationAndFinalization_eq {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after) :
    2 * total.toNat < 2 ^ 64 ∧ 3 * previous.toNat < 2 ^ 64 ∧ 3 * current.toNat < 2 ^ 64 ∧
      after.justificationBits.bits[0] = decide (2 * total.toNat ≤ 3 * current.toNat) ∧
      after.justificationBits.bits[1] =
        (decide (2 * total.toNat ≤ 3 * previous.toNat) || state.justificationBits.bits[0]) ∧
      after.justificationBits.bits[2] = state.justificationBits.bits[1] ∧
      after.justificationBits.bits[3] = state.justificationBits.bits[2] ∧
      after.previousJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
      (if 2 * total.toNat ≤ 3 * current.toNat then
        ∃ root, getBlockRoot state (getCurrentEpoch state) = .ok root ∧
          after.currentJustifiedCheckpoint = ⟨getCurrentEpoch state, root⟩
      else if 2 * total.toNat ≤ 3 * previous.toNat then
        ∃ root, getBlockRoot state (getPreviousEpoch state) = .ok root ∧
          after.currentJustifiedCheckpoint = ⟨getPreviousEpoch state, root⟩
      else after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint) ∧
      after.finalizedCheckpoint =
        (if (after.justificationBits.bits[0] && after.justificationBits.bits[1] &&
              after.justificationBits.bits[2] &&
              decide (state.currentJustifiedCheckpoint.epoch.toNat + 2 =
                (getCurrentEpoch state).toNat)) ||
            (after.justificationBits.bits[0] && after.justificationBits.bits[1] &&
              decide (state.currentJustifiedCheckpoint.epoch.toNat + 1 =
                (getCurrentEpoch state).toNat)) then
          state.currentJustifiedCheckpoint
        else if (after.justificationBits.bits[1] && after.justificationBits.bits[2] &&
              after.justificationBits.bits[3] &&
              decide (state.previousJustifiedCheckpoint.epoch.toNat + 3 =
                (getCurrentEpoch state).toNat)) ||
            (after.justificationBits.bits[1] && after.justificationBits.bits[2] &&
              decide (state.previousJustifiedCheckpoint.epoch.toNat + 2 =
                (getCurrentEpoch state).toNat)) then
          state.previousJustifiedCheckpoint
        else state.finalizedCheckpoint) ∧
      { after with
        previousJustifiedCheckpoint := state.previousJustifiedCheckpoint,
        currentJustifiedCheckpoint := state.currentJustifiedCheckpoint,
        justificationBits := state.justificationBits,
        finalizedCheckpoint := state.finalizedCheckpoint } = state := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, mulChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨previousWeight, ⟨previousFits, previousEq⟩, threshold, ⟨thresholdFits, thresholdEq⟩,
    first, firstOk, currentWeight, ⟨currentFits, currentEq⟩, second, secondOk,
    old3, old3Ok, old2, old2Ok, cur2, cur2Ok, cur1, cur1Ok, rfl⟩ := computed
  have two : (2 : UInt64).toNat = 2 := rfl
  have three : (3 : UInt64).toNat = 3 := rfl
  -- Each test on 64-bit words is the same test on natural numbers.
  have previousTest : decide (threshold ≤ previousWeight) =
      decide (2 * total.toNat ≤ 3 * previous.toNat) := by
    apply decide_eq_decide.mpr
    rw [UInt64.le_iff_toNat_le, thresholdEq, previousEq, two, three]
    omega
  have currentTest : decide (threshold ≤ currentWeight) =
      decide (2 * total.toNat ≤ 3 * current.toNat) := by
    apply decide_eq_decide.mpr
    rw [UInt64.le_iff_toNat_le, thresholdEq, currentEq, two, three]
    omega
  rw [three] at previousFits currentFits
  rw [two] at thresholdFits
  simp only [previousTest, currentTest] at *
  rw [finalizes_ok old3Ok, finalizes_ok old2Ok, finalizes_ok cur2Ok, finalizes_ok cur1Ok]
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_, by first | rfl | trivial, ?_, ?_,
    by first | rfl | trivial⟩
  · simp
  · simp [shiftJustificationBits]
  · simp [shiftJustificationBits]
  · simp [shiftJustificationBits]
  · have firstEq := justifyCheckpoint_eq firstOk
    have secondEq := justifyCheckpoint_eq secondOk
    by_cases currentPass : 2 * total.toNat ≤ 3 * current.toNat
    · simp only [currentPass, decide_true, ↓reduceIte] at secondEq ⊢
      exact secondEq
    · simp only [currentPass, decide_false, Bool.false_eq_true, ↓reduceIte] at secondEq ⊢
      subst secondEq
      by_cases previousPass : 2 * total.toNat ≤ 3 * previous.toNat
      · simp only [previousPass, decide_true, ↓reduceIte] at firstEq ⊢
        exact firstEq
      · simp only [previousPass, decide_false, Bool.false_eq_true, ↓reduceIte] at firstEq ⊢
        exact firstEq
  · rfl

/-- An epoch that passes the test at a weighing call has its first block root read by the call.

That holds for the previous epoch even when the current one passes too and overwrites it. -/
theorem weighJustificationAndFinalization_roots {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after) :
    (2 * total.toNat ≤ 3 * previous.toNat →
        ∃ root, getBlockRoot state (getPreviousEpoch state) = .ok root) ∧
      (2 * total.toNat ≤ 3 * current.toNat →
        ∃ root, getBlockRoot state (getCurrentEpoch state) = .ok root) := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, mulChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨previousWeight, ⟨_, previousEq⟩, threshold, ⟨_, thresholdEq⟩, first, firstOk,
    currentWeight, ⟨_, currentEq⟩, second, secondOk, -⟩ := computed
  have two : (2 : UInt64).toNat = 2 := rfl
  have three : (3 : UInt64).toNat = 3 := rfl
  refine ⟨fun passes => ?_, fun passes => ?_⟩
  · have test : threshold ≤ previousWeight := by
      rw [UInt64.le_iff_toNat_le, thresholdEq, previousEq, two, three]
      omega
    have read := justifyCheckpoint_eq firstOk
    simp only [test, decide_true, ↓reduceIte] at read
    obtain ⟨root, rootOk, -⟩ := read
    exact ⟨root, rootOk⟩
  · have test : threshold ≤ currentWeight := by
      rw [UInt64.le_iff_toNat_le, thresholdEq, currentEq, two, three]
      omega
    have read := justifyCheckpoint_eq secondOk
    simp only [test, decide_true, ↓reduceIte] at read
    obtain ⟨root, rootOk, -⟩ := read
    exact ⟨root, rootOk⟩

/-! ## The weighing at an epoch boundary -/

/-- The voters for the first block of an epoch that a weighing counts, by the rule of the fork.

Before Altair they are the unslashed signers of the pending attestations with that target.

From Altair they are the unslashed active validators with the timely target flag of the epoch.

The list is a set: sorted, each index once. -/
def TargetVoters (state : BeaconState preset fork) (epoch : Epoch)
    (voters : List ValidatorIndex) : Prop :=
  if altair : .altair ≤ fork then
    getUnslashedParticipatingIndices state altair TIMELY_TARGET_FLAG_INDEX epoch = .ok voters
  else
    ∃ attestations,
      getMatchingTargetAttestations state (Nat.lt_of_not_le altair) epoch = .ok attestations ∧
        getUnslashedAttestingIndices state attestations = .ok voters

/-- The raw sum of the effective balances of a set of validators, without the floor. -/
def rawBalance (state : BeaconState preset fork) (indices : List ValidatorIndex) : Nat :=
  sumMarked state.validators.data (markIndices state.validators.data.size indices)

/-- What justification and finalization did at an epoch boundary.

In the first two epochs it changed nothing.

Otherwise it weighed the voters of the previous and of the current epoch.

The total is that of the validators active in the current epoch.

All three balances are read in the state before the call. -/
theorem processJustificationAndFinalization_weighs
    (computed : processJustificationAndFinalization state = .ok after) :
    (getCurrentEpoch state ≤ GENESIS_EPOCH + 1 ∧ after = state) ∨
      (GENESIS_EPOCH + 1 < getCurrentEpoch state ∧
        ∃ previousVoters currentVoters total previous current,
          TargetVoters state (getPreviousEpoch state) previousVoters ∧
          TargetVoters state (getCurrentEpoch state) currentVoters ∧
          getTotalActiveBalance state = .ok total ∧
          getTotalBalance state previousVoters = .ok previous ∧
          getTotalBalance state currentVoters = .ok current ∧
          weighJustificationAndFinalization state total previous current = .ok after) := by
  unfold processJustificationAndFinalization at computed
  split at computed
  · next altair =>
    unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl ⟨‹_›, computed.symm⟩
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨previousVoters, previousOk, currentVoters, currentOk, total, totalOk, previous,
        previousBalance, current, currentBalance, weighed⟩ := computed
      refine .inr ⟨UInt64.not_le.mp ‹_›, previousVoters, currentVoters, total, previous,
        current, ?_, ?_, totalOk, previousBalance, currentBalance, weighed⟩ <;>
        simp only [TargetVoters, altair, ↓reduceDIte] <;> assumption
  · next altair =>
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl ⟨‹_›, computed.symm⟩
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨previousAttestations, previousOk, currentAttestations, currentOk, total, totalOk,
        previous, previousBalance, current, currentBalance, weighed⟩ := computed
      simp only [getAttestingBalance, bind_ok_iff] at previousBalance currentBalance
      obtain ⟨previousVoters, previousVotersOk, previousBalance⟩ := previousBalance
      obtain ⟨currentVoters, currentVotersOk, currentBalance⟩ := currentBalance
      refine .inr ⟨UInt64.not_le.mp ‹_›, previousVoters, currentVoters, total, previous,
        current, ?_, ?_, totalOk, previousBalance, currentBalance, weighed⟩ <;>
        simp only [TargetVoters, altair, ↓reduceDIte] <;> exact ⟨_, ‹_›, ‹_›⟩

/-- The test of one epoch at a weighing, in raw sums.

Both sides are floored at one increment, as the spec's total balance is.

The total is over the validators active in the current epoch, the target over the voters. -/
def PassesThreshold (state : BeaconState preset fork) (voters : List ValidatorIndex) : Prop :=
  2 * max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
      (rawBalance state (getActiveValidatorIndices state (getCurrentEpoch state))) ≤
    3 * max preset.EFFECTIVE_BALANCE_INCREMENT.toNat (rawBalance state voters)

/-- A total balance is its raw sum floored at one increment, as a natural number. -/
theorem getTotalBalance_toNat {indices : List ValidatorIndex} {total : Gwei}
    (computed : getTotalBalance state indices = .ok total) :
    total.toNat = max preset.EFFECTIVE_BALANCE_INCREMENT.toNat (rawBalance state indices) := by
  obtain ⟨-, fits, rfl⟩ := getTotalBalance_ok_iff.mp computed
  rw [toNat_max, UInt64.toNat_ofNat_of_lt' fits]
  rfl

/-- Where the current justified checkpoint after an epoch boundary comes from.

Either it did not change, or it is the checkpoint of the previous or the current epoch.

That epoch's voters then passed the test, in the state before the call.

Its root is the root the state held for the first slot of the epoch. -/
theorem processJustificationAndFinalization_justified
    (computed : processJustificationAndFinalization state = .ok after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
      ∃ epoch voters root,
        (epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state) ∧
        TargetVoters state epoch voters ∧ PassesThreshold state voters ∧
        getBlockRoot state epoch = .ok root ∧
        after.currentJustifiedCheckpoint = ⟨epoch, root⟩ := by
  rcases processJustificationAndFinalization_weighs computed with ⟨_, rfl⟩ |
    ⟨_, previousVoters, currentVoters, total, previous, current, previousIs, currentIs, totalOk,
      previousOk, currentOk, weighed⟩
  · exact .inl rfl
  have justified := (weighJustificationAndFinalization_eq weighed).2.2.2.2.2.2.2.2.1
  have totalEq := getTotalBalance_toNat totalOk
  have previousEq := getTotalBalance_toNat previousOk
  have currentEq := getTotalBalance_toNat currentOk
  unfold PassesThreshold
  split at justified
  · obtain ⟨root, rootOk, eq⟩ := justified
    exact .inr ⟨_, currentVoters, root, .inr rfl, currentIs, by omega, rootOk, eq⟩
  · split at justified
    · obtain ⟨root, rootOk, eq⟩ := justified
      exact .inr ⟨_, previousVoters, root, .inl rfl, previousIs, by omega, rootOk, eq⟩
    · exact .inl justified

/-- What one weighing call writes into the justification bits, at an epoch boundary.

In the first two epochs the call writes nothing.

Otherwise the newest bit is set when the current epoch's voters pass the test.

The next bit is set when the previous epoch's voters pass, or when the newest bit was set.

The two oldest bits are the old bits moved one place.

A passing epoch has its first block root read by the call. -/
theorem processJustificationAndFinalization_bits
    (computed : processJustificationAndFinalization state = .ok after) :
    (getCurrentEpoch state ≤ GENESIS_EPOCH + 1 ∧ after = state) ∨
      (GENESIS_EPOCH + 1 < getCurrentEpoch state ∧
        (after.justificationBits.bits[0] = true →
          ∃ voters root, TargetVoters state (getCurrentEpoch state) voters ∧
            PassesThreshold state voters ∧
            getBlockRoot state (getCurrentEpoch state) = .ok root) ∧
        (after.justificationBits.bits[1] = true →
          (∃ voters root, TargetVoters state (getPreviousEpoch state) voters ∧
            PassesThreshold state voters ∧
            getBlockRoot state (getPreviousEpoch state) = .ok root) ∨
          state.justificationBits.bits[0] = true) ∧
        after.justificationBits.bits[2] = state.justificationBits.bits[1] ∧
        after.justificationBits.bits[3] = state.justificationBits.bits[2]) := by
  rcases processJustificationAndFinalization_weighs computed with early |
    ⟨later, previousVoters, currentVoters, total, previous, current, previousIs, currentIs,
      totalOk, previousOk, currentOk, weighed⟩
  · exact .inl early
  obtain ⟨_, _, _, bit0, bit1, bit2, bit3, -⟩ := weighJustificationAndFinalization_eq weighed
  obtain ⟨previousRoot, currentRoot⟩ := weighJustificationAndFinalization_roots weighed
  have totalEq := getTotalBalance_toNat totalOk
  have previousEq := getTotalBalance_toNat previousOk
  have currentEq := getTotalBalance_toNat currentOk
  refine .inr ⟨later, fun set => ?_, fun set => ?_, bit2, bit3⟩
  · rw [bit0, decide_eq_true_iff] at set
    obtain ⟨root, rootOk⟩ := currentRoot set
    exact ⟨currentVoters, root, currentIs, by unfold PassesThreshold; omega, rootOk⟩
  · rw [bit1, Bool.or_eq_true, decide_eq_true_iff] at set
    rcases set with passes | old
    · obtain ⟨root, rootOk⟩ := previousRoot passes
      exact .inl ⟨previousVoters, root, previousIs, by unfold PassesThreshold; omega, rootOk⟩
    · exact .inr old

end EthLib.Consensus
