module

public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.EpochJustification
import all Init.Data.List.Control

/-!
# Proofs: justification and finalization

The step finalizes only a checkpoint that was justified before it, or keeps the finalized one.

The old current justified checkpoint becomes the previous one.

The new current justified checkpoint is the old one, or that of the previous or the current epoch.

The checkpoints of a state are in order when finalized, previous and current justified epochs grow.

The step keeps them in order when the current justified epoch is at most the previous epoch.

The finalized epoch then never decreases.

The threshold and bit lemmas read the balances that justification actually computes.

The raw-balance threshold retains the correction from the minimum effective-balance increment.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- Source matching is unchanged when both pending lists and justified checkpoints are unchanged.

Registry and balance updates can use this without assumptions about validator weights. -/
theorem pendingSourcesMatch_of_fields {before : fork < .altair}
    (holds : PendingSourcesMatch state before)
    (current : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint)
    (previous : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint)
    (currentPending : after.currentEpochAttestations before = state.currentEpochAttestations before)
    (previousPending : after.previousEpochAttestations before =
      state.previousEpochAttestations before) :
    PendingSourcesMatch after before := by
  unfold PendingSourcesMatch at holds ⊢
  rw [current, previous, currentPending, previousPending]
  exact holds

/-- Pending epochs are unchanged when the slot and both pending lists are unchanged. -/
theorem pendingEpochsMatch_of_fields {before : fork < .altair}
    (holds : PendingEpochsMatch state before)
    (slot : after.slot = state.slot)
    (currentPending : after.currentEpochAttestations before = state.currentEpochAttestations before)
    (previousPending : after.previousEpochAttestations before =
      state.previousEpochAttestations before) :
    PendingEpochsMatch after before := by
  unfold PendingEpochsMatch getPreviousEpoch getCurrentEpoch at holds ⊢
  rw [slot, currentPending, previousPending]
  exact holds

/-- Compare two participation marks using the effective balances at the same validator index.

The two later balances can grow only to the Phase 0 cap.

The largest decrease below the reference is charged once, with coefficient three.

The initial deficit has coefficient two, even when both branches refill it.

Summing this inequality permits two two-thirds thresholds to cancel their denominators.

This is the balance calculation of Casper FFG §2 with the actual effective balances. -/
theorem validator_two_thirds_comparison (reference left right : Validator)
    (leftMarked rightMarked : Bool)
    (referenceBound : reference.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (leftBound : left.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (rightBound : right.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE) :
    reference.effectiveBalance.toNat +
        3 * (if leftMarked then left.effectiveBalance.toNat else 0) +
        3 * (if rightMarked then right.effectiveBalance.toNat else 0) ≤
      3 * (if leftMarked && rightMarked then reference.effectiveBalance.toNat else 0) +
        3 * max (reference.effectiveBalance.toNat - left.effectiveBalance.toNat)
          (reference.effectiveBalance.toNat - right.effectiveBalance.toNat) +
        2 * (preset.MAX_EFFECTIVE_BALANCE.toNat - reference.effectiveBalance.toNat) +
        2 * left.effectiveBalance.toNat + 2 * right.effectiveBalance.toNat := by
  have referenceLe := UInt64.le_iff_toNat_le.mp referenceBound
  have leftLe := UInt64.le_iff_toNat_le.mp leftBound
  have rightLe := UInt64.le_iff_toNat_le.mp rightBound
  cases leftMarked <;> cases rightMarked <;> simp only [Bool.false_and, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Sum the comparison over concrete registry entries and their two participation marks.

The entries align the same validator index in the reference and the two weighing states.

The maximum loss is taken before summing, so recovery on one branch cannot erase it. -/
theorem validators_two_thirds_comparison
    (entries : List (Validator × Validator × Validator × Bool × Bool))
    (bounded : ∀ entry ∈ entries,
      entry.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE ∧
      entry.2.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE ∧
      entry.2.2.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE) :
    (entries.map fun entry => entry.1.effectiveBalance.toNat).sum +
        3 * (entries.map fun entry =>
          if entry.2.2.2.1 then entry.2.1.effectiveBalance.toNat else 0).sum +
        3 * (entries.map fun entry =>
          if entry.2.2.2.2 then entry.2.2.1.effectiveBalance.toNat else 0).sum ≤
      3 * (entries.map fun entry =>
          if entry.2.2.2.1 && entry.2.2.2.2 then entry.1.effectiveBalance.toNat else 0).sum +
        3 * (entries.map fun entry =>
          max (entry.1.effectiveBalance.toNat - entry.2.1.effectiveBalance.toNat)
            (entry.1.effectiveBalance.toNat - entry.2.2.1.effectiveBalance.toNat)).sum +
        2 * (entries.map fun entry =>
          preset.MAX_EFFECTIVE_BALANCE.toNat - entry.1.effectiveBalance.toNat).sum +
        2 * (entries.map fun entry => entry.2.1.effectiveBalance.toNat).sum +
        2 * (entries.map fun entry => entry.2.2.1.effectiveBalance.toNat).sum := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    have bounds := bounded entry List.mem_cons_self
    have one := validator_two_thirds_comparison entry.1 entry.2.1 entry.2.2.1
      entry.2.2.2.1 entry.2.2.2.2 bounds.1 bounds.2.1 bounds.2.2
    have rest := ih (fun other member => bounded other (List.mem_cons_of_mem entry member))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- Removing a reference validator from either active denominator costs twice its reference stake.

Participation marks here count only validators active in the corresponding current epoch.

Previous-epoch participants absent from that denominator must be charged separately.

The exit charge is shared between the branches rather than summed twice. -/
theorem validator_active_two_thirds_comparison (reference left right : Validator)
    (leftEpoch rightEpoch : Epoch) (leftMarked rightMarked : Bool)
    (referenceBound : reference.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (leftBound : left.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (rightBound : right.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (leftActive : leftMarked = true → isActiveValidator left leftEpoch = true)
    (rightActive : rightMarked = true → isActiveValidator right rightEpoch = true) :
    reference.effectiveBalance.toNat +
        3 * (if leftMarked then left.effectiveBalance.toNat else 0) +
        3 * (if rightMarked then right.effectiveBalance.toNat else 0) ≤
      3 * (if leftMarked && rightMarked then reference.effectiveBalance.toNat else 0) +
        3 * max (reference.effectiveBalance.toNat - left.effectiveBalance.toNat)
          (reference.effectiveBalance.toNat - right.effectiveBalance.toNat) +
        2 * (preset.MAX_EFFECTIVE_BALANCE.toNat - reference.effectiveBalance.toNat) +
        2 * (if isActiveValidator left leftEpoch then left.effectiveBalance.toNat else 0) +
        2 * (if isActiveValidator right rightEpoch then right.effectiveBalance.toNat else 0) +
        2 * (if isActiveValidator left leftEpoch && isActiveValidator right rightEpoch
          then 0 else reference.effectiveBalance.toNat) := by
  have referenceLe := UInt64.le_iff_toNat_le.mp referenceBound
  have leftLe := UInt64.le_iff_toNat_le.mp leftBound
  have rightLe := UInt64.le_iff_toNat_le.mp rightBound
  cases leftIsActive : isActiveValidator left leftEpoch <;>
    cases rightIsActive : isActiveValidator right rightEpoch <;>
    cases leftMarked <;> cases rightMarked <;>
    simp_all only [Bool.false_and, Bool.true_and, Bool.false_eq_true, ↓reduceIte] <;> omega

/-- Two thresholds on aligned registry entries bound their reference-weight intersection.

The exact corrections to the thresholds remain explicit.

The initial deficit has coefficient two, and each validator's largest loss has coefficient three.

This is only the weight calculation, not the extraction of slashable data from finalization. -/
theorem validators_two_thirds_drift
    (entries : List (Validator × Validator × Validator × Bool × Bool))
    (bounded : ∀ entry ∈ entries,
      entry.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE ∧
      entry.2.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE ∧
      entry.2.2.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (leftCorrection rightCorrection : Nat)
    (leftEnough :
      2 * (entries.map fun entry => entry.2.1.effectiveBalance.toNat).sum ≤
        3 * (entries.map fun entry =>
          if entry.2.2.2.1 then entry.2.1.effectiveBalance.toNat else 0).sum + leftCorrection)
    (rightEnough :
      2 * (entries.map fun entry => entry.2.2.1.effectiveBalance.toNat).sum ≤
        3 * (entries.map fun entry =>
          if entry.2.2.2.2 then entry.2.2.1.effectiveBalance.toNat else 0).sum +
            rightCorrection) :
    (entries.map fun entry => entry.1.effectiveBalance.toNat).sum ≤
      3 * (entries.map fun entry =>
          if entry.2.2.2.1 && entry.2.2.2.2 then entry.1.effectiveBalance.toNat else 0).sum +
        3 * (entries.map fun entry =>
          max (entry.1.effectiveBalance.toNat - entry.2.1.effectiveBalance.toNat)
            (entry.1.effectiveBalance.toNat - entry.2.2.1.effectiveBalance.toNat)).sum +
        2 * (entries.map fun entry =>
          preset.MAX_EFFECTIVE_BALANCE.toNat - entry.1.effectiveBalance.toNat).sum +
        leftCorrection + rightCorrection := by
  have compared := validators_two_thirds_comparison entries bounded
  omega

/-- Sum the drift comparison with the actual current-active denominators.

Reference validators absent from either denominator are charged once in the union of exits.

Participants outside these denominators must first be removed and charged to the threshold. -/
theorem validators_active_two_thirds_comparison
    (entries : List (Validator × Validator × Validator × Bool × Bool))
    (leftEpoch rightEpoch : Epoch)
    (bounded : ∀ entry ∈ entries,
      entry.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE ∧
      entry.2.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE ∧
      entry.2.2.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (leftActive : ∀ entry ∈ entries, entry.2.2.2.1 = true →
      isActiveValidator entry.2.1 leftEpoch = true)
    (rightActive : ∀ entry ∈ entries, entry.2.2.2.2 = true →
      isActiveValidator entry.2.2.1 rightEpoch = true) :
    (entries.map fun entry => entry.1.effectiveBalance.toNat).sum +
        3 * (entries.map fun entry =>
          if entry.2.2.2.1 then entry.2.1.effectiveBalance.toNat else 0).sum +
        3 * (entries.map fun entry =>
          if entry.2.2.2.2 then entry.2.2.1.effectiveBalance.toNat else 0).sum ≤
      3 * (entries.map fun entry =>
          if entry.2.2.2.1 && entry.2.2.2.2 then entry.1.effectiveBalance.toNat else 0).sum +
        3 * (entries.map fun entry =>
          max (entry.1.effectiveBalance.toNat - entry.2.1.effectiveBalance.toNat)
            (entry.1.effectiveBalance.toNat - entry.2.2.1.effectiveBalance.toNat)).sum +
        2 * (entries.map fun entry =>
          preset.MAX_EFFECTIVE_BALANCE.toNat - entry.1.effectiveBalance.toNat).sum +
        2 * (entries.map fun entry =>
          if isActiveValidator entry.2.1 leftEpoch then entry.2.1.effectiveBalance.toNat
          else 0).sum +
        2 * (entries.map fun entry =>
          if isActiveValidator entry.2.2.1 rightEpoch then entry.2.2.1.effectiveBalance.toNat
          else 0).sum +
        2 * (entries.map fun entry =>
          if isActiveValidator entry.2.1 leftEpoch && isActiveValidator entry.2.2.1 rightEpoch
          then 0 else entry.1.effectiveBalance.toNat).sum := by
  induction entries with
  | nil => simp
  | cons entry entries ih =>
    have bounds := bounded entry List.mem_cons_self
    have one := validator_active_two_thirds_comparison entry.1 entry.2.1 entry.2.2.1
      leftEpoch rightEpoch entry.2.2.2.1 entry.2.2.2.2 bounds.1 bounds.2.1 bounds.2.2
      (leftActive entry List.mem_cons_self) (rightActive entry List.mem_cons_self)
    have rest := ih
      (fun other member => bounded other (List.mem_cons_of_mem entry member))
      (fun other member => leftActive other (List.mem_cons_of_mem entry member))
      (fun other member => rightActive other (List.mem_cons_of_mem entry member))
    simp only [List.map_cons, List.sum_cons, Nat.mul_add]
    omega

/-- Active-denominator thresholds bound the reference intersection with explicit exit drift.

The exit coefficient is two for the union of absent reference validators, not twice per branch.

Each threshold correction is retained once, without increasing its coefficient. -/
theorem validators_active_two_thirds_drift
    (entries : List (Validator × Validator × Validator × Bool × Bool))
    (leftEpoch rightEpoch : Epoch)
    (bounded : ∀ entry ∈ entries,
      entry.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE ∧
      entry.2.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE ∧
      entry.2.2.1.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (leftActive : ∀ entry ∈ entries, entry.2.2.2.1 = true →
      isActiveValidator entry.2.1 leftEpoch = true)
    (rightActive : ∀ entry ∈ entries, entry.2.2.2.2 = true →
      isActiveValidator entry.2.2.1 rightEpoch = true)
    (leftCorrection rightCorrection : Nat)
    (leftEnough :
      2 * (entries.map fun entry =>
        if isActiveValidator entry.2.1 leftEpoch then entry.2.1.effectiveBalance.toNat
        else 0).sum ≤
      3 * (entries.map fun entry =>
        if entry.2.2.2.1 then entry.2.1.effectiveBalance.toNat else 0).sum + leftCorrection)
    (rightEnough :
      2 * (entries.map fun entry =>
        if isActiveValidator entry.2.2.1 rightEpoch then entry.2.2.1.effectiveBalance.toNat
        else 0).sum ≤
      3 * (entries.map fun entry =>
        if entry.2.2.2.2 then entry.2.2.1.effectiveBalance.toNat else 0).sum + rightCorrection) :
    (entries.map fun entry => entry.1.effectiveBalance.toNat).sum ≤
      3 * (entries.map fun entry =>
          if entry.2.2.2.1 && entry.2.2.2.2 then entry.1.effectiveBalance.toNat else 0).sum +
        3 * (entries.map fun entry =>
          max (entry.1.effectiveBalance.toNat - entry.2.1.effectiveBalance.toNat)
            (entry.1.effectiveBalance.toNat - entry.2.2.1.effectiveBalance.toNat)).sum +
        2 * (entries.map fun entry =>
          preset.MAX_EFFECTIVE_BALANCE.toNat - entry.1.effectiveBalance.toNat).sum +
        2 * (entries.map fun entry =>
          if isActiveValidator entry.2.1 leftEpoch && isActiveValidator entry.2.2.1 rightEpoch
          then 0 else entry.1.effectiveBalance.toNat).sum +
        leftCorrection + rightCorrection := by
  have compared := validators_active_two_thirds_comparison entries leftEpoch rightEpoch
    bounded leftActive rightActive
  omega

/-- The marked sum is a sum of the effective balances paired with true marks.

The array zip discards any unmatched suffix, exactly as `sumMarked` does. -/
theorem sumMarked_eq_sum (validators : Array Validator) (marked : Array Bool) :
    sumMarked validators marked =
      ((validators.zip marked).toList.map fun (validator, mark) =>
        if mark then validator.effectiveBalance.toNat else 0).sum := by
  unfold sumMarked
  rw [← Array.foldl_toList]
  have fold : ∀ (entries : List (Validator × Bool)) (start : Nat),
      entries.foldl (fun sum (validator, mark) =>
        if mark then sum + validator.effectiveBalance.toNat else sum) start =
      start + (entries.map fun (validator, mark) =>
        if mark then validator.effectiveBalance.toNat else 0).sum := by
    intro entries
    induction entries with
    | nil => intro start; simp
    | cons entry rest ih =>
      obtain ⟨validator, mark⟩ := entry
      intro start
      cases mark <;> simp [ih, Nat.add_assoc]
  simpa using fold (validators.zip marked).toList 0

/-- A marked balance is bounded by the balance of any predicate containing its marked entries. -/
theorem sumMarked_le_filter (validators : Array Validator) (marked : Array Bool)
    (predicate : Validator → Bool)
    (contains : ∀ validator, (validator, true) ∈ validators.zip marked →
      predicate validator = true) :
    sumMarked validators marked ≤
      ((validators.toList.filter predicate).map (·.effectiveBalance.toNat)).sum := by
  rw [sumMarked_eq_sum]
  have compare : ∀ (entries : List Validator) (marks : List Bool),
      (∀ validator, (validator, true) ∈ entries.zip marks → predicate validator = true) →
      ((entries.zip marks).map fun (validator, mark) =>
        if mark then validator.effectiveBalance.toNat else 0).sum ≤
        ((entries.filter predicate).map (·.effectiveBalance.toNat)).sum := by
    intro entries
    induction entries with
    | nil => intro marks _; simp
    | cons validator entries ih =>
      intro marks contained
      cases marks with
      | nil => simp
      | cons mark marks =>
        have rest := ih marks (fun other member =>
          contained other (List.mem_cons_of_mem _ member))
        cases mark with
        | false =>
          cases selected : predicate validator <;> simp [selected] at * <;> omega
        | true =>
          have selected := contained validator (by simp)
          simpa only [List.zip_cons_cons, List.map_cons, List.sum_cons, ↓reduceIte,
            List.filter_cons, selected] using Nat.add_le_add_left rest
              validator.effectiveBalance.toNat
  simpa only [Array.toList_zip] using compare validators.toList marked.toList (by
    intro validator member
    apply contains validator
    simpa [← Array.toList_zip] using member)

/-- Intersecting participation with the denominator loses only marks outside that denominator.

The last sum is the concrete correction needed for previous-epoch voters that have exited. -/
theorem sumMarked_le_active_add_gap (validators : Array Validator)
    (participants active : Array Bool)
    (participantsSize : participants.size = validators.size)
    (activeSize : active.size = validators.size) :
    sumMarked validators participants ≤
      sumMarked validators (participants.zipWith (· && ·) active) +
        sumMarked validators
          (participants.zipWith (fun mark active => mark && !active) active) := by
  simp only [sumMarked_eq_sum, Array.toList_zip, Array.toList_zipWith]
  have compare : ∀ (entries : List Validator) (marks denominator : List Bool),
      marks.length = entries.length → denominator.length = entries.length →
      ((entries.zip marks).map fun (validator, mark) =>
        if mark then validator.effectiveBalance.toNat else 0).sum ≤
      ((entries.zip (marks.zipWith (· && ·) denominator)).map fun (validator, mark) =>
        if mark then validator.effectiveBalance.toNat else 0).sum +
      ((entries.zip (marks.zipWith (fun mark active => mark && !active) denominator)).map
          fun (validator, mark) =>
        if mark then validator.effectiveBalance.toNat else 0).sum := by
    intro entries
    induction entries with
    | nil => intro marks denominator hm hd; simp at hm hd; subst hm; subst hd; simp
    | cons validator entries ih =>
      intro marks denominator hm hd
      cases marks with
      | nil => simp at hm
      | cons mark marks =>
        cases denominator with
        | nil => simp at hd
        | cons active denominator =>
          have rest := ih marks denominator (by simpa using hm) (by simpa using hd)
          cases mark <;> cases active <;>
            simp only [List.zip_cons_cons, List.zipWith_cons_cons, List.map_cons, List.sum_cons,
              Bool.false_and, Bool.true_and, Bool.not_false, Bool.not_true, Bool.false_eq_true,
              ↓reduceIte] at * <;> omega
  exact compare validators.toList participants.toList active.toList
    (by simpa using participantsSize) (by simpa using activeSize)

/-- Marking validator indices keeps one mark for every registry entry. -/
theorem size_markIndices (size : Nat) (indices : List ValidatorIndex) :
    (markIndices size indices).size = size := by
  have kept : ∀ (indices : List ValidatorIndex) (initial : Array Bool),
      (indices.foldl (fun marked index => marked.set! index.toNat true) initial).size =
        initial.size := by
    intro indices
    induction indices with
    | nil => intro initial; rfl
    | cons index rest ih =>
      intro initial
      rw [List.foldl_cons, ih]
      simp
  simpa only [markIndices, Array.size_replicate] using kept indices (Array.replicate size false)

/-- Intersecting index lists intersects their registry marks, without counting duplicates. -/
theorem markIndices_filter_mem (size : Nat) (first second : List ValidatorIndex) :
    markIndices size (first.filter (fun index => decide (index ∈ second))) =
      (markIndices size first).zipWith (· && ·) (markIndices size second) := by
  apply Array.ext_getElem?
  intro index
  rw [getElem?_markIndices, Array.getElem?_zipWith,
    getElem?_markIndices, getElem?_markIndices]
  by_cases inside : index < size
  · simp only [inside, ↓reduceIte, Option.some.injEq]
    rw [Bool.eq_iff_iff, Bool.and_eq_true, List.any_eq_true, List.any_eq_true,
      List.any_eq_true]
    constructor
    · rintro ⟨validatorIndex, member, equal⟩
      obtain ⟨firstMember, secondMember⟩ := List.mem_filter.mp member
      exact ⟨⟨validatorIndex, firstMember, equal⟩,
        ⟨validatorIndex, of_decide_eq_true secondMember, equal⟩⟩
    · rintro ⟨⟨left, leftMember, leftEqual⟩, ⟨right, rightMember, rightEqual⟩⟩
      have same : left = right := UInt64.toNat_inj.mp (by
        have leftValue := of_decide_eq_true leftEqual
        have rightValue := of_decide_eq_true rightEqual
        exact leftValue.trans rightValue.symm)
      subst right
      exact ⟨left, List.mem_filter.mpr ⟨leftMember, by simpa using rightMember⟩, leftEqual⟩
  · simp [inside]

/-- Effective weight counted for a target but absent from the current active denominator.

For a previous target, these participants can have exited between the two epochs. -/
def participatingOutsideActiveBalance (state : BeaconState preset fork)
    (indices : List ValidatorIndex) : Nat :=
  sumMarked state.validators.data
    ((markIndices state.validators.data.size indices).zipWith (fun mark active => mark && !active)
      (markIndices state.validators.data.size
        (getActiveValidatorIndices state (getCurrentEpoch state))))

/-- Two marked sets can together count at most the registry plus their intersection.

This is the balance intersection calculation used with the two-thirds threshold of Casper FFG §2.

All weights are the effective balances of this concrete registry. -/
theorem sumMarked_intersection (validators : Array Validator) (left right : Array Bool)
    (leftSize : left.size = validators.size) (rightSize : right.size = validators.size) :
    sumMarked validators left + sumMarked validators right ≤
      (validators.toList.map (·.effectiveBalance.toNat)).sum +
        sumMarked validators (left.zipWith (· && ·) right) := by
  simp only [sumMarked_eq_sum, Array.toList_zip, Array.toList_zipWith]
  have intersection : ∀ (validators : List Validator) (left right : List Bool),
      left.length = validators.length → right.length = validators.length →
      ((validators.zip left).map fun (validator, mark) =>
        if mark then validator.effectiveBalance.toNat else 0).sum +
        ((validators.zip right).map fun (validator, mark) =>
          if mark then validator.effectiveBalance.toNat else 0).sum ≤
        (validators.map (·.effectiveBalance.toNat)).sum +
          ((validators.zip (left.zipWith (· && ·) right)).map fun (validator, mark) =>
            if mark then validator.effectiveBalance.toNat else 0).sum := by
    intro validators
    induction validators with
    | nil => intro left right l r; simp at l r; subst l; subst r; simp
    | cons validator validators ih =>
      intro left right l r
      cases left with
      | nil => simp at l
      | cons a left =>
        cases right with
        | nil => simp at r
        | cons b right =>
          have rest := ih left right (by simpa using l) (by simpa using r)
          cases a <;> cases b <;> simp only [List.zip_cons_cons, List.map_cons,
            List.sum_cons, List.zipWith_cons_cons, Bool.and_false, Bool.false_and,
            Bool.true_and, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  exact intersection validators.toList left.toList right.toList
    (by simpa using leftSize) (by simpa using rightSize)

/-- Two raw two-thirds bounds force one third of the registry into the marked intersection.

Each raw bound can retain an explicit correction, such as the target-balance floor. -/
theorem sumMarked_two_thirds_intersection (validators : Array Validator) (left right : Array Bool)
    (leftSize : left.size = validators.size) (rightSize : right.size = validators.size)
    (leftCorrection rightCorrection : Nat)
    (leftEnough : 2 * (validators.toList.map (·.effectiveBalance.toNat)).sum ≤
      3 * sumMarked validators left + leftCorrection)
    (rightEnough : 2 * (validators.toList.map (·.effectiveBalance.toNat)).sum ≤
      3 * sumMarked validators right + rightCorrection) :
    (validators.toList.map (·.effectiveBalance.toNat)).sum ≤
      3 * sumMarked validators (left.zipWith (· && ·) right) +
        leftCorrection + rightCorrection := by
  have intersection := sumMarked_intersection validators left right leftSize rightSize
  omega

/-- The extra balance that the increment floor adds to a raw sum of effective balances.

`getTotalBalance` returns at least one increment, even when no validator participates. -/
def totalBalanceFloor (state : BeaconState preset fork) (indices : List ValidatorIndex) : Nat :=
  preset.EFFECTIVE_BALANCE_INCREMENT.toNat -
    sumMarked state.validators.data (markIndices state.validators.data.size indices)

/-- A successful total balance is the raw sum plus its explicit increment-floor correction. -/
theorem getTotalBalance_eq_sum_add_floor {indices : List ValidatorIndex} {total : Gwei}
    (computed : getTotalBalance state indices = .ok total) :
    total.toNat = sumMarked state.validators.data
      (markIndices state.validators.data.size indices) + totalBalanceFloor state indices := by
  obtain ⟨_, fits, rfl⟩ := getTotalBalance_ok_iff.mp computed
  unfold totalBalanceFloor
  rw [UInt64.max_def]
  split
  · have bound := UInt64.le_iff_toNat_le.mp ‹_›
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits] at bound ⊢
    omega
  · rename_i notLe
    rw [UInt64.le_iff_toNat_le] at notLe
    have bound := notLe
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits] at bound ⊢
    omega

/-- A two-thirds check on computed balances bounds the raw sums with a target-floor correction.

The denominator's floor only strengthens the check, so the bound drops it. -/
theorem getTotalBalance_threshold_raw {active signers : List ValidatorIndex} {total target : Gwei}
    (totalOk : getTotalBalance state active = .ok total)
    (targetOk : getTotalBalance state signers = .ok target)
    (threshold : 2 * total.toNat ≤ 3 * target.toNat) :
    2 * sumMarked state.validators.data (markIndices state.validators.data.size active) ≤
      3 * sumMarked state.validators.data (markIndices state.validators.data.size signers) +
        3 * totalBalanceFloor state signers := by
  rw [getTotalBalance_eq_sum_add_floor totalOk,
    getTotalBalance_eq_sum_add_floor targetOk] at threshold
  omega

/-- A computed target threshold keeps its force after removing participants outside the denominator.

Each removed unit and each unit of the target floor is charged with coefficient three. -/
theorem getTotalBalance_threshold_current_active
    {indices : List ValidatorIndex} {total target : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total)
    (targetOk : getTotalBalance state indices = .ok target)
    (threshold : 2 * total.toNat ≤ 3 * target.toNat) :
    2 * sumMarked state.validators.data
        (markIndices state.validators.data.size
          (getActiveValidatorIndices state (getCurrentEpoch state))) ≤
      3 * sumMarked state.validators.data
        ((markIndices state.validators.data.size indices).zipWith (· && ·)
          (markIndices state.validators.data.size
            (getActiveValidatorIndices state (getCurrentEpoch state)))) +
      3 * participatingOutsideActiveBalance state indices +
        3 * totalBalanceFloor state indices := by
  have raw := getTotalBalance_threshold_raw totalOk targetOk threshold
  have removed := sumMarked_le_active_add_gap state.validators.data
    (markIndices state.validators.data.size indices)
    (markIndices state.validators.data.size
      (getActiveValidatorIndices state (getCurrentEpoch state)))
    (size_markIndices _ _) (size_markIndices _ _)
  unfold participatingOutsideActiveBalance
  omega

/-- The finalized, previous justified and current justified epochs are in increasing order. -/
def CheckpointsOrdered (state : BeaconState preset fork) : Prop :=
  state.finalizedCheckpoint.epoch ≤ state.previousJustifiedCheckpoint.epoch ∧
    state.previousJustifiedCheckpoint.epoch ≤ state.currentJustifiedCheckpoint.epoch

/-- The epochs whose pending attestations match a source are the current and the previous one. -/
theorem getMatchingSourceAttestations_epoch {before : fork < .altair} {epoch : Epoch}
    {attestations : Array (PendingAttestation preset)}
    (computed : getMatchingSourceAttestations state before epoch = .ok attestations) :
    epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state := by
  simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, recent, _⟩ := computed
  exact recent

/-- Every matching source query reads the source checkpoint assigned to its epoch's pending list.

This uses source matching, not a new source check in the balance calculation. -/
theorem getMatchingSourceAttestations_source {before : fork < .altair} {epoch : Epoch}
    {attestations : Array (PendingAttestation preset)} {pending : PendingAttestation preset}
    (holds : PendingSourcesMatch state before)
    (computed : getMatchingSourceAttestations state before epoch = .ok attestations)
    (member : pending ∈ attestations) :
    pending.data.source = if epoch = getCurrentEpoch state then
      state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint := by
  simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  by_cases same : epoch = getCurrentEpoch state
  · simp only [same, ↓reduceIte] at member ⊢
    exact holds.1 pending member
  · simp only [same, ↓reduceIte] at member ⊢
    exact holds.2 pending member

/-- An unslashed signer returned by the filter belongs to its input and has a clear flag. -/
private theorem mem_filterAuxM_unslashed {indices accumulator result : List ValidatorIndex}
    (computed : List.filterAuxM (fun index => do
      return !(← getValidator state index).slashed) indices accumulator = .ok result)
    {index : ValidatorIndex} (member : index ∈ result) :
    index ∈ accumulator ∨
      (index ∈ indices ∧ ∃ validator, getValidator state index = .ok validator ∧
        validator.slashed = false) := by
  induction indices generalizing accumulator with
  | nil =>
    simp only [List.filterAuxM, pure, Except.pure, Except.ok.injEq] at computed
    exact .inl (computed ▸ member)
  | cons first rest ih =>
    simp only [List.filterAuxM, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨keep, ⟨validator, found, rfl⟩, computed⟩ := computed
    rcases ih computed with accumulated | ⟨member, validator, found, clear⟩
    · cases flag : validator.slashed
      · simp only [flag, Bool.not_false, Bool.cond_true, List.mem_cons] at accumulated
        rcases accumulated with rfl | accumulated
        · exact .inr ⟨List.mem_cons_self, validator, found, flag⟩
        · exact .inl accumulated
      · simpa [flag] using Or.inl accumulated
    · exact .inr ⟨List.mem_cons_of_mem first member, validator, found, clear⟩

/-- Every returned unslashed index occurs in the actual signer lists and is not slashed. -/
theorem mem_unslashedAmong {signers : List (List ValidatorIndex)} {indices : List ValidatorIndex}
    (computed : unslashedAmong state signers = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices) :
    index ∈ signers.flatten ∧
      ∃ validator, getValidator state index = .ok validator ∧ validator.slashed = false := by
  simp only [unslashedAmong, List.filterM, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨result, filtered, rfl⟩ := computed
  rcases mem_filterAuxM_unslashed filtered (List.mem_reverse.mp member) with impossible |
      ⟨member, rest⟩
  · cases impossible
  · exact ⟨mem_sortedSet.mp member, rest⟩

/-- Each index counted for justification comes from an actual pending attestation.

The registry read also certifies that the signer has not been slashed. -/
theorem mem_getUnslashedAttestingIndices {attestations : Array (PendingAttestation preset)}
    {indices : List ValidatorIndex}
    (computed : getUnslashedAttestingIndices state attestations = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices) :
    (∃ attestation ∈ attestations, ∃ signers,
      getPendingAttestingIndices state attestation = .ok signers ∧ index ∈ signers) ∧
      ∃ validator, getValidator state index = .ok validator ∧ validator.slashed = false := by
  simp only [getUnslashedAttestingIndices, bind_ok_iff] at computed
  obtain ⟨signers, mapped, filtered⟩ := computed
  obtain ⟨member, validator⟩ := mem_unslashedAmong filtered member
  obtain ⟨list, listMember, indexMember⟩ := List.mem_flatten.mp member
  obtain ⟨attestation, attestationMember, found⟩ := mapM_ok_mem mapped list listMember
  exact ⟨⟨attestation, Array.mem_toList_iff.mp attestationMember, list, found, indexMember⟩,
    validator⟩

/-- A signer of a pending attestation is active at its slot's epoch in the weighing state. -/
theorem mem_getActiveValidatorIndices_of_pending
    {attestation : PendingAttestation preset} {indices : List ValidatorIndex}
    (computed : getPendingAttestingIndices state attestation = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices) :
    index ∈ getActiveValidatorIndices state (computeEpochAtSlot preset attestation.data.slot) := by
  simp only [getPendingAttestingIndices, bind_ok_iff] at computed
  obtain ⟨committee, committeeOk, signersOk⟩ := computed
  exact mem_getActiveValidatorIndices_of_getBeaconCommittee committeeOk
    (mem_of_committeeAttesters signersOk member)

/-- Pending and included forms recover the same signer indices from the same committee.

The pending record retains the data and aggregation bits checked during inclusion.

The committee equality is needed because weighing reconstructs committees from a later state. -/
theorem getPendingAttestingIndices_indexed {inclusion : BeaconState preset fork}
    {pending : PendingAttestation preset} {attestation : Attestation preset fork}
    {indices : List ValidatorIndex} (before : fork < .altair)
    (data : pending.data = attestation.data)
    (bits : pending.aggregationBits.bits = attestation.aggregationBits.bits)
    (committee : getBeaconCommittee inclusion pending.data.slot pending.data.index =
      getBeaconCommittee state pending.data.slot pending.data.index)
    (computed : getPendingAttestingIndices state pending = .ok indices) :
    ∃ indexed, getIndexedAttestation inclusion attestation = .ok indexed ∧
      indexed.attestingIndices.data = (sortedSet indices).toArray ∧
      indexed.data = pending.data ∧ indexed.signature = attestation.signature := by
  have notElectra : ¬Fork.pectra ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  have signers : getAttestingIndices inclusion attestation = .ok (sortedSet indices) := by
    unfold getPendingAttestingIndices at computed
    rw [← committee, data, bits] at computed
    simp only [getAttestingIndices, notElectra, ↓reduceDIte]
    obtain ⟨members, membersOk, signersOk⟩ := bind_ok_iff.mp computed
    rw [membersOk]
    simp only [bind, Except.bind, signersOk, pure, Except.pure]
  obtain ⟨indexed, indexedOk, listed, indexedData, signature⟩ :=
    getIndexedAttestation_of_getAttestingIndices signers
  exact ⟨indexed, indexedOk, listed, indexedData.trans data.symm, signature⟩

/-- Stable committees identify counted pending indices with an inclusion's authenticated indices.

Both indexed forms use the same concrete attestation, so successful evaluation makes them equal. -/
theorem getPendingAttestingIndices_eq_included {inclusion : BeaconState preset fork}
    {pending : PendingAttestation preset} {attestation : Attestation preset fork}
    {indices : List ValidatorIndex} {indexed : IndexedAttestation preset fork}
    (before : fork < .altair)
    (data : pending.data = attestation.data)
    (bits : pending.aggregationBits.bits = attestation.aggregationBits.bits)
    (committee : getBeaconCommittee inclusion pending.data.slot pending.data.index =
      getBeaconCommittee state pending.data.slot pending.data.index)
    (computed : getPendingAttestingIndices state pending = .ok indices)
    (authenticated : getIndexedAttestation inclusion attestation = .ok indexed) :
    indexed.attestingIndices.data = (sortedSet indices).toArray ∧
      indexed.data = pending.data ∧ indexed.signature = attestation.signature := by
  obtain ⟨reconstructed, indexedOk, listed, indexedData, signature⟩ :=
    getPendingAttestingIndices_indexed before data bits committee computed
  have equal : reconstructed = indexed := Except.ok.inj (indexedOk.symm.trans authenticated)
  subst reconstructed
  exact ⟨listed, indexedData, signature⟩

/-- A successful finalization test gives its exact epoch gap and requires its justification bits.

The checked addition rules out a modular epoch equality. -/
theorem finalizes_true {justified : Bool} {source gap current : Epoch}
    (computed : finalizes justified source gap current = .ok true) :
    justified = true ∧ source.toNat + gap.toNat = current.toNat := by
  unfold finalizes at computed
  split at computed
  · refine ⟨‹_›, ?_⟩
    simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      addChecked_ok_iff, pure, Except.pure, Except.ok.injEq, beq_iff_eq] at computed
    obtain ⟨sum, ⟨_, exactSum⟩, rfl⟩ := computed
    exact exactSum.symm
  · simp [pure, Except.pure] at computed

/-- A justified checkpoint is that of its epoch; otherwise the checkpoint stays. -/
theorem justifyCheckpoint_ok {justified : Bool} {epoch : Epoch} {checkpoint result : Checkpoint}
    (computed : justifyCheckpoint state justified epoch checkpoint = .ok result) :
    (justified = true ∧ result.epoch = epoch) ∨ (justified = false ∧ result = checkpoint) := by
  cases justified
  · simp only [justifyCheckpoint, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at computed
    exact .inr ⟨rfl, computed.symm⟩
  · simp only [justifyCheckpoint, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact .inl ⟨rfl, rfl⟩

/-- A changed justified checkpoint contains exactly the root read for its target epoch.

No block identity or hash injectivity is assumed by this accessor-level statement. -/
theorem justifyCheckpoint_changed {justified : Bool} {epoch : Epoch}
    {checkpoint result : Checkpoint}
    (computed : justifyCheckpoint state justified epoch checkpoint = .ok result)
    (changed : result ≠ checkpoint) :
    justified = true ∧ result.epoch = epoch ∧ getBlockRoot state epoch = .ok result.root := by
  cases justified
  · simp only [justifyCheckpoint, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at computed
    exact (changed computed.symm).elim
  · simp only [justifyCheckpoint, ↓reduceIte, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨root, found, rfl⟩ := computed
    exact ⟨rfl, rfl, found⟩

/-- A changed justified checkpoint requires two thirds of a target balance.

The current epoch wins when both target balances reach the threshold.

The products are natural numbers, not products modulo `2^64`.

This is the threshold of Casper FFG §2, as computed by the justification step. -/
theorem weighJustificationAndFinalization_threshold {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (changed : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint) :
    (after.currentJustifiedCheckpoint.epoch = getCurrentEpoch state ∧
      2 * total.toNat ≤ 3 * current.toNat) ∨
    (after.currentJustifiedCheckpoint.epoch = getPreviousEpoch state ∧
      2 * total.toNat ≤ 3 * previous.toNat) := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨pw, pwOk, threshold, thresholdOk, first, firstOk, cw, cwOk, second, secondOk,
    _, _, _, _, _, _, _, _, rfl⟩ := computed
  simp only [liftArith, mapError_ok_iff] at pwOk thresholdOk cwOk
  have previousProduct := (mulChecked_ok_iff.mp pwOk).2
  have totalProduct := (mulChecked_ok_iff.mp thresholdOk).2
  have currentProduct := (mulChecked_ok_iff.mp cwOk).2
  rcases justifyCheckpoint_ok secondOk with ⟨enough, epoch⟩ | ⟨_, same⟩
  · refine .inl ⟨epoch, ?_⟩
    have bound := UInt64.le_iff_toNat_le.mp (of_decide_eq_true enough)
    simp only [UInt64.reduceToNat] at previousProduct totalProduct currentProduct
    omega
  · rcases justifyCheckpoint_ok firstOk with ⟨enough, epoch⟩ | ⟨_, unchanged⟩
    · refine .inr ⟨same ▸ epoch, ?_⟩
      have bound := UInt64.le_iff_toNat_le.mp (of_decide_eq_true enough)
      simp only [UInt64.reduceToNat] at previousProduct totalProduct currentProduct
      omega
    · exact (changed (same.trans unchanged)).elim

/-- A changed justified checkpoint is the checkpoint read at a successful target threshold.

Both the root and epoch are those returned by the actual block-root accessor. -/
theorem weighJustificationAndFinalization_justified_root {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (changed : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint) :
    getBlockRoot state after.currentJustifiedCheckpoint.epoch =
      .ok after.currentJustifiedCheckpoint.root := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, first, firstOk, _, _, second, secondOk,
    _, _, _, _, _, _, _, _, rfl⟩ := computed
  dsimp only at changed ⊢
  by_cases secondChanged : second ≠ first
  · obtain ⟨_, epoch, root⟩ := justifyCheckpoint_changed secondOk secondChanged
    rw [epoch]
    exact root
  · have same : second = first := Classical.not_not.mp secondChanged
    have firstChanged : first ≠ state.currentJustifiedCheckpoint := by
      simpa only [same] using changed
    obtain ⟨_, epoch, root⟩ := justifyCheckpoint_changed firstOk firstChanged
    rw [same, epoch]
    exact root

/-- Weighing cannot lower a settled current justified epoch.

The previous epoch is weighed before the current one, and both are at least the stored epoch. -/
theorem weighJustificationAndFinalization_justified_mono {total previous current : Gwei}
    (settled : state.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch state)
    (computed : weighJustificationAndFinalization state total previous current = .ok after) :
    state.currentJustifiedCheckpoint.epoch ≤ after.currentJustifiedCheckpoint.epoch := by
  by_cases unchanged : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
  · rw [unchanged]
    exact UInt64.le_refl _
  · rcases weighJustificationAndFinalization_threshold computed unchanged with
        ⟨epoch, _⟩ | ⟨epoch, _⟩
    · rw [epoch]
      exact UInt64.le_trans settled (getPreviousEpoch_le state)
    · rw [epoch]
      exact settled

/-- A matching target attestation comes from the source list and has the epoch's block root.

The source list itself relies on the source check at inclusion, not a second source check here. -/
theorem getMatchingTargetAttestations_mem {before : fork < .altair} {epoch : Epoch}
    {attestations : Array (PendingAttestation preset)} {attestation : PendingAttestation preset}
    (computed : getMatchingTargetAttestations state before epoch = .ok attestations)
    (member : attestation ∈ attestations) :
    ∃ sources root, getMatchingSourceAttestations state before epoch = .ok sources ∧
      getBlockRoot state epoch = .ok root ∧ attestation ∈ sources ∧
      attestation.data.target.root = root := by
  unfold getMatchingTargetAttestations at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨sources, sourceOk, rest⟩ := computed
  split at rest
  · simp only [pure, Except.pure, Except.ok.injEq] at rest
    subst attestations
    simp at member
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨root, rootOk, rfl⟩ := rest
    exact ⟨sources, root, sourceOk, rootOk, (Array.mem_filter.mp member).1,
      by simpa using (Array.mem_filter.mp member).2⟩

/-- A target balance with source matching counts attestations from the stored justified source.

The source is the previous checkpoint for previous-epoch targets and the current one otherwise. -/
theorem getMatchingTargetAttestations_source {before : fork < .altair} {epoch : Epoch}
    {attestations : Array (PendingAttestation preset)} {pending : PendingAttestation preset}
    (holds : PendingSourcesMatch state before)
    (computed : getMatchingTargetAttestations state before epoch = .ok attestations)
    (member : pending ∈ attestations) :
    pending.data.source = if epoch = getCurrentEpoch state then
      state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint := by
  obtain ⟨_, _, sources, _, included, _⟩ := getMatchingTargetAttestations_mem computed member
  exact getMatchingSourceAttestations_source holds sources included

/-- Target matching reads attestations whose checked slot belongs to the requested epoch. -/
theorem getMatchingTargetAttestations_slot_epoch {before : fork < .altair} {epoch : Epoch}
    {attestations : Array (PendingAttestation preset)} {pending : PendingAttestation preset}
    (holds : PendingEpochsMatch state before)
    (computed : getMatchingTargetAttestations state before epoch = .ok attestations)
    (member : pending ∈ attestations) :
    pending.data.target.epoch = epoch ∧ computeEpochAtSlot preset pending.data.slot = epoch := by
  obtain ⟨_, _, sources, _, included, _⟩ := getMatchingTargetAttestations_mem computed member
  simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at sources
  obtain ⟨_, recent, rfl⟩ := sources
  by_cases current : epoch = getCurrentEpoch state
  · simp only [current, ↓reduceIte] at included ⊢
    exact holds.1 pending included
  · simp only [current, ↓reduceIte] at included
    rw [recent.resolve_right current]
    exact holds.2 pending included

/-- Every reconstructed target signer is active at that target epoch.

For previous-epoch targets this does not assert membership in the current denominator. -/
theorem mem_getActiveValidatorIndices_of_target {before : fork < .altair} {epoch : Epoch}
    {attestations : Array (PendingAttestation preset)} {indices : List ValidatorIndex}
    (holds : PendingEpochsMatch state before)
    (matching : getMatchingTargetAttestations state before epoch = .ok attestations)
    (computed : getUnslashedAttestingIndices state attestations = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices) :
    index ∈ getActiveValidatorIndices state epoch := by
  obtain ⟨⟨pending, included, signers, signersOk, signer⟩, _⟩ :=
    mem_getUnslashedAttestingIndices computed member
  have epoch := (getMatchingTargetAttestations_slot_epoch holds matching included).2
  simpa only [epoch] using mem_getActiveValidatorIndices_of_pending signersOk signer

/-- Every signer counted for the current target is in the current active denominator.

The pending-epoch invariant connects committee reconstruction to that denominator. -/
theorem mem_getActiveValidatorIndices_of_current_target {before : fork < .altair}
    {attestations : Array (PendingAttestation preset)} {indices : List ValidatorIndex}
    (holds : PendingEpochsMatch state before)
    (matching : getMatchingTargetAttestations state before (getCurrentEpoch state) =
      .ok attestations)
    (computed : getUnslashedAttestingIndices state attestations = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices) :
    index ∈ getActiveValidatorIndices state (getCurrentEpoch state) :=
  mem_getActiveValidatorIndices_of_target holds matching computed member

/-- A previous-epoch validator absent from the current denominator exits at the current epoch.

The previous epoch saturates at zero, so the conclusion also excludes such a gap at genesis. -/
theorem previous_active_not_current_exits_now (validator : Validator)
    (previous : isActiveValidator validator (getPreviousEpoch state) = true)
    (current : isActiveValidator validator (getCurrentEpoch state) = false) :
    validator.exitEpoch = getCurrentEpoch state := by
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at previous
  have earlier := UInt64.le_iff_toNat_le.mp previous.1
  have later := UInt64.lt_iff_toNat_lt.mp previous.2
  have age : (getPreviousEpoch state).toNat = (getCurrentEpoch state).toNat - 1 := by
    simp only [getPreviousEpoch, toNat_saturatingSub]
    rfl
  have absent : ¬ (validator.activationEpoch ≤ getCurrentEpoch state ∧
      getCurrentEpoch state < validator.exitEpoch) := by
    intro active
    have yes : isActiveValidator validator (getCurrentEpoch state) = true := by
      simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq]
      exact active
    rw [current] at yes
    cases yes
  have activated : validator.activationEpoch ≤ getCurrentEpoch state := by
    rw [UInt64.le_iff_toNat_le]
    omega
  have exited : validator.exitEpoch.toNat ≤ (getCurrentEpoch state).toNat := by
    by_cases le : validator.exitEpoch.toNat ≤ (getCurrentEpoch state).toNat
    · exact le
    · exact (absent ⟨activated, UInt64.lt_iff_toNat_lt.mpr (by omega)⟩).elim
  apply UInt64.toNat_inj.mp
  omega

/-- A reconstructed previous-target signer outside the denominator exits in this epoch.

No activation or deposit can create this mismatch between consecutive active sets. -/
theorem previous_target_signer_outside_active_exits_now {before : fork < .altair}
    {attestations : Array (PendingAttestation preset)} {indices : List ValidatorIndex}
    (within : state.RegistryWithinLimit) (holds : PendingEpochsMatch state before)
    (matching : getMatchingTargetAttestations state before (getPreviousEpoch state) =
      .ok attestations)
    (computed : getUnslashedAttestingIndices state attestations = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices)
    (outside : index ∉ getActiveValidatorIndices state (getCurrentEpoch state)) :
    ∃ validator, state.validators.data[index.toNat]? = some validator ∧
      validator.exitEpoch = getCurrentEpoch state := by
  obtain ⟨validator, found, previous⟩ := (mem_getActiveValidatorIndices within).mp
    (mem_getActiveValidatorIndices_of_target holds matching computed member)
  have current : isActiveValidator validator (getCurrentEpoch state) = false := by
    cases active : isActiveValidator validator (getCurrentEpoch state)
    · rfl
    · exact (outside ((mem_getActiveValidatorIndices within).mpr
        ⟨validator, found, active⟩)).elim
  exact ⟨validator, found, previous_active_not_current_exits_now validator previous current⟩

/-- Previous-target weight outside the denominator is bounded by this epoch's exiting weight.

The bound counts each registry entry once, even if several attestations name it. -/
theorem previous_target_outside_active_balance_le_exits {before : fork < .altair}
    {attestations : Array (PendingAttestation preset)} {indices : List ValidatorIndex}
    (within : state.RegistryWithinLimit) (holds : PendingEpochsMatch state before)
    (matching : getMatchingTargetAttestations state before (getPreviousEpoch state) =
      .ok attestations)
    (computed : getUnslashedAttestingIndices state attestations = .ok indices) :
    participatingOutsideActiveBalance state indices ≤
      ((state.validators.data.toList.filter
          (fun validator => validator.exitEpoch == getCurrentEpoch state)).map
        (·.effectiveBalance.toNat)).sum := by
  apply sumMarked_le_filter
  intro validator member
  obtain ⟨position, found⟩ := Array.mem_iff_getElem?.mp member
  simp only [Array.zip_eq_zipWith, Array.getElem?_zipWith, getElem?_markIndices] at found
  by_cases inside : position < state.validators.data.size
  · simp only [inside, ↓reduceIte] at found
    cases atPosition : state.validators.data[position]? with
    | none => simp [atPosition] at found
    | some entry =>
      simp only [atPosition, Option.some.injEq, Prod.mk.injEq,
        Bool.and_eq_true, Bool.not_eq_true'] at found
      obtain ⟨rfl, marked, absent⟩ := found
      obtain ⟨index, included, same⟩ := List.any_eq_true.mp marked
      have indexEq : index.toNat = position := of_decide_eq_true same
      have outside : index ∉ getActiveValidatorIndices state (getCurrentEpoch state) := by
        intro active
        have present : (getActiveValidatorIndices state (getCurrentEpoch state)).any
            (·.toNat == position) = true :=
          List.any_eq_true.mpr ⟨index, active, same⟩
        rw [present] at absent
        cases absent
      obtain ⟨other, otherFound, exits⟩ :=
        previous_target_signer_outside_active_exits_now within holds matching computed
          included outside
      rw [indexEq, atPosition] at otherFound
      cases otherFound
      simp only [exits, beq_self_eq_true]
  · simp [inside] at found

/-- The previous-voter gap costs at most one effective-balance cap per exit in this epoch.

This separates the balance invariant from the exit-queue population bound. -/
theorem previous_target_outside_active_balance_le_exit_count {before : fork < .altair}
    {attestations : Array (PendingAttestation preset)} {indices : List ValidatorIndex}
    (within : state.RegistryWithinLimit) (holds : PendingEpochsMatch state before)
    (bounded : ∀ validator ∈ state.validators.data,
      validator.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE)
    (matching : getMatchingTargetAttestations state before (getPreviousEpoch state) =
      .ok attestations)
    (computed : getUnslashedAttestingIndices state attestations = .ok indices) :
    participatingOutsideActiveBalance state indices ≤
      (state.validators.data.toList.filter
        (fun validator => validator.exitEpoch == getCurrentEpoch state)).length *
          preset.MAX_EFFECTIVE_BALANCE.toNat := by
  have cap : ∀ (validators : List Validator),
      (∀ validator ∈ validators,
        validator.effectiveBalance.toNat ≤ preset.MAX_EFFECTIVE_BALANCE.toNat) →
      (validators.map (·.effectiveBalance.toNat)).sum ≤
        validators.length * preset.MAX_EFFECTIVE_BALANCE.toNat := by
    intro validators
    induction validators with
    | nil => intro _; simp
    | cons validator validators ih =>
      intro bounded
      have first := bounded validator List.mem_cons_self
      have rest := ih (fun other member => bounded other (List.mem_cons_of_mem _ member))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      omega
  apply Nat.le_trans (previous_target_outside_active_balance_le_exits
    within holds matching computed)
  apply cap
  intro validator member
  exact UInt64.le_iff_toNat_le.mp (bounded validator (by
    simpa using (List.mem_filter.mp member).1))

/-- Before Altair, a changed justified checkpoint has a computed target balance above threshold.

The attestations and balances here are exactly those read by the epoch transition. -/
theorem processJustificationAndFinalization_target_balance (before : fork < .altair)
    (computed : processJustificationAndFinalization state = .ok after)
    (changed : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint) :
    ∃ epoch attestations total target,
      (epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state) ∧
      getMatchingTargetAttestations state before epoch = .ok attestations ∧
      getTotalActiveBalance state = .ok total ∧
      getAttestingBalance state attestations = .ok target ∧
      after.currentJustifiedCheckpoint.epoch = epoch ∧
      2 * total.toNat ≤ 3 * target.toNat := by
  unfold processJustificationAndFinalization at computed
  split at computed
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact (changed (computed.symm ▸ rfl)).elim
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨previous, previousOk, current, currentOk, total, totalOk,
      previousBalance, previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
    rcases weighJustificationAndFinalization_threshold weighed changed with
      ⟨epoch, enough⟩ | ⟨epoch, enough⟩
    · exact ⟨_, current, total, currentBalance, .inr rfl, currentOk, totalOk,
        currentBalanceOk, epoch, enough⟩
    · exact ⟨_, previous, total, previousBalance, .inl rfl, previousOk, totalOk,
        previousBalanceOk, epoch, enough⟩

/-- A changed justified checkpoint has enough concrete pending signers, up to the target floor.

Each counted index belongs to a pending attestation with the epoch's block root.

The signer is active at the attestation slot's epoch and is not slashed.

The source and signature provenance still require the history of attestation processing. -/
theorem processJustificationAndFinalization_pending_signers (before : fork < .altair)
    (computed : processJustificationAndFinalization state = .ok after)
    (changed : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint) :
    ∃ epoch attestations indices,
      (epoch = getPreviousEpoch state ∨ epoch = getCurrentEpoch state) ∧
      getMatchingTargetAttestations state before epoch = .ok attestations ∧
      getUnslashedAttestingIndices state attestations = .ok indices ∧
      after.currentJustifiedCheckpoint.epoch = epoch ∧
      2 * sumMarked state.validators.data
          (markIndices state.validators.data.size
            (getActiveValidatorIndices state (getCurrentEpoch state))) ≤
        3 * sumMarked state.validators.data (markIndices state.validators.data.size indices) +
          3 * totalBalanceFloor state indices ∧
      (∀ index ∈ indices,
        (∃ attestation ∈ attestations, ∃ signers root,
          getPendingAttestingIndices state attestation = .ok signers ∧ index ∈ signers ∧
          getBlockRoot state epoch = .ok root ∧ attestation.data.target.root = root ∧
          index ∈ getActiveValidatorIndices state
            (computeEpochAtSlot preset attestation.data.slot)) ∧
        ∃ validator, getValidator state index = .ok validator ∧ validator.slashed = false) := by
  obtain ⟨epoch, attestations, total, target, recent, matching, active, attesting,
    epochEq, enough⟩ := processJustificationAndFinalization_target_balance before computed changed
  simp only [getAttestingBalance, bind_ok_iff] at attesting
  obtain ⟨indices, indicesOk, targetOk⟩ := attesting
  refine ⟨epoch, attestations, indices, recent, matching, indicesOk, epochEq,
    getTotalBalance_threshold_raw active targetOk enough, ?_⟩
  intro index member
  obtain ⟨⟨attestation, pending, signers, signersOk, signer⟩, validator⟩ :=
    mem_getUnslashedAttestingIndices indicesOk member
  obtain ⟨_, root, _, rootOk, _, rootEq⟩ := getMatchingTargetAttestations_mem matching pending
  exact ⟨⟨attestation, pending, signers, root, signersOk, signer, rootOk, rootEq,
    mem_getActiveValidatorIndices_of_pending signersOk signer⟩, validator⟩

/-- The newest bit records this call's current threshold.

The next bit records its previous threshold or the old newest bit.

Thus a true next bit alone does not imply that this call met the previous threshold. -/
theorem weighJustificationAndFinalization_bits {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after) :
    (after.justificationBits.bits[0] = true ↔ 2 * total.toNat ≤ 3 * current.toNat) ∧
    (after.justificationBits.bits[1] = true ↔
      2 * total.toNat ≤ 3 * previous.toNat ∨ state.justificationBits.bits[0] = true) := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨pw, pwOk, threshold, thresholdOk, _, _, cw, cwOk, _, _,
    _, _, _, _, _, _, _, _, rfl⟩ := computed
  simp only [liftArith, mapError_ok_iff, mulChecked_ok_iff] at pwOk thresholdOk cwOk
  dsimp only
  simp [shiftJustificationBits, UInt64.le_iff_toNat_le]
  simp only [UInt64.reduceToNat] at pwOk thresholdOk cwOk
  rw [pwOk.2, thresholdOk.2, cwOk.2]
  simp [Nat.mul_comm]

/-- A current threshold sets the justified checkpoint to that exact epoch and cached root.

This also holds when the checkpoint value does not change. -/
theorem weighJustificationAndFinalization_current_checkpoint {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (bit : after.justificationBits.bits[0] = true) :
    after.currentJustifiedCheckpoint.epoch = getCurrentEpoch state ∧
      getBlockRoot state (getCurrentEpoch state) = .ok after.currentJustifiedCheckpoint.root := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, weight, weightOk, checkpoint, checkpointOk,
    _, _, _, _, _, _, _, _, rfl⟩ := computed
  simp only [Vector.getElem_set_self, decide_eq_true_eq] at bit
  simp only [justifyCheckpoint] at checkpointOk
  split at checkpointOk
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at checkpointOk
    obtain ⟨root, rootOk, rfl⟩ := checkpointOk
    exact ⟨rfl, rootOk⟩
  · rename_i notEnough
    exact (notEnough (by simpa using bit)).elim

/-- A changed justified checkpoint has the true bit for its selected target epoch.

The previous bit is allowed to be inherited here; the current threshold always sets bit zero. -/
theorem weighJustificationAndFinalization_justified_bit {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (changed : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint) :
    (after.currentJustifiedCheckpoint.epoch = getCurrentEpoch state ∧
      after.justificationBits.bits[0] = true) ∨
    (after.currentJustifiedCheckpoint.epoch = getPreviousEpoch state ∧
      after.justificationBits.bits[1] = true) := by
  have bits := weighJustificationAndFinalization_bits computed
  rcases weighJustificationAndFinalization_threshold computed changed with
      ⟨epoch, enough⟩ | ⟨epoch, enough⟩
  · exact .inl ⟨epoch, bits.1.mpr enough⟩
  · exact .inr ⟨epoch, bits.2.mpr (.inl enough)⟩

/-- A newest true bit has an actual current-epoch threshold computation behind it.

Unlike a changed checkpoint, this witness also covers a checkpoint already justified before.

It retains both balance accessors and the exact call that weighs them. -/
theorem processJustificationAndFinalization_current_bit (before : fork < .altair)
    (computed : processJustificationAndFinalization state = .ok after)
    (eligible : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (bit : after.justificationBits.bits[0] = true) :
    ∃ previous current total previousBalance currentBalance,
      getMatchingTargetAttestations state before (getPreviousEpoch state) = .ok previous ∧
      getMatchingTargetAttestations state before (getCurrentEpoch state) = .ok current ∧
      getTotalActiveBalance state = .ok total ∧
      getAttestingBalance state previous = .ok previousBalance ∧
      getAttestingBalance state current = .ok currentBalance ∧
      weighJustificationAndFinalization state total previousBalance currentBalance = .ok after ∧
      2 * total.toNat ≤ 3 * currentBalance.toNat := by
  unfold processJustificationAndFinalization at computed
  split at computed
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨previous, previousOk, current, currentOk, total, totalOk, previousBalance,
    previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
  exact ⟨previous, current, total, previousBalance, currentBalance, previousOk, currentOk,
    totalOk, previousBalanceOk, currentBalanceOk, weighed,
    (weighJustificationAndFinalization_bits weighed).1.mp bit⟩

/-- A newly set previous bit has a previous-target threshold behind it.

An already set current bit instead survives the shift, without another threshold computation. -/
theorem processJustificationAndFinalization_previous_bit (before : fork < .altair)
    (computed : processJustificationAndFinalization state = .ok after)
    (eligible : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (bit : after.justificationBits.bits[1] = true)
    (notInherited : state.justificationBits.bits[0] = false) :
    ∃ previous current total previousBalance currentBalance,
      getMatchingTargetAttestations state before (getPreviousEpoch state) = .ok previous ∧
      getMatchingTargetAttestations state before (getCurrentEpoch state) = .ok current ∧
      getTotalActiveBalance state = .ok total ∧
      getAttestingBalance state previous = .ok previousBalance ∧
      getAttestingBalance state current = .ok currentBalance ∧
      weighJustificationAndFinalization state total previousBalance currentBalance = .ok after ∧
      2 * total.toNat ≤ 3 * previousBalance.toNat := by
  unfold processJustificationAndFinalization at computed
  split at computed
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨previous, previousOk, current, currentOk, total, totalOk, previousBalance,
    previousBalanceOk, currentBalance, currentBalanceOk, weighed⟩ := computed
  have threshold := (weighJustificationAndFinalization_bits weighed).2.mp bit
  simp only [notInherited, Bool.false_eq_true, or_false] at threshold
  exact ⟨previous, current, total, previousBalance, currentBalance, previousOk, currentOk,
    totalOk, previousBalanceOk, currentBalanceOk, weighed, threshold⟩

/-- The current justification bit counts actual pending signers, retaining the increment floor.

The source is the checkpoint checked at inclusion when the pending-source invariant holds.

Membership in the current active denominator still requires the pending target-epoch invariant. -/
theorem processJustificationAndFinalization_current_bit_signers (before : fork < .altair)
    (computed : processJustificationAndFinalization state = .ok after)
    (eligible : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (bit : after.justificationBits.bits[0] = true)
    (sources : PendingSourcesMatch state before) :
    ∃ attestations indices,
      getMatchingTargetAttestations state before (getCurrentEpoch state) = .ok attestations ∧
      getUnslashedAttestingIndices state attestations = .ok indices ∧
      2 * sumMarked state.validators.data
          (markIndices state.validators.data.size
            (getActiveValidatorIndices state (getCurrentEpoch state))) ≤
        3 * sumMarked state.validators.data (markIndices state.validators.data.size indices) +
          3 * totalBalanceFloor state indices ∧
      (∀ index ∈ indices,
        (∃ pending ∈ attestations, ∃ signers root,
          getPendingAttestingIndices state pending = .ok signers ∧ index ∈ signers ∧
          pending.data.source = state.currentJustifiedCheckpoint ∧
          getBlockRoot state (getCurrentEpoch state) = .ok root ∧
          pending.data.target.root = root) ∧
        ∃ validator, getValidator state index = .ok validator ∧ validator.slashed = false) := by
  obtain ⟨_, current, total, _, target, _, matching, totalOk, _, targetOk, _, enough⟩ :=
    processJustificationAndFinalization_current_bit before computed eligible bit
  simp only [getAttestingBalance, bind_ok_iff] at targetOk
  obtain ⟨indices, indicesOk, targetOk⟩ := targetOk
  refine ⟨current, indices, matching, indicesOk,
    getTotalBalance_threshold_raw totalOk targetOk enough, ?_⟩
  intro index member
  obtain ⟨⟨pending, pendingMember, signers, signersOk, signer⟩, validator⟩ :=
    mem_getUnslashedAttestingIndices indicesOk member
  obtain ⟨_, root, _, rootOk, _, rootEq⟩ :=
    getMatchingTargetAttestations_mem matching pendingMember
  have source := getMatchingTargetAttestations_source sources matching pendingMember
  simp only [↓reduceIte] at source
  exact ⟨⟨pending, pendingMember, signers, root, signersOk, signer, source, rootOk, rootEq⟩,
    validator⟩

/-- A new previous bit counts pending signers with the stored previous justified source.

Its threshold still uses the current active denominator, not the previous active set. -/
theorem processJustificationAndFinalization_previous_bit_signers (before : fork < .altair)
    (computed : processJustificationAndFinalization state = .ok after)
    (eligible : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (bit : after.justificationBits.bits[1] = true)
    (notInherited : state.justificationBits.bits[0] = false)
    (sources : PendingSourcesMatch state before) :
    ∃ attestations indices,
      getMatchingTargetAttestations state before (getPreviousEpoch state) = .ok attestations ∧
      getUnslashedAttestingIndices state attestations = .ok indices ∧
      2 * sumMarked state.validators.data
          (markIndices state.validators.data.size
            (getActiveValidatorIndices state (getCurrentEpoch state))) ≤
        3 * sumMarked state.validators.data (markIndices state.validators.data.size indices) +
          3 * totalBalanceFloor state indices ∧
      (∀ index ∈ indices,
        (∃ pending ∈ attestations, ∃ signers root,
          getPendingAttestingIndices state pending = .ok signers ∧ index ∈ signers ∧
          pending.data.source = state.previousJustifiedCheckpoint ∧
          getBlockRoot state (getPreviousEpoch state) = .ok root ∧
          pending.data.target.root = root) ∧
        ∃ validator, getValidator state index = .ok validator ∧ validator.slashed = false) := by
  obtain ⟨previous, _, total, target, _, matching, _, totalOk, targetOk, _, _, enough⟩ :=
    processJustificationAndFinalization_previous_bit before computed eligible bit notInherited
  simp only [getAttestingBalance, bind_ok_iff] at targetOk
  obtain ⟨indices, indicesOk, targetOk⟩ := targetOk
  refine ⟨previous, indices, matching, indicesOk,
    getTotalBalance_threshold_raw totalOk targetOk enough, ?_⟩
  intro index member
  obtain ⟨⟨pending, pendingMember, signers, signersOk, signer⟩, validator⟩ :=
    mem_getUnslashedAttestingIndices indicesOk member
  obtain ⟨_, root, _, rootOk, _, rootEq⟩ :=
    getMatchingTargetAttestations_mem matching pendingMember
  have source := getMatchingTargetAttestations_source sources matching pendingMember
  have notCurrent : getPreviousEpoch state ≠ getCurrentEpoch state := by
    have positive : getCurrentEpoch state ≠ 0 := by
      intro zero
      apply eligible
      simp [zero, GENESIS_EPOCH]
    intro equal
    have := congrArg UInt64.toNat equal
    simp only [getPreviousEpoch, toNat_saturatingSub, UInt64.toNat_one] at this
    have nonzero : (getCurrentEpoch state).toNat ≠ 0 := by
      intro zero
      apply positive
      exact UInt64.toNat_inj.mp zero
    omega
  simp only [notCurrent, ↓reduceIte] at source
  exact ⟨⟨pending, pendingMember, signers, root, signersOk, signer, source, rootOk, rootEq⟩,
    validator⟩

/-- The two oldest justification bits retain the preceding call's two middle bits.

Only the newest two positions can receive a threshold result in this call. -/
theorem weighJustificationAndFinalization_old_bits {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after) :
    after.justificationBits.bits[2] = state.justificationBits.bits[1] ∧
      after.justificationBits.bits[3] = state.justificationBits.bits[2] := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
  simp [shiftJustificationBits]

/-- A true justification bit is a new threshold result or a shifted true bit.

The previous-epoch threshold is needed only when the shifted current bit was false.

The returned index states exactly which earlier bit supplies an inherited result. -/
theorem weighJustificationAndFinalization_bit_origin {total previous current : Gwei}
    {index : Fin 4}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (bit : after.justificationBits.bits[index] = true) :
    (index.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
      (index.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
        state.justificationBits.bits[0] = false) ∨
      ∃ earlier : Fin 4,
        index.val = earlier.val + 1 ∧ state.justificationBits.bits[earlier] = true := by
  have thresholds := weighJustificationAndFinalization_bits computed
  have old := weighJustificationAndFinalization_old_bits computed
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
    have bound := index.isLt
    have values : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨ index.val = 3 := by omega
    rcases values with value | value | value | value
    · exact .inl (Fin.ext value)
    · exact .inr (.inl (Fin.ext value))
    · exact .inr (.inr (.inl (Fin.ext value)))
    · exact .inr (.inr (.inr (Fin.ext value)))
  rcases cases with rfl | rfl | rfl | rfl
  · exact .inl ⟨rfl, thresholds.1.mp bit⟩
  · by_cases inherited : state.justificationBits.bits[0] = true
    · exact .inr (.inr ⟨0, rfl, inherited⟩)
    · have cleared : state.justificationBits.bits[0] = false := by
        cases flag : state.justificationBits.bits[0] <;> simp_all
      exact .inr (.inl ⟨rfl, (thresholds.2.mp bit).resolve_right inherited, cleared⟩)
  · exact .inr (.inr ⟨1, rfl, old.1 ▸ bit⟩)
  · exact .inr (.inr ⟨2, rfl, old.2 ▸ bit⟩)

/-- The checkpoints that weighing the votes sets.

The old current justified checkpoint becomes the previous one.

The new current justified checkpoint is the old one, or that of the previous or the current epoch.

The new finalized checkpoint is the old one, or one of the two old justified checkpoints.

Nothing else changes but the bits of justification. -/
theorem weighJustificationAndFinalization_checkpoints {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after) :
    after.previousJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
      (after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
        after.currentJustifiedCheckpoint.epoch = getPreviousEpoch state ∨
        after.currentJustifiedCheckpoint.epoch = getCurrentEpoch state) ∧
      (after.finalizedCheckpoint = state.finalizedCheckpoint ∨
        after.finalizedCheckpoint = state.previousJustifiedCheckpoint ∨
        after.finalizedCheckpoint = state.currentJustifiedCheckpoint) ∧
      { after with
        previousJustifiedCheckpoint := state.previousJustifiedCheckpoint,
        currentJustifiedCheckpoint := state.currentJustifiedCheckpoint,
        justificationBits := state.justificationBits,
        finalizedCheckpoint := state.finalizedCheckpoint } = state := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, first, firstOk, _, _, second, secondOk, _, _, _, _, _, _, _, _, rfl⟩ :=
    computed
  refine ⟨rfl, ?_, ?_, rfl⟩
  · rcases justifyCheckpoint_ok secondOk with ⟨_, epoch⟩ | ⟨_, rfl⟩
    · exact .inr (.inr epoch)
    · rcases justifyCheckpoint_ok firstOk with ⟨_, epoch⟩ | ⟨_, rfl⟩
      · exact .inr (.inl epoch)
      · exact .inl rfl
  · dsimp only
    split
    · exact .inr (.inr rfl)
    · split
      · exact .inr (.inl rfl)
      · exact .inl rfl

/-- Every changed finalization satisfies one of the four concrete epoch-and-bit rules.

The bits belong to the result of this weighing call, not to an abstract finality predicate. -/
theorem weighJustificationAndFinalization_finalized_rules {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (changed : after.finalizedCheckpoint ≠ state.finalizedCheckpoint) :
    (after.finalizedCheckpoint = state.currentJustifiedCheckpoint ∧
      ((after.justificationBits.bits[0] = true ∧ after.justificationBits.bits[1] = true ∧
          after.justificationBits.bits[2] = true ∧
          state.currentJustifiedCheckpoint.epoch.toNat + 2 = (getCurrentEpoch state).toNat) ∨
        (after.justificationBits.bits[0] = true ∧ after.justificationBits.bits[1] = true ∧
          state.currentJustifiedCheckpoint.epoch.toNat + 1 = (getCurrentEpoch state).toNat))) ∨
    (after.finalizedCheckpoint = state.previousJustifiedCheckpoint ∧
      ((after.justificationBits.bits[1] = true ∧ after.justificationBits.bits[2] = true ∧
          after.justificationBits.bits[3] = true ∧
          state.previousJustifiedCheckpoint.epoch.toNat + 3 = (getCurrentEpoch state).toNat) ∨
        (after.justificationBits.bits[1] = true ∧ after.justificationBits.bits[2] = true ∧
          state.previousJustifiedCheckpoint.epoch.toNat + 2 = (getCurrentEpoch state).toNat))) := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, p3, p3Ok, p2, p2Ok, c2, c2Ok, c1, c1Ok, rfl⟩ :=
    computed
  dsimp only at changed ⊢
  split
  · rename_i currentRule
    refine .inl ⟨rfl, ?_⟩
    have currentCases : c2 = true ∨ c1 = true := by simpa using currentRule
    rcases currentCases with yes | yes
    · subst c2
      obtain ⟨bits, gap⟩ := finalizes_true c2Ok
      simp only [Bool.and_eq_true] at bits
      exact .inl ⟨bits.1.1, bits.1.2, bits.2, gap⟩
    · subst c1
      obtain ⟨bits, gap⟩ := finalizes_true c1Ok
      simp only [Bool.and_eq_true] at bits
      exact .inr ⟨bits.1, bits.2, gap⟩
  · split
    · rename_i previousRule
      refine .inr ⟨rfl, ?_⟩
      have previousCases : p3 = true ∨ p2 = true := by simpa using previousRule
      rcases previousCases with yes | yes
      · subst p3
        obtain ⟨bits, gap⟩ := finalizes_true p3Ok
        simp only [Bool.and_eq_true] at bits
        exact .inl ⟨bits.1.1, bits.1.2, bits.2, gap⟩
      · subst p2
        obtain ⟨bits, gap⟩ := finalizes_true p2Ok
        simp only [Bool.and_eq_true] at bits
        exact .inr ⟨bits.1, bits.2, gap⟩
    · exact (changed (by simp_all)).elim

/-- A changed finalization identifies the source field and the last target bit of its rule.

The final bit is current or previous, with the source one or two epochs before its target. -/
theorem weighJustificationAndFinalization_finalized_endpoint {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (changed : after.finalizedCheckpoint ≠ state.finalizedCheckpoint) :
    (after.finalizedCheckpoint = state.currentJustifiedCheckpoint ∧
      after.justificationBits.bits[0] = true ∧
      (after.finalizedCheckpoint.epoch.toNat + 1 = (getCurrentEpoch state).toNat ∨
        after.finalizedCheckpoint.epoch.toNat + 2 = (getCurrentEpoch state).toNat)) ∨
    (after.finalizedCheckpoint = state.previousJustifiedCheckpoint ∧
      after.justificationBits.bits[1] = true ∧
      (after.finalizedCheckpoint.epoch.toNat + 2 = (getCurrentEpoch state).toNat ∨
        after.finalizedCheckpoint.epoch.toNat + 3 = (getCurrentEpoch state).toNat)) := by
  rcases weighJustificationAndFinalization_finalized_rules computed changed with
      ⟨assigned, two | one⟩ | ⟨assigned, three | two⟩
  · exact .inl ⟨assigned, two.1, .inr (assigned ▸ two.2.2.2)⟩
  · exact .inl ⟨assigned, one.1, .inl (assigned ▸ one.2.2)⟩
  · exact .inr ⟨assigned, three.1, .inr (assigned ▸ three.2.2.2)⟩
  · exact .inr ⟨assigned, two.1, .inl (assigned ▸ two.2.2)⟩

/-- The last target required by a changed finalization is strictly after its checkpoint.

Both previous-checkpoint rules use the previous epoch, not the current epoch. -/
theorem weighJustificationAndFinalization_finalized_target_gt {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (changed : after.finalizedCheckpoint ≠ state.finalizedCheckpoint) :
    (after.finalizedCheckpoint = state.currentJustifiedCheckpoint ∧
      after.justificationBits.bits[0] = true ∧
      after.finalizedCheckpoint.epoch.toNat < (getCurrentEpoch state).toNat) ∨
    (after.finalizedCheckpoint = state.previousJustifiedCheckpoint ∧
      after.justificationBits.bits[1] = true ∧
      after.finalizedCheckpoint.epoch.toNat < (getPreviousEpoch state).toNat) := by
  rcases weighJustificationAndFinalization_finalized_endpoint computed changed with
      ⟨assigned, bit, gap⟩ | ⟨assigned, bit, gap⟩
  · exact .inl ⟨assigned, bit, by rcases gap with gap | gap <;> omega⟩
  · refine .inr ⟨assigned, bit, ?_⟩
    simp only [getPreviousEpoch, toNat_saturatingSub, UInt64.toNat_one]
    rcases gap with gap | gap <;> omega

/-- Every changed finalization has a true bit for the epoch immediately after its checkpoint.

The longer finalization rules require this intermediate justified epoch too.

The equation identifies the bit's target epoch without introducing a finalization model. -/
theorem weighJustificationAndFinalization_finalized_successor_bit {total previous current : Gwei}
    (computed : weighJustificationAndFinalization state total previous current = .ok after)
    (changed : after.finalizedCheckpoint ≠ state.finalizedCheckpoint) :
    ∃ index : Fin 4, after.justificationBits.bits[index] = true ∧
      after.finalizedCheckpoint.epoch.toNat + 1 + index.val = (getCurrentEpoch state).toNat := by
  rcases weighJustificationAndFinalization_finalized_rules computed changed with
      ⟨assigned, two | one⟩ | ⟨assigned, three | two⟩
  · refine ⟨1, two.2.1, ?_⟩
    rw [assigned]
    omega
  · refine ⟨0, one.1, ?_⟩
    rw [assigned]
    omega
  · refine ⟨2, three.2.1, ?_⟩
    rw [assigned]
    omega
  · refine ⟨1, two.1, ?_⟩
    rw [assigned]
    omega

/-- Weighing the votes keeps the checkpoints in order.

The current justified epoch must be at most the previous epoch.

The finalized epoch then does not decrease. -/
theorem weighJustificationAndFinalization_ordered {total previous current : Gwei}
    (ordered : CheckpointsOrdered state)
    (settled : state.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch state)
    (computed : weighJustificationAndFinalization state total previous current = .ok after) :
    CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  obtain ⟨previousJustified, currentJustified, finalized, _⟩ :=
    weighJustificationAndFinalization_checkpoints computed
  obtain ⟨finalizedLe, previousLe⟩ := ordered
  have epochs := getPreviousEpoch_le state
  simp only [CheckpointsOrdered, UInt64.le_iff_toNat_le] at *
  rw [previousJustified]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rcases finalized with same | same | same <;> rw [same] <;> omega
  · rcases currentJustified with same | same | same <;> rw [same] <;> omega
  · rcases finalized with same | same | same <;> rw [same] <;> omega

/-- In the first two epochs, justification and finalization change nothing before Altair. -/
theorem processJustificationAndFinalization_early (before : fork < .altair)
    (early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1) :
    processJustificationAndFinalization state = .ok state := by
  have notAltair : ¬Fork.altair ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before le)
  simp [processJustificationAndFinalization, notAltair, early, pure, Except.pure]

/-- What a successful justification and finalization did.

It changed nothing in the first two epochs, and else weighed some target balances. -/
theorem processJustificationAndFinalization_ok
    (computed : processJustificationAndFinalization state = .ok after) :
    after = state ∨ ∃ total previous current,
      weighJustificationAndFinalization state total previous current = .ok after := by
  unfold processJustificationAndFinalization at computed
  split at computed
  · unfold processJustificationAndFinalizationAltair at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl computed.symm
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, total, _, previous, _, current, _, weighed⟩ := computed
      exact .inr ⟨total, previous, current, weighed⟩
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact .inl computed.symm
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, total, _, previous, _, current, _, weighed⟩ := computed
    exact .inr ⟨total, previous, current, weighed⟩

/-- Stored checkpoints retain any property of the old checkpoints and newly assigned justification.

This applies to provenance in an actual transition history, including the previous source. -/
theorem processJustificationAndFinalization_checkpoint_property
    (property : Checkpoint → Prop)
    (current : property state.currentJustifiedCheckpoint)
    (previous : property state.previousJustifiedCheckpoint)
    (finalized : property state.finalizedCheckpoint)
    (computed : processJustificationAndFinalization state = .ok after)
    (assigned : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint →
      property after.currentJustifiedCheckpoint) :
    property after.currentJustifiedCheckpoint ∧ property after.previousJustifiedCheckpoint ∧
      property after.finalizedCheckpoint := by
  rcases processJustificationAndFinalization_ok computed with same | ⟨_, _, _, weighed⟩
  · subst after
    exact ⟨current, previous, finalized⟩
  · obtain ⟨previousEq, _, finalCases, _⟩ :=
      weighJustificationAndFinalization_checkpoints weighed
    refine ⟨?_, previousEq ▸ current, ?_⟩
    · by_cases same : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
      · exact same ▸ current
      · exact assigned same
    · rcases finalCases with same | same | same
      · exact same ▸ finalized
      · exact same ▸ previous
      · exact same ▸ current

/-- A changed finalization requires the immediately following epoch's justification bit.

The witness refers to the actual result of the spec's justification computation. -/
theorem processJustificationAndFinalization_finalized_successor_bit
    (computed : processJustificationAndFinalization state = .ok after)
    (changed : after.finalizedCheckpoint ≠ state.finalizedCheckpoint) :
    ∃ index : Fin 4, after.justificationBits.bits[index] = true ∧
      after.finalizedCheckpoint.epoch.toNat + 1 + index.val = (getCurrentEpoch state).toNat := by
  rcases processJustificationAndFinalization_ok computed with same | ⟨_, _, _, weighed⟩
  · exact (changed (same ▸ rfl)).elim
  · exact weighJustificationAndFinalization_finalized_successor_bit weighed changed

/-- A justification step leaves the current pending sources ready for rotation.

The step assigns the old current checkpoint to the previous checkpoint.

In the first two epochs it does nothing, so the two checkpoints must already agree.

It does not change the pending attestations, even when it justifies a new current checkpoint. -/
theorem processJustificationAndFinalization_sources_for_rotation (before : fork < .altair)
    (holds : PendingSourcesMatch state before)
    (early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      state.currentJustifiedCheckpoint = state.previousJustifiedCheckpoint)
    (computed : processJustificationAndFinalization state = .ok after) :
    ∀ pending ∈ (after.currentEpochAttestations before).data,
      pending.data.source = after.previousJustifiedCheckpoint := by
  unfold processJustificationAndFinalization at computed
  split at computed
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  split at computed
  · rename_i firstEpochs
    cases computed
    intro entry member
    exact (holds.1 entry member).trans (early firstEpochs)
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, weighed⟩ := computed
  obtain ⟨previous, _, _, unchanged⟩ := weighJustificationAndFinalization_checkpoints weighed
  have pending := congrArg (fun s => s.currentEpochAttestations before) unchanged
  intro entry member
  rw [previous]
  rw [pending] at member
  exact holds.1 entry member

/-- A changed justified checkpoint is exactly the block root read for its epoch. -/
theorem processJustificationAndFinalization_justified_root
    (computed : processJustificationAndFinalization state = .ok after)
    (changed : after.currentJustifiedCheckpoint ≠ state.currentJustifiedCheckpoint) :
    getBlockRoot state after.currentJustifiedCheckpoint.epoch =
      .ok after.currentJustifiedCheckpoint.root := by
  rcases processJustificationAndFinalization_ok computed with rfl | ⟨_, _, _, weighed⟩
  · exact (changed rfl).elim
  · exact weighJustificationAndFinalization_justified_root weighed changed

/-- From Altair, in the first two epochs, justification and finalization change nothing. -/
theorem processJustificationAndFinalization_early_altair (altair : .altair ≤ fork)
    (early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1) :
    processJustificationAndFinalization state = .ok state := by
  simp [processJustificationAndFinalization, processJustificationAndFinalizationAltair, altair,
    early, pure, Except.pure]

/-- Justification and finalization keep the checkpoints in order.

The current justified epoch must be at most the previous epoch.

The finalized epoch then does not decrease. -/
theorem processJustificationAndFinalization_ordered (ordered : CheckpointsOrdered state)
    (settled : state.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch state)
    (computed : processJustificationAndFinalization state = .ok after) :
    CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact ⟨ordered, UInt64.le_refl _⟩
  · exact weighJustificationAndFinalization_ordered ordered settled weighed

/-- A successful justification step cannot lower the settled justified epoch. -/
theorem processJustificationAndFinalization_justified_mono
    (settled : state.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch state)
    (computed : processJustificationAndFinalization state = .ok after) :
    state.currentJustifiedCheckpoint.epoch ≤ after.currentJustifiedCheckpoint.epoch := by
  rcases processJustificationAndFinalization_ok computed with same | ⟨_, _, _, weighed⟩
  · rw [same]
    exact UInt64.le_refl _
  · exact weighJustificationAndFinalization_justified_mono settled weighed

theorem sameSizes_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    SameSizes state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact SameSizes.refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]
    exact SameSizes.refl _

end EthLib.Consensus
