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

/-- Every signer counted for the current target is in the current active denominator.

The pending-epoch invariant connects committee reconstruction to that denominator. -/
theorem mem_getActiveValidatorIndices_of_current_target {before : fork < .altair}
    {attestations : Array (PendingAttestation preset)} {indices : List ValidatorIndex}
    (holds : PendingEpochsMatch state before)
    (matching : getMatchingTargetAttestations state before (getCurrentEpoch state) =
      .ok attestations)
    (computed : getUnslashedAttestingIndices state attestations = .ok indices)
    {index : ValidatorIndex} (member : index ∈ indices) :
    index ∈ getActiveValidatorIndices state (getCurrentEpoch state) := by
  obtain ⟨⟨pending, included, signers, signersOk, signer⟩, _⟩ :=
    mem_getUnslashedAttestingIndices computed member
  have epoch := (getMatchingTargetAttestations_slot_epoch holds matching included).2
  simpa only [epoch] using mem_getActiveValidatorIndices_of_pending signersOk signer

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
