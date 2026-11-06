module

public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.EpochJustification

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
