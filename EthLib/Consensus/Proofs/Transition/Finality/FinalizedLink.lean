module

public import EthLib.Consensus.Proofs.Transition.Finality.Ancestry

/-!
# Threshold links from finalized checkpoints

The source and target queries belong to actual cached states of validated Phase 0 histories.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Base.Uint64 Serialization.Ssz Serialization.Ssz.SszType

variable {p : Preset}

/-- A successful cache in a block's slot prefix belongs to the observations of that history. -/
theorem finality_observations_cached_of_split
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {s before atStep cached : FinalityState p} {bs earlier later : List (FinalityBlock p)}
    {b : FinalityBlock p} {n : Nat}
    (split : bs = earlier ++ b :: later)
    (prefixRun : finalityRuns cfg checks eng s earlier before)
    (inside : n < b.message.slot.toNat - before.slot.toNat)
    (advanced : advanceSlots cfg n before = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached) :
    cached ∈ finalityObservations cfg checks eng s bs := by
  apply finality_observations_cached (i := earlier.length) (b := b) (n := n)
  · simp [split]
  · simpa [split] using prefixRun
  · exact inside
  · exact advanced
  · exact cachedOk

/-- Recover the original newest-bit weighing without discarding its bounded cache location. -/
theorem finality_newest_bit_source_at_cached_slot
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g before atStep cached : FinalityState p}
    {h : Hash32} {t : UInt64} {ds : Array Deposit}
    {bs earlier later : List (FinalityBlock p)} {b : FinalityBlock p} {n : Nat}
    (initialized : initializeBeaconStateFromEth1 cfg checks h t ds = .ok g)
    (split : bs = earlier ++ b :: later)
    (prefixRun : finalityRuns cfg checks eng g earlier before)
    (inside : n < b.message.slot.toNat - before.slot.toNat)
    (advanced : advanceSlots cfg n before = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (bit : cached.justificationBits.bits[0] = true) :
    ∃ originCached justified total previous current,
      originCached ∈ finalityObservations cfg checks eng g bs ∧
      (∃ originEarlier originBefore offset originStep,
        originEarlier <+: bs ∧ finalityRuns cfg checks eng g originEarlier originBefore ∧
        advanceSlots cfg offset originBefore = .ok originStep ∧
        processSlot originStep = .ok originCached) ∧
      processJustificationAndFinalization originCached = .ok justified ∧
      weighJustificationAndFinalization originCached total previous current = .ok justified ∧
      justified.justificationBits.bits[0] = true ∧
      ¬getCurrentEpoch originCached ≤ GENESIS_EPOCH + 1 ∧
      cached.currentJustifiedCheckpoint = justified.currentJustifiedCheckpoint ∧
      cached.previousJustifiedCheckpoint = originCached.currentJustifiedCheckpoint := by
  have frame := frame_processSlot cachedOk
  have atBit : atStep.justificationBits.bits[0] = true := by
    simpa only [frame.justificationBits] using bit
  rcases advanceSlots_newest_bit_source (by decide) advanced atBit with inherited | occurred
  · obtain ⟨target, source, oldBit⟩ := inherited
    rcases stateTransition_chain_newest_bit_source (by decide) prefixRun oldBit with
        inherited | occurred
    · have cleared := initializeBeaconStateFromEth1_bits (by decide) initialized 0
      simp_all
    · obtain ⟨oldEarlier, oldBlock, oldLater, oldBefore, offset, originStep, next,
        originCached, epoched, justified, total, previous, current, oldSplit, oldRun,
        oldInside, oldAdvanced, _, originCache, _, justifiedOk, weighed, originBit,
        originTarget, originSource⟩ := occurred
      refine ⟨originCached, justified, total, previous, current, ?_, ?_, justifiedOk, weighed,
        originBit, ?_, frame.currentJustified.trans (target.trans originTarget),
        frame.previousJustified.trans (source.trans originSource)⟩
      apply finality_observations_cached_of_split
        (earlier := oldEarlier) (later := oldLater ++ b :: later)
      · rw [split, oldSplit, List.append_assoc, List.cons_append]
      · exact oldRun
      · exact oldInside
      · exact oldAdvanced
      · exact originCache
      · refine ⟨oldEarlier, oldBefore, offset, originStep, ?_, oldRun,
          oldAdvanced, originCache⟩
        refine ⟨oldBlock :: (oldLater ++ b :: later), ?_⟩
        rw [split, oldSplit, List.append_assoc, List.cons_append]
      · intro early
        have same : justified = originCached := by
          simpa only [processJustificationAndFinalization_early (by decide) early,
            Except.ok.injEq] using justifiedOk.symm
        have cleared := early_justificationBits_at_cached_slot initialized oldRun
          oldAdvanced originCache early 0
        have set : originCached.justificationBits.bits[0] = true := by
          simpa only [same] using originBit
        simp_all
  · obtain ⟨offset, originStep, next, originCached, epoched, justified, total, previous,
      current, oldInside, oldAdvanced, _, originCache, _, justifiedOk, weighed, originBit,
      originTarget, originSource⟩ := occurred
    refine ⟨originCached, justified, total, previous, current,
      finality_observations_cached_of_split split prefixRun (by omega) oldAdvanced originCache,
      ⟨earlier, before, offset, originStep, ⟨b :: later, split.symm⟩, prefixRun,
        oldAdvanced, originCache⟩,
      justifiedOk, weighed, originBit, ?_, frame.currentJustified.trans originTarget,
      frame.previousJustified.trans originSource⟩
    intro early
    have same : justified = originCached := by
      simpa only [processJustificationAndFinalization_early (by decide) early,
        Except.ok.injEq] using justifiedOk.symm
    have cleared := early_justificationBits_at_cached_slot initialized prefixRun
      oldAdvanced originCache early 0
    have set : originCached.justificationBits.bits[0] = true := by
      simpa only [same] using originBit
    simp_all

/-- A newly weighed previous target retains its root even if current justification wins. -/
theorem finality_previous_threshold_root
    {s justified : FinalityState p} {total previous current : Gwei}
    (weighed : weighJustificationAndFinalization s total previous current = .ok justified)
    (enough : 2 * total.toNat ≤ 3 * previous.toNat) :
    ∃ root, getBlockRoot s (getPreviousEpoch s) = .ok root := by
  simp only [weighJustificationAndFinalization, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at weighed
  obtain ⟨pw, pwOk, threshold, thresholdOk, checkpoint, checkpointOk,
    cw, cwOk, rest⟩ := weighed
  simp only [liftArith, mapError_ok_iff] at pwOk thresholdOk
  have pwValue := (mulChecked_ok_iff.mp pwOk).2
  have thresholdValue := (mulChecked_ok_iff.mp thresholdOk).2
  have justified : threshold ≤ pw := by
    apply UInt64.le_iff_toNat_le.mpr
    simp only [UInt64.reduceToNat] at pwValue thresholdValue
    omega
  simp only [justifyCheckpoint, justified, decide_true, ↓reduceIte, bind_ok_iff,
    liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at checkpointOk
  obtain ⟨root, rootOk, _⟩ := checkpointOk
  exact ⟨root, rootOk⟩

/-- The last target of a finalization rule gives an observed link from its exact source.

An inherited previous bit is traced to the current query that originally set it. -/
theorem finality_finalized_source_query
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g after : FinalityState p} {bs : List (FinalityBlock p)}
    (initialized : finalityInitialized cfg checks g)
    (run : finalityRuns cfg checks eng g bs after)
    (nonGenesis : after.finalizedCheckpoint.epoch ≠ GENESIS_EPOCH) :
    ∃ cached justified e attestations indices root,
      cached ∈ finalityObservations cfg checks eng g bs ∧
      (∃ earlier atBlock offset atStep,
        earlier <+: bs ∧ finalityRuns cfg checks eng g earlier atBlock ∧
        advanceSlots cfg offset atBlock = .ok atStep ∧ processSlot atStep = .ok cached) ∧
      processJustificationAndFinalization cached = .ok justified ∧
      FinalityThreshold cached e indices ∧
      after.finalizedCheckpoint.epoch.toNat < e.toNat ∧
      e.toNat ≤ after.finalizedCheckpoint.epoch.toNat + 2 ∧
      getMatchingTargetAttestations cached (by decide) e = .ok attestations ∧
      getUnslashedAttestingIndices cached attestations = .ok indices ∧
      (e = getCurrentEpoch cached ∨ e = getPreviousEpoch cached) ∧
      (if e = getCurrentEpoch cached then cached.currentJustifiedCheckpoint
        else cached.previousJustifiedCheckpoint) = after.finalizedCheckpoint ∧
      getBlockRoot cached e = .ok root := by
  obtain ⟨⟨h, t, ds, initialized⟩, _⟩ := initialized
  have changed : after.finalizedCheckpoint ≠ g.finalizedCheckpoint := by
    intro same
    exact nonGenesis ((congrArg (·.epoch) same).trans
      (initializeBeaconStateFromEth1_checkpoint_epochs (by decide) initialized).2.2)
  obtain ⟨earlier, block, later, atBlock, offset, atStep, next, cached, epoched, justified,
    split, prefixRun, _, inside, advanced, _, cachedOk, _, justifiedOk, assigned, changed⟩ :=
    stateTransition_chain_finalized_origin (by decide) run changed
  rcases processJustificationAndFinalization_ok justifiedOk with same |
      ⟨total, previous, current, weighed⟩
  · exact (changed (same ▸ rfl)).elim
  have observed := finality_observations_cached_of_split split prefixRun inside advanced cachedOk
  have site : ∃ originEarlier originBlock originOffset originStep,
      originEarlier <+: bs ∧ finalityRuns cfg checks eng g originEarlier originBlock ∧
      advanceSlots cfg originOffset originBlock = .ok originStep ∧
      processSlot originStep = .ok cached :=
    ⟨earlier, atBlock, offset, atStep, ⟨block :: later, split.symm⟩,
      prefixRun, advanced, cachedOk⟩
  have eligible : ¬getCurrentEpoch cached ≤ GENESIS_EPOCH + 1 := by
    intro early
    have same : justified = cached := by
      simpa only [processJustificationAndFinalization_early (by decide) early,
        Except.ok.injEq] using justifiedOk.symm
    exact changed (same ▸ rfl)
  rcases weighJustificationAndFinalization_finalized_endpoint weighed changed with
      ⟨source, bit, gap⟩ | ⟨source, bit, gap⟩
  · obtain ⟨_, attestations, total, _, target, _, matching, totalOk, _, targetOk, _, enough⟩ :=
      processJustificationAndFinalization_current_bit (by decide) justifiedOk eligible bit
    obtain ⟨indices, indicesOk, balanceOk⟩ := bind_ok_iff.mp targetOk
    obtain ⟨_, rootOk⟩ := weighJustificationAndFinalization_current_checkpoint weighed bit
    refine ⟨cached, justified, getCurrentEpoch cached, attestations, indices,
      justified.currentJustifiedCheckpoint.root, observed, site, justifiedOk,
      ⟨attestations, matching, indicesOk,
        getTotalBalance_threshold_raw totalOk balanceOk enough⟩, ?_, ?_, matching, indicesOk,
      .inl rfl, ?_, rootOk⟩
    · rw [assigned]
      rcases gap with gap | gap <;> omega
    · rw [assigned]
      rcases gap with gap | gap <;> omega
    · simpa only [↓reduceIte] using source.symm.trans assigned.symm
  · by_cases inherited : cached.justificationBits.bits[0] = true
    · obtain ⟨origin, originJustified, t, prev, curr, originObserved, originSite, originOk,
        originWeighed, originBit, originEligible, target, originSource⟩ :=
        finality_newest_bit_source_at_cached_slot initialized split prefixRun inside
          advanced cachedOk inherited
      have oldEpoch := newest_bit_epoch_at_cached_slot_of_initialized_chain initialized
        prefixRun advanced cachedOk inherited
      obtain ⟨targetEpoch, rootOk⟩ :=
        weighJustificationAndFinalization_current_checkpoint originWeighed originBit
      have sameEpoch := congrArg (fun cp : Checkpoint => cp.epoch.toNat) target
      have targetEpochNat := congrArg UInt64.toNat targetEpoch
      obtain ⟨_, attestations, total, _, balance, _, matching, totalOk, _, targetOk,
        _, enough⟩ := processJustificationAndFinalization_current_bit (by decide)
          originOk originEligible originBit
      obtain ⟨indices, indicesOk, balanceOk⟩ := bind_ok_iff.mp targetOk
      refine ⟨origin, originJustified, getCurrentEpoch origin, attestations, indices,
        originJustified.currentJustifiedCheckpoint.root, originObserved, originSite, originOk,
        ⟨attestations, matching, indicesOk,
          getTotalBalance_threshold_raw totalOk balanceOk enough⟩, ?_, ?_, matching, indicesOk,
        .inl rfl, ?_, rootOk⟩
      · rw [assigned]
        rcases gap with gap | gap <;> omega
      · rw [assigned]
        rcases gap with gap | gap <;> omega
      · simpa only [↓reduceIte] using originSource.symm.trans (source.symm.trans assigned.symm)
    · have cleared : cached.justificationBits.bits[0] = false := by
        cases bit : cached.justificationBits.bits[0] <;> simp_all
      obtain ⟨attestations, _, total, balance, _, matching, _, totalOk, targetOk, _,
        queryWeighed, enough⟩ := processJustificationAndFinalization_previous_bit (by decide)
          justifiedOk eligible bit cleared
      obtain ⟨indices, indicesOk, balanceOk⟩ := bind_ok_iff.mp targetOk
      obtain ⟨root, rootOk⟩ := finality_previous_threshold_root queryWeighed enough
      have prevEpoch := getPreviousEpoch_toNat cached
      have different : getPreviousEpoch cached ≠ getCurrentEpoch cached := by
        intro equal
        have eq := congrArg UInt64.toNat equal
        rw [assigned] at nonGenesis
        rcases gap with gap | gap <;> omega
      refine ⟨cached, justified, getPreviousEpoch cached, attestations, indices, root,
        observed, site, justifiedOk, ⟨attestations, matching, indicesOk,
          getTotalBalance_threshold_raw totalOk balanceOk enough⟩, ?_, ?_, matching, indicesOk,
        .inr rfl, ?_, rootOk⟩
      · rw [assigned]
        rcases gap with gap | gap <;> omega
      · rw [assigned]
        rcases gap with gap | gap <;> omega
      · simpa only [different, ↓reduceIte] using source.symm.trans assigned.symm

/-- Every true bit at a cache has an observed original weighing with its exact epoch age. -/
theorem finality_bit_origin_at_cached_slot
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g before atStep cached : FinalityState p}
    {h : Hash32} {t : UInt64} {ds : Array Deposit}
    {bs earlier later : List (FinalityBlock p)} {b : FinalityBlock p} {n : Nat}
    {index : Fin 4}
    (initialized : initializeBeaconStateFromEth1 cfg checks h t ds = .ok g)
    (split : bs = earlier ++ b :: later)
    (prefixRun : finalityRuns cfg checks eng g earlier before)
    (inside : n < b.message.slot.toNat - before.slot.toNat)
    (advanced : advanceSlots cfg n before = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (bit : cached.justificationBits.bits[index] = true) :
    ∃ originCached justified total previous current, ∃ origin : Fin 4,
      originCached ∈ finalityObservations cfg checks eng g bs ∧
      (∃ originEarlier originBefore offset originStep,
        originEarlier <+: bs ∧ finalityRuns cfg checks eng g originEarlier originBefore ∧
        advanceSlots cfg offset originBefore = .ok originStep ∧
        processSlot originStep = .ok originCached) ∧
      processJustificationAndFinalization originCached = .ok justified ∧
      weighJustificationAndFinalization originCached total previous current = .ok justified ∧
      (getCurrentEpoch cached).toNat + origin.val =
        (getCurrentEpoch originCached).toNat + 1 + index.val ∧
      ((origin.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
        (origin.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
          originCached.justificationBits.bits[0] = false)) := by
  have frame := frame_processSlot cachedOk
  have atBit : atStep.justificationBits.bits[index] = true := by
    simpa only [frame.justificationBits] using bit
  have earlyBits : getCurrentEpoch before ≤ GENESIS_EPOCH + 1 →
      ∀ i : Fin 4, before.justificationBits.bits[i] = false := by
    apply foldlM_ok_invariant
      (fun state => getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
        ∀ i : Fin 4, state.justificationBits.bits[i] = false)
      (fun _ _ _ holds ok => stateTransition_early_bits (by decide) holds ok) _ prefixRun
    intro _ i
    exact initializeBeaconStateFromEth1_bits (by decide) initialized i
  have epochEq : getCurrentEpoch cached = getCurrentEpoch atStep := by
    simp only [getCurrentEpoch, frame.slot]
  rcases advanceSlots_bit_epoch_origin (by decide) earlyBits advanced atBit with
      inherited | occurred
  · obtain ⟨oldIndex, age, oldBit⟩ := inherited
    obtain ⟨oldEarlier, oldBlock, oldLater, oldBefore, offset, originStep, next,
      originCached, epoched, justified, total, previous, current, origin, oldSplit, oldRun,
      oldInside, oldAge, oldAdvanced, _, originCache, _, justifiedOk, weighed, threshold⟩ :=
      justificationBit_origin_of_initialized_chain initialized prefixRun oldBit
    refine ⟨originCached, justified, total, previous, current, origin, ?_, ?_, justifiedOk,
      weighed, ?_, threshold⟩
    · apply finality_observations_cached_of_split
        (earlier := oldEarlier) (later := oldLater ++ b :: later)
      · rw [split, oldSplit, List.append_assoc, List.cons_append]
      · exact oldRun
      · exact oldInside
      · exact oldAdvanced
      · exact originCache
    · refine ⟨oldEarlier, oldBefore, offset, originStep, ?_, oldRun, oldAdvanced, originCache⟩
      refine ⟨oldBlock :: (oldLater ++ b :: later), ?_⟩
      rw [split, oldSplit, List.append_assoc, List.cons_append]
    · rw [epochEq]
      omega
  · obtain ⟨offset, originStep, next, originCached, epoched, justified, total, previous,
      current, origin, oldInside, age, oldAdvanced, _, originCache, _, justifiedOk,
      weighed, threshold⟩ := occurred
    exact ⟨originCached, justified, total, previous, current, origin,
      finality_observations_cached_of_split split prefixRun (by omega) oldAdvanced originCache,
      ⟨earlier, before, offset, originStep, ⟨b :: later, split.symm⟩, prefixRun,
        oldAdvanced, originCache⟩,
      justifiedOk, weighed, by simpa only [epochEq] using age, threshold⟩

/-- A true output bit has an observed original weighing, including when the bit was inherited. -/
theorem finality_bit_origin_after_weigh
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g before atStep cached justified : FinalityState p}
    {h : Hash32} {t : UInt64} {ds : Array Deposit}
    {bs earlier later : List (FinalityBlock p)} {b : FinalityBlock p} {n : Nat}
    {index : Fin 4} {total previous current : Gwei}
    (initialized : initializeBeaconStateFromEth1 cfg checks h t ds = .ok g)
    (split : bs = earlier ++ b :: later)
    (prefixRun : finalityRuns cfg checks eng g earlier before)
    (inside : n < b.message.slot.toNat - before.slot.toNat)
    (advanced : advanceSlots cfg n before = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (justifiedOk : processJustificationAndFinalization cached = .ok justified)
    (weighed : weighJustificationAndFinalization cached total previous current = .ok justified)
    (bit : justified.justificationBits.bits[index] = true) :
    ∃ originCached originJustified t prev curr, ∃ origin : Fin 4,
      originCached ∈ finalityObservations cfg checks eng g bs ∧
      (∃ originEarlier originBefore offset originStep,
        originEarlier <+: bs ∧ finalityRuns cfg checks eng g originEarlier originBefore ∧
        advanceSlots cfg offset originBefore = .ok originStep ∧
        processSlot originStep = .ok originCached) ∧
      processJustificationAndFinalization originCached = .ok originJustified ∧
      weighJustificationAndFinalization originCached t prev curr = .ok originJustified ∧
      (getCurrentEpoch cached).toNat + origin.val =
        (getCurrentEpoch originCached).toNat + index.val ∧
      ((origin.val = 0 ∧ 2 * t.toNat ≤ 3 * curr.toNat) ∨
        (origin.val = 1 ∧ 2 * t.toNat ≤ 3 * prev.toNat ∧
          originCached.justificationBits.bits[0] = false)) := by
  have observed := finality_observations_cached_of_split split prefixRun inside advanced cachedOk
  have site : ∃ originEarlier originBefore offset originStep,
      originEarlier <+: bs ∧ finalityRuns cfg checks eng g originEarlier originBefore ∧
      advanceSlots cfg offset originBefore = .ok originStep ∧
      processSlot originStep = .ok cached :=
    ⟨earlier, before, n, atStep, ⟨b :: later, split.symm⟩, prefixRun, advanced, cachedOk⟩
  rcases weighJustificationAndFinalization_bit_origin weighed bit with fresh | fresh | inherited
  · exact ⟨cached, justified, total, previous, current, index, observed, site,
      justifiedOk, weighed, rfl, .inl fresh⟩
  · exact ⟨cached, justified, total, previous, current, index, observed, site,
      justifiedOk, weighed, rfl, .inr fresh⟩
  · obtain ⟨oldIndex, shifted, oldBit⟩ := inherited
    obtain ⟨originCached, originJustified, t, prev, curr, origin, originObserved, originSite,
      originOk, originWeighed, age, threshold⟩ := finality_bit_origin_at_cached_slot initialized
        split prefixRun inside advanced cachedOk oldBit
    exact ⟨originCached, originJustified, t, prev, curr, origin, originObserved, originSite,
      originOk, originWeighed, by omega, threshold⟩

/-- Finalization retains an observed threshold at the immediately following epoch.

The target-age equation covers the intermediate bit required by a two-epoch finalization link. -/
theorem finality_finalized_successor_weigh
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g after : FinalityState p} {bs : List (FinalityBlock p)}
    (initialized : finalityInitialized cfg checks g)
    (run : finalityRuns cfg checks eng g bs after)
    (nonGenesis : after.finalizedCheckpoint.epoch ≠ GENESIS_EPOCH) :
    ∃ cached justified total previous current, ∃ origin : Fin 4,
      cached ∈ finalityObservations cfg checks eng g bs ∧
      (∃ earlier atBlock offset atStep,
        earlier <+: bs ∧ finalityRuns cfg checks eng g earlier atBlock ∧
        advanceSlots cfg offset atBlock = .ok atStep ∧ processSlot atStep = .ok cached) ∧
      processJustificationAndFinalization cached = .ok justified ∧
      weighJustificationAndFinalization cached total previous current = .ok justified ∧
      after.finalizedCheckpoint.epoch.toNat + 1 + origin.val =
        (getCurrentEpoch cached).toNat ∧
      ((origin.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
        (origin.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
          cached.justificationBits.bits[0] = false)) := by
  obtain ⟨⟨h, t, ds, initialized⟩, _⟩ := initialized
  have changed : after.finalizedCheckpoint ≠ g.finalizedCheckpoint := by
    intro same
    exact nonGenesis ((congrArg (·.epoch) same).trans
      (initializeBeaconStateFromEth1_checkpoint_epochs (by decide) initialized).2.2)
  obtain ⟨earlier, block, later, atBlock, offset, atStep, next, cached, epoched, justified,
    split, prefixRun, _, inside, advanced, _, cachedOk, _, justifiedOk, assigned, changed⟩ :=
    stateTransition_chain_finalized_origin (by decide) run changed
  rcases processJustificationAndFinalization_ok justifiedOk with same |
      ⟨total, previous, current, weighed⟩
  · exact (changed (same ▸ rfl)).elim
  obtain ⟨index, bit, successor⟩ :=
    weighJustificationAndFinalization_finalized_successor_bit weighed changed
  obtain ⟨originCached, originJustified, t, prev, curr, origin, observed, site, originOk,
    originWeighed, age, threshold⟩ := finality_bit_origin_after_weigh initialized split
      prefixRun inside advanced cachedOk justifiedOk weighed bit
  refine ⟨originCached, originJustified, t, prev, curr, origin, observed, site,
    originOk, originWeighed, ?_, threshold⟩
  rw [assigned]
  omega

/-- A non-genesis finalized checkpoint has its own observed justification query. -/
theorem finality_finalized_checkpoint_query
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g after : FinalityState p} {bs : List (FinalityBlock p)}
    (initialized : finalityInitialized cfg checks g)
    (run : finalityRuns cfg checks eng g bs after)
    (nonGenesis : after.finalizedCheckpoint.epoch ≠ GENESIS_EPOCH) :
    ∃ cached justified attestations indices,
      cached ∈ finalityObservations cfg checks eng g bs ∧
      (∃ earlier atBlock offset atStep,
        earlier <+: bs ∧ finalityRuns cfg checks eng g earlier atBlock ∧
        advanceSlots cfg offset atBlock = .ok atStep ∧ processSlot atStep = .ok cached) ∧
      processJustificationAndFinalization cached = .ok justified ∧
      after.finalizedCheckpoint = justified.currentJustifiedCheckpoint ∧
      FinalityThreshold cached after.finalizedCheckpoint.epoch indices ∧
      getMatchingTargetAttestations cached (by decide) after.finalizedCheckpoint.epoch =
        .ok attestations ∧
      getUnslashedAttestingIndices cached attestations = .ok indices ∧
      getBlockRoot cached after.finalizedCheckpoint.epoch = .ok after.finalizedCheckpoint.root := by
  obtain ⟨⟨h, t, ds, initialized⟩, _⟩ := initialized
  obtain ⟨earlier, block, later, atBlock, offset, atStep, next, cached, epoched, justified,
    attestations, indices, split, prefixRun, inside, advanced, _, cachedOk, _, justifiedOk,
    assigned, rootOk, matching, indicesOk, threshold⟩ :=
    checkpoint_threshold_of_initialized_chain initialized run (.inr (.inr rfl)) nonGenesis
  exact ⟨cached, justified, attestations, indices,
    finality_observations_cached_of_split split prefixRun inside advanced cachedOk,
    ⟨earlier, atBlock, offset, atStep, ⟨block :: later, split.symm⟩,
      prefixRun, advanced, cachedOk⟩,
    justifiedOk, assigned, ⟨attestations, matching, indicesOk, threshold⟩,
    matching, indicesOk, rootOk⟩

/-- The successor of a non-genesis finalized checkpoint has an observed concrete query. -/
theorem finality_finalized_successor_query
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g after : FinalityState p} {bs : List (FinalityBlock p)}
    (initialized : finalityInitialized cfg checks g)
    (run : finalityRuns cfg checks eng g bs after)
    (nonGenesis : after.finalizedCheckpoint.epoch ≠ GENESIS_EPOCH) :
    ∃ cached justified e attestations indices root,
      cached ∈ finalityObservations cfg checks eng g bs ∧
      (∃ earlier atBlock offset atStep,
        earlier <+: bs ∧ finalityRuns cfg checks eng g earlier atBlock ∧
        advanceSlots cfg offset atBlock = .ok atStep ∧ processSlot atStep = .ok cached) ∧
      processJustificationAndFinalization cached = .ok justified ∧
      e.toNat = after.finalizedCheckpoint.epoch.toNat + 1 ∧
      FinalityThreshold cached e indices ∧
      getMatchingTargetAttestations cached (by decide) e = .ok attestations ∧
      getUnslashedAttestingIndices cached attestations = .ok indices ∧
      (e = getCurrentEpoch cached ∨ e = getPreviousEpoch cached) ∧
      getBlockRoot cached e = .ok root := by
  obtain ⟨cached, justified, total, previous, current, origin, observed, site, justifiedOk,
    weighed, age, threshold⟩ := finality_finalized_successor_weigh initialized run nonGenesis
  have nonzero : 0 < after.finalizedCheckpoint.epoch.toNat := by
    have ne : after.finalizedCheckpoint.epoch ≠ 0 := nonGenesis
    have neNat : after.finalizedCheckpoint.epoch.toNat ≠ 0 := by
      intro zero
      exact ne (UInt64.toNat_inj.mp zero)
    omega
  have eligible : ¬getCurrentEpoch cached ≤ GENESIS_EPOCH + 1 := by
    intro early
    have bound := UInt64.le_iff_toNat_le.mp early
    change (getCurrentEpoch cached).toNat ≤ 1 at bound
    omega
  rcases threshold with ⟨zero, enough⟩ | ⟨one, enough, notInherited⟩
  · have bit := (weighJustificationAndFinalization_bits weighed).1.mpr enough
    obtain ⟨_, attestations, total, _, target, _, matching, totalOk, _, targetOk,
      _, enough⟩ := processJustificationAndFinalization_current_bit (by decide)
        justifiedOk eligible bit
    obtain ⟨indices, indicesOk, balanceOk⟩ := bind_ok_iff.mp targetOk
    obtain ⟨_, rootOk⟩ := weighJustificationAndFinalization_current_checkpoint weighed bit
    exact ⟨cached, justified, getCurrentEpoch cached, attestations, indices,
      justified.currentJustifiedCheckpoint.root, observed, site, justifiedOk, by omega,
      ⟨attestations, matching, indicesOk, getTotalBalance_threshold_raw totalOk balanceOk enough⟩,
      matching, indicesOk, .inl rfl, rootOk⟩
  · have bit := (weighJustificationAndFinalization_bits weighed).2.mpr (.inl enough)
    obtain ⟨attestations, _, total, target, _, matching, _, totalOk, targetOk, _,
      queryWeighed, enough⟩ := processJustificationAndFinalization_previous_bit (by decide)
        justifiedOk eligible bit notInherited
    obtain ⟨indices, indicesOk, balanceOk⟩ := bind_ok_iff.mp targetOk
    obtain ⟨root, rootOk⟩ := finality_previous_threshold_root queryWeighed enough
    have previousEpoch := getPreviousEpoch_toNat cached
    exact ⟨cached, justified, getPreviousEpoch cached, attestations, indices, root,
      observed, site, justifiedOk, by omega,
      ⟨attestations, matching, indicesOk, getTotalBalance_threshold_raw totalOk balanceOk enough⟩,
      matching, indicesOk, .inr rfl, rootOk⟩

/-- A zero header state root is filled even after an earlier cache left it zero.

The slot and parent root stay fixed, so this operation supplies no actual block ancestry edge. -/
theorem finality_cache_refills_zero_header
    {s cached : FinalityState p} {root : Root}
    (cacheOk : processSlot s = .ok cached)
    (empty : s.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (stateRoot : hashTreeRoot s = .ok root) :
    cached.latestBlockHeader = { s.latestBlockHeader with stateRoot := root } := by
  obtain ⟨actual, actualOk, header⟩ := processSlot_latestBlockHeader (by decide) cacheOk
  have same : actual = root := Except.ok.inj (actualOk.symm.trans stateRoot)
  simpa only [empty, ↓reduceIte, same] using header

/-- After a nonzero state hash fills a header, every later empty-slot cache keeps that header. -/
theorem finality_cached_header_stable
    {cfg : Config} {s cached atStep laterCached : FinalityState p} {count : Nat}
    {stateRoot : Root}
    (first : processSlot s = .ok cached)
    (hashed : hashTreeRoot s = .ok stateRoot)
    (nonzero : stateRoot ≠ Vector.replicate 32 0)
    (advanced : advanceSlots cfg count cached = .ok atStep)
    (last : processSlot atStep = .ok laterCached) :
    laterCached.latestBlockHeader = cached.latestBlockHeader := by
  have filled : cached.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0 := by
    obtain ⟨actual, actualOk, header⟩ := processSlot_latestBlockHeader (by decide) first
    have same : actual = stateRoot := Except.ok.inj (actualOk.symm.trans hashed)
    rw [header]
    split
    · simpa only [same] using nonzero
    · exact ‹s.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0›
  have same := advanceSlots_latestBlockHeader_of_nonzero (by decide) count filled advanced
  exact (processSlot_latestBlockHeader_of_nonzero (by decide) last
    (by simpa only [same] using filled)).trans same

/-- A validated block's nonzero post-state root fixes every cache before the next block. -/
theorem finality_block_cached_header
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {s after atStep cached : FinalityState p} {b : FinalityBlock p} {count : Nat}
    (ran : stateTransition cfg checks eng s b true = .ok after)
    (nonzero : b.message.stateRoot ≠ Vector.replicate 32 0)
    (advanced : advanceSlots cfg count after = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached) :
    ∃ bodyRoot, hashTreeRoot b.message.body = .ok bodyRoot ∧
      cached.latestBlockHeader =
        ⟨b.message.slot, b.message.proposerIndex, b.message.parentRoot,
          b.message.stateRoot, bodyRoot⟩ := by
  obtain ⟨atSlot, _, _, _, blockOk, hashed⟩ := stateTransition_ok ran
  obtain ⟨_, bodyRoot, bodyOk, header⟩ := processBlock_block_history (by decide) blockOk
  have rootOk := hashed rfl
  have firstHeader {firstCached : FinalityState p}
      (first : processSlot after = .ok firstCached) :
      firstCached.latestBlockHeader =
        ⟨b.message.slot, b.message.proposerIndex, b.message.parentRoot,
          b.message.stateRoot, bodyRoot⟩ := by
    have filled := finality_cache_refills_zero_header first (by rw [header]) rootOk
    simpa only [header] using filled
  cases count with
  | zero =>
    cases advanced
    exact ⟨bodyRoot, bodyOk, firstHeader cachedOk⟩
  | succ count =>
    obtain ⟨middle, first, rest⟩ := bind_ok_iff.mp advanced
    obtain ⟨firstCached, firstCache, middleHeader, _⟩ :=
      advanceSlot_block_history (by decide) first
    have fixed := firstHeader firstCache
    have middleFilled : middle.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0 := by
      simpa only [middleHeader, fixed] using nonzero
    have laterHeader := advanceSlots_latestBlockHeader_of_nonzero (by decide)
      count middleFilled rest
    have finalHeader := processSlot_latestBlockHeader_of_nonzero (by decide) cachedOk
      (by simpa only [laterHeader] using middleFilled)
    exact ⟨bodyRoot, bodyOk, finalHeader.trans (laterHeader.trans (middleHeader.trans fixed))⟩

/-- A cache whose target epoch is after C lies in the suffix, not the common history. -/
theorem finality_cached_site_after_common
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g c atBlock atStep cached : FinalityState p}
    {common bs earlier later : List (FinalityBlock p)} {b : FinalityBlock p}
    {offset : Nat} {e : Epoch}
    (commonRun : finalityRuns cfg checks eng g common c)
    (split : common ++ bs = earlier ++ b :: later)
    (prefixRun : finalityRuns cfg checks eng g earlier atBlock)
    (inside : offset < b.message.slot.toNat - atBlock.slot.toNat)
    (advanced : advanceSlots cfg offset atBlock = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (recent : e = getCurrentEpoch cached ∨ e = getPreviousEpoch cached)
    (targetAfter : (getCurrentEpoch c).toNat < e.toNat) :
    ∃ earlierFork,
      bs = earlierFork ++ b :: later ∧ finalityRuns cfg checks eng c earlierFork atBlock ∧
      cached ∈ finalityObservations cfg checks eng c bs := by
  have earlierPrefix : earlier <+: common ++ bs := ⟨b :: later, split.symm⟩
  have commonPrefix : common <+: common ++ bs := List.prefix_append _ _
  by_cases cut : common.length ≤ earlier.length
  · obtain ⟨earlierFork, equal⟩ :=
      List.prefix_of_prefix_length_le commonPrefix earlierPrefix cut
    have forkSplit : bs = earlierFork ++ b :: later := by
      rw [← equal, List.append_assoc] at split
      exact List.append_cancel_left split
    have forkPrefix : finalityRuns cfg checks eng c earlierFork atBlock := by
      change earlier.foldlM (fun s b => stateTransition cfg checks eng s b true) g =
        .ok atBlock at prefixRun
      rw [← equal, List.foldlM_append, commonRun] at prefixRun
      exact prefixRun
    exact ⟨earlierFork, forkSplit, forkPrefix,
      finality_observations_cached_of_split forkSplit forkPrefix inside advanced cachedOk⟩
  · have throughPrefix : earlier ++ [b] <+: common := by
      apply List.prefix_of_prefix_length_le
        (show earlier ++ [b] <+: common ++ bs from
          ⟨later, by simpa only [List.append_assoc, List.singleton_append] using split.symm⟩)
        commonPrefix
      simp only [List.length_append, List.length_singleton]
      omega
    obtain ⟨rest, equal⟩ := throughPrefix
    change common.foldlM (fun s b => stateTransition cfg checks eng s b true) g =
      .ok c at commonRun
    rw [← equal, List.append_assoc, List.singleton_append, List.foldlM_append, prefixRun]
      at commonRun
    obtain ⟨_, same, remaining⟩ := bind_ok_iff.mp commonRun
    cases same
    obtain ⟨middle, blockOk, tailOk⟩ := bind_ok_iff.mp remaining
    obtain ⟨atSlot, slotsOk, atSlotSlot, _, processed, _⟩ := stateTransition_ok blockOk
    have middleSlot := (frame_processBlock (by decide) processed).slot.trans atSlotSlot
    have upper := stateTransition_chain_slot_le (by decide) tailOk
    have cacheSlot := processSlot_slot cachedOk
    have moved := advanceSlots_slot offset advanced
    have cacheLe : cached.slot.toNat ≤ c.slot.toNat := by
      rw [middleSlot] at upper
      rw [cacheSlot]
      omega
    have epochLe : (getCurrentEpoch cached).toNat ≤ (getCurrentEpoch c).toNat := by
      simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
      exact Nat.div_le_div_right cacheLe
    rcases recent with rfl | rfl
    · omega
    · have previous := getPreviousEpoch_toNat cached
      omega

/-- A block's later cached header hashes to its block root, or its observed state hashes to zero. -/
theorem finality_block_cached_root_or_zero
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {ss : List (FinalityState p)} {pool : List (FinalityBlock p)}
    {s after atStep cached : FinalityState p} {b : FinalityBlock p} {count : Nat}
    (ran : stateTransition cfg checks eng s b true = .ok after)
    (observed : after ∈ ss)
    (advanced : advanceSlots cfg count after = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached) :
    (∀ root, hashTreeRoot cached.latestBlockHeader = .ok root →
      hashTreeRoot b.message = .ok root) ∨ FinalityZeroRootFound ss pool := by
  by_cases zero : b.message.stateRoot = Vector.replicate 32 0
  · have hashed := (stateTransition_ok ran).choose_spec.2.2.2.2 rfl
    exact .inr (finality_zero_root_found observed (zero ▸ hashed))
  · obtain ⟨bodyRoot, bodyOk, header⟩ := finality_block_cached_header ran zero advanced cachedOk
    refine .inl ?_
    intro root rooted
    rw [header] at rooted
    rw [← BeaconBlock.hashTreeRoot_header b.message bodyOk]
    exact rooted

/-- Empty-slot advancement after a validated nonzero block keeps that block's completed header. -/
theorem finality_block_advanced_header
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {s after atStep : FinalityState p} {b : FinalityBlock p} {count : Nat}
    (ran : stateTransition cfg checks eng s b true = .ok after)
    (nonzero : b.message.stateRoot ≠ Vector.replicate 32 0)
    (positive : 0 < count)
    (advanced : advanceSlots cfg count after = .ok atStep) :
    ∃ bodyRoot, hashTreeRoot b.message.body = .ok bodyRoot ∧
      atStep.latestBlockHeader =
        ⟨b.message.slot, b.message.proposerIndex, b.message.parentRoot,
          b.message.stateRoot, bodyRoot⟩ := by
  cases count with
  | zero => omega
  | succ count =>
    obtain ⟨middle, first, rest⟩ := bind_ok_iff.mp advanced
    obtain ⟨cached, cacheOk, middleHeader, _⟩ := advanceSlot_block_history (by decide) first
    obtain ⟨bodyRoot, bodyOk, fixed⟩ := finality_block_cached_header ran nonzero
      (show advanceSlots cfg 0 after = .ok after from rfl) cacheOk
    have middleFilled : middle.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0 := by
      simpa only [middleHeader, fixed] using nonzero
    exact ⟨bodyRoot, bodyOk,
      (advanceSlots_latestBlockHeader_of_nonzero (by decide) count middleFilled rest).trans
        (middleHeader.trans fixed)⟩

/-- Consecutive validated blocks form a parent-root edge or the first state hashes zero. -/
theorem finality_consecutive_blocks_parent_or_zero
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {ss : List (FinalityState p)} {pool : List (FinalityBlock p)}
    {s middle after : FinalityState p} {left right : FinalityBlock p}
    (first : stateTransition cfg checks eng s left true = .ok middle)
    (second : stateTransition cfg checks eng middle right true = .ok after)
    (observed : middle ∈ ss) :
    hashTreeRoot left.message = .ok right.message.parentRoot ∨ FinalityZeroRootFound ss pool := by
  by_cases zero : left.message.stateRoot = Vector.replicate 32 0
  · obtain ⟨_, _, _, _, _, rooted⟩ := stateTransition_ok first
    exact .inr (finality_zero_root_found observed (zero ▸ rooted rfl))
  · obtain ⟨atSlot, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok second
    have moved := UInt64.lt_iff_toNat_lt.mp (processSlots_slot slotsOk).1
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, advanced⟩ := slotsOk
    obtain ⟨bodyRoot, bodyOk, header⟩ := finality_block_advanced_header first zero
      (by omega) advanced
    have notAltair : ¬Fork.altair ≤ Fork.phase0 := by decide
    simp only [processBlock, notAltair, ↓reduceDIte, bind_ok_iff] at blockOk
    obtain ⟨headerState, headerOk, _⟩ := blockOk
    have parent := (processBlockHeader_checks headerOk).2.2.2.1
    rw [header] at parent
    exact .inl ((BeaconBlock.hashTreeRoot_header left.message bodyOk).symm.trans parent)

/-- Parent roots of a validated chain connect to every later block root.

Every intermediate post-state is retained so a zero state root gives concrete evidence. -/
theorem finality_chain_parent_ancestor_or_zero
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {ss : List (FinalityState p)} {pool : List (FinalityBlock p)}
    {s after : FinalityState p} {bs : List (FinalityBlock p)}
    (run : finalityRuns cfg checks eng s bs after)
    (blocksIn : ∀ b ∈ bs, b ∈ pool)
    (outputsIn : ∀ earlier state, earlier <+: bs →
      finalityRuns cfg checks eng s earlier state → state ∈ ss) :
    ∀ first rest, bs = first :: rest →
      ∀ b ∈ bs, ∀ root, hashTreeRoot b.message = .ok root →
        FinalityAncestor pool first.message.parentRoot root ∨ FinalityZeroRootFound ss pool := by
  induction bs generalizing s with
  | nil => intro first rest split; cases split
  | cons first rest ih =>
    intro named tail split b member root rooted
    cases split
    obtain ⟨middle, firstOk, restOk⟩ := bind_ok_iff.mp run
    rcases List.mem_cons.mp member with equal | inRest
    · subst b
      exact .inl (finalityAncestor_parent (blocksIn first List.mem_cons_self) rooted)
    · cases rest with
      | nil => simp at inRest
      | cons next more =>
        obtain ⟨nextState, nextOk, _⟩ := bind_ok_iff.mp restOk
        rcases finality_consecutive_blocks_parent_or_zero firstOk nextOk
            (outputsIn [first] middle ⟨next :: more, rfl⟩ (by
              change (first :: []).foldlM
                (fun s b => stateTransition cfg checks eng s b true) s = .ok middle
              exact bind_ok_iff.mpr ⟨middle, firstOk, rfl⟩)) with parent | zero
        · rcases ih restOk (fun b member => blocksIn b (List.mem_cons_of_mem first member))
            (fun earlier state pref ok => outputsIn (first :: earlier) state
              (by obtain ⟨remaining, eq⟩ := pref; exact ⟨remaining, by simp [eq]⟩)
              (by exact bind_ok_iff.mpr ⟨middle, firstOk, ok⟩))
            next more rfl b inRest root rooted with ancestor | zero
          · exact .inl ((finalityAncestor_parent (blocksIn first List.mem_cons_self) parent).trans
              ancestor)
          · exact .inr zero
        · exact .inr zero

/-- Actual parent-root reachability along a history needs no assumption on state-root outputs. -/
theorem finality_chain_parent_ancestor
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {s after : FinalityState p} {first : FinalityBlock p} {rest : List (FinalityBlock p)}
    (run : finalityRuns cfg checks eng s (first :: rest) after)
    {b : FinalityBlock p} {root : Root} (member : b ∈ first :: rest)
    (rooted : hashTreeRoot b.message = .ok root) :
    FinalityAncestor (first :: rest) first.message.parentRoot root ∨
      FinalityZeroRootFound (finalityObservations cfg checks eng s (first :: rest))
        (first :: rest) := by
  apply finality_chain_parent_ancestor_or_zero run (fun _ h => h) ?_ first rest rfl
    b member root rooted
  intro earlier state pref ran
  obtain ⟨remaining, equal⟩ := pref
  rw [← equal]
  exact finality_observations_prefix remaining (finality_observations_endpoint ran)

/-- A slot cache connects to the parent of the next validated block, or exhibits a zero root. -/
theorem finality_cache_next_parent_or_zero
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {ss : List (FinalityState p)} {pool : List (FinalityBlock p)}
    {before after atStep cached : FinalityState p} {b : FinalityBlock p} {offset : Nat}
    {root : Root}
    (ran : stateTransition cfg checks eng before b true = .ok after)
    (inside : offset < b.message.slot.toNat - before.slot.toNat)
    (advanced : advanceSlots cfg offset before = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (rooted : hashTreeRoot cached.latestBlockHeader = .ok root)
    (observed : atStep ∈ ss) :
    root = b.message.parentRoot ∨ FinalityZeroRootFound ss pool := by
  obtain ⟨stateRoot, stateRootOk, cacheHeader⟩ :=
    processSlot_latestBlockHeader (by decide) cachedOk
  by_cases zero : stateRoot = Vector.replicate 32 0
  · exact .inr (finality_zero_root_found observed (zero ▸ stateRootOk))
  · have filled : cached.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0 := by
      rw [cacheHeader]
      split
      · exact zero
      · exact ‹atStep.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0›
    obtain ⟨atSlot, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok ran
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
    obtain ⟨_, _, slotsAdvanced⟩ := slotsOk
    have countEq : b.message.slot.toNat - before.slot.toNat =
        offset + (b.message.slot.toNat - before.slot.toNat - offset) := by omega
    rw [countEq] at slotsAdvanced
    obtain ⟨sameStep, prefixOk, suffixOk⟩ := advanceSlots_add slotsAdvanced
    have equal : sameStep = atStep := Except.ok.inj (prefixOk.symm.trans advanced)
    subst sameStep
    obtain ⟨remaining, remainingEq⟩ := Nat.exists_eq_succ_of_ne_zero
      (by omega : b.message.slot.toNat - before.slot.toNat - offset ≠ 0)
    rw [remainingEq] at suffixOk
    obtain ⟨next, stepOk, restOk⟩ := bind_ok_iff.mp suffixOk
    obtain ⟨stepCached, stepCache, nextHeader, _⟩ := advanceSlot_block_history (by decide) stepOk
    have cacheEq : stepCached = cached := Except.ok.inj (stepCache.symm.trans cachedOk)
    rw [cacheEq] at nextHeader
    have nextFilled : next.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0 := by
      simpa only [nextHeader] using filled
    have header := (advanceSlots_latestBlockHeader_of_nonzero (by decide)
      remaining nextFilled restOk).trans nextHeader
    have notAltair : ¬Fork.altair ≤ Fork.phase0 := by decide
    simp only [processBlock, notAltair, ↓reduceDIte, bind_ok_iff] at blockOk
    obtain ⟨headerState, headerOk, _⟩ := blockOk
    have parent := (processBlockHeader_checks headerOk).2.2.2.1
    rw [header] at parent
    exact .inl (Except.ok.inj (rooted.symm.trans parent))

end EthLib.Consensus
