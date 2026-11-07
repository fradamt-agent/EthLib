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

end EthLib.Consensus
