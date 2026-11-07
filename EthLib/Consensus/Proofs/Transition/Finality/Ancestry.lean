module

public import EthLib.Consensus.Proofs.Transition.Finality.Definitions

/-!
# Block ancestry and collision evidence for direct finality safety

Parent-root ancestry uses the actual blocks of the supplied histories.

Every collision alternative retains an executable search over their SSZ hash inputs.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Serialization.Ssz.SszType

variable {p : Preset}

/-- Adding actual blocks preserves every existing parent-root ancestry witness. -/
theorem FinalityAncestor.mono {bs more : List (FinalityBlock p)} {x y : Root}
    (subset : ∀ b ∈ bs, b ∈ more) (ancestor : FinalityAncestor bs x y) :
    FinalityAncestor more x y :=
  Relation.ReflTransGen.mono
    (fun _ _ ⟨b, member, parent, rooted⟩ => ⟨b, subset b member, parent, rooted⟩) x y ancestor

/-- The root of a block descends from its recorded parent root. -/
theorem finalityAncestor_parent {bs : List (FinalityBlock p)} {b : FinalityBlock p}
    {root : Root} (member : b ∈ bs) (rooted : hashTreeRoot b.message = .ok root) :
    FinalityAncestor bs b.message.parentRoot root :=
  Relation.ReflTransGen.single ⟨b, member, rfl, rooted⟩

/-- A conflict cannot have two equal roots, independently of their epoch labels. -/
theorem FinalityConflicting.roots_ne {bs : List (FinalityBlock p)} {x y : Checkpoint}
    (conflict : FinalityConflicting bs x y) : x.root ≠ y.root := by
  intro equal
  exact conflict.2.2.1 (equal ▸ Relation.ReflTransGen.refl)

/-- Search success certifies different inputs and equal SHA-256 digests. -/
theorem finalityCollision_search_valid {ss : List (FinalityState p)}
    {bs : List (FinalityBlock p)} {x y : Bytes}
    (found : findMessageCollision (finalityMessages ss bs) (finalityMessages ss bs) =
      some (x, y)) :
    x ∈ finalityMessages ss bs ∧ y ∈ finalityMessages ss bs ∧ MessageCollision x y :=
  findMessageCollision_valid found

/-- A collision between retained inputs makes the explicit history search return a collision. -/
theorem finalityCollisionFound_of_messages {ss : List (FinalityState p)}
    {bs : List (FinalityBlock p)} {x y : Bytes}
    (left : x ∈ finalityMessages ss bs) (right : y ∈ finalityMessages ss bs)
    (collision : MessageCollision x y) : FinalityCollisionFound ss bs := by
  obtain ⟨a, b, found⟩ := findMessageCollision_of_collision left right collision
  exact ⟨a, b, found, (findMessageCollision_valid found).2.2⟩

/-- Hash inputs of an observed state's latest header belong to the concrete search pool. -/
theorem finalityMessages_header {ss : List (FinalityState p)} {bs : List (FinalityBlock p)}
    {s : FinalityState p} {tree : CommitmentTree} {x : Bytes} (observed : s ∈ ss)
    (computed : valueTree (desc BeaconBlockHeader) (toValue s.latestBlockHeader) = .ok tree)
    (member : x ∈ tree.messages) : x ∈ finalityMessages ss bs := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨s, observed, List.mem_append_right _ ?_⟩
  simp only [computed, Except.toOption, Option.toList_some, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  exact member

/-- Hash inputs of an actual block belong to the concrete search pool. -/
theorem finalityMessages_block {ss : List (FinalityState p)} {bs : List (FinalityBlock p)}
    {b : FinalityBlock p} {tree : CommitmentTree} {x : Bytes} (included : b ∈ bs)
    (computed : valueTree (desc (BeaconBlock p .phase0)) (toValue b.message) = .ok tree)
    (member : x ∈ tree.messages) : x ∈ finalityMessages ss bs := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨b, included, List.mem_append_left _ ?_⟩
  simp only [computed, Except.toOption, Option.toList_some, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]
  exact member

/-- Equal roots of two observed headers give equal headers or the history's collision search. -/
theorem finality_observed_headers_binding {ss : List (FinalityState p)}
    {bs : List (FinalityBlock p)} {s t : FinalityState p} {root : Root}
    (left : s ∈ ss) (right : t ∈ ss)
    (leftRoot : hashTreeRoot s.latestBlockHeader = .ok root)
    (rightRoot : hashTreeRoot t.latestBlockHeader = .ok root) :
    s.latestBlockHeader = t.latestBlockHeader ∨ FinalityCollisionFound ss bs := by
  rcases beaconBlockHeader_root_binding leftRoot rightRoot with equal | collision
  · exact .inl equal
  · obtain ⟨leftTree, rightTree, leftOk, rightOk, x, y, _, xMember, yMember, collides⟩ := collision
    exact .inr (finalityCollisionFound_of_messages
      (finalityMessages_header left leftOk xMember)
      (finalityMessages_header right rightOk yMember) collides)

/-- A boundary identifying an observed post-C header has an epoch strictly after C.

If the headers differ despite equal roots, the history search supplies a real collision. -/
theorem finality_checkpoint_epoch_after_common_or_collision
    {cfg : Config} {ss : List (FinalityState p)} {bs : List (FinalityBlock p)}
    {start atStep cached other common : FinalityState p} {count : Nat} {epoch : Epoch}
    {root : Root}
    (ordered : start.latestBlockHeader.slot.toNat ≤ start.slot.toNat)
    (advanced : advanceSlots cfg count start = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (boundary : computeStartSlotAtEpoch p epoch = .ok atStep.slot)
    (later : common.slot.toNat < other.latestBlockHeader.slot.toNat)
    (cachedRoot : hashTreeRoot cached.latestBlockHeader = .ok root)
    (otherRoot : hashTreeRoot other.latestBlockHeader = .ok root)
    (cachedMember : cached ∈ ss) (otherMember : other ∈ ss) :
    (getCurrentEpoch common).toNat + 1 ≤ epoch.toNat ∨ FinalityCollisionFound ss bs := by
  rcases cached_checkpoint_epoch_after_common_or_collision (by decide) ordered advanced
    cachedOk boundary later cachedRoot otherRoot with after | collision
  · exact .inl after
  · obtain ⟨leftTree, rightTree, leftOk, rightOk, x, y, _, xMember, yMember, collides⟩ := collision
    exact .inr (finalityCollisionFound_of_messages
      (finalityMessages_header cachedMember leftOk xMember)
      (finalityMessages_header otherMember rightOk yMember) collides)

/-- Every successful slot cache before a supplied block is a recorded observation. -/
theorem finality_observations_cached {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s before atStep cached : FinalityState p}
    {bs : List (FinalityBlock p)} {b : FinalityBlock p} {i n : Nat}
    (listed : bs[i]? = some b)
    (prefixRun : finalityRuns cfg checks eng s (bs.take i) before)
    (inside : n < b.message.slot.toNat - before.slot.toNat)
    (advanced : advanceSlots cfg n before = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached) :
    cached ∈ finalityObservations cfg checks eng s bs := by
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨(b, i), List.mk_mem_zipIdx_iff_getElem?.mpr listed, ?_⟩
  change cached ∈ (match (bs.take i).foldlM
    (fun s b => stateTransition cfg checks eng s b true) s with
    | .error _ => []
    | .ok before => (stateTransition cfg checks eng before b true).toOption.toList ++
      before :: (List.range (b.message.slot.toNat - before.slot.toNat)).flatMap fun n =>
        match advanceSlots cfg n before with
        | .error _ => []
        | .ok atStep => atStep :: (processSlot atStep).toOption.toList)
  rw [show (bs.take i).foldlM
    (fun s b => stateTransition cfg checks eng s b true) s = .ok before from prefixRun]
  apply List.mem_append_right
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_range.mpr inside, ?_⟩
  simp only [advanced, cachedOk, Except.toOption, Option.toList_some]
  exact List.mem_cons_of_mem _ List.mem_cons_self

/-- The first justification above a boundary is weighed on the supplied fork suffix.

Both stored source epochs at that call are below the boundary.

The threshold retains the exact new checkpoint, its block-root query and its observation. -/
theorem finality_justified_crossing
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {c after : FinalityState p} {bs : List (FinalityBlock p)} {boundary : Nat}
    (inv : Invariant c) (ran : finalityRuns cfg checks eng c bs after)
    (below : c.currentJustifiedCheckpoint.epoch.toNat ≤ boundary)
    (above : boundary < after.currentJustifiedCheckpoint.epoch.toNat) :
    ∃ earlier block later atBlock offset atStep cached justified indices,
      bs = earlier ++ block :: later ∧
      finalityRuns cfg checks eng c earlier atBlock ∧
      offset < block.message.slot.toNat - atBlock.slot.toNat ∧
      advanceSlots cfg offset atBlock = .ok atStep ∧
      processSlot atStep = .ok cached ∧
      processJustificationAndFinalization cached = .ok justified ∧
      cached ∈ finalityObservations cfg checks eng c bs ∧
      cached.previousJustifiedCheckpoint.epoch.toNat ≤ boundary ∧
      cached.currentJustifiedCheckpoint.epoch.toNat ≤ boundary ∧
      boundary < justified.currentJustifiedCheckpoint.epoch.toNat ∧
      FinalityThreshold cached justified.currentJustifiedCheckpoint.epoch indices ∧
      getBlockRoot cached justified.currentJustifiedCheckpoint.epoch =
        .ok justified.currentJustifiedCheckpoint.root := by
  obtain ⟨earlier, block, later, atBlock, offset, atStep, next, split, prefixOk,
    inside, advanced, stepOk, stepBelow, stepAbove⟩ :=
    stateTransition_chain_justified_crossing (by decide) ran below above
  have changed : next.currentJustifiedCheckpoint ≠ atStep.currentJustifiedCheckpoint := by
    intro equal
    rw [equal] at stepAbove
    omega
  obtain ⟨cached, epoched, justified, cachedOk, _, weighed, assigned, changedEpoch⟩ :=
    advanceSlot_justified_origin (by decide) stepOk changed
  have atInv := (advanceSlots_invariant (by decide)
    (foldlM_ok_invariant Invariant
      (fun _ _ _ h ok => (stateTransition_invariant (by decide) h ok).1) inv prefixOk)
    advanced).1
  have frame := frame_processSlot cachedOk
  have previousBelow : cached.previousJustifiedCheckpoint.epoch.toNat ≤ boundary := by
    rw [frame.previousJustified]
    have ordered := UInt64.le_iff_toNat_le.mp atInv.ordered.2
    omega
  obtain ⟨epoch, attestations, indices, _, matching, indicesOk, epochEq, enough, _⟩ :=
    processJustificationAndFinalization_pending_signers (by decide) weighed changedEpoch
  have observed : cached ∈ finalityObservations cfg checks eng c bs := by
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    refine ⟨(block, earlier.length), ?_, ?_⟩
    · apply List.mk_mem_zipIdx_iff_getElem?.mpr
      simp [split]
    · simp only [show bs.take earlier.length = earlier by simp [split], prefixOk]
      apply List.mem_append_right
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨offset, List.mem_range.mpr inside, ?_⟩
      simp only [advanced, cachedOk, Except.toOption, Option.toList_some]
      exact List.mem_cons_of_mem _ List.mem_cons_self
  refine ⟨earlier, block, later, atBlock, offset, atStep, cached, justified, indices,
    split, prefixOk, inside, advanced, cachedOk, weighed, observed, previousBelow,
    ?_, ?_, ?_, processJustificationAndFinalization_justified_root weighed changedEpoch⟩
  · simpa only [frame.currentJustified] using stepBelow
  · simpa only [assigned] using stepAbove
  · exact ⟨attestations, epochEq ▸ matching, indicesOk, enough⟩

/-- Recording a pending attestation preserves the indexed signature check at its input. -/
theorem finality_recording_valid {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {pending : PendingAttestation p} {current : Bool}
    {indexed : IndexedAttestation p .phase0}
    (recorded : recordPendingAttestation s (by decide) current pending = .ok t) :
    isValidIndexedAttestation cfg checks t indexed =
      isValidIndexedAttestation cfg checks s indexed := by
  cases current <;>
    simp only [recordPendingAttestation, Bool.false_eq_true, ↓reduceIte] at recorded <;>
    split at recorded <;> cases recorded <;> rfl

/-- An actual processing site supplies its input-state indexed form and signature check. -/
theorem finality_attestation_site_valid {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {attestation : Attestation p .phase0}
    (processed : processAttestation cfg checks s attestation = .ok t) :
    ∃ indexed, getIndexedAttestation s attestation = .ok indexed ∧
      isValidIndexedAttestation cfg checks s indexed = .ok true := by
  obtain ⟨pending, _, _, _, _, recorded, indexed, indexedOk, valid⟩ :=
    processAttestation_records (by decide) processed
  rw [recordPendingAttestation_indexed attestation recorded] at indexedOk
  rw [finality_recording_valid recorded] at valid
  exact ⟨indexed, indexedOk, valid⟩

/-- A reconstructed block-input signer has evidence at the original attestation site.

The witness keeps the same block and operation prefix throughout committee preservation. -/
theorem finality_pending_included
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {c before atSlot : FinalityState p} {bs earlier later : List (FinalityBlock p)}
    {block : FinalityBlock p} {pending : PendingAttestation p}
    {indices : List ValidatorIndex} {i : ValidatorIndex}
    (positive : 0 < p.MIN_SEED_LOOKAHEAD.toNat)
    (history : p.MIN_SEED_LOOKAHEAD.toNat + 3 < p.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (split : bs = earlier ++ block :: later)
    (prefixOk : finalityRuns cfg checks eng c earlier before)
    (slots : processSlots cfg before block.message.slot = .ok atSlot)
    (included : PendingIncludedInBlock cfg checks (by decide) atSlot block.message pending)
    (computed : getPendingAttestingIndices atSlot pending = .ok indices)
    (member : i ∈ indices) : FinalityIncluded cfg checks eng c bs i pending.data := by
  obtain ⟨header, randao, eth1, proposers, attesters, attPrefix, attestation, attSuffix,
    inclusion, recorded, headerOk, randaoOk, eth1Ok, proposersOk, attestersOk,
    attSplit, earlierOk, attestationOk, data, bits⟩ := included
  have attChecks := processAttestation_checks (by decide) attestationOk
  have inclusionPast : computeEpochAtSlot p pending.data.slot ≤
      getCurrentEpoch inclusion := by
    rw [data, ← attChecks.2.1]
    rcases attChecks.1 with previous | current
    · rw [previous]
      exact getPreviousEpoch_le _
    · rw [current]
      exact UInt64.le_refl _
  have earlierFrame := Frame.foldlM
    (fun _ _ _ ok => frame_processAttestation (by decide) ok) earlierOk
  have attestersFrame := Frame.foldlM
    (fun _ _ _ ok => frame_processAttesterSlashing ok) attestersOk
  have proposersFrame := Frame.foldlM
    (fun _ _ _ ok => frame_processProposerSlashing ok) proposersOk
  have headerFrame := frame_processBlockHeader headerOk
  have randaoFrame := frame_processRandao randaoOk
  have eth1Frame := frame_processEth1Data eth1Ok
  have inputRecent : computeEpochAtSlot p pending.data.slot = getCurrentEpoch atSlot ∨
      (computeEpochAtSlot p pending.data.slot).toNat + 1 =
        (getCurrentEpoch atSlot).toNat := by
    have same : getCurrentEpoch inclusion = getCurrentEpoch atSlot := by
      simp only [getCurrentEpoch, earlierFrame.slot, attestersFrame.slot,
        proposersFrame.slot, eth1Frame.slot, randaoFrame.slot, headerFrame.slot]
    rw [data, ← attChecks.2.1]
    rcases attChecks.1 with previous | current
    · rw [previous, getPreviousEpoch_toNat, same]
      by_cases zero : (getCurrentEpoch atSlot).toNat = 0
      · left
        apply UInt64.toNat_inj.mp
        simp only [getPreviousEpoch_toNat, same, zero, Nat.zero_sub]
      · right
        omega
    · exact .inl (current.trans same)
  have earlierCommittee := foldlM_ok_invariant
    (fun s => getBeaconCommittee s pending.data.slot pending.data.index =
      getBeaconCommittee attesters pending.data.slot pending.data.index)
    (fun _ _ _ prior ok =>
      (processAttestation_committee (by decide) _ _ ok).trans prior) rfl earlierOk
  have attestersCommittee := foldlM_ok_invariant
    (fun s => s.slot = proposers.slot ∧
      getBeaconCommittee s pending.data.slot pending.data.index =
        getBeaconCommittee proposers pending.data.slot pending.data.index)
    (fun s _ _ prior ok => by
      have past : computeEpochAtSlot p pending.data.slot ≤ getCurrentEpoch s := by
        simpa only [getCurrentEpoch, prior.1, earlierFrame.slot, attestersFrame.slot] using
          inclusionPast
      exact ⟨(frame_processAttesterSlashing ok).slot.trans prior.1,
        (processAttesterSlashing_committee past ok).trans prior.2⟩)
    (show proposers.slot = proposers.slot ∧ _ from ⟨rfl, rfl⟩) attestersOk
  have proposersCommittee := foldlM_ok_invariant
    (fun s => s.slot = eth1.slot ∧
      getBeaconCommittee s pending.data.slot pending.data.index =
        getBeaconCommittee eth1 pending.data.slot pending.data.index)
    (fun s _ _ prior ok => by
      have past : computeEpochAtSlot p pending.data.slot ≤ getCurrentEpoch s := by
        simpa only [getCurrentEpoch, prior.1, earlierFrame.slot, attestersFrame.slot,
          proposersFrame.slot] using inclusionPast
      exact ⟨(frame_processProposerSlashing ok).slot.trans prior.1,
        (processProposerSlashing_committee past ok).trans prior.2⟩)
    (show eth1.slot = eth1.slot ∧ _ from ⟨rfl, rfl⟩) proposersOk
  have eth1Committee : getBeaconCommittee eth1 pending.data.slot pending.data.index =
      getBeaconCommittee randao pending.data.slot pending.data.index := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq eth1Ok
    rw [← rest]
    rfl
  have headerCommittee : getBeaconCommittee header pending.data.slot pending.data.index =
      getBeaconCommittee atSlot pending.data.slot pending.data.index := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    rfl
  have randaoCommittee : getBeaconCommittee randao pending.data.slot pending.data.index =
      getBeaconCommittee header pending.data.slot pending.data.index := by
    apply getBeaconCommittee_congr
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
      rfl
    · exact processRandao_attester_seed positive history randaoOk
        (by simpa only [getCurrentEpoch, headerFrame.slot] using inputRecent)
  have committee := earlierCommittee.trans (attestersCommittee.2.trans
    (proposersCommittee.2.trans (eth1Committee.trans (randaoCommittee.trans headerCommittee))))
  obtain ⟨indexed, indexedOk, valid⟩ := finality_attestation_site_valid attestationOk
  obtain ⟨listed, indexedData, _⟩ := getPendingAttestingIndices_eq_included (by decide)
    data bits committee computed indexedOk
  refine ⟨earlier, block, later, before, atSlot, inclusion, recorded, indexed, attestation,
    header, randao, eth1, proposers, attesters, attPrefix, attSuffix,
    split, prefixOk, slots, headerOk, randaoOk, eth1Ok, proposersOk, attestersOk,
    attSplit, earlierOk, attestationOk, indexedData, ?_, valid, data.symm, indexedOk⟩
  rw [listed]
  simpa only [List.mem_toArray] using mem_sortedSet.mpr member

/-- A counted signer with target after C has an actual inclusion on that fork's suffix. -/
theorem finality_matching_signer_included
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g c after atStep cached : FinalityState p}
    {common bs : List (FinalityBlock p)} {count : Nat} {epoch : Epoch}
    {attestations : Array (PendingAttestation p)} {indices : List ValidatorIndex}
    {i : ValidatorIndex}
    (positive : 0 < p.MIN_SEED_LOOKAHEAD.toNat)
    (history : p.MIN_SEED_LOOKAHEAD.toNat + 3 < p.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (initialized : finalityInitialized cfg checks g)
    (shared : finalityRuns cfg checks eng g common c)
    (ran : finalityRuns cfg checks eng c bs after)
    (advanced : advanceSlots cfg count after = .ok atStep)
    (cache : processSlot atStep = .ok cached)
    (matching : getMatchingTargetAttestations cached (by decide) epoch = .ok attestations)
    (indicesOk : getUnslashedAttestingIndices cached attestations = .ok indices)
    (member : i ∈ indices) (laterTarget : getCurrentEpoch c < epoch) :
    ∃ data, FinalityIncluded cfg checks eng c bs i data ∧
      data.target.epoch = epoch ∧
      data.source = (if epoch = getCurrentEpoch cached then cached.currentJustifiedCheckpoint
        else cached.previousJustifiedCheckpoint) ∧
      getBlockRoot cached epoch = .ok data.target.root := by
  obtain ⟨h, timestamp, deposits, genesis⟩ := initialized.1
  obtain ⟨pending, pendingListed, signers, earlier, block, later, atBlock, atSlot, root,
    signersOk, signer, targetEpoch, source, rootOk, targetRoot, split, prefixOk, slots,
    included⟩ := matchingTarget_signer_included_after_common_at_cached_slot (by decide)
      genesis shared ran advanced cache matching indicesOk member laterTarget
  have epochs := pendingEpochsMatch_of_initialized_chain (by decide) genesis shared
  have pendingEpochs := foldlM_ok_invariant (fun s => PendingEpochsMatch s (by decide))
    (fun _ _ _ prior ok => stateTransition_pending_epochs (by decide) prior ok) epochs ran
  have cachedEpochs := (pendingUnchanged_processSlot cache).epochs (frame_processSlot cache)
    (advanceSlots_pending_epochs (by decide) count pendingEpochs advanced)
  have full : finalityRuns cfg checks eng g (common ++ bs) after := by
    unfold finalityRuns
    rw [List.foldlM_append, shared]
    exact ran
  have pendingMember : pending ∈ (cached.currentEpochAttestations (by decide)).data ∨
      pending ∈ (cached.previousEpochAttestations (by decide)).data := by
    obtain ⟨_, _, sources', _, listed', _⟩ := getMatchingTargetAttestations_mem matching
      pendingListed
    simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
      Except.ok.injEq] at sources'
    obtain ⟨_, _, rfl⟩ := sources'
    split at listed'
    · exact .inl listed'
    · exact .inr listed'
  have recentAfter : (getCurrentEpoch after).toNat ≤
      (computeEpochAtSlot p pending.data.slot).toNat + 1 := by
    have oldEpochs := pendingEpochs
    have oldMember := advanceSlots_pending_mem (by decide) count advanced
      (((pendingUnchanged_processSlot cache).mem_iff pending).mp pendingMember)
    rcases oldMember with current | previous
    · rw [(oldEpochs.1 pending current).2]
      omega
    · rw [(oldEpochs.2 pending previous).2, getPreviousEpoch_toNat]
      omega
  have afterSigners : getPendingAttestingIndices after pending = .ok signers := by
    have past : computeEpochAtSlot p pending.data.slot ≤ getCurrentEpoch after := by
      rw [UInt64.le_iff_toNat_le]
      have oldMember := advanceSlots_pending_mem (by decide) count advanced
        (((pendingUnchanged_processSlot cache).mem_iff pending).mp pendingMember)
      rcases oldMember with current | previous
      · rw [(pendingEpochs.1 pending current).2]
        exact Nat.le_refl _
      · rw [(pendingEpochs.2 pending previous).2, getPreviousEpoch_toNat]
        omega
    have recent : (getCurrentEpoch atStep).toNat ≤
        (computeEpochAtSlot p pending.data.slot).toNat + 1 := by
      have same : getCurrentEpoch cached = getCurrentEpoch atStep := by
        simp only [getCurrentEpoch, (frame_processSlot cache).slot]
      rcases pendingMember with current | previous
      · rw [(cachedEpochs.1 pending current).2, same]
        omega
      · rw [(cachedEpochs.2 pending previous).2, getPreviousEpoch_toNat, same]
        omega
    have inv := foldlM_ok_invariant Invariant
      (fun _ _ _ prior ok => (stateTransition_invariant (by decide) prior ok).1)
      (initializeBeaconStateFromEth1_invariant genesis).2 full
    have committee := getBeaconCommittee_congr (index := pending.data.index)
      (advanceSlots_active_indices (by decide) count inv past advanced)
      (advanceSlots_attester_seed positive history count inv past recent advanced)
    have cachedCommittee : getBeaconCommittee cached pending.data.slot pending.data.index =
        getBeaconCommittee atStep pending.data.slot pending.data.index := by
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
      rfl
    simpa only [getPendingAttestingIndices, cachedCommittee, committee] using signersOk
  obtain ⟨_, _, _, _, _, _, recent, _⟩ := included.committee positive history
  have past : computeEpochAtSlot p pending.data.slot ≤ getCurrentEpoch atSlot := by
    rcases recent with current | previous
    · rw [current]
      exact UInt64.le_refl _
    · rw [UInt64.le_iff_toNat_le]
      omega
  unfold finalityRuns at ran
  rw [split, List.foldlM_append, prefixOk] at ran
  simp only [bind_ok_iff, List.foldlM_cons] at ran
  obtain ⟨_, first, afterBlock, blockOk, tail⟩ := ran
  cases first
  obtain ⟨advancedBlock, advancedOk, _, _, processed, _⟩ := stateTransition_ok blockOk
  have equal : advancedBlock = atSlot := Except.ok.inj (advancedOk.symm.trans slots)
  subst advancedBlock
  have inv := foldlM_ok_invariant Invariant
    (fun _ _ _ prior ok => (stateTransition_invariant (by decide) prior ok).1)
    (initializeBeaconStateFromEth1_invariant genesis).2 shared
  have atInv := (processSlots_invariant (by decide)
    (foldlM_ok_invariant Invariant
      (fun _ _ _ prior ok => (stateTransition_invariant (by decide) prior ok).1)
      inv prefixOk) slots).1
  have frame := frame_processBlock (by decide) processed
  have pastBlock : computeEpochAtSlot p pending.data.slot ≤ getCurrentEpoch afterBlock := by
    simpa only [getCurrentEpoch, frame.slot] using past
  have tailCommittee := stateTransition_chain_committee (index := pending.data.index)
    positive history (frame.invariant atInv) pastBlock recentAfter tail
  have blockCommittee := processBlock_committee (index := pending.data.index)
    positive history recent processed
  have atSigners : getPendingAttestingIndices atSlot pending = .ok signers := by
    simpa only [getPendingAttestingIndices, tailCommittee, blockCommittee] using afterSigners
  exact ⟨pending.data, finality_pending_included positive history split prefixOk slots
    included atSigners signer, targetEpoch, source, targetRoot ▸ rootOk⟩

/-- Extending a fork suffix retains every original attestation processing site. -/
theorem FinalityIncluded.append {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c : FinalityState p}
    {bs : List (FinalityBlock p)} {i : ValidatorIndex} {data : AttestationData}
    (included : FinalityIncluded cfg checks eng c bs i data) (rest : List (FinalityBlock p)) :
    FinalityIncluded cfg checks eng c (bs ++ rest) i data := by
  obtain ⟨earlier, block, later, before, atSlot, inclusion, recorded, indexed, attestation,
    header, randao, eth1, proposers, attesters, attPrefix, attSuffix,
    split, facts⟩ := included
  refine ⟨earlier, block, later ++ rest, before, atSlot, inclusion, recorded, indexed,
    attestation, header, randao, eth1, proposers, attesters, attPrefix, attSuffix, ?_, facts⟩
  simp only [split, List.append_assoc, List.cons_append]

/-- Threshold signers at a suffix cache remain included on the complete suffix. -/
theorem finality_threshold_signer_on_suffix
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g c before atStep cached : FinalityState p}
    {common bs earlier rest : List (FinalityBlock p)} {count : Nat} {epoch : Epoch}
    {indices : List ValidatorIndex} {i : ValidatorIndex}
    (positive : 0 < p.MIN_SEED_LOOKAHEAD.toNat)
    (history : p.MIN_SEED_LOOKAHEAD.toNat + 3 < p.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (initialized : finalityInitialized cfg checks g)
    (shared : finalityRuns cfg checks eng g common c)
    (split : bs = earlier ++ rest) (prefixOk : finalityRuns cfg checks eng c earlier before)
    (advanced : advanceSlots cfg count before = .ok atStep)
    (cache : processSlot atStep = .ok cached)
    (threshold : FinalityThreshold cached epoch indices)
    (member : i ∈ indices) (laterTarget : getCurrentEpoch c < epoch) :
    ∃ data, FinalityIncluded cfg checks eng c bs i data ∧
      data.target.epoch = epoch ∧
      data.source = (if epoch = getCurrentEpoch cached then cached.currentJustifiedCheckpoint
        else cached.previousJustifiedCheckpoint) ∧
      getBlockRoot cached epoch = .ok data.target.root := by
  obtain ⟨attestations, matching, indicesOk, _⟩ := threshold
  obtain ⟨data, included, facts⟩ := finality_matching_signer_included positive history
    initialized shared prefixOk advanced cache matching indicesOk member laterTarget
  exact ⟨data, split ▸ included.append rest, facts⟩

/-- The first crossing query above C consists only of checked suffix attestations. -/
theorem finality_crossing_signers
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {g c after : FinalityState p} {common bs : List (FinalityBlock p)} {boundary : Nat}
    (positive : 0 < p.MIN_SEED_LOOKAHEAD.toNat)
    (history : p.MIN_SEED_LOOKAHEAD.toNat + 3 < p.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (initialized : finalityInitialized cfg checks g)
    (shared : finalityRuns cfg checks eng g common c)
    (ran : finalityRuns cfg checks eng c bs after)
    (commonEpoch : (getCurrentEpoch c).toNat ≤ boundary)
    (below : c.currentJustifiedCheckpoint.epoch.toNat ≤ boundary)
    (above : boundary < after.currentJustifiedCheckpoint.epoch.toNat) :
    ∃ cached checkpoint indices,
      cached ∈ finalityObservations cfg checks eng c bs ∧
      FinalityThreshold cached checkpoint.epoch indices ∧
      boundary < checkpoint.epoch.toNat ∧
      ∀ i ∈ indices, ∃ data, FinalityIncluded cfg checks eng c bs i data ∧
        data.target = checkpoint ∧ data.source.epoch.toNat ≤ boundary := by
  obtain ⟨h, timestamp, deposits, genesis⟩ := initialized.1
  have inv := foldlM_ok_invariant Invariant
    (fun _ _ _ prior ok => (stateTransition_invariant (by decide) prior ok).1)
    (initializeBeaconStateFromEth1_invariant genesis).2 shared
  obtain ⟨earlier, block, later, atBlock, offset, atStep, cached, justified, indices,
    split, prefixOk, _, advanced, cache, _, observed, previousBelow, currentBelow,
    targetAbove, threshold, rootOk⟩ := finality_justified_crossing inv ran below above
  refine ⟨cached, justified.currentJustifiedCheckpoint, indices, observed, threshold,
    targetAbove, ?_⟩
  intro i member
  have laterTarget : getCurrentEpoch c < justified.currentJustifiedCheckpoint.epoch := by
    rw [UInt64.lt_iff_toNat_lt]
    omega
  obtain ⟨data, included, epochEq, sourceEq, targetRoot⟩ :=
    finality_threshold_signer_on_suffix positive history initialized shared split prefixOk
      advanced cache threshold member laterTarget
  have roots : data.target.root = justified.currentJustifiedCheckpoint.root :=
    Except.ok.inj (targetRoot.symm.trans rootOk)
  have targetEq : data.target = justified.currentJustifiedCheckpoint := by
    cases left : data.target
    cases right : justified.currentJustifiedCheckpoint
    simp only [left, right] at epochEq roots
    cases epochEq
    cases roots
    rfl
  refine ⟨data, included, targetEq, ?_⟩
  rw [sourceEq]
  split
  · exact currentBelow
  · exact previousBelow

/-- Strictly nested targets and sources give slashable suffix evidence at every common signer. -/
theorem finality_included_surround
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {c : FinalityState p} {a b : List (FinalityBlock p)} {i : ValidatorIndex}
    {outer inner : AttestationData}
    (outerIncluded : FinalityIncluded cfg checks eng c a i outer ∨
      FinalityIncluded cfg checks eng c b i outer)
    (innerIncluded : FinalityIncluded cfg checks eng c a i inner ∨
      FinalityIncluded cfg checks eng c b i inner)
    (sources : outer.source.epoch.toNat < inner.source.epoch.toNat)
    (targets : inner.target.epoch.toNat < outer.target.epoch.toNat) :
    FinalitySlashable cfg checks eng c a b i := by
  refine ⟨outer, inner, outerIncluded, innerIncluded, ?_⟩
  simp only [isSlashableAttestationData, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  exact .inr ⟨UInt64.lt_iff_toNat_lt.mpr sources, UInt64.lt_iff_toNat_lt.mpr targets⟩

/-- Different target roots at the same epoch give an executable double-vote witness. -/
theorem finality_included_double_vote
    {cfg : Config} {checks : SignatureChecks} {eng : ExecutionEngine p .phase0}
    {c : FinalityState p} {a b : List (FinalityBlock p)} {i : ValidatorIndex}
    {left right : AttestationData}
    (leftIncluded : FinalityIncluded cfg checks eng c a i left ∨
      FinalityIncluded cfg checks eng c b i left)
    (rightIncluded : FinalityIncluded cfg checks eng c a i right ∨
      FinalityIncluded cfg checks eng c b i right)
    (epochs : left.target.epoch = right.target.epoch)
    (roots : left.target.root ≠ right.target.root) : FinalitySlashable cfg checks eng c a b i := by
  have different : left ≠ right := by
    intro same
    exact roots (congrArg (fun d : AttestationData => d.target.root) same)
  refine ⟨left, right, leftIncluded, rightIncluded, ?_⟩
  simp only [isSlashableAttestationData, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne,
    beq_iff_eq]
  exact .inl ⟨different, epochs⟩

end EthLib.Consensus
