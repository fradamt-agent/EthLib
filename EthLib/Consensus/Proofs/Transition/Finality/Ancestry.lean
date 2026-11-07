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

end EthLib.Consensus
