module

public import EthLib.Consensus.Proofs.ForkChoice.ChainLinks
public import EthLib.Consensus.Proofs.Transition.FfgProvenance

/-!
# Proofs: the store's descent check gives conflicting epoch-boundary pairs

The store checks that its justified block descends from its finalized block with a walk.

The walk goes from the justified root back to the first slot of the finalized epoch.

The check passes when it reaches the finalized root.

Suppose that it does not.

Then the finalized and the justified checkpoint conflict as epoch-boundary pairs, Gasper §4.

That holds over any parent links that name a header with the child's root, parent root and slot.

Otherwise a link names a header with the zero root, or two different headers have one root.

Or the store keeps a block at the zero root.

The finalized root must be the root of a header at or before the first slot of its epoch.

Both roots must be nonzero, and the store must hold the justified block.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz SszType Models.Ffg

variable {preset : Preset} {fork : Fork} {store : Store preset fork}

namespace Store

variable {links : Root → Root → ℕ → Prop}

/-- A pair with a nonzero root is below another only along links after its epoch's first slot. -/
private theorem path_of_le {s t : Checkpoint} (nonzero : s.root ≠ Vector.replicate 32 0)
    (le : EpochBlock.ofCheckpoint (links := links) (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat)
      s ≤ EpochBlock.ofCheckpoint t) :
    s.epoch.toNat ≤ t.epoch.toNat ∧
      Relation.ReflTransGen
        (EpochBlock.after links preset.SLOTS_PER_EPOCH.toNat s.epoch.toNat) s.root t.root := by
  rcases le with none | ⟨r, e, r', e', hs, ht, le, path⟩
  · simp [EpochBlock.ofCheckpoint, nonzero] at none
  · by_cases tz : t.root = Vector.replicate 32 0
    · simp [EpochBlock.ofCheckpoint, tz] at ht
    simp only [EpochBlock.ofCheckpoint, nonzero, tz, ↓reduceIte, Option.some.injEq,
      Prod.mk.injEq] at hs ht
    obtain ⟨rfl, rfl⟩ := hs
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨le, path⟩

/-- Two headers with one root and different slots collide. -/
private theorem headerCollision_of_slot_ne {left right : BeaconBlockHeader} {root : Root}
    (leftRoot : hashTreeRoot left = .ok root) (rightRoot : hashTreeRoot right = .ok root)
    (slots : left.slot ≠ right.slot) : HeaderCollision := by
  rcases beaconBlockHeader_root_binding leftRoot rightRoot with same | collision
  · exact absurd (congrArg BeaconBlockHeader.slot same) slots
  · exact ⟨left, right, root, fun same => slots (congrArg BeaconBlockHeader.slot same),
      leftRoot, rightRoot, collision⟩

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

/-- When the store's descent check fails, the finalized and the justified checkpoint conflict.

They conflict as epoch-boundary pairs over the links.

Each link must name a header with the child's root, its parent root and its slot.

The store keys each block by its root, and its parents sit at lower slots.

A known block with an unknown parent has the zero root as parent, as in a store from genesis.

The finalized epoch is at most the justified epoch, and its first slot fits in a slot number.

Both roots are nonzero, and the store holds the justified block.

The finalized root is the root of a header at or before the first slot of the finalized epoch.

Otherwise a link names a header with the zero root, or two different headers have one root. -/
theorem conflicting_of_not_descends
    (linkHeader : ∀ {parentRoot root : Root} {slot : ℕ}, links parentRoot root slot →
      ∃ header : BeaconBlockHeader, hashTreeRoot header = .ok root ∧
        header.parentRoot = parentRoot ∧ header.slot.toNat = slot)
    (keys : store.KeysAreRoots) (lower : store.ParentsBelow)
    (orphan : ∀ {root : Root} {block : BeaconBlock preset fork}, store.blocks[root]? = some block →
      store.blocks[block.parentRoot]? = none → block.parentRoot = Vector.replicate 32 0)
    {finalized justified : Checkpoint}
    (fits : finalized.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (hle : finalized.epoch.toNat ≤ justified.epoch.toNat)
    {justifiedBlock : BeaconBlock preset fork}
    (justifiedFound : store.blocks[justified.root]? = some justifiedBlock)
    (finalizedNonzero : finalized.root ≠ Vector.replicate 32 0)
    (justifiedNonzero : justified.root ≠ Vector.replicate 32 0)
    (finalizedHeader : ∃ header : BeaconBlockHeader, hashTreeRoot header = .ok finalized.root ∧
      header.slot.toNat ≤ finalized.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (notDescends :
      store.getCheckpointBlock justified.root finalized.epoch ≠ .ok finalized.root) :
    Conflicting
        (EpochBlock.ofCheckpoint (links := links) (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat)
          finalized)
        (EpochBlock.ofCheckpoint justified) ∨
      (∃ parentRoot slot, links parentRoot (Vector.replicate 32 0) slot) ∨ HeaderCollision := by
  obtain ⟨header, headerRoot, headerSlot⟩ := finalizedHeader
  -- The first slot of the finalized epoch.
  obtain ⟨start, startOk⟩ : ∃ start, computeStartSlotAtEpoch preset finalized.epoch = .ok start :=
    ⟨finalized.epoch * preset.SLOTS_PER_EPOCH, Uint64.mulChecked_ok_iff.mpr ⟨fits, by
      rw [UInt64.toNat_mul]
      exact Nat.mod_eq_of_lt fits⟩⟩
  have startNat : start.toNat = finalized.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat :=
    (Uint64.mulChecked_ok_iff.mp startOk).2
  -- The store holding the finalized root at or before the first slot makes the check pass.
  have passes : ∀ {block : BeaconBlock preset fork}, store.blocks[finalized.root]? = some block →
      start < block.slot → HeaderCollision := by
    intro block found late
    rcases keys.header_eq found headerRoot with ⟨sameSlot, -⟩ | collision
    · rw [UInt64.lt_iff_toNat_lt, startNat, ← sameSlot] at late
      omega
    · exact collision
  -- The direction `¬ F ≤ J`.
  have notBelow : ¬ (EpochBlock.ofCheckpoint (links := links)
      (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat) finalized ≤
        EpochBlock.ofCheckpoint justified) ∨
      (∃ parentRoot slot, links parentRoot (Vector.replicate 32 0) slot) ∨ HeaderCollision := by
    by_contra none
    simp only [not_or, not_not] at none
    obtain ⟨le, noZero, noCollision⟩ := none
    obtain ⟨-, path⟩ := path_of_le finalizedNonzero le
    have headerOf : ∀ {parentRoot root : Root},
        EpochBlock.after links preset.SLOTS_PER_EPOCH.toNat finalized.epoch.toNat parentRoot root →
        ∃ header : BeaconBlockHeader, hashTreeRoot header = .ok root ∧
          header.parentRoot = parentRoot ∧ start < header.slot := by
      rintro parentRoot root ⟨slot, link, late⟩
      obtain ⟨h, rootOk, parent, slotEq⟩ := linkHeader link
      exact ⟨h, rootOk, parent, by rw [UInt64.lt_iff_toNat_lt, startNat, slotEq]; exact late⟩
    rcases getCheckpointBlock_of_links keys lower startOk headerOf path justifiedFound with
      same | ⟨block, found, late⟩ | ⟨known, knownBlock, head, knownFound, knownLate, unknown⟩ |
      collision
    · exact notDescends same
    · exact noCollision (passes found late)
    · rcases Relation.ReflTransGen.cases_tail head with same | ⟨parentRoot, before, step⟩
      · subst same
        exact noCollision (passes knownFound knownLate)
      · obtain ⟨h, rootOk, parent, -⟩ := headerOf step
        rcases keys.header_eq knownFound rootOk with ⟨-, sameParent⟩ | collision
        · -- The path reaches the zero root, whose last link names a header with that root.
          rw [← parent, sameParent, orphan knownFound unknown] at before
          rcases Relation.ReflTransGen.cases_tail before with same | ⟨p, -, ⟨slot, link, -⟩⟩
          · exact finalizedNonzero same.symm
          · exact noZero ⟨p, slot, link⟩
        · exact noCollision collision
    · exact noCollision collision
  -- The direction `¬ J ≤ F`.
  have notAbove : ¬ (EpochBlock.ofCheckpoint (links := links)
      (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat) justified ≤
        EpochBlock.ofCheckpoint finalized) ∨ HeaderCollision := by
    by_contra none
    simp only [not_or, not_not] at none
    obtain ⟨le, noCollision⟩ := none
    obtain ⟨epochLe, path⟩ := path_of_le justifiedNonzero le
    have sameEpoch : justified.epoch.toNat = finalized.epoch.toNat := Nat.le_antisymm epochLe hle
    rcases Relation.ReflTransGen.cases_tail path with same | ⟨parentRoot, -, ⟨slot, link, late⟩⟩
    · -- The same root: the store holds it at or before the first slot, so the check passes.
      rw [← same] at justifiedFound
      by_cases le : justifiedBlock.slot ≤ start
      · apply notDescends
        rw [getCheckpointBlock_eq startOk, ← same]
        exact getAncestor_root_of_le justifiedFound le
      · exact noCollision (passes justifiedFound (UInt64.not_le.mp le))
    · -- A link into the finalized root after the first slot names a second header for it.
      obtain ⟨h, rootOk, -, slotEq⟩ := linkHeader link
      rw [sameEpoch] at late
      exact noCollision (headerCollision_of_slot_ne headerRoot rootOk (fun same => by
        have := congrArg UInt64.toNat same
        omega))
  rcases notAbove with notAbove | collision
  · rcases notBelow with notBelow | zero | collision
    · exact .inl ⟨notBelow, notAbove⟩
    · exact .inr (.inl zero)
    · exact .inr (.inr collision)
  · exact .inr (.inr collision)

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork}

/-- In a reachable store whose head computes, take a failed descent check.

Then the finalized and the justified checkpoint conflict as epoch-boundary pairs.

The anchor block sits at or before the slot of its state.

It has the zero root as parent, as the genesis block does.

Otherwise a link names a header with the zero root, or two different headers have one root.

Or the store keeps a block at the zero root. -/
theorem Reachable.conflicting_of_not_descends
    (reachable : Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (anchorParent : anchorBlock.parentRoot = Vector.replicate 32 0)
    {head : ForkChoiceNode} (headOk : store.getHead config = .ok head)
    (linkHeader : ∀ {parentRoot root : Root} {slot : ℕ}, links parentRoot root slot →
      ∃ header : BeaconBlockHeader, hashTreeRoot header = .ok root ∧
        header.parentRoot = parentRoot ∧ header.slot.toNat = slot)
    (fits : store.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat < 2 ^ 64)
    (hle : store.finalizedCheckpoint.epoch.toNat ≤ store.justifiedCheckpoint.epoch.toNat)
    (finalizedNonzero : store.finalizedCheckpoint.root ≠ Vector.replicate 32 0)
    (justifiedNonzero : store.justifiedCheckpoint.root ≠ Vector.replicate 32 0)
    (finalizedHeader : ∃ header : BeaconBlockHeader,
      hashTreeRoot header = .ok store.finalizedCheckpoint.root ∧
      header.slot.toNat ≤ store.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat)
    (notDescends : store.getCheckpointBlock store.justifiedCheckpoint.root
      store.finalizedCheckpoint.epoch ≠ .ok store.finalizedCheckpoint.root) :
    Conflicting
        (EpochBlock.ofCheckpoint (links := links) (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat)
          store.finalizedCheckpoint)
        (EpochBlock.ofCheckpoint store.justifiedCheckpoint) ∨
      (∃ parentRoot slot, links parentRoot (Vector.replicate 32 0) slot) ∨ HeaderCollision ∨
      ∃ block, store.blocks[(Vector.replicate 32 0 : Root)]? = some block := by
  rcases reachable.linked anchorSlot with linked | known
  swap
  · rw [anchorParent, Std.TreeMap.contains_eq_isSome_getElem?] at known
    exact .inr (.inr (.inr (Option.isSome_iff_exists.mp known)))
  -- The head computes, so the store holds the justified block.
  have justifiedKnown : ∃ block, store.blocks[store.justifiedCheckpoint.root]? = some block := by
    unfold getHead at headOk
    cases tree : store.getFilteredNodeTree config with
    | error e => simp [tree, bind, Except.bind] at headOk
    | ok nodes => exact filterNodeTree_known tree
  obtain ⟨justifiedBlock, justifiedFound⟩ := justifiedKnown
  rcases Store.conflicting_of_not_descends linkHeader reachable.keysAreRoots linked.parentsBelow
      (fun found unknown => (linked.orphan _ _ found unknown).trans anchorParent) fits hle
      justifiedFound finalizedNonzero justifiedNonzero finalizedHeader notDescends with
    conflicting | zero | collision
  · exact .inl conflicting
  · exact .inr (.inl zero)
  · exact .inr (.inr (.inl collision))

end Store

end EthLib.Consensus
