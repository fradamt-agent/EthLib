module

public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.ForkChoice.Runs
public import EthLib.Consensus.Proofs.Transition.Provenance.Ancestry

/-!
# Proofs: the checkpoint walk of a store follows the parent links of a chain

The store finds the checkpoint block of a root at an epoch with a walk on its own blocks.

The walk starts at the root.

It moves to the parent while the block sits after the first slot of the epoch.

A chain links a parent root to the root of each block that it runs.

That root is the root of the block's header, with the root of the state after it.

Take a path of such links from a root `f` to a known root `j`.

Each link leads to a block after the first slot of the epoch.

The walk of the store from `j` then follows the same path back to `f`.

It stops at `f` when the store holds `f` at or before the first slot of the epoch.

Otherwise one of three things happened:

- The store holds `f` after the first slot of the epoch.
- The path reaches a known block whose parent the store does not hold.
- Two different headers have one root, and a search over their hash inputs finds a collision.

The store keys each block by its own root, and a block and its header have one root.

So the store's walk and the chain's links compare through header roots.

That needs no assumption on SHA-256.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz SszType

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-- Every block step of a chain has the slot of its block. -/
theorem ChainBlock.exists_slot {start after : ForkedBeaconState preset} {parentRoot root : Root}
    (block : ChainBlock config checks start after parentRoot root) :
    ∃ slot, ChainBlockAt config checks start after parentRoot root slot :=
  have ⟨fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot, head, notDue,
    applied, tail, bodyOk, stateOk, parent, rootOk⟩ := block
  ⟨_, fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot, head, notDue,
    applied, tail, bodyOk, stateOk, parent, rootOk, rfl⟩

/-- A block step of a chain has a header with its root, its parent root and its slot. -/
theorem ChainBlockAt.header {start after : ForkedBeaconState preset} {parentRoot root : Root}
    {slot : Slot} (block : ChainBlockAt config checks start after parentRoot root slot) :
    ∃ header : BeaconBlockHeader, hashTreeRoot header = .ok root ∧
      header.parentRoot = parentRoot ∧ header.slot = slot :=
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, parent, rootOk, slot⟩ := block
  ⟨_, rootOk, parent, slot⟩

/-- Two different headers have one root, and a search over their hash inputs finds a collision.
-/
def HeaderCollision : Prop :=
  ∃ (left right : BeaconBlockHeader) (root : Root), left ≠ right ∧
    hashTreeRoot left = .ok root ∧ hashTreeRoot right = .ok root ∧
    HashCollisionFound (sszMessages left ++ sszMessages right)

namespace Store

variable {store : Store preset fork}

/-- The store keys each block by its own root. -/
def KeysAreRoots (store : Store preset fork) : Prop :=
  ∀ {root : Root} {block : BeaconBlock preset fork}, store.blocks[root]? = some block →
    hashTreeRoot block = .ok root

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork}

/-- A reachable store keys each block by its own root. -/
theorem Reachable.keysAreRoots (reachable : Reachable config anchorState anchorBlock store) :
    store.KeysAreRoots := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, rootOk, blocks, -⟩ := getForkchoiceStore_maps made
    intro r b found
    rw [blocks, getElem?_insert_root] at found
    split at found
    · rename_i same
      cases found
      rw [← same]
      exact rootOk
    · simp at found
  | tick _ ticked ih =>
    intro r b found
    rw [(onTick_frame ticked).2.2.1] at found
    exact ih found
  | attestation _ attested ih =>
    intro r b found
    rw [(onAttestation_frame attested).2.1] at found
    exact ih found
  | attesterSlashing _ slashed ih =>
    intro r b found
    rw [(onAttesterSlashing_frame slashed).2.1] at found
    exact ih found
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    intro r b found
    rw [(onExecutionPayloadEnvelope_frame accepted).2.1] at found
    exact ih found
  | inclusionList _ accepted ih =>
    intro r b found
    rw [(onInclusionList_frame accepted).2.1] at found
    exact ih found
  | block _ added ih =>
    obtain same | ⟨blockRoot, rootOk, -, blocks, -⟩ := onBlock_same_or_insert added
    · subst same
      exact ih
    intro r b found
    rw [blocks, getElem?_insert_root] at found
    split at found
    · rename_i same
      cases found
      rw [← same]
      exact rootOk
    · exact ih found

/-! ## The walk to a slot, by roots -/

/-- The walk from a known block above the slot moves to its parent, as far as roots go. -/
theorem getAncestor_root_step {root : Root} {slot : Slot} {block parent : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block) (above : ¬ block.slot ≤ slot)
    (parentFound : store.blocks[block.parentRoot]? = some parent)
    (lower : parent.slot < block.slot) :
    (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot =
      (·.root) <$> store.getAncestor ⟨block.parentRoot, .pending⟩ slot := by
  rw [getAncestor_step (node := ⟨root, .pending⟩) found above parentFound lower]
  exact getAncestor_root _ _ _

/-- The walk to a slot from a known block at or before the slot stays there. -/
theorem getAncestor_root_of_le {root : Root} {slot : Slot} {block : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block) (le : block.slot ≤ slot) :
    (·.root) <$> store.getAncestor ⟨root, .pending⟩ slot = .ok root := by
  rw [getAncestor_of_le (node := ⟨root, .pending⟩) found le]
  rfl

/-- The checkpoint block of a root at an epoch is the root that the walk reaches.

The walk goes to the first slot of the epoch. -/
theorem getCheckpointBlock_eq {root : Root} {epoch : Epoch} {start : Slot}
    (startOk : computeStartSlotAtEpoch preset epoch = .ok start) :
    store.getCheckpointBlock root epoch =
      (·.root) <$> store.getAncestor ⟨root, .pending⟩ start := by
  simp only [getCheckpointBlock, startOk, Except.mapError, bind, Except.bind]
  cases store.getAncestor ⟨root, .pending⟩ start <;> rfl

/-! ## Following the links of a chain -/

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

/-- Take a header with the root of a block that the store keys by its root.

It is the block's header, or two headers collide.

The block's header has its slot and its parent root. -/
theorem KeysAreRoots.header_eq (keys : store.KeysAreRoots) {root : Root}
    {block : BeaconBlock preset fork} (found : store.blocks[root]? = some block)
    {header : BeaconBlockHeader} (headerRoot : hashTreeRoot header = .ok root) :
    (header.slot = block.slot ∧ header.parentRoot = block.parentRoot) ∨ HeaderCollision := by
  obtain ⟨bodyRoot, bodyRootOk⟩ := SszType.hashTreeRoot_total block.body
  have blockHeader : hashTreeRoot (block.toHeader bodyRoot) = .ok root := by
    rw [hashTreeRoot_toHeader bodyRootOk]
    exact keys found
  rcases beaconBlockHeader_root_binding headerRoot blockHeader with same | collision
  · subst same
    exact .inl ⟨rfl, rfl⟩
  · by_cases same : header = block.toHeader bodyRoot
    · subst same
      exact .inl ⟨rfl, rfl⟩
    · exact .inr ⟨_, _, root, same, headerRoot, blockHeader, collision⟩

/-- Along a path of links to blocks after a slot, the store's walk to the slot follows the path.

Each link names a header with the root of its child, its parent root and a slot.

That slot is after the given one.

From each root of the path that the store holds, the walk ends where it ends from `f`.

Otherwise the path reaches a known block, above the slot, whose parent the store does not hold.

Or two headers collide. -/
theorem getAncestor_root_of_links (keys : store.KeysAreRoots) (lower : store.ParentsBelow)
    {slot : Slot} {link : Root → Root → Prop}
    (headerOf : ∀ {parentRoot root : Root}, link parentRoot root →
      ∃ header : BeaconBlockHeader, hashTreeRoot header = .ok root ∧
        header.parentRoot = parentRoot ∧ slot < header.slot)
    {f r : Root} (path : Relation.ReflTransGen link f r) :
    ∀ {block : BeaconBlock preset fork}, store.blocks[r]? = some block →
      ((∃ fBlock, store.blocks[f]? = some fBlock) ∧
        (·.root) <$> store.getAncestor ⟨r, .pending⟩ slot =
          (·.root) <$> store.getAncestor ⟨f, .pending⟩ slot) ∨
        (∃ (known : Root) (knownBlock : BeaconBlock preset fork),
          Relation.ReflTransGen link f known ∧ store.blocks[known]? = some knownBlock ∧
          slot < knownBlock.slot ∧ store.blocks[knownBlock.parentRoot]? = none) ∨
        HeaderCollision := by
  induction path with
  | refl => exact fun found => .inl ⟨⟨_, found⟩, rfl⟩
  | @tail parentRoot root head step ih =>
    intro block found
    obtain ⟨header, headerRoot, headerParent, headerSlot⟩ := headerOf step
    rcases keys.header_eq found headerRoot with ⟨sameSlot, sameParent⟩ | collision
    · rw [sameSlot] at headerSlot
      rw [sameParent] at headerParent
      cases parentFound : store.blocks[block.parentRoot]? with
      | none => exact .inr (.inl ⟨root, block, head.tail step, found, headerSlot, parentFound⟩)
      | some parent =>
        rw [headerParent] at parentFound
        rcases ih parentFound with ⟨fKnown, same⟩ | exits | collision
        · refine .inl ⟨fKnown, ?_⟩
          rw [getAncestor_root_step found (UInt64.not_le.mpr headerSlot)
            (headerParent ▸ parentFound) (lower _ block parent found (headerParent ▸ parentFound)),
            headerParent, same]
        · exact .inr (.inl exits)
        · exact .inr (.inr collision)
    · exact .inr (.inr collision)

/-- The checkpoint block of a known root is the start of a path of links.

Each link leads to a block after the first slot of the epoch.

The store must hold the start at or before the first slot of the epoch.

Otherwise the store holds the start after that slot.

Or the path reaches a known block, after that slot, whose parent the store does not hold.

Or two headers collide. -/
theorem getCheckpointBlock_of_links (keys : store.KeysAreRoots) (lower : store.ParentsBelow)
    {epoch : Epoch} {start : Slot} (startOk : computeStartSlotAtEpoch preset epoch = .ok start)
    {link : Root → Root → Prop}
    (headerOf : ∀ {parentRoot root : Root}, link parentRoot root →
      ∃ header : BeaconBlockHeader, hashTreeRoot header = .ok root ∧
        header.parentRoot = parentRoot ∧ start < header.slot)
    {f j : Root} (path : Relation.ReflTransGen link f j) {jBlock : BeaconBlock preset fork}
    (jFound : store.blocks[j]? = some jBlock) :
    store.getCheckpointBlock j epoch = .ok f ∨
      (∃ fBlock, store.blocks[f]? = some fBlock ∧ start < fBlock.slot) ∨
      (∃ (known : Root) (knownBlock : BeaconBlock preset fork),
        Relation.ReflTransGen link f known ∧ store.blocks[known]? = some knownBlock ∧
        start < knownBlock.slot ∧ store.blocks[knownBlock.parentRoot]? = none) ∨
      HeaderCollision := by
  rw [getCheckpointBlock_eq startOk]
  rcases getAncestor_root_of_links keys lower headerOf path jFound with
    ⟨⟨fBlock, fFound⟩, same⟩ | exits | collision
  · rw [same]
    by_cases le : fBlock.slot ≤ start
    · exact .inl (getAncestor_root_of_le fFound le)
    · exact .inr (.inl ⟨fBlock, fFound, UInt64.not_le.mp le⟩)
  · exact .inr (.inr (.inl exits))
  · exact .inr (.inr (.inr collision))


variable {config : Config} {checks : SignatureChecks} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork}

/-- In a reachable store, the checkpoint block of a known root is the start of a path.

The path is of chain links along one chain, each to a block after the first slot of the epoch.

The store must hold the start at or before the first slot of the epoch.

Otherwise one of three things happened:

- The store holds the start after that slot.
- The path passes through the parent root of the anchor.
- Two headers collide.

The anchor block must sit at or before the slot of the anchor state.

Every block body must have a root, which the positive sizes of the preset give.

The parent root of the anchor must name no known block. -/
theorem Reachable.getCheckpointBlock_of_chainLinks
    (reachable : Reachable config anchorState anchorBlock store)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (unknown : store.blocks[anchorBlock.parentRoot]? = none)
    {epoch : Epoch} {start : Slot} (startOk : computeStartSlotAtEpoch preset epoch = .ok start)
    {first last : ForkedBeaconState preset} {f j : Root}
    (path : PastAncestor config checks first last start.toNat f j)
    {jBlock : BeaconBlock preset fork} (jFound : store.blocks[j]? = some jBlock) :
    store.getCheckpointBlock j epoch = .ok f ∨
      (∃ fBlock, store.blocks[f]? = some fBlock ∧ start < fBlock.slot) ∨
      PastAncestor config checks first last start.toNat f anchorBlock.parentRoot ∨
      HeaderCollision := by
  have keys : store.KeysAreRoots := reachable.keysAreRoots
  have lower := reachable.parentsBelow anchorSlot unknown
  have linked := (reachable.linked anchorSlot).resolve_right (by
    rw [Std.TreeMap.contains_eq_isSome_getElem?, unknown]
    simp)
  have headerOf : ∀ {parentRoot root : Root},
      ChainBlockAfter config checks first last start.toNat parentRoot root →
      ∃ header : BeaconBlockHeader, hashTreeRoot header = .ok root ∧
        header.parentRoot = parentRoot ∧ start < header.slot := by
    rintro parentRoot root ⟨blockSlot, block, after⟩
    obtain ⟨header, rootOk, parent, slot⟩ := block.header
    exact ⟨header, rootOk, parent, UInt64.lt_iff_toNat_lt.mpr (slot ▸ after)⟩
  rcases getCheckpointBlock_of_links keys lower startOk headerOf path jFound with
    same | late | ⟨known, knownBlock, head, knownFound, knownLate, parentUnknown⟩ | collision
  · exact .inl same
  · exact .inr (.inl late)
  · -- A known block with an unknown parent has the anchor's parent root.
    have orphan := linked.orphan known knownBlock knownFound parentUnknown
    rcases Relation.ReflTransGen.cases_tail head with same | ⟨parentRoot, before, step⟩
    · subst same
      exact .inr (.inl ⟨knownBlock, knownFound, knownLate⟩)
    · obtain ⟨header, headerRoot, headerParent, -⟩ := headerOf step
      rcases keys.header_eq knownFound headerRoot with ⟨-, sameParent⟩ | collision
      · rw [← headerParent, sameParent, orphan] at before
        exact .inr (.inr (.inl before))
      · exact .inr (.inr (.inr collision))
  · exact .inr (.inr (.inr collision))

end Store

end EthLib.Consensus
