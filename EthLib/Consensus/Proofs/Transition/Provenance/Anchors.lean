module

public import EthLib.Consensus.Proofs.Transition.Provenance.Links

/-!
# Proofs: the blocks behind the roots of checkpoints

A checkpoint's root is the root a weighing call read for the first slot of its epoch.

The caching of that slot stored the root of the latest header then.

That header is the header of the latest block at or before the slot.

Or no block ran since the start, and it is the start's header.

So the root of a justified checkpoint is the root of an actual block of the chain, at or before
the first slot of its epoch.

A block whose root is zero leaves that zero root in the next caching, which is evidence.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The root of the start's latest header, with some state root.

From genesis this is the genesis block, which no block step of the chain applied. -/
def StartHeaderRoot (start : ForkedBeaconState preset) (root : Root) : Prop :=
  ∃ stateRoot, hashTreeRoot { start.state.latestBlockHeader with stateRoot } = .ok root

/-- The header that a caching stores is the header of a block of the chain at or before the slot,
or the start's header, or a state of the chain has the zero root. -/
theorem Reaches.cachedHeader_block {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached : BeaconState preset fork} (head : Reaches config checks start ⟨fork, state⟩)
    (cachedOk : processSlot state = .ok cached) (tail : Reaches config checks ⟨fork, state⟩ after)
    {root : Root} (rootOk : hashTreeRoot cached.latestBlockHeader = .ok root) :
    (∃ (parentRoot : Root) (slot : Slot), ChainBlockAt config checks start after parentRoot root slot ∧
        slot.toNat ≤ state.slot.toNat) ∨
      StartHeaderRoot start root ∨ ZeroRootFound config checks start after := by
  obtain ⟨stateRoot, -, stateRootOk, header, -⟩ := processSlot_roots cachedOk
  rw [header] at rootOk
  rcases head.latestBlockHeader with settled | ⟨fork', engine, signed, validateResult, blockState,
    post, bodyRoot, blockHead, notDue, applied, bodyRootOk, settled⟩
  · -- No block ran: the header is the start's, with some state root.
    obtain ⟨-, settledRoot, current, -⟩ := settled
    simp only at current
    rw [current] at rootOk
    right; left
    unfold fillStateRoot at rootOk
    split at rootOk
    · exact ⟨_, rootOk⟩
    · exact ⟨_, rootOk⟩
  obtain ⟨blockSlot, -, -, -, postSlot, -⟩ := applySignedBlock_roots applied
  have blockChain : Reaches config checks start ⟨fork', post⟩ :=
    blockHead.step (.block engine signed validateResult notDue applied)
  have toState := settled.1
  have slotLe : signed.message.slot.toNat ≤ state.slot.toNat := by
    have := toState.slot_le
    simp only at this
    rw [blockSlot, ← postSlot]
    exact this
  rcases settled.of_block notDue applied with ⟨same, written⟩ | ⟨postRoot, postRootOk, current, -⟩ |
    zero
  · -- The chain is at the state after the block, so the caching fills the block's header.
    simp only [ForkedBeaconState.mk.injEq] at same
    obtain ⟨rfl, same⟩ := same
    cases same
    rw [written] at rootOk
    simp only [fillStateRoot, BeaconBlock.header, ↓reduceIte] at rootOk
    exact .inl ⟨_, _, ⟨_, engine, signed, validateResult, blockState, _, bodyRoot, stateRoot,
      blockHead, notDue, applied, tail, bodyRootOk, stateRootOk, rfl, rootOk, rfl⟩, slotLe⟩
  · simp only at current
    by_cases unfilled : postRoot = Vector.replicate 32 0
    · subst unfilled
      exact .inr (.inr ⟨_, blockChain, toState.trans tail, postRootOk⟩)
    · rw [current, fillStateRoot_of_ne unfilled] at rootOk
      exact .inl ⟨_, _, ⟨fork', engine, signed, validateResult, blockState, post, bodyRoot,
        postRoot, blockHead, notDue, applied, toState.trans tail, bodyRootOk, postRootOk, rfl,
        rootOk, rfl⟩, slotLe⟩
  · exact .inr (.inr ⟨_, blockChain, toState.trans tail, zero⟩)

/-- The root of a checkpoint that a call justified is the root of a block of the chain at or
before the first slot of its epoch.

Or it is the start's header, or a state of the chain has the zero root.

The first slot of the epoch must be from the start on, as from genesis, and the buffer of roots
must span two epochs. -/
theorem JustifiedBy.root_block {start after : ForkedBeaconState preset} {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (justified : JustifiedBy config checks start after checkpoint)
    (fromStart : start.state.slot.toNat ≤
      checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    (∃ (parentRoot : Root) (slot : Slot),
        ChainBlockAt config checks start after parentRoot checkpoint.root slot ∧
        slot.toNat ≤ checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) ∨
      StartHeaderRoot start checkpoint.root ∨ ZeroRootFound config checks start after := by
  obtain ⟨fork, state, cached, _, next, _, call⟩ := justified
  obtain ⟨slot, slotEq, below, near, read⟩ :=
    processSlot_read wide call.cachedOk call.later call.recent call.rootOk
  -- A slot step before the call cached that slot, and wrote the root of its header.
  obtain ⟨fork', state', cached', ⟨atSlot, cachedOk', next', nextOk', notDue', head', tail'⟩,
    ⟨root, rootOk', written⟩, -⟩ :=
    call.head.roots_written (by rw [slotEq]; exact fromStart) below near
  rw [read] at written
  cases written
  have toAfter : Reaches config checks ⟨fork', state'⟩ after :=
    ((Reaches.refl _).step (.slot notDue' nextOk')).trans (tail'.trans call.toAfter)
  rcases head'.cachedHeader_block cachedOk' toAfter rootOk' with
    ⟨parentRoot, blockSlot, block, slotLe⟩ | genesisRoot | zero
  · refine .inl ⟨parentRoot, blockSlot, block, ?_⟩
    rw [← slotEq, ← atSlot]
    exact slotLe
  · exact .inr (.inl genesisRoot)
  · exact .inr (.inr zero)

/-- From genesis, the finalized and the current justified checkpoint of a chain's end have the
root of a block of the chain at or before the first slot of their epoch.

Or the root is zero, of the genesis checkpoint, or the genesis block's, or a state of the chain
has the zero root. -/
theorem Reaches.checkpoint_root_block {start after : ForkedBeaconState preset}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start) (chain : Reaches config checks start after)
    {checkpoint : Checkpoint}
    (isOne : checkpoint = after.state.finalizedCheckpoint ∨
      checkpoint = after.state.currentJustifiedCheckpoint) :
    checkpoint.root = Vector.replicate 32 0 ∨
      (∃ (parentRoot : Root) (slot : Slot),
        ChainBlockAt config checks start after parentRoot checkpoint.root slot ∧
        slot.toNat ≤ checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) ∨
      StartHeaderRoot start checkpoint.root ∨ ZeroRootFound config checks start after := by
  obtain ⟨startSlot, startPrevious, startCurrent, startFinalized⟩ := genesis_state genesis
  obtain ⟨finalized, -, current⟩ := chain.checkpoints
  have justified : JustifiedOrStart config checks start after checkpoint := by
    rcases isOne with rfl | rfl
    · exact finalized
    · exact current
  rcases justified with same | same | same | justified
  · exact .inl (by rw [same, startFinalized])
  · exact .inl (by rw [same, startPrevious])
  · exact .inl (by rw [same, startCurrent])
  · exact .inr (justified.root_block wide (by rw [startSlot]; exact Nat.zero_le _))

/-- A block of a chain whose root is zero leaves the zero root in the next caching.

So once the chain is past the block's slot, a header that a slot step cached has the zero root.
-/
theorem ChainBlockAt.zeroHeader {start after : ForkedBeaconState preset} {parentRoot : Root}
    {slot : Slot}
    (block : ChainBlockAt config checks start after parentRoot (Vector.replicate 32 0) slot)
    (past : slot.toNat < after.state.slot.toNat) :
    ZeroHeaderFound config checks start after := by
  obtain ⟨fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot, head, notDue,
    applied, tail, bodyRootOk, stateRootOk, _, rootOk, rfl⟩ := block
  obtain ⟨blockSlot, -, -, ⟨bodyRoot', bodyRootOk', written⟩, postSlot, -⟩ :=
    applySignedBlock_roots applied
  have postNotDue : upgradeDue config ⟨fork, post⟩ = false := by
    rw [upgradeDue_of_slot postSlot]
    exact notDue
  have headerSlot : post.latestBlockHeader.slot = post.slot := by
    rw [written, postSlot]
    exact blockSlot
  -- The first step past the block's slot starts at the state after the block.
  obtain ⟨before, next, toBefore, notPast, ⟨step⟩, isPast, toAfter⟩ :=
    tail.split (holds := fun forked => post.slot.toNat < forked.state.slot.toNat)
      (Nat.lt_irrefl _) (by rw [postSlot, ← blockSlot]; exact past)
  have beforeSlot : before.state.slot = post.slot := by
    have := toBefore.slot_le
    simp only at this notPast
    exact UInt64.toNat_inj.mp (by omega)
  have same := toBefore.eq_of_slot_after_block postNotDue headerSlot beforeSlot
  subst same
  cases step with
  | @slot _ _ next' stepNotDue computed =>
    obtain ⟨cached, cachedOk, -, -, -, -⟩ := advanceSlot_roots computed
    obtain ⟨postRoot, -, postRootOk, header, -⟩ := processSlot_roots cachedOk
    cases postRootOk.symm.trans stateRootOk
    cases bodyRootOk'.symm.trans bodyRootOk
    refine ⟨post.slot, fork, post, cached, ⟨rfl, cachedOk, next', computed, stepNotDue,
      head.step (.block engine signed validateResult notDue applied), toAfter⟩, ?_⟩
    rw [header, written]
    simpa [fillStateRoot, BeaconBlock.header] using rootOk
  | upgrade due computed =>
    exact absurd postNotDue (by rw [due]; decide)
  | block _ _ _ _ computed =>
    obtain ⟨-, -, -, -, sameSlot, -⟩ := applySignedBlock_roots computed
    simp only at isPast
    rw [sameSlot] at isPast
    exact absurd isPast (Nat.lt_irrefl _)

end EthLib.Consensus
