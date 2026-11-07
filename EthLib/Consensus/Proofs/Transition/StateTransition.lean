module

public import EthLib.Consensus.Proofs.Transition.Block
public import EthLib.Consensus.Transition.StateTransition

/-!
# Proofs: the beacon state transition

The caching of a slot keeps the slot, and each slot step moves it on by exactly one.

From Gloas the caching also marks the payload of the next slot as not yet available.

Advancing to a slot fails when the slot is not after that of the state.

When it succeeds, the state ends exactly at that slot.

A valid block ran on the state at its slot.

When the result is validated, it carries its proposer's signature.

It then also commits to the root of the state after it.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- Clearing the availability of the next payload changes only the availability bits.

Their bit at the slot after the state's slot, in the circular buffer, is then false. -/
theorem unsetNextPayloadAvailability_ok {gloas : .glamsterdam ≤ fork}
    (computed : unsetNextPayloadAvailability state gloas = .ok after) :
    ∃ next : Slot, next.toNat = state.slot.toNat + 1 ∧
      after = { state with executionPayloadAvailability := fun _ =>
        ⟨(state.executionPayloadAvailability gloas).bits.set!
          (next % preset.SLOTS_PER_HISTORICAL_ROOT).toNat false⟩ } := by
  simp only [unsetNextPayloadAvailability, bind_ok_iff, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, rfl⟩ := computed
  exact ⟨next, by simpa using sum, rfl⟩

/-- The caching of a slot keeps every field but the roots and, from Gloas, the availability bits.

The result is the state with those fields replaced. -/
theorem processSlot_ok (computed : processSlot state = .ok after) :
    ∃ (stateRoots blockRoots : Vector Root preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
      (header : BeaconBlockHeader)
      (availability : Since .glamsterdam fork (ExecutionPayloadAvailability preset)),
      after = { state with
        stateRoots := stateRoots
        blockRoots := blockRoots
        latestBlockHeader := header
        executionPayloadAvailability := availability } := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · obtain ⟨_, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
    exact ⟨_, _, _, _, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨_, _, _, _, rfl⟩

/-- The caching of a slot keeps the slot. -/
theorem processSlot_slot (computed : processSlot state = .ok after) : after.slot = state.slot := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  rfl

/-- Slot caching fills an empty header state root with the root of the input state.

It keeps a nonempty header unchanged, including across empty slots. -/
theorem processSlot_latestBlockHeader (before : fork < .glamsterdam)
    (computed : processSlot state = .ok after) :
    ∃ stateRoot, hashTreeRoot state = .ok stateRoot ∧
      after.latestBlockHeader =
        if state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
          { state.latestBlockHeader with stateRoot } else state.latestBlockHeader := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok] at computed
  obtain ⟨stateRoot, stateRootOk, _, _, computed⟩ := computed
  have notGloas : ¬Fork.glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at computed
  subst after
  exact ⟨stateRoot, stateRootOk, rfl⟩

/-- Filling the state root keeps the slot of the most recent block header. -/
theorem processSlot_latestBlockHeader_slot (before : fork < .glamsterdam)
    (computed : processSlot state = .ok after) :
    after.latestBlockHeader.slot = state.latestBlockHeader.slot := by
  obtain ⟨_, _, header⟩ := processSlot_latestBlockHeader before computed
  rw [header]
  split <;> rfl

/-- Once its state root is filled, slot caching preserves the latest header. -/
theorem processSlot_latestBlockHeader_of_nonzero (before : fork < .glamsterdam)
    (computed : processSlot state = .ok after)
    (filled : state.latestBlockHeader.stateRoot ≠ Vector.replicate 32 0) :
    after.latestBlockHeader = state.latestBlockHeader := by
  obtain ⟨_, _, header⟩ := processSlot_latestBlockHeader before computed
  simpa only [filled, ↓reduceIte] using header

/-- Slot caching stores the root of its resulting latest header in the block-root buffer.

The zero state root is filled before that header is hashed. -/
theorem processSlot_blockRoot (before : fork < .glamsterdam)
    (nonzero : preset.SLOTS_PER_HISTORICAL_ROOT ≠ 0)
    (computed : processSlot state = .ok after) :
    ∃ root, hashTreeRoot after.latestBlockHeader = .ok root ∧
      readCircular after.blockRoots state.slot = .ok root := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok] at computed
  obtain ⟨stateRoot, stateRootOk, blockRoot, blockRootOk, computed⟩ := computed
  have notGloas : ¬Fork.glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at computed
  subst after
  refine ⟨blockRoot, blockRootOk, ?_⟩
  simp only [readCircular, nonzero, ↓reduceDIte, Vector.getElem_set!_self]

/-- Caching a different circular-buffer position preserves an earlier block-root read.

The explicit position inequality records the overwrite boundary. -/
theorem processSlot_readBlockRoot_of_ne (before : fork < .glamsterdam)
    (computed : processSlot state = .ok after) (slot : Slot)
    (different : (state.slot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat ≠
      (slot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat) :
    readCircular after.blockRoots slot = readCircular state.blockRoots slot := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  have notGloas : ¬Fork.glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at computed
  subst after
  unfold readCircular
  split
  · rfl
  · simp only [Vector.getElem_set!, different, ↓reduceIte]

/-- A recent earlier slot cannot share the position being cached before its overwrite boundary. -/
theorem processSlot_readBlockRoot_recent (before : fork < .glamsterdam)
    (computed : processSlot state = .ok after) (slot : Slot)
    (earlier : slot.toNat < state.slot.toNat)
    (recent : state.slot.toNat < slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    readCircular after.blockRoots slot = readCircular state.blockRoots slot := by
  apply processSlot_readBlockRoot_of_ne before computed slot
  intro same
  simp only [UInt64.toNat_mod] at same
  have oldDecomposition := Nat.mod_add_div slot.toNat preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  have newDecomposition := Nat.mod_add_div state.slot.toNat preset.SLOTS_PER_HISTORICAL_ROOT.toNat
  have dividesLater : slot.toNat / preset.SLOTS_PER_HISTORICAL_ROOT.toNat + 1 ≤
      state.slot.toNat / preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    by_cases le : state.slot.toNat / preset.SLOTS_PER_HISTORICAL_ROOT.toNat ≤
        slot.toNat / preset.SLOTS_PER_HISTORICAL_ROOT.toNat
    · have products := Nat.mul_le_mul_left preset.SLOTS_PER_HISTORICAL_ROOT.toNat le
      omega
    · omega
  have products := Nat.mul_le_mul_left preset.SLOTS_PER_HISTORICAL_ROOT.toNat dividesLater
  rw [Nat.mul_add, Nat.mul_one] at products
  omega

/-- Each successful block-root read after caching is old or names the newly cached header.

This includes overwrites of the circular buffer and needs no hash assumption. -/
theorem processSlot_readBlockRoot_origin (before : fork < .glamsterdam)
    (computed : processSlot state = .ok after) {slot : Slot} {root : Root}
    (read : readCircular after.blockRoots slot = .ok root) :
    readCircular state.blockRoots slot = .ok root ∨
      hashTreeRoot after.latestBlockHeader = .ok root := by
  by_cases same : (state.slot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat =
      (slot % preset.SLOTS_PER_HISTORICAL_ROOT).toNat
  · have nonzero : preset.SLOTS_PER_HISTORICAL_ROOT ≠ 0 := by
      intro zero
      simp [readCircular, zero] at read
    obtain ⟨actual, rooted, saved⟩ := processSlot_blockRoot before nonzero computed
    have sameRead : readCircular after.blockRoots state.slot =
        readCircular after.blockRoots slot := by
      simp only [readCircular, nonzero, ↓reduceDIte, same]
    have equal : actual = root := Except.ok.inj (saved.symm.trans (sameRead.trans read))
    exact .inr (equal ▸ rooted)
  · exact .inl ((processSlot_readBlockRoot_of_ne before computed slot same).symm.trans read)

/-- A cached root shared with another header gives the same header or an explicit collision.

The two collision inputs come from the cached and competing header computations. -/
theorem processSlot_blockRoot_binding (before : fork < .glamsterdam)
    (nonzero : preset.SLOTS_PER_HISTORICAL_ROOT ≠ 0)
    (computed : processSlot state = .ok after) {other : BeaconBlockHeader} {root : Root}
    (cached : readCircular after.blockRoots state.slot = .ok root)
    (otherRoot : hashTreeRoot other = .ok root) :
    after.latestBlockHeader = other ∨ ∃ leftTree rightTree,
      valueTree (desc BeaconBlockHeader) (toValue after.latestBlockHeader) = .ok leftTree ∧
      valueTree (desc BeaconBlockHeader) (toValue other) = .ok rightTree ∧
      ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
        x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y := by
  obtain ⟨actual, rooted, saved⟩ := processSlot_blockRoot before nonzero computed
  have same : actual = root := Except.ok.inj (saved.symm.trans cached)
  exact beaconBlockHeader_root_binding (same ▸ rooted) otherRoot

/-- From Gloas, after the caching of a slot, the payload of the next slot is not available.

Its bit is the one at the next slot modulo the length of the circular buffer. -/
theorem processSlot_nextPayloadUnavailable (gloas : .glamsterdam ≤ fork)
    (positive : 0 < preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (computed : processSlot state = .ok after) :
    (after.executionPayloadAvailability gloas).bits[(state.slot.toNat + 1) %
      preset.SLOTS_PER_HISTORICAL_ROOT.toNat]'(Nat.mod_lt _ positive) = false := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · obtain ⟨next, sum, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
    simp [UInt64.toNat_mod, sum]
  · contradiction

/-- One slot step moves the slot on by exactly one. -/
theorem advanceSlot_slot (computed : advanceSlot config state = .ok after) :
    after.slot.toNat = state.slot.toNat + 1 := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, _, _, _, _, rfl⟩ := computed
  exact sum

/-- Some count of slot steps moves the slot on by exactly that count. -/
theorem advanceSlots_slot :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config count state = .ok after → after.slot.toNat = state.slot.toNat + count
  | 0, _, _, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    rw [computed]
    rfl
  | count + 1, _, _, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    rw [advanceSlots_slot count rest, advanceSlot_slot first]
    omega

/-- A successful slot run splits at any prescribed initial number of steps. -/
theorem advanceSlots_add {first rest : Nat}
    (computed : advanceSlots config (first + rest) state = .ok after) :
    ∃ middle, advanceSlots config first state = .ok middle ∧
      advanceSlots config rest middle = .ok after := by
  induction first generalizing state with
  | zero => exact ⟨state, rfl, by simpa using computed⟩
  | succ first ih =>
    rw [Nat.succ_add] at computed
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, firstOk, restOk⟩ := computed
    obtain ⟨middle, prefixOk, suffixOk⟩ := ih restOk
    refine ⟨middle, ?_, suffixOk⟩
    simp only [advanceSlots, bind_ok_iff]
    exact ⟨next, firstOk, prefixOk⟩

/-- Advancing to a slot that is not after the slot of the state fails. -/
theorem processSlots_of_le {slot : Slot} (notAfter : slot ≤ state.slot) :
    processSlots config state slot = .error (.slotNotAfter slot state.slot) := by
  have : ¬state.slot < slot := UInt64.not_lt.mpr notAfter
  simp [processSlots, ensure, this, bind, Except.bind]

/-- Advancing to a slot succeeds only when the slot is after that of the state.

The state then ends exactly at that slot. -/
theorem processSlots_slot {slot : Slot} (computed : processSlots config state slot = .ok after) :
    state.slot < slot ∧ after.slot = slot := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, later, advanced⟩ := computed
  refine ⟨later, UInt64.toNat_inj.mp ?_⟩
  rw [advanceSlots_slot _ advanced]
  have := UInt64.lt_iff_toNat_lt.mp later
  omega

/-- A valid signed block ran on the state at its slot.

When the result is validated, the block carries its proposer's signature on that state.

Its state root is then the root of the state after it. -/
theorem applySignedBlock_ok {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : applySignedBlock config checks engine state signed validateResult = .ok after) :
    (validateResult = true → verifyBlockSignature config checks state signed = .ok true) ∧
      processBlock config checks engine state signed.message = .ok after ∧
      (validateResult = true → hashTreeRoot after = .ok signed.message.stateRoot) := by
  simp only [applySignedBlock, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, signatureOk, processed, blockOk, _, rootOk, rfl⟩ := computed
  refine ⟨fun validate => ?_, blockOk, fun validate => ?_⟩
  · simp only [checkBlockSignature, validate, ↓reduceIte, bind_ok_iff, ensure_ok_iff]
      at signatureOk
    obtain ⟨verified, verifiedOk, _, rfl, _⟩ := signatureOk
    exact verifiedOk
  · simp only [checkStateRoot, validate, ↓reduceIte, bind_ok_iff, ensure_ok_iff, liftSsz_ok]
      at rootOk
    obtain ⟨root, rootOk, same⟩ := rootOk
    rw [rootOk, same]

/-- A valid signed block ran on the state advanced to its slot.

When the result is validated, the block carries its proposer's signature on that state.

Its state root is then the root of the state after it. -/
theorem stateTransition_ok {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    ∃ advanced, processSlots config state signed.message.slot = .ok advanced ∧
      advanced.slot = signed.message.slot ∧
      (validateResult = true → verifyBlockSignature config checks advanced signed = .ok true) ∧
      processBlock config checks engine advanced signed.message = .ok after ∧
      (validateResult = true → hashTreeRoot after = .ok signed.message.stateRoot) := by
  simp only [stateTransition, bind_ok_iff] at computed
  obtain ⟨advanced, slotsOk, applied⟩ := computed
  exact ⟨advanced, slotsOk, (processSlots_slot slotsOk).2, applySignedBlock_ok applied⟩

end EthLib.Consensus
