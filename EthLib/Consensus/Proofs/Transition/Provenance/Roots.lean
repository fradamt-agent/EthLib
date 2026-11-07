module

public import EthLib.Consensus.Proofs.Transition.Provenance.Kept
public import EthLib.Consensus.Proofs.Transition.Reachable
public import EthLib.Consensus.Proofs.Transition.Slot

/-!
# Proofs: where the block roots and state roots come from

A state keeps the roots of its recent history in two circular buffers.

```text
    blockRoots[slot mod N]  the root of the latest block header, cached at that slot
    stateRoots[slot mod N]  the root of the state at the end of that slot
```

Here `N` is `SLOTS_PER_HISTORICAL_ROOT`.

Only the caching of a slot, `processSlot`, writes the buffers.

It writes one entry, at the slot of the state.

It also fills the state root of the latest block header, if that root is still zero.

A block writes the header, with a zero state root, since the state after it has no root yet.

This file traces each entry of a buffer to the slot step of a chain that wrote it.

It traces the latest header to the block step that wrote it, or to the start of the chain.

No statement assumes that SHA-256 has no collision, or that no state has the zero root.

The zero root matters: a header whose state root stays zero is filled again at the next slot.

So when the state after a block has the zero root, the header can take a later state's root.

The statements keep that case as an explicit alternative.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- The latest header with its state root filled, as the caching of a slot does.

A header whose state root is not zero keeps it. -/
def fillStateRoot (header : BeaconBlockHeader) (stateRoot : Root) : BeaconBlockHeader :=
  if header.stateRoot = Vector.replicate 32 0 then { header with stateRoot } else header

/-! ## One step -/

/-- What the caching of a slot writes.

The root of the state goes into the state roots, at the slot of the state.

The latest header has its state root filled with that root, if it was zero.

The root of that header goes into the block roots, at the same slot.

The justification bits stay. -/
theorem processSlot_roots (computed : processSlot state = .ok after) :
    ∃ stateRoot blockRoot,
      hashTreeRoot state = .ok stateRoot ∧
      after.latestBlockHeader = fillStateRoot state.latestBlockHeader stateRoot ∧
      hashTreeRoot after.latestBlockHeader = .ok blockRoot ∧
      writeCircular state.stateRoots.elements state.slot stateRoot =
        .ok after.stateRoots.elements ∧
      writeCircular state.blockRoots.elements state.slot blockRoot =
        .ok after.blockRoots.elements ∧
      after.justificationBits = state.justificationBits := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
  obtain ⟨stateRoot, stateRootOk, stateRoots, stateRootsOk, blockRoot, blockRootOk, blockRoots,
    blockRootsOk, computed⟩ := computed
  -- From Gloas the last step also clears one bit of payload availability, and nothing else.
  have last : after = { state with
      stateRoots, latestBlockHeader := fillStateRoot state.latestBlockHeader stateRoot,
      blockRoots } ∨
      ∃ availability, after = { state with
        stateRoots, latestBlockHeader := fillStateRoot state.latestBlockHeader stateRoot,
        blockRoots, executionPayloadAvailability := availability } := by
    split at computed
    · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
      exact .inr ⟨_, rfl⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact .inl computed.symm
  have stateWrite := writeCircularRooted_elements state.stateRoots state.slot stateRoot
  have blockWrite := writeCircularRooted_elements state.blockRoots state.slot blockRoot
  rw [stateRootsOk] at stateWrite
  rw [blockRootsOk] at blockWrite
  rcases last with rfl | ⟨_, rfl⟩ <;>
    exact ⟨stateRoot, blockRoot, stateRootOk, rfl, blockRootOk, stateWrite.symm,
      blockWrite.symm, rfl⟩

/-- One slot step caches the slot, then may close the epoch, then moves the slot on.

Closing the epoch keeps the header and the two buffers, so they are those of the cached state.
-/
theorem advanceSlot_roots (computed : advanceSlot config checks state = .ok after) :
    ∃ cached, processSlot state = .ok cached ∧
      after.slot.toNat = state.slot.toNat + 1 ∧
      after.latestBlockHeader = cached.latestBlockHeader ∧
      after.blockRoots = cached.blockRoots ∧ after.stateRoots = cached.stateRoots := by
  have slot := advanceSlot_slot computed
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  refine ⟨cached, cachedOk, slot, ?_⟩
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨justified, justifiedOk, kept⟩ := processEpoch_kept epochedOk
    obtain ⟨header, blockRoots, stateRoots⟩ := processJustificationAndFinalization_roots justifiedOk
    exact ⟨kept.latestBlockHeader.trans header, kept.blockRoots.trans blockRoots,
      kept.stateRoots.trans stateRoots⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact ⟨rfl, rfl, rfl⟩

/-- What a block step writes.

The block runs at the slot of the state, after the latest block, and names it as its parent.

From Gloas the payload of the parent runs first, and keeps the latest header.

The new latest header is that of the block, with a zero state root.

The slot and the two buffers stay.

When the result is validated, the block's state root is the root of the state after it. -/
theorem applySignedBlock_roots {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : applySignedBlock config checks engine state signed validateResult = .ok after) :
    signed.message.slot = state.slot ∧
      state.latestBlockHeader.slot < signed.message.slot ∧
      hashTreeRoot state.latestBlockHeader = .ok signed.message.parentRoot ∧
      (∃ bodyRoot, hashTreeRoot signed.message.body = .ok bodyRoot ∧
        after.latestBlockHeader =
          { slot := signed.message.slot, proposerIndex := signed.message.proposerIndex,
            parentRoot := signed.message.parentRoot, stateRoot := Vector.replicate 32 0,
            bodyRoot }) ∧
      after.slot = state.slot ∧ after.blockRoots = state.blockRoots ∧
      after.stateRoots = state.stateRoots ∧
      (validateResult = true → hashTreeRoot after = .ok signed.message.stateRoot) := by
  obtain ⟨-, processed, validated⟩ := applySignedBlock_ok computed
  obtain ⟨paid, headed, paidKept, headedOk, headedKept⟩ := processBlock_kept processed
  obtain ⟨slot, newer, -, parent, -⟩ := processBlockHeader_checks headedOk
  obtain ⟨bodyRoot, bodyRootOk, rfl⟩ := processBlockHeader_eq headedOk
  rw [paidKept.latestBlockHeader, paidKept.slot] at *
  exact ⟨slot, newer, parent, ⟨bodyRoot, bodyRootOk, headedKept.latestBlockHeader⟩,
    headedKept.slot, headedKept.blockRoots.trans paidKept.blockRoots,
    headedKept.stateRoots.trans paidKept.stateRoots, validated⟩

/-- An upgrade keeps the slot, the latest header and the two buffers. -/
theorem upgradeNext_roots {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.slot = pre.state.slot ∧
      post.val.state.latestBlockHeader = pre.state.latestBlockHeader ∧
      post.val.state.blockRoots = pre.state.blockRoots ∧
      post.val.state.stateRoots = pre.state.stateRoots := by
  have same := upgradeNext_history computed
  simp only [BeaconState.history, Prod.mk.injEq] at same
  exact ⟨same.1, same.2.1, same.2.2.1, same.2.2.2.1⟩

/-! ## Chains -/

/-- Along a chain the slot never decreases. -/
theorem stepRelation_slot :
    StepRelation config checks fun (forked after : ForkedBeaconState preset) =>
      forked.state.slot.toNat ≤ after.state.slot.toNat where
  refl _ := Nat.le_refl _
  trans first second := Nat.le_trans first second
  advanceSlot computed := by
    simp only [advanceSlot_slot computed]
    omega
  upgradeNext _ computed := Nat.le_of_eq (by rw [(upgradeNext_roots computed).1])
  applySignedBlock computed :=
    Nat.le_of_eq (by simp only [(applySignedBlock_roots computed).2.2.2.2.1])

theorem Reaches.slot_le {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) :
    start.state.slot.toNat ≤ after.state.slot.toNat :=
  stepRelation_slot.reaches chain

/-- A chain caches a slot at one of its slot steps.

The step starts at `state`, whose slot is that slot, and its caching gives `cached`.

No upgrade is due at `state`, since a slot step runs only after the upgrades due.

The chain runs from its start to `state`, and on from the state after the step. -/
def CachesSlot (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset)
    (slot : Slot) {fork : Fork} (state cached : BeaconState preset fork) : Prop :=
  state.slot = slot ∧ processSlot state = .ok cached ∧
    ∃ next, advanceSlot config checks state = .ok next ∧ upgradeDue config ⟨fork, state⟩ = false ∧
      Reaches config checks start ⟨fork, state⟩ ∧ Reaches config checks ⟨fork, next⟩ after

theorem CachesSlot.extend {start middle after : ForkedBeaconState preset} {slot : Slot}
    {fork : Fork} {state cached : BeaconState preset fork}
    (caches : CachesSlot config checks start middle slot state cached)
    (step : Step config checks middle after) :
    CachesSlot config checks start after slot state cached :=
  have ⟨atSlot, cachedOk, next, nextOk, notDue, head, tail⟩ := caches
  ⟨atSlot, cachedOk, next, nextOk, notDue, head, tail.step step⟩

/-- Two different slots less than the length of the buffer apart take different entries. -/
theorem mod_ne_of_lt {n earlier later : UInt64} (before : earlier.toNat < later.toNat)
    (near : later.toNat < earlier.toNat + n.toNat) : later % n ≠ earlier % n := by
  intro same
  have same := congrArg UInt64.toNat same
  rw [UInt64.toNat_mod, UInt64.toNat_mod] at same
  have := Nat.sub_mod_eq_zero_of_mod_eq same
  have positive : 0 < later.toNat - earlier.toNat := by omega
  obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero this
  rcases k with _ | k
  · omega
  · rw [Nat.mul_succ] at hk
    omega

/-- Where an entry of the two buffers of roots comes from.

Take a chain, and a slot from the start of the chain up to the slot before its end.

The entry must still be in the buffer: the end is at most `N` slots after that slot.

Then one slot step of the chain cached that slot.

The block root is the root of the latest header after that caching.

The state root is the root of the state that the caching started from. -/
theorem Reaches.roots_written {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) {slot : Slot}
    (fromStart : start.state.slot.toNat ≤ slot.toNat)
    (written : slot.toNat < after.state.slot.toNat)
    (recent : after.state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ∃ (fork : Fork) (state cached : BeaconState preset fork),
      CachesSlot config checks start after slot state cached ∧
      (∃ root, hashTreeRoot cached.latestBlockHeader = .ok root ∧
        readCircular after.state.blockRoots.elements slot = .ok root) ∧
      (∃ root, hashTreeRoot state = .ok root ∧
        readCircular after.state.stateRoots.elements slot = .ok root) := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => omega
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    cases step with
    | @slot fork state next notDue computed =>
      obtain ⟨cached, cachedOk, nextSlot, header, blockRoots, stateRoots⟩ :=
        advanceSlot_roots computed
      obtain ⟨stateRoot, blockRoot, stateRootOk, _, blockRootOk, stateWrite, blockWrite, _⟩ :=
        processSlot_roots cachedOk
      simp only at written recent nextSlot ⊢
      rw [blockRoots, stateRoots]
      by_cases here : slot.toNat = state.slot.toNat
      · -- This step cached the slot.
        have same : state.slot = slot := UInt64.toNat_inj.mp here.symm
        subst same
        refine ⟨fork, state, cached, ⟨rfl, cachedOk, next, computed, notDue, middleChain, .refl _⟩,
          ⟨blockRoot, blockRootOk, ?_⟩, ⟨stateRoot, stateRootOk, ?_⟩⟩
        · exact readCircular_writeCircular blockWrite
        · exact readCircular_writeCircular stateWrite
      · -- An earlier step cached it, and this step writes another entry.
        obtain ⟨fork', state', cached', caches, ⟨blockRoot', blockRootOk', blockRead⟩,
          ⟨stateRoot', stateRootOk', stateRead⟩⟩ :=
          more (by simp only; omega) (by simp only; omega)
        have other : state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
            slot % preset.SLOTS_PER_HISTORICAL_ROOT :=
          mod_ne_of_lt (by simp only at *; omega) (by simp only at *; omega)
        refine ⟨fork', state', cached', caches.extend (.slot notDue computed),
          ⟨blockRoot', blockRootOk', ?_⟩, ⟨stateRoot', stateRootOk', ?_⟩⟩
        · rw [readCircular_writeCircular_of_ne blockWrite other]
          exact blockRead
        · rw [readCircular_writeCircular_of_ne stateWrite other]
          exact stateRead
    | upgrade due computed =>
      obtain ⟨slotSame, _, blockRoots, stateRoots⟩ := upgradeNext_roots computed
      rw [slotSame] at written recent
      obtain ⟨fork', state', cached', caches, blockPart, statePart⟩ :=
        more written recent
      rw [blockRoots, stateRoots]
      exact ⟨fork', state', cached', caches.extend (.upgrade due computed), blockPart, statePart⟩
    | block engine signed validateResult notDue computed =>
      obtain ⟨-, -, -, -, slotSame, blockRoots, stateRoots, -⟩ := applySignedBlock_roots computed
      simp only at written recent ⊢
      rw [slotSame] at written recent
      obtain ⟨fork', state', cached', caches, blockPart, statePart⟩ :=
        more written recent
      rw [blockRoots, stateRoots]
      exact ⟨fork', state', cached',
        caches.extend (.block engine signed validateResult notDue computed),
        blockPart, statePart⟩

/-- An entry of the two buffers stays along a chain while it is still in the buffers.

The chain runs from a state past the entry's slot to a state at most `N` slots after it. -/
theorem Reaches.roots_stable {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) {slot : Slot}
    (written : slot.toNat < start.state.slot.toNat)
    (recent : after.state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    readCircular after.state.blockRoots.elements slot =
        readCircular start.state.blockRoots.elements slot ∧
      readCircular after.state.stateRoots.elements slot =
        readCircular start.state.stateRoots.elements slot := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | @snoc middle last run step more =>
    have middleLe := Reaches.slot_le (config := config) (checks := checks) ⟨run⟩
    have lastLe := stepRelation_slot.step step
    obtain ⟨blockSame, stateSame⟩ := more (by omega)
    rw [← blockSame, ← stateSame]
    cases step with
    | @slot fork state next notDue computed =>
      obtain ⟨cached, cachedOk, nextSlot, -, blockRoots, stateRoots⟩ := advanceSlot_roots computed
      obtain ⟨_, _, _, _, _, stateWrite, blockWrite, _⟩ := processSlot_roots cachedOk
      simp only at middleLe recent nextSlot ⊢
      have other : state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
          slot % preset.SLOTS_PER_HISTORICAL_ROOT :=
        mod_ne_of_lt (by omega) (by omega)
      rw [blockRoots, stateRoots, readCircular_writeCircular_of_ne blockWrite other,
        readCircular_writeCircular_of_ne stateWrite other]
      exact ⟨rfl, rfl⟩
    | upgrade due computed =>
      obtain ⟨-, -, blockRoots, stateRoots⟩ := upgradeNext_roots computed
      rw [blockRoots, stateRoots]
      exact ⟨rfl, rfl⟩
    | block engine signed validateResult notDue computed =>
      obtain ⟨-, -, -, -, -, blockRoots, stateRoots, -⟩ := applySignedBlock_roots computed
      simp only
      rw [blockRoots, stateRoots]
      exact ⟨rfl, rfl⟩

/-! ## The latest header -/

/-- The header that a block writes: its fields, the root of its body, and a zero state root. -/
def BeaconBlock.header (block : BeaconBlock preset fork) (bodyRoot : Root) : BeaconBlockHeader :=
  { slot := block.slot, proposerIndex := block.proposerIndex, parentRoot := block.parentRoot,
    stateRoot := Vector.replicate 32 0, bodyRoot }

/-- The latest header of `after` is `header`, written at `base`, with its state root settled.

A chain runs from `base` to `after`.

The latest header of `after` is `header` with some state root `r`.

- Either `r` is the state root of `header`.
  It is then not zero, or the chain has not left the slot of `base`.
- Or `header` had a zero state root, and the first caching after `base` filled it.
  That caching started from a state `middle` at the slot of `base`.
  Then `r` is the root of `middle`, or `middle` has the zero root.

A zero root leaves the header unfilled, and a later caching fills it again.

So the zero root of `middle` is the one case in which `r` can be the root of a later state. -/
def HeaderSettled (config : Config) (checks : SignatureChecks)
    (base after : ForkedBeaconState preset) (header : BeaconBlockHeader) : Prop :=
  Reaches config checks base after ∧
    ∃ stateRoot, after.state.latestBlockHeader = { header with stateRoot } ∧
      ((stateRoot = header.stateRoot ∧
          (header.stateRoot ≠ Vector.replicate 32 0 ∨ after.state.slot = base.state.slot)) ∨
        (header.stateRoot = Vector.replicate 32 0 ∧
          ∃ middle root, Reaches config checks base middle ∧
            Reaches config checks middle after ∧ middle.state.slot = base.state.slot ∧
            hashTreeRoot middle.state = .ok root ∧
            (stateRoot = root ∨ root = Vector.replicate 32 0)))

/-- At its base, a header is settled. -/
theorem HeaderSettled.base {base : ForkedBeaconState preset} :
    HeaderSettled config checks base base base.state.latestBlockHeader :=
  ⟨.refl _, _, rfl, .inl ⟨rfl, .inr rfl⟩⟩

/-- A slot step keeps a header settled. -/
theorem HeaderSettled.slot {base : ForkedBeaconState preset} {fork : Fork}
    {state next : BeaconState preset fork} {header : BeaconBlockHeader}
    (settled : HeaderSettled config checks base ⟨fork, state⟩ header)
    (notDue : upgradeDue config ⟨fork, state⟩ = false)
    (computed : advanceSlot config checks state = .ok next) :
    HeaderSettled config checks base ⟨fork, next⟩ header := by
  obtain ⟨chain, stateRoot, current, settledRoot⟩ := settled
  obtain ⟨cached, cachedOk, nextSlot, nextHeader, -, -⟩ := advanceSlot_roots computed
  obtain ⟨root, -, rootOk, cachedHeader, -⟩ := processSlot_roots cachedOk
  have step : Step config checks ⟨fork, state⟩ ⟨fork, next⟩ := .slot notDue computed
  refine ⟨chain.step step, ?_⟩
  simp only at current nextSlot ⊢
  rw [nextHeader, cachedHeader, current]
  unfold fillStateRoot
  rcases settledRoot with ⟨rfl, nonzero | sameSlot⟩ | ⟨zero, middle, middleRoot, head, tail,
    middleSlot, middleRootOk, filled⟩
  · -- A filled header stays.
    simp only [nonzero, ↓reduceIte]
    exact ⟨header.stateRoot, rfl, .inl ⟨rfl, .inl nonzero⟩⟩
  · by_cases zero : header.stateRoot = Vector.replicate 32 0
    · -- The first caching after the base fills the header.
      simp only [zero, ↓reduceIte]
      exact ⟨root, rfl, .inr ⟨trivial, ⟨fork, state⟩, root, chain,
        Reaches.refl _ |>.step step,
        sameSlot, rootOk, .inl rfl⟩⟩
    · simp only [zero, ↓reduceIte]
      exact ⟨header.stateRoot, rfl, .inl ⟨rfl, .inl zero⟩⟩
  · by_cases unfilled : stateRoot = Vector.replicate 32 0
    · -- An unfilled header after the first caching means the zero root.
      subst unfilled
      simp only [↓reduceIte]
      refine ⟨root, rfl, .inr ⟨zero, middle, middleRoot, head, tail.step step, middleSlot,
        middleRootOk, .inr ?_⟩⟩
      rcases filled with same | zeroRoot
      · exact same.symm
      · exact zeroRoot
    · simp only [unfilled, ↓reduceIte]
      exact ⟨stateRoot, rfl, .inr ⟨zero, middle, middleRoot, head, tail.step step, middleSlot,
        middleRootOk, filled⟩⟩

/-- An upgrade keeps a header settled. -/
theorem HeaderSettled.upgrade {base pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    {header : BeaconBlockHeader} (settled : HeaderSettled config checks base pre header)
    (due : upgradeDue config pre = true) (computed : upgradeNext config checks pre = .ok post) :
    HeaderSettled config checks base post.val header := by
  obtain ⟨chain, stateRoot, current, settledRoot⟩ := settled
  obtain ⟨slotSame, headerSame, -, -⟩ := upgradeNext_roots computed
  have step : Step config checks pre post.val := .upgrade due computed
  refine ⟨chain.step step, stateRoot, headerSame.trans current, ?_⟩
  rw [slotSame]
  rcases settledRoot with first | ⟨zero, middle, root, head, tail, rest⟩
  · exact .inl first
  · exact .inr ⟨zero, middle, root, head, tail.step step, rest⟩

/-- Where the latest header of a chain's end comes from.

Either no block step wrote it, and it is the header of the start, settled.

Or the last block step wrote it: the header of that block, settled from the state after it. -/
theorem Reaches.latestBlockHeader {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) :
    HeaderSettled config checks start after start.state.latestBlockHeader ∨
      ∃ (fork : Fork) (engine : ExecutionEngine preset fork)
        (signed : SignedBeaconBlock preset fork)
        (validateResult : Bool) (state post : BeaconState preset fork) (bodyRoot : Root),
        Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
        applySignedBlock config checks engine state signed validateResult = .ok post ∧
        hashTreeRoot signed.message.body = .ok bodyRoot ∧
        HeaderSettled config checks ⟨fork, post⟩ after (signed.message.header bodyRoot) := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact .inl HeaderSettled.base
  | @snoc middle last run step more =>
    cases step with
    | slot notDue computed =>
      rcases more with settled | ⟨fork, engine, signed, validateResult, state, post, bodyRoot,
        head, blockNotDue, applied, bodyRootOk, settled⟩
      · exact .inl (settled.slot notDue computed)
      · exact .inr ⟨fork, engine, signed, validateResult, state, post, bodyRoot, head, blockNotDue,
          applied, bodyRootOk, settled.slot notDue computed⟩
    | upgrade due computed =>
      rcases more with settled | ⟨fork, engine, signed, validateResult, state, post, bodyRoot,
        head, blockNotDue, applied, bodyRootOk, settled⟩
      · exact .inl (settled.upgrade due computed)
      · exact .inr ⟨fork, engine, signed, validateResult, state, post, bodyRoot, head, blockNotDue,
          applied, bodyRootOk, settled.upgrade due computed⟩
    | block engine signed validateResult notDue computed =>
      -- The block writes its own header, so the header settles from the state after it.
      obtain ⟨-, -, -, ⟨bodyRoot, bodyRootOk, written⟩, -⟩ := applySignedBlock_roots computed
      refine .inr ⟨_, engine, signed, validateResult, _, _, bodyRoot, ⟨run⟩, notDue, computed,
        bodyRootOk, ?_⟩
      exact ⟨.refl _, _, written, .inl ⟨rfl, .inr rfl⟩⟩

/-- After a block, the chain stays at the state after the block until its next slot step.

No upgrade is due there, since none was due when the block ran.

No second block runs at that slot, since a block must come after the latest one. -/
theorem Reaches.eq_of_slot_after_block {fork : Fork} {post : BeaconState preset fork}
    {after : ForkedBeaconState preset} (chain : Reaches config checks ⟨fork, post⟩ after)
    (notDue : upgradeDue config ⟨fork, post⟩ = false)
    (headerSlot : post.latestBlockHeader.slot = post.slot)
    (sameSlot : after.state.slot = post.slot) : after = ⟨fork, post⟩ := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => rfl
  | @snoc middle last run step more =>
    have middleLe := Reaches.slot_le (config := config) (checks := checks) ⟨run⟩
    have lastLe := stepRelation_slot.step step
    simp only at middleLe lastLe sameSlot
    have middleSlot : middle.state.slot = post.slot := by
      apply UInt64.toNat_inj.mp
      rw [sameSlot] at lastLe
      omega
    have same := more middleSlot
    subst same
    cases step with
    | slot _ computed =>
      have := advanceSlot_slot computed
      simp only at sameSlot
      rw [sameSlot] at this
      omega
    | upgrade due _ =>
      rw [notDue] at due
      cases due
    | block _ _ _ _ computed =>
      obtain ⟨blockSlot, newer, -⟩ := applySignedBlock_roots computed
      rw [blockSlot, headerSlot] at newer
      exact absurd newer (UInt64.lt_irrefl _)

/-- The header of a block, with the state root that the block names. -/
def BeaconBlock.toHeader (block : BeaconBlock preset fork) (bodyRoot : Root) :
    BeaconBlockHeader :=
  { block.header bodyRoot with stateRoot := block.stateRoot }

/-- Where the latest header of a chain's end comes from, once a block step wrote it.

The header is that of the last block, with one of three state roots.

- Zero, while the chain is still at the state after the block.
- The root of the state after the block, which a validated block names as its state root.
- Any root, but then the state after the block has the zero root.

The last case is the zero-root alternative: it records a state whose SSZ root is zero. -/
theorem HeaderSettled.of_block {fork : Fork} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    {state post : BeaconState preset fork} {bodyRoot : Root} {after : ForkedBeaconState preset}
    (notDue : upgradeDue config ⟨fork, state⟩ = false)
    (applied : applySignedBlock config checks engine state signed validateResult = .ok post)
    (settled : HeaderSettled config checks ⟨fork, post⟩ after (signed.message.header bodyRoot)) :
    (after = ⟨fork, post⟩ ∧ post.latestBlockHeader = signed.message.header bodyRoot) ∨
      (∃ root, hashTreeRoot post = .ok root ∧
        after.state.latestBlockHeader = { signed.message.header bodyRoot with stateRoot := root } ∧
        (validateResult = true → root = signed.message.stateRoot)) ∨
      hashTreeRoot post = .ok (Vector.replicate 32 0) := by
  obtain ⟨blockSlot, -, -, ⟨_, _, written⟩, postSlot, -, -, validated⟩ :=
    applySignedBlock_roots applied
  have postNotDue : upgradeDue config ⟨fork, post⟩ = false := by
    rw [upgradeDue_of_slot postSlot]
    exact notDue
  have headerSlot : post.latestBlockHeader.slot = post.slot := by
    rw [written, postSlot]
    exact blockSlot
  obtain ⟨chain, stateRoot, current, first | ⟨_, middle, root, head, _, middleSlot, rootOk,
    filled⟩⟩ := settled
  · obtain ⟨same, nonzero | atSlot⟩ := first
    · exact absurd rfl nonzero
    · -- The chain has not left the block's slot, so it is still at the state after the block.
      have stays := chain.eq_of_slot_after_block postNotDue headerSlot atSlot
      subst stays
      exact .inl ⟨rfl, by rw [current, same]⟩
  · -- The first caching after the block started from the state after the block.
    have same := head.eq_of_slot_after_block postNotDue headerSlot middleSlot
    subst same
    rcases filled with rfl | zero
    · exact .inr (.inl ⟨stateRoot, rootOk, current, fun validate => by
        have := validated validate
        rw [this] at rootOk
        exact (Except.ok.inj rootOk).symm⟩)
    · exact .inr (.inr (zero ▸ rootOk))

end EthLib.Consensus
