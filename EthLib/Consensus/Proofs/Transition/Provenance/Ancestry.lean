module

public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Proofs.Transition.Provenance.Roots
public import EthLib.Serialization.Proofs.Ssz.Codec.RootUnfold
public import EthLib.Serialization.Proofs.Ssz.Codec.Summary
public import EthLib.Serialization.Proofs.Ssz.Typed.Root
public import Mathlib.Logic.Relation

/-!
# Proofs: parent roots, and the hash evidence that replaces collision-freedom

A block names its parent by the root of the latest header of the state it runs on.

Along one chain that header is the header of the previous block, or of the start.

Its state root was filled at the first slot after that block, with the root of the state then.

So the parent root of a block is the root of the previous block's header, with that state root.

This needs no assumption on SHA-256: it follows the computations of one chain.

One case needs care: the state after a block may have the zero root.

Then the header stays unfilled, and a later slot fills it with another state's root.

The statement keeps that case as an alternative, with the state that has the zero root.

Comparing roots across two chains does need an assumption, or evidence.

Two equal header roots give equal headers, or two different 64-byte inputs of SHA-256 with one
digest.

`HashCollisionFound` records such a pair, found by an executable search over the hash inputs.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-! ## Hash evidence -/

/-- The inputs of the SHA-256 calls that compute the SSZ root of a value. -/
def sszMessages {α : Type} [SszType α] (value : α) : List Bytes :=
  (valueTree (desc α) (toValue value)).toOption.toList.flatMap (·.messages)

/-- The search over a pool of SHA-256 inputs finds two different 64-byte inputs with one digest.

Such a pair is a collision of SHA-256's compression of two nodes. -/
def HashCollisionFound (pool : List Bytes) : Prop :=
  ∃ first second, findMessageCollision pool pool = some (first, second) ∧
    MessageCollision first second

/-- A collision found in a pool is found in any larger pool. -/
theorem HashCollisionFound.mono {pool larger : List Bytes} (subset : ∀ x ∈ pool, x ∈ larger)
    (found : HashCollisionFound pool) : HashCollisionFound larger := by
  obtain ⟨first, second, searched, collision⟩ := found
  obtain ⟨firstMember, secondMember, -⟩ := findMessageCollision_valid searched
  obtain ⟨a, b, again⟩ :=
    findMessageCollision_of_collision (subset _ firstMember) (subset _ secondMember) collision
  exact ⟨a, b, again, (findMessageCollision_valid again).2.2⟩

/-- A beacon block header has no variable-size count in its SSZ commitment. -/
theorem beaconBlockHeader_commitmentSized (header : BeaconBlockHeader) :
    CommitmentSized (desc BeaconBlockHeader) (toValue header) := by
  apply CommitmentSized.container
  intro pair member
  simp only [desc, toValue, SszFields.descs, SszFields.toValues,
    List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact .uint _ _
  · exact .uint _ _
  · exact .byteVector _ _
  · exact .byteVector _ _
  · exact .byteVector _ _

/-- Two headers with one root are equal, or the search over their hash inputs finds a
collision. -/
theorem beaconBlockHeader_root_binding {left right : BeaconBlockHeader} {root : Root}
    (leftRoot : hashTreeRoot left = .ok root) (rightRoot : hashTreeRoot right = .ok root) :
    left = right ∨ HashCollisionFound (sszMessages left ++ sszMessages right) := by
  rcases hashTreeRoot_binding (beaconBlockHeader_commitmentSized left)
      (beaconBlockHeader_commitmentSized right) leftRoot rightRoot with same |
    ⟨leftTree, rightTree, leftOk, rightOk, x, y, _, xMember, yMember, collision⟩
  · exact .inl same
  · refine .inr ?_
    have xIn : x ∈ sszMessages left ++ sszMessages right := by
      apply List.mem_append_left
      simp only [sszMessages, leftOk, Except.toOption, Option.toList_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact xMember
    have yIn : y ∈ sszMessages left ++ sszMessages right := by
      apply List.mem_append_right
      simp only [sszMessages, rightOk, Except.toOption, Option.toList_some, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      exact yMember
    obtain ⟨a, b, found⟩ := findMessageCollision_of_collision xIn yIn collision
    exact ⟨a, b, found, (findMessageCollision_valid found).2.2⟩

/-! ## The root of a block and of its header -/

/-- A block and its header have one root.

The header holds the root of the body where the block holds the body.

A container's root is built from the roots of its fields, so the two roots agree. -/
theorem hashTreeRoot_toHeader {block : BeaconBlock preset fork} {bodyRoot : Root}
    (bodyRootOk : hashTreeRoot block.body = .ok bodyRoot) :
    hashTreeRoot (block.toHeader bodyRoot) = hashTreeRoot block := by
  -- The body's root, as bytes.
  have bodyBytes : SszType.root block.body = .ok bodyRoot.toArray := by
    unfold SszType.hashTreeRoot at bodyRootOk
    simp only [bind, Except.bind] at bodyRootOk
    split at bodyRootOk
    · cases bodyRootOk
    · next bytes rootOk =>
      rw [rootOk]
      unfold toChunk at bodyRootOk
      split at bodyRootOk
      · cases bodyRootOk
        rfl
      · cases bodyRootOk
  -- A 32-byte root is its own root.
  have rootBytes : SszType.root bodyRoot = .ok bodyRoot.toArray :=
    hashTreeRoot_chunk (by simp [bytesPerChunk])
  unfold SszType.hashTreeRoot
  congr 1
  show (do summaryRoot (.container _) (← SszFields.roots _)) =
    (do summaryRoot (.container _) (← SszFields.roots _))
  simp only [SszFields.roots, bind, Except.bind, pure, Except.pure, rootBytes, bodyBytes,
    BeaconBlock.toHeader, BeaconBlock.header]
  -- The two containers differ only in the name of their last field.
  have names : ∀ roots, summaryRoot (.container ["slot", "proposer_index", "parent_root",
      "state_root", "body_root"]) roots = summaryRoot (.container ["slot", "proposer_index",
      "parent_root", "state_root", "body"]) roots :=
    fun _ => hashTreeRoot_container_names _ _ _ _
  simp only [names]

/-- A validated block of a chain has its own root as the root that its header takes.

So along a chain of validated blocks, parent roots are the roots of the blocks themselves. -/
theorem ChainBlock.root_of_validated {fork : Fork} {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {state post : BeaconState preset fork}
    {bodyRoot stateRoot root : Root}
    (applied : applySignedBlock config checks engine state signed true = .ok post)
    (bodyRootOk : hashTreeRoot signed.message.body = .ok bodyRoot)
    (stateRootOk : hashTreeRoot post = .ok stateRoot)
    (rootOk : hashTreeRoot { signed.message.header bodyRoot with stateRoot } = .ok root) :
    hashTreeRoot signed.message = .ok root := by
  have named := (applySignedBlock_ok applied).2.2 rfl
  rw [named] at stateRootOk
  cases stateRootOk
  rw [← hashTreeRoot_toHeader bodyRootOk]
  exact rootOk

/-! ## Parent roots along a chain -/

/-- The parent root of a block of a chain.

The block runs on `state`, which a chain from `start` reaches with no upgrade due.

Either no block step came before it in the chain.
Then its parent root is the root of the start's header, with its state root settled.

Or the last block step before it ran on `state'` and left `post'`.
Then its parent root is the root of that block's header, with the root of `post'` as state root.
Or `post'` has the zero root. -/
theorem Reaches.parentRoot {start : ForkedBeaconState preset} {fork : Fork}
    {engine : ExecutionEngine preset fork} {signed : SignedBeaconBlock preset fork}
    {validateResult : Bool} {state post : BeaconState preset fork}
    (chain : Reaches config checks start ⟨fork, state⟩)
    (applied : applySignedBlock config checks engine state signed validateResult = .ok post) :
    (HeaderSettled config checks start ⟨fork, state⟩ start.state.latestBlockHeader ∧
        hashTreeRoot state.latestBlockHeader = .ok signed.message.parentRoot) ∨
      ∃ (fork' : Fork) (engine' : ExecutionEngine preset fork')
        (signed' : SignedBeaconBlock preset fork') (validateResult' : Bool)
        (state' post' : BeaconState preset fork') (bodyRoot : Root),
        Reaches config checks start ⟨fork', state'⟩ ∧ upgradeDue config ⟨fork', state'⟩ = false ∧
        applySignedBlock config checks engine' state' signed' validateResult' = .ok post' ∧
        hashTreeRoot signed'.message.body = .ok bodyRoot ∧
        Reaches config checks ⟨fork', post'⟩ ⟨fork, state⟩ ∧
        ((∃ stateRoot, hashTreeRoot post' = .ok stateRoot ∧
            hashTreeRoot { signed'.message.header bodyRoot with stateRoot } =
              .ok signed.message.parentRoot ∧
            (validateResult' = true → stateRoot = signed'.message.stateRoot)) ∨
          hashTreeRoot post' = .ok (Vector.replicate 32 0)) := by
  obtain ⟨blockSlot, newer, parent, -⟩ := applySignedBlock_roots applied
  rcases chain.latestBlockHeader with settled | ⟨fork', engine', signed', validateResult',
    state', post', bodyRoot, head, notDue', applied', bodyRootOk, settled⟩
  · exact .inl ⟨settled, parent⟩
  · refine .inr ⟨fork', engine', signed', validateResult', state', post', bodyRoot, head, notDue',
      applied', bodyRootOk, settled.1, ?_⟩
    rcases settled.of_block notDue' applied' with ⟨same, header⟩ | ⟨root, rootOk, header,
      validated⟩ | zero
    · -- A block at the slot of the previous one is not newer than it.
      exfalso
      obtain ⟨headerSlot, -, -, -, postSlot, -⟩ := applySignedBlock_roots applied'
      cases same
      have : state.latestBlockHeader.slot = state.slot := by
        rw [header, postSlot]
        exact headerSlot
      rw [this, blockSlot] at newer
      exact UInt64.lt_irrefl _ newer
    · simp only at header
      rw [header] at parent
      exact .inl ⟨root, rootOk, parent, validated⟩
    · exact .inr zero

/-! ## Ancestry along a chain -/

/-- A state of a chain has the zero root.

The caching of a slot reads the zero root as an unfilled header, so the header can take the
root of a later state.

This records the cryptographic event instead of assuming it cannot happen. -/
def ZeroRootFound (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) : Prop :=
  ∃ middle, Reaches config checks start middle ∧ Reaches config checks middle after ∧
    hashTreeRoot middle.state = .ok (Vector.replicate 32 0)

theorem ZeroRootFound.extend {start middle after : ForkedBeaconState preset}
    (found : ZeroRootFound config checks start middle) (step : Step config checks middle after) :
    ZeroRootFound config checks start after :=
  have ⟨state, head, tail, zero⟩ := found
  ⟨state, head, tail.step step, zero⟩

/-- A block step of a chain links its parent root to its own root.

Its own root is that of its header, with the root of the state after it as state root.

That is the root the next caching stores, unless the state after it has the zero root. -/
def ChainBlock (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset)
    (parentRoot root : Root) : Prop :=
  ∃ (fork : Fork) (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
    (validateResult : Bool) (state post : BeaconState preset fork) (bodyRoot stateRoot : Root),
    Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
    applySignedBlock config checks engine state signed validateResult = .ok post ∧
    Reaches config checks ⟨fork, post⟩ after ∧
    hashTreeRoot signed.message.body = .ok bodyRoot ∧ hashTreeRoot post = .ok stateRoot ∧
    signed.message.parentRoot = parentRoot ∧
    hashTreeRoot { signed.message.header bodyRoot with stateRoot } = .ok root

theorem ChainBlock.extend {start middle after : ForkedBeaconState preset} {parentRoot root : Root}
    (block : ChainBlock config checks start middle parentRoot root)
    (step : Step config checks middle after) : ChainBlock config checks start after parentRoot root :=
  have ⟨fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot, head, notDue,
    applied, tail, rest⟩ := block
  ⟨fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot, head, notDue, applied,
    tail.step step, rest⟩

/-- One root is an ancestor of another along the parent links of the blocks of a chain. -/
def ChainAncestor (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) : Root → Root → Prop :=
  Relation.ReflTransGen (ChainBlock config checks start after)

theorem ChainAncestor.extend {start middle after : ForkedBeaconState preset} {first second : Root}
    (ancestor : ChainAncestor config checks start middle first second)
    (step : Step config checks middle after) :
    ChainAncestor config checks start after first second :=
  Relation.ReflTransGen.mono (fun _ _ (block : ChainBlock config checks start middle _ _) =>
    block.extend step) _ _ ancestor

/-- A block step of a chain at a given slot, as `ChainBlock`, with the block's slot exposed. -/
def ChainBlockAt (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) (parentRoot root : Root) (slot : Slot) : Prop :=
  ∃ (fork : Fork) (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
    (validateResult : Bool) (state post : BeaconState preset fork) (bodyRoot stateRoot : Root),
    Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
    applySignedBlock config checks engine state signed validateResult = .ok post ∧
    Reaches config checks ⟨fork, post⟩ after ∧
    hashTreeRoot signed.message.body = .ok bodyRoot ∧ hashTreeRoot post = .ok stateRoot ∧
    signed.message.parentRoot = parentRoot ∧
    hashTreeRoot { signed.message.header bodyRoot with stateRoot } = .ok root ∧
    signed.message.slot = slot

/-- A block step of a chain whose block is past a slot number.

With `bound = e * SLOTS_PER_EPOCH` this is the relation `R_e` of the epoch-boundary pairs of
[Gasper]: the child block is past the first slot of epoch `e`.

[Gasper]: https://arxiv.org/abs/2003.03052 -/
def ChainBlockAfter (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) (bound : Nat) (parentRoot root : Root) : Prop :=
  ∃ slot : Slot, ChainBlockAt config checks start after parentRoot root slot ∧ bound < slot.toNat

/-- One root is an ancestor of another along blocks of a chain that are all past a slot number.
-/
def PastAncestor (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) (bound : Nat) : Root → Root → Prop :=
  Relation.ReflTransGen (ChainBlockAfter config checks start after bound)

theorem ChainBlockAt.chainBlock {start after : ForkedBeaconState preset} {parentRoot root : Root}
    {slot : Slot} (block : ChainBlockAt config checks start after parentRoot root slot) :
    ChainBlock config checks start after parentRoot root :=
  have ⟨fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot, head, notDue,
    applied, tail, bodyOk, stateOk, parent, rootOk, _⟩ := block
  ⟨fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot, head, notDue, applied,
    tail, bodyOk, stateOk, parent, rootOk⟩

/-- Ancestry past a slot is ancestry. -/
theorem PastAncestor.chainAncestor {start after : ForkedBeaconState preset} {bound : Nat}
    {root root' : Root} (ancestor : PastAncestor config checks start after bound root root') :
    ChainAncestor config checks start after root root' :=
  Relation.ReflTransGen.mono (fun _ _ ⟨_, block, _⟩ => block.chainBlock) _ _ ancestor

/-- Ancestry past a slot is ancestry past any earlier slot. -/
theorem PastAncestor.mono {start after : ForkedBeaconState preset} {bound bound' : Nat}
    (le : bound' ≤ bound) {root root' : Root}
    (ancestor : PastAncestor config checks start after bound root root') :
    PastAncestor config checks start after bound' root root' :=
  Relation.ReflTransGen.mono (fun _ _ ⟨slot, block, past⟩ => ⟨slot, block, by omega⟩) _ _
    ancestor

/-- Ancestry past a slot, along a longer chain. -/
theorem PastAncestor.extendChain {start middle after : ForkedBeaconState preset} {bound : Nat}
    {root root' : Root} (ancestor : PastAncestor config checks start middle bound root root')
    (chain : Reaches config checks middle after) :
    PastAncestor config checks start after bound root root' :=
  Relation.ReflTransGen.mono (fun _ _ ⟨slot, ⟨fork, engine, signed, validateResult, state, post,
      bodyRoot, stateRoot, head, notDue, applied, tail, rest⟩, past⟩ =>
    ⟨slot, ⟨fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot, head, notDue,
      applied, tail.trans chain, rest⟩, past⟩) _ _ ancestor

/-- Ancestry past a slot, from an earlier start. -/
theorem PastAncestor.prefix {first start after : ForkedBeaconState preset} {bound : Nat}
    {root root' : Root} (head : Reaches config checks first start)
    (ancestor : PastAncestor config checks start after bound root root') :
    PastAncestor config checks first after bound root root' :=
  Relation.ReflTransGen.mono (fun _ _ ⟨slot, ⟨fork, engine, signed, validateResult, state, post,
      bodyRoot, stateRoot, chain, rest⟩, past⟩ =>
    ⟨slot, ⟨fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot,
      head.trans chain, rest⟩, past⟩) _ _ ancestor

/-- A filled header keeps its state root. -/
theorem fillStateRoot_of_ne {header : BeaconBlockHeader} {stateRoot : Root}
    (filled : header.stateRoot ≠ Vector.replicate 32 0) :
    fillStateRoot header stateRoot = header := by
  simp [fillStateRoot, filled]

/-- How the latest header of a chain's state relates to the header cached at its first step.

- No block ran since, and the cached header, whose state root is filled, stays.
- Or a block ran since, past the cached slot, its header is settled, and its parent descends
  from the cached root along blocks past that slot.
- Or a state of the chain has the zero root. -/
def HeaderSince (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset)
    (cached : BeaconBlockHeader) (root : Root) : Prop :=
  (after.state.latestBlockHeader = cached ∧ cached.stateRoot ≠ Vector.replicate 32 0) ∨
    (∃ (fork : Fork) (engine : ExecutionEngine preset fork)
      (signed : SignedBeaconBlock preset fork) (validateResult : Bool)
      (state post : BeaconState preset fork) (bodyRoot : Root),
      Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
      applySignedBlock config checks engine state signed validateResult = .ok post ∧
      hashTreeRoot signed.message.body = .ok bodyRoot ∧
      HeaderSettled config checks ⟨fork, post⟩ after (signed.message.header bodyRoot) ∧
      start.state.slot.toNat < signed.message.slot.toNat ∧
      PastAncestor config checks start after start.state.slot.toNat root
        signed.message.parentRoot) ∨
    ZeroRootFound config checks start after

/-- Along a chain, the block root that a later slot caches descends from the one cached first.

The chain starts at `state`, whose slot step caches `cached`.

It reaches `after`, whose caching would give `cachedLater`.

The root of `cachedLater`'s header descends from the root of `cached`'s header, along the
parent links of the blocks of the chain.

Each of those blocks is past the slot of `state`, since the chain moved on from it.

Or a state of the chain has the zero root. -/
theorem Reaches.cachedRoot_pastAncestor {fork : Fork} {state next cached : BeaconState preset fork}
    {after : ForkedBeaconState preset} (notDue : upgradeDue config ⟨fork, state⟩ = false)
    (computed : advanceSlot config checks state = .ok next)
    (chain : Reaches config checks ⟨fork, next⟩ after)
    (cachedOk : processSlot state = .ok cached)
    {cachedLater : BeaconState preset after.fork}
    (laterOk : processSlot after.state = .ok cachedLater) {root rootLater : Root}
    (rootOk : hashTreeRoot cached.latestBlockHeader = .ok root)
    (rootLaterOk : hashTreeRoot cachedLater.latestBlockHeader = .ok rootLater) :
    PastAncestor config checks ⟨fork, state⟩ after state.slot.toNat root rootLater ∨
      ZeroRootFound config checks ⟨fork, state⟩ after := by
  have stepSlot := advanceSlot_slot computed
  have first : Reaches config checks ⟨fork, state⟩ ⟨fork, next⟩ :=
    (Reaches.refl _).step (.slot notDue computed)
  -- After the first step, the header is the cached one, filled unless the state's root is zero.
  have start : HeaderSince config checks ⟨fork, state⟩ ⟨fork, next⟩ cached.latestBlockHeader
      root := by
    obtain ⟨cached', cachedOk', -, nextHeader, -, -⟩ := advanceSlot_roots computed
    cases cachedOk.symm.trans cachedOk'
    obtain ⟨stateRoot, -, stateRootOk, header, -⟩ := processSlot_roots cachedOk
    by_cases filled : cached.latestBlockHeader.stateRoot = Vector.replicate 32 0
    · -- An unfilled header after caching means the state had the zero root.
      refine .inr (.inr ⟨⟨fork, state⟩, .refl _, first, ?_⟩)
      rw [header] at filled
      unfold fillStateRoot at filled
      split at filled
      · simp only at filled
        rw [filled] at stateRootOk
        exact stateRootOk
      · contradiction
    · exact .inl ⟨nextHeader, filled⟩
  obtain ⟨run⟩ := chain
  -- The relation holds at every state of the run.
  have holds : ∀ {last : ForkedBeaconState preset}, Run config checks ⟨fork, next⟩ last →
      HeaderSince config checks ⟨fork, state⟩ last cached.latestBlockHeader root := by
    intro last run
    induction run with
    | nil => exact start
    | @snoc middle last run step more =>
      have middleChain : Reaches config checks ⟨fork, state⟩ middle := first.trans ⟨run⟩
      cases step with
      | @slot fork' state' next' notDue' computed' =>
        have theStep : Step config checks ⟨fork', state'⟩ ⟨fork', next'⟩ :=
          .slot notDue' computed'
        rcases more with ⟨same, filled⟩ | ⟨fork'', engine, signed, validateResult, state'', post,
          bodyRoot, head, notDue'', applied, bodyRootOk, settled, past, ancestor⟩ | zero
        · obtain ⟨cached', cachedOk', -, nextHeader, -, -⟩ := advanceSlot_roots computed'
          obtain ⟨_, -, -, header, -⟩ := processSlot_roots cachedOk'
          refine .inl ⟨?_, filled⟩
          simp only at same ⊢
          rw [nextHeader, header, same, fillStateRoot_of_ne filled]
        · exact .inr (.inl ⟨fork'', engine, signed, validateResult, state'', post, bodyRoot, head,
            notDue'', applied, bodyRootOk, settled.slot notDue' computed', past,
            ancestor.extendChain ((Reaches.refl _).step theStep)⟩)
        · exact .inr (.inr (zero.extend theStep))
      | @upgrade _ post due computed' =>
        have theStep : Step config checks middle post.val := .upgrade due computed'
        have header := (upgradeNext_roots computed').2.1
        rcases more with ⟨same, filled⟩ | ⟨fork'', engine, signed, validateResult, state'',
          post', bodyRoot, head, notDue'', applied, bodyRootOk, settled, past, ancestor⟩ | zero
        · exact .inl ⟨header.trans same, filled⟩
        · exact .inr (.inl ⟨fork'', engine, signed, validateResult, state'', post', bodyRoot, head,
            notDue'', applied, bodyRootOk, settled.upgrade due computed', past,
            ancestor.extendChain ((Reaches.refl _).step theStep)⟩)
        · exact .inr (.inr (zero.extend theStep))
      | @block fork' engine signed validateResult state' post notDue' computed' =>
        have theStep : Step config checks ⟨fork', state'⟩ ⟨fork', post⟩ :=
          .block engine signed validateResult notDue' computed'
        obtain ⟨blockSlot, newer, parent, ⟨bodyRoot, bodyRootOk, written⟩, -⟩ :=
          applySignedBlock_roots computed'
        -- The block's own header settles from the state after it.
        have settled : HeaderSettled config checks ⟨fork', post⟩ ⟨fork', post⟩
            (signed.message.header bodyRoot) :=
          ⟨.refl _, _, written, .inl ⟨rfl, .inr rfl⟩⟩
        -- The block is past the cached slot, since the chain moved on from it.
        have newSlot : state.slot.toNat < signed.message.slot.toNat := by
          have := Reaches.slot_le (config := config) (checks := checks)
            (start := ⟨fork, next⟩) (after := ⟨fork', state'⟩) ⟨run⟩
          simp only at this
          rw [blockSlot]
          omega
        rcases more with ⟨same, filled⟩ | ⟨fork'', engine', signed', validateResult', state'',
          post', bodyRoot', head, notDue'', applied, bodyRootOk', settled', past, ancestor⟩ | zero
        · -- The block's parent is the cached header.
          simp only at same
          rw [same, rootOk] at parent
          cases parent
          exact .inr (.inl ⟨fork', engine, signed, validateResult, state', post, bodyRoot,
            middleChain, notDue', computed', bodyRootOk, settled, newSlot, .refl⟩)
        · -- The block's parent is the previous block, whose parent descends from the root.
          have tail := settled'.1
          rcases settled'.of_block notDue'' applied with ⟨same, header⟩ | ⟨stateRoot,
            stateRootOk, header, -⟩ | zero
          · -- The chain is still at the state after the previous block: no block is newer.
            exfalso
            obtain ⟨previousSlot, -, -, -, previousPostSlot, -⟩ := applySignedBlock_roots applied
            cases same
            rw [header, blockSlot] at newer
            simp only [BeaconBlock.header] at newer
            rw [previousSlot, ← previousPostSlot] at newer
            exact UInt64.lt_irrefl _ newer
          · simp only at header
            rw [header] at parent
            have link : ChainBlockAfter config checks ⟨fork, state⟩ ⟨fork', post⟩ state.slot.toNat
                signed'.message.parentRoot signed.message.parentRoot :=
              ⟨_, ⟨fork'', engine', signed', validateResult', state'', post', bodyRoot', stateRoot,
                head, notDue'', applied, tail.step theStep, bodyRootOk', stateRootOk, rfl, parent,
                rfl⟩, past⟩
            exact .inr (.inl ⟨fork', engine, signed, validateResult, state', post, bodyRoot,
              middleChain, notDue', computed', bodyRootOk, settled, newSlot,
              (ancestor.extendChain ((Reaches.refl _).step theStep)).tail link⟩)
          · exact .inr (.inr ⟨_, head.step (.block engine' signed' validateResult' notDue'' applied),
              tail.step theStep, zero⟩)
        · exact .inr (.inr (zero.extend theStep))
  obtain ⟨stateRoot, -, stateRootOk, laterHeader, -⟩ := processSlot_roots laterOk
  rw [laterHeader] at rootLaterOk
  rcases holds run with ⟨same, filled⟩ | ⟨fork', engine, signed, validateResult, state', post,
    bodyRoot, head, notDue', applied, bodyRootOk, settled, past, ancestor⟩ | zero
  · -- No block ran: the cached header stays, and so does its root.
    rw [same, fillStateRoot_of_ne filled, rootOk] at rootLaterOk
    cases rootLaterOk
    exact .inl .refl
  · have tail := settled.1
    rcases settled.of_block notDue' applied with ⟨rfl, header⟩ | ⟨root', root'Ok, header, -⟩ | zero
    · -- The chain is at the state after the block, so the caching fills the block's header.
      rw [header] at rootLaterOk
      simp only [fillStateRoot, BeaconBlock.header, ↓reduceIte] at rootLaterOk
      exact .inl (ancestor.tail ⟨_, ⟨fork', engine, signed, validateResult, state', post, bodyRoot,
        stateRoot, head, notDue', applied, tail, bodyRootOk, stateRootOk, rfl, rootLaterOk, rfl⟩,
        past⟩)
    · by_cases unfilled : root' = Vector.replicate 32 0
      · subst unfilled
        exact .inr ⟨_, head.step (.block engine signed validateResult notDue' applied), tail,
          root'Ok⟩
      · rw [header, fillStateRoot_of_ne unfilled] at rootLaterOk
        exact .inl (ancestor.tail ⟨_, ⟨fork', engine, signed, validateResult, state', post,
          bodyRoot, root', head, notDue', applied, tail, bodyRootOk, root'Ok, rfl, rootLaterOk,
          rfl⟩, past⟩)
    · exact .inr ⟨_, head.step (.block engine signed validateResult notDue' applied), tail, zero⟩
  · exact .inr zero

/-- `Reaches.cachedRoot_pastAncestor`, as ancestry along any blocks of the chain. -/
theorem Reaches.cachedRoot_ancestor {fork : Fork} {state next cached : BeaconState preset fork}
    {after : ForkedBeaconState preset} (notDue : upgradeDue config ⟨fork, state⟩ = false)
    (computed : advanceSlot config checks state = .ok next)
    (chain : Reaches config checks ⟨fork, next⟩ after)
    (cachedOk : processSlot state = .ok cached)
    {cachedLater : BeaconState preset after.fork}
    (laterOk : processSlot after.state = .ok cachedLater) {root rootLater : Root}
    (rootOk : hashTreeRoot cached.latestBlockHeader = .ok root)
    (rootLaterOk : hashTreeRoot cachedLater.latestBlockHeader = .ok rootLater) :
    ChainAncestor config checks ⟨fork, state⟩ after root rootLater ∨
      ZeroRootFound config checks ⟨fork, state⟩ after :=
  (chain.cachedRoot_pastAncestor notDue computed cachedOk laterOk rootOk rootLaterOk).imp_left
    (·.chainAncestor)

/-- A block step of a chain from a later start is a block step of the chain from an earlier one.
-/
theorem ChainBlock.prefix {first start after : ForkedBeaconState preset} {parentRoot root : Root}
    (head : Reaches config checks first start)
    (block : ChainBlock config checks start after parentRoot root) :
    ChainBlock config checks first after parentRoot root :=
  have ⟨fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot, chain, rest⟩ :=
    block
  ⟨fork, engine, signed, validateResult, state, post, bodyRoot, stateRoot, head.trans chain, rest⟩

theorem ChainAncestor.prefix {first start after : ForkedBeaconState preset} {root root' : Root}
    (head : Reaches config checks first start)
    (ancestor : ChainAncestor config checks start after root root') :
    ChainAncestor config checks first after root root' :=
  Relation.ReflTransGen.mono (fun _ _ (block : ChainBlock config checks start after _ _) =>
    block.prefix head) _ _ ancestor

theorem ZeroRootFound.prefix {first start after : ForkedBeaconState preset}
    (head : Reaches config checks first start) (found : ZeroRootFound config checks start after) :
    ZeroRootFound config checks first after :=
  have ⟨middle, chain, tail, zero⟩ := found
  ⟨middle, head.trans chain, tail, zero⟩

/-- Ancestry along the blocks of a chain is ancestry along any larger set of parent links.

So the ancestry of one history lifts to the ancestry of the union of several histories. -/
theorem ChainAncestor.lift {start after : ForkedBeaconState preset}
    {links : Root → Root → Prop}
    (subset : ∀ parentRoot root, ChainBlock config checks start after parentRoot root →
      links parentRoot root) {root root' : Root}
    (ancestor : ChainAncestor config checks start after root root') :
    Relation.ReflTransGen links root root' :=
  Relation.ReflTransGen.mono subset _ _ ancestor

theorem ChainAncestor.extendChain {start middle after : ForkedBeaconState preset}
    {first second : Root} (ancestor : ChainAncestor config checks start middle first second)
    (chain : Reaches config checks middle after) :
    ChainAncestor config checks start after first second := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact ancestor
  | snoc _ step more => exact more.extend step

theorem ZeroRootFound.extendChain {start middle after : ForkedBeaconState preset}
    (found : ZeroRootFound config checks start middle) (chain : Reaches config checks middle after) :
    ZeroRootFound config checks start after :=
  have ⟨state, head, tail, zero⟩ := found
  ⟨state, head, tail.trans chain, zero⟩

/-- Two roots that a state of a chain holds for two slots: the earlier descends to the later.

Both slots are from the start of the chain on, before the end, and still in the buffer.

The root of the earlier slot is an ancestor of the root of the later slot, along the parent
links of the blocks from the caching of the earlier slot on.

Each of those blocks is past the earlier slot.

Or a state of the chain has the zero root. -/
theorem Reaches.blockRoots_pastAncestor {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) {earlier later : Slot} {root root' : Root}
    (fromStart : start.state.slot.toNat ≤ earlier.toNat) (ordered : earlier.toNat < later.toNat)
    (written : later.toNat < after.state.slot.toNat)
    (recent : after.state.slot.toNat ≤ earlier.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (read : readCircular after.state.blockRoots.elements earlier = .ok root)
    (read' : readCircular after.state.blockRoots.elements later = .ok root') :
    ∃ (fork : Fork) (state cached : BeaconState preset fork),
      CachesSlot config checks start after earlier state cached ∧
      (PastAncestor config checks ⟨fork, state⟩ after earlier.toNat root root' ∨
        ZeroRootFound config checks ⟨fork, state⟩ after) := by
  -- The later slot was cached by one slot step of the chain.
  obtain ⟨fork', state', cached', ⟨atLater, cachedOk', next', nextOk', notDue', head', tail'⟩,
    ⟨laterRoot, laterRootOk, laterRead⟩, -⟩ :=
    chain.roots_written (by omega) written (by omega)
  rw [read'] at laterRead
  cases laterRead
  -- The earlier slot was cached before it, and its entry has not changed since.
  obtain ⟨fork, state, cached, ⟨atEarlier, cachedOk, next, nextOk, notDue, head, tail⟩,
    ⟨earlierRoot, earlierRootOk, earlierRead⟩, -⟩ :=
    head'.roots_written fromStart (by simp only; rw [atLater]; exact ordered)
      (by simp only; rw [atLater]; omega)
  have later' : Reaches config checks ⟨fork', state'⟩ after :=
    ((Reaches.refl _).step (.slot notDue' nextOk')).trans tail'
  have stable := (later'.roots_stable (slot := earlier) (by simp only; rw [atLater]; exact ordered)
    recent).1
  rw [read, earlierRead] at stable
  cases stable
  refine ⟨fork, state, cached, ⟨atEarlier, cachedOk, next, nextOk, notDue, head,
    tail.trans later'⟩, ?_⟩
  rcases tail.cachedRoot_pastAncestor notDue nextOk cachedOk cachedOk' earlierRootOk laterRootOk
    with ancestor | zero
  · rw [atEarlier] at ancestor
    exact .inl (ancestor.extendChain later')
  · exact .inr (zero.extendChain later')

/-- `Reaches.blockRoots_pastAncestor`, as ancestry along any blocks of the chain. -/
theorem Reaches.blockRoots_ancestor {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) {earlier later : Slot} {root root' : Root}
    (fromStart : start.state.slot.toNat ≤ earlier.toNat) (ordered : earlier.toNat < later.toNat)
    (written : later.toNat < after.state.slot.toNat)
    (recent : after.state.slot.toNat ≤ earlier.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (read : readCircular after.state.blockRoots.elements earlier = .ok root)
    (read' : readCircular after.state.blockRoots.elements later = .ok root') :
    ∃ (fork : Fork) (state cached : BeaconState preset fork),
      CachesSlot config checks start after earlier state cached ∧
      (ChainAncestor config checks ⟨fork, state⟩ after root root' ∨
        ZeroRootFound config checks ⟨fork, state⟩ after) :=
  have ⟨fork, state, cached, caches, found⟩ :=
    chain.blockRoots_pastAncestor fromStart ordered written recent read read'
  ⟨fork, state, cached, caches, found.imp_left (·.chainAncestor)⟩

/-- Two roots read at two states of one chain, for slots in order: the earlier is an ancestor.

The chain runs from `start` to `middle`, where one root is read, then on to `after`, where the
other is read.

Each read is of an entry still in the buffer, and the first slot is from the start on.

The first root is an ancestor of the second along the parent links of the chain's blocks.

Each of those blocks is past the first slot.

Or a state of the chain has the zero root. -/
theorem Reaches.reads_pastAncestor {start middle after : ForkedBeaconState preset}
    (head : Reaches config checks start middle) (tail : Reaches config checks middle after)
    {slot slot' : Slot} {root root' : Root}
    (fromStart : start.state.slot.toNat ≤ slot.toNat) (ordered : slot.toNat ≤ slot'.toNat)
    (read : readCircular middle.state.blockRoots.elements slot = .ok root)
    (inside : slot.toNat < middle.state.slot.toNat)
    (recent : middle.state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (read' : readCircular after.state.blockRoots.elements slot' = .ok root')
    (inside' : slot'.toNat < after.state.slot.toNat)
    (recent' : after.state.slot.toNat ≤ slot'.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    PastAncestor config checks start after slot.toNat root root' ∨
      ZeroRootFound config checks start after := by
  by_cases later : middle.state.slot.toNat ≤ slot'.toNat
  · -- The second slot was cached after the first read, by a step of the second part.
    obtain ⟨fork, state, cached, ⟨atSlot, cachedOk, next, nextOk, notDue, headOne, tailOne⟩,
      ⟨root1, root1Ok, read1⟩, -⟩ := head.roots_written fromStart inside recent
    rw [read] at read1
    cases read1
    obtain ⟨fork', state', cached', ⟨_, cachedOk', next', nextOk', notDue', headTwo, tailTwo⟩,
      ⟨root2, root2Ok, read2⟩, -⟩ := tail.roots_written later inside' recent'
    rw [read'] at read2
    cases read2
    have toLater : Reaches config checks ⟨fork', state'⟩ after :=
      ((Reaches.refl _).step (.slot notDue' nextOk')).trans tailTwo
    rcases (tailOne.trans headTwo).cachedRoot_pastAncestor notDue nextOk cachedOk cachedOk' root1Ok
      root2Ok with ancestor | zero
    · rw [atSlot] at ancestor
      exact .inl ((ancestor.prefix headOne).extendChain toLater)
    · exact .inr ((zero.prefix headOne).extendChain toLater)
  · -- Both slots were cached before the first read, and the second entry stayed.
    have stable := (tail.roots_stable (slot := slot') (by omega) recent').1
    rw [read'] at stable
    rcases Nat.lt_or_ge slot.toNat slot'.toNat with before | same
    · rcases head.blockRoots_pastAncestor fromStart before (by omega) recent read stable.symm with
        ⟨fork, state, cached, ⟨_, _, _, _, _, headOne, _⟩, ancestor | zero⟩
      · exact .inl ((ancestor.prefix headOne).extendChain tail)
      · exact .inr ((zero.prefix headOne).extendChain tail)
    · have sameSlot : slot = slot' := UInt64.toNat_inj.mp (by omega)
      subst sameSlot
      rw [read] at stable
      cases stable
      exact .inl .refl

/-- `Reaches.reads_pastAncestor`, as ancestry along any blocks of the chain. -/
theorem Reaches.reads_ancestor {start middle after : ForkedBeaconState preset}
    (head : Reaches config checks start middle) (tail : Reaches config checks middle after)
    {slot slot' : Slot} {root root' : Root}
    (fromStart : start.state.slot.toNat ≤ slot.toNat) (ordered : slot.toNat ≤ slot'.toNat)
    (read : readCircular middle.state.blockRoots.elements slot = .ok root)
    (inside : slot.toNat < middle.state.slot.toNat)
    (recent : middle.state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (read' : readCircular after.state.blockRoots.elements slot' = .ok root')
    (inside' : slot'.toNat < after.state.slot.toNat)
    (recent' : after.state.slot.toNat ≤ slot'.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ChainAncestor config checks start after root root' ∨
      ZeroRootFound config checks start after :=
  (head.reads_pastAncestor tail fromStart ordered read inside recent read' inside' recent').imp_left
    (·.chainAncestor)

end EthLib.Consensus
