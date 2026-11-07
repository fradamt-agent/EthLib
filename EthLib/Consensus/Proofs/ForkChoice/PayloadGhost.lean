module

public import EthLib.Consensus.Proofs.ForkChoice.Ghost
public import EthLib.Consensus.Proofs.ForkChoice.PayloadVotes
public import EthLib.Consensus.Proofs.Models.ForkChoice.PayloadTree

/-!
# Proofs: from Gloas, the head of the fork choice is LMD-GHOST over payload-status nodes

From Gloas the head rule of the store is the rule of the LMD-GHOST model over nodes.

A node of the model is a block with its payload pending, empty or full, as EIP-7732 says.

The tree of nodes stands over the tree of the known blocks of the store.

A pending node hangs under the empty or the full node of its parent, as its bid builds on it.

A vote supports the node that the store gives it.

That is the pending node in the slot of its block, and later the empty or the full node.

The empty and the full node of a block of the previous slot are payload decisions.

There the payload committee and the proposer decide: such a node weighs nothing, and the tie
between the two goes to a tiebreak of their own.

The plain model holds away from these decisions.

The walk of the model by an order with overrides covers them: it gives each decision its weight
and its tiebreak, and keeps the order of every other node.

The proposer boost counts as one more vote, for the pending node of the boosted block, when the
store applies the boost.

A tie between two children goes to the greater root, then to the greater status number.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models.ForkChoice BlockTree

/-- The status of a payload in the model: none while pending, then whether the payload is present.
-/
def PayloadStatus.toStatus : PayloadStatus → Status
  | .empty => some false
  | .full => some true
  | .pending => none

/-- The node of the model for a node of the store: its root as a known root, and its status. -/
def ForkChoiceNode.toModel (node : ForkChoiceNode) : Option Root × Status :=
  (some node.root, node.payloadStatus.toStatus)

theorem PayloadStatus.toStatus_injective : Function.Injective PayloadStatus.toStatus := by
  intro a b same
  cases a <;> cases b <;> simp_all [toStatus]

/-- The tiebreaker of a status is the number of its status in the model. -/
theorem PayloadStatus.code_toNat (status : PayloadStatus) :
    status.code.toNat = status.toStatus.code := by
  cases status <;> rfl

/-- An empty or full status is present exactly when it is full. -/
theorem PayloadStatus.toStatus_of_ne_pending {status : PayloadStatus}
    (notPending : status ≠ .pending) : status.toStatus = some (status == .full) := by
  cases status <;> simp_all [toStatus]

theorem ForkChoiceNode.toModel_injective : Function.Injective ForkChoiceNode.toModel := by
  rintro ⟨r, s⟩ ⟨r', s'⟩ same
  simp only [toModel, Prod.mk.injEq, Option.some.injEq] at same
  rw [same.1, PayloadStatus.toStatus_injective same.2]

/-- Every node of a known root in the model is the node of a node of the store. -/
theorem ForkChoiceNode.exists_toModel (root : Root) (status : Status) :
    ∃ node : ForkChoiceNode, node.toModel = (some root, status) := by
  rcases status with _ | _ | _
  · exact ⟨⟨root, .pending⟩, rfl⟩
  · exact ⟨⟨root, .empty⟩, rfl⟩
  · exact ⟨⟨root, .full⟩, rfl⟩

variable {preset : Preset} {fork : Fork}

namespace Store

variable (store : Store preset fork)

/-- Whether a root of the tree of the store builds on the full node of its parent.

A known block with a known parent builds as its bid says.

Any other root hangs under the full node of its parent.

So when every known block builds on a full parent, every root does. -/
def buildsOnFull : Option Root → Bool
  | some root =>
    match store.blocks[root]? with
    | some block =>
      match store.blocks[block.parentRoot]? with
      | some parent => parentPayloadStatus block parent == .full
      | none => true
    | none => true
  | none => true

variable {store} {lower : store.ParentsBelow}

variable (lower) in
/-- The tree of payload-status nodes over the tree of the store. -/
def nodeTree : BlockTree (Option Root × Status) :=
  (blockTree lower).payloadTree store.buildsOnFull

/-- The node of a block of the store hangs under the node of its parent that it builds on. -/
theorem nodeTree_parent_of {root : Root} {block parent : BeaconBlock preset fork}
    (found : store.blocks[root]? = some block)
    (parentFound : store.blocks[block.parentRoot]? = some parent) :
    (nodeTree lower).parent (some root, none) =
      (some block.parentRoot, some (parentPayloadStatus block parent == .full)) := by
  rw [nodeTree, payloadTree_parent_none (Option.some_ne_none _), blockTree_parent_of found]
  simp [buildsOnFull, found, parentFound]

/-- From Gloas each child of a node in the store is its child in the tree of nodes. -/
theorem isChild_of_mem_getNodeChildren (gloas : .glamsterdam ≤ fork) {node child : ForkChoiceNode}
    {children : List ForkChoiceNode} (childrenOk : store.getNodeChildren node = .ok children)
    (mem : child ∈ children) : (nodeTree lower).IsChild child.toModel node.toModel := by
  by_cases pending : node.payloadStatus = .pending
  · rw [getNodeChildren_of_pending gloas pending, Except.ok.injEq] at childrenOk
    subst childrenOk
    have same : node.toModel = (some node.root, none) := by
      simp [ForkChoiceNode.toModel, pending, PayloadStatus.toStatus]
    rw [same]
    simp only [List.mem_cons] at mem
    rcases mem with rfl | mem
    · exact payloadTree_isChild_some.mpr rfl
    · split at mem
      · rw [List.mem_singleton.mp mem]
        exact payloadTree_isChild_some.mpr rfl
      · cases mem
  · obtain ⟨childPending, block, parent, found, parentRoot, parentFound, built⟩ :=
      (mem_getNodeChildren_of_gloas gloas pending childrenOk).mp mem
    have toModel : child.toModel = (some child.root, none) := by
      simp [ForkChoiceNode.toModel, childPending, PayloadStatus.toStatus]
    rw [toModel]
    refine ⟨fun same => Option.some_ne_none _ (Prod.mk.inj same).1, ?_⟩
    rw [nodeTree_parent_of found (parentRoot ▸ parentFound), parentRoot, built,
      ← PayloadStatus.toStatus_of_ne_pending pending]
    rfl

/-! ## Ancestors -/

/-- From Gloas the ancestor walk climbs the tree of nodes.

It returns the node itself, or an empty or full node. -/
theorem getAncestor_nodeTree (gloas : .glamsterdam ≤ fork) {node ancestor : ForkChoiceNode}
    {slot : Slot} (walk : store.getAncestor node slot = .ok ancestor) :
    (nodeTree lower).Ancestor ancestor.toModel node.toModel ∧
      (ancestor = node ∨ ancestor.payloadStatus ≠ .pending) := by
  obtain ⟨-, origin, -⟩ := getAncestor_climbs (lower := lower) walk
  rcases origin with rfl | ⟨child, block, parent, found, parentFound, parentRoot, status, below⟩
  · exact ⟨.refl _, .inl rfl⟩
  have notPending : ancestor.payloadStatus ≠ .pending :=
    status ▸ parentPayloadStatus_ne_pending gloas
  refine ⟨?_, .inr notPending⟩
  -- The pending node of the child block is below the start, and the ancestor is its parent.
  have climb : (nodeTree lower).Ancestor (some child, none) node.toModel :=
    payloadTree_ancestor_none_of below
  refine Ancestor.trans ⟨1, ?_⟩ climb
  rw [Function.iterate_one, nodeTree_parent_of found parentFound, parentRoot, ← status,
    ← PayloadStatus.toStatus_of_ne_pending notPending]
  rfl

/-- The height of a node: twice the height of its block, plus one unless it is pending. -/
theorem nodeTree_height (node : ForkChoiceNode) :
    (nodeTree lower).height node.toModel =
      2 * (blockTree lower).height (some node.root) +
        if node.payloadStatus = .pending then 0 else 1 := by
  obtain ⟨root, _ | _ | _⟩ := node <;> rfl

/-- From Gloas a node descends from a known node exactly as in the tree of nodes. -/
theorem isAncestor_iff_of_gloas {start node : ForkChoiceNode} {block : BeaconBlock preset fork}
    {result : Bool} (gloas : .glamsterdam ≤ fork) (found : store.blocks[node.root]? = some block)
    (computed : store.isAncestor start node = .ok result) :
    result = true ↔ (nodeTree lower).Ancestor node.toModel start.toModel := by
  have known : store.block node.root = .ok block := block_ok_iff.mpr found
  simp only [isAncestor, known, gloas, ↓reduceIte, bind, Except.bind] at computed
  cases walk : store.getAncestor start block.slot with
  | error e => simp [walk] at computed
  | ok ancestor =>
  simp only [walk, pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  obtain ⟨tree, origin⟩ := getAncestor_nodeTree (lower := lower) gloas walk
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨sameRoot, same | pending⟩
    · have : ancestor = node := by
        cases ancestor
        cases node
        simp_all
      exact this ▸ tree
    · -- The pending node of a block is an ancestor of its other nodes.
      have pendingNode : node.toModel = (some ancestor.root, none) := by
        simp [ForkChoiceNode.toModel, sameRoot, pending, PayloadStatus.toStatus]
      rw [pendingNode]
      exact (payloadTree_ancestor_none_of (Ancestor.refl _)).trans tree
  · intro above
    have sameRoot :=
      getAncestor_root_eq found walk (payloadTree_ancestor_fst above)
    refine ⟨sameRoot, ?_⟩
    by_cases pending : node.payloadStatus = .pending
    · exact .inr pending
    refine .inl ?_
    -- Both nodes of the block sit one level above its pending node.
    have heights := nodeTree_height (lower := lower) node
    have ancestorHeights := nodeTree_height (lower := lower) ancestor
    rw [sameRoot] at ancestorHeights
    simp only [pending, ↓reduceIte] at heights
    by_cases ancestorPending : ancestor.payloadStatus = .pending
    · have startIs : ancestor = start := origin.resolve_right (· ancestorPending)
      subst startIs
      simp only [ancestorPending, ↓reduceIte] at ancestorHeights
      have := above.height_le
      omega
    · simp only [ancestorPending, ↓reduceIte] at ancestorHeights
      have same : ancestor.toModel = node.toModel := by
        rcases above.total tree with low | high
        · by_contra ne
          have := low.height_lt (Ne.symm ne)
          omega
        · by_contra ne
          have := high.height_lt ne
          omega
      rw [ForkChoiceNode.toModel_injective same]

/-! ## Votes and weights -/

variable (store) in
/-- The latest vote of a validator, by its index, as the node of the model that it supports.

An equivocator has none. -/
def latestNode (index : ValidatorIndex) : Option (Option Root × Status) :=
  if store.equivocatingIndices.contains index then none
  else store.latestMessages[index]?.bind fun message =>
    (store.getSupportedNode message).toOption.map (·.toModel)

variable (lower) in
/-- The view of the given nodes, their ancestors and the latest votes of the store, as nodes. -/
noncomputable def nodeView (nodes : List ForkChoiceNode) :
    View ℕ (Option Root × Status) (nodeTree lower) :=
  View.ofBlocks (nodes.map (·.toModel)).toFinset (store.latestNode ·.toUInt64)

/-- From Gloas, the votes for a known node are its weight in the model of nodes.

The voters are those that count in the given state, with their effective balances. -/
theorem getAttestationScore_eq_weight_of_gloas {node : ForkChoiceNode}
    {block : BeaconBlock preset fork} {state : BeaconState preset fork} {score : Gwei}
    (gloas : .glamsterdam ≤ fork) (found : store.blocks[node.root]? = some block)
    (nodes : List ForkChoiceNode) (computed : store.getAttestationScore node state = .ok score) :
    score.toNat = weight (voters state) (balanceAt state) (nodeView lower nodes) node.toModel := by
  refine getAttestationScore_eq_weight_of_reads (vote := store.latestNode) _ (fun _ => rfl)
    ⟨fun index none => ?_, fun index equivocating => ?_,
      fun index message supported result message' honest supportedOk computed' => ?_⟩ computed
  · simp [latestNode, none]
  · simp only [latestNode, equivocating, ↓reduceIte]
  · rw [isAncestor_iff_of_gloas (lower := lower) gloas found computed']
    simp only [latestNode, honest, Bool.false_eq_true, ↓reduceIte, message']
    simp [supportedOk, Except.toOption]

variable {config : Config} {state : BeaconState preset fork}

/-- From Gloas, a known node weighs its weight in the model of nodes.

The node must not be a payload decision of the previous slot, and the boost must not apply. -/
theorem getWeight_eq_weight_of_gloas {node : ForkChoiceNode} {block : BeaconBlock preset fork}
    {weightValue : Gwei} (gloas : .glamsterdam ≤ fork)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (decision : store.isPreviousSlotPayloadDecision config node = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (found : store.blocks[node.root]? = some block) (nodes : List ForkChoiceNode)
    (computed : store.getWeight config node = .ok weightValue) :
    weightValue.toNat =
      weight (voters state) (balanceAt state) (nodeView lower nodes) node.toModel := by
  rw [getWeight_of_not_boost gloas decision noBoost, justifiedState] at computed
  exact getAttestationScore_eq_weight_of_gloas gloas found nodes computed

variable (store config) in
/-- From Gloas, the pending node of the boosted block, when the boost applies.

The boost applies when the store says so.

When that check fails, the model has no boost.

Then the weight of each node that is not a payload decision of the previous slot fails too. -/
def boostedNode (gloas : .glamsterdam ≤ fork) : Option (Option Root × Status) :=
  match store.shouldApplyProposerBoost config gloas with
  | .ok true => some (some store.proposerBoostRoot, none)
  | _ => none

variable (store config) in
/-- From Gloas, the score of the boost as a stake: the proposer score, from the justified state.

It is 0 when the boost does not apply.

It is also 0 when the proposer score fails.

Then the weight of each node in the chain of the boosted block fails, unless it is a payload
decision of the previous slot.

So the head fails when the walk weighs such a node, and else the score does not count. -/
def boostScoreOfGloas (gloas : .glamsterdam ≤ fork) : ℕ :=
  match store.shouldApplyProposerBoost config gloas, store.getProposerScore config with
  | .ok true, .ok score => score.toNat
  | _, _ => 0

/-- From Gloas, a known node weighs its weight in the model of nodes with the boost.

The node must not be a payload decision of the previous slot.

The boost is a vote for the pending node of the boosted block, with the score of the boost as its
stake. -/
theorem getWeight_eq_weight_withBoost_of_gloas {node : ForkChoiceNode}
    {block : BeaconBlock preset fork} {weightValue : Gwei} (gloas : .glamsterdam ≤ fork)
    (decision : store.isPreviousSlotPayloadDecision config node = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (found : store.blocks[node.root]? = some block) (nodes : List ForkChoiceNode)
    (computed : store.getWeight config node = .ok weightValue) :
    weightValue.toNat =
      weight (voters state).insertNone
        (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
        ((nodeView lower nodes).withBoost (store.boostedNode config gloas)) node.toModel := by
  rw [weight_withBoost]
  cases boost : store.shouldApplyProposerBoost config gloas with
  | error e =>
    cases votes : store.getAttestationScore node state <;>
      simp [getWeight, gloas, decision, justifiedState, votes, boost, bind, Except.bind] at computed
  | ok applies =>
  cases applies with
  | false =>
    rw [getWeight_eq_weight_of_gloas (lower := lower) gloas boost decision justifiedState found
      nodes computed]
    simp [boostedNode, boost]
  | true =>
  cases votes : store.getAttestationScore node state with
  | error e =>
    simp [getWeight, gloas, decision, justifiedState, votes, bind, Except.bind] at computed
  | ok votesValue =>
  rw [← getAttestationScore_eq_weight_of_gloas (lower := lower) gloas found nodes votes]
  cases check : store.isAncestor ⟨store.proposerBoostRoot, .pending⟩ node with
  | error e =>
    simp [getWeight, gloas, decision, justifiedState, votes, boost, check, bind, Except.bind]
      at computed
  | ok result =>
  -- The boost counts exactly when the pending node of the boosted block descends from the node.
  have counts : (∃ m, store.boostedNode config gloas = some m ∧
      (nodeTree lower).Ancestor node.toModel m) ↔ result = true := by
    rw [isAncestor_iff_of_gloas (lower := lower) gloas found check]
    simp [boostedNode, boost, ForkChoiceNode.toModel, PayloadStatus.toStatus]
  cases result with
  | false =>
    simp only [Bool.false_eq_true, iff_false] at counts
    simp [getWeight, gloas, decision, justifiedState, votes, boost, check, bind, Except.bind,
      pure, Except.pure, Except.mapError] at computed
    cases add : Uint64.addChecked votesValue 0 with
    | error e => simp [add] at computed
    | ok sum =>
      simp only [add, Except.ok.injEq] at computed
      subst computed
      rw [(Uint64.addChecked_ok_iff.mp add).2, ite_eq_right counts]
      rfl
  | true =>
    simp only [iff_true] at counts
    simp [getWeight, gloas, decision, justifiedState, votes, boost, check, bind, Except.bind,
      Except.mapError] at computed
    cases score : store.getProposerScore config with
    | error e => simp [score] at computed
    | ok scoreValue =>
    cases add : Uint64.addChecked votesValue scoreValue with
    | error e => simp [score, add] at computed
    | ok sum =>
      simp only [score, add, Except.ok.injEq] at computed
      subst computed
      rw [(Uint64.addChecked_ok_iff.mp add).2, ite_eq_left counts, boostScoreOfGloas, boost, score]

/-! ## The head -/

/-- From Gloas, the children of a viable node in the view and in the store.

The node is in the subtree of the pending node of the justified block.

A node is a child in the view exactly when it is a viable child in the store. -/
theorem mem_children_nodeView {nodes : List ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (tree : store.getFilteredNodeTree config = .ok nodes) {node : ForkChoiceNode}
    (below : (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) node.toModel)
    {children : List ForkChoiceNode} (childrenOk : store.getNodeChildren node = .ok children)
    {child : ForkChoiceNode} :
    child.toModel ∈ Models.ForkChoice.children (nodeView lower nodes) node.toModel ↔
      child ∈ children.filter (· ∈ nodes) := by
  have closed := filterNodeTree_closed (T := nodeTree lower) (·.toModel) tree
    fun _ _ _ ok _ mem => isChild_of_mem_getNodeChildren gloas ok mem
  simp only [Models.ForkChoice.mem_children, nodeView, View.mem_ofBlocks, List.mem_filter,
    decide_eq_true_eq, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨⟨_, ⟨m, mMem, rfl⟩, above⟩, isChild⟩
    obtain ⟨c, cMem, same⟩ := (closed m mMem).2 _ (below.trans isChild.ancestor) above
    rw [← ForkChoiceNode.toModel_injective same] at cMem
    -- The child is not the start of the viable nodes, which sits above its parent.
    obtain ⟨-, -, parent⟩ := filterNodeTree_mem tree child cMem
    rcases parent with start | ⟨p, -, pChildren, pChildrenOk, childIn⟩
    · rw [start] at isChild
      exact absurd below.height_le (Nat.not_le_of_lt isChild.height_lt)
    have pChild := isChild_of_mem_getNodeChildren (lower := lower) gloas pChildrenOk childIn
    obtain rfl : p = node := ForkChoiceNode.toModel_injective (pChild.2.symm.trans isChild.2)
    rw [childrenOk, Except.ok.injEq] at pChildrenOk
    exact ⟨pChildrenOk ▸ childIn, cMem⟩
  · rintro ⟨childMem, inNodes⟩
    exact ⟨⟨_, ⟨child, inNodes, rfl⟩, .refl _⟩,
      isChild_of_mem_getNodeChildren gloas childrenOk childMem⟩

/-- The order of nodes in a tie in the model: by root as bytes, then by status. -/
abbrev nodeOrder : Option Root × Status → Lex (ℕ × ℕ) :=
  nodeKey rootValue

/-- From Gloas, the order in which the store compares two weighed nodes: by weight, then by root
as bytes, then by tiebreaker. -/
abbrev weighedKey (y : WeightedNode) : Lex (ℕ × Lex (ℕ × ℕ)) :=
  toLex (y.2.1.toNat, toLex (rootValue (some y.1.root), y.2.2.toNat))

/-- From Gloas, the walk of the store ends where the walk of the model by a key ends.

The model has the blocks of the view.

Each viable node has as key the order in which the store weighs it.

Two viable children of one node with one key are the same node.

The walk starts from a node in the subtree of the pending node of the justified block. -/
private theorem getHeadFrom_eq_ghostBy_of_gloas_of_keys {ν : Type}
    {G : View ν (Option Root × Status) (nodeTree lower)} {nodes : List ForkChoiceNode}
    {key : Option Root × Status → Lex (ℕ × Lex (ℕ × ℕ))}
    (gloas : .glamsterdam ≤ fork) (tree : store.getFilteredNodeTree config = .ok nodes)
    (blocks : G.blocks = (nodeView lower nodes).blocks)
    (keyed : ∀ {node : ForkChoiceNode} {y : WeightedNode}, node ∈ nodes →
      store.weighNode config node = .ok y → weighedKey y = key node.toModel)
    (distinct : ∀ {parent : ForkChoiceNode} {children : List ForkChoiceNode},
      store.getNodeChildren parent = .ok children → ∀ a ∈ children, ∀ b ∈ children,
        key a.toModel = key b.toModel → a = b) :
    ∀ {start head : ForkChoiceNode},
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) start.toModel →
      store.getHeadFrom config nodes start = .ok head →
      ghostBy G key start.toModel = head.toModel := by
  -- The model has the children of the view.
  have sameChildren : ∀ b, Models.ForkChoice.children G b =
      Models.ForkChoice.children (nodeView lower nodes) b := by
    intro b
    unfold Models.ForkChoice.children
    rw [blocks]
  intro start
  induction start using getHeadFrom.induct store with
  | _ start ih =>
  intro head below walk
  rw [getHeadFrom] at walk
  cases found : store.heaviestChild config nodes start with
  | error e => simp [found, bind, Except.bind] at walk
  | ok result =>
  obtain ⟨children, weighted, childrenOk, weightedOk, choice⟩ := heaviestChild_eq found
  -- Every child of the view is the node of a node of the store.
  have isNode : ∀ c ∈ Models.ForkChoice.children G start.toModel,
      ∃ child : ForkChoiceNode, c = child.toModel := by
    intro c mem
    obtain ⟨-, isChild⟩ := Models.ForkChoice.mem_children.mp mem
    obtain ⟨r, s⟩ := c
    have known : r ≠ none := by
      rcases s with _ | x
      · exact fun none => isChild.1 (by rw [none]; rfl)
      · have := (Prod.mk.inj (payloadTree_isChild_some.mp isChild)).1
        rw [← this]
        exact Option.some_ne_none _
    obtain ⟨root, rfl⟩ := Option.ne_none_iff_exists'.mp known
    obtain ⟨child, same⟩ := ForkChoiceNode.exists_toModel root s
    exact ⟨child, same.symm⟩
  cases result with
  | none =>
    simp only [found, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at walk
    subst walk
    rw [chooseHeaviest_eq_none] at choice
    subst choice
    have empty := List.length_eq_zero_iff.mp (mapM_ok_length weightedOk).symm
    refine ghostBy_of_not_nonempty _ _ fun ⟨c, mem⟩ => ?_
    obtain ⟨child, rfl⟩ := isNode c mem
    have := (mem_children_nodeView gloas tree below childrenOk).mp (sameChildren _ ▸ mem)
    rw [empty] at this
    cases this
  | some child =>
    simp only [found, bind, Except.bind] at walk
    split at walk
    swap
    · cases walk
    obtain ⟨childKey, chosen, largest⟩ := chooseHeaviest_some choice
    obtain ⟨source, sourceMem, sourceOk⟩ := mapM_ok_mem weightedOk _ chosen
    obtain ⟨same, -, -⟩ := weighNode_ok_iff.mp sourceOk
    replace same : source = child := same.symm
    subst same
    have inView : source.toModel ∈ Models.ForkChoice.children G start.toModel := by
      rw [sameChildren]
      exact (mem_children_nodeView gloas tree below childrenOk).mpr sourceMem
    -- The chosen child is above every other child, by weight, then by root and status.
    have largestModel : ∀ c ∈ Models.ForkChoice.children G start.toModel,
        key c ≤ key source.toModel := by
      intro c mem
      obtain ⟨other, rfl⟩ := isNode c mem
      have otherMem := (mem_children_nodeView gloas tree below childrenOk).mp (sameChildren _ ▸ mem)
      obtain ⟨y, yMem, otherOk⟩ := exists_mem_of_mapM_ok weightedOk otherMem
      have le := toLex_le_of_compareWeighted_tiebreaker (largest _ yMem)
      have inNodes : ∀ {c}, c ∈ children.filter (· ∈ nodes) → c ∈ nodes :=
        fun cMem => of_decide_eq_true (List.mem_filter.mp cMem).2
      change weighedKey y ≤ weighedKey (source, childKey) at le
      rwa [keyed (inNodes otherMem) otherOk, keyed (inNodes sourceMem) sourceOk] at le
    have injective : Set.InjOn key (Models.ForkChoice.children G start.toModel) := by
      intro a aMem b bMem same
      obtain ⟨na, rfl⟩ := isNode a aMem
      obtain ⟨nb, rfl⟩ := isNode b bMem
      have naMem := (mem_children_nodeView gloas tree below childrenOk).mp (sameChildren _ ▸ aMem)
      have nbMem := (mem_children_nodeView gloas tree below childrenOk).mp (sameChildren _ ▸ bMem)
      rw [distinct childrenOk na (List.mem_filter.mp naMem).1 nb (List.mem_filter.mp nbMem).1
        same]
    have step : (nodeTree lower).parent source.toModel = start.toModel :=
      (isChild_of_mem_getNodeChildren gloas childrenOk (List.mem_filter.mp sourceMem).1).2
    rw [ghostBy_of_nonempty _ _ ⟨_, inView⟩, heaviestChildBy_eq inView largestModel injective]
    exact ih source ‹_› (below.trans ⟨1, step⟩) walk


/-- From Gloas, the walk of the store ends where LMD-GHOST over nodes ends, in a model of its
weights.

The model has the blocks of the view.

Each viable node weighs in the model what the store computes.

No viable node may be a payload decision of the previous slot.

The walk starts from a node in the subtree of the pending node of the justified block. -/
private theorem getHeadFrom_eq_ghost_of_gloas_of_weights {ν : Type} {V : Finset ν} {w : ν → ℕ}
    {G : View ν (Option Root × Status) (nodeTree lower)} {nodes : List ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (blocks : G.blocks = (nodeView lower nodes).blocks)
    (weighs : ∀ {node : ForkChoiceNode} {weightValue : Gwei}, node ∈ nodes →
      store.getWeight config node = .ok weightValue →
        weightValue.toNat = weight V w G node.toModel) :
    ∀ {start head : ForkChoiceNode},
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) start.toModel →
      store.getHeadFrom config nodes start = .ok head →
      ghost V w G nodeOrder start.toModel = head.toModel := by
  intro start head below walk
  rw [ghost_eq_ghostBy]
  refine getHeadFrom_eq_ghostBy_of_gloas_of_keys gloas tree blocks ?_ ?_ below walk
  · -- A viable node weighs its model weight, and breaks ties by its status number.
    intro c y inNodes yOk
    obtain ⟨yNode, yWeight, yTie⟩ := weighNode_ok_iff.mp yOk
    simp only [tiebreaker, gloas, ↓reduceDIte,
      getPayloadStatusTiebreaker_of_not_decision (noDecision c inNodes), Except.ok.injEq] at yTie
    rw [weighedKey, weighs inNodes yWeight, ← yTie, yNode, PayloadStatus.code_toNat]
    rfl
  · -- Root and status tell nodes apart.
    intro _ _ _ na _ nb _ same
    obtain ⟨-, codes⟩ := Prod.ext_iff.mp (toLex.injective same)
    obtain ⟨roots, codes⟩ := Prod.ext_iff.mp (toLex.injective codes)
    have rootsEq := rootValue_some_injective roots
    have statuses : na.payloadStatus = nb.payloadStatus := by
      have := codes
      simp only [ForkChoiceNode.toModel] at this
      rw [← PayloadStatus.code_toNat, ← PayloadStatus.code_toNat] at this
      cases h : na.payloadStatus <;> cases h' : nb.payloadStatus <;> simp_all [PayloadStatus.code]
    obtain ⟨_, _⟩ := na
    obtain ⟨_, _⟩ := nb
    simp_all

/-- From Gloas, the walk of the store ends where LMD-GHOST over nodes ends.

No viable node may be a payload decision of the previous slot, and the boost must not apply.

It starts from a node in the subtree of the pending node of the justified block. -/
theorem getHeadFrom_eq_ghost_of_gloas {nodes : List ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ∀ {start head : ForkChoiceNode},
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) start.toModel →
      store.getHeadFrom config nodes start = .ok head →
      ghost (voters state) (balanceAt state) (nodeView lower nodes) nodeOrder start.toModel =
        head.toModel :=
  getHeadFrom_eq_ghost_of_gloas_of_weights gloas noDecision tree rfl fun inNodes computed =>
    have ⟨_, ⟨_, found⟩, _⟩ := filterNodeTree_mem tree _ inNodes
    getWeight_eq_weight_of_gloas gloas noBoost (noDecision _ inNodes) justifiedState found nodes
      computed

/-- From Gloas, the walk of the store ends where LMD-GHOST over nodes with the boost ends.

No viable node may be a payload decision of the previous slot.

The boost is a vote for the pending node of the boosted block, with the score of the boost as its
stake.

It starts from a node in the subtree of the pending node of the justified block. -/
theorem getHeadFrom_eq_ghost_withBoost_of_gloas {nodes : List ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ∀ {start head : ForkChoiceNode},
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) start.toModel →
      store.getHeadFrom config nodes start = .ok head →
      ghost (voters state).insertNone
        (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
        ((nodeView lower nodes).withBoost (store.boostedNode config gloas)) nodeOrder
        start.toModel = head.toModel :=
  getHeadFrom_eq_ghost_of_gloas_of_weights
    (G := (nodeView lower nodes).withBoost (store.boostedNode config gloas)) gloas noDecision tree
    rfl fun inNodes computed =>
    have ⟨_, ⟨_, found⟩, _⟩ := filterNodeTree_mem tree _ inNodes
    getWeight_eq_weight_withBoost_of_gloas gloas (noDecision _ inNodes) justifiedState found nodes
      computed

variable (lower) in
/-- From Gloas, the head of the store is the head of LMD-GHOST over nodes.

No viable node may be a payload decision of the previous slot, and the boost must not apply.

Each known block must sit at a later slot than its known parent, and some node must be viable.

The model starts at the pending node of the justified block, over the view of the viable nodes.

Its voters are the validators active and not slashed in the justified state.

Its stakes are their effective balances, and an equivocator has no vote.

A tie goes to the greater root, as bytes, then to the greater status number. -/
theorem getHead_eq_ghost_of_gloas {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (found : store.getHead config = .ok head) :
    ghost (voters state) (balanceAt state) (nodeView lower nodes) nodeOrder
      (some store.justifiedCheckpoint.root, none) = head.toModel := by
  have notEmpty : ¬ (.glamsterdam ≤ fork ∧ nodes.isEmpty = true) :=
    fun ⟨_, empty⟩ => someViable (List.isEmpty_iff.mp empty)
  simp only [getHead, tree, notEmpty, ↓reduceIte, bind, Except.bind] at found
  exact getHeadFrom_eq_ghost_of_gloas gloas noBoost noDecision justifiedState tree (.refl _) found

variable (lower) in
/-- From Gloas, the head of the store is the head of LMD-GHOST over nodes with the boost.

No viable node may be a payload decision of the previous slot.

Each known block must sit at a later slot than its known parent, and some node must be viable.

The model starts at the pending node of the justified block, over the view of the viable nodes.

Its voters are the validators active and not slashed in the justified state.

Its stakes are their effective balances, and an equivocator has no vote.

The boost is one more vote, for the pending node of the boosted block, and its stake is the score
of the boost.

When the boost does not apply, that vote is absent.

A tie goes to the greater root, as bytes, then to the greater status number. -/
theorem getHead_eq_ghost_withBoost_of_gloas {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (found : store.getHead config = .ok head) :
    ghost (voters state).insertNone
      (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
      ((nodeView lower nodes).withBoost (store.boostedNode config gloas)) nodeOrder
      (some store.justifiedCheckpoint.root, none) = head.toModel := by
  have notEmpty : ¬ (.glamsterdam ≤ fork ∧ nodes.isEmpty = true) :=
    fun ⟨_, empty⟩ => someViable (List.isEmpty_iff.mp empty)
  simp only [getHead, tree, notEmpty, ↓reduceIte, bind, Except.bind] at found
  exact getHeadFrom_eq_ghost_withBoost_of_gloas gloas noDecision justifiedState tree (.refl _) found

/-! ## Payload decisions of the previous slot

The empty and the full node of a block of the previous slot weigh nothing in the store.

The tie between them goes to a tiebreak of their own, which the proposer and the payload committee
decide, and not to their status numbers.

The model keeps every other node, and overrides the weight and the tiebreak of these nodes. -/

/-- The status of a payload for a status of the model. -/
def _root_.EthLib.Consensus.PayloadStatus.ofStatus : Status → PayloadStatus
  | none => .pending
  | some false => .empty
  | some true => .full

/-- The node of the store for a node of the model.

The common root has no node, and gets the pending node of the zero root. -/
def _root_.EthLib.Consensus.ForkChoiceNode.ofModel : Option Root × Status → ForkChoiceNode
  | (some root, status) => ⟨root, PayloadStatus.ofStatus status⟩
  | (none, _) => ⟨Vector.replicate 32 0, .pending⟩

@[simp] theorem _root_.EthLib.Consensus.ForkChoiceNode.ofModel_toModel (node : ForkChoiceNode) :
    ForkChoiceNode.ofModel node.toModel = node := by
  obtain ⟨root, _ | _ | _⟩ := node <;> rfl

variable (store config) in
/-- From Gloas, the tiebreak of a payload decision of the previous slot.

The empty node gets 1.

The full node gets 2 when the proposer should build on its payload, and 0 otherwise. -/
def decisionTiebreak (gloas : .glamsterdam ≤ fork) (node : ForkChoiceNode) : ℕ :=
  if node.payloadStatus = .empty then 1
  else
    match store.shouldExtendPayload config gloas node.root with
    | .ok true => 2
    | _ => 0

variable (store config) in
/-- From Gloas, the override of the order for a node of the model.

A payload decision of the previous slot weighs 0 and takes its own tiebreak, after its root.

Every other node keeps its weight and its order by root and status. -/
def decisionOverride (gloas : .glamsterdam ≤ fork) (node : Option Root × Status) :
    Option (ℕ × Lex (ℕ × ℕ)) :=
  match store.isPreviousSlotPayloadDecision config (ForkChoiceNode.ofModel node) with
  | .ok true =>
    some (0, toLex (rootValue node.1, store.decisionTiebreak config gloas (.ofModel node)))
  | _ => none

variable (store config) in
/-- From Gloas, the order of the model with the payload decisions of the previous slot.

It is by weight, then by root, then by tiebreak, with the decisions overridden. -/
abbrev decisionKey (gloas : .glamsterdam ≤ fork) (weightOf : Option Root × Status → ℕ) :
    Option Root × Status → Lex (ℕ × Lex (ℕ × ℕ)) :=
  overrideKey weightOf nodeOrder (store.decisionOverride config gloas)

/-- The order with the decisions keeps the root of a node in second place. -/
theorem decisionKey_root (gloas : .glamsterdam ≤ fork) (weightOf : Option Root × Status → ℕ)
    (node : ForkChoiceNode) :
    (ofLex (ofLex (store.decisionKey config gloas weightOf node.toModel)).2).1 =
      rootValue (some node.root) := by
  unfold decisionKey overrideKey decisionOverride
  rw [ForkChoiceNode.ofModel_toModel]
  cases store.isPreviousSlotPayloadDecision config node with
  | error e => rfl
  | ok decided => cases decided <;> rfl

/-- The empty and the full node of a block are payload decisions together, or neither is. -/
theorem isPreviousSlotPayloadDecision_empty_full (root : Root) :
    store.isPreviousSlotPayloadDecision config ⟨root, .empty⟩ =
      store.isPreviousSlotPayloadDecision config ⟨root, .full⟩ := by
  simp [isPreviousSlotPayloadDecision]

/-- The empty and the full node of a block have different tiebreaks in the order with decisions.
-/
theorem decisionKey_empty_ne_full (gloas : .glamsterdam ≤ fork)
    (weightOf : Option Root × Status → ℕ) (root : Root) :
    (ofLex (ofLex (store.decisionKey config gloas weightOf (some root, some false))).2).2 ≠
      (ofLex (ofLex (store.decisionKey config gloas weightOf (some root, some true))).2).2 := by
  have same := isPreviousSlotPayloadDecision_empty_full (store := store) (config := config) root
  unfold decisionKey overrideKey decisionOverride
  simp only [ForkChoiceNode.ofModel, PayloadStatus.ofStatus] at same ⊢
  rw [← same]
  cases store.isPreviousSlotPayloadDecision config ⟨root, .empty⟩ with
  | error e => simp [nodeOrder, nodeKey, Status.code]
  | ok decided =>
    cases decided
    · simp [nodeOrder, nodeKey, Status.code]
    · simp only [decisionTiebreak, ofLex_toLex]
      simp only [↓reduceIte, reduceCtorEq]
      split <;> simp

/-- From Gloas, the walk of the store ends where the walk of the model with decisions ends.

The model has the blocks of the view, and each node that is not a decision weighs in it what the
store computes.

The decisions of the previous slot weigh 0, and take their own tiebreak.

The walk starts from a node in the subtree of the pending node of the justified block. -/
private theorem getHeadFrom_eq_ghostBy_decisionKey {ν : Type} {V : Finset ν} {w : ν → ℕ}
    {G : View ν (Option Root × Status) (nodeTree lower)} {nodes : List ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork) (tree : store.getFilteredNodeTree config = .ok nodes)
    (blocks : G.blocks = (nodeView lower nodes).blocks)
    (weighs : ∀ {node : ForkChoiceNode} {weightValue : Gwei}, node ∈ nodes →
      store.isPreviousSlotPayloadDecision config node = .ok false →
      store.getWeight config node = .ok weightValue →
        weightValue.toNat = weight V w G node.toModel) :
    ∀ {start head : ForkChoiceNode},
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) start.toModel →
      store.getHeadFrom config nodes start = .ok head →
      ghostBy G (store.decisionKey config gloas (weight V w G)) start.toModel = head.toModel := by
  intro start head below walk
  refine getHeadFrom_eq_ghostBy_of_gloas_of_keys gloas tree blocks ?_ ?_ below walk
  · intro c y inNodes yOk
    obtain ⟨yNode, yWeight, yTie⟩ := weighNode_ok_iff.mp yOk
    obtain ⟨node, weightValue, tie⟩ := y
    simp only at yNode yWeight yTie
    subst yNode
    simp only [tiebreaker, gloas, ↓reduceDIte] at yTie
    unfold decisionKey overrideKey decisionOverride
    rw [ForkChoiceNode.ofModel_toModel]
    cases decision : store.isPreviousSlotPayloadDecision config node with
    | error e => simp [getWeight, gloas, decision, bind, Except.bind] at yWeight
    | ok decided =>
    cases decided with
    | false =>
      rw [weighedKey, weighs inNodes decision yWeight]
      rw [getPayloadStatusTiebreaker_of_not_decision decision, Except.ok.injEq] at yTie
      simp only
      rw [← yTie, PayloadStatus.code_toNat]
      rfl
    | true =>
      rw [getWeight_of_payloadDecision gloas decision, Except.ok.injEq] at yWeight
      subst yWeight
      simp only [weighedKey]
      congr 2
      unfold getPayloadStatusTiebreaker at yTie
      simp only [decision, bind, Except.bind, ↓reduceIte] at yTie
      unfold decisionTiebreak
      by_cases empty : node.payloadStatus = .empty
      · simp [empty, pure, Except.pure] at yTie
        simp [empty, ← yTie, ForkChoiceNode.toModel]
      · simp only [empty, ↓reduceIte] at yTie ⊢
        cases extend : store.shouldExtendPayload config gloas node.root with
        | error e => simp [extend] at yTie
        | ok extend' =>
          cases extend' <;> simp [extend, pure, Except.pure] at yTie <;>
            simp [← yTie, ForkChoiceNode.toModel]
  · intro parent children childrenOk a aMem b bMem same
    by_cases pending : parent.payloadStatus = .pending
    · -- The children are the empty and the full node of the parent's block.
      rw [getNodeChildren_of_pending gloas pending, Except.ok.injEq] at childrenOk
      subst childrenOk
      have members : ∀ c ∈ (⟨parent.root, .empty⟩ :: if store.isPayloadVerified gloas parent.root
          then [⟨parent.root, .full⟩] else [] : List ForkChoiceNode),
          c = ⟨parent.root, .empty⟩ ∨ c = ⟨parent.root, .full⟩ := by
        intro c mem
        simp only [List.mem_cons] at mem
        rcases mem with rfl | mem
        · exact .inl rfl
        · split at mem
          · exact .inr (List.mem_singleton.mp mem)
          · cases mem
      have tie := congrArg (fun k => (ofLex (ofLex k).2).2) same
      have differ := decisionKey_empty_ne_full (store := store) (config := config) gloas
        (weight V w G) parent.root
      rcases members a aMem with rfl | rfl <;> rcases members b bMem with rfl | rfl
      · rfl
      · exact absurd tie differ
      · exact absurd tie.symm differ
      · rfl
    · -- The children are the pending nodes of blocks with distinct roots.
      obtain ⟨aPending, -⟩ := (mem_getNodeChildren_of_gloas gloas pending childrenOk).mp aMem
      obtain ⟨bPending, -⟩ := (mem_getNodeChildren_of_gloas gloas pending childrenOk).mp bMem
      have roots := congrArg (fun k => (ofLex (ofLex k).2).1) same
      simp only [decisionKey_root] at roots
      have rootsEq := rootValue_some_injective roots
      obtain ⟨_, _⟩ := a
      obtain ⟨_, _⟩ := b
      simp_all

/-- From Gloas, the walk of the store ends where LMD-GHOST over nodes with the boost and the
decisions of the previous slot ends.

The boost is a vote for the pending node of the boosted block, with the score of the boost as its
stake.

A payload decision of the previous slot weighs 0, and takes its own tiebreak.

It starts from a node in the subtree of the pending node of the justified block. -/
theorem getHeadFrom_eq_ghostBy_withBoost_of_gloas {nodes : List ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ∀ {start head : ForkChoiceNode},
      (nodeTree lower).Ancestor (some store.justifiedCheckpoint.root, none) start.toModel →
      store.getHeadFrom config nodes start = .ok head →
      ghostBy ((nodeView lower nodes).withBoost (store.boostedNode config gloas))
        (store.decisionKey config gloas (weight (voters state).insertNone
          (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
          ((nodeView lower nodes).withBoost (store.boostedNode config gloas))))
        start.toModel = head.toModel :=
  getHeadFrom_eq_ghostBy_decisionKey
    (G := (nodeView lower nodes).withBoost (store.boostedNode config gloas)) gloas tree rfl
    fun inNodes decision computed =>
    have ⟨_, ⟨_, found⟩, _⟩ := filterNodeTree_mem tree _ inNodes
    getWeight_eq_weight_withBoost_of_gloas gloas decision justifiedState found nodes computed

variable (lower) in
/-- From Gloas, the head of the store is the head of LMD-GHOST over nodes with the boost and the
decisions of the previous slot.

Each known block must sit at a later slot than its known parent, and some node must be viable.

The model starts at the pending node of the justified block, over the view of the viable nodes.

Its voters are the validators active and not slashed in the justified state.

Its stakes are their effective balances, and an equivocator has no vote.

The boost is one more vote, for the pending node of the boosted block, and its stake is the score
of the boost.

A child is greater by weight, then by root as bytes, then by status number.

A payload decision of the previous slot weighs 0 instead, and takes its own tiebreak.

Its tiebreak is 1 for the empty node, and for the full node 2 when the proposer should build on the
payload, and 0 otherwise. -/
theorem getHead_eq_ghostBy_withBoost_of_gloas {nodes : List ForkChoiceNode}
    {head : ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (found : store.getHead config = .ok head) :
    ghostBy ((nodeView lower nodes).withBoost (store.boostedNode config gloas))
      (store.decisionKey config gloas (weight (voters state).insertNone
        (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
        ((nodeView lower nodes).withBoost (store.boostedNode config gloas))))
      (some store.justifiedCheckpoint.root, none) = head.toModel := by
  have notEmpty : ¬ (.glamsterdam ≤ fork ∧ nodes.isEmpty = true) :=
    fun ⟨_, empty⟩ => someViable (List.isEmpty_iff.mp empty)
  simp only [getHead, tree, notEmpty, ↓reduceIte, bind, Except.bind] at found
  exact getHeadFrom_eq_ghostBy_withBoost_of_gloas gloas justifiedState tree (.refl _) found

/-! ## Every payload present -/

variable (lower) in
/-- The view of the blocks of the given nodes, their ancestors, and the block of each vote.

A vote is the block of the node that the store gives it.

So a vote for a block that the store does not hold is no vote here.

The view before Gloas keeps such a vote, and differs from this one only there. -/
noncomputable def blockView (nodes : List ForkChoiceNode) :
    View ℕ (Option Root) (blockTree lower) :=
  View.ofBlocks (nodes.map (some ·.root)).toFinset fun i => (store.latestNode i.toUInt64).map (·.1)

/-- When every known block builds on the full node of its known parent, every root does. -/
theorem buildsOnFull_of_full
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (root : Option Root) : store.buildsOnFull root = true := by
  rcases root with _ | root
  · rfl
  simp only [buildsOnFull]
  split
  · rename_i block found
    split
    · rename_i parent parentFound
      simp [fullParents root block parent found parentFound]
    · rfl
  · rfl

/-- From Gloas no vote supports an empty node when each later vote says the payload is present. -/
theorem latestNode_ne_empty (gloas : .glamsterdam ≤ fork)
    (present : ∀ (index : ValidatorIndex) (message : LatestMessage fork)
      (block : BeaconBlock preset fork),
      store.latestMessages[index]? = some message → store.blocks[message.root]? = some block →
      block.slot < message.slot gloas → message.payloadPresent gloas = true)
    (index : ValidatorIndex) (root : Option Root) :
    store.latestNode index ≠ some (root, some false) := by
  intro vote
  simp only [latestNode] at vote
  split at vote
  · cases vote
  cases message : store.latestMessages[index]? with
  | none => simp [message] at vote
  | some message' =>
  simp only [message, Option.bind_some] at vote
  cases found : store.blocks[message'.root]? with
  | none => simp [getSupportedNode_of_unknown gloas found, Except.toOption] at vote
  | some block =>
  by_cases later : block.slot < message'.slot gloas
  · simp [getSupportedNode_of_lt_slot gloas found later, present index message' block message found
      later, Except.toOption, ForkChoiceNode.toModel, PayloadStatus.toStatus] at vote
  · simp [getSupportedNode_of_same_slot gloas found (UInt64.not_lt.mp later), Except.toOption,
      ForkChoiceNode.toModel, PayloadStatus.toStatus] at vote

/-- From Gloas, when every payload is present, the head of a model of nodes is the full node of
the head of a model of blocks.

The model of nodes has the blocks of the view of nodes, and the model of blocks those of the view
of blocks.

A vote of the model of blocks is the block of the vote of the model of nodes.

No vote of the model of nodes is for an empty node.

Every known block builds on the full node of its known parent.

The full node of each viable block is viable, and some node is viable. -/
private theorem ghost_full_of_gloas {ν : Type} {V : Finset ν} {w : ν → ℕ}
    {N : View ν (Option Root × Status) (nodeTree lower)}
    {G : View ν (Option Root) (blockTree lower)} {nodes : List ForkChoiceNode}
    {head : ForkChoiceNode}
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (fullViable : ∀ n ∈ nodes, ⟨n.root, .full⟩ ∈ nodes)
    (nodeBlocks : N.blocks = (nodeView lower nodes).blocks)
    (blockBlocks : G.blocks = (blockView lower nodes).blocks)
    (hvote : ∀ v r, N.latest v ≠ some (r, some false))
    (hlatest : ∀ v, G.latest v = (N.latest v).map Prod.fst)
    (model : ghost V w N nodeOrder (some store.justifiedCheckpoint.root, none) = head.toModel) :
    head.payloadStatus = .full ∧
      some head.root = ghost V w G rootValue (some store.justifiedCheckpoint.root) := by
  have hfull : ∀ r, r ≠ (blockTree lower).genesis → store.buildsOnFull r = true :=
    fun r _ => buildsOnFull_of_full fullParents r
  -- The order of roots is injective away from the common root.
  have hroot : Set.InjOn rootValue {r | r ≠ (blockTree lower).genesis} := by
    rintro (_ | a) ha (_ | b) hb same
    · rfl
    · exact (ha rfl).elim
    · exact (hb rfl).elim
    · rw [rootValue_some_injective same]
  -- A pending node is in the view of nodes exactly when its block is in the view of blocks.
  have hpending : ∀ r, (r, none) ∈ N.blocks ↔ r ∈ G.blocks := by
    intro r
    simp only [nodeBlocks, blockBlocks, nodeView, blockView, View.mem_ofBlocks, List.mem_toFinset,
      List.mem_map]
    constructor
    · rintro ⟨_, ⟨m, mMem, rfl⟩, above⟩
      exact ⟨_, ⟨m, mMem, rfl⟩, payloadTree_ancestor_fst above⟩
    · rintro ⟨_, ⟨m, mMem, rfl⟩, above⟩
      exact ⟨_, ⟨m, mMem, rfl⟩, payloadTree_ancestor_none_of above⟩
  -- The full node of each block of the view is in the view of nodes.
  have hpayload : ∀ r ∈ G.blocks, (r, some true) ∈ N.blocks := by
    intro r mem
    simp only [blockBlocks, blockView, View.mem_ofBlocks, List.mem_toFinset, List.mem_map] at mem
    obtain ⟨_, ⟨m, mMem, rfl⟩, above⟩ := mem
    simp only [nodeBlocks, nodeView, View.mem_ofBlocks, List.mem_toFinset, List.mem_map]
    by_cases same : r = some m.root
    · exact ⟨_, ⟨⟨m.root, .full⟩, fullViable m mMem, rfl⟩, by rw [same]; exact .refl _⟩
    · -- A child of the block in the chain of the vote hangs under its full node.
      obtain ⟨c, isChild, below⟩ := above.exists_child same
      have parent : (nodeTree lower).parent (c, none) = (r, some true) := by
        rw [nodeTree, payloadTree_parent_none isChild.1, isChild.2, hfull c isChild.1]
      exact ⟨_, ⟨m, mMem, rfl⟩,
        Ancestor.trans ⟨1, parent⟩ (payloadTree_ancestor_none_of (b := m.toModel) below)⟩
  have justified : some store.justifiedCheckpoint.root ∈ G.blocks := by
    simp only [blockBlocks, blockView, View.mem_ofBlocks, List.mem_toFinset, List.mem_map]
    exact ⟨_, ⟨_, filterNodeTree_self tree someViable, rfl⟩, .refl _⟩
  have full : ghost V w N nodeOrder (some store.justifiedCheckpoint.root, none) =
      (ghost V w G rootValue (some store.justifiedCheckpoint.root), some true) :=
    ghost_payloadTree _ _ hroot hfull hpending hpayload hvote hlatest justified
  rw [full] at model
  obtain ⟨roots, status⟩ := Prod.mk.inj model
  exact ⟨PayloadStatus.toStatus_injective (status.symm.trans rfl), roots.symm⟩

/-- From Gloas, when every payload is present, the head is the full node of the head over blocks.

That is the rule that the head follows before Gloas, over the view of the viable blocks.

That view reads each vote as the block of the node that the store gives it.

Every known block builds on the full node of its known parent.

Each vote from a later slot than its block says the payload is present.

The full node of each viable block is viable.

No viable node is a payload decision of the previous slot, and the boost does not apply.

Some node is viable. -/
theorem getHead_eq_ghost_full_of_gloas {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (present : ∀ (index : ValidatorIndex) (message : LatestMessage fork)
      (block : BeaconBlock preset fork),
      store.latestMessages[index]? = some message → store.blocks[message.root]? = some block →
      block.slot < message.slot gloas → message.payloadPresent gloas = true)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (fullViable : ∀ n ∈ nodes, ⟨n.root, .full⟩ ∈ nodes)
    (found : store.getHead config = .ok head) :
    head.payloadStatus = .full ∧
      some head.root = ghost (voters state) (balanceAt state) (blockView lower nodes) rootValue
        (some store.justifiedCheckpoint.root) :=
  ghost_full_of_gloas fullParents tree someViable fullViable rfl rfl
    (fun v r => latestNode_ne_empty gloas present v.toUInt64 r) (fun _ => rfl)
    (getHead_eq_ghost_of_gloas lower gloas noBoost noDecision justifiedState tree someViable found)

/-- From Gloas, when every payload is present, the head is the full node of the head over blocks
with the boost.

That is the rule that the head follows before Gloas, over the view of the viable blocks.

That view reads each vote as the block of the node that the store gives it.

The boost is one more vote, for the boosted block when the boost applies, and its stake is the
score of the boost.

Every known block builds on the full node of its known parent.

Each vote from a later slot than its block says the payload is present.

The full node of each viable block is viable.

No viable node is a payload decision of the previous slot.

Some node is viable. -/
theorem getHead_eq_ghost_full_withBoost_of_gloas {nodes : List ForkChoiceNode}
    {head : ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (present : ∀ (index : ValidatorIndex) (message : LatestMessage fork)
      (block : BeaconBlock preset fork),
      store.latestMessages[index]? = some message → store.blocks[message.root]? = some block →
      block.slot < message.slot gloas → message.payloadPresent gloas = true)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes) (someViable : nodes ≠ [])
    (fullViable : ∀ n ∈ nodes, ⟨n.root, .full⟩ ∈ nodes)
    (found : store.getHead config = .ok head) :
    head.payloadStatus = .full ∧
      some head.root = ghost (voters state).insertNone
        (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
        ((blockView lower nodes).withBoost ((store.boostedNode config gloas).map Prod.fst))
        rootValue (some store.justifiedCheckpoint.root) := by
  refine ghost_full_of_gloas fullParents tree someViable fullViable rfl rfl ?_ ?_
    (getHead_eq_ghost_withBoost_of_gloas lower gloas noDecision justifiedState tree someViable
      found)
  · -- The boost is a vote for a pending node.
    rintro (_ | v) r vote
    · simp [View.withBoost, boostedNode] at vote
      split at vote <;> simp_all
    · exact latestNode_ne_empty gloas present v.toUInt64 r vote
  · rintro (_ | v) <;> rfl

/-- One step of the walk over the viable nodes, from the children of its start.

Without children the start counts alone, if it is a viable leaf.

With children each child ranks lower, and its viable nodes join those of the start.

The start comes last, after some viable node of a child. -/
private theorem filterNodeTree_cases {node : ForkChoiceNode} {nodes : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes) :
    ∃ children, store.getNodeChildren node = .ok children ∧
      ((children = [] ∧ ∃ isViable, store.isViableLeaf config node = .ok isViable ∧
          nodes = if isViable then [node] else []) ∨
        (children ≠ [] ∧ ∃ viable : List ForkChoiceNode,
          (∀ child ∈ children, ∃ below, store.nodeRank child < store.nodeRank node ∧
            store.filterNodeTree config child = .ok below ∧ ∀ y ∈ below, y ∈ viable) ∧
          (∀ y ∈ viable, ∃ child ∈ children, ∃ below,
            store.nodeRank child < store.nodeRank node ∧
            store.filterNodeTree config child = .ok below ∧ y ∈ below) ∧
          ((viable = [] ∧ nodes = []) ∨ (viable ≠ [] ∧ nodes = viable ++ [node])))) := by
  rw [filterNodeTree, bind_ok_iff] at walk
  obtain ⟨children, childrenOk, walk⟩ := walk
  refine ⟨children, childrenOk, ?_⟩
  by_cases empty : children.isEmpty
  · simp only [empty, ↓reduceIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at walk
    obtain ⟨isViable, viableOk, rfl⟩ := walk
    exact .inl ⟨List.isEmpty_iff.mp empty, isViable, viableOk, rfl⟩
  simp only [empty, Bool.false_eq_true, ↓reduceIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at walk
  obtain ⟨viable, viableOk, rfl⟩ := walk
  refine .inr ⟨fun none => by simp [none] at empty, viable, ?_, ?_, ?_⟩
  · intro child childMem
    obtain ⟨below, belowOk⟩ := flatMapM_ok_of_mem viableOk child childMem
    split at belowOk
    · rename_i lowerRank
      exact ⟨below, lowerRank, belowOk, fun y hy => (mem_of_flatMapM_ok viableOk y).mpr
        ⟨child, childMem, below, by simp [lowerRank, belowOk], hy⟩⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk
  · intro y hy
    obtain ⟨child, childMem, below, belowOk, yMem⟩ := (mem_of_flatMapM_ok viableOk y).mp hy
    split at belowOk
    · exact ⟨child, childMem, below, ‹_›, belowOk, yMem⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at belowOk
  · by_cases none : viable = []
    · exact .inl ⟨none, by simp [none]⟩
    · exact .inr ⟨none, by simp [none]⟩

/-- The viable nodes below a child of a node are viable nodes of that node.

The child ranks below the node. -/
private theorem filterNodeTree_sub {node child : ForkChoiceNode}
    {nodes children : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes)
    (childrenOk : store.getNodeChildren node = .ok children) (childMem : child ∈ children) :
    ∃ below, store.nodeRank child < store.nodeRank node ∧
      store.filterNodeTree config child = .ok below ∧ ∀ y ∈ below, y ∈ nodes := by
  obtain ⟨children', childrenOk', cases⟩ := filterNodeTree_cases walk
  rw [childrenOk, Except.ok.injEq] at childrenOk'
  subst childrenOk'
  rcases cases with ⟨rfl, -⟩ | ⟨-, viable, lift, -, result⟩
  · cases childMem
  obtain ⟨below, lowerRank, belowOk, sub⟩ := lift child childMem
  refine ⟨below, lowerRank, belowOk, fun y hy => ?_⟩
  rcases result with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · cases sub y hy
  · exact List.mem_append_left _ (sub y hy)

/-- A viable node of a node is that node, or a viable node below one of its children.

The viable nodes below that child are viable nodes of the node. -/
private theorem filterNodeTree_mem_cases {node n : ForkChoiceNode} {nodes : List ForkChoiceNode}
    (walk : store.filterNodeTree config node = .ok nodes) (mem : n ∈ nodes) :
    n = node ∨ ∃ children, store.getNodeChildren node = .ok children ∧ ∃ child ∈ children,
      ∃ below, store.nodeRank child < store.nodeRank node ∧
        store.filterNodeTree config child = .ok below ∧ n ∈ below ∧
        ∀ y ∈ below, y ∈ nodes := by
  obtain ⟨children, childrenOk, cases⟩ := filterNodeTree_cases walk
  rcases cases with ⟨-, isViable, -, rfl⟩ | ⟨-, viable, -, from', result⟩
  · cases isViable
    · cases mem
    · exact .inl (List.mem_singleton.mp mem)
  rcases result with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · cases mem
  rcases List.mem_append.mp mem with mem | same
  · obtain ⟨child, childMem, below, -, belowOk, nMem⟩ := from' n mem
    obtain ⟨below', lowerRank, belowOk', sub⟩ := filterNodeTree_sub walk childrenOk childMem
    rw [belowOk, Except.ok.injEq] at belowOk'
    subst belowOk'
    exact .inr ⟨children, childrenOk, child, childMem, below, lowerRank, belowOk, nMem, sub⟩
  · exact .inl (List.mem_singleton.mp same)

/-- The start of a walk that succeeds is among its viable nodes.

That holds when every node of a known block is a viable leaf. -/
private theorem filterNodeTree_self_of_viable
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true) :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode},
      store.filterNodeTree config node = .ok nodes → node ∈ nodes := by
  intro node
  induction hrank : store.nodeRank node using Nat.strongRecOn generalizing node with
  | _ rank ih =>
  intro nodes walk
  obtain ⟨children, -, cases⟩ := filterNodeTree_cases walk
  rcases cases with ⟨-, isViable, viableOk, rfl⟩ | ⟨nonempty, viable', lift, -, result⟩
  · obtain ⟨block, found⟩ := filterNodeTree_known walk
    rw [viable node block found, Except.ok.injEq] at viableOk
    subst viableOk
    exact List.mem_singleton_self _
  obtain ⟨child, childMem⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨below, lowerRank, belowOk, sub⟩ := lift child childMem
  have childIn := sub child (ih _ (hrank ▸ lowerRank) rfl belowOk)
  rcases result with ⟨rfl, -⟩ | ⟨-, rfl⟩
  · cases childIn
  · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- From Gloas, each viable node of a pending node has the full node of its block among them.

That holds when the store has verified the payload of every known block.

Every node of a known block must also be a viable leaf. -/
private theorem filterNodeTree_full (gloas : .glamsterdam ≤ fork)
    (verified : ∀ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.isPayloadVerified gloas root = true)
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true) :
    ∀ {node : ForkChoiceNode} {nodes : List ForkChoiceNode}, node.payloadStatus = .pending →
      store.filterNodeTree config node = .ok nodes → ∀ n ∈ nodes, ⟨n.root, .full⟩ ∈ nodes := by
  intro node
  induction hrank : store.nodeRank node using Nat.strongRecOn generalizing node with
  | _ rank ih =>
  intro nodes pending walk n mem
  obtain ⟨block, found⟩ := filterNodeTree_known walk
  have childrenOk := getNodeChildren_of_pending (store := store) gloas pending
  simp only [verified _ block found, ↓reduceIte] at childrenOk
  -- The full node of the start is viable.
  obtain ⟨fullBelow, -, fullOk, fullSub⟩ :=
    filterNodeTree_sub walk childrenOk (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  have fullIn := fullSub _ (filterNodeTree_self_of_viable viable fullOk)
  rcases filterNodeTree_mem_cases walk mem with
    rfl | ⟨children, childrenOk', child, childMem, below, lowerRank, belowOk, nMem, sub⟩
  · exact fullIn
  rw [childrenOk, Except.ok.injEq] at childrenOk'
  subst childrenOk'
  -- The child is the empty or the full node of the start.
  have childRoot : child.root = node.root ∧ child.payloadStatus ≠ .pending := by
    rcases List.mem_cons.mp childMem with rfl | childMem
    · exact ⟨rfl, by simp⟩
    · rw [List.mem_singleton.mp childMem]
      exact ⟨rfl, by simp⟩
  rcases filterNodeTree_mem_cases belowOk nMem with rfl | ⟨grand, grandOk, q, qMem, qBelow,
    qRank, qOk, nqMem, qSub⟩
  · rw [childRoot.1]
    exact fullIn
  -- A child of an empty or full node is pending, and ranks below the start.
  have qPending := ((mem_getNodeChildren_of_gloas gloas childRoot.2 grandOk).mp qMem).1
  exact sub _ (qSub _ (ih _ (hrank ▸ Nat.lt_trans qRank lowerRank) rfl qPending qOk n nqMem))

/-- The filtered tree holds the pending node of the justified block.

That holds when every node of a known block is a viable leaf. -/
theorem justified_mem_getFilteredNodeTree {nodes : List ForkChoiceNode}
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true)
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ⟨store.justifiedCheckpoint.root, .pending⟩ ∈ nodes :=
  filterNodeTree_self_of_viable viable tree

/-- From Gloas, the filtered tree holds the full node of each block that it holds.

That holds when the store has verified the payload of every known block.

Every node of a known block must also be a viable leaf. -/
theorem full_mem_getFilteredNodeTree {nodes : List ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (verified : ∀ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.isPayloadVerified gloas root = true)
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true)
    (tree : store.getFilteredNodeTree config = .ok nodes) :
    ∀ n ∈ nodes, ⟨n.root, .full⟩ ∈ nodes :=
  filterNodeTree_full gloas verified viable rfl tree

/-- From Gloas, when every payload is present and verified, the head is a full node.

Its root is the head over blocks.

That is the rule that the head follows before Gloas, over the view of the viable blocks.

Every known block builds on the full node of its known parent.

The store has verified the payload of every known block.

Each vote from a later slot than its block says the payload is present.

Every node of a known block is a viable leaf.

No viable node is a payload decision of the previous slot, and the boost does not apply. -/
theorem getHead_eq_ghost_full_of_verified {nodes : List ForkChoiceNode} {head : ForkChoiceNode}
    (gloas : .glamsterdam ≤ fork)
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (verified : ∀ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.isPayloadVerified gloas root = true)
    (present : ∀ (index : ValidatorIndex) (message : LatestMessage fork)
      (block : BeaconBlock preset fork),
      store.latestMessages[index]? = some message → store.blocks[message.root]? = some block →
      block.slot < message.slot gloas → message.payloadPresent gloas = true)
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true)
    (noBoost : store.shouldApplyProposerBoost config gloas = .ok false)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (found : store.getHead config = .ok head) :
    head.payloadStatus = .full ∧
      some head.root = ghost (voters state) (balanceAt state) (blockView lower nodes) rootValue
        (some store.justifiedCheckpoint.root) := by
  have someViable := List.ne_nil_of_mem (justified_mem_getFilteredNodeTree viable tree)
  exact getHead_eq_ghost_full_of_gloas gloas fullParents present noBoost noDecision
    justifiedState tree someViable
    (full_mem_getFilteredNodeTree gloas verified viable tree) found

/-- From Gloas, when every payload is present and verified, the head is a full node.

Its root is the head over blocks with the boost.

That is the rule that the head follows before Gloas, over the view of the viable blocks.

The boost is one more vote, for the boosted block when the boost applies, and its stake is the
score of the boost.

Every known block builds on the full node of its known parent.

The store has verified the payload of every known block.

Each vote from a later slot than its block says the payload is present.

Every node of a known block is a viable leaf.

No viable node is a payload decision of the previous slot. -/
theorem getHead_eq_ghost_full_withBoost_of_verified {nodes : List ForkChoiceNode}
    {head : ForkChoiceNode} (gloas : .glamsterdam ≤ fork)
    (fullParents : ∀ (root : Root) (block parent : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.blocks[block.parentRoot]? = some parent →
      parentPayloadStatus block parent = .full)
    (verified : ∀ (root : Root) (block : BeaconBlock preset fork),
      store.blocks[root]? = some block → store.isPayloadVerified gloas root = true)
    (present : ∀ (index : ValidatorIndex) (message : LatestMessage fork)
      (block : BeaconBlock preset fork),
      store.latestMessages[index]? = some message → store.blocks[message.root]? = some block →
      block.slot < message.slot gloas → message.payloadPresent gloas = true)
    (viable : ∀ (node : ForkChoiceNode) (block : BeaconBlock preset fork),
      store.blocks[node.root]? = some block → store.isViableLeaf config node = .ok true)
    (noDecision : ∀ n ∈ nodes, store.isPreviousSlotPayloadDecision config n = .ok false)
    (justifiedState : store.checkpointState store.justifiedCheckpoint = .ok state)
    (tree : store.getFilteredNodeTree config = .ok nodes)
    (found : store.getHead config = .ok head) :
    head.payloadStatus = .full ∧
      some head.root = ghost (voters state).insertNone
        (boostStake (balanceAt state) (store.boostScoreOfGloas config gloas))
        ((blockView lower nodes).withBoost ((store.boostedNode config gloas).map Prod.fst))
        rootValue (some store.justifiedCheckpoint.root) := by
  have someViable := List.ne_nil_of_mem (justified_mem_getFilteredNodeTree viable tree)
  exact getHead_eq_ghost_full_withBoost_of_gloas gloas fullParents present noDecision
    justifiedState tree someViable
    (full_mem_getFilteredNodeTree gloas verified viable tree) found

end Store

end EthLib.Consensus
