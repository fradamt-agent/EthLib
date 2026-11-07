module

public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints

/-!
# Proofs: the data of the blocks that can become the head

A reachable store keeps only blocks whose data passed the availability check of the fork choice.

The anchor block is the only exception, since the store takes it on trust.

At Deneb and Electra the node held the blobs of the block, and their proofs matched.

At Fulu the node got every column that it samples for the block, and each column was valid.

That reads the columns that the block source returns as those that the node samples, as
`validateDataAvailability_ok_of_fulu` says.

From Gloas the check of a block passes, and the data comes with the payload.

There every payload that the store counts as verified passed the check of its columns.

That check runs against the bid in the state after its block, as the store keeps it.

Every known block that builds on the payload of its parent finds that payload verified, except the
anchor.

So the head and every block of its chain that the store holds passed the check, except the anchor.
When the head is a full node, its payload passed the check too.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

namespace Store

variable {config : Config} {store after : Store preset fork}

/-! ## The handlers keep the payloads -/

theorem updateCheckpoints_payloads (justified finalized : Checkpoint) :
    (store.updateCheckpoints justified finalized).payloads = store.payloads := by
  unfold Store.updateCheckpoints
  by_cases hj : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases hf : store.finalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [hj, hf, ↓reduceIte]

theorem updateUnrealizedCheckpoints_payloads (justified finalized : Checkpoint) :
    (store.updateUnrealizedCheckpoints justified finalized).payloads = store.payloads := by
  unfold Store.updateUnrealizedCheckpoints
  by_cases hj : store.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases hf : store.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [hj, hf, ↓reduceIte]

theorem computePulledUpTip_payloads {root : Root}
    (pulled : store.computePulledUpTip config root = .ok after) :
    after.payloads = store.payloads := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨_, -, _, -, _, -, _, -, pulled⟩ := pulled
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled
  · rw [updateCheckpoints_payloads, updateUnrealizedCheckpoints_payloads]
  · rw [updateUnrealizedCheckpoints_payloads]

theorem onTickPerSlot_payloads {timeMs : UInt64}
    (ticked : store.onTickPerSlot config timeMs = .ok after) : after.payloads = store.payloads := by
  unfold onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    · obtain ⟨_, _, ticked⟩ := ticked
      split at ticked <;> simp only [pure, Except.pure, Except.ok.injEq] at ticked <;>
        subst ticked
      · rw [updateCheckpoints_payloads]
      · rfl

theorem catchUp_payloads {tickSlot : Slot} {start : Store preset fork}
    (caught : catchUp config start tickSlot = .ok after) : after.payloads = start.payloads := by
  induction start using catchUp.induct config tickSlot with
  | _ start ih =>
    rw [catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTimeMs, -, ticked, tick, caught⟩ := caught
      split at caught
      · rw [ih ticked ‹_› caught, onTickPerSlot_payloads tick]
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst caught
      rfl

theorem onTick_payloads {timeMs : UInt64} (ticked : store.onTick config timeMs = .ok after) :
    after.payloads = store.payloads := by
  unfold onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨tickSlot, -, caught, caughtUp, ticked⟩ := ticked
  rw [onTickPerSlot_payloads ticked, catchUp_payloads caughtUp]

theorem onAttestation_payloads {checks : SignatureChecks} {attestation : Attestation preset fork}
    {isFromBlock : Bool}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    after.payloads = store.payloads := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, valid, _, attested⟩ := attested
  have kept : stored.payloads = store.payloads := by
    unfold storeTargetCheckpointState at storing
    split at storing
    · simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      rfl
    · simp only [bind_ok_iff] at storing
      obtain ⟨_, _, storing⟩ := storing
      simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      rfl
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    exact kept
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

theorem onAttesterSlashing_payloads {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork}
    (slashed : store.onAttesterSlashing config checks slashing = .ok after) :
    after.payloads = store.payloads := by
  unfold onAttesterSlashing at slashed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
  obtain ⟨_, _, slashed⟩ := slashed
  subst slashed
  rfl

theorem recordBlockTimeliness_payloads {root : Root}
    (recorded : store.recordBlockTimeliness config root = .ok after) :
    after.payloads = store.payloads := by
  unfold recordBlockTimeliness at recorded
  simp only [bind_ok_iff, pure, Except.pure] at recorded
  obtain ⟨_, _, _, _, _, _, _, _, recorded⟩ := recorded
  split at recorded
  · simp only [bind_ok_iff, Except.ok.injEq] at recorded
    obtain ⟨_, _, rfl⟩ := recorded
    rfl
  · cases recorded
    rfl

theorem updateProposerBoostRoot_payloads {head root : Root}
    (updated : store.updateProposerBoostRoot config head root = .ok after) :
    after.payloads = store.payloads := by
  unfold updateProposerBoostRoot at updated
  split at updated
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at updated
  simp only [bind_ok_iff, pure_bind] at updated
  obtain ⟨_, _, _, _, _, _, updated⟩ := updated
  split at updated <;> simp only [pure, Except.pure, Except.ok.injEq] at updated <;>
    subst updated <;> rfl

/-- A signed block leaves the store, or adds a new block whose data and parent payload passed.

The block goes in at a free root, with its state, and the payloads stay. -/
theorem onBlock_checked {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    (added : store.onBlock config checks sources signed = .ok after) :
    after = store ∨ ∃ blockRoot state, store.blocks[blockRoot]? = none ∧
      after.blocks = store.blocks.insert blockRoot signed.message ∧
      after.blockStates = store.blockStates.insert blockRoot state ∧
      after.payloads = store.payloads ∧
      (∃ pre, store.blockStates[signed.message.parentRoot]? = some pre) ∧
      store.validateParentPayload signed.message = .ok () ∧
      validateDataAvailability config sources signed.message blockRoot = .ok () := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e =>
    simp [onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases contained : store.blocks.contains blockRoot
    · rw [onBlock_known root contained] at added
      cases added
      exact .inl rfl
    simp only [onBlock, root, contained, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := recordBlockPtcVotes_onlyPtcVotes vote
    obtain ⟨pre, preFound, parent, available, -⟩ := validateOnBlock_ok valid
    have free : store.blocks[blockRoot]? = none := by
      rw [Std.TreeMap.contains_eq_isSome_getElem?] at contained
      simpa using contained
    refine .inr ⟨blockRoot, state, free, ?_, ?_, ?_, ⟨pre, preFound⟩, parent, available⟩
    · rw [(computePulledUpTip_frame added).2.1, updateCheckpoints_blocks,
        (updateProposerBoostRoot_frame boost).2.1, (recordBlockTimeliness_frame record).2.1]
    · rw [(computePulledUpTip_frame added).2.2, updateCheckpoints_blockStates,
        (updateProposerBoostRoot_frame boost).2.2, (recordBlockTimeliness_frame record).2.2]
    · rw [computePulledUpTip_payloads added, updateCheckpoints_payloads,
        updateProposerBoostRoot_payloads boost, recordBlockTimeliness_payloads record]

variable (config) in
/-- The data checks that the blocks and payloads of a store passed.

Each known block other than the anchor passed the availability check, for some block source.

Each known block other than the anchor has a known parent.

From Gloas each verified payload passed the check of its columns, against the bid in the state
after its block.

Each known block other than the anchor that builds on the payload of its parent finds that payload
verified. -/
structure DataChecked (anchorRoot : Root) (store : Store preset fork) : Prop where
  blocks : ∀ {root : Root} {block : BeaconBlock preset fork}, store.blocks[root]? = some block →
    root = anchorRoot ∨ ∃ sources : BlockSources preset fork,
      validateDataAvailability config sources block root = .ok ()
  parentKnown : ∀ {root : Root} {block : BeaconBlock preset fork},
    store.blocks[root]? = some block → root = anchorRoot ∨ store.blocks[block.parentRoot]? ≠ none
  payloads : ∀ (gloas : .glamsterdam ≤ fork) {root : Root},
    store.isPayloadVerified gloas root = true →
      ∃ (sources : BlockSources preset fork) (state : BeaconState preset fork),
        store.blockStates[root]? = some state ∧
        validatePayloadData config sources root (state.latestExecutionPayloadBid gloas) = .ok ()
  parentPayloads : ∀ (gloas : .glamsterdam ≤ fork) {root : Root}
    {block parent : BeaconBlock preset fork}, store.blocks[root]? = some block →
    store.blocks[block.parentRoot]? = some parent → parentPayloadStatus block parent = .full →
    root = anchorRoot ∨ store.isPayloadVerified gloas block.parentRoot = true

/-- A store with the same blocks, states and payloads passed the same checks. -/
theorem DataChecked.of_eq {anchorRoot : Root} (checked : store.DataChecked config anchorRoot)
    (blocks : after.blocks = store.blocks) (states : after.blockStates = store.blockStates)
    (payloads : after.payloads = store.payloads) : after.DataChecked config anchorRoot := by
  have verified : ∀ gloas root, after.isPayloadVerified gloas root =
      store.isPayloadVerified gloas root := by
    intro gloas root
    simp [isPayloadVerified, payloads]
  obtain ⟨b, k, p, pp⟩ := checked
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [blocks]; exact b
  · rw [blocks]; exact k
  · intro gloas root ok
    rw [verified] at ok
    rw [states]
    exact p gloas ok
  · intro gloas root block parent found parentFound full
    rw [blocks] at found parentFound
    rw [verified]
    exact pp gloas found parentFound full

end Store

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}

/-- The blocks and payloads of a reachable store passed the data checks of the fork choice.

The anchor block is the only exception: the store takes it on trust. -/
theorem Store.Reachable.dataChecked
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      store.DataChecked config anchorRoot := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, rootOk, blocks, states⟩ := getForkchoiceStore_maps made
    obtain ⟨root', rootOk', -, -, fields⟩ := getForkchoiceStore_fields made
    refine ⟨anchorRoot, rootOk, ⟨fun found => ?_, fun found => ?_, fun gloas root ok => ?_,
      fun gloas root block parent found _ _ => ?_⟩⟩
    all_goals try (rw [blocks, getElem?_insert_root] at found; split at found
                   · rename_i same; exact .inl same.symm
                   · simp at found)
    simp [isPayloadVerified, (fields gloas).2.1] at ok
  | tick _ ticked ih =>
    obtain ⟨anchorRoot, rootOk, checked⟩ := ih
    obtain ⟨-, -, blocks, states⟩ := Store.onTick_frame ticked
    exact ⟨anchorRoot, rootOk, checked.of_eq blocks states (Store.onTick_payloads ticked)⟩
  | attestation _ attested ih =>
    obtain ⟨anchorRoot, rootOk, checked⟩ := ih
    obtain ⟨-, blocks, states⟩ := Store.onAttestation_frame attested
    exact ⟨anchorRoot, rootOk,
      checked.of_eq blocks states (Store.onAttestation_payloads attested)⟩
  | attesterSlashing _ slashed ih =>
    obtain ⟨anchorRoot, rootOk, checked⟩ := ih
    obtain ⟨-, blocks, states⟩ := Store.onAttesterSlashing_frame slashed
    exact ⟨anchorRoot, rootOk,
      checked.of_eq blocks states (Store.onAttesterSlashing_payloads slashed)⟩
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
    obtain ⟨anchorRoot, rootOk, checked⟩ := ih
    exact ⟨anchorRoot, rootOk, checked.of_eq rfl rfl rfl⟩
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := onInclusionList_ok _ accepted
    obtain ⟨anchorRoot, rootOk, checked⟩ := ih
    exact ⟨anchorRoot, rootOk, checked.of_eq rfl rfl rfl⟩
  | @envelope old new checks sources gloas signed _ accepted ih =>
    obtain ⟨anchorRoot, rootOk, checked⟩ := ih
    obtain ⟨state, found, data, -, recorded, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := recordEnvelope_frame record
    -- The verified payloads grow by the payload of the envelope, which passed its check.
    have grow : ∀ (g : .glamsterdam ≤ fork) root, old.isPayloadVerified g root = true →
        ((old.payloads gloas).insert signed.message.beaconBlockRoot signed.message).contains
          root = true := by
      intro g root ok
      simp only [isPayloadVerified] at ok
      simp [Std.TreeMap.contains_insert, ok]
    refine ⟨anchorRoot, rootOk, fun found => checked.blocks found,
      fun found => checked.parentKnown found, fun g root ok => ?_,
      fun g root block parent found parentFound full => ?_⟩
    · simp only [isPayloadVerified, Std.TreeMap.contains_insert] at ok
      rcases Bool.or_eq_true_iff.mp ok with same | old'
      · have same : signed.message.beaconBlockRoot = root := by simpa using same
        subst same
        exact ⟨sources, state, found, data⟩
      · exact checked.payloads g old'
    · rcases checked.parentPayloads g found parentFound full with same | ok
      · exact .inl same
      · exact .inr (grow g _ ok)
  | @block old new checks sources signed earlier added ih =>
    obtain ⟨anchorRoot, rootOk, checked⟩ := ih
    refine ⟨anchorRoot, rootOk, ?_⟩
    obtain same | ⟨blockRoot, state, free, blocks, states, payloads, ⟨pre, preFound⟩, parentOk,
      available⟩ := Store.onBlock_checked added
    · subst same
      exact checked
    obtain ⟨-, -, _, known, -⟩ := earlier.checkpointsFrom
    have verified : ∀ g root, new.isPayloadVerified g root = old.isPayloadVerified g root := by
      intro g root
      simp [Store.isPayloadVerified, payloads]
    -- The parent of the new block is known, at another root.
    have parentContained := known preFound
    rw [Std.TreeMap.contains_eq_isSome_getElem?] at parentContained
    obtain ⟨parentBlock, parentFound⟩ := Option.isSome_iff_exists.mp parentContained
    have parentNe : signed.message.parentRoot ≠ blockRoot := by
      rintro same
      rw [same, free] at parentFound
      cases parentFound
    have keep : ∀ {r : Root} {b : BeaconBlock preset fork}, old.blocks[r]? = some b →
        new.blocks[r]? = some b := by
      intro r b found
      rw [blocks, getElem?_insert_root]
      split
      · rename_i same
        rw [← same, free] at found
        cases found
      · exact found
    have keepState : ∀ {r : Root} {s : BeaconState preset fork}, old.blockStates[r]? = some s →
        new.blockStates[r]? = some s := by
      intro r s found
      rw [states, getElem?_insert_root]
      split
      · rename_i same
        have := known found
        rw [← same, Std.TreeMap.contains_eq_isSome_getElem?, free] at this
        cases this
      · exact found
    refine ⟨fun found => ?_, fun found => ?_, fun g root ok => ?_,
      fun g root block parent found parentFound' full => ?_⟩
    · rw [blocks, getElem?_insert_root] at found
      split at found
      · rename_i same
        cases found
        exact .inr ⟨sources, same ▸ available⟩
      · exact checked.blocks found
    · rw [blocks, getElem?_insert_root] at found
      split at found
      · cases found
        exact .inr (by rw [keep parentFound]; simp)
      · rcases checked.parentKnown found with same | some
        · exact .inl same
        · obtain ⟨p, pFound⟩ := Option.ne_none_iff_exists'.mp some
          exact .inr (by rw [keep pFound]; simp)
    · rw [verified] at ok
      obtain ⟨src, s, sFound, data⟩ := checked.payloads g ok
      exact ⟨src, s, keepState sFound, data⟩
    · rw [verified]
      rw [blocks, getElem?_insert_root] at found
      split at found
      · -- The new block: its parent payload passed the check when it went in.
        cases found
        rw [keep parentFound, Option.some.injEq] at parentFound'
        subst parentFound'
        obtain ⟨p, pFound, needs⟩ := (Store.validateParentPayload_ok_iff g).mp parentOk
        rw [parentFound, Option.some.injEq] at pFound
        subst pFound
        exact .inr (needs full)
      · -- An old block: its parent was known before, so it is not the new block.
        rcases checked.parentKnown found with same | some
        · exact .inl same
        obtain ⟨p, pFound⟩ := Option.ne_none_iff_exists'.mp some
        rw [keep pFound, Option.some.injEq] at parentFound'
        subst parentFound'
        exact checked.parentPayloads g found pFound full

namespace Store

/-- The head is a known block, and from Gloas a full head has a verified payload.

The head is the justified block, or a viable node, whose block the store holds.

A full node is viable only as the child of the pending node of its block, when its payload is
verified. -/
theorem getHead_known_verified {head : ForkChoiceNode} (found : store.getHead config = .ok head) :
    (∃ block, store.blocks[head.root]? = some block) ∧
      ∀ gloas : .glamsterdam ≤ fork, head.payloadStatus = .full →
        store.isPayloadVerified gloas head.root = true := by
  unfold getHead at found
  cases tree : store.getFilteredNodeTree config with
  | error e => simp [tree, bind, Except.bind] at found
  | ok nodes =>
  obtain ⟨justifiedBlock, justifiedFound⟩ := filterNodeTree_known tree
  simp only [tree, bind, Except.bind] at found
  split at found
  · simp only [pure, Except.pure, Except.ok.injEq] at found
    subst found
    exact ⟨⟨_, justifiedFound⟩, fun _ full => by cases full⟩
  rcases getHeadFrom_mem found with rfl | mem
  · exact ⟨⟨_, justifiedFound⟩, fun _ full => by cases full⟩
  obtain ⟨-, known, origin⟩ := filterNodeTree_mem tree head mem
  refine ⟨known, fun gloas full => ?_⟩
  rcases origin with rfl | ⟨p, -, children, childrenOk, child⟩
  · cases full
  by_cases pending : p.payloadStatus = .pending
  · rw [getNodeChildren_of_pending gloas pending, Except.ok.injEq] at childrenOk
    subst childrenOk
    simp only [List.mem_cons] at child
    rcases child with rfl | child
    · cases full
    · split at child
      · rename_i verified
        rw [List.mem_singleton.mp child]
        exact verified
      · cases child
  · obtain ⟨childPending, -⟩ := (mem_getNodeChildren_of_gloas gloas pending childrenOk).mp child
    rw [full] at childPending
    cases childPending

end Store

/-- The head of a reachable store passed the data checks of the fork choice.

So did every block that the store holds, which includes each block of the chain of the head.

The anchor block is the only exception: the store takes it on trust.

At Fulu the check means that the block source returned every column that the node samples, each
valid, as `validateDataAvailability_ok_of_fulu` says.

From Gloas a full head has a payload that passed the check of its columns, against the bid in the
state after its block. -/
theorem Store.Reachable.getHead_dataChecked {head : ForkChoiceNode}
    (reachable : Store.Reachable config anchorState anchorBlock store)
    (found : store.getHead config = .ok head) :
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      store.DataChecked config anchorRoot ∧
      (∃ block, store.blocks[head.root]? = some block ∧
        (head.root = anchorRoot ∨ ∃ sources : BlockSources preset fork,
          validateDataAvailability config sources block head.root = .ok ())) ∧
      ∀ gloas : .glamsterdam ≤ fork, head.payloadStatus = .full →
        ∃ (sources : BlockSources preset fork) (state : BeaconState preset fork),
          store.blockStates[head.root]? = some state ∧
          validatePayloadData config sources head.root
            (state.latestExecutionPayloadBid gloas) = .ok () := by
  obtain ⟨anchorRoot, rootOk, checked⟩ := reachable.dataChecked
  obtain ⟨⟨block, known⟩, verified⟩ := Store.getHead_known_verified found
  exact ⟨anchorRoot, rootOk, checked, ⟨block, known, checked.blocks known⟩,
    fun gloas full => checked.payloads gloas (verified gloas full)⟩

end EthLib.Consensus
