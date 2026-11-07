module

public import EthLib.Consensus.Proofs.LightClient.Execution
public import EthLib.Consensus.Proofs.LightClient.Upgrade
public import EthLib.Serialization.Proofs.Ssz.Type.ValueEquality

/-!
# Proofs: a light client accepts what an honest full node gives

The other proofs of the light client state what the data that the client accepts proves.

This module states the converse: the client accepts the data that a full node builds.

A block must be of the fork of its slot, as `Config.SlotOfFork` states.

For Capella, Deneb, Electra and Gloas, the block has the type of that fork when its slot does.

The header that a full node builds from such a block passes the header check.

The bootstrap of such a block and its post state starts a store that trusts the block.

An update built from a block, its parent and the post state of the parent passes its checks.

This holds under the hypotheses that the protocol asks, with or without a finalized block.

The store must know the committee of the signing period and finalize an earlier slot.

The signature must verify, and a built branch must not be all zero.

Only a SHA-256 output of zero could make such a branch all zero.

The hypothesis on the fork of the slot is needed.

A Gloas block at a slot before Capella gives a header that fails the check.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork}

/-- A branch fits a vector of its depth exactly when the vector lists it. -/
theorem branchVector_ok_iff {depth : Nat} {branch : List Bytes32} {v : Vector Bytes32 depth} :
    branchVector depth branch = .ok v ↔ v.toList = branch := by
  unfold branchVector
  split
  · rename_i h
    constructor
    · intro e; cases e; simp
    · intro e; subst e; congr 1
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    intro e; exact h (by rw [← e]; simp)

/-- The branch that a full node builds for a node of a value climbs to the root of the value.

It climbs from the node, at the depth and the index of its generalized index. -/
theorem computeMerkleProof_valid {α : Type} [SszType α] [LawfulSszType α] (value : α)
    {gindex : Nat} (named : 2 ≤ gindex) {leaf root : Bytes32}
    (read : nodeRoot (SszType.desc α) (SszType.toValue value) gindex = .ok leaf.toArray)
    (rooted : SszType.hashTreeRoot value = .ok root) {branch : List Bytes32}
    (built : computeMerkleProof value gindex = .ok branch) :
    isValidMerkleBranch leaf branch (Nat.log2 gindex) (gindex % 2 ^ Nat.log2 gindex) root =
      true := by
  obtain ⟨root', nodes, rooted', proved, valid⟩ :=
    SszType.buildProof_isValidMerkleBranch value named read
  rw [rooted] at rooted'
  cases rooted'
  have : computeMerkleProof value gindex = .ok nodes := by
    simp only [computeMerkleProof, proved, bind, Except.bind]
    exact mapM_toChunk_map_toArray nodes
  rw [this] at built
  cases built
  exact valid

/-- Whether a fork is the fork of a slot, for the forks that change light client data.

From Capella, Deneb, Electra and Gloas, the fork is from that fork exactly when the slot is. -/
def Config.SlotOfFork (config : Config) (preset : Preset) (fork : Fork) (slot : Slot) : Prop :=
  (.shapella ≤ fork ↔ config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset slot) ∧
    (.dencun ≤ fork ↔ config.DENEB_FORK_EPOCH ≤ computeEpochAtSlot preset slot) ∧
    (.pectra ≤ fork ↔ config.ELECTRA_FORK_EPOCH ≤ computeEpochAtSlot preset slot) ∧
    (.glamsterdam ≤ fork ↔ config.GLOAS_FORK_EPOCH ≤ computeEpochAtSlot preset slot)

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

/-- The light client header that a full node builds from a block passes the header check.

The block must be of the fork of its slot, as `Config.SlotOfFork` states. -/
theorem blockToLightClientHeader_valid {config : Config} {block : SignedBeaconBlock preset fork}
    {header : LightClientHeader preset fork}
    (scheduled : config.SlotOfFork preset fork block.message.slot)
    (made : blockToLightClientHeader config block = .ok header) :
    isValidLightClientHeader config header = .ok true := by
  unfold blockToLightClientHeader at made
  simp only [bind_ok_iff] at made
  obtain ⟨⟨altair⟩, -, bodyRoot, bodyRooted, rest⟩ := made
  have bodyRooted := LightClientError.liftRoot_ok.mp bodyRooted
  obtain ⟨-, ⟨deneb, -⟩, -, ⟨gloasSlot, -⟩⟩ := scheduled
  by_cases gloas : Fork.glamsterdam ≤ fork
  · -- From Gloas the branch proves the parent block hash of the bid.
    simp only [gloas, ↓reduceDIte, bind_ok_iff] at rest
    obtain ⟨nodes, proved, branch, vectored, built⟩ := rest
    cases built
    have proved := LightClientError.liftRoot_ok.mp proved
    obtain ⟨root, honest, honestRooted, honestBuilt, valid⟩ :=
      computeMerkleProof_isValidNormalizedMerkleBranch block.message.body (by decide)
        (BeaconBlockBody.nodeRoot_parentBlockHash gloas block.message.body)
    rw [bodyRooted] at honestRooted
    cases honestRooted
    rw [proved] at honestBuilt
    cases honestBuilt
    unfold isValidLightClientHeader
    simp only [LightClientError.requireFork, altair, ↓reduceIte, gloas, ↓reduceDIte,
      gloasSlot gloas, bind, Except.bind, LightClientError.liftRoot, Except.mapError,
      branchVector_ok_iff.mp vectored, valid]
  simp only [gloas, ↓reduceDIte] at rest
  by_cases capella : Fork.shapella ≤ fork
  swap
  · -- Before Capella a header has only its beacon header, which the check accepts.
    simp only [capella, not_false_eq_true, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at rest
    subst rest
    unfold isValidLightClientHeader
    simp [LightClientError.requireFork, altair, gloas, capella, pure, Except.pure, bind,
      Except.bind]
  simp only [capella, not_true_eq_false, ↓reduceDIte] at rest
  by_cases early : computeEpochAtSlot preset block.message.slot < config.CAPELLA_FORK_EPOCH
  · -- Before the Capella slot, the header is empty with a branch of zeros.
    simp only [early, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at rest
    subst rest
    unfold isValidLightClientHeader
    simp [LightClientError.requireFork, altair, gloas, capella, early, sameSszValue,
      ExecutionPayloadHeader.empty, pure, Except.pure, bind, Except.bind]
  -- From the Capella slot, the header is the header of the payload, proved at node 25.
  have started : config.CAPELLA_FORK_EPOCH ≤ computeEpochAtSlot preset block.message.slot :=
    UInt64.not_lt.mp early
  simp only [early, ↓reduceIte, bind_ok_iff] at rest
  obtain ⟨payloadHeader, madeHeader, nodes, proved, branch, vectored, built⟩ := rest
  cases built
  have madeHeader := LightClientError.liftRoot_ok.mp madeHeader
  have proved := LightClientError.liftRoot_ok.mp proved
  have beforeGloas : fork < .glamsterdam := Nat.lt_of_not_le gloas
  set payload := block.message.body.executionPayload
    ⟨Nat.le_trans (by decide) capella, beforeGloas⟩ with payloadIs
  obtain ⟨payloadRoot, payloadRooted⟩ := SszType.hashTreeRoot_total payload
  have climbs := computeMerkleProof_valid block.message.body (by decide)
    (BeaconBlockBody.nodeRoot_executionPayload capella beforeGloas block.message.body
      payloadRooted) bodyRooted proved
  have headerRooted : SszType.hashTreeRoot payloadHeader = .ok payloadRoot := by
    rw [ExecutionPayload.hashTreeRoot_header beforeGloas madeHeader, payloadRooted]
  have below : getSubtreeIndex EXECUTION_PAYLOAD_GINDEX =
      .ok (EXECUTION_PAYLOAD_GINDEX % 2 ^ Nat.log2 EXECUTION_PAYLOAD_GINDEX) := by
    simp [getSubtreeIndex, gindexDepth, gindexBelow, EXECUTION_PAYLOAD_GINDEX, bind,
      Except.bind, pure, Except.pure]
  by_cases denebFork : Fork.dencun ≤ fork
  · have denebSlot := deneb denebFork
    have notEarly : ¬ computeEpochAtSlot preset block.message.slot < config.DENEB_FORK_EPOCH :=
      UInt64.not_lt.mpr denebSlot
    unfold isValidLightClientHeader getLcExecutionRoot
    simp [LightClientError.requireFork, altair, gloas, capella, denebFork, notEarly, denebSlot,
      UInt64.not_lt.mpr started, headerRooted, branchVector_ok_iff.mp vectored, climbs, below,
      LightClientError.liftRoot, Except.mapError, pure, Except.pure, bind, Except.bind]
  · -- Without Deneb the fork is Capella, where the header has no blob gas to clear.
    have capellaFork : fork = .shapella := by
      cases fork <;> first
        | rfl | exact absurd capella (by decide) | exact absurd denebFork (by decide)
    subst capellaFork
    have same : (if computeEpochAtSlot preset block.message.slot < config.DENEB_FORK_EPOCH then
        { payloadHeader with blobGasUsed := fun _ => 0, excessBlobGas := fun _ => 0 }
      else payloadHeader) = payloadHeader := by
      split
      · cases payloadHeader
        congr 1 <;> funext later <;> exact absurd later (by decide)
      · rfl
    unfold isValidLightClientHeader getLcExecutionRoot
    simp [LightClientError.requireFork, altair, gloas, denebFork, same, started, early,
      ExecutionPayloadHeader.toCapella_self, headerRooted, branchVector_ok_iff.mp vectored,
      climbs, below, LightClientError.liftRoot, Except.mapError, pure, Except.pure, bind,
      Except.bind]

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- The header of a block, with the root of its body, has the root of the block.

A field and its root give one leaf, so the two containers have one root. -/
theorem BeaconBlock.hashTreeRoot_header {block : BeaconBlock preset fork} {bodyRoot : Root}
    (rooted : SszType.hashTreeRoot block.body = .ok bodyRoot) :
    SszType.hashTreeRoot (⟨block.slot, block.proposerIndex, block.parentRoot, block.stateRoot,
      bodyRoot⟩ : BeaconBlockHeader) = SszType.hashTreeRoot block := by
  have bodyRoots : SszType.root block.body = .ok bodyRoot.toArray := by
    simp only [SszType.hashTreeRoot, bind_ok_iff] at rooted
    obtain ⟨bytes, rooted, chunked⟩ := rooted
    rw [toChunk_ok_iff] at chunked
    rw [rooted, chunked]
  have chunk : SszType.root bodyRoot = .ok bodyRoot.toArray :=
    hashTreeRoot_chunk (by simp [bytesPerChunk])
  -- Both containers root the same five field roots; the names of the fields do not count.
  have names (first second : List String) (roots : List Bytes) :
      summaryRoot (.container first) roots = summaryRoot (.container second) roots := by
    simp only [summaryRoot, Serialization.Ssz.hashTreeRoot, Desc.nesting, hashTreeRootAt,
      merkleLayout]
  show (do toChunk (← (do summaryRoot (.container _) (← SszFields.roots
      (block.slot, block.proposerIndex, block.parentRoot, block.stateRoot, bodyRoot))))) =
    (do toChunk (← (do summaryRoot (.container _) (← SszFields.roots
      (block.slot, block.proposerIndex, block.parentRoot, block.stateRoot, block.body)))))
  have same : SszFields.roots
      (block.slot, block.proposerIndex, block.parentRoot, block.stateRoot, bodyRoot) =
      SszFields.roots
        (block.slot, block.proposerIndex, block.parentRoot, block.stateRoot, block.body) := by
    simp only [SszFields.roots, chunk, bodyRoots]
  rw [same]
  cases SszFields.roots
      (block.slot, block.proposerIndex, block.parentRoot, block.stateRoot, block.body) with
  | error e => rfl
  | ok roots => simp only [bind, Except.bind, names _ ["slot", "proposer_index", "parent_root",
      "state_root", "body"]]

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- At a slot of the fork of the store, the client reads the indices of that fork. -/
theorem lightClientGindices_of_slotOfFork {config : Config} {slot : Slot}
    (altair : .altair ≤ fork) (scheduled : config.SlotOfFork preset fork slot) :
    finalizedRootGindexAtSlot (preset := preset) (fork := fork) config slot =
        .ok (finalizedRootGindex fork) ∧
      currentSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config slot =
        .ok (currentSyncCommitteeGindex fork) ∧
      nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config slot =
        .ok (nextSyncCommitteeGindex fork) := by
  obtain ⟨-, -, ⟨electra, -⟩, ⟨gloas, -⟩⟩ := scheduled
  have forkAt : stateForkAtSlot (preset := preset) (fork := fork) config slot =
      .ok (if .glamsterdam ≤ fork then .glamsterdam
        else if .pectra ≤ fork then .pectra else .altair) := by
    simp only [stateForkAtSlot, LightClientError.requireFork, altair, ↓reduceIte, bind,
      Except.bind, pure, Except.pure]
    by_cases g : Fork.glamsterdam ≤ fork
    · simp [g, gloas g]
    · by_cases e : Fork.pectra ≤ fork
      · simp [g, e, electra e]
      · simp [g, e]
  unfold finalizedRootGindexAtSlot currentSyncCommitteeGindexAtSlot nextSyncCommitteeGindexAtSlot
  rw [forkAt]
  simp only [Functor.map, Except.map, Except.ok.injEq]
  split_ifs <;>
    simp_all +decide [finalizedRootGindex, currentSyncCommitteeGindex, nextSyncCommitteeGindex]

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- A value with its kept root has the root of the value. -/
theorem Rooted.hashTreeRoot_value {α : Type} [SszType α] [LawfulSszType α] (r : Rooted α) :
    SszType.hashTreeRoot r = SszType.hashTreeRoot r.value := by
  simp only [SszType.hashTreeRoot, LawfulSszType.root_eq]
  rfl

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- The beacon header of the light client header of a block is the header of the block.

Its body root is the root of the body of the block. -/
theorem blockToLightClientHeader_beacon {config : Config} {block : SignedBeaconBlock preset fork}
    {header : LightClientHeader preset fork}
    (made : blockToLightClientHeader config block = .ok header) :
    ∃ bodyRoot, SszType.hashTreeRoot block.message.body = .ok bodyRoot ∧
      header.beacon = ⟨block.message.slot, block.message.proposerIndex, block.message.parentRoot,
        block.message.stateRoot, bodyRoot⟩ := by
  unfold blockToLightClientHeader at made
  simp only [bind_ok_iff] at made
  obtain ⟨_, -, bodyRoot, bodyRooted, rest⟩ := made
  refine ⟨bodyRoot, LightClientError.liftRoot_ok.mp bodyRooted, ?_⟩
  repeat' split at rest
  all_goals first
    | (cases rest; rfl)
    | (simp only [bind_ok_iff] at rest
       obtain ⟨_, -, _, -, built⟩ := rest
       cases built; rfl)
    | (simp only [bind_ok_iff] at rest
       obtain ⟨_, -, _, -, _, -, built⟩ := rest
       cases built; rfl)

/-- A store starts from the bootstrap that a full node builds, trusting the block of the bootstrap.

The block must be of the fork of its slot, and at the slot of the state.

The state must be the post state of the block: its root is the state root of the block. -/
theorem createLightClientBootstrap_accepted [LawfulSszType (BeaconState preset fork)]
    {config : Config} {state : BeaconState preset fork} {block : SignedBeaconBlock preset fork}
    {bootstrap : LightClientBootstrap preset fork}
    (scheduled : config.SlotOfFork preset fork block.message.slot)
    (atSlot : block.message.slot = state.slot)
    (stateRooted : SszType.hashTreeRoot state = .ok block.message.stateRoot)
    {blockRoot : Root} (blockRooted : SszType.hashTreeRoot block.message = .ok blockRoot)
    (created : createLightClientBootstrap config state block = .ok bootstrap) :
    ∃ store, initializeLightClientStore config blockRoot bootstrap = .ok store := by
  unfold createLightClientBootstrap at created
  simp only [bind_ok_iff] at created
  obtain ⟨⟨altair⟩, -, _, -, _, -, _, -, _, -, _, -, _, -, gindex, indexed, header, madeHeader,
    nodes, proved, branch, vectored, built⟩ := created
  simp only [pure, Except.pure, Except.ok.injEq] at built
  subst built
  have proved := LightClientError.liftRoot_ok.mp proved
  obtain ⟨-, current, -⟩ := lightClientGindices_of_slotOfFork altair scheduled
  rw [← atSlot, current] at indexed
  cases indexed
  obtain ⟨bodyRoot, bodyRooted, beacon⟩ := blockToLightClientHeader_beacon madeHeader
  have valid := blockToLightClientHeader_valid scheduled madeHeader
  have headerRooted : SszType.hashTreeRoot header.beacon = .ok blockRoot := by
    rw [beacon, BeaconBlock.hashTreeRoot_header bodyRooted, blockRooted]
  -- The branch is the proof of the current committee in the state of the block.
  obtain ⟨leaf, leafRooted⟩ := SszType.hashTreeRoot_total (state.currentSyncCommittee altair)
  obtain ⟨root, honest, honestRooted, honestBuilt, climbs⟩ :=
    computeMerkleProof_isValidNormalizedMerkleBranch state
      (by unfold currentSyncCommitteeGindex; split <;> (try split) <;> decide)
      (BeaconState.nodeRoot_currentSyncCommittee altair state leafRooted)
  rw [stateRooted] at honestRooted
  cases honestRooted
  rw [proved] at honestBuilt
  cases honestBuilt
  rw [Rooted.hashTreeRoot_value] at leafRooted
  rw [beacon] at headerRooted
  unfold initializeLightClientStore
  simp only [LightClientError.requireFork, altair, ↓reduceIte, valid, beacon, headerRooted,
    leafRooted, current, branchVector_ok_iff.mp vectored, climbs, LightClientError.require,
    LightClientError.liftRoot, Except.mapError, bind, Except.bind, pure, Except.pure]
  exact ⟨_, rfl⟩

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- The upgrade of a valid header of a block of the fork of its slot is valid.

The block must not be the genesis block, and the schedule starts Capella no later than Deneb. -/
theorem LightClientHeader.upgrade_valid {config : Config} {pre post : Fork} {later : pre ≤ post}
    {header : LightClientHeader preset pre} {upgraded : LightClientHeader preset post}
    (valid : isValidLightClientHeader config header = .ok true)
    (scheduled : config.SlotOfFork preset pre header.beacon.slot)
    (notGenesis : header.beacon.slot ≠ GENESIS_SLOT)
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH)
    (altair : .altair ≤ pre)
    (computed : header.upgrade config post later = .ok upgraded) :
    isValidLightClientHeader config upgraded = .ok true := by
  obtain ⟨capella, deneb, -, gloas⟩ := scheduled
  have capellaSlot : .shapella ≤ pre ∨
      computeEpochAtSlot preset header.beacon.slot < config.CAPELLA_FORK_EPOCH := by
    by_cases c : Fork.shapella ≤ pre
    · exact .inl c
    · exact .inr (UInt64.not_le.mp fun h => c (capella.mpr h))
  have denebSlot : .dencun ≤ pre ∨
      computeEpochAtSlot preset header.beacon.slot < config.DENEB_FORK_EPOCH := by
    by_cases c : Fork.dencun ≤ pre
    · exact .inl c
    · exact .inr (UInt64.not_le.mp fun h => c (deneb.mpr h))
  by_cases postGloas : Fork.glamsterdam ≤ post
  · have beforeGloas : .glamsterdam ≤ pre ∨
        computeEpochAtSlot preset header.beacon.slot < config.GLOAS_FORK_EPOCH := by
      by_cases c : Fork.glamsterdam ≤ pre
      · exact .inl c
      · exact .inr (UInt64.not_le.mp fun h => c (gloas.mpr h))
    refine LightClientHeader.isValidLightClientHeader_upgrade postGloas valid ?_ capellaSlot
      denebSlot ordered beforeGloas computed
    intro same
    exact notGenesis (by rw [same]; rfl)
  · have preBefore : pre < .glamsterdam := Nat.lt_of_le_of_lt later (Nat.lt_of_not_le postGloas)
    have preGloas : ¬ Fork.glamsterdam ≤ pre := Nat.not_le_of_lt preBefore
    unfold LightClientHeader.upgrade at computed
    simp only [preGloas, postGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact LightClientHeader.isValidLightClientHeader_upgradeFields (Nat.le_trans altair later)
      (fun c => Nat.le_trans c later) (fun d => Nat.le_trans d later) preBefore
      (Nat.lt_of_not_le postGloas) valid capellaSlot denebSlot

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- What an update that a full node builds carries.

Its attested header is the header of the attested block.

When the attested and signing blocks share a period, it carries the next committee and its proof.

That committee is the next committee of the attested state.

Otherwise it carries the zero committee and a branch of zeros.

Without a finalized block it carries the zero header and a branch of zeros.

With one, it carries the proof of the finalized root of the attested state.

Its finalized header is then the upgraded header of that block, whose root is that finalized root.

At the genesis slot it is the zero header instead, and the finalized root is zero. -/
theorem createLightClientUpdate_shape {config : Config} {signatureFork finalizedFork : Fork}
    {state : BeaconState preset signatureFork} {block : SignedBeaconBlock preset signatureFork}
    {attestedState : BeaconState preset fork} {attestedBlock : SignedBeaconBlock preset fork}
    {finalizedBlock : Option (SignedBeaconBlock preset finalizedFork)}
    {finalizedEarlier : finalizedFork ≤ fork} {update : LightClientUpdate preset fork}
    (created : createLightClientUpdate config state block attestedState attestedBlock
      finalizedBlock finalizedEarlier = .ok update) :
    ∃ altair : .altair ≤ fork,
      blockToLightClientHeader config attestedBlock = .ok update.attestedHeader ∧
      (computeSyncCommitteePeriodAtSlot preset attestedBlock.message.slot =
          computeSyncCommitteePeriodAtSlot preset block.message.slot →
        update.nextSyncCommittee = (attestedState.nextSyncCommittee altair).value ∧
        ∃ gindex, nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
            attestedState.slot = .ok gindex ∧
          computeMerkleProof attestedState gindex = .ok update.nextSyncCommitteeBranch.toList) ∧
      (computeSyncCommitteePeriodAtSlot preset attestedBlock.message.slot ≠
          computeSyncCommitteePeriodAtSlot preset block.message.slot →
        update.nextSyncCommittee = SyncCommittee.empty preset ∧
        update.nextSyncCommitteeBranch = Vector.replicate _ zeroBytes32) ∧
      (finalizedBlock = none → update.finalizedHeader = LightClientHeader.empty preset fork ∧
        update.finalityBranch = Vector.replicate _ zeroBytes32) ∧
      (∀ finalized, finalizedBlock = some finalized →
        (∃ gindex, finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
            attestedState.slot = .ok gindex ∧
          computeMerkleProof attestedState gindex = .ok update.finalityBranch.toList) ∧
        ((finalized.message.slot ≠ GENESIS_SLOT ∧ ∃ header,
            blockToLightClientHeader config finalized = .ok header ∧
            SszType.hashTreeRoot header.beacon = .ok attestedState.finalizedCheckpoint.root ∧
            header.upgrade config fork finalizedEarlier = .ok update.finalizedHeader) ∨
          (finalized.message.slot = GENESIS_SLOT ∧
            attestedState.finalizedCheckpoint.root = zeroBytes32 ∧
            update.finalizedHeader = LightClientHeader.empty preset fork))) := by
  unfold createLightClientUpdate at created
  simp only [bind_ok_iff] at created
  obtain ⟨⟨altair⟩, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -,
    rest⟩ := created
  refine ⟨altair, ?_⟩
  split at rest <;> rename_i period
  · -- The attested period signs: the update carries the next committee and its branch.
    simp only [bind_ok_iff] at rest
    obtain ⟨gindex, indexed, nodes, proved, branch, vectored, pair, paired, rest⟩ := rest
    simp only [pure, Except.pure, Except.ok.injEq] at paired
    subst paired
    have proved := LightClientError.liftRoot_ok.mp proved
    rcases finalizedBlock with _ | finalized
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
      obtain ⟨_, rfl, attested, made, rfl⟩ := rest
      refine ⟨made, fun _ => ⟨rfl, gindex, indexed, ?_⟩, fun differ => absurd period differ,
        fun _ => ⟨rfl, rfl⟩, nofun⟩
      rw [branchVector_ok_iff.mp vectored]
      exact proved
    · dsimp only at rest
      split at rest <;> rename_i genesis
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
        obtain ⟨header, made, headerRoot, rooted, _, same, upgraded, upgradedOk, findex, findexed,
          fnodes, fproved, fbranch, fvectored, _, rfl, attested, attestedOk, rfl⟩ := rest
        obtain rfl := LightClientError.require_ok.mp same
        refine ⟨attestedOk, (fun _ => ⟨rfl, gindex, indexed,
            by rw [branchVector_ok_iff.mp vectored]; exact proved⟩),
            (fun differ => absurd period differ),
          nofun, fun _ picked => ?_⟩
        cases picked
        refine ⟨⟨findex, findexed, ?_⟩, .inl ⟨genesis, header, made,
          LightClientError.liftRoot_ok.mp rooted, upgradedOk⟩⟩
        rw [branchVector_ok_iff.mp fvectored]
        exact LightClientError.liftRoot_ok.mp fproved
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at rest
        obtain ⟨_, zero, _, rfl, findex, findexed, fnodes, fproved, fbranch, fvectored, _, rfl,
          attested, attestedOk, rfl⟩ := rest
        refine ⟨attestedOk, (fun _ => ⟨rfl, gindex, indexed,
            by rw [branchVector_ok_iff.mp vectored]; exact proved⟩),
            (fun differ => absurd period differ),
          nofun, fun _ picked => ?_⟩
        cases picked
        refine ⟨⟨findex, findexed, ?_⟩, .inr ⟨Classical.not_not.mp genesis,
          LightClientError.require_ok.mp zero, rfl⟩⟩
        rw [branchVector_ok_iff.mp fvectored]
        exact LightClientError.liftRoot_ok.mp fproved
  · -- Another period signs: the update carries no committee.
    simp only [pure, Except.pure, bind_ok_iff] at rest
    obtain ⟨pair, paired, rest⟩ := rest
    simp only [Except.ok.injEq] at paired
    subst paired
    rcases finalizedBlock with _ | finalized
    · simp only [bind_ok_iff, Except.ok.injEq] at rest
      obtain ⟨_, rfl, attested, made, rfl⟩ := rest
      exact ⟨made, fun same => absurd same period, fun _ => ⟨rfl, rfl⟩, fun _ => ⟨rfl, rfl⟩,
        nofun⟩
    · dsimp only at rest
      split at rest <;> rename_i genesis
      · simp only [bind_ok_iff, Except.ok.injEq] at rest
        obtain ⟨header, made, headerRoot, rooted, _, same, upgraded, upgradedOk, findex, findexed,
          fnodes, fproved, fbranch, fvectored, _, rfl, attested, attestedOk, rfl⟩ := rest
        obtain rfl := LightClientError.require_ok.mp same
        refine ⟨attestedOk, (fun same => absurd same period), (fun _ => ⟨rfl, rfl⟩),
          nofun, fun _ picked => ?_⟩
        cases picked
        refine ⟨⟨findex, findexed, ?_⟩, .inl ⟨genesis, header, made,
          LightClientError.liftRoot_ok.mp rooted, upgradedOk⟩⟩
        rw [branchVector_ok_iff.mp fvectored]
        exact LightClientError.liftRoot_ok.mp fproved
      · simp only [bind_ok_iff, Except.ok.injEq] at rest
        obtain ⟨_, zero, _, rfl, findex, findexed, fnodes, fproved, fbranch, fvectored, _, rfl,
          attested, attestedOk, rfl⟩ := rest
        refine ⟨attestedOk, (fun same => absurd same period), (fun _ => ⟨rfl, rfl⟩),
          nofun, fun _ picked => ?_⟩
        cases picked
        refine ⟨⟨findex, findexed, ?_⟩, .inr ⟨Classical.not_not.mp genesis,
          LightClientError.require_ok.mp zero, rfl⟩⟩
        rw [branchVector_ok_iff.mp fvectored]
        exact LightClientError.liftRoot_ok.mp fproved

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- A light client header comes only from a block from Altair. -/
theorem blockToLightClientHeader_altair {config : Config} {block : SignedBeaconBlock preset fork}
    {header : LightClientHeader preset fork}
    (made : blockToLightClientHeader config block = .ok header) : .altair ≤ fork := by
  unfold blockToLightClientHeader at made
  obtain ⟨⟨altair⟩, -, -⟩ := bind_ok_iff.mp made
  exact altair

/-- The finality of an update that a full node builds passes the check of the client.

The attested and finalized blocks must be of the forks of their slots.

The attested state must be the post state of the attested block, at its slot.

An update with a finalized block must also prove finality: its branch is not all zero. -/
theorem createLightClientUpdate_finality [LawfulSszType (BeaconState preset fork)]
    {config : Config} {signatureFork finalizedFork : Fork}
    {state : BeaconState preset signatureFork} {block : SignedBeaconBlock preset signatureFork}
    {attestedState : BeaconState preset fork} {attestedBlock : SignedBeaconBlock preset fork}
    {finalizedBlock : Option (SignedBeaconBlock preset finalizedFork)}
    {finalizedEarlier : finalizedFork ≤ fork} {update : LightClientUpdate preset fork}
    (attestedScheduled : config.SlotOfFork preset fork attestedBlock.message.slot)
    (attestedAtSlot : attestedBlock.message.slot = attestedState.slot)
    (attestedRooted : SszType.hashTreeRoot attestedState = .ok attestedBlock.message.stateRoot)
    (finalizedScheduled : ∀ finalized, finalizedBlock = some finalized →
      config.SlotOfFork preset finalizedFork finalized.message.slot)
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH)
    (finalityProved : finalizedBlock.isSome → update.isFinalityUpdate = true)
    (created : createLightClientUpdate config state block attestedState attestedBlock
      finalizedBlock finalizedEarlier = .ok update) :
    validateFinality config update = .ok () := by
  obtain ⟨altair, attestedMade, -, -, none, some⟩ := createLightClientUpdate_shape created
  obtain ⟨bodyRoot, -, attestedBeacon⟩ := blockToLightClientHeader_beacon attestedMade
  rcases finalizedBlock with _ | finalized
  · obtain ⟨header, branch⟩ := none rfl
    unfold validateFinality
    simp [LightClientUpdate.isFinalityUpdate, header, branch, sameSszValue,
      LightClientError.require]
  obtain ⟨⟨gindex, indexed, proved⟩, chosen⟩ := some finalized rfl
  have finality := finalityProved rfl
  obtain ⟨finalizedIndex, -, -⟩ := lightClientGindices_of_slotOfFork altair attestedScheduled
  rw [attestedAtSlot, indexed] at finalizedIndex
  cases finalizedIndex
  have named : 2 ≤ finalizedRootGindex fork := by
    unfold finalizedRootGindex; split <;> (try split) <;> decide
  -- The node of the finality branch is the finalized root of the attested state.
  obtain ⟨node, nodeRooted⟩ := SszType.hashTreeRoot_total attestedState.finalizedCheckpoint.root
  obtain ⟨root, honest, honestRooted, honestBuilt, climbs⟩ :=
    computeMerkleProof_isValidNormalizedMerkleBranch attestedState named
      (BeaconState.nodeRoot_finalizedCheckpoint_root altair attestedState nodeRooted)
  rw [attestedRooted] at honestRooted
  cases honestRooted
  rw [proved] at honestBuilt
  cases honestBuilt
  have chunk : node = attestedState.finalizedCheckpoint.root := by
    have direct : SszType.hashTreeRoot attestedState.finalizedCheckpoint.root =
        .ok attestedState.finalizedCheckpoint.root :=
      SszType.hashTreeRoot_ok_iff.mpr (hashTreeRoot_chunk (by simp [bytesPerChunk]))
    rw [direct] at nodeRooted
    exact (Except.ok.inj nodeRooted).symm
  subst chunk
  have attestedIndex : finalizedRootGindexAtSlot (preset := preset) (fork := fork) config
      update.attestedHeader.beacon.slot = .ok (finalizedRootGindex fork) := by
    rw [attestedBeacon, attestedAtSlot, indexed]
  have attestedRoot : update.attestedHeader.beacon.stateRoot = attestedBlock.message.stateRoot := by
    rw [attestedBeacon]
  unfold validateFinality
  rcases chosen with ⟨later, header, made, headerRooted, upgraded⟩ | ⟨genesis, zero, empty⟩
  · -- A later finalized block gives its header, valid once upgraded, with its root as the leaf.
    have beacon := LightClientHeader.upgrade_beacon upgraded
    obtain ⟨_, -, finalizedBeacon⟩ := blockToLightClientHeader_beacon made
    have slot : header.beacon.slot ≠ GENESIS_SLOT := by
      rw [finalizedBeacon]; exact later
    have valid := LightClientHeader.upgrade_valid
      (blockToLightClientHeader_valid (finalizedScheduled finalized rfl) made)
      (by rw [finalizedBeacon]; exact finalizedScheduled finalized rfl)
      (by rw [finalizedBeacon]; exact later) ordered (blockToLightClientHeader_altair made)
      upgraded
    simp [finality, slot, valid, beacon, headerRooted, attestedIndex, attestedRoot, climbs,
      LightClientError.require, LightClientError.liftRoot, Except.mapError, bind, Except.bind]
  · -- The genesis block gives the zero header and the zero root, which the state holds.
    rw [zero] at climbs
    simp [finality, empty, LightClientHeader.empty, GENESIS_SLOT, sameSszValue, attestedIndex,
      attestedRoot, climbs, LightClientError.require, LightClientError.liftRoot, Except.mapError,
      bind, Except.bind, pure, Except.pure]

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat]
  [NeZero preset.PTC_SIZE.toNat] [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- An update whose attested and signing blocks share a period proves the next committee.

The committee is the next committee of the attested state, and its branch passes the check. -/
theorem createLightClientUpdate_nextSyncCommittee [LawfulSszType (BeaconState preset fork)]
    {config : Config} {signatureFork finalizedFork : Fork}
    {state : BeaconState preset signatureFork} {block : SignedBeaconBlock preset signatureFork}
    {attestedState : BeaconState preset fork} {attestedBlock : SignedBeaconBlock preset fork}
    {finalizedBlock : Option (SignedBeaconBlock preset finalizedFork)}
    {finalizedEarlier : finalizedFork ≤ fork} {update : LightClientUpdate preset fork}
    (attestedScheduled : config.SlotOfFork preset fork attestedBlock.message.slot)
    (attestedAtSlot : attestedBlock.message.slot = attestedState.slot)
    (attestedRooted : SszType.hashTreeRoot attestedState = .ok attestedBlock.message.stateRoot)
    (samePeriod : computeSyncCommitteePeriodAtSlot preset attestedBlock.message.slot =
      computeSyncCommitteePeriodAtSlot preset block.message.slot)
    (created : createLightClientUpdate config state block attestedState attestedBlock
      finalizedBlock finalizedEarlier = .ok update) :
    update.nextSyncCommittee = (attestedState.nextSyncCommittee
        (blockToLightClientHeader_altair (createLightClientUpdate_shape created).2.1)).value ∧
      validateNextSyncCommitteeBranch config update = .ok () := by
  obtain ⟨altair, attestedMade, committee, -, -, -⟩ := createLightClientUpdate_shape created
  obtain ⟨value, gindex, indexed, proved⟩ := committee samePeriod
  obtain ⟨bodyRoot, -, attestedBeacon⟩ := blockToLightClientHeader_beacon attestedMade
  refine ⟨value, ?_⟩
  obtain ⟨-, -, nextIndex⟩ := lightClientGindices_of_slotOfFork altair attestedScheduled
  rw [attestedAtSlot, indexed] at nextIndex
  cases nextIndex
  obtain ⟨leaf, leafRooted⟩ := SszType.hashTreeRoot_total (attestedState.nextSyncCommittee altair)
  obtain ⟨root, honest, honestRooted, honestBuilt, climbs⟩ :=
    computeMerkleProof_isValidNormalizedMerkleBranch attestedState
      (by unfold nextSyncCommitteeGindex; split <;> (try split) <;> decide)
      (BeaconState.nodeRoot_nextSyncCommittee altair attestedState leafRooted)
  rw [attestedRooted] at honestRooted
  cases honestRooted
  rw [proved] at honestBuilt
  cases honestBuilt
  rw [Rooted.hashTreeRoot_value] at leafRooted
  have attestedIndex : nextSyncCommitteeGindexAtSlot (preset := preset) (fork := fork) config
      attestedBlock.message.slot = .ok (nextSyncCommitteeGindex fork) := by
    rw [attestedAtSlot, indexed]
  unfold validateNextSyncCommitteeBranch
  simp [value, leafRooted, attestedIndex, attestedBeacon, climbs, LightClientError.require,
    LightClientError.liftRoot, Except.mapError, bind, Except.bind]

/-- A store accepts an update that a full node builds, under the natural hypotheses.

The blocks must be of the forks of their slots, and the attested state the post state of its block.

The signing block comes after the attested block, and no later than the current slot.

The finalized block comes no later than the attested block.

A built branch that the update carries must not be all zero.

That fails only if SHA-256 maps some message to the zero root.

The store must know the committee of the signing period, and finalize an earlier slot.

A next committee that the store knows must be the one that the update proves, in that period.

The signature check must accept the participants of the committee on the signing root. -/
theorem createLightClientUpdate_accepted [LawfulSszType (BeaconState preset fork)]
    {config : Config} {checks : SignatureChecks} {signatureFork finalizedFork : Fork}
    {state : BeaconState preset signatureFork} {block : SignedBeaconBlock preset signatureFork}
    {attestedState : BeaconState preset fork} {attestedBlock : SignedBeaconBlock preset fork}
    {finalizedBlock : Option (SignedBeaconBlock preset finalizedFork)}
    {finalizedEarlier : finalizedFork ≤ fork} {update : LightClientUpdate preset fork}
    {store : LightClientStore preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (attestedScheduled : config.SlotOfFork preset fork attestedBlock.message.slot)
    (attestedAtSlot : attestedBlock.message.slot = attestedState.slot)
    (attestedRooted : SszType.hashTreeRoot attestedState = .ok attestedBlock.message.stateRoot)
    (finalizedScheduled : ∀ finalized, finalizedBlock = some finalized →
      config.SlotOfFork preset finalizedFork finalized.message.slot ∧
        finalized.message.slot ≤ attestedBlock.message.slot)
    (ordered : config.CAPELLA_FORK_EPOCH ≤ config.DENEB_FORK_EPOCH)
    (signedLater : attestedBlock.message.slot < block.message.slot)
    (arrived : block.message.slot ≤ currentSlot)
    (finalityProved : finalizedBlock.isSome → update.isFinalityUpdate = true)
    (committeeProved : computeSyncCommitteePeriodAtSlot preset attestedBlock.message.slot =
      computeSyncCommitteePeriodAtSlot preset block.message.slot →
      update.isSyncCommitteeUpdate = true)
    (knownPeriod : computeSyncCommitteePeriodAtSlot preset block.message.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot ∨
      store.isNextSyncCommitteeKnown = true ∧
        computeSyncCommitteePeriodAtSlot preset block.message.slot =
          computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1)
    (newer : store.finalizedHeader.beacon.slot < attestedBlock.message.slot)
    (agrees : update.isSyncCommitteeUpdate = true →
      computeSyncCommitteePeriodAtSlot preset attestedBlock.message.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot →
      store.isNextSyncCommitteeKnown = true → update.nextSyncCommittee = store.nextSyncCommittee)
    (signed : ∃ signingRoot,
      syncCommitteeSigningRoot config update genesisValidatorsRoot = .ok signingRoot ∧
      checks.fastAggregateVerify
        (((store.signatureCommittee update).participantKeys update.syncAggregate).map packBytes)
        (packBytes signingRoot) (packBytes update.syncAggregate.syncCommitteeSignature) = true)
    (created : createLightClientUpdate config state block attestedState attestedBlock
      finalizedBlock finalizedEarlier = .ok update) :
    validateLightClientUpdate config checks store update currentSlot genesisValidatorsRoot =
      .ok () := by
  obtain ⟨altair, attestedMade, -, apart, noneCase, someCase⟩ :=
    createLightClientUpdate_shape created
  obtain ⟨signatureSlot, participants⟩ := createLightClientUpdate_signature created
  obtain ⟨bodyRoot, -, attestedBeacon⟩ := blockToLightClientHeader_beacon attestedMade
  have attestedValid := blockToLightClientHeader_valid attestedScheduled attestedMade
  have finality := createLightClientUpdate_finality attestedScheduled attestedAtSlot
    attestedRooted (fun f picked => (finalizedScheduled f picked).1) ordered finalityProved created
  -- The finalized slot is at most the attested slot: zero, or that of the finalized block.
  have finalizedSlot : update.finalizedHeader.beacon.slot ≤ attestedBlock.message.slot := by
    rcases finalizedBlock with _ | finalized
    · rw [(noneCase rfl).1]
      exact UInt64.zero_le
    · rcases (someCase finalized rfl).2 with ⟨-, header, made, -, upgraded⟩ | ⟨-, -, empty⟩
      · rw [LightClientHeader.upgrade_beacon upgraded]
        obtain ⟨_, -, beacon⟩ := blockToLightClientHeader_beacon made
        rw [beacon]
        exact (finalizedScheduled finalized rfl).2
      · rw [empty]
        exact UInt64.zero_le
  obtain ⟨signingRoot, signingOk, verified⟩ := signed
  unfold validateLightClientUpdate
  simp only [LightClientError.requireFork, altair, ↓reduceIte, bind, Except.bind,
    LightClientError.require, participants, attestedValid, attestedBeacon, signatureSlot,
    finality, signingOk, verified]
  -- With a committee branch the periods match, and the branch proves the committee.
  have committee : update.isSyncCommitteeUpdate = true →
      validateNextSyncCommitteeBranch config update = .ok () := fun proving => by
    by_cases same : computeSyncCommitteePeriodAtSlot preset attestedBlock.message.slot =
        computeSyncCommitteePeriodAtSlot preset block.message.slot
    · exact (createLightClientUpdate_nextSyncCommittee attestedScheduled attestedAtSlot
        attestedRooted same created).2
    · have zeros := (apart same).2
      simp [LightClientUpdate.isSyncCommitteeUpdate, zeros] at proving
  have noCommittee : update.isSyncCommitteeUpdate = false →
      update.nextSyncCommittee = SyncCommittee.empty preset := fun notProving => by
    by_cases same : computeSyncCommitteePeriodAtSlot preset attestedBlock.message.slot =
        computeSyncCommitteePeriodAtSlot preset block.message.slot
    · rw [committeeProved same] at notProving
      cases notProving
    · exact (apart same).1
  have ordering : currentSlot ≥ block.message.slot ∧
      block.message.slot > attestedBlock.message.slot ∧
      attestedBlock.message.slot ≥ update.finalizedHeader.beacon.slot :=
    ⟨arrived, signedLater, finalizedSlot⟩
  simp only [ordering, and_self, ↓reduceIte, gt_iff_lt, newer, true_or]
  cases known : store.isNextSyncCommitteeKnown
  · have period := knownPeriod.resolve_right (by simp [known])
    cases proving : update.isSyncCommitteeUpdate
    · simp [period, noCommittee proving]
    · simp [period, committee proving]
  · have period : computeSyncCommitteePeriodAtSlot preset block.message.slot =
          computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot ∨
        computeSyncCommitteePeriodAtSlot preset block.message.slot =
          computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1 :=
      knownPeriod.imp_right And.right
    cases proving : update.isSyncCommitteeUpdate
    · simp [period, noCommittee proving]
    · by_cases same : computeSyncCommitteePeriodAtSlot preset attestedBlock.message.slot =
          computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot
      · simp [period, committee proving, same, agrees proving same known]
      · simp [period, committee proving, same]

omit [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat] in
/-- The hypothesis that a block is of the fork of its slot is needed.

A block of Gloas at a slot before Capella, Deneb and Gloas gives a header that fails the check.

It does so whenever the parent block hash of its bid is not zero. -/
theorem blockToLightClientHeader_invalid_of_early {config : Config}
    {block : SignedBeaconBlock preset fork} {header : LightClientHeader preset fork}
    (gloas : .glamsterdam ≤ fork)
    (early : computeEpochAtSlot preset block.message.slot < config.CAPELLA_FORK_EPOCH)
    (beforeDeneb : computeEpochAtSlot preset block.message.slot < config.DENEB_FORK_EPOCH)
    (beforeGloas : computeEpochAtSlot preset block.message.slot < config.GLOAS_FORK_EPOCH)
    (nonzero : (block.message.body.signedExecutionPayloadBid gloas).message.parentBlockHash ≠
      zeroBytes32)
    (made : blockToLightClientHeader config block = .ok header) :
    isValidLightClientHeader config header = .ok false := by
  unfold blockToLightClientHeader at made
  simp only [bind_ok_iff] at made
  obtain ⟨⟨altair⟩, -, bodyRoot, -, rest⟩ := made
  simp only [gloas, ↓reduceDIte, bind_ok_iff] at rest
  obtain ⟨nodes, -, branch, -, built⟩ := rest
  cases built
  unfold isValidLightClientHeader
  simp [LightClientError.requireFork, altair, gloas, UInt64.not_le.mpr early,
    UInt64.not_le.mpr beforeDeneb, UInt64.not_le.mpr beforeGloas, nonzero, bind, Except.bind,
    pure, Except.pure]
