module

public import EthLib.Consensus.Proofs.Transition.Invariants
public import EthLib.Consensus.Transition.Genesis

/-!
# Proofs: the genesis of the beacon chain

A candidate genesis state satisfies the invariant that each valid block keeps before Altair.

Its registry and balances have one entry for each validator.

Each of its validators may withdraw no earlier than it exits.

Its checkpoints all have the genesis epoch, so they are in order and settled.

A candidate state launches the chain exactly when it is late enough.

It must also have enough active validators.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The empty state before the deposits satisfies the invariant. -/
theorem emptyGenesisState_invariant (before : fork < .altair) (genesisTime : UInt64)
    (eth1BlockHash : Hash32) (depositCount : UInt64) (bodyRoot : Root) :
    Invariant (emptyGenesisState (preset := preset) config before genesisTime eth1BlockHash
      depositCount bodyRoot) where
  balancesMatch := rfl
  exitsOrdered := fun _ member => by simp [emptyGenesisState] at member
  ordered := ⟨UInt64.le_refl _, UInt64.le_refl _⟩
  settled := UInt64.zero_le
  effectiveBalancesBounded := fun _ member => by simp [emptyGenesisState] at member

theorem frame_genesisDeposit (altair : fork < .altair) {before : fork < .hegota}
    {leaves : Array DepositData}
    {entry : Deposit × Nat}
    (computed : genesisDeposit config checks before leaves state entry = .ok after) :
    Frame state after := by
  simp only [genesisDeposit, bind_ok_iff] at computed
  obtain ⟨depositRoot, _, deposited⟩ := computed
  exact (Frame.of_validators (state := state)
    (after := { state with eth1Data := fun _ => { state.eth1Data before with depositRoot } })
    ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl).trans (frame_processDeposit altair deposited)

/-- Setting the effective balance and the activation at genesis changes no exit. -/
theorem frame_activateAtGenesis {index : Nat}
    (computed : activateAtGenesis state index = .ok after) : Frame state after := by
  simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, _, rfl⟩ := computed
  apply frame_setValidator
  · intro ordered
    have le := ordered validator (mem_of_getValidator found)
    split <;> exact le
  · intro _
    split <;> exact Std.min_le_right

/-- A candidate genesis state satisfies the invariant that each valid block keeps before Altair.

The theorems on the state transition then apply to every chain that starts from it. -/
theorem initializeBeaconStateFromEth1_invariant {eth1BlockHash : Hash32} {eth1Timestamp : UInt64}
    {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    fork < .altair ∧ Invariant after := by
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  rename_i altair
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, rfl⟩ :=
    computed
  have before : fork < .altair := Nat.lt_of_not_le altair
  refine ⟨before, ?_⟩
  have frame := (Frame.foldlM (fun _ _ _ ok => frame_genesisDeposit before ok) depositedOk).trans
    (Frame.foldlM (fun _ _ _ ok => frame_activateAtGenesis ok) activatedOk)
  have rooted : Frame activated { activated with genesisValidatorsRoot := root } :=
    Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl
  exact rooted.invariant (frame.invariant (emptyGenesisState_invariant before _ _ _ _))

/-- Genesis initialization leaves both pending-attestation lists empty and checkpoints equal. -/
theorem initializeBeaconStateFromEth1_pending_empty {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (before : fork < .altair)
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    (after.currentEpochAttestations before).data = #[] ∧
    (after.previousEpochAttestations before).data = #[] ∧
    after.currentJustifiedCheckpoint = after.previousJustifiedCheckpoint := by
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, rfl⟩ :=
    computed
  have depositsKeep : ∀ (s : BeaconState preset fork) (entry : Deposit × Nat) s',
      genesisDeposit config checks (Nat.lt_trans before (by decide))
        (deposits.map (·.data)) s entry = .ok s' → PendingUnchanged s s' before := by
    intro s entry s' applied
    simp only [genesisDeposit, bind_ok_iff] at applied
    obtain ⟨_, _, applied⟩ := applied
    have pending := pendingUnchanged_processDeposit before applied
    exact ⟨pending.current, pending.previous⟩
  have activationsKeep : ∀ (s : BeaconState preset fork) index s',
      activateAtGenesis s index = .ok s' →
      PendingUnchanged s s' before := by
    intro s index s' applied
    simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at applied
    obtain ⟨_, _, _, _, rfl⟩ := applied
    split <;> exact ⟨rfl, rfl⟩
  have pending := (PendingUnchanged.foldlM depositsKeep depositedOk).trans
    (PendingUnchanged.foldlM activationsKeep activatedOk)
  have frame := (Frame.foldlM (fun _ _ _ ok => frame_genesisDeposit before ok) depositedOk).trans
    (Frame.foldlM (fun _ _ _ ok => frame_activateAtGenesis ok) activatedOk)
  exact ⟨congrArg (·.data) pending.current, congrArg (·.data) pending.previous,
    frame.currentJustified.trans frame.previousJustified.symm⟩

/-- Genesis initialization sets every justification bit to false.

Neither deposits nor activation at genesis can introduce justification evidence. -/
theorem initializeBeaconStateFromEth1_bits {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (before : fork < .altair)
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) (index : Fin 4) : after.justificationBits.bits[index] = false := by
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, rfl⟩ :=
    computed
  have frame := (Frame.foldlM (fun _ _ _ ok => frame_genesisDeposit before ok) depositedOk).trans
    (Frame.foldlM (fun _ _ _ ok => frame_activateAtGenesis ok) activatedOk)
  change activated.justificationBits.bits[index] = false
  rw [frame.justificationBits]
  simp [emptyGenesisState]

/-- Genesis initialization satisfies the source condition without any pending attestations. -/
theorem initializeBeaconStateFromEth1_pending_sources {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (before : fork < .altair)
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) : PendingSourcesInvariant after before := by
  obtain ⟨current, previous, equal⟩ :=
    initializeBeaconStateFromEth1_pending_empty before computed
  refine ⟨⟨?_, ?_⟩, fun _ => equal⟩
  · intro entry member
    simp [current] at member
  · intro entry member
    simp [previous] at member

/-- Every pending record on an initialized chain comes from a successful block inclusion.

The witness retains the actual inclusion state rather than reconstructing its committee. -/
theorem pendingIncludedInBlock_of_initialized_chain
    {engine : ExecutionEngine preset fork} {genesis : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset fork)} {pending : PendingAttestation preset}
    (before : fork < .altair)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (member : pending ∈ (after.currentEpochAttestations before).data ∨
      pending ∈ (after.previousEpochAttestations before).data) :
    ∃ earlier block later atBlock atSlot,
      blocks = earlier ++ block :: later ∧
      earlier.foldlM
        (fun state block => stateTransition config checks engine state block true)
          genesis = .ok atBlock ∧
      processSlots config atBlock block.message.slot = .ok atSlot ∧
      PendingIncludedInBlock config checks before atSlot block.message pending := by
  rcases stateTransition_chain_pending_origin before computed member with old | included
  · obtain ⟨current, previous, _⟩ :=
      initializeBeaconStateFromEth1_pending_empty before initialized
    simp [current, previous] at old
  · exact included

/-- Target matching on an initialized chain counts only records included by successful processing.

The source and target roots are the checkpoints that the concrete matching query selects. -/
theorem matchingTarget_included_of_initialized_chain
    {engine : ExecutionEngine preset fork} {genesis : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset fork)} {pending : PendingAttestation preset}
    {epoch : Epoch} {attestations : Array (PendingAttestation preset)}
    (before : fork < .altair)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (matching : getMatchingTargetAttestations after before epoch = .ok attestations)
    (member : pending ∈ attestations) :
    ∃ earlier block later atBlock atSlot root,
      blocks = earlier ++ block :: later ∧
      earlier.foldlM
        (fun state block => stateTransition config checks engine state block true)
          genesis = .ok atBlock ∧
      processSlots config atBlock block.message.slot = .ok atSlot ∧
      PendingIncludedInBlock config checks before atSlot block.message pending ∧
      getBlockRoot after epoch = .ok root ∧ pending.data.target.root = root := by
  obtain ⟨sources, root, sourceOk, rootOk, sourceMember, rootEq⟩ :=
    getMatchingTargetAttestations_mem matching member
  have pendingMember : pending ∈ (after.currentEpochAttestations before).data ∨
      pending ∈ (after.previousEpochAttestations before).data := by
    simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
      Except.ok.injEq] at sourceOk
    obtain ⟨_, _, rfl⟩ := sourceOk
    split at sourceMember
    · exact .inl sourceMember
    · exact .inr sourceMember
  obtain ⟨earlier, block, later, atBlock, atSlot, split, earlierOk, slots, included⟩ :=
    pendingIncludedInBlock_of_initialized_chain before initialized computed pendingMember
  exact ⟨earlier, block, later, atBlock, atSlot, root, split, earlierOk, slots, included,
    rootOk, rootEq⟩

/-- Every initialized Phase 0 chain retains the sources checked during attestation inclusion.

No participation or checkpoint hypothesis is required from the caller. -/
theorem pendingSourcesMatch_of_initialized_chain
    {engine : ExecutionEngine preset fork} {genesis : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset fork)}
    (before : fork < .altair)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after) : PendingSourcesMatch after before := by
  have holds := initializeBeaconStateFromEth1_pending_sources before initialized
  exact (foldlM_ok_invariant (fun s => PendingSourcesInvariant s before)
    (fun _ _ _ prior ok => stateTransition_pending_sources before prior ok) holds computed).1

/-- Genesis initialization contains no pending attestations with an incorrect epoch. -/
theorem initializeBeaconStateFromEth1_pending_epochs {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (before : fork < .altair)
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) : PendingEpochsMatch after before := by
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, rfl⟩ :=
    computed
  have depositsKeep : ∀ (s : BeaconState preset fork) (entry : Deposit × Nat) s',
      genesisDeposit config checks (Nat.lt_trans before (by decide))
        (deposits.map (·.data)) s entry = .ok s' → PendingUnchanged s s' before := by
    intro s entry s' applied
    simp only [genesisDeposit, bind_ok_iff] at applied
    obtain ⟨_, _, applied⟩ := applied
    have pending := pendingUnchanged_processDeposit before applied
    exact ⟨pending.current, pending.previous⟩
  have activationsKeep : ∀ (s : BeaconState preset fork) index s',
      activateAtGenesis s index = .ok s' → PendingUnchanged s s' before := by
    intro s index s' applied
    simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at applied
    obtain ⟨_, _, _, _, rfl⟩ := applied
    split <;> exact ⟨rfl, rfl⟩
  have pending := (PendingUnchanged.foldlM depositsKeep depositedOk).trans
    (PendingUnchanged.foldlM activationsKeep activatedOk)
  constructor
  · intro entry member
    rw [pending.current] at member
    simp [emptyGenesisState] at member
  · intro entry member
    rw [pending.previous] at member
    simp [emptyGenesisState] at member

/-- Every initialized chain retains the target and slot epochs checked at inclusion. -/
theorem pendingEpochsMatch_of_initialized_chain
    {engine : ExecutionEngine preset fork} {genesis : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset fork)}
    (before : fork < .altair)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after) : PendingEpochsMatch after before := by
  exact foldlM_ok_invariant (fun s => PendingEpochsMatch s before)
    (fun _ _ _ prior ok => stateTransition_pending_epochs before prior ok)
    (initializeBeaconStateFromEth1_pending_epochs before initialized) computed

/-- The pending invariants hold at the cached state where an epoch weighs attestations.

The slot prefix may stop inside the empty slots before the next block. -/
theorem pending_invariants_at_cached_slot_of_initialized_chain
    {engine : ExecutionEngine preset fork} {genesis atStep cached : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset fork)} {count : Nat}
    (before : fork < .altair)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (advanced : advanceSlots config count after = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached) :
    PendingSourcesMatch cached before ∧ PendingEpochsMatch cached before := by
  have sources := foldlM_ok_invariant (fun s => PendingSourcesInvariant s before)
    (fun _ _ _ prior ok => stateTransition_pending_sources before prior ok)
    (initializeBeaconStateFromEth1_pending_sources before initialized) computed
  have atSources := (advanceSlots_pending_sources before count sources advanced).1
  have atEpochs := advanceSlots_pending_epochs before count
    (pendingEpochsMatch_of_initialized_chain before initialized computed) advanced
  have pending := pendingUnchanged_processSlot (before := before) cachedOk
  have frame := frame_processSlot cachedOk
  exact ⟨pending.sources frame atSources, pending.epochs frame atEpochs⟩

/-- A record counted at an epoch boundary was included in a preceding successful block.

Neither the empty slot prefix nor root caching can create a pending record. -/
theorem pendingIncluded_at_cached_slot_of_initialized_chain
    {engine : ExecutionEngine preset fork} {genesis atStep cached : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset fork)} {count : Nat}
    {pending : PendingAttestation preset}
    (before : fork < .altair)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (advanced : advanceSlots config count after = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (member : pending ∈ (cached.currentEpochAttestations before).data ∨
      pending ∈ (cached.previousEpochAttestations before).data) :
    ∃ earlier block later atBlock atSlot,
      blocks = earlier ++ block :: later ∧
      earlier.foldlM
        (fun state block => stateTransition config checks engine state block true)
          genesis = .ok atBlock ∧
      processSlots config atBlock block.message.slot = .ok atSlot ∧
      PendingIncludedInBlock config checks before atSlot block.message pending := by
  have kept := pendingUnchanged_processSlot (before := before) cachedOk
  have atMember := (kept.mem_iff pending).mp member
  exact pendingIncludedInBlock_of_initialized_chain before initialized computed
    (advanceSlots_pending_mem before count advanced atMember)

/-- A current justification bit on an initialized chain has concrete included target attesters.

Their reconstructed indices belong to the current active denominator.

The threshold retains the exact minimum-increment correction.

This does not yet identify reconstructed indices with those authenticated at inclusion. -/
theorem currentJustification_included_of_initialized_chain
    {engine : ExecutionEngine preset fork} {genesis justified : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset fork)}
    (before : fork < .altair)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (weighed : processJustificationAndFinalization after = .ok justified)
    (eligible : ¬getCurrentEpoch after ≤ GENESIS_EPOCH + 1)
    (bit : justified.justificationBits.bits[0] = true) :
    ∃ attestations indices,
      getMatchingTargetAttestations after before (getCurrentEpoch after) = .ok attestations ∧
      getUnslashedAttestingIndices after attestations = .ok indices ∧
      2 * sumMarked after.validators.data
          (markIndices after.validators.data.size
            (getActiveValidatorIndices after (getCurrentEpoch after))) ≤
        3 * sumMarked after.validators.data (markIndices after.validators.data.size indices) +
          3 * totalBalanceFloor after indices ∧
      ∀ index ∈ indices,
        index ∈ getActiveValidatorIndices after (getCurrentEpoch after) ∧
        ∃ pending ∈ attestations, ∃ signers earlier block later atBlock atSlot,
          getPendingAttestingIndices after pending = .ok signers ∧ index ∈ signers ∧
          pending.data.source = after.currentJustifiedCheckpoint ∧
          pending.data.target.epoch = getCurrentEpoch after ∧
          blocks = earlier ++ block :: later ∧
          earlier.foldlM
            (fun state block => stateTransition config checks engine state block true)
              genesis = .ok atBlock ∧
          processSlots config atBlock block.message.slot = .ok atSlot ∧
          PendingIncludedInBlock config checks before atSlot block.message pending := by
  have sources := pendingSourcesMatch_of_initialized_chain before initialized computed
  have epochs := pendingEpochsMatch_of_initialized_chain before initialized computed
  obtain ⟨attestations, indices, matching, indicesOk, threshold, witnesses⟩ :=
    processJustificationAndFinalization_current_bit_signers before weighed eligible bit sources
  refine ⟨attestations, indices, matching, indicesOk, threshold, ?_⟩
  intro index member
  have active := mem_getActiveValidatorIndices_of_current_target epochs matching indicesOk member
  obtain ⟨⟨pending, pendingMember, signers, _, signersOk, signer, source, _, _⟩, _⟩ :=
    witnesses index member
  obtain ⟨earlier, block, later, atBlock, atSlot, _, split, earlierOk, slots, included, _, _⟩ :=
    matchingTarget_included_of_initialized_chain before initialized computed matching pendingMember
  exact ⟨active, pending, pendingMember, signers, earlier, block, later, atBlock, atSlot,
    signersOk, signer, source,
    (getMatchingTargetAttestations_slot_epoch epochs matching pendingMember).1,
    split, earlierOk, slots, included⟩

/-- Pending signers on an initialized Phase 0 chain were checked at inclusion.

The reconstructed indices equal the sorted signer indices of the checked indexed attestation.

No committee-equality hypothesis is required from the caller. -/
theorem pending_signers_of_initialized_chain
    {engine : ExecutionEngine preset .phase0}
    {genesis after : BeaconState preset .phase0}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset .phase0)}
    {pending : PendingAttestation preset} {indices : List ValidatorIndex}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (member : pending ∈ (after.currentEpochAttestations (by decide)).data ∨
      pending ∈ (after.previousEpochAttestations (by decide)).data)
    (signers : getPendingAttestingIndices after pending = .ok indices) :
    ∃ (recorded : BeaconState preset .phase0)
      (attestation : Attestation preset .phase0)
      (indexed : IndexedAttestation preset .phase0),
      getIndexedAttestation recorded attestation = .ok indexed ∧
      indexed.attestingIndices.data = (sortedSet indices).toArray ∧
      indexed.data = pending.data ∧ indexed.signature = attestation.signature ∧
      isValidIndexedAttestation config checks recorded indexed = .ok true := by
  obtain ⟨earlier, block, later, atBlock, atSlot, split, earlierOk, slots, included⟩ :=
    pendingIncludedInBlock_of_initialized_chain (by decide) initialized computed member
  have epochs := pendingEpochsMatch_of_initialized_chain (by decide) initialized computed
  have recentAfter : (getCurrentEpoch after).toNat ≤
      (computeEpochAtSlot preset pending.data.slot).toNat + 1 := by
    rcases member with current | previous
    · rw [(epochs.1 pending current).2]
      omega
    · rw [(epochs.2 pending previous).2, getPreviousEpoch_toNat]
      omega
  obtain ⟨_, _, _, _, _, _, recent, _⟩ := included.committee positive history
  have past : computeEpochAtSlot preset pending.data.slot ≤ getCurrentEpoch atSlot := by
    rcases recent with current | previous
    · rw [current]
      exact UInt64.le_refl _
    · rw [UInt64.le_iff_toNat_le]
      omega
  rw [split, List.foldlM_append, earlierOk] at computed
  simp only [bind_ok_iff, List.foldlM_cons] at computed
  obtain ⟨_, first, afterBlock, blockOk, tail⟩ := computed
  cases first
  obtain ⟨advanced, advancedOk, _, _, processed, _⟩ := stateTransition_ok blockOk
  have equal : advanced = atSlot := Except.ok.inj (advancedOk.symm.trans slots)
  subst advanced
  have genesisInvariant := (initializeBeaconStateFromEth1_invariant initialized).2
  have beforeInvariant := foldlM_ok_invariant Invariant
    (fun _ _ _ prior ok => (stateTransition_invariant (by decide) prior ok).1)
    genesisInvariant earlierOk
  have atInvariant := (processSlots_invariant (by decide) beforeInvariant slots).1
  have afterInvariant := (frame_processBlock (by decide) processed).invariant atInvariant
  have blockFrame := frame_processBlock (by decide) processed
  have pastBlock : computeEpochAtSlot preset pending.data.slot ≤
      getCurrentEpoch afterBlock := by
    simpa only [getCurrentEpoch, blockFrame.slot] using past
  have tailCommittee := stateTransition_chain_committee
    (index := pending.data.index) positive history afterInvariant pastBlock recentAfter tail
  have blockCommittee := processBlock_committee
    (index := pending.data.index) positive history recent processed
  have atSigners : getPendingAttestingIndices atSlot pending = .ok indices := by
    simpa only [getPendingAttestingIndices, tailCommittee, blockCommittee] using signers
  exact included.signers positive history atSigners

/-- Signers reconstructed where an initialized Phase 0 chain weighs votes were checked at inclusion.

Empty slots and root caching preserve the committees of pending records that remain recent. -/
theorem pending_signers_at_cached_slot_of_initialized_chain
    {engine : ExecutionEngine preset .phase0}
    {genesis after atStep cached : BeaconState preset .phase0}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset .phase0)} {count : Nat}
    {pending : PendingAttestation preset} {indices : List ValidatorIndex}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (advanced : advanceSlots config count after = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (member : pending ∈ (cached.currentEpochAttestations (by decide)).data ∨
      pending ∈ (cached.previousEpochAttestations (by decide)).data)
    (signers : getPendingAttestingIndices cached pending = .ok indices) :
    ∃ (recorded : BeaconState preset .phase0)
      (attestation : Attestation preset .phase0)
      (indexed : IndexedAttestation preset .phase0),
      getIndexedAttestation recorded attestation = .ok indexed ∧
      indexed.attestingIndices.data = (sortedSet indices).toArray ∧
      indexed.data = pending.data ∧ indexed.signature = attestation.signature ∧
      isValidIndexedAttestation config checks recorded indexed = .ok true := by
  have frame := frame_processSlot cachedOk
  have kept := pendingUnchanged_processSlot (before := by decide) cachedOk
  have oldMember := advanceSlots_pending_mem (by decide) count advanced
    ((kept.mem_iff pending).mp member)
  have oldEpochs := pendingEpochsMatch_of_initialized_chain (by decide) initialized computed
  have cachedEpochs :=
    (pending_invariants_at_cached_slot_of_initialized_chain (by decide)
      initialized computed advanced cachedOk).2
  have past : computeEpochAtSlot preset pending.data.slot ≤ getCurrentEpoch after := by
    rcases oldMember with current | previous
    · rw [(oldEpochs.1 pending current).2]
      exact UInt64.le_refl _
    · rw [(oldEpochs.2 pending previous).2]
      exact getPreviousEpoch_le _
  have recent : (getCurrentEpoch atStep).toNat ≤
      (computeEpochAtSlot preset pending.data.slot).toNat + 1 := by
    have same : getCurrentEpoch cached = getCurrentEpoch atStep := by
      simp only [getCurrentEpoch, frame.slot]
    rcases member with current | previous
    · rw [(cachedEpochs.1 pending current).2, same]
      omega
    · rw [(cachedEpochs.2 pending previous).2, getPreviousEpoch_toNat, same]
      omega
  have invariant := foldlM_ok_invariant Invariant
    (fun _ _ _ prior ok => (stateTransition_invariant (by decide) prior ok).1)
    (initializeBeaconStateFromEth1_invariant initialized).2 computed
  have population := advanceSlots_active_indices (by decide) count invariant past advanced
  have seed := advanceSlots_attester_seed positive history count invariant past recent advanced
  have committee := getBeaconCommittee_congr (index := pending.data.index) population seed
  have cachedCommittee : getBeaconCommittee cached pending.data.slot pending.data.index =
      getBeaconCommittee atStep pending.data.slot pending.data.index := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have oldSigners : getPendingAttestingIndices after pending = .ok indices := by
    simpa only [getPendingAttestingIndices, cachedCommittee, committee] using signers
  exact pending_signers_of_initialized_chain positive history initialized computed oldMember
    oldSigners

/-- A current justification at an epoch boundary counts authenticated included signers.

The source is the stored current justified checkpoint and the target is the cached epoch root.

The threshold retains the exact artificial balance from the increment floor. -/
theorem currentJustification_authenticated_at_cached_slot
    {engine : ExecutionEngine preset .phase0}
    {genesis after atStep cached justified : BeaconState preset .phase0}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset .phase0)} {count : Nat}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (advanced : advanceSlots config count after = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (weighed : processJustificationAndFinalization cached = .ok justified)
    (eligible : ¬getCurrentEpoch cached ≤ GENESIS_EPOCH + 1)
    (bit : justified.justificationBits.bits[0] = true) :
    ∃ attestations indices,
      getMatchingTargetAttestations cached (by decide) (getCurrentEpoch cached) =
        .ok attestations ∧
      getUnslashedAttestingIndices cached attestations = .ok indices ∧
      2 * sumMarked cached.validators.data
          (markIndices cached.validators.data.size
            (getActiveValidatorIndices cached (getCurrentEpoch cached))) ≤
        3 * sumMarked cached.validators.data (markIndices cached.validators.data.size indices) +
          3 * totalBalanceFloor cached indices ∧
      ∀ index ∈ indices,
        ∃ pending ∈ attestations, ∃ earlier block later atBlock atSlot,
          blocks = earlier ++ block :: later ∧
          earlier.foldlM
            (fun state block => stateTransition config checks engine state block true)
              genesis = .ok atBlock ∧
          processSlots config atBlock block.message.slot = .ok atSlot ∧
          PendingIncludedInBlock config checks (by decide) atSlot block.message pending ∧
        ∃ (recorded : BeaconState preset .phase0)
          (attestation : Attestation preset .phase0)
          (indexed : IndexedAttestation preset .phase0) (root : Root),
          indexed.data = pending.data ∧
          getIndexedAttestation recorded attestation = .ok indexed ∧
          index ∈ indexed.attestingIndices.data ∧
          indexed.data.source = cached.currentJustifiedCheckpoint ∧
          indexed.data.target.epoch = getCurrentEpoch cached ∧
          getBlockRoot cached (getCurrentEpoch cached) = .ok root ∧
          indexed.data.target.root = root ∧
          isValidIndexedAttestation config checks recorded indexed = .ok true := by
  obtain ⟨sources, epochs⟩ := pending_invariants_at_cached_slot_of_initialized_chain
    (by decide) initialized computed advanced cachedOk
  obtain ⟨attestations, indices, matching, indicesOk, threshold, witnesses⟩ :=
    processJustificationAndFinalization_current_bit_signers (by decide)
      weighed eligible bit sources
  refine ⟨attestations, indices, matching, indicesOk, threshold, ?_⟩
  intro index member
  obtain ⟨⟨pending, pendingMember, signers, root, signersOk, signer, source, rootOk, rootEq⟩,
    _⟩ := witnesses index member
  obtain ⟨_, _, sourceOk, _, sourceMember, _⟩ :=
    getMatchingTargetAttestations_mem matching pendingMember
  have pendingMember' : pending ∈ (cached.currentEpochAttestations (by decide)).data ∨
      pending ∈ (cached.previousEpochAttestations (by decide)).data := by
    simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
      Except.ok.injEq] at sourceOk
    obtain ⟨_, _, rfl⟩ := sourceOk
    split at sourceMember
    · exact .inl sourceMember
    · exact .inr sourceMember
  obtain ⟨recorded, attestation, indexed, indexedOk, listed, data, _, valid⟩ :=
    pending_signers_at_cached_slot_of_initialized_chain positive history
      initialized computed advanced cachedOk pendingMember' signersOk
  obtain ⟨earlier, block, later, atBlock, atSlot, split, prefixOk, slotsOk, included⟩ :=
    pendingIncluded_at_cached_slot_of_initialized_chain (by decide)
      initialized computed advanced cachedOk pendingMember'
  refine ⟨pending, pendingMember, earlier, block, later, atBlock, atSlot,
    split, prefixOk, slotsOk, included, recorded, attestation, indexed, root,
    data, indexedOk, ?_, ?_, ?_, rootOk, ?_, valid⟩
  · rw [listed]
    simpa only [List.mem_toArray] using mem_sortedSet.mpr signer
  · rw [data]
    exact source
  · rw [data]
    exact (getMatchingTargetAttestations_slot_epoch epochs matching pendingMember).1
  · rw [data]
    exact rootEq

/-- A new previous justification at an epoch boundary counts authenticated included signers.

The source is the stored previous justified checkpoint, not the current one.

An inherited previous bit is excluded because its threshold was checked in an earlier call. -/
theorem previousJustification_authenticated_at_cached_slot
    {engine : ExecutionEngine preset .phase0}
    {genesis after atStep cached justified : BeaconState preset .phase0}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset .phase0)} {count : Nat}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (advanced : advanceSlots config count after = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (weighed : processJustificationAndFinalization cached = .ok justified)
    (eligible : ¬getCurrentEpoch cached ≤ GENESIS_EPOCH + 1)
    (bit : justified.justificationBits.bits[1] = true)
    (notInherited : cached.justificationBits.bits[0] = false) :
    ∃ attestations indices,
      getMatchingTargetAttestations cached (by decide) (getPreviousEpoch cached) =
        .ok attestations ∧
      getUnslashedAttestingIndices cached attestations = .ok indices ∧
      2 * sumMarked cached.validators.data
          (markIndices cached.validators.data.size
            (getActiveValidatorIndices cached (getCurrentEpoch cached))) ≤
        3 * sumMarked cached.validators.data (markIndices cached.validators.data.size indices) +
          3 * totalBalanceFloor cached indices ∧
      ∀ index ∈ indices,
        ∃ pending ∈ attestations, ∃ earlier block later atBlock atSlot,
          blocks = earlier ++ block :: later ∧
          earlier.foldlM
            (fun state block => stateTransition config checks engine state block true)
              genesis = .ok atBlock ∧
          processSlots config atBlock block.message.slot = .ok atSlot ∧
          PendingIncludedInBlock config checks (by decide) atSlot block.message pending ∧
        ∃ (recorded : BeaconState preset .phase0)
          (attestation : Attestation preset .phase0)
          (indexed : IndexedAttestation preset .phase0) (root : Root),
          indexed.data = pending.data ∧
          getIndexedAttestation recorded attestation = .ok indexed ∧
          index ∈ indexed.attestingIndices.data ∧
          indexed.data.source = cached.previousJustifiedCheckpoint ∧
          indexed.data.target.epoch = getPreviousEpoch cached ∧
          getBlockRoot cached (getPreviousEpoch cached) = .ok root ∧
          indexed.data.target.root = root ∧
          isValidIndexedAttestation config checks recorded indexed = .ok true := by
  obtain ⟨sources, epochs⟩ := pending_invariants_at_cached_slot_of_initialized_chain
    (by decide) initialized computed advanced cachedOk
  obtain ⟨attestations, indices, matching, indicesOk, threshold, witnesses⟩ :=
    processJustificationAndFinalization_previous_bit_signers (by decide)
      weighed eligible bit notInherited sources
  refine ⟨attestations, indices, matching, indicesOk, threshold, ?_⟩
  intro index member
  obtain ⟨⟨pending, pendingMember, signers, root, signersOk, signer, source, rootOk, rootEq⟩,
    _⟩ := witnesses index member
  obtain ⟨_, _, sourceOk, _, sourceMember, _⟩ :=
    getMatchingTargetAttestations_mem matching pendingMember
  have pendingMember' : pending ∈ (cached.currentEpochAttestations (by decide)).data ∨
      pending ∈ (cached.previousEpochAttestations (by decide)).data := by
    simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
      Except.ok.injEq] at sourceOk
    obtain ⟨_, _, rfl⟩ := sourceOk
    split at sourceMember
    · exact .inl sourceMember
    · exact .inr sourceMember
  obtain ⟨recorded, attestation, indexed, indexedOk, listed, data, _, valid⟩ :=
    pending_signers_at_cached_slot_of_initialized_chain positive history
      initialized computed advanced cachedOk pendingMember' signersOk
  obtain ⟨earlier, block, later, atBlock, atSlot, split, prefixOk, slotsOk, included⟩ :=
    pendingIncluded_at_cached_slot_of_initialized_chain (by decide)
      initialized computed advanced cachedOk pendingMember'
  refine ⟨pending, pendingMember, earlier, block, later, atBlock, atSlot,
    split, prefixOk, slotsOk, included, recorded, attestation, indexed, root,
    data, indexedOk, ?_, ?_, ?_, rootOk, ?_, valid⟩
  · rw [listed]
    simpa only [List.mem_toArray] using mem_sortedSet.mpr signer
  · rw [data]
    exact source
  · rw [data]
    exact (getMatchingTargetAttestations_slot_epoch epochs matching pendingMember).1
  · rw [data]
    exact rootEq

/-- A changed justified checkpoint counts authenticated included attestations for that checkpoint.

The source is selected from the cached state's own justified checkpoints.

The previous-target case uses its actual threshold, even when a justification bit was inherited. -/
theorem changedJustification_authenticated_at_cached_slot
    {engine : ExecutionEngine preset .phase0}
    {genesis after atStep cached justified : BeaconState preset .phase0}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset .phase0)} {count : Nat}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (advanced : advanceSlots config count after = .ok atStep)
    (cachedOk : processSlot atStep = .ok cached)
    (weighed : processJustificationAndFinalization cached = .ok justified)
    (changed : justified.currentJustifiedCheckpoint ≠ cached.currentJustifiedCheckpoint) :
    ∃ epoch attestations indices,
      (epoch = getPreviousEpoch cached ∨ epoch = getCurrentEpoch cached) ∧
      justified.currentJustifiedCheckpoint.epoch = epoch ∧
      getBlockRoot cached epoch = .ok justified.currentJustifiedCheckpoint.root ∧
      getMatchingTargetAttestations cached (by decide) epoch = .ok attestations ∧
      getUnslashedAttestingIndices cached attestations = .ok indices ∧
      2 * sumMarked cached.validators.data
          (markIndices cached.validators.data.size
            (getActiveValidatorIndices cached (getCurrentEpoch cached))) ≤
        3 * sumMarked cached.validators.data (markIndices cached.validators.data.size indices) +
          3 * totalBalanceFloor cached indices ∧
      ∀ index ∈ indices,
        ∃ pending ∈ attestations, ∃ earlier block later atBlock atSlot,
          blocks = earlier ++ block :: later ∧
          earlier.foldlM
            (fun state block => stateTransition config checks engine state block true)
              genesis = .ok atBlock ∧
          processSlots config atBlock block.message.slot = .ok atSlot ∧
          PendingIncludedInBlock config checks (by decide) atSlot block.message pending ∧
        ∃ (recorded : BeaconState preset .phase0)
          (attestation : Attestation preset .phase0)
          (indexed : IndexedAttestation preset .phase0),
          indexed.data = pending.data ∧
          getIndexedAttestation recorded attestation = .ok indexed ∧
          index ∈ indexed.attestingIndices.data ∧
          indexed.data.source =
            (if epoch = getCurrentEpoch cached then cached.currentJustifiedCheckpoint
              else cached.previousJustifiedCheckpoint) ∧
          indexed.data.target = justified.currentJustifiedCheckpoint ∧
          isValidIndexedAttestation config checks recorded indexed = .ok true := by
  obtain ⟨sources, epochs⟩ := pending_invariants_at_cached_slot_of_initialized_chain
    (by decide) initialized computed advanced cachedOk
  obtain ⟨epoch, attestations, indices, recent, matching, indicesOk, epochEq, threshold,
    witnesses⟩ := processJustificationAndFinalization_pending_signers (by decide) weighed changed
  have rootOk := processJustificationAndFinalization_justified_root weighed changed
  rw [epochEq] at rootOk
  refine ⟨epoch, attestations, indices, recent, epochEq, rootOk,
    matching, indicesOk, threshold, ?_⟩
  intro index member
  obtain ⟨⟨pending, pendingMember, signers, root, signersOk, signer, pendingRootOk,
    pendingRoot, _⟩, _⟩ := witnesses index member
  obtain ⟨_, _, sourceOk, _, sourceMember, _⟩ :=
    getMatchingTargetAttestations_mem matching pendingMember
  have pendingMember' : pending ∈ (cached.currentEpochAttestations (by decide)).data ∨
      pending ∈ (cached.previousEpochAttestations (by decide)).data := by
    simp only [getMatchingSourceAttestations, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
      Except.ok.injEq] at sourceOk
    obtain ⟨_, _, rfl⟩ := sourceOk
    split at sourceMember
    · exact .inl sourceMember
    · exact .inr sourceMember
  obtain ⟨recorded, attestation, indexed, indexedOk, listed, data, _, valid⟩ :=
    pending_signers_at_cached_slot_of_initialized_chain positive history
      initialized computed advanced cachedOk pendingMember' signersOk
  obtain ⟨earlier, block, later, atBlock, atSlot, split, prefixOk, slotsOk, included⟩ :=
    pendingIncluded_at_cached_slot_of_initialized_chain (by decide)
      initialized computed advanced cachedOk pendingMember'
  refine ⟨pending, pendingMember, earlier, block, later, atBlock, atSlot, split,
    prefixOk, slotsOk, included, recorded, attestation, indexed, data, indexedOk, ?_, ?_, ?_,
    valid⟩
  · rw [listed]
    simpa only [List.mem_toArray] using mem_sortedSet.mpr signer
  · rw [data]
    exact getMatchingTargetAttestations_source sources matching pendingMember
  · have rootEq : root = justified.currentJustifiedCheckpoint.root := by
      simpa only [rootOk, Except.ok.injEq] using pendingRootOk.symm
    have targetEpoch : indexed.data.target.epoch = justified.currentJustifiedCheckpoint.epoch := by
      rw [data, (getMatchingTargetAttestations_slot_epoch epochs matching pendingMember).1,
        epochEq]
    have targetRoot : indexed.data.target.root = justified.currentJustifiedCheckpoint.root := by
      rw [data, pendingRoot, rootEq]
    have checkpointEq : ∀ x y : Checkpoint,
        x.epoch = y.epoch → x.root = y.root → x = y := by
      intro ⟨epoch1, root1⟩ ⟨epoch2, root2⟩ epochs roots
      cases epochs
      cases roots
      rfl
    exact checkpointEq _ _ targetEpoch targetRoot

/-- The first crossing of an epoch uses a cached state whose two stored sources are below it.

The concrete justification call creates a checkpoint above the boundary.

This locates the epoch-order witness needed for the surround case of Casper FFG §2. -/
theorem justifiedCrossing_of_initialized_chain
    {engine : ExecutionEngine preset .phase0}
    {genesis after : BeaconState preset .phase0}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset .phase0)} {boundary : Nat}
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (below : genesis.currentJustifiedCheckpoint.epoch.toNat ≤ boundary)
    (above : boundary < after.currentJustifiedCheckpoint.epoch.toNat) :
    ∃ earlier block later atBlock offset atStep next cached epoched justified,
      blocks = earlier ++ block :: later ∧
      earlier.foldlM
        (fun state block => stateTransition config checks engine state block true)
          genesis = .ok atBlock ∧
      offset < block.message.slot.toNat - atBlock.slot.toNat ∧
      advanceSlots config offset atBlock = .ok atStep ∧
      advanceSlot config atStep = .ok next ∧
      processSlot atStep = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      cached.previousJustifiedCheckpoint.epoch.toNat ≤ boundary ∧
      cached.currentJustifiedCheckpoint.epoch.toNat ≤ boundary ∧
      boundary < justified.currentJustifiedCheckpoint.epoch.toNat ∧
      justified.currentJustifiedCheckpoint ≠ cached.currentJustifiedCheckpoint := by
  obtain ⟨earlier, block, later, atBlock, offset, atStep, next, split, prefixOk,
    inside, advanced, stepOk, stepBelow, stepAbove⟩ :=
    stateTransition_chain_justified_crossing (by decide) computed below above
  have changed : next.currentJustifiedCheckpoint ≠ atStep.currentJustifiedCheckpoint := by
    intro equal
    rw [equal] at stepAbove
    omega
  obtain ⟨cached, epoched, justified, cachedOk, epochOk, weighed, assigned, changedEpoch⟩ :=
    advanceSlot_justified_origin (by decide) stepOk changed
  have atBlockInvariant := foldlM_ok_invariant Invariant
    (fun _ _ _ holds ok => (stateTransition_invariant (by decide) holds ok).1)
    (initializeBeaconStateFromEth1_invariant initialized).2 prefixOk
  have atStepInvariant := (advanceSlots_invariant (by decide) atBlockInvariant advanced).1
  have frame := frame_processSlot cachedOk
  have currentBelow : cached.currentJustifiedCheckpoint.epoch.toNat ≤ boundary := by
    simpa only [frame.currentJustified] using stepBelow
  have previousBelow : cached.previousJustifiedCheckpoint.epoch.toNat ≤ boundary := by
    rw [frame.previousJustified]
    have ordered := UInt64.le_iff_toNat_le.mp atStepInvariant.ordered.2
    omega
  refine ⟨earlier, block, later, atBlock, offset, atStep, next, cached, epoched, justified,
    split, prefixOk, inside, advanced, stepOk, cachedOk, epochOk, weighed,
    previousBelow, currentBelow, ?_, changedEpoch⟩
  simpa only [assigned] using stepAbove

/-- Current justifications of different roots at one epoch expose double-vote evidence.

The conclusion names checked indexed attestations for every index counted on both chains.

Both thresholds use their own cached state's effective balances and retain their floors.

This is the same-target case of Casper FFG §2, directly on Phase 0 justification calls. -/
theorem currentJustifications_double_vote
    {engine : ExecutionEngine preset .phase0}
    {genesis left right leftStep rightStep leftCached rightCached leftJustified rightJustified :
      BeaconState preset .phase0}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {leftBlocks rightBlocks : List (SignedBeaconBlock preset .phase0)}
    {leftCount rightCount : Nat} {leftRoot rightRoot : Root}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (leftRun : leftBlocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok left)
    (rightRun : rightBlocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok right)
    (leftAdvanced : advanceSlots config leftCount left = .ok leftStep)
    (rightAdvanced : advanceSlots config rightCount right = .ok rightStep)
    (leftCache : processSlot leftStep = .ok leftCached)
    (rightCache : processSlot rightStep = .ok rightCached)
    (leftWeighed : processJustificationAndFinalization leftCached = .ok leftJustified)
    (rightWeighed : processJustificationAndFinalization rightCached = .ok rightJustified)
    (leftEligible : ¬getCurrentEpoch leftCached ≤ GENESIS_EPOCH + 1)
    (rightEligible : ¬getCurrentEpoch rightCached ≤ GENESIS_EPOCH + 1)
    (leftBit : leftJustified.justificationBits.bits[0] = true)
    (rightBit : rightJustified.justificationBits.bits[0] = true)
    (sameEpoch : getCurrentEpoch leftCached = getCurrentEpoch rightCached)
    (leftRootOk : getBlockRoot leftCached (getCurrentEpoch leftCached) = .ok leftRoot)
    (rightRootOk : getBlockRoot rightCached (getCurrentEpoch rightCached) = .ok rightRoot)
    (different : leftRoot ≠ rightRoot) :
    ∃ leftIndices rightIndices,
      2 * sumMarked leftCached.validators.data
          (markIndices leftCached.validators.data.size
            (getActiveValidatorIndices leftCached (getCurrentEpoch leftCached))) ≤
        3 * sumMarked leftCached.validators.data
            (markIndices leftCached.validators.data.size leftIndices) +
          3 * totalBalanceFloor leftCached leftIndices ∧
      2 * sumMarked rightCached.validators.data
          (markIndices rightCached.validators.data.size
            (getActiveValidatorIndices rightCached (getCurrentEpoch rightCached))) ≤
        3 * sumMarked rightCached.validators.data
            (markIndices rightCached.validators.data.size rightIndices) +
          3 * totalBalanceFloor rightCached rightIndices ∧
      ∀ index ∈ leftIndices, index ∈ rightIndices →
        ∃ (leftRecorded rightRecorded : BeaconState preset .phase0)
          (leftIndexed rightIndexed : IndexedAttestation preset .phase0),
          index ∈ leftIndexed.attestingIndices.data ∧
          index ∈ rightIndexed.attestingIndices.data ∧
          isValidIndexedAttestation config checks leftRecorded leftIndexed = .ok true ∧
          isValidIndexedAttestation config checks rightRecorded rightIndexed = .ok true ∧
          isSlashableAttestationData leftIndexed.data rightIndexed.data = true := by
  obtain ⟨_, leftIndices, _, _, leftThreshold, leftWitness⟩ :=
    currentJustification_authenticated_at_cached_slot positive history initialized leftRun
      leftAdvanced leftCache leftWeighed leftEligible leftBit
  obtain ⟨_, rightIndices, _, _, rightThreshold, rightWitness⟩ :=
    currentJustification_authenticated_at_cached_slot positive history initialized rightRun
      rightAdvanced rightCache rightWeighed rightEligible rightBit
  refine ⟨leftIndices, rightIndices, leftThreshold, rightThreshold, ?_⟩
  intro index leftMember rightMember
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, leftRecorded, _, leftIndexed, root1,
    _, _, leftSigner, _, leftEpoch, root1Ok, leftTarget, leftValid⟩ :=
    leftWitness index leftMember
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rightRecorded, _, rightIndexed, root2,
    _, _, rightSigner, _, rightEpoch, root2Ok, rightTarget, rightValid⟩ :=
    rightWitness index rightMember
  have root1Eq : root1 = leftRoot := by
    simpa only [leftRootOk, Except.ok.injEq] using root1Ok.symm
  have root2Eq : root2 = rightRoot := by
    simpa only [rightRootOk, Except.ok.injEq] using root2Ok.symm
  refine ⟨leftRecorded, rightRecorded, leftIndexed, rightIndexed,
    leftSigner, rightSigner, leftValid, rightValid, ?_⟩
  apply isSlashableAttestationData_of_double
  · intro equal
    apply different
    calc
      leftRoot = leftIndexed.data.target.root := (leftTarget.trans root1Eq).symm
      _ = rightIndexed.data.target.root := congrArg (·.target.root) equal
      _ = rightRoot := rightTarget.trans root2Eq
  · exact leftEpoch.trans (sameEpoch.trans rightEpoch.symm)

/-- A true bit on an initialized chain has an actual threshold computation behind it.

Genesis has no true bits, so an inherited bit cannot be the end of the search.

The block prefix and slot offset locate the original computation in the concrete execution.

The epoch equation retains the age of that computation through every intervening bit shift. -/
theorem justificationBit_origin_of_initialized_chain
    {engine : ExecutionEngine preset .phase0}
    {genesis after : BeaconState preset .phase0}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset .phase0)} {index : Fin 4}
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (bit : after.justificationBits.bits[index] = true) :
    ∃ earlier block later atBlock offset atStep next cached epoched justified total previous,
      ∃ current, ∃ origin : Fin 4,
      blocks = earlier ++ block :: later ∧
      earlier.foldlM
        (fun state block => stateTransition config checks engine state block true)
          genesis = .ok atBlock ∧
      offset < block.message.slot.toNat - atBlock.slot.toNat ∧
      (getCurrentEpoch after).toNat + origin.val =
        (getCurrentEpoch cached).toNat + 1 + index.val ∧
      advanceSlots config offset atBlock = .ok atStep ∧
      advanceSlot config atStep = .ok next ∧
      processSlot atStep = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      weighJustificationAndFinalization cached total previous current = .ok justified ∧
      ((origin.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
        (origin.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
          cached.justificationBits.bits[0] = false)) := by
  have earlyBits : getCurrentEpoch genesis ≤ GENESIS_EPOCH + 1 →
      ∀ index : Fin 4, genesis.justificationBits.bits[index] = false := by
    intro _ index
    exact initializeBeaconStateFromEth1_bits (by decide) initialized index
  rcases stateTransition_chain_bit_epoch_origin (by decide) earlyBits computed bit with
      inherited | originated
  · obtain ⟨earlier, _, earlierBit⟩ := inherited
    have cleared := initializeBeaconStateFromEth1_bits (by decide) initialized earlier
    rw [cleared] at earlierBit
    cases earlierBit
  · exact originated

/-- Every Phase 0 state reached from initialized genesis keeps the effective-balance cap.

The block list uses the actual state transition, including result validation. -/
theorem effectiveBalancesBounded_of_initialized_chain
    {engine : ExecutionEngine preset fork} {genesis : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset fork)}
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after) :
    EffectiveBalancesBounded after := by
  obtain ⟨before, holds⟩ := initializeBeaconStateFromEth1_invariant initialized
  have invariant := foldlM_ok_invariant Invariant
    (fun _ _ _ current ok => (stateTransition_invariant before current ok).1) holds computed
  exact invariant.effectiveBalancesBounded

/-- Growth from any reference balance on an initialized chain is bounded by its initial deficit.

The reference can be the effective balance of the same validator at the common ancestor. -/
theorem effectiveBalance_growth_le_deficit_of_initialized_chain
    {engine : ExecutionEngine preset fork} {genesis : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {blocks : List (SignedBeaconBlock preset fork)} {reference : Gwei} {validator : Validator}
    (initialized : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp
      deposits = .ok genesis)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block true) genesis =
        .ok after)
    (member : validator ∈ after.validators.data) :
    validator.effectiveBalance.toNat - reference.toNat ≤
      preset.MAX_EFFECTIVE_BALANCE.toNat - reference.toNat :=
  effectiveBalance_growth_le_initial_deficit
    (effectiveBalancesBounded_of_initialized_chain initialized computed) member

/-- A candidate state launches the chain exactly when it is late enough.

It must also have enough validators active at the genesis epoch. -/
theorem isValidGenesisState_iff :
    isValidGenesisState config state = true ↔
      config.MIN_GENESIS_TIME ≤ state.genesisTime ∧
        config.MIN_GENESIS_ACTIVE_VALIDATOR_COUNT.toNat ≤
          (getActiveValidatorIndices state GENESIS_EPOCH).length := by
  simp [isValidGenesisState]

end EthLib.Consensus
