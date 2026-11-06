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
