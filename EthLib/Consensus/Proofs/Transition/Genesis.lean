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
