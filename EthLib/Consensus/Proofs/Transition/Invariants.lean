module

public import EthLib.Consensus.Proofs.Transition.EpochJustification
public import EthLib.Consensus.Proofs.Transition.EpochRewards
public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Proofs.Transition.StateTransition

/-!
# Proofs: invariants of the Phase 0 state transition

The following properties hold after each valid block, before Altair.

The registry and the balances keep one entry for each validator.

Each validator may withdraw no earlier than it exits.

Each effective balance is at most the Phase 0 cap.

The finalized, previous justified and current justified epochs stay in increasing order.

The current justified epoch is at most the previous epoch.

So the next epoch transition cannot lower the finalized epoch.

The finalized epoch then never decreases.

Most steps change neither the slot nor the checkpoints, and keep the first two properties.

Justification and finalization change the checkpoints, and the slot step moves the epoch on.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- A balance credit does not change the RANDAO mixes used to reconstruct committees. -/
theorem increaseBalance_randao {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [increaseBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  rfl

/-- A balance deduction does not change the RANDAO mixes. -/
theorem decreaseBalance_randao {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [decreaseBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  rfl

/-- Before Electra, allocating an exit epoch leaves the state unchanged. -/
theorem exitQueue_state (before : fork < .pectra) {balance : Gwei} {epoch : Epoch}
    (computed : exitQueue config state balance = .ok (after, epoch)) : after = state := by
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt before
  simp only [exitQueue, notElectra, ↓reduceDIte, bind_ok_iff, pure,
    Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
  obtain ⟨_, _, rfl, _⟩ := computed
  rfl

/-- Exit scheduling before Electra preserves the mixes used by historical committees. -/
theorem initiateValidatorExit_randao (before : fork < .pectra) {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, rfl⟩⟩ :=
    initiateValidatorExit_ok computed
  · rfl
  · change queued.randaoMixes = state.randaoMixes
    rw [exitQueue_state before queue]

/-- Slashing before Electra preserves the mixes despite its balance and registry changes. -/
theorem slashValidator_randao (before : fork < .pectra)
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (computed : slashValidator config state index whistleblower = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, _, _, _, _, _, _, _, _, lowered, loweredOk,
    _, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  have exitedMixes := initiateValidatorExit_randao before exitedOk
  have loweredMixes := decreaseBalance_randao loweredOk
  have raisedMixes := increaseBalance_randao raisedOk
  have lastMixes := increaseBalance_randao lastOk
  have notGloas : ¬Fork.glamsterdam ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at done
  subst done
  exact lastMixes.trans (raisedMixes.trans (loweredMixes.trans exitedMixes))

/-- A proposer slashing before Electra preserves the committee seed buffer. -/
theorem processProposerSlashing_randao (before : fork < .pectra)
    {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact slashValidator_randao before slashed

/-- An individual attester-slashing step preserves the committee seed buffer. -/
theorem slashIfSlashable_randao (before : fork < .pectra)
    {step next : BeaconState preset fork × Bool} {index : ValidatorIndex}
    (computed : slashIfSlashable config step index = .ok next) :
    next.1.randaoMixes = step.1.randaoMixes := by
  obtain ⟨state, flag⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact slashValidator_randao before slashed
  · cases computed
    rfl

/-- The full attester-slashing operation preserves the committee seed buffer. -/
theorem processAttesterSlashing_randao (before : fork < .pectra)
    {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => step.1.randaoMixes = state.randaoMixes)
    (fun _ _ _ prior ok => (slashIfSlashable_randao before ok).trans prior) rfl folded

/-- Recording a Phase 0 attestation leaves the committee seed buffer unchanged. -/
theorem processAttestation_randao (before : fork < .altair)
    {attestation : Attestation preset fork}
    (computed : processAttestation config checks state attestation = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  obtain ⟨_, _, _, _, _, recorded, _, _, _⟩ := processAttestation_records before computed
  cases current : attestation.data.target.epoch == getCurrentEpoch state <;>
    simp only [recordPendingAttestation, current, Bool.false_eq_true, ↓reduceIte] at recorded <;>
    split at recorded <;> cases recorded <;> rfl

/-- Phase 0 registry insertion leaves the committee seed buffer unchanged. -/
theorem addValidatorToRegistry_randao (before : fork < .altair)
    {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey credentials amount = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  unfold addValidatorToRegistry at computed
  split at computed
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  split at computed <;> cases computed
  rfl

/-- A Phase 0 deposit credit leaves the committee seed buffer unchanged. -/
theorem applyDeposit_randao (before : fork < .altair)
    {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (computed : applyDeposit config checks state pubkey credentials amount signature =
      .ok after) : after.randaoMixes = state.randaoMixes := by
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  simp only [applyDeposit, notElectra, ↓reduceDIte, applyPendingDeposit] at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact addValidatorToRegistry_randao before computed
    · cases computed
      rfl
  · exact increaseBalance_randao (liftAccessor_ok.mp computed)

/-- The complete Phase 0 deposit operation leaves the committee seed buffer unchanged. -/
theorem processDeposit_randao (before : fork < .altair)
    {beforeHeze : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks beforeHeze state deposit = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact applyDeposit_randao (state := { state with eth1DepositIndex := fun _ => next })
    before applied

/-- A voluntary exit before Electra preserves the committee seed buffer. -/
theorem processVoluntaryExit_randao (before : fork < .pectra)
    {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  unfold processVoluntaryExit at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact initiateValidatorExit_randao before exited

/-- Phase 0 block operations preserve all RANDAO mixes.

Only the separate reveal-processing step can change the buffer within a block. -/
theorem processOperations_randao (before : fork < .altair)
    {body : BeaconBlockBody preset fork}
    (computed : processOperations config checks state body = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  unfold processOperations at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := computed
  have capella : ¬Fork.shapella ≤ fork := Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  simp only [capella, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at changesOk
  subst changesOk
  have earlier : fork < .pectra := Nat.lt_trans before (by decide)
  have p := foldlM_ok_invariant (fun s => s.randaoMixes = state.randaoMixes)
    (fun _ _ _ prior ok => (processProposerSlashing_randao earlier ok).trans prior)
    rfl proposersOk
  have a := foldlM_ok_invariant (fun s => s.randaoMixes = proposers.randaoMixes)
    (fun _ _ _ prior ok => (processAttesterSlashing_randao earlier ok).trans prior)
    rfl attestersOk
  have t := foldlM_ok_invariant (fun s => s.randaoMixes = attesters.randaoMixes)
    (fun _ _ _ prior ok => (processAttestation_randao before ok).trans prior)
    rfl attestedOk
  have d := foldlM_ok_invariant (fun s => s.randaoMixes = attested.randaoMixes)
    (fun _ _ _ prior ok => (processDeposit_randao before ok).trans prior)
    rfl depositedOk
  have e := foldlM_ok_invariant (fun s => s.randaoMixes = deposited.randaoMixes)
    (fun _ _ _ prior ok => (processVoluntaryExit_randao earlier ok).trans prior)
    rfl exitsOk
  exact e.trans (d.trans (t.trans (a.trans p)))

/-- Applying one reward/penalty pair preserves the seed buffer. -/
theorem applyDeltas_randao {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, raised, lowered⟩ := computed
  exact (decreaseBalance_randao lowered).trans (increaseBalance_randao raised)

/-- Applying all epoch deltas preserves the seed buffer. -/
theorem applyAllDeltas_randao {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) :
    after.randaoMixes = state.randaoMixes :=
  foldlM_ok_invariant (fun s => s.randaoMixes = state.randaoMixes)
    (fun _ _ _ prior ok => (applyDeltas_randao ok).trans prior) rfl computed

/-- Phase 0 rewards and penalties do not reseed committees. -/
theorem processRewardsAndPenalties_randao (before : fork < .altair)
    (computed : processRewardsAndPenalties config state = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · cases computed
    rfl
  split at computed
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp computed
    exact applyAllDeltas_randao applied

/-- Eligibility and ejection processing before Electra preserve the seed buffer. -/
theorem updateRegistryEntry_randao (before : fork < .pectra) {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, queued, _, computed⟩ := computed
  split at computed
  · exact initiateValidatorExit_randao (state := state.setValidator index queued)
      before (liftAccessor_ok.mp computed)
  · cases computed
    rfl

/-- Scheduling an activation preserves the seed buffer. -/
theorem activateValidator_randao {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  rfl

/-- The Phase 0 registry pass preserves the seed buffer. -/
theorem processRegistryUpdates_randao (before : fork < .pectra)
    (computed : processRegistryUpdates config state = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  unfold processRegistryUpdates at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  have first := foldlM_ok_invariant (fun s => s.randaoMixes = state.randaoMixes)
    (fun _ _ _ prior ok => (updateRegistryEntry_randao before ok).trans prior) rfl updatedOk
  have second := foldlM_ok_invariant (fun s => s.randaoMixes = updated.randaoMixes)
    (fun _ _ _ prior ok => (activateValidator_randao ok).trans prior) rfl activated
  exact second.trans first

/-- The delayed slashing penalty changes balances, not the seed buffer. -/
theorem applySlashingPenalty_randao {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact decreaseBalance_randao lowered
    · cases computed
      rfl
  · cases computed
    rfl

/-- Applying the epoch slashing penalties preserves the seed buffer. -/
theorem processSlashings_randao (computed : processSlashings state = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  unfold processSlashings at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, applied⟩ := computed
  exact foldlM_ok_invariant (fun s => s.randaoMixes = state.randaoMixes)
    (fun _ _ _ prior ok => (applySlashingPenalty_randao ok).trans prior) rfl applied

/-- Resetting deposit-contract votes preserves the seed buffer. -/
theorem processEth1DataReset_randao {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed <;> cases computed <;> rfl

/-- Updating one effective balance preserves the seed buffer. -/
theorem updateEffectiveBalance_randao {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, rfl⟩ := computed
  rfl

/-- Updating all effective balances preserves the seed buffer. -/
theorem processEffectiveBalanceUpdates_randao
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  unfold processEffectiveBalanceUpdates at computed
  split at computed
  · cases computed
  exact foldlM_ok_invariant (fun s => s.randaoMixes = state.randaoMixes)
    (fun _ _ _ prior ok => (updateEffectiveBalance_randao ok).trans prior) rfl computed

/-- Updating historical roots preserves the seed buffer. -/
theorem processHistoricalRootsUpdate_randao
    (computed : processHistoricalRootsUpdate state = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, rest⟩ := computed
  split at rest
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨_, _, _, _, rfl⟩ := rest
    rfl
  · cases rest
    rfl

/-- Rotating Phase 0 participation records preserves the seed buffer. -/
theorem processParticipationRecordUpdates_randao
    (computed : processParticipationRecordUpdates state = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  cases computed
  rfl

/-- Justification changes checkpoints and bits, not the committee seed buffer. -/
theorem processJustificationAndFinalization_randao
    (computed : processJustificationAndFinalization state = .ok after) :
    after.randaoMixes = state.randaoMixes := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · rw [same]
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]

/-- Each validator may withdraw no earlier than it exits. -/
def ExitsOrdered (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data, validator.exitEpoch ≤ validator.withdrawableEpoch

/-- A step that keeps the slot and the three checkpoints.

When they hold before it, it also keeps one balance for each validator.

It then also keeps each exit no later than its withdrawal. -/
structure Frame (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  finalized : after.finalizedCheckpoint = state.finalizedCheckpoint
  previousJustified : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint
  currentJustified : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint
  justificationBits : after.justificationBits = state.justificationBits
  balancesMatch : BalancesMatch state → BalancesMatch after
  exitsOrdered : ExitsOrdered state → ExitsOrdered after
  effectiveBalancesBounded : EffectiveBalancesBounded state → EffectiveBalancesBounded after

theorem Frame.refl (state : BeaconState preset fork) : Frame state state :=
  ⟨rfl, rfl, rfl, rfl, rfl, id, id, id⟩

theorem Frame.trans {first second third : BeaconState preset fork} (one : Frame first second)
    (two : Frame second third) : Frame first third :=
  ⟨two.slot.trans one.slot, two.finalized.trans one.finalized,
    two.previousJustified.trans one.previousJustified,
    two.currentJustified.trans one.currentJustified,
    two.justificationBits.trans one.justificationBits, two.balancesMatch ∘ one.balancesMatch,
    two.exitsOrdered ∘ one.exitsOrdered,
    two.effectiveBalancesBounded ∘ one.effectiveBalancesBounded⟩

/-- A step that keeps the slot, the checkpoints and the registry, and the number of balances. -/
theorem Frame.of_validators (sizes : SameSizes state after)
    (validators : after.validators = state.validators) (slot : after.slot = state.slot)
    (finalized : after.finalizedCheckpoint = state.finalizedCheckpoint)
    (previousJustified : after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint)
    (currentJustified : after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint)
    (bits : after.justificationBits = state.justificationBits) :
    Frame state after :=
  ⟨slot, finalized, previousJustified, currentJustified, bits, balancesMatch_of_sameSizes sizes,
    (fun ordered => by rw [ExitsOrdered, validators]; exact ordered),
    fun bounded => by rw [EffectiveBalancesBounded, validators]; exact bounded⟩

/-- A fold whose every step is a frame is a frame. -/
theorem Frame.foldlM {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
    (frame : ∀ s x s', step s x = .ok s' → Frame s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : Frame state after :=
  foldlM_ok_invariant (Frame state) (fun _ _ _ before ok => before.trans (frame _ _ _ ok))
    (Frame.refl state) computed

/-- Equality of the two pending-attestation lists before Altair.

Balance, registry and randomness updates preserve these lists until participation rotation. -/
structure PendingUnchanged (state after : BeaconState preset fork) (before : fork < .altair) :
    Prop where
  current : after.currentEpochAttestations before = state.currentEpochAttestations before
  previous : after.previousEpochAttestations before = state.previousEpochAttestations before

theorem PendingUnchanged.refl (state : BeaconState preset fork) (before : fork < .altair) :
    PendingUnchanged state state before := ⟨rfl, rfl⟩

theorem PendingUnchanged.trans {first second third : BeaconState preset fork}
    {before : fork < .altair} (one : PendingUnchanged first second before)
    (two : PendingUnchanged second third before) : PendingUnchanged first third before :=
  ⟨two.current.trans one.current, two.previous.trans one.previous⟩

/-- An unchanged pair of lists has exactly the same pending records. -/
theorem PendingUnchanged.mem_iff {before : fork < .altair}
    (kept : PendingUnchanged state after before) (pending : PendingAttestation preset) :
    (pending ∈ (after.currentEpochAttestations before).data ∨
      pending ∈ (after.previousEpochAttestations before).data) ↔
    (pending ∈ (state.currentEpochAttestations before).data ∨
      pending ∈ (state.previousEpochAttestations before).data) := by
  rw [kept.current, kept.previous]

theorem PendingUnchanged.foldlM {α : Type} {before : fork < .altair}
    {step : BeaconState preset fork → α → Except TransitionError _}
    (keeps : ∀ s x s', step s x = .ok s' → PendingUnchanged s s' before) {items : List α}
    (computed : items.foldlM step state = .ok after) : PendingUnchanged state after before :=
  foldlM_ok_invariant (fun next => PendingUnchanged state next before)
    (fun _ _ _ prior ok => prior.trans (keeps _ _ _ ok))
    (PendingUnchanged.refl state before) computed

theorem pendingUnchanged_increaseBalance {before : fork < .altair}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    PendingUnchanged state after before := by
  simp only [increaseBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact ⟨rfl, rfl⟩

theorem pendingUnchanged_decreaseBalance {before : fork < .altair}
    {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) :
    PendingUnchanged state after before := by
  simp only [decreaseBalance, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact ⟨rfl, rfl⟩

theorem pendingUnchanged_exitQueue {before : fork < .altair} {balance : Gwei} {epoch : Epoch}
    (computed : exitQueue config state balance = .ok (after, epoch)) :
    PendingUnchanged state after before := by
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  simp only [exitQueue, notElectra, ↓reduceDIte, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at computed
  obtain ⟨_, _, rfl, _⟩ := computed
  exact ⟨rfl, rfl⟩

theorem pendingUnchanged_initiateValidatorExit {before : fork < .altair}
    {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    PendingUnchanged state after before := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, rfl⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _ _
  · have kept : PendingUnchanged state queued before := pendingUnchanged_exitQueue queue
    exact ⟨kept.current, kept.previous⟩

theorem pendingUnchanged_applyDeltas {before : fork < .altair}
    {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) :
    PendingUnchanged state after before := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, raised, lowered⟩ := computed
  exact (pendingUnchanged_increaseBalance raised).trans (pendingUnchanged_decreaseBalance lowered)

theorem pendingUnchanged_applyAllDeltas {before : fork < .altair}
    {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) :
    PendingUnchanged state after before :=
  PendingUnchanged.foldlM (fun _ _ _ ok => pendingUnchanged_applyDeltas ok) computed

theorem pendingUnchanged_processRewardsAndPenalties {before : fork < .altair}
    (computed : processRewardsAndPenalties config state = .ok after) :
    PendingUnchanged state after before := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · cases computed
    exact .refl _ _
  split at computed
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  · obtain ⟨_, _, applied⟩ := bind_ok_iff.mp computed
    exact pendingUnchanged_applyAllDeltas applied

theorem pendingUnchanged_updateRegistryEntry {before : fork < .altair} {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    PendingUnchanged state after before := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, _, queued, _, computed⟩ := computed
  have kept : PendingUnchanged state (state.setValidator index queued) before := ⟨rfl, rfl⟩
  split at computed
  · exact kept.trans (pendingUnchanged_initiateValidatorExit (liftAccessor_ok.mp computed))
  · cases computed
    exact kept

theorem pendingUnchanged_activateValidator {before : fork < .altair} {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) :
    PendingUnchanged state after before := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, rfl⟩ := computed
  exact ⟨rfl, rfl⟩

theorem pendingUnchanged_processRegistryUpdates {before : fork < .altair}
    (computed : processRegistryUpdates config state = .ok after) :
    PendingUnchanged state after before := by
  unfold processRegistryUpdates at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, updated, activated⟩ := computed
  exact (PendingUnchanged.foldlM
    (fun _ _ _ ok => pendingUnchanged_updateRegistryEntry ok) updated).trans
      (PendingUnchanged.foldlM (fun _ _ _ ok => pendingUnchanged_activateValidator ok) activated)

theorem pendingUnchanged_applySlashingPenalty {before : fork < .altair}
    {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    PendingUnchanged state after before := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact pendingUnchanged_decreaseBalance lowered
    · cases computed
      exact .refl _ _
  · cases computed
    exact .refl _ _

theorem pendingUnchanged_processSlashings {before : fork < .altair}
    (computed : processSlashings state = .ok after) :
    PendingUnchanged state after before := by
  unfold processSlashings at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, applied⟩ := computed
  exact PendingUnchanged.foldlM (fun _ _ _ ok => pendingUnchanged_applySlashingPenalty ok) applied

theorem pendingUnchanged_processEth1DataReset {before : fork < .altair}
    {beforeHeze : fork < .hegota}
    (computed : processEth1DataReset beforeHeze state = .ok after) :
    PendingUnchanged state after before := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed <;> cases computed <;> exact ⟨rfl, rfl⟩

theorem pendingUnchanged_updateEffectiveBalance {before : fork < .altair} {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) :
    PendingUnchanged state after before := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, rfl⟩ := computed
  exact ⟨rfl, rfl⟩

theorem pendingUnchanged_processEffectiveBalanceUpdates {before : fork < .altair}
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    PendingUnchanged state after before := by
  unfold processEffectiveBalanceUpdates at computed
  split at computed
  · cases computed
  exact PendingUnchanged.foldlM
    (fun _ _ _ ok => pendingUnchanged_updateEffectiveBalance ok) computed

theorem pendingUnchanged_processSlashingsReset {before : fork < .altair}
    (computed : processSlashingsReset state = .ok after) :
    PendingUnchanged state after before := by
  obtain ⟨_, _, rfl⟩ := processSlashingsReset_eq computed
  exact ⟨rfl, rfl⟩

theorem pendingUnchanged_processRandaoMixesReset {before : fork < .altair}
    (computed : processRandaoMixesReset state = .ok after) :
    PendingUnchanged state after before := by
  obtain ⟨_, _, _, _, rfl⟩ := processRandaoMixesReset_eq computed
  exact ⟨rfl, rfl⟩

theorem pendingUnchanged_processHistoricalRootsUpdate {before : fork < .altair}
    (computed : processHistoricalRootsUpdate state = .ok after) :
    PendingUnchanged state after before := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩
  · cases computed
    exact .refl _ _

theorem pendingUnchanged_slashValidator {before : fork < .altair}
    {index : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (computed : slashValidator config state index whistleblower = .ok after) :
    PendingUnchanged state after before := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, _, delay, _, _, _, _, _, lowered, loweredOk,
    _, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  have exitedPending : PendingUnchanged state exited before :=
    pendingUnchanged_initiateValidatorExit exitedOk
  have loweredPending := pendingUnchanged_decreaseBalance (before := before) loweredOk
  have marked : PendingUnchanged exited lowered before :=
    ⟨loweredPending.current, loweredPending.previous⟩
  have changed := exitedPending.trans <| marked.trans <|
    (pendingUnchanged_increaseBalance raisedOk).trans (pendingUnchanged_increaseBalance lastOk)
  have notGloas : ¬Fork.glamsterdam ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at done
  subst done
  exact changed

theorem pendingUnchanged_processProposerSlashing {before : fork < .altair}
    {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    PendingUnchanged state after before := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact pendingUnchanged_slashValidator slashed

theorem pendingUnchanged_slashIfSlashable {before : fork < .altair}
    {step next : BeaconState preset fork × Bool} {index : ValidatorIndex}
    (computed : slashIfSlashable config step index = .ok next) :
    PendingUnchanged step.1 next.1 before := by
  obtain ⟨state, flag⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact pendingUnchanged_slashValidator slashed
  · cases computed
    exact .refl _ _

theorem pendingUnchanged_processAttesterSlashing {before : fork < .altair}
    {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    PendingUnchanged state after before := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => PendingUnchanged state step.1 before)
    (fun _ _ _ prior ok => prior.trans (pendingUnchanged_slashIfSlashable ok))
    (show PendingUnchanged state (state, false).1 before from .refl _ _) folded

theorem pendingUnchanged_addValidatorToRegistry (before : fork < .altair)
    {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey credentials amount = .ok after) :
    PendingUnchanged state after before := by
  unfold addValidatorToRegistry at computed
  split at computed
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  split at computed <;> cases computed
  exact ⟨rfl, rfl⟩

theorem pendingUnchanged_applyDeposit (before : fork < .altair)
    {pubkey : BLSPubkey} {credentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (computed : applyDeposit config checks state pubkey credentials amount signature =
      .ok after) : PendingUnchanged state after before := by
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  simp only [applyDeposit, notElectra, ↓reduceDIte, applyPendingDeposit] at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact pendingUnchanged_addValidatorToRegistry before computed
    · cases computed
      exact .refl _ _
  · exact pendingUnchanged_increaseBalance (liftAccessor_ok.mp computed)

theorem pendingUnchanged_processDeposit (before : fork < .altair)
    {beforeHeze : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks beforeHeze state deposit = .ok after) :
    PendingUnchanged state after before := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  have kept : PendingUnchanged state { state with eth1DepositIndex := fun _ => next } before :=
    ⟨rfl, rfl⟩
  exact kept.trans (pendingUnchanged_applyDeposit before applied)

theorem pendingUnchanged_processVoluntaryExit {before : fork < .altair}
    {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    PendingUnchanged state after before := by
  unfold processVoluntaryExit at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact pendingUnchanged_initiateValidatorExit exited

/-! ## Mutators -/

theorem mem_of_getValidator {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator) : validator ∈ state.validators.data := by
  unfold getValidator at found
  split at found
  · rename_i read
    cases found
    exact Array.mem_of_getElem? read
  · cases found

/-- Replacing a validator by one that exits no later than it may withdraw keeps the order. -/
theorem ExitsOrdered.setValidator {index : Nat} {validator : Validator}
    (ordered : ExitsOrdered state) (le : validator.exitEpoch ≤ validator.withdrawableEpoch) :
    ExitsOrdered (state.setValidator index validator) := by
  intro other member
  rcases Array.mem_or_eq_of_mem_setIfInBounds member with old | rfl
  · exact ordered other old
  · exact le

theorem frame_setValidator {index : Nat} {validator : Validator}
    (le : ExitsOrdered state → validator.exitEpoch ≤ validator.withdrawableEpoch)
    (bound : EffectiveBalancesBounded state →
      validator.effectiveBalance ≤ preset.MAX_EFFECTIVE_BALANCE) :
    Frame state (state.setValidator index validator) :=
  ⟨rfl, rfl, rfl, rfl, rfl, balancesMatch_of_sameSizes (sameSizes_setValidator _ _ _),
    (fun ordered => ordered.setValidator (le ordered)),
    fun bounded => effectiveBalancesBounded_setValidator bounded (bound bounded)⟩

theorem frame_increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : Frame state after := by
  simp only [increaseBalance, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed; · cases computed)
  cases computed
  exact Frame.of_validators (sameSizes_setBalance _ _ _) rfl rfl rfl rfl rfl rfl

theorem frame_decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : Frame state after := by
  simp only [decreaseBalance, bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed; · cases computed)
  cases computed
  exact Frame.of_validators (sameSizes_setBalance _ _ _) rfl rfl rfl rfl rfl rfl

theorem frame_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    Frame state after := by
  obtain ⟨validators, balances⟩ := exitQueue_validators computed
  unfold exitQueue at computed
  have sizes : SameSizes state after := ⟨by rw [validators], by rw [balances]⟩
  split at computed
  · simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, _, _, _, _, rfl, _⟩ := computed
    exact Frame.of_validators sizes validators rfl rfl rfl rfl rfl
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact Frame.refl _

/-- Starting an exit sets a withdrawable epoch no earlier than the exit epoch. -/
theorem frame_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) : Frame state after := by
  obtain ⟨validator, found,
    ⟨_, rfl⟩ | ⟨_, queued, exitEpoch, withdrawableEpoch, queue, summed, rfl⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact Frame.refl _
  · refine (frame_exitQueue queue).trans (frame_setValidator (fun _ => ?_) (fun bounded => ?_))
    · have sum := (addChecked_ok_iff.mp summed).2
      exact UInt64.le_iff_toNat_le.mpr (by simp only at sum ⊢; omega)
    · have queuedFound : getValidator queued index = .ok validator := by
        rw [getValidator_of_validators_eq (exitQueue_validators queue).1]
        exact found
      exact bounded validator (mem_of_getValidator queuedFound)

theorem frame_slashings (state : BeaconState preset fork) (slashings : Vector Gwei _) :
    Frame state { state with slashings } :=
  Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl

/-- The last step of a slashing, which from Gloas cancels builder payments, keeps the frame. -/
theorem frame_slashValidatorLast {last : BeaconState preset fork} {index : ValidatorIndex}
    (done : (pure (if gloas : .glamsterdam ≤ fork then cancelProposerPayments last gloas index
      else last) : Except AccessorError (BeaconState preset fork)) = .ok after) :
    Frame last after := by
  simp only [pure, Except.pure, Except.ok.injEq] at done
  subst done
  split
  · exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl
  · exact Frame.refl _

/-- Slashing a validator only delays its withdrawal. -/
theorem frame_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    Frame state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, _, _, _, _, lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  refine (frame_initiateValidatorExit exitedOk).trans <|
    ((frame_setValidator (index := slashedIndex.toNat)
      (validator := { validator with
        slashed := true, withdrawableEpoch := max validator.withdrawableEpoch delay })
      (fun ordered => ?_) (fun bounded => bounded validator (mem_of_getValidator found))).trans
      (frame_slashings _ _)).trans <|
    (frame_decreaseBalance loweredOk).trans <| (frame_increaseBalance raisedOk).trans <|
    (frame_increaseBalance lastOk).trans (frame_slashValidatorLast done)
  refine UInt64.le_trans (ordered validator (mem_of_getValidator found)) ?_
  rw [UInt64.max_def]
  split
  · assumption
  · exact UInt64.le_refl _

/-! ## The steps of a block -/

theorem frame_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : Frame state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl

theorem frame_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : Frame state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl

theorem frame_processEth1Data {before : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : Frame state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact Frame.of_validators (sameSizes_processEth1Data computed) (by rw [← rest])
    (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest])

theorem frame_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    Frame state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact frame_slashValidator slashed

theorem frame_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    Frame step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact frame_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    Frame state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => Frame state step.1)
    (fun _ _ _ before ok => before.trans (frame_slashIfSlashable ok))
    (show Frame state (state, false).1 from Frame.refl state) folded

/-- An attester-slashing step preserves every past activity query. -/
theorem slashIfSlashable_active {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} {epoch : Epoch}
    (before : fork < .pectra) (past : epoch ≤ getCurrentEpoch step.1)
    (computed : slashIfSlashable config step index = .ok next) (other : ValidatorIndex) :
    (getValidator next.1 other).map (isActiveValidator · epoch) =
      (getValidator step.1 other).map (isActiveValidator · epoch) := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, rest⟩ := computed
  split at rest
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨_, slashed, rfl⟩ := rest
    exact slashValidator_active before past slashed other
  · simp only [pure, Except.pure, Except.ok.injEq] at rest
    subst next
    rfl

/-- A complete attester slashing preserves activity for every past epoch.

Every step keeps the slot, so all steps use the same past-epoch bound. -/
theorem processAttesterSlashing_active {slashing : AttesterSlashing preset fork} {epoch : Epoch}
    (before : fork < .pectra) (past : epoch ≤ getCurrentEpoch state)
    (computed : processAttesterSlashing config checks state slashing = .ok after)
    (other : ValidatorIndex) :
    (getValidator after other).map (isActiveValidator · epoch) =
      (getValidator state other).map (isActiveValidator · epoch) := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  have kept := foldlM_ok_invariant (fun step : BeaconState preset fork × Bool =>
    step.1.slot = state.slot ∧
      (getValidator step.1 other).map (isActiveValidator · epoch) =
        (getValidator state other).map (isActiveValidator · epoch))
    (fun prior index next holds ok => by
      have recent : epoch ≤ getCurrentEpoch prior.1 := by
        simpa only [getCurrentEpoch, holds.1] using past
      exact ⟨(frame_slashIfSlashable ok).slot.trans holds.1,
        (slashIfSlashable_active before recent ok other).trans holds.2⟩)
    (show state.slot = state.slot ∧ _ from ⟨rfl, rfl⟩) folded
  exact kept.2

theorem frame_processAttestation (altair : fork < .altair) {attestation : Attestation preset fork}
    (computed : processAttestation config checks state attestation = .ok after) :
    Frame state after := by
  unfold processAttestation at computed
  split at computed
  · exact absurd ‹_› (Nat.not_le_of_lt altair)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, 
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept
  · obtain ⟨_, rest⟩ := kept
    exact Frame.of_validators (by rw [← rest]; exact ⟨rfl, rfl⟩) (by rw [← rest])
      (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest])
  · obtain ⟨_, rest⟩ := kept
    exact Frame.of_validators (by rw [← rest]; exact ⟨rfl, rfl⟩) (by rw [← rest])
      (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest]) (by rw [← rest])

/-- A new validator exits and withdraws at the far future epoch. -/
theorem frame_addValidatorToRegistry (altair : fork < .altair) {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    Frame state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · exact absurd ‹_› (Nat.not_le_of_lt altair)
  split at computed
  · cases computed
    refine ⟨rfl, rfl, rfl, rfl, rfl, (fun holds => ?_),
      (fun ordered validator member => ?_), fun bounded validator member => ?_⟩
    · simp only [BalancesMatch, Array.size_push] at holds ⊢
      omega
    · rcases Array.mem_push.mp member with old | rfl
      · exact ordered validator old
      · exact UInt64.le_refl _
    · rcases Array.mem_push.mp member with old | rfl
      · exact bounded validator old
      · have notElectra : ¬Fork.pectra ≤ fork := fun le =>
          Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_trans altair (by decide)) le)
        simpa [getValidatorFromDeposit, withdrawalMaxEffectiveBalance, notElectra] using
          (Std.min_le_right
            (a := amount - amount % preset.EFFECTIVE_BALANCE_INCREMENT)
            (b := preset.MAX_EFFECTIVE_BALANCE))
  · cases computed

theorem frame_applyDeposit (altair : fork < .altair) {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    Frame state after := by
  have notElectra : ¬Fork.pectra ≤ fork := fun le =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_trans altair (by decide)) le)
  simp only [applyDeposit, notElectra, ↓reduceDIte, applyPendingDeposit] at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨valid, _, computed⟩ := computed
    split at computed
    · exact frame_addValidatorToRegistry altair computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Frame.refl _
  · rw [liftAccessor_ok] at computed
    exact frame_increaseBalance computed

theorem frame_processDeposit (altair : fork < .altair) {before : fork < .hegota}
    {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    Frame state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (Frame.of_validators (state := state)
    (after := { state with eth1DepositIndex := fun _ => next })
    ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl).trans (frame_applyDeposit altair applied)

theorem frame_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    Frame state after := by
  unfold processVoluntaryExit at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact frame_initiateValidatorExit exited

/-- Before Altair, the operations of a block form a frame. -/
theorem frame_processOperations (altair : fork < .altair) {body : BeaconBlockBody preset fork}
    (computed : processOperations config checks state body = .ok after) : Frame state after := by
  unfold processOperations at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := computed
  have order : Fork.altair ≤ Fork.shapella := by decide
  have capella : ¬Fork.shapella ≤ fork := fun le =>
    Nat.lt_irrefl _ (Nat.lt_of_lt_of_le altair (Nat.le_trans order le))
  simp only [capella, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at changesOk
  subst changesOk
  exact (Frame.foldlM (fun _ _ _ ok => frame_processProposerSlashing ok) proposersOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processAttesterSlashing ok) attestersOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processAttestation altair ok) attestedOk).trans <|
    (Frame.foldlM (fun _ _ _ ok => frame_processDeposit altair ok) depositedOk).trans <|
    Frame.foldlM (fun _ _ _ ok => frame_processVoluntaryExit ok) exitsOk

/-- Preserved indexed activity queries preserve the ordered active population. -/
theorem active_indices_of_validator_queries {epoch : Epoch}
    (within : state.RegistryWithinLimit) (afterWithin : after.RegistryWithinLimit)
    (same : ∀ index, (getValidator after index).map (isActiveValidator · epoch) =
      (getValidator state index).map (isActiveValidator · epoch)) :
    getActiveValidatorIndices after epoch = getActiveValidatorIndices state epoch := by
  apply getActiveValidatorIndices_congr within afterWithin
  intro index
  have equal := same index
  simp only [getValidator] at equal
  cases old : state.validators.data[index.toNat]? <;>
    cases new : after.validators.data[index.toNat]? <;>
    simp only [old, new, Except.map] at equal <;> simp_all

/-- Phase 0 block operations preserve the ordered committee population for a past epoch.

Slashing changes participation eligibility, while activation and exit scheduling take effect later.

Deposits append inactive validators or change balances, neither of which reassigns committees. -/
theorem processOperations_active_indices (before : fork < .altair)
    {body : BeaconBlockBody preset fork} {epoch : Epoch}
    (past : epoch ≤ getCurrentEpoch state)
    (computed : processOperations config checks state body = .ok after) :
    getActiveValidatorIndices after epoch = getActiveValidatorIndices state epoch := by
  have earlier : fork < .pectra := Nat.lt_trans before (by decide)
  have within (s : BeaconState preset fork) : s.RegistryWithinLimit :=
    s.validators.bound (Nat.lt_trans before (by decide))
  have proposerStep : ∀ (s : BeaconState preset fork) slashing s', epoch ≤ getCurrentEpoch s →
      processProposerSlashing config checks s slashing = .ok s' →
      getActiveValidatorIndices s' epoch = getActiveValidatorIndices s epoch := by
    intro s slashing s' recent ok
    exact active_indices_of_validator_queries (within s) (within s')
      (processProposerSlashing_active earlier recent ok)
  have attesterStep : ∀ (s : BeaconState preset fork) slashing s', epoch ≤ getCurrentEpoch s →
      processAttesterSlashing config checks s slashing = .ok s' →
      getActiveValidatorIndices s' epoch = getActiveValidatorIndices s epoch := by
    intro s slashing s' recent ok
    exact active_indices_of_validator_queries (within s) (within s')
      (processAttesterSlashing_active earlier recent ok)
  have exitStep : ∀ (s : BeaconState preset fork) exit s', epoch ≤ getCurrentEpoch s →
      processVoluntaryExit config checks s exit = .ok s' →
      getActiveValidatorIndices s' epoch = getActiveValidatorIndices s epoch := by
    intro s exit s' recent ok
    exact active_indices_of_validator_queries (within s) (within s')
      (processVoluntaryExit_active earlier recent ok)
  have foldPreserves {α : Type} {operation : BeaconState preset fork → α →
        Except TransitionError (BeaconState preset fork)} {xs : List α}
      {s s' : BeaconState preset fork}
      (frame : ∀ s item s', operation s item = .ok s' → Frame s s')
      (step : ∀ s item s', epoch ≤ getCurrentEpoch s → operation s item = .ok s' →
        getActiveValidatorIndices s' epoch = getActiveValidatorIndices s epoch)
      (recent : epoch ≤ getCurrentEpoch s) (ok : xs.foldlM operation s = .ok s') :
      s'.slot = s.slot ∧
        getActiveValidatorIndices s' epoch = getActiveValidatorIndices s epoch := by
    apply foldlM_ok_invariant (fun t => t.slot = s.slot ∧
      getActiveValidatorIndices t epoch = getActiveValidatorIndices s epoch)
      (fun t item next holds applied => ?_) ⟨rfl, rfl⟩ ok
    have recent' : epoch ≤ getCurrentEpoch t := by
      simpa only [getCurrentEpoch, holds.1] using recent
    exact ⟨(frame _ _ _ applied).slot.trans holds.1,
      (step _ _ _ recent' applied).trans holds.2⟩
  unfold processOperations at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := computed
  have capella : ¬Fork.shapella ≤ fork := Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  simp only [capella, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at changesOk
  subst changesOk
  have p := foldPreserves (fun _ _ _ ok => frame_processProposerSlashing ok)
    proposerStep past proposersOk
  have a := foldPreserves (fun _ _ _ ok => frame_processAttesterSlashing ok)
    attesterStep (by simpa only [getCurrentEpoch, p.1] using past) attestersOk
  have t := foldPreserves (fun _ _ _ ok => frame_processAttestation before ok)
    (fun _ _ _ _ ok => processAttestation_active_indices before epoch ok)
    (by simpa only [getCurrentEpoch, a.1, p.1] using past) attestedOk
  have d := foldPreserves (fun _ _ _ ok => frame_processDeposit before ok)
    (fun _ _ _ _ ok => processDeposit_active_indices before epoch ok)
    (by simpa only [getCurrentEpoch, t.1, a.1, p.1] using past) depositedOk
  have e := foldPreserves (fun _ _ _ ok => frame_processVoluntaryExit ok)
    exitStep (by simpa only [getCurrentEpoch, d.1, t.1, a.1, p.1] using past) exitsOk
  exact e.2.trans (d.2.trans (t.2.trans (a.2.trans p.2)))

/-- Before Altair, a block forms a frame. -/
theorem frame_processBlock (altair : fork < .altair) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) : Frame state after := by
  have notAltair : ¬Fork.altair ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le altair le)
  simp only [processBlock, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (frame_processBlockHeader headerOk).trans <| (frame_processRandao randaoOk).trans <|
    (frame_processEth1Data eth1Ok).trans (frame_processOperations altair operationsOk)

/-- A Phase 0 block preserves the active population for every past or current epoch. -/
theorem processBlock_active_indices (before : fork < .altair)
    {block : BeaconBlock preset fork} {epoch : Epoch}
    (past : epoch ≤ getCurrentEpoch state)
    (computed : processBlock config checks engine state block = .ok after) :
    getActiveValidatorIndices after epoch = getActiveValidatorIndices state epoch := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  simp only [processBlock, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨header, headerOk, randao, randaoOk, eth1, eth1Ok, operationsOk⟩ := computed
  have headerFrame := frame_processBlockHeader headerOk
  have randaoFrame := frame_processRandao randaoOk
  have eth1Frame := frame_processEth1Data eth1Ok
  have recent : epoch ≤ getCurrentEpoch eth1 := by
    simpa only [getCurrentEpoch, eth1Frame.slot, randaoFrame.slot, headerFrame.slot] using past
  have headerRegistry : header.validators = state.validators := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    rfl
  have randaoRegistry : randao.validators = header.validators := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
    rfl
  have eth1Registry : eth1.validators = randao.validators := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq eth1Ok
    rw [← rest]
  rw [processOperations_active_indices before recent operationsOk]
  simp only [getActiveValidatorIndices, eth1Registry, randaoRegistry, headerRegistry]

/-- Phase 0 block processing preserves recent attester seeds.

The reveal changes only the current mix, while recent committees read an older mix. -/
theorem processBlock_attester_seed
    {state after : BeaconState preset .phase0}
    {engine : ExecutionEngine preset .phase0}
    {block : BeaconBlock preset .phase0} {epoch : Epoch}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (recent : epoch = getCurrentEpoch state ∨ epoch.toNat + 1 = (getCurrentEpoch state).toNat)
    (computed : processBlock config checks engine state block = .ok after) :
    getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
  simp only [processBlock, show ¬Fork.altair ≤ Fork.phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at computed
  obtain ⟨header, headerOk, randao, randaoOk, eth1, eth1Ok, operationsOk⟩ := computed
  have headerSlot := (frame_processBlockHeader headerOk).slot
  have headerMixes : header.randaoMixes = state.randaoMixes := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    rfl
  have eth1Mixes : eth1.randaoMixes = randao.randaoMixes := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq eth1Ok
    rw [← rest]
  have seed := processRandao_attester_seed positive history randaoOk
    (by simpa only [getCurrentEpoch, headerSlot] using recent)
  have preserved := processOperations_randao (by decide) operationsOk
  have lastSeed : getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed randao epoch DOMAIN_BEACON_ATTESTER := by
    apply getSeed_congr
    intro shifted _
    simp only [getRandaoMix, preserved, eth1Mixes]
  have firstSeed : getSeed header epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
    apply getSeed_congr
    intro shifted _
    simp only [getRandaoMix, headerMixes]
  exact lastSeed.trans (seed.trans firstSeed)

/-- A Phase 0 block preserves committees for attestations it can include.

Both the ordered active population and its shuffle seed are unchanged. -/
theorem processBlock_committee
    {state after : BeaconState preset .phase0}
    {engine : ExecutionEngine preset .phase0}
    {block : BeaconBlock preset .phase0} {slot : Slot} {index : CommitteeIndex}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (recent : computeEpochAtSlot preset slot = getCurrentEpoch state ∨
      (computeEpochAtSlot preset slot).toNat + 1 = (getCurrentEpoch state).toNat)
    (computed : processBlock config checks engine state block = .ok after) :
    getBeaconCommittee after slot index = getBeaconCommittee state slot index := by
  apply getBeaconCommittee_congr
  · apply processBlock_active_indices (by decide) _ computed
    rcases recent with same | previous
    · rw [same]
      exact UInt64.le_refl _
    · rw [UInt64.le_iff_toNat_le]
      omega
  · exact processBlock_attester_seed positive history recent computed

/-- A Phase 0 attestation preserves every committee query, not just its own. -/
theorem processAttestation_committee (before : fork < .altair)
    {attestation : Attestation preset fork} (slot : Slot) (index : CommitteeIndex)
    (computed : processAttestation config checks state attestation = .ok after) :
    getBeaconCommittee after slot index = getBeaconCommittee state slot index := by
  obtain ⟨_, _, _, _, _, recorded, _, _, _⟩ := processAttestation_records before computed
  exact recordPendingAttestation_committee slot index recorded

/-- A proposer slashing preserves committees for current and previous attestations. -/
theorem processProposerSlashing_committee
    {state after : BeaconState preset .phase0} {slashing : ProposerSlashing}
    {slot : Slot} {index : CommitteeIndex}
    (past : computeEpochAtSlot preset slot ≤ getCurrentEpoch state)
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    getBeaconCommittee after slot index = getBeaconCommittee state slot index := by
  apply getBeaconCommittee_congr
  · exact active_indices_of_validator_queries
      (state.validators.bound (by decide)) (after.validators.bound (by decide))
      (processProposerSlashing_active (by decide) past computed)
  · apply getSeed_congr
    intro shifted _
    simp only [getRandaoMix, processProposerSlashing_randao (by decide) computed]

/-- An attester slashing preserves committees for every epoch already reached. -/
theorem processAttesterSlashing_committee
    {state after : BeaconState preset .phase0}
    {slashing : AttesterSlashing preset .phase0} {slot : Slot} {index : CommitteeIndex}
    (past : computeEpochAtSlot preset slot ≤ getCurrentEpoch state)
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    getBeaconCommittee after slot index = getBeaconCommittee state slot index := by
  apply getBeaconCommittee_congr
  · exact active_indices_of_validator_queries
      (state.validators.bound (by decide)) (after.validators.bound (by decide))
      (processAttesterSlashing_active (by decide) past computed)
  · apply getSeed_congr
    intro shifted _
    simp only [getRandaoMix, processAttesterSlashing_randao (by decide) computed]

/-- A frame that preserves the pending lists preserves their checked sources. -/
theorem PendingUnchanged.sources {before : fork < .altair}
    (pending : PendingUnchanged state after before) (frame : Frame state after)
    (holds : PendingSourcesMatch state before) : PendingSourcesMatch after before :=
  pendingSourcesMatch_of_fields holds frame.currentJustified frame.previousJustified
    pending.current pending.previous

/-- A frame that preserves the pending lists preserves their checked epochs. -/
theorem PendingUnchanged.epochs {before : fork < .altair}
    (pending : PendingUnchanged state after before) (frame : Frame state after)
    (holds : PendingEpochsMatch state before) : PendingEpochsMatch after before :=
  pendingEpochsMatch_of_fields holds frame.slot pending.current pending.previous

/-- All Phase 0 block operations preserve the checked sources of pending attestations.

Only attestation processing appends records, and it checks the source before appending. -/
theorem processOperations_pending_sources (before : fork < .altair)
    (holds : PendingSourcesMatch state before) {body : BeaconBlockBody preset fork}
    (computed : processOperations config checks state body = .ok after) :
    PendingSourcesMatch after before := by
  unfold processOperations at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := computed
  have notCapella : ¬Fork.shapella ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  simp only [notCapella, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at changesOk
  subst changesOk
  have proposersHold := foldlM_ok_invariant (fun s => PendingSourcesMatch s before)
    (fun _ _ _ prior ok => (pendingUnchanged_processProposerSlashing ok).sources
      (frame_processProposerSlashing ok) prior) holds proposersOk
  have attestersHold := foldlM_ok_invariant (fun s => PendingSourcesMatch s before)
    (fun _ _ _ prior ok => (pendingUnchanged_processAttesterSlashing ok).sources
      (frame_processAttesterSlashing ok) prior) proposersHold attestersOk
  have attestedHold := foldlM_ok_invariant (fun s => PendingSourcesMatch s before)
    (fun _ _ _ prior ok => processAttestation_sources before prior ok) attestersHold attestedOk
  have depositedHold := foldlM_ok_invariant (fun s => PendingSourcesMatch s before)
    (fun _ _ _ prior ok => (pendingUnchanged_processDeposit before ok).sources
      (frame_processDeposit before ok) prior) attestedHold depositedOk
  exact foldlM_ok_invariant (fun s => PendingSourcesMatch s before)
    (fun _ _ _ prior ok => (pendingUnchanged_processVoluntaryExit ok).sources
      (frame_processVoluntaryExit ok) prior) depositedHold exitsOk

/-- The header, RANDAO and deposit-contract vote do not change pending sources. -/
theorem processBlock_pending_sources (before : fork < .altair)
    (holds : PendingSourcesMatch state before) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    PendingSourcesMatch after before := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  simp only [processBlock, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨header, headerOk, randao, randaoOk, eth1, eth1Ok, operationsOk⟩ := computed
  have headerPending : PendingUnchanged state header before := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    exact ⟨rfl, rfl⟩
  have randaoPending : PendingUnchanged header randao before := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
    exact ⟨rfl, rfl⟩
  have eth1Pending : PendingUnchanged randao eth1 before := by
    obtain ⟨_, _, unchanged⟩ := processEth1Data_eq eth1Ok
    exact ⟨by rw [← unchanged], by rw [← unchanged]⟩
  apply processOperations_pending_sources before _ operationsOk
  exact (headerPending.trans (randaoPending.trans eth1Pending)).sources
    ((frame_processBlockHeader headerOk).trans
      ((frame_processRandao randaoOk).trans (frame_processEth1Data eth1Ok))) holds

/-- Block operations preserve the target and slot epochs checked at inclusion. -/
theorem processOperations_pending_epochs (before : fork < .altair)
    (holds : PendingEpochsMatch state before) {body : BeaconBlockBody preset fork}
    (computed : processOperations config checks state body = .ok after) :
    PendingEpochsMatch after before := by
  unfold processOperations at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := computed
  have notCapella : ¬Fork.shapella ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  simp only [notCapella, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at changesOk
  subst changesOk
  have proposersHold := foldlM_ok_invariant (fun s => PendingEpochsMatch s before)
    (fun _ _ _ prior ok => (pendingUnchanged_processProposerSlashing ok).epochs
      (frame_processProposerSlashing ok) prior) holds proposersOk
  have attestersHold := foldlM_ok_invariant (fun s => PendingEpochsMatch s before)
    (fun _ _ _ prior ok => (pendingUnchanged_processAttesterSlashing ok).epochs
      (frame_processAttesterSlashing ok) prior) proposersHold attestersOk
  have attestedHold := foldlM_ok_invariant (fun s => PendingEpochsMatch s before)
    (fun _ _ _ prior ok => processAttestation_epochs before prior ok) attestersHold attestedOk
  have depositedHold := foldlM_ok_invariant (fun s => PendingEpochsMatch s before)
    (fun _ _ _ prior ok => (pendingUnchanged_processDeposit before ok).epochs
      (frame_processDeposit before ok) prior) attestedHold depositedOk
  exact foldlM_ok_invariant (fun s => PendingEpochsMatch s before)
    (fun _ _ _ prior ok => (pendingUnchanged_processVoluntaryExit ok).epochs
      (frame_processVoluntaryExit ok) prior) depositedHold exitsOk

/-- The preliminary block steps preserve the pending lists and their assigned epochs. -/
theorem processBlock_pending_epochs (before : fork < .altair)
    (holds : PendingEpochsMatch state before) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    PendingEpochsMatch after before := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  simp only [processBlock, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨header, headerOk, randao, randaoOk, eth1, eth1Ok, operationsOk⟩ := computed
  have headerPending : PendingUnchanged state header before := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    exact ⟨rfl, rfl⟩
  have randaoPending : PendingUnchanged header randao before := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
    exact ⟨rfl, rfl⟩
  have eth1Pending : PendingUnchanged randao eth1 before := by
    obtain ⟨_, _, unchanged⟩ := processEth1Data_eq eth1Ok
    exact ⟨by rw [← unchanged], by rw [← unchanged]⟩
  apply processOperations_pending_epochs before _ operationsOk
  exact (headerPending.trans (randaoPending.trans eth1Pending)).epochs
    ((frame_processBlockHeader headerOk).trans
      ((frame_processRandao randaoOk).trans (frame_processEth1Data eth1Ok))) holds

/-- A pending record after block operations was already present or was included in this body.

The witness retains the successful slashing prefix and the exact attestation-processing call. -/
theorem processOperations_pending_origin (before : fork < .altair)
    {body : BeaconBlockBody preset fork} {pending : PendingAttestation preset}
    (computed : processOperations config checks state body = .ok after)
    (member : pending ∈ (after.currentEpochAttestations before).data ∨
      pending ∈ (after.previousEpochAttestations before).data) :
    (pending ∈ (state.currentEpochAttestations before).data ∨
      pending ∈ (state.previousEpochAttestations before).data) ∨
    ∃ proposers attesters earlier attestation later inclusion included,
      body.proposerSlashings.data.toList.foldlM (processProposerSlashing config checks) state =
        .ok proposers ∧
      body.attesterSlashings.data.toList.foldlM (processAttesterSlashing config checks) proposers =
        .ok attesters ∧
      body.attestations.data.toList = earlier ++ attestation :: later ∧
      earlier.foldlM (processAttestation config checks) attesters = .ok inclusion ∧
      processAttestation config checks inclusion attestation = .ok included ∧
      pending.data = attestation.data ∧
      pending.aggregationBits.bits = attestation.aggregationBits.bits := by
  unfold processOperations at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := computed
  have notCapella : ¬Fork.shapella ≤ fork :=
    Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  simp only [notCapella, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at changesOk
  subst changesOk
  have tailPending : PendingUnchanged attested exited before :=
    (PendingUnchanged.foldlM
      (fun _ _ _ ok => pendingUnchanged_processDeposit before ok) depositedOk).trans
        (PendingUnchanged.foldlM (fun _ _ _ ok => pendingUnchanged_processVoluntaryExit ok) exitsOk)
  have attestedMember := (tailPending.mem_iff pending).mp member
  rcases foldlM_processAttestation_pending_origin before attestedOk attestedMember with
      old | old | ⟨earlier, attestation, later, inclusion, included, split, earlierOk,
        includedOk, data, bits, _⟩
  · apply Or.inl
    have prefixPending : PendingUnchanged state attesters before :=
      (PendingUnchanged.foldlM
        (fun _ _ _ ok => pendingUnchanged_processProposerSlashing ok) proposersOk).trans
          (PendingUnchanged.foldlM
            (fun _ _ _ ok => pendingUnchanged_processAttesterSlashing ok) attestersOk)
    exact (prefixPending.mem_iff pending).mp (.inl old)
  · apply Or.inl
    have prefixPending : PendingUnchanged state attesters before :=
      (PendingUnchanged.foldlM
        (fun _ _ _ ok => pendingUnchanged_processProposerSlashing ok) proposersOk).trans
          (PendingUnchanged.foldlM
            (fun _ _ _ ok => pendingUnchanged_processAttesterSlashing ok) attestersOk)
    exact (prefixPending.mem_iff pending).mp (.inr old)
  · exact .inr ⟨proposers, attesters, earlier, attestation, later, inclusion, included,
      proposersOk, attestersOk, split, earlierOk, includedOk, data, bits⟩

/-- A pending record after a block either predates the block or has a successful inclusion in it.

The inclusion state is after the header, randomness and deposit-contract vote of this block. -/
theorem processBlock_pending_origin (before : fork < .altair)
    {block : BeaconBlock preset fork} {pending : PendingAttestation preset}
    (computed : processBlock config checks engine state block = .ok after)
    (member : pending ∈ (after.currentEpochAttestations before).data ∨
      pending ∈ (after.previousEpochAttestations before).data) :
    (pending ∈ (state.currentEpochAttestations before).data ∨
      pending ∈ (state.previousEpochAttestations before).data) ∨
    ∃ header randao eth1 proposers attesters earlier attestation later inclusion included,
      processBlockHeader state block = .ok header ∧
      processRandao config checks header block.body = .ok randao ∧
      processEth1Data (Nat.lt_trans before (by decide)) randao block.body = .ok eth1 ∧
      block.body.proposerSlashings.data.toList.foldlM
        (processProposerSlashing config checks) eth1 = .ok proposers ∧
      block.body.attesterSlashings.data.toList.foldlM
        (processAttesterSlashing config checks) proposers = .ok attesters ∧
      block.body.attestations.data.toList = earlier ++ attestation :: later ∧
      earlier.foldlM (processAttestation config checks) attesters = .ok inclusion ∧
      processAttestation config checks inclusion attestation = .ok included ∧
      pending.data = attestation.data ∧
      pending.aggregationBits.bits = attestation.aggregationBits.bits := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  simp only [processBlock, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨header, headerOk, randao, randaoOk, eth1, eth1Ok, operationsOk⟩ := computed
  rcases processOperations_pending_origin before operationsOk member with old |
      ⟨proposers, attesters, earlier, attestation, later, inclusion, included, rest⟩
  · apply Or.inl
    have headerPending : PendingUnchanged state header before := by
      obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
      exact ⟨rfl, rfl⟩
    have randaoPending : PendingUnchanged header randao before := by
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
      exact ⟨rfl, rfl⟩
    have eth1Pending : PendingUnchanged randao eth1 before := by
      obtain ⟨_, _, unchanged⟩ := processEth1Data_eq eth1Ok
      exact ⟨by rw [← unchanged], by rw [← unchanged]⟩
    exact ((headerPending.trans (randaoPending.trans eth1Pending)).mem_iff pending).mp old
  · exact .inr ⟨header, randao, eth1, proposers, attesters, earlier, attestation, later,
      inclusion, included, headerOk, randaoOk, eth1Ok, rest⟩

/-! ## The steps of an epoch -/

theorem frame_applyDeltas {rewards penalties : Array Gwei} {index : Nat}
    (computed : applyDeltas rewards penalties state index = .ok after) : Frame state after := by
  simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, raised, lowered⟩ := computed
  exact (frame_increaseBalance raised).trans (frame_decreaseBalance lowered)

theorem frame_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : Frame state after :=
  Frame.foldlM (fun _ _ _ ok => frame_applyDeltas ok) computed

theorem frame_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) : Frame state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact Frame.foldlM (fun _ _ _ ok => frame_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact frame_applyAllDeltas applied

/-- Joining the activation queue changes neither the exit nor the withdrawable epoch. -/
theorem queueForActivation_epochs {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    queued.exitEpoch = validator.exitEpoch ∧
      queued.withdrawableEpoch = validator.withdrawableEpoch := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ ⟨rfl, rfl⟩

theorem frame_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) : Frame state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, computed⟩ := computed
  obtain ⟨exitSame, withdrawableSame⟩ := queueForActivation_epochs queuedOk
  have sameBalance : queued.effectiveBalance = validator.effectiveBalance := by
    unfold queueForActivation at queuedOk
    split at queuedOk
    · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at queuedOk
      obtain ⟨_, _, rfl⟩ := queuedOk
      rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at queuedOk
      exact congrArg Validator.effectiveBalance queuedOk.symm
  have set : Frame state (state.setValidator index queued) := frame_setValidator
    (fun ordered => by
      rw [exitSame, withdrawableSame]
      exact ordered validator (mem_of_getValidator found))
    (fun bounded => by rw [sameBalance]; exact bounded validator (mem_of_getValidator found))
  split at computed
  · rw [liftAccessor_ok] at computed
    exact set.trans (frame_initiateValidatorExit computed)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

theorem frame_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) : Frame state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, _, rfl⟩ := computed
  exact frame_setValidator (fun ordered => ordered validator (mem_of_getValidator found))
    (fun bounded => bounded validator (mem_of_getValidator found))

theorem frame_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) : Frame state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  exact (Frame.foldlM (fun _ _ _ ok => frame_updateRegistryEntry ok) updatedOk).trans
    (Frame.foldlM (fun _ _ _ ok => frame_activateValidator ok) activated)

theorem frame_applySlashingPenalty {total adjusted : Gwei} {index : Nat}
    (computed : applySlashingPenalty state total adjusted index = .ok after) :
    Frame state after := by
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, _, _, lowered⟩ := computed
      exact frame_decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ Frame.refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_processSlashings (computed : processSlashings state = .ok after) :
    Frame state after := by
  unfold processSlashings at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, applied⟩ := computed
  exact Frame.foldlM (fun _ _ _ ok => frame_applySlashingPenalty ok) applied

theorem frame_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) : Frame state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_updateEffectiveBalance {index : Nat}
    (computed : updateEffectiveBalance state index = .ok after) : Frame state after := by
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨validator, found, _, _, _, updated, rfl⟩ := computed
  exact frame_setValidator (fun ordered => ordered validator (mem_of_getValidator found))
    (fun bounded => updatedEffectiveBalance_le_max
      (bounded validator (mem_of_getValidator found)) updated)

theorem frame_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) : Frame state after := by
  unfold processEffectiveBalanceUpdates at computed
  split at computed
  · cases computed
  exact Frame.foldlM (fun _ _ _ ok => frame_updateEffectiveBalance ok) computed

theorem frame_processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    Frame state after := by
  obtain ⟨_, _, rfl⟩ := processSlashingsReset_eq computed
  exact frame_slashings _ _

theorem frame_processRandaoMixesReset (computed : processRandaoMixesReset state = .ok after) :
    Frame state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processRandaoMixesReset_eq computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl

theorem frame_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : Frame state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ Frame.refl _

theorem frame_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) : Frame state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl

/-! ## Justification and the epoch transition -/

/-- Resetting Eth1 voting data preserves the registry. -/
theorem processEth1DataReset_validators {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    after.validators = state.validators := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, rest⟩ := computed
  split at rest <;> cases rest <;> rfl

/-- Extending the historical roots preserves the registry. -/
theorem processHistoricalRootsUpdate_validators
    (computed : processHistoricalRootsUpdate state = .ok after) :
    after.validators = state.validators := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, rest⟩ := computed
  split at rest
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at rest
    obtain ⟨_, _, _, _, rfl⟩ := rest
    rfl
  · cases rest
    rfl

/-- Rotating pending attestations preserves the registry. -/
theorem processParticipationRecordUpdates_validators
    (computed : processParticipationRecordUpdates state = .ok after) :
    after.validators = state.validators := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  cases computed
  rfl

/-- The current justified epoch is at most the previous epoch. -/
def JustifiedSettled (state : BeaconState preset fork) : Prop :=
  state.currentJustifiedCheckpoint.epoch ≤ getPreviousEpoch state

/-- The checked source of a Phase 0 attestation is no later than its target epoch.

For a current target, settledness puts the source in the previous epoch or earlier.

For a previous target, checkpoint order gives the same bound for the previous source. -/
theorem processAttestation_source_le_target (before : fork < .altair)
    (ordered : CheckpointsOrdered state) (settled : JustifiedSettled state)
    {attestation : Attestation preset fork}
    (computed : processAttestation config checks state attestation = .ok after) :
    attestation.data.source.epoch ≤ attestation.data.target.epoch := by
  obtain ⟨recent, _, _, _, _, _, source⟩ := processAttestation_checks before computed
  by_cases current : attestation.data.target.epoch = getCurrentEpoch state
  · simp only [current, ↓reduceIte] at source
    rw [source, current]
    exact UInt64.le_trans settled (getPreviousEpoch_le state)
  · simp only [current, ↓reduceIte] at source
    have previous : attestation.data.target.epoch = getPreviousEpoch state :=
      recent.resolve_right current
    rw [source, previous]
    exact UInt64.le_trans ordered.2 settled

/-- The properties that each valid block keeps before Altair. -/
structure Invariant (state : BeaconState preset fork) : Prop where
  balancesMatch : BalancesMatch state
  exitsOrdered : ExitsOrdered state
  ordered : CheckpointsOrdered state
  settled : JustifiedSettled state
  effectiveBalancesBounded : EffectiveBalancesBounded state

theorem getPreviousEpoch_toNat (state : BeaconState preset fork) :
    (getPreviousEpoch state).toNat = (getCurrentEpoch state).toNat - 1 := by
  unfold getPreviousEpoch saturatingSub
  split
  · rename_i lt
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt lt)]
    rfl
  · rename_i notLt
    rw [UInt64.lt_iff_toNat_lt] at notLt
    simp only [UInt64.toNat_one] at notLt
    simp only [UInt64.toNat_zero]
    omega

theorem Frame.invariant (frame : Frame state after) (holds : Invariant state) :
    Invariant after where
  balancesMatch := frame.balancesMatch holds.balancesMatch
  exitsOrdered := frame.exitsOrdered holds.exitsOrdered
  effectiveBalancesBounded := frame.effectiveBalancesBounded holds.effectiveBalancesBounded
  ordered := by
    have := holds.ordered
    unfold CheckpointsOrdered at this ⊢
    rw [frame.finalized, frame.previousJustified, frame.currentJustified]
    exact this
  settled := by
    have := holds.settled
    unfold JustifiedSettled getPreviousEpoch getCurrentEpoch at this ⊢
    rw [frame.currentJustified, frame.slot]
    exact this

/-- Justification and finalization keep the checkpoints in order, and the finalized epoch rises.

They change neither the slot, nor the registry, nor the balances.

The new current justified epoch is at most the current epoch. -/
theorem processJustificationAndFinalization_invariant (ordered : CheckpointsOrdered state)
    (settled : JustifiedSettled state)
    (computed : processJustificationAndFinalization state = .ok after) :
    CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch ∧
      after.currentJustifiedCheckpoint.epoch ≤ getCurrentEpoch state ∧
      after.slot = state.slot ∧ after.validators = state.validators ∧
      after.balances = state.balances := by
  obtain ⟨ordered', finalized⟩ :=
    processJustificationAndFinalization_ordered ordered settled computed
  have previous := getPreviousEpoch_le state
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact ⟨ordered', finalized, UInt64.le_trans settled previous, rfl, rfl, rfl⟩
  · obtain ⟨_, current, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    refine ⟨ordered', finalized, ?_, by rw [← rest], by rw [← rest], by rw [← rest]⟩
    rcases current with same | same | same
    · rw [same]
      exact UInt64.le_trans settled previous
    · rw [same]
      exact previous
    · rw [same]
      exact UInt64.le_refl _

/-- Before Altair, the epoch transition keeps the order of the checkpoints and the slot.

The finalized epoch does not decrease.

The current justified epoch ends at most at the current epoch.

The registry keeps one balance for each validator, and each exit no later than its withdrawal. -/
theorem processEpoch_invariant (altair : fork < .altair) (holds : Invariant state)
    (computed : processEpoch config state = .ok after) :
    after.slot = state.slot ∧ BalancesMatch after ∧ ExitsOrdered after ∧
      CheckpointsOrdered after ∧
      state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch ∧
      after.currentJustifiedCheckpoint.epoch ≤ getCurrentEpoch state ∧
      EffectiveBalancesBounded after := by
  have notAltair : ¬Fork.altair ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le altair le)
  simp only [processEpoch, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  obtain ⟨ordered, finalized, current, slot, validators, balances⟩ :=
    processJustificationAndFinalization_invariant holds.ordered holds.settled justifiedOk
  have frame : Frame justified after :=
    (frame_processRewardsAndPenalties rewardedOk).trans <|
    (frame_processRegistryUpdates registeredOk).trans <|
    (frame_processSlashings slashedOk).trans <|
    (frame_processEth1DataReset resetOk).trans <|
    (frame_processEffectiveBalanceUpdates balancedOk).trans <|
    (frame_processSlashingsReset clearedOk).trans <|
    (frame_processRandaoMixesReset mixedOk).trans <|
    (frame_processHistoricalRootsUpdate rootedOk).trans <|
    frame_processParticipationRecordUpdates rotated
  have balancesMatch : BalancesMatch justified := by
    have := holds.balancesMatch
    unfold BalancesMatch at this ⊢
    rw [validators, balances]
    exact this
  have exitsOrdered : ExitsOrdered justified := by
    have := holds.exitsOrdered
    unfold ExitsOrdered at this ⊢
    rw [validators]
    exact this
  refine ⟨frame.slot.trans slot, frame.balancesMatch balancesMatch,
    frame.exitsOrdered exitsOrdered, ?_, ?_, ?_, ?_⟩
  · unfold CheckpointsOrdered at ordered ⊢
    rw [frame.finalized, frame.previousJustified, frame.currentJustified]
    exact ordered
  · rw [frame.finalized]
    exact finalized
  · rw [frame.currentJustified]
    exact current
  · apply frame.effectiveBalancesBounded
    rw [EffectiveBalancesBounded, validators]
    exact holds.effectiveBalancesBounded

/-- A Phase 0 epoch transition preserves the current and previous attester seeds.

The only mix write is to the next epoch's circular-buffer position. -/
theorem processEpoch_attester_seed
    {state after : BeaconState preset .phase0}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (holds : Invariant state)
    {epoch : Epoch}
    (recent : epoch = getCurrentEpoch state ∨ epoch.toNat + 1 = (getCurrentEpoch state).toNat)
    (computed : processEpoch config state = .ok after) :
    getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
  simp only [processEpoch, show ¬Fork.altair ≤ Fork.phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have justifiedMixes := processJustificationAndFinalization_randao justifiedOk
  have rewardedMixes := processRewardsAndPenalties_randao (by decide) rewardedOk
  have registeredMixes := processRegistryUpdates_randao (by decide) registeredOk
  have slashedMixes := processSlashings_randao slashedOk
  have resetMixes := processEth1DataReset_randao resetOk
  have balancedMixes := processEffectiveBalanceUpdates_randao balancedOk
  have clearedMixes : cleared.randaoMixes = balanced.randaoMixes := by
    obtain ⟨_, _, rfl⟩ := processSlashingsReset_eq clearedOk
    rfl
  have rootedMixes := processHistoricalRootsUpdate_randao rootedOk
  have rotatedMixes := processParticipationRecordUpdates_randao rotated
  have slot := (processJustificationAndFinalization_invariant
    holds.ordered holds.settled justifiedOk).2.2.2.1
  have frame := (frame_processRewardsAndPenalties rewardedOk).trans <|
    (frame_processRegistryUpdates registeredOk).trans <|
    (frame_processSlashings slashedOk).trans <|
    (frame_processEth1DataReset resetOk).trans <|
    (frame_processEffectiveBalanceUpdates balancedOk).trans <|
    frame_processSlashingsReset clearedOk
  have seed := processRandaoMixesReset_attester_seed positive history mixedOk
    (by simpa only [getCurrentEpoch, frame.slot, slot] using recent)
  have beforeSeed : getSeed cleared epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
    apply getSeed_congr
    intro shifted _
    simp only [getRandaoMix, clearedMixes, balancedMixes, resetMixes, slashedMixes,
      registeredMixes, rewardedMixes, justifiedMixes]
  have afterSeed : getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed mixed epoch DOMAIN_BEACON_ATTESTER := by
    apply getSeed_congr
    intro shifted _
    simp only [getRandaoMix, rotatedMixes, rootedMixes]
  exact afterSeed.trans (seed.trans beforeSeed)

/-- A Phase 0 epoch preserves committees for its current and all earlier epochs.

The registry schedules changes for later epochs, and balance updates do not reassign committees. -/
theorem processEpoch_active_indices (before : fork < .altair) (holds : Invariant state)
    {epoch : Epoch} (past : epoch ≤ getCurrentEpoch state)
    (computed : processEpoch config state = .ok after) :
    getActiveValidatorIndices after epoch = getActiveValidatorIndices state epoch := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  simp only [processEpoch, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  obtain ⟨_, _, _, slot, validators, _⟩ :=
    processJustificationAndFinalization_invariant holds.ordered holds.settled justifiedOk
  have rewardRegistry := processRewardsAndPenalties_validators rewardedOk
  have rewardSlot := (frame_processRewardsAndPenalties rewardedOk).slot
  have recent : epoch ≤ getCurrentEpoch rewarded := by
    simpa only [getCurrentEpoch, rewardSlot, slot] using past
  have registry := processRegistryUpdates_active_indices
    (Nat.lt_trans before (by decide)) (rewarded.validators.bound (Nat.lt_trans before (by decide)))
    recent registeredOk
  have slashingRegistry := processSlashings_validators slashedOk
  have resetRegistry := processEth1DataReset_validators resetOk
  have effective := active_indices_of_validator_queries (epoch := epoch)
    (reset.validators.bound (Nat.lt_trans before (by decide)))
    (balanced.validators.bound (Nat.lt_trans before (by decide)))
    (processEffectiveBalanceUpdates_active (epoch := epoch)
      (reset.validators.bound (Nat.lt_trans before (by decide))) balancedOk)
  have clearedRegistry : cleared.validators = balanced.validators := by
    obtain ⟨_, _, rfl⟩ := processSlashingsReset_eq clearedOk
    rfl
  have mixedRegistry : mixed.validators = cleared.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    rfl
  have rootedRegistry := processHistoricalRootsUpdate_validators rootedOk
  have rotatedRegistry := processParticipationRecordUpdates_validators rotated
  calc
    getActiveValidatorIndices after epoch = getActiveValidatorIndices balanced epoch := by
      simp only [getActiveValidatorIndices, rotatedRegistry, rootedRegistry, mixedRegistry,
        clearedRegistry]
    _ = getActiveValidatorIndices reset epoch := effective
    _ = getActiveValidatorIndices registered epoch := by
      simp only [getActiveValidatorIndices, resetRegistry, slashingRegistry]
    _ = getActiveValidatorIndices rewarded epoch := registry
    _ = getActiveValidatorIndices state epoch := by
      simp only [getActiveValidatorIndices, rewardRegistry, validators]

/-- The bits and checkpoints at the end of a Phase 0 epoch come from its justification step.

All later epoch operations preserve those fields, including participation rotation.

The witness is the actual successful call at the start of `processEpoch`. -/
theorem processEpoch_justification (before : fork < .altair)
    (computed : processEpoch config state = .ok after) :
    ∃ justified, processJustificationAndFinalization state = .ok justified ∧
      after.justificationBits = justified.justificationBits ∧
      after.currentJustifiedCheckpoint = justified.currentJustifiedCheckpoint ∧
      after.previousJustifiedCheckpoint = justified.previousJustifiedCheckpoint ∧
      after.finalizedCheckpoint = justified.finalizedCheckpoint := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  simp only [processEpoch, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have frame : Frame justified after :=
    (frame_processRewardsAndPenalties rewardedOk).trans <|
    (frame_processRegistryUpdates registeredOk).trans <|
    (frame_processSlashings slashedOk).trans <|
    (frame_processEth1DataReset resetOk).trans <|
    (frame_processEffectiveBalanceUpdates balancedOk).trans <|
    (frame_processSlashingsReset clearedOk).trans <|
    (frame_processRandaoMixesReset mixedOk).trans <|
    (frame_processHistoricalRootsUpdate rootedOk).trans <|
    frame_processParticipationRecordUpdates rotated
  exact ⟨justified, justifiedOk, frame.justificationBits, frame.currentJustified,
    frame.previousJustified, frame.finalized⟩

/-- Phase 0 epoch processing restores the checked sources after rotating participation.

The intervening rewards, registry updates, penalties and resets preserve the pending lists. -/
theorem processEpoch_pending_sources (before : fork < .altair)
    (holds : PendingSourcesMatch state before)
    (early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      state.currentJustifiedCheckpoint = state.previousJustifiedCheckpoint)
    (computed : processEpoch config state = .ok after) : PendingSourcesMatch after before := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  simp only [processEpoch, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have pending : PendingUnchanged justified rooted before :=
    (pendingUnchanged_processRewardsAndPenalties rewardedOk).trans <|
    (pendingUnchanged_processRegistryUpdates registeredOk).trans <|
    (pendingUnchanged_processSlashings slashedOk).trans <|
    (pendingUnchanged_processEth1DataReset resetOk).trans <|
    (pendingUnchanged_processEffectiveBalanceUpdates balancedOk).trans <|
    (pendingUnchanged_processSlashingsReset clearedOk).trans <|
    (pendingUnchanged_processRandaoMixesReset mixedOk).trans <|
    pendingUnchanged_processHistoricalRootsUpdate rootedOk
  have frame : Frame justified rooted :=
    (frame_processRewardsAndPenalties rewardedOk).trans <|
    (frame_processRegistryUpdates registeredOk).trans <|
    (frame_processSlashings slashedOk).trans <|
    (frame_processEth1DataReset resetOk).trans <|
    (frame_processEffectiveBalanceUpdates balancedOk).trans <|
    (frame_processSlashingsReset clearedOk).trans <|
    (frame_processRandaoMixesReset mixedOk).trans <|
    frame_processHistoricalRootsUpdate rootedOk
  apply processParticipationRecordUpdates_sources before _ rotated
  intro entry member
  rw [pending.current] at member
  rw [frame.previousJustified]
  exact processJustificationAndFinalization_sources_for_rotation before holds early
    justifiedOk entry member

/-- In the first two epochs, epoch processing keeps both justified checkpoints unchanged. -/
theorem processEpoch_justified_of_early (before : fork < .altair)
    (early : getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (computed : processEpoch config state = .ok after) :
    after.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
      after.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint := by
  obtain ⟨justified, justifiedOk, _, current, previous, _⟩ :=
    processEpoch_justification before computed
  unfold processJustificationAndFinalization at justifiedOk
  split at justifiedOk
  · exact absurd ‹_› (Nat.not_le_of_lt before)
  simp only [pure, Except.pure, Except.ok.injEq] at justifiedOk
  subst justifiedOk
  exact ⟨current, previous⟩

/-- Epoch processing rotates the current pending records unchanged and clears the current list.

The records retain their target and slot epochs until the following slot increment. -/
theorem processEpoch_pending_rotation (before : fork < .altair)
    (computed : processEpoch config state = .ok after) :
    after.previousEpochAttestations before = state.currentEpochAttestations before ∧
      (after.currentEpochAttestations before).data = #[] := by
  have notAltair : ¬Fork.altair ≤ fork := Nat.not_le_of_lt before
  simp only [processEpoch, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have justificationPending : PendingUnchanged state justified before := by
    rcases processJustificationAndFinalization_ok justifiedOk with rfl | ⟨_, _, _, weighed⟩
    · exact .refl _ _
    · obtain ⟨_, _, _, unchanged⟩ := weighJustificationAndFinalization_checkpoints weighed
      exact ⟨by rw [← unchanged], by rw [← unchanged]⟩
  have pending : PendingUnchanged state rooted before := justificationPending.trans <|
    (pendingUnchanged_processRewardsAndPenalties rewardedOk).trans <|
    (pendingUnchanged_processRegistryUpdates registeredOk).trans <|
    (pendingUnchanged_processSlashings slashedOk).trans <|
    (pendingUnchanged_processEth1DataReset resetOk).trans <|
    (pendingUnchanged_processEffectiveBalanceUpdates balancedOk).trans <|
    (pendingUnchanged_processSlashingsReset clearedOk).trans <|
    (pendingUnchanged_processRandaoMixesReset mixedOk).trans <|
    pendingUnchanged_processHistoricalRootsUpdate rootedOk
  obtain ⟨result, resultOk, previous, current, _⟩ :=
    processParticipationRecordUpdates_eq (state := rooted) before
  rw [resultOk] at rotated
  cases rotated
  exact ⟨previous.trans pending.current, current⟩

/-- A newest true bit after an eligible Phase 0 epoch has a current target balance above threshold.

The balances are read before rewards, penalties, registry updates and effective-balance updates.

Thus later balance changes cannot be substituted for the weights of this justification. -/
theorem processEpoch_current_bit (before : fork < .altair)
    (computed : processEpoch config state = .ok after)
    (eligible : ¬getCurrentEpoch state ≤ GENESIS_EPOCH + 1)
    (bit : after.justificationBits.bits[0] = true) :
    ∃ justified previous current total previousBalance currentBalance,
      processJustificationAndFinalization state = .ok justified ∧
      getMatchingTargetAttestations state before (getPreviousEpoch state) = .ok previous ∧
      getMatchingTargetAttestations state before (getCurrentEpoch state) = .ok current ∧
      getTotalActiveBalance state = .ok total ∧
      getAttestingBalance state previous = .ok previousBalance ∧
      getAttestingBalance state current = .ok currentBalance ∧
      weighJustificationAndFinalization state total previousBalance currentBalance =
        .ok justified ∧
      2 * total.toNat ≤ 3 * currentBalance.toNat := by
  obtain ⟨justified, justifiedOk, bits, _⟩ := processEpoch_justification before computed
  rw [bits] at bit
  obtain ⟨previous, current, total, previousBalance, currentBalance, rest⟩ :=
    processJustificationAndFinalization_current_bit before justifiedOk eligible bit
  exact ⟨justified, previous, current, total, previousBalance, currentBalance, justifiedOk, rest⟩

/-! ## Slots and blocks -/

theorem getCurrentEpoch_toNat (state : BeaconState preset fork) :
    (getCurrentEpoch state).toNat = state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
  simp [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]

theorem frame_processSlot (computed : processSlot state = .ok after) : Frame state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact Frame.of_validators ⟨rfl, rfl⟩ rfl rfl rfl rfl rfl rfl

/-- Caching roots at a slot preserves both lists of pending attestations. -/
theorem pendingUnchanged_processSlot {before : fork < .altair}
    (computed : processSlot state = .ok after) : PendingUnchanged state after before := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact ⟨rfl, rfl⟩

/-- Pending sources match, and the two justified checkpoints agree during the first two epochs.

The early equality permits participation rotation while justification is still disabled. -/
def PendingSourcesInvariant (state : BeaconState preset fork) (before : fork < .altair) : Prop :=
  PendingSourcesMatch state before ∧
    (getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      state.currentJustifiedCheckpoint = state.previousJustifiedCheckpoint)

/-- A Phase 0 block preserves pending sources and the early checkpoint equality. -/
theorem processBlock_pending_sources_invariant (before : fork < .altair)
    (holds : PendingSourcesInvariant state before) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    PendingSourcesInvariant after before := by
  have frame := frame_processBlock before computed
  refine ⟨processBlock_pending_sources before holds.1 computed, ?_⟩
  intro early
  rw [frame.currentJustified, frame.previousJustified]
  apply holds.2
  simpa only [getCurrentEpoch, frame.slot] using early

/-- Slot processing preserves checked pending sources, including across epoch boundaries. -/
theorem advanceSlot_pending_sources (before : fork < .altair)
    (holds : PendingSourcesInvariant state before)
    (computed : advanceSlot config state = .ok after) :
    PendingSourcesInvariant after before := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have frame := frame_processSlot cachedOk
  have cachedPending : PendingUnchanged state cached before := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl⟩
  have sources := cachedPending.sources frame holds.1
  have earlyCached : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1 →
      cached.currentJustifiedCheckpoint = cached.previousJustifiedCheckpoint := by
    intro early
    rw [frame.currentJustified, frame.previousJustified]
    apply holds.2
    simpa only [getCurrentEpoch, frame.slot] using early
  have epochLe : getCurrentEpoch cached ≤ computeEpochAtSlot preset next := by
    rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, frame.slot]
    simp only [computeEpochAtSlot, UInt64.toNat_div]
    exact Nat.div_le_div_right (by omega)
  unfold epochIfLast at epochedOk
  split at epochedOk
  · have epochedSources := processEpoch_pending_sources before sources earlyCached epochedOk
    refine ⟨⟨epochedSources.1, epochedSources.2⟩, ?_⟩
    intro early
    have earlyInput : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1 :=
      UInt64.le_trans epochLe early
    obtain ⟨current, previous⟩ := processEpoch_justified_of_early before earlyInput epochedOk
    exact current.trans ((earlyCached earlyInput).trans previous.symm)
  · cases epochedOk
    exact ⟨sources, fun early => earlyCached (UInt64.le_trans epochLe early)⟩

/-- A successful run of slots preserves the pending-source invariant. -/
theorem advanceSlots_pending_sources (before : fork < .altair) :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      PendingSourcesInvariant state before → advanceSlots config count state = .ok after →
        PendingSourcesInvariant after before
  | 0, _, _, holds, computed => by
    cases computed
    exact holds
  | count + 1, _, _, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    exact advanceSlots_pending_sources before count (advanceSlot_pending_sources before holds first)
      rest

/-- The complete Phase 0 state transition preserves the pending-source invariant. -/
theorem stateTransition_pending_sources (before : fork < .altair)
    (holds : PendingSourcesInvariant state before) {block : SignedBeaconBlock preset fork}
    {validateResult : Bool}
    (computed : stateTransition config checks engine state block validateResult = .ok after) :
    PendingSourcesInvariant after before := by
  simp only [stateTransition, bind_ok_iff] at computed
  obtain ⟨atSlot, slots, applied⟩ := computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slots
  obtain ⟨_, _, advanced⟩ := slots
  have atSlotHolds := advanceSlots_pending_sources before _ holds advanced
  simp only [applySignedBlock, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, processed, _, _, rfl⟩ := applied
  exact processBlock_pending_sources_invariant before atSlotHolds processed

/-- A slot step keeps each pending record in the list for its checked target and slot epoch. -/
theorem advanceSlot_pending_epochs (before : fork < .altair)
    (holds : PendingEpochsMatch state before)
    (computed : advanceSlot config state = .ok after) : PendingEpochsMatch after before := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have frame := frame_processSlot cachedOk
  have cachedPending : PendingUnchanged state cached before := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl⟩
  have cachedHolds := cachedPending.epochs frame holds
  simp only [UInt64.toNat_one] at sum
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have boundary' : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa [UInt64.toNat_mod] using congrArg UInt64.toNat boundary
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
      rw [sum]
      exact Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero (sum ▸ boundary'))
    have previousEpoch : getPreviousEpoch { epoched with slot := next } =
        getCurrentEpoch cached := by
      apply UInt64.toNat_inj.mp
      rw [getPreviousEpoch_toNat, getCurrentEpoch_toNat, getCurrentEpoch_toNat, frame.slot]
      change next.toNat / preset.SLOTS_PER_EPOCH.toNat - 1 =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat
      rw [step, Nat.add_sub_cancel]
    obtain ⟨previous, current⟩ := processEpoch_pending_rotation before epochedOk
    constructor
    · intro entry member
      rw [current] at member
      simp at member
    · intro entry member
      rw [previous] at member
      rw [previousEpoch]
      exact cachedHolds.1 entry member
  · rename_i notBoundary
    cases epochedOk
    have notBoundary' : ¬preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 := by
      intro divides
      apply notBoundary
      apply UInt64.toNat_inj.mp
      simpa [UInt64.toNat_mod, sum] using Nat.mod_eq_zero_of_dvd divides
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      rw [sum]
      exact Nat.succ_div_of_not_dvd notBoundary'
    have sameEpoch : getCurrentEpoch { cached with slot := next } = getCurrentEpoch cached := by
      apply UInt64.toNat_inj.mp
      simpa only [getCurrentEpoch_toNat, frame.slot] using step
    have samePrevious : getPreviousEpoch { cached with slot := next } =
        getPreviousEpoch cached := by simp only [getPreviousEpoch, sameEpoch]
    constructor
    · intro entry member
      rw [sameEpoch]
      exact cachedHolds.1 entry member
    · intro entry member
      rw [samePrevious]
      exact cachedHolds.2 entry member

/-- Advancing slots preserves the checked epochs of pending attestations. -/
theorem advanceSlots_pending_epochs (before : fork < .altair) :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      PendingEpochsMatch state before → advanceSlots config count state = .ok after →
        PendingEpochsMatch after before
  | 0, _, _, holds, computed => by
    cases computed
    exact holds
  | count + 1, _, _, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    exact advanceSlots_pending_epochs before count (advanceSlot_pending_epochs before holds first)
      rest

/-- The complete Phase 0 transition preserves the checked epochs of pending attestations. -/
theorem stateTransition_pending_epochs (before : fork < .altair)
    (holds : PendingEpochsMatch state before) {block : SignedBeaconBlock preset fork}
    {validateResult : Bool}
    (computed : stateTransition config checks engine state block validateResult = .ok after) :
    PendingEpochsMatch after before := by
  simp only [stateTransition, bind_ok_iff] at computed
  obtain ⟨atSlot, slots, applied⟩ := computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slots
  obtain ⟨_, _, advanced⟩ := slots
  have atSlotHolds := advanceSlots_pending_epochs before _ holds advanced
  simp only [applySignedBlock, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, processed, _, _, rfl⟩ := applied
  exact processBlock_pending_epochs before atSlotHolds processed

/-- Slot processing cannot create a pending attestation.

At an epoch boundary it can only retain the old current list as the previous list. -/
theorem advanceSlot_pending_mem (before : fork < .altair)
    {pending : PendingAttestation preset}
    (computed : advanceSlot config state = .ok after)
    (member : pending ∈ (after.currentEpochAttestations before).data ∨
      pending ∈ (after.previousEpochAttestations before).data) :
    pending ∈ (state.currentEpochAttestations before).data ∨
      pending ∈ (state.previousEpochAttestations before).data := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have kept : PendingUnchanged state cached before := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl⟩
  apply (kept.mem_iff pending).mp
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨previous, current⟩ := processEpoch_pending_rotation before epochedOk
    rcases member with member | member
    · rw [current] at member
      simp at member
    · exact .inl (previous ▸ member)
  · cases epochedOk
    exact member

/-- No number of successful slot steps can create a pending attestation. -/
theorem advanceSlots_pending_mem (before : fork < .altair) {pending : PendingAttestation preset} :
    ∀ (count : Nat) {state after : BeaconState preset fork},
      advanceSlots config count state = .ok after →
      (pending ∈ (after.currentEpochAttestations before).data ∨
        pending ∈ (after.previousEpochAttestations before).data) →
      pending ∈ (state.currentEpochAttestations before).data ∨
        pending ∈ (state.previousEpochAttestations before).data
  | 0, _, _, computed, member => by
    cases computed
    exact member
  | count + 1, _, _, computed, member => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    exact advanceSlot_pending_mem before first (advanceSlots_pending_mem before count rest member)

/-- Successful processing of an attestation in a concrete block, with its stored data and bits.

The state arguments are the actual intermediate states of block processing.

This predicate records execution, not an abstract vote or a supermajority relation. -/
def PendingIncludedInBlock (config : Config) (checks : SignatureChecks)
    (before : fork < .altair) (atSlot : BeaconState preset fork)
    (block : BeaconBlock preset fork) (pending : PendingAttestation preset) : Prop :=
  ∃ header randao eth1 proposers attesters earlier attestation later inclusion included,
    processBlockHeader atSlot block = .ok header ∧
    processRandao config checks header block.body = .ok randao ∧
    processEth1Data (Nat.lt_trans before (by decide)) randao block.body = .ok eth1 ∧
    block.body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing config checks) eth1 = .ok proposers ∧
    block.body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing config checks) proposers = .ok attesters ∧
    block.body.attestations.data.toList = earlier ++ attestation :: later ∧
    earlier.foldlM (processAttestation config checks) attesters = .ok inclusion ∧
    processAttestation config checks inclusion attestation = .ok included ∧
    pending.data = attestation.data ∧
    pending.aggregationBits.bits = attestation.aggregationBits.bits

/-- A concrete inclusion supplies the checked source and a valid indexed signature.

The signature check uses the state after recording the pending attestation, as processing does. -/
theorem PendingIncludedInBlock.checked {before : fork < .altair}
    {atSlot : BeaconState preset fork} {block : BeaconBlock preset fork}
    {pending : PendingAttestation preset}
    (included : PendingIncludedInBlock config checks before atSlot block pending) :
    ∃ (inclusion recorded : BeaconState preset fork) (attestation : Attestation preset fork)
      (indexed : IndexedAttestation preset fork),
      processAttestation config checks inclusion attestation = .ok recorded ∧
      pending.data = attestation.data ∧
      pending.aggregationBits.bits = attestation.aggregationBits.bits ∧
      pending.data.source =
        (if pending.data.target.epoch = getCurrentEpoch inclusion then
          inclusion.currentJustifiedCheckpoint else inclusion.previousJustifiedCheckpoint) ∧
      getIndexedAttestation recorded attestation = .ok indexed ∧
      indexed.data = pending.data ∧
      isValidIndexedAttestation config checks recorded indexed = .ok true := by
  obtain ⟨_, _, _, _, _, _, attestation, _, inclusion, recorded, _, _, _, _, _, _, _,
    computed, data, bits⟩ := included
  obtain ⟨_, _, _, _, _, _, indexed, indexedOk, valid⟩ :=
    processAttestation_records before computed
  refine ⟨inclusion, recorded, attestation, indexed, computed, data, bits, ?_,
    indexedOk, ?_, valid⟩
  · rw [data]
    exact (processAttestation_checks before computed).2.2.2.2.2.2
  · simp only [getIndexedAttestation, bind_ok_iff] at indexedOk
    obtain ⟨_, _, result⟩ := indexedOk
    split at result
    · cases result
      exact data.symm
    · cases result

/-- A pending record's inclusion checked the same committee as its block's input state.

Slashings and earlier attestations in the block do not change historical assignments. -/
theorem PendingIncludedInBlock.committee
    {atSlot : BeaconState preset .phase0}
    {block : BeaconBlock preset .phase0} {pending : PendingAttestation preset}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (included : PendingIncludedInBlock config checks (by decide) atSlot block pending) :
    ∃ (inclusion recorded : BeaconState preset .phase0)
      (attestation : Attestation preset .phase0),
      processAttestation config checks inclusion attestation = .ok recorded ∧
      pending.data = attestation.data ∧
      pending.aggregationBits.bits = attestation.aggregationBits.bits ∧
      (computeEpochAtSlot preset pending.data.slot = getCurrentEpoch atSlot ∨
        (computeEpochAtSlot preset pending.data.slot).toNat + 1 =
          (getCurrentEpoch atSlot).toNat) ∧
      getBeaconCommittee recorded pending.data.slot pending.data.index =
        getBeaconCommittee atSlot pending.data.slot pending.data.index := by
  obtain ⟨header, randao, eth1, proposers, attesters, earlier, attestation, later,
    inclusion, recorded, headerOk, randaoOk, eth1Ok, proposersOk, attestersOk,
    _, earlierOk, attestationOk, data, bits⟩ := included
  have attChecks := processAttestation_checks (by decide) attestationOk
  have inclusionPast : computeEpochAtSlot preset pending.data.slot ≤
      getCurrentEpoch inclusion := by
    rw [data, ← attChecks.2.1]
    rcases attChecks.1 with previous | current
    · rw [previous]
      exact getPreviousEpoch_le _
    · rw [current]
      exact UInt64.le_refl _
  have earlierFrame := Frame.foldlM
    (fun _ _ _ ok => frame_processAttestation (by decide) ok) earlierOk
  have attestersFrame := Frame.foldlM
    (fun _ _ _ ok => frame_processAttesterSlashing ok) attestersOk
  have proposersFrame := Frame.foldlM
    (fun _ _ _ ok => frame_processProposerSlashing ok) proposersOk
  have headerFrame := frame_processBlockHeader headerOk
  have randaoFrame := frame_processRandao randaoOk
  have eth1Frame := frame_processEth1Data eth1Ok
  have inputRecent : computeEpochAtSlot preset pending.data.slot =
        getCurrentEpoch atSlot ∨
      (computeEpochAtSlot preset pending.data.slot).toNat + 1 =
        (getCurrentEpoch atSlot).toNat := by
    have same : getCurrentEpoch inclusion = getCurrentEpoch atSlot := by
      simp only [getCurrentEpoch, earlierFrame.slot, attestersFrame.slot,
        proposersFrame.slot, eth1Frame.slot, randaoFrame.slot, headerFrame.slot]
    rw [data, ← attChecks.2.1]
    rcases attChecks.1 with previous | current
    · rw [previous, getPreviousEpoch_toNat, same]
      by_cases zero : (getCurrentEpoch atSlot).toNat = 0
      · left
        apply UInt64.toNat_inj.mp
        simp only [getPreviousEpoch_toNat, same, zero, Nat.zero_sub]
      · right
        omega
    · exact .inl (current.trans same)
  have earlierCommittee := foldlM_ok_invariant
    (fun s => getBeaconCommittee s pending.data.slot pending.data.index =
      getBeaconCommittee attesters pending.data.slot pending.data.index)
    (fun _ _ _ prior ok =>
      (processAttestation_committee (by decide) _ _ ok).trans prior) rfl earlierOk
  have attestersCommittee := foldlM_ok_invariant
    (fun s => s.slot = proposers.slot ∧
      getBeaconCommittee s pending.data.slot pending.data.index =
        getBeaconCommittee proposers pending.data.slot pending.data.index)
    (fun s _ _ prior ok => by
      have past : computeEpochAtSlot preset pending.data.slot ≤ getCurrentEpoch s := by
        simpa only [getCurrentEpoch, prior.1, earlierFrame.slot, attestersFrame.slot] using
          inclusionPast
      exact ⟨(frame_processAttesterSlashing ok).slot.trans prior.1,
        (processAttesterSlashing_committee past ok).trans prior.2⟩)
    (show proposers.slot = proposers.slot ∧ _ from ⟨rfl, rfl⟩) attestersOk
  have proposersCommittee := foldlM_ok_invariant
    (fun s => s.slot = eth1.slot ∧
      getBeaconCommittee s pending.data.slot pending.data.index =
        getBeaconCommittee eth1 pending.data.slot pending.data.index)
    (fun s _ _ prior ok => by
      have past : computeEpochAtSlot preset pending.data.slot ≤ getCurrentEpoch s := by
        simpa only [getCurrentEpoch, prior.1, earlierFrame.slot, attestersFrame.slot,
          proposersFrame.slot] using inclusionPast
      exact ⟨(frame_processProposerSlashing ok).slot.trans prior.1,
        (processProposerSlashing_committee past ok).trans prior.2⟩)
    (show eth1.slot = eth1.slot ∧ _ from ⟨rfl, rfl⟩) proposersOk
  have eth1Committee : getBeaconCommittee eth1 pending.data.slot pending.data.index =
      getBeaconCommittee randao pending.data.slot pending.data.index := by
    obtain ⟨_, _, rest⟩ := processEth1Data_eq eth1Ok
    rw [← rest]
    rfl
  have headerCommittee : getBeaconCommittee header pending.data.slot pending.data.index =
      getBeaconCommittee atSlot pending.data.slot pending.data.index := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    rfl
  have randaoCommittee : getBeaconCommittee randao pending.data.slot pending.data.index =
      getBeaconCommittee header pending.data.slot pending.data.index := by
    apply getBeaconCommittee_congr
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
      rfl
    · exact processRandao_attester_seed positive history randaoOk
        (by simpa only [getCurrentEpoch, headerFrame.slot] using inputRecent)
  exact ⟨inclusion, recorded, attestation, attestationOk, data, bits, inputRecent,
    (processAttestation_committee (by decide) _ _ attestationOk).trans
      (earlierCommittee.trans (attestersCommittee.2.trans
        (proposersCommittee.2.trans (eth1Committee.trans
          (randaoCommittee.trans headerCommittee)))))⟩

/-- Pending indices reconstructed at a block's input are its authenticated signer indices.

The inclusion witness supplies the actual signature check, rather than a separate vote premise. -/
theorem PendingIncludedInBlock.signers
    {atSlot : BeaconState preset .phase0}
    {block : BeaconBlock preset .phase0} {pending : PendingAttestation preset}
    {indices : List ValidatorIndex}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (included : PendingIncludedInBlock config checks (by decide) atSlot block pending)
    (computed : getPendingAttestingIndices atSlot pending = .ok indices) :
    ∃ (recorded : BeaconState preset .phase0)
      (attestation : Attestation preset .phase0)
      (indexed : IndexedAttestation preset .phase0),
      getIndexedAttestation recorded attestation = .ok indexed ∧
      indexed.attestingIndices.data = (sortedSet indices).toArray ∧
      indexed.data = pending.data ∧ indexed.signature = attestation.signature ∧
      isValidIndexedAttestation config checks recorded indexed = .ok true := by
  obtain ⟨inclusion, recorded, attestation, processed, data, bits, _, committee⟩ :=
    included.committee positive history
  obtain ⟨_, _, _, _, _, _, indexed, indexedOk, valid⟩ :=
    processAttestation_records (by decide) processed
  obtain ⟨listed, indexedData, signature⟩ :=
    getPendingAttestingIndices_eq_included (by decide) data bits committee computed indexedOk
  exact ⟨recorded, attestation, indexed, indexedOk, listed, indexedData, signature, valid⟩

/-- Every new pending record of a state transition has an inclusion in its signed block. -/
theorem stateTransition_pending_origin (before : fork < .altair)
    {block : SignedBeaconBlock preset fork} {pending : PendingAttestation preset}
    {validateResult : Bool}
    (computed : stateTransition config checks engine state block validateResult = .ok after)
    (member : pending ∈ (after.currentEpochAttestations before).data ∨
      pending ∈ (after.previousEpochAttestations before).data) :
    (pending ∈ (state.currentEpochAttestations before).data ∨
      pending ∈ (state.previousEpochAttestations before).data) ∨
    ∃ atSlot, processSlots config state block.message.slot = .ok atSlot ∧
      PendingIncludedInBlock config checks before atSlot block.message pending := by
  simp only [stateTransition, bind_ok_iff] at computed
  obtain ⟨atSlot, slots, applied⟩ := computed
  simp only [applySignedBlock, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, processed, _, _, rfl⟩ := applied
  rcases processBlock_pending_origin before processed member with old | included
  · apply Or.inl
    simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slots
    obtain ⟨_, _, advanced⟩ := slots
    exact advanceSlots_pending_mem before _ advanced old
  · exact .inr ⟨atSlot, slots, included⟩

/-- A pending record after a chain was already present or was included in one of its blocks.

The successful block prefix identifies the state whose committees checked the inclusion. -/
theorem stateTransition_chain_pending_origin (before : fork < .altair)
    {blocks : List (SignedBeaconBlock preset fork)} {pending : PendingAttestation preset}
    {validateResult : Bool}
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block validateResult)
        state = .ok after)
    (member : pending ∈ (after.currentEpochAttestations before).data ∨
      pending ∈ (after.previousEpochAttestations before).data) :
    (pending ∈ (state.currentEpochAttestations before).data ∨
      pending ∈ (state.previousEpochAttestations before).data) ∨
    ∃ earlier block later atBlock atSlot,
      blocks = earlier ++ block :: later ∧
      earlier.foldlM
        (fun state block => stateTransition config checks engine state block validateResult)
          state = .ok atBlock ∧
      processSlots config atBlock block.message.slot = .ok atSlot ∧
      PendingIncludedInBlock config checks before atSlot block.message pending := by
  induction blocks generalizing state with
  | nil =>
    cases computed
    exact .inl member
  | cons first rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    rcases ih restOk with old | ⟨earlier, block, later, atBlock, atSlot,
        split, earlierOk, slots, included⟩
    · rcases stateTransition_pending_origin before firstOk old with old | ⟨atSlot, slots, included⟩
      · exact .inl old
      · exact .inr ⟨[], first, rest, state, atSlot, rfl, rfl, slots, included⟩
    · refine .inr ⟨first :: earlier, block, later, atBlock, atSlot,
        by simp [split], ?_, slots, included⟩
      simp only [List.foldlM_cons, bind_ok_iff]
      exact ⟨middle, firstOk, earlierOk⟩

/-- A slot that changes finalization contains an actual epoch and justification computation.

Caching precedes that computation and preserves the old finalized checkpoint. -/
theorem advanceSlot_finalized_origin (before : fork < .altair)
    (computed : advanceSlot config state = .ok after)
    (changed : after.finalizedCheckpoint ≠ state.finalizedCheckpoint) :
    ∃ cached epoched justified,
      processSlot state = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      after.finalizedCheckpoint = justified.finalizedCheckpoint ∧
      justified.finalizedCheckpoint ≠ cached.finalizedCheckpoint := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedFrame := frame_processSlot cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨justified, justifiedOk, _, _, _, finalized⟩ :=
      processEpoch_justification before epochedOk
    refine ⟨cached, epoched, justified, cachedOk, epochedOk, justifiedOk, finalized, ?_⟩
    intro same
    apply changed
    exact finalized.trans (same.trans cachedFrame.finalized)
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact (changed cachedFrame.finalized).elim

/-- Advancing one slot cannot set a bit before justification is enabled.

The early epoch calls return their input, and all other slot operations preserve the bits. -/
theorem advanceSlot_early_bits (before : fork < .altair)
    (holds : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ index : Fin 4, state.justificationBits.bits[index] = false)
    (computed : advanceSlot config state = .ok after)
    (early : getCurrentEpoch after ≤ GENESIS_EPOCH + 1) :
    ∀ index : Fin 4, after.justificationBits.bits[index] = false := by
  have slot := advanceSlot_slot computed
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have frame := frame_processSlot cachedOk
  have earlier : getCurrentEpoch state ≤ getCurrentEpoch { epoched with slot := next } := by
    rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat]
    exact Nat.div_le_div_right (by simpa using Nat.le_of_lt (by omega : state.slot.toNat <
      ({ epoched with slot := next } : BeaconState preset fork).slot.toNat))
  have earlyState := UInt64.le_trans earlier early
  have earlyCached : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1 := by
    simpa only [getCurrentEpoch, frame.slot] using earlyState
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨justified, justifiedOk, bits, _⟩ :=
      processEpoch_justification before epochedOk
    rw [processJustificationAndFinalization_early before earlyCached] at justifiedOk
    cases justifiedOk
    intro index
    change epoched.justificationBits.bits[index] = false
    rw [bits, frame.justificationBits]
    exact holds earlyState index
  · cases epochedOk
    intro index
    change cached.justificationBits.bits[index] = false
    rw [frame.justificationBits]
    exact holds earlyState index

/-- Advancing any number of slots preserves the absence of early justification bits. -/
theorem advanceSlots_early_bits (before : fork < .altair) {count : Nat}
    (holds : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ index : Fin 4, state.justificationBits.bits[index] = false)
    (computed : advanceSlots config count state = .ok after) :
    getCurrentEpoch after ≤ GENESIS_EPOCH + 1 →
      ∀ index : Fin 4, after.justificationBits.bits[index] = false := by
  induction count generalizing state with
  | zero => cases computed; exact holds
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    exact ih (advanceSlot_early_bits before holds firstOk) restOk

/-- A true bit after one slot is inherited or comes from a threshold at that slot.

Inherited bits keep their index outside epoch processing and shift by one inside it.

The witness retains the actual root caching and epoch processing calls. -/
theorem advanceSlot_bit_origin (before : fork < .altair) {index : Fin 4}
    (computed : advanceSlot config state = .ok after)
    (bit : after.justificationBits.bits[index] = true) :
    (∃ earlier : Fin 4,
      (index.val = earlier.val ∨ index.val = earlier.val + 1) ∧
        state.justificationBits.bits[earlier] = true) ∨
    ∃ cached epoched justified total previous current,
      processSlot state = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      weighJustificationAndFinalization cached total previous current = .ok justified ∧
      ((index.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
        (index.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
          cached.justificationBits.bits[0] = false)) := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have frame := frame_processSlot cachedOk
  unfold epochIfLast at epochedOk
  split at epochedOk
  · obtain ⟨justified, justifiedOk, bits, _⟩ :=
      processEpoch_justification before epochedOk
    change epoched.justificationBits.bits[index] = true at bit
    rw [bits] at bit
    rcases processJustificationAndFinalization_ok justifiedOk with same |
        ⟨total, previous, current, weighed⟩
    · subst justified
      exact .inl ⟨index, .inl rfl, frame.justificationBits ▸ bit⟩
    · rcases weighJustificationAndFinalization_bit_origin weighed bit with now | prior | inherited
      · exact .inr ⟨cached, epoched, justified, total, previous, current,
          cachedOk, epochedOk, justifiedOk, weighed, .inl now⟩
      · exact .inr ⟨cached, epoched, justified, total, previous, current,
          cachedOk, epochedOk, justifiedOk, weighed, .inr prior⟩
      · obtain ⟨earlier, shifted, earlierBit⟩ := inherited
        exact .inl ⟨earlier, .inr shifted, frame.justificationBits ▸ earlierBit⟩
  · cases epochedOk
    exact .inl ⟨index, .inl rfl, frame.justificationBits ▸ bit⟩

/-- One slot preserves the epoch named by an inherited justification bit.

A new bit names the current or previous epoch of the actual weighing call.

Bits in the first two epochs must be clear because those calls do not shift them. -/
theorem advanceSlot_bit_epoch_origin (before : fork < .altair) {index : Fin 4}
    (earlyBits : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ index : Fin 4, state.justificationBits.bits[index] = false)
    (computed : advanceSlot config state = .ok after)
    (bit : after.justificationBits.bits[index] = true) :
    (∃ earlier : Fin 4,
      (getCurrentEpoch after).toNat + earlier.val = (getCurrentEpoch state).toNat + index.val ∧
        state.justificationBits.bits[earlier] = true) ∨
    ∃ cached epoched justified total previous current,
      processSlot state = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      weighJustificationAndFinalization cached total previous current = .ok justified ∧
      (getCurrentEpoch after).toNat = (getCurrentEpoch cached).toNat + 1 ∧
      ((index.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
        (index.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
          cached.justificationBits.bits[0] = false)) := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have frame := frame_processSlot cachedOk
  simp only [UInt64.toNat_one] at sum
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have boundary' : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa [UInt64.toNat_mod] using congrArg UInt64.toNat boundary
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
      rw [sum]
      exact Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero (sum ▸ boundary'))
    have stepEpoch :
        (getCurrentEpoch { epoched with slot := next }).toNat =
          (getCurrentEpoch cached).toNat + 1 := by
      simpa only [getCurrentEpoch_toNat, frame.slot] using step
    obtain ⟨justified, justifiedOk, bits, _⟩ :=
      processEpoch_justification before epochedOk
    change epoched.justificationBits.bits[index] = true at bit
    rw [bits] at bit
    by_cases early : getCurrentEpoch cached ≤ GENESIS_EPOCH + 1
    · rw [processJustificationAndFinalization_early before early] at justifiedOk
      cases justifiedOk
      have cleared := earlyBits (by simpa only [getCurrentEpoch, frame.slot] using early) index
      rw [frame.justificationBits, cleared] at bit
      cases bit
    · have weighed := justifiedOk
      unfold processJustificationAndFinalization at weighed
      split at weighed
      · exact absurd ‹_› (Nat.not_le_of_lt before)
      simp only [bind_ok_iff, liftAccessor_ok] at weighed
      obtain ⟨_, _, _, _, total, _, previous, _, current, _, weighed⟩ := weighed
      rcases weighJustificationAndFinalization_bit_origin weighed bit with now | prior | inherited
      · exact .inr ⟨cached, epoched, justified, total, previous, current,
          cachedOk, epochedOk, justifiedOk, weighed, stepEpoch, .inl now⟩
      · exact .inr ⟨cached, epoched, justified, total, previous, current,
          cachedOk, epochedOk, justifiedOk, weighed, stepEpoch, .inr prior⟩
      · obtain ⟨earlier, shifted, earlierBit⟩ := inherited
        refine .inl ⟨earlier, ?_, frame.justificationBits ▸ earlierBit⟩
        rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
        change next.toNat / preset.SLOTS_PER_EPOCH.toNat + earlier.val = _
        omega
  · rename_i notBoundary
    cases epochedOk
    have notBoundary' : ¬preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 := by
      intro divides
      apply notBoundary
      apply UInt64.toNat_inj.mp
      simpa [UInt64.toNat_mod, sum] using Nat.mod_eq_zero_of_dvd divides
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      rw [sum]
      exact Nat.succ_div_of_not_dvd notBoundary'
    refine .inl ⟨index, ?_, frame.justificationBits ▸ bit⟩
    simpa only [getCurrentEpoch_toNat] using congrArg (· + index.val) step

/-- The origin of a bit in a slot run retains the exact epoch equation.

The equation uses addition so that no truncated epoch subtraction loses information. -/
theorem advanceSlots_bit_epoch_origin (before : fork < .altair) {count : Nat} {index : Fin 4}
    (earlyBits : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ index : Fin 4, state.justificationBits.bits[index] = false)
    (computed : advanceSlots config count state = .ok after)
    (bit : after.justificationBits.bits[index] = true) :
    (∃ earlier : Fin 4,
      (getCurrentEpoch after).toNat + earlier.val = (getCurrentEpoch state).toNat + index.val ∧
        state.justificationBits.bits[earlier] = true) ∨
    ∃ offset atStep next cached epoched justified total previous current, ∃ origin : Fin 4,
      offset < count ∧
      (getCurrentEpoch after).toNat + origin.val =
        (getCurrentEpoch cached).toNat + 1 + index.val ∧
      advanceSlots config offset state = .ok atStep ∧
      advanceSlot config atStep = .ok next ∧
      processSlot atStep = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      weighJustificationAndFinalization cached total previous current = .ok justified ∧
      ((origin.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
        (origin.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
          cached.justificationBits.bits[0] = false)) := by
  induction count generalizing state index with
  | zero =>
    cases computed
    exact .inl ⟨index, rfl, bit⟩
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    rcases ih (advanceSlot_early_bits before earlyBits firstOk) restOk bit with
        inherited | occurred
    · obtain ⟨earlier, epochEq, earlierBit⟩ := inherited
      rcases advanceSlot_bit_epoch_origin before earlyBits firstOk earlierBit with
          inherited | occurred
      · obtain ⟨old, oldEq, oldBit⟩ := inherited
        exact .inl ⟨old, by omega, oldBit⟩
      · obtain ⟨cached, epoched, justified, total, previous, current, cachedOk, epochOk,
          justifiedOk, weighed, nextEpoch, threshold⟩ := occurred
        exact .inr ⟨0, state, middle, cached, epoched, justified, total, previous, current,
          earlier, by omega, by omega, rfl, firstOk, cachedOk, epochOk,
          justifiedOk, weighed, threshold⟩
    · obtain ⟨offset, atStep, next, cached, epoched, justified, total, previous, current,
        origin, inside, epochEq, prefixOk, stepOk, cachedOk, epochOk, justifiedOk,
        weighed, threshold⟩ := occurred
      refine .inr ⟨offset + 1, atStep, next, cached, epoched, justified, total, previous,
        current, origin, by omega, epochEq, ?_, stepOk, cachedOk, epochOk,
        justifiedOk, weighed, threshold⟩
      simp only [advanceSlots, bind_ok_iff]
      exact ⟨middle, firstOk, prefixOk⟩

/-- Every true bit in a slot run was already true or came from a concrete weighing call.

The offset locates the call in the successful run, including runs with empty slots.

The index at that call cannot exceed the terminal index, because later calls only shift bits. -/
theorem advanceSlots_bit_origin (before : fork < .altair) {count : Nat} {index : Fin 4}
    (computed : advanceSlots config count state = .ok after)
    (bit : after.justificationBits.bits[index] = true) :
    (∃ earlier : Fin 4, earlier.val ≤ index.val ∧
      state.justificationBits.bits[earlier] = true) ∨
    ∃ offset atStep next cached epoched justified total previous current, ∃ origin : Fin 4,
      offset < count ∧ origin.val ≤ index.val ∧
      advanceSlots config offset state = .ok atStep ∧
      advanceSlot config atStep = .ok next ∧
      processSlot atStep = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      weighJustificationAndFinalization cached total previous current = .ok justified ∧
      ((origin.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
        (origin.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
          cached.justificationBits.bits[0] = false)) := by
  induction count generalizing state index with
  | zero =>
    cases computed
    exact .inl ⟨index, Nat.le_refl _, bit⟩
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    rcases ih restOk bit with inherited | occurred
    · obtain ⟨earlier, earlierLe, earlierBit⟩ := inherited
      rcases advanceSlot_bit_origin before firstOk earlierBit with inherited | occurred
      · obtain ⟨old, relation, oldBit⟩ := inherited
        exact .inl ⟨old, by omega, oldBit⟩
      · obtain ⟨cached, epoched, justified, total, previous, current, cachedOk, epochOk,
          justifiedOk, weighed, threshold⟩ := occurred
        exact .inr ⟨0, state, middle, cached, epoched, justified, total, previous, current,
          earlier, by omega, earlierLe, rfl, firstOk, cachedOk, epochOk,
          justifiedOk, weighed, threshold⟩
    · obtain ⟨offset, atStep, next, cached, epoched, justified, total, previous, current,
        origin, inside, originLe, prefixOk, stepOk, cachedOk, epochOk, justifiedOk,
        weighed, threshold⟩ := occurred
      refine .inr ⟨offset + 1, atStep, next, cached, epoched, justified, total, previous,
        current, origin, by omega, originLe, ?_, stepOk, cachedOk, epochOk,
        justifiedOk, weighed, threshold⟩
      simp only [advanceSlots, bind_ok_iff]
      exact ⟨middle, firstOk, prefixOk⟩

/-- A changed final checkpoint in a slot run was assigned at a particular slot step.

The successful prefix identifies that step on the actual execution.

The selected step assigns the terminal checkpoint, not merely some intermediate checkpoint. -/
theorem advanceSlots_finalized_origin {count : Nat}
    (computed : advanceSlots config count state = .ok after)
    (changed : after.finalizedCheckpoint ≠ state.finalizedCheckpoint) :
    ∃ offset atStep next, offset < count ∧
      advanceSlots config offset state = .ok atStep ∧
      advanceSlot config atStep = .ok next ∧
      next.finalizedCheckpoint = after.finalizedCheckpoint ∧
      next.finalizedCheckpoint ≠ atStep.finalizedCheckpoint := by
  induction count generalizing state with
  | zero =>
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    exact (changed (congrArg BeaconState.finalizedCheckpoint computed.symm)).elim
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    by_cases same : after.finalizedCheckpoint = middle.finalizedCheckpoint
    · exact ⟨0, state, middle, by omega, rfl, firstOk, same.symm, fun equal =>
        changed (same.trans equal)⟩
    · obtain ⟨offset, atStep, next, inside, prefixOk, stepOk, finalEq, changedStep⟩ :=
        ih restOk same
      refine ⟨offset + 1, atStep, next, by omega, ?_, stepOk, finalEq, changedStep⟩
      simp only [advanceSlots, bind_ok_iff]
      exact ⟨middle, firstOk, prefixOk⟩

/-- A slot that stays in the same epoch cannot change the finalized checkpoint.

The epoch transition runs only at a boundary, where the epoch quotient increases by one. -/
theorem advanceSlot_finalized_of_same_epoch
    (computed : advanceSlot config state = .ok after)
    (sameEpoch : getCurrentEpoch after = getCurrentEpoch state) :
    after.finalizedCheckpoint = state.finalizedCheckpoint := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedFrame := frame_processSlot cachedOk
  simp only [UInt64.toNat_one] at sum
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    have boundary' : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa [UInt64.toNat_mod] using congrArg UInt64.toNat boundary
    have step := Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero (sum ▸ boundary'))
    have epochs := congrArg UInt64.toNat sameEpoch
    simp only [getCurrentEpoch_toNat] at epochs
    rw [sum] at epochs
    omega
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    exact cachedFrame.finalized

/-- Advancing within one epoch leaves the finalized checkpoint unchanged.

This applies without a checkpoint invariant or a signature assumption. -/
theorem advanceSlots_finalized_of_same_epoch :
    ∀ {count : Nat} {state after : BeaconState preset fork},
      advanceSlots config count state = .ok after →
      getCurrentEpoch after = getCurrentEpoch state →
      after.finalizedCheckpoint = state.finalizedCheckpoint
  | 0, _, _, computed, _ => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  | count + 1, state, after, computed, sameEpoch => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    have firstSlot := advanceSlot_slot first
    have restSlots := advanceSlots_slot count rest
    have lower : state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
        middle.slot.toNat / preset.SLOTS_PER_EPOCH.toNat :=
      Nat.div_le_div_right (by omega)
    have upper : middle.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
        after.slot.toNat / preset.SLOTS_PER_EPOCH.toNat :=
      Nat.div_le_div_right (by omega)
    have epochNats := congrArg UInt64.toNat sameEpoch
    simp only [getCurrentEpoch_toNat] at epochNats
    have middleEpoch : getCurrentEpoch middle = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      simp only [getCurrentEpoch_toNat]
      omega
    exact (advanceSlots_finalized_of_same_epoch rest (sameEpoch.trans middleEpoch.symm)).trans
      (advanceSlot_finalized_of_same_epoch first middleEpoch)

/-- Before Altair, one slot keeps the invariant, and the finalized epoch does not decrease.

When the slot ends an epoch, the current justified epoch is at most that epoch.

The next slot starts the next epoch, whose previous epoch is that one. -/
theorem advanceSlot_invariant (altair : fork < .altair) (holds : Invariant state)
    (computed : advanceSlot config state = .ok after) :
    Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedFrame := frame_processSlot cachedOk
  have cachedHolds := cachedFrame.invariant holds
  simp only [UInt64.toNat_one] at sum
  have stateEpoch := getCurrentEpoch_toNat state
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    obtain ⟨_, balancesMatch, exitsOrdered, ordered, finalized, current, bounded⟩ :=
      processEpoch_invariant altair cachedHolds epochedOk
    have boundary' : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa [UInt64.toNat_mod] using congrArg UInt64.toNat boundary
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
      rw [sum]
      exact Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero (sum ▸ boundary'))
    refine ⟨⟨balancesMatch, exitsOrdered, ordered, ?_, bounded⟩, ?_⟩
    · have current' := UInt64.le_iff_toNat_le.mp current
      rw [getCurrentEpoch_toNat, cachedFrame.slot] at current'
      unfold JustifiedSettled
      rw [UInt64.le_iff_toNat_le, getPreviousEpoch_toNat, getCurrentEpoch_toNat]
      dsimp only
      omega
    · rw [← cachedFrame.finalized]
      exact finalized
  · rename_i notBoundary
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have notBoundary' : ¬preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 := by
      intro divides
      apply notBoundary
      apply UInt64.toNat_inj.mp
      simpa [UInt64.toNat_mod, sum] using Nat.mod_eq_zero_of_dvd divides
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      rw [sum]
      exact Nat.succ_div_of_not_dvd notBoundary'
    refine ⟨⟨cachedHolds.balancesMatch, cachedHolds.exitsOrdered, cachedHolds.ordered, ?_,
      cachedHolds.effectiveBalancesBounded⟩, ?_⟩
    · have settled := UInt64.le_iff_toNat_le.mp holds.settled
      rw [getPreviousEpoch_toNat, getCurrentEpoch_toNat] at settled
      unfold JustifiedSettled
      rw [UInt64.le_iff_toNat_le, getPreviousEpoch_toNat, getCurrentEpoch_toNat]
      dsimp only
      rw [cachedFrame.currentJustified, step]
      exact settled
    · rw [cachedFrame.finalized]
      exact UInt64.le_refl _

theorem advanceSlots_invariant (altair : fork < .altair) :
    ∀ {count : Nat} {state after : BeaconState preset fork}, Invariant state →
      advanceSlots config count state = .ok after →
      Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch
  | 0, state, after, holds, computed => by
    simp only [advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨holds, UInt64.le_refl _⟩
  | count + 1, state, after, holds, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    obtain ⟨nextHolds, first⟩ := advanceSlot_invariant altair holds nextOk
    obtain ⟨afterHolds, second⟩ := advanceSlots_invariant altair nextHolds rest
    exact ⟨afterHolds, UInt64.le_trans first second⟩

/-- Advancing one Phase 0 slot preserves active indices for every already reached epoch. -/
theorem advanceSlot_active_indices (before : fork < .altair) (holds : Invariant state)
    {epoch : Epoch} (past : epoch ≤ getCurrentEpoch state)
    (computed : advanceSlot config state = .ok after) :
    getActiveValidatorIndices after epoch = getActiveValidatorIndices state epoch := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have frame := frame_processSlot cachedOk
  have recent : epoch ≤ getCurrentEpoch cached := by
    simpa only [getCurrentEpoch, frame.slot] using past
  have registry : cached.validators = state.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have kept : getActiveValidatorIndices epoched epoch =
      getActiveValidatorIndices cached epoch := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch_active_indices before (frame.invariant holds) recent epochedOk
    · cases epochedOk
      rfl
  change getActiveValidatorIndices epoched epoch = _
  rw [kept]
  simp only [getActiveValidatorIndices, registry]

/-- A Phase 0 slot run preserves committee populations for epochs reached before the run. -/
theorem advanceSlots_active_indices (before : fork < .altair) {epoch : Epoch} :
    ∀ (count : Nat) {state after : BeaconState preset fork}, Invariant state →
      epoch ≤ getCurrentEpoch state → advanceSlots config count state = .ok after →
      getActiveValidatorIndices after epoch = getActiveValidatorIndices state epoch
  | 0, _, _, _, _, computed => by
    cases computed
    rfl
  | count + 1, state, _, holds, past, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    have slot := advanceSlot_slot first
    have later : getCurrentEpoch state ≤ getCurrentEpoch middle := by
      rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat, slot]
      exact Nat.div_le_div_right (by omega)
    exact (advanceSlots_active_indices before count
      (advanceSlot_invariant before holds first).1 (UInt64.le_trans past later) tail).trans
      (advanceSlot_active_indices before holds past first)

/-- A Phase 0 slot step preserves the seeds of its input's recent epochs. -/
theorem advanceSlot_attester_seed
    {state after : BeaconState preset .phase0}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (holds : Invariant state)
    {epoch : Epoch}
    (recent : epoch = getCurrentEpoch state ∨ epoch.toNat + 1 = (getCurrentEpoch state).toNat)
    (computed : advanceSlot config state = .ok after) :
    getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have frame := frame_processSlot cachedOk
  have sameMixes : cached.randaoMixes = state.randaoMixes := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  have recent' : epoch = getCurrentEpoch cached ∨
      epoch.toNat + 1 = (getCurrentEpoch cached).toNat := by
    simpa only [getCurrentEpoch, frame.slot] using recent
  have kept : getSeed epoched epoch DOMAIN_BEACON_ATTESTER =
      getSeed cached epoch DOMAIN_BEACON_ATTESTER := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact processEpoch_attester_seed positive history (frame.invariant holds) recent' epochedOk
    · cases epochedOk
      rfl
  have cachedSeed : getSeed cached epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
    apply getSeed_congr
    intro shifted _
    simp only [getRandaoMix, sameMixes]
  change getSeed epoched epoch DOMAIN_BEACON_ATTESTER = _
  exact kept.trans cachedSeed

/-- A Phase 0 slot run preserves a reached epoch's seed while it remains recent. -/
theorem advanceSlots_attester_seed {epoch : Epoch}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    ∀ (count : Nat) {state after : BeaconState preset .phase0}, Invariant state →
      epoch ≤ getCurrentEpoch state → (getCurrentEpoch after).toNat ≤ epoch.toNat + 1 →
      advanceSlots config count state = .ok after →
      getSeed after epoch DOMAIN_BEACON_ATTESTER =
        getSeed state epoch DOMAIN_BEACON_ATTESTER
  | 0, _, _, _, _, _, computed => by
    cases computed
    rfl
  | count + 1, state, after, holds, past, recentAfter, computed => by
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    have firstSlot := advanceSlot_slot first
    have tailSlot := advanceSlots_slot count tail
    have lower : getCurrentEpoch state ≤ getCurrentEpoch middle := by
      rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat, firstSlot]
      exact Nat.div_le_div_right (by omega)
    have upper : (getCurrentEpoch middle).toNat ≤ (getCurrentEpoch after).toNat := by
      rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, tailSlot]
      exact Nat.div_le_div_right (by omega)
    have recent : epoch = getCurrentEpoch state ∨
        epoch.toNat + 1 = (getCurrentEpoch state).toNat := by
      have lo := UInt64.le_iff_toNat_le.mp past
      have hi := UInt64.le_iff_toNat_le.mp lower
      by_cases same : epoch.toNat = (getCurrentEpoch state).toNat
      · exact .inl (UInt64.toNat_inj.mp same)
      · exact .inr (by omega)
    exact (advanceSlots_attester_seed positive history count
      (advanceSlot_invariant (by decide) holds first).1
      (UInt64.le_trans past lower) recentAfter tail).trans
      (advanceSlot_attester_seed positive history holds recent first)

/-- Before Altair, advancing to a later slot keeps the invariant.

The finalized epoch does not decrease. -/
theorem processSlots_invariant (altair : fork < .altair) {slot : Slot} (holds : Invariant state)
    (computed : processSlots config state slot = .ok after) :
    Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, advanced⟩ := computed
  exact advanceSlots_invariant altair holds advanced

/-- Before Altair, each valid block keeps the invariant, and the finalized epoch never decreases.

The registry and the balances keep one entry for each validator.

Each validator may withdraw no earlier than it exits.

The checkpoints stay in order, and the current justified epoch stays at most the previous epoch.

This holds for every signature check and with or without validating the result. -/
theorem stateTransition_invariant (altair : fork < .altair)
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool} (holds : Invariant state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    Invariant after ∧ state.finalizedCheckpoint.epoch ≤ after.finalizedCheckpoint.epoch := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  obtain ⟨advancedHolds, finalized⟩ := processSlots_invariant altair holds slotsOk
  have frame := frame_processBlock altair blockOk
  refine ⟨frame.invariant advancedHolds, ?_⟩
  rw [frame.finalized]
  exact finalized

/-- A successful Phase 0 transition preserves committees for epochs already reached at its input. -/
theorem stateTransition_active_indices (before : fork < .altair) (holds : Invariant state)
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool} {epoch : Epoch}
    (past : epoch ≤ getCurrentEpoch state)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    getActiveValidatorIndices after epoch = getActiveValidatorIndices state epoch := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  have advancedPast : epoch ≤ getCurrentEpoch advanced := by
    have slots := processSlots_slot slotsOk
    have later : getCurrentEpoch state ≤ getCurrentEpoch advanced := by
      rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat, slots.2]
      have less := UInt64.lt_iff_toNat_lt.mp slots.1
      exact Nat.div_le_div_right (by omega)
    exact UInt64.le_trans past later
  have blockKept := processBlock_active_indices before advancedPast blockOk
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  exact blockKept.trans (advanceSlots_active_indices before _ holds past advancedOk)

/-- A Phase 0 block transition preserves a reached epoch's seed while it remains recent. -/
theorem stateTransition_attester_seed
    {state after : BeaconState preset .phase0}
    {engine : ExecutionEngine preset .phase0}
    {signed : SignedBeaconBlock preset .phase0} {epoch : Epoch}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (holds : Invariant state) (past : epoch ≤ getCurrentEpoch state)
    (recentAfter : (getCurrentEpoch after).toNat ≤ epoch.toNat + 1)
    (computed : stateTransition config checks engine state signed true = .ok after) :
    getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  have frame := frame_processBlock (by decide) blockOk
  have sameEpoch : getCurrentEpoch after = getCurrentEpoch advanced := by
    simp only [getCurrentEpoch, frame.slot]
  have lower : getCurrentEpoch state ≤ getCurrentEpoch advanced := by
    have slots := processSlots_slot slotsOk
    rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat, slots.2]
    have less := UInt64.lt_iff_toNat_lt.mp slots.1
    exact Nat.div_le_div_right (by omega)
  have recent : epoch = getCurrentEpoch advanced ∨
      epoch.toNat + 1 = (getCurrentEpoch advanced).toNat := by
    have lo := UInt64.le_iff_toNat_le.mp (UInt64.le_trans past lower)
    rw [sameEpoch] at recentAfter
    by_cases same : epoch.toNat = (getCurrentEpoch advanced).toNat
    · exact .inl (UInt64.toNat_inj.mp same)
    · exact .inr (by omega)
  have seed := processBlock_attester_seed positive history recent blockOk
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  exact seed.trans (advanceSlots_attester_seed positive history _ holds past
    (by simpa only [sameEpoch] using recentAfter) advancedOk)

/-- A Phase 0 chain preserves a reached epoch's seed while it remains recent. -/
theorem stateTransition_chain_attester_seed
    {state after : BeaconState preset .phase0}
    {engine : ExecutionEngine preset .phase0}
    {blocks : List (SignedBeaconBlock preset .phase0)} {epoch : Epoch}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (holds : Invariant state) (past : epoch ≤ getCurrentEpoch state)
    (recentAfter : (getCurrentEpoch after).toNat ≤ epoch.toNat + 1)
    (computed : blocks.foldlM
      (fun s block => stateTransition config checks engine s block true) state = .ok after) :
    getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
  induction blocks generalizing state with
  | nil =>
    cases computed
    rfl
  | cons block rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    have transitionEpoch {s t : BeaconState preset .phase0}
        {block : SignedBeaconBlock preset .phase0}
        (ok : stateTransition config checks engine s block true = .ok t) :
        getCurrentEpoch s ≤ getCurrentEpoch t := by
      obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok ok
      have slots := processSlots_slot slotsOk
      have frame := frame_processBlock (by decide) blockOk
      rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat,
        frame.slot, slots.2]
      have less := UInt64.lt_iff_toNat_lt.mp slots.1
      exact Nat.div_le_div_right (by omega)
    have lower := transitionEpoch first
    have upper := foldlM_ok_invariant
      (fun s => getCurrentEpoch middle ≤ getCurrentEpoch s)
      (fun _ _ _ prior ok => UInt64.le_trans prior (transitionEpoch ok))
      (UInt64.le_refl _) tail
    have recentMiddle : (getCurrentEpoch middle).toNat ≤ epoch.toNat + 1 := by
      have hi := UInt64.le_iff_toNat_le.mp upper
      omega
    exact (ih (stateTransition_invariant (by decide) holds first).1
      (UInt64.le_trans past lower) tail).trans
      (stateTransition_attester_seed positive history holds past recentMiddle first)

/-- Actual Phase 0 chains preserve active indices at every epoch reached before the chain. -/
theorem stateTransition_chain_active_indices (before : fork < .altair)
    (holds : Invariant state) {epoch : Epoch} (past : epoch ≤ getCurrentEpoch state)
    {blocks : List (SignedBeaconBlock preset fork)}
    (computed : blocks.foldlM
      (fun s block => stateTransition config checks engine s block true) state = .ok after) :
    getActiveValidatorIndices after epoch = getActiveValidatorIndices state epoch := by
  have result := foldlM_ok_invariant (fun s => Invariant s ∧
    epoch ≤ getCurrentEpoch s ∧
    getActiveValidatorIndices s epoch = getActiveValidatorIndices state epoch)
    (fun s block next prior ok => by
      have invariant := (stateTransition_invariant before prior.1 ok).1
      obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok ok
      have slots := processSlots_slot slotsOk
      have frame := frame_processBlock before blockOk
      have epochLe : getCurrentEpoch s ≤ getCurrentEpoch next := by
        rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat,
          frame.slot, slots.2]
        have less := UInt64.lt_iff_toNat_lt.mp slots.1
        exact Nat.div_le_div_right (by omega)
      exact ⟨invariant, UInt64.le_trans prior.2.1 epochLe,
        (stateTransition_active_indices before prior.1 prior.2.1 ok).trans prior.2.2⟩)
    ⟨holds, past, rfl⟩ computed
  exact result.2.2

/-- Phase 0 chains preserve a reached epoch's committees while that epoch stays recent.

This compares the actual committee function at the two execution states. -/
theorem stateTransition_chain_committee
    {state after : BeaconState preset .phase0}
    {engine : ExecutionEngine preset .phase0}
    {blocks : List (SignedBeaconBlock preset .phase0)}
    {slot : Slot} {index : CommitteeIndex}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (holds : Invariant state)
    (past : computeEpochAtSlot preset slot ≤ getCurrentEpoch state)
    (recentAfter : (getCurrentEpoch after).toNat ≤
      (computeEpochAtSlot preset slot).toNat + 1)
    (computed : blocks.foldlM
      (fun s block => stateTransition config checks engine s block true) state = .ok after) :
    getBeaconCommittee after slot index = getBeaconCommittee state slot index := by
  apply getBeaconCommittee_congr
  · exact stateTransition_chain_active_indices (by decide) holds past computed
  · exact stateTransition_chain_attester_seed positive history holds past recentAfter computed

/-- A true bit after a block is inherited or comes from a threshold in its slot run.

Block processing itself cannot introduce justification bits. -/
theorem stateTransition_bit_origin (before : fork < .altair) {index : Fin 4}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after)
    (bit : after.justificationBits.bits[index] = true) :
    (∃ earlier : Fin 4, earlier.val ≤ index.val ∧
      state.justificationBits.bits[earlier] = true) ∨
    ∃ offset atStep next cached epoched justified total previous current, ∃ origin : Fin 4,
      offset < signed.message.slot.toNat - state.slot.toNat ∧ origin.val ≤ index.val ∧
      advanceSlots config offset state = .ok atStep ∧
      advanceSlot config atStep = .ok next ∧
      processSlot atStep = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      weighJustificationAndFinalization cached total previous current = .ok justified ∧
      ((origin.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
        (origin.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
          cached.justificationBits.bits[0] = false)) := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  have frame := frame_processBlock before blockOk
  rw [frame.justificationBits] at bit
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  exact advanceSlots_bit_origin before advancedOk bit

/-- A successful block preserves the absence of early justification bits. -/
theorem stateTransition_early_bits (before : fork < .altair)
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (holds : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ index : Fin 4, state.justificationBits.bits[index] = false)
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    getCurrentEpoch after ≤ GENESIS_EPOCH + 1 →
      ∀ index : Fin 4, after.justificationBits.bits[index] = false := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  have frame := frame_processBlock before blockOk
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  intro early index
  rw [frame.justificationBits]
  apply advanceSlots_early_bits before holds advancedOk _ index
  simpa only [getCurrentEpoch, frame.slot] using early

/-- A bit's epoch equation is unchanged by the block after its slot run. -/
theorem stateTransition_bit_epoch_origin (before : fork < .altair) {index : Fin 4}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (earlyBits : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ index : Fin 4, state.justificationBits.bits[index] = false)
    (computed : stateTransition config checks engine state signed validateResult = .ok after)
    (bit : after.justificationBits.bits[index] = true) :
    (∃ earlier : Fin 4,
      (getCurrentEpoch after).toNat + earlier.val = (getCurrentEpoch state).toNat + index.val ∧
        state.justificationBits.bits[earlier] = true) ∨
    ∃ offset atStep next cached epoched justified total previous current, ∃ origin : Fin 4,
      offset < signed.message.slot.toNat - state.slot.toNat ∧
      (getCurrentEpoch after).toNat + origin.val =
        (getCurrentEpoch cached).toNat + 1 + index.val ∧
      advanceSlots config offset state = .ok atStep ∧
      advanceSlot config atStep = .ok next ∧
      processSlot atStep = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      weighJustificationAndFinalization cached total previous current = .ok justified ∧
      ((origin.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
        (origin.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
          cached.justificationBits.bits[0] = false)) := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  have frame := frame_processBlock before blockOk
  rw [frame.justificationBits] at bit
  simp only [getCurrentEpoch, frame.slot]
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  exact advanceSlots_bit_epoch_origin before earlyBits advancedOk bit

/-- A true bit on a chain retains the exact epoch of its original threshold computation. -/
theorem stateTransition_chain_bit_epoch_origin (before : fork < .altair) {index : Fin 4}
    {blocks : List (SignedBeaconBlock preset fork)} {validateResult : Bool}
    (earlyBits : getCurrentEpoch state ≤ GENESIS_EPOCH + 1 →
      ∀ index : Fin 4, state.justificationBits.bits[index] = false)
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block validateResult)
        state = .ok after)
    (bit : after.justificationBits.bits[index] = true) :
    (∃ earlier : Fin 4,
      (getCurrentEpoch after).toNat + earlier.val = (getCurrentEpoch state).toNat + index.val ∧
        state.justificationBits.bits[earlier] = true) ∨
    ∃ earlier block later atBlock offset atStep next cached epoched justified total previous,
      ∃ current, ∃ origin : Fin 4,
      blocks = earlier ++ block :: later ∧
      earlier.foldlM
        (fun state block => stateTransition config checks engine state block validateResult)
          state = .ok atBlock ∧
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
  induction blocks generalizing state index with
  | nil =>
    cases computed
    exact .inl ⟨index, rfl, bit⟩
  | cons first rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    rcases ih (stateTransition_early_bits before earlyBits firstOk) restOk bit with
        inherited | occurred
    · obtain ⟨earlier, epochEq, earlierBit⟩ := inherited
      rcases stateTransition_bit_epoch_origin before earlyBits firstOk earlierBit with
          inherited | occurred
      · obtain ⟨old, oldEq, oldBit⟩ := inherited
        exact .inl ⟨old, by omega, oldBit⟩
      · obtain ⟨offset, atStep, next, cached, epoched, justified, total, previous, current,
          origin, inside, originEq, prefixOk, stepOk, cachedOk, epochOk, justifiedOk,
          weighed, threshold⟩ := occurred
        exact .inr ⟨[], first, rest, state, offset, atStep, next, cached, epoched,
          justified, total, previous, current, origin, rfl, rfl, inside,
          by omega, prefixOk, stepOk, cachedOk, epochOk, justifiedOk, weighed, threshold⟩
    · obtain ⟨earlier, block, later, atBlock, offset, atStep, next, cached, epoched,
        justified, total, previous, current, origin, split, blocksOk, inside, originEq,
        prefixOk, stepOk, cachedOk, epochOk, justifiedOk, weighed, threshold⟩ := occurred
      refine .inr ⟨first :: earlier, block, later, atBlock, offset, atStep, next,
        cached, epoched, justified, total, previous, current, origin, by simp [split],
        ?_, inside, originEq, prefixOk, stepOk, cachedOk, epochOk, justifiedOk,
        weighed, threshold⟩
      simp only [List.foldlM_cons, bind_ok_iff]
      exact ⟨middle, firstOk, blocksOk⟩

/-- A true bit on a chain is inherited or comes from one of its actual weighing calls.

The two successful prefixes locate the block and then the slot at which it originated. -/
theorem stateTransition_chain_bit_origin (before : fork < .altair) {index : Fin 4}
    {blocks : List (SignedBeaconBlock preset fork)} {validateResult : Bool}
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block validateResult)
        state = .ok after)
    (bit : after.justificationBits.bits[index] = true) :
    (∃ earlier : Fin 4, earlier.val ≤ index.val ∧
      state.justificationBits.bits[earlier] = true) ∨
    ∃ earlier block later atBlock offset atStep next cached epoched justified total previous,
      ∃ current, ∃ origin : Fin 4,
      blocks = earlier ++ block :: later ∧
      earlier.foldlM
        (fun state block => stateTransition config checks engine state block validateResult)
          state = .ok atBlock ∧
      offset < block.message.slot.toNat - atBlock.slot.toNat ∧ origin.val ≤ index.val ∧
      advanceSlots config offset atBlock = .ok atStep ∧
      advanceSlot config atStep = .ok next ∧
      processSlot atStep = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      weighJustificationAndFinalization cached total previous current = .ok justified ∧
      ((origin.val = 0 ∧ 2 * total.toNat ≤ 3 * current.toNat) ∨
        (origin.val = 1 ∧ 2 * total.toNat ≤ 3 * previous.toNat ∧
          cached.justificationBits.bits[0] = false)) := by
  induction blocks generalizing state index with
  | nil =>
    cases computed
    exact .inl ⟨index, Nat.le_refl _, bit⟩
  | cons first rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    rcases ih restOk bit with inherited | occurred
    · obtain ⟨earlier, earlierLe, earlierBit⟩ := inherited
      rcases stateTransition_bit_origin before firstOk earlierBit with inherited | occurred
      · obtain ⟨old, oldLe, oldBit⟩ := inherited
        exact .inl ⟨old, Nat.le_trans oldLe earlierLe, oldBit⟩
      · obtain ⟨offset, atStep, next, cached, epoched, justified, total, previous, current,
          origin, inside, originLe, prefixOk, stepOk, cachedOk, epochOk, justifiedOk,
          weighed, threshold⟩ := occurred
        exact .inr ⟨[], first, rest, state, offset, atStep, next, cached, epoched,
          justified, total, previous, current, origin, rfl, rfl, inside,
          Nat.le_trans originLe earlierLe, prefixOk, stepOk, cachedOk, epochOk,
          justifiedOk, weighed, threshold⟩
    · obtain ⟨earlier, block, later, atBlock, offset, atStep, next, cached, epoched,
        justified, total, previous, current, origin, split, blocksOk, inside, originLe,
        prefixOk, stepOk, cachedOk, epochOk, justifiedOk, weighed, threshold⟩ := occurred
      refine .inr ⟨first :: earlier, block, later, atBlock, offset, atStep, next,
        cached, epoched, justified, total, previous, current, origin, by simp [split],
        ?_, inside, originLe, prefixOk, stepOk, cachedOk, epochOk, justifiedOk,
        weighed, threshold⟩
      simp only [List.foldlM_cons, bind_ok_iff]
      exact ⟨middle, firstOk, blocksOk⟩

/-- A changed finalized checkpoint after a block comes from a justification call in its slot run.

The offset identifies the weighing state before that slot's epoch transition. -/
theorem stateTransition_finalized_origin (before : fork < .altair)
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after)
    (changed : after.finalizedCheckpoint ≠ state.finalizedCheckpoint) :
    ∃ offset atStep next cached epoched justified,
      offset < signed.message.slot.toNat - state.slot.toNat ∧
      advanceSlots config offset state = .ok atStep ∧
      advanceSlot config atStep = .ok next ∧
      processSlot atStep = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      after.finalizedCheckpoint = justified.finalizedCheckpoint ∧
      justified.finalizedCheckpoint ≠ cached.finalizedCheckpoint := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  have frame := frame_processBlock before blockOk
  have changedSlots : advanced.finalizedCheckpoint ≠ state.finalizedCheckpoint := by
    simpa only [frame.finalized] using changed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  obtain ⟨offset, atStep, next, inside, prefixOk, stepOk, finalEq, changedStep⟩ :=
    advanceSlots_finalized_origin advancedOk changedSlots
  obtain ⟨cached, epoched, justified, cachedOk, epochOk, justifiedOk, assigned, changedEpoch⟩ :=
    advanceSlot_finalized_origin before stepOk changedStep
  exact ⟨offset, atStep, next, cached, epoched, justified, inside, prefixOk, stepOk,
    cachedOk, epochOk, justifiedOk, frame.finalized.trans (finalEq.symm.trans assigned),
    changedEpoch⟩

/-- A valid block in the same epoch cannot change Phase 0's finalized checkpoint. -/
theorem stateTransition_finalized_of_same_epoch (before : fork < .altair)
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after)
    (sameEpoch : getCurrentEpoch after = getCurrentEpoch state) :
    after.finalizedCheckpoint = state.finalizedCheckpoint := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  have frame := frame_processBlock before blockOk
  have same : getCurrentEpoch advanced = getCurrentEpoch state := by
    simpa only [getCurrentEpoch, frame.slot] using sameEpoch
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  exact frame.finalized.trans (advanceSlots_finalized_of_same_epoch advancedOk same)

/-- The epoch of a valid block transition cannot decrease. -/
theorem stateTransition_epoch_le (before : fork < .altair)
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    getCurrentEpoch state ≤ getCurrentEpoch after := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  have frame := frame_processBlock before blockOk
  have slots := (processSlots_slot slotsOk).1
  rw [UInt64.le_iff_toNat_le, getCurrentEpoch_toNat, getCurrentEpoch_toNat, frame.slot]
  have earlier := UInt64.lt_iff_toNat_lt.mp slots
  rw [(processSlots_slot slotsOk).2]
  exact Nat.div_le_div_right (by omega)

/-- The epoch cannot decrease along a chain of successful state transitions. -/
theorem stateTransition_chain_epoch_le (before : fork < .altair)
    {blocks : List (SignedBeaconBlock preset fork)}
    {validateResult : Bool}
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block validateResult)
        state = .ok after) :
    getCurrentEpoch state ≤ getCurrentEpoch after := by
  induction blocks generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact UInt64.le_refl _
  | cons first rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    exact UInt64.le_trans (stateTransition_epoch_le before firstOk) (ih restOk)

/-- A changed terminal checkpoint of a chain was assigned during one of its blocks' slot runs.

The witness gives the successful block prefix and the successful slot prefix within that block.

Its justification result has the terminal checkpoint, even if later blocks retain it. -/
theorem stateTransition_chain_finalized_origin (before : fork < .altair)
    {blocks : List (SignedBeaconBlock preset fork)} {validateResult : Bool}
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block validateResult)
        state = .ok after)
    (changed : after.finalizedCheckpoint ≠ state.finalizedCheckpoint) :
    ∃ earlier block later atBlock offset atStep next cached epoched justified,
      blocks = earlier ++ block :: later ∧
      earlier.foldlM
        (fun state block => stateTransition config checks engine state block validateResult)
          state = .ok atBlock ∧
      (∃ afterBlock, stateTransition config checks engine atBlock block validateResult =
        .ok afterBlock) ∧
      offset < block.message.slot.toNat - atBlock.slot.toNat ∧
      advanceSlots config offset atBlock = .ok atStep ∧
      advanceSlot config atStep = .ok next ∧
      processSlot atStep = .ok cached ∧ processEpoch config cached = .ok epoched ∧
      processJustificationAndFinalization cached = .ok justified ∧
      after.finalizedCheckpoint = justified.finalizedCheckpoint ∧
      justified.finalizedCheckpoint ≠ cached.finalizedCheckpoint := by
  induction blocks generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact (changed (congrArg BeaconState.finalizedCheckpoint computed.symm)).elim
  | cons first rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    by_cases same : after.finalizedCheckpoint = middle.finalizedCheckpoint
    · have changedFirst : middle.finalizedCheckpoint ≠ state.finalizedCheckpoint :=
        fun equal => changed (same.trans equal)
      obtain ⟨offset, atStep, next, cached, epoched, justified, inside, prefixOk, stepOk,
        cachedOk, epochOk, justifiedOk, assigned, changedEpoch⟩ :=
        stateTransition_finalized_origin before firstOk changedFirst
      exact ⟨[], first, rest, state, offset, atStep, next, cached, epoched, justified,
        rfl, rfl, ⟨middle, firstOk⟩, inside, prefixOk, stepOk, cachedOk, epochOk, justifiedOk,
        same.trans assigned, changedEpoch⟩
    · obtain ⟨earlier, block, later, atBlock, offset, atStep, next, cached, epoched, justified,
        split, blocksOk, blockOk, inside, prefixOk, stepOk, cachedOk, epochOk, justifiedOk,
        assigned, changedEpoch⟩ := ih restOk same
      refine ⟨first :: earlier, block, later, atBlock, offset, atStep, next, cached, epoched,
        justified, by simp [split], ?_, blockOk, inside, prefixOk, stepOk, cachedOk, epochOk,
        justifiedOk, assigned, changedEpoch⟩
      simp only [List.foldlM_cons, bind_ok_iff]
      exact ⟨middle, firstOk, blocksOk⟩

/-- A Phase 0 chain that stays in its starting epoch leaves finalization unchanged.

This establishes the zero-epoch boundary case without any drift or signature hypothesis. -/
theorem stateTransition_chain_finalized_of_same_epoch (before : fork < .altair)
    {blocks : List (SignedBeaconBlock preset fork)} {validateResult : Bool}
    (computed : blocks.foldlM
      (fun state block => stateTransition config checks engine state block validateResult)
        state = .ok after)
    (sameEpoch : getCurrentEpoch after = getCurrentEpoch state) :
    after.finalizedCheckpoint = state.finalizedCheckpoint := by
  induction blocks generalizing state with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  | cons first rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    have lower := stateTransition_epoch_le before firstOk
    have upper := stateTransition_chain_epoch_le before restOk
    have same : getCurrentEpoch middle = getCurrentEpoch state := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.le_iff_toNat_le] at lower upper
      rw [sameEpoch] at upper
      omega
    exact (ih restOk (sameEpoch.trans same.symm)).trans
      (stateTransition_finalized_of_same_epoch before firstOk same)

/-- Two Phase 0 suffixes within zero epochs have the same finalized checkpoint.

The epoch differences use natural subtraction, so monotonicity is needed before cancelling them. -/
theorem stateTransition_chains_finalized_eq_of_zero_epochs (before : fork < .altair)
    {left right : BeaconState preset fork}
    {leftBlocks rightBlocks : List (SignedBeaconBlock preset fork)}
    (leftRun : leftBlocks.foldlM
      (fun state block => stateTransition config checks engine state block true) state = .ok left)
    (rightRun : rightBlocks.foldlM
      (fun state block => stateTransition config checks engine state block true) state = .ok right)
    (leftHorizon : (getCurrentEpoch left).toNat - (getCurrentEpoch state).toNat ≤ 0)
    (rightHorizon : (getCurrentEpoch right).toNat - (getCurrentEpoch state).toNat ≤ 0) :
    left.finalizedCheckpoint = right.finalizedCheckpoint := by
  have leftLe := UInt64.le_iff_toNat_le.mp (stateTransition_chain_epoch_le before leftRun)
  have rightLe := UInt64.le_iff_toNat_le.mp (stateTransition_chain_epoch_le before rightRun)
  have leftEpoch : getCurrentEpoch left = getCurrentEpoch state :=
    UInt64.toNat_inj.mp (by omega)
  have rightEpoch : getCurrentEpoch right = getCurrentEpoch state :=
    UInt64.toNat_inj.mp (by omega)
  exact (stateTransition_chain_finalized_of_same_epoch before leftRun leftEpoch).trans
    (stateTransition_chain_finalized_of_same_epoch before rightRun rightEpoch).symm

end EthLib.Consensus
