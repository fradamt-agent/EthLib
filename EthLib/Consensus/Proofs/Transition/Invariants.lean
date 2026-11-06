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

/-- Before Altair, a block forms a frame. -/
theorem frame_processBlock (altair : fork < .altair) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) : Frame state after := by
  have notAltair : ¬Fork.altair ≤ fork := fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le altair le)
  simp only [processBlock, notAltair, ↓reduceDIte, bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (frame_processBlockHeader headerOk).trans <| (frame_processRandao randaoOk).trans <|
    (frame_processEth1Data eth1Ok).trans (frame_processOperations altair operationsOk)

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
