module

public import EthLib.Consensus.Proofs.Transition.Finality.Definitions

/-!
# Registry alignment for Phase 0 finality

Phase 0 registry updates and deposits preserve the identity of each existing registry position.

Splitting voting weight uses registry positions, not a search by public key.

The raw marked sum keeps the array zip's truncation rule.
-/

@[expose] public section

namespace EthLib.Consensus

section Finality

open Base Uint64 Cryptography.Bls Serialization.Ssz

variable {p : Preset}

/-- Identity fields and an activation epoch already assigned by the Phase 0 registry.

The `process_registry_updates` rule only assigns activation to far-future entries. -/
def FinalityValidatorStable (v w : Validator) : Prop :=
  w.pubkey = v.pubkey ∧ w.withdrawalCredentials = v.withdrawalCredentials ∧
    (v.activationEpoch ≠ FAR_FUTURE_EPOCH → w.activationEpoch = v.activationEpoch)

/-- Existing positions survive, with their identity and assigned activation epoch.

New deposits may append positions but cannot replace an existing position. -/
def FinalityRegistryExtends (s t : BeaconState p .phase0) : Prop :=
  s.validators.data.size ≤ t.validators.data.size ∧
    ∀ i v, getValidator s i = .ok v →
      ∃ w, getValidator t i = .ok w ∧ FinalityValidatorStable v w

theorem FinalityRegistryExtends.refl (s : BeaconState p .phase0) :
    FinalityRegistryExtends s s :=
  ⟨Nat.le_refl _, fun _ v h => ⟨v, h, rfl, rfl, fun _ => rfl⟩⟩

theorem FinalityRegistryExtends.trans {s t u : BeaconState p .phase0}
    (st : FinalityRegistryExtends s t) (tu : FinalityRegistryExtends t u) :
    FinalityRegistryExtends s u := by
  refine ⟨Nat.le_trans st.1 tu.1, ?_⟩
  intro i v read
  obtain ⟨w, found, key, credentials, epoch⟩ := st.2 i v read
  obtain ⟨x, found', key', credentials', epoch'⟩ := tu.2 i w found
  refine ⟨x, found', key'.trans key, credentials'.trans credentials, ?_⟩
  intro assigned
  have same := epoch assigned
  exact (epoch' (same ▸ assigned)).trans same

/-- A step that does not write the registry preserves every existing position. -/
theorem FinalityRegistryExtends.of_validators {s t : BeaconState p .phase0}
    (same : t.validators = s.validators) : FinalityRegistryExtends s t := by
  refine ⟨by simpa only [same] using Nat.le_refl s.validators.data.size, ?_⟩
  intro i v read
  exact ⟨v, (getValidator_of_validators_eq same i).trans read, rfl, rfl, fun _ => rfl⟩

/-- Replacing one position by a stable validator preserves all positions. -/
theorem FinalityRegistryExtends.setValidator {s : BeaconState p .phase0}
    {i : ValidatorIndex} {v w : Validator} (read : getValidator s i = .ok v)
    (stable : FinalityValidatorStable v w) :
    FinalityRegistryExtends s (s.setValidator i.toNat w) := by
  refine ⟨by simp [BeaconState.setValidator], ?_⟩
  intro j old found
  by_cases same : j = i
  · subst j
    have equal := Except.ok.inj (found.symm.trans read)
    subst old
    exact ⟨w, getValidator_setValidator_self read w, stable⟩
  · exact ⟨old, (getValidator_setValidator_of_ne same w).trans found,
      rfl, rfl, fun _ => rfl⟩

/-- Composition follows the actual successful list fold, including an empty fold. -/
theorem FinalityRegistryExtends.foldlM {α : Type}
    {f : BeaconState p .phase0 → α → Except TransitionError (BeaconState p .phase0)}
    {xs : List α} {s t : BeaconState p .phase0}
    (step : ∀ s x t, f s x = .ok t → FinalityRegistryExtends s t)
    (ran : xs.foldlM f s = .ok t) : FinalityRegistryExtends s t :=
  foldlM_ok_invariant (FinalityRegistryExtends s)
    (fun _ x _ h ok => h.trans (step _ x _ ok)) (.refl s) ran

/-- Exit scheduling writes only exit and withdrawability epochs.

Phase 0 `initiate_validator_exit` leaves signing identity and activation unchanged. -/
theorem finality_initiateValidatorExit_registry {cfg : Config}
    {s t : BeaconState p .phase0} {i : ValidatorIndex}
    (ran : initiateValidatorExit cfg s i = .ok t) : FinalityRegistryExtends s t := by
  obtain ⟨v, read, ⟨_, rfl⟩ | ⟨_, queued, _, _, queue, _, rfl⟩⟩ :=
    initiateValidatorExit_ok ran
  · exact .refl _
  · have same := (exitQueue_validators queue).1
    exact (FinalityRegistryExtends.of_validators same).trans
      (.setValidator ((getValidator_of_validators_eq same i).trans read)
        ⟨rfl, rfl, fun _ => rfl⟩)

/-- Slashing changes flags, withdrawability and balances, not signing identity. -/
theorem finality_slashValidator_registry {cfg : Config}
    {s t : BeaconState p .phase0} {i : ValidatorIndex} {whistleblower : Option ValidatorIndex}
    (ran : slashValidator cfg s i whistleblower = .ok t) : FinalityRegistryExtends s t := by
  unfold slashValidator at ran
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at ran
  obtain ⟨exited, exitedOk, validator, found, withdrawable, _, _, _, _, _, _, lowered,
    _, _, _, _, _, raised, _, final, done⟩ := ran
  have same := (slashValidator_last done).1.trans ((increaseBalance_validators final).trans
    ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered)))
  let marked := { validator with
    slashed := true
    withdrawableEpoch := max validator.withdrawableEpoch withdrawable }
  exact (finality_initiateValidatorExit_registry exitedOk).trans
    ((FinalityRegistryExtends.setValidator (w := marked) found ⟨rfl, rfl, fun _ => rfl⟩).trans
      (.of_validators same))

/-- A queued validator keeps its identity and activation epoch. -/
theorem finality_queueForActivation_stable {s : FinalityState p} {v w : Validator}
    (ran : queueForActivation s v = .ok w) : FinalityValidatorStable v w := by
  unfold queueForActivation at ran
  split at ran
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ran
    obtain ⟨_, _, rfl⟩ := ran
    exact ⟨rfl, rfl, fun _ => rfl⟩
  · cases ran
    exact ⟨rfl, rfl, fun _ => rfl⟩

/-- One eligibility or ejection step preserves existing positions.

The natural-number loop index is exact within the typed Phase 0 registry bound. -/
theorem finality_updateRegistryEntry_registry {cfg : Config} {s t : FinalityState p}
    {i : Nat} (inside : i < s.validators.data.size)
    (ran : updateRegistryEntry cfg s i = .ok t) : FinalityRegistryExtends s t := by
  have exactIndex := toNat_toUInt64_of_lt (s.validators.bound (by decide)) inside
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ran
  obtain ⟨v, read, w, queued, rest⟩ := ran
  have kept := FinalityRegistryExtends.setValidator read (finality_queueForActivation_stable queued)
  rw [exactIndex] at kept
  split at rest
  · exact kept.trans (finality_initiateValidatorExit_registry (liftAccessor_ok.mp rest))
  · cases rest
    exact kept

/-- A complete eligibility pass preserves existing positions. -/
theorem finality_fold_updateRegistryEntry_registry {cfg : Config}
    {indices : List Nat} {s t : FinalityState p}
    (inside : ∀ i ∈ indices, i < s.validators.data.size)
    (ran : indices.foldlM (updateRegistryEntry cfg) s = .ok t) :
    FinalityRegistryExtends s t := by
  induction indices generalizing s with
  | nil => cases ran; exact .refl _
  | cons i rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    have kept := finality_updateRegistryEntry_registry (inside i List.mem_cons_self) first
    have sizes := sameSizes_updateRegistryEntry first
    exact kept.trans (ih (fun j member => by
      rw [sizes.1]
      exact inside j (List.mem_cons_of_mem _ member)) tail)

/-- Activation scheduling only changes entries whose activation is still far future.

The eligibility witness is from the actual queue before its fold. -/
theorem finality_fold_activateValidator_registry {indices : List ValidatorIndex}
    {s t : FinalityState p} (unique : indices.Nodup)
    (eligible : ∀ i ∈ indices, ∃ v, getValidator s i = .ok v ∧
      isEligibleForActivation s v = true)
    (ran : indices.foldlM activateValidator s = .ok t) : FinalityRegistryExtends s t := by
  induction indices generalizing s with
  | nil => cases ran; exact .refl _
  | cons i rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨v, read, allowed⟩ := eligible i List.mem_cons_self
    have future : v.activationEpoch = FAR_FUTURE_EPOCH := by
      simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at allowed
      exact allowed.2
    have first' := first
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at first'
    obtain ⟨old, found, epoch, _, rfl⟩ := first'
    have equal := Except.ok.inj (found.symm.trans read)
    subst old
    have kept := FinalityRegistryExtends.setValidator read
      (show FinalityValidatorStable v { v with activationEpoch := epoch } from
        ⟨rfl, rfl, fun h => (h future).elim⟩)
    refine kept.trans (ih (List.nodup_cons.mp unique).2 (fun j member => ?_) tail)
    obtain ⟨w, found, allowed⟩ := eligible j (List.mem_cons_of_mem _ member)
    have ne : j ≠ i := fun h => (List.nodup_cons.mp unique).1 (h ▸ member)
    exact ⟨w, (getValidator_setValidator_of_ne ne _).trans found, allowed⟩

/-- Phase 0 registry processing preserves the identity of every existing index. -/
theorem finality_processRegistryUpdates_registry {cfg : Config} {s t : FinalityState p}
    (ran : processRegistryUpdates cfg s = .ok t) : FinalityRegistryExtends s t := by
  simp only [processRegistryUpdates, show ¬Fork.pectra ≤ Fork.phase0 by decide,
    ↓reduceIte, bind_ok_iff] at ran
  obtain ⟨middle, updated, activated⟩ := ran
  exact (finality_fold_updateRegistryEntry_registry
    (fun _ member => List.mem_range.mp member) updated).trans
    (finality_fold_activateValidator_registry
      (activationQueue_nodup (middle.validators.bound (by decide))).take
      (fun _ member => getValidator_of_mem_activationQueue
        (middle.validators.bound (by decide)) (List.mem_of_mem_take member)) activated)

/-- Effective-balance updates leave identity and activation unchanged. -/
theorem finality_processEffectiveBalanceUpdates_registry {s t : FinalityState p}
    (ran : processEffectiveBalanceUpdates s = .ok t) : FinalityRegistryExtends s t := by
  simp only [processEffectiveBalanceUpdates, show ¬Fork.pectra ≤ Fork.phase0 by decide,
    ↓reduceIte] at ran
  have preserve : ∀ (indices : List Nat) (a b : FinalityState p),
      (∀ i ∈ indices, i < a.validators.data.size) →
      indices.foldlM updateEffectiveBalance a = .ok b → FinalityRegistryExtends a b := by
    intro indices
    induction indices with
    | nil => intro a b _ ok; cases ok; exact .refl _
    | cons i rest ih =>
      intro a b inside ok
      obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ok
      have sizes := sameSizes_updateEffectiveBalance first
      have exactIndex := toNat_toUInt64_of_lt (a.validators.bound (by decide))
        (inside i List.mem_cons_self)
      have first' := first
      simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
        Except.ok.injEq] at first'
      obtain ⟨v, read, _, _, balance, _, eq⟩ := first'
      have kept := FinalityRegistryExtends.setValidator read
        (show FinalityValidatorStable v { v with effectiveBalance := balance } from
          ⟨rfl, rfl, fun _ => rfl⟩)
      rw [exactIndex, eq] at kept
      exact kept.trans (ih middle b (fun j member => by
        rw [sizes.1]
        exact inside j (List.mem_cons_of_mem _ member)) tail)
  exact preserve _ s t (fun _ member => List.mem_range.mp member) ran

/-- A Phase 0 attestation only appends a pending record. -/
theorem finality_processAttestation_registry {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {a : Attestation p .phase0}
    (ran : processAttestation cfg checks s a = .ok t) : FinalityRegistryExtends s t := by
  apply FinalityRegistryExtends.of_validators
  obtain ⟨_, _, _, _, _, recorded, _, _, _⟩ := processAttestation_records (by decide) ran
  cases current : a.data.target.epoch == getCurrentEpoch s <;>
    simp only [recordPendingAttestation, current, Bool.false_eq_true, ↓reduceIte] at recorded <;>
    split at recorded <;> cases recorded <;> rfl

/-- Proposer slashing preserves every existing registry position. -/
theorem finality_processProposerSlashing_registry {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {a : ProposerSlashing}
    (ran : processProposerSlashing cfg checks s a = .ok t) : FinalityRegistryExtends s t := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ran
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ran
  exact finality_slashValidator_registry slashed

/-- One attester-slashing index either changes no state or performs a real slashing. -/
theorem finality_slashIfSlashable_registry {cfg : Config}
    {s t : FinalityState p × Bool} {i : ValidatorIndex}
    (ran : slashIfSlashable cfg s i = .ok t) : FinalityRegistryExtends s.1 t.1 := by
  obtain ⟨s, flag⟩ := s
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ran
  obtain ⟨_, _, ran⟩ := ran
  split at ran
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ran
    obtain ⟨_, slashed, rfl⟩ := ran
    exact finality_slashValidator_registry slashed
  · cases ran
    exact .refl _

/-- Attester slashing composes the actual per-index slashing calls. -/
theorem finality_processAttesterSlashing_registry {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {a : AttesterSlashing p .phase0}
    (ran : processAttesterSlashing cfg checks s a = .ok t) : FinalityRegistryExtends s t := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ran
  exact foldlM_ok_invariant (fun step => FinalityRegistryExtends s step.1)
    (fun _ _ _ prior ok => prior.trans (finality_slashIfSlashable_registry ok)) (.refl s) folded

/-- A new Phase 0 deposit appends a fresh position, leaving the prefix unchanged. -/
theorem finality_addValidatorToRegistry_registry {s t : FinalityState p}
    {key : BLSPubkey} {credentials : Bytes32} {amount : Gwei}
    (ran : addValidatorToRegistry s key credentials amount = .ok t) :
    FinalityRegistryExtends s t := by
  simp only [addValidatorToRegistry, show ¬Fork.altair ≤ Fork.phase0 by decide,
    ↓reduceDIte] at ran
  split at ran
  · cases ran
    refine ⟨by simp, ?_⟩
    intro i v found
    have inside : i.toNat < s.validators.data.size := by
      unfold getValidator at found
      split at found
      · exact (Array.getElem?_eq_some_iff.mp ‹_›).1
      · cases found
    refine ⟨v, ?_, rfl, rfl, fun _ => rfl⟩
    simpa only [getValidator, Array.getElem?_push,
      show i.toNat ≠ s.validators.data.size by omega, ↓reduceIte] using found
  · cases ran

/-- Deposits to known keys change balances; deposits to new keys only append. -/
theorem finality_applyDeposit_registry {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {key : BLSPubkey} {credentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (ran : applyDeposit cfg checks s key credentials amount signature = .ok t) :
    FinalityRegistryExtends s t := by
  simp only [applyDeposit, show ¬Fork.pectra ≤ Fork.phase0 by decide, ↓reduceDIte,
    applyPendingDeposit] at ran
  split at ran
  · simp only [bind_ok_iff] at ran
    obtain ⟨_, _, ran⟩ := ran
    split at ran
    · exact finality_addValidatorToRegistry_registry ran
    · cases ran; exact .refl _
  · exact .of_validators (increaseBalance_validators (liftAccessor_ok.mp ran))

/-- Advancing the deposit cursor does not write the validator registry. -/
theorem finality_processDeposit_registry {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {a : Deposit}
    (ran : processDeposit cfg checks (by decide) s a = .ok t) : FinalityRegistryExtends s t := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok ran
  exact (FinalityRegistryExtends.of_validators
    (s := s) (t := { s with eth1DepositIndex := fun _ => next }) rfl).trans
    (finality_applyDeposit_registry applied)

/-- Voluntary exits preserve signing identity and the assigned activation epoch. -/
theorem finality_processVoluntaryExit_registry {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {a : SignedVoluntaryExit}
    (ran : processVoluntaryExit cfg checks s a = .ok t) : FinalityRegistryExtends s t := by
  simp only [processVoluntaryExit, show ¬Fork.pectra ≤ Fork.phase0 by decide,
    ↓reduceIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ran
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ran
  exact finality_initiateValidatorExit_registry exited

/-- All Phase 0 block operations preserve existing registry identities. -/
theorem finality_processOperations_registry {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {body : BeaconBlockBody p .phase0}
    (ran : processOperations cfg checks s body = .ok t) : FinalityRegistryExtends s t := by
  unfold processOperations at ran
  split at ran
  · cases ran
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ran
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := ran
  simp only [show ¬Fork.shapella ≤ Fork.phase0 by decide, ↓reduceDIte,
    pure, Except.pure, Except.ok.injEq] at changesOk
  subst t
  exact (FinalityRegistryExtends.foldlM
    (fun _ _ _ ok => finality_processProposerSlashing_registry ok) proposersOk).trans <|
    (FinalityRegistryExtends.foldlM
      (fun _ _ _ ok => finality_processAttesterSlashing_registry ok) attestersOk).trans <|
    (FinalityRegistryExtends.foldlM
      (fun _ _ _ ok => finality_processAttestation_registry ok) attestedOk).trans <|
    (FinalityRegistryExtends.foldlM
      (fun _ _ _ ok => finality_processDeposit_registry ok) depositedOk).trans <|
    FinalityRegistryExtends.foldlM
      (fun _ _ _ ok => finality_processVoluntaryExit_registry ok) exitsOk

/-- Header processing writes no registry field. -/
theorem finality_processBlockHeader_registry {s t : FinalityState p} {b : BeaconBlock p .phase0}
    (ran : processBlockHeader s b = .ok t) : FinalityRegistryExtends s t := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq ran
  exact .of_validators rfl

/-- RANDAO processing writes no registry field. -/
theorem finality_processRandao_registry {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {body : BeaconBlockBody p .phase0}
    (ran : processRandao cfg checks s body = .ok t) : FinalityRegistryExtends s t := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq ran
  exact .of_validators rfl

/-- Deposit voting writes no registry field. -/
theorem finality_processEth1Data_registry {s t : FinalityState p}
    {body : BeaconBlockBody p .phase0}
    (ran : processEth1Data (by decide) s body = .ok t) : FinalityRegistryExtends s t := by
  have same := (processEth1Data_eq ran).2.2
  exact .of_validators (congrArg (fun s => s.validators) same)

/-- A Phase 0 block preserves existing registry identities. -/
theorem finality_processBlock_registry {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {b : BeaconBlock p .phase0}
    (ran : processBlock cfg checks eng s b = .ok t) : FinalityRegistryExtends s t := by
  simp only [processBlock, show ¬Fork.altair ≤ Fork.phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at ran
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := ran
  exact (finality_processBlockHeader_registry headerOk).trans <|
    (finality_processRandao_registry randaoOk).trans <|
    (finality_processEth1Data_registry eth1Ok).trans
      (finality_processOperations_registry operationsOk)

/-- Epoch processing preserves identities and activation epochs already assigned. -/
theorem finality_processEpoch_registry {cfg : Config} {s t : FinalityState p}
    (inv : Invariant s) (ran : processEpoch cfg s = .ok t) : FinalityRegistryExtends s t := by
  simp only [processEpoch, show ¬Fork.altair ≤ Fork.phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at ran
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := ran
  have justifiedRegistry :=
    (processJustificationAndFinalization_invariant inv.ordered inv.settled justifiedOk).2.2.2.2.1
  have clearedRegistry : cleared.validators = balanced.validators := by
    obtain ⟨_, _, rfl⟩ := processSlashingsReset_eq clearedOk
    rfl
  have mixedRegistry : mixed.validators = cleared.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    rfl
  exact (FinalityRegistryExtends.of_validators justifiedRegistry).trans <|
    (FinalityRegistryExtends.of_validators
      (processRewardsAndPenalties_validators rewardedOk)).trans <|
    (finality_processRegistryUpdates_registry registeredOk).trans <|
    (FinalityRegistryExtends.of_validators (processSlashings_validators slashedOk)).trans <|
    (FinalityRegistryExtends.of_validators (processEth1DataReset_validators resetOk)).trans <|
    (finality_processEffectiveBalanceUpdates_registry balancedOk).trans <|
    (FinalityRegistryExtends.of_validators clearedRegistry).trans <|
    (FinalityRegistryExtends.of_validators mixedRegistry).trans <|
    (FinalityRegistryExtends.of_validators
      (processHistoricalRootsUpdate_validators rootedOk)).trans <|
    FinalityRegistryExtends.of_validators (processParticipationRecordUpdates_validators rotated)

/-- Slot caching changes roots and the latest header, never the registry. -/
theorem finality_processSlot_registry {s t : FinalityState p}
    (ran : processSlot s = .ok t) : FinalityRegistryExtends s t := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok ran
  exact .of_validators rfl

/-- One slot composes caching, optional epoch processing and the slot increment. -/
theorem finality_advanceSlot_registry {cfg : Config} {s t : FinalityState p}
    (inv : Invariant s) (ran : advanceSlot cfg s = .ok t) : FinalityRegistryExtends s t := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := ran
  have kept := finality_processSlot_registry cachedOk
  have epoch : FinalityRegistryExtends cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact finality_processEpoch_registry ((frame_processSlot cachedOk).invariant inv) epochedOk
    · cases epochedOk; exact .refl _
  exact (kept.trans epoch).trans (.of_validators rfl)

/-- Any successful slot prefix preserves existing registry positions. -/
theorem finality_advanceSlots_registry {cfg : Config} {s t : FinalityState p} {n : Nat}
    (inv : Invariant s) (ran : advanceSlots cfg n s = .ok t) : FinalityRegistryExtends s t := by
  induction n generalizing s with
  | zero => cases ran; exact .refl _
  | succ n ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    exact (finality_advanceSlot_registry inv first).trans
      (ih (advanceSlot_invariant (by decide) inv first).1 tail)

/-- Advancing to a block slot preserves existing registry positions. -/
theorem finality_processSlots_registry {cfg : Config} {s t : FinalityState p} {slot : Slot}
    (inv : Invariant s) (ran : processSlots cfg s slot = .ok t) : FinalityRegistryExtends s t := by
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at ran
  obtain ⟨_, _, advanced⟩ := ran
  exact finality_advanceSlots_registry inv advanced

/-- A validated transition preserves existing registry positions. -/
theorem finality_stateTransition_registry {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {b : FinalityBlock p}
    (inv : Invariant s) (ran : stateTransition cfg checks eng s b true = .ok t) :
    FinalityRegistryExtends s t := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok ran
  exact (finality_processSlots_registry inv slotsOk).trans (finality_processBlock_registry blockOk)

/-- A chain preserves existing registry positions without a cryptographic assumption. -/
theorem finality_runs_registry {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {bs : List (FinalityBlock p)}
    (inv : Invariant s) (ran : finalityRuns cfg checks eng s bs t) :
    FinalityRegistryExtends s t := by
  induction bs generalizing s with
  | nil => cases ran; exact .refl _
  | cons b bs ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    exact (finality_stateTransition_registry inv first).trans
      (ih (stateTransition_invariant (by decide) inv first).1 tail)

/-- Existing keys, credentials and C-active activation epochs remain at their indices. -/
theorem finality_validator_alignment (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) (c after : FinalityState p) (bs : List (FinalityBlock p))
    (inv : Invariant c) (ran : finalityRuns cfg checks eng c bs after) :
    c.validators.data.size ≤ after.validators.data.size ∧
      ∀ (i : ValidatorIndex) (v : Validator), getValidator c i = .ok v →
        ∃ w, getValidator after i = .ok w ∧ w.pubkey = v.pubkey ∧
          w.withdrawalCredentials = v.withdrawalCredentials ∧
          (isActiveValidator v (getCurrentEpoch c) = true →
            w.activationEpoch = v.activationEpoch) := by
  have kept := finality_runs_registry inv ran
  refine ⟨kept.1, fun i v read => ?_⟩
  obtain ⟨w, found, key, credentials, epoch⟩ := kept.2 i v read
  refine ⟨w, found, key, credentials, fun active => epoch ?_⟩
  intro future
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  have ordered := inv.exitsOrdered v (mem_of_getValidator read)
  rw [future] at active
  have top := v.exitEpoch.toNat_lt
  have current := (getCurrentEpoch c).toNat_lt
  have a := UInt64.le_iff_toNat_le.mp active.1
  have b := UInt64.lt_iff_toNat_lt.mp active.2
  change 18446744073709551615 ≤ _ at a
  omega

/-- Successful block prefixes retain the invariant needed by intermediate slot proofs. -/
theorem finality_runs_invariant {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {bs : List (FinalityBlock p)}
    (inv : Invariant s) (ran : finalityRuns cfg checks eng s bs t) : Invariant t :=
  foldlM_ok_invariant Invariant
    (fun _ _ _ h ok => (stateTransition_invariant (by decide) h ok).1) inv ran

/-- Every collected block, slot and cache observation preserves C's registry prefix.

The collector emits a state only after the corresponding prefix succeeds.

No assumption about a failed continuation is needed. -/
theorem finality_observations_registry {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t : FinalityState p} {bs : List (FinalityBlock p)}
    (inv : Invariant c) (member : t ∈ finalityObservations cfg checks eng c bs) :
    FinalityRegistryExtends c t := by
  simp only [finalityObservations, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨⟨b, i⟩, _, member⟩
  · exact .refl _
  cases prefixOk : (bs.take i).foldlM (fun s b => stateTransition cfg checks eng s b true) c with
  | error e => simp [prefixOk] at member
  | ok before =>
    simp only [prefixOk, List.mem_append, List.mem_cons, List.mem_flatMap] at member
    have kept := finality_runs_registry inv prefixOk
    have holds := finality_runs_invariant inv prefixOk
    rcases member with output | rfl | ⟨n, _, member⟩
    · cases block : stateTransition cfg checks eng before b true with
      | error e => simp [block, Except.toOption] at output
      | ok after =>
        simp only [block, Except.toOption, Option.toList, List.mem_singleton] at output
        subst t
        exact kept.trans (finality_stateTransition_registry holds block)
    · exact kept
    · cases slots : advanceSlots cfg n before with
      | error e => simp [slots] at member
      | ok atStep =>
        simp only [slots, List.mem_cons] at member
        have step := kept.trans (finality_advanceSlots_registry holds slots)
        rcases member with rfl | member
        · exact step
        · cases cache : processSlot atStep with
          | error e => simp [cache, Except.toOption] at member
          | ok cached =>
            simp only [cache, Except.toOption, Option.toList, List.mem_singleton] at member
            subst t
            exact step.trans (finality_processSlot_registry cache)

/-- Alignment at the actual checked attestation input, through its concrete processing prefix.

Phase 0 `process_block` runs header, randomness, voting and slashing before attestations.

Thus signer keys at these positions are C's keys. -/
theorem finality_attestation_site_registry {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c before atSlot header randao eth1 proposers attesters
      inclusion : FinalityState p} {earlier : List (FinalityBlock p)} {b : FinalityBlock p}
    {attestationPrefix : List (Attestation p .phase0)} (inv : Invariant c)
    (ran : finalityRuns cfg checks eng c earlier before)
    (slots : processSlots cfg before b.message.slot = .ok atSlot)
    (headerOk : processBlockHeader atSlot b.message = .ok header)
    (randaoOk : processRandao cfg checks header b.message.body = .ok randao)
    (eth1Ok : processEth1Data (by decide) randao b.message.body = .ok eth1)
    (proposersOk : b.message.body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing cfg checks) eth1 = .ok proposers)
    (attestersOk : b.message.body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing cfg checks) proposers = .ok attesters)
    (attestationsOk : attestationPrefix.foldlM (processAttestation cfg checks) attesters =
      .ok inclusion) :
    FinalityRegistryExtends c inclusion := by
  exact (finality_runs_registry inv ran).trans <|
    (finality_processSlots_registry (finality_runs_invariant inv ran) slots).trans <|
    (finality_processBlockHeader_registry headerOk).trans <|
    (finality_processRandao_registry randaoOk).trans <|
    (finality_processEth1Data_registry eth1Ok).trans <|
    (FinalityRegistryExtends.foldlM
      (fun _ _ _ ok => finality_processProposerSlashing_registry ok) proposersOk).trans <|
    (FinalityRegistryExtends.foldlM
      (fun _ _ _ ok => finality_processAttesterSlashing_registry ok) attestersOk).trans <|
    FinalityRegistryExtends.foldlM
      (fun _ _ _ ok => finality_processAttestation_registry ok) attestationsOk

/-- Partition a raw marked sum by a predicate on its validator entries.

The Phase 0 `get_total_balance` raw sum counts each marked position once.

Both parts retain the original validator and mark at that position. -/
theorem sumMarked_partition (validators : Array Validator) (marked : Array Bool)
    (select : Validator → Bool) :
    sumMarked validators marked =
      ((validators.zip marked).toList.map fun (v, m) =>
        if m && select v then v.effectiveBalance.toNat else 0).sum +
      ((validators.zip marked).toList.map fun (v, m) =>
        if m && !select v then v.effectiveBalance.toNat else 0).sum := by
  rw [sumMarked_eq_sum]
  have partition : ∀ entries : List (Validator × Bool),
      (entries.map fun (v, m) => if m then v.effectiveBalance.toNat else 0).sum =
        (entries.map fun (v, m) => if m && select v then v.effectiveBalance.toNat else 0).sum +
        (entries.map fun (v, m) => if m && !select v then v.effectiveBalance.toNat else 0).sum := by
    intro entries
    induction entries with
    | nil => simp
    | cons entry rest ih =>
      obtain ⟨v, m⟩ := entry
      cases m <;> cases h : select v <;> simp [h, ih, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
  exact partition _

/-- Split a raw marked sum at a reference registry length.

The prefix and suffix retain the exact indexed entries of the later registry.

This also holds when the marks are shorter than the registry. -/
theorem sumMarked_prefix_suffix (validators : Array Validator) (marked : Array Bool)
    (n : Nat) :
    sumMarked validators marked =
      (((validators.zip marked).toList.take n).map fun (v, m) =>
        if m then v.effectiveBalance.toNat else 0).sum +
      (((validators.zip marked).toList.drop n).map fun (v, m) =>
        if m then v.effectiveBalance.toNat else 0).sum := by
  rw [sumMarked_eq_sum, ← List.sum_append, ← List.map_append, List.take_append_drop]

/-- A raw marked sum as a sum over exact natural-number registry indices.

Missing marks contribute zero, matching the array zip's truncation. -/
theorem sumMarked_eq_index_sum (validators : Array Validator) (marked : Array Bool) :
    sumMarked validators marked =
      ((List.range validators.size).map fun i =>
        if marked[i]?.getD false then
          (validators[i]?.map (fun v => v.effectiveBalance.toNat)).getD 0 else 0).sum := by
  rw [sumMarked_eq_sum]
  have lists : ∀ (vs : List Validator) (ms : List Bool),
      ((vs.zip ms).map fun (v, m) => if m then v.effectiveBalance.toNat else 0).sum =
        ((List.range vs.length).map fun i =>
          if ms[i]?.getD false then
            (vs[i]?.map (fun v => v.effectiveBalance.toNat)).getD 0 else 0).sum := by
    intro vs
    induction vs with
    | nil => intro ms; simp
    | cons v vs ih =>
      intro ms
      cases ms with
      | nil => simp [List.map_const', List.sum_replicate_nat]
      | cons m ms =>
        simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons,
          List.range_succ_eq_map, List.map_map, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Option.getD_some, Option.map_some, Function.comp_def]
        rw [ih]
  simpa only [Array.toList_zip, Array.length_toList, Array.getElem?_toList] using
    lists validators.toList marked.toList

/-- Split a threshold's raw marked sum into C-active and non-C-active indices.

The partition reads activity from C but weight and marks from the weighing state.

It never matches validators by key or changes the identity at an index. -/
theorem finality_sumMarked_active_partition (c s : FinalityState p) (marked : Array Bool) :
    sumMarked s.validators.data marked =
      ((List.range s.validators.data.size).map fun i =>
        if finalityActive c i && marked[i]?.getD false then finalityEffective s i else 0).sum +
      ((List.range s.validators.data.size).map fun i =>
        if !finalityActive c i && marked[i]?.getD false then finalityEffective s i else 0).sum := by
  rw [sumMarked_eq_index_sum]
  have partition : ∀ indices : List Nat,
      (indices.map fun i =>
        if marked[i]?.getD false then finalityEffective s i else 0).sum =
      (indices.map fun i =>
        if finalityActive c i && marked[i]?.getD false then finalityEffective s i else 0).sum +
      (indices.map fun i =>
        if !finalityActive c i && marked[i]?.getD false then finalityEffective s i else 0).sum := by
    intro indices
    induction indices with
    | nil => simp
    | cons i rest ih =>
      cases h : finalityActive c i <;> cases m : marked[i]?.getD false <;>
        simp [h, m, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  convert partition (List.range s.validators.data.size) using 1
  congr 1
  apply List.map_congr_left
  intro i _
  cases h : s.validators.data[i]? <;> simp [finalityEffective, h]

/-- C-active weight is supported on C's registry prefix even in a larger later registry. -/
theorem finality_active_sum_prefix (c s : FinalityState p) (weight : Nat → Nat)
    (size : c.validators.data.size ≤ s.validators.data.size) :
    ((List.range s.validators.data.size).map fun i =>
      if finalityActive c i then weight i else 0).sum =
    ((List.range c.validators.data.size).map fun i =>
      if finalityActive c i then weight i else 0).sum := by
  have length : s.validators.data.size =
      c.validators.data.size + (s.validators.data.size - c.validators.data.size) := by omega
  rw [length, List.range_add, List.map_append, List.sum_append, List.map_map]
  have zero : ((List.range (s.validators.data.size - c.validators.data.size)).map
      fun i => if finalityActive c (c.validators.data.size + i)
        then weight (c.validators.data.size + i) else 0).sum = 0 := by
    have empty : ∀ i, finalityActive c (c.validators.data.size + i) = false := by
      intro i
      have outside : c.validators.data[c.validators.data.size + i]? = none :=
        Array.getElem?_eq_none (by omega)
      simp only [finalityActive, outside]
    simp [empty, List.map_const', List.sum_replicate_nat]
  simp only [Function.comp_def, zero, Nat.add_zero]

/-- Threshold weight from C-active positions can be summed on C's own prefix. -/
theorem finality_sumMarked_reference_partition (c s : FinalityState p) (marked : Array Bool)
    (size : c.validators.data.size ≤ s.validators.data.size) :
    sumMarked s.validators.data marked =
      ((List.range c.validators.data.size).map fun i =>
        if finalityActive c i && marked[i]?.getD false then finalityEffective s i else 0).sum +
      ((List.range s.validators.data.size).map fun i =>
        if !finalityActive c i && marked[i]?.getD false then finalityEffective s i else 0).sum := by
  rw [finality_sumMarked_active_partition]
  congr 1
  have prefixSum := finality_active_sum_prefix c s
    (fun i => if marked[i]?.getD false then finalityEffective s i else 0) size
  simpa only [Bool.and_eq_true, ite_and] using prefixSum

end Finality

end EthLib.Consensus
