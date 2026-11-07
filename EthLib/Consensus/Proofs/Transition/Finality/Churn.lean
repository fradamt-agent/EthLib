module

public import EthLib.Consensus.Proofs.Transition.Finality.Definitions

/-!
# Realized Phase 0 churn

The Phase 0 beacon-chain specification, `get_validator_churn_limit`, caps a scheduling pass.

Its `initiate_validator_exit` allocates exits to cohorts with that cap.

Activation cohorts instead share the epoch computed by `compute_activation_exit_epoch`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Cryptography.Bls

variable {p : Preset}

/-- A registry population bound also bounds the Phase 0 scheduling limit.

The divisor may be zero, as in Lean's natural-number division.

No positivity assumption on a configurable field is needed. -/
theorem finality_churnLimit_le {cfg : Config} {s : FinalityState p} {population : Nat}
    (within : s.RegistryWithinLimit) (size : s.validators.data.size ≤ population) :
    (getValidatorChurnLimit cfg s).toNat ≤
      max cfg.MIN_PER_EPOCH_CHURN_LIMIT.toNat (population / cfg.CHURN_LIMIT_QUOTIENT.toNat) := by
  have count : (getActiveValidatorIndices s (getCurrentEpoch s)).length ≤ population := by
    apply Nat.le_trans (List.length_filterMap_le _ _) ?_
    simpa only [List.length_zipIdx, Array.length_toList] using size
  have divided := Nat.div_le_div_right (c := cfg.CHURN_LIMIT_QUOTIENT.toNat) count
  -- The registry bound makes the conversion of the active count exact.
  have exactCount := toNat_length_getActiveValidatorIndices within (getCurrentEpoch s)
  unfold getValidatorChurnLimit
  change UInt64.toNat (if _ then _ else _) ≤ _
  split
  · rw [UInt64.toNat_div, exactCount]
    exact Nat.le_trans divided (Nat.le_max_right _ _)
  · exact Nat.le_max_left _ _

/-- An observed registry-size envelope bounds the scheduling limit by the horizon cap. -/
theorem finality_churnLimit_le_cap {cfg : Config} {c s : FinalityState p} {n : Nat}
    (within : s.RegistryWithinLimit)
    (size : s.validators.data.size ≤ c.validators.data.size +
      (n + 1) * p.SLOTS_PER_EPOCH.toNat * p.MAX_DEPOSITS.toNat) :
    (getValidatorChurnLimit cfg s).toNat ≤ finalityChurnCap cfg c n := by
  exact Nat.le_trans (finality_churnLimit_le within size) (Nat.le_max_right _ _)

/-- A newly allocated finite exit joins a cohort strictly below the uniform cap.

The outer `max 1` is needed when the configured churn limit is zero. -/
theorem finality_exitQueueEpoch_cohort {cfg : Config} {c s : FinalityState p}
    {n : Nat} {epoch : Epoch} (within : s.RegistryWithinLimit)
    (size : s.validators.data.size ≤ c.validators.data.size +
      (n + 1) * p.SLOTS_PER_EPOCH.toNat * p.MAX_DEPOSITS.toNat)
    (allocated : exitQueueEpoch cfg s = .ok epoch) (finite : epoch ≠ FAR_FUTURE_EPOCH) :
    (s.validators.data.toList.filter (·.exitEpoch == epoch)).length <
      finalityChurnCap cfg c n := by
  have localBound := exitQueueEpoch_churn allocated finite
  have limit := finality_churnLimit_le_cap (cfg := cfg) within size
  have positive : 1 ≤ finalityChurnCap cfg c n := Nat.le_max_left _ _
  exact Nat.lt_of_lt_of_le localBound (Nat.max_le.mpr ⟨positive, limit⟩)

/-- Replacing one registry entry adds at most one member to an exit cohort. -/
theorem finality_exitCohort_setValidator_le (s : FinalityState p) (index : Nat)
    (validator : Validator) (epoch : Epoch) :
    (((s.setValidator index validator).validators.data.toList).filter
      (·.exitEpoch == epoch)).length ≤
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length + 1 := by
  simp only [BeaconState.setValidator, Array.toList_set!]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  by_cases inside : index < s.validators.data.toList.length
  · rw [List.countP_set inside]
    split <;> split <;> omega
  · rw [List.set_eq_of_length_le (by omega)]
    omega

/-- Replacing an entry without changing its exit epoch preserves every exit cohort. -/
theorem finality_exitCohort_setValidator_eq {s : FinalityState p} {index : Nat}
    {old : Validator} (found : s.validators.data[index]? = some old)
    (validator : Validator) (same : validator.exitEpoch = old.exitEpoch) (epoch : Epoch) :
    (((s.setValidator index validator).validators.data.toList).filter
      (·.exitEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
  have inside := (Array.getElem?_eq_some_iff.mp found).1
  have read := (Array.getElem?_eq_some_iff.mp found).2
  simp only [BeaconState.setValidator, Array.toList_set!]
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
    List.countP_set (by simpa using inside)]
  simp only [Array.getElem_toList, read, same]
  split
  · have present : 0 < s.validators.data.toList.countP (·.exitEpoch == epoch) := by
      apply List.countP_pos_iff.mpr
      exact ⟨old, by simpa using (Array.mem_of_getElem? found), ‹_›⟩
    omega
  · omega

/-- Starting an exit cannot overfill its allocated finite cohort.

This counts validators assigned to the exit epoch, not calls made in the current epoch. -/
theorem finality_initiateValidatorExit_cohort {cfg : Config} {s t : FinalityState p}
    {index : ValidatorIndex} {cap : Nat}
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : max 1 (getValidatorChurnLimit cfg s).toNat ≤ cap)
    (computed : initiateValidatorExit cfg s index = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  obtain ⟨old, found, ⟨_, rfl⟩ | ⟨fresh, queued, allocated, withdrawable, queue, _, rfl⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact bounded
  have unchanged := exitQueue_state (by decide : Fork.phase0 < .pectra) queue
  subst queued
  have allocation : exitQueueEpoch cfg s = .ok allocated := by
    simp only [exitQueue, show ¬Fork.pectra ≤ .phase0 by decide, ↓reduceDIte,
      bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at queue
    obtain ⟨epoch, ok, _, rfl⟩ := queue
    exact ok
  intro epoch finite
  by_cases same : allocated = epoch
  · subst epoch
    have before := exitQueueEpoch_churn allocation finite
    have afterBound := finality_exitCohort_setValidator_le s index.toNat
      { old with exitEpoch := allocated, withdrawableEpoch := withdrawable } allocated
    omega
  · have noChange :
        ((s.validators.data.toList.set index.toNat
          { old with exitEpoch := allocated, withdrawableEpoch := withdrawable }).filter
          (·.exitEpoch == epoch)).length =
        (s.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
      have found : s.validators.data[index.toNat]? = some old := by
        unfold getValidator at found
        split at found
        · cases found
          assumption
        · cases found
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have read := (Array.getElem?_eq_some_iff.mp found).2
      rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter,
        List.countP_set (by simpa using inside)]
      simp only [Array.getElem_toList, read, fresh, beq_iff_eq,
        show FAR_FUTURE_EPOCH ≠ epoch from Ne.symm finite, same, ↓reduceIte,
        Nat.sub_zero, Nat.add_zero]
    simpa only [BeaconState.setValidator, Array.toList_set!, noChange] using bounded epoch finite

/-- A successful Phase 0 deposit appends at most one registry entry. -/
theorem finality_applyDeposit_size {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {pubkey : BLSPubkey} {credentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed : applyDeposit cfg checks s pubkey credentials amount signature = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + 1 := by
  simp only [applyDeposit, show ¬Fork.pectra ≤ .phase0 by decide, ↓reduceDIte,
    applyPendingDeposit] at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨valid, _, rest⟩ := computed
    cases valid
    · cases rest
      omega
    · simp only [↓reduceIte] at rest
      unfold addValidatorToRegistry at rest
      split at rest
      · contradiction
      split at rest
      · cases rest
        simp only [Array.size_push, Nat.le_refl]
      · cases rest
  · have same := increaseBalance_validators (liftAccessor_ok.mp computed)
    rw [same]
    omega

/-- The Merkle-checked deposit step appends at most one registry entry. -/
theorem finality_processDeposit_size {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {deposit : Deposit}
    (computed : processDeposit cfg checks (by decide) s deposit = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + 1 := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok computed
  simpa only using finality_applyDeposit_size applied

/-- A list of successful Phase 0 deposits adds at most its length to the registry. -/
theorem finality_deposits_size {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {deposits : List Deposit}
    (computed : deposits.foldlM (processDeposit cfg checks (by decide)) s = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + deposits.length := by
  induction deposits generalizing s with
  | nil => cases computed; simp
  | cons deposit deposits ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    have added := finality_processDeposit_size first
    have remaining := ih rest
    simp only [List.length_cons]
    omega

/-- Phase 0 block operations grow the registry only through their deposits. -/
theorem finality_processOperations_size {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {body : BeaconBlockBody p .phase0}
    (computed : processOperations cfg checks s body = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + p.MAX_DEPOSITS.toNat := by
  have deposits := (processOperations_deposits computed).2 (by decide)
  unfold processOperations at computed
  split at computed
  · contradiction
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := computed
  simp only [show ¬Fork.shapella ≤ .phase0 by decide, ↓reduceDIte, pure, Except.pure,
    Except.ok.injEq] at changesOk
  subst t
  have one := foldlM_ok_invariant (SameSizes s)
    (fun _ _ _ prior ok => prior.trans (sameSizes_processProposerSlashing ok))
    (SameSizes.refl s) proposersOk
  have two := foldlM_ok_invariant (SameSizes s)
    (fun _ _ _ prior ok => prior.trans (sameSizes_processAttesterSlashing ok)) one attestersOk
  have three := foldlM_ok_invariant (SameSizes s)
    (fun _ _ _ prior ok => prior.trans (sameSizes_processAttestation ok)) two attestedOk
  have four := finality_deposits_size depositedOk
  have five := foldlM_ok_invariant (SameSizes deposited)
    (fun _ _ _ prior ok => prior.trans (sameSizes_processVoluntaryExit ok))
    (SameSizes.refl deposited) exitsOk
  have depositCap := Nat.min_le_left p.MAX_DEPOSITS.toNat
    ((s.eth1Data (by decide)).depositCount.toNat - (s.eth1DepositIndex (by decide)).toNat)
  rw [← deposits.2] at depositCap
  simp only [Array.length_toList] at four
  rw [five.1, three.1] at *
  omega

/-- A Phase 0 block grows the registry by at most its preset deposit limit. -/
theorem finality_processBlock_size {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {block : BeaconBlock p .phase0}
    (computed : processBlock cfg checks eng s block = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + p.MAX_DEPOSITS.toNat := by
  simp only [processBlock, show ¬Fork.altair ≤ .phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at computed
  obtain ⟨header, headerOk, randao, randaoOk, eth1, eth1Ok, operationsOk⟩ := computed
  have sizes := (sameSizes_processBlockHeader headerOk).trans
    ((sameSizes_processRandao randaoOk).trans (sameSizes_processEth1Data eth1Ok))
  have bound := finality_processOperations_size operationsOk
  rwa [sizes.1] at bound

/-- Epoch processing changes registry entries but not their number. -/
theorem finality_processEpoch_size {cfg : Config} {s t : FinalityState p}
    (computed : processEpoch cfg s = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  simp only [processEpoch, show ¬Fork.altair ≤ .phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have first := (sameSizes_processJustificationAndFinalization justifiedOk).trans
    ((processRewardsAndPenalties_sameSizes rewardedOk).trans
      ((processRegistryUpdates_ok registeredOk).2.trans
        ((processSlashings_ok slashedOk).2)))
  have resetRegistry := processEth1DataReset_validators resetOk
  have balanceSize := sameSizes_processEffectiveBalanceUpdates balancedOk
  have clearRegistry : cleared.validators = balanced.validators := by
    obtain ⟨_, _, rfl⟩ := processSlashingsReset_eq clearedOk
    rfl
  have mixRegistry : mixed.validators = cleared.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    rfl
  rw [processParticipationRecordUpdates_validators rotated,
    processHistoricalRootsUpdate_validators rootedOk, mixRegistry, clearRegistry,
    balanceSize.1, resetRegistry, first.1]

/-- Slot advancement never changes the registry size. -/
theorem finality_advanceSlot_size {cfg : Config} {s t : FinalityState p}
    (computed : advanceSlot cfg s = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cacheRegistry : cached.validators = s.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  change epoched.validators.data.size = _
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rw [finality_processEpoch_size epochedOk, cacheRegistry]
  · cases epochedOk
    rw [cacheRegistry]

/-- Any successful sequence of empty slots preserves the registry size. -/
theorem finality_advanceSlots_size {cfg : Config} {s t : FinalityState p} {count : Nat}
    (computed : advanceSlots cfg count s = .ok t) :
    t.validators.data.size = s.validators.data.size := by
  induction count generalizing s with
  | zero => cases computed; rfl
  | succ count ih =>
    simp only [advanceSlots, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    exact (ih rest).trans (finality_advanceSlot_size first)

/-- A block transition grows the registry by at most one block's deposit limit. -/
theorem finality_stateTransition_size {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {b : FinalityBlock p}
    (computed : stateTransition cfg checks eng s b true = .ok t) :
    t.validators.data.size ≤ s.validators.data.size + p.MAX_DEPOSITS.toNat := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok computed
  have bound := finality_processBlock_size blockOk
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  rwa [finality_advanceSlots_size advancedOk] at bound

/-- Registry growth is bounded by the number of blocks times the deposit limit. -/
theorem finality_runs_size {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {bs : List (FinalityBlock p)}
    (computed : finalityRuns cfg checks eng s bs t) :
    t.validators.data.size ≤ s.validators.data.size + bs.length * p.MAX_DEPOSITS.toNat := by
  unfold finalityRuns at computed
  induction bs generalizing s with
  | nil => cases computed; simp
  | cons b bs ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    have added := finality_stateTransition_size first
    have remaining := ih rest
    simp only [List.length_cons, Nat.succ_mul]
    omega

/-- Strictly increasing block slots bound the number of blocks by the elapsed slots. -/
theorem finality_runs_length {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {bs : List (FinalityBlock p)}
    (computed : finalityRuns cfg checks eng s bs t) :
    s.slot.toNat + bs.length ≤ t.slot.toNat := by
  unfold finalityRuns at computed
  induction bs generalizing s with
  | nil => cases computed; simp
  | cons b bs ih =>
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, rest⟩ := computed
    obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok first
    have slots := UInt64.lt_iff_toNat_lt.mp (processSlots_slot slotsOk).1
    rw [← (processSlots_slot slotsOk).2,
      ← (frame_processBlock (by decide) blockOk).slot] at slots
    have remaining := ih rest
    simp only [List.length_cons]
    omega

/-- A horizon of n epochs allows at most n plus one partial epochs of slots. -/
theorem finality_slot_horizon {s t : FinalityState p} {n : Nat}
    (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (horizon : (getCurrentEpoch t).toNat - (getCurrentEpoch s).toNat ≤ n) :
    t.slot.toNat - s.slot.toNat ≤ (n + 1) * p.SLOTS_PER_EPOCH.toNat := by
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat] at horizon
  have remainder := Nat.mod_lt t.slot.toNat positive
  have decompose := Nat.mod_add_div t.slot.toNat p.SLOTS_PER_EPOCH.toNat
  have lower := Nat.div_mul_le_self s.slot.toNat p.SLOTS_PER_EPOCH.toNat
  have epochs : t.slot.toNat / p.SLOTS_PER_EPOCH.toNat ≤
      s.slot.toNat / p.SLOTS_PER_EPOCH.toNat + n := by omega
  have scaled := Nat.mul_le_mul_right p.SLOTS_PER_EPOCH.toNat epochs
  rw [Nat.add_mul] at scaled
  rw [Nat.mul_comm p.SLOTS_PER_EPOCH.toNat (t.slot.toNat / p.SLOTS_PER_EPOCH.toNat)]
    at decompose
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- Successful chains within a positive epoch horizon satisfy the registry envelope. -/
theorem finality_runs_size_horizon {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {bs : List (FinalityBlock p)}
    {n : Nat} (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (computed : finalityRuns cfg checks eng s bs t)
    (horizon : (getCurrentEpoch t).toNat - (getCurrentEpoch s).toNat ≤ n) :
    t.validators.data.size ≤ s.validators.data.size +
      (n + 1) * p.SLOTS_PER_EPOCH.toNat * p.MAX_DEPOSITS.toNat := by
  have size := finality_runs_size computed
  have length := finality_runs_length computed
  have elapsed := finality_slot_horizon positive horizon
  have count : bs.length ≤ (n + 1) * p.SLOTS_PER_EPOCH.toNat := by omega
  have deposits := Nat.mul_le_mul_right p.MAX_DEPOSITS.toNat count
  omega

end EthLib.Consensus
