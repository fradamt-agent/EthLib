module

public import EthLib.Consensus.Proofs.Transition.Finality.Definitions
public import EthLib.Consensus.Proofs.Transition.Finality.Registry

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

/-- Every collected observation preserves the active indices of an already reached epoch. -/
theorem finality_observations_active_indices {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t : FinalityState p} {bs : List (FinalityBlock p)}
    {epoch : Epoch} (inv : Invariant c) (past : epoch ≤ getCurrentEpoch c)
    (member : t ∈ finalityObservations cfg checks eng c bs) :
    getActiveValidatorIndices t epoch = getActiveValidatorIndices c epoch := by
  simp only [finalityObservations, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨⟨b, i⟩, _, member⟩
  · rfl
  cases prefixOk : (bs.take i).foldlM (fun s b => stateTransition cfg checks eng s b true) c with
  | error e => simp [prefixOk] at member
  | ok before =>
    simp only [prefixOk, List.mem_append, List.mem_cons, List.mem_flatMap] at member
    have kept := stateTransition_chain_active_indices (by decide) inv past prefixOk
    have holds := finality_runs_invariant inv prefixOk
    have later : epoch ≤ getCurrentEpoch before := by
      have slots := stateTransition_chain_slot_le (by decide) prefixOk
      have epochs := Nat.div_le_div_right (c := p.SLOTS_PER_EPOCH.toNat) slots
      apply UInt64.le_iff_toNat_le.mpr
      rw [getCurrentEpoch_toNat] at *
      exact Nat.le_trans (UInt64.le_iff_toNat_le.mp past) epochs
    rcases member with output | rfl | ⟨n, _, member⟩
    · cases block : stateTransition cfg checks eng before b true with
      | error e => simp [block, Except.toOption] at output
      | ok after =>
        simp only [block, Except.toOption, Option.toList, List.mem_singleton] at output
        subst t
        exact (stateTransition_active_indices (by decide) holds later block).trans kept
    · exact kept
    · cases slots : advanceSlots cfg n before with
      | error e => simp [slots] at member
      | ok atStep =>
        simp only [slots, List.mem_cons] at member
        have step := (advanceSlots_active_indices (by decide) n holds later slots).trans kept
        rcases member with rfl | member
        · exact step
        · cases cache : processSlot atStep with
          | error e => simp [cache, Except.toOption] at member
          | ok cached =>
            simp only [cache, Except.toOption, Option.toList, List.mem_singleton] at member
            subst t
            obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
            exact step

/-- Equal active-index queries give equal activity flags at every natural-number position. -/
theorem finalityActive_eq_of_indices {s t : FinalityState p}
    (same : getActiveValidatorIndices s (getCurrentEpoch s) =
      getActiveValidatorIndices t (getCurrentEpoch t)) (i : Nat) :
    finalityActive s i = finalityActive t i := by
  by_cases fits : i < 2 ^ 64
  · have exactIndex : i.toUInt64.toNat = i := by
      rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt fits]
    have one := mem_getActiveValidatorIndices (state := s)
      (s.validators.bound (by decide)) (epoch := getCurrentEpoch s) (index := i.toUInt64)
    have two := mem_getActiveValidatorIndices (state := t)
      (t.validators.bound (by decide)) (epoch := getCurrentEpoch t) (index := i.toUInt64)
    rw [exactIndex, same] at one
    rw [exactIndex] at two
    have equivalent := one.symm.trans two
    unfold finalityActive
    cases hs : s.validators.data[i]? <;> cases ht : t.validators.data[i]? <;>
      simp only [hs, ht, Option.some.injEq, reduceCtorEq, false_and,
        exists_false] at equivalent ⊢ <;> simp_all
  · have outside (u : FinalityState p) : u.validators.data[i]? = none := by
      have bounded := u.validators.bound (by decide : Fork.phase0 < .glamsterdam)
      have limit := p.VALIDATOR_REGISTRY_LIMIT.toNat_lt
      exact Array.getElem?_eq_none (by omega)
    simp only [finalityActive, outside]

/-- Joining the activation queue does not change an assigned exit epoch. -/
theorem finality_queueForActivation_exit {s : FinalityState p} {v w : Validator}
    (ran : queueForActivation s v = .ok w) : w.exitEpoch = v.exitEpoch := by
  unfold queueForActivation at ran
  split at ran
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ran
    obtain ⟨_, _, rfl⟩ := ran
    rfl
  · cases ran
    rfl

/-- An eligibility or ejection step preserves a uniform finite exit-cohort cap.

The scheduling limit is checked at the state after eligibility is updated. -/
theorem finality_updateRegistryEntry_cohort {cfg : Config} {s t : FinalityState p}
    {i cap : Nat} (inside : i < s.validators.data.size)
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : updateRegistryEntry cfg s i = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  have exactIndex := toNat_toUInt64_of_lt (s.validators.bound (by decide)) inside
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at ran
  obtain ⟨v, read, w, queued, rest⟩ := ran
  have found : s.validators.data[i]? = some v := by
    rw [← exactIndex]
    unfold getValidator at read
    split at read
    · cases read
      assumption
    · cases read
  have unchanged := finality_exitCohort_setValidator_eq found w
    (finality_queueForActivation_exit queued)
  have middle : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      ((s.setValidator i w).validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
    intro epoch finite
    rw [unchanged epoch]
    exact bounded epoch finite
  split at rest
  · exact finality_initiateValidatorExit_cohort middle
      (limit _ (by simp [BeaconState.setValidator])) (liftAccessor_ok.mp rest)
  · cases rest
    exact middle

/-- Assigning activation does not change any exit cohort. -/
theorem finality_activateValidator_exitCohort {s t : FinalityState p}
    {i : ValidatorIndex} (ran : activateValidator s i = .ok t) (epoch : Epoch) :
    (t.validators.data.toList.filter (·.exitEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨v, read, assigned, _, rfl⟩ := ran
  have found : s.validators.data[i.toNat]? = some v := by
    unfold getValidator at read
    split at read
    · cases read
      assumption
    · cases read
  exact finality_exitCohort_setValidator_eq found
    { v with activationEpoch := assigned } rfl epoch

/-- The complete registry pass preserves the finite exit-cohort cap.

Activation assignments leave the exit cohorts unchanged. -/
theorem finality_processRegistryUpdates_cohort {cfg : Config} {s t : FinalityState p}
    {cap : Nat}
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : processRegistryUpdates cfg s = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  simp only [processRegistryUpdates, show ¬Fork.pectra ≤ Fork.phase0 by decide,
    ↓reduceIte, bind_ok_iff] at ran
  obtain ⟨middle, updated, activated⟩ := ran
  have pass : ∀ (indices : List Nat) (a b : FinalityState p),
      a.validators.data.size = s.validators.data.size →
      (∀ i ∈ indices, i < a.validators.data.size) →
      (∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
        (a.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap) →
      indices.foldlM (updateRegistryEntry cfg) a = .ok b →
      ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
        (b.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
    intro indices
    induction indices with
    | nil => intro a b _ _ bounded ok; cases ok; exact bounded
    | cons i rest ih =>
      intro a b sizes inside bounded ok
      obtain ⟨next, first, tail⟩ := bind_ok_iff.mp ok
      have sizeNext := (sameSizes_updateRegistryEntry first).1
      have nextBound := finality_updateRegistryEntry_cohort (inside i List.mem_cons_self)
        bounded (fun u hu => limit u (hu.trans sizes)) first
      exact ih next b (sizeNext.trans sizes) (fun j member => by
        rw [sizeNext]
        exact inside j (List.mem_cons_of_mem _ member)) nextBound tail
  have middleBound := pass _ s middle rfl (fun _ member => List.mem_range.mp member)
    bounded updated
  intro epoch finite
  have same : (t.validators.data.toList.filter (·.exitEpoch == epoch)).length =
      (middle.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
    exact foldlM_ok_invariant
      (fun u => (u.validators.data.toList.filter (·.exitEpoch == epoch)).length =
        (middle.validators.data.toList.filter (·.exitEpoch == epoch)).length)
      (fun _ _ _ previous step => (finality_activateValidator_exitCohort step epoch).trans previous)
      rfl activated
  rw [same]
  exact middleBound epoch finite

/-- Slashing preserves the finite exit-cohort cap after allocating the validator's exit.

The later flag, withdrawability and reward writes do not change exit epochs. -/
theorem finality_slashValidator_cohort {cfg : Config} {s t : FinalityState p}
    {i : ValidatorIndex} {whistleblower : Option ValidatorIndex} {cap : Nat}
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : max 1 (getValidatorChurnLimit cfg s).toNat ≤ cap)
    (ran : slashValidator cfg s i whistleblower = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  unfold slashValidator at ran
  simp only [bind_ok_iff, liftArith, mapError_ok_iff] at ran
  obtain ⟨exited, exitedOk, validator, found, withdrawable, _, _, _, _, _, _, lowered,
    _, _, _, _, _, raised, _, final, done⟩ := ran
  have same := (slashValidator_last done).1.trans ((increaseBalance_validators final).trans
    ((increaseBalance_validators raised).trans (decreaseBalance_validators lowered)))
  have read : exited.validators.data[i.toNat]? = some validator := by
    unfold getValidator at found
    split at found
    · cases found
      assumption
    · cases found
  intro epoch finite
  let marked := { validator with
    slashed := true
    withdrawableEpoch := max validator.withdrawableEpoch withdrawable }
  rw [same, finality_exitCohort_setValidator_eq read marked rfl epoch]
  exact finality_initiateValidatorExit_cohort bounded limit exitedOk epoch finite

/-- Depositing a new validator changes no finite exit cohort. -/
theorem finality_applyDeposit_exitCohort {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {key : BLSPubkey} {credentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (ran : applyDeposit cfg checks s key credentials amount signature = .ok t)
    {epoch : Epoch} (finite : epoch ≠ FAR_FUTURE_EPOCH) :
    (t.validators.data.toList.filter (·.exitEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
  simp only [applyDeposit, show ¬Fork.pectra ≤ Fork.phase0 by decide, ↓reduceDIte,
    applyPendingDeposit] at ran
  split at ran
  · simp only [bind_ok_iff] at ran
    obtain ⟨_, _, ran⟩ := ran
    split at ran
    · simp only [addValidatorToRegistry, show ¬Fork.altair ≤ Fork.phase0 by decide,
        ↓reduceDIte] at ran
      split at ran
      · cases ran
        simp [Array.toList_push, getValidatorFromDeposit, Ne.symm finite]
      · cases ran
    · cases ran
      rfl
  · rw [increaseBalance_validators (liftAccessor_ok.mp ran)]

/-- A successful deposit cursor update preserves every finite exit cohort. -/
theorem finality_processDeposit_exitCohort {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {deposit : Deposit}
    (ran : processDeposit cfg checks (by decide) s deposit = .ok t)
    {epoch : Epoch} (finite : epoch ≠ FAR_FUTURE_EPOCH) :
    (t.validators.data.toList.filter (·.exitEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok ran
  exact finality_applyDeposit_exitCohort applied finite

/-- A proposer slashing respects the finite exit-cohort cap. -/
theorem finality_processProposerSlashing_cohort {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {a : ProposerSlashing} {cap : Nat}
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : max 1 (getValidatorChurnLimit cfg s).toNat ≤ cap)
    (ran : processProposerSlashing cfg checks s a = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at ran
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := ran
  exact finality_slashValidator_cohort bounded limit slashed

/-- Each attester-slashing index either preserves the state or allocates one exit. -/
theorem finality_slashIfSlashable_cohort {cfg : Config}
    {s t : FinalityState p × Bool} {i : ValidatorIndex} {cap : Nat}
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.1.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : max 1 (getValidatorChurnLimit cfg s.1).toNat ≤ cap)
    (ran : slashIfSlashable cfg s i = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.1.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  obtain ⟨s, flag⟩ := s
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ran
  obtain ⟨_, _, ran⟩ := ran
  split at ran
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ran
    obtain ⟨_, slashed, rfl⟩ := ran
    exact finality_slashValidator_cohort bounded limit slashed
  · cases ran
    exact bounded

/-- An attester slashing composes finite-cohort bounds over its actual index fold. -/
theorem finality_processAttesterSlashing_cohort {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {a : AttesterSlashing p .phase0} {cap : Nat}
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : processAttesterSlashing cfg checks s a = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := ran
  have kept := foldlM_ok_invariant
    (fun u : FinalityState p × Bool =>
      u.1.validators.data.size = s.validators.data.size ∧
      ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
        (u.1.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (fun _ _ _ prior ok =>
      ⟨((slashIfSlashable_ok ok).1.1).trans prior.1,
        finality_slashIfSlashable_cohort prior.2 (limit _ prior.1) ok⟩)
    ⟨rfl, bounded⟩ folded
  exact kept.2

/-- A voluntary exit respects the finite exit-cohort cap. -/
theorem finality_processVoluntaryExit_cohort {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {a : SignedVoluntaryExit} {cap : Nat}
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : max 1 (getValidatorChurnLimit cfg s).toNat ≤ cap)
    (ran : processVoluntaryExit cfg checks s a = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  simp only [processVoluntaryExit, show ¬Fork.pectra ≤ Fork.phase0 by decide,
    ↓reduceIte, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ran
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ran
  exact finality_initiateValidatorExit_cohort bounded limit exited

/-- An effective-balance write leaves every exit cohort unchanged. -/
theorem finality_updateEffectiveBalance_exitCohort {s t : FinalityState p} {i : Nat}
    (inside : i < s.validators.data.size)
    (ran : updateEffectiveBalance s i = .ok t) (epoch : Epoch) :
    (t.validators.data.toList.filter (·.exitEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
  have exactIndex := toNat_toUInt64_of_lt (s.validators.bound (by decide)) inside
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨v, read, _, _, balance, _, rfl⟩ := ran
  have found : s.validators.data[i]? = some v := by
    rw [← exactIndex]
    unfold getValidator at read
    split at read
    · cases read
      assumption
    · cases read
  exact finality_exitCohort_setValidator_eq found
    { v with effectiveBalance := balance } rfl epoch

/-- Effective-balance hysteresis preserves every exit cohort. -/
theorem finality_processEffectiveBalanceUpdates_exitCohort {s t : FinalityState p}
    (ran : processEffectiveBalanceUpdates s = .ok t) (epoch : Epoch) :
    (t.validators.data.toList.filter (·.exitEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
  simp only [processEffectiveBalanceUpdates, show ¬Fork.pectra ≤ Fork.phase0 by decide,
    ↓reduceIte] at ran
  have pass : ∀ (indices : List Nat) (a b : FinalityState p),
      (∀ i ∈ indices, i < a.validators.data.size) →
      indices.foldlM updateEffectiveBalance a = .ok b →
      (b.validators.data.toList.filter (·.exitEpoch == epoch)).length =
        (a.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
    intro indices
    induction indices with
    | nil => intro a b _ ok; cases ok; rfl
    | cons i rest ih =>
      intro a b inside ok
      obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ok
      have same := finality_updateEffectiveBalance_exitCohort (inside i List.mem_cons_self)
        first epoch
      have sizes := (sameSizes_updateEffectiveBalance first).1
      exact (ih middle b (fun j member => by
        rw [sizes]
        exact inside j (List.mem_cons_of_mem _ member)) tail).trans same
  exact pass _ s t (fun _ member => List.mem_range.mp member) ran

/-- Epoch processing preserves a uniform finite exit-cohort cap. -/
theorem finality_processEpoch_cohort {cfg : Config} {s t : FinalityState p} {cap : Nat}
    (inv : Invariant s)
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : processEpoch cfg s = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  simp only [processEpoch, show ¬Fork.altair ≤ Fork.phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at ran
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := ran
  have justifiedRegistry :=
    (processJustificationAndFinalization_invariant inv.ordered inv.settled justifiedOk).2.2.2.2.1
  have rewardedRegistry :=
    (processRewardsAndPenalties_validators rewardedOk).trans justifiedRegistry
  have registeredBound := finality_processRegistryUpdates_cohort
    (s := rewarded) (by simpa only [rewardedRegistry] using bounded)
    (fun u same => limit u (by simpa only [rewardedRegistry] using same)) registeredOk
  have clearedRegistry : cleared.validators = balanced.validators := by
    obtain ⟨_, _, rfl⟩ := processSlashingsReset_eq clearedOk
    rfl
  have mixedRegistry : mixed.validators = cleared.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    rfl
  intro epoch finite
  rw [processParticipationRecordUpdates_validators rotated,
    processHistoricalRootsUpdate_validators rootedOk, mixedRegistry, clearedRegistry,
    finality_processEffectiveBalanceUpdates_exitCohort balancedOk epoch,
    processEth1DataReset_validators resetOk, processSlashings_validators slashedOk]
  exact registeredBound epoch finite

/-- Attestation processing changes no exit cohort. -/
theorem finality_processAttestation_exitCohort {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {a : Attestation p .phase0}
    (ran : processAttestation cfg checks s a = .ok t) (epoch : Epoch) :
    (t.validators.data.toList.filter (·.exitEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
  obtain ⟨_, _, _, _, _, recorded, _, _, _⟩ := processAttestation_records (by decide) ran
  cases current : a.data.target.epoch == getCurrentEpoch s <;>
    simp only [recordPendingAttestation, current, Bool.false_eq_true, ↓reduceIte] at recorded <;>
    split at recorded <;> cases recorded <;> rfl

/-- Block operations preserve finite exit-cohort caps under a population envelope.

The same envelope covers intermediate deposits as well as each exit allocation. -/
theorem finality_processOperations_cohort {cfg : Config} {checks : SignatureChecks}
    {s t : FinalityState p} {body : BeaconBlockBody p .phase0} {population cap : Nat}
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (size : t.validators.data.size ≤ population)
    (limit : ∀ u : FinalityState p, u.validators.data.size ≤ population →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : processOperations cfg checks s body = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  unfold processOperations at ran
  split at ran
  · cases ran
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ran
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, attested, attestedOk,
    deposited, depositedOk, exited, exitsOk, changesOk⟩ := ran
  simp only [show ¬Fork.shapella ≤ Fork.phase0 by decide, ↓reduceDIte,
    pure, Except.pure, Except.ok.injEq] at changesOk
  subst t
  have oneSize := foldlM_ok_invariant (SameSizes s)
    (fun _ _ _ prior ok => prior.trans (sameSizes_processProposerSlashing ok))
    (SameSizes.refl s) proposersOk
  have twoSize := foldlM_ok_invariant (SameSizes proposers)
    (fun _ _ _ prior ok => prior.trans (sameSizes_processAttesterSlashing ok))
    (SameSizes.refl proposers) attestersOk
  have threeSize := foldlM_ok_invariant (SameSizes attesters)
    (fun _ _ _ prior ok => prior.trans (sameSizes_processAttestation ok))
    (SameSizes.refl attesters) attestedOk
  have fourSize := (FinalityRegistryExtends.foldlM
    (fun _ _ _ ok => finality_processDeposit_registry ok) depositedOk).1
  have fiveSize := foldlM_ok_invariant (SameSizes deposited)
    (fun _ _ _ prior ok => prior.trans (sameSizes_processVoluntaryExit ok))
    (SameSizes.refl deposited) exitsOk
  have depositedSize : deposited.validators.data.size ≤ population := by
    rwa [fiveSize.1] at size
  have startSize : s.validators.data.size ≤ population := by
    rw [threeSize.1, twoSize.1, oneSize.1] at fourSize
    exact Nat.le_trans fourSize depositedSize
  have one := foldlM_ok_invariant
    (fun u : FinalityState p => u.validators.data.size = s.validators.data.size ∧
      ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
        (u.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (fun _ _ _ prior ok => ⟨(sameSizes_processProposerSlashing ok).1.trans prior.1,
      finality_processProposerSlashing_cohort prior.2
        (limit _ (prior.1 ▸ startSize)) ok⟩) ⟨rfl, bounded⟩ proposersOk
  have two := foldlM_ok_invariant
    (fun u : FinalityState p => u.validators.data.size = s.validators.data.size ∧
      ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
        (u.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (fun _ _ _ prior ok => ⟨(sameSizes_processAttesterSlashing ok).1.trans prior.1,
      finality_processAttesterSlashing_cohort prior.2
        (fun u same => limit u ((same.trans prior.1) ▸ startSize)) ok⟩) one attestersOk
  have three := foldlM_ok_invariant
    (fun u : FinalityState p => ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (u.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (fun _ _ _ prior ok epoch finite => by
      rw [finality_processAttestation_exitCohort ok epoch]
      exact prior epoch finite) two.2 attestedOk
  have four := foldlM_ok_invariant
    (fun u : FinalityState p => ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (u.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (fun _ _ _ prior ok epoch finite => by
      rw [finality_processDeposit_exitCohort ok finite]
      exact prior epoch finite) three depositedOk
  have five := foldlM_ok_invariant
    (fun u : FinalityState p => u.validators.data.size = deposited.validators.data.size ∧
      ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
        (u.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (fun _ _ _ prior ok => ⟨(sameSizes_processVoluntaryExit ok).1.trans prior.1,
      finality_processVoluntaryExit_cohort prior.2
        (limit _ (prior.1 ▸ depositedSize)) ok⟩)
    ⟨rfl, four⟩ exitsOk
  exact five.2

/-- A block preserves finite exit-cohort caps under a population envelope. -/
theorem finality_processBlock_cohort {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {b : BeaconBlock p .phase0}
    {population cap : Nat}
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (size : t.validators.data.size ≤ population)
    (limit : ∀ u : FinalityState p, u.validators.data.size ≤ population →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : processBlock cfg checks eng s b = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  simp only [processBlock, show ¬Fork.altair ≤ Fork.phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at ran
  obtain ⟨header, headerOk, randao, randaoOk, eth1, eth1Ok, operationsOk⟩ := ran
  have headerRegistry : header.validators = s.validators := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    rfl
  have randaoRegistry : randao.validators = header.validators := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
    rfl
  have eth1Registry : eth1.validators = randao.validators :=
    congrArg (fun u => u.validators) (processEth1Data_eq eth1Ok).2.2
  exact finality_processOperations_cohort
    (by simpa only [eth1Registry, randaoRegistry, headerRegistry] using bounded)
    size limit operationsOk

/-- One slot preserves finite exit-cohort caps under a fixed population envelope. -/
theorem finality_advanceSlot_cohort {cfg : Config} {s t : FinalityState p} {cap : Nat}
    (inv : Invariant s)
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : advanceSlot cfg s = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ran
  obtain ⟨_, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := ran
  have cacheRegistry : cached.validators = s.validators := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  change ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
    (epoched.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap
  unfold epochIfLast at epochedOk
  split at epochedOk
  · exact finality_processEpoch_cohort ((frame_processSlot cachedOk).invariant inv)
      (by simpa only [cacheRegistry] using bounded)
      (fun u same => limit u (by simpa only [cacheRegistry] using same)) epochedOk
  · cases epochedOk
    simpa only [cacheRegistry] using bounded

/-- An empty-slot prefix preserves finite exit-cohort caps. -/
theorem finality_advanceSlots_cohort {cfg : Config} {s t : FinalityState p}
    {count cap : Nat} (inv : Invariant s)
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (limit : ∀ u : FinalityState p, u.validators.data.size = s.validators.data.size →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : advanceSlots cfg count s = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  induction count generalizing s with
  | zero => cases ran; exact bounded
  | succ count ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    exact ih (advanceSlot_invariant (by decide) inv first).1
      (finality_advanceSlot_cohort inv bounded limit first)
      (fun u same => limit u (same.trans (finality_advanceSlot_size first))) tail

/-- A validated block transition preserves finite exit-cohort caps. -/
theorem finality_stateTransition_cohort {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {b : FinalityBlock p}
    {population cap : Nat} (inv : Invariant s)
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (size : t.validators.data.size ≤ population)
    (limit : ∀ u : FinalityState p, u.validators.data.size ≤ population →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : stateTransition cfg checks eng s b true = .ok t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  have startSize := Nat.le_trans (finality_stateTransition_registry inv ran).1 size
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok ran
  have slots := slotsOk
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slots
  obtain ⟨_, _, advancedOk⟩ := slots
  have advancedBound := finality_advanceSlots_cohort inv bounded
    (fun u same => limit u (same ▸ startSize)) advancedOk
  exact finality_processBlock_cohort advancedBound size limit blockOk

/-- A validated chain preserves finite exit-cohort caps under its final population bound. -/
theorem finality_runs_cohort {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {bs : List (FinalityBlock p)}
    {population cap : Nat} (inv : Invariant s)
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (size : t.validators.data.size ≤ population)
    (limit : ∀ u : FinalityState p, u.validators.data.size ≤ population →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (ran : finalityRuns cfg checks eng s bs t) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  induction bs generalizing s with
  | nil => cases ran; exact bounded
  | cons b bs ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    have middleInv := finality_runs_invariant inv (bs := [b])
      (by simpa [finalityRuns] using first)
    have middleSize := Nat.le_trans (finality_runs_registry middleInv tail).1 size
    exact ih middleInv (finality_stateTransition_cohort inv bounded middleSize limit first)
      tail

/-- Genesis effective-balance and activation writes preserve every exit cohort. -/
theorem finality_activateAtGenesis_exitCohort {s t : FinalityState p} {i : Nat}
    (ran : activateAtGenesis s i = .ok t) (epoch : Epoch) :
    (t.validators.data.toList.filter (·.exitEpoch == epoch)).length =
      (s.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
  simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨v, read, _, _, rfl⟩ := ran
  have found : s.validators.data[i.toUInt64.toNat]? = some v := by
    unfold getValidator at read
    split at read
    · cases read
      assumption
    · cases read
  by_cases inside : i < s.validators.data.size
  · rw [toNat_toUInt64_of_lt (s.validators.bound (by decide)) inside] at found
    split <;> apply finality_exitCohort_setValidator_eq found <;> rfl
  · simp only [BeaconState.setValidator, Array.toList_set!]
    rw [List.set_eq_of_length_le (by simpa using Nat.le_of_not_gt inside)]

/-- A successfully initialized Phase 0 state has no finite exit cohorts.

Deposits create far-future exits, and genesis activation leaves them unchanged. -/
theorem finality_initialized_exitCohort {cfg : Config} {checks : SignatureChecks}
    {g : FinalityState p} (initialized : finalityInitialized cfg checks g)
    {epoch : Epoch} (finite : epoch ≠ FAR_FUTURE_EPOCH) :
    (g.validators.data.toList.filter (·.exitEpoch == epoch)).length = 0 := by
  obtain ⟨⟨hash, time, deposits, ran⟩, _⟩ := initialized
  simp only [initializeBeaconStateFromEth1, show ¬Fork.altair ≤ Fork.phase0 by decide,
    ↓reduceDIte, bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, _, _, rfl⟩ := ran
  have initial : ∀ (a b : FinalityState p) entry,
      genesisDeposit cfg checks (by decide) (deposits.map (·.data)) a entry = .ok b →
      (b.validators.data.toList.filter (·.exitEpoch == epoch)).length =
        (a.validators.data.toList.filter (·.exitEpoch == epoch)).length := by
    intro a b entry ok
    simp only [genesisDeposit, bind_ok_iff] at ok
    obtain ⟨_, _, applied⟩ := ok
    exact finality_processDeposit_exitCohort applied finite
  have depositedZero := foldlM_ok_invariant
    (fun u : FinalityState p => (u.validators.data.toList.filter (·.exitEpoch == epoch)).length = 0)
    (fun _ _ _ previous ok => (initial _ _ _ ok).trans previous)
    (by simp [emptyGenesisState]) depositedOk
  change (activated.validators.data.toList.filter (·.exitEpoch == epoch)).length = 0
  exact foldlM_ok_invariant
    (fun u : FinalityState p => (u.validators.data.toList.filter (·.exitEpoch == epoch)).length = 0)
    (fun _ _ _ previous ok => (finality_activateAtGenesis_exitCohort ok epoch).trans previous)
    depositedZero activatedOk

/-- Every finite exit cohort of a reachable state fits its population-based churn cap.

Registry growth is monotone, so the final population bounds every earlier allocation. -/
theorem finality_reachable_exitCohort {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {g t : FinalityState p}
    {bs : List (FinalityBlock p)} {population : Nat}
    (initialized : finalityInitialized cfg checks g)
    (ran : finalityRuns cfg checks eng g bs t)
    (size : t.validators.data.size ≤ population) :
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤
        max 1 (max cfg.MIN_PER_EPOCH_CHURN_LIMIT.toNat
          (population / cfg.CHURN_LIMIT_QUOTIENT.toNat)) := by
  obtain ⟨_, _, _, genesis⟩ := initialized.1
  have inv := (initializeBeaconStateFromEth1_invariant genesis).2
  apply finality_runs_cohort inv ?_ size ?_ ran
  · intro epoch finite
    rw [finality_initialized_exitCohort initialized finite]
    exact Nat.zero_le _
  · intro u envelope
    apply Nat.max_le.mpr
    exact ⟨Nat.le_max_left _ _, Nat.le_trans
      (finality_churnLimit_le (u.validators.bound (by decide)) envelope)
      (Nat.le_max_right _ _)⟩

/-- A validator active in the previous epoch but not now exits in the current epoch. -/
theorem finality_previousGap_exitEpoch {s : FinalityState p} {v : Validator}
    (previous : isActiveValidator v (getPreviousEpoch s) = true)
    (absent : isActiveValidator v (getCurrentEpoch s) = false) :
    v.exitEpoch = getCurrentEpoch s := by
  have previousNat := getPreviousEpoch_toNat s
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at previous
  have activation := UInt64.le_iff_toNat_le.mp previous.1
  have exit := UInt64.lt_iff_toNat_lt.mp previous.2
  have notActive : ¬(v.activationEpoch ≤ getCurrentEpoch s ∧
      getCurrentEpoch s < v.exitEpoch) := by
    intro both
    have yes : isActiveValidator v (getCurrentEpoch s) = true := by
      simp [isActiveValidator, both.1, both.2]
    rw [absent] at yes
    contradiction
  have before : v.activationEpoch ≤ getCurrentEpoch s := by
    apply UInt64.le_iff_toNat_le.mpr
    omega
  have after : v.exitEpoch ≤ getCurrentEpoch s := by
    apply UInt64.le_iff_toNat_le.mpr
    by_contra h
    have later : getCurrentEpoch s < v.exitEpoch := UInt64.lt_iff_toNat_lt.mpr (by omega)
    exact notActive ⟨before, later⟩
  apply UInt64.toNat_inj.mp
  have afterNat := UInt64.le_iff_toNat_le.mp after
  omega

/-- Previous-only weight is bounded by the size of the current exit cohort times the cap. -/
theorem finality_previousGap_weight {s : FinalityState p}
    (inv : Invariant s) :
    (s.validators.data.toList.map fun v =>
      if isActiveValidator v (getPreviousEpoch s) && !isActiveValidator v (getCurrentEpoch s)
      then v.effectiveBalance.toNat else 0).sum ≤
    (s.validators.data.toList.filter (·.exitEpoch == getCurrentEpoch s)).length *
      p.MAX_EFFECTIVE_BALANCE.toNat := by
  have sumBound : ∀ vs : List Validator,
      (∀ v ∈ vs, v.effectiveBalance ≤ p.MAX_EFFECTIVE_BALANCE) →
      (vs.map fun v =>
        if isActiveValidator v (getPreviousEpoch s) && !isActiveValidator v (getCurrentEpoch s)
        then v.effectiveBalance.toNat else 0).sum ≤
      (vs.filter (·.exitEpoch == getCurrentEpoch s)).length * p.MAX_EFFECTIVE_BALANCE.toNat := by
    intro vs
    induction vs with
    | nil => simp
    | cons v vs ih =>
      intro bound
      have tail := ih (fun w member => bound w (List.mem_cons_of_mem _ member))
      have weight := UInt64.le_iff_toNat_le.mp (bound v List.mem_cons_self)
      simp only [List.map_cons, List.sum_cons, List.filter_cons]
      by_cases active : (isActiveValidator v (getPreviousEpoch s) &&
          !isActiveValidator v (getCurrentEpoch s)) = true
      · have flags : isActiveValidator v (getPreviousEpoch s) = true ∧
            isActiveValidator v (getCurrentEpoch s) = false := by
          simpa using active
        have exits := finality_previousGap_exitEpoch flags.1 flags.2
        rw [ite_eq_left active]
        simp only [exits, beq_self_eq_true, ↓reduceIte, List.length_cons, Nat.add_mul,
          Nat.one_mul]
        omega
      · rw [ite_eq_right active]
        split
        · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
          omega
        · omega
  exact sumBound _ (fun v member => inv.effectiveBalancesBounded v (by simpa using member))

/-- The previous-only weight of a reachable state is bounded by one exit cohort.

The current epoch is explicitly finite because far-future exits are not scheduled cohorts. -/
theorem finality_reachable_previousGap {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {g t : FinalityState p}
    {bs : List (FinalityBlock p)} {population : Nat}
    (initialized : finalityInitialized cfg checks g)
    (ran : finalityRuns cfg checks eng g bs t)
    (size : t.validators.data.size ≤ population)
    (finite : getCurrentEpoch t ≠ FAR_FUTURE_EPOCH) :
    (t.validators.data.toList.map fun v =>
      if isActiveValidator v (getPreviousEpoch t) && !isActiveValidator v (getCurrentEpoch t)
      then v.effectiveBalance.toNat else 0).sum ≤
      max 1 (max cfg.MIN_PER_EPOCH_CHURN_LIMIT.toNat
        (population / cfg.CHURN_LIMIT_QUOTIENT.toNat)) * p.MAX_EFFECTIVE_BALANCE.toNat := by
  obtain ⟨_, _, _, genesis⟩ := initialized.1
  have inv := finality_runs_invariant (initializeBeaconStateFromEth1_invariant genesis).2 ran
  exact Nat.le_trans (finality_previousGap_weight inv)
    (Nat.mul_le_mul_right _ (finality_reachable_exitCohort initialized ran size _ finite))

/-- Every collected observation preserves a finite exit-cohort cap.

Successful prefix witnesses suffice even if a later continuation fails. -/
theorem finality_observations_cohort {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t : FinalityState p} {bs : List (FinalityBlock p)}
    {population cap : Nat} (inv : Invariant c)
    (bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (c.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap)
    (size : t.validators.data.size ≤ population)
    (limit : ∀ u : FinalityState p, u.validators.data.size ≤ population →
      max 1 (getValidatorChurnLimit cfg u).toNat ≤ cap)
    (member : t ∈ finalityObservations cfg checks eng c bs) :
    Invariant t ∧ ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap := by
  simp only [finalityObservations, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨⟨b, i⟩, _, member⟩
  · exact ⟨inv, bounded⟩
  cases prefixOk : (bs.take i).foldlM (fun s b => stateTransition cfg checks eng s b true) c with
  | error e => simp [prefixOk] at member
  | ok before =>
    simp only [prefixOk, List.mem_append, List.mem_cons, List.mem_flatMap] at member
    have holds := finality_runs_invariant inv prefixOk
    rcases member with output | rfl | ⟨n, _, member⟩
    · cases block : stateTransition cfg checks eng before b true with
      | error e => simp [block, Except.toOption] at output
      | ok after =>
        simp only [block, Except.toOption, Option.toList, List.mem_singleton] at output
        subst t
        have beforeSize := Nat.le_trans (finality_stateTransition_registry holds block).1 size
        exact ⟨(stateTransition_invariant (by decide) holds block).1,
          finality_stateTransition_cohort holds
            (finality_runs_cohort inv bounded beforeSize limit prefixOk) size limit block⟩
    · exact ⟨holds, finality_runs_cohort inv bounded size limit prefixOk⟩
    · cases slots : advanceSlots cfg n before with
      | error e => simp [slots] at member
      | ok atStep =>
        simp only [slots, List.mem_cons] at member
        have stepInv := (advanceSlots_invariant (by decide) holds slots).1
        have sizes := finality_advanceSlots_size slots
        rcases member with rfl | member
        · have beforeSize : before.validators.data.size ≤ population := by rwa [sizes] at size
          exact ⟨stepInv, finality_advanceSlots_cohort holds
            (finality_runs_cohort inv bounded beforeSize limit prefixOk)
            (fun u same => limit u (same ▸ beforeSize)) slots⟩
        · cases cache : processSlot atStep with
          | error e => simp [cache, Except.toOption] at member
          | ok cached =>
            simp only [cache, Except.toOption, Option.toList, List.mem_singleton] at member
            subst t
            obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
            have beforeSize : before.validators.data.size ≤ population := by
              change atStep.validators.data.size ≤ population at size
              rwa [sizes] at size
            refine ⟨(frame_processSlot cache).invariant stepInv, ?_⟩
            change ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
              (atStep.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤ cap
            exact finality_advanceSlots_cohort holds
              (finality_runs_cohort inv bounded beforeSize limit prefixOk)
              (fun u same => limit u (same ▸ beforeSize)) slots

/-- A collected registry has at most one deposit allowance per listed block.

Every successful prefix has no more blocks than the supplied list. -/
theorem finality_observations_size {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t : FinalityState p} {bs : List (FinalityBlock p)}
    (member : t ∈ finalityObservations cfg checks eng c bs) :
    t.validators.data.size ≤ c.validators.data.size + bs.length * p.MAX_DEPOSITS.toNat := by
  simp only [finalityObservations, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨⟨b, i⟩, listed, member⟩
  · omega
  have index := List.mk_mem_zipIdx_iff_getElem?.mp listed
  have inside := (List.getElem?_eq_some_iff.mp index).1
  cases prefixOk : (bs.take i).foldlM (fun s b => stateTransition cfg checks eng s b true) c with
  | error e => simp [prefixOk] at member
  | ok before =>
    simp only [prefixOk, List.mem_append, List.mem_cons, List.mem_flatMap] at member
    have prefixSize := finality_runs_size prefixOk
    have prefixLength : (bs.take i).length = i := List.length_take_of_le (by omega)
    rw [prefixLength] at prefixSize
    have allowances := Nat.mul_le_mul_right p.MAX_DEPOSITS.toNat
      (show i + 1 ≤ bs.length by omega)
    rw [Nat.add_mul, Nat.one_mul] at allowances
    rcases member with output | rfl | ⟨n, _, member⟩
    · cases block : stateTransition cfg checks eng before b true with
      | error e => simp [block, Except.toOption] at output
      | ok after =>
        simp only [block, Except.toOption, Option.toList, List.mem_singleton] at output
        subst t
        have added := finality_stateTransition_size block
        omega
    · omega
    · cases slots : advanceSlots cfg n before with
      | error e => simp [slots] at member
      | ok atStep =>
        simp only [slots, List.mem_cons] at member
        have sizes := finality_advanceSlots_size slots
        rcases member with rfl | member
        · omega
        · cases cache : processSlot atStep with
          | error e => simp [cache, Except.toOption] at member
          | ok cached =>
            simp only [cache, Except.toOption, Option.toList, List.mem_singleton] at member
            subst t
            obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cache
            change atStep.validators.data.size ≤ _
            omega

/-- The positive-slots horizon envelope covers every collected observation. -/
theorem finality_observations_size_horizon {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t after : FinalityState p}
    {bs : List (FinalityBlock p)} {n : Nat}
    (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (ran : finalityRuns cfg checks eng c bs after)
    (horizon : (getCurrentEpoch after).toNat - (getCurrentEpoch c).toNat ≤ n)
    (member : t ∈ finalityObservations cfg checks eng c bs) :
    t.validators.data.size ≤ c.validators.data.size +
      (n + 1) * p.SLOTS_PER_EPOCH.toNat * p.MAX_DEPOSITS.toNat := by
  have size := finality_observations_size member
  have count := finality_runs_length ran
  have elapsed := finality_slot_horizon positive horizon
  have blocks : bs.length ≤ (n + 1) * p.SLOTS_PER_EPOCH.toNat := by omega
  have scaled := Nat.mul_le_mul_right p.MAX_DEPOSITS.toNat blocks
  omega

/-- Every observed finite exit cohort fits the horizon cap derived from C. -/
theorem finality_observations_exitCohort {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {g c t after : FinalityState p}
    {common bs : List (FinalityBlock p)} {n : Nat}
    (initialized : finalityInitialized cfg checks g)
    (shared : finalityRuns cfg checks eng g common c)
    (ran : finalityRuns cfg checks eng c bs after)
    (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (horizon : (getCurrentEpoch after).toNat - (getCurrentEpoch c).toNat ≤ n)
    (member : t ∈ finalityObservations cfg checks eng c bs) :
    Invariant t ∧ ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      (t.validators.data.toList.filter (·.exitEpoch == epoch)).length ≤
        finalityChurnCap cfg c n := by
  let population := c.validators.data.size +
    (n + 1) * p.SLOTS_PER_EPOCH.toNat * p.MAX_DEPOSITS.toNat
  have referenceSize : c.validators.data.size ≤ population := Nat.le_add_right _ _
  obtain ⟨_, _, _, genesis⟩ := initialized.1
  have inv := finality_runs_invariant (initializeBeaconStateFromEth1_invariant genesis).2 shared
  exact finality_observations_cohort inv
    (finality_reachable_exitCohort initialized shared referenceSize)
    (finality_observations_size_horizon positive ran horizon member)
    (fun u size => Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      Nat.le_trans (finality_churnLimit_le (u.validators.bound (by decide)) size)
        (Nat.le_max_right _ _)⟩) member

/-- A bound on every observation bounds its maximum, including an empty history. -/
theorem finalityMaxOn_le {ss : List (FinalityState p)} {f : FinalityState p → Nat}
    {cap : Nat} (bounded : ∀ s ∈ ss, f s ≤ cap) : finalityMaxOn ss f ≤ cap := by
  unfold finalityMaxOn
  have fold : ∀ (xs : List Nat) (start : Nat), start ≤ cap →
      (∀ x ∈ xs, x ≤ cap) → xs.foldl max start ≤ cap := by
    intro xs
    induction xs with
    | nil => intro start initial _; exact initial
    | cons x xs ih =>
      intro start initial within
      exact ih (max start x) (Nat.max_le.mpr ⟨initial, within x List.mem_cons_self⟩)
        (fun y member => within y (List.mem_cons_of_mem _ member))
  apply fold _ _ (Nat.zero_le _)
  intro value member
  obtain ⟨s, inside, rfl⟩ := List.mem_map.mp member
  exact bounded s inside

/-- The observed previous-only weight fits one horizon cohort when current epochs are finite.

Finiteness remains an explicit helper premise, not a premise of realized churn. -/
theorem finality_previousGap_le_of_finite {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {g c after : FinalityState p}
    {common bs : List (FinalityBlock p)} {n : Nat}
    (initialized : finalityInitialized cfg checks g)
    (shared : finalityRuns cfg checks eng g common c)
    (ran : finalityRuns cfg checks eng c bs after)
    (positive : 0 < p.SLOTS_PER_EPOCH.toNat)
    (horizon : (getCurrentEpoch after).toNat - (getCurrentEpoch c).toNat ≤ n)
    (finite : ∀ t ∈ finalityObservations cfg checks eng c bs,
      getCurrentEpoch t ≠ FAR_FUTURE_EPOCH) :
    finalityPreviousGap (finalityObservations cfg checks eng c bs) ≤
      finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat := by
  apply finalityMaxOn_le
  intro t member
  have observed := finality_observations_exitCohort initialized shared ran positive horizon member
  exact Nat.le_trans (finality_previousGap_weight observed.1)
    (Nat.mul_le_mul_right _ (observed.2 _ (finite t member)))

/-- A successful Phase 0 block needs a proposer active at a finite epoch. -/
theorem finality_processBlock_epoch_finite {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {b : BeaconBlock p .phase0}
    (ran : processBlock cfg checks eng s b = .ok t) :
    getCurrentEpoch t ≠ FAR_FUTURE_EPOCH := by
  have slot := (frame_processBlock (by decide) ran).slot
  have sameEpoch : getCurrentEpoch t = getCurrentEpoch s := by
    simp only [getCurrentEpoch, slot]
  simp only [processBlock, show ¬Fork.altair ≤ Fork.phase0 by decide, ↓reduceDIte,
    bind_ok_iff] at ran
  obtain ⟨_, headerOk, _, _, _, _, _⟩ := ran
  have proposer := (processBlockHeader_checks headerOk).2.2.1
  have active := mem_getActiveValidatorIndices_of_getBeaconProposerIndex (by decide) proposer
  obtain ⟨v, _, active⟩ :=
    (mem_getActiveValidatorIndices (s.validators.bound (by decide))).mp active
  intro far
  rw [sameEpoch] at far
  simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at active
  have exit := UInt64.lt_iff_toNat_lt.mp active.2
  rw [far] at exit
  have top := v.exitEpoch.toNat_lt
  change 18446744073709551615 < v.exitEpoch.toNat at exit
  omega

/-- A successful nonempty chain ends at a finite epoch. -/
theorem finality_runs_epoch_finite {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {s t : FinalityState p} {bs : List (FinalityBlock p)}
    (initial : getCurrentEpoch s ≠ FAR_FUTURE_EPOCH)
    (ran : finalityRuns cfg checks eng s bs t) : getCurrentEpoch t ≠ FAR_FUTURE_EPOCH := by
  induction bs generalizing s with
  | nil => cases ran; exact initial
  | cons b bs ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨_, _, _, _, processed, _⟩ := stateTransition_ok first
    exact ih (finality_processBlock_epoch_finite processed) tail

/-- Initialization fixes the slot at genesis, hence the current epoch at zero. -/
theorem finality_initialized_epoch {cfg : Config} {checks : SignatureChecks}
    {g : FinalityState p} (initialized : finalityInitialized cfg checks g) :
    getCurrentEpoch g = 0 := by
  obtain ⟨⟨_, _, deposits, ran⟩, _⟩ := initialized
  simp only [initializeBeaconStateFromEth1, show ¬Fork.altair ≤ Fork.phase0 by decide,
    ↓reduceDIte, bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at ran
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, _, _, rfl⟩ := ran
  have frame := (Frame.foldlM
    (fun _ _ _ ok => frame_genesisDeposit (by decide : Fork.phase0 < .altair) ok)
    depositedOk).trans (Frame.foldlM (fun _ _ _ ok => frame_activateAtGenesis ok) activatedOk)
  apply UInt64.toNat_inj.mp
  rw [getCurrentEpoch_toNat]
  change activated.slot.toNat / p.SLOTS_PER_EPOCH.toNat = 0
  rw [frame.slot]
  simp [emptyGenesisState, GENESIS_SLOT]

/-- A successful full run bounds every collected observation's slot by its final slot. -/
theorem finality_observations_slot_le {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t after : FinalityState p}
    {bs : List (FinalityBlock p)}
    (ran : finalityRuns cfg checks eng c bs after)
    (member : t ∈ finalityObservations cfg checks eng c bs) :
    t.slot.toNat ≤ after.slot.toNat := by
  simp only [finalityObservations, List.mem_cons, List.mem_flatMap] at member
  rcases member with rfl | ⟨⟨b, i⟩, listed, member⟩
  · exact stateTransition_chain_slot_le (by decide) ran
  have index := List.mk_mem_zipIdx_iff_getElem?.mp listed
  obtain ⟨inside, equal⟩ := List.getElem?_eq_some_iff.mp index
  have split : bs = bs.take i ++ b :: bs.drop (i + 1) := by
    rw [← equal, ← List.drop_eq_getElem_cons inside, List.take_append_drop]
  cases prefixOk : (bs.take i).foldlM (fun s b => stateTransition cfg checks eng s b true) c with
  | error e => simp [prefixOk] at member
  | ok before =>
    have remaining := ran
    unfold finalityRuns at remaining
    rw [split, List.foldlM_append, prefixOk] at remaining
    change (b :: bs.drop (i + 1)).foldlM
      (fun s b => stateTransition cfg checks eng s b true) before = .ok after at remaining
    obtain ⟨middle, blockOk, tailOk⟩ := bind_ok_iff.mp remaining
    have endSlot := stateTransition_chain_slot_le (by decide) tailOk
    obtain ⟨advanced, slotsOk, advancedSlot, _, processed, _⟩ := stateTransition_ok blockOk
    have middleSlot := (frame_processBlock (by decide) processed).slot.trans advancedSlot
    have beforeSlot := UInt64.lt_iff_toNat_lt.mp (processSlots_slot slotsOk).1
    have middleNat := congrArg UInt64.toNat middleSlot
    simp only [prefixOk, List.mem_append, List.mem_cons, List.mem_flatMap] at member
    rcases member with output | rfl | ⟨n, count, member⟩
    · simp only [blockOk, Except.toOption, Option.toList, List.mem_singleton] at output
      subst t
      exact endSlot
    · omega
    · have within := List.mem_range.mp count
      cases slots : advanceSlots cfg n before with
      | error e => simp [slots] at member
      | ok atStep =>
        have stepSlot := advanceSlots_slot n slots
        simp only [slots, List.mem_cons] at member
        rcases member with rfl | member
        · omega
        · cases cache : processSlot atStep with
          | error e => simp [cache, Except.toOption] at member
          | ok cached =>
            simp only [cache, Except.toOption, Option.toList, List.mem_singleton] at member
            subst t
            have cachedSlot := (frame_processSlot cache).slot
            rw [cachedSlot]
            omega

/-- All observations of a successful initialized chain have finite current epochs. -/
theorem finality_observations_epoch_finite {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {g c t after : FinalityState p}
    {common bs : List (FinalityBlock p)}
    (initialized : finalityInitialized cfg checks g)
    (shared : finalityRuns cfg checks eng g common c)
    (ran : finalityRuns cfg checks eng c bs after)
    (member : t ∈ finalityObservations cfg checks eng c bs) :
    getCurrentEpoch t ≠ FAR_FUTURE_EPOCH := by
  have genesisFinite : getCurrentEpoch g ≠ FAR_FUTURE_EPOCH := by
    rw [finality_initialized_epoch initialized]
    decide
  have endFinite := finality_runs_epoch_finite (finality_runs_epoch_finite genesisFinite shared) ran
  have epochs := Nat.div_le_div_right (c := p.SLOTS_PER_EPOCH.toNat)
    (finality_observations_slot_le ran member)
  rw [← getCurrentEpoch_toNat, ← getCurrentEpoch_toNat] at epochs
  intro far
  rw [far] at epochs
  have top := (getCurrentEpoch after).toNat_lt
  have same : getCurrentEpoch after = FAR_FUTURE_EPOCH := UInt64.toNat_inj.mp (by
    change (getCurrentEpoch after).toNat = 18446744073709551615
    change 18446744073709551615 ≤ (getCurrentEpoch after).toNat at epochs
    omega)
  exact endFinite same

/-- A zero slot divisor makes both the current and previous epoch zero. -/
theorem finality_epochs_zero {s : FinalityState p} (zero : p.SLOTS_PER_EPOCH = 0) :
    getCurrentEpoch s = 0 ∧ getPreviousEpoch s = 0 := by
  have current : getCurrentEpoch s = 0 := by
    apply UInt64.toNat_inj.mp
    simp only [getCurrentEpoch_toNat, zero, UInt64.toNat_zero, Nat.div_zero]
  refine ⟨current, ?_⟩
  simp only [getPreviousEpoch, current, Uint64.saturatingSub]
  rfl

/-- Zero epoch length cannot change an observed active population.

This uses preservation of already reached committees rather than a slot-count envelope. -/
theorem finality_zero_slots_active {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c t : FinalityState p} {bs : List (FinalityBlock p)}
    (zero : p.SLOTS_PER_EPOCH = 0) (inv : Invariant c)
    (member : t ∈ finalityObservations cfg checks eng c bs) (i : Nat) :
    finalityActive t i = finalityActive c i := by
  have kept := finality_observations_active_indices inv (UInt64.le_refl _) member
  have sameEpoch : getCurrentEpoch t = getCurrentEpoch c :=
    (finality_epochs_zero zero).1.trans (finality_epochs_zero zero).1.symm
  apply finalityActive_eq_of_indices
  rwa [sameEpoch]

/-- Maximum over observations vanishes when every observed value vanishes. -/
theorem finalityMaxOn_zero {ss : List (FinalityState p)} {f : FinalityState p → Nat}
    (zero : ∀ s ∈ ss, f s = 0) : finalityMaxOn ss f = 0 := by
  unfold finalityMaxOn
  have mapped : ss.map f = List.replicate ss.length 0 := by
    induction ss with
    | nil => rfl
    | cons s ss ih =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ,
        zero s List.mem_cons_self, ih (fun t ht => zero t (List.mem_cons_of_mem _ ht))]
  rw [mapped]
  have fold : ∀ n : Nat, (List.replicate n 0).foldl max 0 = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simpa only [List.replicate_succ, List.foldl_cons, Nat.max_self] using ih
  exact fold _

/-- All three realized-churn charges vanish for zero slots per epoch. -/
theorem finality_realized_churn_zero_slots {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {c : FinalityState p} {bs : List (FinalityBlock p)}
    (zero : p.SLOTS_PER_EPOCH = 0) (inv : Invariant c) :
    let ss := finalityObservations cfg checks eng c bs
    finalityAdditions c ss = 0 ∧ finalityExits c ss = 0 ∧ finalityPreviousGap ss = 0 := by
  dsimp only
  have active : ∀ s ∈ finalityObservations cfg checks eng c bs, ∀ i,
      finalityActive s i = finalityActive c i :=
    fun _ member i => finality_zero_slots_active zero inv member i
  refine ⟨?_, ?_, ?_⟩
  · apply finalityMaxOn_zero
    intro s member
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro value inMap
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp inMap
    rw [active s member i]
    cases finalityActive c i <;> rfl
  · unfold finalityExits
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro value inMap
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp inMap
    have none : (finalityObservations cfg checks eng c bs).any
        (fun s => !(finalityActive s i)) = !(finalityActive c i) := by
      cases h : finalityActive c i
      · apply List.any_eq_true.mpr
        exact ⟨c, List.mem_cons_self, by simp [h]⟩
      · apply Bool.eq_false_iff.mpr
        intro yes
        obtain ⟨s, member, bad⟩ := List.any_eq_true.mp yes
        simp only [active s member i, h, Bool.not_true, Bool.false_eq_true] at bad
    rw [none]
    cases finalityActive c i <;> rfl
  · apply finalityMaxOn_zero
    intro s _
    apply List.sum_eq_zero_iff_forall_eq_nat.mpr
    intro value inMap
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp inMap
    rw [(finality_epochs_zero zero).1, (finality_epochs_zero zero).2]
    cases isActiveValidator v 0 <;> rfl

/-- The previous-epoch denominator gap fits one realized exit cohort.

This includes zero slots per epoch and needs no extra preset hypothesis. -/
theorem finality_previousGap_le {cfg : Config} {checks : SignatureChecks}
    {eng : ExecutionEngine p .phase0} {g c after : FinalityState p}
    {common bs : List (FinalityBlock p)} {n : Nat}
    (initialized : finalityInitialized cfg checks g)
    (shared : finalityRuns cfg checks eng g common c)
    (ran : finalityRuns cfg checks eng c bs after)
    (horizon : (getCurrentEpoch after).toNat - (getCurrentEpoch c).toNat ≤ n) :
    finalityPreviousGap (finalityObservations cfg checks eng c bs) ≤
      finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat := by
  by_cases zero : p.SLOTS_PER_EPOCH = 0
  · obtain ⟨_, _, _, genesis⟩ := initialized.1
    have inv := finality_runs_invariant (initializeBeaconStateFromEth1_invariant genesis).2 shared
    rw [(finality_realized_churn_zero_slots zero inv).2.2]
    exact Nat.zero_le _
  · have positive : 0 < p.SLOTS_PER_EPOCH.toNat := by
      have nonzero : p.SLOTS_PER_EPOCH.toNat ≠ 0 := by
        intro h
        exact zero (UInt64.toNat_inj.mp (by simpa using h))
      omega
    exact finality_previousGap_le_of_finite initialized shared ran positive horizon
      (fun _ member => finality_observations_epoch_finite initialized shared ran member)

end EthLib.Consensus
