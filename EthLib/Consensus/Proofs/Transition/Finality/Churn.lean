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

end EthLib.Consensus
