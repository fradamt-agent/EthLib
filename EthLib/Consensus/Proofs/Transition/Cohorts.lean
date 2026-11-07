module

public import EthLib.Consensus.Proofs.Transition.Lifecycle

/-!
# Proofs: activation and exit cohorts before Electra

Before Electra, the churn limit counts validators.

It caps how many validators may exit, and how many may be activated, in one epoch.

The exit queue gives each new exit the latest exit epoch, or the next one if that epoch is full.

The registry updates of an epoch activate the first validators of the queue, at most the limit.

They all get one activation epoch, some epochs after the current one.

Both bounds hold in every state that a chain reaches before Electra.

- An exit cohort, the validators that exit at one epoch, has at most `max 1 cap` validators.
- An activation cohort has at most `cap` validators, except at the genesis epoch.

Here `cap` is the churn limit of a registry with as many active validators as the whole registry.

It only grows along a chain, since the registry never shrinks.

The activation epochs of the cohorts also stay below the next activation epoch.

So each pass of the registry updates starts an empty cohort.

From Electra the churn counts balance instead, and the bounds here say nothing.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-! ## Cohorts and the cap -/

/-- The number of validators of a state that exit at an epoch. -/
def exitCohort (state : BeaconState preset fork) (epoch : Epoch) : Nat :=
  state.validators.data.toList.countP (·.exitEpoch == epoch)

/-- The number of validators of a state that are activated at an epoch. -/
def activationCohort (state : BeaconState preset fork) (epoch : Epoch) : Nat :=
  state.validators.data.toList.countP (·.activationEpoch == epoch)

/-- The churn limit before Electra, for a registry of a given size whose validators are all active.
-/
def churnCap (config : Config) (size : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT.toNat (size / config.CHURN_LIMIT_QUOTIENT.toNat)

private theorem max_le_max_left {first second third : Nat} (le : second ≤ third) :
    max first second ≤ max first third :=
  Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans le (Nat.le_max_right _ _)⟩

theorem churnCap_mono {first second : Nat} (le : first ≤ second) :
    churnCap config first ≤ churnCap config second :=
  max_le_max_left (Nat.div_le_div_right le)

/-- The churn limit of a state is at most the cap of its registry size.

The registry must be below `2^64`, so that the count of active validators converts exactly. -/
theorem getValidatorChurnLimit_le_churnCap (small : state.validators.data.size < 2 ^ 64) :
    (getValidatorChurnLimit config state).toNat ≤ churnCap config state.validators.data.size := by
  have count : (getActiveValidatorIndices state (getCurrentEpoch state)).length ≤
      state.validators.data.size := by
    apply Nat.le_trans (List.length_filterMap_le _ _)
    simp
  have exact : (getActiveValidatorIndices state (getCurrentEpoch state)).length.toUInt64.toNat =
      (getActiveValidatorIndices state (getCurrentEpoch state)).length := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt count small)]
  unfold getValidatorChurnLimit churnCap
  rw [UInt64.max_def]
  split
  · rw [UInt64.toNat_div, exact]
    exact Nat.le_trans (Nat.div_le_div_right count) (Nat.le_max_right _ _)
  · exact Nat.le_max_left _ _

/-- Each exit cohort other than that of the far future has at most `max 1 cap` validators. -/
def ExitCohortsBounded (config : Config) (state : BeaconState preset fork) : Prop :=
  ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
    exitCohort state epoch ≤ max 1 (churnCap config state.validators.data.size)

/-- The activation epoch that the registry updates of a state would give, as a number.

It is some epochs after the current epoch. -/
def nextActivationEpoch (state : BeaconState preset fork) : Nat :=
  (getCurrentEpoch state).toNat + 1 + preset.MAX_SEED_LOOKAHEAD.toNat

/-- The activation cohorts of a state.

Each one other than those of the genesis epoch and the far future has at most `cap` validators.

Each one that is not empty is at an epoch before the next activation epoch. -/
structure ActivationCohorts (config : Config) (state : BeaconState preset fork) : Prop where
  bounded : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch ≠ GENESIS_EPOCH →
    activationCohort state epoch ≤ churnCap config state.validators.data.size
  scheduled : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → 0 < activationCohort state epoch →
    epoch.toNat < nextActivationEpoch state

/-! ## Counting -/

/-- Two lists have one count of a test when they agree on it at the positions of the first.

The second may be longer, and must fail the test past the first. -/
theorem countP_eq_of_getElem {α : Type} {test : α → Bool} :
    ∀ {first second : List α}, first.length ≤ second.length →
      (∀ index (inside : index < first.length) (inside' : index < second.length),
        test second[index] = test first[index]) →
      (∀ index (inside : index < second.length), first.length ≤ index →
        test second[index] = false) →
      second.countP test = first.countP test
  | [], second, _, _, past => by
    rw [List.countP_eq_zero.mpr fun item member => ?_]
    · rfl
    · obtain ⟨index, inside, rfl⟩ := List.getElem_of_mem member
      simp [past index inside (Nat.zero_le _)]
  | head :: rest, [], longer, _, _ => by simp at longer
  | head :: rest, head' :: rest', longer, same, past => by
    have first := same 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at first
    have tail := countP_eq_of_getElem (first := rest) (second := rest')
      (by simpa using longer)
      (fun index inside inside' => by
        have := same (index + 1) (by simpa using inside) (by simpa using inside')
        rwa [List.getElem_cons_succ, List.getElem_cons_succ] at this)
      (fun index inside le => by
        have := past (index + 1) (by simpa using inside) (by simpa using le)
        rwa [List.getElem_cons_succ] at this)
    simp only [List.countP_cons, first, tail]

/-! ## Steps that keep the cohorts -/

/-- A step of a block or an epoch that keeps the cohorts before Electra.

The registry does not shrink, and the slot stays.

The exit cohorts stay within their cap, and no activation cohort changes.

An exit cohort before the next activation epoch does not change either. -/
structure CohortStep (config : Config) (state after : BeaconState preset fork) : Prop where
  size_le : state.validators.data.size ≤ after.validators.data.size
  slot : after.slot = state.slot
  exits : ExitCohortsBounded config state → ExitCohortsBounded config after
  exitsBelow : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch.toNat < nextActivationEpoch state →
    exitCohort after epoch = exitCohort state epoch
  activations : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
    activationCohort after epoch = activationCohort state epoch

namespace CohortStep

theorem refl (state : BeaconState preset fork) : CohortStep config state state :=
  ⟨Nat.le_refl _, rfl, id, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem trans {first second third : BeaconState preset fork}
    (one : CohortStep config first second) (two : CohortStep config second third) :
    CohortStep config first third :=
  have next : nextActivationEpoch second = nextActivationEpoch first := by
    simp [nextActivationEpoch, getCurrentEpoch, one.slot]
  ⟨Nat.le_trans one.size_le two.size_le, two.slot.trans one.slot, two.exits ∘ one.exits,
    fun epoch far below =>
      (two.exitsBelow epoch far (next ▸ below)).trans (one.exitsBelow epoch far below),
    fun epoch far => (two.activations epoch far).trans (one.activations epoch far)⟩

theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → CohortStep config s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : CohortStep config state after :=
  foldlM_ok_invariant (CohortStep config state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

/-- A step that keeps the exit and activation epochs at each index.

It may add validators with neither. -/
theorem of_epochs
    (size_le : state.validators.data.size ≤ after.validators.data.size)
    (slot : after.slot = state.slot)
    (kept : ∀ index (inside : index < state.validators.data.size)
      (inside' : index < after.validators.data.size),
      after.validators.data[index].exitEpoch = state.validators.data[index].exitEpoch ∧
        after.validators.data[index].activationEpoch =
          state.validators.data[index].activationEpoch)
    (added : ∀ index (inside : index < after.validators.data.size),
      state.validators.data.size ≤ index →
      after.validators.data[index].exitEpoch = FAR_FUTURE_EPOCH ∧
        after.validators.data[index].activationEpoch = FAR_FUTURE_EPOCH) :
    CohortStep config state after := by
  have exits : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      exitCohort after epoch = exitCohort state epoch :=
    fun epoch far => countP_eq_of_getElem (by simpa using size_le)
      (fun index inside inside' => by
        simp only [Array.getElem_toList]
        rw [(kept index (by simpa using inside) (by simpa using inside')).1])
      (fun index inside le => by
        simp only [Array.getElem_toList]
        rw [(added index (by simpa using inside) (by simpa using le)).1]
        simpa using Ne.symm far)
  refine ⟨size_le, slot, fun bounded epoch far => ?_, fun epoch far _ => exits epoch far,
    fun epoch far => ?_⟩
  · rw [exits epoch far]
    exact Nat.le_trans (bounded epoch far) (max_le_max_left (churnCap_mono size_le))
  · exact countP_eq_of_getElem (by simpa using size_le)
      (fun index inside inside' => by
        simp only [Array.getElem_toList]
        rw [(kept index (by simpa using inside) (by simpa using inside')).2])
      (fun index inside le => by
        simp only [Array.getElem_toList]
        rw [(added index (by simpa using inside) (by simpa using le)).2]
        simpa using Ne.symm far)

theorem of_data (same : after.validators.data = state.validators.data)
    (slot : after.slot = state.slot) : CohortStep config state after :=
  .of_epochs (Nat.le_of_eq (by rw [same])) slot (fun index _ _ => by simp [same])
    (fun index inside le => absurd inside (by rw [same]; omega))

theorem setValidator {index : ValidatorIndex} {old validator : Validator}
    (found : getValidator state index = .ok old)
    (set : state.setValidator index validator = .ok after)
    (exit : validator.exitEpoch = old.exitEpoch)
    (activation : validator.activationEpoch = old.activationEpoch) :
    CohortStep config state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read : state.validators.data[index.toNat]? = some old := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      exact read
    · cases found
  refine .of_epochs (by simp [BeaconState.putValidator]) rfl (fun position _ _ => ?_)
    (fun position inside' le => absurd inside' (by simp [BeaconState.putValidator]; omega))
  simp only [BeaconState.putValidator, RootedForkList.data_set, Array.getElem_set]
  split
  · rename_i same
    subst same
    rw [Array.getElem?_eq_getElem inside] at read
    cases read
    exact ⟨exit, activation⟩
  · exact ⟨rfl, rfl⟩

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : EthLib.Consensus.increaseBalance state index delta = .ok after) :
    CohortStep config state after :=
  .of_data (by rw [increaseBalance_validators computed]) (by
    obtain ⟨_, set⟩ := increaseBalance_ok computed
    exact setBalance_slot set)

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : EthLib.Consensus.decreaseBalance state index delta = .ok after) :
    CohortStep config state after :=
  .of_data (by rw [decreaseBalance_validators computed]) (by
    obtain ⟨_, set⟩ := decreaseBalance_ok computed
    exact setBalance_slot set)

end CohortStep

/-! ## Mutators -/

/-- Before Electra, the exit queue gives an epoch no earlier than the next activation epoch. -/
theorem nextActivationEpoch_le_exitQueueEpoch {epoch : Epoch}
    (computed : exitQueueEpoch config state = .ok epoch) :
    nextActivationEpoch state ≤ epoch.toNat := by
  simp only [exitQueueEpoch, bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  rename_i earliest earliestOk
  have earliestValue := (computeActivationExitEpoch_ok_iff.mp
    (mapError_ok_iff.mp earliestOk)).2
  have atLeast := (le_foldl_maxExitEpoch
    (state.validators.data.toList.filter (·.exitEpoch != FAR_FUTURE_EPOCH)) earliest).1
  rw [UInt64.le_iff_toNat_le] at atLeast
  unfold nextActivationEpoch
  split at computed
  · have sum := (addChecked_ok_iff.mp (mapError_ok_iff.mp computed)).2
    rw [UInt64.toNat_one] at sum
    omega
  · cases computed
    omega

/-- Before Electra, an exit joins a cohort with room for it, and changes no other cohort. -/
theorem cohortStep_initiateValidatorExit (before : fork < .pectra) {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    CohortStep config state after := by
  obtain ⟨old, found, ⟨_, rfl⟩ | ⟨far, queued, exitEpoch, withdrawable, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _
  simp only [exitQueue, show ¬Fork.pectra ≤ fork from Nat.not_le_of_lt before, ↓reduceDIte,
    bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at queue
  obtain ⟨allocated, allocatedOk, rfl, rfl⟩ := queue
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read : state.validators.data[index.toNat] = old := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      rw [Array.getElem?_eq_getElem inside] at read
      exact Option.some.inj read
    · cases found
  -- The registry is below `2^64`, since its type bounds it before Gloas.
  have small : state.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (state.validators.bound (Nat.lt_trans before (by decide)))
      (UInt64.toNat_lt _)
  have sizeSame : (state.putValidator index.toNat inside
      { old with exitEpoch := allocated, withdrawableEpoch := withdrawable }).validators.data.size =
      state.validators.data.size := by
    simp [BeaconState.putValidator]
  -- Setting the exit epoch of one validator moves it from the far future cohort to its own.
  have count : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      exitCohort (state.putValidator index.toNat inside
        { old with exitEpoch := allocated, withdrawableEpoch := withdrawable }) epoch =
        exitCohort state epoch + (if allocated = epoch then 1 else 0) := by
    intro epoch finite
    unfold exitCohort
    simp only [BeaconState.putValidator, RootedForkList.data_set, Array.toList_set]
    rw [List.countP_set (by simpa using inside)]
    simp only [Array.getElem_toList, read, far, beq_iff_eq, Ne.symm finite, ↓reduceIte]
    split <;> omega
  have late := nextActivationEpoch_le_exitQueueEpoch allocatedOk
  refine ⟨Nat.le_of_eq sizeSame.symm, rfl, fun bounded epoch finite => ?_,
    fun epoch finite below => ?_, fun epoch _ => ?_⟩
  · rw [count epoch finite, sizeSame]
    split
    · rename_i same
      subst same
      have room := exitQueueEpoch_churn allocatedOk finite
      have limit := getValidatorChurnLimit_le_churnCap (config := config) small
      unfold exitCohort at room ⊢
      rw [← List.countP_eq_length_filter] at room
      omega
    · simpa using bounded epoch finite
  · have other : allocated ≠ epoch := by
      rintro rfl
      omega
    rw [count epoch finite]
    simp [other]
  · exact countP_eq_of_getElem (by simp [BeaconState.putValidator])
      (fun position _ _ => by
        simp only [BeaconState.putValidator, RootedForkList.data_set, Array.toList_set,
          List.getElem_set, Array.getElem_toList]
        split
        · rename_i same
          subst same
          rw [read]
        · rfl)
      (fun position inside' le => absurd inside' (by simp [BeaconState.putValidator]; omega))

theorem cohortStep_slashValidator (before : fork < .pectra) {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    CohortStep config state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  exact (cohortStep_initiateValidatorExit before exitedOk).trans <|
    ((CohortStep.setValidator found markedOk rfl rfl).trans (by exact .of_data rfl rfl)).trans <|
    (CohortStep.decreaseBalance loweredOk).trans <|
    (CohortStep.increaseBalance raisedOk).trans <|
    (CohortStep.increaseBalance lastOk).trans
      (.of_data (by rw [(slashValidator_last done).1]) (by
        simp only [pure, Except.pure, Except.ok.injEq] at done
        subst done
        split <;> rfl))

/-! ## The steps of a block -/

theorem cohortStep_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : CohortStep config state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_data rfl rfl

theorem cohortStep_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    CohortStep config state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_data rfl rfl

theorem cohortStep_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) : CohortStep config state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_data (by rw [← rest]) (by rw [← rest])

theorem cohortStep_processProposerSlashing (early : fork < .pectra) {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    CohortStep config state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact cohortStep_slashValidator early slashed

theorem cohortStep_slashIfSlashable (early : fork < .pectra)
    {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    CohortStep config step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact cohortStep_slashValidator early slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem cohortStep_processAttesterSlashing (early : fork < .pectra)
    {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    CohortStep config state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => CohortStep config state step.1)
    (fun _ _ _ before ok => before.trans (cohortStep_slashIfSlashable early ok))
    (show CohortStep config state (state, false).1 from .refl state) folded

theorem cohortStep_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    CohortStep config state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : CohortStep config raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_data rfl rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        CohortStep config state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_data rfl rfl
    exact (flagged _ _).trans ((CohortStep.increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact .of_data (by rw [← rest]) (by rw [← rest])

/-- A new validator goes to the end of the registry, with no activation or exit epoch.

Before Gloas the registry is below `2^64`, so the index for a new validator is its size. -/
theorem cohortStep_addValidatorToRegistry (early : fork < .pectra) {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    CohortStep config state after := by
  have small : state.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (state.validators.bound (Nat.lt_trans early (by decide)))
      (UInt64.toNat_lt _)
  have exact : (getIndexForNewValidator state).toNat = state.validators.data.size := by
    rw [getIndexForNewValidator, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' small]
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨validators, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
    have read := setOrAppendRooted_getElem? validatorsOk
    rw [exact] at read
    have present : state.validators.data.size < validators.data.size := by
      have := read state.validators.data.size
      simp only [↓reduceIte] at this
      exact (Array.getElem?_eq_some_iff.mp this).1
    refine .of_epochs (Nat.le_of_lt present) rfl (fun index inside inside' => ?_)
      (fun index inside le => ?_)
    · have same := read index
      rw [ite_eq_right_iff.mpr (fun equal => absurd equal (Nat.ne_of_lt inside)),
        Array.getElem?_eq_getElem inside, Array.getElem?_eq_getElem inside'] at same
      rw [Option.some.inj same]
      exact ⟨rfl, rfl⟩
    · have same := read index
      by_cases equal : index = state.validators.data.size
      · rw [ite_eq_left_iff.mpr (fun notEqual => absurd equal notEqual),
          Array.getElem?_eq_getElem inside] at same
        rw [Option.some.inj same]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right_iff.mpr (fun same => absurd same equal), Array.getElem?_eq_none le,
          Array.getElem?_eq_getElem inside] at same
        cases same
  · split at computed
    · cases computed
      refine .of_epochs (by simp [RootedForkList.data_push]) rfl (fun index inside _ => ?_)
        (fun index inside le => ?_)
      · simp [RootedForkList.data_push, Array.getElem_push, inside]
      · have equal : index = state.validators.data.size := by
          simp [RootedForkList.data_push] at inside
          omega
        subst equal
        simp [RootedForkList.data_push]
        exact ⟨rfl, rfl⟩
    · cases computed

theorem cohortStep_applyPendingDeposit (early : fork < .pectra) {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    CohortStep config state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact cohortStep_addValidatorToRegistry early computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · rw [liftAccessor_ok] at computed
    exact .increaseBalance computed

theorem cohortStep_applyDeposit (early : fork < .pectra) {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    CohortStep config state after := by
  unfold applyDeposit at computed
  split at computed
  · unfold applyDepositElectra at computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, added, pushed⟩ := computed
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (cohortStep_addValidatorToRegistry early added).trans (.of_data rfl rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_data rfl rfl
  · exact cohortStep_applyPendingDeposit early computed

theorem cohortStep_processDeposit (early : fork < .pectra) {before : fork < .hegota}
    {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    CohortStep config state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (CohortStep.of_data (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl rfl).trans
    (cohortStep_applyDeposit early applied)

theorem cohortStep_processVoluntaryExit (early : fork < .pectra) {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    CohortStep config state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact cohortStep_initiateValidatorExit early exited

/-! ## Requests of the execution layer -/

/-- The requests of the execution layer start at Electra. -/
theorem cohortStep_processExecutionRequests (early : fork < .pectra)
    {body : BeaconBlockBody preset fork} {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (_computed : processExecutionRequests config state body electra = .ok after) :
    CohortStep config state after :=
  absurd electra.1 (Nat.not_le_of_lt early)

/-! ## Withdrawals -/

theorem cohortStep_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) : CohortStep config state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, set⟩ := computed
    obtain ⟨_, rfl⟩ := setBuilder_ok set
    exact .of_data rfl rfl
  · exact .decreaseBalance computed

theorem cohortStep_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    CohortStep config state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : CohortStep config state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact CohortStep.foldlM (fun _ _ _ ok => cohortStep_applyWithdrawal ok) appliedOk
  have two : CohortStep config applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_data rfl rfl
    · cases indexedOk
      exact .refl _
  have queued : ∀ kept : BeaconState preset fork,
      CohortStep config kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl rfl
    · exact .refl _
  have partials : ∀ kept : BeaconState preset fork,
      CohortStep config kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_data rfl rfl
    · exact .refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → CohortStep config kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact .of_data rfl rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact .of_data rfl rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  have lastKept : CohortStep config finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact .of_data rfl rfl
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

theorem cohortStep_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    CohortStep config state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact cohortStep_applyExpectedWithdrawals applied
    · cases computed
      exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact cohortStep_applyExpectedWithdrawals applied

/-- A change to an execution address changes only the withdrawal credentials of the validator. -/
theorem cohortStep_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    CohortStep config state after := by
  obtain ⟨validator, found, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact .setValidator found set rfl rfl

/-! ## The parent payload and the execution part of a block -/

theorem cohortStep_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    CohortStep config state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_data rfl rfl

/-- The payload of the parent runs from Gloas. -/
theorem cohortStep_processParentExecutionPayload (early : fork < .pectra)
    {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (_computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    CohortStep config state after :=
  absurd (Nat.lt_of_lt_of_le early (Nat.le_trans (by decide) gloas)) (Nat.lt_irrefl _)

theorem cohortStep_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    CohortStep config state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_data rfl rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_data rfl rfl

theorem cohortStep_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    CohortStep config state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (cohortStep_processWithdrawals withdrawnOk).trans
      (cohortStep_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (cohortStep_processWithdrawals withdrawnOk).trans
      (cohortStep_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact cohortStep_processExecutionPayload computed
    · cases computed
      exact .refl _

/-! ## The sync aggregate -/

theorem cohortStep_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    CohortStep config state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine CohortStep.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (CohortStep.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

/-! ## Blocks -/

theorem cohortStep_processOperations (early : fork < .pectra) {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    CohortStep config state after := by
  unfold processOperations at computed
  split at computed
  · rename_i gloas
    exact absurd (Nat.lt_of_lt_of_le early (Nat.le_trans (by decide) gloas)) (Nat.lt_irrefl _)
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : CohortStep config exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact CohortStep.foldlM
        (fun _ _ _ ok => cohortStep_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : CohortStep config changed after := by
    split at requestsOk
    · exact cohortStep_processExecutionRequests early requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  exact (CohortStep.foldlM (fun _ _ _ ok => cohortStep_processProposerSlashing early ok)
      proposersOk).trans <|
    (CohortStep.foldlM (fun _ _ _ ok => cohortStep_processAttesterSlashing early ok)
      attestersOk).trans <|
    (CohortStep.foldlM (fun _ _ _ ok => cohortStep_processAttestation ok)
      attestedOk).trans <|
    (CohortStep.foldlM (fun _ _ _ ok => cohortStep_processDeposit early ok)
      depositedOk).trans <|
    (CohortStep.foldlM (fun _ _ _ ok => cohortStep_processVoluntaryExit early ok)
      exitsOk).trans <|
    changes.trans requests

theorem cohortStep_processBlock (early : fork < .pectra) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    CohortStep config state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs before the header.
    have paidKept : CohortStep config state paid := by
      split at paidOk
      · exact cohortStep_processParentExecutionPayload early paidOk
      · cases paidOk
        exact .refl _
    -- From Bellatrix the execution part runs between the header and the RANDAO reveal.
    have executedKept : CohortStep config headed executed := by
      split at executedOk
      · exact cohortStep_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    -- Heze drops the vote on the deposit contract.
    have votedKept : CohortStep config revealed voted := by
      split at votedOk
      · exact cohortStep_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    exact paidKept.trans <| (cohortStep_processBlockHeader headedOk).trans <|
      executedKept.trans <| (cohortStep_processRandao revealedOk).trans <|
      votedKept.trans <| (cohortStep_processOperations early operatedOk).trans
        (cohortStep_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (cohortStep_processBlockHeader headerOk).trans <|
    (cohortStep_processRandao randaoOk).trans <|
    (cohortStep_processEth1Data eth1Ok).trans
      (cohortStep_processOperations early operationsOk)

/-! ## The steps of an epoch -/

/-- Joining the activation queue keeps the activation epoch. -/
theorem queueForActivation_activationEpoch {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    queued.activationEpoch = validator.activationEpoch := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    rw [computed]

theorem cohortStep_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    CohortStep config state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_data (by rw [← rest]) (by rw [← rest])

theorem cohortStep_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : CohortStep config state after :=
  CohortStep.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (CohortStep.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem cohortStep_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    CohortStep config state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact CohortStep.foldlM (fun _ _ _ ok => cohortStep_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact cohortStep_applyAllDeltas applied

theorem cohortStep_updateRegistryEntry (early : fork < .pectra) {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    CohortStep config state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set := CohortStep.setValidator (config := config) found markedOk
    (queueForActivation_epochs queuedOk).1 (queueForActivation_activationEpoch queuedOk)
  split at computed
  · exact set.trans (cohortStep_initiateValidatorExit early (liftAccessor_ok.mp computed))
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

theorem cohortStep_processSlashings (computed : processSlashings state = .ok after) :
    CohortStep config state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine CohortStep.foldlM (fun _ _ _ ok => ?_) applied
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, lowered⟩ := ok
        exact .decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ .refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  · refine CohortStep.foldlM (fun _ _ _ ok => ?_) computed
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact .decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ .refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _

theorem cohortStep_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    CohortStep config state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_data rfl rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem cohortStep_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    CohortStep config state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine CohortStep.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, _, _, _, _, set⟩ := ok
  exact .setValidator found set rfl rfl

theorem cohortStep_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    CohortStep config state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_data rfl rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem cohortStep_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    CohortStep config state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_data rfl rfl

/-! ## The steps of an epoch from Altair -/

theorem cohortStep_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    CohortStep config state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_data rfl rfl

private theorem cohortStep_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : CohortStep config rooted after := by
  have syncedKept : CohortStep config rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact .of_data rfl rfl
  have lookedKept : CohortStep config synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_data rfl rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedKept : CohortStep config looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_data rfl rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedKept.trans (lookedKept.trans windowedKept)
/-- The pending deposits and consolidations start at Electra. -/
theorem cohortStep_processPendingBalances (early : fork < .pectra)
    (computed : processPendingBalances config checks state = .ok after) :
    CohortStep config state after := by
  unfold processPendingBalances at computed
  split at computed
  · rename_i electra
    exact absurd electra (Nat.not_le_of_lt early)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _


/-! ## Activations -/

/-- Activating a validator that has no activation epoch moves it to the next activation epoch.

It changes no other cohort, and neither the slot nor the size of the registry. -/
theorem activateValidator_cohorts {index : ValidatorIndex} {validator : Validator}
    (found : getValidator state index = .ok validator)
    (far : validator.activationEpoch = FAR_FUTURE_EPOCH)
    (computed : activateValidator state index = .ok after) :
    after.validators.data.size = state.validators.data.size ∧ after.slot = state.slot ∧
      (∀ epoch, exitCohort after epoch = exitCohort state epoch) ∧
      ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
        activationCohort after epoch = activationCohort state epoch +
          if epoch.toNat = nextActivationEpoch state then 1 else 0 := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff]
    at computed
  obtain ⟨old, oldFound, activation, activationOk, set⟩ := computed
  have same := Except.ok.inj (oldFound.symm.trans found)
  subst same
  have scheduled := (computeActivationExitEpoch_ok_iff.mp activationOk).2
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read : state.validators.data[index.toNat] = old := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      rw [Array.getElem?_eq_getElem inside] at read
      exact Option.some.inj read
    · cases found
  refine ⟨by simp [BeaconState.putValidator], rfl, fun epoch => ?_, fun epoch finite => ?_⟩
  · exact countP_eq_of_getElem (by simp [BeaconState.putValidator])
      (fun position _ _ => by
        simp only [BeaconState.putValidator, RootedForkList.data_set, Array.toList_set,
          List.getElem_set, Array.getElem_toList]
        split
        · rename_i same
          subst same
          rw [read]
        · rfl)
      (fun position inside' le => absurd inside' (by simp [BeaconState.putValidator]; omega))
  · have key : (activation == epoch) = decide (epoch.toNat = nextActivationEpoch state) := by
      rw [Bool.eq_iff_iff]
      simp only [beq_iff_eq, decide_eq_true_eq]
      constructor
      · rintro rfl
        exact scheduled
      · intro equal
        exact UInt64.toNat_inj.mp (scheduled.trans equal.symm)
    unfold activationCohort
    simp only [BeaconState.putValidator, RootedForkList.data_set, Array.toList_set]
    rw [List.countP_set (by simpa using inside)]
    simp only [Array.getElem_toList, read, far, beq_iff_eq, Ne.symm finite, ↓reduceIte, key]
    by_cases at_next : epoch.toNat = nextActivationEpoch state <;> simp [at_next]

/-- Activating distinct validators, none of which has an activation epoch at the start. -/
theorem foldActivateValidator_cohorts :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      indices.Nodup →
      (∀ index ∈ indices, ∃ validator, getValidator state index = .ok validator ∧
        validator.activationEpoch = FAR_FUTURE_EPOCH) →
      indices.foldlM activateValidator state = .ok after →
      after.validators.data.size = state.validators.data.size ∧ after.slot = state.slot ∧
        (∀ epoch, exitCohort after epoch = exitCohort state epoch) ∧
        ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
          activationCohort after epoch = activationCohort state epoch +
            if epoch.toNat = nextActivationEpoch state then indices.length else 0
  | [], state, after, _, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨rfl, rfl, fun _ => rfl, fun _ _ => by simp⟩
  | index :: rest, state, after, unique, eligible, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    obtain ⟨validator, found, far⟩ := eligible index List.mem_cons_self
    obtain ⟨absent, restUnique⟩ := List.nodup_cons.mp unique
    obtain ⟨size₁, slot₁, exits₁, activations₁⟩ := activateValidator_cohorts found far first
    have set : ∃ activated, state.setValidator index activated = .ok middle := by
      simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at first
      obtain ⟨_, _, _, _, set⟩ := first
      exact ⟨_, set⟩
    obtain ⟨_, set⟩ := set
    obtain ⟨size₂, slot₂, exits₂, activations₂⟩ :=
      foldActivateValidator_cohorts restUnique (fun other member => by
        -- The other validators of the list are untouched by this activation.
        have distinct : other ≠ index := fun same => absent (same ▸ member)
        obtain ⟨otherValidator, otherFound, otherFar⟩ :=
          eligible other (List.mem_cons_of_mem _ member)
        exact ⟨otherValidator, (getValidator_setValidator_of_ne set distinct).trans otherFound,
          otherFar⟩) tail
    have next : nextActivationEpoch middle = nextActivationEpoch state := by
      simp [nextActivationEpoch, getCurrentEpoch, slot₁]
    refine ⟨size₂.trans size₁, slot₂.trans slot₁, fun epoch => (exits₂ epoch).trans (exits₁ epoch),
      fun epoch finite => ?_⟩
    rw [activations₂ epoch finite, activations₁ epoch finite, next]
    simp only [List.length_cons]
    split <;> omega

/-- The registry updates before Electra.

The exit cohorts stay within their cap.

Only the cohort of the next activation epoch changes, and it grows by at most the cap. -/
theorem cohorts_processRegistryUpdates (early : fork < .pectra)
    (computed : processRegistryUpdates config state = .ok after) :
    state.validators.data.size ≤ after.validators.data.size ∧ after.slot = state.slot ∧
      (ExitCohortsBounded config state → ExitCohortsBounded config after) ∧
      (∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
        (epoch.toNat ≠ nextActivationEpoch state →
          activationCohort after epoch = activationCohort state epoch) ∧
        activationCohort after epoch ≤
          activationCohort state epoch + churnCap config after.validators.data.size) ∧
      ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch.toNat < nextActivationEpoch state →
        exitCohort after epoch = exitCohort state epoch := by
  unfold processRegistryUpdates at computed
  split at computed
  · rename_i electra
    exact absurd electra (Nat.not_le_of_lt early)
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  have updatedKept := CohortStep.foldlM (config := config)
    (fun _ _ _ ok => cohortStep_updateRegistryEntry early ok) updatedOk
  have updatedSlot := (Frame.foldlM (fun _ _ _ ok => frame_updateRegistryEntry ok) updatedOk).slot
  -- The registry is below `2^64`, since its type bounds it before Gloas.
  have small : updated.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (updated.validators.bound (Nat.lt_trans early (by decide)))
      (UInt64.toNat_lt _)
  obtain ⟨size, slot, exits, activations⟩ := foldActivateValidator_cohorts
    (List.Nodup.sublist (List.take_sublist _ _) (activationQueue_nodup small))
    (fun index member => by
      obtain ⟨position, validator, equal, found, eligible⟩ :=
        mem_activationQueue (List.mem_of_mem_take member)
      refine ⟨validator, ?_, activationEpoch_of_isEligibleForActivation eligible⟩
      have inside := (Array.getElem?_eq_some_iff.mp found).1
      have exact : index.toNat = position := by
        rw [← equal, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans inside small)]
      simp [getValidator, exact, found]) activated
  have next : nextActivationEpoch updated = nextActivationEpoch state := by
    simp [nextActivationEpoch, getCurrentEpoch, updatedSlot]
  -- At most the limit of validators are activated, which is at most the cap.
  have limit : (List.take
      (if Fork.dencun ≤ fork then getValidatorActivationChurnLimit config updated
        else getValidatorChurnLimit config updated).toNat (activationQueue updated)).length ≤
      churnCap config after.validators.data.size := by
    refine Nat.le_trans (List.length_take_le _ _) ?_
    rw [size]
    refine Nat.le_trans ?_ (getValidatorChurnLimit_le_churnCap small)
    split
    · exact UInt64.le_iff_toNat_le.mp getValidatorActivationChurnLimit_le.2
    · exact Nat.le_refl _
  refine ⟨Nat.le_trans updatedKept.size_le (Nat.le_of_eq size.symm), slot.trans updatedSlot,
    fun bounded epoch finite => ?_, fun epoch finite => ⟨fun other => ?_, ?_⟩,
    fun epoch finite below => ?_⟩
  · rw [exits epoch, size]
    exact updatedKept.exits bounded epoch finite
  · simp only [activations epoch finite, next, other, ↓reduceIte, Nat.add_zero,
      updatedKept.activations epoch finite]
  · rw [activations epoch finite, updatedKept.activations epoch finite]
    split <;> omega
  · rw [exits epoch]
    exact updatedKept.exitsBelow epoch finite below

/-! ## The epoch transition -/

theorem processJustificationAndFinalization_slot
    (computed : processJustificationAndFinalization state = .ok after) :
    after.slot = state.slot := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · rw [same]
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    rw [← rest]

/-- An epoch transition is steps that keep the cohorts, the registry updates, and more steps.

The next activation epoch only gets the activations of this pass. -/
private theorem cohorts_epochParts (early : fork < .pectra)
    {middle registered : BeaconState preset fork}
    (exits : ExitCohortsBounded config state) (activations : ActivationCohorts config state)
    (head : CohortStep config state middle) (middleSlot : middle.slot = state.slot)
    (registry : processRegistryUpdates config middle = .ok registered)
    (tail : CohortStep config registered after) :
    ExitCohortsBounded config after ∧
      (∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch ≠ GENESIS_EPOCH →
        activationCohort after epoch ≤ churnCap config after.validators.data.size) ∧
      (∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → 0 < activationCohort after epoch →
        epoch.toNat ≤ nextActivationEpoch state) ∧
      (∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch.toNat < nextActivationEpoch state →
        exitCohort after epoch = exitCohort state epoch ∧
          activationCohort after epoch = activationCohort state epoch) := by
  obtain ⟨sizeLe, registeredSlot, registryExits, registryActivations, registryBelow⟩ :=
    cohorts_processRegistryUpdates early registry
  have next : nextActivationEpoch middle = nextActivationEpoch state := by
    simp [nextActivationEpoch, getCurrentEpoch, middleSlot]
  have same : ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH →
      activationCohort after epoch = activationCohort registered epoch ∧
        activationCohort middle epoch = activationCohort state epoch :=
    fun epoch finite => ⟨tail.activations epoch finite, head.activations epoch finite⟩
  have registeredNext : nextActivationEpoch registered = nextActivationEpoch state := by
    simp [nextActivationEpoch, getCurrentEpoch, registeredSlot, middleSlot]
  refine ⟨tail.exits (registryExits (head.exits exits)), fun epoch finite genesis => ?_,
    fun epoch finite occupied => ?_, fun epoch finite below => ?_⟩
  · obtain ⟨afterSame, middleSame⟩ := same epoch finite
    obtain ⟨other, grown⟩ := registryActivations epoch finite
    rw [afterSame]
    by_cases at_next : epoch.toNat = nextActivationEpoch state
    · -- The cohort of the next activation epoch is empty before the pass.
      have empty : activationCohort state epoch = 0 := by
        refine Nat.eq_zero_of_not_pos fun occupied => ?_
        have := activations.scheduled epoch finite occupied
        omega
      rw [middleSame, empty, Nat.zero_add] at grown
      exact Nat.le_trans grown (churnCap_mono tail.size_le)
    · rw [other (by rw [next]; exact at_next), middleSame]
      exact Nat.le_trans (activations.bounded epoch finite genesis)
        (churnCap_mono (Nat.le_trans head.size_le (Nat.le_trans sizeLe tail.size_le)))
  · obtain ⟨afterSame, middleSame⟩ := same epoch finite
    obtain ⟨other, _⟩ := registryActivations epoch finite
    by_cases at_next : epoch.toNat = nextActivationEpoch state
    · exact Nat.le_of_eq at_next
    · rw [afterSame, other (by rw [next]; exact at_next), middleSame] at occupied
      exact Nat.le_of_lt (activations.scheduled epoch finite occupied)
  · -- Every step changes the cohorts only at the next activation epoch or later.
    obtain ⟨afterSame, middleSame⟩ := same epoch finite
    obtain ⟨other, _⟩ := registryActivations epoch finite
    refine ⟨?_, ?_⟩
    · rw [tail.exitsBelow epoch finite (by rw [registeredNext]; exact below),
        registryBelow epoch finite (by rw [next]; exact below),
        head.exitsBelow epoch finite below]
    · rw [afterSame, other (by rw [next]; omega), middleSame]

/-- The epoch transition before Electra keeps the exit cohorts within their cap.

The activation cohorts stay within theirs, at epochs up to the next activation epoch. -/
theorem cohorts_processEpoch (early : fork < .pectra) (exits : ExitCohortsBounded config state)
    (activations : ActivationCohorts config state)
    (computed : processEpoch config checks state = .ok after) :
    after.slot = state.slot ∧ ExitCohortsBounded config after ∧
      (∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch ≠ GENESIS_EPOCH →
        activationCohort after epoch ≤ churnCap config after.validators.data.size) ∧
      (∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → 0 < activationCohort after epoch →
        epoch.toNat ≤ nextActivationEpoch state) ∧
      (∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch.toNat < nextActivationEpoch state →
        exitCohort after epoch = exitCohort state epoch ∧
          activationCohort after epoch = activationCohort state epoch) := by
  unfold processEpoch at computed
  split at computed
  · have whole := computed
    obtain ⟨justified, justifiedOk, frame⟩ := processEpochAltair_frame whole
    unfold processEpochAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨justified', justifiedOk', scored, scoredOk, rewarded, rewardedOk, registered,
      registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk,
      balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
    have resetKept : CohortStep config slashed reset := by
      split at resetOk
      · exact cohortStep_processEth1DataReset resetOk
      · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
        exact resetOk ▸ .refl _
    have paidKept : CohortStep config pending paid := by
      split at paidOk
      · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure,
          Except.pure, Except.ok.injEq] at paidOk
        obtain ⟨_, _, rfl⟩ := paidOk
        exact .of_data rfl rfl
      · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
        exact paidOk ▸ .refl _
    have clearedKept : CohortStep config balanced cleared := by
      obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
      exact .of_data rfl rfl
    have mixedKept : CohortStep config cleared mixed := by
      obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
      exact .of_data rfl rfl
    have head : CohortStep config state rewarded :=
      (cohortStep_processJustificationAndFinalization justifiedOk').trans <|
      (cohortStep_processInactivityUpdates scoredOk).trans
        (cohortStep_processRewardsAndPenalties rewardedOk)
    have headSlot : rewarded.slot = state.slot :=
      (frame_processRewardsAndPenalties rewardedOk).slot.trans <|
        (frame_processInactivityUpdates scoredOk).slot.trans
          (processJustificationAndFinalization_slot justifiedOk')
    have middle : CohortStep config registered mixed :=
      (cohortStep_processSlashings slashedOk).trans <| resetKept.trans <|
      (cohortStep_processPendingBalances early pendingOk).trans <| paidKept.trans <|
      (cohortStep_processEffectiveBalanceUpdates balancedOk).trans <| clearedKept.trans mixedKept
    have tail : CohortStep config registered after := by
      split at computed <;> simp only [bind_ok_iff] at computed <;>
        obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
      · have rootedKept : CohortStep config mixed rooted := by
          unfold processHistoricalSummariesUpdate at rootedOk
          simp only [bind, Except.bind, pure, Except.pure] at rootedOk
          repeat' (split at rootedOk <;> try cases rootedOk)
          all_goals first
            | exact .refl _
            | exact .of_data rfl rfl
        exact middle.trans <| rootedKept.trans (cohortStep_epochEnd syncedOk lookedOk windowed)
      · exact middle.trans <| (cohortStep_processHistoricalRootsUpdate rootedOk).trans
          (cohortStep_epochEnd syncedOk lookedOk windowed)
    exact ⟨frame.slot.trans (processJustificationAndFinalization_slot justifiedOk),
      cohorts_epochParts early exits activations head headSlot registeredOk tail⟩
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have clearedKept : CohortStep config balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_data rfl rfl
  have mixedKept : CohortStep config cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_data rfl rfl
  have head : CohortStep config state rewarded :=
    (cohortStep_processJustificationAndFinalization justifiedOk).trans
      (cohortStep_processRewardsAndPenalties rewardedOk)
  have headSlot : rewarded.slot = state.slot :=
    (frame_processRewardsAndPenalties rewardedOk).slot.trans
      (processJustificationAndFinalization_slot justifiedOk)
  have tail : CohortStep config registered after :=
    (cohortStep_processSlashings slashedOk).trans <|
    (cohortStep_processEth1DataReset resetOk).trans <|
    (cohortStep_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans <| mixedKept.trans <|
    (cohortStep_processHistoricalRootsUpdate rootedOk).trans
      (cohortStep_processParticipationRecordUpdates rotated)
  have tailFrame : Frame registered after :=
    (frame_processSlashings slashedOk).trans <|
    (frame_processEth1DataReset resetOk).trans <|
    (frame_processEffectiveBalanceUpdates balancedOk).trans <|
    (frame_processSlashingsReset clearedOk).trans <|
    (frame_processRandaoMixesReset mixedOk).trans <|
    (frame_processHistoricalRootsUpdate rootedOk).trans
      (frame_processParticipationRecordUpdates rotated)
  exact ⟨tailFrame.slot.trans ((cohorts_processRegistryUpdates early registeredOk).2.1.trans
      headSlot),
    cohorts_epochParts early exits activations head headSlot registeredOk tail⟩


/-! ## Slots, upgrades and chains -/

/-- A state of another fork keeps the cohorts when it keeps the registry and the slot. -/
theorem cohorts_of_carried {fork' : Base.Fork} {after : BeaconState preset fork'}
    (validators : after.validators.data = state.validators.data) (slot : after.slot = state.slot)
    (exits : ExitCohortsBounded config state) (activations : ActivationCohorts config state) :
    ExitCohortsBounded config after ∧ ActivationCohorts config after := by
  have next : nextActivationEpoch after = nextActivationEpoch state := by
    simp [nextActivationEpoch, getCurrentEpoch, slot]
  refine ⟨fun epoch finite => ?_, ⟨fun epoch finite genesis => ?_,
    fun epoch finite occupied => ?_⟩⟩
  · simpa [exitCohort, validators] using exits epoch finite
  · simpa [activationCohort, validators] using activations.bounded epoch finite genesis
  · rw [next]
    exact activations.scheduled epoch finite
      (by simpa [activationCohort, validators] using occupied)

/-- The cohorts of a later state agree with those of a state before its next activation epoch.

The next activation epoch does not move back. -/
def PastCohortsKept {fork' : Base.Fork} (state : BeaconState preset fork)
    (after : BeaconState preset fork') : Prop :=
  nextActivationEpoch state ≤ nextActivationEpoch after ∧
    ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch.toNat < nextActivationEpoch state →
      exitCohort after epoch = exitCohort state epoch ∧
        activationCohort after epoch = activationCohort state epoch

/-- One slot before Electra keeps the cohorts within their caps.

At the last slot of an epoch, the epoch transition fills the cohort of the next activation epoch.

The slot then moves to the next epoch, whose next activation epoch is one later.

No cohort before the next activation epoch changes. -/
theorem cohorts_advanceSlot (early : fork < .pectra) (exits : ExitCohortsBounded config state)
    (activations : ActivationCohorts config state)
    (computed : advanceSlot config checks state = .ok after) :
    (ExitCohortsBounded config after ∧ ActivationCohorts config after) ∧
      PastCohortsKept state after := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  simp only [UInt64.toNat_one] at sum
  have cachedSlot := (frame_processSlot cachedOk).slot
  have cachedValidators : cached.validators.data = state.validators.data := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  obtain ⟨cachedExits, cachedActivations⟩ :=
    cohorts_of_carried (state := state) (after := cached) cachedValidators cachedSlot exits
      activations
  have cachedNext : nextActivationEpoch cached = nextActivationEpoch state := by
    simp [nextActivationEpoch, getCurrentEpoch, cachedSlot]
  have cachedSame : ∀ epoch, exitCohort cached epoch = exitCohort state epoch ∧
      activationCohort cached epoch = activationCohort state epoch := fun epoch => by
    simp [exitCohort, activationCohort, cachedValidators]
  -- The next slot is in the same epoch or a later one.
  have later : state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤
      next.toNat / preset.SLOTS_PER_EPOCH.toNat := Nat.div_le_div_right (by omega)
  have nextLe : nextActivationEpoch state ≤
      nextActivationEpoch ({ epoched with slot := next } : BeaconState preset fork) := by
    simp only [nextActivationEpoch, getCurrentEpoch_toNat]
    omega
  unfold epochIfLast at epochedOk
  split at epochedOk
  · rename_i boundary
    obtain ⟨slot, epochedExits, bounded, scheduled, below⟩ :=
      cohorts_processEpoch early cachedExits cachedActivations epochedOk
    have boundary' : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      simpa [UInt64.toNat_mod] using congrArg UInt64.toNat boundary
    -- The slot moves to the first slot of the next epoch.
    have step : next.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by
      rw [sum]
      exact Nat.succ_div_of_dvd (Nat.dvd_of_mod_eq_zero (sum ▸ boundary'))
    refine ⟨⟨epochedExits, bounded, fun epoch finite occupied => ?_⟩, nextLe,
      fun epoch finite below' => ?_⟩
    · have := scheduled epoch finite occupied
      simp only [nextActivationEpoch, getCurrentEpoch_toNat] at this ⊢
      rw [step]
      rw [cachedSlot] at this
      omega
    · obtain ⟨exitsSame, activationsSame⟩ := below epoch finite (by rw [cachedNext]; exact below')
      exact ⟨exitsSame.trans (cachedSame epoch).1, activationsSame.trans (cachedSame epoch).2⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    refine ⟨⟨cachedExits, cachedActivations.bounded, fun epoch finite occupied => ?_⟩, nextLe,
      fun epoch _ _ => cachedSame epoch⟩
    have := cachedActivations.scheduled epoch finite occupied
    simp only [nextActivationEpoch, getCurrentEpoch_toNat] at this ⊢
    rw [cachedSlot] at this
    omega

/-- Before Electra, the exit and activation cohorts of a forked state stay within their caps.

From Electra it holds with no condition. -/
def PreElectraCohorts (config : Config) (forked : ForkedBeaconState preset) : Prop :=
  forked.fork < .pectra →
    ExitCohortsBounded config forked.state ∧ ActivationCohorts config forked.state

/-- Every step of a chain keeps the cohorts before Electra. -/
theorem stepRelation_cohorts :
    StepRelation config checks fun (forked after : ForkedBeaconState preset) =>
      PreElectraCohorts config forked → PreElectraCohorts config after :=
  StepRelation.ofPreserves
    (fun holds computed early =>
      have ⟨exits, activations⟩ := holds early
      (cohorts_advanceSlot early exits activations computed).1)
    (fun {pre} {post} holds _ computed postEarly => by
      have preEarly : pre.fork < .pectra := Nat.lt_trans post.property postEarly
      obtain ⟨exits, activations⟩ := holds preEarly
      obtain ⟨fork, state⟩ := pre
      cases fork <;>
        simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
          throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
      · obtain ⟨_, upgraded, rfl⟩ := computed
        simp only [upgradeToAltair, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
        obtain ⟨_, folded, _, -, rfl⟩ := upgraded
        rw [← Array.foldlM_toList] at folded
        obtain ⟨_, rfl, -⟩ := foldlM_translateAttestation folded
        exact cohorts_of_carried (state := state) rfl rfl exits activations
      all_goals first
        | (subst computed; exact cohorts_of_carried (state := state) rfl rfl exits activations)
        | (obtain ⟨_, _, rfl⟩ := computed; simp only at postEarly
           exact absurd postEarly (by decide)))
    (fun {_} {_} {state} {after} {_} {_} holds computed early => by
      obtain ⟨exits, activations⟩ := holds early
      have blockOk := (applySignedBlock_ok computed).2.1
      have kept := cohortStep_processBlock early blockOk
      have next : nextActivationEpoch after = nextActivationEpoch state := by
        simp [nextActivationEpoch, getCurrentEpoch, (frame_processBlock blockOk).slot]
      refine ⟨kept.exits exits, ⟨fun epoch finite genesis => ?_, fun epoch finite occupied => ?_⟩⟩
      · rw [kept.activations epoch finite]
        exact Nat.le_trans (activations.bounded epoch finite genesis) (churnCap_mono kept.size_le)
      · rw [next]
        exact activations.scheduled epoch finite (kept.activations epoch finite ▸ occupied))

/-- An upgrade to a fork before Electra keeps the registry and the slot. -/
theorem upgradeNext_carried {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (early : post.val.fork < .pectra) (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.validators.data = pre.state.validators.data ∧
      post.val.state.slot = pre.state.slot := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToAltair, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, folded, _, -, rfl⟩ := upgraded
    rw [← Array.foldlM_toList] at folded
    obtain ⟨_, rfl, -⟩ := foldlM_translateAttestation folded
    exact ⟨rfl, rfl⟩
  all_goals first
    | (subst computed; exact ⟨rfl, rfl⟩)
    | (obtain ⟨_, _, rfl⟩ := computed; simp only at early
       exact absurd early (by decide))

/-- Along a chain before Electra, no cohort before the next activation epoch of its start changes.
-/
def PastCohorts (start after : ForkedBeaconState preset) : Prop :=
  start.fork ≤ after.fork ∧ (after.fork < .pectra → PastCohortsKept start.state after.state)

/-- Every step of a chain keeps the cohorts, and changes none before the next activation epoch. -/
theorem stepRelation_pastCohorts :
    StepRelation config checks fun (forked after : ForkedBeaconState preset) =>
      PreElectraCohorts config forked →
        PreElectraCohorts config after ∧ PastCohorts forked after :=
  StepRelation.ofGuarded (holds := PreElectraCohorts config) (relates := PastCohorts)
    (fun _ => ⟨Nat.le_refl _, fun _ => ⟨Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl⟩⟩⟩)
    (fun one two => ⟨Nat.le_trans one.1 two.1, fun late => by
      obtain ⟨firstLe, firstSame⟩ := one.2 (Nat.lt_of_le_of_lt two.1 late)
      obtain ⟨secondLe, secondSame⟩ := two.2 late
      refine ⟨Nat.le_trans firstLe secondLe, fun epoch finite below => ?_⟩
      obtain ⟨exitsSecond, activationsSecond⟩ :=
        secondSame epoch finite (Nat.lt_of_lt_of_le below firstLe)
      obtain ⟨exitsFirst, activationsFirst⟩ := firstSame epoch finite below
      exact ⟨exitsSecond.trans exitsFirst, activationsSecond.trans activationsFirst⟩⟩)
    (fun {fork} {_} {_} holds computed => by
      by_cases early : fork < .pectra
      · obtain ⟨exits, activations⟩ := holds early
        obtain ⟨kept, past⟩ := cohorts_advanceSlot early exits activations computed
        exact ⟨fun _ => kept, Nat.le_refl _, fun _ => past⟩
      · exact ⟨fun late => absurd late early, Nat.le_refl _, fun late => absurd late early⟩)
    (fun {pre} {post} holds due computed => by
      refine ⟨stepRelation_cohorts.upgradeNext due computed holds,
        Nat.le_of_lt post.property, fun early => ?_⟩
      obtain ⟨validators, slot⟩ := upgradeNext_carried early computed
      have next : nextActivationEpoch post.val.state = nextActivationEpoch pre.state := by
        simp [nextActivationEpoch, getCurrentEpoch, slot]
      exact ⟨Nat.le_of_eq next.symm, fun epoch _ _ => by
        simp [exitCohort, activationCohort, validators]⟩)
    (fun {fork} {_} {state} {after} {_} {_} holds computed => by
      refine ⟨stepRelation_cohorts.applySignedBlock computed holds, Nat.le_refl _,
        fun early => ?_⟩
      have kept := cohortStep_processBlock (config := config) early
        (applySignedBlock_ok computed).2.1
      have next : nextActivationEpoch after = nextActivationEpoch state := by
        simp [nextActivationEpoch, getCurrentEpoch, kept.slot]
      exact ⟨Nat.le_of_eq next.symm, fun epoch finite below =>
        ⟨kept.exitsBelow epoch finite below, kept.activations epoch finite⟩⟩)

/-- Along every chain from a state whose cohorts are within their caps, past cohorts stay.

They are those before its next activation epoch, while the chain stays before Electra. -/
theorem Reaches.pastCohorts {start after : ForkedBeaconState preset}
    (holds : PreElectraCohorts config start) (chain : Reaches config checks start after) :
    PastCohorts start after :=
  (stepRelation_pastCohorts.reaches chain holds).2

/-- Along every chain from a state whose cohorts are within their caps, every state keeps them so.

This says something only before Electra. -/
theorem Reaches.cohorts {start after : ForkedBeaconState preset}
    (holds : PreElectraCohorts config start) (chain : Reaches config checks start after) :
    PreElectraCohorts config after :=
  stepRelation_cohorts.reaches chain holds


/-! ## Genesis -/

/-- At genesis, each activation epoch is the genesis epoch or the far future. -/
def GenesisActivations (state : BeaconState preset fork) : Prop :=
  ∀ validator ∈ state.validators.data,
    validator.activationEpoch = FAR_FUTURE_EPOCH ∨ validator.activationEpoch = GENESIS_EPOCH

theorem genesisActivations_iff :
    GenesisActivations state ↔ ∀ epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch ≠ GENESIS_EPOCH →
      activationCohort state epoch = 0 := by
  constructor
  · intro holds epoch finite genesis
    refine List.countP_eq_zero.mpr fun validator member same => ?_
    have same : validator.activationEpoch = epoch := by simpa using same
    rcases holds validator (by simpa using member) with far | zero
    · exact finite (same ▸ far)
    · exact genesis (same ▸ zero)
  · intro empty validator member
    by_contra neither
    simp only [not_or] at neither
    have := empty validator.activationEpoch neither.1 neither.2
    rw [activationCohort, List.countP_eq_zero] at this
    exact this validator (by simpa using member) (by simp)

/-- A deposit at genesis keeps the cohorts, and adds a validator with no activation epoch. -/
theorem genesisCohorts_genesisDeposit (early : fork < .pectra) {before : fork < .hegota}
    {leaves : Array DepositData} {entry : Deposit × Nat}
    (holds : ExitCohortsBounded config state ∧ GenesisActivations state)
    (computed : genesisDeposit config checks before leaves state entry = .ok after) :
    ExitCohortsBounded config after ∧ GenesisActivations after := by
  simp only [genesisDeposit, bind_ok_iff] at computed
  obtain ⟨depositRoot, _, deposited⟩ := computed
  have kept := (CohortStep.of_data (config := config) (state := state)
    (after := { state with eth1Data := fun _ => { state.eth1Data before with depositRoot } })
    rfl rfl).trans (cohortStep_processDeposit early deposited)
  refine ⟨kept.exits holds.1, genesisActivations_iff.mpr fun epoch finite genesis => ?_⟩
  rw [kept.activations epoch finite]
  exact genesisActivations_iff.mp holds.2 epoch finite genesis

/-- Activating a validator at genesis gives it the genesis epoch, or changes no epoch. -/
theorem genesisCohorts_activateAtGenesis {index : Nat}
    (holds : ExitCohortsBounded config state ∧ GenesisActivations state)
    (computed : activateAtGenesis state index = .ok after) :
    ExitCohortsBounded config after ∧ GenesisActivations after := by
  simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨old, found, _, _, set⟩ := computed
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  have read : state.validators.data[index.toUInt64.toNat] = old := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      rw [Array.getElem?_eq_getElem inside] at read
      exact Option.some.inj read
    · cases found
  generalize newValidator : (if _ = preset.MAX_EFFECTIVE_BALANCE then _ else _) = validator
  have sameExit : validator.exitEpoch = old.exitEpoch := by
    rw [← newValidator]
    split <;> rfl
  have activation : validator.activationEpoch = old.activationEpoch ∨
      validator.activationEpoch = GENESIS_EPOCH := by
    rw [← newValidator]
    split
    · exact .inr rfl
    · exact .inl rfl
  have exits : ∀ epoch, exitCohort (state.putValidator _ inside validator) epoch =
      exitCohort state epoch := fun epoch =>
    countP_eq_of_getElem (by simp [BeaconState.putValidator])
      (fun position _ _ => by
        simp only [BeaconState.putValidator, RootedForkList.data_set, Array.toList_set,
          List.getElem_set, Array.getElem_toList]
        split
        · rename_i same
          subst same
          rw [read, sameExit]
        · rfl)
      (fun position inside' le => absurd inside' (by simp [BeaconState.putValidator]; omega))
  refine ⟨fun epoch finite => ?_, fun member mem => ?_⟩
  · rw [exits epoch]
    simpa [BeaconState.putValidator] using holds.1 epoch finite
  · simp only [BeaconState.putValidator, RootedForkList.data_set] at mem
    rcases Array.mem_or_eq_of_mem_set mem with earlier | rfl
    · exact holds.2 member earlier
    · rcases activation with same | genesis
      · rw [same]
        exact holds.2 old (read ▸ Array.getElem_mem inside)
      · exact .inr genesis

/-- A genesis state before Electra has its cohorts within their caps.

Its validators exit at the far future, and are activated at the genesis epoch or not at all. -/
theorem genesis_cohorts {forked : ForkedBeaconState preset}
    (launched : Genesis config checks forked) : PreElectraCohorts config forked := by
  intro early
  obtain ⟨fork, state⟩ := forked
  obtain ⟨⟨_, _, _, computed⟩, _⟩ := launched
  have holds : ExitCohortsBounded config state ∧ GenesisActivations state := by
    unfold initializeBeaconStateFromEth1 at computed
    split at computed
    · cases computed
    simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, rfl⟩ :=
      computed
    have afterDeposits := foldlM_ok_invariant
      (fun state => ExitCohortsBounded config state ∧ GenesisActivations state)
      (fun _ _ _ before ok => genesisCohorts_genesisDeposit early before ok)
      ⟨fun _ _ => by simp [exitCohort, emptyGenesisState],
        fun _ member => by simp [emptyGenesisState] at member⟩ depositedOk
    have afterActivations := foldlM_ok_invariant _
      (fun _ _ _ before ok => genesisCohorts_activateAtGenesis before ok) afterDeposits
      activatedOk
    exact ⟨fun epoch finite => afterActivations.1 epoch finite, afterActivations.2⟩
  obtain ⟨exits, activations⟩ := holds
  refine ⟨exits, ⟨fun epoch finite genesis => ?_, fun epoch finite occupied => ?_⟩⟩
  · rw [genesisActivations_iff.mp activations epoch finite genesis]
    exact Nat.zero_le _
  · by_cases genesis : epoch = GENESIS_EPOCH
    · subst genesis
      simp only [nextActivationEpoch, GENESIS_EPOCH, UInt64.toNat_zero]
      omega
    · rw [genesisActivations_iff.mp activations epoch finite genesis] at occupied
      exact absurd occupied (Nat.lt_irrefl _)

/-- Every reachable state before Electra has its exit and activation cohorts within their caps.
-/
theorem Reachable.cohorts {forked : ForkedBeaconState preset}
    (reachable : Reachable config checks forked) : PreElectraCohorts config forked :=
  have ⟨_, launched, chain⟩ := reachable
  chain.cohorts (genesis_cohorts launched)

end EthLib.Consensus
