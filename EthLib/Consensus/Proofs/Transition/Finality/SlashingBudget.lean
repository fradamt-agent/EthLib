module

public import EthLib.Consensus.Proofs.Transition.Finality.Definitions

/-!
# Phase 0 slashing credit ledger

The ledger follows `processProposerSlashing` and `processAttesterSlashing`.

Each entry retains the states on either side of the actual `slashValidator` call.

Each newly slashed validator pays its effective balance divided by the whistleblower quotient.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {p : Preset}

/-- An actual slashing site and its combined proposer and whistleblower credit. -/
abbrev FinalityCreditEvent (p : Preset) :=
  BeaconState p .phase0 × BeaconState p .phase0 × ValidatorIndex × Nat

/-- Read the quotient at the slashing site, before any operation changes the state. -/
def finalityCreditEvent (state after : BeaconState p .phase0) (index : ValidatorIndex) :
    Except TransitionError (FinalityCreditEvent p) := do
  let validator ← liftAccessor (getValidator state index)
  return (state, after, index, validator.effectiveBalance.toNat /
    (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)

/-- Record every proposer operation, in its original order. -/
def finalityProposerCredits (cfg : Config) (checks : SignatureChecks) :
    List ProposerSlashing → BeaconState p .phase0 →
      Except TransitionError (BeaconState p .phase0 × List (FinalityCreditEvent p))
  | [], state => .ok (state, [])
  | slashing :: rest, state => do
    let middle ← processProposerSlashing cfg checks state slashing
    let event ← finalityCreditEvent state middle slashing.signedHeader1.message.proposerIndex
    let (after, events) ← finalityProposerCredits cfg checks rest middle
    return (after, event :: events)

/-- Follow every attester intersection step, retaining exactly the steps that pay. -/
def finalityIndexCredits (cfg : Config) :
    List ValidatorIndex → BeaconState p .phase0 × Bool →
      Except TransitionError ((BeaconState p .phase0 × Bool) × List (FinalityCreditEvent p))
  | [], step => .ok (step, [])
  | index :: rest, step => do
    let validator ← liftAccessor (getValidator step.1 index)
    let middle ← slashIfSlashable cfg step index
    let (after, events) ← finalityIndexCredits cfg rest middle
    if isSlashableValidator validator (getCurrentEpoch step.1) then
      let event ← finalityCreditEvent step.1 middle.1 index
      return (after, event :: events)
    else return (after, events)

/-- The extra quotient lookup always succeeds after a successful proposer slashing. -/
theorem finalityProposerCredits_ok (cfg : Config) (checks : SignatureChecks)
    (slashings : List ProposerSlashing) {state after : BeaconState p .phase0}
    (ran : slashings.foldlM (processProposerSlashing cfg checks) state = .ok after) :
    ∃ events, finalityProposerCredits cfg checks slashings state = .ok (after, events) := by
  induction slashings generalizing state with
  | nil => cases ran; exact ⟨[], rfl⟩
  | cons slashing rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨events, collected⟩ := ih tail
    obtain ⟨validator, found, _⟩ := (processProposerSlashing_checks first).2.2.2
    refine ⟨(state, middle, slashing.signedHeader1.message.proposerIndex,
      validator.effectiveBalance.toNat /
        (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) :: events, ?_⟩
    simp [finalityProposerCredits, first, finalityCreditEvent, found, liftAccessor,
      Except.mapError, collected, bind, Except.bind, pure, Except.pure]

/-- Recording the intersection does not change its resulting state or flag. -/
theorem finalityIndexCredits_ok (cfg : Config) (indices : List ValidatorIndex)
    {step after : BeaconState p .phase0 × Bool}
    (ran : indices.foldlM (slashIfSlashable cfg) step = .ok after) :
    ∃ events, finalityIndexCredits cfg indices step = .ok (after, events) := by
  induction indices generalizing step with
  | nil => cases ran; exact ⟨[], rfl⟩
  | cons index rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨events, collected⟩ := ih tail
    have read := first
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at read
    obtain ⟨validator, found, _⟩ := read
    by_cases paid : isSlashableValidator validator (getCurrentEpoch step.1) = true
    · refine ⟨(step.1, middle.1, index, validator.effectiveBalance.toNat /
        (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) :: events, ?_⟩
      simp [finalityIndexCredits, first, found, liftAccessor, Except.mapError,
        collected, paid, finalityCreditEvent, bind, Except.bind, pure, Except.pure]
    · refine ⟨events, ?_⟩
      simp [finalityIndexCredits, first, found, liftAccessor, Except.mapError,
        collected, paid, bind, Except.bind, pure, Except.pure]

/-- Check the original attester operation and then record its actual intersection fold. -/
def finalityAttesterCredits (cfg : Config) (checks : SignatureChecks) :
    List (AttesterSlashing p .phase0) → BeaconState p .phase0 →
      Except TransitionError (BeaconState p .phase0 × List (FinalityCreditEvent p))
  | [], state => .ok (state, [])
  | slashing :: rest, state => do
    let middle ← processAttesterSlashing cfg checks state slashing
    let (_, events) ← finalityIndexCredits cfg (slashingIndices slashing) (state, false)
    let (after, tail) ← finalityAttesterCredits cfg checks rest middle
    return (after, events ++ tail)

/-- Run the checked block, retaining the slashing sites at its operation boundary. -/
def finalityBlockCredits (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) (state : FinalityState p) (block : FinalityBlock p) :
    Except TransitionError (FinalityState p × List (FinalityCreditEvent p)) := do
  let after ← stateTransition cfg checks eng state block true
  let advanced ← processSlots cfg state block.message.slot
  let header ← processBlockHeader advanced block.message
  let randao ← processRandao cfg checks header block.message.body
  let eth1 ← processEth1Data (by decide) randao block.message.body
  let (proposers, first) ← finalityProposerCredits cfg checks
    block.message.body.proposerSlashings.data.toList eth1
  let (_, second) ← finalityAttesterCredits cfg checks
    block.message.body.attesterSlashings.data.toList proposers
  return (after, first ++ second)

/-- Collect every paid call along the validated chain, preserving execution order. -/
def collectSlashingCredits (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) (state : FinalityState p) :
    List (FinalityBlock p) →
      Except TransitionError (FinalityState p × List (FinalityCreditEvent p))
  | [] => .ok (state, [])
  | block :: rest => do
    let (middle, first) ← finalityBlockCredits cfg checks eng state block
    let (after, tail) ← collectSlashingCredits cfg checks eng middle rest
    return (after, first ++ tail)

/-- Every successful attester list admits its complete ledger. -/
theorem finalityAttesterCredits_ok (cfg : Config) (checks : SignatureChecks)
    (slashings : List (AttesterSlashing p .phase0)) {state after : BeaconState p .phase0}
    (ran : slashings.foldlM (processAttesterSlashing cfg checks) state = .ok after) :
    ∃ events, finalityAttesterCredits cfg checks slashings state = .ok (after, events) := by
  induction slashings generalizing state with
  | nil => cases ran; exact ⟨[], rfl⟩
  | cons slashing rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨events, collected⟩ := ih tail
    have read := first
    simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at read
    obtain ⟨_, _, _, _, _, _, _, _, _, _, folded, foldOk, _⟩ := read
    obtain ⟨paid, paidOk⟩ := finalityIndexCredits_ok cfg _ foldOk
    exact ⟨paid ++ events, by
      simp [finalityAttesterCredits, first, paidOk, collected, bind, Except.bind,
        pure, Except.pure]⟩

/-- Each event records both successful balance increases of its slashing call. -/
theorem finalityCreditEvent_payments {cfg : Config} {e : FinalityCreditEvent p}
    (valid : FinalitySlashCredit cfg e.1 e.2.1 e.2.2.1 e.2.2.2) :
    ∃ lowered raised proposer proposerReward whistleblowerReward,
      getBeaconProposerIndex lowered = .ok proposer ∧
      increaseBalance lowered proposer proposerReward = .ok raised ∧
      increaseBalance raised proposer whistleblowerReward = .ok e.2.1 ∧
      proposerReward.toNat + whistleblowerReward.toNat = e.2.2.2 := by
  obtain ⟨called, original, found, credit⟩ := valid
  obtain ⟨validator, lowered, raised, proposer, whistleblower, proposerReward,
    whistleblowerReward, read, proposerOk, recipient, first, second, total⟩ :=
    slashValidator_phase0_credits called
  have same := Except.ok.inj (found.symm.trans read)
  subst validator
  simp only [Option.getD_none] at recipient
  subst whistleblower
  exact ⟨lowered, raised, proposer, proposerReward, whistleblowerReward,
    proposerOk, first, second, total.trans credit.symm⟩

/-- A ledger's local facts, including the cap at each actual payment site. -/
def FinalityCreditLedger (cfg : Config) (state after : FinalityState p)
    (events : List (FinalityCreditEvent p)) : Prop :=
  (events.map fun e => e.2.2.1).Nodup ∧
    (∀ e ∈ events, slashedFlag state e.2.2.1 ≠ .ok true ∧
      slashedFlag after e.2.2.1 = .ok true) ∧
    (∀ e ∈ events, FinalitySlashCredit cfg e.1 e.2.1 e.2.2.1 e.2.2.2 ∧
      e.2.2.2 ≤ p.MAX_EFFECTIVE_BALANCE.toNat /
        (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)

/-- The empty execution has no credits. -/
theorem finalityCreditLedger_nil (cfg : Config) (state : FinalityState p) :
    FinalityCreditLedger cfg state state [] := by simp [FinalityCreditLedger]

/-- Flags prevent overlap when two consecutive executions' ledgers are joined. -/
theorem finalityCreditLedger_append {cfg : Config} {state middle after : FinalityState p}
    {first tail : List (FinalityCreditEvent p)}
    (one : FinalityCreditLedger cfg state middle first)
    (two : FinalityCreditLedger cfg middle after tail)
    (keptOne : ∀ i, slashedFlag state i = .ok true → slashedFlag middle i = .ok true)
    (keptTwo : ∀ i, slashedFlag middle i = .ok true → slashedFlag after i = .ok true) :
    FinalityCreditLedger cfg state after (first ++ tail) := by
  obtain ⟨uniqueOne, flagsOne, validOne⟩ := one
  obtain ⟨uniqueTwo, flagsTwo, validTwo⟩ := two
  refine ⟨?_, ?_, ?_⟩
  · rw [List.map_append]
    apply List.nodup_append.mpr
    refine ⟨uniqueOne, uniqueTwo, ?_⟩
    intro i member j other same
    obtain ⟨e, emem, ei⟩ := List.mem_map.mp member
    obtain ⟨f, fmem, fi⟩ := List.mem_map.mp other
    exact (flagsTwo f fmem).1 (by rw [fi, ← same, ← ei]; exact (flagsOne e emem).2)
  · intro e member
    rcases List.mem_append.mp member with member | member
    · exact ⟨(flagsOne e member).1, keptTwo _ (flagsOne e member).2⟩
    · exact ⟨fun old => (flagsTwo e member).1 (keptOne _ old), (flagsTwo e member).2⟩
  · intro e member
    rcases List.mem_append.mp member with member | member
    · exact validOne e member
    · exact validTwo e member

/-- A newly paid slashing contributes one bounded credit, even when its quotient is zero. -/
theorem finalityCreditLedger_singleton {cfg : Config} {state after : FinalityState p}
    {index : ValidatorIndex} {validator : Validator}
    (bounded : EffectiveBalancesBounded state)
    (found : getValidator state index = .ok validator)
    (clear : slashedFlag state index ≠ .ok true)
    (called : slashValidator cfg state index = .ok after) :
    FinalityCreditLedger cfg state after
      [(state, after, index, validator.effectiveBalance.toNat /
        (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)] := by
  refine ⟨by simp, ?_, ?_⟩
  · intro e member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨clear, (slashValidator_slashedFlag called).1⟩
  · intro e member
    obtain rfl := List.mem_singleton.mp member
    exact ⟨⟨called, validator, found, rfl⟩,
      Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp
        (bounded validator (mem_of_getValidator found)))⟩

/-- The proposer ledger contains precisely the newly paid calls and their site bounds. -/
theorem finalityProposerCredits_ledger (cfg : Config) (checks : SignatureChecks)
    (slashings : List ProposerSlashing) {state after : FinalityState p}
    (bounded : EffectiveBalancesBounded state)
    (ran : slashings.foldlM (processProposerSlashing cfg checks) state = .ok after) :
    ∃ events, finalityProposerCredits cfg checks slashings state = .ok (after, events) ∧
      FinalityCreditLedger cfg state after events := by
  induction slashings generalizing state with
  | nil => cases ran; exact ⟨[], rfl, finalityCreditLedger_nil _ _⟩
  | cons slashing rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨events, collected, ledger⟩ :=
      ih ((frame_processProposerSlashing first).effectiveBalancesBounded bounded) tail
    obtain ⟨validator, found, slashable, _⟩ := (processProposerSlashing_checks first).2.2.2
    have read := first
    simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at read
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, called⟩ := read
    have clear : slashedFlag state slashing.signedHeader1.message.proposerIndex ≠
        .ok true := by
      have unslashed : validator.slashed = false := by
        cases flag : validator.slashed <;> simp_all [isSlashableValidator]
      simp [slashedFlag, found, Except.map, unslashed]
    let event : FinalityCreditEvent p :=
      (state, middle, slashing.signedHeader1.message.proposerIndex,
        validator.effectiveBalance.toNat /
          (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
    refine ⟨event :: events, ?_, ?_⟩
    · simp [finalityProposerCredits, first, finalityCreditEvent, found, liftAccessor,
        Except.mapError, collected, bind, Except.bind, pure, Except.pure, event]
    · exact finalityCreditLedger_append
        (finalityCreditLedger_singleton bounded found clear called) ledger
        (fun _ flag => processProposerSlashing_slashedFlag first flag)
        (fun i flag => foldlM_ok_invariant (fun s => slashedFlag s i = .ok true)
          (fun _ _ _ old ok => processProposerSlashing_slashedFlag ok old) flag tail)

/-- The attester intersection ledger contains exactly the branches that slash. -/
theorem finalityIndexCredits_ledger (cfg : Config) (indices : List ValidatorIndex)
    {step after : FinalityState p × Bool} (bounded : EffectiveBalancesBounded step.1)
    (ran : indices.foldlM (slashIfSlashable cfg) step = .ok after) :
    ∃ events, finalityIndexCredits cfg indices step = .ok (after, events) ∧
      FinalityCreditLedger cfg step.1 after.1 events := by
  induction indices generalizing step with
  | nil => cases ran; exact ⟨[], rfl, finalityCreditLedger_nil _ _⟩
  | cons index rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    have read := first
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at read
    obtain ⟨validator, found, action⟩ := read
    by_cases paid : isSlashableValidator validator (getCurrentEpoch step.1) = true
    · simp only [paid, ↓reduceIte, bind_ok_iff, liftAccessor_ok,
        pure, Except.pure, Except.ok.injEq] at action
      obtain ⟨slashed, called, equal⟩ := action
      have middleEq : middle.1 = slashed := congrArg Prod.fst equal.symm
      obtain ⟨events, collected, ledger⟩ := ih
        (middleEq.symm ▸ (frame_slashValidator called).effectiveBalancesBounded bounded) tail
      have clear : slashedFlag step.1 index ≠ .ok true := by
        have unslashed : validator.slashed = false := by
          cases flag : validator.slashed <;> simp_all [isSlashableValidator]
        simp [slashedFlag, found, Except.map, unslashed]
      let event : FinalityCreditEvent p := (step.1, middle.1, index,
        validator.effectiveBalance.toNat /
          (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
      refine ⟨event :: events, ?_, ?_⟩
      · simp [finalityIndexCredits, first, found, liftAccessor, Except.mapError,
          collected, paid, finalityCreditEvent, bind, Except.bind, pure, Except.pure, event]
      · exact finalityCreditLedger_append
          (finalityCreditLedger_singleton bounded found clear (middleEq.symm ▸ called)) ledger
          (slashIfSlashable_ok first).2.1 (foldlM_slashIfSlashable rest tail).2.1
    · have middleEq : middle = step := by
        simpa [paid, pure, Except.pure] using action.symm
      obtain ⟨events, collected, ledger⟩ := ih (middleEq.symm ▸ bounded) tail
      refine ⟨events, ?_, ?_⟩
      · simp [finalityIndexCredits, first, found, liftAccessor, Except.mapError,
          collected, paid, bind, Except.bind, pure, Except.pure]
      · simpa only [middleEq] using ledger

/-- Attester operations compose their complete, disjoint payment ledgers. -/
theorem finalityAttesterCredits_ledger (cfg : Config) (checks : SignatureChecks)
    (slashings : List (AttesterSlashing p .phase0)) {state after : FinalityState p}
    (bounded : EffectiveBalancesBounded state)
    (ran : slashings.foldlM (processAttesterSlashing cfg checks) state = .ok after) :
    ∃ events, finalityAttesterCredits cfg checks slashings state = .ok (after, events) ∧
      FinalityCreditLedger cfg state after events := by
  induction slashings generalizing state with
  | nil => cases ran; exact ⟨[], rfl, finalityCreditLedger_nil _ _⟩
  | cons slashing rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨events, collected, ledger⟩ :=
      ih ((frame_processAttesterSlashing first).effectiveBalancesBounded bounded) tail
    have read := first
    simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at read
    obtain ⟨_, _, _, _, _, _, _, _, _, _, folded, foldOk, done⟩ := read
    simp only [pure, Except.pure, Except.ok.injEq] at done
    obtain ⟨_, _, equal⟩ := done
    obtain ⟨paid, paidOk, paidLedger⟩ := finalityIndexCredits_ledger cfg _ bounded foldOk
    have paidLedger' : FinalityCreditLedger cfg state middle paid := equal ▸ paidLedger
    refine ⟨paid ++ events, ?_, ?_⟩
    · simp [finalityAttesterCredits, first, paidOk, collected, bind, Except.bind,
        pure, Except.pure]
    · exact finalityCreditLedger_append paidLedger' ledger
        (fun _ flag => processAttesterSlashing_slashedFlag first flag)
        (fun i flag => foldlM_ok_invariant (fun s => slashedFlag s i = .ok true)
          (fun _ _ _ old ok => processAttesterSlashing_slashedFlag ok old) flag tail)

private theorem finalityAttestation_flag {cfg : Config} {checks : SignatureChecks}
    {state after : FinalityState p} {a : Attestation p .phase0} {i : ValidatorIndex}
    (ok : processAttestation cfg checks state a = .ok after) :
    slashedFlag after i = slashedFlag state i := by
  obtain ⟨_, _, _, _, _, recorded, _, _, _⟩ := processAttestation_records (by decide) ok
  cases current : a.data.target.epoch == getCurrentEpoch state <;>
    simp only [recordPendingAttestation, current, Bool.false_eq_true, ↓reduceIte] at recorded <;>
    split at recorded <;> cases recorded <;> rfl

private theorem finalityExit_flag {cfg : Config} {checks : SignatureChecks}
    {state after : FinalityState p} {e : SignedVoluntaryExit} {i : ValidatorIndex}
    (ok : processVoluntaryExit cfg checks state e = .ok after) :
    slashedFlag after i = slashedFlag state i := by
  unfold processVoluntaryExit at ok
  split at ok
  · cases ok
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at ok
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := ok
  exact slashedFlag_initiateValidatorExit exited i

/-- A block's complete ledger is bounded at the actual pre-slashing states. -/
theorem finalityBlockCredits_ledger (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) {state after : FinalityState p} (block : FinalityBlock p)
    (inv : Invariant state) (ran : stateTransition cfg checks eng state block true = .ok after) :
    ∃ events, finalityBlockCredits cfg checks eng state block = .ok (after, events) ∧
      FinalityCreditLedger cfg state after events := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok ran
  have read := blockOk
  simp only [processBlock, show ¬Fork.altair ≤ Fork.phase0 by decide,
    ↓reduceDIte, bind_ok_iff] at read
  obtain ⟨header, headerOk, randao, randaoOk, eth1, eth1Ok, operationsOk⟩ := read
  have ops := operationsOk
  simp only [processOperations, show ¬Fork.pectra ≤ Fork.phase0 by decide,
    ↓reduceDIte, bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at ops
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk,
    attested, attestedOk, deposited, depositedOk, exited, exitsOk, done⟩ := ops
  have advancedInv := (processSlots_invariant (by decide) inv slotsOk).1
  have eth1Inv := (frame_processEth1Data eth1Ok).invariant
    ((frame_processRandao randaoOk).invariant ((frame_processBlockHeader headerOk).invariant
      advancedInv))
  obtain ⟨first, firstOk, one⟩ := finalityProposerCredits_ledger cfg checks _
    eth1Inv.effectiveBalancesBounded proposersOk
  have proposerFrame := Frame.foldlM
    (fun _ _ _ ok => frame_processProposerSlashing ok) proposersOk
  obtain ⟨second, secondOk, two⟩ := finalityAttesterCredits_ledger cfg checks _
    (proposerFrame.effectiveBalancesBounded eth1Inv.effectiveBalancesBounded) attestersOk
  have ledger := finalityCreditLedger_append one two
    (fun i flag => foldlM_ok_invariant (fun s => slashedFlag s i = .ok true)
      (fun _ _ _ old ok => processProposerSlashing_slashedFlag ok old) flag proposersOk)
    (fun i flag => foldlM_ok_invariant (fun s => slashedFlag s i = .ok true)
      (fun _ _ _ old ok => processAttesterSlashing_slashedFlag ok old) flag attestersOk)
  refine ⟨first ++ second, ?_, ledger.1, ?_, ledger.2.2⟩
  · simp [finalityBlockCredits, ran, slotsOk, headerOk, randaoOk, eth1Ok, firstOk,
      secondOk, bind, Except.bind, pure, Except.pure]
  · intro e member
    refine ⟨?_, ?_⟩
    · intro flag
      apply (ledger.2.1 e member).1
      have slots := slotsOk
      simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slots
      obtain ⟨_, _, advancedOk⟩ := slots
      have atSlot := (advanceSlots_slashedFlag (by decide) inv advancedOk e.2.2.1).trans flag
      have headerRegistry : header.validators = advanced.validators := by
        obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
        rfl
      have randaoRegistry : randao.validators = header.validators := by
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq randaoOk
        rfl
      have eth1Registry : eth1.validators = randao.validators := by
        obtain ⟨_, _, unchanged⟩ := processEth1Data_eq eth1Ok
        rw [← unchanged]
      simpa only [slashedFlag, getValidator_of_validators_eq
        (eth1Registry.trans (randaoRegistry.trans headerRegistry))] using atSlot
    · have flag := (ledger.2.1 e member).2
      have atAttestations := foldlM_ok_invariant (fun s => slashedFlag s e.2.2.1 = .ok true)
        (fun _ _ _ old ok => (finalityAttestation_flag ok).trans old)
        flag attestedOk
      have atDeposits := foldlM_ok_invariant (fun s => slashedFlag s e.2.2.1 = .ok true)
        (fun _ _ _ old ok => processDeposit_slashedFlag (by decide) ok old)
        atAttestations depositedOk
      have atExits := foldlM_ok_invariant (fun s => slashedFlag s e.2.2.1 = .ok true)
        (fun _ _ _ old ok => (finalityExit_flag ok).trans old) atDeposits exitsOk
      have equal : exited = after := by
        simpa [show ¬Fork.shapella ≤ Fork.phase0 by decide, pure, Except.pure] using done
      exact equal ▸ atExits

/-- The complete chain ledger retains each validator at most once. -/
theorem collectSlashingCredits_ledger (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) (bs : List (FinalityBlock p))
    {state after : FinalityState p} (inv : Invariant state)
    (ran : finalityRuns cfg checks eng state bs after) :
    ∃ events, collectSlashingCredits cfg checks eng state bs = .ok (after, events) ∧
      FinalityCreditLedger cfg state after events := by
  induction bs generalizing state with
  | nil => cases ran; exact ⟨[], rfl, finalityCreditLedger_nil _ _⟩
  | cons block rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨head, headOk, headLedger⟩ := finalityBlockCredits_ledger cfg checks eng block inv first
    obtain ⟨events, collected, ledger⟩ :=
      ih (stateTransition_invariant (by decide) inv first).1 tail
    refine ⟨head ++ events, ?_, ?_⟩
    · simp [collectSlashingCredits, headOk, collected, bind, Except.bind, pure, Except.pure]
    · exact finalityCreditLedger_append headLedger ledger
        (fun _ flag => stateTransition_slashedFlag (by decide) inv first flag)
        (fun _ flag => stateTransition_chain_slashedFlag (by decide)
          (stateTransition_invariant (by decide) inv first).1 tail flag)

/-- The total credits use the number of distinct paid validators, not the registry size. -/
theorem finality_slashing_budget (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) (c after : FinalityState p) (bs : List (FinalityBlock p))
    (inv : Invariant c) (ran : finalityRuns cfg checks eng c bs after) :
    ∃ es, collectSlashingCredits cfg checks eng c bs = .ok (after, es) ∧
      (es.map fun e => e.2.2.1).Nodup ∧
      (∀ e ∈ es, FinalitySlashCredit cfg e.1 e.2.1 e.2.2.1 e.2.2.2) ∧
      (es.map fun e => e.2.2.2).sum ≤ es.length *
        (p.MAX_EFFECTIVE_BALANCE.toNat /
          (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat) := by
  obtain ⟨es, collected, unique, flags, valid⟩ :=
    collectSlashingCredits_ledger cfg checks eng bs inv ran
  refine ⟨es, collected, unique, fun e member => (valid e member).1, ?_⟩
  clear collected unique flags
  induction es with
  | nil => simp
  | cons e es ih =>
    have bound := (valid e List.mem_cons_self).2
    have tail := ih (fun e member => valid e (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- An original intersection prefix reaches a paid call with these exact event fields. -/
def FinalityIndexPaid (cfg : Config) (indices : List ValidatorIndex)
    (step : FinalityState p × Bool) (e : FinalityCreditEvent p) : Prop :=
  ∃ earlier later atStep validator,
    indices = earlier ++ e.2.2.1 :: later ∧
    earlier.foldlM (slashIfSlashable cfg) step = .ok atStep ∧
    atStep.1 = e.1 ∧ getValidator atStep.1 e.2.2.1 = .ok validator ∧
    isSlashableValidator validator (getCurrentEpoch atStep.1) = true ∧
    slashIfSlashable cfg atStep e.2.2.1 = .ok (e.2.1, true) ∧
    e.2.2.2 = validator.effectiveBalance.toNat /
      (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat

/-- The intersection collector records a paid original prefix if and only if it retains its event.

The caller supplies the successful original fold, not a filtered replacement execution.
-/
theorem finalityIndexCredits_complete (cfg : Config) (indices : List ValidatorIndex)
    {step after : FinalityState p × Bool} {events : List (FinalityCreditEvent p)}
    (ran : indices.foldlM (slashIfSlashable cfg) step = .ok after)
    (collected : finalityIndexCredits cfg indices step = .ok (after, events))
    (e : FinalityCreditEvent p) :
    e ∈ events ↔ FinalityIndexPaid cfg indices step e := by
  induction indices generalizing step events with
  | nil =>
    cases ran
    cases collected
    simp [FinalityIndexPaid]
  | cons index rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨paid, paidOk⟩ := finalityIndexCredits_ok cfg rest tail
    have read := first
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at read
    obtain ⟨validator, found, action⟩ := read
    have tailIff := ih tail paidOk
    by_cases slashable : isSlashableValidator validator (getCurrentEpoch step.1) = true
    · simp only [slashable, ↓reduceIte, bind_ok_iff, liftAccessor_ok,
        pure, Except.pure, Except.ok.injEq] at action
      obtain ⟨slashed, called, equal⟩ := action
      have recording := collected
      simp [finalityIndexCredits, found, first, paidOk, liftAccessor, Except.mapError,
        finalityCreditEvent, slashable, bind, Except.bind, pure, Except.pure] at recording
      subst events
      constructor
      · intro member
        rcases List.mem_cons.mp member with same | member
        · subst e
          exact ⟨[], rest, step, validator, rfl, rfl, rfl, found, slashable,
            by simpa only [← equal] using first, rfl⟩
        · obtain ⟨earlier, later, atStep, v, split, prefixOk, fields⟩ := tailIff.mp member
          exact ⟨index :: earlier, later, atStep, v, by simp [split],
            bind_ok_iff.mpr ⟨middle, first, prefixOk⟩, fields⟩
      · rintro ⟨earlier, later, atStep, v, split, prefixOk, pre, readV, may, call, credit⟩
        cases earlier with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          cases prefixOk
          have idx := split.1
          have sameV : v = validator := Except.ok.inj (readV.symm.trans (idx ▸ found))
          have samePost : e.2.1 = middle.1 := by
            have sameCall := Except.ok.inj (call.symm.trans (idx ▸ first))
            exact congrArg Prod.fst sameCall
          apply List.mem_cons.mpr
          left
          rcases e with ⟨preState, postState, eventIndex, reward⟩
          simp only [Prod.mk.injEq] at *
          exact ⟨pre.symm, samePost, idx.symm, by simpa [sameV] using credit⟩
        | cons head earlier =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, splitTail⟩ := split
          obtain ⟨next, headOk, restOk⟩ := bind_ok_iff.mp prefixOk
          have same := Except.ok.inj (headOk.symm.trans first)
          subst next
          exact List.mem_cons_of_mem _ (tailIff.mpr
            ⟨earlier, later, atStep, v, splitTail, restOk, pre, readV, may, call, credit⟩)
    · have recording := collected
      simp [finalityIndexCredits, found, first, paidOk, liftAccessor, Except.mapError,
        slashable, bind, Except.bind, pure, Except.pure] at recording
      subst events
      constructor
      · intro member
        obtain ⟨earlier, later, atStep, v, split, prefixOk, fields⟩ := tailIff.mp member
        exact ⟨index :: earlier, later, atStep, v, by simp [split],
          bind_ok_iff.mpr ⟨middle, first, prefixOk⟩, fields⟩
      · rintro ⟨earlier, later, atStep, v, split, prefixOk, pre, readV, may, call, credit⟩
        cases earlier with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at split
          cases prefixOk
          have sameV : v = validator := Except.ok.inj (readV.symm.trans (split.1 ▸ found))
          exact (slashable (sameV ▸ may)).elim
        | cons head earlier =>
          simp only [List.cons_append, List.cons.injEq] at split
          obtain ⟨rfl, splitTail⟩ := split
          obtain ⟨next, headOk, restOk⟩ := bind_ok_iff.mp prefixOk
          have same := Except.ok.inj (headOk.symm.trans first)
          subst next
          exact tailIff.mpr
            ⟨earlier, later, atStep, v, splitTail, restOk, pre, readV, may, call, credit⟩

/-- A proposer operation at an original list prefix pays the recorded event. -/
def FinalityProposerPaid (cfg : Config) (checks : SignatureChecks)
    (slashings : List ProposerSlashing) (state : FinalityState p)
    (e : FinalityCreditEvent p) : Prop :=
  ∃ earlier slashing later,
    slashings = earlier ++ slashing :: later ∧
    earlier.foldlM (processProposerSlashing cfg checks) state = .ok e.1 ∧
    processProposerSlashing cfg checks e.1 slashing = .ok e.2.1 ∧
    slashing.signedHeader1.message.proposerIndex = e.2.2.1 ∧
    finalityCreditEvent e.1 e.2.1 e.2.2.1 = .ok e

/-- Every proposer call in the original list is retained, with no additional event. -/
theorem finalityProposerCredits_complete (cfg : Config) (checks : SignatureChecks)
    (slashings : List ProposerSlashing) {state after : FinalityState p}
    {events : List (FinalityCreditEvent p)}
    (ran : slashings.foldlM (processProposerSlashing cfg checks) state = .ok after)
    (collected : finalityProposerCredits cfg checks slashings state = .ok (after, events))
    (e : FinalityCreditEvent p) :
    e ∈ events ↔ FinalityProposerPaid cfg checks slashings state e := by
  induction slashings generalizing state events with
  | nil => cases ran; cases collected; simp [FinalityProposerPaid]
  | cons slashing rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨paid, paidOk⟩ := finalityProposerCredits_ok cfg checks rest tail
    obtain ⟨validator, found, _⟩ := (processProposerSlashing_checks first).2.2.2
    let event : FinalityCreditEvent p :=
      (state, middle, slashing.signedHeader1.message.proposerIndex,
        validator.effectiveBalance.toNat /
          (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat)
    have eventOk : finalityCreditEvent state middle
        slashing.signedHeader1.message.proposerIndex = .ok event := by
      simp [finalityCreditEvent, found, liftAccessor, Except.mapError,
        bind, Except.bind, pure, Except.pure, event]
    have recorded : event :: paid = events := by
      simpa [finalityProposerCredits, first, eventOk, paidOk,
        bind, Except.bind, pure, Except.pure] using collected
    subst events
    have tailIff := ih tail paidOk
    constructor
    · intro member
      rcases List.mem_cons.mp member with same | member
      · subst e
        exact ⟨[], slashing, rest, rfl, rfl, first, rfl, eventOk⟩
      · obtain ⟨earlier, item, later, split, prefixOk, fields⟩ := tailIff.mp member
        exact ⟨slashing :: earlier, item, later, by simp [split],
          bind_ok_iff.mpr ⟨middle, first, prefixOk⟩, fields⟩
    · rintro ⟨earlier, item, later, split, prefixOk, called, index, credit⟩
      cases earlier with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, _⟩ := split
        cases prefixOk
        have post := Except.ok.inj (called.symm.trans first)
        have same : e = event := Except.ok.inj
          (credit.symm.trans (by simpa [post, ← index] using eventOk))
        exact List.mem_cons.mpr (.inl same)
      | cons head earlier =>
        simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, splitTail⟩ := split
        obtain ⟨next, headOk, restOk⟩ := bind_ok_iff.mp prefixOk
        have same := Except.ok.inj (headOk.symm.trans first)
        subst next
        exact List.mem_cons_of_mem _ (tailIff.mpr
          ⟨earlier, item, later, splitTail, restOk, called, index, credit⟩)

/-- A paid intersection step inside an attester operation reached by its original prefix. -/
def FinalityAttesterPaid (cfg : Config) (checks : SignatureChecks)
    (slashings : List (AttesterSlashing p .phase0)) (state : FinalityState p)
    (e : FinalityCreditEvent p) : Prop :=
  ∃ earlier slashing later atSlashing,
    slashings = earlier ++ slashing :: later ∧
    earlier.foldlM (processAttesterSlashing cfg checks) state = .ok atSlashing ∧
    FinalityIndexPaid cfg (slashingIndices slashing) (atSlashing, false) e

/-- Attester-list membership is exactly original-operation-prefix payment provenance. -/
theorem finalityAttesterCredits_complete (cfg : Config) (checks : SignatureChecks)
    (slashings : List (AttesterSlashing p .phase0)) {state after : FinalityState p}
    {events : List (FinalityCreditEvent p)}
    (ran : slashings.foldlM (processAttesterSlashing cfg checks) state = .ok after)
    (collected : finalityAttesterCredits cfg checks slashings state = .ok (after, events))
    (e : FinalityCreditEvent p) :
    e ∈ events ↔ FinalityAttesterPaid cfg checks slashings state e := by
  induction slashings generalizing state events with
  | nil => cases ran; cases collected; simp [FinalityAttesterPaid]
  | cons slashing rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨paid, paidOk⟩ := finalityAttesterCredits_ok cfg checks rest tail
    have read := first
    simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at read
    obtain ⟨_, _, _, _, _, _, _, _, _, _, folded, foldOk, _⟩ := read
    obtain ⟨head, headOk⟩ := finalityIndexCredits_ok cfg _ foldOk
    have recorded : head ++ paid = events := by
      simpa [finalityAttesterCredits, first, headOk, paidOk,
        bind, Except.bind, pure, Except.pure] using collected
    subst events
    have headIff := finalityIndexCredits_complete cfg _ foldOk headOk e
    have tailIff := ih tail paidOk
    constructor
    · intro member
      rcases List.mem_append.mp member with member | member
      · exact ⟨[], slashing, rest, state, rfl, rfl, headIff.mp member⟩
      · obtain ⟨earlier, item, later, atSlashing, split, prefixOk, fields⟩ := tailIff.mp member
        exact ⟨slashing :: earlier, item, later, atSlashing, by simp [split],
          bind_ok_iff.mpr ⟨middle, first, prefixOk⟩, fields⟩
    · rintro ⟨earlier, item, later, atSlashing, split, prefixOk, fields⟩
      cases earlier with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, _⟩ := split
        cases prefixOk
        exact List.mem_append.mpr (.inl (headIff.mpr fields))
      | cons head earlier =>
        simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, splitTail⟩ := split
        obtain ⟨next, headOk, restOk⟩ := bind_ok_iff.mp prefixOk
        have same := Except.ok.inj (headOk.symm.trans first)
        subst next
        exact List.mem_append.mpr (.inr (tailIff.mpr
          ⟨earlier, item, later, atSlashing, splitTail, restOk, fields⟩))

/-- A paid call inside the actual Phase 0 operation boundary of a block. -/
def FinalityBlockPaid (cfg : Config) (checks : SignatureChecks)
    (state : FinalityState p) (block : FinalityBlock p) (e : FinalityCreditEvent p) : Prop :=
  ∃ advanced header randao eth1 proposers,
    processSlots cfg state block.message.slot = .ok advanced ∧
    processBlockHeader advanced block.message = .ok header ∧
    processRandao cfg checks header block.message.body = .ok randao ∧
    processEth1Data (by decide) randao block.message.body = .ok eth1 ∧
    block.message.body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing cfg checks) eth1 = .ok proposers ∧
    (FinalityProposerPaid cfg checks block.message.body.proposerSlashings.data.toList eth1 e ∨
      FinalityAttesterPaid cfg checks block.message.body.attesterSlashings.data.toList proposers e)

/-- A paid call on the chain, located by its original block prefix. -/
def FinalityChainPaid (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) (state : FinalityState p)
    (bs : List (FinalityBlock p)) (e : FinalityCreditEvent p) : Prop :=
  ∃ earlier block later atBlock,
    bs = earlier ++ block :: later ∧
    finalityRuns cfg checks eng state earlier atBlock ∧
    FinalityBlockPaid cfg checks atBlock block e

/-- Block ledger membership is exactly a paid call at the actual operation boundary. -/
theorem finalityBlockCredits_complete (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) {state after : FinalityState p}
    {events : List (FinalityCreditEvent p)} (block : FinalityBlock p)
    (ran : stateTransition cfg checks eng state block true = .ok after)
    (collected : finalityBlockCredits cfg checks eng state block = .ok (after, events))
    (e : FinalityCreditEvent p) :
    e ∈ events ↔ FinalityBlockPaid cfg checks state block e := by
  obtain ⟨advanced, slotsOk, _, _, blockOk, _⟩ := stateTransition_ok ran
  simp only [processBlock, show ¬Fork.altair ≤ Fork.phase0 by decide,
    ↓reduceDIte, bind_ok_iff] at blockOk
  obtain ⟨header, headerOk, randao, randaoOk, eth1, eth1Ok, operationsOk⟩ := blockOk
  simp only [processOperations, show ¬Fork.pectra ≤ Fork.phase0 by decide,
    ↓reduceDIte, bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at operationsOk
  obtain ⟨_, _, _, _, proposers, proposersOk, attesters, attestersOk, _⟩ := operationsOk
  obtain ⟨first, firstOk⟩ := finalityProposerCredits_ok cfg checks _ proposersOk
  obtain ⟨second, secondOk⟩ := finalityAttesterCredits_ok cfg checks _ attestersOk
  have recorded : first ++ second = events := by
    simpa [finalityBlockCredits, ran, slotsOk, headerOk, randaoOk, eth1Ok,
      firstOk, secondOk, bind, Except.bind, pure, Except.pure] using collected
  subst events
  have firstIff := finalityProposerCredits_complete cfg checks _ proposersOk firstOk e
  have secondIff := finalityAttesterCredits_complete cfg checks _ attestersOk secondOk e
  constructor
  · intro member
    exact ⟨advanced, header, randao, eth1, proposers, slotsOk, headerOk, randaoOk,
      eth1Ok, proposersOk, (List.mem_append.mp member).imp firstIff.mp secondIff.mp⟩
  · rintro ⟨a, h, r, eth, ps, slots, headers, randaos, eth1s, proposersRun, paid⟩
    have same := Except.ok.inj (slots.symm.trans slotsOk)
    subst a
    have same := Except.ok.inj (headers.symm.trans headerOk)
    subst h
    have same := Except.ok.inj (randaos.symm.trans randaoOk)
    subst r
    have same := Except.ok.inj (eth1s.symm.trans eth1Ok)
    subst eth
    have same := Except.ok.inj (proposersRun.symm.trans proposersOk)
    subst ps
    exact List.mem_append.mpr (paid.imp firstIff.mpr secondIff.mpr)

/-- Every original chain-prefix paid call appears in the ledger, and every event has that origin. -/
theorem collectSlashingCredits_complete (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) (bs : List (FinalityBlock p))
    {state after : FinalityState p} {events : List (FinalityCreditEvent p)}
    (inv : Invariant state) (ran : finalityRuns cfg checks eng state bs after)
    (collected : collectSlashingCredits cfg checks eng state bs = .ok (after, events))
    (e : FinalityCreditEvent p) :
    e ∈ events ↔ FinalityChainPaid cfg checks eng state bs e := by
  induction bs generalizing state events with
  | nil => cases ran; cases collected; simp [FinalityChainPaid]
  | cons block rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp ran
    obtain ⟨head, headOk, _⟩ := finalityBlockCredits_ledger cfg checks eng block inv first
    have middleInv := (stateTransition_invariant (by decide) inv first).1
    obtain ⟨paid, paidOk, _⟩ := collectSlashingCredits_ledger cfg checks eng rest middleInv tail
    have recorded : head ++ paid = events := by
      simpa [collectSlashingCredits, headOk, paidOk, bind, Except.bind, pure, Except.pure]
        using collected
    subst events
    have headIff := finalityBlockCredits_complete cfg checks eng block first headOk e
    have tailIff := ih middleInv tail paidOk
    constructor
    · intro member
      rcases List.mem_append.mp member with member | member
      · exact ⟨[], block, rest, state, rfl, rfl, headIff.mp member⟩
      · obtain ⟨earlier, item, later, atBlock, split, prefixOk, fields⟩ := tailIff.mp member
        exact ⟨block :: earlier, item, later, atBlock, by simp [split],
          bind_ok_iff.mpr ⟨middle, first, prefixOk⟩, fields⟩
    · rintro ⟨earlier, item, later, atBlock, split, prefixOk, fields⟩
      cases earlier with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at split
        obtain ⟨rfl, _⟩ := split
        cases prefixOk
        exact List.mem_append.mpr (.inl (headIff.mpr fields))
      | cons head earlier =>
        simp only [List.cons_append, List.cons.injEq] at split
        obtain ⟨rfl, splitTail⟩ := split
        obtain ⟨next, headOk, restOk⟩ := bind_ok_iff.mp prefixOk
        have same := Except.ok.inj (headOk.symm.trans first)
        subst next
        exact List.mem_append.mpr (.inr (tailIff.mpr
          ⟨earlier, item, later, atBlock, splitTail, restOk, fields⟩))

/-- Every actual paid call contributes exactly one occurrence of its validator index. -/
theorem collectSlashingCredits_paid_once (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) (bs : List (FinalityBlock p))
    {state after : FinalityState p} {events : List (FinalityCreditEvent p)}
    (inv : Invariant state) (ran : finalityRuns cfg checks eng state bs after)
    (collected : collectSlashingCredits cfg checks eng state bs = .ok (after, events))
    (e : FinalityCreditEvent p) (paid : FinalityChainPaid cfg checks eng state bs e) :
    (events.map fun e => e.2.2.1).count e.2.2.1 = 1 := by
  obtain ⟨es, recorded, unique, _⟩ := collectSlashingCredits_ledger cfg checks eng bs inv ran
  have same : es = events := congrArg Prod.snd (Except.ok.inj (recorded.symm.trans collected))
  subst es
  exact unique.count_of_mem (List.mem_map.mpr
    ⟨e, (collectSlashingCredits_complete cfg checks eng bs inv ran collected e).mpr paid, rfl⟩)

end EthLib.Consensus
