module

public import EthLib.Consensus.Proofs.Transition.Provenance.Attestations
public import EthLib.Consensus.Proofs.Transition.Provenance.Weighing

/-!
# Proofs: where the participation flags of a chain come from

From Altair a state holds one byte of flags per validator, for the previous and current epochs.

A flag of the current epoch's list votes for the current epoch, and likewise for the previous.

This file traces each set flag of a chain's end to the step that set it.

There are three possible origins.

- The start of the chain already had the flag.
- The chain crossed the upgrade to Altair, which turned pending attestations into flags.
- A block of the chain included an attestation that earned the flag for that validator.

In the last case the attestation's target is the epoch of the list that holds the flag.

The attestation ran at its site, where its indexed form was valid, so its signature was checked.

The end of an epoch moves the current list to the previous one, so the epoch follows the list.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The flags of one epoch: the current one, or the previous one. -/
def epochFlags (state : BeaconState preset fork) (altair : .altair ≤ fork) (current : Bool) :
    Array ParticipationFlags :=
  if current then (state.currentEpochParticipation altair).data
  else (state.previousEpochParticipation altair).data

/-- The epoch that a list of flags votes for. -/
def flagsEpoch (state : BeaconState preset fork) (current : Bool) : Epoch :=
  if current then getCurrentEpoch state else getPreviousEpoch state

/-- At a site, an attestation earned a flag for a validator, and its indexed form was valid.

The validator is one of its attesters, and an earned flag index sets the same bit. -/
def AttestationFlagged (config : Config) (checks : SignatureChecks)
    (site : BeaconState preset fork) (parentSlot : Slot) (attestation : Attestation preset fork)
    (index : Nat) (flagIndex : UInt64) : Prop :=
  ∃ earned attesters indexed,
    getAttestationParticipationFlagIndices site attestation.data
      (site.slot - attestation.data.slot) parentSlot = .ok earned ∧
    getAttestingIndices site attestation = .ok attesters ∧
    (∃ attester ∈ attesters, attester.toNat = index) ∧
    (∃ added ∈ earned, added.toNat % 8 = flagIndex.toNat % 8) ∧
    getIndexedAttestation site attestation = .ok indexed ∧
    isValidIndexedAttestation config checks site indexed = .ok true

/-- The flags after the attestations of a block come from before them, or from one of them.

That attestation ran at a state of the block's slot, and earned the flag there.

It wrote the list of its target's epoch. -/
theorem foldlM_processAttestation_flags (altair : .altair ≤ fork) {parentSlot : Slot} :
    ∀ {attestations : List (Attestation preset fork)} {first attested : BeaconState preset fork},
      attestations.foldlM (processAttestation config checks · parentSlot ·) first =
        .ok attested →
      ∀ (current : Bool) (index : Nat) (flags : ParticipationFlags) (flagIndex : UInt64),
        (epochFlags attested altair current)[index]? = some flags →
        hasFlag flags flagIndex = true →
        (∃ old, (epochFlags first altair current)[index]? = some old ∧
          hasFlag old flagIndex = true) ∨
        ∃ pre attestation suf site recorded,
          attestations = pre ++ attestation :: suf ∧
          pre.foldlM (processAttestation config checks · parentSlot ·) first = .ok site ∧
          processAttestation config checks site parentSlot attestation = .ok recorded ∧
          Kept first site ∧ attestation.data.target.epoch = flagsEpoch site current ∧
          AttestationFlagged config checks site parentSlot attestation index flagIndex
  | [], first, attested, computed, _, _, flags, _, found, set => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .inl ⟨flags, found, set⟩
  | attestation :: rest, first, attested, computed, current, index, flags, flagIndex, found, set => by
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, folded⟩ := computed
    have stepAltair : processAttestationAltair config checks first attestation altair parentSlot =
        .ok middle := by
      unfold processAttestation at step
      simpa only [altair, ↓reduceDIte] using step
    rcases foldlM_processAttestation_flags altair folded current index flags flagIndex found set with
      ⟨old, oldFound, oldSet⟩ |
      ⟨pre, later, suf, site, recorded, split, prefixOk, laterOk, siteSlot, epoch, flagged⟩
    · -- The flag was there after this attestation: it was there before, or this one set it.
      obtain ⟨earned, attesters, indexed, earnedOk, attestersOk, indexedOk, valid, recent, -, -,
        lists⟩ := processAttestationAltair_votes stepAltair
      have origin : (∃ old', (epochFlags first altair current)[index]? = some old' ∧
            hasFlag old' flagIndex = true) ∨
          (attestation.data.target.epoch = flagsEpoch first current ∧
            (∃ attester ∈ attesters, attester.toNat = index) ∧
            ∃ added ∈ earned, added.toNat % 8 = flagIndex.toNat % 8) := by
        unfold epochFlags flagsEpoch at *
        by_cases isCurrent : attestation.data.target.epoch = getCurrentEpoch first
        · simp only [isCurrent, ↓reduceIte] at lists
          cases current
          · simp only [Bool.false_eq_true, ↓reduceIte] at oldFound ⊢
            exact .inl (lists.2 index old flagIndex oldFound oldSet)
          · simp only [↓reduceIte] at oldFound ⊢
            rcases lists.1 index old flagIndex oldFound oldSet with before | ⟨who, added⟩
            · exact .inl before
            · exact .inr ⟨isCurrent, who, added⟩
        · simp only [isCurrent, ↓reduceIte] at lists
          have previous : attestation.data.target.epoch = getPreviousEpoch first :=
            recent.resolve_right isCurrent
          cases current
          · simp only [Bool.false_eq_true, ↓reduceIte] at oldFound ⊢
            rcases lists.1 index old flagIndex oldFound oldSet with before | ⟨who, added⟩
            · exact .inl before
            · exact .inr ⟨previous, who, added⟩
          · simp only [↓reduceIte] at oldFound ⊢
            exact .inl (lists.2 index old flagIndex oldFound oldSet)
      rcases origin with before | ⟨epoch, who, added⟩
      · exact .inl before
      · exact .inr ⟨[], attestation, rest, first, middle, rfl, rfl, step, Kept.refl _, epoch,
          earned, attesters, indexed, earnedOk, attestersOk, who, added, indexedOk, valid⟩
    · -- A later attestation set it, from a state at the same slot.
      refine .inr ⟨attestation :: pre, later, suf, site, recorded, by rw [split]; rfl, ?_, laterOk,
        (kept_processAttestation step).trans siteSlot, epoch, flagged⟩
      simp only [List.foldlM_cons, bind_ok_iff]
      exact ⟨middle, step, prefixOk⟩

/-! ## Along a chain -/

/-- The start of a chain had a flag of a validator, in one of its two lists. -/
def FlagAtStart (start : ForkedBeaconState preset) (index : Nat) (flagIndex : UInt64) : Prop :=
  ∃ (altair : .altair ≤ start.fork) (current : Bool) (flags : ParticipationFlags),
    (epochFlags start.state altair current)[index]? = some flags ∧
      hasFlag flags flagIndex = true

/-- The chain crossed the upgrade to Altair, and the upgrade set a flag of a validator.

The upgrade turns the pending attestations of the previous epoch into flags of that epoch. -/
def FlagFromAltairUpgrade (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) (index : Nat) (flagIndex : UInt64) (epoch : Epoch) :
    Prop :=
  ∃ (pre : BeaconState preset .phase0) (post : BeaconState preset .altair)
    (flags : ParticipationFlags),
    Reaches config checks start ⟨.phase0, pre⟩ ∧ upgradeToAltair config pre = .ok post ∧
    Reaches config checks ⟨.altair, post⟩ after ∧
    (post.previousEpochParticipation (by decide)).data[index]? = some flags ∧
    hasFlag flags flagIndex = true ∧ epoch = getPreviousEpoch post

/-- A block of a chain included an attestation that set a flag of a validator.

The attestation ran at `site`, a state of the block's slot, after the attestations before it.

Its target is `epoch`, and it earned the flag there, with a valid indexed form. -/
def FlagSetBy (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset)
    (index : Nat) (flagIndex : UInt64) (epoch : Epoch) : Prop :=
  ∃ (fork : Fork) (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
    (validateResult : Bool) (state post first site recorded : BeaconState preset fork)
    (pre suf : List (Attestation preset fork)) (attestation : Attestation preset fork),
    Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
    applySignedBlock config checks engine state signed validateResult = .ok post ∧
    Reaches config checks ⟨fork, post⟩ after ∧
    VotesKept state first ∧
    signed.message.body.attestations.data.toList = pre ++ attestation :: suf ∧
    pre.foldlM (processAttestation config checks · state.latestBlockHeader.slot ·) first =
      .ok site ∧
    processAttestation config checks site state.latestBlockHeader.slot attestation = .ok recorded ∧
    SameReads state site ∧ attestation.data.target.epoch = epoch ∧
    AttestationFlagged config checks site state.latestBlockHeader.slot attestation index flagIndex

/-- Where a flag of a chain's end came from. -/
def FlagOrigin (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset)
    (index : Nat) (flagIndex : UInt64) (epoch : Epoch) : Prop :=
  FlagAtStart start index flagIndex ∨
    FlagFromAltairUpgrade config checks start after index flagIndex epoch ∨
    FlagSetBy config checks start after index flagIndex epoch

theorem FlagOrigin.extend {start middle after : ForkedBeaconState preset} {index : Nat}
    {flagIndex : UInt64} {epoch : Epoch}
    (origin : FlagOrigin config checks start middle index flagIndex epoch)
    (step : Step config checks middle after) :
    FlagOrigin config checks start after index flagIndex epoch := by
  rcases origin with atStart | ⟨pre, post, flags, head, upgraded, tail, rest⟩ |
    ⟨fork, engine, signed, validateResult, state, post, first, site, recorded, pre, suf,
      attestation, head, notDue, applied, tail, rest⟩
  · exact .inl atStart
  · exact .inr (.inl ⟨pre, post, flags, head, upgraded, tail.step step, rest⟩)
  · exact .inr (.inr ⟨fork, engine, signed, validateResult, state, post, first, site, recorded,
      pre, suf, attestation, head, notDue, applied, tail.step step, rest⟩)

/-- Every flag of a chain's end has an origin, with the epoch of the list that holds it. -/
def FlagsTraced (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset) :
    Prop :=
  ∀ (altair : .altair ≤ after.fork) (current : Bool) (index : Nat) (flags : ParticipationFlags)
    (flagIndex : UInt64), (epochFlags after.state altair current)[index]? = some flags →
    hasFlag flags flagIndex = true →
    FlagOrigin config checks start after index flagIndex (flagsEpoch after.state current)

/-- A slot step closes its epoch when the next slot is a multiple of the epoch length. -/
theorem closesEpoch_iff (fits : state.slot.toNat + 1 < 2 ^ 64) :
    ClosesEpoch preset state ↔ preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 := by
  unfold ClosesEpoch
  rw [← UInt64.toNat_inj, UInt64.toNat_mod, UInt64.toNat_add, UInt64.toNat_one,
    Nat.mod_eq_of_lt fits, UInt64.toNat_zero, Nat.dvd_iff_mod_eq_zero]

/-- A slot step that does not close its epoch keeps the epoch.

So both lists of flags vote for the same epochs as before. -/
theorem flagsEpoch_of_open {next : BeaconState preset fork}
    (slot : next.slot.toNat = state.slot.toNat + 1) (notClosing : ¬ClosesEpoch preset state)
    (current : Bool) : flagsEpoch next current = flagsEpoch state current := by
  have fits : state.slot.toNat + 1 < 2 ^ 64 := slot ▸ UInt64.toNat_lt next.slot
  rw [closesEpoch_iff fits] at notClosing
  have same : getCurrentEpoch next = getCurrentEpoch state := by
    apply UInt64.toNat_inj.mp
    rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slot, Nat.succ_div]
    simp [notClosing]
  unfold flagsEpoch getPreviousEpoch
  rw [same]

/-- A slot step that closes its epoch starts the next one.

The previous epoch after it is the current epoch before it. -/
theorem getPreviousEpoch_of_closes {next : BeaconState preset fork}
    (slot : next.slot.toNat = state.slot.toNat + 1) (closes : ClosesEpoch preset state) :
    getPreviousEpoch next = getCurrentEpoch state := by
  have fits : state.slot.toNat + 1 < 2 ^ 64 := slot ▸ UInt64.toNat_lt next.slot
  rw [closesEpoch_iff fits] at closes
  apply UInt64.toNat_inj.mp
  rw [getPreviousEpoch_toNat, getCurrentEpoch_toNat, getCurrentEpoch_toNat, slot, Nat.succ_div]
  simp [closes]

/-- Two states at one slot, of any forks, have the same epochs. -/
theorem flagsEpoch_of_slot {fork' : Fork} {other : BeaconState preset fork'}
    (slot : other.slot = state.slot) (current : Bool) :
    flagsEpoch other current = flagsEpoch state current := by
  simp only [flagsEpoch, getPreviousEpoch, getCurrentEpoch, slot]

/-- Where the flags of a chain's end come from.

Each set flag of a validator, in the list of an epoch, was set at the start of the chain.

Or the chain crossed the upgrade to Altair, which set it in the list of that epoch.

Or a block of the chain included an attestation with that epoch as its target, which earned it.
-/
theorem Reaches.flags {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) : FlagsTraced config checks start after := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil =>
    intro altair current index flags flagIndex found set
    exact .inl ⟨altair, current, flags, found, set⟩
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    intro altair current index flags flagIndex found set
    cases step with
    | @slot fork state next notDue computed =>
      have stepSlot := advanceSlot_slot computed
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, next⟩ := .slot notDue computed
      simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
        addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
      obtain ⟨nextSlot, ⟨fits, nextEq⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
      have nextIs : nextSlot = state.slot + 1 := by
        apply UInt64.toNat_inj.mp
        rw [nextEq, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
      obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
      simp only at found stepSlot ⊢
      unfold epochIfLast at epochedOk
      rw [nextIs] at epochedOk
      by_cases closes : ClosesEpoch preset state
      · have last : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := closes
        simp only [last, ↓reduceIte] at epochedOk
        obtain ⟨before, rotated, head, rotates, tail⟩ := processEpoch_votes epochedOk
        cases current
        · -- The previous list after the step is the current list before it.
          have rotatedFlag := tail.previousEpochParticipation altair index flags flagIndex found set
          obtain ⟨old, oldFound, oldSet⟩ := rotatedFlag
          rw [rotates.previousEpochParticipation altair] at oldFound
          obtain ⟨older, olderFound, olderSet⟩ :=
            head.currentEpochParticipation altair index old flagIndex oldFound oldSet
          have origin := more altair true index older flagIndex olderFound olderSet
          have epoch : flagsEpoch { epoched with slot := nextSlot } false =
              flagsEpoch state true :=
            getPreviousEpoch_of_closes stepSlot closes
          rw [epoch]
          exact origin.extend theStep
        · -- The current list after the step is empty.
          obtain ⟨old, oldFound, oldSet⟩ :=
            tail.currentEpochParticipation altair index flags flagIndex found set
          rw [rotates.currentEpochParticipation altair index old oldFound, hasFlag_zero] at oldSet
          cases oldSet
      · have notLast : ¬(state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := closes
        simp only [notLast, ↓reduceIte] at epochedOk
        cases epochedOk
        rw [flagsEpoch_of_open stepSlot closes]
        exact (more altair current index flags flagIndex found set).extend theStep
    | @upgrade _ post due computed =>
      have theStep : Step config checks middle post.val := .upgrade due computed
      have slot := congrArg Prod.fst (upgradeNext_history computed)
      simp only [BeaconState.history] at slot
      by_cases fromAltair : .altair ≤ middle.fork
      · -- From Altair on, each list carries over.
        obtain ⟨previousWithin, currentWithin⟩ := upgradeNext_flags computed fromAltair
        have carried : ∃ old, (epochFlags middle.state fromAltair current)[index]? = some old ∧
            hasFlag old flagIndex = true := by
          cases current
          · exact previousWithin index flags flagIndex found set
          · exact currentWithin index flags flagIndex found set
        obtain ⟨old, oldFound, oldSet⟩ := carried
        rw [flagsEpoch_of_slot slot]
        exact (more fromAltair current index old flagIndex oldFound oldSet).extend theStep
      · -- The upgrade from Phase 0 sets flags in the previous list only.
        obtain ⟨fork, state⟩ := middle
        obtain ⟨⟨fork', post⟩, later⟩ := post
        cases fork <;>
          simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
            throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
        all_goals try exact absurd (by dsimp only; decide) fromAltair
        obtain ⟨upgraded, upgradedOk, same⟩ := computed
        cases same
        have translated := upgradedOk
        simp only [upgradeToAltair, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at translated
        obtain ⟨_, folded, _, -, rfl⟩ := translated
        rw [← Array.foldlM_toList] at folded
        obtain ⟨participation, rfl, -⟩ := foldlM_translateAttestation folded
        cases current
        · exact .inr (.inl ⟨state, _, flags, middleChain, upgradedOk, .refl _, found, set, rfl⟩)
        · -- The current list starts with no flag.
          obtain ⟨-, zeros, -⟩ := carryFields_of_lt_altair (config := config) (post := .altair)
            state (by decide) (by decide) (by decide) (by decide)
          simp only [epochFlags, ↓reduceIte] at found
          rw [zeros, Array.getElem?_replicate] at found
          split at found
          · cases found
            rw [hasFlag_zero] at set
            cases set
          · cases found
    | @block fork engine signed validateResult state post notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, post⟩ :=
        .block engine signed validateResult notDue computed
      obtain ⟨-, processed, -⟩ := applySignedBlock_ok computed
      have postSlot := processBlock_slot processed
      obtain ⟨first, attested, head, firstReads, folded, tail, -⟩ := processBlock_votes processed
      have attestedFlag : ∃ old, (epochFlags attested altair current)[index]? = some old ∧
          hasFlag old flagIndex = true := by
        cases current
        · exact tail.previousEpochParticipation altair index flags flagIndex found set
        · exact tail.currentEpochParticipation altair index flags flagIndex found set
      obtain ⟨old, oldFound, oldSet⟩ := attestedFlag
      simp only at postSlot ⊢
      rcases foldlM_processAttestation_flags altair folded current index old flagIndex oldFound
        oldSet with ⟨older, olderFound, olderSet⟩ |
        ⟨pre, attestation, suf, site, recorded, split, prefixOk, siteOk, siteSlot, epoch, flagged⟩
      · -- The flag was there before the block.
        have before : ∃ oldest, (epochFlags state altair current)[index]? = some oldest ∧
            hasFlag oldest flagIndex = true := by
          cases current
          · exact head.previousEpochParticipation altair index older flagIndex olderFound olderSet
          · exact head.currentEpochParticipation altair index older flagIndex olderFound olderSet
        obtain ⟨oldest, oldestFound, oldestSet⟩ := before
        rw [flagsEpoch_of_slot postSlot]
        exact (more altair current index oldest flagIndex oldestFound oldestSet).extend theStep
      · -- An attestation of the block set it.
        rw [flagsEpoch_of_slot postSlot, ← flagsEpoch_of_slot (firstReads.trans (Kept.sameReads siteSlot)).slot]
        exact .inr (.inr ⟨fork, engine, signed, validateResult, state, post, first, site, recorded,
          pre, suf,
          attestation, middleChain, notDue, computed, .refl _, head, split, prefixOk, siteOk,
          firstReads.trans (Kept.sameReads siteSlot), epoch, flagged⟩)

end EthLib.Consensus
