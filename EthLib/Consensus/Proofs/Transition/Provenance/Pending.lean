module

public import EthLib.Consensus.Proofs.Transition.Provenance.Flags

/-!
# Proofs: where the pending attestations of a chain come from

Before Altair a state holds the attestations that blocks included, for two epochs.

A pending attestation of the current epoch's list votes for the current epoch, and likewise for
the previous one.

This file traces each pending attestation of a chain's end to the block that included it.

It holds the bits and the data of an attestation of that block.

That attestation ran at its site, where its indexed form was valid, so its signature was checked.

Its target is the epoch of the list that holds it.

The end of an epoch moves the current list to the previous one, so the epoch follows the list.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The pending attestations of one epoch: the current one, or the previous one. -/
def epochPending (state : BeaconState preset fork) (before : fork < .altair) (current : Bool) :
    Array (PendingAttestation preset) :=
  if current then (state.currentEpochAttestations before).data
  else (state.previousEpochAttestations before).data

/-- At a site, an attestation was recorded as a pending attestation, and its indexed form was
valid.

The pending attestation holds its bits and data, its inclusion delay and the proposer. -/
def AttestationRecorded (config : Config) (checks : SignatureChecks)
    (site : BeaconState preset fork) (attestation : Attestation preset fork)
    (pending : PendingAttestation preset) : Prop :=
  ∃ indexed,
    pending.aggregationBits.bits = attestation.aggregationBits.bits ∧
    pending.data = attestation.data ∧
    pending.inclusionDelay = site.slot - attestation.data.slot ∧
    getBeaconProposerIndex site = .ok pending.proposerIndex ∧
    getIndexedAttestation site attestation = .ok indexed ∧
    isValidIndexedAttestation config checks site indexed = .ok true

/-- The pending attestations after the attestations of a block come from before them, or from
one of them.

That attestation ran at a state of the block's slot, and wrote the list of its target's epoch. -/
theorem foldlM_processAttestation_pending (before : fork < .altair) {parentSlot : Slot} :
    ∀ {attestations : List (Attestation preset fork)} {first attested : BeaconState preset fork},
      attestations.foldlM (processAttestation config checks · parentSlot ·) first =
        .ok attested →
      ∀ (current : Bool) (pending : PendingAttestation preset),
        pending ∈ epochPending attested before current →
        pending ∈ epochPending first before current ∨
        ∃ pre attestation suf site recorded,
          attestations = pre ++ attestation :: suf ∧
          pre.foldlM (processAttestation config checks · parentSlot ·) first = .ok site ∧
          processAttestation config checks site parentSlot attestation = .ok recorded ∧
          Kept first site ∧ attestation.data.target.epoch = flagsEpoch site current ∧
          AttestationRecorded config checks site attestation pending
  | [], first, attested, computed, _, _, member => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .inl member
  | attestation :: rest, first, attested, computed, current, pending, member => by
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, folded⟩ := computed
    rcases foldlM_processAttestation_pending before folded current pending member with old |
      ⟨pre, later, suf, site, recorded, split, prefixOk, laterOk, siteSlot, epoch, written⟩
    · -- The attestation was there after this one: it was there before, or this one wrote it.
      obtain ⟨written, indexed, bits, data, delay, proposer, indexedOk, valid, lists⟩ :=
        processAttestation_pending before step
      have checked := processAttestation_checks before step
      have origin : pending ∈ epochPending first before current ∨
          (attestation.data.target.epoch = flagsEpoch first current ∧ pending = written) := by
        unfold epochPending flagsEpoch at *
        by_cases isCurrent : attestation.data.target.epoch = getCurrentEpoch first
        · simp only [isCurrent, ↓reduceIte] at lists
          cases current
          · simp only [Bool.false_eq_true, ↓reduceIte] at old ⊢
            rw [lists.2] at old
            exact .inl old
          · simp only [↓reduceIte] at old ⊢
            rw [lists.1, Array.mem_push] at old
            exact old.imp id fun same => ⟨isCurrent, same⟩
        · simp only [isCurrent, ↓reduceIte] at lists
          have previous : attestation.data.target.epoch = getPreviousEpoch first :=
            checked.1.resolve_right isCurrent
          cases current
          · simp only [Bool.false_eq_true, ↓reduceIte] at old ⊢
            rw [lists.1, Array.mem_push] at old
            exact old.imp id fun same => ⟨previous, same⟩
          · simp only [↓reduceIte] at old ⊢
            rw [lists.2] at old
            exact .inl old
      rcases origin with before | ⟨epoch, rfl⟩
      · exact .inl before
      · exact .inr ⟨[], attestation, rest, first, middle, rfl, rfl, step, Kept.refl _, epoch,
          indexed, bits, data, delay, proposer, indexedOk, valid⟩
    · -- A later attestation wrote it, from a state at the same slot.
      refine .inr ⟨attestation :: pre, later, suf, site, recorded, by rw [split]; rfl, ?_, laterOk,
        (kept_processAttestation step).trans siteSlot, epoch, written⟩
      simp only [List.foldlM_cons, bind_ok_iff]
      exact ⟨middle, step, prefixOk⟩

/-! ## Along a chain -/

/-- The start of a chain held a pending attestation, in one of its two lists. -/
def PendingAtStart (start : ForkedBeaconState preset) (pending : PendingAttestation preset) :
    Prop :=
  ∃ (before : start.fork < .altair) (current : Bool),
    pending ∈ epochPending start.state before current

/-- A block of a chain included an attestation, recorded as a pending attestation.

The attestation ran at `site`, a state of the block's slot, after the attestations before it.

The steps of the block before the attestations kept the inputs of the shuffles near its epoch.

Its target is `epoch`, and its indexed form was valid there. -/
def PendingRecordedBy (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) (pending : PendingAttestation preset) (epoch : Epoch) :
    Prop :=
  ∃ (fork : Fork) (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
    (validateResult : Bool) (state post first site recorded : BeaconState preset fork)
    (pre suf : List (Attestation preset fork)) (attestation : Attestation preset fork),
    Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
    applySignedBlock config checks engine state signed validateResult = .ok post ∧
    Reaches config checks ⟨fork, post⟩ after ∧
    VotesKept state first ∧ ShuffleKeptNear state first ∧
    signed.message.body.attestations.data.toList = pre ++ attestation :: suf ∧
    pre.foldlM (processAttestation config checks · state.latestBlockHeader.slot ·) first =
      .ok site ∧
    processAttestation config checks site state.latestBlockHeader.slot attestation = .ok recorded ∧
    SameReads state site ∧ attestation.data.target.epoch = epoch ∧
    AttestationRecorded config checks site attestation pending

/-- Where a pending attestation of a chain's end came from. -/
def PendingOrigin (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) (pending : PendingAttestation preset) (epoch : Epoch) :
    Prop :=
  PendingAtStart start pending ∨ PendingRecordedBy config checks start after pending epoch

theorem PendingOrigin.extend {start middle after : ForkedBeaconState preset}
    {pending : PendingAttestation preset} {epoch : Epoch}
    (origin : PendingOrigin config checks start middle pending epoch)
    (step : Step config checks middle after) :
    PendingOrigin config checks start after pending epoch := by
  rcases origin with atStart | ⟨fork, engine, signed, validateResult, state, post, first, site,
    recorded, pre, suf, attestation, head, notDue, applied, tail, rest⟩
  · exact .inl atStart
  · exact .inr ⟨fork, engine, signed, validateResult, state, post, first, site, recorded, pre,
      suf, attestation, head, notDue, applied, tail.step step, rest⟩

/-- Where the pending attestations of a chain's end come from.

Each pending attestation, in the list of an epoch, was held by the start of the chain.

Or a block of the chain included an attestation with that epoch as its target, and recorded it.
-/
theorem Reaches.pending {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) (before : after.fork < .altair) (current : Bool)
    {pending : PendingAttestation preset} (member : pending ∈ epochPending after.state before current) :
    PendingOrigin config checks start after pending (flagsEpoch after.state current) := by
  obtain ⟨run⟩ := chain
  induction run generalizing current pending with
  | nil => exact .inl ⟨before, current, member⟩
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
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
      simp only at member stepSlot before ⊢
      unfold epochIfLast at epochedOk
      rw [nextIs] at epochedOk
      by_cases closes : ClosesEpoch preset state
      · have last : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := closes
        simp only [last, ↓reduceIte] at epochedOk
        obtain ⟨kept, rotated, head, rotates, tail⟩ := processEpoch_votes epochedOk
        cases current
        · -- The previous list after the step is the current list before it.
          simp only [epochPending, Bool.false_eq_true, ↓reduceIte] at member
          rw [tail.previousEpochAttestations, rotates.previousEpochAttestations before,
            head.currentEpochAttestations] at member
          have origin := more before true (pending := pending) (by
            simp only [epochPending, ↓reduceIte]
            exact member)
          have epoch : flagsEpoch { epoched with slot := nextSlot } false =
              flagsEpoch state true :=
            getPreviousEpoch_of_closes stepSlot closes
          rw [epoch]
          exact origin.extend theStep
        · -- The current list after the step is empty.
          simp only [epochPending, ↓reduceIte] at member
          rw [tail.currentEpochAttestations, rotates.currentEpochAttestations before] at member
          simp at member
      · have notLast : ¬(state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := closes
        simp only [notLast, ↓reduceIte] at epochedOk
        cases epochedOk
        rw [flagsEpoch_of_open stepSlot closes]
        exact (more before current member).extend theStep
    | @upgrade _ post due computed =>
      -- Every upgrade leads to Altair or a later fork.
      exfalso
      obtain ⟨fork, state⟩ := middle
      cases fork <;>
        simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
          throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
      all_goals
        obtain ⟨_, _, rfl⟩ := computed
        exact absurd before (by dsimp only; decide)
    | @block fork engine signed validateResult state post notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, post⟩ :=
        .block engine signed validateResult notDue computed
      obtain ⟨-, processed, -⟩ := applySignedBlock_ok computed
      have postSlot := processBlock_slot processed
      obtain ⟨first, attested, head, firstReads, folded, tail, shuffle⟩ :=
        processBlock_votes processed
      simp only at member postSlot before ⊢
      have attestedMember : pending ∈ epochPending attested before current := by
        cases current
        · simpa only [epochPending, Bool.false_eq_true, ↓reduceIte, tail.previousEpochAttestations]
            using member
        · simpa only [epochPending, ↓reduceIte, tail.currentEpochAttestations] using member
      rcases foldlM_processAttestation_pending before folded current pending attestedMember with
        firstMember | ⟨pre, attestation, suf, site, recorded, split, prefixOk, siteOk, siteSlot,
          epoch, written⟩
      · -- The attestation was there before the block.
        have stateMember : pending ∈ epochPending state before current := by
          cases current
          · simpa only [epochPending, Bool.false_eq_true, ↓reduceIte,
              head.previousEpochAttestations] using firstMember
          · simpa only [epochPending, ↓reduceIte, head.currentEpochAttestations] using firstMember
        rw [flagsEpoch_of_slot postSlot]
        exact (more before current stateMember).extend theStep
      · -- An attestation of the block recorded it.
        rw [flagsEpoch_of_slot postSlot, ← flagsEpoch_of_slot (firstReads.trans (Kept.sameReads siteSlot)).slot]
        exact .inr ⟨fork, engine, signed, validateResult, state, post, first, site, recorded,
          pre, suf, attestation, middleChain, notDue, computed, .refl _, head, shuffle, split,
          prefixOk,
          siteOk, firstReads.trans (Kept.sameReads siteSlot), epoch, written⟩

end EthLib.Consensus
