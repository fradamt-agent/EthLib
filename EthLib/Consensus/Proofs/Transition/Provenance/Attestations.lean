module

public import EthLib.Consensus.Proofs.Transition.Provenance.Votes

/-!
# Proofs: what one attestation of a block records

An attestation of a block is checked on the state where the block runs it, its site.

Its signature is that of its indexed attestation: the attesters and the data.

The check passes at the site, so the state records a vote only for a checked attestation.

- Before Altair, the attestation joins the pending attestations, with its bits and data.
- From Altair, each attester gains the flags that the attestation earned at the site.

A flag is one bit of a byte, at its index modulo 8.

So a statement about a flag says which earned index sets the same bit.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Flags as bits -/

/-- A flag is the bit at its index modulo 8. -/
theorem flagBit_toBitVec (flagIndex : UInt64) :
    (flagBit flagIndex).toBitVec = BitVec.twoPow 8 (flagIndex.toNat % 8) := by
  unfold flagBit
  rw [UInt8.toBitVec_shiftLeft]
  ext i inside
  simp
  by_cases below : i < flagIndex.toNat % 8 <;> simp [below] <;> omega

/-- A flag is set when the bit at its index modulo 8 is set. -/
theorem hasFlag_eq_getLsbD (flags : ParticipationFlags) (flagIndex : UInt64) :
    hasFlag flags flagIndex = flags.toBitVec.getLsbD (flagIndex.toNat % 8) := by
  unfold hasFlag
  have masked : (flags &&& flagBit flagIndex == flagBit flagIndex) =
      decide (flags.toBitVec &&& BitVec.twoPow 8 (flagIndex.toNat % 8) =
        BitVec.twoPow 8 (flagIndex.toNat % 8)) := by
    rw [← flagBit_toBitVec, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff,
      ← UInt8.toBitVec_and, UInt8.toBitVec_inj]
  rw [masked, BitVec.and_twoPow]
  split
  · simp_all
  · simp_all only [decide_eq_false_iff_not]
    -- The bit is inside the byte, so its power of two is not zero.
    intro zero
    have bit := congrArg (·.getLsbD (flagIndex.toNat % 8)) zero
    simp only [BitVec.getLsbD_zero, BitVec.getLsbD_twoPow] at bit
    have : flagIndex.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
    simp_all

/-- Setting a flag sets exactly the bit of its index modulo 8. -/
theorem hasFlag_addFlag_eq (flags : ParticipationFlags) (added flagIndex : UInt64) :
    hasFlag (addFlag flags added) flagIndex =
      (hasFlag flags flagIndex || decide (added.toNat % 8 = flagIndex.toNat % 8)) := by
  simp only [addFlag, hasFlag_eq_getLsbD, UInt8.toBitVec_or, BitVec.getLsbD_or,
    flagBit_toBitVec, BitVec.getLsbD_twoPow]
  have : flagIndex.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  have : added.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
  simp [*]

/-! ## Flags set by one attestation -/

/-- The flags of one epoch after an attestation, from those before it.

Each flag after it was set before it, or the validator attested.

Then the attestation earned a flag index with the same bit. -/
def FlagsAddedBy (before after : Array ParticipationFlags) (attesters : List ValidatorIndex)
    (earned : List UInt64) : Prop :=
  ∀ (index : Nat) (flags : ParticipationFlags) (flagIndex : UInt64),
    after[index]? = some flags → hasFlag flags flagIndex = true →
      (∃ old, before[index]? = some old ∧ hasFlag old flagIndex = true) ∨
        ((∃ attester ∈ attesters, attester.toNat = index) ∧
          ∃ added ∈ earned, added.toNat % 8 = flagIndex.toNat % 8)

/-- The flags of one attester, after the flags its attestation earned. -/
theorem foldlM_addFlagReward {total numerator numerator' : Gwei} {earned : List UInt64}
    {index : ValidatorIndex} {flags flags' : ParticipationFlags}
    {list : List (Fin PARTICIPATION_FLAG_WEIGHTS.length)}
    (computed : list.foldlM (addFlagReward state total earned index) (flags, numerator) =
      .ok (flags', numerator')) (flagIndex : UInt64) (set : hasFlag flags' flagIndex = true) :
    hasFlag flags flagIndex = true ∨ ∃ added ∈ earned, added.toNat % 8 = flagIndex.toNat % 8 := by
  induction list generalizing flags numerator with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, -⟩ := computed
    exact .inl set
  | cons flag rest more =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middle, middleNumerator⟩, step, folded⟩ := computed
    rcases more folded with old | new
    · unfold addFlagReward at step
      dsimp only at step
      by_cases earnedFlag : flag.val.toUInt64 ∈ earned ∧ hasFlag flags flag.val.toUInt64 = false
      · simp only [earnedFlag, and_self, ↓reduceIte] at step
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at step
        obtain ⟨_, _, _, _, _, _, rfl, -⟩ := step
        rw [hasFlag_addFlag_eq, Bool.or_eq_true, decide_eq_true_iff] at old
        rcases old with old | same
        · exact .inl old
        · exact .inr ⟨_, earnedFlag.1, same⟩
      · simp only [earnedFlag, ↓reduceIte] at step
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at step
        obtain ⟨rfl, -⟩ := step
        exact .inl old
    · exact .inr new

/-- The flags of an epoch after its attesters gain their earned flags. -/
theorem foldlM_addAttesterFlags_added {total numerator numerator' : Gwei} {earned : List UInt64}
    {participation participation' : EpochParticipation preset fork}
    {attesters : List ValidatorIndex}
    (computed : attesters.foldlM (addAttesterFlags state total earned) (participation, numerator) =
      .ok (participation', numerator')) :
    FlagsAddedBy participation.data participation'.data attesters earned := by
  induction attesters generalizing participation numerator with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, -⟩ := computed
    exact fun _ flags _ found set => .inl ⟨flags, found, set⟩
  | cons attester rest more =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middle, middleNumerator⟩, step, folded⟩ := computed
    intro index flags flagIndex found set
    rcases more folded index flags flagIndex found set with ⟨old, oldFound, oldSet⟩ | ⟨mem, added⟩
    · unfold addAttesterFlags at step
      dsimp only at step
      by_cases inside : attester.toNat < participation.data.size
      · simp only [inside, ↓reduceDIte] at step
        simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at step
        obtain ⟨⟨written, _⟩, writtenOk, rfl, -⟩ := step
        simp only [Array.getElem?_set] at oldFound
        split at oldFound
        · next here =>
          cases oldFound
          rcases foldlM_addFlagReward writtenOk flagIndex oldSet with before | added
          · exact .inl ⟨_, by rw [← here]; exact Array.getElem?_eq_getElem inside, before⟩
          · exact .inr ⟨⟨attester, List.mem_cons_self, here⟩, added⟩
        · exact .inl ⟨old, oldFound, oldSet⟩
      · simp only [inside, ↓reduceDIte] at step
        cases step
    · obtain ⟨other, member, same⟩ := mem
      exact .inr ⟨⟨other, List.mem_cons_of_mem _ member, same⟩, added⟩

/-- Writing the flags of one epoch keeps the other epoch's flags and the pending attestations. -/
theorem setEpochParticipation_votes (current : Bool)
    (participation : EpochParticipation preset fork) :
    let after := setEpochParticipation state current participation
    after.previousEpochAttestations = state.previousEpochAttestations ∧
      after.currentEpochAttestations = state.currentEpochAttestations ∧
      (∀ altair : .altair ≤ fork, after.currentEpochParticipation altair =
        if current then participation else state.currentEpochParticipation altair) ∧
      (∀ altair : .altair ≤ fork, after.previousEpochParticipation altair =
        if current then state.previousEpochParticipation altair else participation) := by
  cases current <;> exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-- From Altair, what one attestation records, and where it was checked.

The attestation's indexed form is valid on the state where it runs, its site.

Its target is the previous or the current epoch of the site.

The attesters gain flags in the list of the target's epoch, from the flags that it earned.

The other list gains no flag, and the pending attestations stay. -/
theorem processAttestationAltair_votes {attestation : Attestation preset fork}
    {altair : .altair ≤ fork} {parentSlot : Slot}
    (computed :
      processAttestationAltair config checks state attestation altair parentSlot = .ok after) :
    ∃ earned attesters indexed,
      getAttestationParticipationFlagIndices state attestation.data
        (state.slot - attestation.data.slot) parentSlot = .ok earned ∧
      getAttestingIndices state attestation = .ok attesters ∧
      getIndexedAttestation state attestation = .ok indexed ∧
      isValidIndexedAttestation config checks state indexed = .ok true ∧
      (attestation.data.target.epoch = getPreviousEpoch state ∨
        attestation.data.target.epoch = getCurrentEpoch state) ∧
      after.previousEpochAttestations = state.previousEpochAttestations ∧
      after.currentEpochAttestations = state.currentEpochAttestations ∧
      (if attestation.data.target.epoch = getCurrentEpoch state then
        FlagsAddedBy (state.currentEpochParticipation altair).data
            (after.currentEpochParticipation altair).data attesters earned ∧
          FlagsWithin (state.previousEpochParticipation altair).data
            (after.previousEpochParticipation altair).data
      else
        FlagsAddedBy (state.previousEpochParticipation altair).data
            (after.previousEpochParticipation altair).data attesters earned ∧
          FlagsWithin (state.currentEpochParticipation altair).data
            (after.currentEpochParticipation altair).data) := by
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, recent, _, _, _, _, _, _, _, _, _, _, earned, earnedOk, indexed, indexedOk, valid,
    validOk, _, validTrue, total, _, attesters, attestersOk, ⟨updated, numerator⟩, folded, _, _,
    raised, raisedOk, final⟩ := computed
  subst validTrue
  -- The flags are written once, and the last two steps keep every vote.
  have last : VotesKept (setEpochParticipation state
      (attestation.data.target.epoch == getCurrentEpoch state) updated) after := by
    have rest : VotesKept raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_votes rfl
      · cases final
        exact VotesKept.refl _
    exact (votesKept_increaseBalance raisedOk).trans rest
  have added := foldlM_addAttesterFlags_added folded
  simp only [beq_iff_eq] at added
  obtain ⟨previousPending, currentPending, currentFlags, previousFlags⟩ :=
    setEpochParticipation_votes (state := state)
      (attestation.data.target.epoch == getCurrentEpoch state) updated
  refine ⟨earned, attesters, indexed, earnedOk, attestersOk, indexedOk, validOk, recent,
    last.previousEpochAttestations.trans previousPending,
    last.currentEpochAttestations.trans currentPending, ?_⟩
  have currentLast := last.currentEpochParticipation altair
  have previousLast := last.previousEpochParticipation altair
  rw [currentFlags altair] at currentLast
  rw [previousFlags altair] at previousLast
  by_cases isCurrent : attestation.data.target.epoch = getCurrentEpoch state
  · simp only [isCurrent, beq_self_eq_true, ↓reduceIte] at currentLast previousLast ⊢
    simp only [isCurrent, ↓reduceIte] at added
    -- The list of the current epoch gained the flags, then lost none it did not have.
    refine ⟨fun index flags flagIndex found set => ?_, previousLast⟩
    obtain ⟨middle, middleFound, middleSet⟩ := currentLast index flags flagIndex found set
    exact added index middle flagIndex middleFound middleSet
  · have notCurrent : (attestation.data.target.epoch == getCurrentEpoch state) = false := by
      simpa using isCurrent
    simp only [isCurrent, ↓reduceIte] at added
    simp only [isCurrent, notCurrent, Bool.false_eq_true, ↓reduceIte] at currentLast previousLast ⊢
    refine ⟨fun index flags flagIndex found set => ?_, currentLast⟩
    obtain ⟨middle, middleFound, middleSet⟩ := previousLast index flags flagIndex found set
    exact added index middle flagIndex middleFound middleSet

/-- Recording a pending attestation changes nothing that the check of an attestation reads. -/
theorem recordPendingAttestation_reads {before : fork < .altair} {current : Bool}
    {pending : PendingAttestation preset} {attestation : Attestation preset fork}
    (computed : recordPendingAttestation state before current pending = .ok after) :
    getIndexedAttestation after attestation = getIndexedAttestation state attestation ∧
      ∀ indexed, isValidIndexedAttestation config checks after indexed =
        isValidIndexedAttestation config checks state indexed := by
  -- Before Electra the attesters come from one committee, which reads no pending attestation.
  have notElectra : ¬Fork.pectra ≤ fork := Nat.not_le_of_lt (Nat.lt_trans before (by decide))
  cases current <;>
    simp only [recordPendingAttestation, Bool.false_eq_true, ↓reduceIte] at computed <;>
    split at computed <;> cases computed <;>
    refine ⟨?_, fun _ => rfl⟩ <;>
    simp only [getIndexedAttestation, getAttestingIndices, notElectra, ↓reduceDIte] <;> rfl

/-- Before Altair, what one attestation records, and where it was checked.

The attestation's indexed form is valid on the state where it runs, its site.

It joins the pending attestations of its target's epoch, with its bits and data.

The flags, which no state before Altair has, stay. -/
theorem processAttestation_pending {attestation : Attestation preset fork} {parentSlot : Slot}
    (before : fork < .altair)
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ∃ pending : PendingAttestation preset, ∃ indexed,
      pending.aggregationBits.bits = attestation.aggregationBits.bits ∧
      pending.data = attestation.data ∧
      pending.inclusionDelay = state.slot - attestation.data.slot ∧
      getBeaconProposerIndex state = .ok pending.proposerIndex ∧
      getIndexedAttestation state attestation = .ok indexed ∧
      isValidIndexedAttestation config checks state indexed = .ok true ∧
      (if attestation.data.target.epoch = getCurrentEpoch state then
        (after.currentEpochAttestations before).data =
            (state.currentEpochAttestations before).data.push pending ∧
          after.previousEpochAttestations = state.previousEpochAttestations
      else
        (after.previousEpochAttestations before).data =
            (state.previousEpochAttestations before).data.push pending ∧
          after.currentEpochAttestations = state.currentEpochAttestations) := by
  obtain ⟨pending, bits, data, delay, proposer, recorded, indexed, indexedOk, valid⟩ :=
    processAttestation_records before computed
  have kept := recordPendingAttestation_ok recorded
  have reads := recordPendingAttestation_reads (config := config) (checks := checks)
    (attestation := attestation) recorded
  by_cases isCurrent : attestation.data.target.epoch = getCurrentEpoch state
  · simp only [isCurrent, beq_self_eq_true, ↓reduceIte] at kept ⊢
    obtain ⟨pushed, rest⟩ := kept
    -- Recording the attestation changes only the pending list, which the check does not read.
    rw [← reads.1]
    exact ⟨pending, indexed, bits, data, delay, proposer, indexedOk, (reads.2 indexed) ▸ valid,
      pushed, by rw [← rest]⟩
  · have notCurrent : (attestation.data.target.epoch == getCurrentEpoch state) = false := by
      simpa using isCurrent
    simp only [isCurrent, notCurrent, Bool.false_eq_true, ↓reduceIte] at kept ⊢
    obtain ⟨pushed, rest⟩ := kept
    rw [← reads.1]
    exact ⟨pending, indexed, bits, data, delay, proposer, indexedOk, (reads.2 indexed) ▸ valid,
      pushed, by rw [← rest]⟩

end EthLib.Consensus
