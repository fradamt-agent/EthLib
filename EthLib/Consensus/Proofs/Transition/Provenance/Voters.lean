module

public import EthLib.Consensus.Proofs.Participation
public import EthLib.Consensus.Proofs.Transition.Provenance.Flags

/-!
# Proofs: the voters of a weighing call signed attestations

From Altair a weighing call counts the validators with the timely-target flag of an epoch.

Each such flag was set by an attestation that a block of the chain included.

That attestation ran at its site, where the call that set the flag checked three things.

- Its source was the justified checkpoint of its target's epoch, at the site.
- Its target root was the root the site held for the first slot of the target's epoch.
- Its indexed form, which names the voter among its attesters, was valid.

So each voter signed attestation data with the call's target epoch, checked at an actual site.

Two other origins remain possible, and the statement keeps them.

- The start of the chain already had the flag.
- The flag came from the upgrade to Altair, which turns pending attestations into flags.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- An attestation earns the timely-target flag only when its target root is the state's.

That is the state's root for the first slot of its target's epoch. -/
theorem getAttestationParticipationFlagIndices_target {data : AttestationData}
    {inclusionDelay : UInt64} {parentSlot : Slot} {flags : List UInt64}
    (computed :
      getAttestationParticipationFlagIndices state data inclusionDelay parentSlot = .ok flags)
    (target : TIMELY_TARGET_FLAG_INDEX ∈ flags) :
    getBlockRoot state data.target.epoch = .ok data.target.root := by
  unfold getAttestationParticipationFlagIndices at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨root, rootOk, _, _, _, _, computed⟩ := computed
  by_cases matching : data.source = (if data.target.epoch = getCurrentEpoch state then
      state.currentJustifiedCheckpoint else state.previousJustifiedCheckpoint)
  · rw [ite_eq_left_of_eq_true _ _ (eq_true matching)] at computed
    cases computed
    simp only [List.mem_append] at target
    rcases target with (source | target) | head
    · split at source <;> simp_all [TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX]
    · split at target <;> split at target <;> simp_all
    · split at head <;> simp_all [TIMELY_HEAD_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false matching)] at computed
    cases computed

/-- An earned flag index that sets the target bit is the timely-target flag index. -/
theorem earned_target {data : AttestationData} {inclusionDelay : UInt64} {parentSlot : Slot}
    {flags : List UInt64}
    (computed :
      getAttestationParticipationFlagIndices state data inclusionDelay parentSlot = .ok flags)
    {added : UInt64} (member : added ∈ flags)
    (bit : added.toNat % 8 = TIMELY_TARGET_FLAG_INDEX.toNat % 8) :
    added = TIMELY_TARGET_FLAG_INDEX := by
  have within := (getAttestationParticipationFlagIndices_spec computed).2.subset member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at within
  rcases within with rfl | rfl | rfl
  · simp [TIMELY_SOURCE_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX] at bit
  · rfl
  · simp [TIMELY_HEAD_FLAG_INDEX, TIMELY_TARGET_FLAG_INDEX] at bit

/-- A block of a chain included an attestation that a validator signed, with this data.

The attestation ran at `site`, a state of the block's slot, after the attestations before it.

Its indexed form names the validator among its attesters, and is valid at the site.

Its source is the justified checkpoint of its target's epoch at the site.

Its target root is the site's root for the first slot of its target's epoch. -/
def SignedTarget (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset)
    (index : ValidatorIndex) (data : AttestationData) : Prop :=
  ∃ (fork : Fork) (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
    (validateResult : Bool) (state post first site recorded : BeaconState preset fork)
    (pre suf : List (Attestation preset fork)) (attestation : Attestation preset fork)
    (indexed : IndexedAttestation preset fork),
    Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
    applySignedBlock config checks engine state signed validateResult = .ok post ∧
    Reaches config checks ⟨fork, post⟩ after ∧
    VotesKept state first ∧
    signed.message.body.attestations.data.toList = pre ++ attestation :: suf ∧
    pre.foldlM (processAttestation config checks · state.latestBlockHeader.slot ·) first =
      .ok site ∧
    processAttestation config checks site state.latestBlockHeader.slot attestation = .ok recorded ∧
    SameReads state site ∧ attestation.data = data ∧
    getIndexedAttestation site attestation = .ok indexed ∧ index ∈ indexed.attestingIndices.data ∧
    indexed.data = data ∧ isValidIndexedAttestation config checks site indexed = .ok true ∧
    data.source = (if data.target.epoch = getCurrentEpoch site then site.currentJustifiedCheckpoint
      else site.previousJustifiedCheckpoint) ∧
    getBlockRoot site data.target.epoch = .ok data.target.root

/-- A validator signed attestation data, checked at an actual site of a chain.

This is `SignedTarget` without its last fact, the read of the target root at the site.

Before Altair the inclusion does not read the target root: the weighing call compares it.

A block step of the chain included an attestation with that data.

The attestation ran at `site`, a state of the block's slot, after the attestations before it.

Its indexed form names the validator among its attesters, and is valid at the site.

Its source is the justified checkpoint of its target's epoch at the site. -/
def SignedVote (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset)
    (index : ValidatorIndex) (data : AttestationData) : Prop :=
  ∃ (fork : Fork) (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
    (validateResult : Bool) (state post first site recorded : BeaconState preset fork)
    (pre suf : List (Attestation preset fork)) (attestation : Attestation preset fork)
    (indexed : IndexedAttestation preset fork),
    Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
    applySignedBlock config checks engine state signed validateResult = .ok post ∧
    Reaches config checks ⟨fork, post⟩ after ∧
    VotesKept state first ∧
    signed.message.body.attestations.data.toList = pre ++ attestation :: suf ∧
    pre.foldlM (processAttestation config checks · state.latestBlockHeader.slot ·) first =
      .ok site ∧
    processAttestation config checks site state.latestBlockHeader.slot attestation = .ok recorded ∧
    SameReads state site ∧ attestation.data = data ∧
    getIndexedAttestation site attestation = .ok indexed ∧ index ∈ indexed.attestingIndices.data ∧
    indexed.data = data ∧ isValidIndexedAttestation config checks site indexed = .ok true ∧
    data.source = (if data.target.epoch = getCurrentEpoch site then site.currentJustifiedCheckpoint
      else site.previousJustifiedCheckpoint)

theorem SignedTarget.vote {start after : ForkedBeaconState preset} {index : ValidatorIndex}
    {data : AttestationData} (signed : SignedTarget config checks start after index data) :
    SignedVote config checks start after index data :=
  have ⟨fork, engine, block, validateResult, state, post, first, site, recorded, pre, suf,
    attestation, indexed, head, notDue, applied, tail, kept, split, prefixOk, siteOk, reads,
    sameData, indexedOk, attesting, indexedData, valid, source, _⟩ := signed
  ⟨fork, engine, block, validateResult, state, post, first, site, recorded, pre, suf, attestation,
    indexed, head, notDue, applied, tail, kept, split, prefixOk, siteOk, reads, sameData, indexedOk,
    attesting, indexedData, valid, source⟩

/-- From Altair, a counted voter of a weighing call signed data with the call's target epoch.

Take a weighing call of a chain, at a fork from Altair on, that reads `cached`.

Each voter counted for an epoch had its timely-target flag in `cached`.

That flag was set at the start of the chain, or by the upgrade to Altair.

Otherwise the voter signed attestation data with that target epoch, checked at an actual site.
-/
theorem TargetVoters.origin {start : ForkedBeaconState preset} {checkpoint : Checkpoint}
    {fork : Fork} {state cached : BeaconState preset fork}
    {voters : List ValidatorIndex} (altair : .altair ≤ fork)
    (head : Reaches config checks start ⟨fork, state⟩)
    (reads : ReadsFrom state cached)
    (recent : checkpoint.epoch = getPreviousEpoch cached ∨
      checkpoint.epoch = getCurrentEpoch cached)
    (counted : TargetVoters cached checkpoint.epoch voters)
    {index : ValidatorIndex} (member : index ∈ voters) :
    FlagAtStart start index.toNat TIMELY_TARGET_FLAG_INDEX ∨
      FlagFromAltairUpgrade config checks start ⟨fork, state⟩ index.toNat
        TIMELY_TARGET_FLAG_INDEX checkpoint.epoch ∨
      ∃ data, data.target.epoch = checkpoint.epoch ∧
        SignedTarget config checks start ⟨fork, state⟩ index data := by
  simp only [TargetVoters, altair, ↓reduceDIte] at counted
  obtain ⟨-, -, flags, found, set⟩ := mem_getUnslashedParticipatingIndices counted index member
  -- The caching keeps the flags and the slot, so the voter had the flag before it.
  have epochSame : getCurrentEpoch cached = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [reads.slot]
  have flagsSame :
      cached.currentEpochParticipation altair = state.currentEpochParticipation altair ∧
      cached.previousEpochParticipation altair = state.previousEpochParticipation altair := by
    obtain ⟨_, _, _, _, same⟩ := reads.eq
    subst same
    exact ⟨rfl, rfl⟩
  rw [epochSame, flagsSame.1, flagsSame.2] at found
  have previousSame : getPreviousEpoch cached = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [epochSame]
  rw [epochSame, previousSame] at recent
  have current : flagsEpoch state (decide (checkpoint.epoch = getCurrentEpoch state)) =
      checkpoint.epoch := by
    unfold flagsEpoch
    by_cases isCurrent : checkpoint.epoch = getCurrentEpoch state
    · simp [isCurrent]
    · simp only [isCurrent, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact (recent.resolve_right isCurrent).symm
  have listed : (epochFlags state altair (decide (checkpoint.epoch = getCurrentEpoch state)))[
      index.toNat]? = some flags := by
    unfold epochFlags
    by_cases isCurrent : checkpoint.epoch = getCurrentEpoch state
    · simpa [isCurrent] using found
    · simpa [isCurrent] using found
  have origin := head.flags altair _ index.toNat flags _ listed set
  rw [current] at origin
  rcases origin with atStart | upgraded | ⟨fork', engine, signed, validateResult, state', post,
    first, site, recorded, pre, suf, attestation, chain, notDue, applied, tail, kept, split,
    prefixOk, siteOk, siteSlot, epoch, earned, attesters, indexed, earnedOk, attestersOk,
    ⟨attester, attesterMember, sameIndex⟩, ⟨added, addedMember, bit⟩, indexedOk, valid⟩
  · exact .inl atStart
  · exact .inr (.inl upgraded)
  · refine .inr (.inr ⟨attestation.data, epoch, fork', engine, signed, validateResult, state',
      post, first, site, recorded, pre, suf, attestation, ?_⟩)
    have targetEarned := earned_target earnedOk addedMember bit
    subst targetEarned
    obtain ⟨indexed', indexedOk', attesting, sameData, -⟩ :=
      getIndexedAttestation_of_getAttestingIndices attestersOk
    cases indexedOk.symm.trans indexedOk'
    have sameAttester : attester = index := UInt64.toNat_inj.mp sameIndex
    subst sameAttester
    exact ⟨indexed, chain, notDue, applied, tail, kept, split, prefixOk, siteOk, siteSlot, rfl,
      indexedOk, by rw [attesting]; exact List.mem_toArray.mpr attesterMember, sameData, valid,
      (getAttestationParticipationFlagIndices_spec earnedOk).1,
      getAttestationParticipationFlagIndices_target earnedOk addedMember⟩

/-- The record of a weighing call that justified a checkpoint, with the origin of its voters.

From Altair each counted voter signed data with the checkpoint's epoch as target, at a site.

Or its flag came from the start or from the upgrade to Altair.

Before Altair the voters come from pending attestations; this statement says nothing of them. -/
theorem JustifiedBy.voters {start after : ForkedBeaconState preset} {checkpoint : Checkpoint}
    (justified : JustifiedBy config checks start after checkpoint) :
    ∃ (fork : Fork) (state cached : BeaconState preset fork) (voters : List ValidatorIndex),
      Reaches config checks start ⟨fork, state⟩ ∧
      Reaches config checks ⟨fork, state⟩ after ∧ processSlot state = .ok cached ∧
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
      TargetVoters cached checkpoint.epoch voters ∧ PassesThreshold cached voters ∧
      getBlockRoot cached checkpoint.epoch = .ok checkpoint.root ∧
      (.altair ≤ fork → ∀ index ∈ voters,
        FlagAtStart start index.toNat TIMELY_TARGET_FLAG_INDEX ∨
        FlagFromAltairUpgrade config checks start ⟨fork, state⟩ index.toNat
          TIMELY_TARGET_FLAG_INDEX checkpoint.epoch ∨
        ∃ data, data.target.epoch = checkpoint.epoch ∧
          SignedTarget config checks start ⟨fork, state⟩ index data) := by
  obtain ⟨fork, state, cached, _, next, voters, head, notDue, nextOk, tail, _, cachedOk, _, _,
    recent, counted, passes, rootOk⟩ := justified
  exact ⟨fork, state, cached, voters, head,
    (Reaches.refl _).step (.slot notDue nextOk) |>.trans tail,
    cachedOk, recent, counted, passes, rootOk,
    fun altair _ member => TargetVoters.origin altair head (.inl cachedOk) recent counted member⟩

end EthLib.Consensus
