module

public import EthLib.Consensus.Proofs.Transition.Provenance.Links
public import EthLib.Consensus.Proofs.Transition.Provenance.Pending
public import EthLib.Consensus.Proofs.ShufflePermutation
import all Init.Data.List.Control

/-!
# Proofs: the counted voters of a weighing call before Altair

Before Altair a weighing call counts the signers of the pending attestations of an epoch.

It finds the signers from the bits of each pending attestation and a committee.

It computes that committee anew, in its own state.

This file shows that the committee is the one the inclusion of the attestation used.

So each counted voter is a signer of an attestation that a block of the chain included.

That attestation's indexed form was valid at its site.

The inputs of the committee stay fixed between the two, by `ShuffleKept`.

The site is in the target epoch or the one after, and so is the call.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Lists -/

/-- A member of a filtered list is a member of the list or of the start of the result. -/
theorem mem_of_filterAuxM_ok {α ε : Type} {p : α → Except ε Bool} :
    ∀ {items accumulated result : List α},
      List.filterAuxM p items accumulated = .ok result →
      ∀ x ∈ result, x ∈ items ∨ x ∈ accumulated
  | [], accumulated, result, computed, x, member => by
    simp only [List.filterAuxM] at computed
    simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact .inr (computed ▸ member)
  | head :: tail, accumulated, result, computed, x, member => by
    simp only [List.filterAuxM] at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨kept, _, rest⟩ := computed
    rcases mem_of_filterAuxM_ok rest x member with inTail | inAccumulated
    · exact .inl (List.mem_cons_of_mem _ inTail)
    · cases kept
      · exact .inr inAccumulated
      · rcases List.mem_cons.mp inAccumulated with rfl | inAccumulated
        · exact .inl List.mem_cons_self
        · exact .inr inAccumulated

/-- A member of a filtered list is a member of the list. -/
theorem mem_of_filterM_ok {α ε : Type} {p : α → Except ε Bool} {items result : List α}
    (computed : items.filterM p = .ok result) {x : α} (member : x ∈ result) : x ∈ items := by
  simp only [List.filterM] at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨reversed, auxOk, rfl⟩ := computed
  rcases mem_of_filterAuxM_ok auxOk x (List.mem_reverse.mp member) with inItems | inNil
  · exact inItems
  · cases inNil

/-! ## The counted voters before Altair -/

/-- Before Altair each counted voter is a signer of one of the pending attestations. -/
theorem mem_getUnslashedAttestingIndices {attestations : Array (PendingAttestation preset)}
    {voters : List ValidatorIndex}
    (computed : getUnslashedAttestingIndices state attestations = .ok voters)
    {index : ValidatorIndex} (member : index ∈ voters) :
    ∃ pending ∈ attestations.toList, ∃ signers,
      getPendingAttestingIndices state pending = .ok signers ∧ index ∈ signers := by
  simp only [getUnslashedAttestingIndices, unslashedAmong, bind_ok_iff] at computed
  obtain ⟨lists, listsOk, filtered⟩ := computed
  have inSet := mem_of_filterM_ok filtered member
  rw [mem_sortedSet, List.mem_flatten] at inSet
  obtain ⟨signers, signersMember, inSigners⟩ := inSet
  obtain ⟨pending, pendingMember, pendingOk⟩ := mapM_ok_mem listsOk signers signersMember
  exact ⟨pending, pendingMember, signers, pendingOk, inSigners⟩

/-- Before Altair the matching target attestations of an epoch are pending attestations of it.

Their target root is the root the state reads for the epoch. -/
theorem mem_getMatchingTargetAttestations (before : fork < .altair) {epoch : Epoch}
    {attestations : Array (PendingAttestation preset)}
    (computed : getMatchingTargetAttestations state before epoch = .ok attestations)
    {pending : PendingAttestation preset} (member : pending ∈ attestations.toList) :
    pending ∈ epochPending state before (decide (epoch = getCurrentEpoch state)) ∧
      getBlockRoot state epoch = .ok pending.data.target.root := by
  simp only [getMatchingTargetAttestations, getMatchingSourceAttestations, bind_ok_iff,
    ensure_ok_iff, pure, Except.pure] at computed
  obtain ⟨source, ⟨_, -, sourceOk⟩, computed⟩ := computed
  have sourceIs := Except.ok.inj sourceOk
  split at computed
  · cases computed
    simp at member
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨root, rootOk, rest⟩ := computed
    cases rest
    simp only [Array.toList_filter, List.mem_filter, beq_iff_eq] at member
    obtain ⟨inSource, sameRoot⟩ := member
    refine ⟨?_, sameRoot ▸ rootOk⟩
    rw [← sourceIs] at inSource
    unfold epochPending
    by_cases current : epoch = getCurrentEpoch state
    · simpa [current] using inSource
    · simpa [current] using inSource

/-! ## Committees -/

/-- Each position that the shuffle gives is below the number of indices it shuffles. -/
theorem lt_of_mem_computeShuffledPermutation {count : UInt64} {seed : Bytes32}
    {shuffled : Array UInt64}
    (computed : computeShuffledPermutation preset count seed = .ok shuffled)
    {position : UInt64} (member : position ∈ shuffled) : position.toNat < count.toNat := by
  obtain ⟨fits, rfl⟩ := computeShuffledPermutation_ok computed
  obtain ⟨index, inside, read⟩ := Array.mem_iff_getElem.mp member
  have size := Shuffle.shuffledPositions_size preset.SHUFFLE_ROUND_COUNT.toNat seed count.toNat
  have entry := Shuffle.shuffledPositions_getElem (rounds := preset.SHUFFLE_ROUND_COUNT.toNat)
    (seed := seed) (lt := size ▸ inside)
  rw [Array.getElem?_eq_getElem inside, read, Option.some.injEq] at entry
  have below := Shuffle.shuffledIndex_lt (rounds := preset.SHUFFLE_ROUND_COUNT.toNat)
    (seed := seed) (size ▸ inside)
  have small : Shuffle.shuffledIndex preset.SHUFFLE_ROUND_COUNT.toNat seed count.toNat index <
      2 ^ 64 := by omega
  rw [entry, UInt64.toNat_ofNat_of_lt' small]
  exact below

/-- Each member of a committee is active in the epoch of its slot. -/
theorem mem_getBeaconCommittee {slot : Slot} {index : CommitteeIndex}
    {committee : Array ValidatorIndex}
    (computed : getBeaconCommittee state slot index = .ok committee)
    {member : ValidatorIndex} (inCommittee : member ∈ committee) :
    member ∈ getActiveValidatorIndices state (computeEpochAtSlot preset slot) := by
  simp only [getBeaconCommittee, beaconCommitteeOf, bind_ok_iff, mapError_ok_iff] at computed
  obtain ⟨seed, _, shuffled, shuffledOk, _, _, _, _, cut⟩ := computed
  set active := (getActiveValidatorIndices state (computeEpochAtSlot preset slot)).toArray
  -- Every shuffled position is below the number of active validators.
  have positions : ∀ position ∈ shuffled, position.toNat < active.size := fun position inside =>
    Nat.lt_of_lt_of_le (lt_of_mem_computeShuffledPermutation shuffledOk inside)
      (by rw [UInt64.toNat_ofNat']; exact Nat.mod_le _ _)
  simp only [shuffledCommittee, bind, Except.bind] at cut
  split at cut
  · cases cut
  split at cut
  swap
  · simp [throw, throwThe, MonadExceptOf.throw] at cut
  split at cut
  · simp [throw, throwThe, MonadExceptOf.throw] at cut
  rename_i inRange
  simp only [pure, Except.pure, Except.ok.injEq] at cut
  subst cut
  simp only [List.mem_toArray, List.mem_map, List.mem_range] at inCommittee
  obtain ⟨offset, below, rfl⟩ := inCommittee
  -- The cut is within the active validators, so there is at least one.
  have nonempty : 0 < active.size := by
    rcases Nat.eq_zero_or_pos active.size with empty | positive
    · exfalso
      rw [empty, Nat.zero_mul, Nat.zero_div, Nat.zero_mul, Nat.zero_div] at below
      exact Nat.not_lt_zero _ below
    · exact positive
  have chosen : ∀ position, (shuffled.getD position 0).toNat < active.size := fun position => by
    rw [Array.getD_eq_getD_getElem?]
    cases read : shuffled[position]? with
    | none => exact nonempty
    | some found => exact positions found (Array.mem_of_getElem? read)
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (chosen _)]
  exact List.mem_toArray.mp (Array.getElem_mem (chosen _))


/-! ## Along a chain -/

namespace ShuffleKept

variable {epoch : Epoch}

/-- Before Altair a slot step keeps the inputs of the shuffle of an epoch up to its end.

The step starts in the epoch or the one after, and ends at most one epoch after it. -/
theorem advanceSlot {next : BeaconState preset fork} (before : fork < .altair)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (finite : epoch ≠ FAR_FUTURE_EPOCH) (bound : epoch ≤ getCurrentEpoch state)
    (near : (getCurrentEpoch next).toNat ≤ epoch.toNat + 1)
    (computed : advanceSlot config checks state = .ok next) : ShuffleKept epoch state next := by
  have stepSlot := advanceSlot_slot computed
  simp only [EthLib.Consensus.advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith,
    mapError_ok_iff, addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨nextSlot, ⟨fits, nextEq⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have nextIs : nextSlot = state.slot + 1 := by
    apply UInt64.toNat_inj.mp
    rw [nextEq, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have cachedEpoch : getCurrentEpoch cached = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [processSlot_slot cachedOk]
  refine (processSlot cachedOk).trans ((?_ : ShuffleKept epoch cached epoched).trans
    (of_eq rfl rfl))
  unfold epochIfLast at epochedOk
  rw [nextIs] at epochedOk
  by_cases closes : ClosesEpoch preset state
  · have last : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := closes
    simp only [last, ↓reduceIte] at epochedOk
    -- The step closes the epoch, so the state is in the epoch itself.
    have moved := epoch_of_closes stepSlot closes
    have boundNat := UInt64.le_iff_toNat_le.mp bound
    have atEpoch : getCurrentEpoch cached = epoch := by
      rw [cachedEpoch]
      exact UInt64.toNat_inj.mp (by omega)
    exact processEpoch before lookahead finite atEpoch epochedOk
  · have notLast : ¬(state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 := closes
    simp only [notLast, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at epochedOk
    exact epochedOk ▸ refl _

end ShuffleKept

/-- Before Altair a chain keeps the inputs of the shuffle of an epoch from the epoch on.

The chain ends before Altair, so it stays in one fork, and at most one epoch past the epoch. -/
theorem Reaches.shuffleKept {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) (before : after.fork < .altair)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {epoch : Epoch} (finite : epoch ≠ FAR_FUTURE_EPOCH)
    (bound : epoch ≤ getCurrentEpoch start.state)
    (near : (getCurrentEpoch after.state).toNat ≤ epoch.toNat + 1) :
    ∃ same : start.fork = after.fork, ShuffleKept epoch (same ▸ start.state) after.state := by
  obtain ⟨run⟩ := chain
  obtain ⟨startFork, startState⟩ := start
  induction run with
  | nil => exact ⟨rfl, .refl _⟩
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks ⟨startFork, startState⟩ middle := ⟨run⟩
    have middleBound : epoch ≤ getCurrentEpoch middle.state := by
      have := middleChain.epoch_le
      exact UInt64.le_iff_toNat_le.mpr (Nat.le_trans (UInt64.le_iff_toNat_le.mp bound) this)
    have stepEpoch := ((Reaches.refl _).step step : Reaches config checks middle last).epoch_le
    cases step with
    | @slot fork state next notDue computed =>
      obtain ⟨same, kept⟩ := more before (Nat.le_trans stepEpoch near)
      change startFork = fork at same
      subst same
      exact ⟨rfl, kept.trans (ShuffleKept.advanceSlot before lookahead finite middleBound near
        computed)⟩
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
      obtain ⟨same, kept⟩ := more before (Nat.le_trans stepEpoch near)
      change startFork = fork at same
      subst same
      obtain ⟨-, processed, -⟩ := applySignedBlock_ok computed
      have postSlot := processBlock_slot processed
      have stateNear : (getCurrentEpoch state).toNat ≤ epoch.toNat + 1 := by
        simp only at near
        unfold getCurrentEpoch at near ⊢
        rw [postSlot] at near
        exact near
      exact ⟨rfl, kept.trans (ShuffleKept.processBlock before lookahead finite middleBound
        stateNear processed)⟩

/-- A chain that ends before Altair stays in one fork: every upgrade leads to Altair or later. -/
theorem Reaches.fork_eq_of_before {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) (before : after.fork < .altair) :
    start.fork = after.fork := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => rfl
  | @snoc middle last run step more =>
    cases step with
    | slot _ _ => exact more before
    | @upgrade _ post due computed =>
      exfalso
      obtain ⟨fork, state⟩ := middle
      cases fork <;>
        simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
          throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
      all_goals
        obtain ⟨_, _, rfl⟩ := computed
        exact absurd before (by dsimp only; decide)
    | block _ _ _ _ _ => exact more before

/-- The state a call reads keeps the inputs of the shuffle of the state it reads from. -/
theorem ReadsFrom.shuffleKept {cached : BeaconState preset fork} {epoch : Epoch}
    (readsFrom : ReadsFrom state cached) : ShuffleKept epoch state cached := by
  obtain ⟨_, _, _, _, rfl⟩ := readsFrom.eq
  exact .of_eq rfl rfl

/-! ## The counted voters signed the call's link -/

/-- Before Altair, a signer that a later state finds for a recorded pending attestation signed it.

A block of the chain recorded the pending attestation, with `epoch` as its target.

A later state of the chain, before Altair and at most one epoch past `epoch`, finds a committee.

It finds a signer from the attestation's bits and that committee.

That signer is active in `epoch`, and signed the attestation's data, checked at its site. -/
theorem PendingRecordedBy.signed {start : ForkedBeaconState preset} {fork : Fork}
    {state : BeaconState preset fork} {pending : PendingAttestation preset} {epoch : Epoch}
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (before : fork < .altair)
    (recordedBy : PendingRecordedBy config checks start ⟨fork, state⟩ pending epoch)
    (near : (getCurrentEpoch state).toNat ≤ epoch.toNat + 1)
    (finite : epoch ≠ FAR_FUTURE_EPOCH) {committee : Array ValidatorIndex}
    {signers : List ValidatorIndex}
    (committeeOk : getBeaconCommittee state pending.data.slot pending.data.index = .ok committee)
    (attestersOk : committeeAttesters pending.aggregationBits.bits 0 committee = .ok signers)
    {index : ValidatorIndex} (inSigners : index ∈ signers) :
    pending.data.target.epoch = epoch ∧ index ∈ getActiveValidatorIndices state epoch ∧
      SignedVote config checks start ⟨fork, state⟩ index pending.data := by
  obtain ⟨fork', engine, block, validateResult, blockState, post, first, site, recorded, pre, suf,
    attestation, blockHead, blockNotDue, applied, blockTail, votesKept, shuffleNear, split,
    prefixOk, siteOk, reads, epochEq, recordedFacts⟩ := recordedBy
  obtain ⟨indexed, bitsEq, dataEq, -, -, indexedOk, valid⟩ := recordedFacts
  -- The block ran in the same fork as the later state, before Altair.
  have sameFork : fork' = fork := blockTail.fork_eq_of_before before
  subst sameFork
  obtain ⟨siteRecent, slotEpoch, _, _, _, _, source⟩ := processAttestation_checks before siteOk
  rw [epochEq] at siteRecent slotEpoch
  have siteEpoch : getCurrentEpoch site = getCurrentEpoch blockState := by
    simp only [getCurrentEpoch, reads.slot]
  have sitePrevious : getPreviousEpoch site = getPreviousEpoch blockState := by
    unfold getPreviousEpoch
    rw [siteEpoch]
  rw [siteEpoch, sitePrevious] at siteRecent
  -- The block is in the target's epoch or the one after.
  have blockBound : epoch ≤ getCurrentEpoch blockState := by
    apply UInt64.le_iff_toNat_le.mpr
    have := getPreviousEpoch_toNat blockState
    rcases siteRecent with same | same <;> rw [same] <;> omega
  have blockNear : (getCurrentEpoch blockState).toNat ≤ epoch.toNat + 1 := by
    have := getPreviousEpoch_toNat blockState
    rcases siteRecent with same | same <;> rw [same] <;> omega
  -- The inputs of the shuffle are the same at the site and later, as at the block's start.
  obtain ⟨-, processed, -⟩ := applySignedBlock_ok applied
  have toFirst := shuffleNear before lookahead _ finite blockBound blockNear
  have toSite : ShuffleKept epoch first site :=
    foldlM_ok_invariant (ShuffleKept epoch first)
      (fun _ _ _ held ok => held.trans (ShuffleKept.processAttestation before ok))
      (ShuffleKept.refl _) prefixOk
  have toPost := ShuffleKept.processBlock before lookahead finite blockBound blockNear processed
  have postBound : epoch ≤ getCurrentEpoch post := by
    unfold getCurrentEpoch at blockBound ⊢
    rw [processBlock_slot processed]
    exact blockBound
  obtain ⟨_, toState⟩ := blockTail.shuffleKept before lookahead finite postBound near
  have toLater : ShuffleKept epoch blockState state := toPost.trans toState
  rw [slotEpoch] at toFirst toSite toLater
  -- The signer is in the committee, so it is active in the target epoch.
  have active :=
    mem_getBeaconCommittee committeeOk (mem_of_committeeAttesters attestersOk inSigners)
  rw [dataEq, ← slotEpoch] at active
  -- The site found the same signers.
  rw [dataEq, toLater.getBeaconCommittee, ← (toFirst.trans toSite).getBeaconCommittee]
    at committeeOk
  rw [bitsEq] at attestersOk
  have attestingOk : getAttestingIndices site attestation = .ok (sortedSet signers) := by
    have notElectra : ¬Fork.pectra ≤ fork' := not_le_of_before before (by decide)
    simp only [getAttestingIndices, notElectra, ↓reduceDIte, bind, Except.bind, committeeOk,
      attestersOk, pure, Except.pure]
  obtain ⟨indexed', indexedOk', attesting, indexedData, -⟩ :=
    getIndexedAttestation_of_getAttestingIndices attestingOk
  cases indexedOk.symm.trans indexedOk'
  rw [dataEq]
  exact ⟨epochEq, active, fork', engine, block, validateResult, blockState, post, first, site,
    recorded, pre, suf, attestation, indexed, blockHead, blockNotDue, applied, blockTail, votesKept,
    split, prefixOk, siteOk, reads, rfl, indexedOk,
    by rw [attesting]; exact List.mem_toArray.mpr (mem_sortedSet.mpr inSigners),
    indexedData, valid, source⟩

/-- Before Altair, a counted voter of a weighing call signed the call's link.

Take a weighing call of a chain that justified a checkpoint, at a fork before Altair.

The buffer of mixes must be longer than `MIN_SEED_LOOKAHEAD + 2`.

Each counted voter is a signer of a pending attestation of the checkpoint's epoch.

That attestation was held by the start of the chain.

Otherwise a block of the chain included it, and the voter signed its data, checked at the site.

The voter is a member of the attestation's committee, so it is active in the checkpoint's epoch.

That data has the checkpoint as target, since the call compares the target root.

Its source is the call's source, except for a target in epoch 1, as from Altair. -/
theorem CallRecord.pending_voters_signed {start after : ForkedBeaconState preset}
    {fork : Fork} {state cached weighed : BeaconState preset fork}
    {voters : List ValidatorIndex} {checkpoint : Checkpoint}
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    fork < .altair → ∀ index ∈ voters,
      (∃ pending, PendingAtStart start pending) ∨
      ∃ data, data.target = checkpoint ∧
        index ∈ getActiveValidatorIndices cached checkpoint.epoch ∧
        SignedVote config checks start ⟨fork, state⟩ index data ∧
        (data.source = recordSource cached checkpoint.epoch ∨
          (checkpoint.epoch.toNat = 1 ∧ ∃ (fork' : Fork) (epochOne : BeaconState preset fork'),
            Reaches config checks start ⟨fork', epochOne⟩ ∧
            Reaches config checks ⟨fork', epochOne⟩ ⟨fork, state⟩ ∧
            (getCurrentEpoch epochOne).toNat = 1 ∧
            data.source = epochOne.currentJustifiedCheckpoint)) := by
  obtain ⟨head, _, readsFrom, _, later, recent, counted, _, rootOk⟩ := call
  intro before index member
  simp only [TargetVoters, not_le_of_before before (Nat.le_refl _), ↓reduceDIte] at counted
  obtain ⟨attestations, matching, unslashed⟩ := counted
  obtain ⟨pending, pendingMember, signers, signersOk, inSigners⟩ :=
    mem_getUnslashedAttestingIndices unslashed member
  obtain ⟨listed, rootRead⟩ := mem_getMatchingTargetAttestations before matching pendingMember
  have targetRoot : pending.data.target.root = checkpoint.root :=
    Except.ok.inj (rootRead.symm.trans rootOk)
  -- The caching keeps the pending attestations and the epoch.
  have cachedSame : cached.slot = state.slot ∧
      epochPending cached before = epochPending state before := by
    obtain ⟨_, _, _, _, rfl⟩ := readsFrom.eq
    exact ⟨rfl, rfl⟩
  have cachedEpoch : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, cachedSame.1]
  have cachedPrevious : getPreviousEpoch cached = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [cachedEpoch]
  rw [cachedSame.2, cachedEpoch] at listed
  rw [cachedEpoch, cachedPrevious] at recent
  have listEpoch : flagsEpoch state (decide (checkpoint.epoch = getCurrentEpoch state)) =
      checkpoint.epoch := by
    unfold flagsEpoch
    by_cases isCurrent : checkpoint.epoch = getCurrentEpoch state
    · simp [isCurrent]
    · simp only [isCurrent, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact (recent.resolve_right isCurrent).symm
  have origin := head.pending before _ listed
  rw [listEpoch] at origin
  rcases origin with atStart | recordedBy
  · exact .inl ⟨pending, atStart⟩
  have stateNear : (getCurrentEpoch state).toNat ≤ checkpoint.epoch.toNat + 1 := by
    have := getPreviousEpoch_toNat state
    rcases recent with same | same <;> rw [same] <;> omega
  -- The epoch is before the far future, since the call reads a slot of it before its own.
  have finite : checkpoint.epoch ≠ FAR_FUTURE_EPOCH := by
    intro far
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    obtain ⟨slot, slotEq, below, -, -⟩ := getBlockRoot_ok rootOk
    have := cached.slot.toNat_lt
    have laterNat := UInt64.lt_iff_toNat_lt.mp later
    change 0 + 1 < _ at laterNat
    have epochNat := getCurrentEpoch_toNat cached
    -- With no slot in an epoch, every epoch is the genesis epoch, which weighs nothing.
    have spe : 1 ≤ preset.SLOTS_PER_EPOCH.toNat := by
      rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
      · rw [zero, Nat.div_zero] at epochNat
        omega
      · exact positive
    have := Nat.le_mul_of_pos_right checkpoint.epoch.toNat spe
    rw [far, farNat] at slotEq this
    omega
  -- The caching keeps the inputs of the shuffle, so the call computes the state's committee.
  have toCached : ShuffleKept (computeEpochAtSlot preset pending.data.slot) state cached :=
    readsFrom.shuffleKept
  simp only [getPendingAttestingIndices, bind_ok_iff] at signersOk
  obtain ⟨committee, committeeOk, attestersOk⟩ := signersOk
  rw [toCached.getBeaconCommittee] at committeeOk
  obtain ⟨epochEq, active, vote⟩ :=
    recordedBy.signed lookahead before stateNear finite committeeOk attestersOk inSigners
  have activeCached : index ∈ getActiveValidatorIndices cached checkpoint.epoch := by
    rw [(readsFrom.shuffleKept (epoch := checkpoint.epoch)).getActiveValidatorIndices]
    exact active
  have target : pending.data.target = checkpoint := by
    cases checkpoint
    cases dataTarget : pending.data.target
    rw [dataTarget] at epochEq targetRoot
    simp only at epochEq targetRoot
    rw [epochEq, targetRoot]
  rw [← cachedEpoch, ← cachedPrevious] at recent
  exact .inr ⟨pending.data, target, activeCached, vote,
    vote.source_link (by rw [target]) readsFrom later recent⟩

/-- `CallRecord.pending_voters_signed` for a weighing call at an epoch boundary. -/
theorem WeighingCall.pending_voters_signed {start after : ForkedBeaconState preset}
    {fork : Fork} {state cached weighed next : BeaconState preset fork}
    {voters : List ValidatorIndex} {checkpoint : Checkpoint}
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    fork < .altair → ∀ index ∈ voters,
      (∃ pending, PendingAtStart start pending) ∨
      ∃ data, data.target = checkpoint ∧
        index ∈ getActiveValidatorIndices cached checkpoint.epoch ∧
        SignedVote config checks start ⟨fork, state⟩ index data ∧
        (data.source = recordSource cached checkpoint.epoch ∨
          (checkpoint.epoch.toNat = 1 ∧ ∃ (fork' : Fork) (epochOne : BeaconState preset fork'),
            Reaches config checks start ⟨fork', epochOne⟩ ∧
            Reaches config checks ⟨fork', epochOne⟩ ⟨fork, state⟩ ∧
            (getCurrentEpoch epochOne).toNat = 1 ∧
            data.source = epochOne.currentJustifiedCheckpoint)) :=
  call.record.pending_voters_signed lookahead

/-- `WeighingCall.pending_voters_signed` for a call that `JustifiedBy` names. -/
theorem JustifiedBy.pending_voters_signed {start after : ForkedBeaconState preset}
    {checkpoint : Checkpoint}
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (justified : JustifiedBy config checks start after checkpoint) :
    ∃ (fork : Fork) (state cached : BeaconState preset fork) (voters : List ValidatorIndex),
      Reaches config checks start ⟨fork, state⟩ ∧
      Reaches config checks ⟨fork, state⟩ after ∧ processSlot state = .ok cached ∧
      GENESIS_EPOCH + 1 < getCurrentEpoch cached ∧
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
      TargetVoters cached checkpoint.epoch voters ∧ PassesThreshold cached voters ∧
      getBlockRoot cached checkpoint.epoch = .ok checkpoint.root ∧
      (fork < .altair → ∀ index ∈ voters,
        (∃ pending, PendingAtStart start pending) ∨
        ∃ data, data.target = checkpoint ∧
          index ∈ getActiveValidatorIndices cached checkpoint.epoch ∧
          SignedVote config checks start ⟨fork, state⟩ index data ∧
          (data.source = recordSource cached checkpoint.epoch ∨
            (checkpoint.epoch.toNat = 1 ∧ ∃ (fork' : Fork) (epochOne : BeaconState preset fork'),
              Reaches config checks start ⟨fork', epochOne⟩ ∧
              Reaches config checks ⟨fork', epochOne⟩ ⟨fork, state⟩ ∧
              (getCurrentEpoch epochOne).toNat = 1 ∧
              data.source = epochOne.currentJustifiedCheckpoint))) := by
  obtain ⟨fork, state, cached, _, _, voters, call⟩ := justified
  exact ⟨fork, state, cached, voters, call.head, call.toAfter, call.cachedOk, call.later,
    call.recent, call.counted, call.passes, call.rootOk, call.pending_voters_signed lookahead⟩

/-! ## From genesis -/

/-- A deposit at genesis adds no vote. -/
theorem votesKept_genesisDeposit {beforeHeze : fork < .hegota} {leaves : Array DepositData}
    {entry : Deposit × Nat}
    (computed : genesisDeposit config checks beforeHeze leaves state entry = .ok after) :
    VotesKept state after := by
  simp only [genesisDeposit, bind_ok_iff] at computed
  obtain ⟨depositRoot, _, deposited⟩ := computed
  exact (VotesKept.of_votes (state := state)
    (after := { state with eth1Data := fun _ => { state.eth1Data beforeHeze with depositRoot } })
    rfl).trans (votesKept_processDeposit deposited)

/-- A genesis state holds no pending attestation.

Its lists start empty, and neither the deposits nor the activations at genesis add a vote. -/
theorem genesis_epochPending {forked : ForkedBeaconState preset}
    (genesis : Genesis config checks forked) (before : forked.fork < .altair) (current : Bool) :
    epochPending forked.state before current = #[] := by
  obtain ⟨⟨_, _, _, computed⟩, _⟩ := genesis
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, same⟩ :=
    computed
  have kept := (VotesKept.foldlM (fun _ _ _ ok => votesKept_genesisDeposit ok) depositedOk).trans
    (VotesKept.foldlM (fun _ _ _ ok => by
      simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, set⟩ := ok
      exact votesKept_setValidator set) activatedOk)
  rw [← same]
  cases current
  · simp only [epochPending, Bool.false_eq_true, ↓reduceIte]
    rw [show ({ activated with genesisValidatorsRoot := root } :
        BeaconState preset _).previousEpochAttestations
      = activated.previousEpochAttestations from rfl, kept.previousEpochAttestations]
    rfl
  · simp only [epochPending, ↓reduceIte]
    rw [show ({ activated with genesisValidatorsRoot := root } :
        BeaconState preset _).currentEpochAttestations
      = activated.currentEpochAttestations from rfl, kept.currentEpochAttestations]
    rfl

/-- From genesis, before Altair, a counted voter of a weighing call signed the call's link.

The voter's data has the checkpoint as target and the call's source as source, with no exception.
-/
theorem CallRecord.pending_voters_signed_of_genesis {start after : ForkedBeaconState preset}
    {fork : Fork} {state cached weighed : BeaconState preset fork}
    {voters : List ValidatorIndex} {checkpoint : Checkpoint}
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (genesis : Genesis config checks start)
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    fork < .altair → ∀ index ∈ voters,
      ∃ data, data.target = checkpoint ∧
        index ∈ getActiveValidatorIndices cached checkpoint.epoch ∧
        SignedVote config checks start ⟨fork, state⟩ index data ∧
        data.source = recordSource cached checkpoint.epoch := by
  intro before index member
  rcases call.pending_voters_signed lookahead before index member with
    ⟨pending, startBefore, current, held⟩ | ⟨data, target, active, signed, source⟩
  · rw [genesis_epochPending genesis startBefore current] at held
    simp at held
  refine ⟨data, target, active, signed, ?_⟩
  rcases source with same | exception
  · exact same
  · exact recordSource_of_epochOne ⟨start, genesis, .refl _⟩ call.reads call.later call.recent
      exception

/-- `CallRecord.pending_voters_signed_of_genesis` for a weighing call at an epoch boundary. -/
theorem WeighingCall.pending_voters_signed_of_genesis {start after : ForkedBeaconState preset}
    {fork : Fork} {state cached weighed next : BeaconState preset fork}
    {voters : List ValidatorIndex} {checkpoint : Checkpoint}
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (genesis : Genesis config checks start)
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    fork < .altair → ∀ index ∈ voters,
      ∃ data, data.target = checkpoint ∧
        index ∈ getActiveValidatorIndices cached checkpoint.epoch ∧
        SignedVote config checks start ⟨fork, state⟩ index data ∧
        data.source = recordSource cached checkpoint.epoch :=
  call.record.pending_voters_signed_of_genesis lookahead genesis

/-- `WeighingCall.pending_voters_signed_of_genesis` for a call that `JustifiedBy` names. -/
theorem JustifiedBy.pending_voters_signed_of_genesis {start after : ForkedBeaconState preset}
    {checkpoint : Checkpoint}
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (genesis : Genesis config checks start)
    (justified : JustifiedBy config checks start after checkpoint) :
    ∃ (fork : Fork) (state cached : BeaconState preset fork) (voters : List ValidatorIndex),
      Reaches config checks start ⟨fork, state⟩ ∧
      Reaches config checks ⟨fork, state⟩ after ∧ processSlot state = .ok cached ∧
      GENESIS_EPOCH + 1 < getCurrentEpoch cached ∧
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
      TargetVoters cached checkpoint.epoch voters ∧ PassesThreshold cached voters ∧
      getBlockRoot cached checkpoint.epoch = .ok checkpoint.root ∧
      (fork < .altair → ∀ index ∈ voters,
        ∃ data, data.target = checkpoint ∧
          index ∈ getActiveValidatorIndices cached checkpoint.epoch ∧
          SignedVote config checks start ⟨fork, state⟩ index data ∧
          data.source = recordSource cached checkpoint.epoch) := by
  obtain ⟨fork, state, cached, _, _, voters, call⟩ := justified
  exact ⟨fork, state, cached, voters, call.head, call.toAfter, call.cachedOk, call.later,
    call.recent, call.counted, call.passes, call.rootOk,
    call.pending_voters_signed_of_genesis lookahead genesis⟩

end EthLib.Consensus
