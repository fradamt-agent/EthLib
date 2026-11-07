module

public import EthLib.Consensus.Proofs.Transition.Provenance.PendingVoters

/-!
# Proofs: voters whose flags come from the upgrade to Altair

From Altair a weighing call counts the validators with a timely-target flag.

The upgrade to Altair sets flags too.

It turns the pending attestations of the previous epoch into flags of that epoch.

Such a flag has no attestation of an Altair block behind it.

It has a Phase 0 pending attestation behind it, which a block of the chain recorded.

This file traces such a voter to that attestation, where the voter signed.

From genesis, no flag is set at the start, since genesis is before Altair.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Genesis -/

/-- A genesis state is before Altair. -/
theorem genesis_fork {forked : ForkedBeaconState preset} (genesis : Genesis config checks forked) :
    forked.fork < .altair := by
  obtain ⟨⟨_, _, _, computed⟩, _⟩ := genesis
  exact (initializeBeaconStateFromEth1_invariant computed).1

/-- From genesis, the start of a chain holds no flag. -/
theorem not_flagAtStart_of_genesis {start : ForkedBeaconState preset}
    (genesis : Genesis config checks start) {index : Nat} {flagIndex : UInt64} :
    ¬FlagAtStart start index flagIndex := fun ⟨altair, _⟩ =>
  Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (genesis_fork genesis) altair)

/-! ## Flags added by the upgrade -/

/-- A flag set after some flags are added was set before, or one of them has its bit. -/
theorem hasFlag_foldl_addFlag :
    ∀ (added : List UInt64) (old : ParticipationFlags) (flagIndex : UInt64),
      hasFlag (added.foldl addFlag old) flagIndex = true →
      hasFlag old flagIndex = true ∨ ∃ a ∈ added, a.toNat % 8 = flagIndex.toNat % 8
  | [], _, _, set => .inl set
  | a :: rest, old, flagIndex, set => by
    rcases hasFlag_foldl_addFlag rest (addFlag old a) flagIndex set with first | ⟨b, member, bit⟩
    · rw [hasFlag_addFlag_eq, Bool.or_eq_true, decide_eq_true_iff] at first
      rcases first with first | bit
      · exact .inl first
      · exact .inr ⟨a, List.mem_cons_self, bit⟩
    · exact .inr ⟨b, List.mem_cons_of_mem _ member, bit⟩

/-- A fold whose every step adds flags only at its own index adds them only at the indices of
the list. -/
theorem FlagsAddedBy.foldlM {ε : Type} {list : Type} {data : list → Array ParticipationFlags}
    {step : list → ValidatorIndex → Except ε list} {earned : List UInt64}
    (added : ∀ l x l', step l x = .ok l' → FlagsAddedBy (data l) (data l') [x] earned) :
    ∀ {indices : List ValidatorIndex} {first last : list},
      indices.foldlM step first = .ok last → FlagsAddedBy (data first) (data last) indices earned
  | [], first, last, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact fun _ flags _ found set => .inl ⟨flags, found, set⟩
  | x :: rest, first, last, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepOk, restOk⟩ := computed
    intro index flags flagIndex found set
    rcases FlagsAddedBy.foldlM added restOk index flags flagIndex found set with
      ⟨old, oldFound, oldSet⟩ | ⟨⟨attester, member, same⟩, earnedBit⟩
    · rcases added _ _ _ stepOk index old flagIndex oldFound oldSet with before |
        ⟨⟨attester, member, same⟩, earnedBit⟩
      · exact .inl before
      · rw [List.mem_singleton] at member
        subst member
        exact .inr ⟨⟨attester, List.mem_cons_self, same⟩, earnedBit⟩
    · exact .inr ⟨⟨attester, List.mem_cons_of_mem _ member, same⟩, earnedBit⟩

/-- One translated pending attestation adds its earned flags to its signers, and nothing else. -/
theorem translateAttestation_flags {altair : .altair ≤ fork}
    {pending : PendingAttestation preset}
    (computed : translateAttestation state altair pending = .ok after) :
    ∃ (participation : EpochParticipation preset fork) (earned : List UInt64)
      (attesters : List ValidatorIndex),
      after = { state with previousEpochParticipation := fun _ => participation } ∧
      getAttestationParticipationFlagIndices state pending.data pending.inclusionDelay
        state.latestBlockHeader.slot = .ok earned ∧
      getPendingAttestingIndices state pending = .ok attesters ∧
      FlagsAddedBy (state.previousEpochParticipation altair).data participation.data attesters
        earned := by
  simp only [translateAttestation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨earned, earnedOk, attesters, attestersOk, participation, folded, rfl⟩ := computed
  refine ⟨participation, earned, attesters, rfl, earnedOk, attestersOk, ?_⟩
  refine FlagsAddedBy.foldlM (data := fun (list : EpochParticipation preset fork) => list.data)
    (fun list x list' step => ?_) folded
  split at step
  · rename_i inside
    simp only [Except.ok.injEq] at step
    subst step
    intro index flags flagIndex found set
    simp only [Array.getElem?_set] at found
    split at found
    · rename_i same
      subst same
      simp only [Option.some.injEq] at found
      subst found
      rcases hasFlag_foldl_addFlag earned _ flagIndex set with old | bit
      · exact .inl ⟨_, Array.getElem?_eq_getElem inside, old⟩
      · exact .inr ⟨⟨x, List.mem_singleton_self _, rfl⟩, bit⟩
    · exact .inl ⟨flags, found, set⟩
  · cases step

/-- The state that the upgrade to Altair builds from a Phase 0 state, before any flag. -/
abbrev carriedToAltair (config : Config) (pre : BeaconState preset .phase0) :
    BeaconState preset .altair :=
  carryFields config .altair pre (by decide) (by decide)

/-- A flag that the upgrade to Altair set came from one pending attestation of the previous
epoch.

The upgrade computed the attestation's earned flags and its signers in a state that holds the
carried fields of the Phase 0 state, with some flags. -/
theorem upgradeToAltair_flags {pre : BeaconState preset .phase0}
    {post : BeaconState preset .altair} (computed : upgradeToAltair config pre = .ok post)
    {index : Nat} {flags : ParticipationFlags} {flagIndex : UInt64}
    (found : (post.previousEpochParticipation (by decide)).data[index]? = some flags)
    (set : hasFlag flags flagIndex = true) :
    ∃ pending ∈ (pre.previousEpochAttestations (by decide)).data.toList,
      ∃ (participation : EpochParticipation preset .altair) (earned : List UInt64)
        (attesters : List ValidatorIndex),
        getAttestationParticipationFlagIndices
          { carriedToAltair config pre with previousEpochParticipation := fun _ => participation }
          pending.data pending.inclusionDelay
          (carriedToAltair config pre).latestBlockHeader.slot = .ok earned ∧
        getPendingAttestingIndices
          { carriedToAltair config pre with previousEpochParticipation := fun _ => participation }
          pending = .ok attesters ∧
        (∃ attester ∈ attesters, attester.toNat = index) ∧
        ∃ added ∈ earned, added.toNat % 8 = flagIndex.toNat % 8 := by
  simp only [upgradeToAltair, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨translated, folded, _, -, rfl⟩ := computed
  rw [← Array.foldlM_toList] at folded
  -- Along the fold, a set flag was set at the start, or by one of the attestations so far.
  have traced : ∀ {pendings : List (PendingAttestation preset)}
      {start : EpochParticipation preset .altair} {last : BeaconState preset .altair},
      pendings.foldlM (fun state attestation => translateAttestation state (by decide) attestation)
        { carriedToAltair config pre with previousEpochParticipation := fun _ => start } =
        .ok last →
      ∀ (index : Nat) (flags : ParticipationFlags),
        (last.previousEpochParticipation (by decide)).data[index]? = some flags →
        hasFlag flags flagIndex = true →
        (∃ old, start.data[index]? = some old ∧ hasFlag old flagIndex = true) ∨
        ∃ pending ∈ pendings,
          ∃ (participation : EpochParticipation preset .altair) (earned : List UInt64)
            (attesters : List ValidatorIndex),
            getAttestationParticipationFlagIndices
              { carriedToAltair config pre with previousEpochParticipation := fun _ => participation }
              pending.data pending.inclusionDelay
              (carriedToAltair config pre).latestBlockHeader.slot = .ok earned ∧
            getPendingAttestingIndices
              { carriedToAltair config pre with previousEpochParticipation := fun _ => participation }
              pending = .ok attesters ∧
            (∃ attester ∈ attesters, attester.toNat = index) ∧
            ∃ added ∈ earned, added.toNat % 8 = flagIndex.toNat % 8 := by
    intro pendings
    induction pendings with
    | nil =>
      intro start last computed index flags found set
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact .inl ⟨flags, found, set⟩
    | cons pending rest more =>
      intro start last computed index flags found set
      rw [List.foldlM_cons, bind_ok_iff] at computed
      obtain ⟨middle, stepOk, restOk⟩ := computed
      obtain ⟨participation, earned, attesters, rfl, earnedOk, attestersOk, added⟩ :=
        translateAttestation_flags stepOk
      rcases more restOk index flags found set with ⟨old, oldFound, oldSet⟩ |
        ⟨later, member, rest'⟩
      · rcases added index old flagIndex oldFound oldSet with before | ⟨attester, earnedBit⟩
        · exact .inl before
        · exact .inr ⟨pending, List.mem_cons_self, start, earned, attesters, earnedOk,
            attestersOk, attester, earnedBit⟩
      · exact .inr ⟨later, List.mem_cons_of_mem _ member, rest'⟩
  rcases traced (start := (carriedToAltair config pre).previousEpochParticipation (by decide))
      folded index flags found set with ⟨old, oldFound, oldSet⟩ | ⟨pending, member, rest⟩
  · -- The carried state has no flag.
    exfalso
    obtain ⟨zeros, -, -⟩ := carryFields_of_lt_altair (config := config) (post := .altair)
      pre (by decide) (by decide) (by decide) (by decide)
    rw [zeros, Array.getElem?_replicate] at oldFound
    split at oldFound
    · simp only [Option.some.injEq] at oldFound
      subst oldFound
      rw [hasFlag_zero] at oldSet
      cases oldSet
    · cases oldFound
  · exact ⟨pending, member, rest⟩

/-! ## Reads that the upgrade keeps -/

/-- Two states of any forks with the same registry and mixes have the same committees. -/
theorem getBeaconCommittee_of_same {fork' : Fork} {other : BeaconState preset fork'}
    (validators : other.validators.data = state.validators.data)
    (mixes : other.randaoMixes = state.randaoMixes) (slot : Slot) (index : CommitteeIndex) :
    getBeaconCommittee other slot index = getBeaconCommittee state slot index := by
  simp only [getBeaconCommittee, beaconCommitteeOf, getCommitteeCountPerSlot, getSeed,
    getRandaoMix, getActiveValidatorIndices, validators, mixes]

/-- Two states of any forks at one slot with the same block roots read the same roots. -/
theorem getBlockRoot_of_same {fork' : Fork} {other : BeaconState preset fork'}
    (slot : other.slot = state.slot) (blockRoots : other.blockRoots = state.blockRoots)
    (epoch : Epoch) : getBlockRoot other epoch = getBlockRoot state epoch := by
  simp only [getBlockRoot, getBlockRootAtSlot, slot, blockRoots]

/-- A root that an earlier state of a chain reads for an epoch is the root a later weighing call
reads for it.

The call reads the previous or the current epoch, so both reads take an entry still in the
buffer, which spans two epochs. -/
theorem getBlockRoot_of_earlier {fork' : Fork} {earlier : BeaconState preset fork'}
    {cached : BeaconState preset fork} {epoch : Epoch} {root root' : Root}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (chain : Reaches config checks ⟨fork', earlier⟩ ⟨fork, state⟩)
    (read : getBlockRoot earlier epoch = .ok root) (readsFrom : ReadsFrom state cached)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch cached)
    (recent : epoch = getPreviousEpoch cached ∨ epoch = getCurrentEpoch cached)
    (rootOk : getBlockRoot cached epoch = .ok root') : root = root' := by
  obtain ⟨slot, slotEq, below, _, read⟩ := getBlockRoot_ok read
  obtain ⟨slot', slotEq', _, near', stateRead⟩ := readsFrom.read wide later recent rootOk
  have sameSlot : slot' = slot := UInt64.toNat_inj.mp (slotEq'.trans slotEq.symm)
  subst sameSlot
  have stable := (chain.roots_stable (slot := slot') below near').1
  simp only at stable
  rw [stateRead, read] at stable
  exact (Except.ok.inj stable).symm

/-- A signed vote of a chain is a signed vote of a longer chain. -/
theorem SignedVote.extendChain {start middle last : ForkedBeaconState preset}
    {index : ValidatorIndex} {data : AttestationData}
    (vote : SignedVote config checks start middle index data)
    (chain : Reaches config checks middle last) : SignedVote config checks start last index data :=
  have ⟨fork, engine, signed, validateResult, state, post, first, site, recorded, pre, suf,
    attestation, indexed, head, notDue, applied, tail, rest⟩ := vote
  ⟨fork, engine, signed, validateResult, state, post, first, site, recorded, pre, suf, attestation,
    indexed, head, notDue, applied, tail.trans chain, rest⟩

/-! ## The voters -/

/-- From genesis, a voter of a weighing call whose flag the upgrade to Altair set signed the link.

The upgrade turned a pending attestation into the voter's flag, at the epoch before Altair.

A block of the chain recorded that attestation, and the voter is a signer of it.

So the voter signed its data, checked at its site.

Its target is the call's checkpoint, as the flag is a timely-target flag, and its source is the
call's source.

The buffer of roots must span two epochs.

The buffer of mixes must be longer than `MIN_SEED_LOOKAHEAD + 2`, as before Altair. -/
theorem CallRecord.upgrade_voter_signed {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (genesis : Genesis config checks start)
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint)
    {index : ValidatorIndex}
    (upgraded : FlagFromAltairUpgrade config checks start ⟨fork, state⟩ index.toNat
      TIMELY_TARGET_FLAG_INDEX checkpoint.epoch) :
    ∃ data, data.target = checkpoint ∧
      SignedVote config checks start ⟨fork, state⟩ index data ∧
      data.source = recordSource cached checkpoint.epoch := by
  obtain ⟨pre, post, flags, preChain, upgradedOk, postChain, found, set, epochIs, upgradeChain⟩ :=
    upgraded
  obtain ⟨pending, member, participation, earned, attesters, earnedOk, attestersOk,
    ⟨attester, attesterMember, sameIndex⟩, ⟨added, addedMember, bit⟩⟩ :=
    upgradeToAltair_flags upgradedOk found set
  have sameAttester : attester = index := UInt64.toNat_inj.mp sameIndex
  subst sameAttester
  have targetFlag := earned_target earnedOk addedMember bit
  subst targetFlag
  -- The carried state reads what the Phase 0 state reads.
  have carriedValidators : (carriedToAltair config pre).validators.data = pre.validators.data := by
    simp [carryFields, carryRooted]
  have carriedMixes : (carriedToAltair config pre).randaoMixes = pre.randaoMixes := by
    simp [carryFields]
  have carriedRoots : (carriedToAltair config pre).blockRoots = pre.blockRoots := by
    simp [carryFields]
  have carriedSlot : (carriedToAltair config pre).slot = pre.slot := by
    simp [carryFields]
  -- The pending attestation was in the Phase 0 state's list of the previous epoch.
  have before : Fork.phase0 < .altair := by decide
  have listed : pending ∈ epochPending pre before false := by
    simp only [epochPending, Bool.false_eq_true, ↓reduceIte]
    exact Array.mem_toList_iff.mp member
  rcases preChain.pending before false listed with ⟨startBefore, current, held⟩ | recordedBy
  · rw [genesis_epochPending genesis startBefore current] at held
    simp at held
  -- The upgrade computed the signers with the committee of the Phase 0 state.
  simp only [getPendingAttestingIndices, bind_ok_iff] at attestersOk
  obtain ⟨committee, committeeOk, signersOk⟩ := attestersOk
  rw [getBeaconCommittee_of_same (state := pre) (other := { carriedToAltair config pre with
    previousEpochParticipation := fun _ => participation }) carriedValidators carriedMixes]
    at committeeOk
  have previousNat := getPreviousEpoch_toNat pre
  have finite : flagsEpoch pre false ≠ FAR_FUTURE_EPOCH := by
    intro far
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have := (getCurrentEpoch pre).toNat_lt
    simp only [flagsEpoch, Bool.false_eq_true, ↓reduceIte] at far
    rw [far] at previousNat
    omega
  obtain ⟨epochEq, -, vote⟩ := recordedBy.signed lookahead before
    (by simp only [flagsEpoch, Bool.false_eq_true, ↓reduceIte]; omega) finite committeeOk signersOk
    attesterMember
  have toState : Reaches config checks ⟨.phase0, pre⟩ ⟨fork, state⟩ := upgradeChain.trans postChain
  -- The upgrade keeps the slot, so the epoch of the list is the call's epoch.
  have postSlot : post.slot = pre.slot := by
    simp only [upgradeToAltair, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgradedOk
    obtain ⟨translated, folded, _, -, rfl⟩ := upgradedOk
    rw [← Array.foldlM_toList] at folded
    obtain ⟨_, rfl, -⟩ := foldlM_translateAttestation folded
    exact carriedSlot
  have epoch : pending.data.target.epoch = checkpoint.epoch := by
    rw [epochEq, epochIs]
    simp only [flagsEpoch, Bool.false_eq_true, ↓reduceIte, getPreviousEpoch, getCurrentEpoch,
      postSlot]
  -- The target root is the call's, since the flag is a timely-target flag.
  have siteRoot := getAttestationParticipationFlagIndices_target earnedOk addedMember
  rw [getBlockRoot_of_same (state := pre) (other := { carriedToAltair config pre with
    previousEpochParticipation := fun _ => participation }) carriedSlot carriedRoots, epoch]
    at siteRoot
  have sameRoot := getBlockRoot_of_earlier wide toState siteRoot call.reads call.later call.recent
    call.rootOk
  have target : pending.data.target = checkpoint := by
    cases checkpoint
    cases dataTarget : pending.data.target
    rw [dataTarget] at epoch sameRoot
    simp only at epoch sameRoot
    rw [epoch, sameRoot]
  have voteLater := vote.extendChain toState
  refine ⟨pending.data, target, voteLater, ?_⟩
  rcases voteLater.source_link epoch call.reads call.later call.recent with same | exception
  · exact same
  · exact recordSource_of_epochOne ⟨start, genesis, .refl _⟩ call.reads call.later call.recent
      exception

/-- `CallRecord.upgrade_voter_signed` for a weighing call at an epoch boundary. -/
theorem WeighingCall.upgrade_voter_signed {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed next : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (genesis : Genesis config checks start)
    (call : WeighingCall config checks start after fork state cached weighed next voters checkpoint)
    {index : ValidatorIndex}
    (upgraded : FlagFromAltairUpgrade config checks start ⟨fork, state⟩ index.toNat
      TIMELY_TARGET_FLAG_INDEX checkpoint.epoch) :
    ∃ data, data.target = checkpoint ∧
      SignedVote config checks start ⟨fork, state⟩ index data ∧
      data.source = recordSource cached checkpoint.epoch :=
  call.record.upgrade_voter_signed wide lookahead genesis upgraded

/-- From genesis and from Altair, each counted voter of a weighing call signed the call's link.

Its flag came from an attestation of an Altair block, or from the upgrade to Altair, which turned
a Phase 0 attestation into it.

Either way, the voter signed attestation data with the call's checkpoint as target and the call's
source as source, checked at a site. -/
theorem CallRecord.voters_signed_of_genesis {start after : ForkedBeaconState preset}
    {fork : Fork} {state cached weighed : BeaconState preset fork}
    {voters : List ValidatorIndex} {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (genesis : Genesis config checks start)
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    .altair ≤ fork → ∀ index ∈ voters,
      ∃ data, data.target = checkpoint ∧
        SignedVote config checks start ⟨fork, state⟩ index data ∧
        data.source = recordSource cached checkpoint.epoch := by
  intro altair index member
  rcases call.voters_signed_of_reachable wide ⟨start, genesis, .refl _⟩ altair index member with
    atStart | upgraded | ⟨data, target, signed, source⟩
  · exact absurd atStart (not_flagAtStart_of_genesis genesis)
  · exact call.upgrade_voter_signed wide lookahead genesis upgraded
  · exact ⟨data, target, signed.vote, source⟩


/-- `CallRecord.voters_signed_of_genesis` for a weighing call at an epoch boundary. -/
theorem WeighingCall.voters_signed_of_genesis {start after : ForkedBeaconState preset}
    {fork : Fork} {state cached weighed next : BeaconState preset fork}
    {voters : List ValidatorIndex} {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (genesis : Genesis config checks start)
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    .altair ≤ fork → ∀ index ∈ voters,
      ∃ data, data.target = checkpoint ∧
        SignedVote config checks start ⟨fork, state⟩ index data ∧
        data.source = recordSource cached checkpoint.epoch :=
  call.record.voters_signed_of_genesis wide lookahead genesis

end EthLib.Consensus
