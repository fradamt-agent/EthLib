module

public import EthLib.Consensus.Proofs.Transition.Provenance.Roots

/-!
# Proofs: the committees of an epoch stay fixed before Altair

Before Altair a state keeps pending attestations with their bits, and no list of signers.

The weighing call finds the signers again: it computes each committee anew, in its own state.

So the signers it counts are the signers that the inclusion checked only if both states agree.

They must have the same committee.

A committee of an epoch is computed from two inputs of the state.

- The validators active in that epoch.
- The RANDAO mix at the position that the seed of that epoch reads.

This file shows that both stay fixed while the current epoch is the epoch or the next one.

Every step that sets an activation or an exit epoch sets one past the current epoch.

A new validator is not active yet.

The writes to the mixes are at the current and the next epoch, and the seed reads an older one.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- Whether each validator of the registry is active in an epoch, in the order of the registry.
-/
def activity (state : BeaconState preset fork) (epoch : Epoch) : List Bool :=
  state.validators.data.toList.map (isActiveValidator · epoch)

/-- The inputs of the shuffle of an epoch are the same in a later state.

- The registry may grow, but each validator keeps whether it is active in the epoch.
  Each new validator is not active in it.
- The mix that the seed of the epoch reads is the same.
  The seed reads the mix of `epoch + N - MIN_SEED_LOOKAHEAD - 1`, for `N` the number of mixes.
  -/
structure ShuffleKept (epoch : Epoch) (state after : BeaconState preset fork) : Prop where
  active : ∃ added, activity after epoch = activity state epoch ++ List.replicate added false
  mix : ∀ mixEpoch : Epoch,
    mixEpoch.toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 =
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat →
    getRandaoMix after mixEpoch = getRandaoMix state mixEpoch

namespace ShuffleKept

variable {epoch : Epoch}

theorem refl (state : BeaconState preset fork) : ShuffleKept epoch state state :=
  ⟨⟨0, by simp⟩, fun _ _ => rfl⟩

theorem trans {first second third : BeaconState preset fork}
    (one : ShuffleKept epoch first second) (two : ShuffleKept epoch second third) :
    ShuffleKept epoch first third where
  active := by
    obtain ⟨added, oneActive⟩ := one.active
    obtain ⟨added', twoActive⟩ := two.active
    exact ⟨added + added', by rw [twoActive, oneActive, List.append_assoc,
      List.replicate_append_replicate]⟩
  mix mixEpoch reads := (two.mix mixEpoch reads).trans (one.mix mixEpoch reads)

/-- A step that keeps the registry and the mixes keeps the inputs. -/
theorem of_eq (validators : after.validators.data = state.validators.data)
    (mixes : after.randaoMixes = state.randaoMixes) : ShuffleKept epoch state after :=
  ⟨⟨0, by simp [activity, validators]⟩, fun _ _ => by simp [getRandaoMix, mixes]⟩

/-- A fold whose every step keeps the inputs, while the slot stays, keeps them.

Each step may need the current epoch to be at least the epoch. -/
theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → Kept s s')
    (shuffle : ∀ s x s', epoch ≤ getCurrentEpoch s → step s x = .ok s' → ShuffleKept epoch s s')
    (bound : epoch ≤ getCurrentEpoch state) {items : List α}
    (computed : items.foldlM step state = .ok after) : ShuffleKept epoch state after := by
  have both := foldlM_ok_invariant (fun s => Kept state s ∧ ShuffleKept epoch state s)
    (fun s x s' before ok => by
      have sameEpoch : getCurrentEpoch s = getCurrentEpoch state := by
        unfold getCurrentEpoch
        rw [before.1.slot]
      exact ⟨before.1.trans (kept s x s' ok),
        before.2.trans (shuffle s x s' (sameEpoch ▸ bound) ok)⟩)
    ⟨Kept.refl state, refl state⟩ computed
  exact both.2

/-- A validator replaced by one that is active in the epoch exactly when it was. -/
theorem putValidator {index : Nat} (inside : index < state.validators.data.size)
    {validator : Validator}
    (same : isActiveValidator validator epoch =
      isActiveValidator state.validators.data[index] epoch) :
    ShuffleKept epoch state (state.putValidator index inside validator) where
  active := ⟨0, by
    simp only [activity, BeaconState.putValidator, RootedForkList.data_set, Array.toList_set,
      List.map_set, List.replicate_zero, List.append_nil, same]
    have inside' : index < (state.validators.data.toList.map (isActiveValidator · epoch)).length :=
      by simpa using inside
    have read := List.getElem_map (f := (isActiveValidator · epoch))
      (l := state.validators.data.toList) (i := index) (h := inside')
    simp only [Array.getElem_toList] at read
    rw [← read, List.set_getElem_self]⟩
  mix _ _ := rfl

/-- A validator that is set to one active in the epoch exactly when it was. -/
theorem setValidator {index : ValidatorIndex} {old validator : Validator}
    (found : getValidator state index = .ok old)
    (set : state.setValidator index validator = .ok after)
    (same : isActiveValidator validator epoch = isActiveValidator old epoch) :
    ShuffleKept epoch state after := by
  obtain ⟨inside, rfl⟩ := setValidator_ok set
  refine putValidator inside ?_
  have read : state.validators.data[index.toNat]? = some old := by
    unfold getValidator at found
    split at found
    · rename_i read
      cases found
      exact read
    · cases found
  rw [Array.getElem?_eq_getElem inside] at read
  rw [same, Option.some.inj read]

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : ShuffleKept epoch state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact of_eq rfl rfl

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : ShuffleKept epoch state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact of_eq rfl rfl

end ShuffleKept

end EthLib.Consensus

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-- The active validators of an epoch depend only on which validators are active. -/
theorem getActiveValidatorIndices_eq_activity (state : BeaconState preset fork) (epoch : Epoch) :
    getActiveValidatorIndices state epoch =
      (activity state epoch).zipIdx.filterMap fun (active, index) =>
        if active then some index.toUInt64 else none := by
  unfold getActiveValidatorIndices activity
  rw [List.zipIdx_map, List.filterMap_map]
  rfl

theorem ShuffleKept.getActiveValidatorIndices {epoch : Epoch}
    (kept : ShuffleKept epoch state after) :
    getActiveValidatorIndices after epoch = getActiveValidatorIndices state epoch := by
  obtain ⟨added, active⟩ := kept.active
  rw [getActiveValidatorIndices_eq_activity, getActiveValidatorIndices_eq_activity, active,
    List.zipIdx_append, List.filterMap_append]
  -- A new validator is not active, so it adds no index.
  have none :
      (List.zipIdx (List.replicate added false) (0 + (activity state epoch).length)).filterMap
      (fun (active, index) => if active then some index.toUInt64 else none) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro pair member
    obtain ⟨active, index⟩ := pair
    have inactive : active = false := List.eq_of_mem_replicate (List.fst_mem_of_mem_zipIdx member)
    subst inactive
    rfl
  rw [none, List.append_nil]

theorem ShuffleKept.getSeed {epoch : Epoch} (kept : ShuffleKept epoch state after)
    (domainType : DomainType) :
    getSeed after epoch domainType = getSeed state epoch domainType := by
  unfold EthLib.Consensus.getSeed
  -- The position of the mix does not depend on the state.
  cases arith : (liftArith (do
      subChecked (← subChecked (← addChecked epoch preset.EPOCHS_PER_HISTORICAL_VECTOR)
        preset.MIN_SEED_LOOKAHEAD) 1) : Except AccessorError UInt64) with
  | error => rfl
  | ok shifted =>
    simp only [bind, Except.bind]
    simp only [liftArith, mapError_ok_iff, bind_ok_iff] at arith
    obtain ⟨sum, sumOk, lowered, loweredOk, shiftedOk⟩ := arith
    obtain ⟨_, sumEq⟩ := addChecked_ok_iff.mp sumOk
    obtain ⟨_, loweredEq⟩ := subChecked_ok_iff.mp loweredOk
    obtain ⟨_, shiftedEq⟩ := subChecked_ok_iff.mp shiftedOk
    have one : (1 : UInt64).toNat = 1 := rfl
    rw [kept.mix shifted (by omega)]

/-- A committee of a slot is the same while the inputs of its epoch's shuffle are. -/
theorem ShuffleKept.getBeaconCommittee {slot : Slot}
    (kept : ShuffleKept (computeEpochAtSlot preset slot) state after) (index : CommitteeIndex) :
    getBeaconCommittee after slot index = getBeaconCommittee state slot index := by
  unfold EthLib.Consensus.getBeaconCommittee beaconCommitteeOf getCommitteeCountPerSlot
  simp only [kept.getSeed, kept.getActiveValidatorIndices]

/-- Before Altair the weighing call finds the signers of a pending attestation as they were. -/
theorem ShuffleKept.getPendingAttestingIndices {pending : PendingAttestation preset}
    (kept : ShuffleKept (computeEpochAtSlot preset pending.data.slot) state after) :
    getPendingAttestingIndices after pending = getPendingAttestingIndices state pending := by
  unfold EthLib.Consensus.getPendingAttestingIndices
  rw [kept.getBeaconCommittee]


/-! ## Exits and activations go past the current epoch -/

/-- Before Electra the exit queue gives an epoch past the current one.

It is at least the first epoch at which an exit may take effect, `current + 1 + MAX_SEED_LOOKAHEAD`.
-/
theorem exitQueueEpoch_gt {config : Config} {epoch : Epoch}
    (computed : exitQueueEpoch config state = .ok epoch) :
    (getCurrentEpoch state).toNat < epoch.toNat := by
  simp only [exitQueueEpoch, bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  rename_i earliest earliestOk
  have bounds := (computeActivationExitEpoch_ok_iff.mp (mapError_ok_iff.mp earliestOk)).2
  have startLe := UInt64.le_iff_toNat_le.mp (le_foldl_maxExitEpoch
    (state.validators.data.toList.filter (·.exitEpoch != FAR_FUTURE_EPOCH)) earliest).1
  split at computed
  · have sum := (addChecked_ok_iff.mp (mapError_ok_iff.mp computed)).2
    have one : (1 : UInt64).toNat = 1 := rfl
    omega
  · cases computed
    omega

/-- Before Electra an exit keeps the inputs of the shuffle of an epoch up to the current one.

A validator that starts to exit leaves past the current epoch, so it stays active in the epoch.
-/
theorem ShuffleKept.initiateValidatorExit {config : Config} {epoch : Epoch}
    (before : ¬.pectra ≤ fork) (bound : epoch ≤ getCurrentEpoch state) {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    ShuffleKept epoch state after := by
  obtain ⟨validator, found, ⟨_, rfl⟩ | ⟨far, queued, exitEpoch, _, queue, _, set⟩⟩ :=
    initiateValidatorExit_ok computed
  · exact .refl _
  · unfold exitQueue at queue
    simp only [before, ↓reduceDIte, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at queue
    obtain ⟨queueEpoch, queueOk, rfl, rfl⟩ := queue
    have later := exitQueueEpoch_gt queueOk
    have boundNat := UInt64.le_iff_toNat_le.mp bound
    refine setValidator found set ?_
    -- The epoch is before the exit epoch, and so before the far future.
    have beforeExit : epoch < queueEpoch := UInt64.lt_iff_toNat_lt.mpr (by omega)
    have beforeFar : epoch < FAR_FUTURE_EPOCH :=
      UInt64.lt_iff_toNat_lt.mpr (by have := queueEpoch.toNat_lt; simp [FAR_FUTURE_EPOCH]; omega)
    simp [isActiveValidator, far, beforeExit, beforeFar]


/-! ## The mixes -/

/-- A write to the mixes at the epoch or the one after leaves the mix that its seed reads.

The seed of an epoch reads the mix of `epoch + N - MIN_SEED_LOOKAHEAD - 1`.

That is at least two epochs before the epoch, around the buffer, while `MIN_SEED_LOOKAHEAD + 2 < N`.
-/
theorem mix_of_write {epoch written : Epoch} {value : Bytes32}
    {mixes : RootedVector Bytes32 preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat}
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (computed : writeCircularRooted state.randaoMixes written value = .ok mixes)
    (fromEpoch : epoch.toNat ≤ written.toNat) (near : written.toNat ≤ epoch.toNat + 1)
    (mixEpoch : Epoch)
    (reads : mixEpoch.toNat + preset.MIN_SEED_LOOKAHEAD.toNat + 1 =
      epoch.toNat + preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat) :
    readCircular mixes.elements mixEpoch = readCircular state.randaoMixes.elements mixEpoch := by
  have plain := writeCircularRooted_elements state.randaoMixes written value
  rw [computed] at plain
  exact readCircular_writeCircular_of_ne plain.symm
    (mod_ne_of_lt (by omega) (by omega)).symm

/-! ## The steps of a block, before Altair -/

/-- Before Altair, a fork is below each fork from Altair on. -/
theorem not_le_of_before {later : Base.Fork} (before : fork < .altair)
    (fromAltair : Base.Fork.altair ≤ later) : ¬later ≤ fork :=
  fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le before (Nat.le_trans fromAltair le))

/-- Before Altair, a step keeps the inputs of the shuffle of each epoch near the current one.

The epoch is the current one or the one before, and not the far future.

The buffer of mixes must be longer than `MIN_SEED_LOOKAHEAD + 2`. -/
def ShuffleKeptNear (state after : BeaconState preset fork) : Prop :=
  fork < .altair →
    preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat →
    ∀ epoch : Epoch, epoch ≠ FAR_FUTURE_EPOCH → epoch ≤ getCurrentEpoch state →
      (getCurrentEpoch state).toNat ≤ epoch.toNat + 1 → ShuffleKept epoch state after


namespace ShuffleKept

variable {config : Config} {checks : SignatureChecks} {epoch : Epoch}

theorem slashValidator (before : fork < .altair) (bound : epoch ≤ getCurrentEpoch state)
    {slashedIndex : ValidatorIndex} {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    ShuffleKept epoch state after := by
  simp only [EthLib.Consensus.slashValidator, bind_ok_iff, liftArith, mapError_ok_iff]
    at computed
  obtain ⟨exited, exitedOk, validator, found, _, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk, _, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  have notGloas := not_le_of_before before (later := .glamsterdam) (by decide)
  simp only [notGloas, ↓reduceDIte, pure, Except.pure, Except.ok.injEq] at done
  subst done
  -- Being slashed changes neither the activation nor the exit epoch.
  refine (initiateValidatorExit (not_le_of_before before (by decide)) bound exitedOk).trans <|
    (setValidator found markedOk rfl).trans <| (of_eq ?_ ?_).trans <|
    (decreaseBalance loweredOk).trans <| (increaseBalance raisedOk).trans (increaseBalance lastOk)
  · rfl
  · rfl

theorem processProposerSlashing (before : fork < .altair) (bound : epoch ≤ getCurrentEpoch state)
    {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    ShuffleKept epoch state after := by
  simp only [EthLib.Consensus.processProposerSlashing, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact slashValidator before bound slashed

theorem processAttesterSlashing (before : fork < .altair) (bound : epoch ≤ getCurrentEpoch state)
    {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    ShuffleKept epoch state after := by
  simp only [EthLib.Consensus.processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  -- Each slashing keeps the slot, so the bound holds at every step of the fold.
  refine (foldlM_ok_invariant (fun step => Kept state step.1 ∧ ShuffleKept epoch state step.1)
    (fun step index next held ok => ?_)
    (show Kept state (state, false).1 ∧ ShuffleKept epoch state (state, false).1 from
      ⟨Kept.refl state, refl state⟩) folded).2
  have kept := kept_slashIfSlashable ok
  refine ⟨held.1.trans kept, held.2.trans ?_⟩
  have sameEpoch : getCurrentEpoch step.1 = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [held.1.slot]
  obtain ⟨current, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, slashed, rfl⟩ := ok
    exact slashValidator before (sameEpoch ▸ bound) slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ refl _

theorem processAttestation (before : fork < .altair) {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processAttestation at computed
  split at computed
  · exact absurd ‹_› (not_le_of_before before (Nat.le_refl _))
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept
  · obtain ⟨_, rest⟩ := kept
    exact of_eq (congrArg (·.validators.data) rest) (congrArg (·.randaoMixes) rest)
  · obtain ⟨_, rest⟩ := kept
    exact of_eq (congrArg (·.validators.data) rest) (congrArg (·.randaoMixes) rest)

/-- A new validator is not active in an epoch before the far future. -/
theorem addValidatorToRegistry (before : fork < .altair) (finite : epoch ≠ FAR_FUTURE_EPOCH)
    {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.addValidatorToRegistry at computed
  split at computed
  · exact absurd ‹_› (not_le_of_before before (Nat.le_refl _))
  split at computed
  · cases computed
    refine ⟨⟨1, ?_⟩, fun _ _ => rfl⟩
    have inactive : isActiveValidator
        (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount) epoch =
          false := by
      have below : ¬FAR_FUTURE_EPOCH ≤ epoch := by
        intro le
        apply finite
        have := UInt64.le_iff_toNat_le.mp le
        have := epoch.toNat_lt
        have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
        apply UInt64.toNat_inj.mp
        omega
      simp [isActiveValidator, getValidatorFromDeposit, below]
    simp [activity, inactive]
  · cases computed


theorem applyPendingDeposit (before : fork < .altair) (finite : epoch ≠ FAR_FUTURE_EPOCH)
    {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact addValidatorToRegistry before finite computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ refl _
  · rw [liftAccessor_ok] at computed
    exact increaseBalance computed

theorem processDeposit (before : fork < .altair) (finite : epoch ≠ FAR_FUTURE_EPOCH)
    {beforeHeze : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks beforeHeze state deposit = .ok after) :
    ShuffleKept epoch state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  unfold applyDeposit at applied
  split at applied
  · exact absurd ‹_› (not_le_of_before before (by decide))
  exact (of_eq (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl rfl).trans
    (applyPendingDeposit before finite applied)

theorem processVoluntaryExit (before : fork < .altair) (bound : epoch ≤ getCurrentEpoch state)
    {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact initiateValidatorExit (not_le_of_before before (by decide)) bound exited

/-- The RANDAO reveal writes the mix of the current epoch.

The seed of the epoch, or of the one before, does not read that mix. -/
theorem processRandao
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (bound : epoch ≤ getCurrentEpoch state)
    (near : (getCurrentEpoch state).toNat ≤ epoch.toNat + 1) {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    ShuffleKept epoch state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, written, rfl⟩ := processRandao_eq computed
  refine ⟨⟨0, by simp [activity]⟩, fun mixEpoch reads => ?_⟩
  exact mix_of_write lookahead written (UInt64.le_iff_toNat_le.mp bound) near mixEpoch reads

theorem processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : ShuffleKept epoch state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact of_eq rfl rfl

theorem processEth1Data {beforeHeze : fork < .hegota} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data beforeHeze state body = .ok after) :
    ShuffleKept epoch state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact of_eq (congrArg (·.validators.data) rest) (congrArg (·.randaoMixes) rest)


/-- Before Altair the operations keep the inputs of the shuffle of an epoch up to the current one.

That holds for the operations before the attestations too, the state the attestations start from.
-/
theorem processOperations (before : fork < .altair) (finite : epoch ≠ FAR_FUTURE_EPOCH)
    (bound : epoch ≤ getCurrentEpoch state) {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processOperations at computed
  split at computed
  · exact absurd ‹_› (not_le_of_before before (by decide))
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, slashed, proposersOk, attested, attestersOk, included, attestedOk,
    deposited, depositedOk, exited, exitsOk, changed, changesOk, requestsOk⟩ := computed
  -- Every operation keeps the slot, so the bound holds at each of them.
  have keptSlashed := Kept.foldlM (fun _ _ _ ok => kept_processProposerSlashing ok) proposersOk
  have keptAttested := Kept.foldlM (fun _ _ _ ok => kept_processAttesterSlashing ok) attestersOk
  have keptIncluded := Kept.foldlM (fun _ _ _ ok => kept_processAttestation ok) attestedOk
  have keptDeposited := Kept.foldlM (fun _ _ _ ok => kept_processDeposit ok) depositedOk
  have epochOf : ∀ {s t : BeaconState preset fork}, Kept s t →
      getCurrentEpoch t = getCurrentEpoch s := fun kept => by
    unfold getCurrentEpoch
    rw [kept.slot]
  have changes : changed = exited := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · exact absurd ‹_› (not_le_of_before before (by decide))
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk.symm
  have requests : after = changed := by
    split at requestsOk
    · rename_i electra
      exact absurd electra (not_le_of_before before (by decide))
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk.symm
  subst changes requests
  exact (foldlM (fun _ _ _ ok => kept_processProposerSlashing ok)
      (fun _ _ _ bound ok => processProposerSlashing before bound ok) bound proposersOk).trans <|
    (foldlM (fun _ _ _ ok => kept_processAttesterSlashing ok)
      (fun _ _ _ bound ok => processAttesterSlashing before bound ok)
      (epochOf keptSlashed ▸ bound) attestersOk).trans <|
    (foldlM (fun _ _ _ ok => kept_processAttestation ok)
      (fun _ _ _ _ ok => processAttestation before ok)
      (epochOf (keptSlashed.trans keptAttested) ▸ bound) attestedOk).trans <|
    (foldlM (fun _ _ _ ok => kept_processDeposit ok)
      (fun _ _ _ _ ok => processDeposit before finite ok)
      (epochOf (keptSlashed.trans keptAttested |>.trans keptIncluded) ▸ bound) depositedOk).trans <|
    foldlM (fun _ _ _ ok => kept_processVoluntaryExit ok)
      (fun _ _ _ bound ok => processVoluntaryExit before bound ok)
      (epochOf (keptSlashed.trans keptAttested |>.trans keptIncluded |>.trans keptDeposited) ▸
        bound) exitsOk

/-- Before Altair a block keeps the inputs of the shuffle of the current epoch and the one before.
-/
theorem processBlock {engine : ExecutionEngine preset fork} (before : fork < .altair)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (finite : epoch ≠ FAR_FUTURE_EPOCH) (bound : epoch ≤ getCurrentEpoch state)
    (near : (getCurrentEpoch state).toNat ≤ epoch.toNat + 1) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processBlock at computed
  split at computed
  · exact absurd ‹_› (not_le_of_before before (Nat.le_refl _))
  simp only [bind_ok_iff] at computed
  obtain ⟨headed, headerOk, revealed, randaoOk, voted, eth1Ok, operationsOk⟩ := computed
  have headedEpoch : getCurrentEpoch headed = getCurrentEpoch state := by
    obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headerOk
    rfl
  have keptVoted := (kept_processRandao randaoOk).trans (kept_processEth1Data eth1Ok)
  have votedEpoch : getCurrentEpoch voted = getCurrentEpoch state := by
    unfold getCurrentEpoch at headedEpoch ⊢
    rw [keptVoted.slot, headedEpoch]
  exact (processBlockHeader headerOk).trans <|
    (processRandao lookahead (headedEpoch ▸ bound) (headedEpoch ▸ near) randaoOk).trans <|
    (processEth1Data eth1Ok).trans
      (processOperations before finite (votedEpoch ▸ bound) operationsOk)

/-! ## The steps of an epoch, before Altair -/

/-- A validator at a position of the registry is active in the epoch exactly when it was. -/
theorem active_at (kept : ShuffleKept epoch state after) {position : Nat}
    (inside : position < state.validators.data.size) :
    (after.validators.data[position]?).map (isActiveValidator · epoch) =
      (state.validators.data[position]?).map (isActiveValidator · epoch) := by
  obtain ⟨_, active⟩ := kept.active
  have read := congrArg (·[position]?) active
  simp only [activity] at read
  rw [List.getElem?_append_left (by simpa using inside), List.getElem?_map, List.getElem?_map,
    Array.getElem?_toList, Array.getElem?_toList] at read
  exact read

theorem processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    ShuffleKept epoch state after ∧ after.slot = state.slot := by
  rcases processJustificationAndFinalization_ok computed with rfl | ⟨_, _, _, weighed⟩
  · exact ⟨refl _, rfl⟩
  · have rest := (weighJustificationAndFinalization_checkpoints weighed).2.2.2
    exact ⟨of_eq (congrArg (·.validators.data) rest) (congrArg (·.randaoMixes) rest),
      congrArg (·.slot) rest⟩

theorem applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : ShuffleKept epoch state after :=
  foldlM_ok_invariant (ShuffleKept epoch state) (fun _ _ _ held ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact held.trans ((increaseBalance raised).trans (decreaseBalance lowered))) (refl _) computed

theorem processRewardsAndPenalties (before : fork < .altair)
    (computed : processRewardsAndPenalties config state = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ refl _
  split at computed
  · exact absurd ‹_› (not_le_of_before before (Nat.le_refl _))
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact applyAllDeltas applied

/-- Joining the activation queue sets only the eligibility epoch. -/
theorem queueForActivation_active {validator queued : Validator}
    (computed : queueForActivation state validator = .ok queued) :
    isActiveValidator queued epoch = isActiveValidator validator epoch := by
  unfold queueForActivation at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    rw [computed]

theorem updateRegistryEntry (before : fork < .altair) (bound : epoch ≤ getCurrentEpoch state)
    {index : Nat} (computed : updateRegistryEntry config state index = .ok after) :
    ShuffleKept epoch state after := by
  simp only [EthLib.Consensus.updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, found, queued, queuedOk, marked, markedOk, computed⟩ := computed
  have set : ShuffleKept epoch state marked :=
    setValidator found markedOk (queueForActivation_active queuedOk)
  have sameEpoch : getCurrentEpoch marked = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [(kept_setValidator markedOk).slot]
  split at computed
  · exact set.trans (initiateValidatorExit (not_le_of_before before (by decide))
      (sameEpoch ▸ bound) (liftAccessor_ok.mp computed))
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

/-- Each index in the activation queue is the position of a validator with no activation epoch.
-/
theorem activationQueue_far {index : ValidatorIndex} (member : index ∈ activationQueue state) :
    ∃ (position : Nat) (validator : Validator), position.toUInt64 = index ∧
      state.validators.data[position]? = some validator ∧
      validator.activationEpoch = FAR_FUTURE_EPOCH := by
  simp only [activationQueue, List.mem_map, List.mem_mergeSort] at member
  obtain ⟨⟨eligibleEpoch, queuedIndex⟩, member, equal⟩ := member
  simp only [List.mem_filterMap] at member
  obtain ⟨⟨validator, position⟩, positionOk, selected⟩ := member
  split at selected
  · rename_i eligible
    simp only [Option.some.injEq, Prod.mk.injEq] at selected
    obtain ⟨_, rfl⟩ := selected
    simp only [isEligibleForActivation, Bool.and_eq_true, beq_iff_eq] at eligible
    refine ⟨position, validator, equal, ?_, eligible.2⟩
    simpa only [Array.getElem?_toList] using (List.mem_zipIdx_iff_getElem?.mp positionOk)
  · cases selected

/-- A fold of activations of validators that had no activation epoch in `start`.

Each one is activated past the current epoch, so it stays inactive in the epoch. -/
theorem foldActivateValidator {start : BeaconState preset fork}
    (finite : epoch ≠ FAR_FUTURE_EPOCH) (bound : epoch ≤ getCurrentEpoch start)
    (small : start.validators.data.size < 2 ^ 64) :
    ∀ {indices : List ValidatorIndex} {state after : BeaconState preset fork},
      (∀ index ∈ indices, ∃ (position : Nat) (validator : Validator), position.toUInt64 = index ∧
        start.validators.data[position]? = some validator ∧
        validator.activationEpoch = FAR_FUTURE_EPOCH) →
      Kept start state → ShuffleKept epoch start state →
      indices.foldlM activateValidator state = .ok after → ShuffleKept epoch start after
  | [], state, after, _, _, held, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ held
  | index :: rest, state, after, eligible, kept, held, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, first, tail⟩ := computed
    refine foldActivateValidator finite bound small (fun other member => eligible other
      (List.mem_cons_of_mem _ member)) (kept.trans (kept_activateValidator first)) ?_ tail
    refine held.trans ?_
    obtain ⟨position, validator, equal, found, far⟩ := eligible index List.mem_cons_self
    simp only [activateValidator, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff]
      at first
    obtain ⟨old, oldFound, activationEpoch, activationOk, set⟩ := first
    refine setValidator oldFound set ?_
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    have epochNat : epoch.toNat < 2 ^ 64 - 1 := by
      have := epoch.toNat_lt
      have : epoch.toNat ≠ 2 ^ 64 - 1 := fun same => finite (UInt64.toNat_inj.mp (by omega))
      omega
    have sameEpoch : getCurrentEpoch state = getCurrentEpoch start := by
      unfold getCurrentEpoch
      rw [kept.slot]
    -- The new activation epoch is past the current epoch, so past the epoch.
    have later := (computeActivationExitEpoch_ok_iff.mp activationOk).2
    rw [sameEpoch] at later
    have boundNat := UInt64.le_iff_toNat_le.mp bound
    have inactive : isActiveValidator { old with activationEpoch } epoch = false := by
      have : ¬activationEpoch ≤ epoch := fun le => by
        have := UInt64.le_iff_toNat_le.mp le
        omega
      simp [isActiveValidator, this]
    -- The old validator had no activation epoch in `start`, so it is not active either.
    have inside := (Array.getElem?_eq_some_iff.mp found).1
    have position_eq : index.toNat = position := by
      have below : position < 2 ^ 64 := by omega
      rw [← equal, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' below]
    have read : state.validators.data[position]? = some old := by
      unfold getValidator at oldFound
      rw [position_eq] at oldFound
      split at oldFound
      · rename_i read
        cases oldFound
        exact read
      · cases oldFound
    have same := held.active_at inside
    rw [read, found] at same
    simp only [Option.map_some, Option.some.injEq] at same
    rw [inactive, same]
    have : ¬FAR_FUTURE_EPOCH ≤ epoch := fun le => by
      have := UInt64.le_iff_toNat_le.mp le
      omega
    simp [isActiveValidator, far, this]

theorem processRegistryUpdates (before : fork < .altair) (finite : epoch ≠ FAR_FUTURE_EPOCH)
    (bound : epoch ≤ getCurrentEpoch state)
    (computed : processRegistryUpdates config state = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processRegistryUpdates at computed
  split at computed
  · exact absurd ‹_› (not_le_of_before before (by decide))
  simp only [bind_ok_iff] at computed
  obtain ⟨updated, updatedOk, activated⟩ := computed
  have first := foldlM (fun _ _ _ ok => kept_updateRegistryEntry ok)
    (fun _ _ _ bound ok => updateRegistryEntry before bound ok) bound updatedOk
  have kept := Kept.foldlM (fun _ _ _ ok => kept_updateRegistryEntry ok) updatedOk
  have updatedEpoch : getCurrentEpoch updated = getCurrentEpoch state := by
    unfold getCurrentEpoch
    rw [kept.slot]
  -- Before Gloas the registry is within its limit, below `2^64`.
  have small : updated.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (updated.validators.bound (Nat.lt_trans before (by decide)))
      (UInt64.toNat_lt _)
  exact first.trans (foldActivateValidator finite (updatedEpoch ▸ bound) small
    (fun index member => activationQueue_far (List.mem_of_mem_take member)) (Kept.refl _)
    (refl _) activated)

theorem processSlashings (before : fork < .altair)
    (computed : processSlashings state = .ok after) : ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · exact absurd ‹_› (not_le_of_before before (by decide))
  refine foldlM_ok_invariant (ShuffleKept epoch state) (fun _ _ _ held ok => held.trans ?_)
    (refl _) computed
  simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, ok⟩ := ok
  split at ok
  · simp only [bind_ok_iff] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, lowered⟩ := ok
      exact decreaseBalance lowered
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ refl _
  · simp only [pure, Except.pure, Except.ok.injEq] at ok
    exact ok ▸ refl _

theorem processEth1DataReset {beforeHeze : fork < .hegota}
    (computed : processEth1DataReset beforeHeze state = .ok after) :
    ShuffleKept epoch state after := by
  simp only [EthLib.Consensus.processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact of_eq rfl rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ refl _

theorem processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processEffectiveBalanceUpdates at computed
  refine foldlM_ok_invariant (ShuffleKept epoch state) (fun _ _ _ held ok => held.trans ?_)
    (refl _) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨validator, found, _, _, _, _, set⟩ := ok
  exact setValidator found set rfl

theorem processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    ShuffleKept epoch state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq computed
  exact of_eq rfl rfl

/-- The reset of the mixes writes the mix of the next epoch.

The seed of the epoch does not read it while the next epoch is at most one past the epoch. -/
theorem processRandaoMixesReset
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (bound : epoch ≤ getCurrentEpoch state)
    (near : (getCurrentEpoch state).toNat + 1 ≤ epoch.toNat + 1)
    (computed : processRandaoMixesReset state = .ok after) : ShuffleKept epoch state after := by
  obtain ⟨nextEpoch, _, _, nextEq, _, written, rfl⟩ := processRandaoMixesReset_eq computed
  refine ⟨⟨0, by simp [activity]⟩, fun mixEpoch reads => ?_⟩
  have boundNat := UInt64.le_iff_toNat_le.mp bound
  exact mix_of_write lookahead written (by omega) (by omega) mixEpoch reads

theorem processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact of_eq rfl rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ refl _

theorem processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact of_eq rfl rfl


/-- Before Altair the epoch transition at the end of the epoch keeps the inputs of its shuffle.
-/
theorem processEpoch (before : fork < .altair)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (finite : epoch ≠ FAR_FUTURE_EPOCH) (atEpoch : getCurrentEpoch state = epoch)
    (computed : processEpoch config checks state = .ok after) : ShuffleKept epoch state after := by
  unfold EthLib.Consensus.processEpoch at computed
  split at computed
  · exact absurd ‹_› (not_le_of_before before (Nat.le_refl _))
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  obtain ⟨first, justifiedSlot⟩ := processJustificationAndFinalization (epoch := epoch) justifiedOk
  -- Every step keeps the slot, so the current epoch stays the epoch.
  have epochOf : ∀ {t : BeaconState preset fork}, t.slot = state.slot →
      getCurrentEpoch t = epoch := fun same => by
    rw [← atEpoch]
    unfold getCurrentEpoch
    rw [same]
  have keptRewarded := kept_processRewardsAndPenalties rewardedOk
  have keptRegistered := keptRewarded.trans (kept_processRegistryUpdates registeredOk)
  have keptCleared := keptRegistered.trans (kept_processSlashings slashedOk) |>.trans
    (kept_processEth1DataReset resetOk) |>.trans (kept_processEffectiveBalanceUpdates balancedOk)
    |>.trans (kept_processSlashingsReset clearedOk)
  have bound : ∀ {t : BeaconState preset fork}, t.slot = state.slot → epoch ≤ getCurrentEpoch t :=
    fun same => by rw [epochOf same]; exact UInt64.le_refl _
  exact first.trans <| (processRewardsAndPenalties before rewardedOk).trans <|
    (processRegistryUpdates before finite (bound (keptRewarded.slot.trans justifiedSlot))
      registeredOk).trans <|
    (processSlashings before slashedOk).trans <| (processEth1DataReset resetOk).trans <|
    (processEffectiveBalanceUpdates balancedOk).trans <| (processSlashingsReset clearedOk).trans <|
    (processRandaoMixesReset lookahead (bound (keptCleared.slot.trans justifiedSlot))
      (by rw [epochOf (keptCleared.slot.trans justifiedSlot)]; exact Nat.le_refl _)
      mixedOk).trans <|
    (processHistoricalRootsUpdate rootedOk).trans (processParticipationRecordUpdates rotated)

/-- The caching of a slot keeps the registry and the mixes. -/
theorem processSlot (computed : processSlot state = .ok after) : ShuffleKept epoch state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact of_eq rfl rfl


end ShuffleKept

end EthLib.Consensus
