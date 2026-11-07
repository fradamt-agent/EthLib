module

public import EthLib.Consensus.Proofs.Transition.Provenance.Ancestry
public import EthLib.Consensus.Proofs.Transition.Provenance.Voters

/-!
# Proofs: a counted vote names the source and the target of its weighing call

A weighing call justifies a checkpoint of the previous or current epoch.

Its supermajority link runs from a source checkpoint to that target.

The source is the justified checkpoint of the target's epoch.

It is the current justified one while that epoch runs, and the previous one in the epoch after.

An attestation is checked against the same rule when a block includes it.

So a counted vote names the call's target, and the call's source.

Two facts of chains make that work.

- Within one epoch the justified checkpoints stay: only the end of an epoch writes them.
- The end of an epoch makes the current justified checkpoint the previous one.

The second fails at the end of epoch 1, which weighs nothing.

So for a target in epoch 1 the source agrees only when the chain's two justified checkpoints did.

From a genesis state both are the genesis checkpoint, so they agree.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- Along a chain the epoch never decreases. -/
theorem Reaches.epoch_le {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) :
    (getCurrentEpoch start.state).toNat ≤ (getCurrentEpoch after.state).toNat := by
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat]
  exact Nat.div_le_div_right chain.slot_le

/-- A slot step that closes its epoch moves the epoch on by one. -/
theorem epoch_of_closes {next : BeaconState preset fork}
    (slot : next.slot.toNat = state.slot.toNat + 1) (closes : ClosesEpoch preset state) :
    (getCurrentEpoch next).toNat = (getCurrentEpoch state).toNat + 1 := by
  have fits : state.slot.toNat + 1 < 2 ^ 64 := slot ▸ UInt64.toNat_lt next.slot
  rw [closesEpoch_iff fits] at closes
  rw [getCurrentEpoch_toNat, getCurrentEpoch_toNat, slot, Nat.succ_div]
  simp [closes]

/-- A slot step that does not close its epoch keeps the epoch. -/
theorem epoch_of_open {next : BeaconState preset fork}
    (slot : next.slot.toNat = state.slot.toNat + 1) (notClosing : ¬ClosesEpoch preset state) :
    getCurrentEpoch next = getCurrentEpoch state := by
  have same := flagsEpoch_of_open slot notClosing true
  simpa [flagsEpoch] using same

/-- Within one epoch of a chain, the justified checkpoints stay. -/
theorem Reaches.justified_of_same_epoch {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after)
    (same : getCurrentEpoch after.state = getCurrentEpoch start.state) :
    after.state.previousJustifiedCheckpoint = start.state.previousJustifiedCheckpoint ∧
      after.state.currentJustifiedCheckpoint = start.state.currentJustifiedCheckpoint := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | @snoc middle last run step more =>
    have middleLe := Reaches.epoch_le (config := config) (checks := checks) ⟨run⟩
    have lastLe := (Reaches.refl (config := config) (checks := checks) middle).step step
    have stepLe := lastLe.epoch_le
    have middleSame : getCurrentEpoch middle.state = getCurrentEpoch start.state := by
      apply UInt64.toNat_inj.mp
      rw [← same] at middleLe ⊢
      omega
    obtain ⟨previous, current⟩ := more middleSame
    rw [← previous, ← current]
    cases step with
    | @slot fork state next notDue computed =>
      obtain ⟨_, _, stepSlot, -, -, -, closing⟩ := advanceSlot_history computed
      split at closing
      · next closes =>
        exfalso
        have := epoch_of_closes stepSlot closes
        simp only at same middleSame this
        rw [middleSame, ← same] at this
        omega
      · exact ⟨closing.2.1, closing.2.2.1⟩
    | upgrade due computed =>
      have same := upgradeNext_history computed
      simp only [BeaconState.history, Prod.mk.injEq] at same
      exact ⟨same.2.2.2.2.2.1, same.2.2.2.2.2.2.1⟩
    | block engine signed validateResult notDue computed =>
      have frame := frame_processBlock (applySignedBlock_ok computed).2.1
      exact ⟨frame.previousJustified, frame.currentJustified⟩

/-- Across the end of an epoch that weighs, the current justified checkpoint becomes the previous.

The epoch must be at least two, since the first two epochs weigh nothing. -/
theorem Reaches.previousJustified_of_next_epoch {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after)
    (next : (getCurrentEpoch after.state).toNat = (getCurrentEpoch start.state).toNat + 1)
    (weighs : GENESIS_EPOCH + 1 < getCurrentEpoch start.state) :
    after.state.previousJustifiedCheckpoint = start.state.currentJustifiedCheckpoint := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => omega
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    have middleLe := middleChain.epoch_le
    have stepLe := ((Reaches.refl (config := config) (checks := checks) middle).step step).epoch_le
    by_cases moved : (getCurrentEpoch middle.state).toNat = (getCurrentEpoch start.state).toNat + 1
    · -- The epoch had already moved on: this step stays in it and keeps the checkpoints.
      have stays : getCurrentEpoch last.state = getCurrentEpoch middle.state :=
        UInt64.toNat_inj.mp (by omega)
      rw [← more moved]
      exact (((Reaches.refl _).step step).justified_of_same_epoch stays).1
    · -- This step ends the epoch of the start, so it weighs.
      have startEpoch : getCurrentEpoch middle.state = getCurrentEpoch start.state :=
        UInt64.toNat_inj.mp (by omega)
      have kept := middleChain.justified_of_same_epoch startEpoch
      cases step with
      | @slot fork state nextState notDue computed =>
        obtain ⟨cached, cachedOk, stepSlot, -, -, -, closing⟩ := advanceSlot_history computed
        split at closing
        · obtain ⟨weighed, weighedOk, -, previousSame, -, -⟩ := closing
          simp only at kept startEpoch ⊢
          rw [previousSame, ← kept.2]
          have cachedSame : cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
              getCurrentEpoch cached = getCurrentEpoch state := by
            obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
            exact ⟨rfl, rfl⟩
          rcases processJustificationAndFinalization_weighs weighedOk with ⟨early, _⟩ |
            ⟨_, _, _, _, _, _, _, _, _, _, _, weighs'⟩
          · rw [cachedSame.2, startEpoch] at early
            exact absurd early (UInt64.not_le.mpr weighs)
          · rw [(weighJustificationAndFinalization_checkpoints weighs').1, cachedSame.1]
        · next notClosing =>
          have := epoch_of_open stepSlot notClosing
          simp only at this next startEpoch
          rw [this, startEpoch] at next
          omega
      | @upgrade _ post due computed =>
        have same := upgradeNext_history computed
        simp only [BeaconState.history, Prod.mk.injEq] at same
        have : getCurrentEpoch post.val.state = getCurrentEpoch middle.state := by
          simp only [getCurrentEpoch, same.1]
        rw [this, startEpoch] at next
        omega
      | @block fork engine signed validateResult state post notDue computed =>
        have postSlot := processBlock_slot (applySignedBlock_ok computed).2.1
        have : getCurrentEpoch post = getCurrentEpoch state := by
          simp only [getCurrentEpoch, postSlot]
        simp only at next startEpoch
        rw [this, startEpoch] at next
        omega

/-! ## Reads of the block roots -/

/-- A read of the root of an epoch's first block, and what it checked. -/
theorem getBlockRoot_ok {epoch : Epoch} {root : Root}
    (computed : getBlockRoot state epoch = .ok root) :
    ∃ slot : Slot, slot.toNat = epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ∧
      slot.toNat < state.slot.toNat ∧
      state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ∧
      readCircular state.blockRoots.elements slot = .ok root := by
  simp only [getBlockRoot, getBlockRootAtSlot, bind_ok_iff, liftArith, mapError_ok_iff,
    computeStartSlotAtEpoch, mulChecked_ok_iff] at computed
  obtain ⟨slot, ⟨_, slotEq⟩, computed⟩ := computed
  refine ⟨slot, slotEq, ?_⟩
  split at computed
  · next before =>
    cases sumOk : addChecked slot preset.SLOTS_PER_HISTORICAL_ROOT with
    | error _ =>
      simp only [sumOk, Except.mapError, bind, Except.bind, reduceCtorEq] at computed
    | ok sum =>
      simp only [sumOk, Except.mapError, bind, Except.bind] at computed
      split at computed
      · next within =>
        obtain ⟨_, sumEq⟩ := addChecked_ok_iff.mp sumOk
        refine ⟨UInt64.lt_iff_toNat_lt.mp before, ?_, computed⟩
        rw [← sumEq]
        exact UInt64.le_iff_toNat_le.mp within
      · simp only [throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · cases computed

/-- A read of an epoch's first block root depends only on the slot and the block roots. -/
theorem getBlockRoot_congr {other : BeaconState preset fork} (slot : other.slot = state.slot)
    (blockRoots : other.blockRoots = state.blockRoots) (epoch : Epoch) :
    getBlockRoot other epoch = getBlockRoot state epoch := by
  simp only [getBlockRoot, getBlockRootAtSlot, slot, blockRoots]

/-- An attestation's target is the previous or the current epoch of its site, at every fork. -/
theorem processAttestation_recent {attestation : Attestation preset fork} {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    attestation.data.target.epoch = getPreviousEpoch state ∨
      attestation.data.target.epoch = getCurrentEpoch state := by
  by_cases altair : .altair ≤ fork
  · have stepAltair : processAttestationAltair config checks state attestation altair parentSlot =
        .ok after := by
      unfold processAttestation at computed
      simpa only [altair, ↓reduceDIte] using computed
    obtain ⟨_, _, _, _, _, _, _, recent, -⟩ := processAttestationAltair_votes stepAltair
    exact recent
  · exact (processAttestation_checks (Nat.lt_of_not_le altair) computed).1

/-- The source that a weighing call gives the votes for an epoch.

It is the current justified checkpoint for the current epoch, and the previous one otherwise. -/
def recordSource (state : BeaconState preset fork) (epoch : Epoch) : Checkpoint :=
  if epoch = getCurrentEpoch state then state.currentJustifiedCheckpoint
  else state.previousJustifiedCheckpoint

/-- A root that a weighing call reads is the root its state held before the caching.

The call reads the first slot of the previous or the current epoch.

The buffer of roots must span two epochs, so the caching wrote another entry. -/
theorem processSlot_read
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {cached : BeaconState preset fork} (cachedOk : processSlot state = .ok cached)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch cached) {epoch : Epoch} {root : Root}
    (recent : epoch = getPreviousEpoch cached ∨ epoch = getCurrentEpoch cached)
    (rootOk : getBlockRoot cached epoch = .ok root) :
    ∃ slot : Slot, slot.toNat = epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ∧
      slot.toNat < state.slot.toNat ∧
      state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ∧
      readCircular state.blockRoots.elements slot = .ok root := by
  obtain ⟨slot, slotEq, below, near, read⟩ := getBlockRoot_ok rootOk
  have sameSlot : cached.slot = state.slot := processSlot_slot cachedOk
  obtain ⟨_, blockRoot, _, _, _, _, blockWrite, _⟩ := processSlot_roots cachedOk
  have epochs : (getCurrentEpoch cached).toNat ≤ epoch.toNat + 1 := by
    have := getPreviousEpoch_toNat cached
    rcases recent with same | same <;> rw [same] <;> omega
  have epochNat := getCurrentEpoch_toNat cached
  rw [sameSlot] at epochNat near below
  have spe : 0 < preset.SLOTS_PER_EPOCH.toNat := by
    -- With no slot in an epoch, every epoch is the genesis epoch, which weighs nothing.
    rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
    · rw [zero, Nat.div_zero] at epochNat
      have weighs := UInt64.lt_iff_toNat_lt.mp later
      rw [epochNat] at weighs
      simp [GENESIS_EPOCH] at weighs
    · exact positive
  -- The state is in the epoch or the one after, so at most two epochs past the slot.
  have other : state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
      slot % preset.SLOTS_PER_HISTORICAL_ROOT := by
    refine mod_ne_of_lt below ?_
    have inEpoch : state.slot.toNat < preset.SLOTS_PER_EPOCH.toNat *
        (state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) := Nat.lt_mul_div_succ _ spe
    have bound : preset.SLOTS_PER_EPOCH.toNat *
          (state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1) ≤
        preset.SLOTS_PER_EPOCH.toNat * (epoch.toNat + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have expand : preset.SLOTS_PER_EPOCH.toNat * (epoch.toNat + 2) =
        epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + 2 * preset.SLOTS_PER_EPOCH.toNat := by
      rw [Nat.mul_add, Nat.mul_comm]
      omega
    omega
  refine ⟨slot, slotEq, below, near, ?_⟩
  rw [← readCircular_writeCircular_of_ne blockWrite other]
  exact read

/-- The root a call reads for the previous or the current epoch is the state's entry for it.

That entry is the one for the epoch's first slot.

The buffer of roots must span two epochs. -/
theorem ReadsFrom.read
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    {cached : BeaconState preset fork} (readsFrom : ReadsFrom state cached)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch cached) {epoch : Epoch} {root : Root}
    (recent : epoch = getPreviousEpoch cached ∨ epoch = getCurrentEpoch cached)
    (rootOk : getBlockRoot cached epoch = .ok root) :
    ∃ slot : Slot, slot.toNat = epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ∧
      slot.toNat < state.slot.toNat ∧
      state.slot.toNat ≤ slot.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat ∧
      readCircular state.blockRoots.elements slot = .ok root := by
  rcases readsFrom with cachedOk | rfl
  · exact processSlot_read wide cachedOk later recent rootOk
  · exact getBlockRoot_ok rootOk

/-- The source of a signed vote read at a weighing call is the call's source.

The attestation's site and the call read the justified checkpoint of the same epoch.

For a target in epoch 1 the source may instead be the current justified checkpoint of epoch 1.

That is, of a state of epoch 1 of the chain, since the end of epoch 1 weighs nothing. -/
theorem SignedVote.source_link {start : ForkedBeaconState preset} {fork : Fork}
    {state cached : BeaconState preset fork} {checkpoint : Checkpoint} {index : ValidatorIndex}
    {data : AttestationData}
    (signed : SignedVote config checks start ⟨fork, state⟩ index data)
    (epoch : data.target.epoch = checkpoint.epoch) (readsFrom : ReadsFrom state cached)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch cached)
    (recent : checkpoint.epoch = getPreviousEpoch cached ∨
      checkpoint.epoch = getCurrentEpoch cached) :
    data.source = recordSource cached checkpoint.epoch ∨
      (checkpoint.epoch.toNat = 1 ∧ ∃ (fork' : Fork) (epochOne : BeaconState preset fork'),
        Reaches config checks start ⟨fork', epochOne⟩ ∧
        Reaches config checks ⟨fork', epochOne⟩ ⟨fork, state⟩ ∧
        (getCurrentEpoch epochOne).toNat = 1 ∧
        data.source = epochOne.currentJustifiedCheckpoint) := by
  obtain ⟨forkB, engine, block, validateResult, stateB, postB, first, site, recorded, pre, suf,
    attestation, indexed, headB, notDueB, applied, tailB, kept, split, prefixOk, siteOk, reads,
    sameData, indexedOk, attesting, indexedData, valid, source⟩ := signed
  -- The chain runs from the block's state to the call's state.
  have chainB : Reaches config checks ⟨forkB, stateB⟩ ⟨fork, state⟩ :=
    ((Reaches.refl _).step (.block engine block validateResult notDueB applied)).trans tailB
  -- The caching keeps the slot, the checkpoints and the epoch.
  have cachedSame : cached.slot = state.slot ∧
      cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
      cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint := by
    obtain ⟨_, _, _, _, rfl⟩ := readsFrom.eq
    exact ⟨rfl, rfl, rfl⟩
  have cachedEpoch : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, cachedSame.1]
  have siteEpoch : getCurrentEpoch site = getCurrentEpoch stateB := by
    simp only [getCurrentEpoch, reads.slot]
  -- The attestation and the call read the justified checkpoint of one epoch.
  have siteRecent := processAttestation_recent siteOk
  have sitePrevious : getPreviousEpoch site = getPreviousEpoch stateB := by
    unfold getPreviousEpoch
    rw [siteEpoch]
  have cachedPrevious : getPreviousEpoch cached = getPreviousEpoch state := by
    unfold getPreviousEpoch
    rw [cachedEpoch]
  rw [sameData, epoch, siteEpoch, sitePrevious] at siteRecent
  rw [epoch, siteEpoch, reads.currentJustifiedCheckpoint, reads.previousJustifiedCheckpoint]
    at source
  rw [cachedEpoch, cachedPrevious] at recent
  rw [cachedEpoch] at later
  unfold recordSource
  rw [cachedEpoch, cachedSame.2.1, cachedSame.2.2, source]
  -- The same facts on natural numbers.
  have ordered := chainB.epoch_le
  simp only at ordered
  have siteNat : checkpoint.epoch.toNat = (getCurrentEpoch stateB).toNat - 1 ∨
      checkpoint.epoch.toNat = (getCurrentEpoch stateB).toNat := by
    rcases siteRecent with same | same <;> rw [same]
    · exact .inl (getPreviousEpoch_toNat stateB)
    · exact .inr rfl
  have stateNat : checkpoint.epoch.toNat = (getCurrentEpoch state).toNat - 1 ∨
      checkpoint.epoch.toNat = (getCurrentEpoch state).toNat := by
    rcases recent with same | same <;> rw [same]
    · exact .inl (getPreviousEpoch_toNat state)
    · exact .inr rfl
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  simp only [GENESIS_EPOCH] at laterNat
  change 0 + 1 < _ at laterNat
  by_cases sameEpoch : getCurrentEpoch state = getCurrentEpoch stateB
  · obtain ⟨previous, current⟩ := chainB.justified_of_same_epoch sameEpoch
    simp only at previous current
    rw [sameEpoch, previous, current]
    exact .inl rfl
  · -- The call is in the epoch after the attestation's, which is the target's.
    have differ : (getCurrentEpoch state).toNat ≠ (getCurrentEpoch stateB).toNat :=
      fun same => sameEpoch (UInt64.toNat_inj.mp same)
    have targetIsSite : checkpoint.epoch = getCurrentEpoch stateB :=
      UInt64.toNat_inj.mp (by omega)
    have notState : checkpoint.epoch ≠ getCurrentEpoch state :=
      fun same => differ (by rw [← same, targetIsSite])
    rw [ite_eq_left_of_eq_true _ _ (eq_true targetIsSite),
      ite_eq_right_of_eq_false _ _ (eq_false notState)]
    by_cases first : checkpoint.epoch.toNat = 1
    · refine .inr ⟨first, forkB, stateB, headB, chainB, ?_, rfl⟩
      rw [← targetIsSite]
      exact first
    · left
      have next : (getCurrentEpoch state).toNat = (getCurrentEpoch stateB).toNat + 1 := by
        omega
      have weighs : GENESIS_EPOCH + 1 < getCurrentEpoch stateB := by
        apply UInt64.lt_iff_toNat_lt.mpr
        change 0 + 1 < _
        omega
      exact (chainB.previousJustified_of_next_epoch next weighs).symm



/-- A signed target read at a weighing call is the call's checkpoint, with the call's source.

The attestation's site and the call read the same entry of the buffer of roots for the target.

They also read the justified checkpoint of the same epoch, except for a target in epoch 1. -/
theorem SignedTarget.link {start : ForkedBeaconState preset} {fork : Fork}
    {state cached : BeaconState preset fork} {checkpoint : Checkpoint} {index : ValidatorIndex}
    {data : AttestationData}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (signed : SignedTarget config checks start ⟨fork, state⟩ index data)
    (epoch : data.target.epoch = checkpoint.epoch) (readsFrom : ReadsFrom state cached)
    (later : GENESIS_EPOCH + 1 < getCurrentEpoch cached)
    (recent : checkpoint.epoch = getPreviousEpoch cached ∨
      checkpoint.epoch = getCurrentEpoch cached)
    (rootOk : getBlockRoot cached checkpoint.epoch = .ok checkpoint.root) :
    data.target = checkpoint ∧
      (data.source = recordSource cached checkpoint.epoch ∨
        (checkpoint.epoch.toNat = 1 ∧ ∃ (fork' : Fork) (epochOne : BeaconState preset fork'),
          Reaches config checks start ⟨fork', epochOne⟩ ∧
          Reaches config checks ⟨fork', epochOne⟩ ⟨fork, state⟩ ∧
          (getCurrentEpoch epochOne).toNat = 1 ∧
          data.source = epochOne.currentJustifiedCheckpoint)) := by
  refine ⟨?_, SignedVote.source_link signed.vote epoch readsFrom later recent⟩
  obtain ⟨forkB, engine, block, validateResult, stateB, postB, first, site, recorded, pre, suf,
    attestation, indexed, headB, notDueB, applied, tailB, kept, split, prefixOk, siteOk, reads,
    sameData, indexedOk, attesting, indexedData, valid, source, targetRoot⟩ := signed
  -- The chain runs from the block's state to the call's state.
  have chainB : Reaches config checks ⟨forkB, stateB⟩ ⟨fork, state⟩ :=
    ((Reaches.refl _).step (.block engine block validateResult notDueB applied)).trans tailB
  -- The call's read is the state's entry for the epoch's first slot.
  obtain ⟨slot', slotEq', below', near', stateRead⟩ := readsFrom.read wide later recent rootOk
  -- The site's read takes the same entry.
  have siteRead := targetRoot
  rw [getBlockRoot_congr reads.slot reads.blockRoots] at siteRead
  obtain ⟨slot, slotEq, below, near, read⟩ := getBlockRoot_ok siteRead
  rw [epoch] at slotEq
  have sameSlot : slot' = slot := UInt64.toNat_inj.mp (slotEq'.trans slotEq.symm)
  subst sameSlot
  have stable := (chainB.roots_stable (slot := slot') below near').1
  simp only at stable
  rw [stateRead, read] at stable
  have sameRoot := Except.ok.inj stable
  cases checkpoint
  cases dataTarget : data.target
  rw [dataTarget] at epoch sameRoot
  simp only at epoch sameRoot
  rw [epoch, sameRoot]

/-- From Altair, a counted voter of a weighing call signed the call's link.

Take a weighing call of a chain that justified a checkpoint, at a fork from Altair on.

The epochs of the buffer of roots must span two epochs: `2 * SLOTS_PER_EPOCH ≤ N`.

Each counted voter signed attestation data whose target is the checkpoint.

Its source is the call's source for that epoch.

For a target in epoch 1 the source may instead be the current justified checkpoint of epoch 1.

That is, of a state of epoch 1 of the chain, since the end of epoch 1 weighs nothing.

The flag may also come from the start of the chain, or from the upgrade to Altair. -/
theorem CallRecord.voters_signed {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    .altair ≤ fork → ∀ index ∈ voters,
      FlagAtStart start index.toNat TIMELY_TARGET_FLAG_INDEX ∨
      FlagFromAltairUpgrade config checks start ⟨fork, state⟩ index.toNat
        TIMELY_TARGET_FLAG_INDEX checkpoint.epoch ∨
      ∃ data, data.target = checkpoint ∧
        SignedTarget config checks start ⟨fork, state⟩ index data ∧
        (data.source = recordSource cached checkpoint.epoch ∨
          (checkpoint.epoch.toNat = 1 ∧ ∃ (fork' : Fork) (epochOne : BeaconState preset fork'),
            Reaches config checks start ⟨fork', epochOne⟩ ∧
            Reaches config checks ⟨fork', epochOne⟩ ⟨fork, state⟩ ∧
            (getCurrentEpoch epochOne).toNat = 1 ∧
            data.source = epochOne.currentJustifiedCheckpoint)) := by
  intro altair index member
  rcases TargetVoters.origin altair call.head call.reads call.recent call.counted member with
    atStart | upgraded | ⟨data, epoch, signed⟩
  · exact .inl atStart
  · exact .inr (.inl upgraded)
  have link := SignedTarget.link wide signed epoch call.reads call.later call.recent call.rootOk
  exact .inr (.inr ⟨data, link.1, signed, link.2⟩)

/-- `CallRecord.voters_signed` for a weighing call at an epoch boundary. -/
theorem WeighingCall.voters_signed {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed next : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (call : WeighingCall config checks start after fork state cached weighed next voters
      checkpoint) :
    .altair ≤ fork → ∀ index ∈ voters,
      FlagAtStart start index.toNat TIMELY_TARGET_FLAG_INDEX ∨
      FlagFromAltairUpgrade config checks start ⟨fork, state⟩ index.toNat
        TIMELY_TARGET_FLAG_INDEX checkpoint.epoch ∨
      ∃ data, data.target = checkpoint ∧
        SignedTarget config checks start ⟨fork, state⟩ index data ∧
        (data.source = recordSource cached checkpoint.epoch ∨
          (checkpoint.epoch.toNat = 1 ∧ ∃ (fork' : Fork) (epochOne : BeaconState preset fork'),
            Reaches config checks start ⟨fork', epochOne⟩ ∧
            Reaches config checks ⟨fork', epochOne⟩ ⟨fork, state⟩ ∧
            (getCurrentEpoch epochOne).toNat = 1 ∧
            data.source = epochOne.currentJustifiedCheckpoint)) :=
  call.record.voters_signed wide

/-- `WeighingCall.voters_signed` for a call that `JustifiedBy` names. -/
theorem JustifiedBy.voters_signed {start after : ForkedBeaconState preset}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (justified : JustifiedBy config checks start after checkpoint) :
    ∃ (fork : Fork) (state cached : BeaconState preset fork) (voters : List ValidatorIndex),
      Reaches config checks start ⟨fork, state⟩ ∧
      Reaches config checks ⟨fork, state⟩ after ∧ processSlot state = .ok cached ∧
      GENESIS_EPOCH + 1 < getCurrentEpoch cached ∧
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
      TargetVoters cached checkpoint.epoch voters ∧ PassesThreshold cached voters ∧
      getBlockRoot cached checkpoint.epoch = .ok checkpoint.root ∧
      (.altair ≤ fork → ∀ index ∈ voters,
        FlagAtStart start index.toNat TIMELY_TARGET_FLAG_INDEX ∨
        FlagFromAltairUpgrade config checks start ⟨fork, state⟩ index.toNat
          TIMELY_TARGET_FLAG_INDEX checkpoint.epoch ∨
        ∃ data, data.target = checkpoint ∧
          SignedTarget config checks start ⟨fork, state⟩ index data ∧
          (data.source = recordSource cached checkpoint.epoch ∨
            (checkpoint.epoch.toNat = 1 ∧ ∃ (fork' : Fork) (epochOne : BeaconState preset fork'),
              Reaches config checks start ⟨fork', epochOne⟩ ∧
              Reaches config checks ⟨fork', epochOne⟩ ⟨fork, state⟩ ∧
              (getCurrentEpoch epochOne).toNat = 1 ∧
              data.source = epochOne.currentJustifiedCheckpoint))) := by
  obtain ⟨fork, state, cached, _, _, voters, call⟩ := justified
  exact ⟨fork, state, cached, voters, call.head, call.toAfter, call.cachedOk, call.later,
    call.recent, call.counted, call.passes, call.rootOk, call.voters_signed wide⟩

/-! ## Justification bits -/

/-- A block keeps the justification bits. -/
theorem applySignedBlock_bits {engine : ExecutionEngine preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : applySignedBlock config checks engine state signed validateResult = .ok after) :
    after.justificationBits = state.justificationBits := by
  obtain ⟨-, processed, -⟩ := applySignedBlock_ok computed
  obtain ⟨paid, headed, paidKept, headedOk, headedKept⟩ := processBlock_kept processed
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
  exact headedKept.justificationBits.trans paidKept.justificationBits

/-- A state after a weighing call is at least in epoch three.

The call reads epoch two or later, and closes that epoch. -/
theorem JustifiedBy.late {start after : ForkedBeaconState preset} {checkpoint : Checkpoint}
    (justified : JustifiedBy config checks start after checkpoint) :
    3 ≤ (getCurrentEpoch after.state).toNat := by
  obtain ⟨fork, state, cached, _, next, _, _, _, nextOk, tail, closes, cachedOk, _, later, _⟩ :=
    justified
  have nextEpoch := epoch_of_closes (advanceSlot_slot nextOk) closes
  have cachedEpoch : getCurrentEpoch cached = getCurrentEpoch state := by
    simp only [getCurrentEpoch, processSlot_slot cachedOk]
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  rw [cachedEpoch] at laterNat
  change 0 + 1 < _ at laterNat
  have := tail.epoch_le
  simp only at this
  omega

/-- Where a set justification bit of a chain's end comes from.

Bit `i` stands for the epoch `i` epochs before the previous epoch.

Either the start of the chain had some bit set.

Or a weighing call of the chain justified a checkpoint of that epoch. -/
theorem Reaches.justificationBit {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) (index : Nat)
    (inside : index < JUSTIFICATION_BITS_LENGTH.toNat)
    (set : after.state.justificationBits.bits[index] = true) :
    (∃ (other : Nat) (inside : other < JUSTIFICATION_BITS_LENGTH.toNat),
        start.state.justificationBits.bits[other] = true) ∨
      ∃ checkpoint : Checkpoint,
        checkpoint.epoch.toNat + index = (getPreviousEpoch after.state).toNat ∧
        JustifiedBy config checks start after checkpoint := by
  obtain ⟨run⟩ := chain
  induction run generalizing index with
  | nil => exact .inl ⟨index, inside, set⟩
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    cases step with
    | @slot fork state next notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, next⟩ := .slot notDue computed
      obtain ⟨cached, cachedOk, stepSlot, -, -, -, closing⟩ := advanceSlot_history computed
      have cachedSame : cached.justificationBits = state.justificationBits ∧
          getCurrentEpoch cached = getCurrentEpoch state := by
        obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
        exact ⟨rfl, rfl⟩
      split at closing
      · next closes =>
        obtain ⟨weighed, weighedOk, bitsSame, -, -, -⟩ := closing
        simp only at set ⊢
        rw [bitsSame] at set
        have previousNext := getPreviousEpoch_of_closes stepSlot closes
        rcases processJustificationAndFinalization_bits weighedOk with ⟨early, rfl⟩ |
          ⟨later, bit0, bit1, bit2, bit3⟩
        · -- The first two epochs keep the bits; no call ran before them.
          rw [cachedSame.1] at set
          rcases more index inside set with atStart | ⟨checkpoint, -, justified⟩
          · exact .inl atStart
          · exfalso
            have := justified.late
            have earlyNat := UInt64.le_iff_toNat_le.mp early
            rw [cachedSame.2] at earlyNat
            change _ ≤ 0 + 1 at earlyNat
            simp only at this
            omega
        · rw [cachedSame.2] at later
          have laterNat := UInt64.lt_iff_toNat_lt.mp later
          change 0 + 1 < _ at laterNat
          have previousMiddle := getPreviousEpoch_toNat state
          rw [previousNext]
          -- A bit the call set stands for a checkpoint it justified.
          have record : ∀ {epoch : Epoch} {voters root},
              (epoch = getPreviousEpoch cached ∨ epoch = getCurrentEpoch cached) →
              TargetVoters cached epoch voters → PassesThreshold cached voters →
              getBlockRoot cached epoch = .ok root →
              JustifiedBy config checks start ⟨fork, next⟩ ⟨epoch, root⟩ :=
            fun recent votersAre passes rootOk =>
              ⟨fork, state, cached, weighed, next, _, middleChain, notDue, computed, .refl _,
                closes, cachedOk, weighedOk, by rw [cachedSame.2]; exact later, recent, votersAre,
                passes, rootOk⟩
          have cachedPrevious : getPreviousEpoch cached = getPreviousEpoch state := by
            unfold getPreviousEpoch
            rw [cachedSame.2]
          -- A bit moved from before stands for the same epoch, one place further back.
          have moved : ∀ (older : Nat) (olderInside : older < JUSTIFICATION_BITS_LENGTH.toNat),
              state.justificationBits.bits[older] = true →
              (∃ (other : Nat) (inside : other < JUSTIFICATION_BITS_LENGTH.toNat),
                  start.state.justificationBits.bits[other] = true) ∨
                ∃ checkpoint : Checkpoint,
                  checkpoint.epoch.toNat + (older + 1) = (getCurrentEpoch state).toNat ∧
                  JustifiedBy config checks start ⟨fork, next⟩ checkpoint := by
            intro older olderInside old
            rcases more older olderInside old with atStart | ⟨checkpoint, epoch, justified⟩
            · exact .inl atStart
            · exact .inr ⟨checkpoint, by simp only at epoch; omega, justified.extend theStep⟩
          rcases index with _ | _ | _ | _ | index
          · obtain ⟨voters, root, votersAre, passes, rootOk⟩ := bit0 set
            exact .inr ⟨⟨_, root⟩, by simp only [cachedSame.2, Nat.add_zero],
              record (.inr rfl) votersAre passes rootOk⟩
          · rcases bit1 set with ⟨voters, root, votersAre, passes, rootOk⟩ | old
            · refine .inr ⟨⟨_, root⟩, ?_, record (.inl rfl) votersAre passes rootOk⟩
              simp only
              rw [cachedPrevious, previousMiddle]
              omega
            · exact moved 0 (by decide) (cachedSame.1 ▸ old)
          · rw [bit2] at set
            exact moved 1 (by decide) (cachedSame.1 ▸ set)
          · rw [bit3] at set
            exact moved 2 (by decide) (cachedSame.1 ▸ set)
          · exact absurd inside (by simp [JUSTIFICATION_BITS_LENGTH])
      · next notClosing =>
        obtain ⟨bitsSame, -, -, -⟩ := closing
        simp only at set ⊢
        rw [bitsSame] at set
        have sameEpoch := epoch_of_open stepSlot notClosing
        have previousSame : getPreviousEpoch next = getPreviousEpoch state := by
          unfold getPreviousEpoch
          rw [sameEpoch]
        rw [previousSame]
        rcases more index inside set with atStart | ⟨checkpoint, epoch, justified⟩
        · exact .inl atStart
        · exact .inr ⟨checkpoint, epoch, justified.extend theStep⟩
    | @upgrade _ post due computed =>
      have theStep : Step config checks middle post.val := .upgrade due computed
      have same := upgradeNext_history computed
      simp only [BeaconState.history, Prod.mk.injEq] at same
      have previousSame : getPreviousEpoch post.val.state = getPreviousEpoch middle.state := by
        simp only [getPreviousEpoch, getCurrentEpoch, same.1]
      rw [same.2.2.2.2.1] at set
      rw [previousSame]
      rcases more index inside set with atStart | ⟨checkpoint, epoch, justified⟩
      · exact .inl atStart
      · exact .inr ⟨checkpoint, epoch, justified.extend theStep⟩
    | @block fork engine signed validateResult state post notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, post⟩ :=
        .block engine signed validateResult notDue computed
      have postSlot := processBlock_slot (applySignedBlock_ok computed).2.1
      have previousSame : getPreviousEpoch post = getPreviousEpoch state := by
        simp only [getPreviousEpoch, getCurrentEpoch, postSlot]
      simp only at set ⊢
      rw [applySignedBlock_bits computed] at set
      rw [previousSame]
      rcases more index inside set with atStart | ⟨checkpoint, epoch, justified⟩
      · exact .inl atStart
      · exact .inr ⟨checkpoint, epoch, justified.extend theStep⟩

/-! ## Finalization -/

/-- A weighing call of a chain finalized a checkpoint by one of its four rules.

The rules read the new justification bits, which the state after the slot step holds.

- The old current justified checkpoint, with bits 0 to 2 set and two epochs back.
- The same, with bits 0 and 1 set and one epoch back.
- Otherwise the old previous justified checkpoint, with bits 1 to 3 set and three epochs back.
- The same, with bits 1 and 2 set and two epochs back.

Bit `i` stands for the epoch `i` epochs before the current epoch of the call. -/
def FinalizedBy (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset)
    (checkpoint : Checkpoint) : Prop :=
  ∃ (fork : Fork) (state cached weighed next : BeaconState preset fork),
    Reaches config checks start ⟨fork, state⟩ ∧ upgradeDue config ⟨fork, state⟩ = false ∧
    advanceSlot config checks state = .ok next ∧ Reaches config checks ⟨fork, next⟩ after ∧
    ClosesEpoch preset state ∧ processSlot state = .ok cached ∧
    processJustificationAndFinalization cached = .ok weighed ∧
    GENESIS_EPOCH + 1 < getCurrentEpoch cached ∧
    next.justificationBits = weighed.justificationBits ∧
    ((checkpoint = cached.currentJustifiedCheckpoint ∧
        ((next.justificationBits.bits[0] && next.justificationBits.bits[1] &&
            next.justificationBits.bits[2] &&
            decide (cached.currentJustifiedCheckpoint.epoch.toNat + 2 =
              (getCurrentEpoch cached).toNat)) ||
          (next.justificationBits.bits[0] && next.justificationBits.bits[1] &&
            decide (cached.currentJustifiedCheckpoint.epoch.toNat + 1 =
              (getCurrentEpoch cached).toNat))) = true) ∨
      (checkpoint = cached.previousJustifiedCheckpoint ∧
        ((next.justificationBits.bits[1] && next.justificationBits.bits[2] &&
            next.justificationBits.bits[3] &&
            decide (cached.previousJustifiedCheckpoint.epoch.toNat + 3 =
              (getCurrentEpoch cached).toNat)) ||
          (next.justificationBits.bits[1] && next.justificationBits.bits[2] &&
            decide (cached.previousJustifiedCheckpoint.epoch.toNat + 2 =
              (getCurrentEpoch cached).toNat))) = true))

theorem FinalizedBy.extend {start middle after : ForkedBeaconState preset} {checkpoint : Checkpoint}
    (finalized : FinalizedBy config checks start middle checkpoint)
    (step : Step config checks middle after) : FinalizedBy config checks start after checkpoint :=
  have ⟨fork, state, cached, weighed, next, head, notDue, nextOk, tail, rest⟩ := finalized
  ⟨fork, state, cached, weighed, next, head, notDue, nextOk, tail.step step, rest⟩

/-- Where the finalized checkpoint of a chain's end comes from.

It is the start's, or the last weighing call that changed it finalized it by one of its rules.
-/
theorem Reaches.finalized {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after) :
    after.state.finalizedCheckpoint = start.state.finalizedCheckpoint ∨
      FinalizedBy config checks start after after.state.finalizedCheckpoint := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact .inl rfl
  | @snoc middle last run step more =>
    have middleChain : Reaches config checks start middle := ⟨run⟩
    cases step with
    | @slot fork state next notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, next⟩ := .slot notDue computed
      obtain ⟨cached, cachedOk, -, -, -, -, closing⟩ := advanceSlot_history computed
      have cachedSame : cached.finalizedCheckpoint = state.finalizedCheckpoint := by
        obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
        rfl
      split at closing
      · next closes =>
        obtain ⟨weighed, weighedOk, bitsSame, -, -, finalizedSame⟩ := closing
        simp only at more ⊢
        rw [finalizedSame]
        rcases processJustificationAndFinalization_weighs weighedOk with ⟨_, rfl⟩ |
          ⟨later, _, _, _, _, _, _, _, _, _, _, weighs⟩
        · rw [cachedSame]
          exact more.imp id (·.extend theStep)
        obtain ⟨_, _, _, _, _, _, _, _, _, finalizedRule, -⟩ :=
          weighJustificationAndFinalization_eq weighs
        rw [← bitsSame] at finalizedRule
        split at finalizedRule
        · next byCurrent =>
          exact .inr ⟨fork, state, cached, weighed, next, middleChain, notDue, computed, .refl _,
            closes, cachedOk, weighedOk, later, bitsSame, .inl ⟨finalizedRule, byCurrent⟩⟩
        · split at finalizedRule
          · next byPrevious =>
            exact .inr ⟨fork, state, cached, weighed, next, middleChain, notDue, computed,
              .refl _, closes, cachedOk, weighedOk, later, bitsSame,
              .inr ⟨finalizedRule, byPrevious⟩⟩
          · rw [finalizedRule, cachedSame]
            exact more.imp id (·.extend theStep)
      · obtain ⟨-, -, -, finalizedSame⟩ := closing
        simp only at more ⊢
        rw [finalizedSame]
        exact more.imp id (·.extend theStep)
    | @upgrade _ post due computed =>
      have same := upgradeNext_history computed
      simp only [BeaconState.history, Prod.mk.injEq] at same
      rw [same.2.2.2.2.2.2.2]
      exact more.imp id (·.extend (.upgrade due computed))
    | @block fork engine signed validateResult state post notDue computed =>
      have frame := frame_processBlock (applySignedBlock_ok computed).2.1
      simp only at more ⊢
      rw [frame.finalized]
      exact more.imp id (·.extend (.block engine signed validateResult notDue computed))

end EthLib.Consensus
