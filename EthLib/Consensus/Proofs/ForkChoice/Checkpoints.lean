module

public import EthLib.Consensus.Proofs.ForkChoice.Reachable

/-!
# Proofs: the order of the checkpoints of a store

The finalized epoch of a reachable store is at most its justified epoch.

The same holds for the unrealized checkpoints, which become those of the store at a new epoch.

The anchor state must keep the invariant of the state transition, as a genesis state does.

Each valid block then keeps that invariant in the state after it, whose checkpoints are in order.

A block writes the checkpoints of such a state, and those it reaches at the end of its epoch.

A new epoch writes the unrealized checkpoints, which are in order too.

From Gloas, a vote of the payload committee and an envelope keep the checkpoints.

From Heze, an inclusion list keeps them too.

Each checkpoint of a reachable store is the anchor checkpoint, or a checkpoint of a kept state.

Or it is a checkpoint of a kept state after the justification and finalization of an epoch.

Every kept state is the anchor state, or the state after a valid block applied to a kept state.

The finalized block need not be an ancestor of the justified block.

The store raises its justified and its finalized checkpoint separately, from any valid block.

A block is checked only to descend from the finalized block of the store at that time.

So the store can first take a justified checkpoint at epoch e+2 from one branch.

It can then take a finalized checkpoint at epoch e from another branch.

That branch has justified epoch e+1, so the justified checkpoint stays in place.

The two checkpoints then conflict, which needs a third of the stake to sign slashable votes.

So the store only gives a disjunction: descent, or two conflicting checkpoints from its states.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Fork}

namespace Store

/-- The finalized epoch is at most the justified epoch, for both pairs of checkpoints. -/
def EpochsOrdered (store : Store preset fork) : Prop :=
  store.finalizedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch ∧
    store.unrealizedFinalizedCheckpoint.epoch ≤ store.unrealizedJustifiedCheckpoint.epoch

/-- Every state that the store keeps for a block keeps the invariant of the state transition. -/
def StatesHold (store : Store preset fork) : Prop :=
  ∀ {root : Root} {state : BeaconState preset fork},
    store.blockStates[root]? = some state → Invariant state

variable {config : Config} {store after : Store preset fork}

theorem StatesHold.of_eq (holds : store.StatesHold)
    (states : after.blockStates = store.blockStates) : after.StatesHold := by
  intro root state found
  rw [states] at found
  exact holds found

/-- The finalized epoch of an ordered state is at most its current justified epoch. -/
theorem finalized_le_currentJustified {state : BeaconState preset fork}
    (ordered : CheckpointsOrdered state) :
    state.finalizedCheckpoint.epoch ≤ state.currentJustifiedCheckpoint.epoch :=
  UInt64.le_trans ordered.1 ordered.2

private theorem le_of_not_lt' {a b : UInt64} (h : ¬ a < b) : b ≤ a := by
  rw [UInt64.lt_iff_toNat_lt] at h
  rw [UInt64.le_iff_toNat_le]
  omega

/-- Replacing the checkpoints by an ordered pair keeps them ordered. -/
theorem updateCheckpoints_ordered {justified finalized : Checkpoint}
    (ordered : store.EpochsOrdered) (le : finalized.epoch ≤ justified.epoch) :
    (store.updateCheckpoints justified finalized).EpochsOrdered := by
  unfold updateCheckpoints EpochsOrdered
  obtain ⟨o1, o2⟩ := ordered
  by_cases j : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.finalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [j, f, ↓reduceIte] <;> refine ⟨?_, o2⟩
  · exact le
  · exact UInt64.le_trans o1 (UInt64.le_of_lt j)
  · exact UInt64.le_trans le (le_of_not_lt' j)
  · exact o1

/-- Replacing the unrealized checkpoints by an ordered pair keeps them ordered. -/
theorem updateUnrealizedCheckpoints_ordered {justified finalized : Checkpoint}
    (ordered : store.EpochsOrdered) (le : finalized.epoch ≤ justified.epoch) :
    (store.updateUnrealizedCheckpoints justified finalized).EpochsOrdered := by
  unfold updateUnrealizedCheckpoints EpochsOrdered
  obtain ⟨o1, o2⟩ := ordered
  by_cases j : store.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases f : store.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [j, f, ↓reduceIte] <;> refine ⟨o1, ?_⟩
  · exact le
  · exact UInt64.le_trans o2 (UInt64.le_of_lt j)
  · exact UInt64.le_trans le (le_of_not_lt' j)
  · exact o2

/-- The tip pulled up to the end of its epoch keeps the checkpoints ordered. -/
theorem computePulledUpTip_ordered {root : Root}
    (ordered : store.EpochsOrdered) (holds : store.StatesHold)
    (pulled : store.computePulledUpTip config root = .ok after) : after.EpochsOrdered := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨state, found, pulledState, weighed, block, -, epoch, -, pulled⟩ := pulled
  have invariant : Invariant state := holds (blockState_ok_iff.mp found)
  have le := finalized_le_currentJustified
    (processJustificationAndFinalization_ordered invariant.ordered invariant.settled
      (Base.mapError_ok_iff.mp weighed)).1
  have unrealized := updateUnrealizedCheckpoints_ordered (store := { store with
    unrealizedJustifications :=
      store.unrealizedJustifications.insert root pulledState.currentJustifiedCheckpoint })
    ordered le
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled
  · exact updateCheckpoints_ordered unrealized le
  · exact unrealized

/-- A tick within a slot keeps the checkpoints ordered. -/
theorem onTickPerSlot_ordered {timeMs : UInt64} (ordered : store.EpochsOrdered)
    (ticked : store.onTickPerSlot config timeMs = .ok after) : after.EpochsOrdered := by
  unfold onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    · obtain ⟨_, _, ticked⟩ := ticked
      split at ticked <;> simp only [pure, Except.pure, Except.ok.injEq] at ticked <;>
        subst ticked
      · exact updateCheckpoints_ordered ordered ordered.2
      · exact ordered

/-- The catch-up loop keeps the checkpoints ordered. -/
theorem catchUp_ordered {tickSlot : Slot} {start : Store preset fork}
    (ordered : start.EpochsOrdered) (caught : catchUp config start tickSlot = .ok after) :
    after.EpochsOrdered := by
  induction start using catchUp.induct config tickSlot with
  | _ start ih =>
    rw [catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTimeMs, -, ticked, tick, caught⟩ := caught
      split at caught
      · exact ih ticked ‹_› (onTickPerSlot_ordered ordered tick) caught
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst caught
      exact ordered

/-- A tick keeps the checkpoints ordered. -/
theorem onTick_ordered {timeMs : UInt64} (ordered : store.EpochsOrdered)
    (ticked : store.onTick config timeMs = .ok after) : after.EpochsOrdered := by
  unfold onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨tickSlot, -, caught, caughtUp, ticked⟩ := ticked
  exact onTickPerSlot_ordered (catchUp_ordered ordered caughtUp) ticked

/-- An attestation keeps the checkpoints. -/
theorem onAttestation_ordered {checks : SignatureChecks} {attestation : Attestation preset fork}
    {isFromBlock : Bool} (ordered : store.EpochsOrdered)
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    after.EpochsOrdered := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, valid, _, attested⟩ := attested
  have kept : stored.EpochsOrdered := by
    unfold storeTargetCheckpointState at storing
    split at storing
    · simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      exact ordered
    · simp only [bind_ok_iff] at storing
      obtain ⟨_, _, storing⟩ := storing
      simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      exact ordered
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    exact kept
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

/-- An attester slashing keeps the checkpoints. -/
theorem onAttesterSlashing_ordered {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork} (ordered : store.EpochsOrdered)
    (slashed : store.onAttesterSlashing config checks slashing = .ok after) :
    after.EpochsOrdered := by
  unfold onAttesterSlashing at slashed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
  obtain ⟨_, _, slashed⟩ := slashed
  subst slashed
  exact ordered

/-- From Gloas, a vote of the payload committee keeps the checkpoints. -/
theorem onPayloadAttestationMessage_ordered {checks : SignatureChecks}
    {gloas : .glamsterdam ≤ fork} {message : PayloadAttestationMessage} {isFromBlock : Bool}
    (ordered : store.EpochsOrdered)
    (voted : store.onPayloadAttestationMessage config checks gloas message isFromBlock =
      .ok after) :
    after.EpochsOrdered := by
  obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
  exact ordered

/-- From Gloas, an accepted envelope keeps the checkpoints. -/
theorem onExecutionPayloadEnvelope_ordered {checks : SignatureChecks}
    {sources : BlockSources preset fork} {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadEnvelope preset fork} (ordered : store.EpochsOrdered)
    (accepted : store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after) :
    after.EpochsOrdered := by
  obtain ⟨_, _, _, _, _, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
  obtain ⟨_, rfl⟩ := recordEnvelope_frame record
  exact ordered

/-- From Heze, an accepted inclusion list keeps the checkpoints. -/
theorem onInclusionList_ordered {checks : SignatureChecks} {heze : .hegota ≤ fork}
    {signed : SignedInclusionList} (ordered : store.EpochsOrdered)
    (accepted : store.onInclusionList config checks heze signed = .ok after) :
    after.EpochsOrdered := by
  obtain ⟨_, _, rfl⟩ := onInclusionList_ok heze accepted
  exact ordered

/-- A block keeps the state of each block within the invariant. -/
theorem onBlock_statesHold {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    (holds : store.StatesHold) (added : store.onBlock config checks sources signed = .ok after) :
    after.StatesHold := by
  obtain same | ⟨blockRoot, -, -, -, pre, state, found, transition, states⟩ :=
    onBlock_same_or_insert added
  · subst same
    exact holds
  intro root kept keptFound
  rw [states, Std.TreeMap.getElem?_insert] at keptFound
  split at keptFound
  · cases keptFound
    exact (stateTransition_invariant (holds found) transition).1
  · exact holds keptFound

/-- A block keeps the checkpoints ordered, when each state of the store keeps the invariant. -/
theorem onBlock_ordered {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    (ordered : store.EpochsOrdered) (holds : store.StatesHold)
    (added : store.onBlock config checks sources signed = .ok after) : after.EpochsOrdered := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e =>
    simp [onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases known : store.blocks.contains blockRoot
    · rw [onBlock_known root known] at added
      cases added
      exact ordered
    simp only [onBlock, root, known, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := recordBlockPtcVotes_onlyPtcVotes vote
    obtain ⟨pre, found, -, -, transition⟩ := validateOnBlock_ok valid
    have invariant := (stateTransition_invariant (holds found) transition).1
    have recordedOrdered : recorded.EpochsOrdered := by
      unfold recordBlockTimeliness at record
      simp only [bind_ok_iff, pure, Except.pure] at record
      obtain ⟨_, _, _, _, _, _, _, _, record⟩ := record
      split at record
      · simp only [bind_ok_iff, Except.ok.injEq] at record
        obtain ⟨_, _, rfl⟩ := record
        exact ordered
      · cases record
        exact ordered
    have boostedOrdered : boosted.EpochsOrdered := by
      unfold updateProposerBoostRoot at boost
      split at boost
      rotate_left
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at boost
      simp only [bind_ok_iff, pure_bind] at boost
      obtain ⟨_, _, _, _, _, _, boost⟩ := boost
      split at boost <;> simp only [pure, Except.pure, Except.ok.injEq] at boost <;>
        subst boost <;> exact recordedOrdered
    have statesHold : (boosted.updateCheckpoints state.currentJustifiedCheckpoint
        state.finalizedCheckpoint).StatesHold := by
      refine StatesHold.of_eq (store := { store with
        blocks := store.blocks.insert blockRoot signed.message
        blockStates := store.blockStates.insert blockRoot state }) ?_ ?_
      · intro root kept keptFound
        simp only [Std.TreeMap.getElem?_insert] at keptFound
        split at keptFound
        · cases keptFound
          exact invariant
        · exact holds keptFound
      · rw [updateCheckpoints_blockStates, (updateProposerBoostRoot_frame boost).2.2,
          (recordBlockTimeliness_frame record).2.2]
    exact computePulledUpTip_ordered
      (updateCheckpoints_ordered boostedOrdered (finalized_le_currentJustified invariant.ordered))
      statesHold added

end Store


/-! ## Where the checkpoints come from -/

namespace Store

variable {config : Config} {store after : Store preset fork}
  {states : Std.TreeMap Root (BeaconState preset fork)} {anchor : Checkpoint}

/-- A checkpoint that comes from some states, as a field of a state.

It is the anchor checkpoint, or the field of one of the states.

Or it is the field of one of the states after the justification and finalization of an epoch. -/
def CheckpointFrom (states : Std.TreeMap Root (BeaconState preset fork)) (anchor : Checkpoint)
    (field : BeaconState preset fork → Checkpoint) (checkpoint : Checkpoint) : Prop :=
  checkpoint = anchor ∨
    (∃ (root : Root) (state : BeaconState preset fork),
      states[root]? = some state ∧ checkpoint = field state) ∨
    ∃ (root : Root) (state pulled : BeaconState preset fork), states[root]? = some state ∧
      processJustificationAndFinalization state = .ok pulled ∧ checkpoint = field pulled

/-- Each checkpoint of a store comes from some states.

The justified checkpoints are current justified checkpoints of states.

The finalized checkpoints are finalized checkpoints of states. -/
structure CheckpointsFrom (store : Store preset fork)
    (states : Std.TreeMap Root (BeaconState preset fork)) (anchor : Checkpoint) : Prop where
  justified : CheckpointFrom states anchor (·.currentJustifiedCheckpoint) store.justifiedCheckpoint
  finalized : CheckpointFrom states anchor (·.finalizedCheckpoint) store.finalizedCheckpoint
  unrealizedJustified :
    CheckpointFrom states anchor (·.currentJustifiedCheckpoint) store.unrealizedJustifiedCheckpoint
  unrealizedFinalized :
    CheckpointFrom states anchor (·.finalizedCheckpoint) store.unrealizedFinalizedCheckpoint

/-- Every state that a map keeps is the anchor state, or the state after a valid block.

That block is applied to a state that the map keeps. -/
def StatesReached (config : Config) (anchorState : BeaconState preset fork)
    (states : Std.TreeMap Root (BeaconState preset fork)) : Prop :=
  ∀ {root : Root} {state : BeaconState preset fork}, states[root]? = some state →
    state = anchorState ∨ ∃ (parentRoot : Root) (pre : BeaconState preset fork)
      (checks : SignatureChecks) (sources : BlockSources preset fork),
      ∃ signed : SignedBeaconBlock preset fork, states[parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre signed true = .ok state

/-- Each state that the store keeps belongs to a known block. -/
def StatesKnown (store : Store preset fork) : Prop :=
  ∀ {root : Root} {state : BeaconState preset fork}, store.blockStates[root]? = some state →
    store.blocks.contains root = true

/-- Two stores with the same four checkpoints. -/
def SameCheckpoints (store after : Store preset fork) : Prop :=
  after.justifiedCheckpoint = store.justifiedCheckpoint ∧
    after.finalizedCheckpoint = store.finalizedCheckpoint ∧
    after.unrealizedJustifiedCheckpoint = store.unrealizedJustifiedCheckpoint ∧
    after.unrealizedFinalizedCheckpoint = store.unrealizedFinalizedCheckpoint

theorem CheckpointFrom.mono {field : BeaconState preset fork → Checkpoint} {checkpoint : Checkpoint}
    {larger : Std.TreeMap Root (BeaconState preset fork)}
    (sub : ∀ {root : Root} {state : BeaconState preset fork}, states[root]? = some state →
      larger[root]? = some state)
    (holds : CheckpointFrom states anchor field checkpoint) :
    CheckpointFrom larger anchor field checkpoint := by
  rcases holds with same | ⟨root, state, found, same⟩ | ⟨root, state, pulled, found, ok, same⟩
  · exact Or.inl same
  · exact Or.inr (Or.inl ⟨root, state, sub found, same⟩)
  · exact Or.inr (Or.inr ⟨root, state, pulled, sub found, ok, same⟩)

theorem CheckpointsFrom.mono {larger : Std.TreeMap Root (BeaconState preset fork)}
    (sub : ∀ {root : Root} {state : BeaconState preset fork}, states[root]? = some state →
      larger[root]? = some state)
    (holds : store.CheckpointsFrom states anchor) : store.CheckpointsFrom larger anchor :=
  ⟨holds.1.mono sub, holds.2.mono sub, holds.3.mono sub, holds.4.mono sub⟩

theorem CheckpointsFrom.of_same (holds : store.CheckpointsFrom states anchor)
    (same : SameCheckpoints store after) : after.CheckpointsFrom states anchor := by
  obtain ⟨j, f, uj, uf⟩ := same
  exact ⟨j ▸ holds.1, f ▸ holds.2, uj ▸ holds.3, uf ▸ holds.4⟩

/-- Raising the checkpoints to a pair from the states keeps them from the states. -/
theorem CheckpointsFrom.updateCheckpoints {justified finalized : Checkpoint}
    (holds : store.CheckpointsFrom states anchor)
    (justifiedFrom : CheckpointFrom states anchor (·.currentJustifiedCheckpoint) justified)
    (finalizedFrom : CheckpointFrom states anchor (·.finalizedCheckpoint) finalized) :
    (store.updateCheckpoints justified finalized).CheckpointsFrom states anchor := by
  obtain ⟨j, f, uj, uf⟩ := holds
  unfold Store.updateCheckpoints
  by_cases hj : store.justifiedCheckpoint.epoch < justified.epoch <;>
    by_cases hf : store.finalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [hj, hf, ↓reduceIte] <;> exact ⟨by assumption, by assumption, uj, uf⟩

/-- Raising the unrealized checkpoints to a pair from the states keeps them from the states. -/
theorem CheckpointsFrom.updateUnrealizedCheckpoints {justified finalized : Checkpoint}
    (holds : store.CheckpointsFrom states anchor)
    (justifiedFrom : CheckpointFrom states anchor (·.currentJustifiedCheckpoint) justified)
    (finalizedFrom : CheckpointFrom states anchor (·.finalizedCheckpoint) finalized) :
    (store.updateUnrealizedCheckpoints justified finalized).CheckpointsFrom states anchor := by
  obtain ⟨j, f, uj, uf⟩ := holds
  unfold Store.updateUnrealizedCheckpoints
  by_cases hj : store.unrealizedJustifiedCheckpoint.epoch < justified.epoch <;>
    by_cases hf : store.unrealizedFinalizedCheckpoint.epoch < finalized.epoch <;>
    simp only [hj, hf, ↓reduceIte] <;> exact ⟨j, f, by assumption, by assumption⟩

/-- The tip pulled up to the end of its epoch keeps the checkpoints from the states.

The states must hold every state of the store. -/
theorem computePulledUpTip_checkpointsFrom {root : Root}
    (holds : store.CheckpointsFrom states anchor)
    (sub : ∀ {root : Root} {state : BeaconState preset fork},
      store.blockStates[root]? = some state → states[root]? = some state)
    (pulled : store.computePulledUpTip config root = .ok after) :
    after.CheckpointsFrom states anchor := by
  unfold computePulledUpTip at pulled
  simp only [bind_ok_iff] at pulled
  obtain ⟨state, found, pulledState, weighed, block, -, epoch, -, pulled⟩ := pulled
  have weighedOk := Base.mapError_ok_iff.mp weighed
  have kept := sub (blockState_ok_iff.mp found)
  have justifiedFrom : CheckpointFrom states anchor (·.currentJustifiedCheckpoint)
      pulledState.currentJustifiedCheckpoint :=
    Or.inr (Or.inr ⟨root, state, _, kept, weighedOk, rfl⟩)
  have finalizedFrom : CheckpointFrom states anchor (·.finalizedCheckpoint)
      pulledState.finalizedCheckpoint := Or.inr (Or.inr ⟨root, state, _, kept, weighedOk, rfl⟩)
  have unrealized := CheckpointsFrom.updateUnrealizedCheckpoints (store := { store with
    unrealizedJustifications :=
      store.unrealizedJustifications.insert root pulledState.currentJustifiedCheckpoint })
    (holds.of_same ⟨rfl, rfl, rfl, rfl⟩) justifiedFrom finalizedFrom
  split at pulled <;> simp only [pure, Except.pure, Except.ok.injEq] at pulled <;> subst pulled
  · exact unrealized.updateCheckpoints justifiedFrom finalizedFrom
  · exact unrealized

/-- A tick within a slot keeps the checkpoints from the states. -/
theorem onTickPerSlot_checkpointsFrom {timeMs : UInt64}
    (holds : store.CheckpointsFrom states anchor)
    (ticked : store.onTickPerSlot config timeMs = .ok after) :
    after.CheckpointsFrom states anchor := by
  unfold onTickPerSlot at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨previous, -, current, -, ticked⟩ := ticked
  split at ticked <;>
    · obtain ⟨_, _, ticked⟩ := ticked
      split at ticked <;> simp only [pure, Except.pure, Except.ok.injEq] at ticked <;>
        subst ticked
      · exact CheckpointsFrom.updateCheckpoints (holds.of_same ⟨rfl, rfl, rfl, rfl⟩) holds.3
          holds.4
      · exact holds.of_same ⟨rfl, rfl, rfl, rfl⟩

/-- The catch-up loop keeps the checkpoints from the states. -/
theorem catchUp_checkpointsFrom {tickSlot : Slot} {start : Store preset fork}
    (holds : start.CheckpointsFrom states anchor)
    (caught : catchUp config start tickSlot = .ok after) : after.CheckpointsFrom states anchor := by
  induction start using catchUp.induct config tickSlot with
  | _ start ih =>
    rw [catchUp.eq_1] at caught
    simp only [bind_ok_iff] at caught
    obtain ⟨current, -, caught⟩ := caught
    split at caught
    · simp only [bind_ok_iff] at caught
      obtain ⟨next, -, nextTimeMs, -, ticked, tick, caught⟩ := caught
      split at caught
      · exact ih ticked ‹_› (onTickPerSlot_checkpointsFrom holds tick) caught
      · cases caught
    · simp only [pure, Except.pure, Except.ok.injEq] at caught
      subst caught
      exact holds

/-- A tick keeps the checkpoints from the states. -/
theorem onTick_checkpointsFrom {timeMs : UInt64} (holds : store.CheckpointsFrom states anchor)
    (ticked : store.onTick config timeMs = .ok after) : after.CheckpointsFrom states anchor := by
  unfold onTick at ticked
  simp only [bind_ok_iff] at ticked
  obtain ⟨tickSlot, -, caught, caughtUp, ticked⟩ := ticked
  exact onTickPerSlot_checkpointsFrom (catchUp_checkpointsFrom holds caughtUp) ticked

/-- An attestation keeps the checkpoints. -/
theorem onAttestation_sameCheckpoints {checks : SignatureChecks}
    {attestation : Attestation preset fork} {isFromBlock : Bool}
    (attested : store.onAttestation config checks attestation isFromBlock = .ok after) :
    SameCheckpoints store after := by
  unfold onAttestation at attested
  simp only [bind_ok_iff] at attested
  obtain ⟨_, _, stored, storing, _, _, _, _, valid, _, attested⟩ := attested
  have kept : SameCheckpoints store stored := by
    unfold storeTargetCheckpointState at storing
    split at storing
    · simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [bind_ok_iff] at storing
      obtain ⟨_, _, storing⟩ := storing
      simp only [pure, Except.pure, Except.ok.injEq] at storing
      subst storing
      exact ⟨rfl, rfl, rfl, rfl⟩
  split at attested
  · simp only [pure, Except.pure, Except.ok.injEq] at attested
    subst attested
    exact kept
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at attested

/-- An attester slashing keeps the checkpoints. -/
theorem onAttesterSlashing_sameCheckpoints {checks : SignatureChecks}
    {slashing : AttesterSlashing preset fork}
    (slashed : store.onAttesterSlashing config checks slashing = .ok after) :
    SameCheckpoints store after := by
  unfold onAttesterSlashing at slashed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at slashed
  obtain ⟨_, _, slashed⟩ := slashed
  subst slashed
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Recording the timeliness of a block keeps the checkpoints. -/
theorem recordBlockTimeliness_sameCheckpoints {root : Root}
    (recorded : store.recordBlockTimeliness config root = .ok after) :
    SameCheckpoints store after := by
  unfold recordBlockTimeliness at recorded
  simp only [bind_ok_iff, pure, Except.pure] at recorded
  obtain ⟨_, _, _, _, _, _, _, _, recorded⟩ := recorded
  split at recorded
  · simp only [bind_ok_iff, Except.ok.injEq] at recorded
    obtain ⟨_, _, rfl⟩ := recorded
    exact ⟨rfl, rfl, rfl, rfl⟩
  · cases recorded
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Updating the boost keeps the checkpoints. -/
theorem updateProposerBoostRoot_sameCheckpoints {head root : Root}
    (updated : store.updateProposerBoostRoot config head root = .ok after) :
    SameCheckpoints store after := by
  unfold updateProposerBoostRoot at updated
  split at updated
  rotate_left
  · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at updated
  simp only [bind_ok_iff, pure_bind] at updated
  obtain ⟨_, _, _, _, _, _, updated⟩ := updated
  split at updated <;> simp only [pure, Except.pure, Except.ok.injEq] at updated <;>
    subst updated <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- A new block keeps the checkpoints from the states, its own state included.

Its state goes in at a root that held no state. -/
theorem onBlock_checkpointsFrom {checks : SignatureChecks}
    {sources : BlockSources preset fork} {signed : SignedBeaconBlock preset fork}
    (holds : store.CheckpointsFrom store.blockStates anchor) (known : store.StatesKnown)
    (added : store.onBlock config checks sources signed = .ok after) :
    after.CheckpointsFrom after.blockStates anchor := by
  cases root : SszType.hashTreeRoot signed.message with
  | error e =>
    simp [onBlock, root, bind, Except.bind, Except.mapError] at added
  | ok blockRoot =>
    by_cases contained : store.blocks.contains blockRoot
    · rw [onBlock_known root contained] at added
      cases added
      exact holds
    simp only [onBlock, root, contained, bind, Except.bind, Except.mapError, ↓reduceIte,
      Bool.false_eq_true] at added
    unfold addBlock at added
    simp only [bind_ok_iff] at added
    obtain ⟨state, valid, head, -, voted, vote, recorded, record, boosted, boost, added⟩ := added
    obtain ⟨_, _, rfl⟩ := recordBlockPtcVotes_onlyPtcVotes vote
    -- The new state goes in at a root that held none, so every state stays.
    have fresh : store.blockStates[blockRoot]? = none := by
      cases kept : store.blockStates[blockRoot]? with
      | none => rfl
      | some s => exact absurd (known kept) contained
    let states := store.blockStates.insert blockRoot state
    have sub : ∀ {r : Root} {s : BeaconState preset fork}, store.blockStates[r]? = some s →
        states[r]? = some s := by
      intro r s found
      simp only [states, getElem?_insert_root]
      split
      · rename_i same
        rw [← same, fresh] at found
        cases found
      · exact found
    have mine : states[blockRoot]? = some state := by simp [states]
    have recordedFrom : recorded.CheckpointsFrom states anchor := by
      have same := recordBlockTimeliness_sameCheckpoints record
      exact CheckpointsFrom.of_same (CheckpointsFrom.of_same (holds.mono sub) ⟨rfl, rfl, rfl, rfl⟩)
        same
    have boostedFrom := recordedFrom.of_same (updateProposerBoostRoot_sameCheckpoints boost)
    have updatedFrom :=
      boostedFrom.updateCheckpoints (Or.inr (Or.inl ⟨blockRoot, state, mine, rfl⟩))
      (Or.inr (Or.inl ⟨blockRoot, state, mine, rfl⟩))
    have boostedStates : boosted.blockStates = states := by
      rw [(updateProposerBoostRoot_frame boost).2.2, (recordBlockTimeliness_frame record).2.2]
    have afterFrom := computePulledUpTip_checkpointsFrom updatedFrom
      (fun found => by rwa [updateCheckpoints_blockStates, boostedStates] at found) added
    have afterStates : after.blockStates = states := by
      rw [(computePulledUpTip_frame added).2.2, updateCheckpoints_blockStates, boostedStates]
    exact afterStates ▸ afterFrom

/-- Raising the checkpoints can keep the justified checkpoint and take a new finalized one.

That happens when the new justified epoch is not above the store's, and the new finalized epoch is.

No condition relates the root of the justified checkpoint to that of the finalized one. -/
theorem updateCheckpoints_of_not_lt_of_lt {justified finalized : Checkpoint}
    (keep : ¬ store.justifiedCheckpoint.epoch < justified.epoch)
    (raise : store.finalizedCheckpoint.epoch < finalized.epoch) :
    (store.updateCheckpoints justified finalized).justifiedCheckpoint = store.justifiedCheckpoint ∧
      (store.updateCheckpoints justified finalized).finalizedCheckpoint = finalized := by
  unfold Store.updateCheckpoints
  simp [keep, raise]

/-- A state that goes in at a free root keeps every kept state reached from the anchor.

It must be the state after a valid block, applied to a kept state. -/
theorem StatesReached.insert {anchorState pre state : BeaconState preset fork}
    {root parentRoot : Root}
    {checks : SignatureChecks} {sources : BlockSources preset fork}
    {signed : SignedBeaconBlock preset fork} (reached : StatesReached config anchorState states)
    (free : states[root]? = none) (parentFound : states[parentRoot]? = some pre)
    (transition : stateTransition config checks sources.engine pre signed true = .ok state) :
    StatesReached config anchorState (states.insert root state) := by
  -- Each state kept before stays at its root.
  have keep : ∀ {r : Root} {s : BeaconState preset fork}, states[r]? = some s →
      (states.insert root state)[r]? = some s := by
    intro r s found
    rw [getElem?_insert_root]
    split
    · rename_i same
      rw [← same, free] at found
      cases found
    · exact found
  intro r s found
  rw [getElem?_insert_root] at found
  split at found
  · cases found
    exact Or.inr ⟨parentRoot, pre, checks, sources, signed, keep parentFound, transition⟩
  · rcases reached found with same | ⟨p, q, c, src, sg, qFound, ok⟩
    · exact Or.inl same
    · exact Or.inr ⟨p, q, c, src, sg, keep qFound, ok⟩

end Store

variable {config : Config} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}

/-- Where the checkpoints of a reachable store come from.

Each justified checkpoint of the store is the anchor checkpoint, or that of a kept state.

Or it is that of a kept state after the justification and finalization of an epoch.

Here the checkpoint of a state is its current justified checkpoint.

Each finalized checkpoint comes from the same places, as a finalized checkpoint of such a state.

Every kept state is the anchor state, or the state after a valid block applied to a kept state.

So the store holds no checkpoint that the states do not give it.

Ancestry needs more: the store raises its justified and finalized checkpoints separately.

So they can come from states on two branches. -/
theorem Store.Reachable.checkpointsFrom
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      store.CheckpointsFrom store.blockStates ⟨getCurrentEpoch anchorState, anchorRoot⟩ ∧
      store.StatesKnown ∧ Store.StatesReached config anchorState store.blockStates := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, rootOk, -, -, justified, finalized, unrealizedJustified,
      unrealizedFinalized⟩ := getForkchoiceStore_anchor made
    obtain ⟨root, rootOk', blocks, states⟩ := getForkchoiceStore_maps made
    rw [rootOk, Except.ok.injEq] at rootOk'
    subst rootOk'
    refine ⟨anchorRoot, rootOk, ⟨Or.inl justified, Or.inl finalized, Or.inl unrealizedJustified,
      Or.inl unrealizedFinalized⟩, fun found => ?_, fun found => ?_⟩
    · rw [states, getElem?_insert_root] at found
      split at found
      · rename_i same
        rw [blocks, ← same]
        simp
      · simp at found
    · rw [states, getElem?_insert_root] at found
      split at found
      · cases found
        exact Or.inl rfl
      · simp at found
  | tick _ ticked ih =>
    obtain ⟨anchorRoot, rootOk, holds, known, reached⟩ := ih
    obtain ⟨-, -, blocks, states⟩ := Store.onTick_frame ticked
    refine ⟨anchorRoot, rootOk, ?_, ?_, ?_⟩
    · rw [states]
      exact Store.onTick_checkpointsFrom holds ticked
    · intro r s found
      rw [states] at found
      rw [blocks]
      exact known found
    · rw [states]
      exact reached
  | @block old new _ _ _ _ added ih =>
    obtain ⟨anchorRoot, rootOk, holds, known, reached⟩ := ih
    refine ⟨anchorRoot, rootOk, Store.onBlock_checkpointsFrom holds known added, ?_⟩
    obtain same | ⟨blockRoot, -, unknown, blocks, pre, state, parentFound, transition, states⟩ :=
      Store.onBlock_same_or_insert added
    · subst same
      exact ⟨known, reached⟩
    have free : old.blockStates[blockRoot]? = none := by
      cases kept : old.blockStates[blockRoot]? with
      | none => rfl
      | some s =>
        have := known kept
        rw [Std.TreeMap.contains_eq_isSome_getElem?, unknown] at this
        cases this
    refine ⟨fun found => ?_, states ▸ reached.insert free parentFound transition⟩
    rw [states, getElem?_insert_root] at found
    rw [blocks, Std.TreeMap.contains_insert]
    split at found
    · rename_i same
      simp [same]
    · simp [known found]
  | attestation _ attested ih =>
    obtain ⟨anchorRoot, rootOk, holds, known, reached⟩ := ih
    obtain ⟨-, blocks, states⟩ := Store.onAttestation_frame attested
    refine ⟨anchorRoot, rootOk,
      states ▸ holds.of_same (Store.onAttestation_sameCheckpoints attested),
      fun found => ?_, states ▸ reached⟩
    rw [states] at found
    rw [blocks]
    exact known found
  | attesterSlashing _ slashed ih =>
    obtain ⟨anchorRoot, rootOk, holds, known, reached⟩ := ih
    obtain ⟨-, blocks, states⟩ := Store.onAttesterSlashing_frame slashed
    refine ⟨anchorRoot, rootOk,
      states ▸ holds.of_same (Store.onAttesterSlashing_sameCheckpoints slashed),
      fun found => ?_, states ▸ reached⟩
    rw [states] at found
    rw [blocks]
    exact known found
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
    obtain ⟨anchorRoot, rootOk, holds, known, reached⟩ := ih
    exact ⟨anchorRoot, rootOk, holds.of_same ⟨rfl, rfl, rfl, rfl⟩, known, reached⟩
  | envelope _ accepted ih =>
    obtain ⟨anchorRoot, rootOk, holds, known, reached⟩ := ih
    obtain ⟨_, _, _, _, _, record, rfl⟩ := onExecutionPayloadEnvelope_ok accepted
    obtain ⟨_, rfl⟩ := recordEnvelope_frame record
    exact ⟨anchorRoot, rootOk, holds.of_same ⟨rfl, rfl, rfl, rfl⟩, known, reached⟩
  | inclusionList _ accepted ih =>
    obtain ⟨_, _, rfl⟩ := onInclusionList_ok _ accepted
    obtain ⟨anchorRoot, rootOk, holds, known, reached⟩ := ih
    exact ⟨anchorRoot, rootOk, holds.of_same ⟨rfl, rfl, rfl, rfl⟩, known, reached⟩


/-- A reachable store keeps its checkpoints ordered and its states in the invariant.

The anchor state must keep the invariant. -/
theorem Store.Reachable.ordered (anchor : Invariant anchorState)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.EpochsOrdered ∧ store.StatesHold := by
  induction reachable with
  | anchor made =>
    obtain ⟨anchorRoot, -, -, -, justified, finalized, unrealizedJustified,
      unrealizedFinalized⟩ := getForkchoiceStore_anchor made
    obtain ⟨root, -, -, states⟩ := getForkchoiceStore_maps made
    refine ⟨?_, ?_⟩
    · unfold Store.EpochsOrdered
      rw [justified, finalized, unrealizedJustified, unrealizedFinalized]
      exact ⟨UInt64.le_refl _, UInt64.le_refl _⟩
    · intro blockRoot state found
      rw [states, Std.TreeMap.getElem?_insert] at found
      split at found
      · cases found
        exact anchor
      · simp at found
  | tick _ ticked ih =>
    exact ⟨Store.onTick_ordered ih.1 ticked,
      Store.StatesHold.of_eq ih.2 (Store.onTick_frame ticked).2.2.2⟩
  | block _ added ih =>
    exact ⟨Store.onBlock_ordered ih.1 ih.2 added, Store.onBlock_statesHold ih.2 added⟩
  | attestation _ attested ih =>
    exact ⟨Store.onAttestation_ordered ih.1 attested,
      Store.StatesHold.of_eq ih.2 (Store.onAttestation_frame attested).2.2⟩
  | attesterSlashing _ slashed ih =>
    exact ⟨Store.onAttesterSlashing_ordered ih.1 slashed,
      Store.StatesHold.of_eq ih.2 (Store.onAttesterSlashing_frame slashed).2.2⟩
  | payloadAttestation _ voted ih =>
    exact ⟨Store.onPayloadAttestationMessage_ordered ih.1 voted,
      Store.StatesHold.of_eq ih.2 (onPayloadAttestationMessage_onlyPtcVotes voted).frame.2.2⟩
  | envelope _ accepted ih =>
    exact ⟨Store.onExecutionPayloadEnvelope_ordered ih.1 accepted,
      Store.StatesHold.of_eq ih.2 (Store.onExecutionPayloadEnvelope_frame accepted).2.2⟩
  | inclusionList _ accepted ih =>
    exact ⟨Store.onInclusionList_ordered ih.1 accepted,
      Store.StatesHold.of_eq ih.2 (Store.onInclusionList_frame accepted).2.2⟩

/-- The finalized epoch of a reachable store is at most its justified epoch.

The anchor state must keep the invariant of the state transition. -/
theorem Store.Reachable.finalized_le_justified (anchor : Invariant anchorState)
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    store.finalizedCheckpoint.epoch ≤ store.justifiedCheckpoint.epoch :=
  (reachable.ordered anchor).1.1

/-- In a reachable store, the justified block descends from the finalized block.

Otherwise the two checkpoints come from states that disagree.

Descent means that the finalized root is the checkpoint block of the justified root.

That checkpoint block is at the finalized epoch, and the genesis epoch counts as descent.

Otherwise the two checkpoints conflict.

Each is the anchor checkpoint or comes from a kept state, as `Store.Reachable.checkpointsFrom` says.

By accountable safety, they conflict only when some stake signed slashable votes. -/
theorem Store.Reachable.justified_descends_or_conflicting
    (reachable : Store.Reachable config anchorState anchorBlock store) :
    (store.finalizedCheckpoint.epoch = GENESIS_EPOCH ∨
      store.getCheckpointBlock store.justifiedCheckpoint.root store.finalizedCheckpoint.epoch =
        .ok store.finalizedCheckpoint.root) ∨
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      Store.CheckpointFrom store.blockStates ⟨getCurrentEpoch anchorState, anchorRoot⟩
        (·.currentJustifiedCheckpoint) store.justifiedCheckpoint ∧
      Store.CheckpointFrom store.blockStates ⟨getCurrentEpoch anchorState, anchorRoot⟩
        (·.finalizedCheckpoint) store.finalizedCheckpoint ∧
      store.finalizedCheckpoint.epoch ≠ GENESIS_EPOCH ∧
      store.getCheckpointBlock store.justifiedCheckpoint.root store.finalizedCheckpoint.epoch ≠
        .ok store.finalizedCheckpoint.root := by
  by_cases descends : store.finalizedCheckpoint.epoch = GENESIS_EPOCH ∨
      store.getCheckpointBlock store.justifiedCheckpoint.root store.finalizedCheckpoint.epoch =
        .ok store.finalizedCheckpoint.root
  · exact .inl descends
  obtain ⟨anchorRoot, rootOk, holds, -⟩ := reachable.checkpointsFrom
  rw [not_or] at descends
  exact .inr ⟨anchorRoot, rootOk, holds.justified, holds.finalized, descends.1, descends.2⟩

end EthLib.Consensus
