module

public import EthLib.Consensus.Proofs.ForkChoice.Checkpoints
public import EthLib.Consensus.Proofs.Transition.Reachable

/-!
# Proofs: the states of a store come from runs of the chain

Take a store that the handlers build with one choice of signature checks.

It keeps only states that runs of the chain reach from the anchor state.

A run is a sequence of slots, due upgrades and blocks, with those signature checks.

The store holds the states of one fork, so a run of its states has no upgrade.

That needs no upgrade to be due at any state of the fork.

It holds at the last fork.

It also holds when the next fork is not scheduled and an epoch has two slots or more.

So each checkpoint of the store is the anchor checkpoint, or a checkpoint of a reached state.

A reached state is one that a run reaches from the anchor state.

Or the checkpoint is that of a reached state after the justification and finalization of an epoch.

The justified block then descends from the finalized block, or the two checkpoints conflict.

In the second case each comes from such a run, which is what accountable safety takes.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz

variable {preset : Preset} {fork : Fork} {config : Config} {checks : SignatureChecks}

/-! ## Runs within one fork -/

/-- No upgrade is due at the last fork. -/
theorem upgradeDue_of_nextFork_none (none : config.nextFork fork = none)
    (state : BeaconState preset fork) : upgradeDue config ⟨fork, state⟩ = false := by
  simp [upgradeDue, none]

/-- No upgrade is due when the next fork is not scheduled, and an epoch has two slots or more.

An unscheduled fork has the epoch `FAR_FUTURE_EPOCH`, which no slot reaches then. -/
theorem upgradeDue_of_farFuture {next : Fork}
    (unscheduled : config.nextFork fork = some (next, FAR_FUTURE_EPOCH))
    (slots : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (state : BeaconState preset fork) :
    upgradeDue config ⟨fork, state⟩ = false := by
  simp only [upgradeDue, unscheduled, Option.any_some, Bool.and_eq_false_iff]
  refine .inr (beq_eq_false_iff_ne.mpr fun same => ?_)
  have value := congrArg UInt64.toNat same
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  rw [computeEpochAtSlot, UInt64.toNat_div, far] at value
  have bound := state.slot.toNat_lt
  have : state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ state.slot.toNat / 2 :=
    Nat.div_le_div_left slots (by decide)
  omega

variable {fork : Fork}

/-- Slots within one fork with no upgrade due are a run. -/
theorem Reaches.advanceSlots
    (notDue : ∀ state : BeaconState preset fork, upgradeDue config ⟨fork, state⟩ = false) :
    ∀ {count : Nat} {state after : BeaconState preset fork},
      advanceSlots config checks count state = .ok after →
      Reaches config checks ⟨fork, state⟩ ⟨fork, after⟩
  | 0, state, after, computed => by
    simp only [EthLib.Consensus.advanceSlots, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | count + 1, state, after, computed => by
    simp only [EthLib.Consensus.advanceSlots, bind_ok_iff] at computed
    obtain ⟨next, nextOk, rest⟩ := computed
    exact ((Reaches.refl _).step (.slot (notDue state) nextOk)).trans
      (Reaches.advanceSlots notDue rest)

/-- A valid block within one fork with no upgrade due is a run. -/
theorem Reaches.stateTransition
    (notDue : ∀ state : BeaconState preset fork, upgradeDue config ⟨fork, state⟩ = false)
    {engine : ExecutionEngine preset fork} {state after : BeaconState preset fork}
    {signed : SignedBeaconBlock preset fork} {validateResult : Bool}
    (computed : stateTransition config checks engine state signed validateResult = .ok after) :
    Reaches config checks ⟨fork, state⟩ ⟨fork, after⟩ := by
  simp only [EthLib.Consensus.stateTransition, bind_ok_iff] at computed
  obtain ⟨advanced, slotsOk, applied⟩ := computed
  simp only [processSlots, bind_ok_iff, ensure_ok_iff] at slotsOk
  obtain ⟨_, _, advancedOk⟩ := slotsOk
  exact (Reaches.advanceSlots notDue advancedOk).step
    (.block engine signed validateResult (notDue advanced) applied)

namespace Store

variable {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}

/-- A store that the handlers build from an anchor, each with the same signature checks. -/
inductive ReachableWith (config : Config) (checks : SignatureChecks)
    (anchorState : BeaconState preset fork) (anchorBlock : BeaconBlock preset fork) :
    Store preset fork → Prop where
  /-- The store built from the anchor. -/
  | anchor {store : Store preset fork} :
    getForkchoiceStore config anchorState anchorBlock = .ok store →
      ReachableWith config checks anchorState anchorBlock store
  /-- The store after a tick. -/
  | tick {store after : Store preset fork} {timeMs : UInt64} :
    ReachableWith config checks anchorState anchorBlock store →
      store.onTick config timeMs = .ok after →
      ReachableWith config checks anchorState anchorBlock after
  /-- The store after a signed block. -/
  | block {store after : Store preset fork} {sources : BlockSources preset fork}
      {signed : SignedBeaconBlock preset fork} :
    ReachableWith config checks anchorState anchorBlock store →
      store.onBlock config checks sources signed = .ok after →
      ReachableWith config checks anchorState anchorBlock after
  /-- The store after an attestation, from the wire or from a block. -/
  | attestation {store after : Store preset fork} {attestation : Attestation preset fork}
      {isFromBlock : Bool} :
    ReachableWith config checks anchorState anchorBlock store →
      store.onAttestation config checks attestation isFromBlock = .ok after →
      ReachableWith config checks anchorState anchorBlock after
  /-- The store after an attester slashing. -/
  | attesterSlashing {store after : Store preset fork} {slashing : AttesterSlashing preset fork} :
    ReachableWith config checks anchorState anchorBlock store →
      store.onAttesterSlashing config checks slashing = .ok after →
      ReachableWith config checks anchorState anchorBlock after
  /-- From Gloas, the store after a vote of a member of the payload committee. -/
  | payloadAttestation {store after : Store preset fork} {gloas : .glamsterdam ≤ fork}
      {message : PayloadAttestationMessage} {isFromBlock : Bool} :
    ReachableWith config checks anchorState anchorBlock store →
      store.onPayloadAttestationMessage config checks gloas message isFromBlock = .ok after →
      ReachableWith config checks anchorState anchorBlock after
  /-- From Gloas, the store after a signed envelope. -/
  | envelope {store after : Store preset fork} {sources : BlockSources preset fork}
      {gloas : .glamsterdam ≤ fork} {signed : SignedExecutionPayloadEnvelope preset fork} :
    ReachableWith config checks anchorState anchorBlock store →
      store.onExecutionPayloadEnvelope config checks sources gloas signed = .ok after →
      ReachableWith config checks anchorState anchorBlock after
  /-- From Heze, the store after an inclusion list. -/
  | inclusionList {store after : Store preset fork} {heze : .hegota ≤ fork}
      {signed : SignedInclusionList} :
    ReachableWith config checks anchorState anchorBlock store →
      store.onInclusionList config checks heze signed = .ok after →
      ReachableWith config checks anchorState anchorBlock after

variable {store : Store preset fork}

/-- A store built with one choice of signature checks is reachable. -/
theorem ReachableWith.reachable
    (reachable : ReachableWith config checks anchorState anchorBlock store) :
    Reachable config anchorState anchorBlock store := by
  induction reachable with
  | anchor made => exact .anchor made
  | tick _ step ih => exact .tick ih step
  | block _ step ih => exact .block ih step
  | attestation _ step ih => exact .attestation ih step
  | attesterSlashing _ step ih => exact .attesterSlashing ih step
  | payloadAttestation _ step ih => exact .payloadAttestation ih step
  | envelope _ step ih => exact .envelope ih step
  | inclusionList _ step ih => exact .inclusionList ih step

/-- Every state that a map keeps is the anchor state, or the state after a valid block.

That block runs with the given signature checks, on a kept state. -/
def StatesReachedWith (config : Config) (checks : SignatureChecks)
    (anchorState : BeaconState preset fork)
    (states : Std.TreeMap Root (BeaconState preset fork)) : Prop :=
  ∀ {root : Root} {state : BeaconState preset fork}, states[root]? = some state →
    state = anchorState ∨ ∃ (parentRoot : Root) (pre : BeaconState preset fork)
      (sources : BlockSources preset fork) (signed : SignedBeaconBlock preset fork),
      states[parentRoot]? = some pre ∧
        stateTransition config checks sources.engine pre signed true = .ok state

/-- Every state that a store built with one choice of checks keeps is reached with those checks. -/
theorem ReachableWith.statesReached
    (reachable : ReachableWith config checks anchorState anchorBlock store) :
    StatesReachedWith config checks anchorState store.blockStates := by
  induction reachable with
  | anchor made =>
    obtain ⟨root, -, -, states⟩ := getForkchoiceStore_maps made
    intro r s found
    rw [states, getElem?_insert_root] at found
    split at found
    · cases found
      exact .inl rfl
    · simp at found
  | tick _ ticked ih =>
    rw [(onTick_frame ticked).2.2.2]
    exact ih
  | attestation _ attested ih =>
    rw [(onAttestation_frame attested).2.2]
    exact ih
  | attesterSlashing _ slashed ih =>
    rw [(onAttesterSlashing_frame slashed).2.2]
    exact ih
  | payloadAttestation _ voted ih =>
    obtain ⟨_, _, rfl⟩ := onPayloadAttestationMessage_onlyPtcVotes voted
    exact ih
  | envelope _ accepted ih =>
    rw [(onExecutionPayloadEnvelope_frame accepted).2.2]
    exact ih
  | inclusionList _ accepted ih =>
    rw [(onInclusionList_frame accepted).2.2]
    exact ih
  | @block old new sources signed earlier added ih =>
    obtain same | ⟨blockRoot, -, unknown, -, pre, state, parentFound, transition, states⟩ :=
      onBlock_same_or_insert added
    · subst same
      exact ih
    obtain ⟨-, -, -, known, -⟩ := earlier.reachable.checkpointsFrom
    have free : old.blockStates[blockRoot]? = none := by
      cases kept : old.blockStates[blockRoot]? with
      | none => rfl
      | some s =>
        have := known kept
        rw [Std.TreeMap.contains_eq_isSome_getElem?, unknown] at this
        cases this
    have keep : ∀ {r : Root} {s : BeaconState preset fork}, old.blockStates[r]? = some s →
        (old.blockStates.insert blockRoot state)[r]? = some s := by
      intro r s found
      rw [getElem?_insert_root]
      split
      · rename_i same
        rw [← same, free] at found
        cases found
      · exact found
    intro r s found
    rw [states, getElem?_insert_root] at found
    rw [states]
    split at found
    · cases found
      exact .inr ⟨_, pre, sources, signed, keep parentFound, transition⟩
    · rcases ih found with same | ⟨p, q, src, sg, qFound, ok⟩
      · exact .inl same
      · exact .inr ⟨p, q, src, sg, keep qFound, ok⟩

/-- Every state that the map keeps is reached from the anchor state by a run.

No upgrade may be due at any state of the fork. -/
theorem StatesReachedWith.reaches {states : Std.TreeMap Root (BeaconState preset fork)}
    (reached : StatesReachedWith config checks anchorState states)
    (notDue : ∀ state : BeaconState preset fork, upgradeDue config ⟨fork, state⟩ = false) :
    ∀ {root : Root} {state : BeaconState preset fork}, states[root]? = some state →
      Reaches config checks ⟨fork, anchorState⟩ ⟨fork, state⟩ := by
  -- The state before each block sits at an earlier slot, so induction on the slot ends.
  suffices ∀ n, ∀ {root : Root} {state : BeaconState preset fork}, state.slot.toNat = n →
      states[root]? = some state → Reaches config checks ⟨fork, anchorState⟩ ⟨fork, state⟩ from
    fun {_ _} found => this _ rfl found
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro root state slot found
    rcases reached found with rfl | ⟨parentRoot, pre, sources, signed, preFound, transition⟩
    · exact .refl _
    have earlier := stateTransition_slot transition
    have lower : pre.slot.toNat < n := by
      rw [← slot, earlier.2]
      exact UInt64.lt_iff_toNat_lt.mp earlier.1
    exact (ih _ lower rfl preFound).trans (Reaches.stateTransition notDue transition)

/-- A checkpoint that comes from runs from the anchor state, as a field of a state.

It is the anchor checkpoint, or the field of a state that a run reaches from the anchor state.

Or it is the field of such a state after the justification and finalization of an epoch. -/
def CheckpointFromRuns (config : Config) (checks : SignatureChecks)
    (anchorState : BeaconState preset fork) (anchor : Checkpoint)
    (field : BeaconState preset fork → Checkpoint) (checkpoint : Checkpoint) : Prop :=
  checkpoint = anchor ∨
    (∃ state : BeaconState preset fork,
      Reaches config checks ⟨fork, anchorState⟩ ⟨fork, state⟩ ∧ checkpoint = field state) ∨
    ∃ state pulled : BeaconState preset fork,
      Reaches config checks ⟨fork, anchorState⟩ ⟨fork, state⟩ ∧
        processJustificationAndFinalization state = .ok pulled ∧ checkpoint = field pulled

/-- A checkpoint from kept states comes from runs, when each kept state is reached by one. -/
theorem CheckpointFrom.runs {states : Std.TreeMap Root (BeaconState preset fork)}
    {anchor checkpoint : Checkpoint} {field : BeaconState preset fork → Checkpoint}
    (reaches : ∀ {root : Root} {state : BeaconState preset fork}, states[root]? = some state →
      Reaches config checks ⟨fork, anchorState⟩ ⟨fork, state⟩)
    (holds : CheckpointFrom states anchor field checkpoint) :
    CheckpointFromRuns config checks anchorState anchor field checkpoint := by
  rcases holds with same | ⟨_, state, found, same⟩ | ⟨_, state, pulled, found, ok, same⟩
  · exact Or.inl same
  · exact Or.inr (Or.inl ⟨state, reaches found, same⟩)
  · exact Or.inr (Or.inr ⟨state, pulled, reaches found, ok, same⟩)

end Store

variable {anchorState : BeaconState preset fork} {anchorBlock : BeaconBlock preset fork}
  {store : Store preset fork}

/-- Each checkpoint of a store built with one choice of signature checks comes from runs.

Each is the anchor checkpoint, or a checkpoint of a reached state.

A reached state is one that a run with those checks reaches from the anchor state.

Or the checkpoint is that of a reached state after the justification and finalization of an epoch.

Each state that the store keeps is reached by such a run.

No upgrade may be due at any state of the fork. -/
theorem Store.ReachableWith.checkpointsFromRuns
    (reachable : Store.ReachableWith config checks anchorState anchorBlock store)
    (notDue : ∀ state : BeaconState preset fork, upgradeDue config ⟨fork, state⟩ = false) :
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      (∀ {root : Root} {state : BeaconState preset fork}, store.blockStates[root]? = some state →
        Reaches config checks ⟨fork, anchorState⟩ ⟨fork, state⟩) ∧
      Store.CheckpointFromRuns config checks anchorState ⟨getCurrentEpoch anchorState, anchorRoot⟩
        (·.currentJustifiedCheckpoint) store.justifiedCheckpoint ∧
      Store.CheckpointFromRuns config checks anchorState ⟨getCurrentEpoch anchorState, anchorRoot⟩
        (·.finalizedCheckpoint) store.finalizedCheckpoint ∧
      Store.CheckpointFromRuns config checks anchorState ⟨getCurrentEpoch anchorState, anchorRoot⟩
        (·.currentJustifiedCheckpoint) store.unrealizedJustifiedCheckpoint ∧
      Store.CheckpointFromRuns config checks anchorState ⟨getCurrentEpoch anchorState, anchorRoot⟩
        (·.finalizedCheckpoint) store.unrealizedFinalizedCheckpoint := by
  obtain ⟨anchorRoot, rootOk, holds, -⟩ := reachable.reachable.checkpointsFrom
  have reaches : ∀ {root : Root} {state : BeaconState preset fork},
      store.blockStates[root]? = some state →
        Reaches config checks ⟨fork, anchorState⟩ ⟨fork, state⟩ :=
    StatesReachedWith.reaches reachable.statesReached notDue
  exact ⟨anchorRoot, rootOk, reaches, holds.justified.runs reaches, holds.finalized.runs reaches,
    holds.unrealizedJustified.runs reaches, holds.unrealizedFinalized.runs reaches⟩

/-- Take a store built with one choice of signature checks.

Its justified block descends from its finalized block, or the two checkpoints come from runs.

Descent means that the finalized root is the checkpoint block of the justified root.

That checkpoint block is at the finalized epoch, and the genesis epoch counts as descent.

In the second case each is the anchor checkpoint, or that of a reached state.

A reached state is one that a run with those checks reaches from the anchor state.

Or the checkpoint is that of a reached state after the justification and finalization of an epoch.

No upgrade may be due at any state of the fork. -/
theorem Store.ReachableWith.justified_descends_or_conflicting_runs
    (reachable : Store.ReachableWith config checks anchorState anchorBlock store)
    (notDue : ∀ state : BeaconState preset fork, upgradeDue config ⟨fork, state⟩ = false) :
    (store.finalizedCheckpoint.epoch = GENESIS_EPOCH ∨
      store.getCheckpointBlock store.justifiedCheckpoint.root store.finalizedCheckpoint.epoch =
        .ok store.finalizedCheckpoint.root) ∨
    ∃ anchorRoot, SszType.hashTreeRoot anchorBlock = .ok anchorRoot ∧
      Store.CheckpointFromRuns config checks anchorState ⟨getCurrentEpoch anchorState, anchorRoot⟩
        (·.currentJustifiedCheckpoint) store.justifiedCheckpoint ∧
      Store.CheckpointFromRuns config checks anchorState ⟨getCurrentEpoch anchorState, anchorRoot⟩
        (·.finalizedCheckpoint) store.finalizedCheckpoint ∧
      store.finalizedCheckpoint.epoch ≠ GENESIS_EPOCH ∧
      store.getCheckpointBlock store.justifiedCheckpoint.root store.finalizedCheckpoint.epoch ≠
        .ok store.finalizedCheckpoint.root := by
  by_cases descends : store.finalizedCheckpoint.epoch = GENESIS_EPOCH ∨
      store.getCheckpointBlock store.justifiedCheckpoint.root store.finalizedCheckpoint.epoch =
        .ok store.finalizedCheckpoint.root
  · exact .inl descends
  obtain ⟨anchorRoot, rootOk, -, justified, finalized, -⟩ :=
    reachable.checkpointsFromRuns notDue
  rw [not_or] at descends
  exact .inr ⟨anchorRoot, rootOk, justified, finalized, descends.1, descends.2⟩

end EthLib.Consensus
