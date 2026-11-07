module

public import EthLib.Consensus.Proofs.Transition.Provenance.Anchors
public import EthLib.Consensus.Proofs.Transition.Provenance.Finality
public import EthLib.Consensus.Proofs.Transition.Provenance.UpgradeVoters

/-!
# Proofs: a direct call of the weighing on a state of a chain

A store of fork choice may call the weighing directly on a state, at any slot.

It does so to see which checkpoints the votes so far would justify and finalize.

Such a call reads the state as it is, with no caching of a slot before it.

`CallRecord` covers it, as it covers a call at an epoch boundary.

So the facts of a call hold for it.

- The source is justified, and earlier than the target.
- The source block is an ancestor of the target block.
- The target root is a block's root.
- The counted voters signed.

This file adds what the call writes.

Its current justified checkpoint is the state's, or the call justified it.

Its finalized checkpoint is the state's, or `k`-finalized by one of the four rules.

The links of those rules are calls of the chain, or this call.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Checkpoints that any call justified -/

/-- Some call of the weighing on a state of a chain justified a checkpoint.

It may be a call at an epoch boundary, or a direct call. -/
def JustifiedByCall (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) (checkpoint : Checkpoint) : Prop :=
  ∃ (fork : Fork) (state cached weighed : BeaconState preset fork)
    (voters : List ValidatorIndex),
    CallRecord config checks start after fork state cached weighed voters checkpoint

theorem JustifiedBy.call {start after : ForkedBeaconState preset} {checkpoint : Checkpoint}
    (justified : JustifiedBy config checks start after checkpoint) :
    JustifiedByCall config checks start after checkpoint :=
  have ⟨fork, state, cached, weighed, _, voters, call⟩ := justified
  ⟨fork, state, cached, weighed, voters, call.record⟩

theorem JustifiedByCall.extendChain {start after last : ForkedBeaconState preset}
    {checkpoint : Checkpoint} (justified : JustifiedByCall config checks start after checkpoint)
    (chain : Reaches config checks after last) :
    JustifiedByCall config checks start last checkpoint :=
  have ⟨fork, state, cached, weighed, voters, call⟩ := justified
  ⟨fork, state, cached, weighed, voters, call.extendChain chain⟩

/-- A checkpoint that a call justified is read again at the end of the chain.

That holds while its root is still in the buffer. -/
theorem JustifiedByCall.read_at_end {start after : ForkedBeaconState preset}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (justified : JustifiedByCall config checks start after checkpoint)
    (recentEnd : after.state.slot.toNat ≤
      checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    ∃ slot : Slot, slot.toNat = checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ∧
      slot.toNat < after.state.slot.toNat ∧
      readCircular after.state.blockRoots.elements slot = .ok checkpoint.root := by
  obtain ⟨fork, state, cached, _, _, _, toAfter, readsFrom, _, later, recent, _, _, rootOk⟩ :=
    justified
  obtain ⟨slot, slotEq, below, _, read⟩ := readsFrom.read wide later recent rootOk
  have stateLe := toAfter.slot_le
  simp only at stateLe
  have stable := (toAfter.roots_stable (slot := slot) below (by rw [slotEq]; exact recentEnd)).1
  rw [read] at stable
  exact ⟨slot, slotEq, by omega, stable⟩

/-- Two checkpoints that calls of one chain justified: the earlier block is an ancestor.

It is one along blocks past the first slot of its epoch, or a state has the zero root.

As `JustifiedBy.pastAncestor`, for any calls. -/
theorem JustifiedByCall.pastAncestor {start after : ForkedBeaconState preset}
    {first second : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start)
    (firstJustified : JustifiedByCall config checks start after first)
    (secondJustified : JustifiedByCall config checks start after second)
    (ordered : first.epoch.toNat ≤ second.epoch.toNat)
    (recentEnd : after.state.slot.toNat ≤
      first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat +
        preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    PastAncestor config checks start after (first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat)
        first.root second.root ∨
      ZeroRootFound config checks start after := by
  obtain ⟨slot, slotEq, below, read⟩ := firstJustified.read_at_end wide recentEnd
  have slotOrder : first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
      second.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := Nat.mul_le_mul_right _ ordered
  obtain ⟨slot', slotEq', below', read'⟩ := secondJustified.read_at_end wide (by omega)
  have chain : Reaches config checks start after := by
    obtain ⟨_, _, _, _, _, head, toAfter, _⟩ := firstJustified
    exact head.trans toAfter
  have startSlot := (genesis_state genesis).1
  rcases Nat.lt_or_ge slot.toNat slot'.toNat with before | same
  · rcases chain.blockRoots_pastAncestor (by rw [startSlot]; exact Nat.zero_le _) before below'
      (by omega) read read' with ⟨_, _, _, ⟨_, _, _, _, _, head, _⟩, ancestor | zero⟩
    · rw [slotEq] at ancestor
      exact .inl (ancestor.prefix head)
    · exact .inr (zero.prefix head)
  · have sameSlot : slot = slot' := UInt64.toNat_inj.mp (by omega)
    subst sameSlot
    rw [read] at read'
    rw [Except.ok.inj read']
    exact .inl .refl

/-- The root of a checkpoint that a call justified is the root of a block of the chain.

That block is at or before the first slot of the checkpoint's epoch.

Or the root is the start's header's, or a state of the chain has the zero root.

As `JustifiedBy.root_block`, for any call. -/
theorem CallRecord.root_block {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint)
    (fromStart : start.state.slot.toNat ≤
      checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) :
    (∃ (parentRoot : Root) (slot : Slot),
        ChainBlockAt config checks start after parentRoot checkpoint.root slot ∧
        slot.toNat ≤ checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) ∨
      StartHeaderRoot start checkpoint.root ∨ ZeroRootFound config checks start after := by
  obtain ⟨slot, slotEq, below, near, read⟩ :=
    call.reads.read wide call.later call.recent call.rootOk
  obtain ⟨fork', state', cached', ⟨atSlot, cachedOk', next', nextOk', notDue', head', tail'⟩,
    ⟨root, rootOk', written⟩, -⟩ :=
    call.head.roots_written (by rw [slotEq]; exact fromStart) below near
  rw [read] at written
  cases written
  have toAfter : Reaches config checks ⟨fork', state'⟩ after :=
    ((Reaches.refl _).step (.slot notDue' nextOk')).trans (tail'.trans call.toAfter)
  rcases head'.cachedHeader_block cachedOk' toAfter rootOk' with
    ⟨parentRoot, blockSlot, block, slotLe⟩ | genesisRoot | zero
  · refine .inl ⟨parentRoot, blockSlot, block, ?_⟩
    rw [← slotEq, ← atSlot]
    exact slotLe
  · exact .inr (.inl genesisRoot)
  · exact .inr (.inr zero)

/-! ## What a direct call writes -/

/-- A direct call on a state of a chain keeps the current justified checkpoint.

Or it justified the new one itself. -/
theorem processJustificationAndFinalization_current {start : ForkedBeaconState preset}
    {fork : Fork} {state weighed : BeaconState preset fork}
    (head : Reaches config checks start ⟨fork, state⟩)
    (weighedOk : processJustificationAndFinalization state = .ok weighed) :
    weighed.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∨
      ∃ voters : List ValidatorIndex,
        CallRecord config checks start ⟨fork, state⟩ fork state state weighed voters
          weighed.currentJustifiedCheckpoint := by
  rcases processJustificationAndFinalization_weighs weighedOk with ⟨_, rfl⟩ |
    ⟨later, _, _, _, _, _, _, _, _, _, _, _⟩
  · exact .inl rfl
  rcases processJustificationAndFinalization_justified weighedOk with same |
    ⟨epoch, voters, root, recent, counted, passes, rootOk, justified⟩
  · exact .inl same
  · rw [justified]
    exact .inr ⟨voters, head, .refl _, .inr rfl, weighedOk, later, recent, counted, passes,
      rootOk⟩

/-- A checkpoint `c` is `k`-finalized along a chain, for `k` 1 or 2, with any calls as witnesses.

As `KFinalizedBy`, with the checkpoints justified by the start or by any call.

The link is a call of any kind. -/
def KFinalizedByCall (config : Config) (checks : SignatureChecks)
    (start after : ForkedBeaconState preset) (c : Checkpoint) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ 2 ∧ ∃ cs : ℕ → Checkpoint, cs 0 = c ∧
    (∀ i ≤ k, (cs i).epoch.toNat = c.epoch.toNat + i) ∧
    (∀ i < k, JustifiedOrStart config checks start after (cs i) ∨
      JustifiedByCall config checks start after (cs i)) ∧
    (∀ i < k, PastAncestor config checks start after
        ((cs i).epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) (cs i).root (cs (i + 1)).root ∨
      ZeroRootFound config checks start after) ∧
    (∀ i ≤ k, 1 ≤ i → (cs i).root ≠ Vector.replicate 32 0 ∨
      ZeroHeaderFound config checks start after) ∧
    ∃ (fork : Fork) (state cached weighed : BeaconState preset fork)
      (voters : List ValidatorIndex),
      CallRecord config checks start after fork state cached weighed voters (cs k) ∧
      recordSource cached (cs k).epoch = c

theorem CallRecord.justifiedByCall {start after : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (call : CallRecord config checks start after fork state cached weighed voters checkpoint) :
    JustifiedByCall config checks start after checkpoint :=
  ⟨fork, state, cached, weighed, voters, call⟩

/-- `1`-finalization from a justified `c` and a link of any call from it to the next epoch. -/
theorem kFinalizedByCall_one {start after : ForkedBeaconState preset} {c : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start)
    (cJustified : JustifiedByCall config checks start after c)
    {fork : Fork} {state cached weighed : BeaconState preset fork}
    {voters : List ValidatorIndex} {d : Checkpoint}
    (link : CallRecord config checks start after fork state cached weighed voters d)
    (source : recordSource cached d.epoch = c) (epoch : d.epoch.toNat = c.epoch.toNat + 1)
    (recentEnd : after.state.slot.toNat ≤
      c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    KFinalizedByCall config checks start after c := by
  have fromStart : start.state.slot.toNat ≤ d.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
    rw [(genesis_state genesis).1]
    exact Nat.zero_le _
  refine ⟨1, Nat.le_refl _, by decide, fun i => if i = 0 then c else d, rfl, ?_, ?_, ?_, ?_,
    fork, state, cached, weighed, voters, link, source⟩
  · intro i below
    rcases i with _ | _ | i
    · simp
    · simp [epoch]
    · omega
  · intro i below
    rcases i with _ | i
    · exact .inr cJustified
    · omega
  · intro i below
    rcases i with _ | i
    · exact JustifiedByCall.pastAncestor wide genesis cJustified link.justifiedByCall
        (by simp [epoch]) recentEnd
    · omega
  · intro i below one
    rcases i with _ | _ | i
    · omega
    · exact link.target_nonzero wide fromStart
    · omega

/-- `2`-finalization from a justified `c` and a justified checkpoint of the next epoch.

A link of any call goes from `c` to the epoch after that. -/
theorem kFinalizedByCall_two {start after : ForkedBeaconState preset} {c d : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start)
    (cJustified : JustifiedByCall config checks start after c)
    (dJustified : JustifiedByCall config checks start after d)
    (dEpoch : d.epoch.toNat = c.epoch.toNat + 1)
    {fork : Fork} {state cached weighed : BeaconState preset fork}
    {voters : List ValidatorIndex} {e : Checkpoint}
    (link : CallRecord config checks start after fork state cached weighed voters e)
    (source : recordSource cached e.epoch = c) (eEpoch : e.epoch.toNat = c.epoch.toNat + 2)
    (recentEnd : after.state.slot.toNat ≤
      c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    KFinalizedByCall config checks start after c := by
  have fromStart : ∀ epoch : Epoch,
      start.state.slot.toNat ≤ epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := fun _ => by
    rw [(genesis_state genesis).1]
    exact Nat.zero_le _
  have dNonzero : d.root ≠ Vector.replicate 32 0 ∨ ZeroHeaderFound config checks start after := by
    obtain ⟨_, _, _, _, _, call⟩ := dJustified
    exact call.target_nonzero wide (fromStart _)
  refine ⟨2, by decide, Nat.le_refl _, fun i => if i = 0 then c else if i = 1 then d else e, rfl,
    ?_, ?_, ?_, ?_, fork, state, cached, weighed, voters, link, source⟩
  · intro i below
    rcases i with _ | _ | _ | i
    · simp
    · simp [dEpoch]
    · simp [eEpoch]
    · omega
  · intro i below
    rcases i with _ | _ | i
    · exact .inr cJustified
    · exact .inr dJustified
    · omega
  · intro i below
    rcases i with _ | _ | i
    · exact JustifiedByCall.pastAncestor wide genesis cJustified dJustified (by simp [dEpoch])
        recentEnd
    · refine JustifiedByCall.pastAncestor wide genesis dJustified link.justifiedByCall
        (by simp [dEpoch, eEpoch]) ?_
      show _ ≤ d.epoch.toNat * _ + _
      rw [dEpoch, Nat.add_mul, Nat.one_mul]
      omega
    · omega
  · intro i below one
    rcases i with _ | _ | _ | i
    · omega
    · exact dNonzero
    · exact link.target_nonzero wide (fromStart _)
    · omega

/-- From genesis, the finalized checkpoint that a direct call writes is `k`-finalized.

Or it is the state's, or genesis.

The rules are those of a call at an epoch boundary, with the state itself as what the call reads.

The link to the current epoch is this call's.

The link to the previous epoch is this call's, or the last call of the chain's.

That last call justified the epoch while it was current.

The buffer of roots must span four epochs: `4 * SLOTS_PER_EPOCH ≤ N`. -/
theorem processJustificationAndFinalization_finalized_rule {start : ForkedBeaconState preset}
    {fork : Fork} {state weighed : BeaconState preset fork}
    (wide : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start) (head : Reaches config checks start ⟨fork, state⟩)
    (weighedOk : processJustificationAndFinalization state = .ok weighed) :
    weighed.finalizedCheckpoint = state.finalizedCheckpoint ∨
      weighed.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      KFinalizedByCall config checks start ⟨fork, state⟩ weighed.finalizedCheckpoint := by
  have wide2 : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    omega
  obtain ⟨-, startPrevious, startCurrent, startFinalized⟩ := genesis_state genesis
  have noStartBit : ¬∃ (other : Nat) (inside : other < JUSTIFICATION_BITS_LENGTH.toNat),
      start.state.justificationBits.bits[other] = true := by
    rintro ⟨other, inside, set⟩
    rw [genesis_bits genesis other inside] at set
    cases set
  rcases processJustificationAndFinalization_weighs weighedOk with ⟨_, rfl⟩ |
    ⟨later, _, _, _, _, _, _, _, _, _, _, weighs⟩
  · exact .inl rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, finalizedRule, -⟩ :=
    weighJustificationAndFinalization_eq weighs
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  change 0 + 1 < _ at laterNat
  have previousNat := getPreviousEpoch_toNat state
  -- The state is in its current epoch, so before the first slot of the next one.
  have slotBound : state.slot.toNat <
      ((getCurrentEpoch state).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    have epochNat := getCurrentEpoch_toNat state
    have spe : 0 < preset.SLOTS_PER_EPOCH.toNat := by
      rcases Nat.eq_zero_or_pos preset.SLOTS_PER_EPOCH.toNat with zero | positive
      · rw [zero, Nat.div_zero] at epochNat
        omega
      · exact positive
    rw [epochNat, Nat.mul_comm]
    exact Nat.lt_mul_div_succ _ spe
  have recent : ∀ (checkpoint : Checkpoint) (back : Nat), back ≤ 3 →
      checkpoint.epoch.toNat + back = (getCurrentEpoch state).toNat →
      (⟨fork, state⟩ : ForkedBeaconState preset).state.slot.toNat ≤
        checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat +
          preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    intro checkpoint back few epochs
    show state.slot.toNat ≤ _
    rw [← epochs, Nat.add_mul, Nat.add_mul, Nat.one_mul] at slotBound
    have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat few
    omega
  -- An old justified checkpoint is genesis, or a call of the chain justified it.
  have old : ∀ checkpoint, JustifiedOrStart config checks start ⟨fork, state⟩ checkpoint →
      checkpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        JustifiedByCall config checks start ⟨fork, state⟩ checkpoint := by
    intro checkpoint justified
    rcases justified with same | same | same | justified
    · exact .inl (same.trans startFinalized)
    · exact .inl (same.trans startPrevious)
    · exact .inl (same.trans startCurrent)
    · exact .inr justified.call
  obtain ⟨-, previousOld, currentOld⟩ := head.checkpoints
  -- What the new bits stand for.
  rcases processJustificationAndFinalization_bits weighedOk with ⟨early, -⟩ |
    ⟨-, bit0, bit1, bit2, bit3⟩
  · exact absurd later (UInt64.not_lt.mpr early)
  have link0 : weighed.justificationBits.bits[0] = true →
      ∃ (voters : List ValidatorIndex) (root : Root),
        CallRecord config checks start ⟨fork, state⟩ fork state state weighed voters
          ⟨getCurrentEpoch state, root⟩ := by
    intro set
    obtain ⟨voters, root, counted, passes, rootOk⟩ := bit0 set
    exact ⟨voters, root, head, .refl _, .inr rfl, weighedOk, later, .inr rfl, counted, passes,
      rootOk⟩
  have link1 : weighed.justificationBits.bits[1] = true →
      ∃ (fork' : Fork) (state' cached' weighed' : BeaconState preset fork')
        (voters : List ValidatorIndex) (d : Checkpoint),
        CallRecord config checks start ⟨fork, state⟩ fork' state' cached' weighed' voters d ∧
        d.epoch.toNat + 1 = (getCurrentEpoch state).toNat ∧
        recordSource cached' d.epoch = state.previousJustifiedCheckpoint := by
    intro set
    rcases bit1 set with ⟨voters, root, counted, passes, rootOk⟩ | older
    · -- This call justified the previous epoch, from the state's previous justified checkpoint.
      have notCurrent : getPreviousEpoch state ≠ getCurrentEpoch state := fun same => by
        rw [same] at previousNat
        omega
      refine ⟨fork, state, state, weighed, voters, ⟨getPreviousEpoch state, root⟩,
        ⟨head, .refl _, .inr rfl, weighedOk, later, .inl rfl, counted, passes, rootOk⟩,
        by simp only; omega, ?_⟩
      unfold recordSource
      exact ite_eq_right_of_eq_false _ _ (eq_false notCurrent)
    · -- The last call of the chain justified it as its current epoch.
      rcases head.newestBit older with atStart | ⟨fork', state', cached', weighed', next', voters,
        root, call, epochs, previous⟩
      · exact absurd atStart noStartBit
      refine ⟨fork', state', cached', weighed', voters, ⟨getCurrentEpoch cached', root⟩,
        call.record, epochs, ?_⟩
      unfold recordSource
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      exact previous.symm
  have justifiedBit : ∀ (index : Nat) (inside : index < JUSTIFICATION_BITS_LENGTH.toNat),
      state.justificationBits.bits[index] = true →
      ∃ d : Checkpoint, d.epoch.toNat + (index + 1) = (getCurrentEpoch state).toNat ∧
        JustifiedByCall config checks start ⟨fork, state⟩ d := by
    intro index inside set
    rcases head.justificationBit index inside set with atStart | ⟨d, epoch, justified⟩
    · exact absurd atStart noStartBit
    refine ⟨d, ?_, justified.call⟩
    simp only at epoch
    omega
  split at finalizedRule
  · next byCurrent =>
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at byCurrent
    rw [finalizedRule]
    rcases old _ currentOld with genesisCheckpoint | cJustified
    · exact .inr (.inl genesisCheckpoint)
    right; right
    rcases byCurrent with ⟨⟨⟨b0, b1⟩, b2⟩, back⟩ | ⟨⟨b0, b1⟩, back⟩
    · -- Old current justified, two epochs back.
      obtain ⟨fork', state', cached', weighed', votersD, d, dCall, dEpoch, -⟩ := link1 b1
      obtain ⟨voters, root, link⟩ := link0 b0
      refine kFinalizedByCall_two wide2 genesis cJustified dCall.justifiedByCall (by omega) link
        ?_ (by simp only; omega) (recent _ 2 (by decide) back)
      unfold recordSource
      exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
    · -- Old current justified, one epoch back.
      obtain ⟨voters, root, link⟩ := link0 b0
      refine kFinalizedByCall_one wide2 genesis cJustified link ?_ (by simp only; omega)
        (recent _ 1 (by decide) back)
      unfold recordSource
      exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
  · split at finalizedRule
    · next byPrevious =>
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at byPrevious
      rw [finalizedRule]
      rcases old _ previousOld with genesisCheckpoint | cJustified
      · exact .inr (.inl genesisCheckpoint)
      right; right
      rcases byPrevious with ⟨⟨⟨b1, b2⟩, b3⟩, back⟩ | ⟨⟨b1, b2⟩, back⟩
      · -- Old previous justified, three epochs back.
        rw [bit2] at b2
        obtain ⟨d, dEpoch, dJustified⟩ := justifiedBit 1 (by decide) b2
        obtain ⟨fork', state', cached', weighed', voters, e, link, eEpoch, source⟩ := link1 b1
        exact kFinalizedByCall_two wide2 genesis cJustified dJustified (by omega) link source
          (by omega) (recent _ 3 (by decide) back)
      · -- Old previous justified, two epochs back.
        obtain ⟨fork', state', cached', weighed', voters, e, link, eEpoch, source⟩ := link1 b1
        exact kFinalizedByCall_one wide2 genesis cJustified link source (by omega)
          (recent _ 2 (by decide) back)
    · exact .inl finalizedRule


end EthLib.Consensus
