module

public import EthLib.Consensus.Proofs.Transition.Provenance.Links

/-!
# Proofs: the finalized checkpoint of a chain is finalized in the sense of FFG

Casper FFG finalizes a checkpoint `c` with `k` justified checkpoints in a row from it.

The last of them is the target of a supermajority link whose source is `c`.

This is `k`-finalization, Definition 4.9 of the Gasper paper.

[Gasper]: https://arxiv.org/abs/2003.03052

A weighing call finalizes by one of four rules.

Each rule reads justification bits and an old justified checkpoint `c`.

This file turns each rule into `k`-finalization, with `k` 1 or 2.

- The checkpoints from `c` on are justified, one per epoch.
- Each root descends from the one before, along blocks past the earlier one's epoch start.
  Or a state of the chain has the zero root.
- A weighing call of the chain justified the last one, with `c` as its source.

The newest bit can come from the call before the finalizing one.

So the link that finalizes may belong to that earlier call.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## Genesis -/

/-- A deposit at genesis keeps the history. -/
theorem kept_genesisDeposit {beforeHeze : fork < .hegota} {leaves : Array DepositData}
    {entry : Deposit × Nat}
    (computed : genesisDeposit config checks beforeHeze leaves state entry = .ok after) :
    Kept state after := by
  simp only [genesisDeposit, bind_ok_iff] at computed
  obtain ⟨depositRoot, _, deposited⟩ := computed
  exact (show Kept state
    { state with eth1Data := fun _ => { state.eth1Data beforeHeze with depositRoot } } from rfl).trans
    (kept_processDeposit deposited)

/-- A genesis state has no justification bit set. -/
theorem genesis_bits {forked : ForkedBeaconState preset} (genesis : Genesis config checks forked)
    (index : Nat) (inside : index < JUSTIFICATION_BITS_LENGTH.toNat) :
    forked.state.justificationBits.bits[index] = false := by
  obtain ⟨⟨_, _, _, computed⟩, _⟩ := genesis
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, same⟩ :=
    computed
  have kept := (Kept.foldlM (fun _ _ _ ok => kept_genesisDeposit ok) depositedOk).trans
    (Kept.foldlM (fun _ _ _ ok => by
      simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, set⟩ := ok
      exact kept_setValidator set) activatedOk)
  rw [← same]
  change activated.justificationBits.bits[index] = false
  rw [kept.justificationBits]
  simp [emptyGenesisState]

/-! ## Calls along a chain -/

theorem WeighingCall.extendChain {start after last : ForkedBeaconState preset} {fork : Fork}
    {state cached weighed next : BeaconState preset fork} {voters : List ValidatorIndex}
    {checkpoint : Checkpoint}
    (call : WeighingCall config checks start after fork state cached weighed next voters checkpoint)
    (chain : Reaches config checks after last) :
    WeighingCall config checks start last fork state cached weighed next voters checkpoint :=
  have ⟨head, notDue, nextOk, tail, rest⟩ := call
  ⟨head, notDue, nextOk, tail.trans chain, rest⟩

theorem JustifiedBy.extendChain {start after last : ForkedBeaconState preset}
    {checkpoint : Checkpoint} (justified : JustifiedBy config checks start after checkpoint)
    (chain : Reaches config checks after last) :
    JustifiedBy config checks start last checkpoint :=
  have ⟨_, _, _, _, _, _, call⟩ := justified
  (call.extendChain chain).justifiedBy

/-- Where the newest justification bit of a chain's end comes from.

The start had some bit set.

Or the last weighing call justified the checkpoint of its current epoch.

That call closed the epoch before the end's, and its source for the epoch is the end's previous
justified checkpoint. -/
theorem Reaches.newestBit {start after : ForkedBeaconState preset}
    (chain : Reaches config checks start after)
    (set : after.state.justificationBits.bits[0] = true) :
    (∃ (other : Nat) (inside : other < JUSTIFICATION_BITS_LENGTH.toNat),
        start.state.justificationBits.bits[other] = true) ∨
      ∃ (fork : Fork) (state cached weighed next : BeaconState preset fork)
        (voters : List ValidatorIndex) (root : Root),
        WeighingCall config checks start after fork state cached weighed next voters
          ⟨getCurrentEpoch cached, root⟩ ∧
        (getCurrentEpoch cached).toNat + 1 = (getCurrentEpoch after.state).toNat ∧
        after.state.previousJustifiedCheckpoint = cached.currentJustifiedCheckpoint := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact .inl ⟨0, by decide, set⟩
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
        obtain ⟨weighed, weighedOk, bitsSame, previousSame, -, -⟩ := closing
        simp only at set ⊢
        rw [bitsSame] at set
        have nextEpoch := epoch_of_closes stepSlot closes
        rcases processJustificationAndFinalization_weighs weighedOk with ⟨early, rfl⟩ |
          ⟨later, _, _, _, _, _, _, _, _, _, _, weighs⟩
        · -- The first two epochs keep the bits, and no call ran before them.
          rw [cachedSame.1] at set
          rcases more set with atStart | ⟨_, _, cached', _, _, _, _, call, epochs, _⟩
          · exact .inl atStart
          · exfalso
            have callLater := UInt64.lt_iff_toNat_lt.mp call.later
            have earlyNat := UInt64.le_iff_toNat_le.mp early
            rw [cachedSame.2] at earlyNat
            change _ ≤ 0 + 1 at earlyNat
            change 0 + 1 < _ at callLater
            simp only at epochs
            omega
        · rcases processJustificationAndFinalization_bits weighedOk with ⟨early, -⟩ |
            ⟨-, bit0, -⟩
          · exact absurd later (UInt64.not_lt.mpr early)
          obtain ⟨voters, root, counted, passes, rootOk⟩ := bit0 set
          refine .inr ⟨fork, state, cached, weighed, next, voters, root,
            ⟨middleChain, notDue, computed, .refl _, closes, cachedOk, weighedOk, later, .inr rfl,
              counted, passes, rootOk⟩, ?_, ?_⟩
          · rw [nextEpoch, cachedSame.2]
          · rw [previousSame, (weighJustificationAndFinalization_checkpoints weighs).1]
      · next notClosing =>
        obtain ⟨bitsSame, previousSame, -, -⟩ := closing
        simp only at set ⊢
        rw [bitsSame] at set
        have sameEpoch := epoch_of_open stepSlot notClosing
        rcases more set with atStart | ⟨fork', state', cached', weighed', next', voters', root',
          call, epochs, previous⟩
        · exact .inl atStart
        · refine .inr ⟨fork', state', cached', weighed', next', voters', root', call.extend theStep,
            ?_, ?_⟩
          · rw [sameEpoch]
            exact epochs
          · rw [previousSame]
            exact previous
    | @upgrade _ post due computed =>
      have theStep : Step config checks middle post.val := .upgrade due computed
      have same := upgradeNext_history computed
      simp only [BeaconState.history, Prod.mk.injEq] at same
      have epochSame : getCurrentEpoch post.val.state = getCurrentEpoch middle.state := by
        simp only [getCurrentEpoch, same.1]
      rw [same.2.2.2.2.1] at set
      rcases more set with atStart | ⟨fork', state', cached', weighed', next', voters', root',
        call, epochs, previous⟩
      · exact .inl atStart
      · refine .inr ⟨fork', state', cached', weighed', next', voters', root', call.extend theStep,
          ?_, ?_⟩
        · rw [epochSame]
          exact epochs
        · rw [same.2.2.2.2.2.1]
          exact previous
    | @block fork engine signed validateResult state post notDue computed =>
      have theStep : Step config checks ⟨fork, state⟩ ⟨fork, post⟩ :=
        .block engine signed validateResult notDue computed
      have frame := frame_processBlock (applySignedBlock_ok computed).2.1
      have epochSame : getCurrentEpoch post = getCurrentEpoch state := by
        simp only [getCurrentEpoch, frame.slot]
      simp only at set ⊢
      rw [applySignedBlock_bits computed] at set
      rcases more set with atStart | ⟨fork', state', cached', weighed', next', voters', root',
        call, epochs, previous⟩
      · exact .inl atStart
      · refine .inr ⟨fork', state', cached', weighed', next', voters', root', call.extend theStep,
          ?_, ?_⟩
        · simp only at epochs ⊢
          rw [epochSame]
          exact epochs
        · simp only at previous ⊢
          rw [frame.previousJustified]
          exact previous

/-! ## `k`-finalization -/

/-- A checkpoint `c` is `k`-finalized along a chain, for `k` 1 or 2, as in [Gasper] Definition 4.9.

- `cs 0 = c`, and `cs i` is in the `i`-th epoch after `c`'s, up to `k`.
- The first `k` are justified, by the start or by a weighing call of the chain.
- Each root descends from the one before, along blocks past the first slot of the earlier
  checkpoint's epoch, or a state of the chain has the zero root.
- The roots after `c` are not zero, or a header of the chain has the zero root.
- A weighing call of the chain justified `cs k`, with `c` as its source. -/
def KFinalizedBy (config : Config) (checks : SignatureChecks) (start after : ForkedBeaconState preset)
    (c : Checkpoint) : Prop :=
  ∃ k, 1 ≤ k ∧ k ≤ 2 ∧ ∃ cs : ℕ → Checkpoint, cs 0 = c ∧
    (∀ i ≤ k, (cs i).epoch.toNat = c.epoch.toNat + i) ∧
    (∀ i < k, JustifiedOrStart config checks start after (cs i)) ∧
    (∀ i < k, PastAncestor config checks start after
        ((cs i).epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) (cs i).root (cs (i + 1)).root ∨
      ZeroRootFound config checks start after) ∧
    (∀ i ≤ k, 1 ≤ i → (cs i).root ≠ Vector.replicate 32 0 ∨
      ZeroHeaderFound config checks start after) ∧
    ∃ (fork : Fork) (state cached weighed next : BeaconState preset fork)
      (voters : List ValidatorIndex),
      WeighingCall config checks start after fork state cached weighed next voters (cs k) ∧
      recordSource cached (cs k).epoch = c

/-- Two checkpoints that calls justified, read at a common end: ancestry at a later end. -/
theorem JustifiedBy.pastAncestor_at {start middle after : ForkedBeaconState preset}
    {first second : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start) (tail : Reaches config checks middle after)
    (firstJustified : JustifiedBy config checks start middle first)
    (secondJustified : JustifiedBy config checks start middle second)
    (ordered : first.epoch.toNat ≤ second.epoch.toNat)
    (recentEnd : middle.state.slot.toNat ≤
      first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    PastAncestor config checks start after (first.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat)
        first.root second.root ∨
      ZeroRootFound config checks start after :=
  (firstJustified.pastAncestor wide genesis secondJustified ordered recentEnd).imp
    (·.extendChain tail) (·.extendChain tail)

/-- A checkpoint that a call justified has a nonzero root at a later end, or there is evidence. -/
theorem JustifiedBy.nonzero_at {start middle after : ForkedBeaconState preset}
    {checkpoint : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start) (tail : Reaches config checks middle after)
    (justified : JustifiedBy config checks start middle checkpoint) :
    checkpoint.root ≠ Vector.replicate 32 0 ∨ ZeroHeaderFound config checks start after :=
  (justified.extendChain tail).target_nonzero wide (by
    rw [(genesis_state genesis).1]
    exact Nat.zero_le _)

/-- `1`-finalization from a justified `c` and a link from it to the next epoch. -/
theorem kFinalizedBy_one {start middle after : ForkedBeaconState preset} {c : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start) (tail : Reaches config checks middle after)
    (cJustified : JustifiedBy config checks start middle c)
    {fork : Fork} {state cached weighed next : BeaconState preset fork}
    {voters : List ValidatorIndex} {d : Checkpoint}
    (link : WeighingCall config checks start middle fork state cached weighed next voters d)
    (source : recordSource cached d.epoch = c) (epoch : d.epoch.toNat = c.epoch.toNat + 1)
    (recentEnd : middle.state.slot.toNat ≤
      c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    KFinalizedBy config checks start after c := by
  refine ⟨1, Nat.le_refl _, by decide, fun i => if i = 0 then c else d, rfl, ?_, ?_, ?_, ?_,
    fork, state, cached, weighed, next, voters, link.extendChain tail, source⟩
  · intro i below
    rcases i with _ | _ | i
    · simp
    · simp [epoch]
    · omega
  · intro i below
    rcases i with _ | i
    · exact .inr (.inr (.inr (cJustified.extendChain tail)))
    · omega
  · intro i below
    rcases i with _ | i
    · exact JustifiedBy.pastAncestor_at wide genesis tail cJustified link.justifiedBy
        (by simp [epoch]) recentEnd
    · omega
  · intro i below one
    rcases i with _ | _ | i
    · omega
    · exact JustifiedBy.nonzero_at wide genesis tail link.justifiedBy
    · omega

/-- `2`-finalization from a justified `c`, a justified checkpoint of the next epoch, and a link
from `c` to the epoch after it. -/
theorem kFinalizedBy_two {start middle after : ForkedBeaconState preset} {c d : Checkpoint}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start) (tail : Reaches config checks middle after)
    (cJustified : JustifiedBy config checks start middle c)
    (dJustified : JustifiedBy config checks start middle d)
    (dEpoch : d.epoch.toNat = c.epoch.toNat + 1)
    {fork : Fork} {state cached weighed next : BeaconState preset fork}
    {voters : List ValidatorIndex} {e : Checkpoint}
    (link : WeighingCall config checks start middle fork state cached weighed next voters e)
    (source : recordSource cached e.epoch = c) (eEpoch : e.epoch.toNat = c.epoch.toNat + 2)
    (recentEnd : middle.state.slot.toNat ≤
      c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat + preset.SLOTS_PER_HISTORICAL_ROOT.toNat) :
    KFinalizedBy config checks start after c := by
  refine ⟨2, by decide, Nat.le_refl _, fun i => if i = 0 then c else if i = 1 then d else e, rfl,
    ?_, ?_, ?_, ?_, fork, state, cached, weighed, next, voters, link.extendChain tail, source⟩
  · intro i below
    rcases i with _ | _ | _ | i
    · simp
    · simp [dEpoch]
    · simp [eEpoch]
    · omega
  · intro i below
    rcases i with _ | _ | i
    · exact .inr (.inr (.inr (cJustified.extendChain tail)))
    · exact .inr (.inr (.inr (dJustified.extendChain tail)))
    · omega
  · intro i below
    rcases i with _ | _ | i
    · exact JustifiedBy.pastAncestor_at wide genesis tail cJustified dJustified
        (by simp [dEpoch]) recentEnd
    · refine JustifiedBy.pastAncestor_at wide genesis tail dJustified link.justifiedBy
        (by simp [dEpoch, eEpoch])
        ?_
      show _ ≤ d.epoch.toNat * _ + _
      rw [dEpoch, Nat.add_mul, Nat.one_mul]
      omega
    · omega
  · intro i below one
    rcases i with _ | _ | _ | i
    · omega
    · exact JustifiedBy.nonzero_at wide genesis tail dJustified
    · exact JustifiedBy.nonzero_at wide genesis tail link.justifiedBy
    · omega


/-! ## The four rules -/

/-- From genesis, the finalized checkpoint of a chain is `k`-finalized along it, or genesis.

The last weighing call that changed it finalized it by one of its four rules.

- Old current justified, two epochs back, bits 0 to 2: `k = 2`, linked to the current epoch.
- Old current justified, one epoch back, bits 0 and 1: `k = 1`, linked to the current epoch.
- Old previous justified, three epochs back, bits 1 to 3: `k = 2`, linked to the previous epoch.
- Old previous justified, two epochs back, bits 1 and 2: `k = 1`, linked to the previous epoch.

The link to the previous epoch is this call's, or the call before, which justified that epoch
while it was current.

The buffer of roots must span four epochs, so that the roots of the checkpoints are still in it
at the call: `4 * SLOTS_PER_EPOCH ≤ N`. -/
theorem Reaches.finalized_rule {start after : ForkedBeaconState preset}
    (wide : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start) (chain : Reaches config checks start after) :
    after.state.finalizedCheckpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
      KFinalizedBy config checks start after after.state.finalizedCheckpoint := by
  have wide2 : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    omega
  obtain ⟨-, startPrevious, startCurrent, startFinalized⟩ := genesis_state genesis
  have noStartBit : ¬∃ (other : Nat) (inside : other < JUSTIFICATION_BITS_LENGTH.toNat),
      start.state.justificationBits.bits[other] = true := by
    rintro ⟨other, inside, set⟩
    rw [genesis_bits genesis other inside] at set
    cases set
  rcases chain.finalized with same | ⟨fork, state, cached, weighed, next, head, notDue, nextOk,
    tail, closes, cachedOk, weighedOk, later, bitsSame, rule⟩
  · exact .inl (same.trans startFinalized)
  generalize after.state.finalizedCheckpoint = c at rule ⊢
  have theStep : Step config checks ⟨fork, state⟩ ⟨fork, next⟩ := .slot notDue nextOk
  have toNext : Reaches config checks start ⟨fork, next⟩ := head.step theStep
  have stepSlot := advanceSlot_slot nextOk
  have nextEpoch := epoch_of_closes stepSlot closes
  have cachedSame : cached.currentJustifiedCheckpoint = state.currentJustifiedCheckpoint ∧
      cached.previousJustifiedCheckpoint = state.previousJustifiedCheckpoint ∧
      cached.justificationBits = state.justificationBits ∧
      getCurrentEpoch cached = getCurrentEpoch state := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl, rfl, rfl⟩
  have laterNat := UInt64.lt_iff_toNat_lt.mp later
  change 0 + 1 < _ at laterNat
  rw [← cachedSame.2.2.2] at nextEpoch
  -- The slot after the call is the first of the next epoch.
  have slotEq : next.slot.toNat =
      ((getCurrentEpoch cached).toNat + 1) * preset.SLOTS_PER_EPOCH.toNat := by
    have fits : state.slot.toNat + 1 < 2 ^ 64 := stepSlot ▸ UInt64.toNat_lt next.slot
    have divides := (closesEpoch_iff fits).mp closes
    have epochIs := getCurrentEpoch_toNat next
    rw [stepSlot] at epochIs ⊢
    rw [← nextEpoch, epochIs, Nat.div_mul_cancel divides]
  -- The roots of checkpoints up to three epochs back are still in the buffer.
  have recent : ∀ (checkpoint : Checkpoint) (back : Nat), back ≤ 3 →
      checkpoint.epoch.toNat + back = (getCurrentEpoch cached).toNat →
      (⟨fork, next⟩ : ForkedBeaconState preset).state.slot.toNat ≤
        checkpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat +
          preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    intro checkpoint back few epochs
    show next.slot.toNat ≤ _
    rw [slotEq, ← epochs, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    have := Nat.mul_le_mul_right preset.SLOTS_PER_EPOCH.toNat few
    omega
  -- An old justified checkpoint is genesis, or a call of the chain justified it.
  have old : ∀ checkpoint, JustifiedOrStart config checks start ⟨fork, state⟩ checkpoint →
      checkpoint = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨
        JustifiedBy config checks start ⟨fork, next⟩ checkpoint := by
    intro checkpoint justified
    rcases justified with same | same | same | justified
    · exact .inl (same.trans startFinalized)
    · exact .inl (same.trans startPrevious)
    · exact .inl (same.trans startCurrent)
    · exact .inr (justified.extend theStep)
  obtain ⟨-, previousOld, currentOld⟩ := head.checkpoints
  rw [← cachedSame.1] at currentOld
  rw [← cachedSame.2.1] at previousOld
  -- What the new bits stand for.
  rcases processJustificationAndFinalization_bits weighedOk with ⟨early, -⟩ |
    ⟨-, bit0, bit1, -, -⟩
  · exact absurd later (UInt64.not_lt.mpr early)
  rw [← bitsSame] at bit0 bit1
  have link0 : next.justificationBits.bits[0] = true →
      ∃ (voters : List ValidatorIndex) (root : Root),
        WeighingCall config checks start ⟨fork, next⟩ fork state cached weighed next voters
          ⟨getCurrentEpoch cached, root⟩ := by
    intro set
    obtain ⟨voters, root, counted, passes, rootOk⟩ := bit0 set
    exact ⟨voters, root, head, notDue, nextOk, .refl _, closes, cachedOk, weighedOk, later,
      .inr rfl, counted, passes, rootOk⟩
  have link1 : next.justificationBits.bits[1] = true →
      ∃ (fork' : Fork) (state' cached' weighed' next' : BeaconState preset fork')
        (voters : List ValidatorIndex) (d : Checkpoint),
        WeighingCall config checks start ⟨fork, next⟩ fork' state' cached' weighed' next' voters d ∧
        d.epoch.toNat + 1 = (getCurrentEpoch cached).toNat ∧
        recordSource cached' d.epoch = cached.previousJustifiedCheckpoint := by
    intro set
    rcases bit1 set with ⟨voters, root, counted, passes, rootOk⟩ | older
    · -- This call justified the previous epoch, from its old previous justified checkpoint.
      have previousNat := getPreviousEpoch_toNat cached
      have notCurrent : getPreviousEpoch cached ≠ getCurrentEpoch cached := fun same => by
        rw [same] at previousNat
        omega
      refine ⟨fork, state, cached, weighed, next, voters, ⟨getPreviousEpoch cached, root⟩,
        ⟨head, notDue, nextOk, .refl _, closes, cachedOk, weighedOk, later, .inl rfl, counted,
          passes, rootOk⟩, by simp only; omega, ?_⟩
      unfold recordSource
      exact ite_eq_right_of_eq_false _ _ (eq_false notCurrent)
    · -- The call before justified it as its current epoch, from this call's old previous one.
      rw [cachedSame.2.2.1] at older
      rcases head.newestBit older with atStart | ⟨fork', state', cached', weighed', next', voters,
        root, call, epochs, previous⟩
      · exact absurd atStart noStartBit
      refine ⟨fork', state', cached', weighed', next', voters, ⟨getCurrentEpoch cached', root⟩,
        call.extend theStep, by simp only; rw [cachedSame.2.2.2]; exact epochs, ?_⟩
      unfold recordSource
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), cachedSame.2.1]
      exact previous.symm
  have justifiedBit : ∀ (index : Nat) (inside : index < JUSTIFICATION_BITS_LENGTH.toNat),
      next.justificationBits.bits[index] = true →
      ∃ d : Checkpoint, d.epoch.toNat + index = (getCurrentEpoch cached).toNat ∧
        JustifiedBy config checks start ⟨fork, next⟩ d := by
    intro index inside set
    rcases toNext.justificationBit index inside set with atStart | ⟨d, epoch, justified⟩
    · exact absurd atStart noStartBit
    refine ⟨d, ?_, justified⟩
    have previousNat := getPreviousEpoch_toNat next
    simp only at epoch
    omega
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at rule
  rcases rule with ⟨rfl, ⟨⟨⟨b0, b1⟩, b2⟩, back⟩ | ⟨⟨b0, b1⟩, back⟩⟩ |
    ⟨rfl, ⟨⟨⟨b1, b2⟩, b3⟩, back⟩ | ⟨⟨b1, b2⟩, back⟩⟩
  · -- Old current justified, two epochs back.
    rcases old _ currentOld with genesisCheckpoint | cJustified
    · exact .inl genesisCheckpoint
    right
    obtain ⟨d, dEpoch, dJustified⟩ := justifiedBit 1 (by decide) b1
    obtain ⟨voters, root, link⟩ := link0 b0
    refine kFinalizedBy_two wide2 genesis tail cJustified dJustified (by omega) link ?_
      (by simp only; omega) (recent _ 2 (by decide) back)
    unfold recordSource
    exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
  · -- Old current justified, one epoch back.
    rcases old _ currentOld with genesisCheckpoint | cJustified
    · exact .inl genesisCheckpoint
    right
    obtain ⟨voters, root, link⟩ := link0 b0
    refine kFinalizedBy_one wide2 genesis tail cJustified link ?_ (by simp only; omega)
      (recent _ 1 (by decide) back)
    unfold recordSource
    exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
  · -- Old previous justified, three epochs back.
    rcases old _ previousOld with genesisCheckpoint | cJustified
    · exact .inl genesisCheckpoint
    right
    obtain ⟨d, dEpoch, dJustified⟩ := justifiedBit 2 (by decide) b2
    obtain ⟨fork', state', cached', weighed', next', voters, e, link, eEpoch, source⟩ := link1 b1
    exact kFinalizedBy_two wide2 genesis tail cJustified dJustified (by omega) link source
      (by omega) (recent _ 3 (by decide) back)
  · -- Old previous justified, two epochs back.
    rcases old _ previousOld with genesisCheckpoint | cJustified
    · exact .inl genesisCheckpoint
    right
    obtain ⟨fork', state', cached', weighed', next', voters, e, link, eEpoch, source⟩ := link1 b1
    exact kFinalizedBy_one wide2 genesis tail cJustified link source (by omega)
      (recent _ 2 (by decide) back)


end EthLib.Consensus
