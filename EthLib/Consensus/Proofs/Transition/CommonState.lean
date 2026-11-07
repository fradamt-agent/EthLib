module

public import EthLib.Consensus.Proofs.Transition.Reachable
public import EthLib.Consensus.Proofs.Transition.Upgrade

/-!
# Proofs: two histories after a state they share

Accountable safety measures slashable stake against the weighing of one reference state.

That state must be one that both conflicting histories pass through.

Facts about each history alone cannot bound the drift from any other reference.
`Models/Ffg/BranchDrift.lean` shows this.

Here two runs share a prefix that ends at a state `X`, and each continues with its own suffix.

The slot never decreases along a run.

So every state of either run with a slot after the slot of `X` lies in that run's suffix.

It is then reached from `X`.

The drift bounds of each history can then start from `X`, through `Run` and `Reaches`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- An upgrade keeps the slot. -/
theorem upgradeNext_slot {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.slot = pre.state.slot := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToAltair, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, folded, _, -, rfl⟩ := upgraded
    rw [← Array.foldlM_toList] at folded
    obtain ⟨participation, rfl, -⟩ := foldlM_translateAttestation folded
    rfl
  · subst computed
    rfl
  · subst computed
    rfl
  · subst computed
    rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, _, queued, compounded⟩ := upgraded
    exact ((Frame.foldlM (fun _ _ _ ok => frame_queuePreActivation ok) queued).trans
      (Frame.foldlM (fun _ _ _ ok => frame_queueCompoundingExcess ok) compounded)).slot
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    unfold upgradeToGloas at upgraded
    obtain ⟨_, -, rest⟩ := bind_ok_iff.mp upgraded
    obtain ⟨_, -, onboarded⟩ := bind_ok_iff.mp rest
    obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    rfl

/-- One step never moves the slot back. -/
theorem Step.slot_le {before after : ForkedBeaconState preset}
    (step : Step config checks before after) :
    before.state.slot.toNat ≤ after.state.slot.toNat := by
  cases step with
  | slot _ computed => have := advanceSlot_slot computed; dsimp; omega
  | upgrade _ computed => rw [upgradeNext_slot computed]; exact Nat.le_refl _
  | block _ _ _ _ computed =>
    exact (frame_processBlock (applySignedBlock_ok computed).2.1).slot.symm ▸ Nat.le_refl _

namespace Run

variable {start : ForkedBeaconState preset}

/-- Every state that a run passes through has a slot at most that of its end. -/
theorem slot_le_of_mem :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      ∀ state ∈ run.states, state.state.slot.toNat ≤ after.state.slot.toNat
  | _, .nil, state, member => by rw [List.mem_singleton.mp member]; exact Nat.le_refl _
  | _, .snoc run last, state, member => by
    rcases List.mem_append.mp member with earlier | now
    · exact Nat.le_trans (slot_le_of_mem run state earlier) last.slot_le
    · rw [List.mem_singleton.mp now]
      exact Nat.le_refl _

/-- A run reaches every state that it passes through. -/
theorem reaches_of_mem :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      ∀ state ∈ run.states, Reaches config checks start state
  | _, .nil, state, member => by
    rw [List.mem_singleton.mp member]
    exact .refl _
  | _, .snoc run last, state, member => by
    rcases List.mem_append.mp member with earlier | now
    · exact reaches_of_mem run state earlier
    · rw [List.mem_singleton.mp now]
      exact Reaches.step ⟨run⟩ last

theorem states_ne_nil {after : ForkedBeaconState preset} (run : Run config checks start after) :
    run.states ≠ [] :=
  List.ne_nil_of_mem (start_mem_states run)

/-- A state of two runs in sequence is a state of the first or of the second. -/
theorem mem_states_append {middle : ForkedBeaconState preset}
    (head : Run config checks start middle) :
    ∀ {after : ForkedBeaconState preset} (tail : Run config checks middle after)
      {state : ForkedBeaconState preset},
      state ∈ (head.append tail).states → state ∈ head.states ∨ state ∈ tail.states
  | _, .nil, _, member => .inl member
  | _, .snoc tail _, _, member => by
    rcases List.mem_append.mp member with earlier | now
    · rcases mem_states_append head tail earlier with h | h
      · exact .inl h
      · exact .inr (List.mem_append_left _ h)
    · exact .inr (List.mem_append_right _ now)

/-- A state of a run through `X`, with a slot after that of `X`, is a state of the part
after `X`, and is reached from `X`. -/
theorem reaches_of_slot_lt {middle after : ForkedBeaconState preset}
    (head : Run config checks start middle) (tail : Run config checks middle after)
    {state : ForkedBeaconState preset} (member : state ∈ (head.append tail).states)
    (later : middle.state.slot.toNat < state.state.slot.toNat) :
    state ∈ tail.states ∧ Reaches config checks middle state := by
  rcases mem_states_append head tail member with h | h
  · exact absurd (slot_le_of_mem head state h) (Nat.not_le.mpr later)
  · exact ⟨h, reaches_of_mem tail state h⟩

end Run

/-- Two histories from one start that share the run to `X`, then go their own ways.

`X` may be any state they share: the end of their longest common prefix gives the tightest
drift bound, and a checkpoint finalized in both gives one that a client knows. -/
structure CommonState (config : Config) (checks : SignatureChecks)
    (start left right : ForkedBeaconState preset) where
  /-- The shared state. -/
  common : ForkedBeaconState preset
  /-- The shared run to it. -/
  shared : Run config checks start common
  /-- The rest of the first history. -/
  leftTail : Run config checks common left
  /-- The rest of the second history. -/
  rightTail : Run config checks common right

namespace CommonState

variable {start left right : ForkedBeaconState preset}
  (X : CommonState config checks start left right)

/-- The first history. -/
def leftRun : Run config checks start left := X.shared.append X.leftTail

/-- The second history. -/
def rightRun : Run config checks start right := X.shared.append X.rightTail

/-- Every state of either history with a slot after the shared state is reached from it on that
history. -/
theorem reaches_of_slot_lt {state : ForkedBeaconState preset}
    (member : state ∈ X.leftRun.states ∨ state ∈ X.rightRun.states)
    (later : X.common.state.slot.toNat < state.state.slot.toNat) :
    (state ∈ X.leftTail.states ∨ state ∈ X.rightTail.states) ∧
      Reaches config checks X.common state := by
  rcases member with h | h
  · obtain ⟨m, r⟩ := Run.reaches_of_slot_lt X.shared X.leftTail h later
    exact ⟨.inl m, r⟩
  · obtain ⟨m, r⟩ := Run.reaches_of_slot_lt X.shared X.rightTail h later
    exact ⟨.inr m, r⟩

/-- The weighing call for a target epoch `t ≥ lo` runs at a state whose slot closes epoch `t`
or `t + 1`. With at least two slots per epoch, its slot is after every slot up to the first slot
of `lo`. So such a call lies after `X` when `X` is no later than that slot. -/
theorem slot_lt_of_epoch {slot xSlot slotsPerEpoch lo t closing : ℕ} (two : 2 ≤ slotsPerEpoch)
    (common : xSlot ≤ lo * slotsPerEpoch) (target : lo ≤ t) (closes : t ≤ closing)
    (atCall : slot = (closing + 1) * slotsPerEpoch - 1) : xSlot < slot := by
  have := Nat.mul_le_mul_right slotsPerEpoch (show lo + 1 ≤ closing + 1 by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

end CommonState

end EthLib.Consensus
