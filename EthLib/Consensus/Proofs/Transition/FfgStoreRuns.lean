module

public import EthLib.Consensus.Proofs.Transition.FfgRuns
public import EthLib.Consensus.Proofs.Transition.StepDebits

/-!
# Proofs: accountable safety for a store, measured at a state that its two runs share

`store_accountable_safety` takes the two checkpoints of a store from two chains from genesis.

Here they come from two runs instead, so each call that justifies or finalizes them is on a run.

`store_accountable_safety_runs_preElectra` measures the drift at a state `X` on both runs.

`X` comes before the first slot of the finalized epoch.

The bound depends on the epochs from `X` to the justified epoch, not on the justified epoch alone.

Genesis is always such a state, by `CommonState.atStart`.

The best choice is the last state that the two runs share.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg Serialization.Ssz SszType

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Base.Fork}

/-- The empty run, then a run, is that run. -/
theorem Run.nil_append {start after : ForkedBeaconState preset}
    (run : Run config checks start after) : (Run.nil : Run config checks start start).append run =
      run := by
  induction run with
  | nil => rfl
  | snoc run step ih => exact congrArg (Run.snoc · step) ih

/-- Two runs from one start share at least that start. -/
def CommonState.atStart {start left right : ForkedBeaconState preset}
    (runA : Run config checks start left) (runB : Run config checks start right) :
    CommonState config checks start left right :=
  ⟨start, .nil, runA, runB⟩

theorem CommonState.atStart_runs {start left right : ForkedBeaconState preset}
    (runA : Run config checks start left) (runB : Run config checks start right) :
    (CommonState.atStart runA runB).leftRun = runA ∧
      (CommonState.atStart runA runB).rightRun = runB :=
  ⟨Run.nil_append runA, Run.nil_append runB⟩

/-- A state of a run ends a prefix of it, which debits each balance at most what the run does.

The state also reaches the end of the run. -/
theorem Run.fallen_prefix {x : ForkedBeaconState preset} :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks x after)
      {y : ForkedBeaconState preset}, y ∈ run.states →
      ∃ pre : Run config checks x y, (∀ j, pre.fallen j ≤ run.fallen j) ∧
        Reaches config checks y after
  | _, .nil, _, member => by
    obtain rfl := List.mem_singleton.mp member
    exact ⟨.nil, fun _ => Nat.le_refl _, ⟨.nil⟩⟩
  | _, .snoc run step, _, member => by
    rcases List.mem_append.mp member with inRun | atEnd
    · obtain ⟨pre, le, ⟨rest⟩⟩ := Run.fallen_prefix run inRun
      exact ⟨pre, fun j => Nat.le_trans (le j) (Nat.le_add_right _ _), ⟨rest.snoc step⟩⟩
    · obtain rfl := List.mem_singleton.mp atEnd
      exact ⟨.snoc run step, fun _ => Nat.le_refl _, ⟨.nil⟩⟩

/-- The loss bound of the validators active at `x`, given a list of step budgets for each.

Each validator gives its slack at `x`, the sum of its budgets over the flows, and the rounding. -/
def lossBudget (x : BeaconState preset fork) (budgets : Nat → List (BalanceFlow → Nat)) : ℕ :=
  ∑ j ∈ (Finset.range x.validators.data.size).filter
      (activeAt x (getCurrentEpoch x) · = true),
    ((effectiveAt x j - balanceAt x j) +
      (BalanceFlow.all.map fun flow => ((budgets j).map (· flow)).sum).sum +
      (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1))

/-- Every state of a run from a reachable state to a state before Gloas is ready for a ledger.

The registry limit must leave room for the pending deposits of an epoch in 64 bits. -/
theorem Run.ledgerReady
    (room : preset.VALIDATOR_REGISTRY_LIMIT.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat <
      2 ^ 64)
    {x after : ForkedBeaconState preset} (reachable : Reachable config checks x)
    (run : Run config checks x after) (early : after.fork < .glamsterdam) :
    ∀ y ∈ run.states, LedgerReady y := by
  intro y member
  obtain ⟨-, -, toEnd⟩ := run.fallen_prefix member
  have before := Nat.lt_of_le_of_lt toEnd.fork_le early
  have limit := BeaconState.registryWithinLimit_of_lt before y.state
  unfold BeaconState.RegistryWithinLimit at limit
  exact LedgerReady.of_reachable (ReachableFrom.reaches reachable (run.reaches_of_mem_states y
    member)) before (by omega)

/-- Along a run from a reachable state, before Gloas, the stake lost up to each state of it.

The validators active at the start lose at most `lossBudget` of step budgets of the whole run.

Each budget is of `StepBudget`, which names its amounts and where they come from.

The registry limit must leave room for the pending deposits of an epoch in 64 bits. -/
theorem Run.lostStake_le_budgets (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (room : preset.VALIDATOR_REGISTRY_LIMIT.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat <
      2 ^ 64)
    {x after : ForkedBeaconState preset} (reachable : Reachable config checks x)
    (run : Run config checks x after) (early : after.fork < .glamsterdam) :
    ∃ budgets : Nat → List (BalanceFlow → Nat), (∀ j, run.Budgets j (budgets j)) ∧
      ∀ y ∈ run.states, lostStake x.state y.state ≤ lossBudget x.state budgets := by
  have ready := run.ledgerReady room reachable early
  have each := fun j => run.fallen_le_stepBudgets j ready
  choose budgets budgetsOk bound using each
  refine ⟨budgets, budgetsOk, fun y member => ?_⟩
  obtain ⟨pre, le, -⟩ := run.fallen_prefix member
  have limit := (ready y member).within
  unfold BeaconState.RegistryWithinLimit at limit
  refine (lostStake_le_fallen caps increment reachable pre (by omega)).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  have := le j
  have := bound j
  omega

/-- On either tail after a shared state, before Gloas, the stake lost from the shared state.

It is at most the larger `lossBudget` of the step budgets of the two tails. -/
theorem CommonState.lostStake_le_budgets {g a b : ForkedBeaconState preset}
    (X : CommonState config checks g a b) (genesis : Genesis config checks g)
    (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (room : preset.VALIDATOR_REGISTRY_LIMIT.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat <
      2 ^ 64)
    (earlyA : a.fork < .glamsterdam) (earlyB : b.fork < .glamsterdam) :
    ∃ budgetsA budgetsB : Nat → List (BalanceFlow → Nat),
      (∀ j, X.leftTail.Budgets j (budgetsA j)) ∧ (∀ j, X.rightTail.Budgets j (budgetsB j)) ∧
      ∀ y, (y ∈ X.leftTail.states ∨ y ∈ X.rightTail.states) →
        lostStake X.common.state y.state ≤
          max (lossBudget X.common.state budgetsA) (lossBudget X.common.state budgetsB) := by
  have reachableX : Reachable config checks X.common := ⟨g, genesis, ⟨X.shared⟩⟩
  obtain ⟨budgetsA, okA, boundA⟩ :=
    X.leftTail.lostStake_le_budgets caps increment room reachableX earlyA
  obtain ⟨budgetsB, okB, boundB⟩ :=
    X.rightTail.lostStake_le_budgets caps increment room reachableX earlyB
  refine ⟨budgetsA, budgetsB, okA, okB, ?_⟩
  rintro y (member | member)
  · exact (boundA y member).trans (le_max_left _ _)
  · exact (boundB y member).trans (le_max_right _ _)

/-- `justified_of_checkpointFromRuns` along a run.

The checkpoint is justified on a run from genesis, by the start or by a call on a prefix of it. -/
theorem justified_of_checkpointFromRunsOn {anchorState : BeaconState preset fork}
    {anchor : Checkpoint}
    (genesis : Genesis config checks ⟨fork, anchorState⟩)
    (anchorEpoch : anchor.epoch = getCurrentEpoch anchorState) {c : Checkpoint}
    (notGenesis : c.epoch ≠ GENESIS_EPOCH)
    (origin : Store.CheckpointFromRuns config checks anchorState anchor
      (·.currentJustifiedCheckpoint) c) :
    ∃ (s : BeaconState preset fork) (run : Run config checks ⟨fork, anchorState⟩ ⟨fork, s⟩),
      JustifiedOrStartOn run c ∨ JustifiedByCallOn run c := by
  rcases origin with rfl | ⟨s, ⟨run⟩, rfl⟩ | ⟨s, t, ⟨run⟩, weighedOk, rfl⟩
  · exact absurd (anchorEpoch.trans (genesis_currentEpoch genesis)) notGenesis
  · exact ⟨s, run, .inl run.checkpointsOn.2.2⟩
  · rcases run.processJustificationAndFinalization_currentOn weighedOk with same | ⟨voters, call⟩
    · exact ⟨s, run, .inl same⟩
    · exact ⟨s, run, .inr ⟨fork, s, s, t, voters, call⟩⟩

/-- `finalized_of_checkpointFromRuns` along a run.

The checkpoint is `k`-finalized on a run from genesis, by calls on prefixes of it. -/
theorem finalized_of_checkpointFromRunsOn {anchorState : BeaconState preset fork}
    {anchor : Checkpoint}
    (genesis : Genesis config checks ⟨fork, anchorState⟩)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (anchorEpoch : anchor.epoch = getCurrentEpoch anchorState) {c : Checkpoint}
    (notGenesis : c.epoch ≠ GENESIS_EPOCH)
    (origin : Store.CheckpointFromRuns config checks anchorState anchor
      (·.finalizedCheckpoint) c) :
    ∃ (s : BeaconState preset fork) (run : Run config checks ⟨fork, anchorState⟩ ⟨fork, s⟩),
      KFinalizedByCallOn run c := by
  have ofState : ∀ (s : BeaconState preset fork)
      (run : Run config checks ⟨fork, anchorState⟩ ⟨fork, s⟩), c = s.finalizedCheckpoint →
      KFinalizedByCallOn run c := by
    intro s run same
    rcases run.finalized_ruleOn wide4 genesis with atGenesis | byOn
    · exact absurd (by rw [same, atGenesis]) notGenesis
    · exact same ▸ byOn.callOn
  rcases origin with rfl | ⟨s, ⟨run⟩, same⟩ | ⟨s, t, ⟨run⟩, weighedOk, same⟩
  · exact absurd (anchorEpoch.trans (genesis_currentEpoch genesis)) notGenesis
  · exact ⟨s, run, ofState s run same⟩
  · subst same
    dsimp only at ofState notGenesis ⊢
    rcases run.processJustificationAndFinalization_finalized_ruleOn wide4 genesis weighedOk with
      kept | atGenesis | byCall
    · exact ⟨s, run, ofState s run kept⟩
    · exact absurd (by rw [atGenesis]) notGenesis
    · exact ⟨s, run, byCall⟩

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

open scoped Classical in
/-- Accountable safety for the checkpoints of a fork-choice store before Electra.

The drift is measured at a state that the two runs share.

The store starts at genesis, and its fork is before Electra.

Its finalized checkpoint `F` is not at the genesis epoch.

The epoch of `F` is at most that of its justified checkpoint `J`.

Its head computes, and its justified block does not descend from `F` at the epoch of `F`.

Then there are two runs from genesis, to states `a` and `b`.

`J` is justified on the run to `a`, and `F` is finalized on the run to `b`.

Split the two runs at a shared state `X` before the first slot of the epoch of `F`.

Let `E` be the epoch of `X`, `n = J + 1 - E` and `K = max 1 (churnCapWithin X n)`.

Each tail after `X` has step budgets for each validator, of `StepBudget`.

Let `L` be the larger `lossBudget` of the two tails: slack at `X`, budgets and rounding.

Then the stake active at `X` is at most the following:

```text
  3 * slashable(X) + 2 * (2 * n * K * MAX + 2 * L + 3 * deficit(X) + 3 * (n + 1) * K * MAX
    + 3 * INC)
```

The slashable validators each signed two attestation data that the beacon chain slashes.

Both data were checked in blocks of the runs.

Otherwise there is hash evidence, one of:

- a state or a cached header of the runs with the zero root;
- two block headers with one root;
- a stored block at the zero root;
- a block of the runs whose root is zero. -/
theorem store_accountable_safety_runs_preElectra {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (genesis : Genesis config checks ⟨fork, anchorState⟩) (caps : EffectiveBalanceCaps preset)
    (two : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    (room : preset.VALIDATOR_REGISTRY_LIMIT.toNat + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat <
      2 ^ 64)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (early : fork < .pectra)
    (reachable : Store.ReachableWith config checks anchorState anchorBlock store)
    (notDue : ∀ state : BeaconState preset fork, upgradeDue config ⟨fork, state⟩ = false)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (anchorParent : anchorBlock.parentRoot = Vector.replicate 32 0)
    {head : ForkChoiceNode} (headOk : store.getHead config = .ok head)
    (notGenesis : store.finalizedCheckpoint.epoch ≠ GENESIS_EPOCH)
    (hle : store.finalizedCheckpoint.epoch.toNat ≤ store.justifiedCheckpoint.epoch.toNat)
    (notDescends : store.getCheckpointBlock store.justifiedCheckpoint.root
      store.finalizedCheckpoint.epoch ≠ .ok store.finalizedCheckpoint.root) :
    ∃ (sJ sF : BeaconState preset fork)
      (runA : Run config checks ⟨fork, anchorState⟩ ⟨fork, sJ⟩)
      (runB : Run config checks ⟨fork, anchorState⟩ ⟨fork, sF⟩),
      store.justifiedCheckpoint ∈ (runRefinement runA runB genesis wide4 lookahead
        (runs_within (Nat.lt_of_lt_of_le early (by decide))
          (Nat.lt_of_lt_of_le early (by decide)))).justified ∧
      store.finalizedCheckpoint ∈ (runRefinement runA runB genesis wide4 lookahead
        (runs_within (Nat.lt_of_lt_of_le early (by decide))
          (Nat.lt_of_lt_of_le early (by decide)))).finalized ∧
      ∀ (X : CommonState config checks ⟨fork, anchorState⟩ ⟨fork, sJ⟩ ⟨fork, sF⟩),
        X.leftRun = runA → X.rightRun = runB →
        X.common.state.slot.toNat <
          store.finalizedCheckpoint.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat →
        ∃ budgetsA budgetsB : Nat → List (BalanceFlow → Nat),
        (∀ j, X.leftTail.Budgets j (budgetsA j)) ∧ (∀ j, X.rightTail.Budgets j (budgetsB j)) ∧
        let ω₀ := Weighing.ofState X.common.state
          (getActiveValidatorIndices X.common.state (getCurrentEpoch X.common.state)).toFinset
        let R := runRefinement runA runB genesis wide4 lookahead
          (runs_within (Nat.lt_of_lt_of_le early (by decide))
            (Nat.lt_of_lt_of_le early (by decide)))
        let n := store.justifiedCheckpoint.epoch.toNat + 1 -
          (getCurrentEpoch X.common.state).toNat
        let K := max 1 (churnCapWithin config X.common n)
        let L := max (lossBudget X.common.state budgetsA) (lossBudget X.common.state budgetsB)
        stake ω₀.stake ω₀.active ≤
            3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2, (i, data1) ∈ R.signed ∧
              (i, data2) ∈ R.signed ∧ isSlashableAttestationData data1 data2 = true} +
            2 * (2 * (n * K * preset.MAX_EFFECTIVE_BALANCE.toNat) + 2 * L +
              3 * deficit (preset := preset) X.common.state +
              3 * ((n + 1) * K * preset.MAX_EFFECTIVE_BALANCE.toNat) +
              3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∨
          runEvidence config checks (g := ⟨fork, anchorState⟩) (a := ⟨fork, sJ⟩)
            (b := ⟨fork, sF⟩) ∨
          StoreEvidence store (runLinks config checks (g := ⟨fork, anchorState⟩)
            (a := ⟨fork, sJ⟩) (b := ⟨fork, sF⟩)) := by
  have wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat := by
    omega
  obtain ⟨anchorRoot, -, -, justifiedOrigin, finalizedOrigin, -, -⟩ :=
    reachable.checkpointsFromRuns notDue
  have justifiedNotGenesis : store.justifiedCheckpoint.epoch ≠ GENESIS_EPOCH := by
    intro atGenesis
    apply notGenesis
    rw [atGenesis] at hle
    exact UInt64.toNat_inj.mp (Nat.le_zero.mp (by simpa [GENESIS_EPOCH] using hle))
  obtain ⟨sJ, runA, justified⟩ :=
    justified_of_checkpointFromRunsOn genesis rfl justifiedNotGenesis justifiedOrigin
  obtain ⟨sF, runB, finalized⟩ :=
    finalized_of_checkpointFromRunsOn genesis wide4 rfl notGenesis finalizedOrigin
  -- The checkpoints are in the refinement of the two runs.
  have hj : store.justifiedCheckpoint ∈ (runRefinement runA runB genesis wide4 lookahead
      (runs_within (Nat.lt_of_lt_of_le early (by decide))
        (Nat.lt_of_lt_of_le early (by decide)))).justified := by
    rcases justified with (h | h | h | byOn) | ⟨fork', state, cached, weighed, voters, call⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))
    · obtain ⟨fork', state, cached, weighed, voters, call⟩ := byOn.callRecordOn
      exact .inr (.inr (.inr ⟨fork', state, cached, weighed, voters, .inl call⟩))
    · exact .inr (.inr (.inr ⟨fork', state, cached, weighed, voters, .inl call⟩))
  have hf : store.finalizedCheckpoint ∈ (runRefinement runA runB genesis wide4 lookahead
      (runs_within (Nat.lt_of_lt_of_le early (by decide))
        (Nat.lt_of_lt_of_le early (by decide)))).finalized := .inr (.inr finalized)
  refine ⟨sJ, sF, runA, runB, hj, hf, fun X onA onB before => ?_⟩
  obtain ⟨budgetsA, budgetsB, okA, okB, lostBound⟩ := X.lostStake_le_budgets genesis caps
    increment room (Nat.lt_of_lt_of_le early (by decide)) (Nat.lt_of_lt_of_le early (by decide))
  refine ⟨budgetsA, budgetsB, okA, okB, ?_⟩
  intro ω₀ R n K L
  -- The root facts that the store bridge needs, from the chains of the runs.
  have finalizedJustified :
      JustifiedOrStart config checks ⟨fork, anchorState⟩ ⟨fork, sF⟩ store.finalizedCheckpoint ∨
        JustifiedByCall config checks ⟨fork, anchorState⟩ ⟨fork, sF⟩
          store.finalizedCheckpoint := by
    obtain ⟨k, hk, -, cs, h0, -, justifiedAt, -⟩ := finalized
    rw [← h0]
    rcases justifiedAt 0 hk with byOn | byCall
    · exact .inl byOn.justifiedOrStart
    · exact .inr byCall.justifiedByCall
  have justifiedChain :
      JustifiedOrStart config checks ⟨fork, anchorState⟩ ⟨fork, sJ⟩ store.justifiedCheckpoint ∨
        JustifiedByCall config checks ⟨fork, anchorState⟩ ⟨fork, sJ⟩
          store.justifiedCheckpoint := by
    rcases justified with byOn | byCall
    · exact .inl byOn.justifiedOrStart
    · exact .inr byCall.justifiedByCall
  obtain ⟨fNonzero, fHeader, fFits⟩ :=
    justified_root_facts genesis wide notGenesis finalizedJustified
  obtain ⟨jNonzero, -, -⟩ :=
    justified_root_facts genesis wide justifiedNotGenesis justifiedChain
  rcases fNonzero with fNonzero | zero
  swap
  · exact .inr (.inl (.inr (.inr (.inr zero))))
  rcases jNonzero with jNonzero | zero
  swap
  · exact .inr (.inl (.inr (.inr (.inl zero))))
  rcases fHeader with fHeader | found
  swap
  · exact .inr (.inl (.inr (.inl found)))
  rcases reachable.reachable.conflicting_of_not_descends
      (links := runLinks config checks (g := ⟨fork, anchorState⟩) (a := ⟨fork, sJ⟩)
        (b := ⟨fork, sF⟩)) anchorSlot anchorParent headOk
      (fun link => by
        rcases link with ⟨s, block, slotEq⟩ | ⟨s, block, slotEq⟩ <;>
        · obtain ⟨header, rootOk, parent, headerSlot⟩ := block.header
          exact ⟨header, rootOk, parent, by rw [headerSlot, slotEq]⟩)
      fFits hle fNonzero jNonzero fHeader notDescends with
    conflicting | zeroLink | collision | zeroBlock
  · subst onA onB
    exact (accountable_safety_runs_preElectra_registry X caps two genesis wide4 lookahead early
      early hf hj hle conflicting before (fun y onTail _ => lostBound y onTail)).imp_right .inl
  · exact .inr (.inr (.inr (.inr zeroLink)))
  · exact .inr (.inr (.inl collision))
  · exact .inr (.inr (.inr (.inl zeroBlock)))

end EthLib.Consensus
