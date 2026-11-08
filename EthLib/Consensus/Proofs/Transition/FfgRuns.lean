module

public import EthLib.Consensus.Proofs.Transition.FfgStore
public import EthLib.Consensus.Proofs.Transition.FfgStorePreElectra
public import EthLib.Consensus.Proofs.Transition.Provenance.RunIndexed
public import EthLib.Consensus.Proofs.Transition.RegistryGrowth

/-!
# Proofs: the FFG refinement of two runs, and the drift from a state they share

`historyRefinement` takes the calls of any chain from genesis to either end.

Here the histories are two runs from genesis, and the records are the calls on prefixes of them.

The provenance proofs give each field along a given run.

So every call that a field names is on one of the two runs.

That places the calls in time.

The two runs share a run to a state `X`.

A call on either run at a slot after `X` runs on a state that `X` reaches.

`accountable_safety_runs_preElectra` measures the drift from such an `X`, before Electra.

Any `X` before the first slot of the earlier finalized epoch places every call between the epochs.

The best choice is the later of the last shared state and that slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

section Runs

variable (config checks) {g a b : ForkedBeaconState preset}
  (runA : Run config checks g a) (runB : Run config checks g b)

/-- The parent links of the blocks of either run, with the child's slot. -/
def runLinks (p r : Root) (slot : ℕ) : Prop :=
  (∃ s : Slot, ChainBlockAt config checks g a p r s ∧ s.toNat = slot) ∨
    ∃ s : Slot, ChainBlockAt config checks g b p r s ∧ s.toNat = slot

/-- A hash with zero output on either run: a state root or a cached header root. -/
def runEvidence : Prop :=
  ZeroRootFound config checks g a ∨ ZeroRootFound config checks g b ∨
    ZeroHeaderFound config checks g a ∨ ZeroHeaderFound config checks g b

/-- A call on a prefix of either run. -/
def OnRuns (fork : Base.Fork) (state cached weighed : BeaconState preset fork)
    (voters : List ValidatorIndex) (c : Checkpoint) : Prop :=
  CallRecordOn runA fork state cached weighed voters c ∨
    CallRecordOn runB fork state cached weighed voters c

end Runs

/-- A call on a prefix of either run, with its end. -/
theorem OnRuns.cases {g a b : ForkedBeaconState preset} {runA : Run config checks g a}
    {runB : Run config checks g b} {fork : Base.Fork}
    {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
    {c : Checkpoint} (on : OnRuns config checks runA runB fork state cached weighed voters c) :
    ∃ x, (x = a ∨ x = b) ∧ CallRecord config checks g x fork state cached weighed voters c ∧
      ((⟨fork, state⟩ : ForkedBeaconState preset) ∈ runA.states ∨
        (⟨fork, state⟩ : ForkedBeaconState preset) ∈ runB.states) := by
  rcases on with call | call
  · exact ⟨a, .inl rfl, call.record, .inl call.mem⟩
  · exact ⟨b, .inr rfl, call.record, .inr call.mem⟩

/-- A `k`-finalization along a run by weighing calls is one by calls of either kind. -/
theorem KFinalizedByOn.callOn {start after : ForkedBeaconState preset}
    {run : Run config checks start after} {c : Checkpoint} (finalized : KFinalizedByOn run c) :
    KFinalizedByCallOn run c :=
  have ⟨k, one, two, cs, first, epochs, justified, ancestry, nonzero, fork, state, cached, weighed,
    _, voters, pre, call, onRun, source⟩ := finalized
  ⟨k, one, two, cs, first, epochs, fun i lt => .inl (justified i lt), ancestry, nonzero, fork,
    state, cached, weighed, voters, ⟨pre, call.record, onRun⟩, source⟩

/-- The FFG refinement of two runs from genesis. -/
def runRefinement {g a b : ForkedBeaconState preset} (runA : Run config checks g a)
    (runB : Run config checks g b) (genesis : Genesis config checks g)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (within : ∀ (fork : Base.Fork) (state : BeaconState preset fork),
      Reaches config checks ⟨fork, state⟩ a ∨ Reaches config checks ⟨fork, state⟩ b →
        state.RegistryWithinLimit) :
    FfgRefinement (EpochBlock (runLinks config checks (g := g) (a := a) (b := b))
      preset.SLOTS_PER_EPOCH.toNat) where
  block := EpochBlock.ofCheckpoint
  genesis := ⟨none⟩
  evidence := runEvidence config checks (g := g) (a := a) (b := b)
  signed := {p | ∃ y, (Reaches config checks y a ∨ Reaches config checks y b) ∧
    SignedVote config checks g y p.1 p.2}
  records := {r | ∃ (fork : Base.Fork) (state cached weighed : BeaconState preset fork)
    (voters : List ValidatorIndex) (c : Checkpoint),
    OnRuns config checks runA runB fork state cached weighed voters c ∧
      r = ⟨recordSource cached c.epoch, c, Weighing.ofState cached voters.toFinset⟩}
  justified := {c | c = g.state.finalizedCheckpoint ∨ c = g.state.previousJustifiedCheckpoint ∨
    c = g.state.currentJustifiedCheckpoint ∨
    ∃ (fork : Base.Fork) (state cached weighed : BeaconState preset fork)
      (voters : List ValidatorIndex),
      OnRuns config checks runA runB fork state cached weighed voters c}
  finalized := {c | c = ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ ∨ KFinalizedByCallOn runA c ∨
    KFinalizedByCallOn runB c}
  justified_recorded := by
    obtain ⟨-, previous, current, finalized⟩ := genesis_state genesis
    rintro c (rfl | rfl | rfl | ⟨fork, state, cached, weighed, voters, on⟩)
    · exact .inl (by rw [finalized]; exact genesis_toFfg)
    · exact .inl (by rw [previous]; exact genesis_toFfg)
    · exact .inl (by rw [current]; exact genesis_toFfg)
    · exact .inr ⟨_, ⟨fork, state, cached, weighed, voters, c, on, rfl⟩, rfl⟩
  source_justified := by
    rintro r ⟨fork, state, cached, weighed, voters, c, on, rfl⟩
    -- The source is justified on the same run, so it is the start's or a call's on the run.
    have toSet : ∀ {x : ForkedBeaconState preset} (run : Run config checks g x),
        (∀ {fork : Base.Fork} {state cached weighed : BeaconState preset fork}
          {voters : List ValidatorIndex} {d : Checkpoint},
          CallRecordOn run fork state cached weighed voters d →
          OnRuns config checks runA runB fork state cached weighed voters d) →
        ∀ {d : Checkpoint}, JustifiedOrStartOn run d →
          d = g.state.finalizedCheckpoint ∨ d = g.state.previousJustifiedCheckpoint ∨
          d = g.state.currentJustifiedCheckpoint ∨
          ∃ (fork : Base.Fork) (state cached weighed : BeaconState preset fork)
            (voters : List ValidatorIndex),
            OnRuns config checks runA runB fork state cached weighed voters d := by
      intro x run lift d justified
      rcases justified with h | h | h | byOn
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
      · obtain ⟨fork, state, cached, weighed, voters, call⟩ := byOn.callRecordOn
        exact .inr (.inr (.inr ⟨fork, state, cached, weighed, voters, lift call⟩))
    rcases on with call | call
    · obtain ⟨-, -, -, justified, -⟩ := call.source ⟨g, genesis, .refl g⟩
      exact toSet runA (fun call => .inl call) justified
    · obtain ⟨-, -, -, justified, -⟩ := call.source ⟨g, genesis, .refl g⟩
      exact toSet runB (fun call => .inr call) justified
  source_lt_target := by
    rintro r ⟨fork, state, cached, weighed, voters, c, on, rfl⟩
    obtain ⟨x, -, call, -⟩ := on.cases
    exact (call.source ⟨g, genesis, .refl g⟩).2
  source_le_target := by
    rintro r ⟨fork, state, cached, weighed, voters, c, on, rfl⟩
    obtain ⟨x, hx, call, -⟩ := on.cases
    have fromStart : g.state.slot.toNat ≤ c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      rw [(genesis_state genesis).1]
      exact Nat.zero_le _
    have evidenceOf : ZeroRootFound config checks g x ∨ ZeroHeaderFound config checks g x →
        runEvidence config checks (g := g) (a := a) (b := b) := by
      rcases hx with rfl | rfl <;> rintro (z | z)
      · exact .inl z
      · exact .inr (.inr (.inl z))
      · exact .inr (.inl z)
      · exact .inr (.inr (.inr z))
    have lift : ∀ {e : ℕ} {r r' : Root},
        PastAncestor config checks g x (e * preset.SLOTS_PER_EPOCH.toNat) r r' →
        Relation.ReflTransGen (EpochBlock.after (runLinks config checks (g := g) (a := a)
          (b := b)) preset.SLOTS_PER_EPOCH.toNat e) r r' := by
      intro e r r' path
      refine Relation.ReflTransGen.mono (fun _ _ ⟨s, at_, lt⟩ => ⟨s.toNat, ?_, lt⟩) _ _ path
      rcases hx with rfl | rfl
      · exact .inl ⟨s, at_, rfl⟩
      · exact .inr ⟨s, at_, rfl⟩
    rcases call.source_pastAncestor (by omega) genesis with zero | path | found
    · exact .inl (EpochBlock.ofCheckpoint_le (.inl zero))
    · rcases call.target_nonzero (by omega) fromStart with nonzero | header
      · exact .inl (EpochBlock.ofCheckpoint_le (.inr ⟨
          (call.source ⟨g, genesis, .refl g⟩).2.le, lift path, nonzero⟩))
      · exact .inr (evidenceOf (.inr header))
    · exact .inr (evidenceOf (.inl found))
  voters_signed := by
    rintro r ⟨fork, state, cached, weighed, voters, c, on, rfl⟩ i hi
    obtain ⟨x, hx, call, -⟩ := on.cases
    simp only [Weighing.ofState, List.mem_toFinset] at hi
    have member : ∀ data, SignedVote config checks g ⟨fork, state⟩ i data →
        (i, data) ∈ {p : ValidatorIndex × AttestationData | ∃ y,
          (Reaches config checks y a ∨ Reaches config checks y b) ∧
          SignedVote config checks g y p.1 p.2} := by
      intro data signed
      refine ⟨⟨fork, state⟩, ?_, signed⟩
      rcases hx with rfl | rfl
      · exact .inl call.toAfter
      · exact .inr call.toAfter
    by_cases altair : .altair ≤ fork
    · obtain ⟨data, target, signed, source⟩ :=
        call.voters_signed_of_genesis (by omega) lookahead genesis altair i hi
      exact ⟨data, member data signed, source, target⟩
    · obtain ⟨data, target, -, signed, source⟩ :=
        call.pending_voters_signed_of_genesis lookahead genesis (Nat.lt_of_not_le altair) i hi
      exact ⟨data, member data signed, source, target⟩
  threshold := by
    rintro r ⟨fork, state, cached, weighed, voters, c, on, rfl⟩
    obtain ⟨x, hx, call, -⟩ := on.cases
    have cachedWithin : cached.RegistryWithinLimit := by
      have toEnd :
          Reaches config checks ⟨fork, state⟩ a ∨ Reaches config checks ⟨fork, state⟩ b := by
        rcases hx with rfl | rfl
        · exact .inl call.toAfter
        · exact .inr call.toAfter
      have := within fork state toEnd
      unfold BeaconState.RegistryWithinLimit at this ⊢
      rcases call.reads with cachedOk | rfl
      · rw [(processSlot_keeps cachedOk).2.1]
        exact this
      · exact this
    have active : ∀ i ∈ voters, i ∈ getActiveValidatorIndices cached c.epoch := by
      by_cases altair : .altair ≤ fork
      · exact TargetVoters.active altair call.counted
      · intro i mem
        obtain ⟨_, _, activeAt, _⟩ :=
          call.pending_voters_signed_of_genesis lookahead genesis (Nat.lt_of_not_le altair) i mem
        exact activeAt
    exact supermajority_of_threshold call.passes cachedWithin fun i mem =>
      activeAt_lt ((mem_active_iff cachedWithin).mp (active i mem))
  finalized_rule := by
    -- A `k`-finalization on either run has every part the field asks for.
    have fromOn : ∀ {x : ForkedBeaconState preset} (run : Run config checks g x),
        (x = a ∨ x = b) →
        (∀ {fork : Base.Fork} {state cached weighed : BeaconState preset fork}
          {voters : List ValidatorIndex} {d : Checkpoint},
          CallRecordOn run fork state cached weighed voters d →
          OnRuns config checks runA runB fork state cached weighed voters d) →
        ∀ {c : Checkpoint}, KFinalizedByCallOn run c →
          ∃ k, 1 ≤ k ∧ ∃ cs : ℕ → Checkpoint, cs 0 = c ∧
            (∀ i ≤ k, (cs i).epoch.toNat = c.epoch.toNat + i) ∧
            (∀ i < k, cs i ∈ {c | c = g.state.finalizedCheckpoint ∨
              c = g.state.previousJustifiedCheckpoint ∨ c = g.state.currentJustifiedCheckpoint ∨
              ∃ (fork : Base.Fork) (state cached weighed : BeaconState preset fork)
                (voters : List ValidatorIndex),
                OnRuns config checks runA runB fork state cached weighed voters c}) ∧
            (∀ i < k, EpochBlock.ofCheckpoint (links := runLinks config checks (g := g) (a := a)
                (b := b)) (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat) (cs i) ≤
                EpochBlock.ofCheckpoint (cs (i + 1)) ∨
                  runEvidence config checks (g := g) (a := a) (b := b)) ∧
            ∃ r ∈ {r : WeighingRecord | ∃ (fork : Base.Fork)
                (state cached weighed : BeaconState preset fork) (voters : List ValidatorIndex)
                (c : Checkpoint),
                OnRuns config checks runA runB fork state cached weighed voters c ∧
                r = ⟨recordSource cached c.epoch, c, Weighing.ofState cached voters.toFinset⟩},
              r.source = c ∧ r.target = cs k := by
      rintro x run hx lift c ⟨k, hk, -, cs, h0, epochs, justified, ancestors, nonzero, fork, state,
        cached, weighed, voters, callOn, source⟩
      have evidenceOf : ZeroRootFound config checks g x ∨ ZeroHeaderFound config checks g x →
          runEvidence config checks (g := g) (a := a) (b := b) := by
        rcases hx with rfl | rfl <;> rintro (z | z)
        · exact .inl z
        · exact .inr (.inr (.inl z))
        · exact .inr (.inl z)
        · exact .inr (.inr (.inr z))
      refine ⟨k, hk, cs, h0, epochs, fun i hi => ?_, fun i hi => ?_,
        _, ⟨fork, state, cached, weighed, voters, cs k, lift callOn, rfl⟩,
        source, rfl⟩
      · rcases justified i hi with (h | h | h | byOn) | ⟨fork, state, cached, weighed, voters, call⟩
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (.inl h))
        · obtain ⟨fork, state, cached, weighed, voters, call⟩ := byOn.callRecordOn
          exact .inr (.inr (.inr ⟨fork, state, cached, weighed, voters, lift call⟩))
        · exact .inr (.inr (.inr ⟨fork, state, cached, weighed, voters, lift call⟩))
      · rcases ancestors i hi with path | zero
        · rcases nonzero (i + 1) hi (Nat.le_add_left 1 i) with ne | header
          · have ei := epochs i hi.le
            have ej := epochs (i + 1) hi
            refine .inl (EpochBlock.ofCheckpoint_le (.inr ⟨by omega, ?_, ne⟩))
            refine Relation.ReflTransGen.mono (fun _ _ ⟨s, at_, lt⟩ => ⟨s.toNat, ?_, lt⟩) _ _ path
            rcases hx with rfl | rfl
            · exact .inl ⟨s, at_, rfl⟩
            · exact .inr ⟨s, at_, rfl⟩
          · exact .inr (evidenceOf (.inr header))
        · exact .inr (evidenceOf (.inl zero))
    rintro c (rfl | byA | byB)
    · exact .inl genesis_toFfg
    · exact .inr (fromOn runA (.inl rfl) (fun call => .inl call) byA)
    · exact .inr (fromOn runB (.inr rfl) (fun call => .inr call) byB)

/-- A step never moves the fork back, so neither does a chain. -/
theorem Reaches.fork_le {x y : ForkedBeaconState preset} (chain : Reaches config checks x y) :
    x.fork ≤ y.fork := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => exact Nat.le_refl _
  | snoc run step ih =>
    cases step with
    | slot _ _ => exact ih
    | block _ _ _ _ _ => exact ih
    | @upgrade pre post _ _ => exact Nat.le_trans ih (Nat.le_of_lt post.2)

/-- Before Electra, a closed form bounds the drift from a reachable state `X` to a call it reaches.

The drift is from the weighing of `X`.

`n` bounds the epochs from `X` to the call's state, `K` the churn cap and `L` the lost stake there.
-/
theorem CallRecord.drift_le_preElectra {g x X : ForkedBeaconState preset} {fork : Base.Fork}
    {state cached weighed : BeaconState preset fork} {voters : List ValidatorIndex}
    {c : Checkpoint} (caps : EffectiveBalanceCaps preset) (two : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (genesis : Genesis config checks g)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (call : CallRecord config checks g x fork state cached weighed voters c)
    (reachableX : Reachable config checks X) (earlyX : X.fork < .pectra)
    (fromX : Reaches config checks X ⟨fork, state⟩) (early : fork < .pectra) {n K L : ℕ}
    (epochs : (getCurrentEpoch state).toNat - (getCurrentEpoch X.state).toNat ≤ n)
    (cap : max 1 (churnCap config state.validators.data.size) ≤ K)
    (lost : lostStake X.state state ≤ L) :
    Weighing.drift
        (Weighing.ofState X.state
          (getActiveValidatorIndices X.state (getCurrentEpoch X.state)).toFinset)
        (Weighing.ofState cached voters.toFinset) ≤
      2 * (n * K * preset.MAX_EFFECTIVE_BALANCE.toNat) + 2 * L +
        3 * deficit (preset := preset) X.state +
        3 * ((n + 1) * K * preset.MAX_EFFECTIVE_BALANCE.toNat) +
        3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat := by
  obtain ⟨stateRoots, blockRoots, header, availability, rfl⟩ := call.reads.eq
  have withinX := BeaconState.registryWithinLimit_of_lt
    (Nat.lt_of_lt_of_le earlyX (by decide)) X.state
  have withinS := BeaconState.registryWithinLimit_of_lt
    (Nat.lt_of_lt_of_le early (by decide)) state
  have capped := Reachable.effectiveBalancesCapped caps (ReachableFrom.reaches reachableX fromX)
  have activeVoters : ∀ i ∈ voters, i ∈ getActiveValidatorIndices state c.epoch := by
    by_cases altair : .altair ≤ fork
    · have := TargetVoters.active altair call.counted
      exact this
    · intro i mem
      obtain ⟨_, _, activeAt, _⟩ :=
        call.pending_voters_signed_of_genesis lookahead genesis (Nat.lt_of_not_le altair) i mem
      exact activeAt
  have voting : ∀ i ∈ voters.toFinset, activeAt state (getPreviousEpoch state) i.toNat = true ∨
      activeAt state (getCurrentEpoch state) i.toNat = true := by
    intro i mem
    have active := (mem_active_iff withinS).mp (activeVoters i (List.mem_toFinset.mp mem))
    rcases call.recent with h | h
    · exact .inl (h ▸ active)
    · exact .inr (h ▸ active)
  have drift := drift_ofState_le withinX withinS
    (getActiveValidatorIndices X.state (getCurrentEpoch X.state)).toFinset voters.toFinset
    capped early voting
  have finite := currentEpoch_lt_farFuture (state := state) two
  have leaving := fromX.leavingStake_le caps reachableX early finite
  have joining := fromX.joiningStakePrev_le_add caps reachableX early finite
  simp only at leaving joining
  have leaveWindow : ((getCurrentEpoch state).toNat - (getCurrentEpoch X.state).toNat) *
      max 1 (churnCap config state.validators.data.size) * preset.MAX_EFFECTIVE_BALANCE.toNat ≤
        n * K * preset.MAX_EFFECTIVE_BALANCE.toNat :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul epochs cap)
  have joinWindow : (((getCurrentEpoch state).toNat - (getCurrentEpoch X.state).toNat) *
      churnCap config state.validators.data.size +
        max 1 (churnCap config state.validators.data.size)) * preset.MAX_EFFECTIVE_BALANCE.toNat ≤
        (n + 1) * K * preset.MAX_EFFECTIVE_BALANCE.toNat := by
    refine Nat.mul_le_mul_right _ ?_
    have := Nat.mul_le_mul epochs ((le_max_right _ _).trans cap)
    calc ((getCurrentEpoch state).toNat - (getCurrentEpoch X.state).toNat) *
          churnCap config state.validators.data.size +
        max 1 (churnCap config state.validators.data.size)
        ≤ n * K + K := Nat.add_le_add this cap
      _ = (n + 1) * K := by rw [Nat.add_mul, Nat.one_mul]
  refine drift.trans ?_
  change 2 * leavingStake X.state state + 2 * lostStake X.state state +
      3 * deficit (preset := preset) X.state + 3 * joiningStakePrev X.state state +
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ _
  omega

/-- A slot is at least its epoch times the slots of an epoch. -/
theorem epoch_mul_le_slot (state : BeaconState preset fork') :
    (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat ≤ state.slot.toNat := by
  simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
  exact Nat.div_mul_le_self _ _

/-- States on runs to ends before Gloas have registries within their limit. -/
theorem runs_within {a b : ForkedBeaconState preset} (earlyA : a.fork < .glamsterdam)
    (earlyB : b.fork < .glamsterdam) :
    ∀ (fork : Base.Fork) (state : BeaconState preset fork),
      Reaches config checks ⟨fork, state⟩ a ∨ Reaches config checks ⟨fork, state⟩ b →
        state.RegistryWithinLimit := by
  intro fork state toEnd
  refine BeaconState.registryWithinLimit_of_lt ?_ state
  rcases toEnd with chain | chain
  · exact Nat.lt_of_le_of_lt chain.fork_le earlyA
  · exact Nat.lt_of_le_of_lt chain.fork_le earlyB

open scoped Classical in
/-- Accountable safety before Electra, measured at `X`, for two runs from genesis.

The two runs share a run to `X`.

`F` is finalized and `J` justified on the runs, and the epoch of `F` is at most that of `J`.

They conflict as epoch-boundary pairs.

`X` comes before the first slot of the epoch of `F`.

So every weighing call between the two epochs runs after `X` on its run, and `X` reaches it.

With `E` the epoch of `X`, `K` bounds the churn cap, and `L` the lost stake on the tails:

```text
  total(X) ≤ 3 * slashable(X) + 2 * (2 * (J + 1 - E) * K * MAX + 2 * L + 3 * deficit(X)
    + 3 * (J + 1 - E + 1) * K * MAX + 3 * INC)
```

Otherwise a state or a cached header of the runs has the zero root. -/
theorem accountable_safety_runs_preElectra {g a b : ForkedBeaconState preset}
    (X : CommonState config checks g a b) (caps : EffectiveBalanceCaps preset)
    (two : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (genesis : Genesis config checks g)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (earlyA : a.fork < .pectra) (earlyB : b.fork < .pectra) {f j : Checkpoint}
    (hf : f ∈ (runRefinement X.leftRun X.rightRun genesis wide4 lookahead
      (runs_within (Nat.lt_of_lt_of_le earlyA (by decide))
        (Nat.lt_of_lt_of_le earlyB (by decide)))).finalized)
    (hj : j ∈ (runRefinement X.leftRun X.rightRun genesis wide4 lookahead
      (runs_within (Nat.lt_of_lt_of_le earlyA (by decide))
        (Nat.lt_of_lt_of_le earlyB (by decide)))).justified)
    (hle : f.epoch.toNat ≤ j.epoch.toNat)
    (conflicting : Conflicting
      (EpochBlock.ofCheckpoint (links := runLinks config checks (g := g) (a := a) (b := b))
        (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat) f)
      (EpochBlock.ofCheckpoint j))
    (before : X.common.state.slot.toNat < f.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat)
    {K L : ℕ}
    (capBound : ∀ y, Reaches config checks X.common y →
      (getCurrentEpoch y.state).toNat ≤ j.epoch.toNat + 1 →
        max 1 (churnCap config y.state.validators.data.size) ≤ K)
    (lost : ∀ y, (y ∈ X.leftTail.states ∨ y ∈ X.rightTail.states) →
      (getCurrentEpoch y.state).toNat ≤ j.epoch.toNat + 1 → lostStake X.common.state y.state ≤ L) :
    let ω₀ := Weighing.ofState X.common.state
      (getActiveValidatorIndices X.common.state (getCurrentEpoch X.common.state)).toFinset
    let R := runRefinement X.leftRun X.rightRun genesis wide4 lookahead
      (runs_within (Nat.lt_of_lt_of_le earlyA (by decide)) (Nat.lt_of_lt_of_le earlyB (by decide)))
    stake ω₀.stake ω₀.active ≤
        3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2, (i, data1) ∈ R.signed ∧
          (i, data2) ∈ R.signed ∧ isSlashableAttestationData data1 data2 = true} +
        2 * (2 * ((j.epoch.toNat + 1 - (getCurrentEpoch X.common.state).toNat) * K *
            preset.MAX_EFFECTIVE_BALANCE.toNat) + 2 * L +
          3 * deficit (preset := preset) X.common.state +
          3 * ((j.epoch.toNat + 1 - (getCurrentEpoch X.common.state).toNat + 1) * K *
            preset.MAX_EFFECTIVE_BALANCE.toNat) +
          3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∨
      runEvidence config checks (g := g) (a := a) (b := b) := by
  intro ω₀ R
  refine R.accountable_safety_justified hf hj hle conflicting ω₀ ?_
  rintro r ⟨fork, state, cached, weighed, voters, c, on, rfl⟩ hlo hhi
  dsimp only at hlo hhi
  obtain ⟨x, hx, call, mem⟩ := on.cases
  have early : fork < .pectra := by
    rcases hx with rfl | rfl
    · exact Nat.lt_of_le_of_lt call.toAfter.fork_le earlyA
    · exact Nat.lt_of_le_of_lt call.toAfter.fork_le earlyB
  have reachableX : Reachable config checks X.common := ⟨g, genesis, ⟨X.shared⟩⟩
  have earlyX : X.common.fork < .pectra := Nat.lt_of_le_of_lt (Reaches.fork_le ⟨X.leftTail⟩) earlyA
  -- The call's state is at or after the first slot of its target, so after `X`.
  have stateEpoch : c.epoch.toNat ≤ (getCurrentEpoch state).toNat ∧
      (getCurrentEpoch state).toNat ≤ c.epoch.toNat + 1 := by
    obtain ⟨_, _, _, _, rfl⟩ := call.reads.eq
    rcases call.recent with h | h
    · change c.epoch = getPreviousEpoch state at h
      have := getPreviousEpoch_toNat state
      rw [h]
      omega
    · change c.epoch = getCurrentEpoch state at h
      rw [h]
      omega
  have later : X.common.state.slot.toNat < state.slot.toNat := by
    have slotEpoch := epoch_mul_le_slot state
    have : f.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
        (getCurrentEpoch state).toNat * preset.SLOTS_PER_EPOCH.toNat :=
      Nat.mul_le_mul_right _ (by have := stateEpoch.1; omega)
    omega
  obtain ⟨onTail, fromX⟩ := X.reaches_of_slot_lt (state := ⟨fork, state⟩) mem later
  exact call.drift_le_preElectra caps two genesis lookahead reachableX earlyX fromX early
    (by have := stateEpoch.2; omega) (capBound _ fromX (by dsimp only; omega))
    (lost _ onTail (by dsimp only; omega))

open scoped Classical in
/-- `accountable_safety_runs_preElectra` with the churn cap bounded by the registry growth from `X`.

The bound is `K = max 1 (churnCapWithin X (J + 1 - E))`. -/
theorem accountable_safety_runs_preElectra_registry {g a b : ForkedBeaconState preset}
    (X : CommonState config checks g a b) (caps : EffectiveBalanceCaps preset)
    (two : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) (genesis : Genesis config checks g)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (earlyA : a.fork < .pectra) (earlyB : b.fork < .pectra) {f j : Checkpoint}
    (hf : f ∈ (runRefinement X.leftRun X.rightRun genesis wide4 lookahead
      (runs_within (Nat.lt_of_lt_of_le earlyA (by decide))
        (Nat.lt_of_lt_of_le earlyB (by decide)))).finalized)
    (hj : j ∈ (runRefinement X.leftRun X.rightRun genesis wide4 lookahead
      (runs_within (Nat.lt_of_lt_of_le earlyA (by decide))
        (Nat.lt_of_lt_of_le earlyB (by decide)))).justified)
    (hle : f.epoch.toNat ≤ j.epoch.toNat)
    (conflicting : Conflicting
      (EpochBlock.ofCheckpoint (links := runLinks config checks (g := g) (a := a) (b := b))
        (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat) f)
      (EpochBlock.ofCheckpoint j))
    (before : X.common.state.slot.toNat < f.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat) {L : ℕ}
    (lost : ∀ y, (y ∈ X.leftTail.states ∨ y ∈ X.rightTail.states) →
      (getCurrentEpoch y.state).toNat ≤ j.epoch.toNat + 1 → lostStake X.common.state y.state ≤ L) :
    let ω₀ := Weighing.ofState X.common.state
      (getActiveValidatorIndices X.common.state (getCurrentEpoch X.common.state)).toFinset
    let R := runRefinement X.leftRun X.rightRun genesis wide4 lookahead
      (runs_within (Nat.lt_of_lt_of_le earlyA (by decide)) (Nat.lt_of_lt_of_le earlyB (by decide)))
    let n := j.epoch.toNat + 1 - (getCurrentEpoch X.common.state).toNat
    let K := max 1 (churnCapWithin config X.common n)
    stake ω₀.stake ω₀.active ≤
        3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2, (i, data1) ∈ R.signed ∧
          (i, data2) ∈ R.signed ∧ isSlashableAttestationData data1 data2 = true} +
        2 * (2 * (n * K * preset.MAX_EFFECTIVE_BALANCE.toNat) + 2 * L +
          3 * deficit (preset := preset) X.common.state +
          3 * ((n + 1) * K * preset.MAX_EFFECTIVE_BALANCE.toNat) +
          3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∨
      runEvidence config checks (g := g) (a := a) (b := b) := by
  refine accountable_safety_runs_preElectra X caps two genesis wide4 lookahead earlyA earlyB hf hj
    hle conflicting before ?_ lost
  intro y chain epochs
  refine (Reaches.churnCap_le (by omega) chain).trans (max_le_max_left 1 ?_)
  exact churnCapWithin_mono config X.common (by omega)

end EthLib.Consensus
