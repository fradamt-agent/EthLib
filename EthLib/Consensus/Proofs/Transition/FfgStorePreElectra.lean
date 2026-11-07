module

public import EthLib.Consensus.Proofs.Transition.FfgStore
public import EthLib.Consensus.Proofs.Transition.StakeLoss

/-!
# Proofs: accountable safety for a fork-choice store before Electra, in closed form

`store_accountable_safety` loses twice a drift bound `D` of the weighing calls between the store's
finalized and justified epochs.

Here `D` is instantiated before Electra, measured in the genesis state, which both chains share.

With `J` the justified epoch, `K` a bound on the churn cap and `L` a bound on lost stake:

```text
  D = 2 * (J + 1) * K * MAX + 2 * L + 3 * deficit(genesis) + 3 * (J + 2) * K * MAX + 3 * INC
```

- Leaving stake: at most `J + 1` epochs of exits, by L1's churn windows.
- Joining stake: at most `J + 2` epochs of activations, by L1's churn windows.
- Gains: at most the room of the genesis validators below `MAX_EFFECTIVE_BALANCE`, by the cap.
- Lost stake, `L`: a named bound on the effective balance that genesis validators lose.
  The inactivity leak drives it.
  `lostStake_le_fallen` bounds it, along any run, by each validator's slack at the start, what the
  run debits it, and the rounding; `Run.lost_le_budgets` splits the debits by flow.
- The churn cap, `K`: a named bound on `max 1 (churnCap config size)` over the reached states.
  It grows with the registry.

The store stays on one fork before Electra, so every state that its chains reach is of that fork.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks} {fork : Base.Fork}

/-- When no upgrade is ever due at a fork, a chain from a state of that fork stays at it. -/
theorem Reaches.fork_eq_of_notDue {s : BeaconState preset fork} {after : ForkedBeaconState preset}
    (notDue : ∀ state : BeaconState preset fork, upgradeDue config ⟨fork, state⟩ = false)
    (chain : Reaches config checks ⟨fork, s⟩ after) : after.fork = fork := by
  obtain ⟨run⟩ := chain
  induction run with
  | nil => rfl
  | @snoc middle last run step ih =>
    cases step with
    | slot _ _ => exact ih
    | block _ _ _ _ _ => exact ih
    | upgrade due _ =>
      obtain ⟨middleFork, middleState⟩ := middle
      simp only at ih
      subst ih
      rw [notDue middleState] at due
      cases due

/-- The epoch of a state whose slot fits in 64 bits, with at least two slots per epoch, is below the
far future epoch. -/
theorem currentEpoch_lt_farFuture {state : BeaconState preset fork}
    (two : 2 ≤ preset.SLOTS_PER_EPOCH.toNat) : (getCurrentEpoch state).toNat < 2 ^ 64 - 1 := by
  have slotBound := state.slot.toNat_lt
  simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div]
  have : state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ state.slot.toNat / 2 :=
    Nat.div_le_div_left two (by decide)
  omega

/-- The lost stake from a reachable state along a run, by validator: its slack at the start, what
the run debits its balance, and the rounding. -/
theorem lostStake_le_fallen (caps : EffectiveBalanceCaps preset)
    (increment : 0 < preset.EFFECTIVE_BALANCE_INCREMENT.toNat)
    {start after : ForkedBeaconState preset} (reachable : Reachable config checks start)
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64) :
    lostStake start.state after.state ≤
      ∑ j ∈ (Finset.range start.state.validators.data.size).filter
          (activeAt start.state (getCurrentEpoch start.state) · = true),
        ((effectiveAt start.state j - balanceAt start.state j) + run.fallen j +
          (preset.EFFECTIVE_BALANCE_INCREMENT.toNat - 1)) := by
  rw [lostStake, list_sum_filter_range]
  exact run.lost_le caps increment reachable small _ fun j member => (Finset.mem_filter.mp member).2

variable [NeZero preset.BYTES_PER_LOGS_BLOOM.toNat] [NeZero preset.SYNC_COMMITTEE_SIZE.toNat]
  [NeZero preset.MAX_COMMITTEES_PER_SLOT.toNat] [NeZero preset.PTC_SIZE.toNat]
  [NeZero preset.INCLUSION_LIST_COMMITTEE_SIZE.toNat]

open scoped Classical in
/-- Accountable safety for a fork-choice store before Electra, measured in the genesis state.

The hypotheses on the store are those of `store_accountable_safety`, and the store's fork is before
Electra.

`K` bounds the churn cap, and `L` the lost stake, from genesis to every state the chains reach.

Then the validators active at genesis hold at most three times the genesis stake of those that
signed two slashable attestation data, both checked in blocks of the chains, plus twice

```text
  2 * (J + 1) * K * MAX + 2 * L + 3 * deficit(genesis) + 3 * (J + 2) * K * MAX + 3 * INC
```

where `J` is the justified epoch.

Otherwise there is hash evidence. -/
theorem store_accountable_safety_preElectra {anchorState : BeaconState preset fork}
    {anchorBlock : BeaconBlock preset fork} {store : Store preset fork}
    (caps : EffectiveBalanceCaps preset) (before : fork < .pectra)
    (two : 2 ≤ preset.SLOTS_PER_EPOCH.toNat)
    (genesis : Genesis config checks ⟨fork, anchorState⟩)
    (genesisHeaderSlot : anchorState.latestBlockHeader.slot = GENESIS_SLOT)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (reachable : Store.ReachableWith config checks anchorState anchorBlock store)
    (notDue : ∀ state : BeaconState preset fork, upgradeDue config ⟨fork, state⟩ = false)
    (anchorSlot : anchorBlock.slot ≤ anchorState.slot)
    (anchorParent : anchorBlock.parentRoot = Vector.replicate 32 0)
    {head : ForkChoiceNode} (headOk : store.getHead config = .ok head)
    (notGenesis : store.finalizedCheckpoint.epoch ≠ GENESIS_EPOCH)
    (hle : store.finalizedCheckpoint.epoch.toNat ≤ store.justifiedCheckpoint.epoch.toNat)
    (notDescends : store.getCheckpointBlock store.justifiedCheckpoint.root
      store.finalizedCheckpoint.epoch ≠ .ok store.finalizedCheckpoint.root)
    {K L : ℕ}
    (capBound : ∀ state : BeaconState preset fork,
      Reaches config checks ⟨fork, anchorState⟩ ⟨fork, state⟩ →
      max 1 (churnCap config state.validators.data.size) ≤ K)
    (lost : ∀ state : BeaconState preset fork,
      Reaches config checks ⟨fork, anchorState⟩ ⟨fork, state⟩ → lostStake anchorState state ≤ L) :
    let ω₀ := Weighing.ofState anchorState
      (getActiveValidatorIndices anchorState (getCurrentEpoch anchorState)).toFinset
    ∃ a b : ForkedBeaconState preset,
      OnEither config checks ⟨fork, anchorState⟩ a b a ∧
      OnEither config checks ⟨fork, anchorState⟩ a b b ∧
      ∃ within, (stake ω₀.stake ω₀.active ≤
          3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2,
            (i, data1) ∈
              (historyRefinement (a := a) (b := b) genesis wide4 lookahead within).signed ∧
            (i, data2) ∈
              (historyRefinement (a := a) (b := b) genesis wide4 lookahead within).signed ∧
            isSlashableAttestationData data1 data2 = true} +
          2 * (2 * ((store.justifiedCheckpoint.epoch.toNat + 1) * K *
              preset.MAX_EFFECTIVE_BALANCE.toNat) + 2 * L +
            3 * deficit (preset := preset) anchorState +
            3 * ((store.justifiedCheckpoint.epoch.toNat + 2) * K *
              preset.MAX_EFFECTIVE_BALANCE.toNat) +
            3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat) ∨
        historyEvidence config checks ⟨fork, anchorState⟩ a b ∨
        StoreEvidence store (historyLinks config checks ⟨fork, anchorState⟩ a b)) := by
  intro ω₀
  generalize hJ : store.justifiedCheckpoint.epoch.toNat = J
  -- Every state that the chains reach is of the store's fork, so its registry is within its limit.
  have within : ∀ (fork' : Base.Fork) (state : BeaconState preset fork'),
      Reaches config checks ⟨fork, anchorState⟩ ⟨fork', state⟩ → state.RegistryWithinLimit := by
    intro fork' state chain
    have same : fork' = fork := chain.fork_eq_of_notDue notDue
    subst same
    exact BeaconState.registryWithinLimit_of_lt (Nat.lt_of_lt_of_le before (by decide)) state
  obtain ⟨a, b, onA, onB, safety⟩ := store_accountable_safety genesis genesisHeaderSlot wide4
    lookahead within reachable notDue anchorSlot anchorParent headOk notGenesis hle notDescends
  refine ⟨a, b, onA, onB, within, safety ω₀ ?_⟩
  -- Each weighing call between the two epochs drifts by at most the closed form.
  rintro r ⟨x, -, fork', state, cached, weighed, voters, c, call, rfl⟩ - hhi
  have same : fork' = fork := call.head.fork_eq_of_notDue notDue
  subst same
  have genesisReachable : Reachable config checks ⟨fork', anchorState⟩ := ⟨_, genesis, .refl _⟩
  have chain := call.head
  obtain ⟨stateRoots, blockRoots, header, availability, rfl⟩ := call.reads.eq
  have withinX := BeaconState.registryWithinLimit_of_lt
    (Nat.lt_of_lt_of_le before (by decide)) anchorState
  have withinS := BeaconState.registryWithinLimit_of_lt
    (Nat.lt_of_lt_of_le before (by decide)) state
  have capped :=
    Reachable.effectiveBalancesCapped caps (ReachableFrom.reaches genesisReachable chain)
  -- The voters were active in the target epoch, which is the previous or the current one.
  have activeVoters : ∀ i ∈ voters, i ∈ getActiveValidatorIndices state c.epoch := by
    by_cases altair : .altair ≤ fork'
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
    (getActiveValidatorIndices anchorState (getCurrentEpoch anchorState)).toFinset voters.toFinset
    capped before voting
  have finite := currentEpoch_lt_farFuture (state := state) two
  have leaving := chain.leavingStake_le caps genesisReachable before finite
  have joining := chain.joiningStakePrev_le_add caps genesisReachable before finite
  simp only at leaving joining
  have cap := capBound state chain
  have lostHere := lost state chain
  -- The epoch of the call's state is at most one after the target, which is at most `J`.
  have genesisEpoch : (getCurrentEpoch anchorState).toNat = 0 := by
    rw [genesis_currentEpoch genesis]
    rfl
  have stateEpoch : (getCurrentEpoch state).toNat ≤ J + 1 := by
    have target : c.epoch.toNat ≤ J := hJ ▸ hhi
    rcases call.recent with h | h
    · have := getPreviousEpoch_toNat state
      change c.epoch = getPreviousEpoch state at h
      rw [h] at target
      omega
    · change c.epoch = getCurrentEpoch state at h
      rw [h] at target
      omega
  have leaveWindow : ((getCurrentEpoch state).toNat - (getCurrentEpoch anchorState).toNat) *
      max 1 (churnCap config state.validators.data.size) * preset.MAX_EFFECTIVE_BALANCE.toNat ≤
        (J + 1) * K * preset.MAX_EFFECTIVE_BALANCE.toNat :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul (by omega) cap)
  have joinWindow : (((getCurrentEpoch state).toNat - (getCurrentEpoch anchorState).toNat) *
      churnCap config state.validators.data.size +
        max 1 (churnCap config state.validators.data.size)) * preset.MAX_EFFECTIVE_BALANCE.toNat ≤
        (J + 2) * K * preset.MAX_EFFECTIVE_BALANCE.toNat := by
    refine Nat.mul_le_mul_right _ ?_
    have := Nat.mul_le_mul (show (getCurrentEpoch state).toNat - (getCurrentEpoch anchorState).toNat
      ≤ J + 1 by omega) ((le_max_right _ _).trans cap)
    rw [show J + 2 = (J + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add this cap
  refine drift.trans ?_
  change 2 * leavingStake anchorState state + 2 * lostStake anchorState state +
      3 * deficit (preset := preset) anchorState + 3 * joiningStakePrev anchorState state +
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat ≤ _
  omega

end EthLib.Consensus
