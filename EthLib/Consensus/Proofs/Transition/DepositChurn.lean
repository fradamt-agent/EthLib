module

public import EthLib.Consensus.Proofs.Transition.EpochPending
public import EthLib.Consensus.Proofs.Transition.ExitStake

/-!
# Proofs: the deposit balance that the churn admits, from Electra

From Electra deposits wait in a queue, as [EIP-7251] specifies.

Each epoch takes deposits from the front of the queue, while their balance fits.

The balance that fits is the churn of deposits, plus the churn that the epoch before carried over.

A deposit to a validator that is exiting waits again at the end, and spends no churn.

A deposit to a withdrawn validator is credited, and spends no churn either.

The balance that an epoch charges, plus the churn it carries over, is at most the balance that fit.

No other step changes the churn carried over.

So over a run, the balance charged is at most the churn carried over at its start.

It may also take one churn per epoch transition of the run.

The churn carried over is not bounded by the churn of one epoch.

It grows while the next deposit is larger than the balance that fits, until that deposit fits.

The churn of each state of the run must be at most a cap.

The facts hold while the registry has fewer than `2^64` validators.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-! ## One epoch's pass over the queue -/

/-- The deposit balance that the pass of an epoch charges to the churn, from a state.

It is the balance that `processPendingDeposits` counts as processed, and zero on an error. -/
def depositsProcessed (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (electra : .pectra ≤ fork) : Nat :=
  match (do
      let nextEpoch ← liftAccessor (liftArith (addChecked (getCurrentEpoch state) 1))
      let churn ← liftAccessor (depositChurnLimit config state)
      let available ←
        liftAccessor (liftArith (addChecked (state.depositBalanceToConsume electra) churn))
      let finalizedSlot ← liftAccessor
        (liftArith (computeStartSlotAtEpoch preset state.finalizedCheckpoint.epoch))
      let pass ← passPendingDeposits config checks (depositWaits state finalizedSlot) nextEpoch
        available state 0 0 #[] (state.pendingDeposits electra).data.toList
      return pass.1.processed : Except TransitionError Gwei) with
  | .ok processed => processed.toNat
  | .error _ => 0

/-- The pass of an epoch charges at most the balance that fits.

The churn it carries over takes the rest of that balance, or nothing. -/
theorem processPendingDeposits_charge {electra : .pectra ≤ fork} {churn : Gwei}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (churnOk : depositChurnLimit config state = .ok churn) :
    (after.depositBalanceToConsume electra).toNat + depositsProcessed config checks state electra ≤
      (state.depositBalanceToConsume electra).toNat + churn.toNat := by
  obtain ⟨nextEpoch, churn', available, finalizedSlot, pass, consumed, delayed, next, limit, added,
    finalized, passed, _, _, _, within, _, _, _, _, carry⟩ := processPendingDeposits_spec computed
  rw [limit] at churnOk
  cases churnOk
  have processed : depositsProcessed config checks state electra = pass.1.processed.toNat := by
    unfold depositsProcessed
    rw [liftAccessor_ok.mpr next, liftAccessor_ok.mpr limit]
    simp only [bind, Except.bind, liftAccessor_ok.mpr added, liftAccessor_ok.mpr finalized, passed,
      pure, Except.pure]
  have sum := (addChecked_ok_iff.mp (mapError_ok_iff.mp added)).2
  have le := UInt64.le_iff_toNat_le.mp within
  rw [processed, carry]
  split <;> omega

/-! ## The steps that keep the churn carried over -/

/-- A later state with the same churn of deposits carried over. -/
structure DepositKept (state after : BeaconState preset fork) : Prop where
  deposit : after.depositBalanceToConsume = state.depositBalanceToConsume

namespace DepositKept

theorem refl (state : BeaconState preset fork) : DepositKept state state := ⟨rfl⟩

theorem trans {first second third : BeaconState preset fork} (one : DepositKept first second)
    (two : DepositKept second third) : DepositKept first third :=
  ⟨two.deposit.trans one.deposit⟩

theorem of_eq (same : after.depositBalanceToConsume = state.depositBalanceToConsume) :
    DepositKept state after :=
  ⟨same⟩

theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → DepositKept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : DepositKept state after :=
  foldlM_ok_invariant (DepositKept state) (fun _ _ _ before ok => before.trans (kept _ _ _ ok))
    (.refl state) computed

theorem setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) :
    DepositKept state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact ⟨rfl⟩

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : EthLib.Consensus.increaseBalance state index delta = .ok after) :
    DepositKept state after := by
  obtain ⟨_, set⟩ := increaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact ⟨rfl⟩

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : EthLib.Consensus.decreaseBalance state index delta = .ok after) :
    DepositKept state after := by
  obtain ⟨_, set⟩ := decreaseBalance_ok computed
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact ⟨rfl⟩

end DepositKept

theorem depositKept_processSlashingsReset (computed : processSlashingsReset state = .ok after) :
    DepositKept state after := by
  obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq computed
  exact .of_eq rfl

theorem depositKept_processRandaoMixesReset (computed : processRandaoMixesReset state = .ok after) :
    DepositKept state after := by
  obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq computed
  exact .of_eq rfl

theorem depositKept_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) : DepositKept state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_eq rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem depositKept_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    DepositKept state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine DepositKept.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, set⟩ := ok
  exact .setValidator set

theorem depositKept_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      DepositKept state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact depositKept_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (DepositKept.decreaseBalance loweredOk).trans <|
      (DepositKept.increaseBalance raisedOk).trans
        (depositKept_passPendingConsolidations (result := (passed, read)) passedOk)

/-- The steps that close an epoch from Altair, after the history. -/
theorem depositKept_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : DepositKept rooted after := by
  have syncedKept : DepositKept rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact .of_eq rfl
  have lookedKept : DepositKept synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedKept : DepositKept looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedKept.trans (lookedKept.trans windowedKept)


/-! ## One slot -/

/-- The churn of deposits reads the state only through its total active balance. -/
theorem depositChurnLimit_of_total
    (total : getTotalActiveBalance after = getTotalActiveBalance state) :
    depositChurnLimit config after = depositChurnLimit config state := by
  simp only [depositChurnLimit, getActivationChurnLimit, getExitChurnLimit,
    getActivationExitChurnLimit, getBalanceChurnLimit, total]

/-- The deposit balance that the epoch transition of a slot charges, from Electra.

It is zero unless the slot is the last of its epoch.

The pass runs on the state after the steps of the epoch that come before the pending deposits.

Those are recomputed here from the state at the start of the slot. -/
def depositsChargedAt (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) : Nat :=
  if (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 then
    if electra : .pectra ≤ fork then
      have altair : .altair ≤ fork := Nat.le_trans (by decide) electra
      match (do
          let state ← processSlot state
          let state ← processJustificationAndFinalization state
          let state ← processInactivityUpdates config state altair
          let state ← processRewardsAndPenalties config state
          let state ← processRegistryUpdates config state
          let state ← processSlashings state
          (if before : fork < .hegota then processEth1DataReset before state else pure state) :
            Except TransitionError (BeaconState preset fork)) with
      | .ok reset => depositsProcessed config checks reset electra
      | .error _ => 0
    else 0
  else 0

/-- One slot from Electra keeps the churn of deposits carried over, or runs one pass of an epoch.

Take the balance the pass charges, plus the churn it carries over.

That is at most the churn carried over before, plus a cap on the churn of deposits of the state.
-/
theorem advanceSlot_depositsCharged {electra : .pectra ≤ fork} {cap : Nat}
    (computed : advanceSlot config checks state = .ok after)
    (small : after.validators.data.size < 2 ^ 64)
    (churns : ∀ churn, depositChurnLimit config state = .ok churn → churn.toNat ≤ cap) :
    (after.depositBalanceToConsume electra).toNat + depositsChargedAt config checks state ≤
      (state.depositBalanceToConsume electra).toNat +
        if (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 then cap else 0 := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, nextValue⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  -- The next slot is the slot plus one, without wrapping.
  have nextIs : next = state.slot + 1 := by
    apply UInt64.toNat_inj.mp
    rw [nextValue, UInt64.toNat_add]
    have : (1 : UInt64).toNat = 1 := rfl
    omega
  have cachedKept : ChargedStep config 0 0 0 electra state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact .of_eq rfl
  -- The last step of the slot sets only the slot.
  show ((epoched.depositBalanceToConsume electra).toNat + _ ≤ _)
  unfold epochIfLast at epochedOk
  rw [nextIs] at epochedOk
  split at epochedOk
  · rename_i last
    unfold processEpoch at epochedOk
    split at epochedOk
    · rename_i altair
      unfold processEpochAltair at epochedOk
      simp only [bind_ok_iff] at epochedOk
      obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
        registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk,
        balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := epochedOk
      -- The steps before the pending deposits keep the churn carried over and the total balance.
      have resetKept : ChargedStep config 0 0 0 electra slashed reset := by
        split at resetOk
        · exact chargedStep_processEth1DataReset resetOk
        · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
          exact resetOk ▸ .refl _
      have charged : ChargedStep config 0 0 0 electra state reset :=
        (cachedKept.trans <|
        (chargedStep_processJustificationAndFinalization justifiedOk).trans <|
        (chargedStep_processInactivityUpdates scoredOk).trans <|
        (chargedStep_processRewardsAndPenalties rewardedOk).trans <|
        (chargedStep_processRegistryUpdates registeredOk).trans
          (chargedStep_processSlashings slashedOk)).trans resetKept
      -- The deposits are the pass of `depositsChargedAt`.
      have recomputed : depositsChargedAt config checks state =
          depositsProcessed config checks reset electra := by
        simp only [depositsChargedAt, last, electra, ↓reduceIte, ↓reduceDIte]
        simp only [bind, Except.bind, cachedOk, justifiedOk, scoredOk, rewardedOk, registeredOk,
          slashedOk, resetOk]
      -- The steps after the slashings start no exit, and only grow the registry.
      have paidQuiet : QuietStep pending paid := by
        split at paidOk
        · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure,
            Except.pure, Except.ok.injEq] at paidOk
          obtain ⟨_, _, rfl⟩ := paidOk
          exact .of_eq rfl
        · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
          exact paidOk ▸ .refl _
      have paidKept : DepositKept pending paid := by
        split at paidOk
        · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure,
            Except.pure, Except.ok.injEq] at paidOk
          obtain ⟨_, _, rfl⟩ := paidOk
          exact .of_eq rfl
        · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
          exact paidOk ▸ .refl _
      have middleQuiet : QuietStep reset mixed :=
        (quietStep_processPendingBalances pendingOk).trans <| paidQuiet.trans <|
        (quietStep_processEffectiveBalanceUpdates balancedOk).trans <|
        (quietStep_processSlashingsReset clearedOk).trans
          (quietStep_processRandaoMixesReset mixedOk)
      have middleKept : DepositKept paid mixed :=
        (depositKept_processEffectiveBalanceUpdates balancedOk).trans <|
        (depositKept_processSlashingsReset clearedOk).trans
          (depositKept_processRandaoMixesReset mixedOk)
      have tail : QuietStep mixed epoched ∧ DepositKept mixed epoched := by
        split at computed <;> simp only [bind_ok_iff] at computed <;>
          obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
        · have rootedQuiet : QuietStep mixed rooted ∧ DepositKept mixed rooted := by
            unfold processHistoricalSummariesUpdate at rootedOk
            simp only [bind, Except.bind, pure, Except.pure] at rootedOk
            repeat' (split at rootedOk <;> try cases rootedOk)
            all_goals first
              | exact ⟨.refl _, .refl _⟩
              | exact ⟨.of_eq rfl, .of_eq rfl⟩
          exact ⟨rootedQuiet.1.trans (quietStep_epochEnd syncedOk lookedOk windowed),
            rootedQuiet.2.trans (depositKept_epochEnd syncedOk lookedOk windowed)⟩
        · exact ⟨(quietStep_processHistoricalRootsUpdate rootedOk).trans
              (quietStep_epochEnd syncedOk lookedOk windowed),
            (depositKept_processHistoricalRootsUpdate rootedOk).trans
              (depositKept_epochEnd syncedOk lookedOk windowed)⟩
      have resetSmall : reset.validators.data.size < 2 ^ 64 :=
        Nat.lt_of_le_of_lt (middleQuiet.trans tail.1).size_le small
      unfold processPendingBalances at pendingOk
      simp only [electra, ↓reduceDIte, bind_ok_iff] at pendingOk
      obtain ⟨deposited, depositedOk, consolidatedOk⟩ := pendingOk
      have consolidatedKept : DepositKept deposited pending := by
        unfold processPendingConsolidations at consolidatedOk
        simp only [bind, Except.bind, pure, Except.pure] at consolidatedOk
        repeat' (split at consolidatedOk <;> try cases consolidatedOk)
        all_goals exact (depositKept_passPendingConsolidations ‹_›).trans (.of_eq rfl)
      obtain ⟨_, churn, _, _, _, _, _, _, limit, _⟩ := processPendingDeposits_spec depositedOk
      have charge := processPendingDeposits_charge depositedOk limit
      -- The churn of deposits of the pass is that of the state, since the total balance is.
      have sameChurn := depositChurnLimit_of_total (config := config)
        (charged.frozen.total resetSmall)
      rw [sameChurn] at limit
      have churnLe := churns churn limit
      have carried := (consolidatedKept.trans (paidKept.trans (middleKept.trans tail.2))).deposit
      rw [recomputed, carried, ← charged.frozen.deposit]
      simp only [last, ↓reduceIte]
      omega
    · rename_i notAltair
      exact absurd (Nat.le_trans (by decide) electra) notAltair
  · rename_i notLast
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    simp only [depositsChargedAt, notLast, ↓reduceIte, Nat.add_zero]
    rw [cachedKept.frozen.deposit]

/-! ## Runs -/

/-- The churn of deposits carried over by a forked state from Electra, and zero before it. -/
def forkedDepositCarry (forked : ForkedBeaconState preset) : Nat :=
  if electra : .pectra ≤ forked.fork then (forked.state.depositBalanceToConsume electra).toNat
  else 0

/-- The deposit balance that one step charges to the churn: only a slot step may. -/
def Step.depositsCharged {before after : ForkedBeaconState preset} :
    Step config checks before after → Nat
  | .slot (state := current) _ _ => depositsChargedAt config checks current
  | .upgrade _ _ => 0
  | .block _ _ _ _ _ => 0

/-- Whether one step is an epoch transition: a slot step at the last slot of its epoch. -/
def Step.epochTransitions {before after : ForkedBeaconState preset} :
    Step config checks before after → Nat
  | .slot (state := current) _ _ =>
    if (current.slot + 1) % preset.SLOTS_PER_EPOCH = 0 then 1 else 0
  | .upgrade _ _ => 0
  | .block _ _ _ _ _ => 0

/-- The deposit balance that the epoch transitions of a run charge to the churn. -/
def Run.depositsCharged {start : ForkedBeaconState preset} :
    {after : ForkedBeaconState preset} → Run config checks start after → Nat
  | _, .nil => 0
  | _, .snoc run step => run.depositsCharged + step.depositsCharged

/-- The epoch transitions of a run: its slots that are the last of their epoch. -/
def Run.epochTransitions {start : ForkedBeaconState preset} :
    {after : ForkedBeaconState preset} → Run config checks start after → Nat
  | _, .nil => 0
  | _, .snoc run step => run.epochTransitions + step.epochTransitions

/-- An upgrade from Electra on carries the churn of deposits carried over. -/
theorem upgradeNext_depositBalanceToConsume {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (electra : .pectra ≤ pre.fork) (computed : upgradeNext config checks pre = .ok post) :
    ∀ electra' : .pectra ≤ post.val.fork,
      post.val.state.depositBalanceToConsume electra' =
        pre.state.depositBalanceToConsume electra := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  all_goals try exact absurd electra (by simp only; decide)
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at upgraded
    obtain ⟨_, -, rfl⟩ := upgraded
    exact fun _ => rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToGloas, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, onboarded⟩ := upgraded
    obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    exact fun _ => rfl
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact fun _ => rfl

/-- The deposit balance that a run from Electra on charges to the churn.

It is at most the churn carried over at the start, plus one cap per epoch transition.

The churn carried over at the end takes part of that bound too.

The cap must bound the churn of deposits of every state of the run.

This holds while the registry has fewer than `2^64` validators. -/
theorem Run.depositsCharged_le {cap : Nat} {start : ForkedBeaconState preset}
    (electra : .pectra ≤ start.fork) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      after.state.validators.data.size < 2 ^ 64 →
      (∀ forked ∈ run.states, ∀ churn,
        depositChurnLimit config forked.state = .ok churn → churn.toNat ≤ cap) →
      forkedDepositCarry after + run.depositsCharged ≤
        forkedDepositCarry start + run.epochTransitions * cap
  | _, .nil, _, _ => by simp [Run.depositsCharged, Run.epochTransitions]
  | _, .snoc (middle := middle) run step, small, churns => by
    have electraMiddle : .pectra ≤ middle.fork := Nat.le_trans electra (Run.fork_le run)
    have middleIn : middle ∈ (Run.snoc run step).states :=
      List.mem_append_left _ (Run.end_mem_states run)
    have earlier : ∀ forked ∈ run.states, forked ∈ (Run.snoc run step).states :=
      fun _ member => List.mem_append_left _ member
    have before := fun (middleSmall : middle.state.validators.data.size < 2 ^ 64) =>
      Run.depositsCharged_le electra run middleSmall
        (fun forked member => churns forked (earlier forked member))
    cases step with
    | slot _ computed =>
      have charge := stepCharge_advanceSlot (capExit := 0) (capConsolidation := 0) (largest := 0)
        (electra := electraMiddle) computed
      have step := advanceSlot_depositsCharged (electra := electraMiddle) computed small
        (churns _ middleIn)
      have rest := before (Nat.lt_of_le_of_lt charge.size_le small)
      simp only [forkedDepositCarry, electraMiddle, ↓reduceDIte] at rest step ⊢
      simp only [Run.depositsCharged, Run.epochTransitions, Step.depositsCharged,
        Step.epochTransitions]
      split at step <;> simp_all only [↓reduceIte, Nat.add_mul, Nat.one_mul, Nat.add_zero] <;>
        omega
    | block _ _ _ _ computed =>
      have charge := chargedStep_processBlock (capExit := 0) (capConsolidation := 0) (largest := 0)
        (electra := electraMiddle) (applySignedBlock_ok computed).2.1
      have rest := before (Nat.lt_of_le_of_lt charge.frozen.size_le small)
      simp only [forkedDepositCarry, electraMiddle, ↓reduceDIte] at rest ⊢
      simp only [Run.depositsCharged, Run.epochTransitions, Step.depositsCharged,
        Step.epochTransitions, charge.frozen.deposit]
      exact rest
    | upgrade _ computed =>
      have same := (upgradeNext_keeps electraMiddle computed).1
      have rest := before (by rw [← same]; exact small)
      rename_i post _
      have electra' : Fork.pectra ≤ post.val.fork :=
        Nat.le_trans electraMiddle (Nat.le_of_lt post.property)
      have carried := upgradeNext_depositBalanceToConsume electraMiddle computed electra'
      simp only [forkedDepositCarry, electraMiddle, electra', ↓reduceDIte, carried] at rest ⊢
      simp only [Run.depositsCharged, Run.epochTransitions, Step.depositsCharged,
        Step.epochTransitions]
      exact rest

/-! ## Epoch transitions -/

/-- One slot moves the epoch on by one exactly when it is the last slot of its epoch. -/
theorem advanceSlot_epoch (computed : advanceSlot config checks state = .ok after) :
    (getCurrentEpoch after).toNat = (getCurrentEpoch state).toNat +
      if (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 then 1 else 0 := by
  have slot := advanceSlot_slot computed
  have small := after.slot.toNat_lt
  -- The slot plus one does not wrap, so its residue is that of the natural number.
  have plusOne : (state.slot + 1).toNat = state.slot.toNat + 1 := by
    rw [UInt64.toNat_add]
    have : (1 : UInt64).toNat = 1 := rfl
    omega
  simp only [getCurrentEpoch, computeEpochAtSlot, UInt64.toNat_div, slot]
  have residue : ((state.slot + 1) % preset.SLOTS_PER_EPOCH = 0) ↔
      (state.slot.toNat + 1) % preset.SLOTS_PER_EPOCH.toNat = 0 := by
    rw [← plusOne, ← UInt64.toNat_mod, ← UInt64.toNat_inj]
    rfl
  rw [Nat.succ_div]
  by_cases last : (state.slot + 1) % preset.SLOTS_PER_EPOCH = 0
  · have := residue.mp last
    simp only [last, ↓reduceIte, Nat.dvd_iff_mod_eq_zero.mpr this]
  · have : ¬ preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 :=
      fun divides => last (residue.mpr (Nat.mod_eq_zero_of_dvd divides))
    simp only [last, ↓reduceIte, this]

/-- Along a run from Electra on, the current epoch moves on by one per epoch transition.

Blocks and upgrades keep the slot. -/
theorem Run.epochTransitions_eq {start : ForkedBeaconState preset}
    (electra : .pectra ≤ start.fork) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      (getCurrentEpoch after.state).toNat =
        (getCurrentEpoch start.state).toNat + run.epochTransitions
  | _, .nil => rfl
  | _, .snoc (middle := middle) run step => by
    have electraMiddle : .pectra ≤ middle.fork := Nat.le_trans electra (Run.fork_le run)
    have before := Run.epochTransitions_eq electra run
    cases step with
    | slot _ computed =>
      simp only [Run.epochTransitions, Step.epochTransitions, advanceSlot_epoch computed, before]
      omega
    | block _ _ _ _ computed =>
      have slot := (chargedStep_processBlock (capExit := 0) (capConsolidation := 0) (largest := 0)
        (electra := electraMiddle) (applySignedBlock_ok computed).2.1).frozen.slot
      simp only [Run.epochTransitions, Step.epochTransitions, getCurrentEpoch, slot] at before ⊢
      omega
    | upgrade _ computed =>
      have slot := (upgradeNext_keeps electraMiddle computed).2.1
      simp only [Run.epochTransitions, Step.epochTransitions, getCurrentEpoch, slot] at before ⊢
      omega

/-- The deposit balance that a run from Electra on charges to the churn, by epochs.

It is at most the churn carried over at the start, plus one cap per epoch of the run.

The churn carried over at the end takes part of that bound too.

The cap must bound the churn of deposits of every state of the run.

This holds while the registry has fewer than `2^64` validators. -/
theorem Run.depositsCharged_le_epochs {cap : Nat} {start after : ForkedBeaconState preset}
    (electra : .pectra ≤ start.fork) (run : Run config checks start after)
    (small : after.state.validators.data.size < 2 ^ 64)
    (churns : ∀ forked ∈ run.states, ∀ churn,
      depositChurnLimit config forked.state = .ok churn → churn.toNat ≤ cap) :
    forkedDepositCarry after + run.depositsCharged ≤ forkedDepositCarry start +
      ((getCurrentEpoch after.state).toNat - (getCurrentEpoch start.state).toNat) * cap := by
  have epochs := Run.epochTransitions_eq electra run
  have charged := Run.depositsCharged_le electra run small churns
  rw [epochs, Nat.add_sub_cancel_left]
  exact charged

/-! ## The stake that joins the active set -/

/-- The effective stake of the validators of a state that are not active in its current epoch.

Only those that have not left before that epoch count.

They are the validators that wait to be active, eligible or not, and those that leave at it. -/
def pendingActivationStake (state : BeaconState preset fork) : Nat :=
  ∑ position ∈ (Finset.range state.validators.data.size).filter (fun position =>
      (state.validators.data[position]?).any fun validator =>
        !isActiveValidator validator (getCurrentEpoch state) &&
          decide (getCurrentEpoch state ≤ validator.exitEpoch)),
    effectiveBalanceAtPosition state position

/-- The stake that joins the active set over a run from Electra on.

Take the validators active at the previous or current epoch of the last state.

Keep those not active at the current epoch of the first state.

Their effective balance in the last state is split three ways.

- The stake waiting to be active in the first state, read from it.
- The growth of the effective balance of the other validators of the first state that join.
- The effective balance of the validators that the run adds.

Deposits and rewards pay for the last two.

In Electra a validator eligible for activation is activated without a limit on their count.

So the stake waiting in the first state may all join in one epoch.

The last state's epoch must be at least the first's.

This holds while the registry has fewer than `2^64` validators. -/
theorem Run.joiningStakePrev_le {start after : ForkedBeaconState preset}
    (electra : .pectra ≤ start.fork) (run : Run config checks start after)
    (small : after.state.validators.data.size < 2 ^ 64)
    (epochs : getCurrentEpoch start.state ≤ getCurrentEpoch after.state) :
    let joins := fun position =>
      ((after.state.validators.data[position]?).any
          (isActiveValidator · (getPreviousEpoch after.state)) ||
        (after.state.validators.data[position]?).any
          (isActiveValidator · (getCurrentEpoch after.state))) &&
        !(start.state.validators.data[position]?).any
          (isActiveValidator · (getCurrentEpoch start.state))
    (((List.range after.state.validators.data.size).filter joins).map
        fun position => effectiveBalanceAtPosition after.state position).sum ≤
      pendingActivationStake start.state +
        ∑ position ∈ ((Finset.range after.state.validators.data.size).filter fun position =>
            joins position = true ∧ position < start.state.validators.data.size),
          (effectiveBalanceAtPosition after.state position -
            effectiveBalanceAtPosition start.state position) +
        ∑ position ∈ ((Finset.range after.state.validators.data.size).filter fun position =>
            joins position = true ∧ ¬ position < start.state.validators.data.size),
          effectiveBalanceAtPosition after.state position := by
  intro joins
  have kept := Run.exitsKept electra run small
  rw [sum_map_filter_range]
  -- Split the joining validators into those of the first state and those that the run adds.
  rw [← Finset.sum_filter_add_sum_filter_not _ (· < start.state.validators.data.size),
    Finset.filter_filter, Finset.filter_filter]
  have old : ∑ position ∈ ((Finset.range after.state.validators.data.size).filter fun position =>
        joins position = true ∧ position < start.state.validators.data.size),
        effectiveBalanceAtPosition after.state position ≤
      pendingActivationStake start.state +
        ∑ position ∈ ((Finset.range after.state.validators.data.size).filter fun position =>
            joins position = true ∧ position < start.state.validators.data.size),
          (effectiveBalanceAtPosition after.state position -
            effectiveBalanceAtPosition start.state position) := by
    -- Each one was waiting in the first state.
    have waiting : ((Finset.range after.state.validators.data.size).filter fun position =>
          joins position = true ∧ position < start.state.validators.data.size) ⊆
        (Finset.range start.state.validators.data.size).filter (fun position =>
          (start.state.validators.data[position]?).any fun validator =>
            !isActiveValidator validator (getCurrentEpoch start.state) &&
              decide (getCurrentEpoch start.state ≤ validator.exitEpoch)) := by
      intro position member
      obtain ⟨_, joined, inside⟩ := Finset.mem_filter.mp member
      obtain ⟨validator, found⟩ : ∃ validator,
          start.state.validators.data[position]? = some validator :=
        ⟨_, Array.getElem?_eq_getElem inside⟩
      obtain ⟨later, laterFound, exits⟩ := kept.exits small position validator found
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr inside, ?_⟩
      simp only [joins, found, laterFound, Option.any_some, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true'] at joined
      obtain ⟨active, inactive⟩ := joined
      simp only [found, Option.any_some, inactive, Bool.not_false, Bool.true_and,
        decide_eq_true_eq]
      -- Active at an epoch from one before the first state's, so it had not left before it.
      rcases exits with same | far
      · have before : ∃ epoch : Epoch, (getCurrentEpoch start.state).toNat ≤ epoch.toNat + 1 ∧
            isActiveValidator later epoch = true := by
          rcases active with previous | current
          · refine ⟨getPreviousEpoch after.state, ?_, previous⟩
            simp only [getPreviousEpoch, toNat_saturatingSub]
            have := UInt64.le_iff_toNat_le.mp epochs
            have : (1 : UInt64).toNat = 1 := rfl
            omega
          · exact ⟨getCurrentEpoch after.state,
              by have := UInt64.le_iff_toNat_le.mp epochs; omega, current⟩
        obtain ⟨epoch, near, isActive⟩ := before
        simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq] at isActive
        have := UInt64.lt_iff_toNat_lt.mp isActive.2
        rw [same] at this
        exact UInt64.le_iff_toNat_le.mpr (by omega)
      · rw [far]
        have farValue : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
        have := (getCurrentEpoch start.state).toNat_lt
        exact UInt64.le_iff_toNat_le.mpr (by omega)
    have bound := Finset.sum_le_sum_of_subset (f := effectiveBalanceAtPosition start.state) waiting
    have split :
        ∑ position ∈ ((Finset.range after.state.validators.data.size).filter fun position =>
          joins position = true ∧ position < start.state.validators.data.size),
          effectiveBalanceAtPosition after.state position ≤
        ∑ position ∈ ((Finset.range after.state.validators.data.size).filter fun position =>
          joins position = true ∧ position < start.state.validators.data.size),
          effectiveBalanceAtPosition start.state position +
        ∑ position ∈ ((Finset.range after.state.validators.data.size).filter fun position =>
            joins position = true ∧ position < start.state.validators.data.size),
          (effectiveBalanceAtPosition after.state position -
            effectiveBalanceAtPosition start.state position) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun _ _ => by omega
    unfold pendingActivationStake
    omega
  omega

end EthLib.Consensus
