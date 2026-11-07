module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import EthLib.Consensus.Proofs.Transition.DepositChurn
public import EthLib.Consensus.Proofs.Transition.GainedBound

/-!
# Proofs: the deposits credited to each validator, from Electra

From Electra a pass over the pending deposits credits each deposit to one validator, if any.

A deposit to a validator not yet withdrawn takes its amount from the churn of deposits.

A deposit to a withdrawn validator takes nothing from that churn.

So the deposits credited to validators not yet withdrawn sum to at most the churn charged.

[EIP-7251] specifies the pending deposits and their churn.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#specification
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-- A position that holds no validator, or one not withdrawn before an epoch. -/
def HoldsUnwithdrawn (state : BeaconState preset fork) (epoch : Nat) (index : Nat) : Prop :=
  ∀ validator, state.validators.data[index]? = some validator →
    epoch ≤ validator.withdrawableEpoch.toNat

/-- A registry that stays, or grows by one validator not withdrawable, keeps the property. -/
theorem HoldsUnwithdrawn.of_grown {state after : BeaconState preset fork} {epoch : Nat}
    {index : Nat} {deposit : PendingDeposit} (bounded : epoch < 2 ^ 64)
    (grown : after.validators.data = state.validators.data ∨
      ∃ validator, after.validators.data = state.validators.data.push validator ∧
        validator.pubkey = deposit.pubkey ∧ validator.withdrawableEpoch = FAR_FUTURE_EPOCH)
    (holds : HoldsUnwithdrawn state epoch index) : HoldsUnwithdrawn after epoch index := by
  intro validator found
  rcases grown with same | ⟨added, pushed, _, far⟩
  · rw [same] at found
    exact holds validator found
  · rw [pushed, Array.getElem?_push] at found
    split at found
    · obtain rfl := Option.some.inj found
      rw [far]
      have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
      omega
    · exact holds validator found

/-- A registry that stays or grows by one has at most one validator more. -/
theorem grown_size {state after : BeaconState preset fork} {deposit : PendingDeposit}
    (grown : after.validators.data = state.validators.data ∨
      ∃ validator, after.validators.data = state.validators.data.push validator ∧
        validator.pubkey = deposit.pubkey ∧ validator.withdrawableEpoch = FAR_FUTURE_EPOCH) :
    after.validators.data.size ≤ state.validators.data.size + 1 := by
  rcases grown with same | ⟨_, pushed, _⟩
  · rw [same]; omega
  · rw [pushed, Array.size_push]

/-- A deposit that credits one position credits a set of positions at most its amount. -/
theorem sum_depositCredit_le (positions : Finset Nat) (target : Option Nat) (amount : Nat) :
    ∑ i ∈ positions, (if target = some i then amount else 0) ≤ amount := by
  cases target with
  | none => simp
  | some j =>
    simp only [Option.some.injEq, Finset.sum_ite_eq]
    split <;> omega

/-- A deposit to a withdrawn validator credits no position that holds a validator not withdrawn.
-/
theorem withdrawn_target_not_mem {state : BeaconState preset fork} {epoch : Epoch}
    {deposit : PendingDeposit} {target : Option Nat}
    (withdrawn : (depositTargetStatus state epoch deposit.pubkey).2 = true)
    (known : ∀ j, state.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some j →
      target = some j)
    {index : Nat} (holds : HoldsUnwithdrawn state epoch.toNat index) :
    target ≠ some index := by
  unfold depositTargetStatus at withdrawn
  split at withdrawn
  · rename_i validator found
    obtain ⟨matching, j, inside, value, before⟩ := Array.find?_eq_some_iff_getElem.mp found
    have index' : state.validators.data.findIdx? (·.pubkey == deposit.pubkey) = some j :=
      Array.findIdx?_eq_some_iff_getElem.mpr
        ⟨inside, value ▸ matching, fun k below => by simpa using before k below⟩
    rw [known j index']
    intro same
    obtain rfl := Option.some.inj same
    have later := holds validator (by rw [Array.getElem?_eq_getElem inside, value])
    simp only [decide_eq_true_eq] at withdrawn
    exact absurd later (Nat.not_le.mpr (UInt64.lt_iff_toNat_lt.mp withdrawn))
  · cases withdrawn

/-- The deposits of a pass credit each position its own amount.

Sum those amounts over positions that hold validators not withdrawn before the next epoch.

That sum is at most what the pass charges to the churn.

That needs one balance for each validator, and room in 64 bits for the new validators. -/
theorem PendingDepositTrace.credits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {state after : BeaconState preset fork} {deposits : List PendingDeposit}
    {postponed : Array PendingDeposit} {charged : Nat}
    (trace : PendingDepositTrace config checks stop nextEpoch state deposits after postponed
      charged) :
    BalancesMatch state → state.validators.data.size + deposits.length < 2 ^ 64 →
    ∃ credits : Nat → Nat,
      (∀ i, balanceNat after i = balanceNat state i + credits i) ∧
      ∀ positions : Finset Nat, (∀ i ∈ positions, HoldsUnwithdrawn state nextEpoch.toNat i) →
        ∑ i ∈ positions, credits i ≤ charged := by
  induction trace with
  | nil state =>
    intro _ _
    exact ⟨fun _ => 0, fun _ => rfl, fun _ _ => by simp⟩
  | exiting _ _ _ _ ih =>
    intro holds room
    simp only [List.length_cons] at room
    exact ih holds (by omega)
  | @withdrawn _ _ _ deposit _ _ _ _ withdrawn applied _ ih =>
    intro holds room
    simp only [List.length_cons] at room
    obtain ⟨target, known, _, grown, ledger⟩ := applyPendingDeposit_ledger applied holds (by omega)
    have size := grown_size grown
    obtain ⟨credits, balances, bound⟩ :=
      ih ((applyPendingDeposit_kept applied).1 holds) (by omega)
    refine ⟨fun i => (if target = some i then deposit.amount.toNat else 0) + credits i, fun i => ?_,
      fun positions inside => ?_⟩
    · rw [balances i, ledger i]
      by_cases here : target = some i
      · simp [depositChanges, here, BalanceChange.apply]; omega
      · simp [depositChanges, here]
    · rw [Finset.sum_add_distrib, Finset.sum_eq_zero fun i member =>
        ite_eq_right (withdrawn_target_not_mem withdrawn known (inside i member))]
      simpa using bound positions fun i member =>
        (inside i member).of_grown nextEpoch.toNat_lt grown
  | @charged _ _ _ deposit _ _ _ _ _ _ applied _ ih =>
    intro holds room
    simp only [List.length_cons] at room
    obtain ⟨target, _, _, grown, ledger⟩ := applyPendingDeposit_ledger applied holds (by omega)
    have size := grown_size grown
    obtain ⟨credits, balances, bound⟩ :=
      ih ((applyPendingDeposit_kept applied).1 holds) (by omega)
    refine ⟨fun i => (if target = some i then deposit.amount.toNat else 0) + credits i, fun i => ?_,
      fun positions inside => ?_⟩
    · rw [balances i, ledger i]
      by_cases here : target = some i
      · simp [depositChanges, here, BalanceChange.apply]; omega
      · simp [depositChanges, here]
    · rw [Finset.sum_add_distrib]
      have := bound positions fun i member => (inside i member).of_grown nextEpoch.toNat_lt grown
      have := sum_depositCredit_le positions target deposit.amount.toNat
      omega

/-- From Electra, the pending deposits of an epoch credit each position its own amount.

Sum those amounts over positions that hold validators not withdrawn before the next epoch.

That sum is at most the balance that the pass charges to the churn.

That needs one balance for each validator, and room in 64 bits for the new validators. -/
theorem processPendingDeposits_credits {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ credits : Nat → Nat,
      (∀ i, balanceNat after i = balanceNat state i + credits i) ∧
      ∀ positions : Finset Nat,
        (∀ i ∈ positions, HoldsUnwithdrawn state ((getCurrentEpoch state).toNat + 1) i) →
          ∑ i ∈ positions, credits i ≤ depositsProcessed config checks state electra := by
  obtain ⟨nextEpoch, churn, available, finalizedSlot, pass, consumed, delayed, next, limit,
    added, finalized, passed, _, length, trace, _, _, _, balances, _, _⟩ :=
    processPendingDeposits_spec computed
  obtain ⟨credits, credited, bound⟩ := trace.credits holds (by omega)
  have processed : depositsProcessed config checks state electra = pass.1.processed.toNat := by
    unfold depositsProcessed
    rw [liftAccessor_ok.mpr next, liftAccessor_ok.mpr limit]
    simp only [bind, Except.bind, liftAccessor_ok.mpr added, liftAccessor_ok.mpr finalized, passed,
      pure, Except.pure]
  have epoch : nextEpoch.toNat = (getCurrentEpoch state).toNat + 1 := by
    rw [(addChecked_ok_iff.mp (mapError_ok_iff.mp next)).2]
    rfl
  refine ⟨credits, fun i => ?_, fun positions inside => ?_⟩
  · rw [← credited i]
    simp [balanceNat, balances]
  · rw [processed]
    exact bound positions fun i member => epoch ▸ inside i member

/-! ## New validators -/

/-- Each validator at or past a position has an effective balance at most its balance. -/
def NewCapped (start : Nat) (state : BeaconState preset fork) : Prop :=
  ∀ i, start ≤ i → ∀ validator, state.validators.data[i]? = some validator →
    validator.effectiveBalance.toNat ≤ balanceNat state i

/-- A deposit keeps each new validator at most its balance.

It raises a balance, or adds a validator with an effective balance at most its first deposit. -/
theorem applyPendingDeposit_newCapped {state after : BeaconState preset fork}
    {deposit : PendingDeposit} {start : Nat}
    (computed : applyPendingDeposit config checks state deposit = .ok after)
    (holds : BalancesMatch state) (small : state.validators.data.size < 2 ^ 64)
    (capped : NewCapped start state) : NewCapped start after := by
  have original := computed
  obtain ⟨target, _, _, _, ledger⟩ := applyPendingDeposit_ledger computed holds small
  have raised : ∀ i, balanceNat state i ≤ balanceNat after i := by
    intro i
    rw [ledger i]
    unfold depositChanges
    split <;> simp [BalanceChange.apply]
  cases known : state.validators.data.findIdx? (·.pubkey == deposit.pubkey) with
  | some j =>
    have registry : after.validators = state.validators := by
      simp only [applyPendingDeposit, known, liftAccessor_ok] at computed
      exact increaseBalance_validators computed
    intro i above validator found
    rw [registry] at found
    exact Nat.le_trans (capped i above validator found) (raised i)
  | none =>
    unfold applyPendingDeposit at computed
    rw [known] at computed
    dsimp only at computed
    split at computed
    · cases computed
      exact capped
    rename_i notBls
    simp only [bind_ok_iff] at computed
    obtain ⟨valid, validOk, computed⟩ := computed
    cases valid with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact capped
    | true =>
      obtain ⟨validators, balances⟩ :=
        applyPendingDeposit_new_valid known notBls validOk original holds small
      have sizes : state.balances.data.size = state.validators.data.size := holds
      intro i above validator found
      rw [validators, Array.getElem?_push] at found
      split at found
      · rename_i same
        subst same
        obtain rfl := Option.some.inj found
        have : balanceNat after state.validators.data.size = deposit.amount.toNat := by
          simp only [balanceNat, balances, Array.getElem?_push, ← sizes, ↓reduceIte,
            Option.map_some, Option.getD_some]
        rw [this]
        exact getValidatorFromDeposit_le_amount
      · exact Nat.le_trans (capped i above validator found) (raised i)

/-- Deposits in turn keep each new validator at most its balance. -/
theorem foldlM_applyPendingDeposit_newCapped {start : Nat} :
    ∀ {deposits : List PendingDeposit} {state after : BeaconState preset fork},
      deposits.foldlM (applyPendingDeposit config checks) state = .ok after →
      BalancesMatch state → state.validators.data.size + deposits.length < 2 ^ 64 →
      NewCapped start state → NewCapped start after
  | [], state, after, computed, _, _, capped => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ capped
  | deposit :: rest, state, after, computed, holds, room, capped => by
    simp only [List.length_cons] at room
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, stepped, folded⟩ := computed
    obtain ⟨_, _, _, grown, _⟩ := applyPendingDeposit_ledger stepped holds (by omega)
    have size := grown_size grown
    exact foldlM_applyPendingDeposit_newCapped folded ((applyPendingDeposit_kept stepped).1 holds)
      (by omega) (applyPendingDeposit_newCapped stepped holds (by omega) capped)

/-- From Electra, the pending deposits of an epoch leave each new validator at most its balance.

That needs one balance for each validator, and room in 64 bits for the new validators. -/
theorem processPendingDeposits_newCapped {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    NewCapped state.validators.data.size after := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, length, inRead, _,
    perm, folded, rfl⟩ := processPendingDeposits_applied computed
  have capped := foldlM_applyPendingDeposit_newCapped folded holds
    (by have := inRead.length_le; omega) (start := state.validators.data.size)
    (fun i above validator found => by
      rw [Array.getElem?_eq_none above] at found
      cases found)
  exact capped

/-! ## One slot -/

/-- The deposit balance that a slot credits at a position, from Electra.

It is zero unless the slot is the last of its epoch.

The pass runs on the state after the steps of the epoch that come before the pending deposits.

Those are recomputed here from the state at the start of the slot, as in `depositsChargedAt`. -/
def depositCreditsAt (config : Config) (checks : SignatureChecks)
    (state : BeaconState preset fork) (index : Nat) : Nat :=
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
      | .ok reset =>
        match processPendingDeposits config checks reset electra with
        | .ok deposited => balanceNat deposited index - balanceNat reset index
        | .error _ => 0
      | .error _ => 0
    else 0
  else 0

/-- One slot from Electra credits deposits to validators that stay, within the churn it charges.

After the slot, each validator at those positions must not exit before the current epoch.

The deposits that the slot credits to those positions sum to at most the balance it charges.

That needs the invariant before the slot, and room in 64 bits for the new validators. -/
theorem advanceSlot_depositCredits {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} (computed : advanceSlot config checks state = .ok after)
    (holds : Invariant state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64)
    (small : after.validators.data.size < 2 ^ 64) (positions : Finset Nat)
    (staying : ∀ i ∈ positions, ∀ validator, after.validators.data[i]? = some validator →
      (getCurrentEpoch after).toNat ≤ validator.exitEpoch.toNat) :
    ∑ i ∈ positions, depositCreditsAt config checks state i ≤
      depositsChargedAt config checks state := by
  have epochAfter := advanceSlot_epoch computed
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
  have cachedSizes : SameSizes state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl⟩
  have cachedHolds : Invariant cached := (frame_processSlot cachedOk).invariant holds
  unfold epochIfLast at epochedOk
  rw [nextIs] at epochedOk
  split at epochedOk
  · rename_i last
    simp only [last, ↓reduceIte] at epochAfter
    unfold processEpoch at epochedOk
    split at epochedOk
    · rename_i altair
      unfold processEpochAltair at epochedOk
      simp only [bind_ok_iff] at epochedOk
      obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
        registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk,
        balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := epochedOk
      -- Up to the pending deposits, the steps keep the registry, its size and the invariant.
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
      have resetSizes : SameSizes state reset := by
        have upTo := cachedSizes.trans <|
          (sameSizes_processJustificationAndFinalization justifiedOk).trans <|
          (sameSizes_processInactivityUpdates scoredOk).trans <|
          (processRewardsAndPenalties_sameSizes rewardedOk).trans <|
          (sameSizes_processRegistryUpdates registeredOk).trans
            (sameSizes_processSlashings slashedOk)
        split at resetOk
        · exact upTo.trans (sameSizes_processEth1DataReset resetOk)
        · cases resetOk
          exact upTo
      obtain ⟨_, _, _, _, validators, balances⟩ :=
        processJustificationAndFinalization_invariant cachedHolds.ordered cachedHolds.settled
          justifiedOk
      have resetFrame : Frame justified reset := by
        have upTo := (frame_processInactivityUpdates scoredOk).trans <|
          (frame_processRewardsAndPenalties rewardedOk).trans <|
          (frame_processRegistryUpdates registeredOk).trans (frame_processSlashings slashedOk)
        split at resetOk
        · exact upTo.trans (frame_processEth1DataReset resetOk)
        · cases resetOk
          exact upTo
      have resetMatch : BalancesMatch reset := resetFrame.balancesMatch (by
        have := cachedHolds.balancesMatch
        unfold BalancesMatch at this ⊢
        rw [validators, balances]
        exact this)
      have resetOrdered : ExitsOrdered reset := resetFrame.exitsOrdered (by
        have := cachedHolds.exitsOrdered
        unfold ExitsOrdered at this ⊢
        rw [validators]
        exact this)
      -- From the pending deposits on, the steps start no exit.
      have paidQuiet : QuietStep pending paid := by
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
      have tail : QuietStep mixed epoched := by
        split at computed <;> simp only [bind_ok_iff] at computed <;>
          obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
        · have rootedQuiet : QuietStep mixed rooted := by
            unfold processHistoricalSummariesUpdate at rootedOk
            simp only [bind, Except.bind, pure, Except.pure] at rootedOk
            repeat' (split at rootedOk <;> try cases rootedOk)
            all_goals first
              | exact .refl _
              | exact .of_eq rfl
          exact rootedQuiet.trans (quietStep_epochEnd syncedOk lookedOk windowed)
        · exact (quietStep_processHistoricalRootsUpdate rootedOk).trans
            (quietStep_epochEnd syncedOk lookedOk windowed)
      have quiet := middleQuiet.trans tail
      -- The pass is the one that `depositCreditsAt` and `depositsChargedAt` recompute.
      unfold processPendingBalances at pendingOk
      simp only [electra, ↓reduceDIte, bind_ok_iff] at pendingOk
      obtain ⟨deposited, depositedOk, _⟩ := pendingOk
      have creditsIs : ∀ i, depositCreditsAt config checks state i =
          balanceNat deposited i - balanceNat reset i := by
        intro i
        simp only [depositCreditsAt, last, electra, ↓reduceIte, ↓reduceDIte]
        simp only [bind, Except.bind, cachedOk, justifiedOk, scoredOk, rewardedOk, registeredOk,
          slashedOk, resetOk, depositedOk]
      have chargedIs : depositsChargedAt config checks state =
          depositsProcessed config checks reset electra := by
        simp only [depositsChargedAt, last, electra, ↓reduceIte, ↓reduceDIte]
        simp only [bind, Except.bind, cachedOk, justifiedOk, scoredOk, rewardedOk, registeredOk,
          slashedOk, resetOk]
      obtain ⟨credits, credited, bound⟩ := processPendingDeposits_credits depositedOk resetMatch
        (by rw [resetSizes.1]; exact room)
      have resetEpoch : getCurrentEpoch reset = getCurrentEpoch state := by
        simp only [getCurrentEpoch, charged.frozen.slot]
      rw [chargedIs]
      refine Nat.le_trans (Finset.sum_le_sum fun i _ => ?_) (bound positions fun i member => ?_)
      · rw [creditsIs i, credited i]
        omega
      · -- The validator at the position stays at least until the next epoch.
        intro validator found
        obtain ⟨later, laterFound, exit⟩ := quiet.exits (by simpa using small) i validator found
        have stays := staying i member later (by simpa using laterFound)
        have ordered := resetOrdered validator (Array.mem_of_getElem? found)
        rw [resetEpoch]
        have := UInt64.le_iff_toNat_le.mp ordered
        rw [exit] at stays
        omega
    · rename_i notAltair
      exact absurd (Nat.le_trans (by decide) electra) notAltair
  · rename_i notLast
    simp [depositCreditsAt, notLast]

/-- One slot from Electra adds validators only in its pass over the pending deposits.

Each has an effective balance at most the deposits the slot credits it, or its balance after.

That needs one balance for each validator, and room in 64 bits for the new validators. -/
theorem advanceSlot_newEffective {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} (computed : advanceSlot config checks state = .ok after)
    (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64)
    (small : after.validators.data.size < 2 ^ 64) {i : Nat}
    (above : state.validators.data.size ≤ i) {validator : Validator}
    (found : after.validators.data[i]? = some validator) :
    validator.effectiveBalance.toNat ≤
      max (depositCreditsAt config checks state i) (balanceAt after i) := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, nextValue⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have nextIs : next = state.slot + 1 := by
    apply UInt64.toNat_inj.mp
    rw [nextValue, UInt64.toNat_add]
    have : (1 : UInt64).toNat = 1 := rfl
    omega
  have cachedSizes : SameSizes state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact ⟨rfl, rfl⟩
  have cachedValidators : cached.validators.data = state.validators.data := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    rfl
  change epoched.validators.data[i]? = some validator at found
  change _ ≤ max _ (balanceAt epoched i)
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
      have resetSizes : SameSizes state reset := by
        have upTo := cachedSizes.trans <|
          (sameSizes_processJustificationAndFinalization justifiedOk).trans <|
          (sameSizes_processInactivityUpdates scoredOk).trans <|
          (processRewardsAndPenalties_sameSizes rewardedOk).trans <|
          (sameSizes_processRegistryUpdates registeredOk).trans
            (sameSizes_processSlashings slashedOk)
        split at resetOk
        · exact upTo.trans (sameSizes_processEth1DataReset resetOk)
        · cases resetOk
          exact upTo
      have resetMatch : BalancesMatch reset := balancesMatch_of_sameSizes resetSizes holds
      have paidUntouched : Untouched pending paid := by
        split at paidOk
        · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure,
            Except.pure, Except.ok.injEq] at paidOk
          obtain ⟨_, _, rfl⟩ := paidOk
          exact ⟨rfl, rfl⟩
        · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
          exact paidOk ▸ ⟨rfl, rfl⟩
      have clearedUntouched : Untouched balanced cleared := by
        obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
        exact ⟨rfl, rfl⟩
      have mixedUntouched : Untouched cleared mixed := by
        obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
        exact ⟨rfl, rfl⟩
      have suffix : Untouched balanced epoched := by
        split at computed <;> simp only [bind_ok_iff] at computed <;>
          obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
        · have rootedUntouched : Untouched mixed rooted := by
            unfold processHistoricalSummariesUpdate at rootedOk
            simp only [bind, Except.bind, pure, Except.pure] at rootedOk
            repeat' (split at rootedOk <;> try cases rootedOk)
            all_goals exact ⟨rfl, rfl⟩
          exact clearedUntouched.trans <| mixedUntouched.trans <| rootedUntouched.trans
            (untouched_epochEnd syncedOk lookedOk windowed)
        · exact clearedUntouched.trans <| mixedUntouched.trans <|
            (untouched_processHistoricalRootsUpdate rootedOk).trans
              (untouched_epochEnd syncedOk lookedOk windowed)
      -- The pass is the one that `depositCreditsAt` recomputes.
      unfold processPendingBalances at pendingOk
      simp only [electra, ↓reduceDIte, bind_ok_iff] at pendingOk
      obtain ⟨deposited, depositedOk, consolidatedOk⟩ := pendingOk
      have creditsIs : depositCreditsAt config checks state i =
          balanceNat deposited i - balanceNat reset i := by
        simp only [depositCreditsAt, last, electra, ↓reduceIte, ↓reduceDIte]
        simp only [bind, Except.bind, cachedOk, justifiedOk, scoredOk, rewardedOk, registeredOk,
          slashedOk, resetOk, depositedOk]
      have consolidated : EffectiveCapped deposited pending ∧
          pending.validators.data = deposited.validators.data := by
        unfold processPendingConsolidations at consolidatedOk
        simp only [bind, Except.bind, pure, Except.pure] at consolidatedOk
        repeat' (split at consolidatedOk <;> try cases consolidatedOk)
        all_goals exact ⟨(effectiveCapped_passPendingConsolidations ‹_›).trans (.of_data rfl),
          by simp [passPendingConsolidations_validators ‹_›]⟩
      have prefixHeld : EffectiveCapped deposited paid :=
        consolidated.1.trans (.of_data paidUntouched.1)
      have ceiling := ceiling_of_update prefixHeld balancedOk suffix
      -- The registry keeps its size from the pass to the end of the epoch.
      have sizes : epoched.validators.data.size = deposited.validators.data.size := by
        rw [suffix.1, (sameSizes_processEffectiveBalanceUpdates balancedOk).1, paidUntouched.1,
          consolidated.2]
      have inside : i < deposited.validators.data.size := by
        rw [← sizes]
        exact (Array.getElem?_eq_some_iff.mp found).1
      obtain ⟨later, laterFound, bound⟩ := ceiling small i deposited.validators.data[i]
        (Array.getElem?_eq_getElem inside)
      obtain rfl := Option.some.inj (laterFound.symm.trans found)
      have capped := processPendingDeposits_newCapped depositedOk resetMatch
        (by rw [resetSizes.1]; exact room) i (by rw [resetSizes.1]; exact above) _
        (Array.getElem?_eq_getElem inside)
      have resetZero : balanceNat reset i = 0 := by
        have sizes' : reset.balances.data.size ≤ i := by
          have match' : state.balances.data.size = state.validators.data.size := holds
          rw [resetSizes.2]; omega
        simp [balanceNat, Array.getElem?_eq_none sizes']
      rw [creditsIs, resetZero, Nat.sub_zero]
      exact Nat.le_trans bound (by simp only [balanceAt] at capped ⊢; omega)
    · rename_i notAltair
      exact absurd (Nat.le_trans (by decide) electra) notAltair
  · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    rw [cachedValidators, Array.getElem?_eq_none above] at found
    cases found

/-! ## Runs -/

/-- The deposit balance that one step credits at a position: only a slot step may. -/
def Step.depositCredits {before after : ForkedBeaconState preset}
    (step : Step config checks before after) (index : Nat) : Nat :=
  match step with
  | .slot (state := current) _ _ => depositCreditsAt config checks current index
  | .upgrade _ _ => 0
  | .block _ _ _ _ _ => 0

/-- The deposit balance that the epoch transitions of a run credit at a position. -/
def Run.depositCredits {start : ForkedBeaconState preset} (index : Nat) :
    {after : ForkedBeaconState preset} → Run config checks start after → Nat
  | _, .nil => 0
  | _, .snoc run step => run.depositCredits index + step.depositCredits index

/-- What a run credits a balance beyond the deposits of its epoch transitions.

Each step counts its rise less the deposits it credits, or zero.

For a validator that the run adds, it is what the validator gains after its deposits.

It counts rewards, rewards of blocks and of reports, and balances received by consolidation. -/
def Run.gainsAfterDeposit {start : ForkedBeaconState preset} (index : Nat) :
    {after : ForkedBeaconState preset} → Run config checks start after → Nat
  | _, .nil => 0
  | after, .snoc (middle := middle) run step =>
    run.gainsAfterDeposit index +
      ((balanceAt after.state index - balanceAt middle.state index) - step.depositCredits index)

/-- What a run credits a balance is at most its deposits, plus what it gains after them. -/
theorem Run.credited_le {start : ForkedBeaconState preset} (index : Nat) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      run.credited index ≤ run.depositCredits index + run.gainsAfterDeposit index
  | _, .nil => by simp [Run.credited, Run.depositCredits, Run.gainsAfterDeposit]
  | _, .snoc run step => by
    have := Run.credited_le index run
    simp only [Run.credited, Run.depositCredits, Run.gainsAfterDeposit]
    omega

/-- The epoch does not decrease over one step from Electra on. -/
theorem Step.epoch_le {before after : ForkedBeaconState preset}
    (electra : .pectra ≤ before.fork) (step : Step config checks before after) :
    (getCurrentEpoch before.state).toNat ≤ (getCurrentEpoch after.state).toNat := by
  have := Run.epochTransitions_eq electra (.snoc .nil step)
  omega

/-- A validator that does not exit before an epoch did not exit before an earlier one either.

An exit epoch, once set, stays, and an unset one is the largest epoch. -/
theorem exitEpoch_ge_of_lifecycle {validator later : Validator} {epoch epoch' : Nat}
    (lifecycle : ValidatorLifecycle validator later) (le : epoch ≤ epoch')
    (bounded : epoch < 2 ^ 64) (stays : epoch' ≤ later.exitEpoch.toNat) :
    epoch ≤ validator.exitEpoch.toNat := by
  by_cases set : validator.exitEpoch = FAR_FUTURE_EPOCH
  · rw [set]
    have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    omega
  · rw [← lifecycle.exitEpoch set]
    omega

/-- A run from Electra on credits deposits to validators that stay, within the churn it charges.

At the end, each validator at the positions must not exit before the current epoch.

A position may be new, and a deposit that creates its validator takes from the churn.

Then it was not withdrawn at any pass of the run, so each deposit to it took from the churn.

A deposit to a withdrawn validator takes nothing from the churn, so such validators are left out.

The start must be reachable.

Each state of the run must have room in 64 bits for the new validators of the pending deposits.

It also needs a registry of fewer than `2^64` validators at the end, which holds before Gloas. -/
theorem Run.depositCredits_le {start : ForkedBeaconState preset}
    (electra : .pectra ≤ start.fork) (reachable : Reachable config checks start) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      after.state.validators.data.size < 2 ^ 64 →
      (∀ state ∈ run.states,
        state.state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) →
      ∀ positions : Finset Nat,
      (∀ i ∈ positions, ∀ validator, after.state.validators.data[i]? = some validator →
        (getCurrentEpoch after.state).toNat ≤ validator.exitEpoch.toNat) →
      ∑ i ∈ positions, run.depositCredits i ≤ run.depositsCharged
  | _, .nil, _, _, positions, _ => by simp [Run.depositCredits, Run.depositsCharged]
  | after, .snoc (middle := middle) run step, small, room, positions, staying => by
    have lifecycle := stepRelation_registryLifecycle.step step
    have middleSmall := Nat.lt_of_le_of_lt lifecycle.size_le small
    have electraMiddle : .pectra ≤ middle.fork := Nat.le_trans electra (Run.fork_le run)
    have epochs := step.epoch_le electraMiddle
    -- Each validator that stays at the end stayed at the end of the run before the step.
    have stayedBefore : ∀ i ∈ positions, ∀ validator,
        middle.state.validators.data[i]? = some validator →
          (getCurrentEpoch middle.state).toNat ≤ validator.exitEpoch.toNat := by
      intro i member validator found
      obtain ⟨later, laterFound, kept⟩ := lifecycle.validators small i validator found
      exact exitEpoch_ge_of_lifecycle kept epochs (getCurrentEpoch middle.state).toNat_lt
        (staying i member later laterFound)
    have earlier := Run.depositCredits_le electra reachable run middleSmall
      (fun state member => room state (List.mem_append_left _ member)) positions stayedBefore
    have here : ∑ i ∈ positions, step.depositCredits i ≤ step.depositsCharged := by
      cases step with
      | slot _ computed =>
        exact advanceSlot_depositCredits (electra := electraMiddle) computed
          (Reachable.invariant (reachable.reaches ⟨run⟩))
          (room _ (List.mem_append_left _ (Run.end_mem_states run))) small positions staying
      | upgrade _ _ => simp [Step.depositCredits, Step.depositsCharged]
      | block _ _ _ _ _ => simp [Step.depositCredits, Step.depositsCharged]
    simp only [Run.depositCredits, Run.depositsCharged, Finset.sum_add_distrib]
    omega

/-- One step from Electra adds validators only by deposits.

A pass over the pending deposits adds them, or a block adds them with no effective balance.

Each has an effective balance at most the deposits the step credits it, or its balance after.

That needs one balance for each validator, and room in 64 bits for the new validators. -/
theorem Step.newEffective {before after : ForkedBeaconState preset}
    (step : Step config checks before after) (electra : .pectra ≤ before.fork)
    (holds : BalancesMatch before.state)
    (room : before.state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat <
      2 ^ 64)
    (small : after.state.validators.data.size < 2 ^ 64) {i : Nat}
    (above : before.state.validators.data.size ≤ i) {validator : Validator}
    (found : after.state.validators.data[i]? = some validator) :
    validator.effectiveBalance.toNat ≤ max (step.depositCredits i) (balanceAt after.state i) := by
  cases step with
  | slot _ computed =>
    exact advanceSlot_newEffective (electra := electra) computed holds room small above found
  | block _ _ _ _ computed =>
    have fresh := (chargedStep_processBlock (capExit := 0) (capConsolidation := 0) (largest := 0)
      (electra := electra) (applySignedBlock_ok computed).2.1).frozen.fresh small i validator
      above found
    simp [fresh]
  | upgrade _ computed =>
    rw [(upgradeNext_keeps electra computed).1, Array.getElem?_eq_none above] at found
    cases found

/-- A run from Electra on bounds the effective balance of each validator that it adds.

The bound is its deposits, plus what it gains after them.

Its balance at the end is at most that bound too.

The start must be reachable.

Each state of the run must have room in 64 bits for the new validators of the pending deposits.

It also needs a registry of fewer than `2^64` validators at the end, which holds before Gloas. -/
theorem Run.effectiveAt_new_le {start : ForkedBeaconState preset}
    (electra : .pectra ≤ start.fork) (reachable : Reachable config checks start) (index : Nat)
    (above : start.state.validators.data.size ≤ index) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      after.state.validators.data.size < 2 ^ 64 →
      (∀ state ∈ run.states,
        state.state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) →
      effectiveAt after.state index ≤ run.depositCredits index + run.gainsAfterDeposit index ∧
        balanceAt after.state index ≤ run.depositCredits index + run.gainsAfterDeposit index
  | _, .nil, _, _ => by
    have sizes : start.state.balances.data.size = start.state.validators.data.size :=
      reachable.invariant.balancesMatch
    simp [effectiveAt, balanceAt, Array.getElem?_eq_none above,
      Array.getElem?_eq_none (sizes ▸ above : start.state.balances.data.size ≤ index)]
  | after, .snoc (middle := middle) run step, small, room => by
    have lifecycle := stepRelation_registryLifecycle.step step
    have middleSmall := Nat.lt_of_le_of_lt lifecycle.size_le small
    have electraMiddle : .pectra ≤ middle.fork := Nat.le_trans electra (Run.fork_le run)
    have middleHolds := (Reachable.invariant (reachable.reaches ⟨run⟩)).balancesMatch
    have middleRoom := room middle (List.mem_append_left _ (Run.end_mem_states run))
    obtain ⟨effective, balance⟩ := Run.effectiveAt_new_le electra reachable index above run
      middleSmall fun state member => room state (List.mem_append_left _ member)
    simp only [Run.depositCredits, Run.gainsAfterDeposit]
    refine ⟨?_, by omega⟩
    cases middleFound : middle.state.validators.data[index]? with
    | some earlier =>
      obtain ⟨later, laterFound, bound⟩ := step.ceilingStep small index earlier middleFound
      have earlierEffective : earlier.effectiveBalance.toNat ≤ effectiveAt middle.state index := by
        simp [effectiveAt, middleFound]
      simp only [effectiveAt, laterFound, Option.map_some, Option.getD_some]
      omega
    | none =>
      have outside : middle.state.validators.data.size ≤ index := by
        by_contra inside
        rw [Array.getElem?_eq_getElem (Nat.lt_of_not_le inside)] at middleFound
        cases middleFound
      cases laterFound : after.state.validators.data[index]? with
      | none => simp [effectiveAt, laterFound]
      | some later =>
        have bound := step.newEffective electraMiddle middleHolds middleRoom small outside
          laterFound
        simp only [effectiveAt, laterFound, Option.map_some, Option.getD_some]
        omega

end EthLib.Consensus
