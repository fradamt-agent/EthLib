module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import EthLib.Consensus.Proofs.Containers.State
public import EthLib.Consensus.Proofs.Transition.BlockLedger
public import EthLib.Consensus.Proofs.Transition.ChurnWindows
public import EthLib.Consensus.Proofs.Transition.EffectiveBalanceCeiling

/-!
# Proofs: what a balance can gain or lose along a run

What a run credits a balance sums, step by step, how much the step raised it.

What a run debits a balance sums, step by step, how much the step lowered it.

Every balance of the run is at most the balance at the start plus what the run credits.

It is at least the balance at the start less what the run debits.

Each step has a ledger, at every fork, which bounds both.

An upgrade keeps the balances, except the upgrade to Electra, which moves some to the deposits.

An effective balance at the end of a run is bounded by the values at its start.

It is at most the larger of the effective balance and the balance, plus what the run credits.

Before Gloas the registry is within its limit by its type, and from Gloas that is a premise.

The room in 64 bits for the new validators of the pending deposits is a premise at every fork.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- `balanceAt` is the balance that ledgers read. -/
theorem balanceAt_eq_balanceNat {fork : Base.Fork} (state : BeaconState preset fork)
    (index : Nat) : balanceAt state index = balanceNat state index := rfl

/-! ## The ledger of each kind of step -/

/-- The epoch at the end of a slot, if it is due, has a ledger.

From Altair it needs the registry within its limit and one balance for each validator.

It also needs room in 64 bits for the new validators of the pending deposits. -/
theorem epochIfLast_ledger {fork : Base.Fork} {state after : BeaconState preset fork}
    {next : Slot} (computed : epochIfLast config checks next state = .ok after)
    (within : state.RegistryWithinLimit) (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ changes, BalanceLedger state after changes := by
  unfold epochIfLast at computed
  split at computed
  · by_cases altair : .altair ≤ fork
    · unfold processEpoch at computed
      simp only [altair, ↓reduceDIte] at computed
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, ledger⟩ :=
        processEpochAltair_ledger within holds room computed
      exact ⟨_, ledger⟩
    · obtain ⟨_, _, _, _, _, _, _, ledger⟩ :=
        processEpoch_ledger_of_lt_altair (Nat.lt_of_not_le altair) computed
      exact ⟨_, ledger⟩
  · cases computed
    exact ⟨_, BalanceLedger.refl state⟩

/-- A slot has a ledger: that of its epoch, if the slot ends one.

The premises are those of `epochIfLast_ledger`. -/
theorem advanceSlot_ledger {fork : Base.Fork} {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after)
    (within : state.RegistryWithinLimit) (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ changes, BalanceLedger state after changes := by
  simp only [advanceSlot, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
  obtain ⟨changes, ledger⟩ := epochIfLast_ledger epochedOk within holds room
  exact ⟨changes, fun i => ledger i⟩

/-! ## The passes of rewards and penalties -/

/-- The passes of deltas debit a balance the sum of their penalties at its position.

So each pass, such as that of inactivity, has its own part of the debit. -/
theorem debited_deltaChanges (deltas : List (Array Gwei × Array Gwei)) (i : Nat) :
    BalanceChange.debited .rewards (deltaChanges deltas i) =
      (deltas.map fun delta => (delta.2.getD i 0).toNat).sum := by
  induction deltas with
  | nil => simp [deltaChanges, BalanceChange.debited]
  | cons delta rest step =>
    simp [deltaChanges, BalanceChange.debited] at step ⊢
    omega

/-- The passes of deltas credit a balance the sum of their rewards at its position. -/
theorem credited_deltaChanges (deltas : List (Array Gwei × Array Gwei)) (i : Nat) :
    BalanceChange.credited .rewards (deltaChanges deltas i) =
      (deltas.map fun delta => (delta.1.getD i 0).toNat).sum := by
  induction deltas with
  | nil => simp [deltaChanges, BalanceChange.credited]
  | cons delta rest step =>
    simp [deltaChanges, BalanceChange.credited] at step ⊢
    omega

/-! ## The upgrade to Electra -/

/-- A debit of a balance moved back to the pending deposits. -/
def IsQueuedDebit : BalanceChange → Prop
  | .credit _ _ => False
  | .debit flow _ => flow = .excessQueued

theorem isQueuedDebit_excessChanges {index : ValidatorIndex} {excess i : Nat} :
    ∀ change ∈ excessChanges index excess i, IsQueuedDebit change := by
  intro change member
  unfold excessChanges at member
  split at member
  · rw [List.mem_singleton.mp member]
    rfl
  · exact absurd member List.not_mem_nil

/-- From Electra, queuing a validator not yet active moves its whole balance to the deposits. -/
theorem queuePreActivation_ledgerOf {fork : Base.Fork} {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : ValidatorIndex}
    (computed : queuePreActivation state electra index = .ok after) :
    LedgerOf IsQueuedDebit state after := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, -, balance, balanceOk, _, -, middle, set₁, cleared, set₂, rfl⟩ := computed
  have kept := setValidator_balances set₂
  obtain ⟨inside, rfl⟩ := setBalance_ok set₁
  have read : state.balances.data[index.toNat]? = some balance := by
    unfold getBalance at balanceOk
    split at balanceOk
    · rename_i found
      cases balanceOk
      exact found
    · cases balanceOk
  refine ⟨excessChanges index balance.toNat, fun i => ?_, fun _ => isQueuedDebit_excessChanges⟩
  change balanceNat cleared i = _
  unfold balanceNat excessChanges
  rw [kept]
  by_cases here : index.toNat = i
  · subst here
    rw [Array.getElem?_eq_getElem inside] at read
    simp [BeaconState.putBalance, inside, read, BalanceChange.apply]
  · simp [BeaconState.putBalance, here]

/-- From Electra, queuing the excess of a compounding validator moves it to the deposits. -/
theorem queueCompoundingExcess_ledgerOf {fork : Base.Fork} {state after : BeaconState preset fork}
    {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    LedgerOf IsQueuedDebit state after := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · obtain ⟨_, _, _, ledger⟩ := queueExcessActiveBalance_ledger (liftAccessor_ok.mp computed)
      exact ⟨_, ledger, fun _ => isQueuedDebit_excessChanges⟩
    · cases computed
      exact LedgerOf.of_balances rfl
  · cases computed
    exact LedgerOf.of_balances rfl

/-- The upgrade to Electra moves balances only to the pending deposits.

A validator not yet active moves its whole balance there.

A compounding validator moves its balance above the activation balance there. -/
theorem upgradeToElectra_ledgerOf {pre : BeaconState preset .dencun}
    {after : BeaconState preset .pectra} (computed : upgradeToElectra config pre = .ok after) :
    ∃ changes : Nat → List BalanceChange,
      (∀ i, balanceNat after i = (changes i).foldl BalanceChange.apply (balanceNat pre i)) ∧
        ∀ i, ∀ change ∈ changes i, IsQueuedDebit change := by
  simp only [upgradeToElectra, bind_ok_iff] at computed
  obtain ⟨_, -, _, -, _, -, _, -, middle, queued, compounded⟩ := computed
  obtain ⟨changes, ledger, allowed⟩ :=
    (LedgerOf.foldlM (fun _ _ _ step => queuePreActivation_ledgerOf step) queued).trans
      (LedgerOf.foldlM (fun _ _ _ step => queueCompoundingExcess_ledgerOf step) compounded)
  exact ⟨changes, fun i => ledger i, allowed⟩

/-! ## The ledger of each step, at every fork -/

/-- What a state needs for the ledger of a step from it.

It needs the registry within its limit and one balance for each validator.

It also needs room in 64 bits for the new validators of the pending deposits. -/
structure LedgerReady (forked : ForkedBeaconState preset) : Prop where
  within : forked.state.RegistryWithinLimit
  holds : BalancesMatch forked.state
  room : forked.state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64

/-- A reachable state is ready for a ledger before Gloas, given the room for new validators.

The type of the registry bounds it before Gloas.

Every reachable state has one balance for each validator. -/
theorem LedgerReady.of_reachable {forked : ForkedBeaconState preset}
    (reachable : Reachable config checks forked) (before : forked.fork < .glamsterdam)
    (room : forked.state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat <
      2 ^ 64) : LedgerReady forked :=
  ⟨forked.state.registryWithinLimit_of_lt before, reachable.invariant.balancesMatch, room⟩

/-- A reachable state is ready for a ledger, given a registry within its limit and the room.

From Gloas no invariant bounds the registry, so its limit is a premise. -/
theorem LedgerReady.of_reachable_of_within {forked : ForkedBeaconState preset}
    (reachable : Reachable config checks forked) (within : forked.state.RegistryWithinLimit)
    (room : forked.state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat <
      2 ^ 64) : LedgerReady forked :=
  ⟨within, reachable.invariant.balancesMatch, room⟩

/-- Every step has a ledger, at every fork, from a state ready for one.

A slot has the ledger of its epoch, if it ends one, and a block the ledger of a block.

An upgrade keeps the balances, except the upgrade to Electra.

That upgrade only moves balances to the pending deposits. -/
theorem Step.ledger {pre post : ForkedBeaconState preset} (step : Step config checks pre post)
    (ready : LedgerReady pre) :
    ∃ changes : Nat → List BalanceChange, ∀ i,
      balanceAt post.state i = (changes i).foldl BalanceChange.apply (balanceAt pre.state i) := by
  cases step with
  | slot _ computed =>
    obtain ⟨changes, ledger⟩ := advanceSlot_ledger computed ready.within ready.holds ready.room
    exact ⟨changes, ledger⟩
  | block _ _ _ _ computed =>
    obtain ⟨_, _, _, _, _, _, _, ledger, _⟩ :=
      processBlock_ledger (applySignedBlock_ok computed).2.1 ready.holds
    exact ⟨_, ledger⟩
  | upgrade due computed =>
    rename_i upgraded
    obtain ⟨fork, state⟩ := pre
    -- Each upgrade but that to Electra keeps the balances.
    suffices kept : upgraded.val.state.balances.data = state.balances.data ∨
        ∃ changes : Nat → List BalanceChange, ∀ i, balanceAt upgraded.val.state i =
          (changes i).foldl BalanceChange.apply (balanceAt state i) by
      rcases kept with same | found
      · exact ⟨fun _ => [], fun i => by simp [balanceAt, same]⟩
      · exact found
    cases fork <;>
      simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
        throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
    · obtain ⟨_, upgradedOk, rfl⟩ := computed
      exact .inl (upgradeToAltair_spec upgradedOk).2.1
    · subst computed
      exact .inl rfl
    · subst computed
      exact .inl rfl
    · subst computed
      exact .inl rfl
    · obtain ⟨_, upgradedOk, rfl⟩ := computed
      obtain ⟨changes, ledger, -⟩ := upgradeToElectra_ledgerOf upgradedOk
      exact .inr ⟨changes, ledger⟩
    · obtain ⟨_, upgradedOk, rfl⟩ := computed
      exact .inl (upgradeToFulu_spec upgradedOk).2.1
    · obtain ⟨_, upgradedOk, rfl⟩ := computed
      exact .inl (upgradeToGloas_spec upgradedOk).2.1
    · obtain ⟨_, upgradedOk, rfl⟩ := computed
      obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgradedOk
      exact .inl (upgradeHezeFields_lists _).2.1

/-- The total that some changes ask to debit, of every kind, before any stop at zero. -/
def BalanceChange.debitedAll (changes : List BalanceChange) : Nat :=
  (changes.map fun
    | .credit _ _ => 0
    | .debit _ amount => amount).sum

/-- Changes lower a balance by at most what they debit. -/
theorem BalanceChange.le_foldl_apply :
    ∀ (changes : List BalanceChange) (balance : Nat),
      balance ≤ changes.foldl BalanceChange.apply balance + BalanceChange.debitedAll changes
  | [], balance => by simp [BalanceChange.debitedAll]
  | change :: rest, balance => by
    have later := BalanceChange.le_foldl_apply rest (BalanceChange.apply balance change)
    cases change <;>
      simp only [List.foldl_cons, BalanceChange.apply, BalanceChange.debitedAll,
        List.map_cons, List.sum_cons] at later ⊢ <;> omega

/-- Each step raises a balance by at most what its ledger credits.

It lowers the balance by at most what its ledger debits.

The state before the step must be ready for a ledger. -/
theorem Step.balanceAt_bounds {pre post : ForkedBeaconState preset}
    (step : Step config checks pre post) (ready : LedgerReady pre) :
    ∃ changes : Nat → List BalanceChange, ∀ i,
      balanceAt post.state i ≤ balanceAt pre.state i + BalanceChange.creditedAll (changes i) ∧
        balanceAt pre.state i ≤ balanceAt post.state i + BalanceChange.debitedAll (changes i) := by
  obtain ⟨changes, ledger⟩ := step.ledger ready
  refine ⟨changes, fun i => ?_⟩
  rw [ledger i]
  exact ⟨BalanceChange.foldl_apply_le _ _, BalanceChange.le_foldl_apply _ _⟩

namespace Run

variable {start : ForkedBeaconState preset}

/-- How much a run credits the balance at a position: the sum of the rise of each step.

A step that lowers the balance counts zero. -/
def credited (index : Nat) :
    {after : ForkedBeaconState preset} → Run config checks start after → Nat
  | _, .nil => 0
  | after, .snoc (middle := middle) run _ =>
    run.credited index + (balanceAt after.state index - balanceAt middle.state index)

/-- Every balance of a run is at most the balance at the start plus what the run credits. -/
theorem balanceAt_le_credited (index : Nat) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      ∀ state ∈ run.states,
        balanceAt state.state index ≤ balanceAt start.state index + run.credited index
  | _, .nil, state, member => by
    rw [List.mem_singleton.mp member]
    simp [credited]
  | after, .snoc (middle := middle) run _, state, member => by
    have earlier := balanceAt_le_credited index run
    have here := earlier middle (end_mem_states run)
    rcases List.mem_append.mp member with member | member
    · have := earlier state member
      simp only [credited]
      omega
    · rw [List.mem_singleton.mp member]
      simp only [credited]
      omega

/-- How much a run debits the balance at a position: the sum of the fall of each step.

A step that raises the balance counts zero. -/
def fallen (index : Nat) :
    {after : ForkedBeaconState preset} → Run config checks start after → Nat
  | _, .nil => 0
  | after, .snoc (middle := middle) run _ =>
    run.fallen index + (balanceAt middle.state index - balanceAt after.state index)

/-- Every balance of a run is at least the balance at the start less what the run debits. -/
theorem balanceAt_ge_fallen (index : Nat) :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      ∀ state ∈ run.states,
        balanceAt start.state index ≤ balanceAt state.state index + run.fallen index
  | _, .nil, state, member => by
    rw [List.mem_singleton.mp member]
    simp [fallen]
  | after, .snoc (middle := middle) run _, state, member => by
    have earlier := balanceAt_ge_fallen index run
    have here := earlier middle (end_mem_states run)
    rcases List.mem_append.mp member with member | member
    · have := earlier state member
      simp only [fallen]
      omega
    · rw [List.mem_singleton.mp member]
      simp only [fallen]
      omega

/-- Every state of a run is reached from its start. -/
theorem reaches_of_mem :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      ∀ state ∈ run.states, Reaches config checks start state
  | _, .nil, state, member => by
    rw [List.mem_singleton.mp member]
    exact .refl _
  | _, .snoc run step, state, member => by
    rcases List.mem_append.mp member with member | member
    · exact reaches_of_mem run state member
    · rw [List.mem_singleton.mp member]
      exact ⟨.snoc run step⟩

/-- What a run credits and debits each balance is at most what the ledgers of its steps do.

Each state of the run must be ready for a ledger. -/
theorem credited_fallen_le {after : ForkedBeaconState preset} :
    ∀ (run : Run config checks start after),
      (∀ state ∈ run.states, LedgerReady state) →
      ∃ changes : Nat → List BalanceChange, ∀ i,
        balanceAt after.state i = (changes i).foldl BalanceChange.apply (balanceAt start.state i) ∧
        run.credited i ≤ BalanceChange.creditedAll (changes i) ∧
        run.fallen i ≤ BalanceChange.debitedAll (changes i)
  | .nil, _ => ⟨fun _ => [], fun i => by simp [credited, fallen]⟩
  | .snoc (middle := middle) run step, ready => by
    obtain ⟨first, firstLedger⟩ :=
      credited_fallen_le run fun state member => ready state (List.mem_append_left _ member)
    obtain ⟨second, secondLedger⟩ := step.ledger (ready middle
      (List.mem_append_left _ (end_mem_states run)))
    refine ⟨fun i => first i ++ second i, fun i => ?_⟩
    obtain ⟨firstEq, firstCredited, firstFallen⟩ := firstLedger i
    have rise := BalanceChange.foldl_apply_le (second i) (balanceAt middle.state i)
    have fall := BalanceChange.le_foldl_apply (second i) (balanceAt middle.state i)
    rw [← secondLedger i] at rise fall
    have credits : BalanceChange.creditedAll (first i ++ second i) =
        BalanceChange.creditedAll (first i) + BalanceChange.creditedAll (second i) := by
      simp [BalanceChange.creditedAll]
    have debits : BalanceChange.debitedAll (first i ++ second i) =
        BalanceChange.debitedAll (first i) + BalanceChange.debitedAll (second i) := by
      simp [BalanceChange.debitedAll]
    rw [credits, debits, List.foldl_append, ← firstEq, ← secondLedger i]
    simp only [credited, fallen]
    exact ⟨trivial, by omega, by omega⟩

/-- An effective balance at the end of a run is bounded by the values at its start.

It is at most the larger of the effective balance and the balance, plus what the run credits.

It is for a position that holds a validator at the start.

It needs a registry of fewer than `2^64` validators at the end, which holds before Gloas. -/
theorem effectiveAt_le_credited {after : ForkedBeaconState preset}
    (run : Run config checks start after) (small : after.state.validators.data.size < 2 ^ 64)
    (index : Nat) (present : index < start.state.validators.data.size) :
    effectiveAt after.state index ≤
      max (effectiveAt start.state index) (balanceAt start.state index) + run.credited index := by
  obtain ⟨later, found, bound⟩ := run.effectiveBalance_ceiling small index
    start.state.validators.data[index] (Array.getElem?_eq_getElem present)
    (max (effectiveAt start.state index) (balanceAt start.state index) + run.credited index)
    (by simp [effectiveAt, Array.getElem?_eq_getElem present]; omega)
    (fun state member => by have := balanceAt_le_credited index run state member; omega)
  simpa [effectiveAt, found] using bound

/-- What the validators at some positions gain in effective balance along a run.

Each gains at most the excess of its balance over its effective balance at the start, plus more.

That more is what the run credits it.

Each position must hold a validator at the start.

It needs a registry of fewer than `2^64` validators at the end, which holds before Gloas. -/
theorem gained_le {after : ForkedBeaconState preset} (run : Run config checks start after)
    (small : after.state.validators.data.size < 2 ^ 64) (positions : Finset Nat)
    (present : ∀ index ∈ positions, index < start.state.validators.data.size) :
    ∑ index ∈ positions, (effectiveAt after.state index - effectiveAt start.state index) ≤
      ∑ index ∈ positions,
        (balanceAt start.state index - effectiveAt start.state index + run.credited index) := by
  apply Finset.sum_le_sum
  intro index member
  have := run.effectiveAt_le_credited small index (present index member)
  omega

end Run

end EthLib.Consensus
