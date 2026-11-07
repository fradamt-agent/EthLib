module

public import EthLib.Consensus.Proofs.Transition.Withdrawals

/-!
# Proofs: the amounts that the withdrawals take, at every fork from Capella

A withdrawal takes from the balance of a validator, or from Gloas from the balance of a builder.

The withdrawal step applies the withdrawals that `AppliedWithdrawals` names.

Before Gloas they are those of the payload; from Gloas they are the expected ones, or none.

They lower the balance of each validator by exactly their total for it, which never exceeds it.

So a validator that withdraws nothing keeps its balance.

From Gloas the withdrawals of builders take nothing from a validator.

They lower the balance of each builder by their total for it, to at least zero.

The sweep of validators visits at most the registry and at most the most validators per sweep.

The other parts of the expected withdrawals have bounds of the same kind.

Each expected withdrawal pays an exact amount, read from the balance left before it.

A queued builder withdrawal pays the amount of its entry.

A queued partial withdrawal pays the balance above the activation balance, or less if asked.

The sweep of builders pays a withdrawable builder all of its balance left.

The sweep of validators pays a fully withdrawable validator all of its balance left.

It pays a partially withdrawable one the part above its largest effective balance.

It pays each validator at most once and comes last.

So a validator that it pays in full ends the step at zero.

One that it pays partially ends at exactly its largest effective balance.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz

variable {preset : Preset} {fork : Base.Fork} {state after : BeaconState preset fork}

/-! ## Applying withdrawals to the balance of a validator -/

/-- At every fork, withdrawals within a validator's balance lower it by exactly their total.

The index of the validator must not name a builder.

From Gloas the withdrawals of builders change no balance of a validator. -/
theorem foldlM_applyWithdrawal_balance {index : ValidatorIndex}
    (notBuilder : isBuilderIndex index = false) :
    ∀ (withdrawals : List Withdrawal) (state after : BeaconState preset fork) (balance : Gwei),
    withdrawals.foldlM applyWithdrawal state = .ok after →
    state.balances.data[index.toNat]? = some balance →
    withdrawnFrom withdrawals.toArray index ≤ balance.toNat →
    (after.balances.data[index.toNat]?).map UInt64.toNat =
      some (balance.toNat - withdrawnFrom withdrawals.toArray index)
  | [], state, after, balance, computed, found, _ => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp [found, withdrawnFrom]
  | withdrawal :: rest, state, after, balance, computed, found, bounded => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, computed⟩ := computed
    rw [withdrawnFrom_cons] at bounded ⊢
    unfold applyWithdrawal at step
    split at step
    · -- A withdrawal of a builder changes only the registry of builders.
      rename_i builder
      have other : withdrawal.validatorIndex ≠ index := fun same => by
        rw [same, notBuilder] at builder
        exact Bool.false_ne_true builder.2
      simp only [bind_ok_iff] at step
      obtain ⟨_, _, set⟩ := step
      obtain ⟨_, rfl⟩ := setBuilder_ok set
      simp only [other, ↓reduceIte, Nat.zero_add] at bounded ⊢
      exact foldlM_applyWithdrawal_balance notBuilder rest _ after balance computed found bounded
    · simp only [decreaseBalance, bind_ok_iff] at step
      obtain ⟨old, oldOk, set⟩ := step
      obtain ⟨inside, rfl⟩ := setBalance_ok set
      by_cases same : withdrawal.validatorIndex = index
      · simp only [same, ↓reduceIte] at bounded ⊢
        subst same
        simp only [getBalance, found, Except.ok.injEq] at oldOk
        subst oldOk
        have inRange := (Array.getElem?_eq_some_iff.mp found).1
        rw [foldlM_applyWithdrawal_balance notBuilder rest _ after
          (saturatingSub balance withdrawal.amount) computed
          (by simp [BeaconState.putBalance, inRange]) (by rw [toNat_saturatingSub]; omega),
          toNat_saturatingSub]
        congr 1
        omega
      · simp only [same, ↓reduceIte, Nat.zero_add] at bounded ⊢
        have apart : withdrawal.validatorIndex.toNat ≠ index.toNat :=
          fun h => same (UInt64.toNat_inj.mp h)
        exact foldlM_applyWithdrawal_balance notBuilder rest _ after balance computed
          (by simp [BeaconState.putBalance, apart, found]) bounded

/-! ## The withdrawals of builders -/

/-- Withdrawals that each name a builder. -/
def AllBuilders (withdrawals : Array Withdrawal) : Prop :=
  ∀ withdrawal ∈ withdrawals.toList, isBuilderIndex withdrawal.validatorIndex = true

/-- Withdrawals of builders take nothing from an index that names no builder. -/
theorem withdrawnFrom_of_allBuilders {withdrawals : Array Withdrawal} {index : ValidatorIndex}
    (builders : AllBuilders withdrawals) (notBuilder : isBuilderIndex index = false) :
    withdrawnFrom withdrawals index = 0 := by
  unfold withdrawnFrom
  rw [List.filter_eq_nil_iff.mpr fun withdrawal member same => by
    have := builders withdrawal member
    rw [of_decide_eq_true same, notBuilder] at this
    cases this]
  rfl

/-- The total of a validator over two lists of withdrawals is the sum of the two totals. -/
theorem withdrawnFrom_append (first second : Array Withdrawal) (index : ValidatorIndex) :
    withdrawnFrom (first ++ second) index =
      withdrawnFrom first index + withdrawnFrom second index := by
  simp [withdrawnFrom, List.filter_append]

/-- A withdrawal of a builder appended to withdrawals of builders keeps them all of builders. -/
theorem appendWithdrawal_allBuilders {withdrawals after : Array Withdrawal}
    {next next' : WithdrawalIndex} {index : BuilderIndex} {address : ExecutionAddress}
    {amount : Gwei} (builders : AllBuilders withdrawals)
    (computed : appendWithdrawal withdrawals next (convertBuilderIndexToValidatorIndex index)
      address amount = .ok (after, next')) :
    AllBuilders after := by
  simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at computed
  obtain ⟨_, _, rfl, rfl⟩ := computed
  intro withdrawal member
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact builders withdrawal member
  · exact isBuilderIndex_convertBuilderIndexToValidatorIndex index

/-- The queued builder withdrawals that a payload pays each name a builder. -/
theorem getBuilderWithdrawals_loop_allBuilders {prior : Array Withdrawal} {limit : UInt64} :
    ∀ (queue : List BuilderPendingWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    AllBuilders withdrawals →
    getBuilderWithdrawals.loop prior limit queue withdrawals next processed = .ok result →
    AllBuilders result.1
  | [], _, _, _, _, builders, computed => by
    simp only [getBuilderWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact builders
  | _ :: rest, _, _, _, _, builders, computed => by
    simp only [getBuilderWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact builders
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, rest'⟩ := computed
      exact getBuilderWithdrawals_loop_allBuilders rest _ _ _
        (appendWithdrawal_allBuilders builders appendedOk) rest'

/-- The withdrawals of the sweep of builders each name a builder. -/
theorem getBuildersSweepWithdrawals_loop_allBuilders {gloas : .glamsterdam ≤ fork}
    {prior : Array Withdrawal} {epoch : Epoch} {count : Nat} {limit : UInt64} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : BuilderIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    AllBuilders withdrawals →
    getBuildersSweepWithdrawals.loop state gloas prior epoch count limit visits withdrawals next
      index processed = .ok result →
    AllBuilders result.1
  | 0, _, _, _, _, _, builders, computed => by
    simp only [getBuildersSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact builders
  | visits + 1, _, _, _, _, _, builders, computed => by
    simp only [getBuildersSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact builders
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest⟩ := computed
        exact getBuildersSweepWithdrawals_loop_allBuilders visits _ _ _ _
          (appendWithdrawal_allBuilders builders appendedOk) rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at computed
        obtain ⟨_, _, rest⟩ := computed
        exact getBuildersSweepWithdrawals_loop_allBuilders visits _ _ _ _ builders rest

/-- No withdrawals at all are withdrawals of builders. -/
theorem allBuilders_empty : AllBuilders #[] := fun _ absent => absurd absent List.not_mem_nil

/-- At every fork, the expected withdrawals take from a validator at most its balance.

The index of the validator must not name a builder. -/
theorem getExpectedWithdrawals_withdrawnFrom_le {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : getExpectedWithdrawals state capella = .ok expected) {index : ValidatorIndex}
    (notBuilder : isBuilderIndex index = false) {balance : Gwei}
    (found : state.balances.data[index.toNat]? = some balance) :
    withdrawnFrom expected.withdrawals index ≤ balance.toNat := by
  unfold getExpectedWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨⟨builders, index1, _⟩, buildersOk, ⟨partials, index2, _⟩, partialsOk,
    ⟨buildersSweep, index3, _⟩, buildersSweepOk, ⟨sweep, index4, _⟩, sweepOk, rfl⟩ := computed
  -- The queued builder withdrawals take nothing from the validator.
  have one : AllBuilders builders := by
    split at buildersOk
    · unfold getBuilderWithdrawals at buildersOk
      simp only [bind_ok_iff, ensure_ok_iff] at buildersOk
      obtain ⟨_, _, _, _, loopOk⟩ := buildersOk
      exact getBuilderWithdrawals_loop_allBuilders _ _ _ _ allBuilders_empty loopOk
    · simp only [Except.ok.injEq, Prod.mk.injEq] at buildersOk
      obtain ⟨rfl, -, -⟩ := buildersOk
      exact allBuilders_empty
  have two : withdrawnFrom (builders ++ partials) index ≤ balance.toNat := by
    split at partialsOk
    · unfold getPendingPartialWithdrawals at partialsOk
      simp only [bind_ok_iff, ensure_ok_iff] at partialsOk
      obtain ⟨_, _, _, _, loopOk⟩ := partialsOk
      exact getPendingPartialWithdrawals_loop_withdrawnFrom found _ _ _ _
        (by simp [withdrawnFrom_of_allBuilders one notBuilder]) loopOk
    · simp only [Except.ok.injEq, Prod.mk.injEq] at partialsOk
      obtain ⟨rfl, -, -⟩ := partialsOk
      simp [withdrawnFrom_of_allBuilders one notBuilder]
  -- The sweep of builders takes nothing from the validator either.
  have three : AllBuilders buildersSweep := by
    split at buildersSweepOk
    · unfold getBuildersSweepWithdrawals at buildersSweepOk
      simp only [bind_ok_iff, ensure_ok_iff] at buildersSweepOk
      obtain ⟨_, _, _, _, loopOk⟩ := buildersSweepOk
      exact getBuildersSweepWithdrawals_loop_allBuilders _ _ _ _ _ allBuilders_empty loopOk
    · simp only [Except.ok.injEq, Prod.mk.injEq] at buildersSweepOk
      obtain ⟨rfl, -, -⟩ := buildersSweepOk
      exact allBuilders_empty
  unfold getValidatorsSweepWithdrawals at sweepOk
  simp only [bind_ok_iff, ensure_ok_iff] at sweepOk
  obtain ⟨_, _, loopOk⟩ := sweepOk
  exact getValidatorsSweepWithdrawals_loop_withdrawnFrom found _ _ _ _ _
    (by simpa [withdrawnFrom_append, withdrawnFrom_of_allBuilders three notBuilder] using two)
    loopOk

/-! ## The withdrawal step -/

/-- Moving the start of the next sweep of builders keeps the balances and the builders. -/
theorem updateNextWithdrawalBuilderIndex_balances {gloas : .glamsterdam ≤ fork} {count : Nat}
    (computed : updateNextWithdrawalBuilderIndex state gloas count = .ok after) :
    after.balances = state.balances ∧ after.builders = state.builders := by
  unfold updateNextWithdrawalBuilderIndex at computed
  dsimp only at computed
  split at computed
  · cases computed
    exact ⟨rfl, rfl⟩
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨rfl, rfl⟩

/-- At every fork, only the withdrawals themselves change the balances and the builders. -/
theorem applyExpectedWithdrawals_applied {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    ∃ applied, applyWithdrawals state expected.withdrawals = .ok applied ∧
      after.balances = applied.balances ∧ after.builders = applied.builders := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, swept, sweptOk, last⟩ := computed
  refine ⟨applied, appliedOk, ?_⟩
  have one : indexed.balances = applied.balances ∧ indexed.builders = applied.builders := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact ⟨rfl, rfl⟩
    · cases indexedOk
      exact ⟨rfl, rfl⟩
  -- The queues, the recorded withdrawals and the sweep of builders hold no balance.
  have two : swept.balances = indexed.balances ∧ swept.builders = indexed.builders := by
    split at sweptOk
    · rw [(updateNextWithdrawalBuilderIndex_balances sweptOk).1,
        (updateNextWithdrawalBuilderIndex_balances sweptOk).2]
      constructor <;> split <;> (try split) <;> rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at sweptOk
      subst sweptOk
      constructor <;> split <;> (try split) <;> rfl
  unfold updateNextWithdrawalValidatorIndex at last
  simp only [bind_ok_iff] at last
  obtain ⟨_, _, last⟩ := last
  split at last
  · cases last
  · cases last
    exact ⟨two.1.trans one.1, two.2.trans one.2⟩

/-- The withdrawals that the withdrawal step applies, at every fork from Capella.

Before Gloas they are those of the payload, which are the expected ones.

From Gloas, after a parent with its payload, they are the expected ones, which the state records.

From Gloas, after a parent without its payload, there are none. -/
def AppliedWithdrawals (state after : BeaconState preset fork) (capella : .shapella ≤ fork)
    (payload : Until .glamsterdam fork (ExecutionPayload preset fork))
    (withdrawals : Array Withdrawal) : Prop :=
  (∀ before : fork < .glamsterdam, withdrawals = ((payload before).withdrawals capella).data) ∧
  ∀ gloas : .glamsterdam ≤ fork,
    (isParentBlockFull state gloas = true →
      withdrawals = (after.payloadExpectedWithdrawals gloas).data) ∧
    (isParentBlockFull state gloas = false → withdrawals = #[])

/-- The withdrawal step applies the withdrawals of `AppliedWithdrawals`, at every fork.

They are the expected withdrawals, or none from Gloas after a parent without its payload.

Only they change the balances and the builders. -/
theorem processWithdrawals_applied {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    ∃ withdrawals applied, AppliedWithdrawals state after capella payload withdrawals ∧
      (withdrawals = #[] ∨ ∃ expected : ExpectedWithdrawals,
          getExpectedWithdrawals state capella = .ok expected ∧
            expected.withdrawals = withdrawals) ∧
      applyWithdrawals state withdrawals = .ok applied ∧
      after.balances = applied.balances ∧ after.builders = applied.builders := by
  by_cases gloas : .glamsterdam ≤ fork
  · by_cases full : isParentBlockFull state gloas = true
    · obtain ⟨expected, expectedOk, appliedOk, recorded⟩ :=
        processWithdrawals_recorded gloas full computed
      obtain ⟨applied, applyOk, balances, builders⟩ := applyExpectedWithdrawals_applied appliedOk
      have kept : AppliedWithdrawals state after capella payload expected.withdrawals := by
        refine ⟨fun before => absurd gloas (Nat.not_le_of_lt before), fun _ => ⟨fun _ => ?_,
          fun empty => ?_⟩⟩
        · exact recorded.symm
        · rw [full] at empty
          cases empty
      refine ⟨expected.withdrawals, applied, kept,
        .inr ⟨expected, expectedOk, rfl⟩, applyOk, balances, builders⟩
    · have empty : isParentBlockFull state gloas = false := by simpa using full
      rw [processWithdrawals_of_parentEmpty payload gloas empty, Except.ok.injEq] at computed
      subst computed
      have kept : AppliedWithdrawals state state capella payload #[] := by
        refine ⟨fun before => absurd gloas (Nat.not_le_of_lt before), fun _ => ⟨fun full' => ?_,
          fun _ => rfl⟩⟩
        rw [empty] at full'
        cases full'
      exact ⟨#[], state, kept, .inl rfl, rfl, rfl, rfl⟩
  · have before : fork < .glamsterdam := Nat.lt_of_not_le gloas
    obtain ⟨expected, expectedOk, carried, appliedOk⟩ := processWithdrawals_expected before computed
    obtain ⟨applied, applyOk, balances, builders⟩ := applyExpectedWithdrawals_applied appliedOk
    refine ⟨expected.withdrawals, applied, ⟨fun before' => ?_, fun gloas' => absurd gloas' gloas⟩,
      .inr ⟨expected, expectedOk, rfl⟩, applyOk, balances, builders⟩
    rw [show before' = before from rfl, carried]

/-- The withdrawal step lowers the balance of a validator by exactly what it withdraws.

This holds at every fork from Capella, for an index that names no builder.

The withdrawals are those that `AppliedWithdrawals` names.

They never take more than the balance.

So the subtraction does not stop at zero, and a balance that withdraws nothing stays. -/
theorem processWithdrawals_balance_of_notBuilder {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) {index : ValidatorIndex}
    (notBuilder : isBuilderIndex index = false) {balance : Gwei}
    (found : state.balances.data[index.toNat]? = some balance) :
    ∃ withdrawals, AppliedWithdrawals state after capella payload withdrawals ∧
      withdrawnFrom withdrawals index ≤ balance.toNat ∧
      (after.balances.data[index.toNat]?).map UInt64.toNat =
        some (balance.toNat - withdrawnFrom withdrawals index) := by
  obtain ⟨withdrawals, applied, named, source, applyOk, balances, -⟩ :=
    processWithdrawals_applied computed
  have bounded : withdrawnFrom withdrawals index ≤ balance.toNat := by
    rcases source with rfl | ⟨expected, expectedOk, rfl⟩
    · simp [withdrawnFrom]
    · exact getExpectedWithdrawals_withdrawnFrom_le expectedOk notBuilder found
  unfold applyWithdrawals at applyOk
  rw [← Array.foldlM_toList] at applyOk
  refine ⟨withdrawals, named, bounded, ?_⟩
  rw [balances]
  simpa using foldlM_applyWithdrawal_balance notBuilder _ _ _ _ applyOk found
    (by simpa using bounded)

/-- The withdrawal step lowers the balance of each validator of the registry by what it withdraws.

The registry must be within its limit, and that limit at most `2^40`.

Then no validator index names a builder. -/
theorem processWithdrawals_balance_of_registry {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    (within : state.RegistryWithinLimit) (limit : preset.VALIDATOR_REGISTRY_LIMIT.toNat ≤ 2 ^ 40)
    {index : ValidatorIndex} (member : index.toNat < state.validators.data.size) {balance : Gwei}
    (found : state.balances.data[index.toNat]? = some balance) :
    ∃ withdrawals, AppliedWithdrawals state after capella payload withdrawals ∧
      withdrawnFrom withdrawals index ≤ balance.toNat ∧
      (after.balances.data[index.toNat]?).map UInt64.toNat =
        some (balance.toNat - withdrawnFrom withdrawals index) :=
  processWithdrawals_balance_of_notBuilder computed
    (isBuilderIndex_eq_false_of_registry within limit member) found

/-! ## The balances of builders -/

/-- From Gloas, withdrawals lower the balance of a builder by their total for it, to at least zero.

The builder index must be below `2^40`, so that the index of its withdrawals names it alone. -/
theorem foldlM_applyWithdrawal_builder (gloas : .glamsterdam ≤ fork) {index : BuilderIndex}
    (small : index.toNat < 2 ^ 40) :
    ∀ (withdrawals : List Withdrawal) (state after : BeaconState preset fork),
    withdrawals.foldlM applyWithdrawal state = .ok after →
    ((after.builders gloas).data[index.toNat]?).map (·.balance.toNat) =
      ((state.builders gloas).data[index.toNat]?).map fun builder => builder.balance.toNat -
        withdrawnFrom withdrawals.toArray (convertBuilderIndexToValidatorIndex index)
  | [], state, after, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    cases (state.builders gloas).data[index.toNat]? <;> simp [withdrawnFrom]
  | withdrawal :: rest, state, after, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, computed⟩ := computed
    rw [foldlM_applyWithdrawal_builder gloas small rest middle after computed]
    simp only [withdrawnFrom_cons]
    unfold applyWithdrawal at step
    split at step
    · rename_i flagged
      simp only [bind_ok_iff] at step
      obtain ⟨builder, builderOk, set⟩ := step
      obtain ⟨inside, rfl⟩ := setBuilder_ok set
      -- The withdrawal names this builder exactly when its builder index is this one.
      have named : convertValidatorIndexToBuilderIndex withdrawal.validatorIndex = index ↔
          withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex index := by
        constructor
        · intro same
          rw [← same, convertBuilderIndexToValidatorIndex_convertValidatorIndexToBuilderIndex
            flagged.2]
        · intro same
          rw [same, convertValidatorIndexToBuilderIndex_convertBuilderIndexToValidatorIndex small]
      by_cases same : convertValidatorIndexToBuilderIndex withdrawal.validatorIndex = index
      · have equal := named.mp same
        simp only [getBuilder, same] at builderOk
        split at builderOk
        · rename_i read
          cases builderOk
          simp [BeaconState.putBuilder, read, equal, toNat_saturatingSub, Nat.sub_sub,
            convertValidatorIndexToBuilderIndex_convertBuilderIndexToValidatorIndex small]
        · cases builderOk
      · have apart : (convertValidatorIndexToBuilderIndex withdrawal.validatorIndex).toNat ≠
            index.toNat := fun h => same (UInt64.toNat_inj.mp h)
        have other : withdrawal.validatorIndex ≠ convertBuilderIndexToValidatorIndex index :=
          fun h => same (named.mpr h)
        simp [BeaconState.putBuilder, apart, other]
    · -- A withdrawal of a validator keeps the builders.
      rename_i notFlagged
      have other : withdrawal.validatorIndex ≠ convertBuilderIndexToValidatorIndex index :=
        fun h => notFlagged ⟨gloas, h ▸ isBuilderIndex_convertBuilderIndexToValidatorIndex index⟩
      simp only [decreaseBalance, bind_ok_iff] at step
      obtain ⟨_, _, set⟩ := step
      obtain ⟨_, rfl⟩ := setBalance_ok set
      simp [BeaconState.putBalance, other]

/-- From Gloas, the withdrawal step lowers each builder's balance by what it withdraws.

The balance stops at zero.

The builder index must be below `2^40`.

The step does not check a queued payment of a builder against its balance. -/
theorem processWithdrawals_builder {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (gloas : .glamsterdam ≤ fork)
    (computed : processWithdrawals state capella payload = .ok after) {index : BuilderIndex}
    (small : index.toNat < 2 ^ 40) :
    ∃ withdrawals, AppliedWithdrawals state after capella payload withdrawals ∧
      ((after.builders gloas).data[index.toNat]?).map (·.balance.toNat) =
        ((state.builders gloas).data[index.toNat]?).map fun builder => builder.balance.toNat -
          withdrawnFrom withdrawals (convertBuilderIndexToValidatorIndex index) := by
  obtain ⟨withdrawals, applied, named, -, applyOk, -, builders⟩ :=
    processWithdrawals_applied computed
  unfold applyWithdrawals at applyOk
  rw [← Array.foldlM_toList] at applyOk
  refine ⟨withdrawals, named, ?_⟩
  rw [builders]
  simpa using foldlM_applyWithdrawal_builder gloas small _ _ _ applyOk

/-! ## The bounds of the sweeps -/

/-- The sweep of validators visits at most the visits it is given. -/
theorem getValidatorsSweepWithdrawals_loop_processed {prior : Array Withdrawal} {epoch : Epoch}
    {count limit : Nat} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : ValidatorIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getValidatorsSweepWithdrawals.loop state prior epoch count limit visits withdrawals next index
      processed = .ok result →
    result.2.2 ≤ processed + visits
  | 0, _, _, _, _, _, computed => by
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | visits + 1, _, _, _, _, _, computed => by
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      simp
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, _, _, _, rest⟩ := computed
        have := getValidatorsSweepWithdrawals_loop_processed visits _ _ _ _ rest
        omega
      · split at computed
        · simp only [bind_ok_iff, liftAccessor_ok] at computed
          obtain ⟨_, _, _, _, rest⟩ := computed
          have := getValidatorsSweepWithdrawals_loop_processed visits _ _ _ _ rest
          omega
        · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left']
            at computed
          obtain ⟨_, _, rest⟩ := computed
          have := getValidatorsSweepWithdrawals_loop_processed visits _ _ _ _ rest
          omega

/-- The sweep of builders visits at most the visits it is given. -/
theorem getBuildersSweepWithdrawals_loop_processed {gloas : .glamsterdam ≤ fork}
    {prior : Array Withdrawal} {epoch : Epoch} {count : Nat} {limit : UInt64} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : BuilderIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getBuildersSweepWithdrawals.loop state gloas prior epoch count limit visits withdrawals next
      index processed = .ok result →
    result.2.2 ≤ processed + visits
  | 0, _, _, _, _, _, computed => by
    simp only [getBuildersSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | visits + 1, _, _, _, _, _, computed => by
    simp only [getBuildersSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      simp
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, _, _, _, rest⟩ := computed
        have := getBuildersSweepWithdrawals_loop_processed visits _ _ _ _ rest
        omega
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at computed
        obtain ⟨_, _, rest⟩ := computed
        have := getBuildersSweepWithdrawals_loop_processed visits _ _ _ _ rest
        omega

/-- The queued partial withdrawals that a payload reads number at most the queue. -/
theorem getPendingPartialWithdrawals_loop_processed {prior : Array Withdrawal} {epoch : Epoch}
    {limit : Nat} :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    result.2.2 ≤ processed + queue.length
  | [], _, _, _, _, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | _ :: rest, _, _, _, _, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      simp
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, _, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, _, rest'⟩ := computed
        have := getPendingPartialWithdrawals_loop_processed rest _ _ _ rest'
        simp only [List.length_cons]
        omega
      · have := getPendingPartialWithdrawals_loop_processed rest _ _ _ computed
        simp only [List.length_cons]
        omega

/-- The queued builder withdrawals that a payload reads number at most the queue. -/
theorem getBuilderWithdrawals_loop_processed {prior : Array Withdrawal} {limit : UInt64} :
    ∀ (queue : List BuilderPendingWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getBuilderWithdrawals.loop prior limit queue withdrawals next processed = .ok result →
    result.2.2 ≤ processed + queue.length
  | [], _, _, _, _, computed => by
    simp only [getBuilderWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    simp
  | _ :: rest, _, _, _, _, computed => by
    simp only [getBuilderWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      simp
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, rest'⟩ := computed
      have := getBuilderWithdrawals_loop_processed rest _ _ _ rest'
      simp only [List.length_cons]
      omega

/-- The bounds of the parts of the expected withdrawals.

The sweep visits at most the registry and at most the most validators per sweep.

From Gloas the sweep of builders visits at most their registry and the most builders per sweep.

From Electra the queued partial withdrawals that are read number at most the queue.

At most the most queued partials per sweep of them are paid.

From Gloas the queued builder withdrawals that are read number at most their queue. -/
theorem getExpectedWithdrawals_bounds {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : getExpectedWithdrawals state capella = .ok expected) :
    expected.processedSweepWithdrawalsCount ≤
        min state.validators.data.size preset.MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP.toNat ∧
      (∀ gloas : .glamsterdam ≤ fork, expected.processedBuildersSweepCount ≤
        min (state.builders gloas).data.size preset.MAX_BUILDERS_PER_WITHDRAWALS_SWEEP.toNat) ∧
      (∀ electra : .pectra ≤ fork, expected.processedPartialWithdrawalsCount ≤
        (state.pendingPartialWithdrawals electra).data.size) ∧
      (∀ gloas : .glamsterdam ≤ fork, expected.processedBuilderWithdrawalsCount ≤
        (state.builderPendingWithdrawals gloas).data.size) := by
  unfold getExpectedWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨⟨builders, index1, builderCount⟩, buildersOk, ⟨partials, index2, partialCount⟩,
    partialsOk, ⟨buildersSweep, index3, buildersSweepCount⟩, buildersSweepOk,
    ⟨sweep, index4, sweepCount⟩, sweepOk, rfl⟩ := computed
  refine ⟨?_, fun gloas => ?_, fun electra => ?_, fun gloas => ?_⟩
  · unfold getValidatorsSweepWithdrawals at sweepOk
    simp only [bind_ok_iff, ensure_ok_iff] at sweepOk
    obtain ⟨_, _, loopOk⟩ := sweepOk
    simpa using getValidatorsSweepWithdrawals_loop_processed _ _ _ _ _ loopOk
  · simp only [gloas, ↓reduceDIte] at buildersSweepOk
    unfold getBuildersSweepWithdrawals at buildersSweepOk
    simp only [bind_ok_iff, ensure_ok_iff] at buildersSweepOk
    obtain ⟨_, _, _, _, loopOk⟩ := buildersSweepOk
    simpa using getBuildersSweepWithdrawals_loop_processed _ _ _ _ _ loopOk
  · simp only [electra, ↓reduceDIte] at partialsOk
    unfold getPendingPartialWithdrawals at partialsOk
    simp only [bind_ok_iff, ensure_ok_iff] at partialsOk
    obtain ⟨_, _, _, _, loopOk⟩ := partialsOk
    simpa using getPendingPartialWithdrawals_loop_processed _ _ _ _ loopOk
  · simp only [gloas, ↓reduceDIte] at buildersOk
    unfold getBuilderWithdrawals at buildersOk
    simp only [bind_ok_iff, ensure_ok_iff] at buildersOk
    obtain ⟨_, _, _, _, loopOk⟩ := buildersOk
    simpa using getBuilderWithdrawals_loop_processed _ _ _ _ loopOk

/-! ## What the sweep pays each validator -/

/-- What the sweep pays one validator, after the withdrawals of the payload before it.

The validator's balance left after those withdrawals is the amount it can still withdraw.

A fully withdrawable validator withdraws all of it.

Otherwise a partially withdrawable one withdraws the part above its largest effective balance. -/
def SweepPays (state : BeaconState preset fork) (epoch : Epoch) (before : Array Withdrawal)
    (withdrawal : Withdrawal) : Prop :=
  ∃ validator left, getValidator state withdrawal.validatorIndex = .ok validator ∧
    getBalanceAfterWithdrawals state withdrawal.validatorIndex before = .ok left ∧
    ((isFullyWithdrawableValidator fork validator left epoch = true ∧ withdrawal.amount = left) ∨
      (isFullyWithdrawableValidator fork validator left epoch = false ∧
        isPartiallyWithdrawableValidator preset fork validator left = true ∧
        withdrawal.amount = left - withdrawalMaxEffectiveBalance preset fork validator))

/-- Two positions of a sweep that wraps around a registry name different validators.

The positions are fewer than the size of the registry. -/
private theorem mod_ne_of_lt {start t u count : Nat} (lt : t < u) (small : u < count) :
    (start + t) % count ≠ (start + u) % count := by
  intro same
  have divides : count ∣ (start + u) - (start + t) :=
    Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq same.symm)
  have := Nat.le_of_dvd (by omega) divides
  omega

/-- The loop of the sweep pays each validator it visits as `SweepPays` says, at most once.

The sweep starts at a validator of the registry, and wraps around it.

It visits fewer validators than the registry holds. -/
theorem getValidatorsSweepWithdrawals_loop_pays {prior : Array Withdrawal} {epoch : Epoch}
    {limit : Nat} (within : state.RegistryWithinLimit) {start : Nat}
    (first : start < state.validators.data.size) :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : ValidatorIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    index.toNat = (start + processed) % state.validators.data.size →
    processed + visits ≤ state.validators.data.size →
    (∀ k (inside : k < withdrawals.size),
      SweepPays state epoch (prior ++ withdrawals.extract 0 k) withdrawals[k]) →
    (∀ k (inside : k < withdrawals.size), ∃ t < processed,
      withdrawals[k].validatorIndex.toNat = (start + t) % state.validators.data.size) →
    (withdrawals.toList.map (·.validatorIndex.toNat)).Nodup →
    getValidatorsSweepWithdrawals.loop state prior epoch state.validators.data.size limit visits
      withdrawals next index processed = .ok result →
    (∀ k (inside : k < result.1.size),
      SweepPays state epoch (prior ++ result.1.extract 0 k) result.1[k]) ∧
    (result.1.toList.map (·.validatorIndex.toNat)).Nodup
  | 0, _, _, _, _, _, _, _, pays, _, distinct, computed => by
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨pays, distinct⟩
  | visits + 1, withdrawals, next, index, processed, _, position, room, pays, named, distinct,
      computed => by
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact ⟨pays, distinct⟩
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨validator, validatorOk, left, leftOk, computed⟩ := computed
    -- The next visit is the next validator of the registry, wrapping at its end.
    have advance : ∀ following : ValidatorIndex, following.toNat = index.toNat + 1 →
        ((following.toNat % state.validators.data.size).toUInt64).toNat =
          (start + (processed + 1)) % state.validators.data.size := by
      intro following value
      rw [toNat_toUInt64_of_lt within (Nat.mod_lt _ (by omega)), value, position,
        Nat.mod_add_mod]
      rfl
    -- A withdrawal appended for this validator keeps what the loop keeps.
    have append : ∀ {appended : Array Withdrawal} {following : WithdrawalIndex} {amount : Gwei},
        appendWithdrawal withdrawals next index (credentialAddress validator.withdrawalCredentials)
          amount = .ok (appended, following) →
        (isFullyWithdrawableValidator fork validator left epoch = true ∧ amount = left) ∨
          (isFullyWithdrawableValidator fork validator left epoch = false ∧
            isPartiallyWithdrawableValidator preset fork validator left = true ∧
            amount = left - withdrawalMaxEffectiveBalance preset fork validator) →
        (∀ k (inside : k < appended.size),
          SweepPays state epoch (prior ++ appended.extract 0 k) appended[k]) ∧
        (∀ k (inside : k < appended.size), ∃ t < processed + 1,
          appended[k].validatorIndex.toNat = (start + t) % state.validators.data.size) ∧
        (appended.toList.map (·.validatorIndex.toNat)).Nodup := by
      intro appended following amount appendedOk kind
      simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at appendedOk
      obtain ⟨_, _, rfl, rfl⟩ := appendedOk
      refine ⟨fun k inside => ?_, fun k inside => ?_, ?_⟩
      · simp only [Array.size_push] at inside
        by_cases old : k < withdrawals.size
        · rw [Array.getElem_push_lt old, Array.extract_push_of_le (by omega)]
          exact pays k old
        · obtain rfl : k = withdrawals.size := by omega
          rw [Array.getElem_push_eq, Array.extract_push_of_le (Nat.le_refl _),
            Array.extract_eq_self_of_le (Nat.le_refl _)]
          exact ⟨validator, left, validatorOk, leftOk, kind⟩
      · simp only [Array.size_push] at inside
        by_cases old : k < withdrawals.size
        · rw [Array.getElem_push_lt old]
          obtain ⟨t, earlier, value⟩ := named k old
          exact ⟨t, by omega, value⟩
        · obtain rfl : k = withdrawals.size := by omega
          rw [Array.getElem_push_eq]
          exact ⟨processed, by omega, position⟩
      · rw [Array.toList_push, List.map_append, List.nodup_append]
        refine ⟨distinct, by simp, fun earlier member last isLast equal => ?_⟩
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at isLast
        obtain ⟨withdrawal, listed, rfl⟩ := List.mem_map.mp member
        obtain ⟨k, inside, found⟩ := List.getElem_of_mem listed
        rw [Array.getElem_toList] at found
        obtain ⟨t, earlier, value⟩ := named k (by simpa using inside)
        rw [← found, value, isLast, position] at equal
        exact mod_ne_of_lt earlier (by omega) equal
    split at computed
    · rename_i full
      simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
        addChecked_ok_iff] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, nextIndex, ⟨_, nextValue⟩, rest⟩ := computed
      obtain ⟨pays', named', distinct'⟩ := append appendedOk (.inl ⟨full, rfl⟩)
      exact getValidatorsSweepWithdrawals_loop_pays within first visits _ _ _ _
        (advance nextIndex (by simpa using nextValue)) (by omega) pays' named' distinct' rest
    · rename_i notFull
      split at computed
      · rename_i excess
        simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
          addChecked_ok_iff] at computed
        obtain ⟨⟨appended, following⟩, appendedOk, nextIndex, ⟨_, nextValue⟩, rest⟩ := computed
        obtain ⟨pays', named', distinct'⟩ :=
          append appendedOk (.inr ⟨by simpa using notFull, excess, rfl⟩)
        exact getValidatorsSweepWithdrawals_loop_pays within first visits _ _ _ _
          (advance nextIndex (by simpa using nextValue)) (by omega) pays' named' distinct' rest
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left',
          liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff] at computed
        obtain ⟨nextIndex, ⟨_, nextValue⟩, rest⟩ := computed
        exact getValidatorsSweepWithdrawals_loop_pays within first visits _ _ _ _
          (advance nextIndex (by simpa using nextValue)) (by omega) pays
          (fun k inside => by
            obtain ⟨t, earlier, value⟩ := named k inside
            exact ⟨t, by omega, value⟩) distinct rest

/-- A sweep that starts past the registry pays nothing: it stops, or it fails at its first visit.
-/
private theorem getValidatorsSweepWithdrawals_loop_outside {prior : Array Withdrawal}
    {epoch : Epoch} {count limit : Nat} {visits : Nat} {next : WithdrawalIndex}
    {index : ValidatorIndex} {result : Array Withdrawal × WithdrawalIndex × Nat}
    (outside : state.validators.data.size ≤ index.toNat)
    (computed : getValidatorsSweepWithdrawals.loop state prior epoch count limit visits #[] next
      index 0 = .ok result) :
    result.1 = #[] := by
  cases visits with
  | zero =>
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    rw [← computed]
  | succ visits =>
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      rw [← computed]
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, found, _⟩ := computed
      simp [getValidator, Array.getElem?_eq_none outside] at found

/-- For a registry within its limit, the sweep pays each validator it visits as `SweepPays` says.

It pays each validator at most once. -/
theorem getValidatorsSweepWithdrawals_pays {capella : .shapella ≤ fork}
    (within : state.RegistryWithinLimit) {start : WithdrawalIndex}
    {prior sweep : Array Withdrawal} {next : WithdrawalIndex} {processed : Nat}
    (computed : getValidatorsSweepWithdrawals state capella start prior =
      .ok (sweep, next, processed)) :
    (∀ k (inside : k < sweep.size),
      SweepPays state (getCurrentEpoch state) (prior ++ sweep.extract 0 k) sweep[k]) ∧
    (sweep.toList.map (·.validatorIndex.toNat)).Nodup := by
  unfold getValidatorsSweepWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, loopOk⟩ := computed
  by_cases first : (state.nextWithdrawalValidatorIndex capella).toNat < state.validators.data.size
  · exact getValidatorsSweepWithdrawals_loop_pays within first _ _ _ _ _
      (by simp [Nat.mod_eq_of_lt first]) (by simpa using Nat.min_le_left _ _)
      (fun _ inside => absurd inside (by simp)) (fun _ inside => absurd inside (by simp))
      (by simp) loopOk
  · have empty := getValidatorsSweepWithdrawals_loop_outside (Nat.le_of_not_lt first) loopOk
    simp only at empty
    subst empty
    exact ⟨fun _ inside => absurd inside (by simp), by simp⟩

/-- For a registry within its limit, the sweep of validators comes last among the withdrawals.

It pays each validator it visits as `SweepPays` says, at most once. -/
theorem getExpectedWithdrawals_sweep {capella : .shapella ≤ fork}
    (within : state.RegistryWithinLimit) {expected : ExpectedWithdrawals}
    (computed : getExpectedWithdrawals state capella = .ok expected) :
    ∃ prior sweep, expected.withdrawals = prior ++ sweep ∧
      (∀ k (inside : k < sweep.size),
        SweepPays state (getCurrentEpoch state) (prior ++ sweep.extract 0 k) sweep[k]) ∧
      (sweep.toList.map (·.validatorIndex.toNat)).Nodup := by
  unfold getExpectedWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, ⟨sweep, _, _⟩, sweepOk, rfl⟩ := computed
  exact ⟨_, sweep, rfl, getValidatorsSweepWithdrawals_pays within sweepOk⟩

/-- The total of a validator over withdrawals that name each validator once.

It is the total over those before its own, plus its own amount. -/
private theorem withdrawnFrom_split {sweep : Array Withdrawal}
    (distinct : (sweep.toList.map (·.validatorIndex.toNat)).Nodup) {k : Nat}
    (inside : k < sweep.size) :
    withdrawnFrom sweep sweep[k].validatorIndex =
      withdrawnFrom (sweep.extract 0 k) sweep[k].validatorIndex + sweep[k].amount.toNat := by
  have insideList : k < sweep.toList.length := by simpa using inside
  have pieces : sweep.toList = sweep.toList.take k ++
      sweep.toList[k] :: sweep.toList.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons insideList, List.take_append_drop]
  -- No withdrawal after this one names the same validator.
  have later : ∀ other ∈ sweep.toList.drop (k + 1),
      other.validatorIndex ≠ sweep[k].validatorIndex := by
    intro other member same
    have whole : (sweep.toList.take (k + 1) ++ sweep.toList.drop (k + 1)).map
        (·.validatorIndex.toNat) |>.Nodup := by
      rw [List.take_append_drop]
      exact distinct
    rw [List.map_append, List.nodup_append] at whole
    refine whole.2.2 _ (List.mem_map_of_mem (List.getElem_mem (l := sweep.toList.take (k + 1))
      (n := k) (by simp; omega))) _ (List.mem_map_of_mem member) ?_
    simp [same]
  unfold withdrawnFrom
  rw [pieces]
  simp only [List.filter_append, List.filter_cons, Array.getElem_toList, decide_true,
    ↓reduceIte, List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  rw [List.filter_eq_nil_iff.mpr fun other member same => later other member
    (of_decide_eq_true same)]
  simp [Array.toList_extract, List.extract_eq_take_drop]

/-- A validator that the sweep pays withdraws, in all, its balance or its excess.

The excess is the part above its largest effective balance.

All its other withdrawals come before the sweep pays it. -/
theorem withdrawnFrom_of_sweepPays {epoch : Epoch} {prior sweep : Array Withdrawal}
    (pays : ∀ k (inside : k < sweep.size),
      SweepPays state epoch (prior ++ sweep.extract 0 k) sweep[k])
    (distinct : (sweep.toList.map (·.validatorIndex.toNat)).Nodup) {k : Nat}
    (inside : k < sweep.size) :
    ∃ validator balance left, getValidator state sweep[k].validatorIndex = .ok validator ∧
      state.balances.data[sweep[k].validatorIndex.toNat]? = some balance ∧
      getBalanceAfterWithdrawals state sweep[k].validatorIndex (prior ++ sweep.extract 0 k) =
        .ok left ∧
      ((isFullyWithdrawableValidator fork validator left epoch = true ∧
          withdrawnFrom (prior ++ sweep) sweep[k].validatorIndex = balance.toNat) ∨
        (isFullyWithdrawableValidator fork validator left epoch = false ∧
          isPartiallyWithdrawableValidator preset fork validator left = true ∧
          withdrawnFrom (prior ++ sweep) sweep[k].validatorIndex = balance.toNat -
            (withdrawalMaxEffectiveBalance preset fork validator).toNat ∧
          (withdrawalMaxEffectiveBalance preset fork validator).toNat < balance.toNat)) := by
  obtain ⟨validator, left, validatorOk, leftOk, kind⟩ := pays k inside
  obtain ⟨balance, found, sum⟩ := getBalanceAfterWithdrawals_ok leftOk
  -- The sweep pays no later withdrawal to this validator.
  have total : withdrawnFrom (prior ++ sweep) sweep[k].validatorIndex =
      withdrawnFrom (prior ++ sweep.extract 0 k) sweep[k].validatorIndex +
        sweep[k].amount.toNat := by
    rw [withdrawnFrom_append, withdrawnFrom_append, Nat.add_assoc]
    congr 1
    exact withdrawnFrom_split distinct inside
  refine ⟨validator, balance, left, validatorOk, found, leftOk, ?_⟩
  rcases kind with ⟨full, amount⟩ | ⟨notFull, excess, amount⟩
  · refine .inl ⟨full, ?_⟩
    rw [total, amount]
    omega
  · simp only [isPartiallyWithdrawableValidator, Bool.and_eq_true, decide_eq_true_eq]
      at excess
    have above := UInt64.lt_iff_toNat_lt.mp excess.2
    refine .inr ⟨notFull, ?_, ?_, by omega⟩
    · simp [isPartiallyWithdrawableValidator, excess.1.1, excess.1.2, excess.2]
    · rw [total, amount, UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt excess.2)]
      omega

/-- The withdrawals that the withdrawal step applies are unique. -/
theorem AppliedWithdrawals.unique {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    {first second : Array Withdrawal}
    (one : AppliedWithdrawals state after capella payload first)
    (two : AppliedWithdrawals state after capella payload second) : first = second := by
  by_cases gloas : .glamsterdam ≤ fork
  · cases full : isParentBlockFull state gloas
    · rw [(one.2 gloas).2 full, (two.2 gloas).2 full]
    · rw [(one.2 gloas).1 full, (two.2 gloas).1 full]
  · have before : fork < .glamsterdam := Nat.lt_of_not_le gloas
    rw [one.1 before, two.1 before]

/-- For a registry within its limit, the sweep leaves each validator it pays at a fixed balance.

The registry limit must be at most `2^40`.

A validator that the sweep pays in full ends the step at zero.

One that it pays partially ends at exactly its largest effective balance.

Whether it pays in full or partially is read from the balance left after the earlier withdrawals.

Those are the queued withdrawals and the earlier visits of the sweep. -/
theorem processWithdrawals_sweep {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    (within : state.RegistryWithinLimit) (limit : preset.VALIDATOR_REGISTRY_LIMIT.toNat ≤ 2 ^ 40) :
    ∃ prior sweep, AppliedWithdrawals state after capella payload (prior ++ sweep) ∧
      ∀ k (inside : k < sweep.size), ∃ validator left final,
        getValidator state sweep[k].validatorIndex = .ok validator ∧
        getBalanceAfterWithdrawals state sweep[k].validatorIndex (prior ++ sweep.extract 0 k) =
          .ok left ∧
        after.balances.data[sweep[k].validatorIndex.toNat]? = some final ∧
        ((isFullyWithdrawableValidator fork validator left (getCurrentEpoch state) = true ∧
            final = 0) ∨
          (isFullyWithdrawableValidator fork validator left (getCurrentEpoch state) = false ∧
            isPartiallyWithdrawableValidator preset fork validator left = true ∧
            final = withdrawalMaxEffectiveBalance preset fork validator)) := by
  obtain ⟨withdrawals, _, named, source, -⟩ := processWithdrawals_applied computed
  rcases source with rfl | ⟨expected, expectedOk, rfl⟩
  · exact ⟨#[], #[], by simpa using named, fun _ inside => absurd inside (by simp)⟩
  obtain ⟨prior, sweep, split, pays, distinct⟩ := getExpectedWithdrawals_sweep within expectedOk
  rw [split] at named
  refine ⟨prior, sweep, named, fun k inside => ?_⟩
  obtain ⟨validator, balance, left, validatorOk, found, leftOk, kind⟩ :=
    withdrawnFrom_of_sweepPays pays distinct inside
  have member : sweep[k].validatorIndex.toNat < state.validators.data.size := by
    simp only [getValidator] at validatorOk
    split at validatorOk
    · rename_i read
      exact (Array.getElem?_eq_some_iff.mp read).1
    · cases validatorOk
  obtain ⟨withdrawals, named', _, lowered⟩ :=
    processWithdrawals_balance_of_registry computed within limit member found
  obtain rfl := named'.unique named
  obtain ⟨final, finalFound, finalValue⟩ : ∃ final,
      after.balances.data[sweep[k].validatorIndex.toNat]? = some final ∧
        final.toNat = balance.toNat - withdrawnFrom (prior ++ sweep) sweep[k].validatorIndex := by
    cases read : after.balances.data[sweep[k].validatorIndex.toNat]? with
    | none => rw [read] at lowered; cases lowered
    | some final =>
      rw [read, Option.map_some, Option.some.injEq] at lowered
      exact ⟨final, rfl, lowered⟩
  refine ⟨validator, left, final, validatorOk, leftOk, finalFound, ?_⟩
  rcases kind with ⟨full, total⟩ | ⟨notFull, excess, total, above⟩
  · exact .inl ⟨full, UInt64.toNat_inj.mp (by rw [finalValue, total]; simp)⟩
  · exact .inr ⟨notFull, excess, UInt64.toNat_inj.mp (by rw [finalValue, total]; omega)⟩

/-! ## What a queued partial withdrawal pays -/

/-- What a queued partial withdrawal pays, after the withdrawals of the payload before it.

It is a withdrawable entry of the queue, for a validator still eligible.

It pays the balance left above the activation balance, or the amount asked if that is less. -/
def PartialPays (state : BeaconState preset fork) (epoch : Epoch)
    (queue : List PendingPartialWithdrawal) (before : Array Withdrawal)
    (withdrawal : Withdrawal) : Prop :=
  ∃ pending ∈ queue, ∃ validator left, pending.withdrawableEpoch ≤ epoch ∧
    withdrawal.validatorIndex = pending.validatorIndex ∧
    getValidator state pending.validatorIndex = .ok validator ∧
    getBalanceAfterWithdrawals state pending.validatorIndex before = .ok left ∧
    isEligibleForPartialWithdrawals preset validator left = true ∧
    withdrawal.amount = min (left - preset.MIN_ACTIVATION_BALANCE) pending.amount

/-- Each withdrawal of the loop of the queued partial withdrawals pays as `PartialPays` says. -/
theorem getPendingPartialWithdrawals_loop_pays {prior : Array Withdrawal} {epoch : Epoch}
    {limit : Nat} {whole : List PendingPartialWithdrawal} :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    (∀ pending ∈ queue, pending ∈ whole) →
    (∀ k (inside : k < withdrawals.size),
      PartialPays state epoch whole (prior ++ withdrawals.extract 0 k) withdrawals[k]) →
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    ∀ k (inside : k < result.1.size),
      PartialPays state epoch whole (prior ++ result.1.extract 0 k) result.1[k]
  | [], _, _, _, _, _, pays, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact pays
  | pending :: rest, withdrawals, next, _, _, within, pays, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact pays
    rename_i ready
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨validator, validatorOk, left, leftOk, computed⟩ := computed
    have rest' : ∀ other ∈ rest, other ∈ whole :=
      fun other member => within other (List.mem_cons_of_mem _ member)
    split at computed
    · rename_i eligible
      simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, loopOk⟩ := computed
      refine getPendingPartialWithdrawals_loop_pays rest _ _ _ rest' (fun k inside => ?_) loopOk
      simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at appendedOk
      obtain ⟨_, _, rfl, rfl⟩ := appendedOk
      simp only [Array.size_push] at inside
      by_cases old : k < withdrawals.size
      · rw [Array.getElem_push_lt old, Array.extract_push_of_le (by omega)]
        exact pays k old
      · obtain rfl : k = withdrawals.size := by omega
        rw [Array.getElem_push_eq, Array.extract_push_of_le (Nat.le_refl _),
          Array.extract_eq_self_of_le (Nat.le_refl _)]
        have ready' : pending.withdrawableEpoch ≤ epoch := by
          simp only [not_or, Nat.not_le] at ready
          exact UInt64.not_lt.mp ready.1
        exact ⟨pending, within pending List.mem_cons_self, validator, left, ready', rfl,
          validatorOk, leftOk, eligible, rfl⟩
    · exact getPendingPartialWithdrawals_loop_pays rest _ _ _ rest' pays computed

/-- From Electra, each queued partial withdrawal that a payload pays is as `PartialPays` says.

It comes from the queue of the state. -/
theorem getPendingPartialWithdrawals_pays {electra : .pectra ≤ fork} {start : WithdrawalIndex}
    {prior partials : Array Withdrawal} {next : WithdrawalIndex} {processed : Nat}
    (computed : getPendingPartialWithdrawals state electra start prior =
      .ok (partials, next, processed)) :
    ∀ k (inside : k < partials.size), PartialPays state (getCurrentEpoch state)
      (state.pendingPartialWithdrawals electra).data.toList (prior ++ partials.extract 0 k)
      partials[k] := by
  unfold getPendingPartialWithdrawals at computed
  simp only [bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, loopOk⟩ := computed
  exact getPendingPartialWithdrawals_loop_pays _ _ _ _ (fun _ member => member)
    (fun _ inside => absurd inside (by simp)) loopOk

/-! ## What the builders withdraw -/

/-- From Gloas, each queued builder withdrawal that a payload pays is one entry of the queue.

It pays the amount of that entry to its fee recipient, under the index that names its builder. -/
theorem getBuilderWithdrawals_loop_pays {prior : Array Withdrawal} {limit : UInt64}
    {whole : List BuilderPendingWithdrawal} :
    ∀ (queue : List BuilderPendingWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    (∀ pending ∈ queue, pending ∈ whole) →
    (∀ withdrawal ∈ withdrawals.toList, ∃ pending ∈ whole,
      withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex pending.builderIndex ∧
      withdrawal.address = pending.feeRecipient ∧ withdrawal.amount = pending.amount) →
    getBuilderWithdrawals.loop prior limit queue withdrawals next processed = .ok result →
    ∀ withdrawal ∈ result.1.toList, ∃ pending ∈ whole,
      withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex pending.builderIndex ∧
      withdrawal.address = pending.feeRecipient ∧ withdrawal.amount = pending.amount
  | [], _, _, _, _, _, pays, computed => by
    simp only [getBuilderWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact pays
  | pending :: rest, _, _, _, _, within, pays, computed => by
    simp only [getBuilderWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact pays
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, loopOk⟩ := computed
      refine getBuilderWithdrawals_loop_pays rest _ _ _
        (fun other member => within other (List.mem_cons_of_mem _ member))
        (fun withdrawal member => ?_) loopOk
      simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at appendedOk
      obtain ⟨_, _, rfl, rfl⟩ := appendedOk
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact pays withdrawal member
      · exact ⟨pending, within pending List.mem_cons_self, rfl, rfl, rfl⟩

/-- What the sweep of builders pays one builder, after the withdrawals of the payload before it.

The builder is withdrawable, and it withdraws all of its balance left, which is not zero. -/
def BuilderSweepPays (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork)
    (epoch : Epoch) (before : Array Withdrawal) (withdrawal : Withdrawal) : Prop :=
  ∃ index builder left, withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex index ∧
    getBuilder state gloas index = .ok builder ∧
    getBuilderBalanceAfterWithdrawals state gloas index before = .ok left ∧
    builder.withdrawableEpoch ≤ epoch ∧ 0 < left ∧ withdrawal.amount = left

/-- From Gloas, each withdrawal of the sweep of builders pays as `BuilderSweepPays` says. -/
theorem getBuildersSweepWithdrawals_loop_pays {gloas : .glamsterdam ≤ fork}
    {prior : Array Withdrawal} {epoch : Epoch} {count : Nat} {limit : UInt64} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : BuilderIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    (∀ k (inside : k < withdrawals.size),
      BuilderSweepPays state gloas epoch (prior ++ withdrawals.extract 0 k) withdrawals[k]) →
    getBuildersSweepWithdrawals.loop state gloas prior epoch count limit visits withdrawals next
      index processed = .ok result →
    ∀ k (inside : k < result.1.size),
      BuilderSweepPays state gloas epoch (prior ++ result.1.extract 0 k) result.1[k]
  | 0, _, _, _, _, _, pays, computed => by
    simp only [getBuildersSweepWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact pays
  | visits + 1, withdrawals, next, index, _, _, pays, computed => by
    simp only [getBuildersSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact pays
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨builder, builderOk, left, leftOk, computed⟩ := computed
    split at computed
    · rename_i paid
      simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, _, _, loopOk⟩ := computed
      refine getBuildersSweepWithdrawals_loop_pays visits _ _ _ _ (fun k inside => ?_) loopOk
      simp only [appendWithdrawal, bind_ok_iff, pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at appendedOk
      obtain ⟨_, _, rfl, rfl⟩ := appendedOk
      simp only [Array.size_push] at inside
      by_cases old : k < withdrawals.size
      · rw [Array.getElem_push_lt old, Array.extract_push_of_le (by omega)]
        exact pays k old
      · obtain rfl : k = withdrawals.size := by omega
        rw [Array.getElem_push_eq, Array.extract_push_of_le (Nat.le_refl _),
          Array.extract_eq_self_of_le (Nat.le_refl _)]
        exact ⟨index, builder, left, rfl, builderOk, leftOk, paid.1, paid.2, rfl⟩
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at computed
      obtain ⟨_, _, loopOk⟩ := computed
      exact getBuildersSweepWithdrawals_loop_pays visits _ _ _ _ pays loopOk

/-! ## Every withdrawal of a payload -/

/-- For a registry within its limit, every expected withdrawal, part by part, in payload order.

From Gloas, the queued builder withdrawals come first, each an entry of the queue.

From Electra, the queued partial withdrawals follow, each as `PartialPays` says.

From Gloas, the sweep of builders follows, each as `BuilderSweepPays` says.

The sweep of validators comes last, each as `SweepPays` says, at most once per validator.

Each part reads the balances left after the parts and withdrawals before it. -/
theorem getExpectedWithdrawals_parts {capella : .shapella ≤ fork}
    (within : state.RegistryWithinLimit) {expected : ExpectedWithdrawals}
    (computed : getExpectedWithdrawals state capella = .ok expected) :
    ∃ builders partials buildersSweep sweep,
      expected.withdrawals = builders ++ partials ++ buildersSweep ++ sweep ∧
      (fork < .glamsterdam → builders = #[] ∧ buildersSweep = #[]) ∧
      (fork < .pectra → partials = #[]) ∧
      (∀ gloas : .glamsterdam ≤ fork, ∀ withdrawal ∈ builders.toList,
        ∃ pending ∈ (state.builderPendingWithdrawals gloas).data.toList,
          withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex pending.builderIndex ∧
          withdrawal.address = pending.feeRecipient ∧ withdrawal.amount = pending.amount) ∧
      (∀ electra : .pectra ≤ fork, ∀ k (inside : k < partials.size),
        PartialPays state (getCurrentEpoch state)
          (state.pendingPartialWithdrawals electra).data.toList
          (builders ++ partials.extract 0 k) partials[k]) ∧
      (∀ gloas : .glamsterdam ≤ fork, ∀ k (inside : k < buildersSweep.size),
        BuilderSweepPays state gloas (getCurrentEpoch state)
          (builders ++ partials ++ buildersSweep.extract 0 k) buildersSweep[k]) ∧
      (∀ k (inside : k < sweep.size), SweepPays state (getCurrentEpoch state)
        (builders ++ partials ++ buildersSweep ++ sweep.extract 0 k) sweep[k]) ∧
      (sweep.toList.map (·.validatorIndex.toNat)).Nodup := by
  unfold getExpectedWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨⟨builders, index1, _⟩, buildersOk, ⟨partials, index2, _⟩, partialsOk,
    ⟨buildersSweep, index3, _⟩, buildersSweepOk, ⟨sweep, index4, _⟩, sweepOk, rfl⟩ := computed
  obtain ⟨paysSweep, distinct⟩ := getValidatorsSweepWithdrawals_pays within sweepOk
  refine ⟨builders, partials, buildersSweep, sweep, rfl, fun before => ⟨?_, ?_⟩,
    fun before => ?_, fun gloas => ?_, fun electra => ?_, fun gloas => ?_, paysSweep, distinct⟩
  · have outside : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
    simp only [outside, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at buildersOk
    exact buildersOk.1.symm
  · have outside : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
    simp only [outside, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at buildersSweepOk
    exact buildersSweepOk.1.symm
  · have outside : ¬ .pectra ≤ fork := Nat.not_le_of_lt before
    simp only [outside, ↓reduceDIte, Except.ok.injEq, Prod.mk.injEq] at partialsOk
    exact partialsOk.1.symm
  · simp only [gloas, ↓reduceDIte] at buildersOk
    unfold getBuilderWithdrawals at buildersOk
    simp only [bind_ok_iff, ensure_ok_iff] at buildersOk
    obtain ⟨_, _, _, _, loopOk⟩ := buildersOk
    exact getBuilderWithdrawals_loop_pays _ _ _ _ (fun _ member => member)
      (fun _ absent => absurd absent (by simp)) loopOk
  · simp only [electra, ↓reduceDIte] at partialsOk
    exact getPendingPartialWithdrawals_pays partialsOk
  · simp only [gloas, ↓reduceDIte] at buildersSweepOk
    unfold getBuildersSweepWithdrawals at buildersSweepOk
    simp only [bind_ok_iff, ensure_ok_iff] at buildersSweepOk
    obtain ⟨_, _, _, _, loopOk⟩ := buildersSweepOk
    exact getBuildersSweepWithdrawals_loop_pays _ _ _ _ _
      (fun _ inside => absurd inside (by simp)) loopOk

end EthLib.Consensus
