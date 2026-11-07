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

end EthLib.Consensus
