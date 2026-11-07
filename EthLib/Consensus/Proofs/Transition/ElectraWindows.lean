module

public import EthLib.Consensus.Proofs.Transition.EffectiveBalanceCap
public import EthLib.Consensus.Proofs.Transition.ExitStake
public import EthLib.Consensus.Proofs.Transition.Lifecycle
public import EthLib.Consensus.Proofs.WeakSubjectivity

/-!
# Proofs: the stake that leaves the active set over a range of epochs, from Electra

From Electra the weak subjectivity period has a closed form.

It assumes that each epoch of the period moves at most the balance churn of the first state.

Take a reachable state from Electra, and a later state that a run reaches from it, before Gloas.

The stake that leaves the active set between their current epochs is at most three parts.

- The stake that the first state has already queued to exit by the last epoch.
- One cap of exits and one of consolidations for each epoch from the first exit epoch on.
- The effective balance that a validator lost before its exit spent churn.

The cap of exits is `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT`.

The cap of consolidations comes from a bound on the total active balance of every state of the run.

The closed form uses the churn of the first state instead, which differs in three ways.

- The churn grows with the total active balance, so a later epoch may take more.
- An exit queued before the first state may spend churn of epochs in the range.
- The churn counts the balance that an exit spends, not the stake that leaves later.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-! ## The states of a run -/

/-- Each state that a run passes through is reached from its start. -/
theorem Run.reaches_of_mem_states {start : ForkedBeaconState preset} :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      ∀ forked ∈ run.states, Reaches config checks start forked
  | _, .nil, forked, member => by
    rw [List.mem_singleton.mp member]
    exact .refl _
  | _, .snoc run step, forked, member => by
    rcases List.mem_append.mp member with earlier | now
    · exact Run.reaches_of_mem_states run forked earlier
    · rw [List.mem_singleton.mp now]
      exact ⟨.snoc run step⟩

/-- Each state that a run passes through is of a fork no later than its end. -/
theorem Run.fork_le_of_mem_states {start : ForkedBeaconState preset} :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      ∀ forked ∈ run.states, forked.fork ≤ after.fork
  | _, .nil, forked, member => by
    rw [List.mem_singleton.mp member]
    exact Nat.le_refl _
  | _, .snoc run step, forked, member => by
    have last := Run.fork_le (Run.snoc .nil step)
    rcases List.mem_append.mp member with earlier | now
    · exact Nat.le_trans (Run.fork_le_of_mem_states run forked earlier) last
    · rw [List.mem_singleton.mp now]
      exact Nat.le_refl _

/-! ## The stake that leaves -/

/-- The churn of consolidations that a bound on the total active balance gives, before Gloas. -/
def consolidationCap (config : Config) (total : Nat) : Nat :=
  max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat (total / config.CHURN_LIMIT_QUOTIENT.toNat)

/-- The stake that leaves the active set over a run from a reachable state.

The run is from Electra on and before Gloas.

The total active balance of every state of the run must be at most `total`.

The churn of consolidations left at the start must be within the cap that `total` gives.

The last epoch must be at least the first one and below the far future epoch. -/
theorem Run.leavingStake_le_caps {start after : ForkedBeaconState preset}
    (caps : EffectiveBalanceCaps preset) (reachable : Reachable config checks start)
    (electra : .pectra ≤ start.fork) (beforeGloas : after.fork < .glamsterdam)
    (run : Run config checks start after)
    (epochs : getCurrentEpoch start.state ≤ getCurrentEpoch after.state)
    (finite : getCurrentEpoch after.state < FAR_FUTURE_EPOCH) {total : Nat}
    (totals : ∀ forked ∈ run.states, ∀ balance,
      getTotalActiveBalance forked.state = .ok balance → balance.toNat ≤ total)
    (consolidationLeft : ∀ electra : .pectra ≤ start.fork,
      (start.state.consolidationBalanceToConsume electra).toNat ≤ consolidationCap config total) :
    (((List.range start.state.validators.data.size).filter fun position =>
        (start.state.validators.data[position]?).any
            (isActiveValidator · (getCurrentEpoch start.state)) &&
          !(after.state.validators.data[position]?).any
            (isActiveValidator · (getCurrentEpoch after.state))).map
        fun position => effectiveBalanceAtPosition start.state position).sum ≤
      (((List.range start.state.validators.data.size).filter fun position =>
          (start.state.validators.data[position]?).any fun validator =>
            isActiveValidator validator (getCurrentEpoch start.state) &&
              decide (validator.exitEpoch ≤ getCurrentEpoch after.state)).map
          fun position => effectiveBalanceAtPosition start.state position).sum +
        ((getCurrentEpoch after.state).toNat + 1 - firstExitEpoch preset start.state) *
          (config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat +
            consolidationCap config total) +
        ∑ position ∈ exitsBetween start.state after.state 0 (getCurrentEpoch after.state).toNat,
          (effectiveBalanceAtPosition start.state position - run.chargedBalance position) := by
  have small : after.state.validators.data.size < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (after.state.validators.bound beforeGloas) (UInt64.toNat_lt _)
  have lifecycle := (Reaches.registryLifecycle ⟨run⟩ :
    RegistryLifecycle start.state after.state)
  -- A validator active at the start keeps its activation epoch, which was set.
  have kept : ∀ (position : Nat) (validator later : Validator),
      start.state.validators.data[position]? = some validator →
        after.state.validators.data[position]? = some later →
        isActiveValidator validator (getCurrentEpoch start.state) = true →
          later.activationEpoch = validator.activationEpoch := by
    intro position validator later found laterFound active
    obtain ⟨kept, keptFound, step⟩ := lifecycle.validators small position validator found
    rw [laterFound] at keptFound
    cases keptFound
    refine step.activationEpoch fun far => ?_
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, far] at active
    exact absurd (UInt64.lt_of_le_of_lt active.1 active.2)
      (UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr (by
        have := UInt64.toNat_lt validator.exitEpoch
        rw [show FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 from rfl]
        omega)))
  have leaving := Run.leavingStake_le electra run small epochs finite kept
  -- Every state of the run is reachable, from Electra and before Gloas, with capped churns.
  have churns : ∀ forked ∈ run.states, ChurnsBounded config
      config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat (consolidationCap config total)
      preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat forked := by
    intro forked member electraHere
    have before := Nat.lt_of_le_of_lt (Run.fork_le_of_mem_states run forked member) beforeGloas
    have here := ReachableFrom.reaches reachable (Run.reaches_of_mem_states run forked member)
    refine ⟨fun churn churnOk => UInt64.le_iff_toNat_le.mp (exitChurnLimit_le_of_lt before churnOk),
      fun churn churnOk => ?_, fun position validator found => ?_⟩
    · cases balanceOk : getTotalActiveBalance forked.state with
      | error fault =>
        simp [getConsolidationChurnLimit, getBalanceChurnLimit, balanceOk, bind,
          Except.bind] at churnOk
      | ok balance =>
        have bound := getConsolidationChurnLimit_le_total balanceOk churnOk
        have notGloas : ¬Base.Fork.glamsterdam ≤ forked.fork := Nat.not_le_of_lt before
        simp only [notGloas, ↓reduceIte] at bound
        have totalLe := totals forked member balance balanceOk
        exact Nat.le_trans bound (Nat.max_le.mpr ⟨Nat.le_max_left _ _,
          Nat.le_trans (Nat.div_le_div_right totalLe) (Nat.le_max_right _ _)⟩)
    · exact UInt64.le_iff_toNat_le.mp ((Reachable.effectiveBalancesCapped caps here).le_max_electra
        caps electraHere (Array.mem_of_getElem? found))
  have lefts : LeftBounded config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
      (consolidationCap config total) start := fun electra' =>
    ⟨UInt64.le_iff_toNat_le.mp (reachable.exitBalanceToConsume_le electra'
        (Nat.lt_of_le_of_lt (Run.fork_le run) beforeGloas)),
      consolidationLeft electra'⟩
  have exiting := Run.exitingStake_le electra run small churns lefts
    (getCurrentEpoch after.state).toNat
  omega

/-- Within some epochs of the first state, the range of exit epochs has at most that many epochs.

Its first epoch is after the current epoch of the first state. -/
theorem firstExitEpoch_range_le {fork fork' : Base.Fork} {state : BeaconState preset fork}
    {after : BeaconState preset fork'} {epochs : Nat}
    (within : (getCurrentEpoch after).toNat ≤ (getCurrentEpoch state).toNat + epochs) :
    (getCurrentEpoch after).toNat + 1 - firstExitEpoch preset state ≤ epochs := by
  unfold firstExitEpoch
  omega

/-! ## The churn of the first state does not bound the range

The closed form takes the balance churn of the first state for every epoch of the period.

The churn of a later state grows with its total active balance.

On mainnet, `2^23` ether of total active balance gives a churn of 128 ether.

The closed form then gives a period of 3532 epochs, 3276 of them for the churn.

Deposits may take up to 256 ether of churn per epoch.

After 256 such epochs the total is `2^23 + 2^16` ether, and the churn is 129 ether.

So later epochs of the period may each move more than the first state's churn.

These theorems give the exact values; they do not build a chain that reaches such states.
-/

/-- The balance churn of a mainnet state, from its total active balance. -/
theorem getBalanceChurnLimit_mainnet {fork : Base.Fork}
    {state : BeaconState Preset.mainnet fork} {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total) :
    getBalanceChurnLimit Config.mainnet state =
      .ok (roundToIncrement Preset.mainnet
        (max Config.mainnet.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
          (total / Config.mainnet.CHURN_LIMIT_QUOTIENT))) := by
  simp [getBalanceChurnLimit, totalOk, bind, Except.bind, pure, Except.pure]

/-- On mainnet, `2^23` ether of total active balance gives 128 ether of churn.

`2^23 + 2^16` ether gives 129. -/
theorem getBalanceChurnLimit_mainnet_values :
    roundToIncrement Preset.mainnet (max Config.mainnet.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        ((2 ^ 23 * 10 ^ 9 : Gwei) / Config.mainnet.CHURN_LIMIT_QUOTIENT)) = 128 * 10 ^ 9 ∧
      roundToIncrement Preset.mainnet (max Config.mainnet.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (((2 ^ 23 + 2 ^ 16) * 10 ^ 9 : Gwei) / Config.mainnet.CHURN_LIMIT_QUOTIENT)) =
        129 * 10 ^ 9 := by
  decide

/-- On mainnet, a churn of 128 ether on `2^23` ether gives a period of 3532 epochs. -/
theorem balanceChurnPeriod_mainnet_value :
    balanceChurnPeriod Config.mainnet.MIN_VALIDATOR_WITHDRAWABILITY_DELAY (2 ^ 23 * 10 ^ 9)
      (128 * 10 ^ 9) = .ok 3532 := by
  rw [balanceChurnPeriod_eq_ok_iff]
  decide

/-! ## From Gloas

From Gloas the registry has no limit, and the churns change.

- The churn of exits is a share of the total active balance, with no maximum.
- The churn of consolidations is its own share of the total active balance.
- Neither carry at the start is within the churn of the state, so both are hypotheses.

The registry must have fewer than `2^64` validators, since a new validator's index wraps there.
-/

/-- The churn of exits that a bound on the total active balance gives, at every fork from Electra.
-/
def exitCapAll (config : Config) (total : Nat) : Nat :=
  max config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT.toNat
    (max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
      (total / config.CHURN_LIMIT_QUOTIENT_GLOAS.toNat))

/-- The churn of consolidations that a bound on the total active balance gives, from Electra. -/
def consolidationCapAll (config : Config) (total : Nat) : Nat :=
  max (total / config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat) (consolidationCap config total)

/-- The stake that leaves the active set over a run from a reachable state, from Electra on.

The run may cross into Gloas and later forks.

The registry at the end must have fewer than `2^64` validators.

The total active balance of every state of the run must be at most `total`.

Both carries at the start must be within the caps that `total` gives. -/
theorem Run.leavingStake_le_capsAll {start after : ForkedBeaconState preset}
    (caps : EffectiveBalanceCaps preset) (reachable : Reachable config checks start)
    (electra : .pectra ≤ start.fork) (run : Run config checks start after)
    (small : after.state.validators.data.size < 2 ^ 64)
    (epochs : getCurrentEpoch start.state ≤ getCurrentEpoch after.state)
    (finite : getCurrentEpoch after.state < FAR_FUTURE_EPOCH) {total : Nat}
    (totals : ∀ forked ∈ run.states, ∀ balance,
      getTotalActiveBalance forked.state = .ok balance → balance.toNat ≤ total)
    (lefts : LeftBounded (exitCapAll config total) (consolidationCapAll config total) start) :
    (((List.range start.state.validators.data.size).filter fun position =>
        (start.state.validators.data[position]?).any
            (isActiveValidator · (getCurrentEpoch start.state)) &&
          !(after.state.validators.data[position]?).any
            (isActiveValidator · (getCurrentEpoch after.state))).map
        fun position => effectiveBalanceAtPosition start.state position).sum ≤
      (((List.range start.state.validators.data.size).filter fun position =>
          (start.state.validators.data[position]?).any fun validator =>
            isActiveValidator validator (getCurrentEpoch start.state) &&
              decide (validator.exitEpoch ≤ getCurrentEpoch after.state)).map
          fun position => effectiveBalanceAtPosition start.state position).sum +
        ((getCurrentEpoch after.state).toNat + 1 - firstExitEpoch preset start.state) *
          (exitCapAll config total + consolidationCapAll config total) +
        ∑ position ∈ exitsBetween start.state after.state 0 (getCurrentEpoch after.state).toNat,
          (effectiveBalanceAtPosition start.state position - run.chargedBalance position) := by
  have lifecycle := (Reaches.registryLifecycle ⟨run⟩ :
    RegistryLifecycle start.state after.state)
  have kept : ∀ (position : Nat) (validator later : Validator),
      start.state.validators.data[position]? = some validator →
        after.state.validators.data[position]? = some later →
        isActiveValidator validator (getCurrentEpoch start.state) = true →
          later.activationEpoch = validator.activationEpoch := by
    intro position validator later found laterFound active
    obtain ⟨kept, keptFound, step⟩ := lifecycle.validators small position validator found
    rw [laterFound] at keptFound
    cases keptFound
    refine step.activationEpoch fun far => ?_
    simp only [isActiveValidator, Bool.and_eq_true, decide_eq_true_eq, far] at active
    exact absurd (UInt64.lt_of_le_of_lt active.1 active.2)
      (UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr (by
        have := UInt64.toNat_lt validator.exitEpoch
        rw [show FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 from rfl]
        omega)))
  have leaving := Run.leavingStake_le electra run small epochs finite kept
  have churns : ∀ forked ∈ run.states, ChurnsBounded config (exitCapAll config total)
      (consolidationCapAll config total) preset.MAX_EFFECTIVE_BALANCE_ELECTRA.toNat forked := by
    intro forked member electraHere
    have here := ReachableFrom.reaches reachable (Run.reaches_of_mem_states run forked member)
    refine ⟨fun churn churnOk => ?_, fun churn churnOk => ?_, fun position validator found => ?_⟩
    · cases balanceOk : getTotalActiveBalance forked.state with
      | error fault =>
        unfold exitChurnLimit at churnOk
        split at churnOk <;>
          simp [getExitChurnLimit, getActivationExitChurnLimit, getBalanceChurnLimit, balanceOk,
            bind, Except.bind] at churnOk
      | ok balance =>
        have totalLe := totals forked member balance balanceOk
        by_cases gloas : Base.Fork.glamsterdam ≤ forked.fork
        · have bound := exitChurnLimit_le_total balanceOk churnOk
          simp only [gloas, ↓reduceIte] at bound
          refine Nat.le_trans bound (Nat.le_trans ?_ (Nat.le_max_right _ _))
          exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
            Nat.le_trans (Nat.div_le_div_right totalLe) (Nat.le_max_right _ _)⟩
        · exact Nat.le_trans (UInt64.le_iff_toNat_le.mp
            (exitChurnLimit_le_of_lt (Nat.lt_of_not_le gloas) churnOk)) (Nat.le_max_left _ _)
    · cases balanceOk : getTotalActiveBalance forked.state with
      | error fault =>
        simp only [getConsolidationChurnLimit] at churnOk
        split at churnOk <;>
          simp [getBalanceChurnLimit, balanceOk, bind, Except.bind] at churnOk
      | ok balance =>
        have totalLe := totals forked member balance balanceOk
        have bound := getConsolidationChurnLimit_le_total balanceOk churnOk
        by_cases gloas : Base.Fork.glamsterdam ≤ forked.fork
        · simp only [gloas, ↓reduceIte] at bound
          exact Nat.le_trans bound
            (Nat.le_trans (Nat.div_le_div_right totalLe) (Nat.le_max_left _ _))
        · simp only [gloas, ↓reduceIte] at bound
          refine Nat.le_trans bound (Nat.le_trans ?_ (Nat.le_max_right _ _))
          exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
            Nat.le_trans (Nat.div_le_div_right totalLe) (Nat.le_max_right _ _)⟩
    · exact UInt64.le_iff_toNat_le.mp ((Reachable.effectiveBalancesCapped caps here).le_max_electra
        caps electraHere (Array.mem_of_getElem? found))
  have exiting := Run.exitingStake_le electra run small churns lefts
    (getCurrentEpoch after.state).toNat
  omega

/-- From Gloas, with `2^64` validators, the index for a new validator is that of the first one.

So a deposit to a new key then replaces the first validator, and the registry keeps its size.

The facts on the registry therefore hold only below `2^64` validators. -/
theorem addValidatorToRegistry_replaces_first {fork : Base.Fork}
    {state after : BeaconState preset fork} (gloas : .glamsterdam ≤ fork)
    {pubkey : Cryptography.Bls.BLSPubkey} {withdrawalCredentials : Bytes32} {amount : Gwei}
    (full : state.validators.data.size = 2 ^ 64)
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    after.validators.data[0]? =
      some (getValidatorFromDeposit preset fork pubkey withdrawalCredentials amount) := by
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  have index : getIndexForNewValidator state = 0 := by
    rw [getIndexForNewValidator, full]
    rfl
  unfold addValidatorToRegistry at computed
  simp only [altair, ↓reduceDIte] at computed
  unfold addValidatorToRegistryAltair at computed
  simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨validators, validatorsOk, _, _, _, _, _, _, _, _, rfl⟩ := computed
  rw [index] at validatorsOk
  simpa using setOrAppendRooted_getElem? validatorsOk 0

/-- The churns of a Gloas mainnet state, from its total active balance. -/
theorem gloasChurns_mainnet {fork : Base.Fork} {state : BeaconState Preset.mainnet fork}
    (gloas : .glamsterdam ≤ fork) {total : Gwei}
    (totalOk : getTotalActiveBalance state = .ok total) :
    getExitChurnLimit Config.mainnet state =
        .ok (roundToIncrement Preset.mainnet (max Config.mainnet.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
          (total / Config.mainnet.CHURN_LIMIT_QUOTIENT_GLOAS))) ∧
      getActivationChurnLimit Config.mainnet state =
        .ok (min Config.mainnet.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS
          (roundToIncrement Preset.mainnet (max Config.mainnet.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
            (total / Config.mainnet.CHURN_LIMIT_QUOTIENT_GLOAS)))) ∧
      getConsolidationChurnLimit Config.mainnet state =
        .ok (roundToIncrement Preset.mainnet
          (total / Config.mainnet.CONSOLIDATION_CHURN_LIMIT_QUOTIENT)) := by
  simp [getExitChurnLimit, getActivationChurnLimit, getConsolidationChurnLimit, gloas, totalOk,
    bind, Except.bind, pure, Except.pure]

/-- Take a Gloas mainnet state with `2^23` ether of total active balance.

Its churns are 256 ether of exits, 256 of activations and 128 of consolidations.

The weighted churn is about 384 ether, and the period is 1348 epochs.

Exits and consolidations alone may then take 384 ether per epoch, the whole weighted churn.

Activations may take 256 ether more. -/
theorem gloasPeriod_mainnet_value {fork : Base.Fork} {state : BeaconState Preset.mainnet fork}
    (gloas : .glamsterdam ≤ fork) (totalOk : getTotalActiveBalance state = .ok (2 ^ 23 * 10 ^ 9)) :
    getExitChurnLimit Config.mainnet state = .ok (256 * 10 ^ 9) ∧
      getActivationChurnLimit Config.mainnet state = .ok (256 * 10 ^ 9) ∧
      getConsolidationChurnLimit Config.mainnet state = .ok (128 * 10 ^ 9) ∧
      computeWeakSubjectivityPeriodGloas Config.mainnet state = .ok 1348 := by
  obtain ⟨exitOk, activationOk, consolidationOk⟩ := gloasChurns_mainnet gloas totalOk
  have exitValue : roundToIncrement Preset.mainnet
      (max Config.mainnet.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        ((2 ^ 23 * 10 ^ 9 : Gwei) / Config.mainnet.CHURN_LIMIT_QUOTIENT_GLOAS)) = 256 * 10 ^ 9 := by
    decide
  have activationValue : min Config.mainnet.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS
      (256 * 10 ^ 9 : Gwei) = 256 * 10 ^ 9 := by
    decide
  have consolidationValue : roundToIncrement Preset.mainnet
      ((2 ^ 23 * 10 ^ 9 : Gwei) / Config.mainnet.CONSOLIDATION_CHURN_LIMIT_QUOTIENT) =
        128 * 10 ^ 9 := by
    decide
  rw [exitValue] at exitOk
  rw [exitValue, activationValue] at activationOk
  rw [consolidationValue] at consolidationOk
  refine ⟨exitOk, activationOk, consolidationOk, ?_⟩
  rw [computeWeakSubjectivityPeriodGloas_eq_ok_iff]
  refine ⟨_, 383999999999, totalOk, ?_, ?_⟩
  · rw [gloasWeightedChurn_eq_ok_iff]
    exact ⟨_, _, _, exitOk, activationOk, consolidationOk, by decide, by decide, by decide⟩
  · rw [balanceChurnPeriod_eq_ok_iff]
    decide

/-- On Gloas mainnet the churn of exits grows with the total active balance and has no maximum.

`2^23` ether gives 256 ether, and `2^23 + 2^15` ether gives 257. -/
theorem gloasExitChurn_mainnet_values :
    roundToIncrement Preset.mainnet (max Config.mainnet.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        ((2 ^ 23 * 10 ^ 9 : Gwei) / Config.mainnet.CHURN_LIMIT_QUOTIENT_GLOAS)) = 256 * 10 ^ 9 ∧
      roundToIncrement Preset.mainnet (max Config.mainnet.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
        (((2 ^ 23 + 2 ^ 15) * 10 ^ 9 : Gwei) / Config.mainnet.CHURN_LIMIT_QUOTIENT_GLOAS)) =
        257 * 10 ^ 9 := by
  decide

end EthLib.Consensus
