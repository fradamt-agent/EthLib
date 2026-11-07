# Phase 0 safety: parallel handoff

## Delivery state

The full safety theorem and d(N) corollary are not proved.

The clean, buildable handoff is branch `proof/phase0-finality-drift`, commit `d3f6c44a414b3190dee63bff6aadabba6b2b6ff2`.

It is pushed only to `fradamt-agent/EthLib`.

Branch: https://github.com/fradamt-agent/EthLib/tree/proof/phase0-finality-drift

Commit: https://github.com/fradamt-agent/EthLib/commit/d3f6c44a414b3190dee63bff6aadabba6b2b6ff2

No PR was opened and nothing was pushed to `ethereum/EthLib`.

The latest commit proves distinct paid attester indices, actual payment-call provenance, effective-balance preservation through slashing, disjoint proposer/attester payments within a block, and distinct newly set flags across validated chains.

The chain-wide flag recorder is not yet a complete credit ledger.

In particular, completeness of the payment collector must be proved, not obtained by choosing an empty list.

## Interface convention and ownership

The accompanying `/tmp/ffg-parallel-interfaces.lean` contains complete proposed definitions and target propositions.

`lake env lean /tmp/ffg-parallel-interfaces.lean` succeeds at this commit.

These are elaborated propositions, not theorems, axioms, or proof stubs.

The theorem declarations below name those fully expanded propositions.

Every hypothesis is inside the named proposition and is written out in the accompanying file.

Adopt the namespace `EthLib.Consensus.Phase0SafetyPlan` provisionally, or rename it consistently before parallel work starts.

One coordinator must first install the reviewed concrete definitions in `EthLib/Consensus/Proofs/Transition/Finality/Definitions.lean`.

Do not install the unproved target propositions as axioms or add placeholder theorem bodies.

The helpers record spec executions and use spec checkpoints and attestation data.

They define no replacement FFG model.

Only the coordinator changes the proof-root imports.

Each worker owns the new file named below and imports the shared definitions.

Before pushing, fetch and fast-forward the shared branch, or rebase local unpushed commits on its updated head.

Never rewrite shared history.

### Required interface review

The old `/tmp/ffg-direct-statement.lean` is superseded and must not be used as an agreed contract.

The accompanying interface fixes its inclusion witness: the indexed attestation must be computed at the actual successful attestation-processing site.

Registry alignment preserves activation epochs only for validators already active in C.

Preserving activation epochs for every registry entry would be false, since inactive entries can activate later.

The proposed observation list contains block input and output states, every intermediate slot input, and each successful slot cache.

For exact loss accounting, prove that these contain every possible effective-balance minimum, or extend the collector to include the post-effective-balance-update epoch state explicitly.

Other epoch steps preserve effective balance, so this is an execution-composition obligation, not a penalty assumption.

The collision pool includes SSZ messages from observed states, latest headers, actual blocks and bodies.

The ancestry worker must prove that every binding reduction's messages belong to this pool, extending the actual-site collector if necessary.

Genesis checkpoints use a zero sentinel rather than a block root.

`Conflicting` in the proposal treats genesis as non-conflicting by definition, and uses parent-root reachability only for non-genesis checkpoints.

Prove that this interpretation agrees with checkpoint ancestry before exposing the final theorem.

Do not treat the raw zero sentinel as an ordinary unrelated block root.

## A. Root ancestry, first crossing and suffix-only evidence

File: `EthLib/Consensus/Proofs/Transition/Finality/Ancestry.lean`.

Size: large, approximately 1,000–2,000 proof lines, with substantial uncertainty around the zero-state-root sentinel.

Start: after the coordinator freezes the shared execution and collision collectors.

Independent of registry drift, churn and slashing budgets.

```lean
theorem conflicting_finalizations_evidence :
    conflicting_finalizations_evidence_statement (p := p)
```

The proposition quantifies over config, checks, execution engine, initialized genesis, C, both terminal states, common blocks and both suffixes.

Its hypotheses are successful initialization, successful common and suffix executions, conflicting terminal finalizations, positive `MIN_SEED_LOOKAHEAD`, and `MIN_SEED_LOOKAHEAD + 3 < EPOCHS_PER_HISTORICAL_VECTOR` in natural numbers.

Its conclusion supplies two concrete observed cached states, actual matching-target queries, actual unslashed index queries, their raw floor-corrected thresholds, target epochs above epoch(C), and suffix-only slashable evidence for every common index, OR a successful explicit SHA-256 collision search.

The first crossing and finalization cases belong together here, so a worker cannot silently assume the surround inequalities or source-root inequality.

Dependencies already proved:

- `checkpoint_origin_of_initialized_chain`
- `checkpoint_threshold_of_initialized_chain`
- `finalized_source_threshold_of_initialized_chain`
- `finalized_source_signers_of_initialized_chain`
- `finalized_source_signers_after_common`
- `justifiedCrossing_of_initialized_chain`
- `changedJustifications_surround`
- `currentJustifications_double_vote`
- `pending_inclusion_after_common_of_target_gt`
- `PendingIncludedInBlock.target_epoch_le`
- `stateTransition_chain_readBlockRoot_at_slot`
- `stateTransition_chain_readBlockRoot_slot_le_or_collision`
- `cached_checkpoint_epoch_after_common_or_collision`
- `BeaconBlock.hashTreeRoot_header`
- `beaconBlockHeader_root_binding`
- `processBlockHeader_parent_binding`
- `findMessageCollision_valid`

Never assume nonzero state roots or hash injectivity.

The inherited previous bit must retain its original stored source.

## B. Registry identity and stake alignment

File: `EthLib/Consensus/Proofs/Transition/Finality/Registry.lean`.

Size: medium-large, approximately 500–1,000 proof lines.

Start now from the pushed commit, independently of A, C and D.

```lean
theorem validator_alignment : validator_alignment_statement (p := p)
```

This takes an invariant C and a successful suffix execution.

It concludes nondecreasing registry size and, for every successful original index lookup, a later successful lookup with the same pubkey and credentials.

For validators active in C, activation epoch also remains fixed.

Extend the result to intermediate slot/cache observations and actual attestation-processing states.

Provide array-prefix/index summation lemmas that split the threshold's raw marked sum into C-active and non-C-active contributions, without changing identities at an index.

Dependencies already proved:

- `getValidator_setValidator_self`
- `getValidator_setValidator_of_ne`
- `getValidator_of_validators_eq`
- `increaseBalance_validators`
- `decreaseBalance_validators`
- `initiateValidatorExit_ok`
- `processDeposit_ok`
- `processAttestation_records`
- `stateTransition_invariant`
- `advanceSlots_invariant`
- `effectiveBalancesBounded_of_initialized_chain`
- `sumMarked_eq_sum`
- `sumMarked_le_filter`

No hash or signature assumption is needed for identity preservation.

## C. Actual activation and exit cohorts

File: `EthLib/Consensus/Proofs/Transition/Finality/Churn.lean`.

Size: large, approximately 800–1,500 proof lines.

Start now on queue/cohort lemmas, independently of A and D.

Use B when converting index populations to reference-weight bounds.

```lean
theorem realized_churn : realized_churn_statement (p := p)
```

The hypotheses are initialized genesis, successful common and suffix execution, and an epoch horizon n.

The conclusion bounds actual added active weight, actual removed C-active weight, and the previous/current voter gap.

The proposed uniform count cap is:

```lean
def churnCap (cfg : Config) (c : State p) (n : Nat) : Nat :=
  max 1 (max cfg.MIN_PER_EPOCH_CHURN_LIMIT.toNat
    ((c.validators.data.size + (n + 1) * p.SLOTS_PER_EPOCH.toNat * p.MAX_DEPOSITS.toNat) /
      cfg.CHURN_LIMIT_QUOTIENT.toNat))
```

The `max 1` reflects the actual exit-allocation guard for arbitrary configurations, not a mainnet assumption.

The registry bound includes partial epochs and deposits to new keys, and also dominates historical registry sizes for already queued cohorts.

Prove the following three concrete bounds for one suffix:

```text
additions <= n * churnCap * MAX_EFFECTIVE_BALANCE
exits <= n * churnCap * MAX_EFFECTIVE_BALANCE
previousGap <= churnCap * MAX_EFFECTIVE_BALANCE
```

These coefficients are proposed cohort bounds, not proved results.

Do not confuse the number scheduled at an epoch with the number becoming active or exiting at that epoch.

Dependencies already proved:

- `processRegistryUpdates_activation_budget`
- `activationQueue_nodup`
- `getValidator_of_mem_activationQueue`
- `exitQueueEpoch_churn`
- `exitQueueEpoch_gt_current`
- `previous_target_signer_outside_active_exits_now`
- `previous_target_outside_active_balance_le_exit_count`
- `stateTransition_chain_slot_le`
- `effectiveBalancesBounded_of_initialized_chain`

## D. Complete once-per-chain slashing credit ledger

File: `EthLib/Consensus/Proofs/Transition/Finality/SlashingBudget.lean`.

Size: medium-large, approximately 500–1,000 proof lines.

Start now, independently of A, B and C.

```lean
theorem slashing_budget :
    slashing_budget_statement (p := p) collectSlashingCredits
```

Implement `collectSlashingCredits` by following actual proposer and attester calls and retaining their pre/post states, validator index and exact credit quotient.

The target proposition in the accompanying file requires successful collection with the same terminal state, distinct event indices, a real `slashValidator` call at every event, and the summed per-validator cap.

Also prove completeness: every paid call in the actual execution contributes exactly one event, and every retained event has its actual two successful `increaseBalance` calls.

The collector must not merely produce some valid events.

The sum of credits is exactly the sum of effective balances at their own slashing sites divided individually by the whistleblower quotient.

Bound it by the number of distinct actually slashed validators times the capped quotient, not registry size times attester-slashing count.

Dependencies already proved:

- `slashValidator_phase0_credits`
- `slashValidator_effectiveBalance_query`
- `foldlM_slashIfSlashable_effectiveBalance_query`
- `foldlM_slashIfSlashable_flag_origin`
- `processAttesterSlashing_paid_credits`
- `foldlM_processAttesterSlashing_distinct_paid`
- `proposer_attester_slashings_distinct_paid`
- `stateTransition_chain_slashedFlag`
- `stateTransitionSlashingIndices_ok`
- `stateTransitionSlashingIndices_fold`
- `stateTransitionSlashingIndices_nodup`
- `slashIfSlashable_eq_after_attester_chain`
- `effectiveBalancesBounded_of_initialized_chain`

The new recorder proves distinct flags, but connecting all actual payments to it remains this task's obligation.

D is useful for the rate-refined growth corollary, but the deficit-only core safety proof does not depend on it.

## E. Threshold arithmetic and final safety assembly

File: `EthLib/Consensus/Proofs/Transition/Finality/Safety.lean`.

Size: medium-large, approximately 400–900 proof lines after A and B.

Start arithmetic adapters now, then integrate A and B.

```lean
theorem threshold_stake_bound : threshold_stake_bound_statement (p := p)

theorem phase0_safety : phase0_safety_statement (p := p) false
```

The first statement has no ancestry hypothesis.

It takes the two actual observed threshold computations and their slashable-index intersection witness.

The proposed concrete inequality is:

```text
S <= 3 * (slashable_C + maxLoss_C)
   + 2 * deficit_C + 2 * additions + 2 * exits
   + 6 * previousGap + 6 * EFFECTIVE_BALANCE_INCREMENT
```

Here additions is the maximum single-state non-C-active weight across both histories, and exits is the union of missing C-active weight across both histories.

The proposed coefficient two on additions comes from one addition correction for each threshold, each bounded by that maximum.

The coefficient two on exits is already present in the proved aligned-registry comparison for their union.

The two raw threshold corrections each charge their voter gap and target floor with coefficient three.

These explanations do not replace the still-required array alignment and cancellation proof.

Dependencies already proved:

- `validators_active_two_thirds_drift`
- `validators_active_two_thirds_comparison`
- `getTotalBalance_threshold_raw`
- `previous_target_outside_active_balance_le_exits`
- `sumMarked_eq_sum`
- `effectiveBalance_growth_le_deficit_of_initialized_chain`

The main theorem adds A's collision alternative and assumes neither churn bounds nor a healthy chain.

Its evidence is checked included data.

To state that the original keys signed those data, add only the existing `checks.AggregateSound signed` hypothesis and derive signatures at the actual signing roots, using B's key alignment.

Do not call checked inclusion an authenticated signature theorem without that step.

## F. Explicit horizon corollary and rate refinement

File: `EthLib/Consensus/Proofs/Transition/Finality/Horizon.lean`.

Size: small for composition after C and E, approximately 100–250 proof lines.

The requested tighter rate refinement is a separate medium-large task, approximately 500–1,000 lines, using D and reward/headroom accounting.

Start the registry/count bounds and scalar arithmetic now.

Final composition depends on C and E.

```lean
theorem phase0_safety_horizon : phase0_safety_statement (p := p) true
```

For n > 0, the candidate unrefined correction is:

```text
H(n) = 2*deficit_C + 6*(n+1)*churnCap(cfg,C,n)*MAX_EFFECTIVE_BALANCE
       + 6*EFFECTIVE_BALANCE_INCREMENT
d(n) = H(n)/(3*S), for S > 0
```

This follows the proposed two-branch cohort bounds: additions costs 2*n*K*M, the union of exits costs at most 4*n*K*M, and the voter-gap cost is 6*K*M.

Handle S = 0 with the undivided natural-number inequality.

Prove the zero-horizon result separately from checkpoint preservation, giving d(0) = 0.

The formula still depends on C's deficit and registry size, plus fixed preset/configuration constants.

It is not yet a proved formula in n and S alone, and must not be reported as one.

Eliminating these dependencies needs an additional proved envelope or an explicit theorem parameter that states them, not an implicit mainnet/healthy-chain hypothesis.

For the stronger requested rate version, replace the deficit contribution by a bound on actual positive growth, at most the initial deficit and at most stored capped headroom plus actual top-up and reward/whistleblower credits.

Already stored balance below the hysteresis trigger can increase effective balance without a new deposit.

Therefore `min(deficit, MAX_DEPOSITS * SLOTS_PER_EPOCH * n * M)` alone is not a proved envelope for all effective-balance growth.

The rate task must include reward and stored-headroom effects rather than assume them away.

Dependencies: C, D, E, `effectiveBalance_growth_le_initial_deficit`, `cappedEffectiveBalanceHeadroom_add_deposit`, and the existing reward-delta lemmas.

## Retained ownership

I would keep A and E, plus shared-definition integration and the final collision/signature audit.

B, C and D are independent substantial jobs for separate workers.

F can start scalar/count work in parallel but must wait for C and E to finish its theorem.

Have a separate owner handle the tighter rate refinement rather than letting it delay the core safety composition invisibly.

I have not created any threads.

## Checks at the pushed head

- `lake build --wfail`: `Build completed successfully (6426 jobs).`
- `lake exe check-decls`: `68965 declarations under EthLib, 0 findings, 0 in the baseline, 0 new, 0 stale`.
- `uv run --no-project --python 3.12 python scripts/soundness_facts.py --check`: passed.
- `uv run --no-project --python 3.12 python scripts/check_layers.py`: `The imports follow the rules of ARCHITECTURE.md.`
- `uv run --no-project --python 3.12 python scripts/check_lean_layout.py --base 787cc1b96287b8d669252ed7b47917473b34784a`: `No layout findings.`
- `uv run --no-project --python 3.12 python scripts/check_writing.py --base 787cc1b96287b8d669252ed7b47917473b34784a`: one retained optional W6 suggestion, `rules out`, in `EpochJustification.lean:713`.
- `git diff --check`: passed.
- `git status --short`: empty.
- GitHub subscription for the exact pushed SHA reported no CI checks found.

The proposed interface file is outside the repository and is not in the pushed commit.

The original design note remains `/tmp/ffg-dynamic-plan.md`, with later appendices superseding its early candidate contracts.

Use this handoff and its accompanying interface definitions, not the early guessed global coefficients.
