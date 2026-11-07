module

public import EthLib.Consensus.Proofs.Models.Ffg.Dynamic
public import EthLib.Consensus.Proofs.Transition.FfgVotes

/-!
# Proofs: what the beacon chain must provide to refine Casper FFG

Accountable safety for the beacon chain is proved in two parts.

The first part is the model of `Models/Ffg/Dynamic.lean`, with a weighing per supermajority link.

The second part is a map from two histories of the beacon chain to that model.

This file states the second part as a structure, `FfgRefinement`.

Its fields are the facts that the map needs.

It then proves that the fields give accountable safety for signed attestations.

No field is proved here.

Each field says which layer of the consensus foundations should prove it:

- L1, reachability: the states that two histories from one genesis pass through.
- L2, lifecycle: activation and exit epochs, slashed flags, effective-balance caps.
- L3, churn: how much the active set can change per epoch.
- L4, stake: how much effective balances can change per epoch.
- L5, provenance: which actual block, attestation and call wrote a value in a state.

The map reads three things from the histories.

```text
  signed     pairs (validator, attestation data) with a signature checked in a block
  records    weighing calls: source, target, and the weighing of the state at the call
  justified  every current or previous justified checkpoint of every state
  finalized  every finalized checkpoint of every state
```

Checkpoints become blocks of the model through `block`, with an order on blocks.

The map takes the whole checkpoint, root and epoch.

So the order can compare epoch-boundary pairs as in Gasper §4.

Then `(r, e) ≤ (r', e')` when `r` is the epoch-boundary block of the chain of `r'` at `e`.

The intended order is ancestry by the parent roots of actual blocks.

That order is meaningful only if no two different SSZ inputs share a SHA-256 digest.

So no field assumes it.

Every field about roots holds, or `evidence` holds.

`evidence` is meant to be a found collision or a found zero root.

The search runs over the hash inputs of the histories.

The conclusion is then slashable stake, or that evidence.

A vote of the model names the validator that signed it.

So `signed` must hold only pairs whose signature was checked, at an actual inclusion site.

The theorem itself needs no assumption on signatures.

Unforgeability is needed only to read slashable data as proof that the validator misbehaved.
-/

@[expose] public section

namespace EthLib.Consensus

open Models Models.Ffg

/-- A call that weighed the votes for one target checkpoint and found two thirds.

The source is the one checkpoint that every counted vote names as its source. -/
structure WeighingRecord where
  /-- The source checkpoint of the counted votes. -/
  source : Checkpoint
  /-- The checkpoint that the call justified. -/
  target : Checkpoint
  /-- The weighing of the state at the call. -/
  weighing : Weighing ValidatorIndex

variable {p : Preset} {fork : Base.Fork}

/-- The effective balance of a validator in a state, and zero for an index outside the registry. -/
def effectiveBalanceAt (state : BeaconState p fork) (index : ValidatorIndex) : ℕ :=
  match state.validators.data[index.toNat]? with
  | none => 0
  | some validator => validator.effectiveBalance.toNat

/-- The weighing that a state uses at a call that justifies a checkpoint.

- `active`: the validators active in the current epoch of the state.
- `voters`: the unslashed validators counted for the target, given by the caller.
- `stake`: the effective balances of the state.
- `floor`: one effective-balance increment, the least total balance. -/
def Weighing.ofState (state : BeaconState p fork) (voters : Finset ValidatorIndex) :
    Weighing ValidatorIndex :=
  ⟨(getActiveValidatorIndices state (getCurrentEpoch state)).toFinset, voters,
    effectiveBalanceAt state, p.EFFECTIVE_BALANCE_INCREMENT.toNat⟩

/-- The checkpoint of the model for a checkpoint, through a map of whole checkpoints. -/
def Checkpoint.toModel {β : Type*} (block : Checkpoint → β) (c : Checkpoint) :
    Models.Ffg.Checkpoint β :=
  ⟨block c, c.epoch.toNat⟩

/-- The votes of the model that signed attestation data cast, through a map of checkpoints. -/
def pairVotes {ν β : Type*} (block : Checkpoint → β) (signed : Set (ν × AttestationData)) :
    Set (Vote ν β) :=
  (fun p => ⟨p.1, p.2.source.toModel block, p.2.target.toModel block⟩) '' signed

/-- A validator that is slashable in the model signed two data that the beacon chain slashes. -/
theorem exists_isSlashableAttestationData_of_pairSlashable {ν β : Type*} {block : Checkpoint → β}
    {signed : Set (ν × AttestationData)} {validator : ν}
    (slashable : Slashable (pairVotes block signed) validator) :
    ∃ data1 data2, (validator, data1) ∈ signed ∧ (validator, data2) ∈ signed ∧
      isSlashableAttestationData data1 data2 = true := by
  obtain ⟨_, ⟨⟨signer1, data1⟩, signed1, rfl⟩, _, ⟨⟨signer2, data2⟩, signed2, rfl⟩, rfl, same,
    broken⟩ := slashable
  obtain rfl : signer2 = signer1 := same
  refine ⟨data1, data2, signed1, signed2, ?_⟩
  simp only [isSlashableAttestationData, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq,
    beq_iff_eq, decide_eq_true_eq]
  rcases broken with ⟨distinct, epochs⟩ | ⟨sources, -, targets⟩
  · refine .inl ⟨fun equal => distinct (by rw [equal]), ?_⟩
    simpa [Checkpoint.toModel, UInt64.toNat_inj] using epochs
  · simp only [Checkpoint.toModel] at sources targets
    exact .inr ⟨UInt64.lt_iff_toNat_lt.mpr sources, UInt64.lt_iff_toNat_lt.mpr targets⟩

/-- The facts that a map from two histories of the beacon chain to the dynamic FFG model needs.

The histories start from one genesis.

Each set below collects what either history shows.

The layer that should prove each field is in its comment. -/
structure FfgRefinement (β : Type*) [Preorder β] where
  /-- The block of the model for a checkpoint.

  The genesis checkpoint of a state has the zero root, so `block` maps it to `genesis`. -/
  block : Checkpoint → β
  /-- The genesis block of the model. -/
  genesis : β
  /-- Hash evidence: a SHA-256 collision or a zero SSZ root, found among the hash inputs. -/
  evidence : Prop
  /-- Pairs of a validator and attestation data, from attestations included in a block.

  Each pair has a site where the signature of the indexed attestation was checked (L5). -/
  signed : Set (ValidatorIndex × AttestationData)
  /-- The weighing calls that justified a checkpoint (L1 for the calls, L5 for their contents). -/
  records : Set WeighingRecord
  /-- The current and previous justified checkpoints of each state, and those a call justified (L1).

  A call that justifies both the previous and the current epoch keeps only the current one.

  The previous one then appears in no state.

  But its justification bit is set, and a finalization rule can read it. -/
  justified : Set Checkpoint
  /-- The finalized checkpoints of every state (L1). -/
  finalized : Set Checkpoint
  /-- A justified checkpoint is genesis, or a weighing call justified it (L5).

  The call wrote the target of its record as the current or previous justified checkpoint. -/
  justified_recorded : ∀ c ∈ justified,
    c.toModel block = ⟨genesis, 0⟩ ∨ ∃ r ∈ records, r.target = c
  /-- The source of a weighing call is a justified checkpoint of an earlier state (L5).

  Inclusion checks each counted vote against the justified checkpoint for its target epoch. -/
  source_justified : ∀ r ∈ records, r.source ∈ justified
  /-- The source of a weighing call has a smaller epoch than its target (L5). -/
  source_lt_target : ∀ r ∈ records, r.source.epoch.toNat < r.target.epoch.toNat
  /-- The source block is in the chain of the target block, or there is hash evidence (L5).

  Both roots are read from the block roots of one chain, which follow parent roots. -/
  source_le_target : ∀ r ∈ records, block r.source ≤ block r.target ∨ evidence
  /-- Every counted voter signed data with the source and the target of the call (L5).

  Before Altair the voters come from pending attestations with a matching target.

  From Altair they come from timely-target flags, set at an inclusion site.

  There the target root was read at inclusion, so it must equal the root at the call. -/
  voters_signed : ∀ r ∈ records, ∀ i ∈ r.weighing.voters,
    ∃ d, (i, d) ∈ signed ∧ d.source = r.source ∧ d.target = r.target
  /-- The voters of a weighing call pass its two-thirds test (L5).

  The call computes `3 * max floor voted ≥ 2 * max floor total`, from effective balances. -/
  threshold : ∀ r ∈ records, r.weighing.Supermajority r.weighing.voters
  /-- A finalized checkpoint is genesis, or one of the four rules of a call finalized it (L5).

  The rules finalize with `k = 1` or `k = 2`.

  Checkpoints `cs 0 = c, ..., cs k` have the epochs of `c` and the next `k` epochs.

  The first `k` are justified, and a weighing call links `c` to `cs k`.

  Each block is in the chain of the next one, or there is evidence. -/
  finalized_rule : ∀ c ∈ finalized, c.toModel block = ⟨genesis, 0⟩ ∨
    ∃ k, 1 ≤ k ∧ ∃ cs : ℕ → Checkpoint, cs 0 = c ∧
      (∀ i ≤ k, (cs i).epoch.toNat = c.epoch.toNat + i) ∧
      (∀ i < k, cs i ∈ justified) ∧
      (∀ i < k, block (cs i) ≤ block (cs (i + 1)) ∨ evidence) ∧
      ∃ r ∈ records, r.source = c ∧ r.target = cs k

namespace FfgRefinement

variable {β : Type*} [Preorder β] (R : FfgRefinement β)

/-- The weighings that the model allows for a target: those of the calls with that target. -/
def weighings (t : Ffg.Checkpoint β) : Set (Weighing ValidatorIndex) :=
  {ω | ∃ r ∈ R.records, r.target.toModel R.block = t ∧ r.weighing = ω}

/-- The votes of the model: those of the signed attestation data. -/
def votes : Set (Vote ValidatorIndex β) :=
  pairVotes R.block R.signed

/-- A larger signed set passes a two-thirds test that a smaller one passes. -/
theorem _root_.EthLib.Consensus.Models.Ffg.Weighing.Supermajority.mono {ν : Type*}
    {ω : Weighing ν} {q q' : Finset ν} (h : ω.Supermajority q) (hq : q ⊆ q') :
    ω.Supermajority q' :=
  h.trans (Nat.mul_le_mul_left 3 (max_le_max le_rfl (stake_mono hq)))

variable {R}

/-- Without hash evidence, a weighing call is a supermajority link of the model. -/
theorem link (hno : ¬R.evidence) {r : WeighingRecord} (hr : r ∈ R.records) :
    Dynamic.SupermajorityLink R.weighings R.votes (r.source.toModel R.block)
      (r.target.toModel R.block) r.weighing := by
  refine ⟨R.source_lt_target r hr, (R.source_le_target r hr).resolve_right hno,
    ⟨r, hr, rfl, rfl⟩, (R.threshold r hr).mono ?_⟩
  intro i hi
  obtain ⟨d, hd, hs, ht⟩ := R.voters_signed r hr i hi
  simp only [Weighing.signers, Ffg.signers, Finset.mem_filter]
  exact ⟨hi, ⟨i, d⟩, hd, by simp [hs, ht]⟩

/-- Without hash evidence, each justified checkpoint of the histories is justified in the model. -/
theorem justified_model (hno : ¬R.evidence) {c : Checkpoint} (hc : c ∈ R.justified) :
    Dynamic.Justified R.weighings R.genesis R.votes (c.toModel R.block) := by
  -- Induct on the epoch: the source of a weighing call has a smaller one.
  induction h : c.epoch.toNat using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    rcases R.justified_recorded c hc with hg | ⟨r, hr, rfl⟩
    · rw [hg]
      exact .root
    · have hlt := R.source_lt_target r hr
      exact .link (ih _ (h ▸ hlt) (R.source_justified r hr) rfl) (link hno hr)

/-- Without hash evidence, each finalized checkpoint of the histories is finalized in the model. -/
theorem finalized_model (hno : ¬R.evidence) {c : Checkpoint} (hc : c ∈ R.finalized) :
    Dynamic.Finalized R.weighings R.genesis R.votes (c.toModel R.block) := by
  rcases R.finalized_rule c hc with hg | ⟨k, hk, cs, h0, hep, hj, hle, r, hr, hs, ht⟩
  · exact .inl hg
  refine .inr ⟨k, hk, fun i => R.block (cs i), by simp [h0, Checkpoint.toModel], ?_, ?_, ?_⟩
  · exact fun i hi => (hle i hi).resolve_right hno
  · intro i hi
    have := justified_model hno (hj i hi)
    simpa [Checkpoint.toModel, hep i hi.le] using this
  · refine ⟨r.weighing, ?_⟩
    have := link hno hr
    rw [hs, ht] at this
    simpa [Checkpoint.toModel, hep k le_rfl] using this

open scoped Classical in
/-- Accountable safety for two histories of the beacon chain, given the facts of the map.

Take two finalized checkpoints of the histories whose blocks conflict.

Consider the weighing calls whose target epoch lies between the two finalized epochs.

Take a reference weighing `ω₀`, and a bound `D` on the drift from it of each such call.

Then there are validators active in `ω₀` with a third of its total stake, less `2 * D`.

Each of them signed two attestation data that the beacon chain slashes.

Otherwise there is hash evidence.

`D` bounds the drift of the actual weighings, in effective stake, not the balance charged to churn.

From Electra the two differ.

A consolidation target can start to exit, then receive the balance of its source.

It then leaves with more effective stake than its exit charged.

In the drift, that growth counts as gained stake, and the exit counts the reference stake.

So L2, L3 and L4 must bound `D` by the effective stake that actually enters, leaves and changes. -/
theorem accountable_safety {c₁ c₂ : Checkpoint} (h₁ : c₁ ∈ R.finalized) (h₂ : c₂ ∈ R.finalized)
    (hc : Conflicting (R.block c₁) (R.block c₂)) (ω₀ : Weighing ValidatorIndex)
    {D : ℕ}
    (hD : ∀ r ∈ R.records, min c₁.epoch.toNat c₂.epoch.toNat ≤ r.target.epoch.toNat →
      r.target.epoch.toNat ≤ max c₁.epoch.toNat c₂.epoch.toNat → Weighing.drift ω₀ r.weighing ≤ D) :
    stake ω₀.stake ω₀.active ≤
      3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2, (i, data1) ∈ R.signed ∧
        (i, data2) ∈ R.signed ∧ isSlashableAttestationData data1 data2 = true} + 2 * D ∨
      R.evidence := by
  by_cases hno : R.evidence
  · exact .inr hno
  refine .inl ?_
  have bound := Dynamic.accountable_safety (finalized_model hno h₁) (finalized_model hno h₂)
    hc ω₀ (D := D) ?_
  · refine bound.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (stake_mono ?_)) _)
    exact Finset.monotone_filter_right _ fun _ _ =>
      exists_isSlashableAttestationData_of_pairSlashable
  · rintro t ω ⟨r, hr, rfl, rfl⟩ hlo hhi
    exact hD r hr hlo hhi

open scoped Classical in
/-- Accountable safety for a finalized and a justified checkpoint of the histories.

The justified epoch is at least the finalized one, and the blocks conflict.

The conclusion is the one of `accountable_safety`, over the epochs between the two. -/
theorem accountable_safety_justified {f j : Checkpoint} (hf : f ∈ R.finalized)
    (hj : j ∈ R.justified) (hle : f.epoch.toNat ≤ j.epoch.toNat)
    (hc : Conflicting (R.block f) (R.block j)) (ω₀ : Weighing ValidatorIndex) {D : ℕ}
    (hD : ∀ r ∈ R.records, f.epoch.toNat ≤ r.target.epoch.toNat →
      r.target.epoch.toNat ≤ j.epoch.toNat → Weighing.drift ω₀ r.weighing ≤ D) :
    stake ω₀.stake ω₀.active ≤
      3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2, (i, data1) ∈ R.signed ∧
        (i, data2) ∈ R.signed ∧ isSlashableAttestationData data1 data2 = true} + 2 * D ∨
      R.evidence := by
  by_cases hno : R.evidence
  · exact .inr hno
  refine .inl ?_
  have bound := (Dynamic.evidence_of_finalized_justified (finalized_model hno hf)
    (justified_model hno hj) hle hc).stake_le ω₀ (D := D) ?_
  · refine bound.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 3 (stake_mono ?_)) _)
    exact Finset.monotone_filter_right _ fun _ _ =>
      exists_isSlashableAttestationData_of_pairSlashable
  · rintro t ω ⟨r, hr, rfl, rfl⟩ hlo hhi
    exact hD r hr hlo hhi

end FfgRefinement

end EthLib.Consensus
