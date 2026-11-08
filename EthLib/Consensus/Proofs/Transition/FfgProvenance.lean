module

public import EthLib.Consensus.Proofs.Transition.FfgPreElectra
public import EthLib.Consensus.Proofs.Transition.Provenance.Links
public import EthLib.Consensus.Proofs.Transition.Provenance.PendingVoters

/-!
# Proofs: L5 provenance in the shape of the FFG refinement

`FfgRefinement` needs an order on blocks and a two-thirds test on weighed sets of indices.

The provenance proofs give parent-root ancestry and raw sums over lists of indices.

Their `ChainAncestor` is a reflexive-transitive closure of parent links.

Their raw balance is `markedStake`.

This file joins the two.

**Blocks.** A block of the model is a root, or `none` for the zero root.

The zero root is the root of the genesis checkpoint, by convention.

It is not the root of an actual block, so it sits below every block and conflicts with none.

Two other roots are ordered when parent links lead from the first to the second.

The links are a parameter: the parent links of the actual blocks of both histories.

A record's source then comes before its target, or the provenance proofs give hash evidence.

**Threshold.** A weighing call compares raw sums of effective balances over lists of indices.

When every index names a validator, those sums are the stakes of the sets of indices.

So a call that passes its threshold passes the test of `Weighing.ofState`.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}

/-! ## Blocks -/

/-- The blocks of the model over parent links: `none` for the genesis sentinel, or a root. -/
structure LinkedRoot (links : Root → Root → Prop) where
  /-- The root, or `none` for the genesis sentinel. -/
  root : Option Root

namespace LinkedRoot

variable {links : Root → Root → Prop}

/-- `none` is below every block, and a root is below another when links lead to it. -/
instance : Preorder (LinkedRoot links) where
  le a b := a.root = none ∨
    ∃ x y, a.root = some x ∧ b.root = some y ∧ Relation.ReflTransGen links x y
  le_refl a := by
    rcases a with ⟨_ | x⟩
    · exact .inl rfl
    · exact .inr ⟨x, x, rfl, rfl, .refl⟩
  le_trans a b c := by
    rintro (ha | ⟨x, y, ha, hb, hxy⟩) (hb' | ⟨y', z, hb', hc, hyz⟩)
    · exact .inl ha
    · exact .inl ha
    · rw [hb] at hb'
      cases hb'
    · rw [hb] at hb'
      cases hb'
      exact .inr ⟨x, z, ha, hc, hxy.trans hyz⟩

/-- The block of a root: `none` for the zero root, the root itself otherwise. -/
def ofRoot (r : Root) : LinkedRoot links :=
  ⟨if r = Vector.replicate 32 0 then none else some r⟩

/-- The zero root is the genesis block. -/
theorem ofRoot_zero : (ofRoot (links := links) (Vector.replicate 32 0)).root = none := by
  simp [ofRoot]

/-- The genesis block is below every block. -/
theorem none_le (b : LinkedRoot links) : (⟨none⟩ : LinkedRoot links) ≤ b :=
  Or.inl rfl

/-- A source root comes before a target root in two cases:

- the source is the zero root;
- links lead from it to a target that is not the zero root. -/
theorem ofRoot_le {s t : Root} (h : s = Vector.replicate 32 0 ∨
      (Relation.ReflTransGen links s t ∧ t ≠ Vector.replicate 32 0)) :
    ofRoot (links := links) s ≤ ofRoot t := by
  by_cases hs : s = Vector.replicate 32 0
  · exact Or.inl (by simp [ofRoot, hs])
  rcases h with h | ⟨path, ht⟩
  · exact absurd h hs
  exact Or.inr ⟨s, t, by simp [ofRoot, hs], by simp [ofRoot, ht], path⟩

end LinkedRoot

/-- Checkpoints as epoch-boundary pairs, Gasper §4, over parent links that carry the child's slot.

Each is `none` for the genesis sentinel, or a root with an epoch. -/
structure EpochBlock (links : Root → Root → ℕ → Prop) (slotsPerEpoch : ℕ) where
  /-- The root and the epoch, or `none` for the genesis sentinel. -/
  point : Option (Root × ℕ)

namespace EpochBlock

variable {links : Root → Root → ℕ → Prop} {slotsPerEpoch : ℕ}

/-- The parent links whose child lies after the first slot of an epoch. -/
def after (links : Root → Root → ℕ → Prop) (slotsPerEpoch epoch : ℕ) (p r : Root) : Prop :=
  ∃ slot, links p r slot ∧ epoch * slotsPerEpoch < slot

/-- A later epoch keeps fewer links. -/
theorem after_mono {e e' : ℕ} (le : e ≤ e') {p r : Root}
    (h : after links slotsPerEpoch e' p r) : after links slotsPerEpoch e p r := by
  obtain ⟨slot, link, lt⟩ := h
  exact ⟨slot, link, lt_of_le_of_lt (Nat.mul_le_mul_right _ le) lt⟩

/-- `(r, e) ≤ (r', e')` when `e ≤ e'` and links lead from `r` to `r'`.

These links pass through blocks after the first slot of `e`.

That is, `r` is the epoch-boundary block of the chain of `r'` at `e`.

The genesis sentinel is below every pair. -/
instance : Preorder (EpochBlock links slotsPerEpoch) where
  le a b := a.point = none ∨ ∃ r e r' e', a.point = some (r, e) ∧ b.point = some (r', e') ∧
    e ≤ e' ∧ Relation.ReflTransGen (after links slotsPerEpoch e) r r'
  le_refl a := by
    rcases a with ⟨_ | ⟨r, e⟩⟩
    · exact .inl rfl
    · exact .inr ⟨r, e, r, e, rfl, rfl, le_rfl, .refl⟩
  le_trans a b c := by
    rintro (ha | ⟨r, e, r', e', ha, hb, le, path⟩) (hb' | ⟨r'', e'', s, f, hb', hc, le', path'⟩)
    · exact .inl ha
    · exact .inl ha
    · rw [hb] at hb'
      cases hb'
    · rw [hb] at hb'
      cases hb'
      exact .inr ⟨r, e, s, f, ha, hc, le.trans le',
        path.trans (Relation.ReflTransGen.mono (fun _ _ h => after_mono le h) _ _ path')⟩

/-- The pair of a checkpoint: the genesis sentinel for the zero root. -/
def ofCheckpoint (c : Checkpoint) : EpochBlock links slotsPerEpoch :=
  ⟨if c.root = Vector.replicate 32 0 then none else some (c.root, c.epoch.toNat)⟩

/-- A checkpoint is below another in two cases:

- its root is zero;
- links lead from its root to the nonzero root of the other.
  They pass through blocks after the first slot of its epoch. -/
theorem ofCheckpoint_le {s t : Checkpoint}
    (h : s.root = Vector.replicate 32 0 ∨ (s.epoch.toNat ≤ t.epoch.toNat ∧
      Relation.ReflTransGen (after links slotsPerEpoch s.epoch.toNat) s.root t.root ∧
      t.root ≠ Vector.replicate 32 0)) :
    ofCheckpoint (links := links) (slotsPerEpoch := slotsPerEpoch) s ≤ ofCheckpoint t := by
  by_cases hs : s.root = Vector.replicate 32 0
  · exact Or.inl (by simp [ofCheckpoint, hs])
  rcases h with h | ⟨le, path, ht⟩
  · exact absurd h hs
  exact Or.inr ⟨s.root, s.epoch.toNat, t.root, t.epoch.toNat, by simp [ofCheckpoint, hs],
    by simp [ofCheckpoint, ht], le, path⟩

/-- The genesis checkpoint is the genesis sentinel. -/
theorem ofCheckpoint_zero (e : Epoch) :
    (ofCheckpoint (links := links) (slotsPerEpoch := slotsPerEpoch)
      ⟨e, Vector.replicate 32 0⟩).point = none := by
  simp [ofCheckpoint]

end EpochBlock

/-- The source of a weighing call comes before its target in the model, or there is evidence.

This is the field `source_le_target` of `FfgRefinement`.

`chain` is the parent links of one history.

Its closure is the provenance proofs' `ChainAncestor`.

The links of the model must contain them.

`zeroFound` is the provenance proofs' `ZeroRootFound`, a state of the history with the zero root.

A target root that is zero would be an actual block whose root is zero, so it is evidence too. -/
theorem source_le_target_model {chain links : Root → Root → Prop}
    (subset : ∀ p r, chain p r → links p r) {source target : Root} {zeroFound evidence : Prop}
    (ancestor : source = Vector.replicate 32 0 ∨ Relation.ReflTransGen chain source target ∨
      zeroFound)
    (zeroEvidence : zeroFound → evidence)
    (targetNonzero : target ≠ Vector.replicate 32 0 ∨ evidence) :
    LinkedRoot.ofRoot (links := links) source ≤ LinkedRoot.ofRoot target ∨ evidence := by
  rcases ancestor with zero | path | found
  · exact .inl (LinkedRoot.ofRoot_le (.inl zero))
  · rcases targetNonzero with nonzero | e
    · exact .inl (LinkedRoot.ofRoot_le (.inr ⟨Relation.ReflTransGen.mono subset _ _ path, nonzero⟩))
    · exact .inr e
  · exact .inr (zeroEvidence found)

/-- From genesis, the source of every weighing call comes before its target in the model.

Otherwise a state of the history has the zero root, or a cached header has the zero root.

The links of the model must contain the parent links of the history.

This is the field `source_le_target` of `FfgRefinement`, for one record of one history. -/
theorem JustifiedBy.source_le_target_linked {start after : ForkedBeaconState preset}
    {checkpoint : Checkpoint} {links : Root → Root → Prop}
    (wide : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (genesis : Genesis config checks start)
    (justified : JustifiedBy config checks start after checkpoint)
    (subset : ∀ p r, ChainBlock config checks start after p r → links p r) :
    ∃ (fork : Base.Fork) (state cached : BeaconState preset fork),
      Reaches config checks start ⟨fork, state⟩ ∧ processSlot state = .ok cached ∧
      (LinkedRoot.ofRoot (links := links) (recordSource cached checkpoint.epoch).root ≤
          LinkedRoot.ofRoot checkpoint.root ∨
        ZeroRootFound config checks start after ∨ ZeroHeaderFound config checks start after) := by
  obtain ⟨fork, state, cached, head, -, cachedOk, -, ancestor⟩ :=
    justified.source_ancestor wide genesis
  have nonzero := justified.target_nonzero wide (by
    rw [(genesis_state genesis).1]
    exact Nat.zero_le _)
  exact ⟨fork, state, cached, head, cachedOk,
    source_le_target_model subset ancestor .inl (nonzero.imp_right .inr)⟩

/-! ## Threshold -/

/-- The fold of `sumMarked` over two lists, as a sum over positions. -/
theorem foldl_zip_markedStake (validators : List Validator) (marks : List Bool) (acc : ℕ) :
    (validators.zip marks).foldl
        (fun sum (validator, mark) => if mark then sum + validator.effectiveBalance.toNat else sum)
        acc =
      acc + ∑ j ∈ Finset.range validators.length,
        if marks[j]? = some true then
          ((validators[j]?).map (·.effectiveBalance.toNat)).getD 0 else 0 := by
  induction validators generalizing marks acc with
  | nil => simp
  | cons validator rest ih =>
    cases marks with
    | nil => simp
    | cons mark marks =>
      rw [List.zip_cons_cons, List.foldl_cons, ih, List.length_cons, Finset.sum_range_succ']
      cases mark
      · simp
      · simp; omega

/-- The raw sum of the effective balances that a list of indices marks.

Each index counts once, and an index outside the registry counts nothing. -/
def markedStake (state : BeaconState preset fork) (indices : List ValidatorIndex) : ℕ :=
  sumMarked state.validators.data (markIndices state.validators.data.size indices)

/-- A raw sum over a list of indices is the stake of their set, when every index is in range. -/
theorem markedStake_eq_stake {state : BeaconState preset fork} {indices : List ValidatorIndex}
    (inRange : ∀ i ∈ indices, i.toNat < state.validators.data.size) :
    markedStake state indices = stake (effectiveBalanceAt state) indices.toFinset := by
  unfold markedStake sumMarked
  rw [← Array.foldl_toList, Array.toList_zip, foldl_zip_markedStake, Nat.zero_add,
    Array.length_toList]
  have term : ∀ j ∈ Finset.range state.validators.data.size,
      (if (markIndices state.validators.data.size indices).toList[j]? = some true then
        ((state.validators.data.toList[j]?).map (·.effectiveBalance.toNat)).getD 0 else 0) =
      if indices.any (·.toNat == j) then effectiveAt state j else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Array.getElem?_toList, getElem?_markIndices, Array.getElem?_toList]
    simp only [hj, ↓reduceIte]
    simp [effectiveAt]
  rw [Finset.sum_congr rfl term, ← Finset.sum_filter, stake]
  simp only [effectiveBalanceAt_eq]
  rw [sum_toNat]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, List.any_eq_true, beq_iff_eq,
    Finset.mem_image, List.mem_toFinset]
  constructor
  · rintro ⟨-, i, mem, rfl⟩
    exact ⟨i, mem, rfl⟩
  · rintro ⟨i, mem, rfl⟩
    exact ⟨inRange i mem, i, mem, rfl⟩

/-- A weighing call that passes its threshold passes the test of the weighing of its state.

The threshold is the raw test of the call, the provenance proofs' `PassesThreshold`.

Every counted voter must name a validator of the state.

This is the field `threshold` of `FfgRefinement`. -/
theorem supermajority_of_threshold {state : BeaconState preset fork}
    {voters : List ValidatorIndex}
    (passes : 2 * max preset.EFFECTIVE_BALANCE_INCREMENT.toNat
        (markedStake state (getActiveValidatorIndices state (getCurrentEpoch state))) ≤
      3 * max preset.EFFECTIVE_BALANCE_INCREMENT.toNat (markedStake state voters))
    (within : state.RegistryWithinLimit)
    (inRange : ∀ i ∈ voters, i.toNat < state.validators.data.size) :
    (Weighing.ofState state voters.toFinset).Supermajority voters.toFinset := by
  have activeInRange : ∀ i ∈ getActiveValidatorIndices state (getCurrentEpoch state),
      i.toNat < state.validators.data.size := fun i mem =>
    activeAt_lt ((mem_active_iff within).mp mem)
  unfold Weighing.Supermajority
  simp only [Weighing.ofState]
  rw [← markedStake_eq_stake activeInRange, ← markedStake_eq_stake inRange]
  exact passes

/-- From Altair, take the weighing call behind a justified checkpoint.

It is a supermajority of the weighing of its state, and its voters were active in the target epoch.

This is the field `threshold` of `FfgRefinement`, for one record of one history.

The record's weighing is `Weighing.ofState cached voters`.

The registry must be within its limit, which its type gives before Gloas. -/
theorem JustifiedBy.supermajority {start after : ForkedBeaconState preset}
    {checkpoint : Checkpoint} (justified : JustifiedBy config checks start after checkpoint) :
    ∃ (fork : Base.Fork) (state cached : BeaconState preset fork) (voters : List ValidatorIndex),
      Reaches config checks start ⟨fork, state⟩ ∧ processSlot state = .ok cached ∧
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
      (.altair ≤ fork → cached.RegistryWithinLimit →
        (∀ i ∈ voters, i ∈ getActiveValidatorIndices cached checkpoint.epoch) ∧
        (Weighing.ofState cached voters.toFinset).Supermajority voters.toFinset) := by
  obtain ⟨fork, state, cached, -, -, voters, head, -, -, -, -, cachedOk, -, -, epoch, counted,
    passes, -⟩ := justified
  refine ⟨fork, state, cached, voters, head, cachedOk, epoch, fun altair within => ?_⟩
  have active := TargetVoters.active altair counted
  exact ⟨active, supermajority_of_threshold passes within fun i mem =>
    activeAt_lt ((mem_active_iff within).mp (active i mem))⟩

/-- From genesis, at every fork, take the weighing call behind a justified checkpoint.

It is a supermajority of the weighing of its state, and its voters were active in the target epoch.

Before Altair the voters come from pending attestations, whose committees were active.

The seed of a committee must stay apart from the RANDAO writes of the target epoch and the next.

The registry must be within its limit, which its type gives before Gloas. -/
theorem JustifiedBy.supermajority_of_genesis {start after : ForkedBeaconState preset}
    {checkpoint : Checkpoint}
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (genesis : Genesis config checks start)
    (justified : JustifiedBy config checks start after checkpoint) :
    ∃ (fork : Base.Fork) (state cached : BeaconState preset fork) (voters : List ValidatorIndex),
      Reaches config checks start ⟨fork, state⟩ ∧ processSlot state = .ok cached ∧
      (checkpoint.epoch = getPreviousEpoch cached ∨ checkpoint.epoch = getCurrentEpoch cached) ∧
      (cached.RegistryWithinLimit →
        (∀ i ∈ voters, i ∈ getActiveValidatorIndices cached checkpoint.epoch) ∧
        (Weighing.ofState cached voters.toFinset).Supermajority voters.toFinset) := by
  obtain ⟨fork, state, cached, voters, head, -, cachedOk, -, epoch, counted, passes, -, pending⟩ :=
    justified.pending_voters_signed_of_genesis lookahead genesis
  refine ⟨fork, state, cached, voters, head, cachedOk, epoch, fun within => ?_⟩
  have active : ∀ i ∈ voters, i ∈ getActiveValidatorIndices cached checkpoint.epoch := by
    by_cases altair : .altair ≤ fork
    · exact TargetVoters.active altair counted
    · intro i mem
      obtain ⟨_, _, activeAt, _⟩ := pending (Nat.lt_of_not_le altair) i mem
      exact activeAt
  exact ⟨active, supermajority_of_threshold passes within fun i mem =>
    activeAt_lt ((mem_active_iff within).mp (active i mem))⟩

end EthLib.Consensus
