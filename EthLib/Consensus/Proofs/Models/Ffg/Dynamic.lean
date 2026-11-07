module

public import EthLib.Consensus.Proofs.Models.Ffg.AccountableSafety

/-!
# Casper FFG with a weighing per link

The model of `Model.lean` weighs every link with one validator set and one stake function.

In the beacon chain the validator set and the stakes change from epoch to epoch.

Gasper §8.6 lets the validator set change, [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).

There, each block has a validator set, and the stake of each validator stays fixed.

Here each supermajority link carries its own weighing.

A weighing says who counts in the total, whose votes count, the stakes, and a floor.

So stakes may change too.

The weighings allowed for a target checkpoint are a parameter `W`.

With one weighing for every target, the model is the one of `Model.lean`.

Two conflicting finalized checkpoints give two supermajority links.

Every validator that signs both links is slashable.

This is Gasper Lemma 8.2.

Both targets have epochs between the epochs of the two finalized checkpoints.

Against a reference weighing, the slashable stake then has a lower bound, as in Gasper Theorem 8.3.

The bound loses the drift of each of the two weighings from the reference.

Gasper's activations and exits are two of the five terms of the drift.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg

/-- A weighing of the votes for one link.

The supermajority test reads `2 * max floor total ≤ 3 * max floor signed`.

- `active`: the validators whose stake forms the total.
- `voters`: the validators whose votes count.
- `stake`: the stake of each validator.
- `floor`: a lower bound applied to both sides.

Casper FFG and Gasper take `voters = active` and `floor = 0`.

The beacon chain needs both fields.

Its denominator is the active set of the current epoch.

Its numerator for the previous epoch can count a validator that is no longer active.

Its balances are at least one increment, so a tiny total stake passes the test with no votes. -/
structure Weighing (ν : Type*) where
  /-- The validators whose stake forms the total. -/
  active : Finset ν
  /-- The validators whose votes count. -/
  voters : Finset ν
  /-- The stake of each validator. -/
  stake : ν → ℕ
  /-- The floor applied to the total and to the signed stake. -/
  floor : ℕ

/-- A set splits into its part inside `t` and its part outside `t`. -/
theorem stake_inter_add_sdiff {ν : Type*} [DecidableEq ν] (w : ν → ℕ) (s t : Finset ν) :
    stake w (s ∩ t) + stake w (s \ t) = stake w s := by
  rw [add_comm, stake, stake, stake, ← Finset.sdiff_inter_self_left s t]
  exact Finset.sum_sdiff Finset.inter_subset_left

namespace Weighing

variable {ν β : Type*}

/-- The weighing of the static model: one set and one stake function, and no floor. -/
def static (V : Finset ν) (w : ν → ℕ) : Weighing ν :=
  ⟨V, V, w, 0⟩

/-- The voters of the weighing that vote for the link from `s` to `t`. -/
noncomputable def signers (ω : Weighing ν) (votes : Set (Vote ν β)) (s t : Checkpoint β) :
    Finset ν :=
  Ffg.signers ω.voters votes s t

/-- A set of validators passes the two-thirds test of the weighing. -/
def Supermajority (ω : Weighing ν) (q : Finset ν) : Prop :=
  2 * max ω.floor (Models.stake ω.stake ω.active) ≤ 3 * max ω.floor (Models.stake ω.stake q)

variable [DecidableEq ν]

/-- How far a weighing `ω` is from a reference weighing `ω₀`, in reference stake.

```text
  drift = 2 * exited + 2 * lost + 3 * gained + 3 * entered + 3 * floor
```

- `exited`: reference stake of validators active in `ω₀` but not in `ω`.
- `lost`: stake that reference-active validators hold in `ω₀` above their stake in `ω`.
- `gained`: stake that reference-active validators hold in `ω` above their stake in `ω₀`.
- `entered`: stake in `ω` of voters of `ω` not active in `ω₀`.
- `floor`: the floor of `ω`.

Each term is zero when `ω = ω₀` is a static weighing. -/
def drift (ω₀ ω : Weighing ν) : ℕ :=
  2 * Models.stake ω₀.stake (ω₀.active \ ω.active) +
    2 * ∑ v ∈ ω₀.active, (ω₀.stake v - ω.stake v) +
    3 * ∑ v ∈ ω₀.active, (ω.stake v - ω₀.stake v) +
    3 * Models.stake ω.stake (ω.voters \ ω₀.active) +
    3 * ω.floor

@[simp]
theorem drift_static_self (V : Finset ν) (w : ν → ℕ) : drift (static V w) (static V w) = 0 := by
  simp [drift, static, Models.stake]

/-- One supermajority, measured in a reference weighing.

Signers that pass the test of `ω` hold two thirds of the reference total, up to the drift.

```text
  2 * total₀ ≤ 3 * stake₀ (q ∩ active₀) + drift ω₀ ω
```
-/
theorem Supermajority.reference {ω : Weighing ν} {q : Finset ν} (ω₀ : Weighing ν)
    (hq : q ⊆ ω.voters) (h : ω.Supermajority q) :
    2 * Models.stake ω₀.stake ω₀.active ≤
      3 * Models.stake ω₀.stake (q ∩ ω₀.active) + drift ω₀ ω := by
  -- The signed stake splits into reference-active signers and voters outside the reference.
  have hsplit : Models.stake ω.stake q ≤ Models.stake ω.stake (q ∩ ω₀.active) +
      Models.stake ω.stake (ω.voters \ ω₀.active) := by
    rw [← stake_inter_add_sdiff ω.stake q ω₀.active]
    exact Nat.add_le_add_left (stake_mono (Finset.sdiff_subset_sdiff hq le_rfl)) _
  -- Reference-active signers hold at most their reference stake plus their gains.
  have hgain : Models.stake ω.stake (q ∩ ω₀.active) ≤ Models.stake ω₀.stake (q ∩ ω₀.active) +
      ∑ v ∈ ω₀.active, (ω.stake v - ω₀.stake v) := by
    calc Models.stake ω.stake (q ∩ ω₀.active)
        ≤ ∑ v ∈ q ∩ ω₀.active, (ω₀.stake v + (ω.stake v - ω₀.stake v)) :=
          Finset.sum_le_sum fun _ _ => by omega
      _ = Models.stake ω₀.stake (q ∩ ω₀.active) + ∑ v ∈ q ∩ ω₀.active, (ω.stake v - ω₀.stake v) :=
          Finset.sum_add_distrib
      _ ≤ _ := Nat.add_le_add_left
          (Finset.sum_le_sum_of_subset (Finset.inter_subset_right)) _
  -- The reference total splits into validators still active in `ω` and the ones that left.
  have htotal : Models.stake ω₀.stake ω₀.active ≤ Models.stake ω.stake ω.active +
      ∑ v ∈ ω₀.active, (ω₀.stake v - ω.stake v) + Models.stake ω₀.stake (ω₀.active \ ω.active) := by
    rw [← stake_inter_add_sdiff ω₀.stake ω₀.active ω.active]
    refine Nat.add_le_add_right ?_ _
    calc ∑ v ∈ ω₀.active ∩ ω.active, ω₀.stake v
        ≤ ∑ v ∈ ω₀.active ∩ ω.active, (ω.stake v + (ω₀.stake v - ω.stake v)) :=
          Finset.sum_le_sum fun _ _ => by omega
      _ = ∑ v ∈ ω₀.active ∩ ω.active, ω.stake v +
            ∑ v ∈ ω₀.active ∩ ω.active, (ω₀.stake v - ω.stake v) :=
          Finset.sum_add_distrib
      _ ≤ _ := Nat.add_le_add
          (stake_mono Finset.inter_subset_right)
          (Finset.sum_le_sum_of_subset Finset.inter_subset_left)
  have h' := h
  unfold Supermajority at h'
  unfold drift
  -- `max floor x` lies between `x` and `x + floor`.
  have hmax₁ := le_max_right ω.floor (Models.stake ω.stake ω.active)
  have hmax₂ : max ω.floor (Models.stake ω.stake q) ≤ ω.floor + Models.stake ω.stake q := by omega
  omega

end Weighing

namespace Dynamic

variable {ν β : Type*} [Preorder β]

/-- A supermajority link from `s` to `t`, weighed by `ω`.

The source comes before the target, in epoch and in the chain of the target, as in Casper FFG §2.

The weighing is one that `W` allows for the target.

Its signers pass its two-thirds test. -/
def SupermajorityLink (W : Checkpoint β → Set (Weighing ν)) (votes : Set (Vote ν β))
    (s t : Checkpoint β) (ω : Weighing ν) : Prop :=
  s.epoch < t.epoch ∧ s.block ≤ t.block ∧ ω ∈ W t ∧ ω.Supermajority (ω.signers votes s t)

/-- The justified checkpoints: the genesis checkpoint, and each target of a supermajority link
from a justified source. -/
inductive Justified (W : Checkpoint β → Set (Weighing ν)) (genesis : β) (votes : Set (Vote ν β)) :
    Checkpoint β → Prop
  /-- The genesis checkpoint is justified. -/
  | root : Justified W genesis votes ⟨genesis, 0⟩
  /-- A supermajority link from a justified checkpoint justifies its target. -/
  | link {s t : Checkpoint β} {ω : Weighing ν} :
      Justified W genesis votes s → SupermajorityLink W votes s t ω →
        Justified W genesis votes t

/-- The checkpoint `c` is `k`-finalized, as in Gasper Definition 4.9.

The shape is the one of `Ffg.KFinalized`, with a weighed link. -/
def KFinalized (W : Checkpoint β → Set (Weighing ν)) (genesis : β) (votes : Set (Vote ν β))
    (k : ℕ) (c : Checkpoint β) : Prop :=
  ∃ b : ℕ → β, b 0 = c.block ∧ (∀ i < k, b i ≤ b (i + 1)) ∧
    (∀ i < k, Justified W genesis votes ⟨b i, c.epoch + i⟩) ∧
    ∃ ω, SupermajorityLink W votes c ⟨b k, c.epoch + k⟩ ω

/-- The finalized checkpoints: genesis, and every `k`-finalized checkpoint with `k ≥ 1`. -/
def Finalized (W : Checkpoint β → Set (Weighing ν)) (genesis : β) (votes : Set (Vote ν β))
    (c : Checkpoint β) : Prop :=
  c = ⟨genesis, 0⟩ ∨ ∃ k, 1 ≤ k ∧ KFinalized W genesis votes k c

/-- Two supermajority links whose votes break a slashing condition for every validator.

Both targets have epochs in `[lo, hi]`.

So every validator that signs both links is slashable. -/
def Evidence (W : Checkpoint β → Set (Weighing ν)) (votes : Set (Vote ν β)) (lo hi : ℕ) :
    Prop :=
  ∃ s₁ t₁ ω₁ s₂ t₂ ω₂, SupermajorityLink W votes s₁ t₁ ω₁ ∧ SupermajorityLink W votes s₂ t₂ ω₂ ∧
    lo ≤ t₁.epoch ∧ t₁.epoch ≤ hi ∧ lo ≤ t₂.epoch ∧ t₂.epoch ≤ hi ∧
    ∀ v : ν, DoubleVote (⟨v, s₁, t₁⟩ : Vote ν β) ⟨v, s₂, t₂⟩ ∨
      SurroundVote (⟨v, s₁, t₁⟩ : Vote ν β) ⟨v, s₂, t₂⟩

variable {W : Checkpoint β → Set (Weighing ν)} {genesis : β} {votes : Set (Vote ν β)}

/-- A link of the static model is a link with the static weighing. -/
theorem supermajorityLink_static_iff {V : Finset ν} {w : ν → ℕ} {s t : Checkpoint β} :
    Ffg.SupermajorityLink V w votes s t ↔
      ∃ ω, SupermajorityLink (fun _ => {Weighing.static V w}) votes s t ω := by
  constructor
  · rintro ⟨hlt, hle, hsm⟩
    exact ⟨_, hlt, hle, rfl, by simpa [Weighing.Supermajority, Weighing.static,
      Weighing.signers] using hsm⟩
  · rintro ⟨ω, hlt, hle, rfl, hsm⟩
    exact ⟨hlt, hle, by simpa [Weighing.Supermajority, Weighing.static,
      Weighing.signers] using hsm⟩

/-- The static model is the dynamic one with the static weighing for every target. -/
theorem justified_static_iff {V : Finset ν} {w : ν → ℕ} {c : Checkpoint β} :
    Ffg.Justified V w genesis votes c ↔
      Justified (fun _ => {Weighing.static V w}) genesis votes c := by
  constructor
  · intro h
    induction h with
    | root => exact .root
    | link _ hl ih =>
      obtain ⟨_, hl⟩ := supermajorityLink_static_iff.mp hl
      exact .link ih hl
  · intro h
    induction h with
    | root => exact .root
    | link _ hl ih => exact .link ih (supermajorityLink_static_iff.mpr ⟨_, hl⟩)

/-- Finalization of the static model is finalization with the static weighing. -/
theorem finalized_static_iff {V : Finset ν} {w : ν → ℕ} {c : Checkpoint β} :
    Ffg.Finalized V w genesis votes c ↔
      Finalized (fun _ => {Weighing.static V w}) genesis votes c := by
  simp only [Ffg.Finalized, Finalized, Ffg.KFinalized, KFinalized, justified_static_iff,
    supermajorityLink_static_iff]

namespace Evidence

/-- Evidence in a window is evidence in every wider window. -/
theorem widen {lo hi lo' hi' : ℕ} (h : Evidence W votes lo hi) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    Evidence W votes lo' hi' := by
  obtain ⟨s₁, t₁, ω₁, s₂, t₂, ω₂, h₁, h₂, a, b, c, d, hv⟩ := h
  exact ⟨s₁, t₁, ω₁, s₂, t₂, ω₂, h₁, h₂, by omega, by omega, by omega, by omega, hv⟩

/-- Two different links with one target epoch are evidence of a double vote. -/
theorem double {s₁ t₁ s₂ t₂ : Checkpoint β} {ω₁ ω₂ : Weighing ν}
    (h₁ : SupermajorityLink W votes s₁ t₁ ω₁) (h₂ : SupermajorityLink W votes s₂ t₂ ω₂)
    (hne : s₁ ≠ s₂ ∨ t₁ ≠ t₂) (he : t₁.epoch = t₂.epoch) {lo hi : ℕ}
    (hlo : lo ≤ t₁.epoch) (hhi : t₁.epoch ≤ hi) : Evidence W votes lo hi :=
  ⟨s₁, t₁, ω₁, s₂, t₂, ω₂, h₁, h₂, hlo, hhi, he ▸ hlo, he ▸ hhi,
    fun _ => .inl ⟨fun h => by cases h; simp at hne, he⟩⟩

/-- A link that surrounds another is evidence of a surround vote. -/
theorem surround {s₁ t₁ s₂ t₂ : Checkpoint β} {ω₁ ω₂ : Weighing ν}
    (h₁ : SupermajorityLink W votes s₁ t₁ ω₁) (h₂ : SupermajorityLink W votes s₂ t₂ ω₂)
    (hs : s₁.epoch < s₂.epoch) (ht : t₂.epoch < t₁.epoch) {lo hi : ℕ}
    (hlo : lo ≤ t₂.epoch) (hhi : t₁.epoch ≤ hi) : Evidence W votes lo hi :=
  ⟨s₁, t₁, ω₁, s₂, t₂, ω₂, h₁, h₂, by omega, hhi, hlo, by omega,
    fun _ => .inr ⟨hs, h₂.1, ht⟩⟩

end Evidence

/-- Gasper Lemma 4.11, with a weighing per link.

Two justified checkpoints of one epoch are equal, or there is evidence at that epoch. -/
theorem Justified.eq_or_evidence {c₁ c₂ : Checkpoint β}
    (h₁ : Justified W genesis votes c₁) (h₂ : Justified W genesis votes c₂)
    (he : c₁.epoch = c₂.epoch) : c₁ = c₂ ∨ Evidence W votes c₁.epoch c₁.epoch := by
  cases h₁ with
  | root =>
    cases h₂ with
    | root => exact .inl rfl
    | link _ hl => exact absurd he (by have := hl.1; dsimp at this ⊢; omega)
  | link _ hl₁ =>
    cases h₂ with
    | root => exact absurd he (by have := hl₁.1; dsimp at this ⊢; omega)
    | link _ hl₂ =>
      by_cases hc : c₁ = c₂
      · exact .inl hc
      · exact .inr (Evidence.double hl₁ hl₂ (.inr hc) he le_rfl le_rfl)

/-- A finalized checkpoint is justified. -/
theorem Finalized.justified {c : Checkpoint β} (h : Finalized W genesis votes c) :
    Justified W genesis votes c := by
  rcases h with rfl | ⟨k, hk, b, hb, -, hj, -⟩
  · exact .root
  · simpa [hb] using hj 0 hk

/-- Gasper Lemma 5.1, with a weighing per link.

Take a finalized checkpoint `f` and a justified checkpoint `j` with a later epoch.

Then the block of `f` is in the chain of the block of `j`.

Otherwise there is evidence with both target epochs between the epochs of `f` and `j`. -/
theorem Finalized.le_or_evidence {f j : Checkpoint β}
    (hf : Finalized W genesis votes f) (hj : Justified W genesis votes j)
    (hlt : f.epoch < j.epoch) : f.block ≤ j.block ∨ Evidence W votes f.epoch j.epoch := by
  induction hj with
  | root => exact absurd hlt (Nat.not_lt_zero _)
  | @link s t ω hs hl ih =>
    rcases lt_trichotomy s.epoch f.epoch with hsf | hsf | hsf
    · -- The link starts before `f`, so `f` is `k`-finalized with `k ≥ 1`.
      rcases hf with rfl | ⟨k, hk, b, hb, hchain, hjust, ω', hlink⟩
      · exact absurd hsf (Nat.not_lt_zero _)
      rcases lt_trichotomy t.epoch (f.epoch + k) with htk | htk | htk
      · -- The target shares its epoch with a justified checkpoint of the finalization.
        have hi : t.epoch - f.epoch < k := by omega
        rcases (Justified.link hs hl).eq_or_evidence (hjust _ hi)
          (by dsimp; omega) with heq | h
        · rw [heq, ← hb]
          exact .inl (le_of_chain hchain _ hi.le)
        · exact .inr (h.widen (by omega) le_rfl)
      · -- The two links share a target epoch, and their sources differ in epoch.
        exact .inr (Evidence.double hl hlink
          (.inl fun h => by rw [h] at hsf; exact lt_irrefl _ hsf) htk (by omega) le_rfl)
      · -- The link surrounds the link that finalizes `f`.
        exact .inr (Evidence.surround hl hlink hsf htk (by dsimp; omega) le_rfl)
    · -- The source shares its epoch with `f`, so it is `f` itself.
      rcases hs.eq_or_evidence hf.justified hsf with rfl | h
      · exact .inl hl.2.1
      · exact .inr (h.widen (by omega) (by have := hl.1; omega))
    · rcases ih hsf with h | h
      · exact .inl (h.trans hl.2.1)
      · exact .inr (h.widen le_rfl (by have := hl.1; omega))

/-- Accountable safety with a weighing per link.

Take two finalized checkpoints whose blocks conflict.

Then two supermajority links break a slashing condition for every validator that signs both.

Both target epochs lie between the epochs of the two finalized checkpoints. -/
theorem evidence_of_conflicting {c₁ c₂ : Checkpoint β}
    (h₁ : Finalized W genesis votes c₁) (h₂ : Finalized W genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) :
    Evidence W votes (min c₁.epoch c₂.epoch) (max c₁.epoch c₂.epoch) := by
  rcases lt_trichotomy c₁.epoch c₂.epoch with h | h | h
  · exact ((h₁.le_or_evidence h₂.justified h).resolve_left hc.1).widen
      (min_le_left _ _) (le_max_right _ _)
  · rcases h₁.justified.eq_or_evidence h₂.justified h with rfl | e
    · exact absurd le_rfl hc.1
    · exact e.widen (min_le_left _ _) (le_max_left _ _)
  · exact ((h₂.le_or_evidence h₁.justified h).resolve_left hc.2).widen
      (min_le_right _ _) (le_max_left _ _)

/-- A finalized checkpoint and a justified checkpoint of no smaller epoch whose blocks conflict.

Then two supermajority links break a slashing condition for every validator that signs both.

Both target epochs lie between the two epochs.

A store can hold such a pair, with its justified and its finalized checkpoint from two branches. -/
theorem evidence_of_finalized_justified {f j : Checkpoint β}
    (hf : Finalized W genesis votes f) (hj : Justified W genesis votes j) (hle : f.epoch ≤ j.epoch)
    (hc : Conflicting f.block j.block) : Evidence W votes f.epoch j.epoch := by
  rcases hle.lt_or_eq with h | h
  · exact (hf.le_or_evidence hj h).resolve_left hc.1
  · rcases hf.justified.eq_or_evidence hj h with rfl | e
    · exact absurd le_rfl hc.1
    · exact e.widen le_rfl (by omega)

open scoped Classical in
/-- Evidence, measured in a reference weighing `ω₀`.

Suppose every weighing that `W` allows for a target in `[lo, hi]` drifts at most `D` from `ω₀`.

Then the slashable validators active in `ω₀` hold a third of its total, less `2 * D`:

```text
  total₀ ≤ 3 * slashable₀ + 2 * D
```
-/
theorem Evidence.stake_le [DecidableEq ν] {lo hi : ℕ} (h : Evidence W votes lo hi)
    (ω₀ : Weighing ν) {D : ℕ}
    (hD : ∀ t ω, ω ∈ W t → lo ≤ t.epoch → t.epoch ≤ hi → Weighing.drift ω₀ ω ≤ D) :
    stake ω₀.stake ω₀.active ≤
      3 * stake ω₀.stake {v ∈ ω₀.active | Slashable votes v} + 2 * D := by
  obtain ⟨s₁, t₁, ω₁, s₂, t₂, ω₂, h₁, h₂, hlo₁, hhi₁, hlo₂, hhi₂, hv⟩ := h
  have hq₁ : ω₁.signers votes s₁ t₁ ⊆ ω₁.voters := Finset.filter_subset _ _
  have hq₂ : ω₂.signers votes s₂ t₂ ⊆ ω₂.voters := Finset.filter_subset _ _
  have r₁ := h₁.2.2.2.reference ω₀ hq₁
  have r₂ := h₂.2.2.2.reference ω₀ hq₂
  have d₁ := hD _ _ h₁.2.2.1 hlo₁ hhi₁
  have d₂ := hD _ _ h₂.2.2.1 hlo₂ hhi₂
  set X₁ := ω₁.signers votes s₁ t₁ ∩ ω₀.active
  set X₂ := ω₂.signers votes s₂ t₂ ∩ ω₀.active
  -- Two subsets of the reference set overlap in at least the stake they have beyond its total.
  have hinter : stake ω₀.stake X₁ + stake ω₀.stake X₂ ≤
      stake ω₀.stake (X₁ ∩ X₂) + stake ω₀.stake ω₀.active := by
    have hu : stake ω₀.stake (X₁ ∪ X₂) + stake ω₀.stake (X₁ ∩ X₂) =
        stake ω₀.stake X₁ + stake ω₀.stake X₂ := Finset.sum_union_inter
    have hle : stake ω₀.stake (X₁ ∪ X₂) ≤ stake ω₀.stake ω₀.active :=
      stake_mono (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
    omega
  -- Every validator in both sets signed both links, so it is slashable.
  have hsl : stake ω₀.stake (X₁ ∩ X₂) ≤
      stake ω₀.stake {v ∈ ω₀.active | Slashable votes v} := by
    refine stake_mono fun v hv' => ?_
    simp only [X₁, X₂, Finset.mem_inter, Weighing.signers, Ffg.signers,
      Finset.mem_filter] at hv'
    exact Finset.mem_filter.mpr ⟨hv'.1.2, _, hv'.1.1.2, _, hv'.2.1.2, rfl, rfl, hv v⟩
  omega

open scoped Classical in
/-- Accountable safety with a weighing per link, measured in a reference weighing.

Take two finalized checkpoints whose blocks conflict.

Let `D` bound the drift from `ω₀` of every weighing allowed for a target between their epochs.

Then the slashable validators active in `ω₀` hold a third of its total stake, less `2 * D`.

With `D = 0` this is Theorem 1 of Casper FFG §2.1. -/
theorem accountable_safety [DecidableEq ν] {c₁ c₂ : Checkpoint β}
    (h₁ : Finalized W genesis votes c₁) (h₂ : Finalized W genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) (ω₀ : Weighing ν) {D : ℕ}
    (hD : ∀ t ω, ω ∈ W t → min c₁.epoch c₂.epoch ≤ t.epoch → t.epoch ≤ max c₁.epoch c₂.epoch →
      Weighing.drift ω₀ ω ≤ D) :
    stake ω₀.stake ω₀.active ≤
      3 * stake ω₀.stake {v ∈ ω₀.active | Slashable votes v} + 2 * D :=
  (evidence_of_conflicting h₁ h₂ hc).stake_le ω₀ hD

/-- The static theorem `Ffg.accountable_safety` is the case of one static weighing. -/
theorem accountable_safety_static [DecidableEq ν] {V : Finset ν} {w : ν → ℕ}
    {c₁ c₂ : Checkpoint β}
    (h₁ : Ffg.Finalized V w genesis votes c₁) (h₂ : Ffg.Finalized V w genesis votes c₂)
    (hc : Conflicting c₁.block c₂.block) : OneThirdSlashable V w votes := by
  have := accountable_safety (finalized_static_iff.mp h₁) (finalized_static_iff.mp h₂) hc
    (Weighing.static V w) (D := 0) (by rintro _ _ rfl - -; simp)
  simpa [OneThirdSlashable, Weighing.static] using this

end Dynamic

end EthLib.Consensus.Models.Ffg
