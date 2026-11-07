module

public import EthLib.Consensus.Proofs.Models.Ffg.Dynamic

/-!
# Casper FFG: the drift bound must reach across the two branches

`Dynamic.accountable_safety` loses twice a bound `D` on the drift from one reference weighing.

That bound must cover the weighings of both conflicting branches.

This file shows that facts about each branch alone cannot give it.

Two branches leave the genesis block.

On each branch every weighing is the same, so two weighings of one branch have drift zero.

Each branch finalizes a checkpoint at epoch 1, and the two blocks conflict.

No validator is slashable.

So `D` must be at least half the reference total, although the two finalized epochs are equal.

In the beacon chain such branches arise when two partitions each stop seeing the other's votes.

The inactivity leak and ejections then move each branch to its own validators.

Gasper §8.6 calls this the "ship of Theseus" case.

The paper is [arXiv 2003.03052v3](https://arxiv.org/abs/2003.03052v3).

So a useful `D` bounds the drift from a state that both branches share.
-/

@[expose] public section

namespace EthLib.Consensus.Models.Ffg.Dynamic

namespace BranchDrift

/-- The weighing of one branch: one validator with stake 1, which counts in the total and votes. -/
def weighing (x : Bool) : Weighing Bool :=
  ⟨{x}, {x}, fun _ => 1, 0⟩

/-- The weighings allowed for a target: the one of its branch, for the block `{x}` of branch `x`.

The genesis block is `∅`. -/
def weighings (t : Checkpoint (Finset Bool)) : Set (Weighing Bool) :=
  {ω | ∃ x, t.block = {x} ∧ ω = weighing x}

/-- The votes: validator `x` links genesis to `({x}, 1)`, then `({x}, 1)` to `({x}, 2)`. -/
def votes : Set (Vote Bool (Finset Bool)) :=
  {v | ∃ x : Bool, v = ⟨x, ⟨∅, 0⟩, ⟨{x}, 1⟩⟩ ∨ v = ⟨x, ⟨{x}, 1⟩, ⟨{x}, 2⟩⟩}

/-- A link that validator `x` votes for, to the block of branch `x`, is a supermajority link. -/
theorem link {x : Bool} {s : Checkpoint (Finset Bool)} {e : ℕ} (he : s.epoch < e)
    (hs : s.block ≤ {x}) (hv : (⟨x, s, ⟨{x}, e⟩⟩ : Vote Bool (Finset Bool)) ∈ votes) :
    SupermajorityLink weighings votes s ⟨{x}, e⟩ (weighing x) := by
  refine ⟨he, hs, ⟨x, rfl, rfl⟩, ?_⟩
  have hsigners : (weighing x).signers votes s ⟨{x}, e⟩ = {x} := by
    ext y
    simp only [Weighing.signers, Ffg.signers, weighing, Finset.mem_filter,
      Finset.mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hv⟩⟩
  rw [hsigners]
  simp [Weighing.Supermajority, weighing, stake]

/-- The checkpoint `({x}, 1)` is finalized, with `k = 1`. -/
theorem finalized (x : Bool) : Finalized weighings ∅ votes ⟨{x}, 1⟩ := by
  refine .inr ⟨1, le_rfl, fun _ => {x}, rfl, fun _ _ => le_rfl, ?_, ⟨weighing x, ?_⟩⟩
  · intro i hi
    obtain rfl : i = 0 := by omega
    exact .link .root (link (by simp) (Finset.empty_subset _) ⟨x, .inl rfl⟩)
  · exact link (by simp) le_rfl ⟨x, .inr rfl⟩

/-- No validator is slashable.

Each signs two votes with different target epochs, and neither surrounds the other. -/
theorem not_slashable (v : Bool) : ¬Slashable votes v := by
  rintro ⟨x, ⟨a, hx⟩, y, ⟨b, hy⟩, rfl, hv, h⟩
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp only at hv <;> subst hv <;> simp [DoubleVote, SurroundVote] at h

/-- Two weighings allowed for targets on one branch have drift zero. -/
theorem drift_eq_zero {t t' : Checkpoint (Finset Bool)} {ω ω' : Weighing Bool}
    (hω : ω ∈ weighings t) (hω' : ω' ∈ weighings t')
    (comparable : t.block ≤ t'.block ∨ t'.block ≤ t.block) : Weighing.drift ω ω' = 0 := by
  obtain ⟨x, hx, rfl⟩ := hω
  obtain ⟨y, hy, rfl⟩ := hω'
  rw [hx, hy] at comparable
  obtain rfl : x = y := by
    rcases comparable with h | h <;> simp at h <;> simp [h]
  simp [Weighing.drift, weighing, stake]

end BranchDrift

open BranchDrift in
/-- Facts about each branch alone cannot bound the drift that accountable safety needs.

There are two finalized checkpoints of one epoch, whose blocks conflict.

Every weighing has positive total stake.

Two weighings allowed for targets whose blocks are comparable have drift zero.

Yet no validator is slashable.

So take any reference weighing with positive total.

Some weighing between the two finalized epochs has drift at least half that total.

This is because `Dynamic.accountable_safety` needs `total₀ ≤ 2 * D`. -/
theorem exists_branches_not_slashable :
    ∃ (W : Checkpoint (Finset Bool) → Set (Weighing Bool))
      (votes : Set (Vote Bool (Finset Bool))) (c₁ c₂ : Checkpoint (Finset Bool)),
      Finalized W ∅ votes c₁ ∧ Finalized W ∅ votes c₂ ∧ Conflicting c₁.block c₂.block ∧
      c₁.epoch = c₂.epoch ∧
      (∀ t ω, ω ∈ W t → 0 < stake ω.stake ω.active) ∧
      (∀ t t' ω ω', ω ∈ W t → ω' ∈ W t' → (t.block ≤ t'.block ∨ t'.block ≤ t.block) →
        Weighing.drift ω ω' = 0) ∧
      ∀ v, ¬Slashable votes v := by
  refine ⟨weighings, votes, ⟨{true}, 1⟩, ⟨{false}, 1⟩, finalized true, finalized false,
    ⟨by decide, by decide⟩, rfl, ?_, fun _ _ _ _ => drift_eq_zero, not_slashable⟩
  rintro t _ ⟨x, -, rfl⟩
  simp [weighing, stake]

end EthLib.Consensus.Models.Ffg.Dynamic
