module

public import EthLib.Consensus.Proofs.Transition.EpochUpdates
public import Batteries.Data.Except
public import Mathlib.Data.Finset.Card

/-!
# Proofs: the count of changed activation epochs

Before Electra, changed activation indices form a subset of the selected queue prefix.

The prefix bounds their count even when a selected write preserves its old value.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {fork : Fork} {state after : BeaconState preset fork}

/-- The registry indices whose activation epoch changes. -/
def changedActivationIndices (state after : BeaconState preset fork) : Finset ValidatorIndex :=
  ((List.range state.validators.data.size).map Nat.toUInt64).toFinset.filter fun index =>
    activationEpochAt after index ≠ activationEpochAt state index

/-- The changed activation indices form a subset of the selected prefix.

Their count is therefore at most the applicable limit. -/
theorem processRegistryUpdates_changedActivationEpochs {config : Config}
    (before : fork < .pectra)
    (computed : processRegistryUpdates config state = .ok after) :
    ∃ updated : BeaconState preset fork,
      (List.range state.validators.data.size).foldlM (updateRegistryEntry config) state =
        .ok updated ∧
      let limit := if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
        else getValidatorChurnLimit config updated
      let selected := (activationQueue updated).take limit.toNat
      changedActivationIndices state after ⊆ selected.toFinset ∧
        (changedActivationIndices state after).card ≤ limit.toNat := by
  obtain ⟨updated, first, bounded, _, _, unchanged, _⟩ :=
    processRegistryUpdates_activationEpochs before computed
  refine ⟨updated, first, ?_⟩
  dsimp only
  have subset : changedActivationIndices state after ⊆
      ((activationQueue updated).take
        (if .dencun ≤ fork then getValidatorActivationChurnLimit config updated
          else getValidatorChurnLimit config updated).toNat).toFinset := by
    intro index member
    apply List.mem_toFinset.mpr
    -- An index outside the prefix cannot have a different activation epoch.
    by_contra outside
    exact (Finset.mem_filter.mp member).2 (unchanged index outside)
  exact ⟨subset, (Finset.card_le_card subset).trans ((List.toFinset_card_le _).trans bounded)⟩

end EthLib.Consensus
