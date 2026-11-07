module

public import EthLib.Consensus.Preset

/-!
# Proofs: the nonzero parameters of the named presets

The lawful SSZ types of the state, the block and the light client data need nonzero parameters.

At the mainnet and minimal presets each such parameter is a known positive number.

These instances let instance search find those lawful types at both presets.
-/

@[expose] public section

namespace EthLib.Consensus

/-! ## The mainnet preset -/
instance : NeZero Preset.mainnet.BYTES_PER_LOGS_BLOOM.toNat := ⟨by decide⟩
instance : NeZero Preset.mainnet.SYNC_COMMITTEE_SIZE.toNat := ⟨by decide⟩
instance : NeZero Preset.mainnet.SLOTS_PER_HISTORICAL_ROOT.toNat := ⟨by decide⟩
instance : NeZero Preset.mainnet.EPOCHS_PER_HISTORICAL_VECTOR.toNat := ⟨by decide⟩
instance : NeZero Preset.mainnet.EPOCHS_PER_SLASHINGS_VECTOR.toNat := ⟨by decide⟩
instance : NeZero Preset.mainnet.PTC_SIZE.toNat := ⟨by decide⟩
instance : NeZero Preset.mainnet.INCLUSION_LIST_COMMITTEE_SIZE.toNat := ⟨by decide⟩
instance : NeZero Preset.mainnet.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
instance : NeZero
    ((Preset.mainnet.MIN_SEED_LOOKAHEAD.toNat + 1) * Preset.mainnet.SLOTS_PER_EPOCH.toNat) :=
  ⟨by decide⟩
instance : NeZero (2 * Preset.mainnet.SLOTS_PER_EPOCH.toNat) := ⟨by decide⟩
instance : NeZero
    ((Preset.mainnet.MIN_SEED_LOOKAHEAD.toNat + 2) * Preset.mainnet.SLOTS_PER_EPOCH.toNat) :=
  ⟨by decide⟩

/-! ## The minimal preset -/
instance : NeZero Preset.minimal.BYTES_PER_LOGS_BLOOM.toNat := ⟨by decide⟩
instance : NeZero Preset.minimal.SYNC_COMMITTEE_SIZE.toNat := ⟨by decide⟩
instance : NeZero Preset.minimal.SLOTS_PER_HISTORICAL_ROOT.toNat := ⟨by decide⟩
instance : NeZero Preset.minimal.EPOCHS_PER_HISTORICAL_VECTOR.toNat := ⟨by decide⟩
instance : NeZero Preset.minimal.EPOCHS_PER_SLASHINGS_VECTOR.toNat := ⟨by decide⟩
instance : NeZero Preset.minimal.PTC_SIZE.toNat := ⟨by decide⟩
instance : NeZero Preset.minimal.INCLUSION_LIST_COMMITTEE_SIZE.toNat := ⟨by decide⟩
instance : NeZero Preset.minimal.MAX_COMMITTEES_PER_SLOT.toNat := ⟨by decide⟩
instance : NeZero
    ((Preset.minimal.MIN_SEED_LOOKAHEAD.toNat + 1) * Preset.minimal.SLOTS_PER_EPOCH.toNat) :=
  ⟨by decide⟩
instance : NeZero (2 * Preset.minimal.SLOTS_PER_EPOCH.toNat) := ⟨by decide⟩
instance : NeZero
    ((Preset.minimal.MIN_SEED_LOOKAHEAD.toNat + 2) * Preset.minimal.SLOTS_PER_EPOCH.toNat) :=
  ⟨by decide⟩

end EthLib.Consensus
