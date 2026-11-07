module

public import EthLib.Consensus.Proofs.Transition.Provenance.Finality

/-!
# Proofs: the latest header of a genesis state

A genesis state starts from an empty state whose latest header is the header of the genesis block.

That header sits at slot 0, and no deposit or activation at genesis writes the header.

So the latest header of a genesis state sits at the genesis slot.
-/

@[expose] public section

namespace EthLib.Consensus

open Base

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- The latest header of a genesis state sits at the genesis slot. -/
theorem genesis_latestBlockHeader_slot {forked : ForkedBeaconState preset}
    (genesis : Genesis config checks forked) :
    forked.state.latestBlockHeader.slot = GENESIS_SLOT := by
  obtain ⟨⟨_, _, _, computed⟩, _⟩ := genesis
  unfold initializeBeaconStateFromEth1 at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, ensure_ok_iff, liftSsz_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, deposited, depositedOk, activated, activatedOk, root, _, same⟩ :=
    computed
  have kept := (Kept.foldlM (fun _ _ _ ok => kept_genesisDeposit ok) depositedOk).trans
    (Kept.foldlM (fun _ _ _ ok => by
      simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, _, _, set⟩ := ok
      exact kept_setValidator set) activatedOk)
  rw [← same]
  change activated.latestBlockHeader.slot = GENESIS_SLOT
  rw [kept.latestBlockHeader]
  simp [emptyGenesisState, GENESIS_SLOT]

end EthLib.Consensus
