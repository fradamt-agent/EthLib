module

public import EthLib.Consensus.Proofs.Transition.FfgProvenance
public import EthLib.Consensus.Proofs.Transition.Provenance.Finality

/-!
# Proofs: the FFG refinement of two histories from genesis

Two histories of the beacon chain start at one genesis state `g` and end at `a` and at `b`.

This file builds the `FfgRefinement` of the pair from the provenance proofs.

- Blocks: epoch-boundary pairs, `EpochBlock`, over the parent links of the actual blocks of both
  histories, with each child's slot.
- Evidence: a state with the zero root, or a cached header with the zero root, on either history.
- Signed votes: data that a validator signed in an attestation checked in a block of either
  history.
- Records: the weighing calls of either history, each with its own source and weighing.
- Justified: the justified checkpoints of every state of either history, and every checkpoint that
  a call justified.
- Finalized: the finalized checkpoint of every state of either history.

The provenance proofs give every field.

One fact behind `voters_signed` stays a hypothesis, `upgradeVoters`.

From Altair, a voter whose timely-target flag was set by the Altair upgrade, which translated
pending attestations, signed matching data.

The finalization rule needs the root of a checkpoint three epochs back to stay in the buffer:
`4 * SLOTS_PER_EPOCH ≤ SLOTS_PER_HISTORICAL_ROOT`.

`accountable_safety_histories` then states accountable safety for the two histories.

No collision resistance is assumed: the conclusion holds, or a hash with zero output is found.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

section Histories

variable (config checks) (g a b : ForkedBeaconState preset)

/-- A state that genesis reaches, and from which one of the two histories continues to its end. -/
def OnEither (x : ForkedBeaconState preset) : Prop :=
  Reaches config checks g x ∧ (Reaches config checks x a ∨ Reaches config checks x b)

/-- The parent links of the actual blocks of both histories. -/
def historyLinks (p r : Root) (slot : ℕ) : Prop :=
  ∃ x, OnEither config checks g a b x ∧
    ∃ s : Slot, ChainBlockAt config checks g x p r s ∧ s.toNat = slot

/-- A hash with zero output on either history: a state root or a cached header root. -/
def historyEvidence : Prop :=
  ∃ x, OnEither config checks g a b x ∧
    (ZeroRootFound config checks g x ∨ ZeroHeaderFound config checks g x)

/-- The fact that the provenance proofs leave open, as a hypothesis. -/
structure HistoryObligations : Prop where
  /-- From Altair, a voter whose flag was there at the start or came from the Altair upgrade
  signed data with the call's source and target. -/
  upgradeVoters : ∀ x, OnEither config checks g a b x →
    ∀ (fork : Base.Fork) (state cached weighed next : BeaconState preset fork)
      (voters : List ValidatorIndex) (c : Checkpoint),
      WeighingCall config checks g x fork state cached weighed next voters c →
      .altair ≤ fork → ∀ i ∈ voters,
        (FlagAtStart g i.toNat TIMELY_TARGET_FLAG_INDEX ∨
          FlagFromAltairUpgrade config checks g ⟨fork, state⟩ i.toNat TIMELY_TARGET_FLAG_INDEX
            c.epoch) →
        ∃ data, data.target = c ∧ SignedVote config checks g ⟨fork, state⟩ i data ∧
          data.source = recordSource cached c.epoch

end Histories

/-- The genesis checkpoint maps to the genesis block. -/
theorem genesis_toFfg {links : Root → Root → ℕ → Prop} {spe : ℕ} :
    Checkpoint.toModel (EpochBlock.ofCheckpoint (links := links) (slotsPerEpoch := spe))
        ⟨GENESIS_EPOCH, Vector.replicate 32 0⟩ = ⟨⟨none⟩, 0⟩ := by
  simp [Checkpoint.toModel, EpochBlock.ofCheckpoint, GENESIS_EPOCH]

/-- Ancestry along blocks of one history past the first slot of an epoch is ancestry in the pair
order of both histories. -/
theorem pastAncestor_history {g a b x : ForkedBeaconState preset}
    (hx : OnEither config checks g a b x) {e : ℕ} {r r' : Root}
    (path : PastAncestor config checks g x (e * preset.SLOTS_PER_EPOCH.toNat) r r') :
    Relation.ReflTransGen
      (EpochBlock.after (historyLinks config checks g a b) preset.SLOTS_PER_EPOCH.toNat e) r r' :=
  Relation.ReflTransGen.mono (fun _ _ ⟨s, at_, lt⟩ => ⟨s.toNat, ⟨x, hx, s, at_, rfl⟩, lt⟩) _ _
    path

/-- The FFG refinement of two histories from genesis. -/
def historyRefinement {g a b : ForkedBeaconState preset} (genesis : Genesis config checks g)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (within : ∀ (fork : Base.Fork) (state : BeaconState preset fork),
      Reaches config checks g ⟨fork, state⟩ → state.RegistryWithinLimit)
    (open_ : HistoryObligations config checks g a b) :
    FfgRefinement
      (EpochBlock (historyLinks config checks g a b) preset.SLOTS_PER_EPOCH.toNat) where
  block := EpochBlock.ofCheckpoint
  genesis := ⟨none⟩
  evidence := historyEvidence config checks g a b
  signed := {p | ∃ y x, OnEither config checks g a b x ∧ Reaches config checks y x ∧
    SignedVote config checks g y p.1 p.2}
  records := {r | ∃ x, OnEither config checks g a b x ∧
    ∃ (fork : Base.Fork) (state cached weighed next : BeaconState preset fork)
      (voters : List ValidatorIndex) (c : Checkpoint),
      WeighingCall config checks g x fork state cached weighed next voters c ∧
      r = ⟨recordSource cached c.epoch, c, Weighing.ofState cached voters.toFinset⟩}
  justified := {c | ∃ x, OnEither config checks g a b x ∧ JustifiedOrStart config checks g x c}
  finalized := {c | ∃ x, OnEither config checks g a b x ∧ c = x.state.finalizedCheckpoint}
  justified_recorded := by
    rintro c ⟨x, hx, j⟩
    obtain ⟨-, previous, current, finalized⟩ := genesis_state genesis
    rcases j with rfl | rfl | rfl | ⟨fork, state, cached, weighed, next, voters, call⟩
    · exact .inl (by rw [finalized]; exact genesis_toFfg)
    · exact .inl (by rw [previous]; exact genesis_toFfg)
    · exact .inl (by rw [current]; exact genesis_toFfg)
    · exact .inr ⟨_, ⟨x, hx, fork, state, cached, weighed, next, voters, c, call, rfl⟩, rfl⟩
  source_justified := by
    rintro r ⟨x, hx, fork, state, cached, weighed, next, voters, c, call, rfl⟩
    exact ⟨x, hx, (call.source ⟨g, genesis, .refl g⟩).1⟩
  source_lt_target := by
    rintro r ⟨x, hx, fork, state, cached, weighed, next, voters, c, call, rfl⟩
    exact (call.source ⟨g, genesis, .refl g⟩).2
  source_le_target := by
    rintro r ⟨x, hx, fork, state, cached, weighed, next, voters, c, call, rfl⟩
    have fromStart : g.state.slot.toNat ≤ c.epoch.toNat * preset.SLOTS_PER_EPOCH.toNat := by
      rw [(genesis_state genesis).1]
      exact Nat.zero_le _
    rcases call.source_pastAncestor (by omega) genesis with zero | path | found
    · exact .inl (EpochBlock.ofCheckpoint_le (.inl zero))
    · rcases call.target_nonzero (by omega) fromStart with nonzero | header
      · exact .inl (EpochBlock.ofCheckpoint_le (.inr ⟨
          (call.source ⟨g, genesis, .refl g⟩).2.le, pastAncestor_history hx path, nonzero⟩))
      · exact .inr ⟨x, hx, .inr header⟩
    · exact .inr ⟨x, hx, .inl found⟩
  voters_signed := by
    rintro r ⟨x, hx, fork, state, cached, weighed, next, voters, c, call, rfl⟩ i hi
    simp only [Weighing.ofState, List.mem_toFinset] at hi
    have member : ∀ data, SignedVote config checks g ⟨fork, state⟩ i data →
        (i, data) ∈ {p : ValidatorIndex × AttestationData | ∃ y x, OnEither config checks g a b x ∧
          Reaches config checks y x ∧ SignedVote config checks g y p.1 p.2} :=
      fun data signed => ⟨⟨fork, state⟩, x, hx, call.toAfter, signed⟩
    by_cases altair : .altair ≤ fork
    · rcases call.voters_signed_of_reachable (by omega) ⟨g, genesis, .refl g⟩ altair i hi with
        start | upgraded | ⟨data, target, signed, source⟩
      · obtain ⟨data, target, signed, source⟩ :=
          open_.upgradeVoters x hx fork state cached weighed next voters c call altair i hi
            (.inl start)
        exact ⟨data, member data signed, source, target⟩
      · obtain ⟨data, target, signed, source⟩ :=
          open_.upgradeVoters x hx fork state cached weighed next voters c call altair i hi
            (.inr upgraded)
        exact ⟨data, member data signed, source, target⟩
      · exact ⟨data, member data signed.vote, source, target⟩
    · obtain ⟨data, target, -, signed, source⟩ :=
        call.pending_voters_signed_of_genesis lookahead genesis (Nat.lt_of_not_le altair) i hi
      exact ⟨data, member data signed, source, target⟩
  threshold := by
    rintro r ⟨x, hx, fork, state, cached, weighed, next, voters, c, call, rfl⟩
    have cachedWithin : cached.RegistryWithinLimit := by
      have := within fork state call.head
      unfold BeaconState.RegistryWithinLimit at this ⊢
      rw [(processSlot_keeps call.cachedOk).2.1]
      exact this
    have active : ∀ i ∈ voters, i ∈ getActiveValidatorIndices cached c.epoch := by
      by_cases altair : .altair ≤ fork
      · exact TargetVoters.active altair call.counted
      · intro i mem
        obtain ⟨_, _, activeAt, _⟩ :=
          call.pending_voters_signed_of_genesis lookahead genesis (Nat.lt_of_not_le altair) i mem
        exact activeAt
    exact supermajority_of_threshold call.passes cachedWithin fun i mem =>
      activeAt_lt ((mem_active_iff cachedWithin).mp (active i mem))
  finalized_rule := by
    rintro c ⟨x, hx, rfl⟩
    rcases Reaches.finalized_rule wide4 genesis hx.1 with genesisCheckpoint |
      ⟨k, hk, -, cs, h0, epochs, justified, ancestors, nonzero, fork, state, cached, weighed, next,
        voters, call, source⟩
    · exact .inl (by rw [genesisCheckpoint]; exact genesis_toFfg)
    refine .inr ⟨k, hk, cs, h0, epochs, fun i hi => ⟨x, hx, justified i hi⟩, fun i hi => ?_,
      _, ⟨x, hx, fork, state, cached, weighed, next, voters, cs k, call, rfl⟩, source, rfl⟩
    rcases ancestors i hi with path | zero
    · rcases nonzero (i + 1) hi (Nat.le_add_left 1 i) with ne | header
      · have ei := epochs i hi.le
        have ej := epochs (i + 1) hi
        exact .inl (EpochBlock.ofCheckpoint_le (.inr ⟨by omega, pastAncestor_history hx path, ne⟩))
      · exact .inr ⟨x, hx, .inr header⟩
    · exact .inr ⟨x, hx, .inl zero⟩

open scoped Classical in
/-- Accountable safety for two histories of the beacon chain from one genesis.

Take a state on each history, or two states of one, whose finalized checkpoints conflict as
epoch-boundary pairs: neither is the epoch-boundary block, at its epoch, of the other's chain,
through the parent links of both histories.

Take a reference weighing `ω₀`, and a bound `D` on the drift from it of every weighing call of
either history with a target between the two finalized epochs.

Then validators active in `ω₀` with a third of its total stake, less `2 * D`, each signed two
attestation data, both checked in blocks of the histories, that the beacon chain slashes.

Otherwise a state or a cached block header of the histories has the zero root.

The open obligation is the voters of the Altair upgrade. -/
theorem accountable_safety_histories {g a b : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (within : ∀ (fork : Base.Fork) (state : BeaconState preset fork),
      Reaches config checks g ⟨fork, state⟩ → state.RegistryWithinLimit)
    (open_ : HistoryObligations config checks g a b)
    {x₁ x₂ : ForkedBeaconState preset} (on₁ : OnEither config checks g a b x₁)
    (on₂ : OnEither config checks g a b x₂)
    (conflicting : Conflicting
      (EpochBlock.ofCheckpoint (links := historyLinks config checks g a b)
        (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat)
        x₁.state.finalizedCheckpoint)
      (EpochBlock.ofCheckpoint x₂.state.finalizedCheckpoint))
    (ω₀ : Weighing ValidatorIndex) {D : ℕ}
    (hD : ∀ r ∈ (historyRefinement genesis wide4 lookahead within open_).records,
      min x₁.state.finalizedCheckpoint.epoch.toNat x₂.state.finalizedCheckpoint.epoch.toNat ≤
        r.target.epoch.toNat →
      r.target.epoch.toNat ≤
        max x₁.state.finalizedCheckpoint.epoch.toNat x₂.state.finalizedCheckpoint.epoch.toNat →
      Weighing.drift ω₀ r.weighing ≤ D) :
    stake ω₀.stake ω₀.active ≤
      3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2,
        (i, data1) ∈ (historyRefinement genesis wide4 lookahead within open_).signed ∧
        (i, data2) ∈ (historyRefinement genesis wide4 lookahead within open_).signed ∧
        isSlashableAttestationData data1 data2 = true} + 2 * D ∨
      historyEvidence config checks g a b :=
  (historyRefinement genesis wide4 lookahead within open_).accountable_safety
    ⟨x₁, on₁, rfl⟩ ⟨x₂, on₂, rfl⟩ conflicting ω₀ hD

open scoped Classical in
/-- Accountable safety for a finalized checkpoint and a later justified one of two histories.

`xF` is a state on the histories, and its finalized checkpoint is `F`.

`xJ` is a state on the histories, and its current justified checkpoint is `J`.

A fork-choice store holds such a pair: its finalized and its justified checkpoint each come from
a state that its chain reached, possibly on different branches.

If the epoch of `F` is at most that of `J` and they conflict as epoch-boundary pairs, which is
what a store's failed descent check gives, the conclusion of
`accountable_safety_histories` holds. -/
theorem accountable_safety_histories_justified {g a b : ForkedBeaconState preset}
    (genesis : Genesis config checks g)
    (wide4 : 4 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    (lookahead : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (within : ∀ (fork : Base.Fork) (state : BeaconState preset fork),
      Reaches config checks g ⟨fork, state⟩ → state.RegistryWithinLimit)
    (open_ : HistoryObligations config checks g a b)
    {xF xJ : ForkedBeaconState preset} (onF : OnEither config checks g a b xF)
    (onJ : OnEither config checks g a b xJ)
    (hle : xF.state.finalizedCheckpoint.epoch.toNat ≤
      xJ.state.currentJustifiedCheckpoint.epoch.toNat)
    (conflicting : Conflicting
      (EpochBlock.ofCheckpoint (links := historyLinks config checks g a b)
        (slotsPerEpoch := preset.SLOTS_PER_EPOCH.toNat)
        xF.state.finalizedCheckpoint)
      (EpochBlock.ofCheckpoint xJ.state.currentJustifiedCheckpoint))
    (ω₀ : Weighing ValidatorIndex) {D : ℕ}
    (hD : ∀ r ∈ (historyRefinement genesis wide4 lookahead within open_).records,
      xF.state.finalizedCheckpoint.epoch.toNat ≤ r.target.epoch.toNat →
      r.target.epoch.toNat ≤ xJ.state.currentJustifiedCheckpoint.epoch.toNat →
      Weighing.drift ω₀ r.weighing ≤ D) :
    stake ω₀.stake ω₀.active ≤
      3 * stake ω₀.stake {i ∈ ω₀.active | ∃ data1 data2,
        (i, data1) ∈ (historyRefinement genesis wide4 lookahead within open_).signed ∧
        (i, data2) ∈ (historyRefinement genesis wide4 lookahead within open_).signed ∧
        isSlashableAttestationData data1 data2 = true} + 2 * D ∨
      historyEvidence config checks g a b :=
  (historyRefinement genesis wide4 lookahead within open_).accountable_safety_justified
    ⟨xF, onF, rfl⟩ ⟨xJ, onJ, onJ.1.checkpoints.2.2⟩ hle conflicting ω₀ hD

end EthLib.Consensus
