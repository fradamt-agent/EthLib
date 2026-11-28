module

public import EthLib.Consensus.Proofs.ForkChoice.FastConfirmation.ConfirmedCallStep

/-!
# Proofs: the root of each call of the fast confirmation rule lies on later honest heads

The root that an honest call of the rule stores is an ancestor of later up-to-date honest heads.

This holds before Gloas, under the run premises and the obligations of each call.

That root is on those heads from the start of the following slot through the inclusive time limit.

Otherwise two honest stores collide, or accountable-safety evidence holds.
-/

@[expose] public section
namespace EthLib.Consensus.Models.Network
open Base Uint64 Models Serialization.Ssz SszType ConfirmedCalls

variable {preset : Preset} {fork : Fork} {config : Config}
  {sources : BlockSources preset fork} {anchorState : BeaconState preset fork}
  {anchorBlock : BeaconBlock preset fork} {assignment : Assignment preset}
  {genesisTimeMs : UInt64} {J : Set ValidatorIndex}
  {e : Execution (honestForkChoice config .bls sources anchorState anchorBlock assignment
    genesisTimeMs) J}

section
set_option hygiene false
local notation "S" i:arg x:arg => ((e.world i).state x)
local notation "T" i:arg => ((e.world i).time)
local notation "Ready" i:arg x:arg =>
  UpToDate config .bls sources (T i) ((e.world i).view x) (S i x)

/-- Before Gloas, the root stored by an honest call lies on each up-to-date honest head.

It covers heads from the start of the call's following slot through the inclusive time limit.

The alternatives are a collision of two honest stores and four kinds of accountable-safety evidence.

Before Electra it assumes the quorum drift bound, which also accepts a collision of honest stores.
-/
theorem Execution.confirmedWalk_end_on_honest_heads [DecidablePred (· ∈ J)]
    {Δ limit : ℕ} {horizon : Epoch} {anchor : Store preset fork} {g : ForkedBeaconState preset}
    -- Every fork before Gloas, Phase 0 included.
    (before : fork < .glamsterdam)
    -- An assumption on the run: before Electra its quorum drift is within each call's reserve.
    --
    -- No theorem derives it before Electra.
    (drift : fork < .pectra → QuorumDriftWithin (e := e) horizon limit)
    -- The run starts from genesis, verifies signatures with BLS and reaches the anchor state.
    (pre : Run config .bls g ⟨fork, anchorState⟩) (genesis : Genesis config .bls g)
    (anchorGenesis : secondsToMilliseconds anchorState.genesisTime = genesisTimeMs)
    (anchored : getForkchoiceStore config anchorState anchorBlock = .ok anchor)
    (anchorSlot : anchorBlock.slot = anchorState.slot)
    (anchorBoundary : isStartSlotAtEpoch preset anchorBlock.slot = .ok true)
    -- Every honest store starts at the anchor store.
    (initial : ∀ x ∈ J, e.start x = anchor)
    -- The anchor's latest header is the anchor block's, and its state root is zero.
    (anchorHeader : anchorState.latestBlockHeader.slot = anchorBlock.slot ∧
      anchorState.latestBlockHeader.proposerIndex = anchorBlock.proposerIndex ∧
      anchorState.latestBlockHeader.parentRoot = anchorBlock.parentRoot ∧
      SszType.hashTreeRoot anchorBlock.body = .ok anchorState.latestBlockHeader.bodyRoot)
    (anchorZero : anchorState.latestBlockHeader.stateRoot = Vector.replicate 32 0)
    (sync : e.Synchronous Δ) (slots : 0 < config.SLOT_DURATION_MS)
    (fits : DelayFits fork config genesisTimeMs Δ) (admitted : BlocksAdmitted e 0 Δ limit)
    (votes : ValidatedDutyVotes (e := e) limit) (prompt : Prompt e limit)
    (windows : AssignmentWindowAgreement (e := e) limit) (fit : config.CommitteeWindowsFit preset)
    (minLookahead : 1 ≤ preset.MIN_SEED_LOOKAHEAD.toNat)
    (exitWindow : preset.SeedLookaheadAtLeastThree)
    (ring : preset.MIN_SEED_LOOKAHEAD.toNat + 3 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (long : 1 < preset.SLOTS_PER_EPOCH) (parameters : DirectSafety.Parameters preset)
    (half : 2 * config.CONFIRMATION_BYZANTINE_THRESHOLD.toNat ≤ 100)
    (maxAligned : MaxEffectiveBalancesAligned preset)
    (increment : preset.EFFECTIVE_BALANCE_INCREMENT.toNat % 100 = 0)
    (band : preset.IncrementWithinUpwardBand) (delay : preset.InclusionDelayPositive)
    (withdrawDelay : 1 ≤ config.MIN_VALIDATOR_WITHDRAWABILITY_DELAY.toNat)
    (caps : CapOrder preset) (activation : ActivationWithinMaxEffective preset)
    -- The horizon precedes the next scheduled fork.
    (forkWindow : ∀ next ∈ config.nextFork fork, horizon.toNat < next.2.toNat)
    (bounded : HonestStoreEpochsBounded (e := e) horizon limit)
    (roots : HeldBlockStateRootsNonzero (e := e) limit) (absent : AnchorParentAbsent (e := e) limit)
    (unslashed : HonestCountedStatesUnslashed (e := e) limit)
    (ceiling : CheckpointStakeCeiling (e := e) (2 * 10 ^ 17) limit)
    (scoreFits : config.ProposerScoreFits preset (2 * 10 ^ 17))
    (enough : HeldRunStakeFloor (e := e) pre horizon limit)
    (terminal : HeldTerminalStakeFloor (e := e) horizon limit)
    -- An assumption on the run: the justification of each call's epoch is pinned.
    --
    -- No endpoint derives it; from Fulu up to Gloas it follows only from further premises.
    (pinned : JustifiedPinned (e := e) anchor.justifiedCheckpoint.epoch 0 0 limit)
    -- An assumption on the run: Byzantine stake is under two thirds in each vote-counting state.
    (byzantine : ByzantineCountedStake (e := e) anchor.justifiedCheckpoint.epoch 0 limit)
    (included : TargetIncluded (e := e) limit) (stale : StaleHeadVotersInWindow (e := e) limit)
    -- An honest store is up to date at or after the limit, and its slot has a checked predecessor.
    (reference : ∃ x ∈ J, ∃ m, ∃ ref finish : Slot, limit ≤ T m ∧ Ready m x ∧
      (S m x).getCurrentSlot config = .ok ref ∧ subChecked ref 1 = .ok finish)
    {u : ValidatorIndex} (caller : u ∈ J) {events : List ℕ} {firstSlot : Slot}
    -- An assumption on the run: the first slot's epoch is at least two.
    --
    -- It is also after the epoch of the anchor state.
    (confirmationEpoch : 2 ≤ computeEpochAtSlot preset firstSlot)
    (anchorEpochBefore : getCurrentEpoch anchorState < computeEpochAtSlot preset firstSlot)
    (upToDate : ∀ n ∈ events, Ready n u)
    -- The calls are at the starts of consecutive slots from the first slot.
    (atSlots : ∀ i n, events[i]? = some n → ∃ slot begin,
      (S n u).getCurrentSlot config = .ok slot ∧ slot.toNat = firstSlot.toNat + i ∧
      computeTimeAtSlotMs config genesisTimeMs slot = .ok begin ∧ T n = begin.toNat)
    {i n : ℕ} {fcr after : FastConfirmationStore}
    (calls : CallAt (e := e) u events (getFastConfirmationStore anchor) i n fcr after)
    -- Each call assumes its obligations, which no theorem derives.
    --
    -- Only the calls up to this one are read, so the run may end at this call.
    (obligations : ∀ j m input out,
      CallAt (e := e) u events (getFastConfirmationStore anchor) j m input out →
      CallObligations (e := e) 0 limit u m input out)
    -- The call's slot has a checked successor, whose start time is representable.
    {slot next : Slot} {following : UInt64}
    (slotOk : (S n u).getCurrentSlot config = .ok slot) (nextOk : addChecked slot 1 = .ok next)
    (followingOk : computeTimeAtSlotMs config genesisTimeMs next = .ok following) :
    (∀ w ∈ J, ∀ k hd, following.toNat ≤ T k → T k ≤ limit → Ready k w →
      (S k w).getHead config = .ok hd →
      (S k w).isAncestor ⟨hd.root, .pending⟩ ⟨after.confirmedRoot, .pending⟩ = .ok true) ∨
      HonestCollision (e := e) limit ∨ HistoricalDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreDirectSafetyEvidence (e := e) pre limit ∨
      CrossStoreJustifiedEvidence (e := e) pre limit ∨
        HeldStateFinalityEvidence (e := e) pre limit := by
  -- A receiver after the limit is not asked about, so a late following slot is vacuous.
  by_cases late : limit < following.toNat
  · exact .inl fun _ _ _ _ low high _ _ => absurd (low.trans high) (Nat.not_le_of_lt late)
  -- Otherwise the following slot starts by the limit.
  have followingLe : following.toNat ≤ limit := Nat.le_of_not_lt late
  obtain ⟨atSlot, begin, atSlotOk, -, beginOk, timeEq⟩ := atSlots i n calls.1
  rw [slotOk] at atSlotOk
  cases atSlotOk
  have nextEq := (addChecked_ok_iff.mp nextOk).2
  have le : slot ≤ next := UInt64.le_iff_toNat_le.mpr (by simp at nextEq; omega)
  obtain ⟨start, startOk, -, startLe⟩ := exists_timeAtSlotMs_of_le le followingOk
  rw [beginOk] at startOk
  cases startOk
  -- The call is at the start of its slot, so it is no later than the following slot.
  have bound : T n ≤ limit := by
    rw [timeEq]
    exact (UInt64.le_iff_toNat_le.mp startLe).trans followingLe
  -- Before Gloas the three assumptions from Gloas say nothing.
  have early : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  rcases e.callInvariant_of_run pre rfl anchorGenesis sync slots minLookahead exitWindow ring
      (fun gloas => absurd gloas early) (fun gloas => absurd gloas early)
      (fun gloas => absurd gloas early) admitted half long maxAligned votes fits prompt windows
      fit anchored anchorSlot anchorBoundary initial rfl increment bounded roots unslashed ceiling
      scoreFits parameters genesis enough terminal absent pinned anchorHeader anchorZero delay
      byzantine drift band withdrawDelay caps activation forkWindow included stale reference
      caller confirmationEpoch anchorEpochBefore upToDate atSlots obligations calls bound with
      holds | bad
  · -- The first clause of the call invariant covers the heads, whose ancestry reads their roots.
    refine .inl fun w member k hd low high ready headOk => ?_
    rw [← Store.isAncestor_getHead_root headOk]
    exact holds.1 slot next following slotOk nextOk followingOk (T k) low
      (Nat.lt_succ_of_le high) w member k hd rfl ready headOk
  · exact .inr bad
end

end EthLib.Consensus.Models.Network
