module

public import EthLib.Consensus.Proofs.Transition.Genesis
public import Mathlib.Logic.Relation

/-!
# Direct Phase 0 finality safety definitions

These expressions record executions of the beacon state transition and measure their stake.

They do not assert accountable safety.

The epoch-order argument follows Casper FFG §2 and Gasper §4 and §5.

The checkpoints and attestations here are the spec's data.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Serialization.Ssz Serialization.Ssz.SszType

section Finality

abbrev FinalityState (p : Preset) := BeaconState p .phase0
abbrev FinalityBlock (p : Preset) := SignedBeaconBlock p .phase0

variable {p : Preset}

/-- Execute a list of Phase 0 blocks with validation enabled. -/
def finalityRuns (cfg : Config) (checks : SignatureChecks) (eng : ExecutionEngine p .phase0)
    (s : FinalityState p) (bs : List (FinalityBlock p)) (t : FinalityState p) : Prop :=
  bs.foldlM (fun s b => stateTransition cfg checks eng s b true) s = .ok t

/-- Initialization succeeds and the resulting state satisfies the genesis launch checks. -/
def finalityInitialized (cfg : Config) (checks : SignatureChecks) (g : FinalityState p) : Prop :=
  (∃ h t ds, initializeBeaconStateFromEth1 cfg checks h t ds = .ok g) ∧
    isValidGenesisState cfg g = true

/-- Block inputs and outputs, intermediate slot inputs, and successful slot caches.

Coverage of effective-balance minima is a separate execution-composition obligation. -/
def finalityObservations (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) (s : FinalityState p)
    (bs : List (FinalityBlock p)) : List (FinalityState p) :=
  s :: bs.zipIdx.flatMap fun (b, i) =>
    match (bs.take i).foldlM (fun s b => stateTransition cfg checks eng s b true) s with
    | .error _ => []
    | .ok before =>
      (stateTransition cfg checks eng before b true).toOption.toList ++
      before :: (List.range (b.message.slot.toNat - before.slot.toNat)).flatMap fun n =>
        match advanceSlots cfg n before with
        | .error _ => []
        | .ok atStep => atStep :: (processSlot atStep).toOption.toList

/-- Whether an index names a validator active in the state's current epoch. -/
def finalityActive (s : FinalityState p) (i : Nat) : Bool :=
  match s.validators.data[i]? with
  | none => false
  | some v => isActiveValidator v (getCurrentEpoch s)

/-- Effective balance at an index, or zero outside the registry. -/
def finalityEffective (s : FinalityState p) (i : Nat) : Nat :=
  match s.validators.data[i]? with
  | none => 0
  | some v => v.effectiveBalance.toNat

/-- Raw active effective stake at C, without the total-balance increment floor. -/
def finalityStake (c : FinalityState p) : Nat :=
  ((List.range c.validators.data.size).map fun i =>
    if finalityActive c i then finalityEffective c i else 0).sum

/-- Remaining effective-balance capacity of C-active validators under the Phase 0 cap. -/
def finalityDeficit (c : FinalityState p) : Nat :=
  ((List.range c.validators.data.size).map fun i =>
    if finalityActive c i then p.MAX_EFFECTIVE_BALANCE.toNat - finalityEffective c i else 0).sum

/-- Maximum of a natural-valued observation, with zero for an empty history. -/
def finalityMaxOn (ss : List (FinalityState p)) (f : FinalityState p → Nat) : Nat :=
  (ss.map f).foldl max 0

/-- Largest observed drop below C per C-active validator, summed once per index. -/
def finalityLoss (c : FinalityState p) (ss : List (FinalityState p)) : Nat :=
  ((List.range c.validators.data.size).map fun i =>
    if finalityActive c i then
      finalityMaxOn ss (fun s => finalityEffective c i - finalityEffective s i) else 0).sum

/-- Maximum added active weight outside C's active set, per one weighing state. -/
def finalityAdditions (c : FinalityState p) (ss : List (FinalityState p)) : Nat :=
  finalityMaxOn ss fun s => ((List.range s.validators.data.size).map fun i =>
    if finalityActive c i then 0 else
      if finalityActive s i then finalityEffective s i else 0).sum

/-- Reference weight absent from at least one observed denominator, counted once per index. -/
def finalityExits (c : FinalityState p) (ss : List (FinalityState p)) : Nat :=
  ((List.range c.validators.data.size).map fun i =>
    if finalityActive c i && ss.any (fun s => !(finalityActive s i))
    then finalityEffective c i else 0).sum

/-- Previous-epoch voting weight missing from the current-active denominator. -/
def finalityPreviousGap (ss : List (FinalityState p)) : Nat :=
  finalityMaxOn ss fun s => (s.validators.data.toList.map fun v =>
    if isActiveValidator v (getPreviousEpoch s) && !isActiveValidator v (getCurrentEpoch s)
    then v.effectiveBalance.toNat else 0).sum

/-- A signer of an attestation successfully checked at its actual processing site after C. -/
def FinalityIncluded (cfg : Config) (checks : SignatureChecks) (eng : ExecutionEngine p .phase0)
    (c : FinalityState p) (bs : List (FinalityBlock p)) (i : ValidatorIndex)
    (d : AttestationData) : Prop :=
  ∃ earlier b later before atSlot inclusion recorded indexed attestation
      header randao eth1 proposers attesters attestationPrefix attestationSuffix,
    bs = earlier ++ b :: later ∧ finalityRuns cfg checks eng c earlier before ∧
    processSlots cfg before b.message.slot = .ok atSlot ∧
    processBlockHeader atSlot b.message = .ok header ∧
    processRandao cfg checks header b.message.body = .ok randao ∧
    processEth1Data (by decide) randao b.message.body = .ok eth1 ∧
    b.message.body.proposerSlashings.data.toList.foldlM
      (processProposerSlashing cfg checks) eth1 = .ok proposers ∧
    b.message.body.attesterSlashings.data.toList.foldlM
      (processAttesterSlashing cfg checks) proposers = .ok attesters ∧
    b.message.body.attestations.data.toList =
      attestationPrefix ++ attestation :: attestationSuffix ∧
    attestationPrefix.foldlM (processAttestation cfg checks) attesters = .ok inclusion ∧
    processAttestation cfg checks inclusion attestation = .ok recorded ∧
    indexed.data = d ∧ i ∈ indexed.attestingIndices.data ∧
    isValidIndexedAttestation cfg checks inclusion indexed = .ok true ∧
    attestation.data = d ∧ getIndexedAttestation inclusion attestation = .ok indexed

/-- Two checked attestations included after C satisfy the spec's slashing-data test. -/
def FinalitySlashable (cfg : Config) (checks : SignatureChecks) (eng : ExecutionEngine p .phase0)
    (c : FinalityState p) (a b : List (FinalityBlock p)) (i : ValidatorIndex) : Prop :=
  ∃ x y, (FinalityIncluded cfg checks eng c a i x ∨ FinalityIncluded cfg checks eng c b i x) ∧
    (FinalityIncluded cfg checks eng c a i y ∨ FinalityIncluded cfg checks eng c b i y) ∧
    isSlashableAttestationData x y = true

/-- C-active effective stake whose indices have checked slashable evidence on the suffixes. -/
noncomputable def finalitySlashableStake (cfg : Config) (checks : SignatureChecks)
    (eng : ExecutionEngine p .phase0) (c : FinalityState p)
    (a b : List (FinalityBlock p)) : Nat := by
  classical
  exact ((List.range c.validators.data.size).map fun i =>
    if finalityActive c i ∧ FinalitySlashable cfg checks eng c a b i.toUInt64
    then finalityEffective c i else 0).sum

/-- Raw parent-root ancestry of actual blocks, used only for non-genesis checkpoints. -/
def FinalityAncestor (bs : List (FinalityBlock p)) (x y : Root) : Prop :=
  Relation.ReflTransGen (fun x y => ∃ b ∈ bs,
    b.message.parentRoot = x ∧ hashTreeRoot b.message = .ok y) x y

/-- Non-genesis checkpoints conflict when neither root is an ancestor of the other.

The genesis checkpoint is a sentinel and never conflicts. -/
def FinalityConflicting (bs : List (FinalityBlock p)) (x y : Checkpoint) : Prop :=
  x.epoch ≠ GENESIS_EPOCH ∧ y.epoch ≠ GENESIS_EPOCH ∧
    ¬FinalityAncestor bs x.root y.root ∧ ¬FinalityAncestor bs y.root x.root

/-- SSZ hash inputs from observed states, latest headers, blocks and block bodies.

Coverage of every binding reduction is a separate proof obligation. -/
def finalityMessages (ss : List (FinalityState p)) (bs : List (FinalityBlock p)) : List Bytes :=
  (ss.flatMap fun s =>
    ((valueTree (desc (FinalityState p)) (toValue s)).toOption.toList.flatMap (·.messages)) ++
    ((valueTree (desc BeaconBlockHeader) (toValue s.latestBlockHeader)).toOption.toList.flatMap
      (·.messages))) ++
  bs.flatMap fun b =>
    ((valueTree (desc (BeaconBlock p .phase0)) (toValue b.message)).toOption.toList.flatMap
      (·.messages)) ++
    ((valueTree (desc (BeaconBlockBody p .phase0)) (toValue b.message.body)).toOption.toList.flatMap
      (·.messages))

/-- The explicit search returns two different messages with the same SHA-256 digest. -/
def FinalityCollisionFound (ss : List (FinalityState p)) (bs : List (FinalityBlock p)) : Prop :=
  ∃ x y, findMessageCollision (finalityMessages ss bs) (finalityMessages ss bs) = some (x, y) ∧
    MessageCollision x y

/-- An observed state has zero SSZ root, with the actual SHA-256 input that produces zero.

Slot caching uses zero as the unfilled header-state-root sentinel.

This alternative records the cryptographic event instead of assuming it cannot occur. -/
def FinalityZeroRootFound (ss : List (FinalityState p)) (bs : List (FinalityBlock p)) : Prop :=
  ∃ s ∈ ss, ∃ tree message,
    hashTreeRoot s = .ok (Vector.replicate 32 0) ∧
    valueTree (desc (FinalityState p)) (toValue s) = .ok tree ∧
    message ∈ tree.messages ∧ message ∈ finalityMessages ss bs ∧
    message.size = 64 ∧
    Cryptography.Hash.Sha256.hash (ByteArray.mk message) =
      ByteArray.mk (Vector.replicate 32 0).toArray

/-- A concrete target query and its raw, floor-corrected two-thirds inequality. -/
def FinalityThreshold (s : FinalityState p) (e : Epoch) (is : List ValidatorIndex) : Prop :=
  ∃ attestations,
    getMatchingTargetAttestations s (by decide) e = .ok attestations ∧
    getUnslashedAttestingIndices s attestations = .ok is ∧
    2 * sumMarked s.validators.data
        (markIndices s.validators.data.size (getActiveValidatorIndices s (getCurrentEpoch s))) ≤
      3 * sumMarked s.validators.data (markIndices s.validators.data.size is) +
        3 * totalBalanceFloor s is

/-- Registry envelope for churn, including pre-C queued cohorts and suffix deposit slots.

The unit lower bound also covers the exit allocator's guard for arbitrary configurations. -/
def finalityChurnCap (cfg : Config) (c : FinalityState p) (n : Nat) : Nat :=
  max 1 (max cfg.MIN_PER_EPOCH_CHURN_LIMIT.toNat
    ((c.validators.data.size + (n + 1) * p.SLOTS_PER_EPOCH.toNat * p.MAX_DEPOSITS.toNat) /
      cfg.CHURN_LIMIT_QUOTIENT.toNat))

/-- Credit quotient at an actual successful slashing site, before effective-balance updates. -/
def FinalitySlashCredit (cfg : Config) (s t : FinalityState p) (i : ValidatorIndex)
    (r : Nat) : Prop :=
  slashValidator cfg s i = .ok t ∧
    ∃ v, getValidator s i = .ok v ∧
      r = v.effectiveBalance.toNat /
        (parameters p .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat

/-- Proposed horizon correction to be justified by safety and actual-cohort bounds.

Zero horizon needs a separate checkpoint-preservation proof. This definition proves no bound. -/
def finalityHorizonCorrection (cfg : Config) (c : FinalityState p) (n : Nat) : Nat :=
  if n = 0 then 0 else
    2 * finalityDeficit c +
      6 * (n + 1) * finalityChurnCap cfg c n * p.MAX_EFFECTIVE_BALANCE.toNat +
      6 * p.EFFECTIVE_BALANCE_INCREMENT.toNat

end Finality

end EthLib.Consensus
