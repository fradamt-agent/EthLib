module

public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Proofs.Accessors
public import EthLib.Consensus.Proofs.Mutators
public import EthLib.Consensus.Proofs.Containers.Misc
public import EthLib.Consensus.Transition.Block
public import EthLib.Serialization.Proofs.Ssz.Typed.Root

/-!
# Proofs: the first steps of a block

Each step keeps the number of validators and the number of balances.

The header step stores the header of the block, and the RANDAO and vote steps change one field.

A valid proposer slashing slashes its proposer.

A valid attester slashing slashes a validator that signed both attestations.

Casper FFG never forbids a vote together with itself.

A valid indexed attestation has strictly increasing indices.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Cryptography.Bls Serialization.Ssz SszType

variable {preset : Preset} {fork : Base.Fork}

/-- The constructor index that a code names, so that codes are read back in one pass. -/
private def ctorIdxOfCode : UInt32 → Nat
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 4
  | 6 => 5
  | 7 => 6
  | 8 => 7
  | 9 => 8
  | 10 => 9
  | 11 => 10
  | 12 => 11
  | 13 => 12
  | 14 => 13
  | 15 => 14
  | 16 => 15
  | 17 => 16
  | 18 => 17
  | 19 => 18
  | 20 => 19
  | 21 => 20
  | 22 => 21
  | 23 => 22
  | 24 => 23
  | 25 => 24
  | 26 => 25
  | 27 => 26
  | 28 => 27
  | 29 => 28
  | 30 => 29
  | 31 => 30
  | 32 => 31
  | 33 => 32
  | 34 => 33
  | 35 => 34
  | 36 => 35
  | 37 => 36
  | 38 => 37
  | 39 => 38
  | 40 => 39
  | 41 => 40
  | 42 => 41
  | 43 => 42
  | 44 => 43
  | 45 => 44
  | 46 => 45
  | 47 => 46
  | 48 => 47
  | 49 => 48
  | 50 => 49
  | 51 => 50
  | 61 => 51
  | 62 => 52
  | 63 => 53
  | 64 => 54
  | 65 => 55
  | 52 => 56
  | 53 => 57
  | 54 => 58
  | 55 => 59
  | 66 => 60
  | 67 => 61
  | 68 => 62
  | 69 => 63
  | 70 => 64
  | 71 => 65
  | 72 => 66
  | 73 => 67
  | 74 => 68
  | _ => 0

/-- Two errors with one code come from one constructor. -/
theorem TransitionError.code_injective (e₁ e₂ : TransitionError) (h : e₁.code = e₂.code) :
    e₁.ctorIdx = e₂.ctorIdx := by
  -- Each code names the index of its constructor, so the code determines the index.
  have back : ∀ e : TransitionError, ctorIdxOfCode e.code = e.ctorIdx := by
    intro e
    cases e <;> rfl
  rw [← back e₁, ← back e₂, h]

theorem liftAccessor_ok {α : Type} {result : Except AccessorError α} {value : α} :
    liftAccessor result = .ok value ↔ result = .ok value :=
  mapError_ok_iff

theorem liftSsz_ok {α : Type} {result : Except Err α} {value : α} :
    liftSsz result = .ok value ↔ result = .ok value :=
  mapError_ok_iff

/-! ## The block header -/

/-- A valid block is at the slot of the state, after the latest block, and from its proposer.

Its parent is the latest block, and its proposer is not slashed. -/
theorem processBlockHeader_checks {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} (computed : processBlockHeader state block = .ok after) :
    block.slot = state.slot ∧ state.latestBlockHeader.slot < block.slot ∧
      getBeaconProposerIndex state = .ok block.proposerIndex ∧
      hashTreeRoot state.latestBlockHeader = .ok block.parentRoot ∧
      ∃ proposer, getValidator state block.proposerIndex = .ok proposer ∧
        proposer.slashed = false := by
  simp only [processBlockHeader, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, slot, _, newer, _, proposer, _, same, _, parent, _, parentSame, _, _, validator,
    found, _, notSlashed, _⟩ := computed
  subst same parentSame
  exact ⟨slot, newer, proposer, parent, validator, found, notSlashed⟩

/-- The header step stores the header of the block, with a zero state root, and nothing else. -/
theorem processBlockHeader_eq {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} (computed : processBlockHeader state block = .ok after) :
    ∃ bodyRoot, hashTreeRoot block.body = .ok bodyRoot ∧
      after = { state with
        latestBlockHeader :=
          { slot := block.slot, proposerIndex := block.proposerIndex,
            parentRoot := block.parentRoot, stateRoot := Vector.replicate 32 0, bodyRoot } } := by
  simp only [processBlockHeader, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, bodyRoot, body, _, _, _, _, stored⟩ := computed
  exact ⟨bodyRoot, body, stored.symm⟩

theorem sameSizes_processBlockHeader {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} (computed : processBlockHeader state block = .ok after) :
    SameSizes state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact SameSizes.refl state

/-! ## RANDAO -/

/-- The RANDAO step checks that the reveal is the proposer's signature of the current epoch.

It then mixes the hash of the reveal into the mix of the epoch, and changes nothing else. -/
theorem processRandao_eq {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    ∃ index proposer domain signingRoot mix,
      getBeaconProposerIndex state = .ok index ∧ getValidator state index = .ok proposer ∧
      getDomain config state DOMAIN_RANDAO = .ok domain ∧
      computeSigningRoot (getCurrentEpoch state) domain = .ok signingRoot ∧
      checks.verify (packBytes proposer.pubkey) (packBytes signingRoot)
        (packBytes body.randaoReveal) = true ∧
      getRandaoMix state (getCurrentEpoch state) = .ok mix ∧
      after = { state with
        randaoMixes := state.randaoMixes.set!
          (getCurrentEpoch state % preset.EPOCHS_PER_HISTORICAL_VECTOR).toNat
          (Vector.zipWith (· ^^^ ·) mix (sha256Bytes32 (packBytes body.randaoReveal))) } := by
  simp only [processRandao, bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨index, indexOk, proposer, found, domain, domainOk, signingRoot, rootOk, _, verified, mix,
    mixOk, stored⟩ := computed
  exact ⟨index, proposer, domain, signingRoot, mix, indexOk, found, domainOk, rootOk, verified,
    mixOk, stored.symm⟩

theorem sameSizes_processRandao {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) : SameSizes state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact SameSizes.refl state

/-- Mixing the current reveal preserves every different circular-buffer position.

Committee-seed stability needs this position inequality, not merely distinct epoch numbers. -/
theorem processRandao_mix_of_ne {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork} {epoch : Epoch}
    (computed : processRandao config checks state body = .ok after)
    (distinct : (epoch % preset.EPOCHS_PER_HISTORICAL_VECTOR).toNat ≠
      (getCurrentEpoch state % preset.EPOCHS_PER_HISTORICAL_VECTOR).toNat) :
    getRandaoMix after epoch = getRandaoMix state epoch := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  simp only [getRandaoMix, readCircular]
  split
  · rfl
  · congr 1
    exact Vector.getElem_set!_ne (toNat_mod_lt ‹_›) (Ne.symm distinct)

/-- Block randomness preserves recent attester seeds when the lookahead separates mix writes. -/
theorem processRandao_attester_seed {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork}
    {body : BeaconBlockBody preset fork} {epoch : Epoch}
    (positive : 0 < preset.MIN_SEED_LOOKAHEAD.toNat)
    (history : preset.MIN_SEED_LOOKAHEAD.toNat + 3 <
      preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    (computed : processRandao config checks state body = .ok after)
    (recent : epoch = getCurrentEpoch state ∨ epoch.toNat + 1 = (getCurrentEpoch state).toNat) :
    getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
  apply getSeed_congr
  intro shifted shiftedOk
  exact processRandao_mix_of_ne computed
    (attester_seed_positions positive history recent shiftedOk).1

/-- Mainnet block randomness preserves the attester seed of the current or previous epoch. -/
theorem processRandao_mainnet_attester_seed {config : Config} {checks : SignatureChecks}
    {state after : BeaconState Preset.mainnet fork}
    {body : BeaconBlockBody Preset.mainnet fork} {epoch : Epoch}
    (computed : processRandao config checks state body = .ok after)
    (recent : epoch = getCurrentEpoch state ∨ epoch.toNat + 1 = (getCurrentEpoch state).toNat) :
    getSeed after epoch DOMAIN_BEACON_ATTESTER =
      getSeed state epoch DOMAIN_BEACON_ATTESTER := by
  apply getSeed_congr
  intro shifted shiftedOk
  exact processRandao_mix_of_ne computed (mainnet_attester_seed_positions recent shiftedOk).1

/-! ## Votes on the deposit contract -/

/-- The vote step appends the vote.

It adopts the vote once more than half the slots of the period cast it.

It changes nothing else. -/
theorem processEth1Data_eq {before : fork < .hegota} {state after : BeaconState preset fork}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) :
    (after.eth1DataVotes before).data =
        (state.eth1DataVotes before).data.push (body.eth1Data before) ∧
      after.eth1Data before =
        (if preset.EPOCHS_PER_ETH1_VOTING_PERIOD.toNat * preset.SLOTS_PER_EPOCH.toNat <
            ((state.eth1DataVotes before).data.push (body.eth1Data before)).count
              (body.eth1Data before) * 2
          then body.eth1Data before else state.eth1Data before) ∧
      { after with eth1DataVotes := state.eth1DataVotes, eth1Data := state.eth1Data } = state := by
  simp only [processEth1Data] at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
      mulChecked_ok_iff] at computed
    obtain ⟨slots, ⟨_, product⟩, computed⟩ := computed
    rw [product] at computed
    split at computed <;>
      · simp only [pure, Except.pure, Except.ok.injEq] at computed
        subst computed
        simp_all
        try (intro; omega)
  · simp [throw, throwThe, MonadExcept.throw, MonadExceptOf.throw] at computed

theorem sameSizes_processEth1Data {before : fork < .hegota}
    {state after : BeaconState preset fork} {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) :
    SameSizes state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  rw [← rest]
  exact SameSizes.refl after

/-! ## Slashable votes and indexed attestations -/

/-- Casper FFG never forbids a vote together with itself. -/
theorem isSlashableAttestationData_self (data : AttestationData) :
    isSlashableAttestationData data data = false := by
  simp [isSlashableAttestationData]

/-- Two different votes for one target epoch are a double vote. -/
theorem isSlashableAttestationData_of_double {data1 data2 : AttestationData}
    (distinct : data1 ≠ data2) (sameTarget : data1.target.epoch = data2.target.epoch) :
    isSlashableAttestationData data1 data2 = true := by
  simp [isSlashableAttestationData, distinct, sameTarget]

/-- A vote whose source and target lie strictly around those of another is a surround vote. -/
theorem isSlashableAttestationData_of_surround {data1 data2 : AttestationData}
    (source : data1.source.epoch < data2.source.epoch)
    (target : data2.target.epoch < data1.target.epoch) :
    isSlashableAttestationData data1 data2 = true := by
  simp [isSlashableAttestationData, source, target]

/-- A valid indexed attestation has nonempty, strictly increasing indices.

From Gloas there are at most as many as one slot can hold. -/
theorem isValidIndexedAttestation_indices {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {attestation : IndexedAttestation preset fork}
    (valid : isValidIndexedAttestation config checks state attestation = .ok true) :
    attestation.attestingIndices.data.toList ≠ [] ∧
      attestation.attestingIndices.data.toList.Pairwise (· < ·) ∧
      (.glamsterdam ≤ fork →
        attestation.attestingIndices.data.toList.length ≤ maxAttesters preset fork) := by
  simp only [isValidIndexedAttestation] at valid
  split at valid
  · simp [pure, Except.pure] at valid
  · rename_i accepted
    simp only [not_or, not_and, Nat.not_lt, Decidable.not_not] at accepted
    obtain ⟨nonempty, sorted, bounded⟩ := accepted
    exact ⟨nonempty, sorted ▸ sortedSet_sorted _, bounded⟩

/-- A valid indexed attestation carries the aggregate signature of its validators on its data. -/
theorem isValidIndexedAttestation_signature {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {attestation : IndexedAttestation preset fork}
    (valid : isValidIndexedAttestation config checks state attestation = .ok true) :
    ∃ pubkeys domain signingRoot,
      attestation.attestingIndices.data.toList.toArray.mapM
          (fun index => do return packBytes (← liftAccessor (getValidator state index)).pubkey) =
        .ok pubkeys ∧
      getDomain config state DOMAIN_BEACON_ATTESTER (some attestation.data.target.epoch) =
        .ok domain ∧
      computeSigningRoot attestation.data domain = .ok signingRoot ∧
      checks.fastAggregateVerify pubkeys (packBytes signingRoot)
        (packBytes attestation.signature) = true := by
  simp only [isValidIndexedAttestation] at valid
  split at valid
  · simp [pure, Except.pure] at valid
  · simp only [bind_ok_iff, liftAccessor_ok, liftSsz_ok, pure, Except.pure,
      Except.ok.injEq] at valid
    obtain ⟨pubkeys, pubkeysOk, domain, domainOk, signingRoot, rootOk, verified⟩ := valid
    exact ⟨pubkeys, domain, signingRoot, pubkeysOk, domainOk, rootOk, verified⟩

/-! ## Proposer slashings -/

/-- A header signature passes when the key signs the header in the epoch of its slot. -/
theorem checkHeaderSignature_ok {config : Config} {checks : SignatureChecks}
    {state : BeaconState preset fork} {pubkey : BLSPubkey} {signed : SignedBeaconBlockHeader}
    {u : Unit} (computed : checkHeaderSignature config checks state pubkey signed = .ok u) :
    ∃ domain signingRoot,
      getDomain config state DOMAIN_BEACON_PROPOSER
          (some (computeEpochAtSlot preset signed.message.slot)) = .ok domain ∧
      computeSigningRoot signed.message domain = .ok signingRoot ∧
      checks.verify (packBytes pubkey) (packBytes signingRoot) (packBytes signed.signature) =
        true := by
  simp only [checkHeaderSignature, bind_ok_iff, ensure_ok_iff, liftAccessor_ok,
    liftSsz_ok] at computed
  obtain ⟨domain, domainOk, signingRoot, rootOk, verified⟩ := computed
  exact ⟨domain, signingRoot, domainOk, rootOk, verified⟩

/-- A valid proposer slashing holds two different headers of one slot and one proposer.

The proposer is slashable in the current epoch, and signed both headers. -/
theorem processProposerSlashing_checks {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    slashing.signedHeader1.message.slot = slashing.signedHeader2.message.slot ∧
      slashing.signedHeader1.message.proposerIndex =
        slashing.signedHeader2.message.proposerIndex ∧
      slashing.signedHeader1.message ≠ slashing.signedHeader2.message ∧
      ∃ proposer, getValidator state slashing.signedHeader1.message.proposerIndex = .ok proposer ∧
        isSlashableValidator proposer (getCurrentEpoch state) = true ∧
        checkHeaderSignature config checks state proposer.pubkey slashing.signedHeader1 =
          .ok () ∧
        checkHeaderSignature config checks state proposer.pubkey slashing.signedHeader2 =
          .ok () := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, slot, _, index, _, distinct, proposer, found, _, slashable, _, first, _, second,
    _⟩ := computed
  exact ⟨slot, index, distinct, proposer, found, slashable, first, second⟩

/-- A valid proposer slashing slashes its proposer. -/
theorem processProposerSlashing_slashed {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    slashedFlag after slashing.signedHeader1.message.proposerIndex = .ok true := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact (slashValidator_slashedFlag slashed).1

/-- A proposer slashing cannot pay a second reward for an already slashed validator. -/
theorem processProposerSlashing_ne_ok_of_slashed {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    (flag : slashedFlag state slashing.signedHeader1.message.proposerIndex = .ok true) :
    processProposerSlashing config checks state slashing ≠ .ok after := by
  intro computed
  obtain ⟨_, _, _, validator, found, slashable, _, _⟩ :=
    processProposerSlashing_checks computed
  have set : validator.slashed = true := by
    simpa [slashedFlag, found, Except.map] using flag
  simp [isSlashableValidator, set] at slashable

/-- A proposer slashing preserves every slashed flag that was already set. -/
theorem processProposerSlashing_slashedFlag {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after)
    {index : ValidatorIndex} (flag : slashedFlag state index = .ok true) :
    slashedFlag after index = .ok true := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  obtain ⟨set, others⟩ := slashValidator_slashedFlag slashed
  by_cases same : index = slashing.signedHeader1.message.proposerIndex
  · exact same ▸ set
  · exact (others index same).trans flag

/-- A successful list of proposer slashings names each slashed validator at most once.

This follows the checked operations, including preservation of flags between slashings. -/
theorem foldlM_processProposerSlashing_nodup {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashings : List ProposerSlashing}
    (computed : slashings.foldlM (processProposerSlashing config checks) state = .ok after) :
    (slashings.map (·.signedHeader1.message.proposerIndex)).Nodup := by
  have excludes : ∀ (items : List ProposerSlashing) (input output : BeaconState preset fork)
      (index : ValidatorIndex),
      items.foldlM (processProposerSlashing config checks) input = .ok output →
      slashedFlag input index = .ok true →
      index ∉ items.map (·.signedHeader1.message.proposerIndex) := by
    intro items
    induction items with
    | nil => simp
    | cons first rest ih =>
      intro input output index run flag
      obtain ⟨middle, firstOk, restOk⟩ := bind_ok_iff.mp run
      simp only [List.map_cons, List.mem_cons, not_or]
      refine ⟨?_, ih middle output index restOk
        (processProposerSlashing_slashedFlag firstOk flag)⟩
      intro equal
      exact processProposerSlashing_ne_ok_of_slashed (equal ▸ flag) firstOk
  induction slashings generalizing state with
  | nil => simp
  | cons first rest ih =>
    obtain ⟨middle, firstOk, restOk⟩ := bind_ok_iff.mp computed
    simp only [List.map_cons, List.nodup_cons]
    exact ⟨excludes rest middle after _ restOk (processProposerSlashing_slashed firstOk),
      ih restOk⟩

/-- Proposer slashings preserve each indexed effective balance before the next epoch update. -/
theorem processProposerSlashing_effectiveBalance_query {config : Config}
    {checks : SignatureChecks} {state after : BeaconState preset fork}
    {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after)
    (other : ValidatorIndex) :
    (getValidator after other).map (·.effectiveBalance) =
      (getValidator state other).map (·.effectiveBalance) := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact slashValidator_effectiveBalance_query slashed other

theorem sameSizes_processProposerSlashing {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    SameSizes state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact sameSizes_slashValidator slashed

/-! ## Attester slashings -/

/-- A proposer slashing preserves committee activity for an epoch no later than the current one.

Slashing excludes later participation tallies, but it does not reassign historical committees. -/
theorem processProposerSlashing_active {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : ProposerSlashing} {epoch : Epoch}
    (before : fork < .pectra) (past : epoch ≤ getCurrentEpoch state)
    (computed : processProposerSlashing config checks state slashing = .ok after)
    (other : ValidatorIndex) :
    (getValidator after other).map (isActiveValidator · epoch) =
      (getValidator state other).map (isActiveValidator · epoch) := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact slashValidator_active before past slashed other

/-- An already slashed validator cannot trigger another slashing or another reward. -/
theorem slashIfSlashable_eq_of_slashed {config : Config}
    {state : BeaconState preset fork} {slashedAny : Bool} {index : ValidatorIndex}
    (flag : slashedFlag state index = .ok true) :
    slashIfSlashable config (state, slashedAny) index = .ok (state, slashedAny) := by
  unfold slashedFlag at flag
  cases found : getValidator state index with
  | error error => simp [found, Except.map] at flag
  | ok validator =>
    have set : validator.slashed = true := by simpa [found, Except.map] using flag
    simp [slashIfSlashable, found, liftAccessor, Except.mapError, bind, Except.bind,
      isSlashableValidator, set, pure, Except.pure]

/-- A step of an attester slashing keeps the sizes, and keeps every slashed flag that is set.

The flag it returns is set only if it was set, or if the step slashed its validator. -/
theorem slashIfSlashable_ok {config : Config} {step after : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok after) :
    SameSizes step.1 after.1 ∧
      (∀ other, slashedFlag step.1 other = .ok true → slashedFlag after.1 other = .ok true) ∧
      (after.2 = true → step.2 = true ∨ slashedFlag after.1 index = .ok true) := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨slashedState, slashed, rfl⟩ := computed
    obtain ⟨flag, others⟩ := slashValidator_slashedFlag slashed
    refine ⟨sameSizes_slashValidator slashed, fun other set => ?_, fun _ => .inr flag⟩
    by_cases same : other = index
    · exact same ▸ flag
    · exact (others other same).trans set
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨SameSizes.refl _, fun _ set => set, .inl⟩

/-- The steps of an attester slashing over some indices keep the sizes and every set flag.

The flag they return is set only if it was set, or if they slashed one of the indices. -/
theorem foldlM_slashIfSlashable {config : Config} (indices : List ValidatorIndex) :
    ∀ {step after : BeaconState preset fork × Bool},
      indices.foldlM (slashIfSlashable config) step = .ok after →
      SameSizes step.1 after.1 ∧
        (∀ other, slashedFlag step.1 other = .ok true → slashedFlag after.1 other = .ok true) ∧
        (after.2 = true → step.2 = true ∨
          ∃ index ∈ indices, slashedFlag after.1 index = .ok true) := by
  induction indices with
  | nil =>
    intro step after computed
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨SameSizes.refl _, fun _ set => set, .inl⟩
  | cons first rest ih =>
    intro step after computed
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    obtain ⟨sizes, kept, flagged⟩ := slashIfSlashable_ok firstOk
    obtain ⟨restSizes, restKept, restFlagged⟩ := ih restOk
    refine ⟨sizes.trans restSizes, fun other set => restKept other (kept other set),
      fun done => ?_⟩
    rcases restFlagged done with middleFlag | ⟨index, member, flag⟩
    · rcases flagged middleFlag with stepFlag | flag
      · exact .inl stepFlag
      · exact .inr ⟨first, List.mem_cons_self, restKept first flag⟩
    · exact .inr ⟨index, List.mem_cons_of_mem first member, flag⟩

/-- After an index is slashed, removing its later occurrences cannot change the slashing fold.

Other slashings preserve its flag, so the removed steps pay no additional reward. -/
theorem foldlM_slashIfSlashable_filter_slashed {config : Config}
    (indices : List ValidatorIndex) {index : ValidatorIndex}
    {step after : BeaconState preset fork × Bool}
    (flag : slashedFlag step.1 index = .ok true)
    (computed : indices.foldlM (slashIfSlashable config) step = .ok after) :
    (indices.filter (· != index)).foldlM (slashIfSlashable config) step = .ok after := by
  induction indices generalizing step with
  | nil => exact computed
  | cons first rest ih =>
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, firstOk, restOk⟩ := computed
    by_cases same : first = index
    · subst first
      have unchanged := slashIfSlashable_eq_of_slashed flag (config := config)
        (slashedAny := step.2)
      rw [unchanged] at firstOk
      cases firstOk
      simpa using ih flag restOk
    · have kept := (slashIfSlashable_ok firstOk).2.1 index flag
      have restFiltered := ih kept restOk
      rw [List.filter_cons_of_pos (by simpa using same)]
      rw [List.foldlM_cons, bind_ok_iff]
      exact ⟨middle, firstOk, restFiltered⟩

/-- An attester-slashing step preserves every indexed effective balance. -/
theorem slashIfSlashable_effectiveBalance_query {config : Config}
    {step after : BeaconState preset fork × Bool} {index : ValidatorIndex}
    (computed : slashIfSlashable config step index = .ok after) (other : ValidatorIndex) :
    (getValidator after.1 other).map (·.effectiveBalance) =
      (getValidator step.1 other).map (·.effectiveBalance) := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨validator, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨slashed, slashedOk, rfl⟩ := computed
    exact slashValidator_effectiveBalance_query slashedOk other
  · cases computed
    rfl

/-- Every effective balance in an attester-slashing fold is its pre-fold effective balance. -/
theorem foldlM_slashIfSlashable_effectiveBalance_query {config : Config}
    (indices : List ValidatorIndex) {step after : BeaconState preset fork × Bool}
    (computed : indices.foldlM (slashIfSlashable config) step = .ok after)
    (other : ValidatorIndex) :
    (getValidator after.1 other).map (·.effectiveBalance) =
      (getValidator step.1 other).map (·.effectiveBalance) := by
  induction indices generalizing step with
  | nil => cases computed; rfl
  | cons index rest ih =>
    obtain ⟨middle, firstOk, restOk⟩ := bind_ok_iff.mp computed
    exact (ih restOk).trans (slashIfSlashable_effectiveBalance_query firstOk other)

/-- An attester-slashing fold has an equivalent execution of distinct newly slashed indices.

Repeated indices and validators already slashed before the fold pay no additional reward. -/
theorem foldlM_slashIfSlashable_distinct_paid {config : Config} (indices : List ValidatorIndex)
    {step after : BeaconState preset fork × Bool}
    (computed : indices.foldlM (slashIfSlashable config) step = .ok after) :
    ∃ paid : List ValidatorIndex,
      paid.Sublist indices ∧ paid.Nodup ∧
      paid.foldlM (slashIfSlashable config) step = .ok after ∧
      ∀ index ∈ paid,
        slashedFlag step.1 index ≠ .ok true ∧ slashedFlag after.1 index = .ok true := by
  induction indices generalizing step with
  | nil =>
    cases computed
    exact ⟨[], .refl _, by simp, rfl, by simp⟩
  | cons index rest ih =>
    obtain ⟨middle, first, tail⟩ := bind_ok_iff.mp computed
    obtain ⟨paid, subset, unique, paidOk, flags⟩ := ih tail
    have kept := (slashIfSlashable_ok first).2.1
    have read := first
    simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at read
    obtain ⟨validator, found, action⟩ := read
    split at action
    · rename_i slashable
      simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at action
      obtain ⟨slashed, slashedOk, equal⟩ := action
      have set : slashedFlag middle.1 index = .ok true := by
        rw [← equal]
        exact (slashValidator_slashedFlag slashedOk).1
      have absent : index ∉ paid := fun member => (flags index member).1 set
      refine ⟨index :: paid, subset.cons_cons _, List.nodup_cons.mpr ⟨absent, unique⟩, ?_, ?_⟩
      · exact bind_ok_iff.mpr ⟨middle, first, paidOk⟩
      · intro other member
        rcases List.mem_cons.mp member with rfl | member
        · refine ⟨?_, (foldlM_slashIfSlashable rest tail).2.1 other set⟩
          have clear : validator.slashed = false := by
            cases flag : validator.slashed <;> simp_all [isSlashableValidator]
          simp [slashedFlag, found, Except.map, clear]
        · exact ⟨fun old => (flags other member).1 (kept other old), (flags other member).2⟩
    · simp only [pure, Except.pure, Except.ok.injEq] at action
      have same : middle = step := action.symm
      refine ⟨paid, subset.cons _, unique, ?_, ?_⟩
      · simpa only [same] using paidOk
      · simpa only [same] using flags

/-- A newly set flag in a slashing fold identifies the actual call that slashed that index.

The prefix retains the state immediately before that call. -/
theorem foldlM_slashIfSlashable_flag_origin {config : Config} (indices : List ValidatorIndex)
    {step after : BeaconState preset fork × Bool} {index : ValidatorIndex}
    (computed : indices.foldlM (slashIfSlashable config) step = .ok after)
    (unset : slashedFlag step.1 index ≠ .ok true)
    (set : slashedFlag after.1 index = .ok true) :
    ∃ earlier later atStep slashed,
      indices = earlier ++ index :: later ∧
      earlier.foldlM (slashIfSlashable config) step = .ok atStep ∧
      slashValidator config atStep.1 index = .ok slashed ∧
      slashIfSlashable config atStep index = .ok (slashed, true) := by
  induction indices generalizing step with
  | nil => cases computed; exact (unset set).elim
  | cons first rest ih =>
    obtain ⟨middle, firstOk, restOk⟩ := bind_ok_iff.mp computed
    by_cases middleSet : slashedFlag middle.1 index = .ok true
    · have read := firstOk
      simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at read
      obtain ⟨validator, _, action⟩ := read
      split at action
      · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at action
        obtain ⟨slashed, slashedOk, equal⟩ := action
        have same : index = first := by
          by_cases distinct : index = first
          · exact distinct
          · apply False.elim
            apply unset
            have saved := (slashValidator_slashedFlag slashedOk).2 index distinct
            rw [← equal] at middleSet
            exact saved.symm.trans middleSet
        subst first
        exact ⟨[], rest, step, slashed, rfl, rfl, slashedOk, by simpa [← equal] using firstOk⟩
      · simp only [pure, Except.pure, Except.ok.injEq] at action
        exact (unset (by simpa only [← action] using middleSet)).elim
    · obtain ⟨earlier, later, atStep, slashed, split, prefixOk, slashedOk, action⟩ :=
        ih restOk middleSet
      refine ⟨first :: earlier, later, atStep, slashed, by simp [split], ?_, slashedOk, action⟩
      exact bind_ok_iff.mpr ⟨middle, firstOk, prefixOk⟩

/-- A valid attester slashing holds two valid attestations that Casper FFG forbids together. -/
theorem processAttesterSlashing_checks {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    isSlashableAttestationData slashing.attestation1.data slashing.attestation2.data = true ∧
      isValidIndexedAttestation config checks state slashing.attestation1 = .ok true ∧
      isValidIndexedAttestation config checks state slashing.attestation2 = .ok true := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, slashable, valid1, first, _, valid1True, valid2, second, _, valid2True, _⟩ := computed
  subst valid1True valid2True
  exact ⟨slashable, first, second⟩

/-- A valid attester slashing slashes a validator that signed both attestations. -/
theorem processAttesterSlashing_slashed {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    ∃ index, index ∈ slashing.attestation1.attestingIndices.data.toList ∧
      index ∈ slashing.attestation2.attestingIndices.data.toList ∧
      slashedFlag after index = .ok true := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, slashedAny⟩, foldOk, computed⟩ := computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, done, rfl⟩ := computed
  obtain ⟨_, _, flagged⟩ := foldlM_slashIfSlashable _ foldOk
  rcases flagged done with never | ⟨index, member, flag⟩
  · cases never
  · rw [slashingIndices, mem_sortedSet, List.mem_filter, decide_eq_true_iff] at member
    exact ⟨index, member.1, member.2, flag⟩

/-- Attester slashing preserves every slashed flag already set before the operation. -/
theorem processAttesterSlashing_slashedFlag {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after)
    {index : ValidatorIndex} (flag : slashedFlag state index = .ok true) :
    slashedFlag after index = .ok true := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, slashedAny⟩, foldOk, computed⟩ := computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact (foldlM_slashIfSlashable _ foldOk).2.1 index flag

/-- A successful attester slashing pays only distinct validators whose flags it newly sets.

The retained indices execute the same slashing fold, including its actual balance credits. -/
theorem processAttesterSlashing_distinct_paid {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    ∃ paid : List ValidatorIndex,
      paid.Sublist (slashingIndices slashing) ∧ paid.Nodup ∧
      paid.foldlM (slashIfSlashable config) (state, false) = .ok (after, true) ∧
      ∀ index ∈ paid,
        slashedFlag state index ≠ .ok true ∧ slashedFlag after index = .ok true := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, slashedAny⟩, foldOk, computed⟩ := computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, done, rfl⟩ := computed
  subst slashedAny
  exact foldlM_slashIfSlashable_distinct_paid _ foldOk

/-- Each distinct paid index has the exact two Phase 0 credits of its actual slashing call.

The reward uses its pre-operation effective balance, since slashings do not change that balance. -/
theorem processAttesterSlashing_paid_credits {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset .phase0} {slashing : AttesterSlashing preset .phase0}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    ∃ paid : List ValidatorIndex,
      paid.Sublist (slashingIndices slashing) ∧ paid.Nodup ∧
      paid.foldlM (slashIfSlashable config) (state, false) = .ok (after, true) ∧
      ∀ index ∈ paid,
        ∃ earlier later atStep slashed original validator lowered raised proposer whistleblower
            proposerReward whistleblowerReward,
          paid = earlier ++ index :: later ∧
          earlier.foldlM (slashIfSlashable config) (state, false) = .ok atStep ∧
          slashValidator config atStep.1 index = .ok slashed ∧
          getValidator state index = .ok original ∧
          getValidator atStep.1 index = .ok validator ∧
          getBeaconProposerIndex lowered = .ok proposer ∧ whistleblower = proposer ∧
          increaseBalance lowered proposer proposerReward = .ok raised ∧
          increaseBalance raised whistleblower whistleblowerReward = .ok slashed ∧
          proposerReward.toNat + whistleblowerReward.toNat =
            original.effectiveBalance.toNat /
              (parameters preset .phase0).WHISTLEBLOWER_REWARD_QUOTIENT.toNat := by
  obtain ⟨paid, subset, unique, paidOk, flags⟩ := processAttesterSlashing_distinct_paid computed
  refine ⟨paid, subset, unique, paidOk, ?_⟩
  intro index member
  obtain ⟨earlier, later, atStep, slashed, split, prefixOk, slashedOk, _⟩ :=
    foldlM_slashIfSlashable_flag_origin paid paidOk (flags index member).1 (flags index member).2
  obtain ⟨validator, lowered, raised, proposer, whistleblower, proposerReward,
    whistleblowerReward, found, proposerOk, recipient, raisedOk, finalOk, credits⟩ :=
    slashValidator_phase0_credits slashedOk
  have saved := foldlM_slashIfSlashable_effectiveBalance_query earlier prefixOk index
  rw [found] at saved
  cases originalFound : getValidator state index with
  | error error => simp [originalFound, Except.map] at saved
  | ok original =>
    have equal : validator.effectiveBalance = original.effectiveBalance := by
      simpa only [originalFound, Except.map, Except.ok.injEq] using saved
    exact ⟨earlier, later, atStep, slashed, original, validator, lowered, raised, proposer,
      whistleblower, proposerReward, whistleblowerReward, split, prefixOk, slashedOk,
      rfl, found, proposerOk, recipient, raisedOk, finalOk, by simpa [equal] using credits⟩

/-- Validators paid by different attester slashings in one list are disjoint.

Each operation retains its actual successful fold, not a bound on the registry size. -/
theorem foldlM_processAttesterSlashing_distinct_paid {config : Config}
    {checks : SignatureChecks} (slashings : List (AttesterSlashing preset fork))
    {state after : BeaconState preset fork}
    (computed : slashings.foldlM (processAttesterSlashing config checks) state = .ok after) :
    ∃ paid : List ValidatorIndex,
      paid.Nodup ∧
      (∀ index ∈ paid,
        slashedFlag state index ≠ .ok true ∧ slashedFlag after index = .ok true) ∧
      ∃ batches : List (List ValidatorIndex),
        batches.flatten = paid ∧ batches.length = slashings.length ∧
        batches.foldlM (fun s batch =>
          (batch.foldlM (slashIfSlashable config) (s, false)).map Prod.fst) state = .ok after ∧
        ∀ pair ∈ slashings.zip batches, pair.2.Sublist (slashingIndices pair.1) := by
  induction slashings generalizing state with
  | nil =>
    cases computed
    exact ⟨[], by simp, by simp, [], rfl, rfl, rfl, by simp⟩
  | cons first rest ih =>
    obtain ⟨middle, firstOk, restOk⟩ := bind_ok_iff.mp computed
    obtain ⟨paid, subset, unique, paidOk, flags⟩ := processAttesterSlashing_distinct_paid firstOk
    obtain ⟨tail, tailUnique, tailFlags, batches, flattened, count, batchesOk, subsets⟩ := ih restOk
    have kept : ∀ index, slashedFlag middle index = .ok true →
        slashedFlag after index = .ok true := by
      intro index flag
      exact foldlM_ok_invariant (fun s => slashedFlag s index = .ok true)
        (fun _ _ _ prior ok => processAttesterSlashing_slashedFlag ok prior) flag restOk
    refine ⟨paid ++ tail, List.nodup_append.mpr ⟨unique, tailUnique, ?_⟩, ?_,
      paid :: batches, by simp [flattened], by simp [count], ?_, ?_⟩
    · intro index member other otherMember equal
      subst other
      exact (tailFlags index otherMember).1 (flags index member).2
    · intro index member
      rcases List.mem_append.mp member with member | member
      · exact ⟨(flags index member).1, kept index (flags index member).2⟩
      · exact ⟨fun flag => (tailFlags index member).1
          (processAttesterSlashing_slashedFlag firstOk flag), (tailFlags index member).2⟩
    · simpa only [List.foldlM_cons, paidOk, Except.map, bind, Except.bind] using batchesOk
    · intro pair member
      rcases List.mem_cons.mp member with rfl | member
      · exact subset
      · exact subsets pair member

/-- A block's proposer and attester slashings pay disjoint sets of validators.

The attester batches retain an equivalent execution of their concrete slashing steps. -/
theorem proposer_attester_slashings_distinct_paid {config : Config} {checks : SignatureChecks}
    {proposers : List ProposerSlashing} {attesters : List (AttesterSlashing preset fork)}
    {state middle after : BeaconState preset fork}
    (proposerOk : proposers.foldlM (processProposerSlashing config checks) state = .ok middle)
    (attesterOk : attesters.foldlM (processAttesterSlashing config checks) middle = .ok after) :
    ∃ batches : List (List ValidatorIndex),
      ((proposers.map (·.signedHeader1.message.proposerIndex)) ++ batches.flatten).Nodup ∧
      batches.length = attesters.length ∧
      batches.foldlM (fun s batch =>
        (batch.foldlM (slashIfSlashable config) (s, false)).map Prod.fst) middle = .ok after ∧
      ∀ pair ∈ attesters.zip batches, pair.2.Sublist (slashingIndices pair.1) := by
  have flagged : ∀ index ∈ proposers.map (·.signedHeader1.message.proposerIndex),
      slashedFlag middle index = .ok true := by
    intro index member
    induction proposers generalizing state with
    | nil => simp at member
    | cons first rest ih =>
      obtain ⟨next, firstOk, restOk⟩ := bind_ok_iff.mp proposerOk
      rcases List.mem_cons.mp member with rfl | member
      · exact foldlM_ok_invariant (fun s => slashedFlag s _ = .ok true)
          (fun _ _ _ prior ok => processProposerSlashing_slashedFlag ok prior)
          (processProposerSlashing_slashed firstOk) restOk
      · exact ih restOk member
  obtain ⟨paid, unique, flags, batches, flattened, count, batchesOk, subsets⟩ :=
    foldlM_processAttesterSlashing_distinct_paid attesters attesterOk
  refine ⟨batches, ?_, count, batchesOk, subsets⟩
  rw [flattened]
  apply List.nodup_append.mpr
  refine ⟨foldlM_processProposerSlashing_nodup proposerOk, unique, ?_⟩
  intro index member other otherMember equal
  subst other
  exact (flags index otherMember).1 (flagged index member)

theorem sameSizes_processAttesterSlashing {config : Config} {checks : SignatureChecks}
    {state after : BeaconState preset fork} {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    SameSizes state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨folded, slashedAny⟩, foldOk, computed⟩ := computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact (foldlM_slashIfSlashable _ foldOk).1

/-- A beacon header has no variable-length counts in its SSZ commitment. -/
theorem beaconBlockHeader_commitmentSized (header : BeaconBlockHeader) :
    CommitmentSized (desc BeaconBlockHeader) (toValue header) := by
  apply CommitmentSized.container
  intro pair member
  simp only [desc, toValue, SszFields.descs, SszFields.toValues,
    List.zip_cons_cons, List.zip_nil_left, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact .uint _ _
  · exact .uint _ _
  · exact .byteVector _ _
  · exact .byteVector _ _
  · exact .byteVector _ _

/-- Equal header roots give equal headers or an explicit collision in their SHA-256 computations.

The returned search contains only messages actually hashed for these two headers. -/
theorem beaconBlockHeader_root_binding {left right : BeaconBlockHeader} {root : Root}
    (leftRoot : hashTreeRoot left = .ok root)
    (rightRoot : hashTreeRoot right = .ok root) :
    left = right ∨ ∃ leftTree rightTree,
      valueTree (desc BeaconBlockHeader) (toValue left) = .ok leftTree ∧
      valueTree (desc BeaconBlockHeader) (toValue right) = .ok rightTree ∧
      ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
        x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y :=
  SszType.hashTreeRoot_binding (beaconBlockHeader_commitmentSized left)
    (beaconBlockHeader_commitmentSized right) leftRoot rightRoot

/-- A processed block's parent root identifies the cached header or exposes a real hash collision.

The other header can come from the competing branch's recorded block history. -/
theorem processBlockHeader_parent_binding {state after : BeaconState preset fork}
    {block : BeaconBlock preset fork} {parent : BeaconBlockHeader}
    (computed : processBlockHeader state block = .ok after)
    (parentRoot : hashTreeRoot parent = .ok block.parentRoot) :
    state.latestBlockHeader = parent ∨ ∃ leftTree rightTree,
      valueTree (desc BeaconBlockHeader) (toValue state.latestBlockHeader) = .ok leftTree ∧
      valueTree (desc BeaconBlockHeader) (toValue parent) = .ok rightTree ∧
      ∃ x y, findMessageCollision leftTree.messages rightTree.messages = some (x, y) ∧
        x ∈ leftTree.messages ∧ y ∈ rightTree.messages ∧ MessageCollision x y :=
  beaconBlockHeader_root_binding (processBlockHeader_checks computed).2.2.2.1 parentRoot

end EthLib.Consensus
