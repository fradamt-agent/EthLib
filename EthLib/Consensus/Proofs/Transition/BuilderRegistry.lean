module

public import EthLib.Consensus.Proofs.Builders
public import EthLib.Consensus.Proofs.Transition.Upgrade
public import EthLib.Consensus.Proofs.Transition.Reachable

/-!
# Proofs: the registry of builders, along every chain

From Gloas a state holds a registry of builders, apart from the validators.

[EIP-7732] adds the builders, and [EIP-8282] their deposit and exit requests.

The registry only grows: no step removes a builder.

A builder keeps its key, version, address and deposit epoch, until its index goes to a new builder.

[EIP-8282] gives the index of a builder to a new one only once the old one is withdrawable.

So a new builder at an index has a deposit epoch no earlier than the old one could withdraw.

A builder starts to exit only by a request, and may then withdraw a fixed delay later.

A later deposit to a builder that has exited with nothing left moves its withdrawal later again.

So a withdrawable epoch that is set never moves back.

These facts hold in every state that a chain reaches, from a state in which they hold.

Each withdrawable epoch that is set is at most the delay after the current epoch.

That holds from the upgrade to Gloas on, since every builder then starts without an exit.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
[EIP-8282]: https://eips.ethereum.org/EIPS/eip-8282#consensus-layer-processing
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- The current epoch of a state, on natural numbers. -/
def epochNat (state : BeaconState preset fork) : Nat :=
  (getCurrentEpoch state).toNat

/-- The earliest epoch at which a builder of a state may withdraw, on natural numbers.

A builder that has started to exit may withdraw at its withdrawable epoch.

Any other builder may withdraw no earlier than the delay after the current epoch. -/
def withdrawFloor (config : Config) (state : BeaconState preset fork) (builder : Builder) : Nat :=
  if builder.withdrawableEpoch = FAR_FUTURE_EPOCH then
    epochNat state + config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat
  else builder.withdrawableEpoch.toNat

/-- Every withdrawable epoch that is set is at most the delay after the current epoch. -/
def BuildersBounded (config : Config) (state : BeaconState preset fork) : Prop :=
  ∀ (gloas : .glamsterdam ≤ fork), ∀ builder ∈ (state.builders gloas).data,
    builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH →
      builder.withdrawableEpoch.toNat ≤
        epochNat state + config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat

/-- Two builders with the same key, version, address and deposit epoch. -/
def SameBuilder (old new : Builder) : Prop :=
  new.pubkey = old.pubkey ∧ new.version = old.version ∧
    new.executionAddress = old.executionAddress ∧ new.depositEpoch = old.depositEpoch

/-- The builder at an index of a later state, given the builder there in a state.

Its withdrawable epoch is unset, or no earlier than the old builder could withdraw.

It is the same builder, or a new one that deposited no earlier than the old one could withdraw. -/
def BuilderFollows (config : Config) (state : BeaconState preset fork) (old new : Builder) :
    Prop :=
  (new.withdrawableEpoch = FAR_FUTURE_EPOCH ∨
      withdrawFloor config state old ≤ new.withdrawableEpoch.toNat) ∧
    (SameBuilder old new ∨ withdrawFloor config state old ≤ new.depositEpoch.toNat)

/-- The slot and the registry of builders of a state. -/
def builderView (state : BeaconState preset fork) :
    Slot × Since .glamsterdam fork Builders :=
  (state.slot, state.builders)

/-- The registry of a later state of the same fork.

The slot is the same, and the registry does not shrink.

From a state whose withdrawable epochs are within the delay, those of the later state are too.

Each builder of the first state is followed, at its index, by a builder of the later state. -/
structure BuildersAdvance (config : Config) (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  size : ∀ gloas, (state.builders gloas).data.size ≤ (after.builders gloas).data.size
  bounded : BuildersBounded config state → BuildersBounded config after
  follows : BuildersBounded config state → ∀ gloas (index : Nat) (old : Builder),
    (state.builders gloas).data[index]? = some old →
      ∃ new, (after.builders gloas).data[index]? = some new ∧ BuilderFollows config state old new

/-! ## The relation -/

/-- The current epoch does not move back when the slot does not. -/
theorem epochNat_le {state : BeaconState preset fork} {fork' : Base.Fork}
    {after : BeaconState preset fork'} (slot : state.slot ≤ after.slot) :
    epochNat state ≤ epochNat after := by
  unfold epochNat getCurrentEpoch computeEpochAtSlot
  rw [UInt64.toNat_div, UInt64.toNat_div]
  exact Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp slot)

/-- The floor of a builder does not move back along a step that it follows. -/
theorem withdrawFloor_le {state : BeaconState preset fork} {fork' : Base.Fork}
    {after : BeaconState preset fork'} {old new : Builder}
    (bounded : old.withdrawableEpoch ≠ FAR_FUTURE_EPOCH →
      old.withdrawableEpoch.toNat ≤ epochNat state + config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat)
    (slot : state.slot ≤ after.slot)
    (later : new.withdrawableEpoch = FAR_FUTURE_EPOCH ∨
      withdrawFloor config state old ≤ new.withdrawableEpoch.toNat) :
    withdrawFloor config state old ≤ withdrawFloor config after new := by
  have epochs := epochNat_le slot
  unfold withdrawFloor at later ⊢
  by_cases far : new.withdrawableEpoch = FAR_FUTURE_EPOCH
  · simp only [far, ↓reduceIte]
    split
    · omega
    · have := bounded ‹_›
      omega
  · simp only [far, ↓reduceIte, false_or] at later ⊢
    exact later

/-- A builder followed twice is followed. -/
theorem BuilderFollows.trans {state : BeaconState preset fork} {fork' : Base.Fork}
    {middle : BeaconState preset fork'} {old mid new : Builder}
    (bounded : old.withdrawableEpoch ≠ FAR_FUTURE_EPOCH →
      old.withdrawableEpoch.toNat ≤ epochNat state + config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat)
    (slot : state.slot ≤ middle.slot) (one : BuilderFollows config state old mid)
    (two : BuilderFollows config middle mid new) : BuilderFollows config state old new := by
  have floor := withdrawFloor_le bounded slot one.1
  obtain ⟨_, identity⟩ := one
  obtain ⟨withdrawable, identity'⟩ := two
  refine ⟨?_, ?_⟩
  · rcases withdrawable with far | le
    · exact .inl far
    · exact .inr (Nat.le_trans floor le)
  · rcases identity' with same' | le'
    · rcases identity with same | le
      · exact .inl ⟨same'.1.trans same.1, same'.2.1.trans same.2.1, same'.2.2.1.trans same.2.2.1,
          same'.2.2.2.trans same.2.2.2⟩
      · exact .inr (same'.2.2.2 ▸ le)
    · exact .inr (Nat.le_trans floor le')

/-- A builder is followed by itself. -/
theorem BuilderFollows.refl (state : BeaconState preset fork) (builder : Builder) :
    BuilderFollows config state builder builder := by
  refine ⟨?_, .inl ⟨rfl, rfl, rfl, rfl⟩⟩
  by_cases far : builder.withdrawableEpoch = FAR_FUTURE_EPOCH
  · exact .inl far
  · right
    simp only [withdrawFloor, far, ↓reduceIte, Nat.le_refl]

namespace BuildersAdvance

theorem refl (state : BeaconState preset fork) : BuildersAdvance config state state :=
  ⟨rfl, fun _ => Nat.le_refl _, id,
    fun _ _ _ old found => ⟨old, found, .refl state old⟩⟩

theorem trans {first second third : BeaconState preset fork}
    (one : BuildersAdvance config first second) (two : BuildersAdvance config second third) :
    BuildersAdvance config first third where
  slot := two.slot.trans one.slot
  size gloas := Nat.le_trans (one.size gloas) (two.size gloas)
  bounded := two.bounded ∘ one.bounded
  follows bounded gloas index old found := by
    obtain ⟨mid, midFound, oneFollows⟩ := one.follows bounded gloas index old found
    obtain ⟨new, newFound, twoFollows⟩ :=
      two.follows (one.bounded bounded) gloas index mid midFound
    exact ⟨new, newFound, oneFollows.trans
      (bounded gloas old (Array.mem_of_getElem? found)) (one.slot ▸ UInt64.le_refl _) twoFollows⟩

/-- A step that keeps the slot and the registry. -/
theorem of_eq (same : builderView after = builderView state) : BuildersAdvance config state after
    := by
  simp only [builderView, Prod.mk.injEq] at same
  obtain ⟨slot, builders⟩ := same
  have bounded : BuildersBounded config state → BuildersBounded config after := by
    intro bounded gloas builder member
    rw [builders] at member
    rw [epochNat, getCurrentEpoch, slot]
    exact bounded gloas builder member
  exact ⟨slot, fun _ => Nat.le_of_eq (by rw [builders]), bounded,
    fun _ _ _ old found => ⟨old, by rw [builders]; exact found, .refl state old⟩⟩

/-- A builder replaced at an index of the registry.

The new builder must follow the old one, and keep its withdrawable epoch within the delay. -/
theorem putBuilder {gloas : .glamsterdam ≤ fork} {index : Nat}
    {inside : index < (state.builders gloas).data.size} {builder : Builder}
    (follows : BuildersBounded config state →
      BuilderFollows config state (state.builders gloas).data[index] builder)
    (bounded : BuildersBounded config state → builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH →
      builder.withdrawableEpoch.toNat ≤
        epochNat state + config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat) :
    BuildersAdvance config state (state.putBuilder gloas index inside builder) := by
  refine ⟨rfl, fun gloas' => ?_, ?_, ?_⟩
  · obtain rfl : gloas = gloas' := rfl
    change _ ≤ ((state.builders gloas).data.set index builder inside).size
    simp
  · intro all gloas' member' member set'
    obtain rfl : gloas = gloas' := rfl
    change member' ∈ (state.builders gloas).data.set index builder inside at member
    rcases Array.mem_or_eq_of_mem_set member with old | rfl
    · exact all gloas _ old set'
    · exact bounded all set'
  · intro all gloas' position old found
    obtain rfl : gloas = gloas' := rfl
    change ∃ new, ((state.builders gloas).data.set index builder inside)[position]? = some new ∧ _
    by_cases same : index = position
    · subst same
      have : old = (state.builders gloas).data[index] := by
        rw [Array.getElem?_eq_getElem inside] at found
        exact (Option.some.inj found).symm
      subst this
      exact ⟨builder, by simp, follows all⟩
    · refine ⟨old, ?_, .refl state old⟩
      rw [Array.getElem?_set]
      simp only [same, ↓reduceIte]
      exact found

/-- A builder added at the end of the registry, which has not started to exit. -/
theorem pushBuilder {gloas : .glamsterdam ≤ fork} {builder : Builder}
    (far : builder.withdrawableEpoch = FAR_FUTURE_EPOCH) :
    BuildersAdvance config state
      { state with builders := fun _ => ⟨(state.builders gloas).data.push builder⟩ } := by
  refine ⟨rfl, fun gloas' => ?_, ?_, ?_⟩
  · obtain rfl : gloas = gloas' := rfl
    simp
  · intro all gloas' member' member set'
    obtain rfl : gloas = gloas' := rfl
    change member' ∈ (state.builders gloas).data.push builder at member
    simp only [Array.mem_push] at member
    rcases member with old | rfl
    · exact all gloas _ old set'
    · exact absurd far set'
  · intro all gloas' position old found
    obtain rfl : gloas = gloas' := rfl
    have inside : position < (state.builders gloas).data.size := by
      by_contra outside
      rw [Array.getElem?_eq_none (Nat.le_of_not_lt outside)] at found
      cases found
    refine ⟨old, ?_, .refl state old⟩
    change ((state.builders gloas).data.push builder)[position]? = some old
    rw [Array.getElem?_push_lt inside]
    rw [Array.getElem?_eq_getElem inside] at found
    exact found

/-- A fold whose every step advances the registry advances it. -/
theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → BuildersAdvance config s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : BuildersAdvance config state after :=
  foldlM_ok_invariant (BuildersAdvance config state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

theorem setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : BuildersAdvance config state after
    := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact .of_eq rfl

theorem setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : BuildersAdvance config state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact .of_eq rfl

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) :
    BuildersAdvance config state after :=
  have ⟨_, set⟩ := increaseBalance_ok computed
  .setBalance set

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) :
    BuildersAdvance config state after :=
  have ⟨_, set⟩ := decreaseBalance_ok computed
  .setBalance set

end BuildersAdvance

/-! ## Mutators -/

theorem buildersAdvance_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    BuildersAdvance config state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, ⟨_, _⟩, _, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact .of_eq rfl

theorem buildersAdvance_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    BuildersAdvance config state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, ⟨_, _⟩, _, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact .of_eq rfl

theorem buildersAdvance_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    BuildersAdvance config state after := by
  unfold exitQueue at computed
  split at computed
  · exact buildersAdvance_computeExitEpochAndUpdateChurn computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact .refl _

theorem buildersAdvance_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    BuildersAdvance config state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact .refl _
  · exact (buildersAdvance_exitQueue queue).trans (.setValidator set)

theorem buildersAdvance_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    BuildersAdvance config state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  have final : BuildersAdvance config last after := by
    simp only [pure, Except.pure, Except.ok.injEq] at done
    subst done
    split
    · exact .of_eq rfl
    · exact .refl _
  exact (buildersAdvance_initiateValidatorExit exitedOk).trans <|
    ((BuildersAdvance.setValidator markedOk).trans (by exact .of_eq rfl)).trans <|
    (BuildersAdvance.decreaseBalance loweredOk).trans <|
    (BuildersAdvance.increaseBalance raisedOk).trans <|
    (BuildersAdvance.increaseBalance lastOk).trans final

/-! ## The steps of a block -/

theorem buildersAdvance_processBlockHeader {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) :
    BuildersAdvance config state after := by
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq computed
  exact .of_eq rfl

theorem buildersAdvance_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    BuildersAdvance config state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_eq rfl

theorem buildersAdvance_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) :
    BuildersAdvance config state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_eq (by rw [← rest]; rfl)

theorem buildersAdvance_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    BuildersAdvance config state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact buildersAdvance_slashValidator slashed

theorem buildersAdvance_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    BuildersAdvance config step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact buildersAdvance_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem buildersAdvance_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    BuildersAdvance config state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => BuildersAdvance config state step.1)
    (fun _ _ _ before ok => before.trans (buildersAdvance_slashIfSlashable ok))
    (show BuildersAdvance config state (state, false).1 from .refl state) folded

theorem buildersAdvance_processAttestation {attestation : Attestation preset fork}
    {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    BuildersAdvance config state after := by
  unfold processAttestation at computed
  split at computed
  · unfold processAttestationAltair at computed
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, raised, raisedOk, final⟩ := computed
    have last : BuildersAdvance config raised after := by
      split at final
      · rw [recordPaymentWeight_eq final]
        exact .of_eq rfl
      · cases final
        exact .refl _
    have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
        BuildersAdvance config state (setEpochParticipation state current participation) := by
      intro current participation
      unfold setEpochParticipation
      split <;> exact .of_eq rfl
    exact (flagged _ _).trans ((BuildersAdvance.increaseBalance raisedOk).trans last)
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, recorded, _, _, _, _, _, _, rfl⟩ := computed
  have kept := recordPendingAttestation_ok recorded
  split at kept <;>
  · obtain ⟨_, rest⟩ := kept
    exact .of_eq (by rw [← rest]; rfl)

theorem buildersAdvance_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    BuildersAdvance config state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact .of_eq rfl
  · split at computed
    · cases computed
      exact .of_eq rfl
    · cases computed

theorem buildersAdvance_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    BuildersAdvance config state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact buildersAdvance_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · rw [liftAccessor_ok] at computed
    exact .increaseBalance computed

theorem buildersAdvance_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    BuildersAdvance config state after := by
  unfold applyDeposit at computed
  split at computed
  · unfold applyDepositElectra at computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨_, _, computed⟩ := computed
      split at computed
      · simp only [bind_ok_iff, liftAccessor_ok] at computed
        obtain ⟨_, added, pushed⟩ := computed
        obtain ⟨_, rfl⟩ := addPendingDeposit_eq pushed
        exact (buildersAdvance_addValidatorToRegistry added).trans (.of_eq rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_eq rfl
  · exact buildersAdvance_applyPendingDeposit computed

theorem buildersAdvance_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    BuildersAdvance config state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (BuildersAdvance.of_eq (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) rfl).trans
    (buildersAdvance_applyDeposit applied)

theorem buildersAdvance_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    BuildersAdvance config state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact buildersAdvance_initiateValidatorExit exited

/-! ## Requests of the execution layer -/

theorem buildersAdvance_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    BuildersAdvance config state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_eq rfl

theorem buildersAdvance_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    BuildersAdvance config state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (buildersAdvance_computeExitEpochAndUpdateChurn churned).trans (.of_eq rfl)
  · cases computed
    exact .refl _

theorem buildersAdvance_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    BuildersAdvance config state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact buildersAdvance_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact buildersAdvance_requestPartialWithdrawal computed

theorem buildersAdvance_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    BuildersAdvance config state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_eq rfl
  · cases computed
    exact .refl _

theorem buildersAdvance_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    BuildersAdvance config state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  exact (BuildersAdvance.setValidator set).trans
    (buildersAdvance_queueExcessActiveBalance queued)

theorem buildersAdvance_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    BuildersAdvance config state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  exact (buildersAdvance_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (BuildersAdvance.setValidator set).trans (.of_eq rfl)

theorem buildersAdvance_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    BuildersAdvance config state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact buildersAdvance_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact buildersAdvance_queueConsolidation computed

theorem buildersAdvance_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    BuildersAdvance config state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_processDepositRequest ok)
      depositsOk).trans <|
    (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    BuildersAdvance.foldlM
      (fun _ _ _ ok => buildersAdvance_processConsolidationRequest ok) consolidationsOk

/-! ## Withdrawals -/

/-- A builder read from the registry is the one at its index. -/
theorem getElem_of_getBuilder {gloas : .glamsterdam ≤ fork} {index : BuilderIndex}
    {builder : Builder} (found : getBuilder state gloas index = .ok builder)
    (inside : index.toNat < (state.builders gloas).data.size) :
    (state.builders gloas).data[index.toNat] = builder := by
  unfold getBuilder at found
  rw [Array.getElem?_eq_getElem inside] at found
  exact Except.ok.inj found

theorem buildersAdvance_applyWithdrawal {withdrawal : Withdrawal}
    (computed : applyWithdrawal state withdrawal = .ok after) :
    BuildersAdvance config state after := by
  unfold applyWithdrawal at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨builder, found, set⟩ := computed
    obtain ⟨inside, rfl⟩ := setBuilder_ok set
    have same := getElem_of_getBuilder found inside
    -- Only the balance of the builder changes.
    refine .putBuilder (fun _ => ?_)
      (fun all set' => all _ builder (same ▸ Array.getElem_mem inside) set')
    rw [same]
    exact ⟨(BuilderFollows.refl state builder).1, .inl ⟨rfl, rfl, rfl, rfl⟩⟩
  · exact .decreaseBalance computed

theorem buildersAdvance_applyExpectedWithdrawals {capella : .shapella ≤ fork}
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    BuildersAdvance config state after := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, finished, sweptOk, last⟩ := computed
  have one : BuildersAdvance config state applied := by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_applyWithdrawal ok)
      appliedOk
  have two : BuildersAdvance config applied indexed := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      exact .of_eq rfl
    · cases indexedOk
      exact .refl _
  have queued : ∀ kept : BeaconState preset fork,
      BuildersAdvance config kept (if gloas : .glamsterdam ≤ fork then
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals kept gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_eq rfl
    · exact .refl _
  have partials : ∀ kept : BeaconState preset fork,
      BuildersAdvance config kept (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals kept electra expected.processedPartialWithdrawalsCount
      else kept) := by
    intro kept
    split
    · exact .of_eq rfl
    · exact .refl _
  have swept : ∀ kept : BeaconState preset fork,
      (if gloas : .glamsterdam ≤ fork then
        updateNextWithdrawalBuilderIndex kept gloas expected.processedBuildersSweepCount
      else pure kept) = .ok finished → BuildersAdvance config kept finished := by
    intro kept ok
    split at ok
    · unfold updateNextWithdrawalBuilderIndex at ok
      dsimp only at ok
      split at ok
      · cases ok
        exact .of_eq rfl
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at ok
        obtain ⟨_, _, rfl⟩ := ok
        exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  have lastKept : BuildersAdvance config finished after := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · cases last
      exact .of_eq rfl
  exact one.trans <| two.trans <| (queued _).trans <| (partials _).trans <|
    (swept _ sweptOk).trans lastKept

theorem buildersAdvance_processWithdrawals {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) :
    BuildersAdvance config state after := by
  unfold processWithdrawals at computed
  split at computed
  · split at computed
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨_, _, applied⟩ := computed
      exact buildersAdvance_applyExpectedWithdrawals applied
    · cases computed
      exact .refl _
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact buildersAdvance_applyExpectedWithdrawals applied

theorem buildersAdvance_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    BuildersAdvance config state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact .setValidator set

/-! ## The parent payload and the execution part of a block -/

theorem buildersAdvance_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    BuildersAdvance config state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_eq rfl

/-! ## The requests of builders -/

/-- A builder that starts to exit may withdraw the delay after the current epoch.

That is no earlier than it could withdraw before. -/
theorem buildersAdvance_initiateBuilderExit {gloas : .glamsterdam ≤ fork} {index : BuilderIndex}
    (computed : initiateBuilderExit config state gloas index = .ok after) :
    BuildersAdvance config state after := by
  simp only [initiateBuilderExit, bind_ok_iff, liftArith, mapError_ok_iff, addChecked_ok_iff]
    at computed
  obtain ⟨builder, found, withdrawableEpoch, ⟨_, sum⟩, set⟩ := computed
  obtain ⟨inside, rfl⟩ := setBuilder_ok set
  have same := getElem_of_getBuilder found inside
  refine .putBuilder (fun all => ?_) (fun _ _ => ?_)
  · rw [same]
    refine ⟨.inr ?_, .inl ⟨rfl, rfl, rfl, rfl⟩⟩
    have bounded := all gloas builder (same ▸ Array.getElem_mem inside)
    simp only [withdrawFloor, epochNat] at bounded ⊢
    split
    · omega
    · have := bounded ‹_›
      omega
  · simp only [epochNat]
    omega

/-- The current epoch is below the far future epoch when an epoch has two slots or more. -/
theorem getCurrentEpoch_lt_far (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    (state : BeaconState preset fork) : (getCurrentEpoch state).toNat < FAR_FUTURE_EPOCH.toNat := by
  have far : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  have small := UInt64.toNat_lt state.slot
  have half : state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ state.slot.toNat / 2 :=
    Nat.div_le_div_left slots (by decide)
  unfold getCurrentEpoch computeEpochAtSlot
  rw [UInt64.toNat_div]
  omega

/-- A new builder joins the registry at the first reusable index, or at its end.

A reusable builder is withdrawable, so the new one deposits no earlier than it could withdraw. -/
theorem buildersAdvance_addBuilderToRegistry (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {gloas : .glamsterdam ≤ fork} {pubkey : BLSPubkey} {version : UInt8}
    {executionAddress : ExecutionAddress} {amount : Gwei} :
    BuildersAdvance config state
      (addBuilderToRegistry state gloas pubkey version executionAddress amount state.slot) := by
  simp only [addBuilderToRegistry]
  split
  · rename_i inside
    have reusable := isReusableBuilder_of_getIndexForNewBuilder_lt inside
    simp only [isReusableBuilder, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at reusable
    have small := getCurrentEpoch_lt_far slots state
    refine .putBuilder (fun _ => ⟨.inl rfl, .inr ?_⟩) (fun _ far => absurd rfl far)
    have le := UInt64.le_iff_toNat_le.mp reusable.1
    simp only [withdrawFloor]
    split
    · rename_i far
      rw [far] at le
      omega
    · exact le
  · exact .pushBuilder rfl

/-- A builder deposit adds to a builder, registers a new one, or changes nothing.

A deposit can reach a builder that has exited with nothing left.

It then moves the withdrawal of that builder to the delay after the current epoch.

That is no earlier than before. -/
theorem buildersAdvance_processBuilderDepositRequest (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {gloas : .glamsterdam ≤ fork} {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    BuildersAdvance config state after := by
  unfold processBuilderDepositRequest at computed
  split at computed
  · cases computed
    exact .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨valid, _, computed⟩ := computed
    split at computed
    · cases computed
      exact buildersAdvance_addBuilderToRegistry slots
    · cases computed
      exact .refl _
  · rename_i index _
    -- The builder keeps its withdrawable epoch, or gets the delay after the current epoch.
    have finish : ∀ (withdrawableEpoch balance : UInt64),
        (withdrawableEpoch = ((state.builders gloas).data[index]).withdrawableEpoch ∨
          withdrawableEpoch.toNat =
            epochNat state + config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat) →
        BuildersAdvance config state (state.putBuilder gloas index index.isLt
          { (state.builders gloas).data[index] with withdrawableEpoch, balance }) := by
      intro withdrawableEpoch balance epochCases
      refine .putBuilder (fun all => ⟨?_, .inl ⟨rfl, rfl, rfl, rfl⟩⟩) (fun all set => ?_)
      · have bounded := all gloas _ (Array.getElem_mem index.isLt)
        dsimp only
        rcases epochCases with same | sum
        · exact same ▸ (BuilderFollows.refl state _).1
        · right
          simp only [withdrawFloor] at bounded ⊢
          split
          · omega
          · have := bounded ‹_›
            omega
      · have bounded := all gloas _ (Array.getElem_mem index.isLt)
        dsimp only at set ⊢
        rcases epochCases with same | sum
        · rw [same] at set ⊢
          exact bounded set
        · omega
    dsimp only at computed
    split at computed
    · obtain ⟨withdrawableEpoch, epochOk, computed⟩ := bind_ok_iff.mp computed
      obtain ⟨balance, _, computed⟩ := bind_ok_iff.mp computed
      cases computed
      simp only [liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff] at epochOk
      exact finish _ _ (.inr epochOk.2)
    · obtain ⟨withdrawableEpoch, epochOk, computed⟩ := bind_ok_iff.mp computed
      obtain ⟨balance, _, computed⟩ := bind_ok_iff.mp computed
      cases computed
      cases epochOk
      exact finish _ _ (.inl rfl)

theorem buildersAdvance_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    BuildersAdvance config state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨_, _, _, _, _, exited⟩
  · exact .refl _
  · exact buildersAdvance_initiateBuilderExit exited

theorem buildersAdvance_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) :
    BuildersAdvance config state after := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    unfold settleBuilderPayment at settled
    split at settled
    · cases settled
      exact .of_eq rfl
    · cases settled
  · simp only at computed
    split at computed <;> cases computed <;> exact .of_eq rfl

theorem buildersAdvance_processParentExecutionPayload (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    BuildersAdvance config state after := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact .refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  unfold applyParentExecutionPayload at applied
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    applied
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, buildersOk, exitsOk⟩ :=
    requestedOk
  exact (buildersAdvance_settleParentPayment settledOk).trans <|
    (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_processDepositRequest ok)
      depositsOk).trans <|
    (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    (BuildersAdvance.foldlM
      (fun _ _ _ ok => buildersAdvance_processConsolidationRequest ok) consolidationsOk).trans <|
    (BuildersAdvance.foldlM
      (fun _ _ _ ok => buildersAdvance_processBuilderDepositRequest slots ok) buildersOk).trans <|
    (BuildersAdvance.foldlM
      (fun _ _ _ ok => buildersAdvance_processBuilderExitRequest ok) exitsOk).trans
      (.of_eq rfl)

theorem buildersAdvance_processExecutionPayloadBid {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    BuildersAdvance config state after := by
  obtain ⟨_, recorded, recordedOk, rfl⟩ := processExecutionPayloadBid_ok computed
  by_cases paid : 0 < signed.message.value
  · obtain ⟨_, _, _, _, rfl⟩ := recordBidPayment_of_pos paid recordedOk
    exact .of_eq rfl
  · simp only [recordBidPayment, paid, ↓reduceIte, pure, Except.pure, Except.ok.injEq]
      at recordedOk
    subst recordedOk
    exact .of_eq rfl

theorem buildersAdvance_processBlockExecution {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    BuildersAdvance config state after := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (buildersAdvance_processWithdrawals withdrawnOk).trans
      (buildersAdvance_processExecutionPayloadBid bid)
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    exact (buildersAdvance_processWithdrawals withdrawnOk).trans
      (buildersAdvance_processExecutionPayload paid)
  · dsimp only at computed
    split at computed
    · exact buildersAdvance_processExecutionPayload computed
    · cases computed
      exact .refl _

/-! ## The sync aggregate -/

theorem buildersAdvance_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    BuildersAdvance config state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine BuildersAdvance.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (BuildersAdvance.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

/-! ## Blocks -/

theorem buildersAdvance_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    BuildersAdvance config state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (BuildersAdvance.foldlM
        (fun _ _ _ ok => buildersAdvance_processProposerSlashing ok) proposersOk).trans <|
      (BuildersAdvance.foldlM
        (fun _ _ _ ok => buildersAdvance_processAttesterSlashing ok) attestersOk).trans <|
      (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_processAttestation ok)
        attestedOk).trans <|
      (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_processVoluntaryExit ok)
        exitsOk).trans <|
      (BuildersAdvance.foldlM
        (fun _ _ _ ok => buildersAdvance_processBlsToExecutionChange ok) changesOk).trans <|
      BuildersAdvance.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  simp only [bind_ok_iff, ensure_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, _, proposersOk, _, attestersOk, _, attestedOk, _, depositedOk, exited,
    exitsOk, changed, changesOk, requestsOk⟩ := computed
  have changes : BuildersAdvance config exited changed := by
    unfold processBlsToExecutionChanges at changesOk
    split at changesOk
    · rw [← Array.foldlM_toList] at changesOk
      exact BuildersAdvance.foldlM
        (fun _ _ _ ok => buildersAdvance_processBlsToExecutionChange ok) changesOk
    · simp only [pure, Except.pure, Except.ok.injEq] at changesOk
      exact changesOk ▸ .refl _
  have requests : BuildersAdvance config changed after := by
    split at requestsOk
    · exact buildersAdvance_processExecutionRequests requestsOk
    · simp only [pure, Except.pure, Except.ok.injEq] at requestsOk
      exact requestsOk ▸ .refl _
  exact (BuildersAdvance.foldlM
      (fun _ _ _ ok => buildersAdvance_processProposerSlashing ok) proposersOk).trans <|
    (BuildersAdvance.foldlM
      (fun _ _ _ ok => buildersAdvance_processAttesterSlashing ok) attestersOk).trans <|
    (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_processAttestation ok)
      attestedOk).trans <|
    (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_processDeposit ok)
      depositedOk).trans <|
    (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_processVoluntaryExit ok)
      exitsOk).trans <|
    changes.trans requests

theorem buildersAdvance_processBlock (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    BuildersAdvance config state after := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, _, operatedOk, synced⟩ := computed
    have paidKept : BuildersAdvance config state paid := by
      split at paidOk
      · exact buildersAdvance_processParentExecutionPayload slots paidOk
      · cases paidOk
        exact .refl _
    have executedKept : BuildersAdvance config headed executed := by
      split at executedOk
      · exact buildersAdvance_processBlockExecution executedOk
      · cases executedOk
        exact .refl _
    have votedKept : BuildersAdvance config revealed voted := by
      split at votedOk
      · exact buildersAdvance_processEth1Data votedOk
      · cases votedOk
        exact .refl _
    exact paidKept.trans <| (buildersAdvance_processBlockHeader headedOk).trans <|
      executedKept.trans <| (buildersAdvance_processRandao revealedOk).trans <|
      votedKept.trans <| (buildersAdvance_processOperations operatedOk).trans
        (buildersAdvance_processSyncAggregate synced)
  simp only [bind_ok_iff] at computed
  obtain ⟨_, headerOk, _, randaoOk, _, eth1Ok, operationsOk⟩ := computed
  exact (buildersAdvance_processBlockHeader headerOk).trans <|
    (buildersAdvance_processRandao randaoOk).trans <|
    (buildersAdvance_processEth1Data eth1Ok).trans
      (buildersAdvance_processOperations operationsOk)

/-! ## The steps of an epoch -/

theorem buildersAdvance_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    BuildersAdvance config state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_eq (by rw [← rest]; rfl)

theorem buildersAdvance_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : BuildersAdvance config state after :=
  BuildersAdvance.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (BuildersAdvance.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem buildersAdvance_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    BuildersAdvance config state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact buildersAdvance_applyAllDeltas applied

theorem buildersAdvance_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    BuildersAdvance config state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, marked, markedOk, computed⟩ := computed
  have set := BuildersAdvance.setValidator (config := config) markedOk
  split at computed
  · exact set.trans (buildersAdvance_initiateValidatorExit (liftAccessor_ok.mp computed))
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

theorem buildersAdvance_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) :
    BuildersAdvance config state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, set⟩ := computed
  exact .setValidator set

theorem buildersAdvance_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    BuildersAdvance config state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine BuildersAdvance.foldlM (fun state _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact .setValidator set
    split at ok
    · exact buildersAdvance_initiateValidatorExit (liftAccessor_ok.mp ok)
    split at ok
    · rw [liftAccessor_ok] at ok
      exact .setValidator ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, updatedOk, activated⟩ := computed
  exact (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_updateRegistryEntry ok)
    updatedOk).trans
    (BuildersAdvance.foldlM (fun _ _ _ ok => buildersAdvance_activateValidator ok)
      activated)

theorem buildersAdvance_processSlashings (computed : processSlashings state = .ok after) :
    BuildersAdvance config state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine BuildersAdvance.foldlM (fun _ _ _ ok => ?_) applied
    simp only [applySlashingPenaltyElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, lowered⟩ := ok
        exact .decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ .refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  · refine BuildersAdvance.foldlM (fun _ _ _ ok => ?_) computed
    simp only [applySlashingPenalty, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff] at ok
      obtain ⟨_, _, ok⟩ := ok
      split at ok
      · simp only [bind_ok_iff, liftAccessor_ok] at ok
        obtain ⟨_, _, _, _, lowered⟩ := ok
        exact .decreaseBalance lowered
      · simp only [pure, Except.pure, Except.ok.injEq] at ok
        exact ok ▸ .refl _
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _

theorem buildersAdvance_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    BuildersAdvance config state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_eq rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem buildersAdvance_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    BuildersAdvance config state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine BuildersAdvance.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, set⟩ := ok
  exact .setValidator set

theorem buildersAdvance_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    BuildersAdvance config state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_eq rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem buildersAdvance_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    BuildersAdvance config state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_eq rfl

/-! ## The steps of an epoch from Altair -/

theorem buildersAdvance_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    BuildersAdvance config state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_eq rfl

theorem buildersAdvance_passPendingDeposits {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      BuildersAdvance config state pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact .refl _
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact (buildersAdvance_applyPendingDeposit credited).trans
        (buildersAdvance_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact buildersAdvance_passPendingDeposits (deposits := rest) ‹_›
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact .refl _
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact (buildersAdvance_applyPendingDeposit credited).trans
      (buildersAdvance_passPendingDeposits (deposits := rest) ‹_›)

theorem buildersAdvance_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    BuildersAdvance config state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (buildersAdvance_passPendingDeposits ‹_›).trans (.of_eq rfl)

theorem buildersAdvance_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      BuildersAdvance config state result.1
  | [], _, _, computed => by
    simp only [passPendingConsolidations, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  | consolidation :: rest, state, result, computed => by
    simp only [passPendingConsolidations, bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨source, _, computed⟩ := computed
    split at computed
    · simp only [bind_ok_iff] at computed
      obtain ⟨⟨passed, read⟩, passedOk, computed⟩ := computed
      cases computed
      exact buildersAdvance_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (BuildersAdvance.decreaseBalance loweredOk).trans <|
      (BuildersAdvance.increaseBalance raisedOk).trans
        (buildersAdvance_passPendingConsolidations (result := (passed, read)) passedOk)

theorem buildersAdvance_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    BuildersAdvance config state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine (buildersAdvance_processPendingDeposits deposited).trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (buildersAdvance_passPendingConsolidations ‹_›).trans (.of_eq rfl)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

/-- The steps that close an epoch from Altair, after the history. -/
private theorem buildersAdvance_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : BuildersAdvance config rooted after := by
  have syncedKept : BuildersAdvance config rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact .of_eq rfl
  have lookedKept : BuildersAdvance config synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedKept : BuildersAdvance config looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedKept.trans (lookedKept.trans windowedKept)

theorem buildersAdvance_processEpochAltair {altair : .altair ≤ fork}
    (computed : processEpochAltair config checks state altair = .ok after) :
    BuildersAdvance config state after := by
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetKept : BuildersAdvance config slashed reset := by
    split at resetOk
    · exact buildersAdvance_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ .refl _
  have paidKept : BuildersAdvance config pending paid := by
    split at paidOk
    · simp only [processBuilderPendingPayments, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at paidOk
      obtain ⟨_, _, rfl⟩ := paidOk
      exact .of_eq rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at paidOk
      exact paidOk ▸ .refl _
  have clearedKept : BuildersAdvance config balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_eq rfl
  have mixedKept : BuildersAdvance config cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_eq rfl
  have head : BuildersAdvance config state mixed :=
    (buildersAdvance_processJustificationAndFinalization justifiedOk).trans <|
    (buildersAdvance_processInactivityUpdates scoredOk).trans <|
    (buildersAdvance_processRewardsAndPenalties rewardedOk).trans <|
    (buildersAdvance_processRegistryUpdates registeredOk).trans <|
    (buildersAdvance_processSlashings slashedOk).trans <|
    resetKept.trans <|
    (buildersAdvance_processPendingBalances pendingOk).trans <|
    paidKept.trans <|
    (buildersAdvance_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans mixedKept
  split at computed <;> simp only [bind_ok_iff] at computed <;>
    obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
  · have rootedKept : BuildersAdvance config mixed rooted := by
      unfold processHistoricalSummariesUpdate at rootedOk
      simp only [bind, Except.bind, pure, Except.pure] at rootedOk
      repeat' (split at rootedOk <;> try cases rootedOk)
      all_goals first
        | exact .refl _
        | exact .of_eq rfl
    exact head.trans <| rootedKept.trans (buildersAdvance_epochEnd syncedOk lookedOk windowed)
  · exact head.trans <| (buildersAdvance_processHistoricalRootsUpdate rootedOk).trans
      (buildersAdvance_epochEnd syncedOk lookedOk windowed)

theorem buildersAdvance_processEpoch
    (computed : processEpoch config checks state = .ok after) :
    BuildersAdvance config state after := by
  unfold processEpoch at computed
  split at computed
  · exact buildersAdvance_processEpochAltair computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, rewarded, rewardedOk, registered, registeredOk, slashed,
    slashedOk, reset, resetOk, balanced, balancedOk, cleared, clearedOk, mixed, mixedOk, rooted,
    rootedOk, rotated⟩ := computed
  have clearedKept : BuildersAdvance config balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_eq rfl
  have mixedKept : BuildersAdvance config cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_eq rfl
  exact (buildersAdvance_processJustificationAndFinalization justifiedOk).trans <|
    (buildersAdvance_processRewardsAndPenalties rewardedOk).trans <|
    (buildersAdvance_processRegistryUpdates registeredOk).trans <|
    (buildersAdvance_processSlashings slashedOk).trans <|
    (buildersAdvance_processEth1DataReset resetOk).trans <|
    (buildersAdvance_processEffectiveBalanceUpdates balancedOk).trans <|
    clearedKept.trans <| mixedKept.trans <|
    (buildersAdvance_processHistoricalRootsUpdate rootedOk).trans
      (buildersAdvance_processParticipationRecordUpdates rotated)

/-- A slot step advances the registry up to its last change, which moves the slot on by one. -/
theorem buildersAdvance_advanceSlot
    (computed : advanceSlot config checks state = .ok after) :
    ∃ middle, BuildersAdvance config state middle ∧ after.builders = middle.builders ∧
      after.slot.toNat = middle.slot.toNat + 1 := by
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  have cachedKept : BuildersAdvance config state cached := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok cachedOk
    exact .of_eq rfl
  have epochedKept : BuildersAdvance config cached epoched := by
    unfold epochIfLast at epochedOk
    split at epochedOk
    · exact buildersAdvance_processEpoch epochedOk
    · simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
      exact epochedOk ▸ .refl _
  have advance := cachedKept.trans epochedKept
  exact ⟨epoched, advance, rfl, by rw [advance.slot]; exact sum⟩

/-! ## Upgrades and chains -/

/-- The registry of a later state, which may be of a later fork.

Once both states have builders, the slot does not move back and the registry does not shrink.

Each builder of the first state is followed, at its index, by a builder of the later state. -/
structure ForkedBuilders (config : Config) (forked after : ForkedBeaconState preset) : Prop where
  fork_le : forked.fork ≤ after.fork
  slot : .glamsterdam ≤ forked.fork → forked.state.slot ≤ after.state.slot
  size : ∀ gloas gloas',
    (forked.state.builders gloas).data.size ≤ (after.state.builders gloas').data.size
  bounded : BuildersBounded config forked.state → BuildersBounded config after.state
  follows : BuildersBounded config forked.state → ∀ gloas gloas' (index : Nat) (old : Builder),
    (forked.state.builders gloas).data[index]? = some old →
      ∃ new, (after.state.builders gloas').data[index]? = some new ∧
        BuilderFollows config forked.state old new

/-- A step within one fork. -/
theorem BuildersAdvance.forked {fork : Base.Fork} {state after : BeaconState preset fork}
    (advance : BuildersAdvance config state after) :
    ForkedBuilders config ⟨fork, state⟩ ⟨fork, after⟩ where
  fork_le := Nat.le_refl _
  slot _ := advance.slot ▸ UInt64.le_refl _
  size gloas _ := advance.size gloas
  bounded := advance.bounded
  follows bounded gloas _ := advance.follows bounded gloas

theorem ForkedBuilders.trans {first second third : ForkedBeaconState preset}
    (one : ForkedBuilders config first second) (two : ForkedBuilders config second third) :
    ForkedBuilders config first third where
  fork_le := Nat.le_trans one.fork_le two.fork_le
  slot gloas := UInt64.le_trans (one.slot gloas) (two.slot (Nat.le_trans gloas one.fork_le))
  size gloas gloas' :=
    Nat.le_trans (one.size gloas (Nat.le_trans gloas one.fork_le))
      (two.size (Nat.le_trans gloas one.fork_le) gloas')
  bounded := two.bounded ∘ one.bounded
  follows bounded gloas gloas' index old found := by
    have middle := Nat.le_trans gloas one.fork_le
    obtain ⟨mid, midFound, oneFollows⟩ := one.follows bounded gloas middle index old found
    obtain ⟨new, newFound, twoFollows⟩ :=
      two.follows (one.bounded bounded) middle gloas' index mid midFound
    exact ⟨new, newFound,
      oneFollows.trans (bounded gloas old (Array.mem_of_getElem? found)) (one.slot gloas)
        twoFollows⟩

/-- The last change of a slot step moves the slot on and keeps the registry. -/
theorem forkedBuilders_of_slot {fork : Base.Fork} {state after : BeaconState preset fork}
    (builders : after.builders = state.builders) (slot : state.slot ≤ after.slot) :
    ForkedBuilders config ⟨fork, state⟩ ⟨fork, after⟩ := by
  have epochs := epochNat_le slot
  refine ⟨Nat.le_refl _, fun _ => slot, fun _ _ => Nat.le_of_eq (by rw [builders]), ?_,
    fun _ _ _ _ old found => ⟨old, by rw [builders]; exact found, .refl state old⟩⟩
  intro bounded gloas builder member set
  rw [builders] at member
  have within : builder.withdrawableEpoch.toNat ≤
      epochNat state + config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat :=
    bounded gloas builder member set
  show builder.withdrawableEpoch.toNat ≤
    epochNat after + config.MIN_BUILDER_WITHDRAWABILITY_DELAY.toNat
  omega

/-- A slot step. -/
theorem forkedBuilders_advanceSlot {fork : Base.Fork} {state after : BeaconState preset fork}
    (computed : advanceSlot config checks state = .ok after) :
    ForkedBuilders config ⟨fork, state⟩ ⟨fork, after⟩ := by
  obtain ⟨middle, advance, builders, slot⟩ := buildersAdvance_advanceSlot computed
  exact advance.forked.trans
    (forkedBuilders_of_slot builders (UInt64.le_iff_toNat_le.mpr (by omega)))

/-- A state before Gloas has no builders, so every claim about its builders holds. -/
theorem buildersBounded_of_before {state : BeaconState preset fork} (early : fork < .glamsterdam) :
    BuildersBounded config state :=
  fun gloas => absurd gloas (Nat.not_le_of_lt early)

/-- No builder of a state has started to exit. -/
def BuildersFresh (state : BeaconState preset fork) : Prop :=
  ∀ (gloas : .glamsterdam ≤ fork), ∀ builder ∈ (state.builders gloas).data,
    builder.withdrawableEpoch = FAR_FUTURE_EPOCH

/-- One pending deposit at the upgrade to Gloas adds to a builder, adds a builder, or neither.

So no builder starts to exit. -/
theorem buildersFresh_onboardDeposit {validatorKeys : List BLSPubkey}
    {step next : BeaconState preset .glamsterdam × Array PendingDeposit} {deposit : PendingDeposit}
    (computed : onboardDeposit config checks validatorKeys step deposit = .ok next)
    (fresh : BuildersFresh step.1) : BuildersFresh next.1 := by
  obtain ⟨state, kept⟩ := step
  have gloas : Fork.glamsterdam ≤ .glamsterdam := by decide
  -- Adding a builder keeps every builder without an exit.
  have added : ∀ (pubkey : BLSPubkey) (version : UInt8) (address : ExecutionAddress)
      (amount : Gwei) (slot : Slot),
      BuildersFresh (addBuilderToRegistry state gloas pubkey version address amount slot) := by
    intro pubkey version address amount slot gloas' builder member
    obtain rfl : gloas = gloas' := rfl
    unfold addBuilderToRegistry at member
    dsimp only at member
    split at member
    · rename_i inside
      change builder ∈ (state.builders gloas).data.set _ _ inside at member
      rcases Array.mem_or_eq_of_mem_set member with old | rfl
      · exact fresh gloas builder old
      · rfl
    · change builder ∈ (state.builders gloas).data.push _ at member
      rcases Array.mem_push.mp member with old | rfl
      · exact fresh gloas builder old
      · rfl
  unfold onboardDeposit at computed
  dsimp only at computed
  split at computed
  · cases computed
    exact fresh
  split at computed
  · rename_i index _
    obtain ⟨balance, _, computed⟩ := bind_ok_iff.mp computed
    cases computed
    intro gloas' builder member
    obtain rfl : gloas = gloas' := rfl
    change builder ∈ (state.builders gloas).data.set _ _ index.isLt at member
    rcases Array.mem_or_eq_of_mem_set member with old | rfl
    · exact fresh gloas builder old
    · exact fresh gloas ((state.builders gloas).data[index]) (Array.getElem_mem index.isLt)
  · split at computed
    · cases computed
      exact fresh
    obtain ⟨_, _, computed⟩ := bind_ok_iff.mp computed
    split at computed
    · cases computed
      exact fresh
    obtain ⟨_, _, computed⟩ := bind_ok_iff.mp computed
    split at computed
    · cases computed
      exact added _ _ _ _ _
    · cases computed
      exact fresh

/-- After the upgrade to Gloas no builder has started to exit.

The registry starts empty, and the onboarding of pending deposits only adds to it. -/
theorem buildersFresh_upgradeToGloas {pre : BeaconState preset .fusaka}
    {post : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok post) :
    BuildersFresh post := by
  unfold upgradeToGloas at computed
  obtain ⟨root, -, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨window, -, onboarded⟩ := bind_ok_iff.mp rest
  unfold onboardBuildersFromPendingDeposits at onboarded
  obtain ⟨⟨folded, kept⟩, foldedOk, rest⟩ := bind_ok_iff.mp onboarded
  cases rest
  rw [← Array.foldlM_toList] at foldedOk
  have start : BuildersFresh
      ({ upgradeFields config pre root with ptcWindow := fun _ => window },
        (#[] : Array PendingDeposit)).1 := by
    intro _ builder member
    simp [upgradeFields] at member
  have done := foldlM_ok_invariant (fun step => BuildersFresh step.1)
    (fun _ _ _ before ok => buildersFresh_onboardDeposit ok before) start foldedOk
  exact done

/-- A registry in which no builder has started to exit is within the delay. -/
theorem BuildersFresh.bounded {state : BeaconState preset fork} (fresh : BuildersFresh state) :
    BuildersBounded config state :=
  fun gloas builder member set => absurd (fresh gloas builder member) set

/-- An upgrade from a fork before Gloas, whose result is within the delay. -/
private theorem forkedBuilders_of_before {fork' : Base.Fork} {state : BeaconState preset fork}
    {post : BeaconState preset fork'} (early : fork < .glamsterdam) (upgrade : fork < fork')
    (bounded : BuildersBounded config post) :
    ForkedBuilders config ⟨fork, state⟩ ⟨fork', post⟩ :=
  ⟨Nat.le_of_lt upgrade, fun gloas => absurd gloas (Nat.not_le_of_lt early),
    fun gloas => absurd gloas (Nat.not_le_of_lt early), fun _ => bounded,
    fun _ gloas => absurd gloas (Nat.not_le_of_lt early)⟩

/-- An upgrade that carries the slot and the registry. -/
private theorem forkedBuilders_of_carried {fork' : Base.Fork} {state : BeaconState preset fork}
    {post : BeaconState preset fork'} (gloas : .glamsterdam ≤ fork) (upgrade : fork ≤ fork')
    (slot : post.slot = state.slot)
    (builders : ∀ gloas gloas', post.builders gloas' = state.builders gloas) :
    ForkedBuilders config ⟨fork, state⟩ ⟨fork', post⟩ where
  fork_le := upgrade
  slot _ := slot ▸ UInt64.le_refl _
  size gloas gloas' := Nat.le_of_eq (by rw [builders gloas gloas'])
  bounded bounded gloas' builder member set := by
    rw [builders gloas gloas'] at member
    have := bounded gloas builder member set
    simp only [epochNat, getCurrentEpoch, slot] at this ⊢
    exact this
  follows _ gloas gloas' _ old found := ⟨old, by rw [builders gloas gloas']; exact found, .refl _ _⟩


/-- An upgrade carries the registry, or starts it at Gloas with no builder that has exited. -/
theorem forkedBuilders_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    ForkedBuilders config pre post.val := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  -- Before Gloas no state has builders.
  · obtain ⟨_, _, rfl⟩ := computed
    exact forkedBuilders_of_before (by decide) (by decide) (buildersBounded_of_before (by decide))
  · subst computed
    exact forkedBuilders_of_before (by decide) (by decide) (buildersBounded_of_before (by decide))
  · subst computed
    exact forkedBuilders_of_before (by decide) (by decide) (buildersBounded_of_before (by decide))
  · subst computed
    exact forkedBuilders_of_before (by decide) (by decide) (buildersBounded_of_before (by decide))
  · obtain ⟨_, _, rfl⟩ := computed
    exact forkedBuilders_of_before (by decide) (by decide) (buildersBounded_of_before (by decide))
  · obtain ⟨_, _, rfl⟩ := computed
    exact forkedBuilders_of_before (by decide) (by decide) (buildersBounded_of_before (by decide))
  -- The upgrade to Gloas starts the registry, with no builder that has exited.
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact forkedBuilders_of_before (by decide) (by decide)
      (buildersFresh_upgradeToGloas upgraded).bounded
  -- The upgrade to Heze carries the registry.
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    exact forkedBuilders_of_carried (by decide) (by decide) rfl fun _ _ => rfl

/-- Every step of a chain carries the registry forward.

An epoch must have two slots or more, so that the current epoch is before the far future. -/
theorem stepRelation_builders (slots : 1 < preset.SLOTS_PER_EPOCH.toNat) :
    StepRelation config checks fun (forked after : ForkedBeaconState preset) =>
      ForkedBuilders config forked after where
  refl forked := (BuildersAdvance.refl forked.state).forked
  trans one two := one.trans two
  advanceSlot computed := forkedBuilders_advanceSlot computed
  upgradeNext _ computed := forkedBuilders_upgradeNext computed
  applySignedBlock computed :=
    (buildersAdvance_processBlock slots (applySignedBlock_ok computed).2.1).forked

/-- Along every chain, the registry of the last state follows that of the first. -/
theorem Reaches.builders (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {start after : ForkedBeaconState preset} (chain : Reaches config checks start after) :
    ForkedBuilders config start after :=
  (stepRelation_builders slots).reaches chain

/-- In every reachable state, each withdrawable epoch that is set is within the delay.

So it is at most the delay after the current epoch.

A genesis state is of Phase 0, which has no builders. -/
theorem Reachable.buildersBounded (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {forked : ForkedBeaconState preset} (reachable : Reachable config checks forked) :
    BuildersBounded config forked.state := by
  obtain ⟨start, ⟨⟨_, _, _, initialized⟩, _⟩, chain⟩ := reachable
  -- Genesis runs only at Phase 0, so the genesis state has no builders.
  have early : start.fork < .altair := by
    unfold initializeBeaconStateFromEth1 at initialized
    split at initialized
    · cases initialized
    · exact Nat.lt_of_not_le ‹_›
  exact (Reaches.builders slots chain).bounded
    (buildersBounded_of_before (Nat.lt_trans early (by decide)))

/-- Along every chain from a reachable state, the registry of builders never shrinks. -/
theorem Reaches.builders_size_le (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {start after : ForkedBeaconState preset} (chain : Reaches config checks start after)
    (gloas : .glamsterdam ≤ start.fork) (gloas' : .glamsterdam ≤ after.fork) :
    (start.state.builders gloas).data.size ≤ (after.state.builders gloas').data.size :=
  (Reaches.builders slots chain).size gloas gloas'

/-- Along every chain from a reachable state, a withdrawable epoch that is set never moves back.

The builder at the same index later has a withdrawable epoch at least as late.

It may be a new builder at that index, which has not started to exit. -/
theorem Reaches.withdrawableEpoch_le (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {start after : ForkedBeaconState preset} (reachable : Reachable config checks start)
    (chain : Reaches config checks start after) (gloas : .glamsterdam ≤ start.fork)
    (gloas' : .glamsterdam ≤ after.fork) {index : Nat} {old : Builder}
    (found : (start.state.builders gloas).data[index]? = some old)
    (set : old.withdrawableEpoch ≠ FAR_FUTURE_EPOCH) :
    ∃ new, (after.state.builders gloas').data[index]? = some new ∧
      old.withdrawableEpoch ≤ new.withdrawableEpoch := by
  obtain ⟨new, newFound, later, _⟩ := (Reaches.builders slots chain).follows
    (Reachable.buildersBounded slots reachable) gloas gloas' index old found
  refine ⟨new, newFound, ?_⟩
  rcases later with far | le
  · -- The far future epoch is the largest epoch.
    have small := UInt64.toNat_lt old.withdrawableEpoch
    have farNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
    rw [far, UInt64.le_iff_toNat_le, farNat]
    omega
  · simp only [withdrawFloor, set, ↓reduceIte] at le
    exact UInt64.le_iff_toNat_le.mpr le

/-- Along every chain from a reachable state, a builder keeps who it is, or loses its index.

It keeps its key, version, address and deposit epoch.

Otherwise its index has gone to a new builder.

A new builder at the index deposited no earlier than the old one could withdraw.

That is its withdrawable epoch if it had started to exit at the start.

Otherwise it is the delay after the current epoch at the start. -/
theorem Reaches.builder_follows (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {start after : ForkedBeaconState preset} (reachable : Reachable config checks start)
    (chain : Reaches config checks start after) (gloas : .glamsterdam ≤ start.fork)
    (gloas' : .glamsterdam ≤ after.fork) {index : Nat} {old : Builder}
    (found : (start.state.builders gloas).data[index]? = some old) :
    ∃ new, (after.state.builders gloas').data[index]? = some new ∧
      (SameBuilder old new ∨ withdrawFloor config start.state old ≤ new.depositEpoch.toNat) := by
  obtain ⟨new, newFound, _, identity⟩ := (Reaches.builders slots chain).follows
    (Reachable.buildersBounded slots reachable) gloas gloas' index old found
  exact ⟨new, newFound, identity⟩

end EthLib.Consensus
