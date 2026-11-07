module

public import EthLib.Consensus.Proofs.LightClient.Authenticate
public import EthLib.Consensus.Proofs.LightClient.Upgrade

/-!
# Proofs: the invariant of a light client store

A sync committee signs the headers of one period, a fixed number of epochs.

A light client keeps the committee of the period of its finalized header.

Once it learns the committee of the next period, it keeps that one too.

In its introduction, the [Altair design][altair] reads the next committee from the state at a slot.

That committee signs the headers of the period after the period of the slot.

The theorems take a relation `serves`, which says which committee serves each period.

It describes the chain that the client follows, and the theorems need no other fact about it.

They assume that each update with a committee branch proves a committee that serves the next period.

`Authenticate.lean` justifies that assumption without hash injectivity.

The committee root that a branch proves is the root in the attested state, or SHA-256 collides.

`LightClientStore.Invariant` collects four facts:

- the finalized slot is at or below the optimistic slot;
- the current committee serves the period of the finalized header;
- a next committee that the store knows serves the period after it;
- the best valid update fits the store, so a forced update can apply it.

A new store meets the invariant when the committee of its bootstrap serves its period.

Each handler keeps it: an update, a finality update, an optimistic update and a forced update.

So does the upgrade of a store to a later fork.

The fork is a parameter of the store, so each theorem holds at every fork.

The finalized header never skips a period.

It moves to the next period only when the store knows the committee of that period.

Once the store knows its next committee, both committees stay until that move.

An optimistic update changes neither the finalized header nor the committees.

Periods are 64-bit numbers, as in the store.

An update that fits has a signature slot after its attested slot.

So the period of the store is below `2 ^ 64 - 1`, and its successor does not wrap.

[altair]: https://github.com/ethereum/annotated-spec/blob/master/altair/sync-protocol.md
-/

@[expose] public section

namespace EthLib.Consensus

open Base

section Periods

variable {preset : Preset}

/-- The period of a slot is the slot divided by the length of an epoch, then of a period. -/
theorem computeSyncCommitteePeriodAtSlot_toNat (slot : Slot) :
    (computeSyncCommitteePeriodAtSlot preset slot).toNat =
      slot.toNat / preset.SLOTS_PER_EPOCH.toNat /
        preset.EPOCHS_PER_SYNC_COMMITTEE_PERIOD.toNat := by
  simp [computeSyncCommitteePeriodAtSlot, computeSyncCommitteePeriod, computeEpochAtSlot,
    UInt64.toNat_div]

/-- A later slot is in the same period or a later one. -/
theorem computeSyncCommitteePeriodAtSlot_mono {a b : Slot} (le : a ≤ b) :
    computeSyncCommitteePeriodAtSlot preset a ≤ computeSyncCommitteePeriodAtSlot preset b := by
  rw [UInt64.le_iff_toNat_le, computeSyncCommitteePeriodAtSlot_toNat,
    computeSyncCommitteePeriodAtSlot_toNat]
  exact Nat.div_le_div_right (Nat.div_le_div_right (UInt64.le_iff_toNat_le.mp le))

/-- The period of a slot is at most the slot. -/
theorem computeSyncCommitteePeriodAtSlot_le (slot : Slot) :
    computeSyncCommitteePeriodAtSlot preset slot ≤ slot := by
  rw [UInt64.le_iff_toNat_le, computeSyncCommitteePeriodAtSlot_toNat]
  exact Nat.le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _)

end Periods

variable {preset : Preset} {fork : Fork}

/-- The facts about an update that a store needs to apply it, read from the checks of the update.

The slots of the update are ordered: finalized, attested, signature.

The update is signed in the period of the store, or the next one if the store knows that committee.

Its attested header is newer than the finalized header of the store, or in the same period.

An update without a committee branch carries the zero committee. -/
structure LightClientStore.FitsUpdate (store : LightClientStore preset fork)
    (update : LightClientUpdate preset fork) : Prop where
  /-- The finalized header is at or before the attested header. -/
  finalized_le_attested :
    update.finalizedHeader.beacon.slot ≤ update.attestedHeader.beacon.slot
  /-- The attested header comes before the signature slot. -/
  attested_lt_signature : update.attestedHeader.beacon.slot < update.signatureSlot
  /-- The signature is in the period of the store, or the next one if the store knows it. -/
  signature_period :
    computeSyncCommitteePeriodAtSlot preset update.signatureSlot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot ∨
      store.isNextSyncCommitteeKnown = true ∧
        computeSyncCommitteePeriodAtSlot preset update.signatureSlot =
          computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1
  /-- The attested header is newer than the finalized header, or in the same period. -/
  relevant :
    store.finalizedHeader.beacon.slot < update.attestedHeader.beacon.slot ∨
      computeSyncCommitteePeriodAtSlot preset update.attestedHeader.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot
  /-- Without a committee branch, the next committee is zero. -/
  empty_of_not_syncCommitteeUpdate :
    update.isSyncCommitteeUpdate = false → update.nextSyncCommittee = SyncCommittee.empty preset

/-- Whether the next committee that an update proves serves the period after its attested header.

The relation `serves` says which committee serves each period on the chain that the client follows.

An update without a committee branch proves no committee, so it meets this at once. -/
def LightClientUpdate.NextSyncCommitteeServes (serves : UInt64 → SyncCommittee preset → Prop)
    (update : LightClientUpdate preset fork) : Prop :=
  update.isSyncCommitteeUpdate = true →
    serves (computeSyncCommitteePeriodAtSlot preset update.attestedHeader.beacon.slot + 1)
      update.nextSyncCommittee

/-- The invariant of a light client store, for a relation that says which committee serves a period.

The finalized slot is at or below the optimistic slot.

The current committee serves the period of the finalized header.

A next committee that the store knows serves the period after it.

The best valid update fits the store, and its next committee serves the period after its own. -/
structure LightClientStore.Invariant (serves : UInt64 → SyncCommittee preset → Prop)
    (store : LightClientStore preset fork) : Prop where
  /-- The finalized slot is at or below the optimistic slot. -/
  finalized_le_optimistic :
    store.finalizedHeader.beacon.slot ≤ store.optimisticHeader.beacon.slot
  /-- The current committee serves the period of the finalized header. -/
  current :
    serves (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot)
      store.currentSyncCommittee
  /-- A next committee that the store knows serves the period after it. -/
  next : store.isNextSyncCommitteeKnown = true →
    serves (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1)
      store.nextSyncCommittee
  /-- The best valid update fits the store, and proves a committee that serves. -/
  best : ∀ best, store.bestValidUpdate = some best →
    store.FitsUpdate best ∧ best.NextSyncCommitteeServes serves

/-- An update that a store accepts fits the store. -/
theorem validateLightClientUpdate_fitsUpdate {config : Config} {checks : SignatureChecks}
    {store : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (accepted : validateLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok ()) :
    store.FitsUpdate update := by
  have empty := (validateLightClientUpdate_proves accepted).2.2.2.1
  unfold validateLightClientUpdate at accepted
  simp only [Base.bind_ok_iff, LightClientError.require_ok] at accepted
  obtain ⟨_, -, _, -, _, -, _, -, _, ⟨-, signed, finalized⟩, rest⟩ := accepted
  -- The checks of the periods depend on whether the store knows the next committee.
  cases known : store.isNextSyncCommitteeKnown <;>
    simp only [known, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true,
      Bool.false_and, Bool.true_and, Bool.and_eq_true, beq_iff_eq, Base.bind_ok_iff,
      LightClientError.require_ok] at rest
  · obtain ⟨_, period, _, relevant, -⟩ := rest
    refine ⟨finalized, signed, Or.inl period, ?_, empty⟩
    rcases relevant with newer | ⟨-, same⟩
    · exact Or.inl newer
    · exact Or.inr same
  · obtain ⟨_, period, _, relevant, -⟩ := rest
    refine ⟨finalized, signed, period.imp_right fun next => ⟨known, next⟩, ?_, empty⟩
    exact Or.inl (by simpa using relevant)

section Apply

variable {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}

/-- The periods of an update that fits a store, as natural numbers.

The period of the store has a successor below `2 ^ 64`, so the 64-bit successor does not wrap. -/
theorem LightClientStore.FitsUpdate.periods (fits : store.FitsUpdate update) :
    (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot).toNat + 1 <
        2 ^ 64 ∧
      (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot).toNat ≤
        (computeSyncCommitteePeriodAtSlot preset update.attestedHeader.beacon.slot).toNat ∧
      (computeSyncCommitteePeriodAtSlot preset update.finalizedHeader.beacon.slot).toNat ≤
        (computeSyncCommitteePeriodAtSlot preset update.attestedHeader.beacon.slot).toNat ∧
      (computeSyncCommitteePeriodAtSlot preset update.attestedHeader.beacon.slot).toNat ≤
        (computeSyncCommitteePeriodAtSlot preset update.signatureSlot).toNat ∧
      ((computeSyncCommitteePeriodAtSlot preset update.signatureSlot).toNat =
          (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot).toNat ∨
        store.isNextSyncCommitteeKnown = true ∧
          (computeSyncCommitteePeriodAtSlot preset update.signatureSlot).toNat =
            (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot).toNat +
              1) := by
  have storeAttested : computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot ≤
      computeSyncCommitteePeriodAtSlot preset update.attestedHeader.beacon.slot := by
    rcases fits.relevant with newer | same
    · exact computeSyncCommitteePeriodAtSlot_mono (UInt64.le_of_lt newer)
    · exact UInt64.le_of_eq same.symm
  have finalizedAttested := computeSyncCommitteePeriodAtSlot_mono (preset := preset)
    fits.finalized_le_attested
  have attestedSignature := computeSyncCommitteePeriodAtSlot_mono (preset := preset)
    (UInt64.le_of_lt fits.attested_lt_signature)
  -- The attested period is at most the attested slot, which is below the signature slot.
  have attestedBound := computeSyncCommitteePeriodAtSlot_le (preset := preset)
    update.attestedHeader.beacon.slot
  have signatureBound := update.signatureSlot.toNat_lt
  have lt := fits.attested_lt_signature
  have signature := fits.signature_period
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj,
    UInt64.toNat_add, UInt64.toNat_one] at *
  have storeBound : (computeSyncCommitteePeriodAtSlot preset
      store.finalizedHeader.beacon.slot).toNat + 1 < 2 ^ 64 := by omega
  refine ⟨storeBound, storeAttested, finalizedAttested, attestedSignature, ?_⟩
  rcases signature with same | ⟨known, next⟩
  · exact Or.inl same
  · exact Or.inr ⟨known, by omega⟩

/-- An update that fits a store fits any store with the same finalized slot and knowledge. -/
theorem LightClientStore.FitsUpdate.congr {other : LightClientStore preset fork}
    (fits : store.FitsUpdate update)
    (finalized : other.finalizedHeader.beacon.slot = store.finalizedHeader.beacon.slot)
    (known : other.isNextSyncCommitteeKnown = store.isNextSyncCommitteeKnown) :
    other.FitsUpdate update := by
  obtain ⟨ordered, signed, signature, relevant, empty⟩ := fits
  rw [← finalized, ← known] at *
  exact ⟨ordered, signed, signature, relevant, empty⟩

/-- An update that fits a store still fits with its attested header as its finalized header. -/
theorem LightClientStore.FitsUpdate.attestedFinalized (fits : store.FitsUpdate update) :
    store.FitsUpdate { update with finalizedHeader := update.attestedHeader } :=
  ⟨UInt64.le_refl _, fits.attested_lt_signature, fits.signature_period, fits.relevant,
    fits.empty_of_not_syncCommitteeUpdate⟩

/-- A committee that serves one period serves any equal period. -/
private theorem serves_of_eq {serves : UInt64 → SyncCommittee preset → Prop} {p q : UInt64}
    {committee : SyncCommittee preset} (holds : serves p committee) (same : p = q) :
    serves q committee :=
  same ▸ holds

/-- An update that fits a store and carries a committee that is not zero has a committee branch. -/
theorem LightClientStore.FitsUpdate.isSyncCommitteeUpdate (fits : store.FitsUpdate update)
    (known : (update.nextSyncCommittee != SyncCommittee.empty preset) = true) :
    update.isSyncCommitteeUpdate = true := by
  cases committee : update.isSyncCommitteeUpdate
  · simp [fits.empty_of_not_syncCommitteeUpdate committee] at known
  · rfl

/-- Applying an update that fits keeps the committees in their periods.

The current committee serves the period of the finalized header, before and after.

A next committee that the store knows serves the period after it, before and after. -/
theorem applyLightClientUpdate_syncCommittees {serves : UInt64 → SyncCommittee preset → Prop}
    (current : serves (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot)
      store.currentSyncCommittee)
    (next : store.isNextSyncCommitteeKnown = true →
      serves (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1)
        store.nextSyncCommittee)
    (fits : store.FitsUpdate update) (proves : update.NextSyncCommitteeServes serves)
    (computed : applyLightClientUpdate store update = .ok after) :
    serves (computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot)
        after.currentSyncCommittee ∧
      (after.isNextSyncCommitteeKnown = true →
        serves (computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot + 1)
          after.nextSyncCommittee) := by
  obtain ⟨storeBound, storeAttested, finalizedAttested, attestedSignature, signature⟩ :=
    fits.periods
  -- The signature period is at most one past the period of the store.
  have signatureLe : (computeSyncCommitteePeriodAtSlot preset update.signatureSlot).toNat ≤
      (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot).toNat + 1 := by
    rcases signature with same | ⟨-, next⟩ <;> omega
  -- A finalized header at or before the store's is in the store's period or an earlier one.
  have notNewer := fun older => UInt64.le_iff_toNat_le.mp
    (computeSyncCommitteePeriodAtSlot_mono (preset := preset)
      (a := update.finalizedHeader.beacon.slot) (b := store.finalizedHeader.beacon.slot) older)
  have newer := fun later => UInt64.le_iff_toNat_le.mp
    (computeSyncCommitteePeriodAtSlot_mono (preset := preset)
      (a := store.finalizedHeader.beacon.slot) (b := update.finalizedHeader.beacon.slot) later)
  unfold applyLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.requireFork] at computed
  split at computed
  · cases computed
  have knownOf (shape : after.nextSyncCommittee = update.nextSyncCommittee)
      (learned : after.isNextSyncCommitteeKnown = true) : update.isSyncCommitteeUpdate = true :=
    fits.isSyncCommitteeUpdate (by simpa [LightClientStore.isNextSyncCommitteeKnown, shape]
      using learned)
  split at computed
  · -- The store learns its first next committee, in the period of its finalized header.
    rename_i unknown
    split at computed
    · cases computed
    rename_i sameOk
    have same := congrArg UInt64.toNat (LightClientError.require_ok.mp sameOk)
    have signatureSame := signature.resolve_right (by simp_all)
    have attestedSame : computeSyncCommitteePeriodAtSlot preset update.attestedHeader.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot :=
      UInt64.toNat_inj.mp (by omega)
    have shape : (after.finalizedHeader = update.finalizedHeader ∨
          after.finalizedHeader = store.finalizedHeader) ∧
        after.currentSyncCommittee = store.currentSyncCommittee ∧
        after.nextSyncCommittee = update.nextSyncCommittee := by
      repeat' split at computed
      all_goals
        cases computed
        simp
    obtain ⟨finalized, keptCurrent, learnedNext⟩ := shape
    have finalizedSame : computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot := by
      rcases finalized with taken | kept
      · rw [taken]
        exact UInt64.toNat_inj.mp same
      · rw [kept]
    rw [keptCurrent, finalizedSame]
    refine ⟨current, fun learned => ?_⟩
    rw [learnedNext, ← attestedSame]
    exact proves (knownOf learnedNext learned)
  rename_i known
  have known : store.isNextSyncCommitteeKnown = true := by simpa using known
  split at computed
  · -- The store moves to the next period, whose committee it knows.
    rename_i moved
    have moved := congrArg UInt64.toNat moved
    simp only [UInt64.toNat_add, UInt64.toNat_one] at moved
    split at computed
    rotate_left
    · -- An update of a later period finalizes a later slot.
      rename_i older
      have := notNewer (UInt64.le_iff_toNat_le.mpr (Nat.le_of_not_lt (by
        simpa [UInt64.lt_iff_toNat_lt] using older)))
      omega
    have shape : after.finalizedHeader = update.finalizedHeader ∧
        after.currentSyncCommittee = store.nextSyncCommittee ∧
        after.nextSyncCommittee = update.nextSyncCommittee := by
      split at computed <;> cases computed <;> exact ⟨rfl, rfl, rfl⟩
    obtain ⟨taken, movedCurrent, learnedNext⟩ := shape
    rw [taken, movedCurrent]
    refine ⟨serves_of_eq (next known) (UInt64.toNat_inj.mp ?_), fun learned => ?_⟩
    · simp only [UInt64.toNat_add, UInt64.toNat_one]
      omega
    have attestedSame : computeSyncCommitteePeriodAtSlot preset update.attestedHeader.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset update.finalizedHeader.beacon.slot :=
      UInt64.toNat_inj.mp (by omega)
    rw [learnedNext, ← attestedSame]
    exact proves (knownOf learnedNext learned)
  · -- The store stays in its period.
    rename_i stays
    split at computed
    rotate_left
    · cases computed
      exact ⟨current, next⟩
    rename_i later
    have shape : after.finalizedHeader = update.finalizedHeader ∧
        after.currentSyncCommittee = store.currentSyncCommittee ∧
        after.nextSyncCommittee = store.nextSyncCommittee := by
      split at computed <;> cases computed <;> exact ⟨rfl, rfl, rfl⟩
    obtain ⟨taken, keptCurrent, keptNext⟩ := shape
    have stays :
        (computeSyncCommitteePeriodAtSlot preset update.finalizedHeader.beacon.slot).toNat ≠
        (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot).toNat + 1 := by
      intro moved
      apply stays
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_add, UInt64.toNat_one]
      omega
    have := newer (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp later)))
    have finalizedSame : computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot := by
      rw [taken]
      exact UInt64.toNat_inj.mp (by omega)
    have knownAfter : after.isNextSyncCommitteeKnown = store.isNextSyncCommitteeKnown := by
      simp only [LightClientStore.isNextSyncCommitteeKnown, keptNext]
    rw [finalizedSame, keptCurrent, keptNext, knownAfter]
    exact ⟨current, next⟩

/-- Applying an update that fits moves the finalized header by at most one period.

It moves to the next period only when the store knows the committee of that period. -/
theorem applyLightClientUpdate_period (fits : store.FitsUpdate update)
    (computed : applyLightClientUpdate store update = .ok after) :
    computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot ∨
      store.isNextSyncCommitteeKnown = true ∧
        computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
          computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1 := by
  obtain ⟨storeBound, -, finalizedAttested, attestedSignature, signature⟩ := fits.periods
  have signatureLe : (computeSyncCommitteePeriodAtSlot preset update.signatureSlot).toNat ≤
      (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot).toNat + 1 := by
    rcases signature with same | ⟨-, next⟩ <;> omega
  have newer := fun later => UInt64.le_iff_toNat_le.mp
    (computeSyncCommitteePeriodAtSlot_mono (preset := preset)
      (a := store.finalizedHeader.beacon.slot) (b := update.finalizedHeader.beacon.slot) later)
  unfold applyLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.requireFork] at computed
  split at computed
  · cases computed
  split at computed
  · -- Without the next committee, the finalized header must stay in the period of the store.
    split at computed
    · cases computed
    have same := LightClientError.require_ok.mp ‹LightClientError.require _ _ = .ok _›
    left
    repeat' split at computed
    all_goals
      cases computed
      first
        | rfl
        | exact same
  rename_i known
  have known : store.isNextSyncCommitteeKnown = true := by simpa using known
  split at computed
  · -- The store moves to the next period.
    rename_i moved
    right
    refine ⟨known, ?_⟩
    repeat' split at computed
    all_goals
      cases computed
      try exact moved
    -- A finalized header of the next period is newer than the store's.
    rename_i older
    have := UInt64.le_iff_toNat_le.mp (computeSyncCommitteePeriodAtSlot_mono (preset := preset)
      (a := update.finalizedHeader.beacon.slot) (b := store.finalizedHeader.beacon.slot)
      (UInt64.le_iff_toNat_le.mpr (Nat.le_of_not_lt (by
        simpa [UInt64.lt_iff_toNat_lt] using older))))
    have moved := congrArg UInt64.toNat moved
    simp only [UInt64.toNat_add, UInt64.toNat_one] at moved
    omega
  · -- Otherwise a newer finalized header stays in the period of the store.
    rename_i stays
    left
    repeat' split at computed
    all_goals
      cases computed
      try rfl
    all_goals
      rename_i later _
      have := newer (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp later)))
      apply UInt64.toNat_inj.mp
      have stays : (computeSyncCommitteePeriodAtSlot preset
          update.finalizedHeader.beacon.slot).toNat ≠
          (computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot).toNat +
            1 := by
        intro moved
        apply stays
        apply UInt64.toNat_inj.mp
        simp only [UInt64.toNat_add, UInt64.toNat_one]
        omega
      dsimp only
      omega

/-- Applying an update that fits keeps both committees while the finalized period stays.

This holds once the store knows its next committee. -/
theorem applyLightClientUpdate_syncCommittees_of_period_eq
    (computed : applyLightClientUpdate store update = .ok after) (fits : store.FitsUpdate update)
    (known : store.isNextSyncCommitteeKnown = true)
    (stays : computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
      computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot) :
    after.currentSyncCommittee = store.currentSyncCommittee ∧
      after.nextSyncCommittee = store.nextSyncCommittee := by
  have bound := fits.periods.1
  unfold applyLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.requireFork] at computed
  split at computed
  · cases computed
  split at computed
  · rename_i unknown
    simp [known] at unknown
  split at computed
  · -- The store would move to the next period, so its finalized period would change.
    rename_i moved
    have moved := congrArg UInt64.toNat moved
    simp only [UInt64.toNat_add, UInt64.toNat_one] at moved
    exfalso
    repeat' split at computed
    all_goals cases computed
    all_goals
      dsimp only at stays
      first
        | have stays := congrArg UInt64.toNat stays
          omega
        | rename_i older
          have := UInt64.le_iff_toNat_le.mp (computeSyncCommitteePeriodAtSlot_mono
            (preset := preset) (a := update.finalizedHeader.beacon.slot)
            (b := store.finalizedHeader.beacon.slot)
            (UInt64.le_iff_toNat_le.mpr (Nat.le_of_not_lt (by
              simpa [UInt64.lt_iff_toNat_lt] using older))))
          omega
  · repeat' split at computed
    all_goals
      cases computed
      exact ⟨rfl, rfl⟩

end Apply

section Handlers

variable {serves : UInt64 → SyncCommittee preset → Prop}

/-- A new store meets the invariant when the committee of its bootstrap serves its period.

The store knows no next committee yet, and keeps no best update. -/
theorem initializeLightClientStore_invariant {config : Config} {trustedBlockRoot : Root}
    {bootstrap : LightClientBootstrap preset fork} {store : LightClientStore preset fork}
    (computed : initializeLightClientStore config trustedBlockRoot bootstrap = .ok store)
    (bootstrapServes : serves
      (computeSyncCommitteePeriodAtSlot preset bootstrap.header.beacon.slot)
      bootstrap.currentSyncCommittee) :
    store.Invariant serves := by
  unfold initializeLightClientStore at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals
    cases computed
    try exact ⟨UInt64.le_refl _, bootstrapServes,
      by simp [LightClientStore.isNextSyncCommitteeKnown], nofun⟩

/-- Processing an update keeps the invariant, when the next committee of the update serves.

The update can become the best update, which fits the store since the store accepted it.

An applied update keeps the committees in their periods, and the store drops its best update. -/
theorem processLightClientUpdate_invariant {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root} (invariant : store.Invariant serves)
    (proves : update.NextSyncCommitteeServes serves)
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    after.Invariant serves := by
  have ordered := (processLightClientUpdate_slots computed).2.2 invariant.finalized_le_optimistic
  unfold processLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  rename_i accepted
  have fits := validateLightClientUpdate_fitsUpdate accepted
  -- The update applies to the store with its new best update and optimistic header.
  have apply {before applied : LightClientStore preset fork}
      (computed : applyLightClientUpdate before update = .ok applied)
      (current : serves
        (computeSyncCommitteePeriodAtSlot preset before.finalizedHeader.beacon.slot)
        before.currentSyncCommittee)
      (next : before.isNextSyncCommitteeKnown = true →
        serves (computeSyncCommitteePeriodAtSlot preset before.finalizedHeader.beacon.slot + 1)
          before.nextSyncCommittee)
      (same : before.finalizedHeader = store.finalizedHeader)
      (sameNext : before.nextSyncCommittee = store.nextSyncCommittee) :=
    applyLightClientUpdate_syncCommittees current next
      (fits.congr (by rw [same]) (by simp [LightClientStore.isNextSyncCommitteeKnown, sameNext]))
      proves computed
  repeat' split at computed
  all_goals
    try
      have step := ‹applyLightClientUpdate _ _ = .ok _›
      have applied := apply step invariant.current invariant.next rfl rfl
    cases computed
  all_goals first
    | exact ⟨ordered, applied.1, applied.2, nofun⟩
    | refine ⟨ordered, invariant.current, invariant.next, fun best kept => ?_⟩
      -- The best update is the processed update, or the one that the store kept.
      have choice : update = best ∨ store.bestValidUpdate = some best := by
        first
          | exact Or.inl (Option.some.inj kept)
          | exact Or.inr kept
      rcases choice with rfl | old
      · exact ⟨fits.congr rfl rfl, proves⟩
      · obtain ⟨fitsBest, provesBest⟩ := invariant.best best old
        exact ⟨fitsBest.congr rfl rfl, provesBest⟩

/-- A forced update keeps the invariant.

The best update fits the store, so it applies as the update that the store accepted. -/
theorem processLightClientStoreForceUpdate_invariant {store after : LightClientStore preset fork}
    {currentSlot : Slot} (invariant : store.Invariant serves)
    (computed : processLightClientStoreForceUpdate store currentSlot = .ok after) :
    after.Invariant serves := by
  have ordered :=
    (processLightClientStoreForceUpdate_slots computed).2.2 invariant.finalized_le_optimistic
  unfold processLightClientStoreForceUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.require,
    LightClientError.requireFork] at computed
  repeat' split at computed
  all_goals
    try
      have step := ‹applyLightClientUpdate _ _ = .ok _›
      obtain ⟨fits, proves⟩ := invariant.best _ ‹store.bestValidUpdate = some _›
      -- The applied update is the best one, perhaps with its attested header as finalized.
      have applied := applyLightClientUpdate_syncCommittees invariant.current invariant.next
        (by split; exacts [fits.attestedFinalized, fits]) (by split <;> exact proves) step
    cases computed
  all_goals first
    | exact invariant
    | exact ⟨ordered, applied.1, applied.2, nofun⟩

/-- Processing a finality update keeps the invariant.

A finality update carries no committee branch, so its committee serves at once. -/
theorem processLightClientFinalityUpdate_invariant {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientFinalityUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root} (invariant : store.Invariant serves)
    (computed : processLightClientFinalityUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    after.Invariant serves :=
  processLightClientUpdate_invariant invariant
    (fun committee => by
      simp [LightClientFinalityUpdate.toUpdate, LightClientUpdate.isSyncCommitteeUpdate]
        at committee)
    computed

/-- Processing an optimistic update keeps the invariant.

An optimistic update carries no committee branch, so its committee serves at once. -/
theorem processLightClientOptimisticUpdate_invariant {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientOptimisticUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root} (invariant : store.Invariant serves)
    (computed : processLightClientOptimisticUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    after.Invariant serves :=
  processLightClientUpdate_invariant invariant
    (fun committee => by
      simp [LightClientOptimisticUpdate.toUpdate, LightClientUpdate.isSyncCommitteeUpdate]
        at committee)
    computed

/-- Processing an update moves the finalized header by at most one period.

It moves to the next period only when the store knows the committee of that period. -/
theorem processLightClientUpdate_period {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot ∨
      store.isNextSyncCommitteeKnown = true ∧
        computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
          computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1 := by
  unfold processLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  rename_i accepted
  have fits := validateLightClientUpdate_fitsUpdate accepted
  repeat' split at computed
  all_goals
    try
      have step := ‹applyLightClientUpdate _ _ = .ok _›
      have moved := (applyLightClientUpdate_period · step) (fits.congr rfl rfl)
    cases computed
  all_goals first
    | exact Or.inl rfl
    | exact moved

/-- A forced update moves the finalized header by at most one period.

It moves to the next period only when the store knows the committee of that period. -/
theorem processLightClientStoreForceUpdate_period {store after : LightClientStore preset fork}
    {currentSlot : Slot} (invariant : store.Invariant serves)
    (computed : processLightClientStoreForceUpdate store currentSlot = .ok after) :
    computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
        computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot ∨
      store.isNextSyncCommitteeKnown = true ∧
        computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
          computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot + 1 := by
  unfold processLightClientStoreForceUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.require,
    LightClientError.requireFork] at computed
  repeat' split at computed
  all_goals
    try
      have step := ‹applyLightClientUpdate _ _ = .ok _›
      obtain ⟨fits, -⟩ := invariant.best _ ‹store.bestValidUpdate = some _›
      have moved := applyLightClientUpdate_period
        (by split; exacts [fits.attestedFinalized, fits]) step
    cases computed
  all_goals first
    | exact Or.inl rfl
    | exact moved

/-- Processing an update keeps both committees while the finalized period stays.

This holds once the store knows its next committee.

So a known committee changes only when the finalized header enters the next period. -/
theorem processLightClientUpdate_syncCommittees_of_period_eq {config : Config}
    {checks : SignatureChecks} {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (known : store.isNextSyncCommitteeKnown = true)
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after)
    (stays : computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
      computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot) :
    after.currentSyncCommittee = store.currentSyncCommittee ∧
      after.nextSyncCommittee = store.nextSyncCommittee := by
  unfold processLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  rename_i accepted
  have fits := validateLightClientUpdate_fitsUpdate accepted
  repeat' split at computed
  all_goals
    try
      have step := ‹applyLightClientUpdate _ _ = .ok _›
      have kept := applyLightClientUpdate_syncCommittees_of_period_eq step (fits.congr rfl rfl)
        known
    cases computed
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact kept stays

/-- A forced update keeps both committees while the finalized period stays.

This holds once the store knows its next committee. -/
theorem processLightClientStoreForceUpdate_syncCommittees_of_period_eq
    {store after : LightClientStore preset fork} {currentSlot : Slot}
    (invariant : store.Invariant serves) (known : store.isNextSyncCommitteeKnown = true)
    (computed : processLightClientStoreForceUpdate store currentSlot = .ok after)
    (stays : computeSyncCommitteePeriodAtSlot preset after.finalizedHeader.beacon.slot =
      computeSyncCommitteePeriodAtSlot preset store.finalizedHeader.beacon.slot) :
    after.currentSyncCommittee = store.currentSyncCommittee ∧
      after.nextSyncCommittee = store.nextSyncCommittee := by
  unfold processLightClientStoreForceUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure, LightClientError.require,
    LightClientError.requireFork] at computed
  repeat' split at computed
  all_goals
    try
      have step := ‹applyLightClientUpdate _ _ = .ok _›
      obtain ⟨fits, -⟩ := invariant.best _ ‹store.bestValidUpdate = some _›
      have kept := applyLightClientUpdate_syncCommittees_of_period_eq step
        (by split; exacts [fits.attestedFinalized, fits]) known
    cases computed
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact kept stays

/-- An update that proves no finalized header newer than the store's keeps the finalized part.

The finalized header and the two committees stay as they are.

The store applies an update only for a newer finalized header, or a committee with finality. -/
theorem processLightClientUpdate_finalized_of_not_newer {config : Config}
    {checks : SignatureChecks} {store after : LightClientStore preset fork}
    {update : LightClientUpdate preset fork} {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (noFinality : update.isFinalityUpdate = false)
    (notNewer : update.finalizedHeader.beacon.slot ≤ store.finalizedHeader.beacon.slot)
    (computed : processLightClientUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    after.finalizedHeader = store.finalizedHeader ∧
      after.currentSyncCommittee = store.currentSyncCommittee ∧
      after.nextSyncCommittee = store.nextSyncCommittee := by
  unfold processLightClientUpdate at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  repeat' split at computed
  all_goals
    try
      have step := ‹applyLightClientUpdate _ _ = .ok _›
      -- The condition to apply the update fails.
      rename_i applies _ _ _
      exfalso
      obtain ⟨-, newer | committee⟩ := applies
      · dsimp only at newer
        simp only [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at newer notNewer
        omega
      · simp [noFinality] at committee
  all_goals cases computed
  all_goals exact ⟨rfl, rfl, rfl⟩

/-- An optimistic update never changes the finalized header or the sync committees.

It proves no finalized header and no committee, so the store never applies it. -/
theorem processLightClientOptimisticUpdate_finalized {config : Config} {checks : SignatureChecks}
    {store after : LightClientStore preset fork} {update : LightClientOptimisticUpdate preset fork}
    {currentSlot : Slot} {genesisValidatorsRoot : Root}
    (computed : processLightClientOptimisticUpdate config checks store update currentSlot
      genesisValidatorsRoot = .ok after) :
    after.finalizedHeader = store.finalizedHeader ∧
      after.currentSyncCommittee = store.currentSyncCommittee ∧
      after.nextSyncCommittee = store.nextSyncCommittee :=
  processLightClientUpdate_finalized_of_not_newer
    (by simp [LightClientOptimisticUpdate.toUpdate, LightClientUpdate.isFinalityUpdate])
    (by simp [LightClientOptimisticUpdate.toUpdate, LightClientHeader.empty,
      UInt64.le_iff_toNat_le])
    computed

end Handlers

section Upgrade

/-- A normalized branch is all zero exactly when the branch is. -/
theorem normalizeBranch_eq_replicate_iff {depth : Nat} (branch : Vector Bytes32 depth)
    (gindex : Nat) (deeper : depth ≤ Nat.log2 gindex) :
    normalizeBranch branch gindex deeper = Vector.replicate _ zeroBytes32 ↔
      branch = Vector.replicate _ zeroBytes32 := by
  rw [← Vector.toList_inj, ← Vector.toList_inj]
  simp only [normalizeBranch, normalizeMerkleBranch, Vector.toList_mk,
    Vector.toList_replicate, List.append_eq_replicate_iff, List.length_replicate,
    Vector.length_toList, true_and]
  constructor
  · exact fun ⟨_, proved⟩ => proved
  · exact fun proved => ⟨by omega, proved⟩

/-- An upgraded update keeps its beacon headers, its signature slot and its next committee.

It proves a next committee exactly when the update did. -/
theorem LightClientUpdate.upgrade_fields {config : Config} {pre post : Fork} {later : pre ≤ post}
    {update : LightClientUpdate preset pre} {upgraded : LightClientUpdate preset post}
    (computed : update.upgrade config post later = .ok upgraded) :
    upgraded.attestedHeader.beacon = update.attestedHeader.beacon ∧
      upgraded.finalizedHeader.beacon = update.finalizedHeader.beacon ∧
      upgraded.signatureSlot = update.signatureSlot ∧
      upgraded.nextSyncCommittee = update.nextSyncCommittee ∧
      upgraded.isSyncCommitteeUpdate = update.isSyncCommitteeUpdate := by
  unfold LightClientUpdate.upgrade at computed
  obtain ⟨attested, attestedOk, rest⟩ := Base.bind_ok_iff.mp computed
  obtain ⟨finalized, finalizedOk, rest⟩ := Base.bind_ok_iff.mp rest
  cases rest
  refine ⟨LightClientHeader.upgrade_beacon attestedOk, LightClientHeader.upgrade_beacon finalizedOk,
    rfl, rfl, ?_⟩
  simp only [LightClientUpdate.isSyncCommitteeUpdate, bne]
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, normalizeBranch_eq_replicate_iff]

/-- An upgraded store keeps the invariant.

It keeps its beacon headers and its committees, and its best update keeps what fits the store. -/
theorem LightClientStore.upgrade_invariant {serves : UInt64 → SyncCommittee preset → Prop}
    {config : Config} {pre post : Fork} {later : pre ≤ post} {store : LightClientStore preset pre}
    {upgraded : LightClientStore preset post} (invariant : store.Invariant serves)
    (computed : store.upgrade config post later = .ok upgraded) :
    upgraded.Invariant serves := by
  obtain ⟨finalizedBeacon, optimisticBeacon⟩ := LightClientStore.upgrade_beacon computed
  unfold LightClientStore.upgrade at computed
  obtain ⟨finalized, finalizedOk, rest⟩ := Base.bind_ok_iff.mp computed
  obtain ⟨best, bestOk, rest⟩ := Base.bind_ok_iff.mp rest
  obtain ⟨optimistic, optimisticOk, rest⟩ := Base.bind_ok_iff.mp rest
  cases rest
  simp only at finalizedBeacon optimisticBeacon
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [finalizedBeacon, optimisticBeacon] using invariant.finalized_le_optimistic
  · simpa [finalizedBeacon] using invariant.current
  · intro known
    rw [finalizedBeacon]
    exact invariant.next known
  · intro kept keptBest
    -- The kept update is the upgrade of the best update of the store.
    cases stored : store.bestValidUpdate with
    | none =>
      rw [stored] at bestOk
      cases bestOk
      cases keptBest
    | some old =>
      rw [stored] at bestOk
      obtain ⟨fits, proves⟩ := invariant.best old stored
      simp only [Option.mapM_some] at bestOk
      cases upgradedOk : old.upgrade config post later with
      | error _ =>
        rw [upgradedOk] at bestOk
        cases bestOk
      | ok new =>
        rw [upgradedOk] at bestOk
        cases bestOk
        cases keptBest
        obtain ⟨attestedBeacon, finalizedBeacon', signature, next, committee⟩ :=
          LightClientUpdate.upgrade_fields upgradedOk
        obtain ⟨ordered, signed, period, relevant, empty⟩ := fits
        simp only [LightClientStore.isNextSyncCommitteeKnown] at period
        refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · simpa [attestedBeacon, finalizedBeacon'] using ordered
        · simpa [attestedBeacon, signature] using signed
        · simpa [LightClientStore.isNextSyncCommitteeKnown, signature, finalizedBeacon] using period
        · simpa [attestedBeacon, finalizedBeacon] using relevant
        · simpa [committee, next] using empty
        · intro proved
          rw [committee] at proved
          simpa [attestedBeacon, next] using proves proved

end Upgrade

end EthLib.Consensus
