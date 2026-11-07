module

public import EthLib.Consensus.Proofs.Transition.BuilderRegistry
public import EthLib.Consensus.Proofs.Transition.BuilderPayments

/-!
# Proofs: builders can always pay what they owe, along every chain from Gloas

From Gloas a builder pays for its bids from its balance, as [EIP-7732] specifies.

The payment of a bid waits among the pending payments of the state.

It joins the queue of builder withdrawals once the payload of the bid is applied.

It also joins it at the end of the next epoch, if enough attesters supported the block.

Otherwise it leaves the pending payments, and the bid may still charge its builder later.

That happens when a later block applies the payload of the bid after the payment has left.

A withdrawal lowers the balance of a builder to at least zero.

The rule does not check that the balance holds the amount of the withdrawal.

This file shows that the check is never needed.

Each builder owes at most its balance.

What it owes is its queued withdrawals and its pending payments.

When the latest bid could still charge it, its balance also holds the value of that bid.

A builder that has started to exit owes nothing, and no bid can charge it.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- The parts of a state from Gloas that what builders owe and hold depends on. -/
structure Ledger (preset : Preset) (fork : Base.Fork) where
  /-- The slot of the state. -/
  slot : Slot
  /-- The slot of the latest block header. -/
  headerSlot : Slot
  /-- The hash of the latest payload that was applied. -/
  blockHash : Hash32
  /-- The latest bid. -/
  bid : ExecutionPayloadBid preset fork
  /-- The registry of builders. -/
  builders : Array Builder
  /-- The pending payments, in order. -/
  payments : List BuilderPendingPayment
  /-- The queue of builder withdrawals, in order. -/
  queue : List BuilderPendingWithdrawal

/-- The ledger of a state from Gloas. -/
def ledgerOf (state : BeaconState preset fork) (gloas : .glamsterdam ≤ fork) :
    Ledger preset fork :=
  ⟨state.slot, state.latestBlockHeader.slot, state.latestBlockHash gloas,
    state.latestExecutionPayloadBid gloas, (state.builders gloas).data,
    (state.builderPendingPayments gloas).elements.toList,
    (state.builderPendingWithdrawals gloas).data.toList⟩

namespace Ledger

variable (ledger : Ledger preset fork)

/-- The current epoch. -/
def currentEpoch : Epoch :=
  computeEpochAtSlot preset ledger.slot

/-- The previous epoch, or the current one at genesis. -/
def previousEpoch : Epoch :=
  saturatingSub ledger.currentEpoch 1

/-- The position of the payment of a bid at a slot, among the pending payments.

A bid of the current epoch has its payment in the second half.

A bid of the previous epoch has it in the first half.

An older bid has no payment there. -/
def position (slot : Slot) : Option UInt64 :=
  let epoch := computeEpochAtSlot preset slot
  let position := slot % preset.SLOTS_PER_EPOCH
  if epoch = ledger.currentEpoch then some (preset.SLOTS_PER_EPOCH + position)
  else if epoch = ledger.previousEpoch then some position
  else none

/-- What a builder owes: its queued withdrawals and its pending payments. -/
def owed (index : BuilderIndex) : Nat :=
  owedBy index ledger.queue + owedBy index (ledger.payments.map (·.withdrawal))

/-- The payload of the latest bid is not applied yet. -/
def Pending : Prop :=
  ledger.blockHash ≠ ledger.bid.blockHash

/-- The payment of the latest bid still waits at its position. -/
def Held : Prop :=
  ∃ position payment, ledger.position ledger.bid.slot = some position ∧
    ledger.payments[position.toNat]? = some payment ∧
    payment.withdrawal.builderIndex = ledger.bid.builderIndex ∧
    payment.withdrawal.amount = ledger.bid.value

/-- The latest bid may still charge a builder, beyond what it owes.

Its payload is not applied yet, and its payment has left its position. -/
def Latent (index : BuilderIndex) : Prop :=
  ledger.Pending ∧ ledger.bid.builderIndex = index ∧ ¬ ledger.Held

/-- Every builder can pay what it owes, and what the latest bid may still charge it.

A builder that has started to exit owes nothing, and no bid of a value charges it.

Neither does an index past the registry.

While the payload of a valued bid is not applied, no attester supports its payment yet. -/
structure Solvent : Prop where
  covered : ∀ (index : BuilderIndex) (builder : Builder),
    ledger.builders[index.toNat]? = some builder → ledger.owed index ≤ builder.balance.toNat
  latent : ∀ (index : BuilderIndex) (builder : Builder),
    ledger.builders[index.toNat]? = some builder → ledger.Latent index →
      ledger.owed index + ledger.bid.value.toNat ≤ builder.balance.toNat
  idle : ∀ index : BuilderIndex,
    (∀ builder, ledger.builders[index.toNat]? = some builder →
      builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH) →
      ledger.owed index = 0 ∧ (ledger.Latent index → ledger.bid.value = 0)
  quiet : ledger.Pending → 0 < ledger.bid.value →
    ∀ (position : UInt64) (payment : BuilderPendingPayment),
      ledger.position ledger.bid.slot = some position →
      ledger.payments[position.toNat]? = some payment → payment.weight = 0

/-- The latest bid has no value, or its payload waits and it is the bid of the latest block.

That block is not later than the state. -/
def Shaped : Prop :=
  ledger.bid.value = 0 ∨
    (ledger.Pending ∧ ledger.bid.slot = ledger.headerSlot ∧ ledger.bid.slot ≤ ledger.slot)

end Ledger

/-- What a builder owes in a state is what it owes in its ledger. -/
theorem pendingBuilderTotal_eq_owed (gloas : .glamsterdam ≤ fork) (index : BuilderIndex) :
    pendingBuilderTotal state gloas index = (ledgerOf state gloas).owed index :=
  rfl

/-- The position of the payment of the parent block is that of its slot in the ledger. -/
theorem parentPaymentPosition_eq (gloas : .glamsterdam ≤ fork) :
    parentPaymentPosition state =
      (ledgerOf state gloas).position state.latestBlockHeader.slot :=
  rfl


/-! ## The presets -/

/-- The conditions on a preset under which builders stay solvent.

An epoch has at least six slots, and at most `2^32`.

The smallest total active balance is two units per slot or more, so the quorum is positive.

An attestation is included at least one slot after its own. -/
structure PaymentPreset (preset : Preset) : Prop where
  slots : 6 ≤ preset.SLOTS_PER_EPOCH.toNat
  small : preset.SLOTS_PER_EPOCH.toNat ≤ 2 ^ 32
  quorum : 2 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.EFFECTIVE_BALANCE_INCREMENT.toNat
  delay : 1 ≤ preset.MIN_ATTESTATION_INCLUSION_DELAY.toNat

/-- Both presets meet the conditions. -/
theorem paymentPreset_mainnet : PaymentPreset Preset.mainnet :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem paymentPreset_minimal : PaymentPreset Preset.minimal :=
  ⟨by decide, by decide, by decide, by decide⟩

/-! ## Owed amounts -/

theorem owedBy_append (index : BuilderIndex) (first second : List BuilderPendingWithdrawal) :
    owedBy index (first ++ second) = owedBy index first + owedBy index second := by
  simp [owedBy]

theorem owedBy_cons (index : BuilderIndex) (withdrawal : BuilderPendingWithdrawal)
    (rest : List BuilderPendingWithdrawal) :
    owedBy index (withdrawal :: rest) = owedBy index [withdrawal] + owedBy index rest := by
  simp [owedBy]

/-- The payments of no bid owe nothing. -/
theorem owedBy_replicate_empty (index : BuilderIndex) (count : Nat) :
    owedBy index ((List.replicate count BuilderPendingPayment.empty).map (·.withdrawal)) = 0 := by
  induction count with
  | zero => simp [owedBy]
  | succ count ih =>
    simp only [List.replicate_succ, List.map_cons] at ih ⊢
    rw [owedBy_cons, ih]
    simp [owedBy, BuilderPendingPayment.empty]

/-- Some payments owe what the part of them that a test keeps owes, plus what the rest owes. -/
theorem owedBy_filter_add (index : BuilderIndex) (keep : BuilderPendingPayment → Bool) :
    ∀ payments : List BuilderPendingPayment,
      owedBy index ((payments.filter keep).map (·.withdrawal)) +
          owedBy index ((payments.filter (fun payment => !keep payment)).map (·.withdrawal)) =
        owedBy index (payments.map (·.withdrawal))
  | [] => by simp [owedBy]
  | payment :: rest => by
    have ih := owedBy_filter_add index keep rest
    simp only [owedBy, List.filter_cons, List.map_cons, List.sum_cons] at ih ⊢
    cases keep payment <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, List.map_cons, List.sum_cons] <;> omega

/-- One withdrawal of a list owes at most what the list owes. -/
theorem owedBy_le_of_mem {index : BuilderIndex} {withdrawal : BuilderPendingWithdrawal} :
    ∀ {withdrawals : List BuilderPendingWithdrawal}, withdrawal ∈ withdrawals →
      owedBy index [withdrawal] ≤ owedBy index withdrawals
  | first :: rest, member => by
    have step : owedBy index (first :: rest) = owedBy index [first] + owedBy index rest := by
      simp [owedBy]
    rw [step]
    rcases List.mem_cons.mp member with rfl | inner
    · omega
    · have := owedBy_le_of_mem (index := index) inner
      omega

/-- One withdrawal of a builder owes it its amount. -/
theorem owedBy_single {index : BuilderIndex} {withdrawal : BuilderPendingWithdrawal}
    (named : withdrawal.builderIndex = index) :
    owedBy index [withdrawal] = withdrawal.amount.toNat := by
  simp [owedBy, named]

/-! ## Positions -/

/-- The position of the payment of a bid, on natural numbers. -/
theorem Ledger.position_toNat (ledger : Ledger preset fork) (pp : PaymentPreset preset)
    (slot : Slot) :
    (ledger.position slot).map UInt64.toNat =
      if slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
          ledger.slot.toNat / preset.SLOTS_PER_EPOCH.toNat then
        some (preset.SLOTS_PER_EPOCH.toNat + slot.toNat % preset.SLOTS_PER_EPOCH.toNat)
      else if slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
          ledger.slot.toNat / preset.SLOTS_PER_EPOCH.toNat - 1 then
        some (slot.toNat % preset.SLOTS_PER_EPOCH.toNat)
      else none := by
  have slots := pp.slots
  have small := pp.small
  have nonzero : preset.SLOTS_PER_EPOCH ≠ 0 := by
    intro zero
    rw [zero] at slots
    simp at slots
  have rest := toNat_mod_lt (i := slot) nonzero
  have sum : (preset.SLOTS_PER_EPOCH + slot % preset.SLOTS_PER_EPOCH).toNat =
      preset.SLOTS_PER_EPOCH.toNat + slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mod, ← UInt64.toNat_mod]
    exact Nat.mod_eq_of_lt (by rw [UInt64.toNat_mod] at rest ⊢; omega)
  unfold Ledger.position Ledger.previousEpoch Ledger.currentEpoch computeEpochAtSlot
  simp only [← UInt64.toNat_inj, UInt64.toNat_div, toNat_saturatingSub, UInt64.toNat_one]
  by_cases same : slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
      ledger.slot.toNat / preset.SLOTS_PER_EPOCH.toNat
  · simp only [same, ↓reduceIte, Option.map_some, sum]
  · simp only [same, ↓reduceIte]
    split
    · simp [UInt64.toNat_mod]
    · rfl

/-! ## A slot step -/

/-- A slot within the same epoch keeps every position, so it keeps a solvent ledger solvent. -/
theorem Ledger.Solvent.tick {ledger : Ledger preset fork} (solvent : ledger.Solvent)
    {next : Slot}
    (epochs : computeEpochAtSlot preset next = computeEpochAtSlot preset ledger.slot) :
    ({ ledger with slot := next } : Ledger preset fork).Solvent := by
  have positions :
      ({ ledger with slot := next } : Ledger preset fork).position = ledger.position := by
    funext slot
    unfold Ledger.position Ledger.previousEpoch Ledger.currentEpoch
    rw [epochs]
  have latents : ∀ index, ({ ledger with slot := next } : Ledger preset fork).Latent index ↔
      ledger.Latent index := by
    intro index
    simp only [Ledger.Latent, Ledger.Held, Ledger.Pending, positions]
  obtain ⟨covered, latent, idle, quiet⟩ := solvent
  refine ⟨covered, ?_, ?_, ?_⟩
  · intro index builder found later
    exact latent index builder found ((latents _).mp later)
  · intro index set
    obtain ⟨zero, charge⟩ := idle index set
    exact ⟨zero, fun later => charge ((latents _).mp later)⟩
  · intro pending positive position payment located found
    rw [positions] at located
    exact quiet pending positive position payment located found

/-- The ledger after the end of an epoch, at the first slot of the next one.

The payments move down by one epoch, and those of the first epoch that reach the quorum are queued.
-/
def Ledger.epochStep (ledger : Ledger preset fork) (next : Slot) (quorum : Gwei) :
    Ledger preset fork :=
  { ledger with
    slot := next
    payments := ledger.payments.drop preset.SLOTS_PER_EPOCH.toNat ++
      List.replicate preset.SLOTS_PER_EPOCH.toNat BuilderPendingPayment.empty
    queue := ledger.queue ++
      releasedPayments ledger.payments preset.SLOTS_PER_EPOCH.toNat quorum }

/-- At the end of an epoch a builder owes no more, and what it owes falls by what is dropped.

The dropped payments are those of the first epoch below the quorum. -/
theorem Ledger.owed_epochStep (ledger : Ledger preset fork) (next : Slot) (quorum : Gwei)
    (index : BuilderIndex) :
    (ledger.epochStep next quorum).owed index +
        owedBy index (((ledger.payments.take preset.SLOTS_PER_EPOCH.toNat).filter
          (fun payment => !decide (quorum ≤ payment.weight))).map (·.withdrawal)) =
      ledger.owed index := by
  have split := owedBy_filter_add index (fun payment => decide (quorum ≤ payment.weight))
    (ledger.payments.take preset.SLOTS_PER_EPOCH.toNat)
  have halves : owedBy index (ledger.payments.map (·.withdrawal)) =
      owedBy index ((ledger.payments.take preset.SLOTS_PER_EPOCH.toNat).map (·.withdrawal)) +
        owedBy index ((ledger.payments.drop preset.SLOTS_PER_EPOCH.toNat).map (·.withdrawal)) := by
    rw [← owedBy_append, ← List.map_append, List.take_append_drop]
  unfold Ledger.owed Ledger.epochStep releasedPayments
  simp only [List.map_append, owedBy_append, owedBy_replicate_empty] at halves ⊢
  omega


/-- The slot before the first slot of an epoch is in the epoch before. -/
theorem div_last {n slots : Nat} (positive : 0 < slots) (first : n % slots = 0) (nonzero : 0 < n) :
    (n - 1) / slots + 1 = n / slots := by
  obtain ⟨q, rfl⟩ : ∃ q, n = slots * q :=
    ⟨n / slots, by have := Nat.div_add_mod n slots; omega⟩
  have later : 0 < q := by
    rcases Nat.eq_zero_or_pos q with zero | pos
    · subst zero
      simp at nonzero
    · exact pos
  have split : slots * q - 1 = slots * (q - 1) + (slots - 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_sub_cancel]
    omega
  rw [split, Nat.mul_add_div positive, Nat.div_eq_of_lt (by omega),
    Nat.mul_div_cancel_left _ positive]
  omega

/-- The end of an epoch keeps a solvent ledger solvent.

The payment of the latest bid, if it is still held and of the epoch that ends, has no support.

So it does not reach the quorum, and leaves the payments instead of joining the queue.

The latest bid may then still charge its builder, who can pay it. -/
theorem Ledger.Solvent.epochStep {ledger : Ledger preset fork} (pp : PaymentPreset preset)
    (solvent : ledger.Solvent) (shaped : ledger.Shaped)
    (length : ledger.payments.length = 2 * preset.SLOTS_PER_EPOCH.toNat)
    {next : Slot} (step : next.toNat = ledger.slot.toNat + 1)
    (boundary : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0)
    {quorum : Gwei} (positive : 0 < quorum) :
    (ledger.epochStep next quorum).Solvent := by
  have slots := pp.slots
  have epochs : ledger.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 =
      (ledger.epochStep next quorum).slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
    have last := div_last (n := next.toNat) (by omega) boundary (by omega)
    have previous : next.toNat - 1 = ledger.slot.toNat := by omega
    rw [previous] at last
    exact last
  obtain ⟨covered, latent, idle, quiet⟩ := solvent
  -- What each builder owes falls by what is dropped.
  have owedLe : ∀ index, (ledger.epochStep next quorum).owed index ≤ ledger.owed index :=
    fun index => by have := ledger.owed_epochStep next quorum index; omega
  have before := ledger.position_toNat pp ledger.bid.slot
  have after := (ledger.epochStep next quorum).position_toNat pp ledger.bid.slot
  rw [← epochs, Nat.add_sub_cancel] at after
  -- A payment of the second half moves to the first, and the second half is empty.
  have moved : ∀ k, k < preset.SLOTS_PER_EPOCH.toNat →
      (ledger.epochStep next quorum).payments[k]? =
        ledger.payments[preset.SLOTS_PER_EPOCH.toNat + k]? := by
    intro k small
    simp only [Ledger.epochStep]
    rw [List.getElem?_append_left (by simp [length]; omega), List.getElem?_drop]
  have mod := Nat.mod_lt ledger.bid.slot.toNat (show 0 < preset.SLOTS_PER_EPOCH.toNat by omega)
  -- The two ledgers agree on the bid and on whether its payload waits.
  have bid : (ledger.epochStep next quorum).bid = ledger.bid := rfl
  have pending : (ledger.epochStep next quorum).Pending ↔ ledger.Pending := Iff.rfl
  by_cases same :
      ledger.bid.slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
        ledger.slot.toNat / preset.SLOTS_PER_EPOCH.toNat
  · -- A bid of the epoch that ends keeps its payment, one epoch lower.
    simp only [same, ↓reduceIte] at before
    have sameNext : ¬ ledger.bid.slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
        ledger.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by omega
    simp only [↓reduceIte, same] at after
    -- The positions of the bid before and after, on natural numbers.
    have positionBefore : ∀ old, ledger.position ledger.bid.slot = some old →
        old.toNat = preset.SLOTS_PER_EPOCH.toNat +
          ledger.bid.slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by
      intro old hp
      simpa [hp] using before
    have positionAfter : ∀ new, (ledger.epochStep next quorum).position ledger.bid.slot = some new →
        new.toNat = ledger.bid.slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by
      intro new hp
      simpa [hp] using after
    have someBefore : ∃ old, ledger.position ledger.bid.slot = some old := by
      cases hp : ledger.position ledger.bid.slot with
      | none => simp [hp] at before
      | some old => exact ⟨old, rfl⟩
    have someAfter : ∃ new, (ledger.epochStep next quorum).position ledger.bid.slot = some new := by
      cases hp : (ledger.epochStep next quorum).position ledger.bid.slot with
      | none => simp [hp] at after
      | some new => exact ⟨new, rfl⟩
    obtain ⟨old, oldAt⟩ := someBefore
    obtain ⟨new, newAt⟩ := someAfter
    have read : (ledger.epochStep next quorum).payments[new.toNat]? =
        ledger.payments[old.toNat]? := by
      rw [positionAfter new newAt, positionBefore old oldAt, moved _ mod]
    have held : (ledger.epochStep next quorum).Held ↔ ledger.Held := by
      unfold Ledger.Held
      rw [bid]
      constructor
      · rintro ⟨position, payment, located, found, named, amount⟩
        rw [newAt, Option.some.injEq] at located
        subst located
        exact ⟨old, payment, oldAt, read ▸ found, named, amount⟩
      · rintro ⟨position, payment, located, found, named, amount⟩
        rw [oldAt, Option.some.injEq] at located
        subst located
        exact ⟨new, payment, newAt, read.trans found, named, amount⟩
    have latents : ∀ index, (ledger.epochStep next quorum).Latent index ↔ ledger.Latent index :=
      fun index => by simp only [Ledger.Latent, pending, held, bid]
    refine ⟨fun index builder found => Nat.le_trans (owedLe _) (covered index builder found),
      fun index builder found later => ?_, fun index set => ?_,
      fun waits valued position payment located found => ?_⟩
    · have := latent index builder found ((latents _).mp later)
      have := owedLe index
      rw [bid]
      omega
    · obtain ⟨zero, charge⟩ := idle index set
      exact ⟨Nat.le_zero.mp (zero ▸ owedLe _), fun later => charge ((latents _).mp later)⟩
    · rw [bid, newAt, Option.some.injEq] at located
      subst located
      exact quiet waits valued old payment oldAt (read ▸ found)
  · -- A bid of no value charges nothing.
    by_cases zero : ledger.bid.value = 0
    · refine ⟨fun index builder found => Nat.le_trans (owedLe _) (covered index builder found),
        fun index builder found _ => ?_, fun index set => ?_,
        fun _ valued => absurd valued (by rw [bid, zero]; decide)⟩
      · have := covered index builder found
        have := owedLe index
        rw [bid, zero]
        simp only [UInt64.toNat_zero, Nat.add_zero]
        omega
      · obtain ⟨owesNothing, _⟩ := idle index set
        exact ⟨Nat.le_zero.mp (owesNothing ▸ owedLe _), fun _ => zero⟩
    -- A bid of a value is of the epoch before, or older, so it has no position after the epoch.
    obtain ⟨waits, _, early⟩ := shaped.resolve_left zero
    have older : ledger.bid.slot.toNat / preset.SLOTS_PER_EPOCH.toNat <
        ledger.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      have := Nat.div_le_div_right (c := preset.SLOTS_PER_EPOCH.toNat)
        (UInt64.le_iff_toNat_le.mp early)
      omega
    have noneAfter : (ledger.epochStep next quorum).position ledger.bid.slot = none := by
      have differ : ¬ ledger.bid.slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
          ledger.slot.toNat / preset.SLOTS_PER_EPOCH.toNat + 1 := by omega
      simp only [differ, ↓reduceIte, same] at after
      cases hp : (ledger.epochStep next quorum).position ledger.bid.slot with
      | none => rfl
      | some _ => simp [hp] at after
    have notHeld : ¬ (ledger.epochStep next quorum).Held := by
      rintro ⟨position, _, located, -⟩
      rw [bid, noneAfter] at located
      cases located
    -- A payment that is still held has no support, so the end of the epoch drops it.
    have dropped : ledger.Held → ledger.owed ledger.bid.builderIndex ≥
        (ledger.epochStep next quorum).owed ledger.bid.builderIndex + ledger.bid.value.toNat := by
      rintro ⟨old, payment, oldAt, found, named, amount⟩
      have spot : old.toNat = ledger.bid.slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by
        have := before
        rw [oldAt] at this
        simp only [same, ↓reduceIte] at this
        split at this <;> simp_all
      have weight := quiet waits (by
        rcases Nat.eq_zero_or_pos ledger.bid.value.toNat with z | z
        · exact absurd (UInt64.toNat_inj.mp (by simpa using z)) zero
        · exact UInt64.lt_iff_toNat_lt.mpr z) old payment oldAt found
      have inside : payment ∈ (ledger.payments.take preset.SLOTS_PER_EPOCH.toNat).filter
          (fun payment => !decide (quorum ≤ payment.weight)) := by
        have taken : (ledger.payments.take preset.SLOTS_PER_EPOCH.toNat)[old.toNat]? =
            some payment := by
          rw [List.getElem?_take, ite_eq_left (by omega)]
          exact found
        refine List.mem_filter.mpr ⟨List.mem_of_getElem? taken, ?_⟩
        · simp only [weight, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
          exact UInt64.not_le.mpr positive
      have single := owedBy_le_of_mem (index := ledger.bid.builderIndex)
        (List.mem_map_of_mem (f := (·.withdrawal)) inside)
      rw [owedBy_single named, amount] at single
      have := ledger.owed_epochStep next quorum ledger.bid.builderIndex
      omega
    refine ⟨fun index builder found => Nat.le_trans (owedLe _) (covered index builder found),
      fun index builder found later => ?_, fun index set => ?_,
      fun _ _ position _ located => by rw [bid, noneAfter] at located; cases located⟩
    · obtain ⟨_, named, _⟩ := later
      rw [bid] at named ⊢
      by_cases isHeld : ledger.Held
      · have drop := dropped isHeld
        rw [named] at drop
        have := covered index builder found
        omega
      · have := latent index builder found ⟨waits, named, isHeld⟩
        have := owedLe index
        omega
    · obtain ⟨owesNothing, charge⟩ := idle index set
      refine ⟨Nat.le_zero.mp (owesNothing ▸ owedLe _), fun later => ?_⟩
      obtain ⟨_, named, _⟩ := later
      rw [bid] at named ⊢
      by_cases isHeld : ledger.Held
      · have := dropped isHeld
        rw [named, owesNothing] at this
        exact UInt64.toNat_inj.mp (by simp only [UInt64.toNat_zero]; omega)
      · exact charge ⟨waits, named, isHeld⟩

/-! ## The epoch transition and the slot step -/

/-- The payments moved by one epoch, as a list. -/
theorem shiftPayments_toList (payments : BuilderPendingPayments preset) :
    (shiftPayments payments).elements.toList =
      payments.elements.toList.drop preset.SLOTS_PER_EPOCH.toNat ++
        List.replicate preset.SLOTS_PER_EPOCH.toNat BuilderPendingPayment.empty := by
  apply List.ext_getElem
  · simp
    omega
  · intro k inside _
    simp only [Vector.getElem_toList]
    by_cases early : k < preset.SLOTS_PER_EPOCH.toNat
    · have read := getElem_shiftPayments_early payments early
      change (shiftPayments payments).elements[k] = _ at read
      rw [read, List.getElem_append_left (by simp; omega)]
      simp [Nat.add_comm]
      rfl
    · have inner : k < 2 * preset.SLOTS_PER_EPOCH.toNat := by simpa using inside
      have read := getElem_shiftPayments_late payments (Nat.le_of_not_lt early) inner
      change (shiftPayments payments).elements[k] = _ at read
      rw [read, List.getElem_append_right (by simp; omega)]
      simp

/-- The total active balance is at least one increment. -/
theorem getTotalActiveBalance_ge {total : Gwei}
    (computed : getTotalActiveBalance state = .ok total) :
    preset.EFFECTIVE_BALANCE_INCREMENT ≤ total := by
  unfold getTotalActiveBalance getTotalBalance at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  split at computed
  · cases computed
  · split at computed
    · cases computed
    · cases computed
      rw [UInt64.max_def]
      split
      · assumption
      · exact UInt64.le_refl _

/-- The quorum of a payment is positive.

It is six tenths of the total active balance per slot, which is at least two units. -/
theorem getBuilderPaymentQuorumThreshold_pos (pp : PaymentPreset preset) {quorum : Gwei}
    (computed : getBuilderPaymentQuorumThreshold state = .ok quorum) : 0 < quorum := by
  have slots := pp.slots
  have least := pp.quorum
  cases totalOk : getTotalActiveBalance state with
  | error _ =>
    simp [getBuilderPaymentQuorumThreshold, totalOk, bind, Except.bind] at computed
  | ok total =>
    rw [getBuilderPaymentQuorumThreshold_of_total totalOk slots] at computed
    cases computed
    have ge := UInt64.le_iff_toNat_le.mp (getTotalActiveBalance_ge totalOk)
    have six : BUILDER_PAYMENT_THRESHOLD_NUMERATOR.toNat = 6 := rfl
    have ten : BUILDER_PAYMENT_THRESHOLD_DENOMINATOR.toNat = 10 := rfl
    have perSlot : 2 ≤ total.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
    have fits : total.toNat / preset.SLOTS_PER_EPOCH.toNat * 6 < 2 ^ 64 := by
      have : total.toNat / preset.SLOTS_PER_EPOCH.toNat ≤ total.toNat / 6 :=
        Nat.div_le_div_left slots (by decide)
      have := total.toNat_lt
      omega
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div, UInt64.toNat_mul, UInt64.toNat_div, six, ten,
      Nat.mod_eq_of_lt fits]
    simp only [UInt64.toNat_zero]
    omega

/-! ## Steps that keep the ledger -/

/-- A later state of the same fork with the same ledger. -/
structure LedgerKept (state after : BeaconState preset fork) : Prop where
  same : ∀ gloas, ledgerOf after gloas = ledgerOf state gloas

namespace LedgerKept

theorem refl (state : BeaconState preset fork) : LedgerKept state state :=
  ⟨fun _ => rfl⟩

theorem trans {first second third : BeaconState preset fork}
    (one : LedgerKept first second) (two : LedgerKept second third) : LedgerKept first third :=
  ⟨fun gloas => (two.same gloas).trans (one.same gloas)⟩

theorem of_eq (same : ∀ gloas, ledgerOf after gloas = ledgerOf state gloas) :
    LedgerKept state after :=
  ⟨same⟩

theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → LedgerKept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : LedgerKept state after :=
  foldlM_ok_invariant (LedgerKept state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

theorem setValidator {index : ValidatorIndex} {validator : Validator}
    (set : state.setValidator index validator = .ok after) : LedgerKept state after := by
  obtain ⟨_, rfl⟩ := setValidator_ok set
  exact .of_eq fun _ => rfl

theorem setBalance {index : ValidatorIndex} {balance : Gwei}
    (set : state.setBalance index balance = .ok after) : LedgerKept state after := by
  obtain ⟨_, rfl⟩ := setBalance_ok set
  exact .of_eq fun _ => rfl

theorem increaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : increaseBalance state index delta = .ok after) : LedgerKept state after :=
  have ⟨_, set⟩ := increaseBalance_ok computed
  .setBalance set

theorem decreaseBalance {index : ValidatorIndex} {delta : Gwei}
    (computed : decreaseBalance state index delta = .ok after) : LedgerKept state after :=
  have ⟨_, set⟩ := decreaseBalance_ok computed
  .setBalance set

end LedgerKept

theorem ledgerKept_computeExitEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {exitBalance : Gwei} {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    LedgerKept state after := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, ⟨_, _⟩, _, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact .of_eq fun _ => rfl

theorem ledgerKept_computeConsolidationEpochAndUpdateChurn {electra : .pectra ≤ fork}
    {balance : Gwei} {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    LedgerKept state after := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, ⟨_, _⟩, _, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact .of_eq fun _ => rfl

theorem ledgerKept_exitQueue {exitBalance : Gwei} {exitEpoch : Epoch}
    (computed : exitQueue config state exitBalance = .ok (after, exitEpoch)) :
    LedgerKept state after := by
  unfold exitQueue at computed
  split at computed
  · exact ledgerKept_computeExitEpochAndUpdateChurn computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨_, _, rfl, _⟩ := computed
    exact .refl _

theorem ledgerKept_initiateValidatorExit {index : ValidatorIndex}
    (computed : initiateValidatorExit config state index = .ok after) :
    LedgerKept state after := by
  obtain ⟨_, _, ⟨_, rfl⟩ | ⟨_, _, _, _, queue, _, set⟩⟩ := initiateValidatorExit_ok computed
  · exact .refl _
  · exact (ledgerKept_exitQueue queue).trans (.setValidator set)

theorem ledgerKept_processRandao {body : BeaconBlockBody preset fork}
    (computed : processRandao config checks state body = .ok after) :
    LedgerKept state after := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := processRandao_eq computed
  exact .of_eq fun _ => rfl

theorem ledgerKept_processEth1Data {before : fork < .hegota}
    {body : BeaconBlockBody preset fork}
    (computed : processEth1Data before state body = .ok after) :
    LedgerKept state after := by
  obtain ⟨_, _, rest⟩ := processEth1Data_eq computed
  exact .of_eq fun _ => by rw [← rest]; rfl

theorem ledgerKept_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    LedgerKept state after := by
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    exact .of_eq fun _ => rfl
  · split at computed
    · cases computed
      exact .of_eq fun _ => rfl
    · cases computed

theorem ledgerKept_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    LedgerKept state after := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    split at computed
    · exact ledgerKept_addValidatorToRegistry computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      exact computed ▸ .refl _
  · rw [liftAccessor_ok] at computed
    exact .increaseBalance computed

theorem ledgerKept_applyDeposit {pubkey : BLSPubkey} {withdrawalCredentials : Bytes32}
    {amount : Gwei} {signature : BLSSignature}
    (computed :
      applyDeposit config checks state pubkey withdrawalCredentials amount signature = .ok after) :
    LedgerKept state after := by
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
        exact (ledgerKept_addValidatorToRegistry added).trans (.of_eq fun _ => rfl)
      · cases computed
        exact .refl _
    · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact .of_eq fun _ => rfl
  · exact ledgerKept_applyPendingDeposit computed

theorem ledgerKept_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    LedgerKept state after := by
  obtain ⟨_, _, next, _, applied⟩ := processDeposit_ok computed
  exact (LedgerKept.of_eq (state := state)
    (after := { state with eth1DepositIndex := fun _ => next }) fun _ => rfl).trans
    (ledgerKept_applyDeposit applied)

theorem ledgerKept_processVoluntaryExit {signed : SignedVoluntaryExit}
    (computed : processVoluntaryExit config checks state signed = .ok after) :
    LedgerKept state after := by
  unfold processVoluntaryExit at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftSsz_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, exited⟩ := computed
  exact ledgerKept_initiateValidatorExit exited

theorem ledgerKept_processDepositRequest {electra : .pectra ≤ fork}
    {request : DepositRequest}
    (computed : processDepositRequest state electra request = .ok after) :
    LedgerKept state after := by
  obtain ⟨start, recorded⟩ :=
    recordDepositRequestsStart_eq (state := state) (index := request.index)
  simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact .of_eq fun _ => rfl

theorem ledgerKept_requestPartialWithdrawal {electra : .pectra ≤ fork}
    {index : ValidatorIndex} {validator : Validator} {amount owed : Gwei}
    (computed : requestPartialWithdrawal config state electra index validator amount owed =
      .ok after) :
    LedgerKept state after := by
  simp only [requestPartialWithdrawal, bind_ok_iff, liftAccessor_ok, pure, Except.pure] at computed
  obtain ⟨_, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, Except.ok.injEq] at computed
    obtain ⟨⟨_, _⟩, churned, _, _, _, _, rfl⟩ := computed
    exact (ledgerKept_computeExitEpochAndUpdateChurn churned).trans (.of_eq fun _ => rfl)
  · cases computed
    exact .refl _

theorem ledgerKept_processWithdrawalRequest {electra : .pectra ≤ fork}
    {request : WithdrawalRequest}
    (computed : processWithdrawalRequest config state electra request = .ok after) :
    LedgerKept state after := by
  unfold processWithdrawalRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact ledgerKept_initiateValidatorExit (liftAccessor_ok.mp computed)
    | exact ledgerKept_requestPartialWithdrawal computed

theorem ledgerKept_queueExcessActiveBalance {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : queueExcessActiveBalance state electra index = .ok after) :
    LedgerKept state after := by
  simp only [queueExcessActiveBalance, bind_ok_iff] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, set, rfl⟩ := computed
    obtain ⟨_, rfl⟩ := setBalance_ok set
    exact .of_eq fun _ => rfl
  · cases computed
    exact .refl _

theorem ledgerKept_switchToCompoundingValidator {electra : .pectra ≤ fork}
    {index : ValidatorIndex}
    (computed : switchToCompoundingValidator state electra index = .ok after) :
    LedgerKept state after := by
  simp only [switchToCompoundingValidator, bind_ok_iff] at computed
  obtain ⟨_, _, _, set, queued⟩ := computed
  exact (LedgerKept.setValidator set).trans
    (ledgerKept_queueExcessActiveBalance queued)

theorem ledgerKept_queueConsolidation {electra : .pectra ≤ fork} {sourcePosition : Nat}
    {source : Validator} {targetIndex : ValidatorIndex}
    (computed :
      queueConsolidation config state electra sourcePosition source targetIndex = .ok after) :
    LedgerKept state after := by
  simp only [queueConsolidation, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    pure, Except.pure] at computed
  obtain ⟨⟨_, _⟩, churned, _, _, _, set, _, _, computed⟩ := computed
  simp only [Except.ok.injEq] at computed
  subst computed
  exact (ledgerKept_computeConsolidationEpochAndUpdateChurn churned).trans <|
    (LedgerKept.setValidator set).trans (.of_eq fun _ => rfl)

theorem ledgerKept_processConsolidationRequest {electra : .pectra ≤ fork}
    {request : ConsolidationRequest}
    (computed : processConsolidationRequest config state electra request = .ok after) :
    LedgerKept state after := by
  unfold processConsolidationRequest at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' split at computed
  all_goals first
    | (cases computed; done)
    | (cases computed; exact .refl _)
    | exact ledgerKept_switchToCompoundingValidator (liftAccessor_ok.mp computed)
    | exact ledgerKept_queueConsolidation computed

theorem ledgerKept_processExecutionRequests {body : BeaconBlockBody preset fork}
    {electra : .pectra ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionRequests config state body electra = .ok after) :
    LedgerKept state after := by
  simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at computed
  obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := computed
  exact (LedgerKept.foldlM (fun _ _ _ ok => ledgerKept_processDepositRequest ok)
      depositsOk).trans <|
    (LedgerKept.foldlM (fun _ _ _ ok => ledgerKept_processWithdrawalRequest ok)
      withdrawalsOk).trans <|
    LedgerKept.foldlM
      (fun _ _ _ ok => ledgerKept_processConsolidationRequest ok) consolidationsOk

theorem ledgerKept_processBlsToExecutionChange {signed : SignedBLSToExecutionChange}
    (computed : processBlsToExecutionChange config checks state signed = .ok after) :
    LedgerKept state after := by
  obtain ⟨_, _, _, _, _, set⟩ := processBlsToExecutionChange_ok computed
  exact .setValidator set

theorem ledgerKept_processExecutionPayload {body : BeaconBlockBody preset fork}
    {bellatrix : .bellatrix ≤ fork ∧ fork < .glamsterdam}
    (computed : processExecutionPayload config engine state body bellatrix = .ok after) :
    LedgerKept state after := by
  obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
  exact .of_eq fun _ => rfl

theorem ledgerKept_processSyncAggregate {altair : .altair ≤ fork}
    {aggregate : SyncAggregate preset}
    (computed : processSyncAggregate config checks state altair aggregate = .ok after) :
    LedgerKept state after := by
  unfold processSyncAggregate at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, folded⟩ := computed
  rw [← Array.foldlM_toList] at folded
  refine LedgerKept.foldlM (fun _ _ _ ok => ?_) folded
  unfold applySyncReward at ok
  split at ok
  · simp only [bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, _, _, paid⟩ := ok
    exact (LedgerKept.increaseBalance raised).trans (.increaseBalance paid)
  · exact .decreaseBalance (liftAccessor_ok.mp ok)

theorem ledgerKept_processJustificationAndFinalization
    (computed : processJustificationAndFinalization state = .ok after) :
    LedgerKept state after := by
  obtain same | ⟨_, _, _, weighed⟩ := processJustificationAndFinalization_ok computed
  · subst same
    exact .refl _
  · obtain ⟨_, _, _, rest⟩ := weighJustificationAndFinalization_checkpoints weighed
    exact .of_eq fun _ => by rw [← rest]; rfl

theorem ledgerKept_applyAllDeltas {deltas : Array Gwei × Array Gwei}
    (computed : applyAllDeltas state deltas = .ok after) : LedgerKept state after :=
  LedgerKept.foldlM (fun _ _ _ ok => by
    simp only [applyDeltas, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, raised, lowered⟩ := ok
    exact (LedgerKept.increaseBalance raised).trans (.decreaseBalance lowered)) computed

theorem ledgerKept_processRewardsAndPenalties
    (computed : processRewardsAndPenalties config state = .ok after) :
    LedgerKept state after := by
  unfold processRewardsAndPenalties at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, _, _, applied⟩ := computed
    exact LedgerKept.foldlM (fun _ _ _ ok => ledgerKept_applyAllDeltas ok) applied
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    exact ledgerKept_applyAllDeltas applied

theorem ledgerKept_updateRegistryEntry {index : Nat}
    (computed : updateRegistryEntry config state index = .ok after) :
    LedgerKept state after := by
  simp only [updateRegistryEntry, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, marked, markedOk, computed⟩ := computed
  have set := LedgerKept.setValidator markedOk
  split at computed
  · exact set.trans (ledgerKept_initiateValidatorExit (liftAccessor_ok.mp computed))
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ set

theorem ledgerKept_activateValidator {index : ValidatorIndex}
    (computed : activateValidator state index = .ok after) :
    LedgerKept state after := by
  simp only [activateValidator, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, set⟩ := computed
  exact .setValidator set

theorem ledgerKept_processRegistryUpdates
    (computed : processRegistryUpdates config state = .ok after) :
    LedgerKept state after := by
  unfold processRegistryUpdates at computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, computed⟩ := computed
    refine LedgerKept.foldlM (fun state _ _ ok => ?_) computed
    simp only [updateRegistryEntryElectra, bind_ok_iff, liftAccessor_ok] at ok
    obtain ⟨_, _, ok⟩ := ok
    split at ok
    · simp only [bind_ok_iff, liftAccessor_ok] at ok
      obtain ⟨_, _, set⟩ := ok
      exact .setValidator set
    split at ok
    · exact ledgerKept_initiateValidatorExit (liftAccessor_ok.mp ok)
    split at ok
    · rw [liftAccessor_ok] at ok
      exact .setValidator ok
    · simp only [pure, Except.pure, Except.ok.injEq] at ok
      exact ok ▸ .refl _
  simp only [bind_ok_iff] at computed
  obtain ⟨_, updatedOk, activated⟩ := computed
  exact (LedgerKept.foldlM (fun _ _ _ ok => ledgerKept_updateRegistryEntry ok)
    updatedOk).trans
    (LedgerKept.foldlM (fun _ _ _ ok => ledgerKept_activateValidator ok)
      activated)

theorem ledgerKept_processSlashings (computed : processSlashings state = .ok after) :
    LedgerKept state after := by
  unfold processSlashings at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, _, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, _, applied⟩ := computed
    refine LedgerKept.foldlM (fun _ _ _ ok => ?_) applied
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
  · refine LedgerKept.foldlM (fun _ _ _ ok => ?_) computed
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

theorem ledgerKept_processEth1DataReset {before : fork < .hegota}
    (computed : processEth1DataReset before state = .ok after) :
    LedgerKept state after := by
  simp only [processEth1DataReset, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .of_eq fun _ => rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem ledgerKept_processEffectiveBalanceUpdates
    (computed : processEffectiveBalanceUpdates state = .ok after) :
    LedgerKept state after := by
  unfold processEffectiveBalanceUpdates at computed
  refine LedgerKept.foldlM (fun _ _ _ ok => ?_) computed
  simp only [updateEffectiveBalance, bind_ok_iff, liftAccessor_ok] at ok
  obtain ⟨_, _, _, _, _, _, set⟩ := ok
  exact .setValidator set

theorem ledgerKept_processHistoricalRootsUpdate
    (computed : processHistoricalRootsUpdate state = .ok after) :
    LedgerKept state after := by
  unfold processHistoricalRootsUpdate at computed
  split at computed
  · cases computed
  simp only [bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftSsz_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_eq fun _ => rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem ledgerKept_processParticipationRecordUpdates
    (computed : processParticipationRecordUpdates state = .ok after) :
    LedgerKept state after := by
  unfold processParticipationRecordUpdates at computed
  split at computed
  · cases computed
  simp only [pure, Except.pure, Except.ok.injEq] at computed
  subst computed
  exact .of_eq fun _ => rfl

theorem ledgerKept_processInactivityUpdates {altair : .altair ≤ fork}
    (computed : processInactivityUpdates config state altair = .ok after) :
    LedgerKept state after := by
  unfold processInactivityUpdates at computed
  split at computed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, rfl⟩ := computed
    exact .of_eq fun _ => rfl

theorem ledgerKept_passPendingDeposits {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      LedgerKept state pass.1.state
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
      exact (ledgerKept_applyPendingDeposit credited).trans
        (ledgerKept_passPendingDeposits (deposits := rest) ‹_›)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact ledgerKept_passPendingDeposits (deposits := rest) ‹_›
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
    exact (ledgerKept_applyPendingDeposit credited).trans
      (ledgerKept_passPendingDeposits (deposits := rest) ‹_›)

theorem ledgerKept_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    LedgerKept state after := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals exact (ledgerKept_passPendingDeposits ‹_›).trans (.of_eq fun _ => rfl)

theorem ledgerKept_passPendingConsolidations {nextEpoch : Epoch} :
    ∀ {consolidations : List PendingConsolidation} {state : BeaconState preset fork}
      {result : BeaconState preset fork × Nat},
      passPendingConsolidations nextEpoch state consolidations = .ok result →
      LedgerKept state result.1
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
      exact ledgerKept_passPendingConsolidations (result := (passed, read)) passedOk
    split at computed
    · cases computed
      exact .refl _
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨_, _, lowered, loweredOk, raised, raisedOk, ⟨passed, read⟩, passedOk, computed⟩ :=
      computed
    cases computed
    exact (LedgerKept.decreaseBalance loweredOk).trans <|
      (LedgerKept.increaseBalance raisedOk).trans
        (ledgerKept_passPendingConsolidations (result := (passed, read)) passedOk)

theorem ledgerKept_processPendingBalances
    (computed : processPendingBalances config checks state = .ok after) :
    LedgerKept state after := by
  unfold processPendingBalances at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, deposited, consolidated⟩ := computed
    refine (ledgerKept_processPendingDeposits deposited).trans ?_
    unfold processPendingConsolidations at consolidated
    simp only [bind, Except.bind, pure, Except.pure] at consolidated
    repeat' (split at consolidated <;> try cases consolidated)
    all_goals exact (ledgerKept_passPendingConsolidations ‹_›).trans (.of_eq fun _ => rfl)
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

private theorem ledgerKept_epochEnd {altair : .altair ≤ fork}
    {rooted synced looked : BeaconState preset fork}
    (syncedOk : processSyncCommitteeUpdates (processParticipationFlagUpdates rooted altair) altair =
      .ok synced)
    (lookedOk : (if fulu : .fusaka ≤ fork then liftAccessor (processProposerLookahead synced fulu)
      else pure synced) = .ok looked)
    (windowed : (if gloas : .glamsterdam ≤ fork then liftAccessor (processPtcWindow looked gloas)
      else pure looked) = .ok after) : LedgerKept rooted after := by
  have syncedKept : LedgerKept rooted synced := by
    unfold processSyncCommitteeUpdates at syncedOk
    simp only [bind, Except.bind, pure, Except.pure] at syncedOk
    repeat' (split at syncedOk <;> try cases syncedOk)
    all_goals exact .of_eq fun _ => rfl
  have lookedKept : LedgerKept synced looked := by
    split at lookedOk
    · simp only [processProposerLookahead, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at lookedOk
      obtain ⟨_, _, _, _, rfl⟩ := lookedOk
      exact .of_eq fun _ => rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at lookedOk
      exact lookedOk ▸ .refl _
  have windowedKept : LedgerKept looked after := by
    split at windowed
    · simp only [processPtcWindow, liftAccessor_ok, bind_ok_iff, pure, Except.pure,
        Except.ok.injEq] at windowed
      obtain ⟨_, _, _, _, rfl⟩ := windowed
      exact .of_eq fun _ => rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at windowed
      exact windowed ▸ .refl _
  exact syncedKept.trans (lookedKept.trans windowedKept)


/-! ## Epochs and slots -/

/-- From Gloas, an epoch transition only moves the payments and queues those that reach a quorum.
-/
theorem ledgerOf_processEpoch (pp : PaymentPreset preset) (gloas : .glamsterdam ≤ fork)
    (computed : processEpoch config checks state = .ok after) :
    ∃ quorum, 0 < quorum ∧
      ledgerOf after gloas = (ledgerOf state gloas).epochStep state.slot quorum := by
  unfold processEpoch at computed
  split at computed
  swap
  · rename_i notAltair
    exact absurd (show Fork.altair ≤ fork from Nat.le_trans (by decide) gloas) notAltair
  unfold processEpochAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨justified, justifiedOk, scored, scoredOk, rewarded, rewardedOk, registered,
    registeredOk, slashed, slashedOk, reset, resetOk, pending, pendingOk, paid, paidOk, balanced,
    balancedOk, cleared, clearedOk, mixed, mixedOk, computed⟩ := computed
  have resetKept : LedgerKept slashed reset := by
    split at resetOk
    · exact ledgerKept_processEth1DataReset resetOk
    · simp only [pure, Except.pure, Except.ok.injEq] at resetOk
      exact resetOk ▸ .refl _
  have clearedKept : LedgerKept balanced cleared := by
    obtain ⟨_, _, _, _, rfl⟩ := processSlashingsReset_eq clearedOk
    exact .of_eq fun _ => rfl
  have mixedKept : LedgerKept cleared mixed := by
    obtain ⟨_, _, _, _, _, _, rfl⟩ := processRandaoMixesReset_eq mixedOk
    exact .of_eq fun _ => rfl
  have head : LedgerKept state pending :=
    (ledgerKept_processJustificationAndFinalization justifiedOk).trans <|
    (ledgerKept_processInactivityUpdates scoredOk).trans <|
    (ledgerKept_processRewardsAndPenalties rewardedOk).trans <|
    (ledgerKept_processRegistryUpdates registeredOk).trans <|
    (ledgerKept_processSlashings slashedOk).trans <|
    resetKept.trans (ledgerKept_processPendingBalances pendingOk)
  have middle : LedgerKept paid mixed :=
    (ledgerKept_processEffectiveBalanceUpdates balancedOk).trans <| clearedKept.trans mixedKept
  have tail : LedgerKept mixed after := by
    split at computed <;> simp only [bind_ok_iff] at computed <;>
      obtain ⟨rooted, rootedOk, synced, syncedOk, looked, lookedOk, windowed⟩ := computed
    · have rootedKept : LedgerKept mixed rooted := by
        unfold processHistoricalSummariesUpdate at rootedOk
        simp only [bind, Except.bind, pure, Except.pure] at rootedOk
        repeat' (split at rootedOk <;> try cases rootedOk)
        all_goals first
          | exact .refl _
          | exact .of_eq fun _ => rfl
      exact rootedKept.trans
        (ledgerKept_epochEnd syncedOk lookedOk (by rw [dite_eq_left gloas]; exact windowed))
    · exact (ledgerKept_processHistoricalRootsUpdate rootedOk).trans
        (ledgerKept_epochEnd syncedOk lookedOk (by rw [dite_eq_left gloas]; exact windowed))
  -- The payments step is the only one that changes the ledger.
  have paidOk' : processBuilderPendingPayments pending gloas = .ok paid := by
    simp only [gloas, ↓reduceDIte, liftAccessor_ok] at paidOk
    exact paidOk
  obtain ⟨quorum, quorumOk, queued, shifted⟩ := processBuilderPendingPayments_spec paidOk'
  refine ⟨quorum, getBuilderPaymentQuorumThreshold_pos pp quorumOk, ?_⟩
  rw [(middle.trans tail).same gloas]
  have pendingSame := head.same gloas
  have slotSame : pending.slot = state.slot := congrArg Ledger.slot pendingSame
  -- The payments step keeps every other part of the ledger.
  have rest : ledgerOf paid gloas = { ledgerOf pending gloas with
      payments := (paid.builderPendingPayments gloas).elements.toList
      queue := (paid.builderPendingWithdrawals gloas).data.toList } := by
    simp only [processBuilderPendingPayments, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at paidOk'
    obtain ⟨_, _, rfl⟩ := paidOk'
    rfl
  have samePayments : (pending.builderPendingPayments gloas).elements.toList =
      (state.builderPendingPayments gloas).elements.toList := congrArg Ledger.payments pendingSame
  have sameQueue : (pending.builderPendingWithdrawals gloas).data.toList =
      (state.builderPendingWithdrawals gloas).data.toList := congrArg Ledger.queue pendingSame
  rw [rest, queued, shifted, shiftPayments_toList, pendingSame, samePayments, sameQueue]
  rfl

/-- The caching of a slot keeps the ledger.

It may set the state root of the latest block header, but not its slot. -/
theorem ledgerKept_processSlot (computed : processSlot state = .ok after) :
    LedgerKept state after := by
  have header : after.latestBlockHeader.slot = state.latestBlockHeader.slot := by
    unfold processSlot at computed
    simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
    obtain ⟨_, _, _, _, _, _, _, _, computed⟩ := computed
    split at computed
    · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
      dsimp only
      split <;> rfl
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      dsimp only
      split <;> rfl
  obtain ⟨_, _, _, _, rfl⟩ := processSlot_ok computed
  exact .of_eq fun _ => by
    simp only [ledgerOf] at header ⊢
    rw [header]

/-- A later slot keeps the shape of the latest bid. -/
theorem Ledger.Shaped.later {ledger : Ledger preset fork} (shaped : ledger.Shaped)
    {other : Ledger preset fork} (bid : other.bid = ledger.bid)
    (header : other.headerSlot = ledger.headerSlot) (hash : other.blockHash = ledger.blockHash)
    (slot : ledger.slot ≤ other.slot) : other.Shaped := by
  unfold Ledger.Shaped Ledger.Pending at shaped ⊢
  rw [bid, header, hash]
  rcases shaped with zero | ⟨waits, same, early⟩
  · exact .inl zero
  · exact .inr ⟨waits, same, UInt64.le_trans early slot⟩

/-- A slot step keeps every ledger solvent and shaped.

Within an epoch the ledger only moves to the next slot.

At the end of an epoch it also moves the payments, as `Ledger.epochStep` says. -/
theorem solvent_advanceSlot (pp : PaymentPreset preset) (gloas : .glamsterdam ≤ fork)
    (computed : advanceSlot config checks state = .ok after)
    (solvent : (ledgerOf state gloas).Solvent) (shaped : (ledgerOf state gloas).Shaped) :
    (ledgerOf after gloas).Solvent ∧ (ledgerOf after gloas).Shaped := by
  have slots := pp.slots
  have nonzero : preset.SLOTS_PER_EPOCH ≠ 0 := by
    intro zero
    rw [zero] at slots
    simp at slots
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  replace sum : next.toNat = state.slot.toNat + 1 := by simpa using sum
  have cachedKept : LedgerKept state cached := ledgerKept_processSlot cachedOk
  have length : (ledgerOf state gloas).payments.length = 2 * preset.SLOTS_PER_EPOCH.toNat := by
    simp [ledgerOf]
  have later : state.slot ≤ next := by
    rw [UInt64.le_iff_toNat_le]
    omega
  unfold epochIfLast at epochedOk
  split at epochedOk
  · -- The last slot of an epoch runs the epoch transition.
    rename_i boundary
    have boundaryNat : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      have := congrArg UInt64.toNat boundary
      simpa [UInt64.toNat_mod] using this
    obtain ⟨quorum, positive, epochLedger⟩ := ledgerOf_processEpoch pp gloas epochedOk
    have result : ledgerOf { epoched with slot := next } gloas =
        (ledgerOf state gloas).epochStep next quorum := by
      have same := cachedKept.same gloas
      change { ledgerOf epoched gloas with slot := next } = _
      rw [epochLedger, same]
      rfl
    rw [result]
    refine ⟨solvent.epochStep pp shaped length sum boundaryNat positive, ?_⟩
    exact shaped.later rfl rfl rfl later
  · -- Any other slot keeps the epoch, and the ledger moves to the next slot.
    rename_i notBoundary
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have result : ledgerOf { cached with slot := next } gloas =
        { ledgerOf state gloas with slot := next } := by
      change { ledgerOf cached gloas with slot := next } = _
      rw [cachedKept.same gloas]
    have epochs : computeEpochAtSlot preset next =
        computeEpochAtSlot preset (ledgerOf state gloas).slot := by
      have notDvd : ¬ preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 := by
        intro dvd
        apply notBoundary
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_mod, sum, UInt64.toNat_zero]
        exact Nat.mod_eq_zero_of_dvd dvd
      unfold computeEpochAtSlot
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div, UInt64.toNat_div, sum]
      exact Nat.succ_div_of_not_dvd notDvd
    rw [result]
    exact ⟨solvent.tick epochs, shaped.later rfl rfl rfl later⟩


/-! ## Changes of the payments within a block -/

/-- A change of payments that keeps each payment or empties it owes no more. -/
theorem owedBy_map_le {index : BuilderIndex}
    {change : BuilderPendingPayment → BuilderPendingPayment}
    (cancels : ∀ payment, change payment = payment ∨ change payment = .empty) :
    ∀ payments : List BuilderPendingPayment,
      owedBy index ((payments.map change).map (·.withdrawal)) ≤
        owedBy index (payments.map (·.withdrawal))
  | [] => by simp [owedBy]
  | payment :: rest => by
    have ih := owedBy_map_le (index := index) cancels rest
    simp only [owedBy, List.map_cons, List.sum_cons] at ih ⊢
    rcases cancels payment with same | empty
    · rw [same]
      omega
    · rw [empty]
      simp only [BuilderPendingPayment.empty, UInt64.toNat_zero]
      split <;> omega

/-- A change that empties one payment owes at most what it owed less that payment. -/
theorem owedBy_map_add_le {index : BuilderIndex}
    {change : BuilderPendingPayment → BuilderPendingPayment}
    (cancels : ∀ payment, change payment = payment ∨ change payment = .empty)
    {emptied : BuilderPendingPayment} (gone : change emptied = .empty) :
    ∀ (payments : List BuilderPendingPayment) (position : Nat),
      payments[position]? = some emptied →
      owedBy index ((payments.map change).map (·.withdrawal)) + owedBy index [emptied.withdrawal] ≤
        owedBy index (payments.map (·.withdrawal))
  | [], _, found => by simp at found
  | payment :: rest, 0, found => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
    subst found
    have := owedBy_map_le (index := index) cancels rest
    simp only [owedBy, List.map_cons, List.sum_cons, gone, BuilderPendingPayment.empty,
      List.map_nil, List.sum_nil, UInt64.toNat_zero] at this ⊢
    split <;> split <;> omega
  | payment :: rest, position + 1, found => by
    simp only [List.getElem?_cons_succ] at found
    have ih := owedBy_map_add_le (index := index) cancels gone rest position found
    simp only [owedBy, List.map_cons, List.sum_cons] at ih ⊢
    rcases cancels payment with same | empty
    · rw [same]
      omega
    · rw [empty]
      simp only [BuilderPendingPayment.empty, UInt64.toNat_zero]
      split <;> omega

/-- Emptying some payments keeps a ledger solvent.

What each builder owes falls, and an emptied payment of the latest bid becomes its charge. -/
theorem Ledger.Solvent.cancel {ledger : Ledger preset fork} (solvent : ledger.Solvent)
    {change : BuilderPendingPayment → BuilderPendingPayment}
    (cancels : ∀ payment, change payment = payment ∨ change payment = .empty) :
    ({ ledger with payments := ledger.payments.map change } : Ledger preset fork).Solvent := by
  obtain ⟨covered, latent, idle, quiet⟩ := solvent
  have owedLe : ∀ index,
      ({ ledger with payments := ledger.payments.map change } : Ledger preset fork).owed index ≤
        ledger.owed index := by
    intro index
    have := owedBy_map_le (index := index) cancels ledger.payments
    unfold Ledger.owed
    dsimp only
    omega
  -- A payment of the latest bid that is not held now was emptied, or was never held.
  have charged : ∀ index, ({ ledger with payments := ledger.payments.map change } :
        Ledger preset fork).Latent index →
      ledger.Latent index ∨
        (ledger.bid.builderIndex = index ∧ ({ ledger with payments := ledger.payments.map change } :
          Ledger preset fork).owed index + ledger.bid.value.toNat ≤ ledger.owed index) := by
    rintro index ⟨waits, named, notHeld⟩
    by_cases held : ledger.Held
    · right
      obtain ⟨position, payment, located, found, payer, amount⟩ := held
      refine ⟨named, ?_⟩
      rcases cancels payment with same | gone
      · exact absurd ⟨position, payment, located, by simp [found, same], payer, amount⟩ notHeld
      · have := owedBy_map_add_le (index := index) cancels gone ledger.payments position.toNat found
        rw [owedBy_single (payer.trans named), amount] at this
        unfold Ledger.owed
        dsimp only
        omega
    · exact .inl ⟨waits, named, held⟩
  refine ⟨fun index builder found => Nat.le_trans (owedLe index) (covered index builder found),
    fun index builder found later => ?_, fun index set => ?_, ?_⟩
  · rcases charged index later with old | ⟨_, fell⟩
    · have := latent index builder found old
      have := owedLe index
      show _ + ledger.bid.value.toNat ≤ _
      omega
    · exact Nat.le_trans fell (covered index builder found)
  · obtain ⟨zero, charge⟩ := idle index set
    refine ⟨Nat.le_zero.mp (zero ▸ owedLe index), fun later => ?_⟩
    rcases charged index later with old | ⟨_, fell⟩
    · exact charge old
    · rw [zero] at fell
      exact UInt64.toNat_inj.mp (by simp only [UInt64.toNat_zero]; omega)
  · intro waits valued position payment located found
    simp only [List.getElem?_map, Option.map_eq_some_iff] at found
    obtain ⟨old, oldFound, rfl⟩ := found
    rcases cancels old with same | gone
    · rw [same]
      exact quiet waits valued position old located oldFound
    · rw [gone]
      rfl

/-- A new weight for a payment other than that of the latest bid keeps a ledger solvent. -/
theorem Ledger.Solvent.reweigh {ledger : Ledger preset fork} (solvent : ledger.Solvent)
    {position : Nat} {payment : BuilderPendingPayment}
    (found : ledger.payments[position]? = some payment) (weight : Gwei)
    (other : ∀ spot, ledger.position ledger.bid.slot = some spot → spot.toNat ≠ position) :
    ({ ledger with payments := ledger.payments.set position { payment with weight } } :
      Ledger preset fork).Solvent := by
  -- The withdrawals of the payments do not change.
  have withdrawals : (ledger.payments.set position { payment with weight }).map (·.withdrawal) =
      ledger.payments.map (·.withdrawal) := by
    rw [List.map_set]
    apply List.ext_getElem?
    intro k
    rw [List.getElem?_set]
    split
    · rename_i same
      subst same
      have inside : position < ledger.payments.length := by
        by_contra outside
        rw [List.getElem?_eq_none (Nat.le_of_not_lt outside)] at found
        cases found
      rw [List.getElem?_eq_getElem inside, Option.some.injEq] at found
      simp [inside, found]
    · rfl
  have owed : ∀ index,
      ({ ledger with payments := ledger.payments.set position { payment with weight } } :
        Ledger preset fork).owed index = ledger.owed index := by
    intro index
    simp only [Ledger.owed, withdrawals]
  have read : ∀ spot, ledger.position ledger.bid.slot = some spot →
      (ledger.payments.set position { payment with weight })[spot.toNat]? =
        ledger.payments[spot.toNat]? := by
    intro spot located
    rw [List.getElem?_set_ne (Ne.symm (other spot located))]
  have held : ({ ledger with payments := ledger.payments.set position { payment with weight } } :
      Ledger preset fork).Held ↔ ledger.Held := by
    constructor
    · rintro ⟨spot, held, located, inside, rest⟩
      exact ⟨spot, held, located, (read spot located) ▸ inside, rest⟩
    · rintro ⟨spot, held, located, inside, rest⟩
      exact ⟨spot, held, located, (read spot located).trans inside, rest⟩
  have latents : ∀ index,
      ({ ledger with payments := ledger.payments.set position { payment with weight } } :
        Ledger preset fork).Latent index ↔ ledger.Latent index :=
    fun index => by simp only [Ledger.Latent, Ledger.Pending, held]
  obtain ⟨covered, latent, idle, quiet⟩ := solvent
  refine ⟨fun index builder found => (owed index) ▸ covered index builder found,
    fun index builder found later => (owed index) ▸ latent index builder found
      ((latents index).mp later),
    fun index set => (owed index) ▸ ⟨(idle index set).1,
      fun later => (idle index set).2 ((latents index).mp later)⟩,
    fun waits valued spot held located inside => ?_⟩
  exact quiet waits valued spot held located ((read spot located) ▸ inside)



/-! ## The operations of a block -/

/-- A later state of the same fork whose ledger differs at most in its payments.

From a solvent ledger whose latest bid is of the current slot, the later ledger is solvent. -/
structure OpsKept (state after : BeaconState preset fork) : Prop where
  frame : ∀ gloas, { ledgerOf after gloas with payments := [] } =
    { ledgerOf state gloas with payments := [] }
  solvent : ∀ gloas, (state.latestExecutionPayloadBid gloas).slot = state.slot →
    (ledgerOf state gloas).Solvent → (ledgerOf after gloas).Solvent

namespace OpsKept

theorem refl (state : BeaconState preset fork) : OpsKept state state :=
  ⟨fun _ => rfl, fun _ _ => id⟩

theorem trans {first second third : BeaconState preset fork}
    (one : OpsKept first second) (two : OpsKept second third) : OpsKept first third where
  frame gloas := (two.frame gloas).trans (one.frame gloas)
  solvent gloas current solvent := by
    have bid := congrArg Ledger.bid (one.frame gloas)
    have slot := congrArg Ledger.slot (one.frame gloas)
    simp only [ledgerOf] at bid slot
    exact two.solvent gloas (by rw [bid, slot]; exact current) (one.solvent gloas current solvent)

theorem of_ledger (kept : LedgerKept state after) : OpsKept state after :=
  ⟨fun gloas => by rw [kept.same gloas], fun gloas _ solvent => (kept.same gloas) ▸ solvent⟩

end OpsKept

/-- Cancelling the payments of a slashed proposer empties them. -/
theorem opsKept_cancelProposerPayments (gloas : .glamsterdam ≤ fork) (proposer : ValidatorIndex) :
    OpsKept state (cancelProposerPayments state gloas proposer) := by
  refine ⟨fun _ => rfl, fun gloas' _ solvent => ?_⟩
  obtain rfl : gloas = gloas' := rfl
  have cancels : ∀ payment : BuilderPendingPayment,
      (if payment.proposerIndex = proposer then .empty else payment) = payment ∨
        (if payment.proposerIndex = proposer then .empty else payment) = .empty := by
    intro payment
    split
    · exact .inr rfl
    · exact .inl rfl
  have cancelled := solvent.cancel cancels
  simpa [ledgerOf, cancelProposerPayments, Vector.toList_map] using cancelled

theorem opsKept_slashValidator {slashedIndex : ValidatorIndex}
    {whistleblowerIndex : Option ValidatorIndex}
    (computed : slashValidator config state slashedIndex whistleblowerIndex = .ok after) :
    OpsKept state after := by
  simp only [slashValidator, bind_ok_iff, liftArith, mapError_ok_iff] at computed
  obtain ⟨exited, exitedOk, validator, found, delay, _, marked, markedOk, _, _, _, _, _, _,
    lowered, loweredOk,
    proposer, _, _, _, raised, raisedOk, last, lastOk, done⟩ := computed
  have final : OpsKept last after := by
    simp only [pure, Except.pure, Except.ok.injEq] at done
    subst done
    split
    · exact opsKept_cancelProposerPayments _ _
    · exact .refl _
  exact (OpsKept.of_ledger <| (ledgerKept_initiateValidatorExit exitedOk).trans <|
    ((LedgerKept.setValidator markedOk).trans (by exact .of_eq fun _ => rfl)).trans <|
    (LedgerKept.decreaseBalance loweredOk).trans <|
    (LedgerKept.increaseBalance raisedOk).trans (LedgerKept.increaseBalance lastOk)).trans final

theorem opsKept_processProposerSlashing {slashing : ProposerSlashing}
    (computed : processProposerSlashing config checks state slashing = .ok after) :
    OpsKept state after := by
  simp only [processProposerSlashing, bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, slashed⟩ := computed
  exact opsKept_slashValidator slashed

theorem opsKept_slashIfSlashable {step next : BeaconState preset fork × Bool}
    {index : ValidatorIndex} (computed : slashIfSlashable config step index = .ok next) :
    OpsKept step.1 next.1 := by
  obtain ⟨state, slashedAny⟩ := step
  simp only [slashIfSlashable, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, computed⟩ := computed
  split at computed
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, slashed, rfl⟩ := computed
    exact opsKept_slashValidator slashed
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    exact computed ▸ .refl _

theorem opsKept_processAttesterSlashing {slashing : AttesterSlashing preset fork}
    (computed : processAttesterSlashing config checks state slashing = .ok after) :
    OpsKept state after := by
  simp only [processAttesterSlashing, bind_ok_iff, ensure_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, folded, _, _, rfl⟩ := computed
  exact foldlM_ok_invariant (fun step => OpsKept state step.1)
    (fun _ _ _ before ok => before.trans (opsKept_slashIfSlashable ok))
    (show OpsKept state (state, false).1 from .refl state) folded

theorem OpsKept.foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → OpsKept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : OpsKept state after :=
  foldlM_ok_invariant (OpsKept state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

/-- An attestation adds weight only to the payment of the block of its own slot.

That slot is before the current slot, so the payment is not the one of the latest bid. -/
theorem opsKept_processAttestation (pp : PaymentPreset preset)
    {attestation : Attestation preset fork} {parentSlot : Slot}
    (computed : processAttestation config checks state parentSlot attestation = .ok after) :
    OpsKept state after := by
  unfold processAttestation at computed
  split at computed
  swap
  · -- Before Altair there are no builders.
    rename_i notAltair
    simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at computed
    refine ⟨fun gloas => absurd (Nat.le_trans (by decide) gloas) notAltair,
      fun gloas => absurd (Nat.le_trans (by decide) gloas) notAltair⟩
  rename_i altair
  unfold processAttestationAltair at computed
  simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff] at computed
  obtain ⟨_, recent, _, slotEpoch, earliest, ⟨_, sum⟩, _, early, rest⟩ := computed
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, raised, raisedOk, final⟩ :=
    rest
  have flagged : ∀ (current : Bool) (participation : EpochParticipation preset fork),
      LedgerKept state (setEpochParticipation state current participation) := by
    intro current participation
    unfold setEpochParticipation
    split <;> exact .of_eq fun _ => rfl
  have head : LedgerKept state raised := (flagged _ _).trans (LedgerKept.increaseBalance raisedOk)
  split at final
  swap
  · simp only [pure, Except.pure, Except.ok.injEq] at final
    subst final
    exact .of_ledger head
  rename_i gloas
  refine (OpsKept.of_ledger head).trans ⟨fun gloas' => ?_, fun gloas' current solvent => ?_⟩
  · obtain rfl : gloas = gloas' := rfl
    rw [recordPaymentWeight_eq final]
    rfl
  obtain rfl : gloas = gloas' := rfl
  -- The weight changes only at the position of the attestation.
  unfold recordPaymentWeight at final
  dsimp only at final
  split at final
  swap
  · cases final
  rename_i inside
  obtain ⟨_, _, final⟩ := bind_ok_iff.mp final
  obtain ⟨weight, _, final⟩ := bind_ok_iff.mp final
  simp only [pure, Except.pure, Except.ok.injEq] at final
  subst final
  have same := head.same gloas
  have slot : raised.slot = state.slot := congrArg Ledger.slot same
  set position := attestationPaymentPosition preset
    (attestation.data.target.epoch == getCurrentEpoch state) attestation.data.slot
  have found : (ledgerOf raised gloas).payments[position]? =
      some (raised.builderPendingPayments gloas)[position] := by
    simp only [ledgerOf, Vector.getElem?_toList]
    rw [Vector.getElem?_eq_getElem inside]
    rfl
  set reweighed : BuilderPendingPayment :=
    { (raised.builderPendingPayments gloas)[position] with weight }
  have result : ledgerOf { raised with builderPendingPayments := fun _ =>
        (raised.builderPendingPayments gloas).set position reweighed inside } gloas =
      { ledgerOf raised gloas with
        payments := (ledgerOf raised gloas).payments.set position reweighed } := by
    simp only [ledgerOf, RootedVector.elements_set, Vector.toList_set]
  rw [result]
  refine solvent.reweigh found weight fun spot located => ?_
  -- The latest bid is of the current slot, so its payment is in the second half.
  have slots := pp.slots
  have delay := pp.delay
  have small := pp.small
  have at_ := (ledgerOf raised gloas).position_toNat pp (ledgerOf raised gloas).bid.slot
  rw [located] at at_
  have bidSlot : (ledgerOf raised gloas).bid.slot = (ledgerOf raised gloas).slot := by
    simp only [ledgerOf]
    exact current
  rw [bidSlot] at at_
  simp only [↓reduceIte, Option.map_some, Option.some.injEq] at at_
  rw [at_]
  have nonzero : preset.SLOTS_PER_EPOCH ≠ 0 := by
    intro zero
    rw [zero] at slots
    simp at slots
  have rest := toNat_mod_lt (i := attestation.data.slot) nonzero
  simp only [position, attestationPaymentPosition]
  have early' : attestation.data.slot.toNat + 1 ≤ state.slot.toNat := by
    have := UInt64.le_iff_toNat_le.mp early
    omega
  split
  · -- A vote of the current epoch is for an earlier slot of it.
    rename_i isCurrent
    have epochs : attestation.data.slot.toNat / preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat := by
      simp only [beq_iff_eq] at isCurrent
      have := congrArg UInt64.toNat (slotEpoch.symm.trans isCurrent)
      simpa [computeEpochAtSlot, getCurrentEpoch, UInt64.toNat_div] using this
    have sum : (preset.SLOTS_PER_EPOCH + attestation.data.slot % preset.SLOTS_PER_EPOCH).toNat =
        preset.SLOTS_PER_EPOCH.toNat +
          attestation.data.slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by
      rw [UInt64.toNat_add, UInt64.toNat_mod, ← UInt64.toNat_mod]
      exact Nat.mod_eq_of_lt (by rw [UInt64.toNat_mod] at rest ⊢; omega)
    rw [sum]
    simp only [ledgerOf, slot]
    intro equal
    have residues : attestation.data.slot.toNat % preset.SLOTS_PER_EPOCH.toNat =
        state.slot.toNat % preset.SLOTS_PER_EPOCH.toNat := by omega
    have := Nat.div_add_mod attestation.data.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    have := Nat.div_add_mod state.slot.toNat preset.SLOTS_PER_EPOCH.toNat
    rw [epochs, residues] at *
    omega
  · -- A vote of the previous epoch has its payment in the first half.
    simp only [UInt64.zero_add, UInt64.toNat_mod]
    have := Nat.mod_lt attestation.data.slot.toNat (show 0 < preset.SLOTS_PER_EPOCH.toNat by omega)
    omega


/-- Before Gloas there are no builders, so every step keeps them. -/
theorem OpsKept.of_before (early : fork < .glamsterdam) : OpsKept state after :=
  ⟨fun gloas => absurd gloas (Nat.not_le_of_lt early),
    fun gloas => absurd gloas (Nat.not_le_of_lt early)⟩

theorem opsKept_processOperations (pp : PaymentPreset preset) {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    OpsKept state after := by
  unfold processOperations at computed
  split at computed
  · unfold processOperationsGloas at computed
    simp only [bind_ok_iff, ← Array.foldlM_toList] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, proposersOk, _, attestersOk, _,
      attestedOk, _, exitsOk, _, changesOk, paid⟩ := computed
    exact (OpsKept.foldlM
        (fun _ _ _ ok => opsKept_processProposerSlashing ok) proposersOk).trans <|
      (OpsKept.foldlM
        (fun _ _ _ ok => opsKept_processAttesterSlashing ok) attestersOk).trans <|
      (OpsKept.foldlM (fun _ _ _ ok => opsKept_processAttestation pp ok) attestedOk).trans <|
      (OpsKept.foldlM (fun _ _ _ ok => .of_ledger (ledgerKept_processVoluntaryExit ok))
        exitsOk).trans <|
      (OpsKept.foldlM
        (fun _ _ _ ok => .of_ledger (ledgerKept_processBlsToExecutionChange ok)) changesOk).trans <|
      OpsKept.foldlM (fun _ _ _ ok => by
        rw [processPayloadAttestation_eq ok]
        exact .refl _) paid
  · exact .of_before (Nat.lt_of_not_le ‹_›)


/-! ## The bid of a block -/

/-- A bid passes the checks of its builder only in two cases.

It has no value, or its builder is active and covers it. -/
theorem checkBidBuilder_cases {gloas : .glamsterdam ≤ fork}
    {signed : SignedExecutionPayloadBid preset fork} {result : Unit}
    (computed : checkBidBuilder config checks state gloas signed = .ok result) :
    signed.message.value = 0 ∨
      ∃ builder, getBuilder state gloas signed.message.builderIndex = .ok builder ∧
        builder.withdrawableEpoch = FAR_FUTURE_EPOCH ∧
        ∃ pending, getPendingBalanceToWithdrawForBuilder state gloas
            signed.message.builderIndex = .ok pending ∧
          preset.MIN_DEPOSIT_AMOUNT.toNat + pending.toNat + signed.message.value.toNat ≤
            builder.balance.toNat := by
  unfold checkBidBuilder at computed
  dsimp only at computed
  split at computed
  · simp only [ensure_ok_iff] at computed
    exact .inl computed.1
  · simp only [bind_ok_iff, ensure_ok_iff, liftAccessor_ok] at computed
    obtain ⟨active, activeOk, _, activeTrue, _, _, _, _, covered, coveredOk, _, coveredTrue, _⟩ :=
      computed
    subst activeTrue coveredTrue
    obtain ⟨builder, pending, found, owed, enough⟩ :=
      canBuilderCoverBid_eq_ok_true_iff.mp coveredOk
    right
    refine ⟨builder, found, ?_, pending, owed, enough⟩
    simp only [isActiveBuilder, found, bind, Except.bind, pure, Except.pure, Except.ok.injEq,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at activeOk
    exact activeOk.2

/-- A new bid of no value keeps a ledger solvent: it may charge no one. -/
theorem Ledger.Solvent.freeBid {ledger : Ledger preset fork} (solvent : ledger.Solvent)
    (bid : ExecutionPayloadBid preset fork) (zero : bid.value = 0) :
    ({ ledger with bid } : Ledger preset fork).Solvent := by
  obtain ⟨covered, _, idle, _⟩ := solvent
  refine ⟨covered, fun index builder found _ => ?_, fun index set => ⟨(idle index set).1,
    fun _ => zero⟩, fun _ valued => absurd valued (by simp [zero])⟩
  have := covered index builder found
  show ledger.owed index + bid.value.toNat ≤ _
  rw [zero]
  simpa using this

/-- A new bid of a value keeps a ledger solvent, once its payment waits at its position.

Its builder has not started to exit, and can pay what it owes and the bid. -/
theorem Ledger.Solvent.valuedBid {ledger : Ledger preset fork} (solvent : ledger.Solvent)
    (bid : ExecutionPayloadBid preset fork) {position : UInt64} {payment : BuilderPendingPayment}
    (inside : position.toNat < ledger.payments.length)
    (located : ({ ledger with bid } : Ledger preset fork).position bid.slot = some position)
    (named : payment.withdrawal.builderIndex = bid.builderIndex)
    (amount : payment.withdrawal.amount = bid.value) (weight : payment.weight = 0)
    {builder : Builder} (found : ledger.builders[bid.builderIndex.toNat]? = some builder)
    (active : builder.withdrawableEpoch = FAR_FUTURE_EPOCH)
    (enough : ledger.owed bid.builderIndex + bid.value.toNat ≤ builder.balance.toNat) :
    ({ ledger with bid, payments := ledger.payments.set position.toNat payment } :
      Ledger preset fork).Solvent := by
  set after : Ledger preset fork :=
    { ledger with bid, payments := ledger.payments.set position.toNat payment }
  have held : after.Held := by
    refine ⟨position, payment, located, ?_, named, amount⟩
    simp only [after, List.getElem?_set_self inside]
  have quietLatent : ∀ index, ¬ after.Latent index := fun _ ⟨_, _, notHeld⟩ => notHeld held
  -- What a builder owes changes by the payment replaced and the new one.
  have owed : ∀ index,
      after.owed index + owedBy index [ledger.payments[position.toNat].withdrawal] =
      ledger.owed index + owedBy index [payment.withdrawal] := by
    intro index
    have := owedBy_set (index := index) (withdrawals := ledger.payments.map (·.withdrawal))
      (k := position.toNat) (by simpa using inside) payment.withdrawal
    simp only [List.getElem_map] at this
    simp only [after, Ledger.owed, List.map_set]
    omega
  have newOwed : ∀ index, owedBy index [payment.withdrawal] =
      if bid.builderIndex = index then bid.value.toNat else 0 := by
    intro index
    simp [owedBy, named, amount]
  obtain ⟨covered, _, idle, _⟩ := solvent
  refine ⟨fun index other found' => ?_, fun index _ _ later => absurd later (quietLatent index),
    fun index set => ⟨?_, fun later => absurd later (quietLatent index)⟩, ?_⟩
  · have step := owed index
    rw [newOwed] at step
    split at step
    · rename_i same
      subst same
      rw [found] at found'
      cases found'
      omega
    · have := covered index other found'
      omega
  · have step := owed index
    rw [newOwed] at step
    split at step
    · rename_i same
      subst same
      exact absurd active (set builder found)
    · have := (idle index set).1
      omega
  · intro _ _ spot paid spotAt spotFound
    change ({ ledger with bid } : Ledger preset fork).position bid.slot = some spot at spotAt
    rw [located, Option.some.injEq] at spotAt
    subst spotAt
    simp only [after, List.getElem?_set_self inside, Option.some.injEq] at spotFound
    subst spotFound
    exact weight

/-- The bid of a block keeps the ledger solvent, and leaves it shaped.

A bid of a value records its payment at the position of the current slot.

Its builder has not started to exit, and covers it: it owes at most its balance less the bid. -/
theorem solvent_processExecutionPayloadBid (pp : PaymentPreset preset)
    (gloas : .glamsterdam ≤ fork) {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after)
    (solvent : (ledgerOf state gloas).Solvent)
    (header : state.latestBlockHeader.slot = state.slot) :
    (ledgerOf after gloas).Solvent ∧ (ledgerOf after gloas).Shaped ∧
      (after.latestExecutionPayloadBid gloas).slot = after.slot ∧ after.slot = state.slot ∧
      after.latestBlockHeader = state.latestBlockHeader := by
  have slots := pp.slots
  have small := pp.small
  simp only [processExecutionPayloadBid, checkExecutionPayloadBid, bind_ok_iff, ensure_ok_iff,
    liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, ⟨_, builderOk, rest⟩, recorded, recordedOk, rfl⟩ := computed
  obtain ⟨_, _, _, slotEq, _, _, _, parentEq, _, differ, -⟩ := rest
  have waits : state.latestBlockHash gloas ≠ signed.message.blockHash := by
    rw [← parentEq]
    exact differ.symm
  unfold recordBidPayment at recordedOk
  split at recordedOk
  · rename_i valued
    simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at recordedOk
    obtain ⟨proposer, _, position, positionOk, rfl⟩ := recordedOk
    unfold bidPaymentPosition at positionOk
    split at positionOk
    · cases positionOk
    rename_i nonzero
    simp only [pure, Except.pure, Except.ok.injEq] at positionOk
    subst positionOk
    rcases checkBidBuilder_cases builderOk with
      zero | ⟨builder, found, active, pending, owed, enough⟩
    · rw [zero] at valued
      exact absurd valued (by decide)
    have rest := toNat_mod_lt (i := signed.message.slot) nonzero
    set spot : UInt64 := preset.SLOTS_PER_EPOCH + signed.message.slot % preset.SLOTS_PER_EPOCH
    have spotNat : spot.toNat =
        preset.SLOTS_PER_EPOCH.toNat + (signed.message.slot % preset.SLOTS_PER_EPOCH).toNat
        := by
      rw [UInt64.toNat_add]
      exact Nat.mod_eq_of_lt (by omega)
    have located : ({ ledgerOf state gloas with bid := signed.message } :
        Ledger preset fork).position signed.message.slot =
        some spot := by
      simp only [Ledger.position, Ledger.currentEpoch, ledgerOf]
      rw [slotEq]
      simp [spot, slotEq]
    have foundAt :
        (ledgerOf state gloas).builders[signed.message.builderIndex.toNat]? = some builder := by
      unfold getBuilder at found
      simp only [ledgerOf]
      split at found
      · rename_i read
        cases found
        exact read
      · cases found
    have owedNat := (getPendingBalanceToWithdrawForBuilder_ok_iff.mp owed).2
    have solventAfter := solvent.valuedBid signed.message (position := spot)
      (payment := bidPayment signed.message proposer) (by simp [ledgerOf]; omega) located
      rfl rfl rfl foundAt active (by rw [← pendingBuilderTotal_eq_owed]; omega)
    refine ⟨?_, .inr ⟨waits, by simp only [ledgerOf]; rw [slotEq, header],
      by simp only [ledgerOf]; rw [slotEq]; exact UInt64.le_refl _⟩,
      slotEq, rfl, rfl⟩
    unfold ledgerOf at solventAfter ⊢
    simpa [spotNat, RootedVector.elements_set, Vector.toList_set] using solventAfter
  · rename_i notValued
    simp only [pure, Except.pure, Except.ok.injEq] at recordedOk
    subst recordedOk
    have zero : signed.message.value = 0 := by
      rw [UInt64.lt_iff_toNat_lt] at notValued
      exact UInt64.toNat_inj.mp (by simp at notValued ⊢; omega)
    exact ⟨solvent.freeBid signed.message zero, .inl zero, slotEq, rfl, rfl⟩


/-! ## The parent payload -/

/-- Every builder can pay what it owes, and a builder that has started to exit owes nothing.

So can every index past the registry. -/
structure Ledger.Covered (ledger : Ledger preset fork) : Prop where
  covered : ∀ (index : BuilderIndex) (builder : Builder),
    ledger.builders[index.toNat]? = some builder → ledger.owed index ≤ builder.balance.toNat
  idle : ∀ index : BuilderIndex,
    (∀ builder, ledger.builders[index.toNat]? = some builder →
      builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH) → ledger.owed index = 0

theorem Ledger.Solvent.covers {ledger : Ledger preset fork} (solvent : ledger.Solvent) :
    ledger.Covered :=
  ⟨solvent.covered, fun index set => (solvent.idle index set).1⟩

/-- Once the payload of the latest bid is applied, a covered ledger is solvent. -/
theorem Ledger.Covered.solvent {ledger : Ledger preset fork} (covered : ledger.Covered)
    (applied : ¬ ledger.Pending) : ledger.Solvent :=
  ⟨covered.covered, fun _ _ _ later => absurd later.1 applied,
    fun index set => ⟨covered.idle index set, fun later => absurd later.1 applied⟩,
    fun waits => absurd waits applied⟩

/-- A builder replaced at an index keeps a ledger covered, if it covers what that index owes. -/
theorem Ledger.Covered.set {ledger : Ledger preset fork} (covered : ledger.Covered)
    {position : Nat} (inside : position < ledger.builders.size) {builder : Builder}
    (enough : ∀ index : BuilderIndex, index.toNat = position →
      ledger.owed index ≤ builder.balance.toNat ∧
        (builder.withdrawableEpoch ≠ FAR_FUTURE_EPOCH → ledger.owed index = 0)) :
    ({ ledger with builders := ledger.builders.set position builder inside } :
      Ledger preset fork).Covered := by
  refine ⟨fun index other found => ?_, fun index set => ?_⟩
  · change (ledger.builders.set position builder inside)[index.toNat]? = some other at found
    rw [Array.getElem?_set] at found
    split at found
    · rename_i same
      cases found
      exact (enough index same.symm).1
    · exact covered.covered index other found
  · show ledger.owed index = 0
    by_cases same : index.toNat = position
    · apply (enough index same).2
      apply set
      change (ledger.builders.set position builder inside)[index.toNat]? = _
      rw [Array.getElem?_set, ite_eq_left same.symm]
    · refine covered.idle index fun other found => set other ?_
      change (ledger.builders.set position builder inside)[index.toNat]? = _
      rw [Array.getElem?_set, ite_eq_right (Ne.symm same)]
      exact found

/-- A builder added at the end of the registry keeps a ledger covered.

No index past the registry owes anything. -/
theorem Ledger.Covered.push {ledger : Ledger preset fork} (covered : ledger.Covered)
    (builder : Builder) :
    ({ ledger with builders := ledger.builders.push builder } : Ledger preset fork).Covered := by
  have outside :
      ∀ index : BuilderIndex, index.toNat = ledger.builders.size → ledger.owed index = 0 :=
    fun index same => covered.idle index fun other found => by
      rw [Array.getElem?_eq_none (by omega)] at found
      cases found
  refine ⟨fun index other found => ?_, fun index set => ?_⟩
  · change (ledger.builders.push builder)[index.toNat]? = some other at found
    rw [Array.getElem?_push] at found
    split at found
    · rename_i same
      show ledger.owed index ≤ _
      rw [outside index same]
      exact Nat.zero_le _
    · exact covered.covered index other found
  · show ledger.owed index = 0
    by_cases same : index.toNat = ledger.builders.size
    · exact outside index same
    · refine covered.idle index fun other found => set other ?_
      change (ledger.builders.push builder)[index.toNat]? = _
      rw [Array.getElem?_push, ite_eq_right same]
      exact found

/-- A later state of the same fork whose ledger differs at most in its builders.

From a covered ledger, the later ledger is covered. -/
structure ReqKept (state after : BeaconState preset fork) : Prop where
  frame : ∀ gloas, { ledgerOf after gloas with builders := #[] } =
    { ledgerOf state gloas with builders := #[] }
  covered : ∀ gloas, (ledgerOf state gloas).Covered → (ledgerOf after gloas).Covered

namespace ReqKept

theorem refl (state : BeaconState preset fork) : ReqKept state state :=
  ⟨fun _ => rfl, fun _ => id⟩

theorem trans {first second third : BeaconState preset fork}
    (one : ReqKept first second) (two : ReqKept second third) : ReqKept first third :=
  ⟨fun gloas => (two.frame gloas).trans (one.frame gloas),
    fun gloas => two.covered gloas ∘ one.covered gloas⟩

theorem of_ledger (kept : LedgerKept state after) : ReqKept state after :=
  ⟨fun gloas => by rw [kept.same gloas], fun gloas covered => (kept.same gloas) ▸ covered⟩

theorem foldlM {α ε : Type} {step : BeaconState preset fork → α → Except ε _}
    (kept : ∀ s x s', step s x = .ok s' → ReqKept s s') {items : List α}
    (computed : items.foldlM step state = .ok after) : ReqKept state after :=
  foldlM_ok_invariant (ReqKept state)
    (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl state) computed

end ReqKept

/-- A builder deposit adds to the balance of a builder, or registers a new one.

A deposit to a builder that has exited may move its withdrawable epoch, but it still owes nothing.

A new builder takes the index of a withdrawable builder, which owes nothing, or a new index. -/
theorem reqKept_processBuilderDepositRequest (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {gloas : .glamsterdam ≤ fork} {request : BuilderDepositRequest}
    (computed : processBuilderDepositRequest config checks state gloas request = .ok after) :
    ReqKept state after := by
  unfold processBuilderDepositRequest at computed
  split at computed
  · cases computed
    exact .refl _
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨valid, _, computed⟩ := computed
    split at computed
    · cases computed
      refine ⟨fun gloas' => ?_, fun gloas' covered => ?_⟩
      all_goals obtain rfl : gloas = gloas' := rfl
      · simp only [addBuilderToRegistry]
        split <;> rfl
      simp only [addBuilderToRegistry]
      split
      · rename_i inside
        have reusable := isReusableBuilder_of_getIndexForNewBuilder_lt inside
        simp only [isReusableBuilder, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at reusable
        have small := getCurrentEpoch_lt_far slots state
        refine covered.set (position := getIndexForNewBuilder state gloas) inside
          fun index same => ?_
        -- The builder at that index is withdrawable, so it owes nothing.
        have zero : (ledgerOf state gloas).owed index = 0 := by
          refine covered.idle index fun old found far => ?_
          simp only [ledgerOf, same] at found
          rw [Array.getElem?_eq_getElem inside, Option.some.injEq] at found
          subst found
          have le := UInt64.le_iff_toNat_le.mp reusable.1
          rw [far] at le
          have : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
          omega
        rw [zero]
        exact ⟨Nat.zero_le _, fun _ => rfl⟩
      · exact covered.push _
    · cases computed
      exact .refl _
  · rename_i index _
    -- The builder keeps its withdrawable epoch, or gets the delay after the current epoch.
    have finish : ∀ (withdrawableEpoch balance : UInt64),
        (withdrawableEpoch = ((state.builders gloas).data[index]).withdrawableEpoch ∨
          ((state.builders gloas).data[index]).withdrawableEpoch ≠ FAR_FUTURE_EPOCH) →
        ((state.builders gloas).data[index]).balance.toNat ≤ balance.toNat →
        ReqKept state (state.putBuilder gloas index index.isLt
          { (state.builders gloas).data[index] with withdrawableEpoch, balance }) := by
      intro withdrawableEpoch balance epochCases more
      refine ⟨fun gloas' => ?_, fun gloas' covered => ?_⟩
      all_goals obtain rfl : gloas = gloas' := rfl
      · rfl
      refine covered.set (position := index.val) index.isLt fun named same => ⟨?_, fun set => ?_⟩
      · have read : (ledgerOf state gloas).builders[named.toNat]? =
            some ((state.builders gloas).data[index]) := by
          simp only [ledgerOf, same]
          exact Array.getElem?_eq_getElem index.isLt
        exact Nat.le_trans (covered.covered named _ read) more
      · refine covered.idle named fun old found => ?_
        simp only [ledgerOf, same, Array.getElem?_eq_getElem index.isLt,
          Option.some.injEq] at found
        subst found
        rcases epochCases with keep | gone
        · intro far
          apply set
          rw [keep]
          exact far
        · exact gone
    dsimp only at computed
    split at computed
    · rename_i reset
      obtain ⟨withdrawableEpoch, _, computed⟩ := bind_ok_iff.mp computed
      obtain ⟨balance, balanceOk, computed⟩ := bind_ok_iff.mp computed
      cases computed
      simp only [liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff] at balanceOk
      exact finish _ _ (.inr reset.1) (by omega)
    · obtain ⟨withdrawableEpoch, epochOk, computed⟩ := bind_ok_iff.mp computed
      obtain ⟨balance, balanceOk, computed⟩ := bind_ok_iff.mp computed
      cases computed
      cases epochOk
      simp only [liftAccessor_ok, liftArith, mapError_ok_iff, addChecked_ok_iff] at balanceOk
      exact finish _ _ (.inl rfl) (by omega)

/-- A builder exits only when it owes nothing. -/
theorem reqKept_processBuilderExitRequest {gloas : .glamsterdam ≤ fork}
    {request : BuilderExitRequest}
    (computed : processBuilderExitRequest config state gloas request = .ok after) :
    ReqKept state after := by
  rcases processBuilderExitRequest_cases computed with rfl | ⟨index, _, _, _, nothing, exited⟩
  · exact .refl _
  have zero := (getPendingBalanceToWithdrawForBuilder_ok_iff.mp nothing).2
  simp only [UInt64.toNat_zero] at zero
  simp only [initiateBuilderExit, bind_ok_iff] at exited
  obtain ⟨builder, found, _, _, set⟩ := exited
  obtain ⟨inside, rfl⟩ := setBuilder_ok set
  refine ⟨fun gloas' => ?_, fun gloas' covered => ?_⟩
  all_goals obtain rfl : gloas = gloas' := rfl
  · rfl
  refine covered.set inside fun named same => ?_
  have named' : named = index.val.toUInt64 := UInt64.toNat_inj.mp same
  subst named'
  rw [← pendingBuilderTotal_eq_owed, ← zero]
  exact ⟨Nat.zero_le _, fun _ => rfl⟩

/-- Settling the payment of the parent keeps every builder covered.

A payment still held moves to the queue.

Otherwise the bid of the parent charges its value now, which its builder can pay. -/
theorem covered_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after)
    (solvent : (ledgerOf state gloas).Solvent) (shaped : (ledgerOf state gloas).Shaped) :
    (ledgerOf after gloas).Covered ∧
      { ledgerOf after gloas with payments := [], queue := [] } =
        { ledgerOf state gloas with payments := [], queue := [] } := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    have same := pendingBuilderTotal_settleBuilderPayment settled
    have frame : { ledgerOf after gloas with payments := [], queue := [] } =
        { ledgerOf state gloas with payments := [], queue := [] } := by
      unfold settleBuilderPayment at settled
      split at settled
      · cases settled
        rfl
      · cases settled
    refine ⟨⟨fun index builder found => ?_, fun index set => ?_⟩, frame⟩
    · have builders := congrArg Ledger.builders frame
      simp only at builders
      rw [← pendingBuilderTotal_eq_owed, same, pendingBuilderTotal_eq_owed]
      exact solvent.covered index builder (builders ▸ found)
    · have builders := congrArg Ledger.builders frame
      simp only at builders
      rw [← pendingBuilderTotal_eq_owed, same, pendingBuilderTotal_eq_owed]
      exact (solvent.idle index fun old found => set old (builders ▸ found)).1
  · rename_i none
    simp only at computed
    split at computed
    · rename_i valued
      cases computed
      -- The bid of the parent waits, and its payment has left its position.
      obtain ⟨waits, header, _⟩ := shaped.resolve_left (UInt64.ne_of_lt valued).symm
      have latent : (ledgerOf state gloas).Latent
          (state.latestExecutionPayloadBid gloas).builderIndex := by
        refine ⟨waits, rfl, ?_⟩
        rintro ⟨position, _, located, -⟩
        rw [header] at located
        change parentPaymentPosition state = some position at located
        rw [none] at located
        cases located
      set bid := state.latestExecutionPayloadBid gloas
      have owed : ∀ index, (ledgerOf { state with builderPendingWithdrawals := fun _ =>
            ⟨(state.builderPendingWithdrawals gloas).data.push
              ⟨bid.feeRecipient, bid.value, bid.builderIndex⟩⟩ } gloas).owed index =
          (ledgerOf state gloas).owed index +
            if bid.builderIndex = index then bid.value.toNat else 0
          := by
        intro index
        simp only [Ledger.owed, ledgerOf, Array.toList_push, owedBy_append]
        simp only [owedBy, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        split <;> omega
      refine ⟨⟨fun index builder found => ?_, fun index set => ?_⟩, rfl⟩
      · rw [owed]
        split
        · rename_i same
          subst same
          exact solvent.latent _ builder found latent
        · simpa using solvent.covered index builder found
      · rw [owed]
        obtain ⟨zero, charge⟩ := solvent.idle index set
        split
        · rename_i same
          subst same
          exact absurd (charge latent) (UInt64.ne_of_lt valued).symm
        · simpa using zero
    · cases computed
      exact ⟨solvent.covers, rfl⟩

/-- The payload of the parent block keeps the ledger solvent.

An empty parent changes nothing.

A full parent settles its payment, runs its requests, and then is applied.

Its bid then charges nothing more. -/
theorem solvent_processParentExecutionPayload (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after)
    (solvent : (ledgerOf state gloas).Solvent) (shaped : (ledgerOf state gloas).Shaped) :
    (ledgerOf after gloas).Solvent ∧ after.slot = state.slot ∧
      after.latestBlockHeader.slot = state.latestBlockHeader.slot := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨solvent, rfl, rfl⟩
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  unfold applyParentExecutionPayload at applied
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    applied
  obtain ⟨coveredSettled, frameSettled⟩ := covered_settleParentPayment settledOk solvent shaped
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, buildersOk, exitsOk⟩ :=
    requestedOk
  have requests : ReqKept settled requested :=
    (ReqKept.foldlM (fun _ _ _ ok => .of_ledger (ledgerKept_processDepositRequest ok))
      depositsOk).trans <|
    (ReqKept.foldlM (fun _ _ _ ok => .of_ledger (ledgerKept_processWithdrawalRequest ok))
      withdrawalsOk).trans <|
    (ReqKept.foldlM (fun _ _ _ ok => .of_ledger (ledgerKept_processConsolidationRequest ok))
      consolidationsOk).trans <|
    (ReqKept.foldlM (fun _ _ _ ok => reqKept_processBuilderDepositRequest slots ok)
      buildersOk).trans
    (ReqKept.foldlM (fun _ _ _ ok => reqKept_processBuilderExitRequest ok) exitsOk)
  have covered := requests.covered gloas coveredSettled
  have frame := requests.frame gloas
  have slot : requested.slot = state.slot := by
    have one := congrArg Ledger.slot frame
    have two := congrArg Ledger.slot frameSettled
    simp only [ledgerOf] at one two
    rw [one, two]
  have header : requested.latestBlockHeader.slot = state.latestBlockHeader.slot := by
    have one := congrArg Ledger.headerSlot frame
    have two := congrArg Ledger.headerSlot frameSettled
    simp only [ledgerOf] at one two
    rw [one, two]
  have bid : requested.latestExecutionPayloadBid gloas = state.latestExecutionPayloadBid gloas := by
    have one := congrArg Ledger.bid frame
    have two := congrArg Ledger.bid frameSettled
    simp only [ledgerOf] at one two
    rw [one, two]
  refine ⟨Ledger.Covered.solvent ⟨covered.covered, covered.idle⟩ ?_, slot, header⟩
  simp [Ledger.Pending, ledgerOf, bid]

/-! ## The withdrawals of a block -/

/-- The index and amount of a withdrawal. -/
def payout (withdrawal : Withdrawal) : ValidatorIndex × Gwei :=
  (withdrawal.validatorIndex, withdrawal.amount)

/-- The index and amount of the withdrawal that pays a queued builder withdrawal. -/
def builderPayout (pending : BuilderPendingWithdrawal) : ValidatorIndex × Gwei :=
  (convertBuilderIndexToValidatorIndex pending.builderIndex, pending.amount)

/-- A withdrawal appended at the end of some withdrawals. -/
theorem appendWithdrawal_eq {withdrawals after : Array Withdrawal}
    {next after' : WithdrawalIndex} {index : ValidatorIndex} {address : ExecutionAddress}
    {amount : Gwei}
    (computed : appendWithdrawal withdrawals next index address amount = .ok (after, after')) :
    after = withdrawals.push ⟨next, index, address, amount⟩ := by
  simp only [appendWithdrawal, bind_ok_iff, liftArith, mapError_ok_iff, pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at computed
  obtain ⟨_, _, rfl, _⟩ := computed
  rfl

/-- The queued builder withdrawals that a payload pays are the first entries of the queue. -/
theorem getBuilderWithdrawals_loop_prefix {prior : Array Withdrawal} {limit : UInt64} :
    ∀ (queue : List BuilderPendingWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    getBuilderWithdrawals.loop prior limit queue withdrawals next processed = .ok result →
    ∃ taken, result.1.toList.map payout =
        withdrawals.toList.map payout ++ (queue.take taken).map builderPayout ∧
      result.2.2 = processed + taken
  | [], _, _, _, _, computed => by
    simp only [getBuilderWithdrawals.loop, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨0, by simp, rfl⟩
  | pending :: rest, withdrawals, _, processed, _, computed => by
    simp only [getBuilderWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact ⟨0, by simp, rfl⟩
    · simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, rest'⟩ := computed
      obtain ⟨taken, paid, count⟩ := getBuilderWithdrawals_loop_prefix rest _ _ _ rest'
      refine ⟨taken + 1, ?_, by rw [count]; omega⟩
      rw [paid, appendWithdrawal_eq appendedOk]
      simp [payout, builderPayout, List.take_succ_cons]

/-- Each queued partial withdrawal that a payload pays names a validator of the registry. -/
theorem getPendingPartialWithdrawals_loop_validators {state : BeaconState preset fork}
    {prior : Array Withdrawal} {epoch : Epoch} {limit : Nat} :
    ∀ (queue : List PendingPartialWithdrawal) (withdrawals : Array Withdrawal)
      (next : WithdrawalIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    (∀ withdrawal ∈ withdrawals.toList,
      withdrawal.validatorIndex.toNat < state.validators.data.size) →
    getPendingPartialWithdrawals.loop state prior epoch limit queue withdrawals next processed =
      .ok result →
    ∀ withdrawal ∈ result.1.toList, withdrawal.validatorIndex.toNat < state.validators.data.size
  | [], _, _, _, _, inside, computed => by
    simp only [getPendingPartialWithdrawals.loop, pure, Except.pure,
      Except.ok.injEq] at computed
    subst computed
    exact inside
  | pending :: rest, withdrawals, _, _, _, inside, computed => by
    simp only [getPendingPartialWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact inside
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨validator, found, balance, _, computed⟩ := computed
    have small : pending.validatorIndex.toNat < state.validators.data.size := by
      unfold getValidator at found
      split at found
      · rename_i read
        exact (Array.getElem?_eq_some_iff.mp read).1
      · cases found
    split at computed
    · obtain ⟨⟨appended, following⟩, appendedOk, rest'⟩ := bind_ok_iff.mp computed
      rw [liftAccessor_ok] at appendedOk
      refine getPendingPartialWithdrawals_loop_validators rest _ _ _ ?_ rest'
      rw [appendWithdrawal_eq appendedOk]
      intro withdrawal member
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact inside withdrawal old
      · exact small
    · exact getPendingPartialWithdrawals_loop_validators rest _ _ _ inside computed

/-- Each withdrawal of the sweep of validators names a validator of the registry. -/
theorem getValidatorsSweepWithdrawals_loop_validators {state : BeaconState preset fork}
    {prior : Array Withdrawal} {epoch : Epoch} {count limit : Nat} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : ValidatorIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    (∀ withdrawal ∈ withdrawals.toList,
      withdrawal.validatorIndex.toNat < state.validators.data.size) →
    getValidatorsSweepWithdrawals.loop state prior epoch count limit visits withdrawals next
      index processed = .ok result →
    ∀ withdrawal ∈ result.1.toList, withdrawal.validatorIndex.toNat < state.validators.data.size
  | 0, _, _, _, _, _, inside, computed => by
    simp only [getValidatorsSweepWithdrawals.loop, pure, Except.pure,
      Except.ok.injEq] at computed
    subst computed
    exact inside
  | visits + 1, withdrawals, _, index, _, _, inside, computed => by
    simp only [getValidatorsSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact inside
    obtain ⟨validator, found, computed⟩ := bind_ok_iff.mp computed
    obtain ⟨balance, _, computed⟩ := bind_ok_iff.mp computed
    rw [liftAccessor_ok] at found
    have small : index.toNat < state.validators.data.size := by
      unfold getValidator at found
      split at found
      · rename_i read
        exact (Array.getElem?_eq_some_iff.mp read).1
      · cases found
    -- A withdrawal of this validator, appended to the others.
    have pushed : ∀ extra : Withdrawal, extra.validatorIndex = index →
        ∀ withdrawal ∈ (withdrawals.push extra).toList,
          withdrawal.validatorIndex.toNat < state.validators.data.size := by
      intro extra named withdrawal member
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact inside withdrawal old
      · rw [named]
        exact small
    split at computed
    · obtain ⟨⟨appended, following⟩, appendedOk, computed⟩ := bind_ok_iff.mp computed
      obtain ⟨_, _, rest'⟩ := bind_ok_iff.mp computed
      rw [liftAccessor_ok] at appendedOk
      rw [appendWithdrawal_eq appendedOk] at rest'
      exact getValidatorsSweepWithdrawals_loop_validators visits _ _ _ _ (pushed _ rfl) rest'
    · split at computed
      · obtain ⟨⟨appended, following⟩, appendedOk, computed⟩ := bind_ok_iff.mp computed
        obtain ⟨_, _, rest'⟩ := bind_ok_iff.mp computed
        rw [liftAccessor_ok] at appendedOk
        rw [appendWithdrawal_eq appendedOk] at rest'
        exact getValidatorsSweepWithdrawals_loop_validators visits _ _ _ _ (pushed _ rfl) rest'
      · obtain ⟨⟨appended, following⟩, appendedOk, computed⟩ := bind_ok_iff.mp computed
        obtain ⟨_, _, rest'⟩ := bind_ok_iff.mp computed
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at appendedOk
        obtain ⟨rfl, -⟩ := appendedOk
        exact getValidatorsSweepWithdrawals_loop_validators visits _ _ _ _ inside rest'

/-- Each withdrawal of the sweep of builders names a withdrawable builder of the registry. -/
theorem getBuildersSweepWithdrawals_loop_withdrawable {state : BeaconState preset fork}
    {gloas : .glamsterdam ≤ fork} {prior : Array Withdrawal} {epoch : Epoch} {count : Nat}
    {limit : UInt64} :
    ∀ (visits : Nat) (withdrawals : Array Withdrawal) (next : WithdrawalIndex)
      (index : BuilderIndex) (processed : Nat)
      {result : Array Withdrawal × WithdrawalIndex × Nat},
    (∀ withdrawal ∈ withdrawals.toList, ∃ named builder,
      withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex named ∧
      (state.builders gloas).data[named.toNat]? = some builder ∧
      builder.withdrawableEpoch ≤ epoch) →
    getBuildersSweepWithdrawals.loop state gloas prior epoch count limit visits withdrawals next
      index processed = .ok result →
    ∀ withdrawal ∈ result.1.toList, ∃ named builder,
      withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex named ∧
      (state.builders gloas).data[named.toNat]? = some builder ∧
      builder.withdrawableEpoch ≤ epoch
  | 0, _, _, _, _, _, named, computed => by
    simp only [getBuildersSweepWithdrawals.loop, pure, Except.pure,
      Except.ok.injEq] at computed
    subst computed
    exact named
  | visits + 1, withdrawals, _, index, _, _, named, computed => by
    simp only [getBuildersSweepWithdrawals.loop] at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      exact named
    simp only [bind_ok_iff, liftAccessor_ok] at computed
    obtain ⟨builder, found, left, _, computed⟩ := computed
    have read : (state.builders gloas).data[index.toNat]? = some builder := by
      unfold getBuilder at found
      split at found
      · rename_i read
        cases found
        exact read
      · cases found
    split at computed
    · rename_i paid
      simp only [bind_ok_iff, liftAccessor_ok] at computed
      obtain ⟨⟨appended, following⟩, appendedOk, _, _, rest'⟩ := computed
      refine getBuildersSweepWithdrawals_loop_withdrawable visits _ _ _ _ ?_ rest'
      rw [appendWithdrawal_eq appendedOk]
      intro withdrawal member
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
      rcases member with old | rfl
      · exact named withdrawal old
      · exact ⟨index, builder, rfl, read, paid.1⟩
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at computed
      obtain ⟨_, _, rest'⟩ := computed
      exact getBuildersSweepWithdrawals_loop_withdrawable visits _ _ _ _ named rest'

/-- From Gloas, the withdrawals that a state expects, in two parts.

The first part pays the first entries of the queue of builder withdrawals, which leave it.

Each later withdrawal names a validator of the registry, or a withdrawable builder. -/
theorem getExpectedWithdrawals_split {capella : .shapella ≤ fork} (gloas : .glamsterdam ≤ fork)
    {expected : ExpectedWithdrawals}
    (computed : getExpectedWithdrawals state capella = .ok expected) :
    ∃ builders rest, expected.withdrawals = builders ++ rest ∧
      builders.toList.map payout =
        ((state.builderPendingWithdrawals gloas).data.toList.take
          expected.processedBuilderWithdrawalsCount).map builderPayout ∧
      ∀ withdrawal ∈ rest.toList,
        withdrawal.validatorIndex.toNat < state.validators.data.size ∨
          ∃ named builder,
            withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex named ∧
            (state.builders gloas).data[named.toNat]? = some builder ∧
            builder.withdrawableEpoch ≤ getCurrentEpoch state := by
  unfold getExpectedWithdrawals at computed
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨⟨builders, index1, builderCount⟩, buildersOk, ⟨partials, index2, _⟩, partialsOk,
    ⟨buildersSweep, index3, _⟩, buildersSweepOk, ⟨sweep, index4, _⟩, sweepOk, rfl⟩ := computed
  refine ⟨builders, partials ++ buildersSweep ++ sweep, by simp [Array.append_assoc], ?_, ?_⟩
  · simp only [gloas, ↓reduceDIte] at buildersOk
    unfold getBuilderWithdrawals at buildersOk
    simp only [bind_ok_iff, ensure_ok_iff] at buildersOk
    obtain ⟨_, _, _, _, loopOk⟩ := buildersOk
    obtain ⟨taken, paid, count⟩ := getBuilderWithdrawals_loop_prefix _ _ _ _ loopOk
    simp only [Nat.zero_add] at count
    simp only at paid count ⊢
    rw [paid, count]
    simp
  · have validators : ∀ withdrawal ∈ partials.toList ++ sweep.toList,
        withdrawal.validatorIndex.toNat < state.validators.data.size := by
      intro withdrawal member
      rcases List.mem_append.mp member with queued | swept
      · split at partialsOk
        · unfold getPendingPartialWithdrawals at partialsOk
          simp only [bind_ok_iff, ensure_ok_iff] at partialsOk
          obtain ⟨_, _, _, _, loopOk⟩ := partialsOk
          exact getPendingPartialWithdrawals_loop_validators _ _ _ _ (by simp) loopOk
            withdrawal queued
        · simp only [Except.ok.injEq, Prod.mk.injEq] at partialsOk
          rw [← partialsOk.1] at queued
          simp at queued
      · unfold getValidatorsSweepWithdrawals at sweepOk
        simp only [bind_ok_iff, ensure_ok_iff] at sweepOk
        obtain ⟨_, _, loopOk⟩ := sweepOk
        exact getValidatorsSweepWithdrawals_loop_validators _ _ _ _ _ (by simp) loopOk
          withdrawal swept
    intro withdrawal member
    simp only [Array.toList_append, List.mem_append] at member
    rcases member with (queued | swept) | swept
    · exact .inl (validators withdrawal (List.mem_append_left _ queued))
    · right
      simp only [gloas, ↓reduceDIte] at buildersSweepOk
      unfold getBuildersSweepWithdrawals at buildersSweepOk
      simp only [bind_ok_iff, ensure_ok_iff] at buildersSweepOk
      obtain ⟨_, _, _, _, loopOk⟩ := buildersSweepOk
      exact getBuildersSweepWithdrawals_loop_withdrawable _ _ _ _ _ (by simp) loopOk
        withdrawal swept
    · exact .inl (validators withdrawal (List.mem_append_right _ swept))

/-- What some withdrawals take under one index, on natural numbers. -/
def takenFrom (withdrawals : List Withdrawal) (named : ValidatorIndex) : Nat :=
  ((withdrawals.filter (·.validatorIndex = named)).map (·.amount.toNat)).sum

/-- From Gloas, withdrawals change the builders only in their balances.

The balance of a builder below `2^40` falls by what the withdrawals take under its index.

It stops at zero. -/
theorem foldlM_applyWithdrawal_ledger (gloas : .glamsterdam ≤ fork) :
    ∀ (withdrawals : List Withdrawal) (state after : BeaconState preset fork),
      withdrawals.foldlM applyWithdrawal state = .ok after →
      { ledgerOf after gloas with builders := #[] } =
          { ledgerOf state gloas with builders := #[] } ∧
        (∀ position : Nat, ((after.builders gloas).data[position]?).map Builder.withdrawableEpoch =
          ((state.builders gloas).data[position]?).map Builder.withdrawableEpoch) ∧
        ∀ index : BuilderIndex, index.toNat < 2 ^ 40 →
          ((after.builders gloas).data[index.toNat]?).map (fun builder : Builder =>
              builder.balance.toNat) =
            ((state.builders gloas).data[index.toNat]?).map fun builder : Builder =>
              builder.balance.toNat -
                takenFrom withdrawals (convertBuilderIndexToValidatorIndex index)
  | [], state, after, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    refine ⟨rfl, fun _ => rfl, fun index _ => ?_⟩
    cases (state.builders gloas).data[index.toNat]? <;> simp [takenFrom]
  | withdrawal :: rest, state, after, computed => by
    rw [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨middle, step, computed⟩ := computed
    obtain ⟨frame, epochs, balances⟩ :=
      foldlM_applyWithdrawal_ledger gloas rest middle after computed
    have taken : ∀ named, takenFrom (withdrawal :: rest) named =
        (if withdrawal.validatorIndex = named then withdrawal.amount.toNat else 0) +
          takenFrom rest named := by
      intro named
      unfold takenFrom
      by_cases same : withdrawal.validatorIndex = named <;> simp [same]
    unfold applyWithdrawal at step
    split at step
    · rename_i flagged
      simp only [bind_ok_iff] at step
      obtain ⟨builder, builderOk, set⟩ := step
      obtain ⟨inside, rfl⟩ := setBuilder_ok set
      have read := getElem_of_getBuilder builderOk inside
      refine ⟨frame.trans rfl, fun position => ?_, fun index small => ?_⟩
      · rw [epochs position]
        change (((state.builders gloas).data.set _ _ inside)[position]?).map _ = _
        rw [Array.getElem?_set]
        split
        · rename_i same
          subst same
          rw [Array.getElem?_eq_getElem inside, read]
          rfl
        · rfl
      · rw [balances index small, taken]
        change (((state.builders gloas).data.set _ _ inside)[index.toNat]?).map _ = _
        rw [Array.getElem?_set]
        -- The withdrawal names this builder exactly when its builder index is this one.
        have named : convertValidatorIndexToBuilderIndex withdrawal.validatorIndex = index ↔
            withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex index := by
          constructor
          · intro same
            rw [← same, convertBuilderIndexToValidatorIndex_convertValidatorIndexToBuilderIndex
              flagged.2]
          · intro same
            rw [same, convertValidatorIndexToBuilderIndex_convertBuilderIndexToValidatorIndex small]
        split
        · rename_i same
          have equal : convertValidatorIndexToBuilderIndex withdrawal.validatorIndex = index :=
            UInt64.toNat_inj.mp same
          rw [← same, Array.getElem?_eq_getElem inside, read]
          simp [named.mp equal, toNat_saturatingSub, Nat.sub_sub]
        · rename_i differ
          have other : ¬ withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex index :=
            fun h => differ (by rw [named.mpr h])
          simp [other]
    · rename_i notFlagged
      -- A withdrawal of a validator keeps the builders.
      have kept := LedgerKept.decreaseBalance step
      have same := kept.same gloas
      have builders : middle.builders gloas = state.builders gloas := by
        simp only [decreaseBalance, bind_ok_iff] at step
        obtain ⟨_, _, set⟩ := step
        obtain ⟨_, rfl⟩ := setBalance_ok set
        rfl
      refine ⟨frame.trans (by rw [same]), fun position => by rw [epochs, builders],
        fun index small => ?_⟩
      have other : ¬ withdrawal.validatorIndex = convertBuilderIndexToValidatorIndex index :=
        fun h => notFlagged ⟨gloas, h ▸ isBuilderIndex_convertBuilderIndexToValidatorIndex index⟩
      rw [balances index small, taken, builders]
      simp [other]

/-- From Gloas, applying the expected withdrawals lowers the balances.

It drops the queued builder withdrawals that were read, and keeps the rest of the ledger. -/
theorem applyExpectedWithdrawals_ledger {capella : .shapella ≤ fork} (gloas : .glamsterdam ≤ fork)
    {expected : ExpectedWithdrawals}
    (computed : applyExpectedWithdrawals state capella expected = .ok after) :
    ∃ applied, expected.withdrawals.toList.foldlM applyWithdrawal state = .ok applied ∧
      ledgerOf after gloas = { ledgerOf applied gloas with
        queue :=
          (ledgerOf applied gloas).queue.drop expected.processedBuilderWithdrawalsCount } := by
  unfold applyExpectedWithdrawals at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨applied, appliedOk, indexed, indexedOk, swept, sweptOk, last⟩ := computed
  refine ⟨applied, by
    unfold applyWithdrawals at appliedOk
    rw [← Array.foldlM_toList] at appliedOk
    exact appliedOk, ?_⟩
  have indexedSame : ledgerOf indexed gloas = ledgerOf applied gloas := by
    unfold updateNextWithdrawalIndex at indexedOk
    split at indexedOk
    · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at indexedOk
      obtain ⟨_, _, rfl⟩ := indexedOk
      rfl
    · cases indexedOk
      rfl
  simp only [gloas, ↓reduceDIte] at sweptOk last
  have lastSame : ledgerOf after gloas = ledgerOf swept gloas := by
    unfold updateNextWithdrawalValidatorIndex at last
    simp only [bind_ok_iff] at last
    obtain ⟨_, _, last⟩ := last
    split at last
    · cases last
    · simp only [pure, Except.pure, Except.ok.injEq] at last
      subst last
      rfl
  rw [lastSame]
  have queued : ∀ kept : BeaconState preset fork, kept =
      (if electra : .pectra ≤ fork then
        updatePendingPartialWithdrawals
          (updateBuilderPendingWithdrawals
            (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
            expected.processedBuilderWithdrawalsCount)
          electra expected.processedPartialWithdrawalsCount
      else
        updateBuilderPendingWithdrawals
          (updatePayloadExpectedWithdrawals indexed gloas expected.withdrawals) gloas
          expected.processedBuilderWithdrawalsCount) →
      ledgerOf kept gloas = { ledgerOf applied gloas with
        queue :=
          (ledgerOf applied gloas).queue.drop expected.processedBuilderWithdrawalsCount } := by
    intro kept same
    subst same
    rw [← indexedSame]
    split <;> simp [ledgerOf, updatePendingPartialWithdrawals, updateBuilderPendingWithdrawals,
      updatePayloadExpectedWithdrawals, List.take_of_length_le]
  have builderIndexSame : ∀ (kept next : BeaconState preset fork) (count : Nat),
      updateNextWithdrawalBuilderIndex kept gloas count = .ok next →
        ledgerOf next gloas = ledgerOf kept gloas := by
    intro kept next count computed
    unfold updateNextWithdrawalBuilderIndex at computed
    dsimp only at computed
    split at computed
    · simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
    · obtain ⟨_, _, computed⟩ := bind_ok_iff.mp computed
      simp only [pure, Except.pure, Except.ok.injEq] at computed
      subst computed
      rfl
  rw [builderIndexSame _ _ _ sweptOk]
  exact queued _ rfl

theorem takenFrom_append (first second : List Withdrawal) (named : ValidatorIndex) :
    takenFrom (first ++ second) named = takenFrom first named + takenFrom second named := by
  simp [takenFrom]

/-- What some withdrawals take under one index reads only their indices and amounts. -/
theorem takenFrom_eq_payouts (withdrawals : List Withdrawal) (named : ValidatorIndex) :
    takenFrom withdrawals named =
      (((withdrawals.map payout).filter (·.1 = named)).map (·.2.toNat)).sum := by
  induction withdrawals with
  | nil => rfl
  | cons withdrawal rest ih =>
    unfold takenFrom at ih ⊢
    by_cases same : withdrawal.validatorIndex = named <;> simp [same, payout, ih]

/-- Withdrawals that take something under an index hold one under that index. -/
theorem exists_of_takenFrom_pos {withdrawals : List Withdrawal} {named : ValidatorIndex}
    (positive : 0 < takenFrom withdrawals named) :
    ∃ withdrawal ∈ withdrawals, withdrawal.validatorIndex = named := by
  induction withdrawals with
  | nil => simp [takenFrom] at positive
  | cons withdrawal rest ih =>
    by_cases same : withdrawal.validatorIndex = named
    · exact ⟨withdrawal, List.mem_cons_self, same⟩
    · have : 0 < takenFrom rest named := by
        unfold takenFrom at positive ⊢
        simpa [same] using positive
      obtain ⟨other, member, named'⟩ := ih this
      exact ⟨other, List.mem_cons_of_mem _ member, named'⟩

/-- The queued withdrawals paid under the index of a builder take at most what it owes there.

An entry under another index that shares the flagged index is past `2^40`, so it owes nothing. -/
theorem payouts_le_owedBy {index : BuilderIndex} (small : index.toNat < 2 ^ 40) :
    ∀ entries : List BuilderPendingWithdrawal,
      (∀ entry ∈ entries, entry.builderIndex ≠ index →
        convertBuilderIndexToValidatorIndex entry.builderIndex =
          convertBuilderIndexToValidatorIndex index → entry.amount = 0) →
      (((entries.map builderPayout).filter
          (·.1 = convertBuilderIndexToValidatorIndex index)).map (·.2.toNat)).sum ≤
        owedBy index entries
  | [], _ => by simp [owedBy]
  | entry :: rest, nothing => by
    have ih := payouts_le_owedBy small rest
      (fun other member => nothing other (List.mem_cons_of_mem _ member))
    have step : owedBy index (entry :: rest) =
        (if entry.builderIndex = index then entry.amount.toNat else 0) + owedBy index rest := by
      simp [owedBy]
    rw [step]
    by_cases flagged : convertBuilderIndexToValidatorIndex entry.builderIndex =
        convertBuilderIndexToValidatorIndex index
    · by_cases same : entry.builderIndex = index
      · simp [builderPayout, same] at ih ⊢
        omega
      · have zero := nothing entry List.mem_cons_self same flagged
        simp [builderPayout, flagged, same, zero] at ih ⊢
        omega
    · have differ : entry.builderIndex ≠ index := fun same => flagged (by rw [same])
      simp [builderPayout, flagged, differ] at ih ⊢
      omega

/-- From Gloas, the withdrawals of a block keep every builder covered.

A queued builder withdrawal takes what its builder owes, which its balance holds.

The sweep of builders takes only from a withdrawable builder, which owes nothing.

The other withdrawals take from validators, whose indices are below `2^40`.

So no withdrawal of a builder ever takes more than its balance. -/
theorem covered_processWithdrawals (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    (gloas : .glamsterdam ≤ fork) {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    (covered : (ledgerOf state gloas).Covered)
    (validators : state.validators.data.size ≤ 2 ^ 40)
    (builders : (state.builders gloas).data.size ≤ 2 ^ 40) :
    (ledgerOf after gloas).Covered ∧
      { ledgerOf after gloas with builders := #[], queue := [] } =
        { ledgerOf state gloas with builders := #[], queue := [] } ∧
      (after.builders gloas).data.size = (state.builders gloas).data.size := by
  unfold processWithdrawals at computed
  simp only [gloas, ↓reduceDIte] at computed
  split at computed
  swap
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨covered, rfl, rfl⟩
  obtain ⟨expected, expectedOk, appliedOk⟩ := bind_ok_iff.mp computed
  rw [liftAccessor_ok] at appliedOk
  obtain ⟨paid, rest, split, payouts, others⟩ := getExpectedWithdrawals_split gloas expectedOk
  obtain ⟨applied, foldOk, ledgerEq⟩ := applyExpectedWithdrawals_ledger gloas appliedOk
  obtain ⟨frame, epochs, balances⟩ := foldlM_applyWithdrawal_ledger gloas _ _ _ foldOk
  have queueSame : (ledgerOf applied gloas).queue = (ledgerOf state gloas).queue := by
    have same := congrArg Ledger.queue frame
    exact same
  have paymentsSame : (ledgerOf applied gloas).payments = (ledgerOf state gloas).payments := by
    have same := congrArg Ledger.payments frame
    exact same
  set count := expected.processedBuilderWithdrawalsCount
  -- What a builder owes after: its old debt less the entries read from the queue.
  have owedAfter : ∀ index, (ledgerOf after gloas).owed index +
      owedBy index ((ledgerOf state gloas).queue.take count) =
        (ledgerOf state gloas).owed index := by
    intro index
    have halves := owedBy_append index ((ledgerOf state gloas).queue.take count)
      ((ledgerOf state gloas).queue.drop count)
    rw [List.take_append_drop] at halves
    rw [ledgerEq]
    unfold Ledger.owed
    dsimp only
    rw [queueSame, paymentsSame]
    omega
  have sizeSame : (applied.builders gloas).data.size = (state.builders gloas).data.size := by
    apply Nat.le_antisymm
    · by_contra more
      have := epochs (state.builders gloas).data.size
      rw [Array.getElem?_eq_none (Nat.le_refl _)] at this
      rw [Array.getElem?_eq_getElem (by omega)] at this
      simp at this
    · by_contra more
      have := epochs (applied.builders gloas).data.size
      rw [Array.getElem?_eq_none (Nat.le_refl _)] at this
      rw [Array.getElem?_eq_getElem (by omega)] at this
      simp at this
  have afterBuilders : (ledgerOf after gloas).builders = (applied.builders gloas).data := by
    rw [ledgerEq]
    rfl
  -- A builder index that is not this one but shares its flagged index owes nothing.
  have nothing : ∀ index : BuilderIndex, index.toNat < 2 ^ 40 →
      ∀ entry ∈ (ledgerOf state gloas).queue.take count, entry.builderIndex ≠ index →
        convertBuilderIndexToValidatorIndex entry.builderIndex =
          convertBuilderIndexToValidatorIndex index → entry.amount = 0 := by
    intro index small entry member differ flagged
    have large : 2 ^ 40 ≤ entry.builderIndex.toNat := by
      by_contra below
      apply differ
      have := congrArg convertValidatorIndexToBuilderIndex flagged
      rwa [convertValidatorIndexToBuilderIndex_convertBuilderIndexToValidatorIndex
          (by omega),
        convertValidatorIndexToBuilderIndex_convertBuilderIndexToValidatorIndex small] at this
    have zero := covered.idle entry.builderIndex fun builder found => by
      simp only [ledgerOf] at found
      rw [Array.getElem?_eq_none (by omega)] at found
      cases found
    have single := owedBy_le_of_mem (index := entry.builderIndex)
      (List.mem_of_mem_take member)
    rw [owedBy_single rfl] at single
    unfold Ledger.owed at zero
    exact UInt64.toNat_inj.mp (by simp only [UInt64.toNat_zero]; omega)
  have small : ∀ index : BuilderIndex, ∀ builder,
      (ledgerOf state gloas).builders[index.toNat]? = some builder → index.toNat < 2 ^ 40 := by
    intro index builder found
    have := (Array.getElem?_eq_some_iff.mp found).1
    simp only [ledgerOf] at this
    omega
  refine ⟨⟨fun index builder' found' => ?_, fun index set => ?_⟩, ?_, ?_⟩
  · rw [afterBuilders] at found'
    -- The builder was there before, with the same withdrawable epoch.
    have position := epochs index.toNat
    rw [found'] at position
    cases before : (state.builders gloas).data[index.toNat]? with
    | none => simp [before] at position
    | some builder =>
      simp only [before, Option.map_some, Option.some.injEq] at position
      have foundBefore : (ledgerOf state gloas).builders[index.toNat]? = some builder := before
      have below := small index builder foundBefore
      have balance := balances index below
      rw [found', before] at balance
      simp only [Option.map_some, Option.some.injEq] at balance
      rw [balance]
      have owed := owedAfter index
      have old := covered.covered index builder foundBefore
      rw [split, Array.toList_append, takenFrom_append]
      by_cases swept : takenFrom rest.toList (convertBuilderIndexToValidatorIndex index) = 0
      · -- Only the queued withdrawals take from this builder.
        have taken := payouts_le_owedBy below _ (nothing index below)
        have paidLe : takenFrom paid.toList (convertBuilderIndexToValidatorIndex index) ≤
            owedBy index ((ledgerOf state gloas).queue.take count) := by
          rw [takenFrom_eq_payouts]
          have same : paid.toList.map payout =
              ((ledgerOf state gloas).queue.take count).map builderPayout := payouts
          rw [same]
          exact taken
        omega
      · -- The sweep of builders took from it, so it is withdrawable and owes nothing.
        obtain ⟨withdrawal, member, named⟩ := exists_of_takenFrom_pos (Nat.pos_of_ne_zero swept)
        rcases others withdrawal member with validator | ⟨other, otherBuilder, flagged, read, early⟩
        · have := isBuilderIndex_eq_false_of_lt (index := withdrawal.validatorIndex) (by omega)
          rw [named, isBuilderIndex_convertBuilderIndexToValidatorIndex] at this
          cases this
        · have otherSmall := small other otherBuilder read
          have same : other = index := by
            have := congrArg convertValidatorIndexToBuilderIndex (flagged.symm.trans named)
            rwa [convertValidatorIndexToBuilderIndex_convertBuilderIndexToValidatorIndex otherSmall,
              convertValidatorIndexToBuilderIndex_convertBuilderIndexToValidatorIndex below] at this
          subst same
          have zero := covered.idle other fun old found far => by
            simp only [ledgerOf] at found
            rw [read, Option.some.injEq] at found
            subst found
            rw [far] at early
            have := UInt64.le_iff_toNat_le.mp early
            have := getCurrentEpoch_lt_far slots state
            omega
          omega
  · -- A builder that is idle after was idle before.
    have before := covered.idle index fun builder found => by
      have position := epochs index.toNat
      simp only [ledgerOf] at found
      rw [found] at position
      cases after' : (applied.builders gloas).data[index.toNat]? with
      | none => simp [after'] at position
      | some builder' =>
        simp only [after', Option.map_some, Option.some.injEq] at position
        rw [← position]
        exact set builder' (by rw [afterBuilders]; exact after')
    have := owedAfter index
    omega
  · rw [ledgerEq]
    simp only at frame ⊢
    simp only [Ledger.mk.injEq] at frame ⊢
    exact ⟨frame.1, frame.2.1, frame.2.2.1, frame.2.2.2.1, trivial, frame.2.2.2.2.2.1, trivial⟩
  · show (ledgerOf after gloas).builders.size = _
    rw [afterBuilders, sizeSame]

/-- From Gloas, the withdrawals of a block keep the ledger solvent.

They run only when the payload of the latest bid is applied, so that bid charges nothing. -/
theorem solvent_processWithdrawals (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    (gloas : .glamsterdam ≤ fork) {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after)
    (solvent : (ledgerOf state gloas).Solvent)
    (validators : state.validators.data.size ≤ 2 ^ 40)
    (builders : (state.builders gloas).data.size ≤ 2 ^ 40) :
    (ledgerOf after gloas).Solvent ∧ after.slot = state.slot ∧
      after.latestBlockHeader.slot = state.latestBlockHeader.slot ∧
      after.latestExecutionPayloadBid gloas = state.latestExecutionPayloadBid gloas := by
  obtain ⟨covered, frame, _⟩ :=
    covered_processWithdrawals slots gloas computed solvent.covers validators builders
  have slot := congrArg Ledger.slot frame
  have header := congrArg Ledger.headerSlot frame
  have hash := congrArg Ledger.blockHash frame
  have bid := congrArg Ledger.bid frame
  simp only at slot header hash bid
  refine ⟨?_, slot, header, bid⟩
  by_cases full : isParentBlockFull state gloas = true
  · refine covered.solvent ?_
    unfold isParentBlockFull at full
    have hash' : after.latestBlockHash gloas = state.latestBlockHash gloas := hash
    have bid' : after.latestExecutionPayloadBid gloas = state.latestExecutionPayloadBid gloas := bid
    simp only [Ledger.Pending, ledgerOf, ne_eq, Decidable.not_not]
    rw [hash', bid']
    simpa using full
  · unfold processWithdrawals at computed
    simp only [gloas, ↓reduceDIte, full, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
      Except.ok.injEq] at computed
    subst computed
    exact solvent

/-- From Gloas, the execution part of a block: the withdrawals, then the bid. -/
theorem solvent_processBlockExecution (pp : PaymentPreset preset) (gloas : .glamsterdam ≤ fork)
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after)
    (solvent : (ledgerOf state gloas).Solvent)
    (header : state.latestBlockHeader.slot = state.slot)
    (validators : state.validators.data.size ≤ 2 ^ 40)
    (builders : (state.builders gloas).data.size ≤ 2 ^ 40) :
    (ledgerOf after gloas).Solvent ∧ (ledgerOf after gloas).Shaped ∧
      (after.latestExecutionPayloadBid gloas).slot = after.slot ∧ after.slot = state.slot ∧
      after.latestBlockHeader.slot = state.latestBlockHeader.slot := by
  unfold processBlockExecution at computed
  simp only [gloas, ↓reduceDIte] at computed
  obtain ⟨withdrawn, withdrawnOk, bidOk⟩ := bind_ok_iff.mp computed
  have slots : 1 < preset.SLOTS_PER_EPOCH.toNat := by have := pp.slots; omega
  obtain ⟨solvent', slot, header', _⟩ :=
    solvent_processWithdrawals slots gloas withdrawnOk solvent validators builders
  obtain ⟨solventAfter, shaped, current, slotAfter, headerAfter⟩ :=
    solvent_processExecutionPayloadBid pp gloas bidOk solvent' (by rw [header', slot, header])
  exact ⟨solventAfter, shaped, current, slotAfter.trans slot,
    by rw [headerAfter, header']⟩

/-- The payload of the parent block keeps the registry of validators and the balances. -/
theorem sameSizes_processParentExecutionPayload {gloas : .glamsterdam ≤ fork}
    {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    SameSizes state after := by
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
  have settledSame : SameSizes state settled := by
    unfold settleParentPayment at settledOk
    split at settledOk
    · have settled := liftAccessor_ok.mp settledOk
      unfold settleBuilderPayment at settled
      split at settled
      · cases settled
        exact ⟨rfl, rfl⟩
      · cases settled
    · simp only at settledOk
      split at settledOk <;> cases settledOk <;> exact ⟨rfl, rfl⟩
  have fold : ∀ {α : Type} {step : BeaconState preset fork → α → Except TransitionError _}
      {items : List α} {first last : BeaconState preset fork},
      (∀ s x s', step s x = .ok s' → SameSizes s s') →
      items.foldlM step first = .ok last → SameSizes first last :=
    fun kept computed => foldlM_ok_invariant (SameSizes _)
      (fun _ _ _ before ok => before.trans (kept _ _ _ ok)) (.refl _) computed
  unfold processParentRequests at requestedOk
  simp only [bind_ok_iff, ← Array.foldlM_toList] at requestedOk
  obtain ⟨_, depositsOk, _, withdrawalsOk, _, consolidationsOk, _, buildersOk, exitsOk⟩ :=
    requestedOk
  have deposits := fold (fun s x s' ok => by
    obtain ⟨start, recorded⟩ := recordDepositRequestsStart_eq (state := s) (index := x.index)
    simp only [processDepositRequest, recorded, liftAccessor_ok, addPendingDeposit, bind_ok_iff,
      pure, Except.pure, Except.ok.injEq] at ok
    obtain ⟨_, _, rfl⟩ := ok
    exact ⟨rfl, rfl⟩) depositsOk
  have withdrawals := fold (fun _ _ _ ok => sameSizes_processWithdrawalRequest ok) withdrawalsOk
  have consolidations :=
    fold (fun _ _ _ ok => sameSizes_processConsolidationRequest ok) consolidationsOk
  have builderDeposits := fold (fun s x s' ok => by
    unfold processBuilderDepositRequest at ok
    split at ok
    · cases ok
      exact .refl _
    split at ok
    · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
      split at ok
      · cases ok
        simp only [addBuilderToRegistry]
        split <;> exact ⟨rfl, rfl⟩
      · cases ok
        exact .refl _
    · dsimp only at ok
      split at ok <;>
      · obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
        obtain ⟨_, _, ok⟩ := bind_ok_iff.mp ok
        cases ok
        exact ⟨rfl, rfl⟩) buildersOk
  have builderExits := fold (fun s x s' ok => by
    rcases processBuilderExitRequest_cases ok with rfl | ⟨_, _, _, _, _, exited⟩
    · exact .refl _
    · simp only [initiateBuilderExit, bind_ok_iff] at exited
      obtain ⟨_, _, _, _, set⟩ := exited
      obtain ⟨_, rfl⟩ := setBuilder_ok set
      exact ⟨rfl, rfl⟩) exitsOk
  exact (settledSame.trans <| deposits.trans <| withdrawals.trans <| consolidations.trans <|
    builderDeposits.trans builderExits).trans ⟨rfl, rfl⟩

/-- A block header is for the slot of the state. -/
theorem processBlockHeader_slot {block : BeaconBlock preset fork}
    (computed : processBlockHeader state block = .ok after) : block.slot = state.slot := by
  simp only [processBlockHeader, bind_ok_iff, ensure_ok_iff] at computed
  obtain ⟨_, same, -⟩ := computed
  exact same

/-! ## Blocks -/

/-- From Gloas, a block keeps the ledger solvent and shaped.

The registries of validators at the start, and of builders at the end, must be below `2^40`. -/
theorem solvent_processBlock (pp : PaymentPreset preset) (gloas : .glamsterdam ≤ fork)
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after)
    (solvent : (ledgerOf state gloas).Solvent) (shaped : (ledgerOf state gloas).Shaped)
    (validators : state.validators.data.size ≤ 2 ^ 40)
    (builders : (after.builders gloas).data.size ≤ 2 ^ 40) :
    (ledgerOf after gloas).Solvent ∧ (ledgerOf after gloas).Shaped := by
  have slots : 1 < preset.SLOTS_PER_EPOCH.toNat := by have := pp.slots; omega
  have altair : .altair ≤ fork := Nat.le_trans (by decide) gloas
  have bellatrix : .bellatrix ≤ fork := Nat.le_trans (by decide) gloas
  unfold processBlock at computed
  simp only [altair, ↓reduceDIte] at computed
  unfold processBlockAltair at computed
  simp only [bind_ok_iff] at computed
  obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
    votedOk, operated, operatedOk, synced⟩ := computed
  simp only [gloas, bellatrix, ↓reduceDIte] at paidOk executedOk
  -- The parent payload.
  obtain ⟨paidSolvent, paidSlot, _⟩ :=
    solvent_processParentExecutionPayload slots paidOk solvent shaped
  have paidSizes := sameSizes_processParentExecutionPayload paidOk
  -- The header: only its slot enters the ledger, and it is the slot of the state.
  have headerSlot := processBlockHeader_slot headedOk
  obtain ⟨_, _, rfl⟩ := processBlockHeader_eq headedOk
  -- The execution part.
  have later : BuildersAdvance config executed after :=
    (buildersAdvance_processRandao revealedOk).trans <|
    (show BuildersAdvance config revealed voted by
      split at votedOk
      · exact buildersAdvance_processEth1Data votedOk
      · cases votedOk
        exact .refl _).trans <|
    (buildersAdvance_processOperations operatedOk).trans
      (buildersAdvance_processSyncAggregate synced)
  have executedSizes := (buildersAdvance_processBlockExecution (config := config) executedOk).size
    gloas
  have headedSolvent := paidSolvent
  replace headedSolvent : ({ ledgerOf paid gloas with headerSlot := block.slot } :
      Ledger preset fork).Solvent :=
    ⟨headedSolvent.covered, headedSolvent.latent, headedSolvent.idle, headedSolvent.quiet⟩
  obtain ⟨executedSolvent, executedShaped, current, executedSlot, executedHeader⟩ :=
    solvent_processBlockExecution pp gloas executedOk headedSolvent
      (by simp only; rw [headerSlot, paidSlot])
      (by rw [paidSizes.1]; exact validators)
      (by have := later.size gloas; simp only at executedSizes ⊢; omega)
  -- The RANDAO reveal and the vote keep the ledger.
  have revealedKept := ledgerKept_processRandao revealedOk
  have votedKept : LedgerKept revealed voted := by
    split at votedOk
    · exact ledgerKept_processEth1Data votedOk
    · cases votedOk
      exact .refl _
  have kept := revealedKept.trans votedKept
  -- The operations keep the ledger solvent.
  have operations := opsKept_processOperations pp operatedOk
  have votedSolvent : (ledgerOf voted gloas).Solvent := (kept.same gloas) ▸ executedSolvent
  have votedCurrent : (voted.latestExecutionPayloadBid gloas).slot = voted.slot := by
    have bid := congrArg Ledger.bid (kept.same gloas)
    have slot := congrArg Ledger.slot (kept.same gloas)
    simp only [ledgerOf] at bid slot
    rw [bid, slot]
    exact current
  have operatedSolvent := operations.solvent gloas votedCurrent votedSolvent
  have syncedKept := ledgerKept_processSyncAggregate synced
  refine ⟨(syncedKept.same gloas) ▸ operatedSolvent, ?_⟩
  -- The shape reads only the parts of the ledger that the steps after the bid keep.
  have frame := operations.frame gloas
  have votedShaped : (ledgerOf voted gloas).Shaped := (kept.same gloas) ▸ executedShaped
  rw [syncedKept.same gloas]
  have bid : (ledgerOf operated gloas).bid = (ledgerOf voted gloas).bid := by
    have same := congrArg Ledger.bid frame
    exact same
  have header : (ledgerOf operated gloas).headerSlot = (ledgerOf voted gloas).headerSlot := by
    have same := congrArg Ledger.headerSlot frame
    exact same
  have hash : (ledgerOf operated gloas).blockHash = (ledgerOf voted gloas).blockHash := by
    have same := congrArg Ledger.blockHash frame
    exact same
  have slot : (ledgerOf operated gloas).slot = (ledgerOf voted gloas).slot := by
    have same := congrArg Ledger.slot frame
    exact same
  exact votedShaped.later bid header hash (slot ▸ UInt64.le_refl _)

/-! ## Upgrades and runs -/

/-- Two ledgers, perhaps of two forks, that agree on every part that solvency reads. -/
structure Ledger.Agree {fork' : Base.Fork} (ledger : Ledger preset fork)
    (other : Ledger preset fork') : Prop where
  slot : other.slot = ledger.slot
  headerSlot : other.headerSlot = ledger.headerSlot
  blockHash : other.blockHash = ledger.blockHash
  builders : other.builders = ledger.builders
  payments : other.payments = ledger.payments
  queue : other.queue = ledger.queue
  bidSlot : other.bid.slot = ledger.bid.slot
  bidHash : other.bid.blockHash = ledger.bid.blockHash
  bidBuilder : other.bid.builderIndex = ledger.bid.builderIndex
  bidValue : other.bid.value = ledger.bid.value

/-- Solvency and shape carry over between ledgers that agree. -/
theorem Ledger.Agree.solvent {fork' : Base.Fork} {ledger : Ledger preset fork}
    {other : Ledger preset fork'} (agree : ledger.Agree other) (solvent : ledger.Solvent)
    (shaped : ledger.Shaped) : other.Solvent ∧ other.Shaped := by
  have owed : ∀ index, other.owed index = ledger.owed index := by
    intro index
    unfold Ledger.owed
    rw [agree.payments, agree.queue]
  have position : other.position = ledger.position := by
    funext slot
    unfold Ledger.position Ledger.previousEpoch Ledger.currentEpoch
    rw [agree.slot]
  have pending : other.Pending ↔ ledger.Pending := by
    unfold Ledger.Pending
    rw [agree.blockHash, agree.bidHash]
  have held : other.Held ↔ ledger.Held := by
    unfold Ledger.Held
    rw [position, agree.bidSlot, agree.payments, agree.bidBuilder, agree.bidValue]
  have latent : ∀ index, other.Latent index ↔ ledger.Latent index := by
    intro index
    unfold Ledger.Latent
    rw [pending, held, agree.bidBuilder]
  obtain ⟨covered, latent', idle, quiet⟩ := solvent
  refine ⟨⟨fun index builder found => ?_, fun index builder found later => ?_,
    fun index set => ?_, fun waits valued spot payment located found => ?_⟩, ?_⟩
  · rw [owed]
    exact covered index builder (agree.builders ▸ found)
  · rw [owed, agree.bidValue]
    exact latent' index builder (agree.builders ▸ found) ((latent index).mp later)
  · rw [owed, agree.bidValue]
    exact ⟨(idle index fun builder found => set builder (agree.builders ▸ found)).1,
      fun later => (idle index fun builder found => set builder (agree.builders ▸ found)).2
        ((latent index).mp later)⟩
  · rw [position, agree.bidSlot] at located
    rw [agree.payments] at found
    rw [agree.bidValue] at valued
    exact quiet (pending.mp waits) valued spot payment located found
  · unfold Ledger.Shaped at shaped ⊢
    rw [agree.bidValue, agree.bidSlot, agree.headerSlot, agree.slot]
    rcases shaped with zero | ⟨waits, same, early⟩
    · exact .inl zero
    · exact .inr ⟨pending.mpr waits, same, early⟩

/-- After the upgrade to Gloas the ledger is solvent and shaped.

No builder owes anything, and the latest bid is the latest payload, already applied, of no value. -/
theorem solvent_upgradeToGloas {pre : BeaconState preset .fusaka}
    {post : BeaconState preset .glamsterdam}
    (computed : upgradeToGloas config checks pre = .ok post) :
    (ledgerOf post (by decide)).Solvent ∧ (ledgerOf post (by decide)).Shaped := by
  unfold upgradeToGloas at computed
  obtain ⟨root, -, rest⟩ := bind_ok_iff.mp computed
  obtain ⟨window, -, onboarded⟩ := bind_ok_iff.mp rest
  obtain ⟨⟨builders, pending, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
  -- No builder owes anything: the queue and the payments are empty.
  have owed : ∀ index, (ledgerOf { { upgradeFields config pre root with
      ptcWindow := fun _ => window } with builders := builders, pendingDeposits := pending }
        (by decide)).owed index = 0 := by
    intro index
    simp only [Ledger.owed, ledgerOf, upgradeFields, RootedVector.elements_ofVector,
      Vector.toList_replicate]
    simp [owedBy, BuilderPendingPayment.empty]
  have applied : ¬ (ledgerOf { { upgradeFields config pre root with
      ptcWindow := fun _ => window } with builders := builders, pendingDeposits := pending }
        (by decide)).Pending := by
    simp [Ledger.Pending, ledgerOf, upgradeFields, upgradeBid]
  refine ⟨Ledger.Covered.solvent ⟨fun index builder _ => by rw [owed]; exact Nat.zero_le _,
    fun index _ => owed index⟩ applied, .inl rfl⟩

/-- From Gloas, the ledger of a forked state is solvent and shaped.

Before Gloas there are no builders, so it holds. -/
def BuilderSolvent (forked : ForkedBeaconState preset) : Prop :=
  ∀ gloas : .glamsterdam ≤ forked.fork,
    (ledgerOf forked.state gloas).Solvent ∧ (ledgerOf forked.state gloas).Shaped

/-- The registries of validators and of builders of a forked state are below `2^40`. -/
def RegistriesBelow (forked : ForkedBeaconState preset) : Prop :=
  forked.state.validators.data.size ≤ 2 ^ 40 ∧
    ∀ gloas : .glamsterdam ≤ forked.fork, (forked.state.builders gloas).data.size ≤ 2 ^ 40

/-- An upgrade keeps the ledger solvent, or starts it solvent at Gloas. -/
theorem builderSolvent_upgradeNext {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) (holds : BuilderSolvent pre) :
    BuilderSolvent post.val := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  -- Before Gloas no state has builders.
  · obtain ⟨_, _, rfl⟩ := computed
    exact fun gloas => absurd gloas (by simp only; decide)
  · subst computed
    exact fun gloas => absurd gloas (by simp only; decide)
  · subst computed
    exact fun gloas => absurd gloas (by simp only; decide)
  · subst computed
    exact fun gloas => absurd gloas (by simp only; decide)
  · obtain ⟨_, _, rfl⟩ := computed
    exact fun gloas => absurd gloas (by simp only; decide)
  · obtain ⟨_, _, rfl⟩ := computed
    exact fun gloas => absurd gloas (by simp only; decide)
  -- The upgrade to Gloas starts the ledger solvent.
  · obtain ⟨_, upgraded, rfl⟩ := computed
    exact fun _ => solvent_upgradeToGloas upgraded
  -- The upgrade to Heze carries every part of the ledger.
  · obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    intro _
    obtain ⟨solvent, shaped⟩ := holds (show Fork.glamsterdam ≤ Fork.glamsterdam by decide)
    have agree : (ledgerOf state (show Fork.glamsterdam ≤ Fork.glamsterdam by decide)).Agree
        (ledgerOf (upgradeHezeFields config state)
          (show Fork.glamsterdam ≤ Fork.hegota by decide)) :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact agree.solvent solvent shaped

/-- Along every run from a state whose builders can pay what they owe, they still can.

Every state of the run must have registries below `2^40`.

Then a withdrawal names a builder or a validator, never both. -/
theorem Run.builderSolvent (pp : PaymentPreset preset) {start : ForkedBeaconState preset} :
    ∀ {after : ForkedBeaconState preset} (run : Run config checks start after),
      (∀ forked ∈ run.states, RegistriesBelow forked) → BuilderSolvent start →
      BuilderSolvent after
  | _, .nil, _, holds => holds
  | after, .snoc (middle := middle) run step, below, holds => by
    have earlier : ∀ forked ∈ run.states, forked ∈ (Run.snoc run step).states :=
      fun _ member => List.mem_append_left _ member
    have middleIn : middle ∈ (Run.snoc run step).states := earlier _ (Run.end_mem_states run)
    have afterIn : after ∈ (Run.snoc run step).states :=
      List.mem_append_right _ (List.mem_singleton_self _)
    have before := Run.builderSolvent pp run
      (fun forked member => below forked (earlier forked member)) holds
    cases step with
    | slot _ computed =>
      exact fun gloas => solvent_advanceSlot pp gloas computed (before gloas).1 (before gloas).2
    | upgrade _ computed => exact builderSolvent_upgradeNext computed before
    | block _ _ _ _ computed =>
      exact fun gloas => solvent_processBlock pp gloas (applySignedBlock_ok computed).2.1
        (before gloas).1 (before gloas).2 (below _ middleIn).1 ((below _ afterIn).2 gloas)

/-- Along every run from a genesis state, builders can pay what they owe.

A genesis state is of Phase 0, which has no builders. -/
theorem Run.builderSolvent_of_genesis (pp : PaymentPreset preset)
    {start after : ForkedBeaconState preset} (genesis : Genesis config checks start)
    (run : Run config checks start after) (below : ∀ forked ∈ run.states, RegistriesBelow forked) :
    BuilderSolvent after := by
  obtain ⟨⟨_, _, _, initialized⟩, _⟩ := genesis
  have early : start.fork < .altair := by
    unfold initializeBeaconStateFromEth1 at initialized
    split at initialized
    · cases initialized
    · exact Nat.lt_of_not_le ‹_›
  exact run.builderSolvent pp below fun gloas =>
    absurd (Nat.lt_of_lt_of_le early (Nat.le_trans (by decide) gloas)) (Nat.lt_irrefl _)

/-- Along every run from a genesis state, a builder can pay what it owes.

Its queued withdrawals and pending payments take at most its balance.

So the withdrawals of a builder never take more than its balance, and never stop at zero early. -/
theorem Run.owed_le_balance (pp : PaymentPreset preset)
    {start after : ForkedBeaconState preset} (genesis : Genesis config checks start)
    (run : Run config checks start after) (below : ∀ forked ∈ run.states, RegistriesBelow forked)
    (gloas : .glamsterdam ≤ after.fork) {index : BuilderIndex} {builder : Builder}
    (found : (after.state.builders gloas).data[index.toNat]? = some builder) :
    pendingBuilderTotal after.state gloas index ≤ builder.balance.toNat :=
  ((Run.builderSolvent_of_genesis pp genesis run below) gloas).1.covered index builder found

end EthLib.Consensus
