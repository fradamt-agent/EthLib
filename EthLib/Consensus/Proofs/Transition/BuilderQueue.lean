module

public import EthLib.Consensus.Proofs.Transition.BuilderSolvency

/-!
# Proofs: how fast the queue of builder withdrawals grows, from Gloas

From Gloas the payments of bids join a queue of builder withdrawals, as [EIP-7732] specifies.

Two rules add to the queue.

A block that applies the payload of its parent settles the payment of the parent bid.

That adds at most one withdrawal.

The end of an epoch releases the payments of the epoch before that reach a quorum.

That adds at most one withdrawal per slot of an epoch.

Only the withdrawals of a block whose parent is full take entries out of the queue.

A block needs a slot of its own, after the slot of the latest block header.

So over a run the queue grows by at most one entry per slot, and one more.

It also grows by at most one entry per slot of an epoch, at each epoch that ends.

That is at most `2 * SLOTS_PER_EPOCH` entries per epoch, and one more.

The queue has no limit on its length, and no rule drains it while payloads are withheld.

What the queue holds for each builder is at most the balance of that builder.

`Run.owed_le_balance` shows it.

[EIP-7732]: https://eips.ethereum.org/EIPS/eip-7732#beacon-chain-changes
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {engine : ExecutionEngine preset fork}
  {state after : BeaconState preset fork}

/-- A later state of the same fork with the same slot and latest header slot.

Its queue of builder withdrawals is at most as long. -/
structure QueueKept (state after : BeaconState preset fork) : Prop where
  slot : after.slot = state.slot
  header : after.latestBlockHeader.slot = state.latestBlockHeader.slot
  queue : ∀ gloas, (ledgerOf after gloas).queue.length ≤ (ledgerOf state gloas).queue.length

namespace QueueKept

theorem refl (state : BeaconState preset fork) : QueueKept state state :=
  ⟨rfl, rfl, fun _ => Nat.le_refl _⟩

theorem trans {first second third : BeaconState preset fork}
    (one : QueueKept first second) (two : QueueKept second third) : QueueKept first third :=
  ⟨two.slot.trans one.slot, two.header.trans one.header,
    fun gloas => Nat.le_trans (two.queue gloas) (one.queue gloas)⟩

/-- A step that keeps the ledger keeps the queue. -/
theorem of_ledger (gloas : .glamsterdam ≤ fork) (kept : LedgerKept state after) :
    QueueKept state after :=
  ⟨congrArg Ledger.slot (kept.same gloas), congrArg Ledger.headerSlot (kept.same gloas),
    fun gloas => Nat.le_of_eq (by rw [kept.same gloas])⟩

/-- A step of the operations keeps the queue. -/
theorem of_ops (gloas : .glamsterdam ≤ fork) (kept : OpsKept state after) :
    QueueKept state after := by
  have frame := kept.frame
  refine ⟨?_, ?_, fun gloas' => ?_⟩
  · have same := congrArg Ledger.slot (frame gloas)
    exact same
  · have same := congrArg Ledger.headerSlot (frame gloas)
    exact same
  · have same : (ledgerOf after gloas').queue = (ledgerOf state gloas').queue := by
      have same := congrArg Ledger.queue (frame gloas')
      exact same
    rw [same]
    exact Nat.le_refl _

end QueueKept


/-! ## The steps of a block -/

/-- Settling the payment of the parent adds at most one withdrawal to the queue. -/
theorem queue_settleParentPayment {gloas : .glamsterdam ≤ fork}
    (computed : settleParentPayment state gloas = .ok after) :
    after.slot = state.slot ∧ after.latestBlockHeader.slot = state.latestBlockHeader.slot ∧
      ∀ gloas', (ledgerOf after gloas').queue.length ≤
        (ledgerOf state gloas').queue.length + 1 := by
  unfold settleParentPayment at computed
  split at computed
  · have settled := liftAccessor_ok.mp computed
    obtain ⟨inRange, _, withdrawals⟩ := settleBuilderPayment_spec settled
    have shape : after.slot = state.slot ∧
        after.latestBlockHeader.slot = state.latestBlockHeader.slot := by
      unfold settleBuilderPayment at settled
      split at settled
      · cases settled
        exact ⟨rfl, rfl⟩
      · rename_i outside
        exact absurd inRange outside
    refine ⟨shape.1, shape.2, fun gloas' => ?_⟩
    obtain rfl : gloas = gloas' := rfl
    have length := congrArg List.length withdrawals
    simp only [ledgerOf] at length ⊢
    rw [length, List.length_append]
    split <;> simp
  · simp only at computed
    split at computed
    · cases computed
      refine ⟨rfl, rfl, fun gloas' => ?_⟩
      obtain rfl : gloas = gloas' := rfl
      simp [ledgerOf]
    · cases computed
      exact ⟨rfl, rfl, fun _ => Nat.le_succ _⟩

/-- The payload of the parent adds at most one withdrawal to the queue. -/
theorem queue_processParentExecutionPayload (slots : 1 < preset.SLOTS_PER_EPOCH.toNat)
    {gloas : .glamsterdam ≤ fork} {body : BeaconBlockBody preset fork}
    (computed : processParentExecutionPayload config checks state gloas body = .ok after) :
    after.slot = state.slot ∧ after.latestBlockHeader.slot = state.latestBlockHeader.slot ∧
      (ledgerOf after gloas).queue.length ≤ (ledgerOf state gloas).queue.length + 1 := by
  unfold processParentExecutionPayload at computed
  dsimp only at computed
  split at computed
  · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, rfl⟩ := computed
    exact ⟨rfl, rfl, Nat.le_succ _⟩
  simp only [bind_ok_iff] at computed
  obtain ⟨_, _, _, _, applied⟩ := computed
  unfold applyParentExecutionPayload at applied
  simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at applied
  obtain ⟨_, _, _, _, _, _, _, _, settled, settledOk, requested, requestedOk, _, _, rfl⟩ :=
    applied
  obtain ⟨settledSlot, settledHeader, settledQueue⟩ := queue_settleParentPayment settledOk
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
  have frame := requests.frame gloas
  have slot : requested.slot = settled.slot := by
    have same := congrArg Ledger.slot frame
    exact same
  have header : requested.latestBlockHeader.slot = settled.latestBlockHeader.slot := by
    have same := congrArg Ledger.headerSlot frame
    exact same
  have queue : (ledgerOf requested gloas).queue = (ledgerOf settled gloas).queue := by
    have same := congrArg Ledger.queue frame
    exact same
  refine ⟨slot.trans settledSlot, header.trans settledHeader, ?_⟩
  have := settledQueue gloas
  change (ledgerOf requested gloas).queue.length ≤ _
  rw [queue]
  exact this

/-- The withdrawals of a block only take entries out of the queue. -/
theorem queueKept_processWithdrawals (gloas : .glamsterdam ≤ fork) {capella : .shapella ≤ fork}
    {payload : Until .glamsterdam fork (ExecutionPayload preset fork)}
    (computed : processWithdrawals state capella payload = .ok after) : QueueKept state after := by
  unfold processWithdrawals at computed
  simp only [gloas, ↓reduceDIte] at computed
  split at computed
  swap
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact .refl _
  obtain ⟨expected, _, appliedOk⟩ := bind_ok_iff.mp computed
  rw [liftAccessor_ok] at appliedOk
  obtain ⟨applied, foldOk, ledgerEq⟩ := applyExpectedWithdrawals_ledger gloas appliedOk
  obtain ⟨frame, -, -⟩ := foldlM_applyWithdrawal_ledger gloas _ _ _ foldOk
  have slot := congrArg Ledger.slot ledgerEq
  have header := congrArg Ledger.headerSlot ledgerEq
  have slot' : applied.slot = state.slot := by
    have same := congrArg Ledger.slot frame
    exact same
  have header' : applied.latestBlockHeader.slot = state.latestBlockHeader.slot := by
    have same := congrArg Ledger.headerSlot frame
    exact same
  have queue' : (ledgerOf applied gloas).queue = (ledgerOf state gloas).queue := by
    have same := congrArg Ledger.queue frame
    exact same
  refine ⟨slot.trans slot', header.trans header', fun gloas' => ?_⟩
  obtain rfl : gloas = gloas' := rfl
  rw [ledgerEq]
  simp only [List.length_drop, queue']
  omega

/-- The bid of a block keeps the queue. -/
theorem queueKept_processExecutionPayloadBid (gloas : .glamsterdam ≤ fork)
    {signed : SignedExecutionPayloadBid preset fork}
    (computed : processExecutionPayloadBid config checks state gloas signed = .ok after) :
    QueueKept state after := by
  simp only [processExecutionPayloadBid, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, recorded, recordedOk, rfl⟩ := computed
  unfold recordBidPayment at recordedOk
  split at recordedOk
  · simp only [bind_ok_iff, liftAccessor_ok, pure, Except.pure, Except.ok.injEq] at recordedOk
    obtain ⟨_, _, _, _, rfl⟩ := recordedOk
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩
  · simp only [pure, Except.pure, Except.ok.injEq] at recordedOk
    subst recordedOk
    exact ⟨rfl, rfl, fun _ => Nat.le_refl _⟩

/-- A block adds at most one withdrawal to the queue.

It needs a slot after that of the latest header, and leaves the header at its own slot. -/
theorem queue_processBlock (pp : PaymentPreset preset)
    (gloas : .glamsterdam ≤ fork) {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    after.slot = state.slot ∧ state.latestBlockHeader.slot < state.slot ∧
      after.latestBlockHeader.slot = after.slot ∧
      (ledgerOf after gloas).queue.length ≤ (ledgerOf state gloas).queue.length + 1 := by
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
  obtain ⟨paidSlot, paidHeader, paidQueue⟩ := queue_processParentExecutionPayload slots paidOk
  -- The header needs a slot after the latest one, and moves to the slot of the block.
  have newer : paid.latestBlockHeader.slot < block.slot := by
    simp only [processBlockHeader, bind_ok_iff, ensure_ok_iff] at headedOk
    obtain ⟨_, _, _, newer, -⟩ := headedOk
    exact newer
  have headerSlot := processBlockHeader_slot headedOk
  obtain ⟨_, _, headedEq⟩ := processBlockHeader_eq headedOk
  have headedSlot : headed.slot = paid.slot := by rw [headedEq]
  have headedHeader : headed.latestBlockHeader.slot = block.slot := by rw [headedEq]
  have headedQueue : (ledgerOf headed gloas).queue = (ledgerOf paid gloas).queue := by
    rw [headedEq]
    rfl
  -- The execution part keeps the queue.
  have executedKept : QueueKept headed executed := by
    unfold processBlockExecution at executedOk
    simp only [gloas, ↓reduceDIte] at executedOk
    obtain ⟨withdrawn, withdrawnOk, bidOk⟩ := bind_ok_iff.mp executedOk
    exact (queueKept_processWithdrawals gloas withdrawnOk).trans
      (queueKept_processExecutionPayloadBid gloas bidOk)
  have votedKept : LedgerKept revealed voted := by
    split at votedOk
    · exact ledgerKept_processEth1Data votedOk
    · cases votedOk
      exact .refl _
  have rest : QueueKept headed after :=
    executedKept.trans <| (QueueKept.of_ledger gloas (ledgerKept_processRandao revealedOk)).trans <|
      (QueueKept.of_ledger gloas votedKept).trans <|
      (QueueKept.of_ops gloas (opsKept_processOperations pp operatedOk)).trans
      (QueueKept.of_ledger gloas (ledgerKept_processSyncAggregate synced))
  obtain ⟨restSlot, restHeader, restQueue⟩ := rest
  refine ⟨restSlot.trans (headedSlot.trans paidSlot),
    by rw [← paidHeader, ← paidSlot, ← headerSlot]; exact newer,
    by rw [restHeader, restSlot, headedHeader, headedSlot, headerSlot], ?_⟩
  have := restQueue gloas
  rw [headedQueue] at this
  omega

/-! ## Slots and runs -/

/-- Whether the slot of the latest block header is before the slot of a state.

Then the state may still take a block at its slot. -/
def blockRoom (state : BeaconState preset fork) : Nat :=
  if state.latestBlockHeader.slot < state.slot then 1 else 0

/-- A slot step adds no withdrawal within an epoch, and at most one per slot of an epoch at its end.

The slot moves on by one, and the latest header stays. -/
theorem queue_advanceSlot (pp : PaymentPreset preset) (gloas : .glamsterdam ≤ fork)
    (computed : advanceSlot config checks state = .ok after) :
    after.slot.toNat = state.slot.toNat + 1 ∧
      after.latestBlockHeader.slot = state.latestBlockHeader.slot ∧
      (ledgerOf after gloas).queue.length + state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat *
          preset.SLOTS_PER_EPOCH.toNat ≤
        (ledgerOf state gloas).queue.length +
          after.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat := by
  have slots := pp.slots
  simp only [advanceSlot, bind_ok_iff, liftAccessor_ok, liftArith, mapError_ok_iff,
    addChecked_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨next, ⟨_, sum⟩, cached, cachedOk, epoched, epochedOk, rfl⟩ := computed
  replace sum : next.toNat = state.slot.toNat + 1 := by simpa using sum
  have cachedKept : LedgerKept state cached := ledgerKept_processSlot cachedOk
  have header : cached.latestBlockHeader.slot = state.latestBlockHeader.slot :=
    congrArg Ledger.headerSlot (cachedKept.same gloas)
  unfold epochIfLast at epochedOk
  split at epochedOk
  · -- The end of an epoch queues at most the payments of one epoch.
    rename_i boundary
    have boundaryNat : next.toNat % preset.SLOTS_PER_EPOCH.toNat = 0 := by
      have := congrArg UInt64.toNat boundary
      simpa [UInt64.toNat_mod] using this
    obtain ⟨quorum, _, epochLedger⟩ := ledgerOf_processEpoch pp gloas epochedOk
    have last := div_last (n := next.toNat) (by omega) boundaryNat (by omega)
    rw [sum, Nat.add_sub_cancel] at last
    have queue : (ledgerOf { epoched with slot := next } gloas).queue.length ≤
        (ledgerOf state gloas).queue.length + preset.SLOTS_PER_EPOCH.toNat := by
      change (ledgerOf epoched gloas).queue.length ≤ _
      rw [epochLedger, cachedKept.same gloas]
      simp only [Ledger.epochStep, releasedPayments, List.length_append, List.length_map]
      have := List.length_filter_le (fun payment : BuilderPendingPayment =>
        decide (quorum ≤ payment.weight))
        ((ledgerOf state gloas).payments.take preset.SLOTS_PER_EPOCH.toNat)
      have := List.length_take_le preset.SLOTS_PER_EPOCH.toNat (ledgerOf state gloas).payments
      omega
    have epochHeader : epoched.latestBlockHeader.slot = cached.latestBlockHeader.slot := by
      have same := congrArg Ledger.headerSlot epochLedger
      exact same
    refine ⟨sum, epochHeader.trans header, ?_⟩
    simp only
    rw [sum, ← last, Nat.add_mul, Nat.one_mul]
    omega
  · -- Any other slot keeps the epoch and the queue.
    rename_i notBoundary
    simp only [pure, Except.pure, Except.ok.injEq] at epochedOk
    subst epochedOk
    have notDvd : ¬ preset.SLOTS_PER_EPOCH.toNat ∣ state.slot.toNat + 1 := by
      intro dvd
      apply notBoundary
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_mod, sum, UInt64.toNat_zero]
      exact Nat.mod_eq_zero_of_dvd dvd
    refine ⟨sum, header, ?_⟩
    simp only
    rw [sum, Nat.succ_div_of_not_dvd notDvd]
    have queue : (ledgerOf { cached with slot := next } gloas).queue =
        (ledgerOf state gloas).queue := by
      change (ledgerOf cached gloas).queue = _
      rw [cachedKept.same gloas]
    rw [queue]
    exact Nat.le_refl _

/-- An upgrade from Gloas on carries the slot, the latest header and the queue. -/
theorem upgradeNext_queue {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (gloas : .glamsterdam ≤ pre.fork) (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.slot = pre.state.slot ∧
      post.val.state.latestBlockHeader.slot = pre.state.latestBlockHeader.slot ∧
      ∀ gloas', (ledgerOf post.val.state gloas').queue.length =
        (ledgerOf pre.state gloas).queue.length := by
  obtain ⟨fork, state⟩ := pre
  cases fork <;>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq, throw,
      throwThe, MonadExceptOf.throw, reduceCtorEq] at computed
  all_goals try exact absurd gloas (by simp only; decide)
  obtain ⟨_, upgraded, rfl⟩ := computed
  obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
  exact ⟨rfl, rfl, fun _ => rfl⟩

/-- Along every run from a state of Gloas, the queue of builder withdrawals grows slowly.

Take the number of slots and of epochs that the run moves on.

The queue grows by at most one entry per slot that the run moves on.

It grows by at most `SLOTS_PER_EPOCH` entries per epoch that ends.

It grows by one more entry for a block at the first slot. -/
theorem Run.queue_le (pp : PaymentPreset preset) {start : ForkedBeaconState preset}
    (gloas : .glamsterdam ≤ start.fork) :
    ∀ {after : ForkedBeaconState preset} (_ : Run config checks start after)
      (gloas' : .glamsterdam ≤ after.fork),
      (ledgerOf after.state gloas').queue.length + blockRoom after.state + start.state.slot.toNat +
          start.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat ≤
        (ledgerOf start.state gloas).queue.length + blockRoom start.state +
          after.state.slot.toNat +
          after.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat * preset.SLOTS_PER_EPOCH.toNat
  | _, .nil, _ => Nat.le_refl _
  | after, .snoc (middle := middle) run step, gloas' => by
    have slots : 1 < preset.SLOTS_PER_EPOCH.toNat := by have := pp.slots; omega
    have middleGloas : .glamsterdam ≤ middle.fork :=
      Nat.le_trans gloas (Reaches.builders slots ⟨run⟩).fork_le
    have before := Run.queue_le pp gloas run middleGloas
    cases step with
    | @slot _ current _ _ computed =>
      obtain ⟨slot, header, queue⟩ := queue_advanceSlot pp middleGloas computed
      simp only at queue slot header before ⊢
      unfold blockRoom at before ⊢
      rw [header]
      -- A slot step leaves room for a block whenever there was room before.
      have room : ∀ (old new : Slot) (latest : Slot), new.toNat = old.toNat + 1 →
          (if latest < old then 1 else 0) ≤ (if latest < new then 1 else 0) := by
        intro old new latest step
        by_cases early : latest < old
        · have later : latest < new := by
            rw [UInt64.lt_iff_toNat_lt] at early ⊢
            omega
          simp [early, later]
        · simp only [early, ↓reduceIte]
          exact Nat.zero_le _
      have := room _ _ current.latestBlockHeader.slot slot
      split at this <;> split at this <;> split <;> split at before <;> omega
    | upgrade _ computed =>
      obtain ⟨slot, header, queue⟩ := upgradeNext_queue middleGloas computed
      unfold blockRoom at before ⊢
      rw [slot, header, queue gloas']
      exact before
    | block _ _ _ _ computed =>
      obtain ⟨slot, newer, header, queue⟩ :=
        queue_processBlock pp middleGloas (applySignedBlock_ok computed).2.1
      simp only at slot newer header queue before ⊢
      unfold blockRoom at before ⊢
      rw [header, slot]
      simp only [newer, ↓reduceIte, UInt64.lt_irrefl] at before ⊢
      omega

/-- Along every run from a state of Gloas, the queue of builder withdrawals grows slowly.

It grows by at most `2 * SLOTS_PER_EPOCH` entries per epoch that the run moves on.

It may grow by `SLOTS_PER_EPOCH + 1` entries more, for the first epoch. -/
theorem Run.queue_le_epochs (pp : PaymentPreset preset) {start after : ForkedBeaconState preset}
    (run : Run config checks start after) (gloas : .glamsterdam ≤ start.fork)
    (gloas' : .glamsterdam ≤ after.fork) :
    (ledgerOf after.state gloas').queue.length ≤
      (ledgerOf start.state gloas).queue.length + 1 + preset.SLOTS_PER_EPOCH.toNat +
        2 * preset.SLOTS_PER_EPOCH.toNat *
          (after.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat -
            start.state.slot.toNat / preset.SLOTS_PER_EPOCH.toNat) := by
  have slots : 1 < preset.SLOTS_PER_EPOCH.toNat := by have := pp.slots; omega
  have bound := Run.queue_le pp gloas run gloas'
  have later := UInt64.le_iff_toNat_le.mp ((Reaches.builders slots ⟨run⟩).slot gloas)
  set count := preset.SLOTS_PER_EPOCH.toNat
  set first := start.state.slot.toNat
  set last := after.state.slot.toNat
  have firstSplit := Nat.div_add_mod first count
  have lastSplit := Nat.div_add_mod last count
  have firstMod := Nat.mod_lt first (show 0 < count by omega)
  have lastMod := Nat.mod_lt last (show 0 < count by omega)
  have epochs : first / count ≤ last / count := Nat.div_le_div_right later
  have room : blockRoom start.state ≤ 1 := by unfold blockRoom; split <;> omega
  -- The slots of the run fit in its epochs, and one more.
  have spread : last / count * count - first / count * count =
      count * (last / count - first / count) := by
    rw [Nat.mul_comm (last / count), Nat.mul_comm (first / count), ← Nat.mul_sub]
  rw [Nat.mul_comm (last / count) count, Nat.mul_comm (first / count) count] at spread
  have mono : count * (first / count) ≤ count * (last / count) := Nat.mul_le_mul_left _ epochs
  rw [Nat.mul_assoc]
  rw [Nat.mul_comm (last / count) count, Nat.mul_comm (first / count) count] at bound
  omega

end EthLib.Consensus
