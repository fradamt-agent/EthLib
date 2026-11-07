module

public import EthLib.Consensus.Proofs.Transition.Operations
public import EthLib.Consensus.Transition.EpochPending

/-!
# Proofs: the pending deposits of an epoch

The pending deposits of an epoch keep one balance for each validator.

The queue never grows.

A pass never credits more inside the churn than the churn available.

A pass reads a prefix of the queue, applies some of it in order, and postpones the others.

So the queue splits into the deposits added to the balances, those dropped, and the queue after.

The balances plus the amounts in the queue never rise.

From Gloas, the churn of deposits is the churn of activations alone.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- The credits and postponements of a consumed prefix, in queue order.

The amount `charged` counts only deposits to targets that are neither withdrawn nor exiting.

Each target status is read from the state at that deposit, not the initial state.

EIP-7251, Consensus layer, introduces the balance-based pending-deposit queue.

The stop predicate must be false before any credit or postponement. -/
inductive PendingDepositTrace (config : Config) (checks : SignatureChecks)
    (stop : PendingDeposit → Bool) (nextEpoch : Epoch) :
    BeaconState preset fork → List PendingDeposit → BeaconState preset fork →
      Array PendingDeposit → Nat → Prop where
  | nil (state : BeaconState preset fork) :
      PendingDepositTrace config checks stop nextEpoch state [] state #[] 0
  | withdrawn {state credited after deposit rest postponed charged}
      (ready : stop deposit = false)
      (withdrawn : (depositTargetStatus state nextEpoch deposit.pubkey).2 = true)
      (applied : applyPendingDeposit config checks state deposit = .ok credited)
      (tail : PendingDepositTrace config checks stop nextEpoch credited rest after
        postponed charged) :
      PendingDepositTrace config checks stop nextEpoch state (deposit :: rest) after
        postponed charged
  | exiting {state after deposit rest postponed charged}
      (ready : stop deposit = false)
      (withdrawn : (depositTargetStatus state nextEpoch deposit.pubkey).2 = false)
      (exited : (depositTargetStatus state nextEpoch deposit.pubkey).1 = true)
      (tail : PendingDepositTrace config checks stop nextEpoch state rest after
        postponed charged) :
      PendingDepositTrace config checks stop nextEpoch state (deposit :: rest) after
        (#[deposit] ++ postponed) charged
  | charged {state credited after deposit rest postponed amount}
      (ready : stop deposit = false)
      (withdrawn : (depositTargetStatus state nextEpoch deposit.pubkey).2 = false)
      (exited : (depositTargetStatus state nextEpoch deposit.pubkey).1 = false)
      (applied : applyPendingDeposit config checks state deposit = .ok credited)
      (tail : PendingDepositTrace config checks stop nextEpoch credited rest after
        postponed amount) :
      PendingDepositTrace config checks stop nextEpoch state (deposit :: rest) after
        postponed (deposit.amount.toNat + amount)

/-- Every consumed entry passes the stop predicate, including withdrawn and exiting targets. -/
theorem PendingDepositTrace.ready {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {deposits : List PendingDeposit} {postponed : Array PendingDeposit} {charged : Nat}
    (trace : PendingDepositTrace config checks stop nextEpoch state deposits after
      postponed charged) : ∀ deposit ∈ deposits, stop deposit = false := by
  induction trace with
  | nil => simp
  | withdrawn ready _ _ _ ih | exiting ready _ _ _ ih | charged ready _ _ _ _ ih =>
    intro deposit member
    rcases List.mem_cons.mp member with rfl | member
    · exact ready
    · exact ih deposit member

/-- Postponed entries form a subsequence of the consumed prefix, with duplicates preserved. -/
theorem PendingDepositTrace.postponed_sublist {stop : PendingDeposit → Bool}
    {nextEpoch : Epoch} {deposits : List PendingDeposit} {postponed : Array PendingDeposit}
    {charged : Nat}
    (trace : PendingDepositTrace config checks stop nextEpoch state deposits after
      postponed charged) : postponed.toList.Sublist deposits := by
  induction trace with
  | nil => exact .refl _
  | withdrawn _ _ _ _ ih | charged _ _ _ _ _ ih => exact ih.cons _
  | @exiting _ _ deposit _ _ _ _ _ _ _ ih =>
    simpa only [Array.toList_append, Array.toList_push, Array.toList_empty, List.singleton_append]
      using ih.cons_cons deposit

/-- A successful pass consumes a bounded prefix and preserves its untouched suffix.

The trace records the postponed entries in order and the exact amount charged to churn.

An initial count within the epoch limit leaves at most the remaining number of entries consumed.

The initial postponed entries precede those encountered by this pass. -/
theorem passPendingDeposits_trace {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      count ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat →
      ∃ consumed delayed charged,
        deposits = consumed ++ pass.1.rest ∧
        count + consumed.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧
        pass.1.postponed = postponed ++ delayed ∧
        PendingDepositTrace config checks stop nextEpoch state consumed pass.1.state delayed
          charged ∧
        pass.1.processed.toNat = processed.toNat + charged
  | [], _, _, _, _, _, computed, within => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    cases computed
    exact ⟨[], #[], 0, rfl, by simpa using within, by simp, .nil _, by simp⟩
  | deposit :: rest, state, processed, count, postponed, pass, computed, within => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact ⟨[], #[], 0, rfl, by simpa using within, by simp, .nil _, by simp⟩
    rename_i proceeds
    have gate : (stop deposit ||
        decide (preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ≤ count)) = false := by
      simpa using proceeds
    have ready : stop deposit = false := (Bool.or_eq_false_iff.mp gate).1
    have room : count + 1 ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
      have := (Bool.or_eq_false_iff.mp gate).2
      simp only [decide_eq_false_iff_not] at this
      omega
    split at computed
    · rename_i withdrawn
      split at computed
      · cases computed
      rename_i credited applied
      split at computed
      · cases computed
      rename_i tail passed
      cases computed
      obtain ⟨consumed, delayed, charged, suffix, bound, queue, trace, amount⟩ :=
        passPendingDeposits_trace passed room
      exact ⟨deposit :: consumed, delayed, charged, by simp [suffix],
        by simp only [List.length_cons]; omega,
        queue, .withdrawn ready withdrawn applied trace, amount⟩
    rename_i withdrawn
    split at computed
    · rename_i exited
      split at computed
      · cases computed
      rename_i tail passed
      cases computed
      obtain ⟨consumed, delayed, charged, suffix, bound, queue, trace, amount⟩ :=
        passPendingDeposits_trace passed room
      refine ⟨deposit :: consumed, #[deposit] ++ delayed, charged, by simp [suffix],
        by simp only [List.length_cons]; omega,
        ?_, .exiting ready (by simpa using withdrawn) exited trace, amount⟩
      dsimp only
      rw [queue, Array.push_eq_append, Array.append_assoc]
    rename_i exited
    split at computed
    · cases computed
    rename_i total added
    split at computed
    · cases computed
      exact ⟨[], #[], 0, rfl, by simpa using within, by simp, .nil _, by simp⟩
    split at computed
    · cases computed
    rename_i credited applied
    split at computed
    · cases computed
    rename_i tail passed
    cases computed
    obtain ⟨consumed, delayed, charged, suffix, bound, queue, trace, amount⟩ :=
      passPendingDeposits_trace passed room
    have sum := (addChecked_ok_iff.mp
      (mapError_ok_iff.mp (liftAccessor_ok.mp added))).2
    refine ⟨deposit :: consumed, delayed, deposit.amount.toNat + charged, by simp [suffix],
      by simp only [List.length_cons]; omega, queue,
      .charged ready (by simpa using withdrawn) (by simpa using exited) applied trace, ?_⟩
    dsimp only at amount ⊢
    rw [amount, sum]
    omega

/-- A pass over the pending deposits keeps one balance for each validator. -/
theorem balancesMatch_passPendingDeposits {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      BalancesMatch state → BalancesMatch pass.1.state
  | [], _, _, _, _, _, computed, holds => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact holds
  | deposit :: rest, state, processed, count, postponed, pass, computed, holds => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact holds
    split at computed
    · split at computed
      · cases computed
      rename_i credited
      split at computed
      · cases computed
      cases computed
      exact balancesMatch_passPendingDeposits (deposits := rest) ‹_›
        ((applyPendingDeposit_kept credited).1 holds)
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact balancesMatch_passPendingDeposits (deposits := rest) ‹_› holds
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact holds
    split at computed
    · cases computed
    rename_i credited
    split at computed
    · cases computed
    cases computed
    exact balancesMatch_passPendingDeposits (deposits := rest) ‹_›
      ((applyPendingDeposit_kept credited).1 holds)

/-- A pass that starts within the churn available credits no more than that churn inside it. -/
theorem passPendingDeposits_processed_le {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      processed ≤ available → pass.1.processed ≤ available
  | [], _, _, _, _, _, computed, within => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact within
  | deposit :: rest, state, processed, count, postponed, pass, computed, within => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact within
    split at computed
    · split at computed
      · cases computed
      split at computed
      · cases computed
      cases computed
      exact passPendingDeposits_processed_le (deposits := rest) ‹_› within
    split at computed
    · split at computed
      · cases computed
      cases computed
      exact passPendingDeposits_processed_le (deposits := rest) ‹_› within
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact within
    rename_i fits
    split at computed
    · cases computed
    split at computed
    · cases computed
    cases computed
    exact passPendingDeposits_processed_le (deposits := rest) ‹_›
      (UInt64.not_lt.mp fits)

/-- The pending deposits of an epoch end with a pass over the queue from its front.

The pass reads the next epoch and the churn available.

That churn is the churn left from the last epoch and the churn of deposits.

It stops at a deposit that waits for the first slot of the finalized epoch.

The registry and the balances are those of the pass.

The queue holds the deposits that the pass did not reach, then those it postponed.

Only a stop at the churn limit carries the unused churn to the next epoch. -/
theorem processPendingDeposits_pass {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ∃ nextEpoch churn available finalizedSlot pass,
      liftArith (addChecked (getCurrentEpoch state) 1) = .ok nextEpoch ∧
      depositChurnLimit config state = .ok churn ∧
      liftArith (addChecked (state.depositBalanceToConsume electra) churn) = .ok available ∧
      liftArith (computeStartSlotAtEpoch preset state.finalizedCheckpoint.epoch) =
        .ok finalizedSlot ∧
      passPendingDeposits config checks (depositWaits state finalizedSlot) nextEpoch available
          state 0 0 #[] (state.pendingDeposits electra).data.toList = .ok pass ∧
        after.validators = pass.1.state.validators ∧ after.balances = pass.1.state.balances ∧
        (after.pendingDeposits electra).data = pass.1.rest.toArray ++ pass.1.postponed ∧
        (after.depositBalanceToConsume electra).toNat =
          if pass.1.churnReached then available.toNat - pass.1.processed.toNat else 0 := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  repeat' (split at computed <;> try cases computed)
  all_goals
    refine ⟨_, _, _, _, _, liftAccessor_ok.mp ‹_›, liftAccessor_ok.mp ‹_›,
      liftAccessor_ok.mp ‹_›, liftAccessor_ok.mp ‹_›, ‹_›, rfl, rfl, rfl, ?_⟩
    first
    | simpa only [‹_ = true›, ↓reduceIte] using
        (subChecked_ok_iff.mp (mapError_ok_iff.mp (liftAccessor_ok.mp ‹_›))).2
    | simp_all

/-- From Fulu the finalized slot is the only gate in the stop predicate. -/
theorem depositWaits_of_fulu (fulu : .fusaka ≤ fork) (finalizedSlot : Slot)
    (deposit : PendingDeposit) :
    depositWaits state finalizedSlot deposit = decide (finalizedSlot < deposit.slot) := by
  have notElectra : ¬ (.pectra ≤ fork ∧ fork < .fusaka) :=
    fun h => Nat.not_lt.mpr fulu h.2
  simp [depositWaits, bridgeDepositsPending, notElectra]

/-- A consumed deposit is no later than the finalized slot, at every fork from Electra. -/
theorem PendingDepositTrace.finalized {nextEpoch : Epoch} {finalizedSlot : Slot}
    {deposits : List PendingDeposit} {credited : BeaconState preset fork}
    {postponed : Array PendingDeposit} {charged : Nat}
    (trace : PendingDepositTrace config checks (depositWaits state finalizedSlot) nextEpoch
      state deposits credited postponed charged) :
    ∀ deposit ∈ deposits, deposit.slot ≤ finalizedSlot := by
  intro deposit member
  have ready := trace.ready deposit member
  simp only [depositWaits, Bool.or_eq_false_iff, decide_eq_false_iff_not] at ready
  exact UInt64.not_lt.mp ready.2

/-- Each epoch consumes a bounded prefix, charges it within churn, and retains queue order.

The trace distinguishes withdrawn credits from charged credits and postponed entries.

All consumed entries pass finality and, before Fulu, the bridge gate.

The carry is exact on natural numbers, without wrapping subtraction. -/
theorem processPendingDeposits_spec {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ∃ nextEpoch churn available finalizedSlot pass consumed delayed,
      liftArith (addChecked (getCurrentEpoch state) 1) = .ok nextEpoch ∧
      depositChurnLimit config state = .ok churn ∧
      liftArith (addChecked (state.depositBalanceToConsume electra) churn) = .ok available ∧
      liftArith (computeStartSlotAtEpoch preset state.finalizedCheckpoint.epoch) =
        .ok finalizedSlot ∧
      passPendingDeposits config checks (depositWaits state finalizedSlot) nextEpoch available
          state 0 0 #[] (state.pendingDeposits electra).data.toList = .ok pass ∧
      (state.pendingDeposits electra).data.toList = consumed ++ pass.1.rest ∧
      consumed.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧
      PendingDepositTrace config checks (depositWaits state finalizedSlot) nextEpoch state
        consumed pass.1.state delayed pass.1.processed.toNat ∧
      pass.1.processed ≤ available ∧
      (∀ deposit ∈ consumed, deposit.slot ≤ finalizedSlot) ∧
      after.validators = pass.1.state.validators ∧ after.balances = pass.1.state.balances ∧
      (after.pendingDeposits electra).data = pass.1.rest.toArray ++ delayed ∧
      (after.depositBalanceToConsume electra).toNat =
        if pass.1.churnReached then available.toNat - pass.1.processed.toNat else 0 := by
  obtain ⟨nextEpoch, churn, available, finalizedSlot, pass, next, limit, added, finalized,
    passed, validators, balances, queue, carry⟩ := processPendingDeposits_pass computed
  obtain ⟨consumed, delayed, charged, suffix, bound, postponed, trace, amount⟩ :=
    passPendingDeposits_trace passed (Nat.zero_le _)
  simp only [UInt64.toNat_zero, Nat.zero_add] at amount
  subst charged
  simp only [Array.empty_append] at postponed
  have within := passPendingDeposits_processed_le passed UInt64.zero_le
  refine ⟨nextEpoch, churn, available, finalizedSlot, pass, consumed, delayed, next, limit,
    added, finalized, passed, suffix, by simpa using bound, trace, within, trace.finalized,
    validators, balances, ?_, carry⟩
  simpa only [postponed] using queue

/-- The pending deposits of an epoch keep one balance for each validator. -/
theorem balancesMatch_processPendingDeposits {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (holds : BalancesMatch state) : BalancesMatch after := by
  obtain ⟨_, _, _, _, pass, _, _, _, _, passed, validators, balances, _⟩ :=
    processPendingDeposits_pass computed
  have kept := balancesMatch_passPendingDeposits passed holds
  unfold BalancesMatch at kept ⊢
  rw [validators, balances]
  exact kept

/-- The pending deposits of an epoch leave a queue at most as long as before. -/
theorem processPendingDeposits_size_le {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    (after.pendingDeposits electra).data.size ≤ (state.pendingDeposits electra).data.size := by
  obtain ⟨_, _, _, _, pass, _, _, _, _, passed, _, _, queue, _⟩ :=
    processPendingDeposits_pass computed
  have fits := pass.2
  simp only [Array.size_empty, Nat.add_zero, Array.length_toList] at fits
  rw [queue, Array.size_append, List.size_toArray]
  exact fits

/-- A pass reads a prefix of its deposits, at most what the limit per epoch still allows.

It applies some of those in order, and postpones the others in order. -/
theorem passPendingDeposits_applied {stop : PendingDeposit → Bool} {nextEpoch : Epoch}
    {available : Gwei} :
    ∀ {deposits : List PendingDeposit} {state : BeaconState preset fork} {processed : Gwei}
      {count : Nat} {postponed : Array PendingDeposit} {pass},
      passPendingDeposits config checks stop nextEpoch available state processed count postponed
        deposits = .ok pass →
      ∃ read applied moved : List PendingDeposit,
        deposits = read ++ pass.1.rest ∧
          pass.1.postponed.toList = postponed.toList ++ moved ∧
          read.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat - count ∧
          applied.Sublist read ∧ moved.Sublist read ∧ (applied ++ moved).Perm read ∧
          applied.foldlM (applyPendingDeposit config checks) state = .ok pass.1.state
  | [], _, _, _, _, _, computed => by
    simp only [passPendingDeposits, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    exact ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
      List.Perm.refl _, rfl⟩
  | deposit :: rest, state, processed, count, postponed, pass, computed => by
    unfold passPendingDeposits at computed
    simp only [bind, Except.bind, pure, Except.pure] at computed
    split at computed
    · cases computed
      exact ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
        List.Perm.refl _, rfl⟩
    rename_i continues
    -- The pass reads this deposit, so the count is below the limit per epoch.
    have below : count < preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at continues
      exact continues.2
    split at computed
    · split at computed
      · cases computed
      rename_i step
      split at computed
      · cases computed
      cases computed
      obtain ⟨read, applied, moved, queue, pushed, length, inRead, movedInRead, perm,
        later⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
      refine ⟨deposit :: read, deposit :: applied, moved, congrArg (deposit :: ·) queue, pushed,
        by simp only [List.length_cons]; omega, inRead.cons_cons _, movedInRead.cons _,
        perm.cons deposit, ?_⟩
      simp only [List.foldlM_cons, bind, Except.bind, step]
      exact later
    split at computed
    · split at computed
      · cases computed
      cases computed
      obtain ⟨read, applied, moved, queue, pushed, length, inRead, movedInRead, perm,
        later⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
      refine ⟨deposit :: read, applied, deposit :: moved, congrArg (deposit :: ·) queue, ?_,
        by simp only [List.length_cons]; omega, inRead.cons _, movedInRead.cons_cons _,
        List.perm_middle.trans (perm.cons deposit), later⟩
      -- The deposit waits after those that earlier steps postponed.
      rw [pushed, Array.toList_push, List.append_assoc]
      rfl
    split at computed
    · cases computed
    split at computed
    · cases computed
      exact ⟨[], [], [], rfl, by simp, by simp, List.nil_sublist _, List.nil_sublist _,
        List.Perm.refl _, rfl⟩
    split at computed
    · cases computed
    rename_i step
    split at computed
    · cases computed
    cases computed
    obtain ⟨read, applied, moved, queue, pushed, length, inRead, movedInRead, perm,
      later⟩ := passPendingDeposits_applied (deposits := rest) ‹_›
    refine ⟨deposit :: read, deposit :: applied, moved, congrArg (deposit :: ·) queue, pushed,
      by simp only [List.length_cons]; omega, inRead.cons_cons _, movedInRead.cons _,
      perm.cons deposit, ?_⟩
    simp only [List.foldlM_cons, bind, Except.bind, step]
    exact later

/-- The pending deposits of an epoch read a prefix of the queue, at most the limit per epoch.

They apply some of those in order, and move the others to the end of the queue in order.

The state after is the state of those applied, with a new queue and a new churn left over. -/
theorem processPendingDeposits_applied {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    ∃ (read rest applied postponed : List PendingDeposit) (next : BeaconState preset fork)
        (pending : PendingDeposits preset fork) (carried : Gwei),
      (state.pendingDeposits electra).data.toList = read ++ rest ∧
        pending.data.toList = rest ++ postponed ∧
        read.length ≤ preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat ∧
        applied.Sublist read ∧ postponed.Sublist read ∧ (applied ++ postponed).Perm read ∧
        applied.foldlM (applyPendingDeposit config checks) state = .ok next ∧
        after = { next with
          pendingDeposits := fun _ => pending
          depositBalanceToConsume := fun _ => carried } := by
  unfold processPendingDeposits at computed
  simp only [bind, Except.bind, pure, Except.pure] at computed
  -- Each success ends in the same record, after a pass from count zero with nothing postponed.
  repeat' (split at computed <;> try cases computed)
  all_goals
    obtain ⟨read, applied, postponed, queue, pushed, length, inRead, postponedInRead, perm,
      later⟩ := passPendingDeposits_applied ‹_›
    exact ⟨read, _, applied, postponed, _, _, _, queue, by simpa using pushed,
      by simpa using length, inRead, postponedInRead, perm, later, rfl⟩

/-- The queue before splits into the deposits added, the deposits dropped, and the queue after.

The sum of the balances rises by the amounts added.

Each dropped deposit is droppable at the state before.

That needs one balance for each validator.

It also needs room in 64 bits for the registry and the limit per epoch. -/
theorem processPendingDeposits_partition {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after)
    (holds : BalancesMatch state)
    (room : state.validators.data.size + preset.MAX_PENDING_DEPOSITS_PER_EPOCH.toNat < 2 ^ 64) :
    ∃ added dropped : List PendingDeposit,
      (added ++ dropped ++ (after.pendingDeposits electra).data.toList).Perm
          (state.pendingDeposits electra).data.toList ∧
        (∀ deposit ∈ dropped, DepositDroppable config checks state deposit) ∧
        balanceSum after = balanceSum state + pendingAmount added := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, length, inRead, _,
    perm, later, rfl⟩ := processPendingDeposits_applied computed
  have fits := inRead.length_le
  obtain ⟨added, dropped, split, all, sum⟩ :=
    foldlM_applyPendingDeposit_partition later holds (by omega)
  refine ⟨added, dropped, ?_, all, sum⟩
  change (added ++ dropped ++ pending.data.toList).Perm _
  rw [queue, kept]
  -- The queue before is `read ++ rest`, and `read` holds `applied` and `postponed` together.
  refine (split.append_right _).trans ((List.perm_append_comm.append_left applied).trans ?_)
  rw [← List.append_assoc]
  exact perm.append_right rest

/-- The pending deposits of an epoch never raise the balances plus the amounts in the queue. -/
theorem processPendingDeposits_total_le {electra : .pectra ≤ fork}
    (computed : processPendingDeposits config checks state electra = .ok after) :
    balanceSum after + pendingAmount (after.pendingDeposits electra).data.toList ≤
      balanceSum state + pendingAmount (state.pendingDeposits electra).data.toList := by
  obtain ⟨read, rest, applied, postponed, next, pending, carried, queue, kept, _, _, _, perm,
    later, rfl⟩ := processPendingDeposits_applied computed
  have raised := foldlM_applyPendingDeposit_le later
  have amounts := (perm.map (·.amount.toNat)).sum_nat
  change balanceSum next + pendingAmount pending.data.toList ≤ _
  rw [queue, kept]
  simp only [pendingAmount, List.map_append, List.sum_append_nat] at amounts raised ⊢
  omega

end EthLib.Consensus
