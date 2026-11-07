module

public import EthLib.Base.Except
public import EthLib.Base.Proofs.MapM
public import EthLib.Base.Proofs.Uint64
public import EthLib.Consensus.Churn

/-!
# Proofs: the balance churn

A queue never places an amount before its earliest open epoch, or before the first epoch allowed.

The queue spends exactly the amount.

The churn left plus the amount equals the churn available, plus a full churn for each added epoch.

An amount that needs later epochs takes the fewest, so less than one churn is left in the last.

An amount that fits the churn available always finds its place in the current epoch.

Amounts queued in turn spend exactly their sum, with one full churn for each added epoch.

So the amounts placed up to an epoch take at most the churn left, then a full churn per epoch.

In Electra, the churns of consolidations and of activations and exits add up to the whole churn.

So their difference does not wrap.

From Gloas, the churn of exits is a whole number of increments.

The churn of activations is the churn of exits up to a maximum, and pending deposits take it.

Requests in turn may each have their own churn, since they come from different states.

Take a cap on every churn and on the churn left at the start.

The churn left then stays within the cap.

The balance placed up to an epoch is at most the churn left, plus one cap per later epoch.

In a range of epochs, every request but the first takes at most one cap per epoch.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64

variable {preset : Preset} {fork : Base.Fork}

/-- The queue places an amount no earlier than its earliest open epoch and the first epoch.

The churn left plus the amount equals the churn available at the first open epoch.

Each epoch that the queue adds contributes one more full churn to that sum.

If the queue adds epochs, less than one full churn is left in the last. -/
theorem churnQueue_spend {earliestEpoch firstEpoch perEpochChurn churnLeft amount epoch left :
    UInt64}
    (computed :
      churnQueue earliestEpoch firstEpoch perEpochChurn churnLeft amount = .ok (epoch, left)) :
    max earliestEpoch firstEpoch ≤ epoch ∧
      left.toNat + amount.toNat =
        (if earliestEpoch < max earliestEpoch firstEpoch then perEpochChurn else churnLeft).toNat +
          (epoch.toNat - (max earliestEpoch firstEpoch).toNat) * perEpochChurn.toNat ∧
      (epoch = max earliestEpoch firstEpoch ∨ left.toNat < perEpochChurn.toNat) := by
  unfold churnQueue at computed
  dsimp only at computed
  generalize max earliestEpoch firstEpoch = first at computed ⊢
  generalize (if earliestEpoch < first then perEpochChurn else churnLeft) = available at computed ⊢
  split at computed
  · rename_i fits
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    have fits := UInt64.le_iff_toNat_le.mp fits
    refine ⟨UInt64.le_refl _, ?_, .inl rfl⟩
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr fits)]
    simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    omega
  · rename_i over
    have over : available.toNat < amount.toNat := by
      rw [UInt64.le_iff_toNat_le] at over
      omega
    simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨quotient, divided, later, added, product, multiplied, total, summed, rfl, rfl⟩ :=
      computed
    obtain ⟨nonzero, quotientValue⟩ := divChecked_ok_iff.mp divided
    have positive : 0 < perEpochChurn.toNat := by
      rcases Nat.eq_zero_or_pos perEpochChurn.toNat with zero | positive
      · exact absurd (UInt64.toNat_inj.mp (by simpa using zero)) nonzero
      · exact positive
    -- The rest of the amount, less one, on natural numbers.
    have rest : (amount - available - 1).toNat = amount.toNat - available.toNat - 1 := by
      have difference : (amount - available).toNat = amount.toNat - available.toNat :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt over))
      have one : (1 : UInt64) ≤ amount - available := by
        rw [UInt64.le_iff_toNat_le, difference]
        show 1 ≤ _
        omega
      rw [UInt64.toNat_sub_of_le _ _ one, difference]
      rfl
    rw [rest] at quotientValue
    have quotientSmall : quotient.toNat < amount.toNat := by
      rw [quotientValue]
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have additional : (quotient + 1).toNat = quotient.toNat + 1 := by
      have := amount.toNat_lt
      exact toNat_add_of_lt (by simp; omega)
    obtain ⟨_, laterValue⟩ := addChecked_ok_iff.mp added
    obtain ⟨_, productValue⟩ := mulChecked_ok_iff.mp multiplied
    obtain ⟨_, totalValue⟩ := addChecked_ok_iff.mp summed
    rw [additional] at laterValue productValue
    -- The added epochs cover the rest of the amount, with less than one churn to spare.
    have cover : amount.toNat - available.toNat ≤ (quotient.toNat + 1) * perEpochChurn.toNat ∧
        (quotient.toNat + 1) * perEpochChurn.toNat <
          amount.toNat - available.toNat + perEpochChurn.toNat := by
      rw [quotientValue, Nat.add_mul, Nat.one_mul]
      have below := Nat.div_mul_le_self (amount.toNat - available.toNat - 1) perEpochChurn.toNat
      have above := Nat.lt_div_mul_add (a := amount.toNat - available.toNat - 1) positive
      omega
    have enough : amount ≤ total := by
      rw [UInt64.le_iff_toNat_le, totalValue, productValue]
      omega
    rw [UInt64.toNat_sub_of_le _ _ enough, totalValue, productValue, laterValue]
    refine ⟨UInt64.le_iff_toNat_le.mpr (by omega), ?_, .inr ?_⟩
    · rw [Nat.add_sub_cancel_left]
      omega
    · omega

/-- An amount that fits the churn available takes the first open epoch, and leaves the rest. -/
theorem churnQueue_of_le {earliestEpoch firstEpoch perEpochChurn churnLeft amount : UInt64}
    (fits :
      amount ≤ if earliestEpoch < max earliestEpoch firstEpoch then perEpochChurn else churnLeft) :
    churnQueue earliestEpoch firstEpoch perEpochChurn churnLeft amount =
      .ok (max earliestEpoch firstEpoch,
        (if earliestEpoch < max earliestEpoch firstEpoch then perEpochChurn else churnLeft) -
          amount) := by
  simp only [churnQueue, fits, ↓reduceIte, pure, Except.pure]

/-- The queue reads its state only through the first open epoch and the churn available there.

So it places an amount as it would from that epoch, with that churn left. -/
theorem churnQueue_normalize {earliestEpoch firstEpoch perEpochChurn churnLeft amount : UInt64} :
    churnQueue earliestEpoch firstEpoch perEpochChurn churnLeft amount =
      churnQueue (max earliestEpoch firstEpoch) firstEpoch perEpochChurn
        (if earliestEpoch < max earliestEpoch firstEpoch then perEpochChurn else churnLeft)
        amount := by
  have same : max (max earliestEpoch firstEpoch) firstEpoch = max earliestEpoch firstEpoch := by
    by_cases order : earliestEpoch ≤ firstEpoch
    · simp only [UInt64.max_def, order, ↓reduceIte, UInt64.le_refl]
    · simp only [UInt64.max_def, order, ↓reduceIte]
  simp only [churnQueue, same, UInt64.lt_irrefl, ↓reduceIte]

/-- Amounts queued in turn, from an open epoch no earlier than the first epoch allowed.

The queue never moves back, and it spends exactly the amounts, one full churn per added epoch. -/
private theorem churnQueue_foldlM {firstEpoch perEpochChurn : UInt64} :
    ∀ {amounts : List UInt64} {earliestEpoch churnLeft epoch left : UInt64},
      firstEpoch ≤ earliestEpoch →
      amounts.foldlM (fun (queue : UInt64 × UInt64) amount =>
          churnQueue queue.1 firstEpoch perEpochChurn queue.2 amount)
        (earliestEpoch, churnLeft) = .ok (epoch, left) →
      earliestEpoch ≤ epoch ∧
        left.toNat + (amounts.map UInt64.toNat).sum =
          churnLeft.toNat + (epoch.toNat - earliestEpoch.toNat) * perEpochChurn.toNat
  | [], earliestEpoch, churnLeft, epoch, left, _, computed => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at computed
    obtain ⟨rfl, rfl⟩ := computed
    simp
  | amount :: rest, earliestEpoch, churnLeft, epoch, left, first, computed => by
    simp only [List.foldlM_cons, bind_ok_iff] at computed
    obtain ⟨⟨middle, middleLeft⟩, step, folded⟩ := computed
    have open_ : max earliestEpoch firstEpoch = earliestEpoch := by
      rw [UInt64.max_def]
      split
      · exact UInt64.le_antisymm first ‹_›
      · rfl
    obtain ⟨placed, spent, -⟩ := churnQueue_spend step
    rw [open_] at placed spent
    simp only [UInt64.lt_irrefl, ↓reduceIte] at spent
    obtain ⟨later, total⟩ := churnQueue_foldlM (UInt64.le_trans first placed) folded
    refine ⟨UInt64.le_trans placed later, ?_⟩
    have placed := UInt64.le_iff_toNat_le.mp placed
    have later := UInt64.le_iff_toNat_le.mp later
    have epochs : (middle.toNat - earliestEpoch.toNat) * perEpochChurn.toNat +
        (epoch.toNat - middle.toNat) * perEpochChurn.toNat =
          (epoch.toNat - earliestEpoch.toNat) * perEpochChurn.toNat := by
      rw [← Nat.add_mul]
      congr 1
      omega
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Amounts queued in turn, from an open epoch no earlier than the first epoch allowed.

The last amount takes an epoch no earlier than the open epoch at the start. -/
theorem churnQueue_foldlM_epoch {firstEpoch perEpochChurn earliestEpoch churnLeft epoch left :
    UInt64} {amounts : List UInt64} (first : firstEpoch ≤ earliestEpoch)
    (computed : amounts.foldlM (fun (queue : UInt64 × UInt64) amount =>
        churnQueue queue.1 firstEpoch perEpochChurn queue.2 amount)
      (earliestEpoch, churnLeft) = .ok (epoch, left)) :
    earliestEpoch ≤ epoch :=
  (churnQueue_foldlM first computed).1

/-- Amounts queued in turn, from an open epoch no earlier than the first epoch allowed.

The churn left at the end plus the amounts equals the churn left at the start.

Each epoch that the queue moves past adds one full churn to that sum. -/
theorem churnQueue_foldlM_spend {firstEpoch perEpochChurn earliestEpoch churnLeft epoch left :
    UInt64} {amounts : List UInt64} (first : firstEpoch ≤ earliestEpoch)
    (computed : amounts.foldlM (fun (queue : UInt64 × UInt64) amount =>
        churnQueue queue.1 firstEpoch perEpochChurn queue.2 amount)
      (earliestEpoch, churnLeft) = .ok (epoch, left)) :
    left.toNat + (amounts.map UInt64.toNat).sum =
      churnLeft.toNat + (epoch.toNat - earliestEpoch.toNat) * perEpochChurn.toNat :=
  (churnQueue_foldlM first computed).2

/-- Amounts queued in turn take at most the churn left at the start of the queue.

Each epoch that the queue moves past allows one more full churn.

The epochs never move back, so the amounts placed up to an epoch are the first ones queued.

So the balance placed up to an epoch is at most the churn left, plus a full churn per later epoch.
-/
theorem churnQueue_foldlM_le {firstEpoch perEpochChurn earliestEpoch churnLeft epoch left :
    UInt64} {amounts : List UInt64} (first : firstEpoch ≤ earliestEpoch)
    (computed : amounts.foldlM (fun (queue : UInt64 × UInt64) amount =>
        churnQueue queue.1 firstEpoch perEpochChurn queue.2 amount)
      (earliestEpoch, churnLeft) = .ok (epoch, left)) :
    (amounts.map UInt64.toNat).sum ≤
      churnLeft.toNat + (epoch.toNat - earliestEpoch.toNat) * perEpochChurn.toNat := by
  have := churnQueue_foldlM_spend first computed
  omega

/-- In Electra, the churns of consolidations and of activations and exits add up to the whole churn.
-/
theorem getConsolidationChurnLimit_add {config : Config} {state : BeaconState preset fork}
    {consolidation activationExit whole : Gwei} (before : fork < .glamsterdam)
    (consolidationOk : getConsolidationChurnLimit config state = .ok consolidation)
    (activationExitOk : getActivationExitChurnLimit config state = .ok activationExit)
    (wholeOk : getBalanceChurnLimit config state = .ok whole) :
    consolidation.toNat + activationExit.toNat = whole.toNat := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [getConsolidationChurnLimit, notGloas, ↓reduceIte, bind_ok_iff, wholeOk,
    activationExitOk, pure, Except.pure, Except.ok.injEq, exists_eq_left'] at consolidationOk
  simp only [getActivationExitChurnLimit, bind_ok_iff, wholeOk, pure, Except.pure,
    Except.ok.injEq, exists_eq_left'] at activationExitOk
  subst consolidationOk activationExitOk
  have le : min config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT whole ≤ whole := by
    rw [UInt64.min_def]
    split
    · assumption
    · exact UInt64.le_refl _
  rw [UInt64.toNat_sub_of_le _ _ le]
  have := UInt64.le_iff_toNat_le.mp le
  omega

/-- A balance rounded down to an increment is a whole number of increments. -/
theorem sub_mod_mod_self (balance increment : Gwei) :
    (balance - balance % increment) % increment = 0 := by
  have le : balance % increment ≤ balance := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
    exact Nat.mod_le _ _
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_mod, UInt64.toNat_sub_of_le _ _ le, UInt64.toNat_mod]
  simpa using Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm

/-- From Gloas, the churn of exits is a whole number of effective balance increments. -/
theorem getExitChurnLimit_mod {config : Config} {state : BeaconState preset fork} {exit : Gwei}
    (computed : getExitChurnLimit config state = .ok exit) :
    exit % preset.EFFECTIVE_BALANCE_INCREMENT = 0 := by
  simp only [getExitChurnLimit, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  exact sub_mod_mod_self _ _

/-- From Gloas, the churn of activations is the churn of exits up to its maximum. -/
theorem getActivationChurnLimit_of_exit {config : Config} {state : BeaconState preset fork}
    {exit : Gwei} (exitOk : getExitChurnLimit config state = .ok exit) :
    getActivationChurnLimit config state =
      .ok (min config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS exit) := by
  simp only [getActivationChurnLimit, exitOk, bind, Except.bind, pure, Except.pure]

/-- From Gloas, the pending deposits take the churn of activations. -/
theorem depositChurnLimit_of_gloas {config : Config} {state : BeaconState preset fork}
    (gloas : .glamsterdam ≤ fork) :
    depositChurnLimit config state = getActivationChurnLimit config state := by
  simp only [depositChurnLimit, gloas, ↓reduceIte]

/-- Before Gloas, the pending deposits take the churn that activations and exits share. -/
theorem depositChurnLimit_of_lt {config : Config} {state : BeaconState preset fork}
    (before : fork < .glamsterdam) :
    depositChurnLimit config state = getActivationExitChurnLimit config state := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [depositChurnLimit, notGloas, ↓reduceIte]

/-- The churn update of an exit records its epoch as the earliest open one. -/
theorem computeExitEpochAndUpdateChurn_earliest {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    after.earliestExitEpoch electra = epoch ∧ after.validators = state.validators ∧
      after.balances = state.balances := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, ⟨queued, left⟩, _, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact ⟨rfl, rfl, rfl⟩

/-- The churn update of a consolidation records its epoch as the earliest open one. -/
theorem computeConsolidationEpochAndUpdateChurn_earliest {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    after.earliestConsolidationEpoch electra = epoch ∧ after.validators = state.validators ∧
      after.balances = state.balances := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨_, _, _, _, ⟨queued, left⟩, _, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact ⟨rfl, rfl, rfl⟩

/-- An exit from Electra leaves no earlier than the first epoch an exit may take. -/
theorem computeExitEpochAndUpdateChurn_first {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch firstEpoch : Epoch}
    (first : computeActivationExitEpoch preset (getCurrentEpoch state) = .ok firstEpoch)
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    firstEpoch ≤ epoch ∧ state.earliestExitEpoch electra ≤ epoch := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, first,
    pure, Except.pure, Except.ok.injEq, exists_eq_left'] at computed
  obtain ⟨_, _, ⟨queued, left⟩, queue, final⟩ := computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨_, rfl⟩ := final
  have placed := UInt64.le_iff_toNat_le.mp (churnQueue_spend queue).1
  rw [UInt64.max_def] at placed
  split at placed <;> rename_i order <;> simp only [UInt64.le_iff_toNat_le] at order ⊢ <;>
    omega

/-! ## Requests in turn, each with its own churn

The requests to one queue come from different states.

So the first epoch allowed and the churn of an epoch may change from one request to the next.

Take a cap that bounds the churn of every request, and the churn left at the start.

Each epoch then adds at most one cap to the churn available, since the queue opens it once.

So the balance placed up to an epoch is at most the churn left, plus one cap per later epoch.

The churn left stays at most the cap, so this holds again from every later state of the queue.

In a range of `n` epochs, every request but the first takes at most `n` caps.

The first request in the range may also take churn from epochs before the range.

The cap must bound the churn of earlier requests too, not only the current one.

The churn left at an epoch comes from the request that opened it, whose churn may be larger.

[EIP-7251] specifies the queue of exits and the queue of consolidations this way.

[EIP-7251]: https://eips.ethereum.org/EIPS/eip-7251#consensus-layer-1
-/

/-- One request to a queue: the first epoch it may take, the churn of an epoch, and the amount.
-/
structure ChurnRequest where
  firstEpoch : Epoch
  perEpochChurn : Gwei
  amount : Gwei

/-- Requests that a queue places in turn, each with the epoch it gets.

The queue starts at an earliest open epoch with some churn left there.

It ends at the epoch and the churn left of its last request. -/
inductive ChurnTrace : Epoch → Gwei → List (ChurnRequest × Epoch) → Epoch → Gwei → Prop where
  | nil (earliestEpoch : Epoch) (churnLeft : Gwei) :
    ChurnTrace earliestEpoch churnLeft [] earliestEpoch churnLeft
  | cons {earliestEpoch churnLeft epoch left lastEpoch lastLeft : UInt64}
    {request : ChurnRequest} {rest : List (ChurnRequest × Epoch)}
    (placed : churnQueue earliestEpoch request.firstEpoch request.perEpochChurn churnLeft
      request.amount = .ok (epoch, left))
    (tail : ChurnTrace epoch left rest lastEpoch lastLeft) :
    ChurnTrace earliestEpoch churnLeft ((request, epoch) :: rest) lastEpoch lastLeft

/-- The balance of the requests whose epoch passes a test, in Gwei. -/
def placedBalance (placements : List (ChurnRequest × Epoch)) (within : Epoch → Bool) : Nat :=
  ((placements.filter fun placement => within placement.2).map
    fun placement => placement.1.amount.toNat).sum

/-- One request, bounded by a cap.

The churn left after it stays at most the cap, and the queue never moves back.

The amount plus the churn left after it, at the epoch it gets, is at most the churn left before.

Each epoch that the queue moves past adds one cap to that bound. -/
theorem churnQueue_cap {earliestEpoch firstEpoch perEpochChurn churnLeft amount epoch left :
    UInt64} {cap : Nat} (leftLe : churnLeft.toNat ≤ cap) (churnLe : perEpochChurn.toNat ≤ cap)
    (computed :
      churnQueue earliestEpoch firstEpoch perEpochChurn churnLeft amount = .ok (epoch, left)) :
    left.toNat ≤ cap ∧ earliestEpoch ≤ epoch ∧
      amount.toNat + left.toNat + earliestEpoch.toNat * cap ≤
        churnLeft.toNat + epoch.toNat * cap := by
  obtain ⟨placed, spent, last⟩ := churnQueue_spend computed
  have earliestLe : earliestEpoch ≤ max earliestEpoch firstEpoch := by
    rw [UInt64.max_def]
    split
    · assumption
    · exact UInt64.le_refl _
  refine ⟨?_, UInt64.le_trans earliestLe placed, ?_⟩ <;>
    generalize max earliestEpoch firstEpoch = first at placed spent last earliestLe <;>
    have placedNat := UInt64.le_iff_toNat_le.mp placed <;>
    have earliestNat := UInt64.le_iff_toNat_le.mp earliestLe
  · -- The last epoch keeps at most the churn available there, or less than one churn.
    rcases last with rfl | below
    · simp only [Nat.sub_self, Nat.zero_mul, Nat.add_zero] at spent
      split at spent <;> omega
    · omega
  · -- Each added epoch contributes at most one cap.
    have added := Nat.mul_le_mul_left (epoch.toNat - first.toNat) churnLe
    have whole : first.toNat * cap + (epoch.toNat - first.toNat) * cap = epoch.toNat * cap := by
      rw [← Nat.add_mul, Nat.add_sub_cancel' placedNat]
    split at spent
    · -- A new epoch opens with its churn, at most one cap past the earliest open epoch.
      rename_i opened
      have opens : earliestEpoch.toNat * cap + cap ≤ first.toNat * cap := by
        have := Nat.mul_le_mul_right cap (UInt64.lt_iff_toNat_lt.mp opened)
        rwa [Nat.succ_mul] at this
      omega
    · -- The earliest open epoch is the first one, with the churn left there.
      rename_i stays
      have same : first = earliestEpoch :=
        UInt64.le_antisymm (UInt64.not_lt.mp stays) earliestLe
      subst same
      omega

/-- Each request takes an epoch no earlier than the queue's earliest open epoch.

The queue never moves back, so the last request's epoch bounds them all. -/
theorem ChurnTrace.epochs {earliestEpoch churnLeft lastEpoch lastLeft : UInt64}
    {placements : List (ChurnRequest × Epoch)}
    (trace : ChurnTrace earliestEpoch churnLeft placements lastEpoch lastLeft) :
    earliestEpoch ≤ lastEpoch ∧
      ∀ placement ∈ placements, earliestEpoch ≤ placement.2 ∧ placement.2 ≤ lastEpoch := by
  induction trace with
  | nil => exact ⟨UInt64.le_refl _, fun _ member => nomatch member⟩
  | cons placed _ more =>
    have stays := (churnQueue_cap (cap := 2 ^ 64) (Nat.le_of_lt (UInt64.toNat_lt _))
      (Nat.le_of_lt (UInt64.toNat_lt _)) placed).2.1
    refine ⟨UInt64.le_trans stays more.1, fun placement member => ?_⟩
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨stays, more.1⟩
    · have later := more.2 placement member
      exact ⟨UInt64.le_trans stays later.1, later.2⟩

/-- The churn left stays at most a cap that bounds it at the start and every request's churn. -/
theorem ChurnTrace.left_le {earliestEpoch churnLeft lastEpoch lastLeft : UInt64}
    {placements : List (ChurnRequest × Epoch)} {cap : Nat}
    (trace : ChurnTrace earliestEpoch churnLeft placements lastEpoch lastLeft)
    (leftLe : churnLeft.toNat ≤ cap)
    (churns : ∀ placement ∈ placements, placement.1.perEpochChurn.toNat ≤ cap) :
    lastLeft.toNat ≤ cap := by
  induction trace with
  | nil => exact leftLe
  | cons placed _ more =>
    exact more (churnQueue_cap leftLe (churns _ List.mem_cons_self) placed).1
      fun placement member => churns placement (List.mem_cons_of_mem _ member)

/-- The balance placed up to an epoch, bounded by a cap on the churn.

It is at most the churn left at the start, plus one cap per epoch past the earliest open one.

An amount counts at the epoch it gets, even when it takes churn from earlier epochs. -/
theorem ChurnTrace.placedBalance_le {earliestEpoch churnLeft lastEpoch lastLeft : UInt64}
    {placements : List (ChurnRequest × Epoch)} {cap : Nat}
    (trace : ChurnTrace earliestEpoch churnLeft placements lastEpoch lastLeft)
    (leftLe : churnLeft.toNat ≤ cap)
    (churns : ∀ placement ∈ placements, placement.1.perEpochChurn.toNat ≤ cap) (upTo : Epoch) :
    placedBalance placements (fun epoch => decide (epoch ≤ upTo)) ≤
      churnLeft.toNat + (upTo.toNat - earliestEpoch.toNat) * cap := by
  induction trace with
  | nil => simp [placedBalance]
  | @cons earliestEpoch churnLeft epoch left _ _ request rest placed tail more =>
    obtain ⟨leftAfter, _, step⟩ := churnQueue_cap leftLe (churns _ List.mem_cons_self) placed
    have restBound := more leftAfter fun placement member =>
      churns placement (List.mem_cons_of_mem _ member)
    have stays := UInt64.le_iff_toNat_le.mp (churnQueue_cap (cap := 2 ^ 64)
      (Nat.le_of_lt (UInt64.toNat_lt _)) (Nat.le_of_lt (UInt64.toNat_lt _)) placed).2.1
    by_cases within : epoch ≤ upTo
    · have withinNat := UInt64.le_iff_toNat_le.mp within
      -- The cap of each epoch from the earliest open one to the bound, split at this request.
      have split : (upTo.toNat - earliestEpoch.toNat) * cap =
          (upTo.toNat - epoch.toNat) * cap + (epoch.toNat - earliestEpoch.toNat) * cap := by
        rw [← Nat.add_mul]
        congr 1
        omega
      have reach : earliestEpoch.toNat * cap + (epoch.toNat - earliestEpoch.toNat) * cap =
          epoch.toNat * cap := by
        rw [← Nat.add_mul, Nat.add_sub_cancel' stays]
      simp only [placedBalance, List.filter_cons, within, decide_true, ↓reduceIte, List.map_cons,
        List.sum_cons] at restBound ⊢
      omega
    · -- Every later request takes this epoch or a later one, so none is up to the bound.
      have none : rest.filter (fun placement => decide (placement.2 ≤ upTo)) = [] := by
        refine List.filter_eq_nil_iff.mpr fun placement member => ?_
        have later := (tail.epochs.2 placement member).1
        simp only [decide_eq_true_eq]
        exact fun le => within (UInt64.le_trans later le)
      simp [placedBalance, within, none]

/-- A list's sum of a function is the value at its head, plus the sum over its tail. -/
private theorem sum_map_head_tail {α : Type} (items : List α) (value : α → Nat) :
    (items.map value).sum = ((items.head?.map value).getD 0) + (items.tail.map value).sum := by
  cases items <;> simp

/-- The balance placed in a range of epochs, bounded by a cap on the churn.

The range runs from just after `start` to `stop`, so it has `stop - start` epochs.

Every request in it but the first takes at most one cap per epoch of the range.

The first request may also take churn from epochs before the range.

So one large amount can fill an epoch past the cap. -/
theorem ChurnTrace.window_tail_le {earliestEpoch churnLeft lastEpoch lastLeft : UInt64}
    {placements : List (ChurnRequest × Epoch)} {cap : Nat}
    (trace : ChurnTrace earliestEpoch churnLeft placements lastEpoch lastLeft)
    (leftLe : churnLeft.toNat ≤ cap)
    (churns : ∀ placement ∈ placements, placement.1.perEpochChurn.toNat ≤ cap)
    (start stop : Epoch) :
    (((placements.filter fun placement =>
        decide (start < placement.2) && decide (placement.2 ≤ stop)).tail).map
      fun placement => placement.1.amount.toNat).sum ≤ (stop.toNat - start.toNat) * cap := by
  induction trace with
  | nil => simp
  | @cons earliestEpoch churnLeft epoch left _ _ request rest placed tail more =>
    obtain ⟨leftAfter, _, _⟩ := churnQueue_cap leftLe (churns _ List.mem_cons_self) placed
    have restChurns : ∀ placement ∈ rest, placement.1.perEpochChurn.toNat ≤ cap :=
      fun placement member => churns placement (List.mem_cons_of_mem _ member)
    by_cases after : start < epoch
    · by_cases within : epoch ≤ stop
      · -- This request is the first in the range, and every later one is past the start.
        have past : rest.filter (fun placement =>
              decide (start < placement.2) && decide (placement.2 ≤ stop)) =
            rest.filter (fun placement => decide (placement.2 ≤ stop)) := by
          refine List.filter_congr fun placement member => ?_
          have later := (tail.epochs.2 placement member).1
          simp [UInt64.lt_of_lt_of_le after later]
        have bound := tail.placedBalance_le leftAfter restChurns stop
        have afterNat := UInt64.lt_iff_toNat_lt.mp after
        have withinNat := UInt64.le_iff_toNat_le.mp within
        -- The churn left here and the epochs after it fit in the epochs of the range.
        have fits : (stop.toNat - epoch.toNat) * cap + cap ≤ (stop.toNat - start.toNat) * cap := by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right cap (by omega)
        simp only [List.filter_cons, after, within, decide_true, Bool.and_self, ↓reduceIte,
          List.tail_cons, past]
        simp only [placedBalance] at bound
        omega
      · -- Every request from here on is past the range.
        have none : rest.filter (fun placement =>
            decide (start < placement.2) && decide (placement.2 ≤ stop)) = [] := by
          refine List.filter_eq_nil_iff.mpr fun placement member => ?_
          have later := (tail.epochs.2 placement member).1
          simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
          exact fun _ le => within (UInt64.le_trans later le)
        simp [within, none]
    · -- This request is before the range, so the range starts with the later ones.
      simp only [List.filter_cons, after, decide_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte]
      exact more leftAfter restChurns

/-- The balance placed in a range of `stop - start` epochs, bounded by a cap on the churn.

It is at most one cap per epoch of the range, plus the first amount placed in the range. -/
theorem ChurnTrace.window_le {earliestEpoch churnLeft lastEpoch lastLeft : UInt64}
    {placements : List (ChurnRequest × Epoch)} {cap : Nat}
    (trace : ChurnTrace earliestEpoch churnLeft placements lastEpoch lastLeft)
    (leftLe : churnLeft.toNat ≤ cap)
    (churns : ∀ placement ∈ placements, placement.1.perEpochChurn.toNat ≤ cap)
    (start stop : Epoch) :
    placedBalance placements (fun epoch => decide (start < epoch) && decide (epoch ≤ stop)) ≤
      (stop.toNat - start.toNat) * cap +
        (((placements.filter fun placement =>
            decide (start < placement.2) && decide (placement.2 ≤ stop)).head?.map
          fun placement => placement.1.amount.toNat).getD 0) := by
  have tailLe := trace.window_tail_le leftLe churns start stop
  simp only [placedBalance]
  rw [sum_map_head_tail]
  omega

/-- Two traces in turn are one trace. -/
theorem ChurnTrace.append {earliestEpoch churnLeft middleEpoch middleLeft lastEpoch lastLeft :
    UInt64} {first second : List (ChurnRequest × Epoch)}
    (head : ChurnTrace earliestEpoch churnLeft first middleEpoch middleLeft)
    (tail : ChurnTrace middleEpoch middleLeft second lastEpoch lastLeft) :
    ChurnTrace earliestEpoch churnLeft (first ++ second) lastEpoch lastLeft := by
  induction head with
  | nil => exact tail
  | cons placed _ more => exact .cons placed (more tail)

/-- An amount of 2048 with 256 of churn per epoch and none left takes eight epochs.

All 2048 leave at the last of them, epoch 18.

So one epoch receives eight times the churn, which the first amount of a range may do. -/
theorem churnQueue_large_amount : churnQueue 10 10 256 0 2048 = .ok (18, 0) := rfl

/-- Two requests to one epoch, with 256 of churn and then 128.

The first opens epoch 10 with 256 and takes 56, so 200 is left.

The second has only 128 of churn per epoch, but takes the 200 left at epoch 10.

So epoch 10 receives 256, above the churn of the second request.

A cap must bound the churn of the request that opened an epoch, not only the current churn. -/
theorem churnTrace_carry_above_churn :
    ChurnTrace 9 0 [(⟨10, 256, 56⟩, 10), (⟨10, 128, 200⟩, 10)] 10 0 :=
  .cons (left := 200) rfl (.cons rfl (.nil _ _))

/-! ## The queues of the state -/

/-- The churn that activations and exits share is at most its configured maximum. -/
theorem getActivationExitChurnLimit_le {config : Config} {state : BeaconState preset fork}
    {churn : Gwei} (computed : getActivationExitChurnLimit config state = .ok churn) :
    churn ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT := by
  simp only [getActivationExitChurnLimit, bind_ok_iff, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, _, rfl⟩ := computed
  rw [UInt64.min_def]
  split
  · exact UInt64.le_refl _
  · exact UInt64.le_of_lt (UInt64.not_le.mp ‹_›)

/-- Before Gloas, the churn of exits is at most the configured maximum of activations and exits.
-/
theorem exitChurnLimit_le_of_lt {config : Config} {state : BeaconState preset fork}
    {churn : Gwei} (before : fork < .glamsterdam)
    (computed : exitChurnLimit config state = .ok churn) :
    churn ≤ config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT := by
  have notGloas : ¬ .glamsterdam ≤ fork := Nat.not_le_of_lt before
  simp only [exitChurnLimit, notGloas, ↓reduceIte] at computed
  exact getActivationExitChurnLimit_le computed

/-- An exit is one request to the queue of exits.

Its first epoch is the activation exit epoch of the current epoch.

Its churn is the churn of exits of the state.

The state changes only in the earliest exit epoch and the churn left there. -/
theorem computeExitEpochAndUpdateChurn_eq {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    ∃ firstEpoch perEpochChurn left,
      computeActivationExitEpoch preset (getCurrentEpoch state) = .ok firstEpoch ∧
      exitChurnLimit config state = .ok perEpochChurn ∧
      churnQueue (state.earliestExitEpoch electra) firstEpoch perEpochChurn
        (state.exitBalanceToConsume electra) exitBalance = .ok (epoch, left) ∧
      after = { state with
        exitBalanceToConsume := fun _ => left, earliestExitEpoch := fun _ => epoch } := by
  simp only [computeExitEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff, pure,
    Except.pure, Except.ok.injEq] at computed
  obtain ⟨firstEpoch, first, perEpochChurn, churn, ⟨placedEpoch, left⟩, queued, final⟩ :=
    computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact ⟨firstEpoch, perEpochChurn, left, first, churn, queued, rfl⟩

/-- A consolidation is one request to the queue of consolidations.

Its first epoch is the activation exit epoch of the current epoch.

Its churn is the churn of consolidations of the state.

The state changes only in the earliest consolidation epoch and the churn left there. -/
theorem computeConsolidationEpochAndUpdateChurn_eq {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    ∃ firstEpoch perEpochChurn left,
      computeActivationExitEpoch preset (getCurrentEpoch state) = .ok firstEpoch ∧
      getConsolidationChurnLimit config state = .ok perEpochChurn ∧
      churnQueue (state.earliestConsolidationEpoch electra) firstEpoch perEpochChurn
        (state.consolidationBalanceToConsume electra) balance = .ok (epoch, left) ∧
      after = { state with
        consolidationBalanceToConsume := fun _ => left,
        earliestConsolidationEpoch := fun _ => epoch } := by
  simp only [computeConsolidationEpochAndUpdateChurn, bind_ok_iff, liftArith, mapError_ok_iff,
    pure, Except.pure, Except.ok.injEq] at computed
  obtain ⟨firstEpoch, first, perEpochChurn, churn, ⟨placedEpoch, left⟩, queued, final⟩ :=
    computed
  simp only [Prod.mk.injEq] at final
  obtain ⟨rfl, rfl⟩ := final
  exact ⟨firstEpoch, perEpochChurn, left, first, churn, queued, rfl⟩

/-- An exit is a trace of one request, from the queue of exits before it to the queue after it.

Its amount is the balance of the exit, and its churn is the churn of exits of the state. -/
theorem computeExitEpochAndUpdateChurn_trace {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {exitBalance : Gwei}
    {epoch : Epoch}
    (computed :
      computeExitEpochAndUpdateChurn config state electra exitBalance = .ok (after, epoch)) :
    ∃ request : ChurnRequest, request.amount = exitBalance ∧
      exitChurnLimit config state = .ok request.perEpochChurn ∧
      ChurnTrace (state.earliestExitEpoch electra) (state.exitBalanceToConsume electra)
        [(request, epoch)] (after.earliestExitEpoch electra) (after.exitBalanceToConsume electra)
    := by
  obtain ⟨firstEpoch, perEpochChurn, left, _, churn, queued, rfl⟩ :=
    computeExitEpochAndUpdateChurn_eq computed
  exact ⟨⟨firstEpoch, perEpochChurn, exitBalance⟩, rfl, churn, .cons queued (.nil _ _)⟩

/-- A consolidation is a trace of one request, in the queue of consolidations.

Its amount is the balance consolidated, and its churn is the churn of consolidations. -/
theorem computeConsolidationEpochAndUpdateChurn_trace {config : Config}
    {state after : BeaconState preset fork} {electra : .pectra ≤ fork} {balance : Gwei}
    {epoch : Epoch}
    (computed :
      computeConsolidationEpochAndUpdateChurn config state electra balance = .ok (after, epoch)) :
    ∃ request : ChurnRequest, request.amount = balance ∧
      getConsolidationChurnLimit config state = .ok request.perEpochChurn ∧
      ChurnTrace (state.earliestConsolidationEpoch electra)
        (state.consolidationBalanceToConsume electra) [(request, epoch)]
        (after.earliestConsolidationEpoch electra) (after.consolidationBalanceToConsume electra)
    := by
  obtain ⟨firstEpoch, perEpochChurn, left, _, churn, queued, rfl⟩ :=
    computeConsolidationEpochAndUpdateChurn_eq computed
  exact ⟨⟨firstEpoch, perEpochChurn, balance⟩, rfl, churn, .cons queued (.nil _ _)⟩

/-! ## The churns as functions of the total active balance -/

/-- Rounding down to an increment never raises an amount. -/
theorem roundToIncrement_le (preset : Preset) (amount : Gwei) :
    (roundToIncrement preset amount).toNat ≤ amount.toNat := by
  unfold roundToIncrement
  have le : amount % preset.EFFECTIVE_BALANCE_INCREMENT ≤ amount := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_mod]
    exact Nat.mod_le _ _
  rw [UInt64.toNat_sub_of_le _ _ le]
  omega

/-- The whole churn is at most the minimum churn or a share of the total active balance. -/
theorem getBalanceChurnLimit_le {config : Config} {state : BeaconState preset fork}
    {total churn : Gwei} (totalOk : getTotalActiveBalance state = .ok total)
    (computed : getBalanceChurnLimit config state = .ok churn) :
    churn.toNat ≤
      max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat) := by
  simp only [getBalanceChurnLimit, totalOk, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at computed
  subst computed
  refine Nat.le_trans (roundToIncrement_le _ _) ?_
  rw [UInt64.max_def]
  split
  · rw [UInt64.toNat_div]
    omega
  · omega

/-- The churn of exits is at most the minimum churn or a share of the total active balance.

The share is `CHURN_LIMIT_QUOTIENT` before Gloas and `CHURN_LIMIT_QUOTIENT_GLOAS` from Gloas. -/
theorem exitChurnLimit_le_total {config : Config} {state : BeaconState preset fork}
    {total churn : Gwei} (totalOk : getTotalActiveBalance state = .ok total)
    (computed : exitChurnLimit config state = .ok churn) :
    churn.toNat ≤ max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat (total.toNat /
      (if .glamsterdam ≤ fork then config.CHURN_LIMIT_QUOTIENT_GLOAS
        else config.CHURN_LIMIT_QUOTIENT).toNat) := by
  unfold exitChurnLimit at computed
  split at computed
  · rename_i gloas
    simp only [getExitChurnLimit, totalOk, bind, Except.bind, pure, Except.pure,
      Except.ok.injEq] at computed
    subst computed
    simp only [gloas, ↓reduceIte]
    refine Nat.le_trans (roundToIncrement_le _ _) ?_
    rw [UInt64.max_def]
    split
    · rw [UInt64.toNat_div]
      omega
    · omega
  · rename_i notGloas
    simp only [notGloas, ↓reduceIte]
    simp only [getActivationExitChurnLimit, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨whole, wholeOk, rfl⟩ := computed
    have := getBalanceChurnLimit_le totalOk wholeOk
    rw [UInt64.min_def]
    split
    · rename_i le
      have := UInt64.le_iff_toNat_le.mp le
      omega
    · exact this

/-- The churn of consolidations is at most a share of the total active balance.

Before Gloas the share is that of the whole churn, which the minimum churn may raise.

From Gloas it is `CONSOLIDATION_CHURN_LIMIT_QUOTIENT`. -/
theorem getConsolidationChurnLimit_le_total {config : Config} {state : BeaconState preset fork}
    {total churn : Gwei} (totalOk : getTotalActiveBalance state = .ok total)
    (computed : getConsolidationChurnLimit config state = .ok churn) :
    churn.toNat ≤ if .glamsterdam ≤ fork then
        total.toNat / config.CONSOLIDATION_CHURN_LIMIT_QUOTIENT.toNat
      else max config.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA.toNat
        (total.toNat / config.CHURN_LIMIT_QUOTIENT.toNat) := by
  by_cases gloas : .glamsterdam ≤ fork
  · simp only [getConsolidationChurnLimit, gloas, ↓reduceIte, totalOk, bind, Except.bind, pure,
      Except.pure, Except.ok.injEq] at computed
    subst computed
    simp only [gloas, ↓reduceIte]
    refine Nat.le_trans (roundToIncrement_le _ _) ?_
    simp only [UInt64.toNat_div, Nat.le_refl]
  · simp only [gloas, ↓reduceIte]
    -- Before Gloas the churn of consolidations is a part of the whole churn.
    have whole := computed
    simp only [getConsolidationChurnLimit, gloas, ↓reduceIte, bind_ok_iff] at whole
    obtain ⟨wholeChurn, wholeOk, part, partOk, _⟩ := whole
    have sum := getConsolidationChurnLimit_add (Nat.lt_of_not_le gloas) computed partOk wholeOk
    have := getBalanceChurnLimit_le totalOk wholeOk
    omega

/-- A churn of exits reads the total active balance, so that balance exists. -/
theorem exitChurnLimit_total {config : Config} {state : BeaconState preset fork} {churn : Gwei}
    (computed : exitChurnLimit config state = .ok churn) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  cases totalOk : getTotalActiveBalance state with
  | ok total => exact ⟨total, rfl⟩
  | error e =>
    unfold exitChurnLimit at computed
    split at computed <;>
      simp [getExitChurnLimit, getActivationExitChurnLimit, getBalanceChurnLimit, totalOk,
        bind, Except.bind] at computed

/-- A churn of consolidations reads the total active balance, so that balance exists. -/
theorem getConsolidationChurnLimit_total {config : Config} {state : BeaconState preset fork}
    {churn : Gwei} (computed : getConsolidationChurnLimit config state = .ok churn) :
    ∃ total, getTotalActiveBalance state = .ok total := by
  cases totalOk : getTotalActiveBalance state with
  | ok total => exact ⟨total, rfl⟩
  | error e =>
    unfold getConsolidationChurnLimit at computed
    split at computed <;>
      simp [getBalanceChurnLimit, totalOk, bind, Except.bind] at computed

/-- The churn of pending deposits has a fixed maximum at every fork.

The maximum is `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` before Gloas.

From Gloas it is `MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS`, as [EIP-8061] specifies.

[EIP-8061]: https://eips.ethereum.org/EIPS/eip-8061 -/
theorem depositChurnLimit_le {config : Config} {state : BeaconState preset fork} {churn : Gwei}
    (computed : depositChurnLimit config state = .ok churn) :
    churn.toNat ≤ (if .glamsterdam ≤ fork then config.MAX_PER_EPOCH_ACTIVATION_CHURN_LIMIT_GLOAS
      else config.MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT).toNat := by
  unfold depositChurnLimit at computed
  split at computed
  · rename_i gloas
    simp only [gloas, ↓reduceIte]
    simp only [getActivationChurnLimit, bind_ok_iff, pure, Except.pure,
      Except.ok.injEq] at computed
    obtain ⟨exit, _, rfl⟩ := computed
    rw [UInt64.min_def]
    split
    · exact Nat.le_refl _
    · rename_i above
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp above)
      omega
  · rename_i notGloas
    simp only [notGloas, ↓reduceIte]
    exact UInt64.le_iff_toNat_le.mp (getActivationExitChurnLimit_le computed)

/-- Known answer: the churn of exits from Gloas, on mainnet, at a total active balance of 2^25 ETH.

The churn is 1024 ETH, four times `MAX_PER_EPOCH_ACTIVATION_EXIT_CHURN_LIMIT` of 256 ETH.

So the fixed maximum of the churn of exits in Electra does not hold from Gloas.

From Gloas a bound on the churn of exits needs a bound on the total active balance. -/
theorem gloasExitChurn_mainnet :
    roundToIncrement Preset.mainnet (max Config.mainnet.MIN_PER_EPOCH_CHURN_LIMIT_ELECTRA
      (2 ^ 25 * 10 ^ 9 / Config.mainnet.CHURN_LIMIT_QUOTIENT_GLOAS)) = 2 ^ 10 * 10 ^ 9 := by
  decide

end EthLib.Consensus
