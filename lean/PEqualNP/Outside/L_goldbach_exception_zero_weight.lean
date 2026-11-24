import Mathlib

/-!
# L-goldbach-exception-zero-weight

Zero representation counts agree exactly with zero prime-weight correlation:

`reps n` is the set of `p ∈ [0, n]` with `p` and `n - p` prime, `w k` is `log k` on primes
and `0` elsewhere, and `conv u v n = ∑ k ∈ [0, n], u k * v (n - k)`.  Then for every `n`,

`(reps n).card = 0 ↔ conv w w n = 0`.

Both directions rest on the same point: every summand `w k * w (n - k)` is nonnegative, and
it is strictly positive exactly when `k` and `n - k` are both prime (a surviving summand is a
representation).  Hence the convolution vanishes iff no summand survives iff the filter is
empty iff its card is zero.
-/

namespace PEqualNP.Outside.GoldbachExceptionZeroWeightAux

/-- Prime weight: the natural log of a prime, `0` for every other natural. -/
noncomputable def goldW (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k:ℝ) else 0

/-- Ordered prime pairs `(p, n - p)` with `p` ranging over `0..n`. -/
def goldReps (n : ℕ) : Finset ℕ :=
  (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p))

theorem goldW_nonneg (k : ℕ) : 0 ≤ goldW k := by
  unfold goldW
  by_cases hp : Nat.Prime k
  · rw [if_pos hp]; exact Real.log_nonneg (le_of_lt (by exact_mod_cast hp.one_lt))
  · rw [if_neg hp]

theorem goldW_pos (k : ℕ) (hp : Nat.Prime k) : 0 < goldW k := by
  unfold goldW; rw [if_pos hp]; exact Real.log_pos (by exact_mod_cast hp.one_lt)

theorem goldW_eq_zero (k : ℕ) (h : ¬Nat.Prime k) : goldW k = 0 := by
  unfold goldW; rw [if_neg h]

theorem goldW_ne_zero_iff (k : ℕ) : goldW k ≠ 0 ↔ Nat.Prime k := by
  by_cases hp : Nat.Prime k
  · exact ⟨fun _ => hp, fun _ => ne_of_gt (goldW_pos k hp)⟩
  · exact ⟨fun h => absurd (goldW_eq_zero k hp) h, fun hp' => absurd hp' hp⟩

theorem goldW_mul_ne_zero {n k : ℕ} :
    goldW k * goldW (n-k) ≠ 0 ↔ (Nat.Prime k ∧ Nat.Prime (n-k)) := by
  constructor
  · intro h
    have hk : goldW k ≠ 0 := fun e => h (by rw [e, zero_mul])
    have hj : goldW (n-k) ≠ 0 := fun e => h (by rw [e, mul_zero])
    exact ⟨(goldW_ne_zero_iff k).1 hk, (goldW_ne_zero_iff (n-k)).1 hj⟩
  · intro hp
    exact mul_ne_zero ((goldW_ne_zero_iff k).2 hp.1) ((goldW_ne_zero_iff (n-k)).2 hp.2)

/-- The convolution vanishes iff every summand vanishes (all summands are nonnegative). -/
theorem conv_zero_iff (n : ℕ) :
    (Finset.sum (Finset.range (n+1)) (fun k => goldW k * goldW (n-k))) = 0
      ↔ ∀ k ∈ Finset.range (n+1), goldW k * goldW (n-k) = 0 := by
  have hnn : ∀ k ∈ Finset.range (n+1), 0 ≤ goldW k * goldW (n-k) :=
    fun k _ => mul_nonneg (goldW_nonneg k) (goldW_nonneg (n-k))
  constructor
  · intro h k hk
    by_contra hne
    have hpos : 0 < goldW k * goldW (n-k) := lt_of_le_of_ne (hnn k hk) (Ne.symm hne)
    exact absurd (le_trans (Finset.single_le_sum hnn hk) (le_of_eq h)) (not_le.2 hpos)
  · intro h
    exact Finset.sum_eq_zero h

/-- The card vanishes iff no index in `[0, n]` yields a prime pair. -/
theorem reps_card_zero_iff (n : ℕ) :
    (goldReps n).card = 0 ↔ ∀ k ∈ Finset.range (n+1), ¬(Nat.Prime k ∧ Nat.Prime (n-k)) := by
  constructor
  · intro hcard k hk hp
    have hmem : k ∈ goldReps n := Finset.mem_filter.2 ⟨hk, hp⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hcard
    exact hcard k hmem
  · intro h
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro a ha
    unfold goldReps at ha
    rw [Finset.mem_filter] at ha
    exact h a ha.1 ⟨ha.2.1, ha.2.2⟩

/-- A surviving summand is exactly a representation, so both sides say: no representation. -/
theorem goldbach_zero_weight_core (n : ℕ) :
    (goldReps n).card = 0 ↔
      Finset.sum (Finset.range (n+1)) (fun k => goldW k * goldW (n-k)) = 0 := by
  rw [conv_zero_iff n]
  constructor
  · intro hcard k hk
    by_contra hne
    exact (reps_card_zero_iff n).1 hcard k hk (goldW_mul_ne_zero.1 hne)
  · intro hall
    exact (reps_card_zero_iff n).2 fun k hk hp => absurd (hall k hk) (goldW_mul_ne_zero.2 hp)

end PEqualNP.Outside.GoldbachExceptionZeroWeightAux

theorem PEqualNP.Outside.L_goldbach_exception_zero_weight :
    let reps := fun n : ℕ => (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p)); let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let conv := fun (u v : ℕ → ℝ) (n : ℕ) => Finset.sum (Finset.range (n+1)) (fun k => u k*v (n-k)); ∀ n, (reps n).card=0 ↔ conv w w n=0 :=
  fun n => PEqualNP.Outside.GoldbachExceptionZeroWeightAux.goldbach_zero_weight_core n
