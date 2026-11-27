import Mathlib

namespace Conjectures.TwinPrimes.SquareLogMass_aux

lemma prime_square_filter_eq_image (Y : ℕ) :
    (Finset.range (Y + 1)).filter
        (fun n => (Nat.sqrt n).Prime ∧ n = (Nat.sqrt n) ^ 2) =
      (Nat.primesLE (Nat.sqrt Y)).image (fun p => p ^ 2) := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hn_range, hn_prime, hn_square⟩
    refine Finset.mem_image.mpr ⟨Nat.sqrt n, Nat.mem_primesLE.mpr ⟨?_, hn_prime⟩, ?_⟩
    · apply Nat.le_sqrt'.mpr
      rw [← hn_square]
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hn_range)
    · exact hn_square.symm
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨p, hp, rfl⟩
    have hp' := Nat.mem_primesLE.mp hp
    have hp_square_le : p ^ 2 ≤ Y := Nat.le_sqrt'.mp hp'.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hp_square_le), ?_⟩
    rw [Nat.sqrt_eq']
    exact ⟨hp'.2, rfl⟩

lemma prime_square_sum_eq_theta_sum (Y : ℕ) :
    ((Finset.range (Y + 1)).filter
        (fun n => (Nat.sqrt n).Prime ∧ n = (Nat.sqrt n) ^ 2)).sum
        ArithmeticFunction.vonMangoldt =
      ∑ p ∈ Nat.primesLE (Nat.sqrt Y), Real.log p := by
  classical
  calc
    ((Finset.range (Y + 1)).filter
          (fun n => (Nat.sqrt n).Prime ∧ n = (Nat.sqrt n) ^ 2)).sum
        ArithmeticFunction.vonMangoldt =
        ∑ p ∈ Nat.primesLE (Nat.sqrt Y),
          ArithmeticFunction.vonMangoldt (p ^ 2) := by
      rw [prime_square_filter_eq_image]
      exact Finset.sum_image (fun p _ q _ hpq => Nat.pow_left_injective (by decide) hpq)
    _ = ∑ p ∈ Nat.primesLE (Nat.sqrt Y), Real.log p := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesLE hp)]

end Conjectures.TwinPrimes.SquareLogMass_aux

theorem Conjectures.TwinPrimes.SquareLogMass :
    let Λ := ArithmeticFunction.vonMangoldt; ∀ Y : ℕ, ((Finset.range (Y+1)).filter (fun n => (Nat.sqrt n).Prime ∧ n = (Nat.sqrt n)^2)).sum (fun n => Λ n) ≤ Real.log 4 * Real.sqrt Y := by
  dsimp
  intro Y
  calc
    ((Finset.range (Y + 1)).filter
          (fun n => (Nat.sqrt n).Prime ∧ n = (Nat.sqrt n) ^ 2)).sum
        ArithmeticFunction.vonMangoldt =
        ∑ p ∈ Nat.primesLE (Nat.sqrt Y), Real.log p :=
      Conjectures.TwinPrimes.SquareLogMass_aux.prime_square_sum_eq_theta_sum Y
    _ = Chebyshev.theta (Nat.sqrt Y) :=
      (Chebyshev.theta_eq_sum_primesLE_log (Nat.sqrt Y)).symm
    _ ≤ Real.log 4 * (Nat.sqrt Y : ℝ) :=
      Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
    _ ≤ Real.log 4 * Real.sqrt Y := by
      exact mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt
        (Real.log_nonneg (by norm_num))
