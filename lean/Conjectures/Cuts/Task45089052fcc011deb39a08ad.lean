import Mathlib

open scoped BigOperators

/-- The product of all prime factors is at least `minFac` raised to their count. -/
private lemma minFac_pow_cardFactors_le {n : ℕ} (hn : n ≠ 0) :
    n.minFac ^ ArithmeticFunction.cardFactors n ≤ n := by
  rw [ArithmeticFunction.cardFactors_apply]
  calc
    n.minFac ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod := by
      apply List.pow_length_le_prod
      intro p _hp
      exact Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactorsList _hp).two_le
        (Nat.dvd_of_mem_primeFactorsList _hp)
    _ = n := Nat.prod_primeFactorsList hn

/-- The roughness hypothesis in the candidate set forces fewer than five prime factors. -/
private lemma cardFactors_lt_five_of_rough {N p : ℕ}
    (_hp : p ∈ Finset.range N) (hk : 1 < N - p)
    (hrough : N < (N - p).minFac ^ 5) :
    ArithmeticFunction.cardFactors (N - p) < 5 := by
  by_contra! h
  have hpow : (N - p).minFac ^ 5 ≤
      (N - p).minFac ^ ArithmeticFunction.cardFactors (N - p) :=
    Nat.pow_le_pow_right (Nat.minFac_pos _) h
  have hle := (minFac_pow_cardFactors_le (by omega : N - p ≠ 0)).trans (Nat.sub_le N p)
  omega

/-- The desired identity holds term by term for numbers with one to four prime factors. -/
private lemma sign_term {k : ℕ} (hk0 : k ≠ 0) (hk1 : 1 < k)
    (hk5 : ArithmeticFunction.cardFactors k < 5) :
    (if k.Prime then (2 : ℝ) else 0) =
      1 - (ArithmeticFunction.liouville k : ℝ) -
        2 * (if ArithmeticFunction.cardFactors k = 3 then (1 : ℝ) else 0) := by
  have hkpos : 0 < ArithmeticFunction.cardFactors k :=
    ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hk1
  have hpiff : k.Prime ↔ ArithmeticFunction.cardFactors k = 1 :=
    ArithmeticFunction.cardFactors_eq_one_iff_prime.symm
  simp only [hpiff]
  have hc : ArithmeticFunction.cardFactors k = 1 ∨ ArithmeticFunction.cardFactors k = 2 ∨
      ArithmeticFunction.cardFactors k = 3 ∨ ArithmeticFunction.cardFactors k = 4 := by
    omega
  rcases hc with h | h | h | h <;>
    simp [ArithmeticFunction.liouville_apply hk0, h] <;> norm_num

/-- PREPUB frozen statement `L-goldbach-cut-45089052fcc011deb39a08ad`. -/
theorem Conjectures.Cuts.Task45089052fcc011deb39a08ad : (∀ (x1 : ℕ), (2 : ℝ) * ↑{x2 ∈ {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)} | Nat.Prime (x1 - x2)}.card = ↑{x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)}.card - ∑ x2 ∈ Finset.range x1 with Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ), ↑(ArithmeticFunction.liouville (x1 - x2)) - (2 : ℝ) * ↑{x2 ∈ {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)} | ArithmeticFunction.cardFactors (x1 - x2) = (3 : ℕ)}.card) := by
  classical
  intro N
  let P := fun p : ℕ => Nat.Prime p ∧ N < 3 * p ∧ 3 * p < 2 * N ∧
    1 < N - p ∧ N < (N - p).minFac ^ 5
  let C := (Finset.range N).filter P
  change (2 : ℝ) * (C.filter (fun p => (N - p).Prime)).card =
    C.card - ∑ p ∈ C, (ArithmeticFunction.liouville (N - p) : ℝ) -
      2 * (C.filter (fun p => ArithmeticFunction.cardFactors (N - p) = 3)).card
  calc
    (2 : ℝ) * (C.filter (fun p => (N - p).Prime)).card =
        ∑ p ∈ C, (if (N - p).Prime then (2 : ℝ) else 0) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = ∑ p ∈ C, (1 - (ArithmeticFunction.liouville (N - p) : ℝ) -
        2 * (if ArithmeticFunction.cardFactors (N - p) = 3 then (1 : ℝ) else 0)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' : p ∈ (Finset.range N).filter P := hp
      obtain ⟨hpRange, hpP⟩ := Finset.mem_filter.mp hp'
      have hk1 : 1 < N - p := hpP.2.2.2.1
      have hrough : N < (N - p).minFac ^ 5 := hpP.2.2.2.2
      exact sign_term (by omega) hk1 (cardFactors_lt_five_of_rough hpRange hk1 hrough)
    _ = C.card - ∑ p ∈ C, (ArithmeticFunction.liouville (N - p) : ℝ) -
        2 * (C.filter (fun p => ArithmeticFunction.cardFactors (N - p) = 3)).card := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
