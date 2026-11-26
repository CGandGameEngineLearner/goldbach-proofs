import Mathlib

private lemma abel_gen (a : ℕ → ℝ) :
    ∀ x y : ℕ, 1 ≤ x → x < y →
      (∑ n ∈ Finset.Ioc x y, a n / n) =
        (∑ n ∈ Finset.Icc 1 y, a n) / y - (∑ n ∈ Finset.Icc 1 x, a n) / ((x : ℝ) + 1)
          + ∑ n ∈ Finset.Ico (x + 1) y,
              (∑ m ∈ Finset.Icc 1 n, a m) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)) := by
  intro x y
  induction y with
  | zero => intro h1 h2; omega
  | succ y ih =>
    intro h1 h2
    rcases lt_or_eq_of_le (show x ≤ y by omega) with hlt | heq
    · have hprev := ih h1 hlt
      have hL : ∑ n ∈ Finset.Ioc x (y + 1), a n / n
          = (∑ n ∈ Finset.Ioc x y, a n / n) + a (y + 1) / (y + 1) := by
        rw [Finset.sum_Ioc_succ_top (le_of_lt hlt)]
        push_cast
        ring
      have hI : ∑ n ∈ Finset.Ico (x + 1) (y + 1),
            (∑ m ∈ Finset.Icc 1 n, a m) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1))
          = (∑ n ∈ Finset.Ico (x + 1) y,
              (∑ m ∈ Finset.Icc 1 n, a m) * (1 / (n : ℝ) - 1 / ((n : ℝ) + 1)))
            + (∑ m ∈ Finset.Icc 1 y, a m) * (1 / (y : ℝ) - 1 / ((y : ℝ) + 1)) := by
        rw [Finset.sum_Ico_succ_top (by omega : x + 1 ≤ y)]
      have hA : ∑ n ∈ Finset.Icc 1 (y + 1), a n
          = (∑ n ∈ Finset.Icc 1 y, a n) + a (y + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ y + 1)]
      rw [hL, hI, hprev, hA]
      push_cast
      field_simp
      ring
    · subst heq
      rw [Nat.Ioc_succ_singleton, Finset.sum_singleton]
      have hA : ∑ n ∈ Finset.Icc 1 (x + 1), a n
          = (∑ n ∈ Finset.Icc 1 x, a n) + a (x + 1) := by
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ x + 1)]
      rw [hA]
      simp only [Finset.Ico_self, Finset.sum_empty, add_zero]
      push_cast
      field_simp
      ring

theorem PEqualNP.Outside.L_quadratic_primes_levent_abel_reciprocal :
    let cheb := fun x : ℕ => ∑ p ∈ (Finset.Icc 1 x).filter (fun p => p.Prime ∧ p%4=1), Real.log (p : ℝ); ∀ x y : ℕ, 1 ≤ x → x < y → (∑ p ∈ (Finset.Ioc x y).filter (fun p => p.Prime ∧ p%4=1), Real.log (p : ℝ)/p) = cheb y / y - cheb x / ((x : ℝ)+1) + ∑ n ∈ Finset.Ico (x+1) y, cheb n * (1/(n : ℝ)-1/((n : ℝ)+1)) := by
  dsimp only
  intro x y h1 h2
  have hA : ∀ N : ℕ, (∑ p ∈ (Finset.Icc 1 N).filter (fun p => p.Prime ∧ p%4=1), Real.log (p : ℝ))
      = ∑ n ∈ Finset.Icc 1 N, (if n.Prime ∧ n % 4 = 1 then Real.log (n : ℝ) else 0) := by
    intro N
    rw [Finset.sum_filter]
  have hB : (∑ p ∈ (Finset.Ioc x y).filter (fun p => p.Prime ∧ p%4=1), Real.log (p : ℝ)/p)
      = ∑ n ∈ Finset.Ioc x y, (if n.Prime ∧ n % 4 = 1 then Real.log (n : ℝ) else 0) / n := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl (fun n _ => by by_cases h : n.Prime ∧ n % 4 = 1 <;> simp [h])
  simp only [hA, hB]
  exact abel_gen (fun n => if n.Prime ∧ n % 4 = 1 then Real.log (n : ℝ) else 0) x y h1 h2
