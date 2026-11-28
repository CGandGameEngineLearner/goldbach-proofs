import Mathlib

-- child 1 zh: 存在 B > 1、K > 0 与阈值 N，使所有满足 0 < a < b、互素、a + b ≥ N 且 rad(a)·rad(b)·rad(a+b) < a + b 的正整数对满足 a + b ≤ K · (rad(a)·rad(b)·rad(a+b))^B。
-- child 1 en: There exist B > 1, K > 0, and N such that for all coprime 0 < a < b with a + b ≥ N and rad(a)·rad(b)·rad(a+b) < a + b, one has a + b ≤ K · (rad(a)·rad(b)·rad(a+b))^B.
-- child 2 zh: 对任意互素正整数 a 与 b，乘积 ab(a+b) 的素因子之积（radical）等于 rad(a)·rad(b)·rad(a+b)。
-- child 2 en: For any coprime positive integers a and b, the radical of a·b·(a+b) equals rad(a)·rad(b)·rad(a+b).
theorem Conjectures.Cuts.Cut96df22cb6e02dab5474aabd0
    (hSplit : ∃ (B K : ℝ), (1 : ℝ) < B ∧ (0 : ℝ) < K ∧ ∃ (N : ℕ),
      ∀ (a b : ℕ), (0 : ℕ) < a → a < b → a.Coprime b → N ≤ a + b →
        a.primeFactors.prod id * b.primeFactors.prod id * (a + b).primeFactors.prod id < a + b →
        (a : ℝ) + (b : ℝ) ≤
          K * ((a.primeFactors.prod id * b.primeFactors.prod id * (a + b).primeFactors.prod id : ℕ) : ℝ) ^ B)
    (hRadMul : ∀ (a b : ℕ), (0 : ℕ) < a → (0 : ℕ) < b → a.Coprime b →
      (a * b * (a + b)).primeFactors.prod id =
        a.primeFactors.prod id * b.primeFactors.prod id * (a + b).primeFactors.prod id) :
    (∃ (x1 : ℝ) (x2 : ℝ), (1 : ℝ) < x1 ∧ (0 : ℝ) < x2 ∧ ∃ (x3 : ℕ), ∀ (x4 x5 : ℕ), (0 : ℕ) < x4 → x4 < x5 → x4.Coprime x5 → x3 ≤ x4 + x5 → (x4 * x5 * (x4 + x5)).primeFactors.prod id < x4 + x5 → ↑x4 + ↑x5 ≤ x2 * ↑((x4 * x5 * (x4 + x5)).primeFactors.prod id) ^ x1) := by
  obtain ⟨B, K, hB, hK, N, hMain⟩ := hSplit
  refine ⟨B, K, hB, hK, N, ?_⟩
  intro a b ha hab hcop hN hrad
  have hEq : (a * b * (a + b)).primeFactors.prod id =
      a.primeFactors.prod id * b.primeFactors.prod id * (a + b).primeFactors.prod id :=
    hRadMul a b ha (lt_trans ha hab) hcop
  rw [hEq] at hrad ⊢
  exact hMain a b ha hab hcop hN hrad
