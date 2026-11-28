import Mathlib

-- child 1 zh: 已验收的小区间证明给出 M0 的数值下界。
-- child 1 en: The verified small-range certificate supplies the lower bound for M0.
-- child 2 zh: 用该数值下界证明中区间内更强的倒数素数和上界。
-- child 2 en: Establish the stronger numerical upper bound over the mid-range.

theorem Conjectures.Cuts.Cut080e3922c4dcc34d1b6f3c44
    (h₁ : (0.261497 : ℝ) ≤ Real.eulerMascheroniConstant +
      ∑' (p : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / (↑(↑p : ℕ) : ℝ)) +
        (1 : ℝ) / (↑(↑p : ℕ) : ℝ)))
    (h₂ : ∀ (x2 : ℝ), Real.exp (10 : ℝ) < x2 → x2 ≤ (10 : ℝ) ^ (12 : ℕ) →
      ∑ x5 ∈ Finset.range ⌈x2⌉₊ with Nat.Prime x5, (1 : ℝ) / (↑x5 : ℝ) ≤
        Real.log (Real.log x2) + (0.261497 : ℝ) +
          (2 : ℝ) / (√x2 * Real.log x2)) :
    (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)) + (1 : ℝ) / (↑(↑x1 : ℕ) : ℝ)); ∀ (x2 : ℝ), Real.exp (10 : ℝ) < x2 → x2 ≤ (10 : ℝ) ^ (12 : ℕ) → ∑ x5 ∈ Finset.range ⌈x2⌉₊ with Nat.Prime x5, (1 : ℝ) / (↑x5 : ℝ) ≤ Real.log (Real.log x2) + x1 + (2 : ℝ) / (√x2 * Real.log x2)) := by
  dsimp only at h₂ ⊢
  intro x hx hbound
  have hnum := h₂ x hx hbound
  linarith only [h₁, hnum]
