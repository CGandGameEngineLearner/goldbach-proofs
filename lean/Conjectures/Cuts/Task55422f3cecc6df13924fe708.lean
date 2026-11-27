import Mathlib

/-!
# `Conjectures.Cuts.Task55422f3cecc6df13924fe708`

For any positive real constants `C` and `ε`, all sufficiently large natural
numbers `X` satisfy `C · X ≤ ε · X · log X`.

Elementary: `log` is monotone and unbounded, so taking the threshold
`X₀ = ⌈exp (C / ε)⌉₊` works, `X ≥ X₀` giving `log X ≥ C / ε` and hence
`C ≤ ε · log X`; multiplying by `X ≥ 0` gives the statement.
-/

namespace Conjectures.Cuts.Task55422f3cecc6df13924fe708_aux

/-- Threshold version of the growth of the logarithm: with `X₀ = ⌈exp (C / ε)⌉₊`,
every `X ≥ X₀` satisfies `C ≤ ε * log X`. -/
theorem le_mul_log_of_ge_exp (C ε : ℝ) (hε : 0 < ε) :
    ∀ (X : ℕ), ⌈Real.exp (C / ε)⌉₊ ≤ X → C ≤ ε * Real.log (X : ℝ) := by
  intro X hX
  have hceil : Real.exp (C / ε) ≤ (⌈Real.exp (C / ε)⌉₊ : ℝ) := Nat.le_ceil _
  have hXle : Real.exp (C / ε) ≤ (X : ℝ) := hceil.trans (by exact_mod_cast hX)
  have hpos : 0 < (X : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hXle
  have hlog : Real.log (Real.exp (C / ε)) ≤ Real.log (X : ℝ) :=
    Real.log_le_log (Real.exp_pos _) hXle
  rw [Real.log_exp] at hlog
  have hmul : ε * (C / ε) ≤ ε * Real.log (X : ℝ) :=
    mul_le_mul_of_nonneg_left hlog hε.le
  rwa [mul_div_cancel₀ _ hε.ne'] at hmul

end Conjectures.Cuts.Task55422f3cecc6df13924fe708_aux

theorem Conjectures.Cuts.Task55422f3cecc6df13924fe708 :
    ∀ (x1 : ℝ), (0 : ℝ) < x1 → ∀ (x3 : ℝ), (0 : ℝ) < x3 → ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → x1 * ↑x6 ≤ x3 * ↑x6 * Real.log ↑x6 := by
  intro x1 _ x3 hx3
  refine ⟨⌈Real.exp (x1 / x3)⌉₊, ?_⟩
  intro x6 hx6
  have hlog : x1 ≤ x3 * Real.log (x6 : ℝ) :=
    Conjectures.Cuts.Task55422f3cecc6df13924fe708_aux.le_mul_log_of_ge_exp x1 x3 hx3 x6 hx6
  have hX0 : (0 : ℝ) ≤ (x6 : ℝ) := Nat.cast_nonneg x6
  calc x1 * (x6 : ℝ) ≤ (x3 * Real.log (x6 : ℝ)) * (x6 : ℝ) :=
        mul_le_mul_of_nonneg_right hlog hX0
    _ = x3 * (x6 : ℝ) * Real.log (x6 : ℝ) := by ring
