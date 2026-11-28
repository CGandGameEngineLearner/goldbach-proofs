import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.NormNum

namespace GoldbachResearch

open DirichletCharacter

open Classical in
/-- The medium-skirt model regularizes the principal character at `1`. The
upstream nonvanishing theorem supplies the `13 / 14` strip needed by that model. -/
theorem skirt_regularizedL_ne_zero
    (sevenEighths : ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ},
      (7 / 8 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) → LFunction χ s ≠ 0)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (13 / 14 : ℝ) ≤ s.re) :
    (if χ = 1 then LFunctionTrivChar₁ q else LFunction χ) s ≠ 0 := by
  have hRe : (7 / 8 : ℝ) < s.re :=
    lt_of_lt_of_le (by norm_num : (7 / 8 : ℝ) < 13 / 14) hs
  by_cases hp : χ = 1
  · subst χ
    rw [ite_eq_left rfl]
    rcases eq_or_ne s 1 with rfl | hs₁
    · exact LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [LFunctionTrivChar₁, Function.update_of_ne hs₁]
      apply mul_ne_zero (sub_ne_zero.mpr hs₁)
      exact sevenEighths 1 hRe (fun h => hs₁ h.2)
  · rw [ite_eq_right hp]
    exact sevenEighths χ hRe (fun h => hp h.1)

end GoldbachResearch
