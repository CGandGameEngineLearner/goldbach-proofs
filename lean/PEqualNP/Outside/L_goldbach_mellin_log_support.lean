import Mathlib

theorem PEqualNP.Outside.L_goldbach_mellin_log_support :
    ∀ (φ : ℝ → ℝ) (a b : ℝ), 0<a → a<b → (∀ u, u<a ∨ b<u → φ u=0) → let F := fun x => Real.exp (x/2)*φ (Real.exp x); (∀ x, x<Real.log a ∨ Real.log b<x → F x=0) ∧ HasCompactSupport F := by
  intro φ a b ha hab hφ
  let F (x : ℝ) := Real.exp (x / 2) * φ (Real.exp x)
  have outside (x : ℝ) (hx : x < Real.log a ∨ Real.log b < x) : F x = 0 := by
    have h : Real.exp x < a ∨ b < Real.exp x := hx.imp
      (Real.lt_log_iff_exp_lt ha).mp (Real.log_lt_iff_lt_exp (ha.trans hab)).mp
    simp only [F, hφ _ h, mul_zero]
  refine ⟨outside, HasCompactSupport.intro (isCompact_Icc (a := Real.log a) (b := Real.log b)) ?_⟩
  intro x hx
  apply outside
  rcases lt_or_ge x (Real.log a) with hleft | hleft
  · exact Or.inl hleft
  · exact Or.inr (lt_of_not_ge fun hright => hx ⟨hleft, hright⟩)
