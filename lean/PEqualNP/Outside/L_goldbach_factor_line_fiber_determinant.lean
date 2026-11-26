import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_line_fiber_determinant :
    ∀ (a b N r₀ s₀ g i j : ℤ), 0 < g → g ∣ a → g ∣ b → a*r₀+b*s₀=N → (r₀+(b/g)*i)*(s₀-(a/g)*j)-(r₀+(b/g)*j)*(s₀-(a/g)*i)=-(N/g)*(j-i) := by
  intro a b N r₀ s₀ g i j hg hga hgb hN
  obtain ⟨A, hA⟩ := hga
  obtain ⟨B, hB⟩ := hgb
  subst hA
  subst hB
  have hg0 : g ≠ 0 := ne_of_gt hg
  have hN' : N = g * (A * r₀ + B * s₀) := by rw [← hN]; ring
  rw [hN', Int.mul_ediv_cancel_left (A * r₀ + B * s₀) hg0,
      Int.mul_ediv_cancel_left B hg0, Int.mul_ediv_cancel_left A hg0]
  ring
