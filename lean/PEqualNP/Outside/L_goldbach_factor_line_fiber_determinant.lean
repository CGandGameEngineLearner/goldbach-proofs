import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_line_fiber_determinant :
    ∀ (a b N r₀ s₀ g i j : ℤ), 0 < g → g ∣ a → g ∣ b → a*r₀+b*s₀=N → (r₀+(b/g)*i)*(s₀-(a/g)*j)-(r₀+(b/g)*j)*(s₀-(a/g)*i)=-(N/g)*(j-i) := by
  intro a b N r s g i j hg ha hb hn
  obtain ⟨A, rfl⟩ := ha
  obtain ⟨B, rfl⟩ := hb
  have hne : g ≠ 0 := ne_of_gt hg
  have hN : N = g * (A*r + B*s) := by nlinarith
  rw [hN]
  simp only [Int.mul_ediv_cancel_left _ hne]
  ring
