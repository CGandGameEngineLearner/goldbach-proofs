import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Group.Nat.Even
import PEqualNP.Defs

theorem PEqualNP.Outside.L_goldbach_finite_even_ceiling_handoff :
    ∀ (X : ℝ) (n : ℕ), 0 ≤ X → Even n → X ≤ n → 2*⌈X/2⌉₊ ≤ n := by
  intro X n hX hEven hXn
  obtain ⟨k, rfl⟩ := hEven
  have hcast : ((2*k : ℕ) : ℝ) = (k : ℝ) * 2 := by
    push_cast
    ring
  have h1 : X / 2 ≤ (k : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), ← hcast]
    simp only [Nat.two_mul]
    exact hXn
  have h3 : (⌈X/2⌉₊ : ℕ) ≤ k := Nat.ceil_le.2 h1
  omega
