import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_finite_even_ceiling_handoff :
    ∀ (X : ℝ) (n : ℕ), 0 ≤ X → Even n → X ≤ n → 2*⌈X/2⌉₊ ≤ n := by
  intro X n _ hn hX
  obtain ⟨k, hk⟩ := hn
  subst n
  have h : X / 2 ≤ (k : ℝ) := by
    push_cast at hX
    linarith
  have hc := Nat.ceil_le.mpr h
  omega
