import Mathlib

theorem PEqualNP.Outside.L_goldbach_moving_weights_window_diff :
    ∀ (a : ℕ → ℂ) (u v : ℕ), u≤v → (∑ k ∈ Finset.Ico u v,a k)=(∑ k ∈ Finset.range v,a k)-(∑ k ∈ Finset.range u,a k) := by
  intro a u v h
  -- Mathlib 现成引理（ℂ 为 AddCommGroup）：
  -- Finset.sum_Ico_eq_sub (f : ℕ → δ) (h : m ≤ n) :
  --   ∑ k ∈ Finset.Ico m n, f k = ∑ k ∈ Finset.range n, f k - ∑ k ∈ Finset.range m, f k
  exact Finset.sum_Ico_eq_sub a h
