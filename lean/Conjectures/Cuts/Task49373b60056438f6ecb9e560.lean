import Mathlib

theorem Conjectures.Cuts.Task49373b60056438f6ecb9e560 : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → ℝ → ℂ := fun (x5 : ℕ) (x6 : ℝ) => x3 x5 x1 x6 ^ (2 : ℕ) * x2 (-(↑x5 : ℝ) * x6); have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊(↑x6 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x7 : ℕ → ℕ := fun (x7 : ℕ) => (256 : ℕ) * x6 x7 * x4 x7; have x8 : ℕ → Set ℝ := fun (x8 : ℕ) => {x9 : ℝ | ∃ (x10 : ℕ) (x11 : ℕ), (1 : ℕ) ≤ x10 ∧ x10 ≤ x6 x8 ∧ x11 ≤ x10 ∧ x11.Coprime x10 ∧ |x9 - (↑x11 : ℝ) / (↑x10 : ℝ)| ≤ (↑(x7 x8) : ℝ) / ((↑x10 : ℝ) * (↑x8 : ℝ))}; have x9 : ℕ → ℂ := fun (x9 : ℕ) => ∫ (x10 : ℝ) in (0 : ℝ)..(1 : ℝ), (x8 x9)ᶜ.indicator (x5 x9) x10; have x10 : ℕ → ℕ → ℂ := fun (x10 x11 : ℕ) => ∫ (x12 : ℝ) in (0 : ℝ)..(1 : ℝ), (x8 x10)ᶜ.indicator (fun (x13 : ℝ) => x3 x10 x1 x13 ^ (2 : ℕ) * x2 (-(↑x11 : ℝ) * x13)) x12; ∀ (x11 : ℝ), (0 : ℝ) < x11 → ∃ (x13 : ℝ) (x14 : ℕ), (0 : ℝ) < x13 ∧ ∀ (x15 : ℕ), x14 ≤ x15 → Even x15 → -(x11 / (2 : ℝ)) * (↑x15 : ℝ) ≤ (x9 x15).re → ∃ (x19 : ℕ → ℝ), (∀ (x20 : ℕ), (0 : ℝ) ≤ x19 x20) ∧ (∑ x20 ∈ Finset.Icc x15 ((2 : ℕ) * x15), x19 x20 ^ (2 : ℕ)) * (↑x15 : ℝ) ^ ((8 / 3 : ℝ) + (1 : ℝ)) ≤ (x11 / (2 : ℝ) * (↑x15 : ℝ)) ^ (2 : ℕ) ∧ ∑ x20 ∈ Finset.Icc x15 ((2 : ℕ) * x15), x19 x20 * (x10 x15 x20).re - x11 / (2 : ℝ) * (↑x15 : ℝ) ≤ (x9 x15).re) := by
  dsimp only
  intro ε hε
  refine ⟨1, 0, by norm_num, ?_⟩
  intro n _ _ hfloor
  refine ⟨fun _ => 0, fun _ => le_rfl, ?_, ?_⟩
  · simp [sq_nonneg]
  · simpa only [zero_mul, Finset.sum_const_zero, zero_sub, neg_mul] using hfloor
