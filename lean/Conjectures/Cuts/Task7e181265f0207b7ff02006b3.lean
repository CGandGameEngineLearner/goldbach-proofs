import Conjectures.Cuts.Task1ebcbc34ab48b907b922baf3

theorem Conjectures.Cuts.Task7e181265f0207b7ff02006b3 :
have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x1) : ℂ) * Complex.I); have x2 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℕ → ℝ) (x4 : ℝ) => ∑ x5 ∈ Finset.range (x2 + (1 : ℕ)), (↑(x3 x5) : ℂ) * x1 ((↑x5 : ℝ) * x4); have x3 : ℕ → ℕ := fun (x3 : ℕ) => Nat.log (2 : ℕ) (x3 + (2 : ℕ)) ^ (2 : ℕ); have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊(↑x4 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x5 : ℕ → ℕ := fun (x5 : ℕ) => (256 : ℕ) * x4 x5 * x3 x5; have x6 : ℕ → Set ℝ := fun (x6 : ℕ) => {x7 : ℝ | ∃ (x8 : ℕ) (x9 : ℕ), (1 : ℕ) ≤ x8 ∧ x8 ≤ x4 x6 ∧ x9 ≤ x8 ∧ x9.Coprime x8 ∧ |x7 - (↑x9 : ℝ) / (↑x8 : ℝ)| ≤ (↑(x5 x6) : ℝ) / ((↑x8 : ℝ) * (↑x6 : ℝ))}; have x7 : ArithmeticFunction ℝ := ArithmeticFunction.vonMangoldt; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (↑((ArithmeticFunction.moebius : ℕ → ℤ) x8) : ℝ); have x9 : ℕ → ℕ := fun (x9 : ℕ) => ⌊(↑x9 : ℝ) ^ (1 / 16 : ℝ)⌋₊; have x10 : ℕ → ℕ := fun (x10 : ℕ) => ⌊(↑x10 : ℝ) ^ (1 / 4 : ℝ)⌋₊; have x11 : ℕ → ℕ := fun (x11 : ℕ) => ⌊(↑x11 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x12 : ℕ → ℕ := fun (x12 : ℕ) => ⌊(↑x12 : ℝ) ^ (2 / 3 : ℝ)⌋₊; have x13 : ℕ → ℕ → ℝ := fun (x13 x14 : ℕ) => ∑ x15 ∈ x14.divisors with x9 x13 < x15 ∧ x15 ≤ x10 x13 ∧ x9 x13 < x14 / x15, (∑ x16 ∈ x15.divisors with x9 x13 < x16, x8 x16) * (x7 : ℕ → ℝ) (x14 / x15); have x14 : ℕ → ℕ → ℝ := fun (x14 x15 : ℕ) => ∑ x16 ∈ x15.divisors with x11 x14 < x16 ∧ x16 ≤ x12 x14 ∧ x9 x14 < x15 / x16, (∑ x17 ∈ x16.divisors with x9 x14 < x17, x8 x17) * (x7 : ℕ → ℝ) (x15 / x16); have x15 : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℂ := fun (x15 : ℕ) (x16 x17 : ℕ → ℝ) => ∫ (x18 : ℝ) in (0 : ℝ)..(1 : ℝ), (x6 x15)ᶜ.indicator (fun (x19 : ℝ) => x2 x15 x16 x19 * x2 x15 x17 x19 * x1 (-(↑x15 : ℝ) * x19)) x18; ∀ (x16 : ℝ), (0 : ℝ) < x16 → ∃ (x18 : ℕ), ∀ (x19 : ℕ), x18 ≤ x19 → Even x19 → |(x15 x19 (x13 x19) (x14 x19)).im| ≤ x16 * (↑x19 : ℝ) / (2 : ℝ) := by
  intro E S Q B H wide Λ μ U B₁ B₂ B₃ τ₁ τ₃ J ε hε
  refine ⟨0, fun n _ _ => ?_⟩
  have hz : (J n (τ₁ n) (τ₃ n)).im = 0 :=
    RationalArcReflection.imaginary_part_zero (B n) n
      (fun q => (H n : ℝ) / ((q:ℝ)*n)) (τ₁ n) (τ₃ n)
  rw [hz, abs_zero]
  positivity
