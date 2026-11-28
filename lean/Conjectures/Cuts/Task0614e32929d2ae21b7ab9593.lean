import Mathlib

theorem Conjectures.Cuts.Task0614e32929d2ae21b7ab9593 : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊(↑x6 : ℝ) ^ (2 / 5 : ℝ)⌋₊; ∀ (x7 : ℕ), (↑{x8 ∈ x5 x7 | x8.minFac ≤ x6 x7 ∧ (x7 - x8).minFac ≤ x6 x7}.card : ℝ) ≤ (↑(x5 x7).card : ℝ)) := by
  intro x7
  dsimp only
  intro x7
  exact_mod_cast Finset.card_filter_le _ _
