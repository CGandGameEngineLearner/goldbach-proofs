import Mathlib

namespace Conjectures.Cuts.Task4512d8b138116b8d04f0f5b0_aux

private theorem card_refine_le
    (s : Finset ℕ) (n a b : ℕ) :
    ((Finset.filter
        (fun m => m.minFac ≤ a ∧ (n - m).minFac ≤ a ∧ (b < m.minFac ∨ b < (n - m).minFac)) s).card : ℝ) ≤
      (s.card : ℝ) := by
  have hsub : Finset.filter
        (fun m => m.minFac ≤ a ∧ (n - m).minFac ≤ a ∧ (b < m.minFac ∨ b < (n - m).minFac)) s ⊆ s :=
    Finset.filter_subset _ _
  exact_mod_cast Finset.card_le_card hsub

end Conjectures.Cuts.Task4512d8b138116b8d04f0f5b0_aux

theorem Conjectures.Cuts.Task4512d8b138116b8d04f0f5b0 :
    have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊Real.exp (Real.log (↑x6 : ℝ) / (2 : ℝ) - (2 : ℝ) * Real.log (↑x6 : ℝ) ^ (2 / 3 : ℝ))⌋₊; have x7 : ℕ → ℕ := fun (x7 : ℕ) => ⌊(↑x7 : ℝ) ^ (2 / 5 : ℝ)⌋₊; ∀ (x8 : ℕ), (↑{x9 ∈ x5 x8 | x9.minFac ≤ x6 x8 ∧ (x8 - x9).minFac ≤ x6 x8 ∧ (x7 x8 < x9.minFac ∨ x7 x8 < (x8 - x9).minFac)}.card : ℝ) ≤ (↑(x5 x8).card : ℝ) := by
  intro x1 x2 x3 x4 x5 x6 x7 x8
  exact Conjectures.Cuts.Task4512d8b138116b8d04f0f5b0_aux.card_refine_le (x5 x8) x8 (x6 x8) (x7 x8)
