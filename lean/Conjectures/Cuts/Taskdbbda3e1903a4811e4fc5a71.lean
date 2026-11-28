import Mathlib

namespace Conjectures.Cuts.Taskdbbda3e1903a4811e4fc5a71_aux

private theorem card_two_sided_le
    (s : Finset ℕ) (n : ℕ) :
    ((Finset.filter (fun m => n - m ∈ s) s).card : ℝ) ≤ (s.card : ℝ) := by
  have hsub : Finset.filter (fun m => n - m ∈ s) s ⊆ s := Finset.filter_subset _ _
  exact_mod_cast Finset.card_le_card hsub

end Conjectures.Cuts.Taskdbbda3e1903a4811e4fc5a71_aux

theorem Conjectures.Cuts.Taskdbbda3e1903a4811e4fc5a71 :
    have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∀ (x5 : ℕ), (↑{x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}.card : ℝ) ≤ (↑(x3 x5).card : ℝ) := by
  intro x1 x2 x3 x4 x5
  exact Conjectures.Cuts.Taskdbbda3e1903a4811e4fc5a71_aux.card_two_sided_le (x3 x5) x5
