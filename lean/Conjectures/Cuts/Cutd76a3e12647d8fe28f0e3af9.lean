import Mathlib
import Conjectures.Goldbach.FareyLateFirstHitFactorSwitch
import Conjectures.Goldbach.FareyLatePrimeSquareLoss

-- child 1 zh: 双侧立方根粗糙半素数配对本身至多占终筛体积的 2/25。
-- child 1 en: The two-sided cube-root-rough semiprime pairing occupies at most 2/25 of the final sieve volume.
-- child 2 zh: 额外的小素因子截断只是子集条件，故计数不超过双侧配对计数。
-- child 2 en: The small-prime-factor truncation only refines the set, so the count is at most the two-sided pairing count.

theorem Conjectures.Cuts.Cutd76a3e12647d8fe28f0e3af9
    (h₁ : have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊(↑x6 : ℝ) ^ (2 / 5 : ℝ)⌋₊; ∃ (x7 : ℕ), ∀ (x8 : ℕ), x7 ≤ x8 → Even x8 → (↑(x5 x8).card : ℝ) ≤ (2 / 25 : ℝ) * x4 x8)
    (h₂ : have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊(↑x6 : ℝ) ^ (2 / 5 : ℝ)⌋₊; ∀ (x8 : ℕ), (↑{x11 ∈ x5 x8 | x11.minFac ≤ x6 x8 ∧ (x8 - x11).minFac ≤ x6 x8}.card : ℝ) ≤ (↑(x5 x8).card : ℝ)) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊(↑x6 : ℝ) ^ (2 / 5 : ℝ)⌋₊; ∃ (x7 : ℕ), ∀ (x8 : ℕ), x7 ≤ x8 → Even x8 → (↑{x11 ∈ x5 x8 | x11.minFac ≤ x6 x8 ∧ (x8 - x11).minFac ≤ x6 x8}.card : ℝ) ≤ (2 / 25 : ℝ) * x4 x8) := by
  obtain ⟨N0, hN0⟩ := h₁
  refine ⟨N0, ?_⟩
  intro n hn hEven
  exact le_trans (h₂ n) (hN0 n hn hEven)
