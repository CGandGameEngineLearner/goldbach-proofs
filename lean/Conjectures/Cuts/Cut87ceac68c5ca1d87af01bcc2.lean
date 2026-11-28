import Mathlib
import Conjectures.Goldbach.FareyLateFirstHitFactorSwitch
import Conjectures.Goldbach.FareyLatePrimeSquareLoss

-- child 1 zh: 中央窗内立方根粗糙半素数（单侧）的计数本身至多占终筛体积的 23/50。
-- child 1 en: The one-sided count of cube-root-rough semiprimes in the central window occupies at most 23/50 of the final sieve volume.
-- child 2 zh: 双侧条件只是单侧集合的子集，故双侧计数不超过单侧计数。
-- child 2 en: The two-sided condition refines the one-sided set, so the two-sided count is at most the one-sided count.

theorem Conjectures.Cuts.Cut87ceac68c5ca1d87af01bcc2
    (h₁ : have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → Even x6 → (↑(x3 x6).card : ℝ) ≤ (23 / 50 : ℝ) * x4 x6)
    (h₂ : have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∀ (x6 : ℕ), (↑{x9 ∈ x3 x6 | x6 - x9 ∈ x3 x6}.card : ℝ) ≤ (↑(x3 x6).card : ℝ)) :
    (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | x2 x3 < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x4.sqrt) with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); ∃ (x5 : ℕ), ∀ (x6 : ℕ), x5 ≤ x6 → Even x6 → (↑{x9 ∈ x3 x6 | x6 - x9 ∈ x3 x6}.card : ℝ) ≤ (23 / 50 : ℝ) * x4 x6) := by
  obtain ⟨N0, hN0⟩ := h₁
  refine ⟨N0, ?_⟩
  intro n hn hEven
  exact le_trans (h₂ n) (hN0 n hn hEven)
