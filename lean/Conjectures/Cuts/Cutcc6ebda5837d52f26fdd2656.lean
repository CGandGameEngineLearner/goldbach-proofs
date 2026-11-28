import Mathlib

set_option maxHeartbeats 4000000

-- child 1 zh: 深次弧：在 √n 级弧族之外（且当然在宽弧之外），指数和满足 3/4 幂界。
-- child 1 en: Deep arcs: outside the sqrt-n arc family, the exponential sum obeys the 3/4-power bound.
-- child 2 zh: 中等弧环带：落在 √n 级弧族之内、但不在 n^(1/3) 级宽弧之内时，同一 3/4 幂界。必须保留宽弧的排除：t=0 属于 √n 级弧族（q=1, a=0），而在 t=0 处该和为 θ(n)，故不带此排除的版本是假的。
-- child 2 en: The medium annulus: inside the sqrt-n arc family but outside the n^(1/3)-level wide arcs, the same 3/4-power bound. The wide-arc exclusion is essential: t = 0 lies in the sqrt-n family (q = 1, a = 0) where the sum equals theta(n), so the version without that exclusion is false.

theorem Conjectures.Cuts.Cutcc6ebda5837d52f26fdd2656
    (h₁ : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      t ∉ {x : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |x - (a : ℝ) / (q : ℝ)| ≤ ((256 * ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))} →
      ‖(∑ k ∈ Finset.range (n + 1), ((if Nat.Prime k then Real.log (k : ℝ) else 0 : ℝ) : ℂ) *
          Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I))‖ ≤ (n : ℝ) ^ (3 / 4 + η))
    (h₂ : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      t ∈ {x : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |x - (a : ℝ) / (q : ℝ)| ≤ ((256 * ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))} →
      t ∉ {x : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |x - (a : ℝ) / (q : ℝ)| ≤ ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))} →
      ‖(∑ k ∈ Finset.range (n + 1), ((if Nat.Prime k then Real.log (k : ℝ) else 0 : ℝ) : ℂ) *
          Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I))‖ ≤ (n : ℝ) ^ (3 / 4 + η)) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * t));
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2;
    let Q₁ := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊;
    let H := fun n : ℕ => 256 * Q₁ n * Q n;
    let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₁ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))};
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ wideArcs n → ‖S n w t‖ ≤ (n : ℝ) ^ (3 / 4 + η)) := by
  classical
  intro w E S Q Q₁ H wideArcs
  intro η hη
  obtain ⟨N₁, hN₁⟩ := h₁ η hη
  obtain ⟨N₂, hN₂⟩ := h₂ η hη
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn t ht hnot
  have hn₁ : N₁ ≤ n := le_trans (le_max_left N₁ N₂) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right N₁ N₂) hn
  have hsum : S n w t = ∑ k ∈ Finset.range (n + 1), ((if Nat.Prime k then Real.log (k : ℝ) else 0 : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * (k : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
    simp only [S, w, E, mul_assoc]
  have hnot' : t ∉ {x : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |x - (a : ℝ) / (q : ℝ)| ≤ ((256 * ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))} := by
    simpa only [wideArcs, Q₁, H, Q] using hnot
  by_cases hb : t ∈ {x : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊ ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |x - (a : ℝ) / (q : ℝ)| ≤ ((256 * ⌊(n : ℝ) ^ (1 / 2 : ℝ)⌋₊ * (Nat.log 2 (n + 2)) ^ 2 : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))}
  · have key := hN₂ n hn₂ t ht hb hnot'
    rw [hsum]
    exact key
  · have key := hN₁ n hn₁ t ht hb
    rw [hsum]
    exact key
