import Mathlib

-- child 1 zh: 对任意正容差，从某个阈值起，[n,2n] 上的均匀权满足指数余量 η=1/6 的平方和预算。
-- child 1 en: For every positive tolerance, the uniform weights on [n,2n] eventually meet the squared-norm budget with exponent margin 1/6.
-- child 2 zh: 对充分大的偶数 n，深次弧系数实部在 [n,2n] 上的算术平均超过第 n 项实部的量至多为 εn/2。
-- child 2 en: For sufficiently large even n, the mean real deep-minor coefficient on [n,2n] exceeds its value at n by at most εn/2, for each ε > 0.

theorem Conjectures.Cuts.Cut1da93ece62a9a4efec5a1fc0
    (h₁ : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      (n : ℝ) ^ (8 / 3 + 1 / 6 : ℝ) / (n + 1) ≤ ((ε / 2) * n) ^ 2)
    (h₂ : let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
          let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
          let S := fun (n : ℕ) (t : ℝ) =>
            ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t)
          let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
          let B := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
          let H := fun n : ℕ => 256 * B n * Q n
          let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ,
            1 ≤ q ∧ q ≤ B n ∧ a ≤ q ∧ a.Coprime q ∧
            |t - (a : ℝ) / q| ≤ (H n : ℝ) / ((q : ℝ) * n)}
          let c := fun (n m : ℕ) => (intervalIntegral
            (fun t => (arcs n)ᶜ.indicator (fun u => (S n u)^2 * E (-(m : ℝ) * u)) t)
            (0 : ℝ) 1 MeasureTheory.volume).re
          ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, Even n →
            (1 / ((n : ℝ) + 1)) * (∑ m ∈ Finset.Icc n (2 * n), c n m) -
              (ε / 2) * n ≤ c n n) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let deepMinor := fun n : ℕ => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; let deepCoeff := fun (n m : ℕ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun u => (S n w u)^2 * E (-(m:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ (η : ℝ) (N : ℕ), 0 < η ∧ ∀ n : ℕ, N ≤ n → Even n → ∃ ω : ℕ → ℝ, (∀ m : ℕ, 0 ≤ ω m) ∧ ((∑ m ∈ Finset.Icc n (2 * n), (ω m) ^ 2) * (n : ℝ) ^ (8 / 3 + η) ≤ ((e / 2) * (n : ℝ)) ^ 2) ∧ (∑ m ∈ Finset.Icc n (2 * n), ω m * (deepCoeff n m).re) - (e / 2) * (n : ℝ) ≤ (deepMinor n).re) := by
  intro w E S Q f B H arcs deepMinor deepCoeff ε hε
  obtain ⟨N₁, bound⟩ := h₁ ε hε
  obtain ⟨N₂, mean⟩ := h₂ ε hε
  refine ⟨1 / 6, max N₁ N₂, by norm_num, ?_⟩
  intro n hn heven
  refine ⟨fun _ => 1 / ((n : ℝ) + 1), fun _ => by positivity, ?_, ?_⟩
  · have card : (Finset.Icc n (2 * n)).card = n + 1 := by rw [Nat.card_Icc]; omega
    rw [Finset.sum_const, nsmul_eq_mul, card, Nat.cast_add_one]
    calc
      _ = (n : ℝ) ^ (8 / 3 + 1 / 6 : ℝ) / (n + 1) := by
        field_simp
      _ ≤ _ := bound n (le_trans (le_max_left _ _) hn)
  · rw [← Finset.mul_sum]
    exact mean n (le_trans (le_max_right _ _) hn) heven
