import Mathlib
import Conjectures.Goldbach.RoughFifthMass
import Conjectures.Goldbach.RoughFifthSquareError

theorem Conjectures.Cuts.Task8abdb25a2b9c6aa06ea8ab0c : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)}; ∀ (x2 : ℝ), (0 : ℝ) < x2 → ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → Even x5 → ↑{x8 ∈ x1 x5 | ¬Squarefree (x5 - x8)}.card ≤ x2 * ↑(x1 x5).card) := by
  dsimp only
  intro ε hε
  obtain ⟨c, hc, N₀, hmass⟩ := Conjectures.Goldbach.RoughFifthMass
  have hbound : ∀ᶠ (x : ℝ) in Filter.atTop,
      ‖(Real.log x) ^ (2 : ℝ)‖ ≤ (ε * c / 2) * ‖x ^ (1 / 5 : ℝ)‖ :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 5)).bound
      (by positivity : (0 : ℝ) < ε * c / 2)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hbound
  refine ⟨max N₀ (max 2 ⌈M⌉₊), ?_⟩
  intro N hN hNeven
  have hNN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  have hNM : M ≤ (N : ℝ) := by
    have h1 : ⌈M⌉₊ ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
    exact (Nat.le_ceil M).trans (by exact_mod_cast h1)
  let z : ℕ := ⌊(N : ℝ) ^ (1 / 5 : ℝ)⌋₊
  have hz_pos : 1 ≤ z :=
    Nat.floor_pos.mpr (Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ N)) (by norm_num))
  have hz5 : z ^ 5 ≤ N := by
    have h1 : (z : ℝ) ≤ (N : ℝ) ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
    have h2 : ((z ^ 5 : ℕ) : ℝ) ≤ ((N : ℝ) ^ (1 / 5 : ℝ)) ^ 5 := by
      push_cast
      exact pow_le_pow_left₀ (Nat.cast_nonneg z) h1 5
    have h3 : ((N : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      norm_num
    exact_mod_cast h2.trans_eq h3
  have hsq : z * ({x8 ∈ {x2 ∈ Finset.range N | Nat.Prime x2 ∧ N < 3 * x2 ∧ 3 * x2 < 2 * N ∧
      1 < N - x2 ∧ N < (N - x2).minFac ^ 5} | ¬Squarefree (N - x8)}).card ≤ N :=
    Conjectures.Goldbach.RoughFifthSquareError N z hz_pos hz5
  have hsqR : (z : ℝ) * (({x8 ∈ {x2 ∈ Finset.range N | Nat.Prime x2 ∧ N < 3 * x2 ∧ 3 * x2 < 2 * N ∧
      1 < N - x2 ∧ N < (N - x2).minFac ^ 5} | ¬Squarefree (N - x8)}).card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hsq
  have hC : c * (N : ℝ) ≤
      (({x2 ∈ Finset.range N | Nat.Prime x2 ∧ N < 3 * x2 ∧ 3 * x2 < 2 * N ∧
        1 < N - x2 ∧ N < (N - x2).minFac ^ 5}).card : ℝ) * (Real.log (N : ℝ)) ^ 2 :=
    hmass N hNN0 hNeven
  have hrpow_nn : 0 ≤ (N : ℝ) ^ (1 / 5 : ℝ) := by positivity
  have hlog2 : (Real.log (N : ℝ)) ^ 2 ≤ (ε * c / 2) * (N : ℝ) ^ (1 / 5 : ℝ) := by
    have h := hM (N : ℝ) hNM
    rw [Real.rpow_two, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg hrpow_nn] at h
    exact h
  have hz_half : (N : ℝ) ^ (1 / 5 : ℝ) ≤ 2 * (z : ℝ) := by
    have hlt : (N : ℝ) ^ (1 / 5 : ℝ) < (z : ℝ) + 1 := Nat.lt_floor_add_one _
    have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz_pos
    linarith
  have hlog2_z : (Real.log (N : ℝ)) ^ 2 ≤ ε * c * (z : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hz_half (by positivity : 0 ≤ ε * c / 2)
    linarith
  have hC1 : c * (N : ℝ) ≤
      (({x2 ∈ Finset.range N | Nat.Prime x2 ∧ N < 3 * x2 ∧ 3 * x2 < 2 * N ∧
        1 < N - x2 ∧ N < (N - x2).minFac ^ 5}).card : ℝ) * (ε * c * (z : ℝ)) :=
    hC.trans (mul_le_mul_of_nonneg_left hlog2_z (Nat.cast_nonneg _))
  have hsq1 : (c * (z : ℝ)) * (({x8 ∈ {x2 ∈ Finset.range N | Nat.Prime x2 ∧ N < 3 * x2 ∧ 3 * x2 < 2 * N ∧
      1 < N - x2 ∧ N < (N - x2).minFac ^ 5} | ¬Squarefree (N - x8)}).card : ℝ) ≤ c * (N : ℝ) := by
    nlinarith
  have hcomb : (c * (z : ℝ)) * (({x8 ∈ {x2 ∈ Finset.range N | Nat.Prime x2 ∧ N < 3 * x2 ∧ 3 * x2 < 2 * N ∧
      1 < N - x2 ∧ N < (N - x2).minFac ^ 5} | ¬Squarefree (N - x8)}).card : ℝ) ≤
      (c * (z : ℝ)) * (ε * (({x2 ∈ Finset.range N | Nat.Prime x2 ∧ N < 3 * x2 ∧ 3 * x2 < 2 * N ∧
        1 < N - x2 ∧ N < (N - x2).minFac ^ 5}).card : ℝ)) := by
    linarith
  have hcz : 0 < c * (z : ℝ) := mul_pos hc (by exact_mod_cast (by omega : 0 < z))
  exact le_of_mul_le_mul_left hcomb hcz
