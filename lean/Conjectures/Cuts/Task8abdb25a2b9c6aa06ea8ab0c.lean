import Mathlib
import Conjectures.Goldbach.RoughFifthMass
import Conjectures.Goldbach.RoughFifthSquareError

open Filter

private theorem choose_cutoff (d : ℝ) (hd : 0 < d) :
    ∃ K : ℕ, ∀ n ≥ K, ∃ z : ℕ, 1 ≤ z ∧ z^5 ≤ n ∧
      (Real.log (n : ℝ))^2 ≤ d * (z : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0:ℝ) < 1 / 5)).bound
    (show (0:ℝ) < d / 2 by positivity)
  apply eventually_atTop.mp
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually h,
    eventually_ge_atTop (1 : ℕ)] with n hn hn₁
  have hn₀ : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hn₁' : 1 ≤ (n : ℝ) := by exact_mod_cast hn₁
  let t := (n : ℝ) ^ (1 / 5 : ℝ)
  let z := ⌊t⌋₊
  have ht : 1 ≤ t := Real.one_le_rpow hn₁' (by norm_num)
  have hz : 1 ≤ z := (Nat.one_le_floor_iff t).mpr ht
  have hz' : 1 ≤ (z : ℝ) := by exact_mod_cast hz
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have hlog : (Real.log (n : ℝ))^2 ≤ (d / 2) * t := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (n : ℝ))),
      abs_of_nonneg ht₀, t] using hn
  refine ⟨z, hz, ?_, ?_⟩
  · have hpow : (z : ℝ)^5 ≤ (n : ℝ) := calc
      _ ≤ t ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le ht₀) _
      _ = (n : ℝ) := by
        dsimp [t]
        rw [← Real.rpow_mul_natCast hn₀]
        norm_num
    exact_mod_cast hpow
  · have hlt : t < (z : ℝ) + 1 := Nat.lt_floor_add_one t
    exact hlog.trans (by nlinarith only [mul_nonneg hd.le (show 0 ≤ 2 * (z : ℝ) - t by linarith)])

theorem Conjectures.Cuts.Task8abdb25a2b9c6aa06ea8ab0c : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)}; ∀ (x2 : ℝ), (0 : ℝ) < x2 → ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → Even x5 → ↑{x8 ∈ x1 x5 | ¬Squarefree (x5 - x8)}.card ≤ x2 * ↑(x1 x5).card) := by
  intro C ε hε
  obtain ⟨c, hc, N₁, hmass⟩ := Conjectures.Goldbach.RoughFifthMass
  obtain ⟨K, hcut⟩ := choose_cutoff (ε * c) (mul_pos hε hc)
  refine ⟨max N₁ K, ?_⟩
  intro n hn heven
  obtain ⟨z, hz, hpow, hlog⟩ := hcut n ((le_max_right _ _).trans hn)
  let B := (C n).filter (fun p => ¬ Squarefree (n - p))
  have hs : z * B.card ≤ n :=
    Conjectures.Goldbach.RoughFifthSquareError n z hz hpow
  have hsR : (z : ℝ) * (B.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hs
  have hm : c * (n : ℝ) ≤ ((C n).card : ℝ) * (Real.log (n : ℝ)) ^ 2 :=
    hmass n ((le_max_left _ _).trans hn) heven
  have hzR : 0 < (z : ℝ) := by exact_mod_cast (show 0 < z by omega)
  change (B.card : ℝ) ≤ ε * ((C n).card : ℝ)
  apply le_of_mul_le_mul_left (a := c * (z : ℝ)) _ (mul_pos hc hzR)
  calc
    (c * (z : ℝ)) * (B.card : ℝ) = c * ((z : ℝ) * (B.card : ℝ)) := by ring
    _ ≤ c * n := mul_le_mul_of_nonneg_left hsR hc.le
    _ ≤ ((C n).card : ℝ) * (Real.log (n : ℝ)) ^ 2 := hm
    _ ≤ ((C n).card : ℝ) * ((ε * c) * (z : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ = (c * (z : ℝ)) * (ε * ((C n).card : ℝ)) := by ring
