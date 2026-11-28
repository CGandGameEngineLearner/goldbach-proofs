import Mathlib
import Conjectures.Goldbach.RoughFifthMass
import Conjectures.Goldbach.RoughFifthSquareError

open Filter Finset
open scoped Topology

private noncomputable def roughC (N : ℕ) : Finset ℕ :=
  (range N).filter (fun p => Nat.Prime p ∧ N < 3*p ∧ 3*p < 2*N ∧
    1 < N-p ∧ N < (N-p).minFac^5)

private theorem rough_assembly
    (mass : ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      c*(N:ℝ) ≤ ((roughC N).card:ℝ)*(Real.log (N:ℝ))^2)
    (cost : ∀ N z : ℕ, 1 ≤ z → z^5 ≤ N →
      z*((roughC N).filter (fun p => ¬ Squarefree (N-p))).card ≤ N) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      (((roughC N).filter (fun p => ¬Squarefree (N-p))).card:ℝ) ≤ ε * (roughC N).card := by
  obtain ⟨c, hc, N₀, hmass⟩ := mass
  intro ε hε
  have hlog := (isLittleO_log_rpow_rpow_atTop (2:ℝ)
    (show (0:ℝ) < 1/6 by norm_num)).bound (show 0 < ε*c/2 by positivity)
  have hlognat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hlog
  have hpow : Tendsto (fun N : ℕ => (N:ℝ)^(1/6:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (show (0:ℝ) < 1/6 by norm_num)).comp tendsto_natCast_atTop_atTop
  apply eventually_atTop.mp
  filter_upwards [hlognat, hpow.eventually_ge_atTop 2,
    eventually_ge_atTop (max N₀ 2)] with N hlogN hpowN hN heven
  let z := ⌊(N:ℝ)^(1/6:ℝ)⌋₊
  have hN₂ : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hz_lower : (N:ℝ)^(1/6:ℝ) / 2 ≤ (z:ℝ) := by
    have hfloor := Nat.lt_floor_add_one ((N:ℝ)^(1/6:ℝ))
    dsimp [z]
    linarith
  have hz : 1 ≤ z := by
    have hzR : (1:ℝ) ≤ z := by linarith
    exact_mod_cast hzR
  have hz_pow : z^5 ≤ N := by
    have hle : (z:ℝ) ≤ (N:ℝ)^(1/6:ℝ) := Nat.floor_le (by positivity)
    have hn : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hr : (z:ℝ)^5 ≤ (N:ℝ) := calc
      _ ≤ ((N:ℝ)^(1/6:ℝ))^5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hle 5
      _ = (N:ℝ)^(5/6:ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ N)]
        norm_num
      _ ≤ (N:ℝ)^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
      _ = _ := Real.rpow_one _
    exact_mod_cast hr
  have hL : (Real.log (N:ℝ))^2 ≤ ε*c*(z:ℝ) := by
    have hb : (Real.log (N:ℝ))^2 ≤ ε*c/2 * (N:ℝ)^(1/6:ℝ) := by
      simpa only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (N:ℝ))),
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using hlogN
    nlinarith [mul_le_mul_of_nonneg_left hz_lower (show 0 ≤ ε*c by positivity)]
  have hLpos : 0 < (Real.log (N:ℝ))^2 := by
    have : (1:ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    exact sq_pos_of_pos (Real.log_pos this)
  have hcost : (z:ℝ) * (((roughC N).filter (fun p => ¬Squarefree (N-p))).card:ℝ) ≤ N := by
    exact_mod_cast cost N z hz hz_pow
  have hmain := hmass N hN₀ heven
  have hbad : (0:ℝ) ≤ (((roughC N).filter (fun p => ¬Squarefree (N-p))).card:ℝ) := by positivity
  have hbound := mul_le_mul_of_nonneg_left hL hbad
  have hcost' := mul_le_mul_of_nonneg_left hcost (show 0 ≤ ε*c by positivity)
  have hmain' := mul_le_mul_of_nonneg_left hmain hε.le
  nlinarith


theorem Conjectures.Cuts.Task8abdb25a2b9c6aa06ea8ab0c : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)}; ∀ (x2 : ℝ), (0 : ℝ) < x2 → ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → Even x5 → ↑{x8 ∈ x1 x5 | ¬Squarefree (x5 - x8)}.card ≤ x2 * ↑(x1 x5).card) := by
  simpa only [roughC] using rough_assembly Conjectures.Goldbach.RoughFifthMass Conjectures.Goldbach.RoughFifthSquareError
