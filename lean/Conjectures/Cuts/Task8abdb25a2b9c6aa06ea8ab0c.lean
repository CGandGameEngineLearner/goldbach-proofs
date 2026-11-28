import Mathlib
import Conjectures.Goldbach.RoughFifthMass
import Conjectures.Goldbach.RoughFifthSquareError

open Filter

theorem Conjectures.Cuts.Task8abdb25a2b9c6aa06ea8ab0c : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => {x2 ∈ Finset.range x1 | Nat.Prime x2 ∧ x1 < (3 : ℕ) * x2 ∧ (3 : ℕ) * x2 < (2 : ℕ) * x1 ∧ (1 : ℕ) < x1 - x2 ∧ x1 < (x1 - x2).minFac ^ (5 : ℕ)}; ∀ (x2 : ℝ), (0 : ℝ) < x2 → ∃ (x4 : ℕ), ∀ (x5 : ℕ), x4 ≤ x5 → Even x5 → ↑{x8 ∈ x1 x5 | ¬Squarefree (x5 - x8)}.card ≤ x2 * ↑(x1 x5).card) := by
  intro candidates ε hε
  obtain ⟨c, hc, M, hmass⟩ := Conjectures.Goldbach.RoughFifthMass
  have hcoefficient : 0 < ε * c / 2 := half_pos (mul_pos hε hc)
  have hlog := (Asymptotics.isLittleO_iff.mp
    (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : 0 < (1 / 5 : ℝ)))) hcoefficient
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hcast.eventually hlog)
  have htends : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 5 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 5 : ℝ))).comp hcast
  obtain ⟨B, hB⟩ := eventually_atTop.mp (htends.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨max (max M K) (max B 2), fun n hn heven => ?_⟩
  have hnM : M ≤ n := by omega
  have hnK : K ≤ n := by omega
  have hnB : B ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  let r : ℝ := (n : ℝ) ^ (1 / 5 : ℝ)
  let z : ℕ := ⌊r⌋₊
  have hr : 2 ≤ r := hB n hnB
  have hrNonneg : 0 ≤ r := by linarith
  have hz : 1 ≤ z := Nat.le_floor (by norm_num; linarith)
  have hfloor : (z : ℝ) ≤ r := Nat.floor_le hrNonneg
  have hfloor' : r < (z : ℝ) + 1 := Nat.lt_floor_add_one r
  have hzLower : r / 2 ≤ (z : ℝ) := by linarith
  have hroot : r ^ 5 = (n : ℝ) := by
    dsimp [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hzPow : z ^ 5 ≤ n := by
    exact_mod_cast (show (z : ℝ) ^ 5 ≤ (n : ℝ) from hroot ▸ pow_le_pow_left₀ (Nat.cast_nonneg z) hfloor 5)
  have hlogBound : Real.log (n : ℝ) ^ 2 ≤ (ε * c / 2) * r := by
    have h := hK n hnK
    change ‖Real.log (n : ℝ) ^ (2 : ℝ)‖ ≤ (ε * c / 2) * ‖r‖ at h
    simpa only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (n : ℝ))),
      abs_of_nonneg hrNonneg] using h
  have hlogZ : Real.log (n : ℝ) ^ 2 ≤ ε * c * (z : ℝ) := by
    calc
      _ ≤ (ε * c / 2) * r := hlogBound
      _ = ε * c * (r / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hzLower (mul_pos hε hc).le
  let bad := ((candidates n).filter (fun p => ¬ Squarefree (n - p))).card
  have hbad : z * bad ≤ n := Conjectures.Goldbach.RoughFifthSquareError n z hz hzPow
  have hbadReal : (z : ℝ) * (bad : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbad
  have hmassReal : c * (n : ℝ) ≤ ((candidates n).card : ℝ) * Real.log (n : ℝ)^2 :=
    hmass n hnM heven
  change (bad : ℝ) ≤ ε * ((candidates n).card : ℝ)
  have hlogPos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  apply le_of_mul_le_mul_right _ (sq_pos_of_pos hlogPos)
  calc
    (bad : ℝ) * Real.log (n : ℝ)^2 ≤ (bad : ℝ) * (ε * c * (z : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogZ (Nat.cast_nonneg bad)
    _ = ε * c * ((z : ℝ) * (bad : ℝ)) := by ring
    _ ≤ ε * c * (n : ℝ) := mul_le_mul_of_nonneg_left hbadReal (mul_pos hε hc).le
    _ = ε * (c * (n : ℝ)) := by ring
    _ ≤ ε * (((candidates n).card : ℝ) * Real.log (n : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hmassReal hε.le
    _ = _ := by ring
