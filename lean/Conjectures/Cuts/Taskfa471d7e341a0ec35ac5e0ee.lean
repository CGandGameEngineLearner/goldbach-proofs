import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Filter Topology

theorem Conjectures.Cuts.Taskfa471d7e341a0ec35ac5e0ee : (∀ (x1 : ℝ), (0 : ℝ) < x1 → ∃ (x3 : ℕ), ∀ x4 ≥ x3, ↑x4 ^ ((8 / 3 : ℝ) + (1 / 6 : ℝ)) / (↑x4 + (1 : ℝ)) ≤ (x1 / (2 : ℝ) * ↑x4) ^ (2 : ℕ)) := by
  intro ε hε
  have decay : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1/6 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/6)).comp tendsto_natCast_atTop_atTop
  have small := decay.eventually (gt_mem_nhds (by positivity : 0 < (ε/2)^2))
  obtain ⟨N, hN⟩ := eventually_atTop.1 small
  refine ⟨max N 1, fun n hn => ?_⟩
  have hpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : (n : ℝ) ^ (-(1/6 : ℝ)) ≤ (ε/2)^2 := (hN n (by omega)).le
  apply (div_le_iff₀ (by positivity)).2
  calc
    (n : ℝ) ^ ((8/3 : ℝ) + 1/6) =
        (n : ℝ)^3 * (n : ℝ)^(-(1/6 : ℝ)) := by
          rw [show (8/3 : ℝ) + 1/6 = (3:ℝ) + -(1/6) by norm_num,
            Real.rpow_add hpos]
          norm_num
    _ ≤ (n : ℝ)^3 * (ε/2)^2 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ ≤ (ε/2 * (n : ℝ))^2 * ((n : ℝ)+1) := by
      nlinarith [sq_nonneg (ε/2*(n:ℝ))]
