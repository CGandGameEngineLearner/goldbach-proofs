import Mathlib

open Filter

theorem Conjectures.Cuts.Taskfa471d7e341a0ec35ac5e0ee : (∀ (x1 : ℝ), (0 : ℝ) < x1 → ∃ (x3 : ℕ), ∀ x4 ≥ x3, ↑x4 ^ ((8 / 3 : ℝ) + (1 / 6 : ℝ)) / (↑x4 + (1 : ℝ)) ≤ (x1 / (2 : ℝ) * ↑x4) ^ (2 : ℕ)) := by
  intro ε hε
  have hc : 0 < (ε / 2)^2 := by positivity
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ (1/6 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/6)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (1 / (ε / 2)^2))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hg : (1 : ℝ) ≤ (ε/2)^2 * (n : ℝ)^(1/6 : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp (hN n (by omega))
  have he : (n : ℝ) ^ ((8/3 : ℝ) + (1/6 : ℝ)) * (n : ℝ)^(1/6 : ℝ) = (n : ℝ)^3 := by
    rw [← Real.rpow_add hn', show (8/3 : ℝ) + 1/6 + 1/6 = 3 by norm_num]
    exact Real.rpow_natCast (n : ℝ) 3
  have hh := mul_le_mul_of_nonneg_left hg
    (Real.rpow_nonneg hn'.le ((8/3 : ℝ) + 1/6))
  rw [mul_one, ← mul_left_comm, he] at hh
  apply (div_le_iff₀ (by positivity)).mpr
  calc
    _ ≤ (ε/2)^2 * (n : ℝ)^3 := hh
    _ ≤ (ε/2 * (n : ℝ))^2 * ((n : ℝ) + 1) := by
      rw [mul_pow]
      nlinarith [mul_nonneg hc.le (sq_nonneg (n : ℝ))]
