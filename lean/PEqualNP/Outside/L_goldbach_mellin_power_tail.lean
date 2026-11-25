import Mathlib

theorem PEqualNP.Outside.L_goldbach_mellin_power_tail :
    ∀ a : ℕ, ∃ C : ℝ, 0<C ∧ ∀ H B : ℕ, (∑ k ∈ Finset.Icc H B, 1/((k+1:ℕ):ℝ)^(a+3)) ≤ C/((H+1:ℕ):ℝ)^(a+2) := by
  intro a
  refine ⟨2, by norm_num, ?_⟩
  intro H B
  have hstep : ∀ (x : ℝ) (d : ℕ), 1 ≤ x → 1 ≤ d → x ^ d ≤ ((x + 1) ^ d - x ^ d) * (x + 1) := by
    intro x d hx hd
    induction d with
    | zero => omega
    | succ d ih =>
      cases d with
      | zero =>
        simp only [pow_one]
        nlinarith
      | succ d =>
        have hih := ih (by omega)
        have hpow_nn : 0 ≤ x ^ (d + 1) := pow_nonneg (by linarith) _
        have hid : ((x + 1) ^ (d + 2) - x ^ (d + 2)) * (x + 1) =
            (((x + 1) ^ (d + 1) - x ^ (d + 1)) * (x + 1) + x ^ (d + 1)) * (x + 1) := by
          rw [pow_succ (x + 1) (d + 1), pow_succ x (d + 1)]
          ring
        rw [hid, pow_succ x (d + 1)]
        nlinarith
  have hterm : ∀ m : ℕ,
      1 / ((m + 2 : ℕ) : ℝ) ^ (a + 3) ≤
        1 / ((m + 1 : ℕ) : ℝ) ^ (a + 2) - 1 / ((m + 2 : ℕ) : ℝ) ^ (a + 2) := by
    intro m
    set x : ℝ := ((m + 1 : ℕ) : ℝ) with hx_def
    have hx1 : (1 : ℝ) ≤ x := by
      rw [hx_def]
      have hm1 : 1 ≤ m + 1 := by omega
      exact_mod_cast hm1
    have hx2 : ((m + 2 : ℕ) : ℝ) = x + 1 := by
      rw [hx_def]
      push_cast
      ring
    rw [hx2]
    have hx_pos : 0 < x := by linarith
    have hx1_pos : 0 < x + 1 := by linarith
    have hkey : x ^ (a + 2) ≤ ((x + 1) ^ (a + 2) - x ^ (a + 2)) * (x + 1) :=
      hstep x (a + 2) hx1 (by omega)
    have hdiff : 1 / x ^ (a + 2) - 1 / (x + 1) ^ (a + 2) - 1 / (x + 1) ^ (a + 3) =
        (((x + 1) ^ (a + 2) - x ^ (a + 2)) * (x + 1) - x ^ (a + 2)) /
          (x ^ (a + 2) * (x + 1) ^ (a + 3)) := by
      have hpow : (x + 1) ^ (a + 3) = (x + 1) ^ (a + 2) * (x + 1) := pow_succ (x + 1) (a + 2)
      rw [hpow]
      field_simp <;> ring
    have hnn : 0 ≤ 1 / x ^ (a + 2) - 1 / (x + 1) ^ (a + 2) - 1 / (x + 1) ^ (a + 3) := by
      rw [hdiff]
      exact div_nonneg (by linarith) (by positivity)
    linarith
  have hmain : ∀ n : ℕ,
      (∑ k ∈ Finset.Icc H (H + n), 1 / ((k + 1 : ℕ) : ℝ) ^ (a + 3)) ≤
        2 / ((H + 1 : ℕ) : ℝ) ^ (a + 2) - 1 / ((H + n + 1 : ℕ) : ℝ) ^ (a + 2) := by
    intro n
    induction n with
    | zero =>
      have hset : Finset.Icc H (H + 0) = {H} := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_singleton]
        omega
      rw [hset, Finset.sum_singleton]
      have hH0 : H + 0 + 1 = H + 1 := by omega
      rw [hH0]
      set x : ℝ := ((H + 1 : ℕ) : ℝ) with hx_def
      have hx1 : (1 : ℝ) ≤ x := by
        rw [hx_def]
        have hH1 : 1 ≤ H + 1 := by omega
        exact_mod_cast hH1
      have hx_pos : 0 < x := by linarith
      have hdiff : 2 / x ^ (a + 2) - 1 / x ^ (a + 2) - 1 / x ^ (a + 3) =
          (x - 1) / x ^ (a + 3) := by
        rw [pow_succ x (a + 2)]
        field_simp <;> ring
      have hnn : 0 ≤ 2 / x ^ (a + 2) - 1 / x ^ (a + 2) - 1 / x ^ (a + 3) := by
        rw [hdiff]
        exact div_nonneg (by linarith) (by positivity)
      linarith
    | succ n ih =>
      have hset : Finset.Icc H (H + (n + 1)) = insert (H + n + 1) (Finset.Icc H (H + n)) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : H + n + 1 ∉ Finset.Icc H (H + n) := by
        simp only [Finset.mem_Icc]
        omega
      rw [hset, Finset.sum_insert hnotmem]
      have hstep_n := hterm (H + n)
      have h1 : H + (n + 1) + 1 = H + n + 2 := by omega
      have h2 : H + n + 1 + 1 = H + n + 2 := by omega
      rw [h1, h2]
      linarith
  by_cases hHB : H ≤ B
  · have hB : B = H + (B - H) := by omega
    rw [hB]
    have h1 := hmain (B - H)
    have hpos : 0 ≤ 1 / ((H + (B - H) + 1 : ℕ) : ℝ) ^ (a + 2) := by positivity
    linarith
  · have hzero : (∑ k ∈ Finset.Icc H B, 1 / ((k + 1 : ℕ) : ℝ) ^ (a + 3)) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      simp only [Finset.mem_Icc] at hk
      omega
    rw [hzero]
    positivity
