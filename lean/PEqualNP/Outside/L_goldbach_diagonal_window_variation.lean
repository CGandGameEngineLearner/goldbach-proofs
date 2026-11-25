import Mathlib

open MeasureTheory
open scoped Topology

theorem PEqualNP.Outside.L_goldbach_diagonal_window_variation : let g := fun (φ : ℝ → ℝ) (n k : ℕ) => Real.log (k:ℝ)*(φ ((k:ℝ)/n))^2; ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → (∀ u : ℝ, u < 1/3 ∨ 2/3 < u → φ u=0) → ∃ K : ℝ, 0<K ∧ ∀ n : ℕ, 2≤n → (∑ k ∈ Finset.range n, |g φ n (k+1)-g φ n k|) ≤ K*Real.log (2*(n:ℝ)) := by
  dsimp only
  intro φ hC hsupp
  have hφc : Continuous φ := hC.continuous
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (1/3:ℝ) (2/3)) hφc.continuousOn
  have hMnn : 0 ≤ M := by
    have h := hM (1/3) (by constructor <;> norm_num)
    exact le_trans (abs_nonneg _) h
  have hMb : ∀ x : ℝ, |φ x| ≤ M := by
    intro x
    by_cases hx : x ∈ Set.Icc (1/3:ℝ) (2/3)
    · simpa using hM x hx
    · have hz : φ x = 0 := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · exact hsupp x (Or.inl hx)
        · exact hsupp x (Or.inr hx)
      simp [hz, hMnn]
  have hdc : Continuous (deriv φ) := hC.continuous_deriv le_rfl
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (1/3:ℝ) (2/3)) hdc.continuousOn
  have hLnn : 0 ≤ L := by
    have h := hL (1/3) (by constructor <;> norm_num)
    exact le_trans (abs_nonneg _) h
  have hderiv : ∀ x : ℝ, |deriv φ x| ≤ L := by
    intro x
    by_cases hx : x ∈ Set.Icc (1/3:ℝ) (2/3)
    · simpa using hL x hx
    · have hz : deriv φ x = 0 := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · have hev : φ =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
            filter_upwards [Iio_mem_nhds hx] with y hy
            exact hsupp y (Or.inl hy)
          rw [hev.deriv_eq]
          simp
        · have hev : φ =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
            filter_upwards [Ioi_mem_nhds hx] with y hy
            exact hsupp y (Or.inr hy)
          rw [hev.deriv_eq]
          simp
      simp [hz, hLnn]
  have hdiff : Differentiable ℝ φ := hC.differentiable (by norm_num)
  have hlip : ∀ x y : ℝ, |φ y - φ x| ≤ L * |y - x| := by
    intro x y
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := φ) (s := Set.univ) (C := L)
      (fun z _ => hdiff z) (fun z _ => by simpa using hderiv z) convex_univ (Set.mem_univ x) (Set.mem_univ y)
    simpa using h
  refine ⟨2*M*L + 3*M^2 + 1, by positivity, ?_⟩
  intro n hn
  have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n:ℝ) := by linarith
  have h2n : (4:ℝ) ≤ 2*(n:ℝ) := by linarith
  have hlog : 1 ≤ Real.log (2*(n:ℝ)) := by
    have h1 : Real.log 4 ≤ Real.log (2*(n:ℝ)) := Real.log_le_log (by norm_num) h2n
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2*2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    linarith [Real.log_two_gt_d9]
  have hlog2nn : 0 ≤ Real.log (2*(n:ℝ)) := by linarith
  have key : ∀ k ∈ Finset.range n,
      |Real.log (((k+1 : ℕ) : ℝ)) * (φ ((((k+1 : ℕ) : ℝ))/(n:ℝ)))^2 - Real.log ((k:ℝ)) * (φ (((k:ℝ))/(n:ℝ)))^2|
        ≤ Real.log (2*(n:ℝ)) * (2*M*L/(n:ℝ)) + M^2*((3:ℝ)/(n:ℝ)) := by
    intro k hk
    have hk' : k < n := Finset.mem_range.mp hk
    have hklt : (k:ℝ) < (n:ℝ) := by exact_mod_cast hk'
    have hk1pos : (0:ℝ) < (k:ℝ)+1 := by positivity
    have hcast : (((k+1 : ℕ) : ℝ)) = (k:ℝ)+1 := by push_cast; ring
    rw [hcast]
    have hp_nn : 0 ≤ Real.log ((k:ℝ)+1) := Real.log_nonneg (by linarith)
    have hp_le : Real.log ((k:ℝ)+1) ≤ Real.log (2*(n:ℝ)) :=
      Real.log_le_log hk1pos (by linarith)
    -- difference of squares bound
    have hqs : |(φ (((k:ℝ)+1)/(n:ℝ)))^2 - (φ ((k:ℝ)/(n:ℝ)))^2| ≤ 2*M*L/(n:ℝ) := by
      have hfac : (φ (((k:ℝ)+1)/(n:ℝ)))^2 - (φ ((k:ℝ)/(n:ℝ)))^2
          = (φ (((k:ℝ)+1)/(n:ℝ)) - φ ((k:ℝ)/(n:ℝ))) *
            (φ (((k:ℝ)+1)/(n:ℝ)) + φ ((k:ℝ)/(n:ℝ))) := by ring
      have hdist : |((k:ℝ)+1)/(n:ℝ) - (k:ℝ)/(n:ℝ)| = 1/(n:ℝ) := by
        have h : ((k:ℝ)+1)/(n:ℝ) - (k:ℝ)/(n:ℝ) = 1/(n:ℝ) := by field_simp; ring
        rw [h, abs_of_pos (by positivity)]
      have hL1 : |φ (((k:ℝ)+1)/(n:ℝ)) - φ ((k:ℝ)/(n:ℝ))| ≤ L * (1/(n:ℝ)) := by
        have h := hlip ((k:ℝ)/(n:ℝ)) (((k:ℝ)+1)/(n:ℝ))
        rwa [hdist] at h
      have hsum2 : |φ (((k:ℝ)+1)/(n:ℝ)) + φ ((k:ℝ)/(n:ℝ))| ≤ 2*M := by
        calc |φ (((k:ℝ)+1)/(n:ℝ)) + φ ((k:ℝ)/(n:ℝ))|
            ≤ |φ (((k:ℝ)+1)/(n:ℝ))| + |φ ((k:ℝ)/(n:ℝ))| := abs_add_le _ _
          _ ≤ M + M := by
              have h1 := hMb (((k:ℝ)+1)/(n:ℝ))
              have h2 := hMb ((k:ℝ)/(n:ℝ))
              linarith
          _ = 2*M := by ring
      calc |(φ (((k:ℝ)+1)/(n:ℝ)))^2 - (φ ((k:ℝ)/(n:ℝ)))^2|
          = |φ (((k:ℝ)+1)/(n:ℝ)) - φ ((k:ℝ)/(n:ℝ))| *
            |φ (((k:ℝ)+1)/(n:ℝ)) + φ ((k:ℝ)/(n:ℝ))| := by rw [hfac, abs_mul]
        _ ≤ (L * (1/(n:ℝ))) * (2*M) := by
            apply mul_le_mul hL1 hsum2 (abs_nonneg _) (by positivity)
        _ = 2*M*L/(n:ℝ) := by field_simp
    -- square bound
    have hsM : (φ ((k:ℝ)/(n:ℝ)))^2 ≤ M^2 := by
      have h := hMb ((k:ℝ)/(n:ℝ))
      have h2 : |φ ((k:ℝ)/(n:ℝ))|^2 ≤ M^2 := by
        apply pow_le_pow_left₀ (abs_nonneg _) h
      rwa [sq_abs] at h2
    -- log difference bound
    have hpr : (φ ((k:ℝ)/(n:ℝ)))^2 * |Real.log ((k:ℝ)+1) - Real.log (k:ℝ)| ≤ M^2*((3:ℝ)/(n:ℝ)) := by
      by_cases hk3 : (k:ℝ) < (n:ℝ)/3
      · have hlt : (k:ℝ)/(n:ℝ) < 1/3 := by
          have h1 : (k:ℝ)/(n:ℝ) < ((n:ℝ)/3)/(n:ℝ) := div_lt_div_of_pos_right hk3 hnpos
          have h2 : ((n:ℝ)/3)/(n:ℝ) = 1/3 := by field_simp
          rwa [h2] at h1
        have hz : φ ((k:ℝ)/(n:ℝ)) = 0 := hsupp _ (Or.inl hlt)
        rw [hz]
        have h0 : (0:ℝ)^2 * |Real.log ((k:ℝ)+1) - Real.log (k:ℝ)| = 0 := by norm_num
        rw [h0]
        exact mul_nonneg (sq_nonneg M) (by positivity)
      · push Not at hk3
        have hkpos : (0:ℝ) < (k:ℝ) := by linarith
        have h1k : |Real.log ((k:ℝ)+1) - Real.log (k:ℝ)| ≤ 1/(k:ℝ) := by
          have hr : Real.log ((k:ℝ)+1) - Real.log (k:ℝ) = Real.log (((k:ℝ)+1)/(k:ℝ)) := by
            rw [Real.log_div (by positivity) (ne_of_gt hkpos)]
          have h1 : 0 ≤ Real.log (((k:ℝ)+1)/(k:ℝ)) := by
            apply Real.log_nonneg
            rw [le_div_iff₀ hkpos]
            linarith
          rw [hr, abs_of_nonneg h1]
          have h2 := Real.log_le_sub_one_of_pos (x := ((k:ℝ)+1)/(k:ℝ)) (by positivity)
          have h3 : ((k:ℝ)+1)/(k:ℝ) - 1 = 1/(k:ℝ) := by field_simp; ring
          linarith
        have h1kle : 1/(k:ℝ) ≤ 3/(n:ℝ) := by
          rw [div_le_div_iff₀ hkpos hnpos]
          nlinarith
        calc (φ ((k:ℝ)/(n:ℝ)))^2 * |Real.log ((k:ℝ)+1) - Real.log (k:ℝ)|
            ≤ M^2 * (1/(k:ℝ)) := by
              apply mul_le_mul hsM h1k (abs_nonneg _) (sq_nonneg M)
          _ ≤ M^2 * ((3:ℝ)/(n:ℝ)) :=
              mul_le_mul_of_nonneg_left h1kle (sq_nonneg M)
    -- assemble
    have hfac2 : Real.log ((k:ℝ)+1) * (φ (((k:ℝ)+1)/(n:ℝ)))^2 - Real.log (k:ℝ) * (φ ((k:ℝ)/(n:ℝ)))^2
        = Real.log ((k:ℝ)+1) * ((φ (((k:ℝ)+1)/(n:ℝ)))^2 - (φ ((k:ℝ)/(n:ℝ)))^2)
          + (φ ((k:ℝ)/(n:ℝ)))^2 * (Real.log ((k:ℝ)+1) - Real.log (k:ℝ)) := by ring
    rw [hfac2]
    calc |Real.log ((k:ℝ)+1) * ((φ (((k:ℝ)+1)/(n:ℝ)))^2 - (φ ((k:ℝ)/(n:ℝ)))^2)
          + (φ ((k:ℝ)/(n:ℝ)))^2 * (Real.log ((k:ℝ)+1) - Real.log (k:ℝ))|
        ≤ |Real.log ((k:ℝ)+1) * ((φ (((k:ℝ)+1)/(n:ℝ)))^2 - (φ ((k:ℝ)/(n:ℝ)))^2)|
          + |(φ ((k:ℝ)/(n:ℝ)))^2 * (Real.log ((k:ℝ)+1) - Real.log (k:ℝ))| := abs_add_le _ _
      _ = Real.log ((k:ℝ)+1) * |(φ (((k:ℝ)+1)/(n:ℝ)))^2 - (φ ((k:ℝ)/(n:ℝ)))^2|
          + (φ ((k:ℝ)/(n:ℝ)))^2 * |Real.log ((k:ℝ)+1) - Real.log (k:ℝ)| := by
          simp only [abs_mul, abs_of_nonneg hp_nn,
            abs_of_nonneg (sq_nonneg (φ ((k:ℝ)/(n:ℝ))))]
      _ ≤ Real.log (2*(n:ℝ)) * (2*M*L/(n:ℝ)) + M^2*((3:ℝ)/(n:ℝ)) :=
          add_le_add (mul_le_mul hp_le hqs (abs_nonneg _) hlog2nn) hpr
  calc (∑ k ∈ Finset.range n, |Real.log (((k+1 : ℕ) : ℝ)) * (φ ((((k+1 : ℕ) : ℝ))/(n:ℝ)))^2 - Real.log ((k:ℝ)) * (φ (((k:ℝ))/(n:ℝ)))^2|)
      ≤ ∑ k ∈ Finset.range n, (Real.log (2*(n:ℝ)) * (2*M*L/(n:ℝ)) + M^2*((3:ℝ)/(n:ℝ))) := Finset.sum_le_sum key
    _ = (n:ℝ) * (Real.log (2*(n:ℝ)) * (2*M*L/(n:ℝ)) + M^2*((3:ℝ)/(n:ℝ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = 2*M*L*Real.log (2*(n:ℝ)) + 3*M^2 := by
        field_simp
    _ ≤ (2*M*L + 3*M^2 + 1) * Real.log (2*(n:ℝ)) := by
        nlinarith [mul_nonneg (sq_nonneg M) (by linarith : (0:ℝ) ≤ Real.log (2*(n:ℝ)) - 1),
          mul_nonneg (mul_nonneg hMnn hLnn) hlog2nn]