import Mathlib

theorem PEqualNP.Outside.L_goldbach_small_bulk_saving :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E ((k : ℝ) * t));
    let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))};
    let low := fun (n k : ℕ) => if k ^ 3 ≤ n then w k else 0;
    let high := fun (n k : ℕ) => w k - low n k;
    let I := fun (n : ℕ) (a b : ℕ → ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t) (0 : ℝ) 1 MeasureTheory.volume;
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n ≥ N, ‖I n (low n) (high n)‖ ≤ e * (n : ℝ) := by
  intro w E S _Q arcs low high I e he
  have hnorm_E : ∀ x : ℝ, ‖E x‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)
  have hcap : ∀ (n : ℕ) (t : ℝ), 2 ≤ n → ‖S n (low n) t‖ ≤ ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ) := by
    intro n t hn
    have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hlow_nonneg : ∀ k : ℕ, 0 ≤ low n k := by
      intro k
      dsimp only [low, w]
      split_ifs with h1 hp
      · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
      · exact le_rfl
      · exact le_rfl
    have hlow_le_log : ∀ k ∈ Finset.range (n + 1), low n k ≤ Real.log (n : ℝ) := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      dsimp only [low, w]
      split_ifs with h1 hp
      · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hkn)
      · exact hlog_nonneg
      · exact hlog_nonneg
    have hstep1 : ‖S n (low n) t‖ ≤ ∑ k ∈ Finset.range (n + 1), low n k := by
      dsimp only [S]
      calc
        ‖∑ k ∈ Finset.range (n + 1), (low n k : ℂ) * E ((k : ℝ) * t)‖
          ≤ ∑ k ∈ Finset.range (n + 1), ‖(low n k : ℂ) * E ((k : ℝ) * t)‖ := norm_sum_le _ _
        _ = ∑ k ∈ Finset.range (n + 1), low n k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlow_nonneg k), hnorm_E, mul_one]
    set s : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k ^ 3 ≤ n)
    have hstep2 : ∑ k ∈ Finset.range (n + 1), low n k = ∑ k ∈ s, low n k := by
      symm
      refine Finset.sum_subset (Finset.filter_subset _ _) fun k hk hks => ?_
      have hnot : ¬ (k ^ 3 ≤ n) := fun hle => hks (Finset.mem_filter.mpr ⟨hk, hle⟩)
      simp [low, hnot]
    set m : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
    have hs_sub : s ⊆ Finset.range (m + 1) := by
      intro k hk
      have hk3 : k ^ 3 ≤ n := (Finset.mem_filter.mp hk).2
      have hk3_real : ((k : ℝ) ^ (3 : ℝ)) ≤ (n : ℝ) := by
        have hcast : ((k ^ 3 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk3
        simpa [Real.rpow_natCast] using hcast
      have hk_le_rpow : (k : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
        have hpow := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg k) (3 : ℝ)) hk3_real (by norm_num : (0 : ℝ) ≤ 1 / 3)
        rw [← Real.rpow_mul (Nat.cast_nonneg k)] at hpow
        have h3 : (3 : ℝ) * (1 / 3 : ℝ) = 1 := by norm_num
        rw [h3, Real.rpow_one] at hpow
        exact hpow
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hk_le_rpow))
    have hcard : (s.card : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) + 1 := by
      have h1 : s.card ≤ m + 1 := by simpa [Finset.card_range] using Finset.card_le_card hs_sub
      have h1r : (s.card : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast h1
      have h2 : (m : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (Real.rpow_nonneg hn_nonneg (1 / 3 : ℝ))
      linarith
    calc
      ‖S n (low n) t‖ ≤ ∑ k ∈ Finset.range (n + 1), low n k := hstep1
      _ = ∑ k ∈ s, low n k := hstep2
      _ ≤ ∑ _k ∈ s, Real.log (n : ℝ) := Finset.sum_le_sum fun k hk => hlow_le_log k (Finset.mem_filter.mp hk).1
      _ = (s.card : ℝ) * Real.log (n : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ) := mul_le_mul_of_nonneg_right hcard hlog_nonneg
  have henergy : ∀ n : ℕ, 2 ≤ n →
      intervalIntegral (fun t => ‖S n (high n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume ≤
        ((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 := by
    intro n hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hstar_E : ∀ x : ℝ, star (E x) = Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) := by
      intro x
      dsimp only [E]
      change (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    have hE_mul_star : ∀ (j k : ℕ) (t : ℝ),
        E ((j : ℝ) * t) * star (E ((k : ℝ) * t)) =
        Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
      intro j k t
      rw [hstar_E]
      dsimp only [E]
      rw [← Complex.exp_add]
      congr 1
      simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_natCast,
        Int.cast_sub, Int.cast_natCast]
      ring
    have hint_exp : ∀ m : ℤ,
        intervalIntegral (fun t : ℝ => Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
          (0 : ℝ) 1 MeasureTheory.volume = if m = 0 then 1 else 0 := by
      intro m
      by_cases hm : m = 0
      · subst hm
        simp
      · simp only [hm, ↓reduceIte]
        set c : ℂ := (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        have hc : c ≠ 0 := by
          dsimp only [c]
          have hm0 : (m : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
          have hpi0 : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
          exact mul_ne_zero hm0 (mul_ne_zero (mul_ne_zero two_ne_zero hpi0) Complex.I_ne_zero)
        have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
            HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)) / c) (Complex.exp (c * (t : ℂ))) t := by
          intro t _
          have h1 : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c t := by
            have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
            simpa using this
          have h2 : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ))) (Complex.exp (c * (t : ℂ)) * c) t :=
            h1.cexp
          have h3 := h2.div_const c
          simpa [mul_div_cancel_right₀ _ hc] using h3
        have hcont : Continuous (fun t : ℝ => Complex.exp (c * (t : ℂ))) := by fun_prop
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)]
        have hexp1 : Complex.exp (c * ((1 : ℝ) : ℂ)) = 1 := by
          rw [Complex.ofReal_one, mul_one]
          exact Complex.exp_int_mul_two_pi_mul_I m
        have hexp0 : Complex.exp (c * ((0 : ℝ) : ℂ)) = 1 := by
          rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        rw [hexp1, hexp0, sub_self]
    have hpoint : ∀ t : ℝ,
        ((‖S n (high n) t‖ ^ 2 : ℝ) : ℂ) =
        ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          ((high n j : ℂ) * (high n k : ℂ)) *
            Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
      intro t
      have hns : ((‖S n (high n) t‖ ^ 2 : ℝ) : ℂ) = S n (high n) t * star (S n (high n) t) := by
        have := Complex.mul_conj (S n (high n) t)
        rw [Complex.normSq_eq_norm_sq] at this
        exact this.symm
      rw [hns]
      dsimp only [S]
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def]
      rw [show (high n j : ℂ) * E ((j : ℝ) * t) * ((high n k : ℂ) * star (E ((k : ℝ) * t))) =
        ((high n j : ℂ) * (high n k : ℂ)) * (E ((j : ℝ) * t) * star (E ((k : ℝ) * t))) by ring]
      rw [hE_mul_star j k t]
    have hparseval_complex :
        ((intervalIntegral (fun t => ‖S n (high n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume : ℝ) : ℂ) =
        ∑ k ∈ Finset.range (n + 1), ((high n k : ℂ) * (high n k : ℂ)) := by
      rw [← intervalIntegral.integral_ofReal]
      calc
        intervalIntegral (fun t => ((‖S n (high n) t‖ ^ 2 : ℝ) : ℂ)) (0 : ℝ) 1 MeasureTheory.volume
          = intervalIntegral
              (fun t => ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
                ((high n j : ℂ) * (high n k : ℂ)) *
                  Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
              (0 : ℝ) 1 MeasureTheory.volume := intervalIntegral.integral_congr fun t _ => hpoint t
        _ = ∑ j ∈ Finset.range (n + 1),
              intervalIntegral
                (fun t => ∑ k ∈ Finset.range (n + 1),
                  ((high n j : ℂ) * (high n k : ℂ)) *
                    Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
                (0 : ℝ) 1 MeasureTheory.volume := by
            refine intervalIntegral.integral_finsetSum fun j _ => ?_
            exact Continuous.intervalIntegrable (by fun_prop) 0 1
        _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              intervalIntegral
                (fun t => ((high n j : ℂ) * (high n k : ℂ)) *
                  Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
                (0 : ℝ) 1 MeasureTheory.volume := by
            refine Finset.sum_congr rfl fun j _ => ?_
            refine intervalIntegral.integral_finsetSum fun k _ => ?_
            exact Continuous.intervalIntegrable (by fun_prop) 0 1
        _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              ((high n j : ℂ) * (high n k : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then (1 : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
            rw [intervalIntegral.integral_const_mul, hint_exp ((j : ℤ) - (k : ℤ))]
        _ = ∑ j ∈ Finset.range (n + 1), ((high n j : ℂ) * (high n j : ℂ)) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Finset.sum_eq_single j]
            · simp
            · intro k _ hkj
              have hne : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
              simp [hne]
            · intro hj'
              exact (hj' hj).elim
    have hparseval :
        intervalIntegral (fun t => ‖S n (high n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        ∑ k ∈ Finset.range (n + 1), (high n k) ^ 2 := by
      have hre := congrArg Complex.re hparseval_complex
      rw [Complex.ofReal_re] at hre
      rw [hre, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]
    have hhigh_bound : ∀ k ∈ Finset.range (n + 1), (high n k) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have h0 : 0 ≤ high n k := by
        dsimp only [high, low]
        by_cases h1 : k ^ 3 ≤ n
        · simp [h1]
        · simp only [h1, ↓reduceIte, sub_zero, w]
          split_ifs with hp
          · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
          · exact le_rfl
      have hle : high n k ≤ Real.log (n : ℝ) := by
        dsimp only [high, low]
        by_cases h1 : k ^ 3 ≤ n
        · simp [h1, hlog_nonneg]
        · simp only [h1, ↓reduceIte, sub_zero, w]
          split_ifs with hp
          · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hkn)
          · exact hlog_nonneg
      exact pow_le_pow_left₀ h0 hle 2
    calc
      intervalIntegral (fun t => ‖S n (high n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume
        = ∑ k ∈ Finset.range (n + 1), (high n k) ^ 2 := hparseval
      _ ≤ ∑ _k ∈ Finset.range (n + 1), (Real.log (n : ℝ)) ^ 2 := Finset.sum_le_sum hhigh_bound
      _ = ((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  refine ⟨Nat.ceil ((2304 / e) ^ (12 : ℕ)) + 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_gt1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlog_pos : 0 < Real.log (n : ℝ) := Real.log_pos hn_gt1
  have hlog_bound : Real.log (n : ℝ) ≤ 24 * (n : ℝ) ^ (1 / 24 : ℝ) := by
    have hpos_p : 0 < (n : ℝ) ^ (1 / 24 : ℝ) := Real.rpow_pos_of_pos hn_pos _
    have h1 := Real.log_le_sub_one_of_pos hpos_p
    rw [Real.log_rpow hn_pos] at h1
    linarith
  have h1_le_rpow : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hn_gt1.le (by norm_num)
  have hM : ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ) ≤ 48 * (n : ℝ) ^ (3 / 8 : ℝ) := by
    have h1 : (n : ℝ) ^ (1 / 3 : ℝ) + 1 ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by linarith
    calc
      ((n : ℝ) ^ (1 / 3 : ℝ) + 1) * Real.log (n : ℝ)
        ≤ (2 * (n : ℝ) ^ (1 / 3 : ℝ)) * (24 * (n : ℝ) ^ (1 / 24 : ℝ)) :=
          mul_le_mul h1 hlog_bound hlog_pos.le (by positivity)
      _ = 48 * ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 24 : ℝ)) := by ring
      _ = 48 * (n : ℝ) ^ (3 / 8 : ℝ) := by
          rw [← Real.rpow_add hn_pos]
          norm_num
  set B : ℝ := Real.sqrt (((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2)
  have hB_pos : 0 < B := Real.sqrt_pos.mpr (by positivity)
  have hB_sq : B ^ 2 = ((n : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hS_high_cont : Continuous (fun t : ℝ => S n (high n) t) := by
    dsimp only [S, E]
    fun_prop
  have hL1_le_B :
      intervalIntegral (fun t => ‖S n (high n) t‖) (0 : ℝ) 1 MeasureTheory.volume ≤ B := by
    have hpt_amgm : ∀ t : ℝ, ‖S n (high n) t‖ ≤ (‖S n (high n) t‖ ^ 2 / B + B) / 2 := by
      intro t
      have hsq_nonneg : 0 ≤ (‖S n (high n) t‖ - B) ^ 2 := sq_nonneg _
      have hmul : 2 * B * ‖S n (high n) t‖ ≤ ‖S n (high n) t‖ ^ 2 + B ^ 2 := by nlinarith
      have hdiv := (div_le_div_iff_of_pos_right (show 0 < 2 * B by positivity)).mpr hmul
      have h1 : 2 * B * ‖S n (high n) t‖ / (2 * B) = ‖S n (high n) t‖ := by
        field_simp [hB_pos.ne']
      have h2 : (‖S n (high n) t‖ ^ 2 + B ^ 2) / (2 * B) = (‖S n (high n) t‖ ^ 2 / B + B) / 2 := by
        field_simp [hB_pos.ne']
      linarith
    have hint1 : IntervalIntegrable (fun t => ‖S n (high n) t‖) MeasureTheory.volume 0 1 :=
      (continuous_norm.comp hS_high_cont).intervalIntegrable 0 1
    have hint2 : IntervalIntegrable (fun t => ‖S n (high n) t‖ ^ 2) MeasureTheory.volume 0 1 :=
      ((continuous_norm.comp hS_high_cont).pow 2).intervalIntegrable 0 1
    have hint_rhs : IntervalIntegrable (fun t => (‖S n (high n) t‖ ^ 2 / B + B) / 2) MeasureTheory.volume 0 1 :=
      ((hint2.div_const B).add intervalIntegrable_const).div_const 2
    have hle := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hint1 hint_rhs (fun t _ => hpt_amgm t)
    have hrhs_eval :
        intervalIntegral (fun t => (‖S n (high n) t‖ ^ 2 / B + B) / 2) (0 : ℝ) 1 MeasureTheory.volume =
        ((intervalIntegral (fun t => ‖S n (high n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume) / B + B) / 2 := by
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint2.div_const B) intervalIntegrable_const,
        intervalIntegral.integral_div, intervalIntegral.integral_const]
      simp
    rw [hrhs_eval] at hle
    have hen := henergy n hn2
    have hen' : (intervalIntegral (fun t => ‖S n (high n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume) / B ≤ B := by
      rw [div_le_iff₀ hB_pos, ← sq, hB_sq]
      exact hen
    linarith
  have hB_le : B ≤ 48 * (n : ℝ) ^ (13 / 24 : ℝ) := by
    have hsqrt_le : Real.sqrt ((n : ℝ) + 1) ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
      have h1 : (n : ℝ) + 1 ≤ 4 * (n : ℝ) := by linarith
      calc
        Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (4 * (n : ℝ)) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt 4 * Real.sqrt (n : ℝ) := Real.sqrt_mul (by norm_num) _
        _ = 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow]
    have hB_eq : B = Real.sqrt ((n : ℝ) + 1) * Real.log (n : ℝ) := by
      dsimp only [B]
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hlog_pos.le]
    rw [hB_eq]
    calc
      Real.sqrt ((n : ℝ) + 1) * Real.log (n : ℝ)
        ≤ (2 * (n : ℝ) ^ (1 / 2 : ℝ)) * (24 * (n : ℝ) ^ (1 / 24 : ℝ)) :=
          mul_le_mul hsqrt_le hlog_bound hlog_pos.le (by positivity)
      _ = 48 * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 24 : ℝ)) := by ring
      _ = 48 * (n : ℝ) ^ (13 / 24 : ℝ) := by
          rw [← Real.rpow_add hn_pos]
          norm_num
  have hnorm_le :
      ‖I n (low n) (high n)‖ ≤
      intervalIntegral (fun t => (48 * (n : ℝ) ^ (3 / 8 : ℝ)) * ‖S n (high n) t‖) (0 : ℝ) 1 MeasureTheory.volume := by
    dsimp only [I]
    have hint_bound : IntervalIntegrable (fun t => (48 * (n : ℝ) ^ (3 / 8 : ℝ)) * ‖S n (high n) t‖) MeasureTheory.volume 0 1 :=
      ((continuous_norm.comp hS_high_cont).const_mul _).intervalIntegrable 0 1
    refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1) ?_ hint_bound
    filter_upwards with t _
    by_cases ht : t ∈ (arcs n)ᶜ
    · rw [Set.indicator_of_mem ht, norm_mul, norm_mul, hnorm_E, mul_one]
      exact mul_le_mul_of_nonneg_right ((hcap n t hn2).trans hM) (norm_nonneg _)
    · rw [Set.indicator_of_notMem ht, norm_zero]
      positivity
  have hprod : ‖I n (low n) (high n)‖ ≤ 2304 * (n : ℝ) ^ (11 / 12 : ℝ) := by
    calc
      ‖I n (low n) (high n)‖
        ≤ intervalIntegral (fun t => (48 * (n : ℝ) ^ (3 / 8 : ℝ)) * ‖S n (high n) t‖) (0 : ℝ) 1 MeasureTheory.volume := hnorm_le
      _ = (48 * (n : ℝ) ^ (3 / 8 : ℝ)) * intervalIntegral (fun t => ‖S n (high n) t‖) (0 : ℝ) 1 MeasureTheory.volume :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ (48 * (n : ℝ) ^ (3 / 8 : ℝ)) * (48 * (n : ℝ) ^ (13 / 24 : ℝ)) :=
          mul_le_mul_of_nonneg_left (hL1_le_B.trans hB_le) (by positivity)
      _ = 2304 * ((n : ℝ) ^ (3 / 8 : ℝ) * (n : ℝ) ^ (13 / 24 : ℝ)) := by ring
      _ = 2304 * (n : ℝ) ^ (11 / 12 : ℝ) := by
          rw [← Real.rpow_add hn_pos]
          norm_num
  have htail : 2304 * (n : ℝ) ^ (11 / 12 : ℝ) ≤ e * (n : ℝ) := by
    have hn_big : (2304 / e) ^ (12 : ℕ) ≤ (n : ℝ) := by
      have hceil : (2304 / e) ^ (12 : ℕ) ≤ (Nat.ceil ((2304 / e) ^ (12 : ℕ)) : ℝ) := Nat.le_ceil _
      have hle : (Nat.ceil ((2304 / e) ^ (12 : ℕ)) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : Nat.ceil ((2304 / e) ^ (12 : ℕ)) ≤ n)
      exact hceil.trans hle
    have hroot : 2304 / e ≤ (n : ℝ) ^ (1 / 12 : ℝ) := by
      have hnonneg : 0 ≤ (2304 / e : ℝ) := by positivity
      have hpow := Real.rpow_le_rpow (pow_nonneg hnonneg 12) hn_big (by norm_num : (0 : ℝ) ≤ 1 / 12)
      rw [← Real.rpow_natCast (2304 / e) 12, ← Real.rpow_mul hnonneg] at hpow
      have h12 : ((12 : ℕ) : ℝ) * (1 / 12 : ℝ) = 1 := by norm_num
      rw [h12, Real.rpow_one] at hpow
      exact hpow
    have h2304 : 2304 ≤ e * (n : ℝ) ^ (1 / 12 : ℝ) := by
      rwa [div_le_iff₀ he, mul_comm] at hroot
    calc
      2304 * (n : ℝ) ^ (11 / 12 : ℝ)
        ≤ (e * (n : ℝ) ^ (1 / 12 : ℝ)) * (n : ℝ) ^ (11 / 12 : ℝ) :=
          mul_le_mul_of_nonneg_right h2304 (by positivity)
      _ = e * ((n : ℝ) ^ (1 / 12 : ℝ) * (n : ℝ) ^ (11 / 12 : ℝ)) := by ring
      _ = e * (n : ℝ) := by
          rw [← Real.rpow_add hn_pos]
          norm_num
  exact hprod.trans htail
