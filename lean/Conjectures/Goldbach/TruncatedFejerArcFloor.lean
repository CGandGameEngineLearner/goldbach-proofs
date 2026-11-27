import Mathlib

/-!
# Goldbach gap `L-goldbach-truncated-fejer-arc-floor`

Lower bound for the truncated Fejer-type square-kernel integral on `[-W, W]`:
for `0 < W ≤ 1/2`,
`N + 1 - 1 / (2 * W) ≤ Re (∫_{-W}^W K_N(b)^2 e(-N b) db)`.
-/

open scoped BigOperators
open MeasureTheory intervalIntegral

theorem Conjectures.Goldbach.TruncatedFejerArcFloor :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let K (N : ℕ) (b : ℝ) := ∑ k ∈ Finset.range (N + 1), E ((k : ℝ) * b); ∀ (N : ℕ) (W : ℝ), 0 < W → W ≤ 1 / 2 → ((N + 1 : ℕ) : ℝ) - 1 / (2 * W) ≤ (intervalIntegral (fun b => (K N b)^2 * E (-(N : ℝ) * b)) (-W) W MeasureTheory.volume).re := by
  intro E K N W hW_pos hW_le
  have hEmul : ∀ a b : ℝ, E a * E b = E (a + b) := by
    intro a b
    simp only [E, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEconj : ∀ x : ℝ, star (E x) = E (-x) := by
    intro x
    simp only [E, Complex.star_def, Complex.exp_ofReal_mul_I, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    have h1 : (2 : ℝ) * Real.pi * (-x) = -(2 * Real.pi * x) := by ring
    rw [h1, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hEpow : ∀ (k : ℕ) (b : ℝ), E ((k : ℝ) * b) = (E b) ^ k := by
    intro k b
    simp only [E, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hKconj : ∀ b : ℝ, E (-(N : ℝ) * b) * K N b = star (K N b) := by
    intro b
    simp only [K, Finset.mul_sum, star_sum, hEconj]
    rw [← Finset.sum_range_reflect (fun k => E (-((k : ℝ) * b))) (N + 1)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hksub : N + 1 - 1 - k = N - k := by omega
    rw [hksub, hEmul, Nat.cast_sub hk']
    congr 1
    ring
  have htwisted : ∀ b : ℝ, (K N b) ^ 2 * E (-(N : ℝ) * b) = ((‖K N b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    calc
      (K N b) ^ 2 * E (-(N : ℝ) * b) = K N b * (E (-(N : ℝ) * b) * K N b) := by ring
      _ = K N b * star (K N b) := by rw [hKconj b]
      _ = ((‖K N b‖ ^ 2 : ℝ) : ℂ) := by
          rw [Complex.star_def, Complex.mul_conj']
          push_cast
          ring
  have hKneg : ∀ b : ℝ, ‖K N (-b)‖ ^ 2 = ‖K N b‖ ^ 2 := by
    intro b
    have h1 : K N (-b) = star (K N b) := by
      simp only [K, star_sum, hEconj]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      ring
    rw [h1, norm_star]
  have hE_cont : ∀ c : ℝ, Continuous (fun b : ℝ => E (c * b)) := fun c => by
    unfold E
    fun_prop
  have hsum_cont : ∀ (s : Finset ℕ) (f : ℕ → ℝ → ℂ),
      (∀ k ∈ s, Continuous (f k)) → Continuous (fun b => ∑ k ∈ s, f k b) := by
    intro s f hf
    induction s using Finset.induction with
    | empty => simpa using continuous_const
    | @insert a s ha ih =>
        simp_rw [Finset.sum_insert ha]
        exact (hf a (Finset.mem_insert_self _ _)).add
          (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
  have hK_cont : Continuous (fun b : ℝ => K N b) :=
    hsum_cont (Finset.range (N + 1)) (fun k b => E ((k : ℝ) * b)) fun k _ => hE_cont (k : ℝ)
  have hnormSq_cont : Continuous (fun b : ℝ => ‖K N b‖ ^ 2) :=
    (hK_cont.norm).pow 2
  have hnormSq_int : ∀ a c : ℝ, IntervalIntegrable (fun b : ℝ => ‖K N b‖ ^ 2) volume a c :=
    fun a c => hnormSq_cont.intervalIntegrable a c
  have h_re_eq :
      (intervalIntegral (fun b => (K N b) ^ 2 * E (-(N : ℝ) * b)) (-W) W volume).re =
        intervalIntegral (fun b => ‖K N b‖ ^ 2) (-W) W volume := by
    simp_rw [htwisted]
    rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  rw [h_re_eq]
  have hint_E_int : ∀ m : ℤ,
      intervalIntegral (fun b : ℝ => E ((m : ℝ) * b)) (-1 / 2) (1 / 2) volume =
        if m = 0 then (1 : ℂ) else 0 := by
    intro m
    by_cases hm : m = 0
    · subst hm
      simp [E]
      norm_num
    · set c : ℂ := ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I
      have hc : c ≠ 0 := by
        have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
        have hpi : (2 * Real.pi * (m : ℝ) : ℝ) ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmR
        exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hpi) Complex.I_ne_zero
      let F : ℝ → ℂ := fun b => Complex.exp ((b : ℂ) * c) / c
      have hderiv : ∀ b ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ),
          HasDerivAt F (E ((m : ℝ) * b)) b := by
        intro b _
        have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 b :=
          Complex.ofRealCLM.hasDerivAt
        have hmul : HasDerivAt (fun x : ℝ => (x : ℂ) * c) (1 * c) b :=
          hid.mul_const c
        have hexp : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * c))
            (Complex.exp ((b : ℂ) * c) * (1 * c)) b :=
          hmul.cexp
        have hdiv : HasDerivAt F (Complex.exp ((b : ℂ) * c) * (1 * c) / c) b :=
          hexp.div_const c
        have hval : Complex.exp ((b : ℂ) * c) * (1 * c) / c = E ((m : ℝ) * b) := by
          rw [one_mul, mul_div_cancel_right₀ _ hc]
          simp only [E, c]
          congr 1
          push_cast
          ring
        rwa [hval] at hdiv
      have hint : IntervalIntegrable (fun b : ℝ => E ((m : ℝ) * b)) volume (-1 / 2) (1 / 2) :=
        (hE_cont (m : ℝ)).intervalIntegrable _ _
      simp only [hm, ↓reduceIte]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
      have hhalf : Complex.exp (((1 / 2 : ℝ) : ℂ) * c) =
          Complex.exp ((((-1 / 2 : ℝ) : ℂ) * c)) := by
        have hpos : ((1 / 2 : ℝ) : ℂ) * c = (((m : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I := by
          simp only [c]; push_cast; ring
        have hneg : ((-1 / 2 : ℝ) : ℂ) * c = ((((-m : ℤ) : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I := by
          simp only [c]; push_cast; ring
        rw [hpos, hneg, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
        rw [Real.sin_int_mul_pi m, Real.sin_int_mul_pi (-m)]
        have hcos : Real.cos (((-m : ℤ) : ℝ) * Real.pi) = Real.cos ((m : ℝ) * Real.pi) := by
          push_cast
          rw [neg_mul, Real.cos_neg]
        rw [hcos]
      simp only [F, hhalf, sub_self]
  have hfull_mass :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (1 / 2) volume = ((N + 1 : ℕ) : ℝ) := by
    have hK_expand : ∀ b : ℝ, ((‖K N b‖ ^ 2 : ℝ) : ℂ) =
        ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
          E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b) := by
      intro b
      calc
        ((‖K N b‖ ^ 2 : ℝ) : ℂ) = K N b * star (K N b) := by
            rw [Complex.star_def, Complex.mul_conj']
            push_cast
            ring
        _ = (∑ j ∈ Finset.range (N + 1), E ((j : ℝ) * b)) *
              (∑ k ∈ Finset.range (N + 1), E (-((k : ℝ) * b))) := by
            simp only [K, star_sum, hEconj]
        _ = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
              E ((j : ℝ) * b) * E (-((k : ℝ) * b)) := Finset.sum_mul_sum ..
        _ = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
              E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b) := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
            rw [hEmul]
            congr 1
            push_cast
            ring
    have hint_sum : ∀ (s : Finset ℕ) (f : ℕ → ℝ → ℂ),
        (∀ k ∈ s, Continuous (f k)) →
        intervalIntegral (fun b => ∑ k ∈ s, f k b) (-1 / 2) (1 / 2) volume =
          ∑ k ∈ s, intervalIntegral (f k) (-1 / 2) (1 / 2) volume := by
      intro s f hf
      induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
          simp_rw [Finset.sum_insert ha]
          have ha_int : IntervalIntegrable (f a) volume (-1 / 2) (1 / 2) :=
            (hf a (Finset.mem_insert_self _ _)).intervalIntegrable (-1 / 2) (1 / 2)
          have hs_int : IntervalIntegrable (fun b => ∑ k ∈ s, f k b) volume (-1 / 2) (1 / 2) :=
            (hsum_cont s f fun k hk => hf k (Finset.mem_insert_of_mem hk)).intervalIntegrable _ _
          rw [intervalIntegral.integral_add ha_int hs_int,
            ih fun k hk => hf k (Finset.mem_insert_of_mem hk)]
    have hC : ((intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (1 / 2) volume : ℝ) : ℂ) =
        ((N + 1 : ℕ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      simp_rw [hK_expand]
      rw [hint_sum _ _ fun j _ =>
        hsum_cont (Finset.range (N + 1)) (fun k b => E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b))
          fun k _ => hE_cont (((j : ℤ) - (k : ℤ) : ℤ) : ℝ)]
      have hinner : ∀ j ∈ Finset.range (N + 1),
          intervalIntegral (fun b => ∑ k ∈ Finset.range (N + 1),
            E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b)) (-1 / 2) (1 / 2) volume = 1 := by
        intro j hj
        rw [hint_sum _ _ fun k _ => hE_cont (((j : ℤ) - (k : ℤ) : ℤ) : ℝ)]
        have hterm : ∀ k ∈ Finset.range (N + 1),
            intervalIntegral (fun b => E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * b))
              (-1 / 2) (1 / 2) volume = if k = j then (1 : ℂ) else 0 := by
          intro k _
          rw [hint_E_int]
          split_ifs with h1 h2 h2
          · rfl
          · exfalso; apply h2; omega
          · exfalso; apply h1; omega
          · rfl
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ j (fun _ => (1 : ℂ))]
        simp only [hj, ↓reduceIte]
      rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact Complex.ofReal_inj.mp hC
  have hK_tail_pointwise : ∀ b ∈ Set.Icc W (1 / 2 : ℝ), ‖K N b‖ ^ 2 ≤ 1 / (4 * b ^ 2) := by
    intro b hb
    have hbW : W ≤ b := hb.1
    have hb12 : b ≤ 1 / 2 := hb.2
    have hb_pos : 0 < b := lt_of_lt_of_le hW_pos hbW
    have hgeom : (1 - E b) * K N b = 1 - E (((N + 1 : ℕ) : ℝ) * b) := by
      simp_rw [K, hEpow]
      rw [mul_comm, geom_sum_mul_neg]
    have hnum : ‖1 - E (((N + 1 : ℕ) : ℝ) * b)‖ ≤ 2 := by
      have hnorm1 : ‖E (((N + 1 : ℕ) : ℝ) * b)‖ = 1 := Complex.norm_exp_ofReal_mul_I _
      have htri := norm_sub_le (1 : ℂ) (E (((N + 1 : ℕ) : ℝ) * b))
      rw [norm_one, hnorm1] at htri
      linarith
    have hsin_lb : 2 * b ≤ Real.sin (Real.pi * b) := by
      have h1 : 0 ≤ Real.pi * b := by positivity
      have h2 : Real.pi * b ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
      have hsin := Real.mul_le_sin h1 h2
      have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
      calc
        2 * b = 2 / Real.pi * (Real.pi * b) := by field_simp [hpi_ne]
        _ ≤ Real.sin (Real.pi * b) := hsin
    have hden_sq : 16 * b ^ 2 ≤ ‖1 - E b‖ ^ 2 := by
      have hnormSq : ‖1 - E b‖ ^ 2 = (1 - Real.cos (2 * Real.pi * b)) ^ 2 +
          (-Real.sin (2 * Real.pi * b)) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [E, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
          Complex.exp_ofReal_mul_I, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, add_zero,
          Complex.add_im, Complex.mul_im, mul_one, zero_add, zero_sub]
        ring
      have hcos2 : Real.cos (2 * Real.pi * b) = 1 - 2 * (Real.sin (Real.pi * b)) ^ 2 := by
        have h := Real.cos_two_mul (Real.pi * b)
        rw [show 2 * (Real.pi * b) = 2 * Real.pi * b by ring] at h
        have hcs := Real.cos_sq_add_sin_sq (Real.pi * b)
        linarith
      have hcs2 := Real.cos_sq_add_sin_sq (2 * Real.pi * b)
      have htrig : (1 - Real.cos (2 * Real.pi * b)) ^ 2 + (-Real.sin (2 * Real.pi * b)) ^ 2 =
          4 * (Real.sin (Real.pi * b)) ^ 2 := by
        nlinarith
      rw [hnormSq, htrig]
      nlinarith [sq_nonneg (Real.sin (Real.pi * b) - 2 * b)]
    have hden : 4 * b ≤ ‖1 - E b‖ := by
      nlinarith [norm_nonneg (1 - E b)]
    have hK_le : ‖K N b‖ ≤ 1 / (2 * b) := by
      have hmul_le : 4 * b * ‖K N b‖ ≤ 2 := by
        calc
          4 * b * ‖K N b‖ ≤ ‖1 - E b‖ * ‖K N b‖ :=
              mul_le_mul_of_nonneg_right hden (norm_nonneg _)
          _ = ‖(1 - E b) * K N b‖ := (norm_mul _ _).symm
          _ = ‖1 - E (((N + 1 : ℕ) : ℝ) * b)‖ := by rw [hgeom]
          _ ≤ 2 := hnum
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hK_sq : ‖K N b‖ ^ 2 ≤ (1 / (2 * b)) ^ 2 := by
      nlinarith [norm_nonneg (K N b)]
    calc
      ‖K N b‖ ^ 2 ≤ (1 / (2 * b)) ^ 2 := hK_sq
      _ = 1 / (4 * b ^ 2) := by ring
  have h_inv_sq_int :
      intervalIntegral (fun b : ℝ => 1 / (4 * b ^ 2)) W (1 / 2) volume =
        1 / (4 * W) - 1 / 2 := by
    let G : ℝ → ℝ := fun b => -(1 / (4 * b))
    have hGderiv : ∀ b ∈ Set.uIcc W (1 / 2 : ℝ),
        HasDerivAt G (1 / (4 * b ^ 2)) b := by
      intro b hb
      rw [Set.uIcc_of_le hW_le] at hb
      have hb_ne : b ≠ 0 := ne_of_gt (lt_of_lt_of_le hW_pos hb.1)
      have h1 : HasDerivAt (fun x : ℝ => -(4 * x)⁻¹) (-(-4 / (4 * b) ^ 2)) b := by
        have hm : HasDerivAt (fun x : ℝ => 4 * x) 4 b := by
          simpa using (hasDerivAt_id b).const_mul (4 : ℝ)
        exact (hm.inv (mul_ne_zero four_ne_zero hb_ne)).neg
      have hGeq : G = fun x : ℝ => -(4 * x)⁻¹ := by
        ext x; simp [G, one_div]
      have hval : -(-4 / (4 * b) ^ 2) = 1 / (4 * b ^ 2) := by
        field_simp [hb_ne]
      rw [hGeq, ← hval]
      exact h1
    have hGint : IntervalIntegrable (fun b : ℝ => 1 / (4 * b ^ 2)) volume W (1 / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hW_le]
      refine continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) ?_
      intro b hb
      have hb_ne : b ≠ 0 := ne_of_gt (lt_of_lt_of_le hW_pos hb.1)
      exact mul_ne_zero four_ne_zero (pow_ne_zero 2 hb_ne)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hGderiv hGint]
    have hW_ne : W ≠ 0 := ne_of_gt hW_pos
    simp only [G]
    field_simp [hW_ne]
    ring
  have hright_tail :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) W (1 / 2) volume ≤ 1 / (4 * W) := by
    have hinv_int : IntervalIntegrable (fun b : ℝ => 1 / (4 * b ^ 2)) volume W (1 / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le hW_le]
      refine continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 2)) ?_
      intro b hb
      have hb_ne : b ≠ 0 := ne_of_gt (lt_of_lt_of_le hW_pos hb.1)
      exact mul_ne_zero four_ne_zero (pow_ne_zero 2 hb_ne)
    have hmono := intervalIntegral.integral_mono_on hW_le (hnormSq_int W (1 / 2)) hinv_int
      hK_tail_pointwise
    linarith [hmono, h_inv_sq_int]
  have hleft_tail :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (-W) volume ≤ 1 / (4 * W) := by
    have hsymm :
        intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (-W) volume =
          intervalIntegral (fun b => ‖K N b‖ ^ 2) W (1 / 2) volume := by
      calc
        intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (-W) volume
            = intervalIntegral (fun b => ‖K N (-b)‖ ^ 2) (-1 / 2) (-W) volume := by
                simp_rw [hKneg]
        _ = intervalIntegral (fun b => ‖K N b‖ ^ 2) (-(-W)) (-(-1 / 2)) volume :=
                intervalIntegral.integral_comp_neg (fun b => ‖K N b‖ ^ 2)
        _ = intervalIntegral (fun b => ‖K N b‖ ^ 2) W (1 / 2) volume := by
                norm_num
    rw [hsymm]
    exact hright_tail
  have hsplit1 :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (-W) volume +
        intervalIntegral (fun b => ‖K N b‖ ^ 2) (-W) (1 / 2) volume =
          intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (1 / 2) volume :=
    intervalIntegral.integral_add_adjacent_intervals (hnormSq_int _ _) (hnormSq_int _ _)
  have hsplit2 :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) (-W) W volume +
        intervalIntegral (fun b => ‖K N b‖ ^ 2) W (1 / 2) volume =
          intervalIntegral (fun b => ‖K N b‖ ^ 2) (-W) (1 / 2) volume :=
    intervalIntegral.integral_add_adjacent_intervals (hnormSq_int _ _) (hnormSq_int _ _)
  have hsum :
      intervalIntegral (fun b => ‖K N b‖ ^ 2) (-1 / 2) (-W) volume +
        intervalIntegral (fun b => ‖K N b‖ ^ 2) (-W) W volume +
        intervalIntegral (fun b => ‖K N b‖ ^ 2) W (1 / 2) volume =
          ((N + 1 : ℕ) : ℝ) := by
    linarith [hsplit1, hsplit2, hfull_mass]
  have hhalf : 1 / (2 * W) = 1 / (4 * W) + 1 / (4 * W) := by ring
  linarith
