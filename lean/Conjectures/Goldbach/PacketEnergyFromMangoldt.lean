import Mathlib

private noncomputable def E_aux (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

private noncomputable def S_aux (n : ℕ) (w : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (w k : ℂ) * E_aux ((k : ℝ) * t))

private def Q_aux (n : ℕ) : ℕ :=
  (Nat.log 2 (n + 2)) ^ 2

private def arcs_aux (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q_aux n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q_aux n : ℝ) / ((q : ℝ) * (n : ℝ))}

private def L_aux (n : ℕ) : ℕ :=
  max 1 (Nat.log 2 n / 2)

private noncomputable def K_aux (n : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (L_aux n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L_aux n : ℝ)

private def B_aux (n : ℕ) : Set ℝ :=
  {t : ℝ | t ∉ arcs_aux n ∧ (1 : ℝ) / 2 < K_aux n t}

private noncomputable def w_aux (k : ℕ) : ℝ :=
  if Nat.Prime k then Real.log (k : ℝ) else 0

private noncomputable def low_aux (n k : ℕ) : ℝ :=
  if k ^ 3 ≤ n then w_aux k else 0

private noncomputable def high_aux (n k : ℕ) : ℝ :=
  w_aux k - low_aux n k

private noncomputable def diff_aux (n k : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt k - high_aux n k

private lemma continuous_E_mul (k : ℕ) :
    Continuous (fun t : ℝ => E_aux ((k : ℝ) * t)) := by
  unfold E_aux
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_const.mul continuous_id))).mul continuous_const)

private lemma continuous_S_aux (n : ℕ) (a : ℕ → ℝ) :
    Continuous (fun t : ℝ => S_aux n a t) := by
  unfold S_aux
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_E_mul k)

private lemma continuous_norm_sq_S_aux (n : ℕ) (a : ℕ → ℝ) :
    Continuous (fun t : ℝ => ‖S_aux n a t‖ ^ 2) :=
  ((continuous_S_aux n a).norm).pow 2

private lemma measurableSet_arcs_aux (n : ℕ) : MeasurableSet (arcs_aux n) := by
  have heq : arcs_aux n = ⋃ (q : ℕ), ⋃ (a : ℕ),
      {t : ℝ | 1 ≤ q ∧ q ≤ Q_aux n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (Q_aux n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
    ext t
    simp [arcs_aux]
  rw [heq]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ q ≤ Q_aux n ∧ a ≤ q ∧ Nat.Coprime a q
  · have hset :
        {t : ℝ | 1 ≤ q ∧ q ≤ Q_aux n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (Q_aux n : ℝ) / ((q : ℝ) * (n : ℝ))} =
        {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Q_aux n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
      ext t
      exact ⟨fun ht => ht.2.2.2.2, fun ht => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ht⟩⟩
    rw [hset]
    exact (isClosed_le ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet
  · have hset :
        {t : ℝ | 1 ≤ q ∧ q ≤ Q_aux n ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (Q_aux n : ℝ) / ((q : ℝ) * (n : ℝ))} = ∅ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      tauto
    rw [hset]
    exact MeasurableSet.empty

private lemma measurableSet_B_aux (n : ℕ) : MeasurableSet (B_aux n) := by
  have hK : Continuous (K_aux n) := by
    unfold K_aux
    refine (continuous_finsetSum _ fun j _ => ?_).div_const _
    exact Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hopen : MeasurableSet {t : ℝ | (1 : ℝ) / 2 < K_aux n t} :=
    (isOpen_lt continuous_const hK).measurableSet
  exact (measurableSet_arcs_aux n).compl.inter hopen

private lemma intervalIntegrable_indicator_of_continuous {f : ℝ → ℝ} {s : Set ℝ}
    (hf : Continuous f) (hs : MeasurableSet s) :
    IntervalIntegrable (s.indicator f) MeasureTheory.volume (0 : ℝ) 1 := by
  have h : IntervalIntegrable f MeasureTheory.volume (0 : ℝ) 1 :=
    hf.intervalIntegrable 0 1
  exact ⟨h.1.indicator hs, h.2.indicator hs⟩

private lemma S_aux_sub (n : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    S_aux n (fun k => a k - b k) t = S_aux n a t - S_aux n b t := by
  unfold S_aux
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

private lemma norm_sq_eq_re_sq_add_im_sq (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  have hmul : z * star z = ((z.re ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [sq] <;> ring
  have hnorm : ‖z * star z‖ = ‖z‖ ^ 2 := by
    rw [norm_mul, norm_star, sq]
  rw [← hnorm, hmul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private lemma E_aux_re (x : ℝ) : (E_aux x).re = Real.cos (2 * Real.pi * x) := by
  unfold E_aux
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add]

private lemma E_aux_im (x : ℝ) : (E_aux x).im = Real.sin (2 * Real.pi * x) := by
  unfold E_aux
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_mul, sub_zero, add_zero, zero_add]

private lemma S_aux_re (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    (S_aux n a t).re =
      ∑ k ∈ Finset.range (n + 1), a k * Real.cos (2 * Real.pi * ((k : ℝ) * t)) := by
  unfold S_aux
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, E_aux_re]

private lemma S_aux_im (n : ℕ) (a : ℕ → ℝ) (t : ℝ) :
    (S_aux n a t).im =
      ∑ k ∈ Finset.range (n + 1), a k * Real.sin (2 * Real.pi * ((k : ℝ) * t)) := by
  unfold S_aux
  rw [Complex.im_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, E_aux_im]

private lemma integral_cos_two_pi_sub (j k : ℕ) :
    intervalIntegral (fun t : ℝ => Real.cos (2 * Real.pi * ((j : ℝ) - (k : ℝ)) * t))
      (0 : ℝ) 1 MeasureTheory.volume = if j = k then 1 else 0 := by
  by_cases hjk : j = k
  · subst hjk
    simp
  · rw [if_neg hjk]
    set c : ℝ := 2 * Real.pi * ((j : ℝ) - (k : ℝ))
    have hc : c ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) ?_
      exact sub_ne_zero.mpr (by exact_mod_cast hjk : (j : ℝ) ≠ (k : ℝ))
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => Real.sin (c * x) / c) (Real.cos (c * t)) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => c * x) c t := by
        simpa using (hasDerivAt_id t).const_mul c
      have h2 : HasDerivAt (fun x : ℝ => Real.sin (c * x)) (Real.cos (c * t) * c) t :=
        (Real.hasDerivAt_sin (c * t)).comp t h1
      have h3 : HasDerivAt (fun x : ℝ => Real.sin (c * x) / c) ((Real.cos (c * t) * c) / c) t :=
        h2.div_const c
      simpa [mul_div_cancel_right₀ _ hc] using h3
    have hint : IntervalIntegrable (fun t : ℝ => Real.cos (c * t)) MeasureTheory.volume (0 : ℝ) 1 :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hsin1 : Real.sin (c * 1) = 0 := by
      have h2 : c * 1 = (((2 * ((j : ℤ) - (k : ℤ)) : ℤ) : ℝ) * Real.pi) := by
        dsimp only [c]
        push_cast
        ring
      rw [h2, Real.sin_int_mul_pi]
    change Real.sin (c * 1) / c - Real.sin (c * 0) / c = 0
    rw [hsin1, mul_zero, Real.sin_zero, zero_div, sub_self]

private lemma parseval_S_aux (n : ℕ) (a : ℕ → ℝ) :
    intervalIntegral (fun t => ‖S_aux n a t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
      ∑ k ∈ Finset.range (n + 1), (a k) ^ 2 := by
  have hexpand : ∀ t : ℝ, ‖S_aux n a t‖ ^ 2 =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        a j * a k * Real.cos (2 * Real.pi * ((j : ℝ) - (k : ℝ)) * t) := by
    intro t
    rw [norm_sq_eq_re_sq_add_im_sq, S_aux_re, S_aux_im, sq, sq,
      Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsub : 2 * Real.pi * ((j : ℝ) - (k : ℝ)) * t =
        2 * Real.pi * ((j : ℝ) * t) - 2 * Real.pi * ((k : ℝ) * t) := by ring
    rw [hsub, Real.cos_sub]
    ring
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul, integral_cos_two_pi_sub]
      simp [hj, sq]
    · intro k _
      exact (continuous_const.mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 1
  · intro j _
    exact (continuous_finsetSum _ fun k _ =>
      continuous_const.mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable 0 1

private lemma diff_aux_eq_zero_of_not_mem (n k : ℕ)
    (h1 : ¬ k ^ 3 ≤ n) (h2 : ¬ (IsPrimePow k ∧ ¬ Nat.Prime k)) :
    diff_aux n k = 0 := by
  unfold diff_aux high_aux low_aux w_aux
  by_cases hp : Nat.Prime k
  · simp [hp, h1, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · have hpp : ¬ IsPrimePow k := fun h => h2 ⟨h, hp⟩
    have hvm : ArithmeticFunction.vonMangoldt k = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
    simp [hp, hvm]

private lemma diff_aux_sq_le_log_sq (n k : ℕ) (hn : 1 ≤ n) (hk : k ≤ n) :
    (diff_aux n k) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn)
  have hd_nonneg : 0 ≤ diff_aux n k := by
    unfold diff_aux high_aux low_aux w_aux
    by_cases hp : Nat.Prime k
    · by_cases h3 : k ^ 3 ≤ n
      · simp [hp, h3, ArithmeticFunction.vonMangoldt_apply_prime hp]
        exact Real.log_nonneg (by exact_mod_cast hp.one_le)
      · simp [hp, h3, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hp, ArithmeticFunction.vonMangoldt_nonneg]
  have hd_le : diff_aux n k ≤ Real.log (n : ℝ) := by
    by_cases hk0 : k = 0
    · subst hk0
      unfold diff_aux high_aux low_aux w_aux
      simp [ArithmeticFunction.map_zero, hlogn_nonneg]
    · have hhigh_nonneg : 0 ≤ high_aux n k := by
        unfold high_aux low_aux w_aux
        by_cases hp : Nat.Prime k
        · by_cases h3 : k ^ 3 ≤ n
          · simp [hp, h3]
          · simp [hp, h3]
            exact Real.log_nonneg (by exact_mod_cast hp.one_le)
        · simp [hp]
      have hvm_le : ArithmeticFunction.vonMangoldt k ≤ Real.log (k : ℝ) :=
        ArithmeticFunction.vonMangoldt_le_log
      have hlogk_le : Real.log (k : ℝ) ≤ Real.log (n : ℝ) :=
        Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk0) (by exact_mod_cast hk)
      unfold diff_aux
      linarith
  nlinarith

private lemma sum_diff_aux_sq_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (diff_aux n k) ^ 2 ≤
      ((Nat.sqrt n + 1 : ℕ) : ℝ) * ((Nat.log 2 n + 2 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  classical
  let S₁ : Finset ℕ := (Finset.range (n + 1)).filter (fun k => k ^ 3 ≤ n)
  let S₂ : Finset ℕ := (Finset.range (n + 1)).filter (fun k => IsPrimePow k ∧ ¬ Nat.Prime k)
  have hsub : S₁ ∪ S₂ ⊆ Finset.range (n + 1) :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsum_eq :
      ∑ k ∈ Finset.range (n + 1), (diff_aux n k) ^ 2 =
        ∑ k ∈ S₁ ∪ S₂, (diff_aux n k) ^ 2 := by
    refine (Finset.sum_subset hsub ?_).symm
    intro k hk hnot
    have h1 : ¬ k ^ 3 ≤ n := by
      intro hc
      exact hnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hk, hc⟩))
    have h2 : ¬ (IsPrimePow k ∧ ¬ Nat.Prime k) := by
      intro hc
      exact hnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hk, hc⟩))
    rw [diff_aux_eq_zero_of_not_mem n k h1 h2]
    norm_num
  rw [hsum_eq]
  have hsum_le :
      ∑ k ∈ S₁ ∪ S₂, (diff_aux n k) ^ 2 ≤
        ((S₁ ∪ S₂).card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    calc ∑ k ∈ S₁ ∪ S₂, (diff_aux n k) ^ 2
        ≤ ∑ _k ∈ S₁ ∪ S₂, (Real.log (n : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hsub hk))
          exact diff_aux_sq_le_log_sq n k hn hkn
      _ = ((S₁ ∪ S₂).card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hS1_card : S₁.card ≤ Nat.sqrt n + 1 := by
    have hS1_sub : S₁ ⊆ Finset.range (Nat.sqrt n + 1) := by
      intro k hk
      have hk3 : k ^ 3 ≤ n := (Finset.mem_filter.mp hk).2
      have hk2 : k * k ≤ n := by
        have : k * k ≤ k ^ 3 := by
          cases k with
          | zero => simp
          | succ m => nlinarith
        exact le_trans this hk3
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_sqrt.mpr hk2))
    exact (Finset.card_le_card hS1_sub).trans_eq (Finset.card_range _)
  have hS2_card : S₂.card ≤ (Nat.sqrt n + 1) * (Nat.log 2 n + 1) := by
    let P : Finset (ℕ × ℕ) :=
      (Finset.range (Nat.sqrt n + 1)) ×ˢ (Finset.range (Nat.log 2 n + 1))
    have hS2_sub : S₂ ⊆ P.image (fun pm => pm.1 ^ pm.2) := by
      intro k hk
      have hk_mem := Finset.mem_filter.mp hk
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk_mem.1)
      have hpp : IsPrimePow k := hk_mem.2.1
      have hnotp : ¬ Nat.Prime k := hk_mem.2.2
      rcases (isPrimePow_nat_iff k).mp hpp with ⟨p, m, hp, hm_pos, hpm⟩
      have hm2 : 2 ≤ m := by
        by_contra hlt
        have hm1 : m = 1 := by omega
        subst hm1
        simp only [pow_one] at hpm
        rw [← hpm] at hnotp
        exact hnotp hp
      have hp_mem : p ∈ Finset.range (Nat.sqrt n + 1) := by
        have hp2 : p * p ≤ n := by
          calc p * p = p ^ 2 := (sq p).symm
            _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm2
            _ = k := hpm
            _ ≤ n := hkn
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_sqrt.mpr hp2))
      have hm_mem : m ∈ Finset.range (Nat.log 2 n + 1) := by
        have h2m : 2 ^ m ≤ n := by
          calc 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp.two_le m
            _ = k := hpm
            _ ≤ n := hkn
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_log_of_pow_le (by norm_num) h2m))
      exact Finset.mem_image.mpr ⟨(p, m), Finset.mem_product.mpr ⟨hp_mem, hm_mem⟩, hpm⟩
    calc S₂.card ≤ (P.image (fun pm => pm.1 ^ pm.2)).card := Finset.card_le_card hS2_sub
      _ ≤ P.card := Finset.card_image_le
      _ = (Nat.sqrt n + 1) * (Nat.log 2 n + 1) := by
          rw [Finset.card_product, Finset.card_range, Finset.card_range]
  have hcard : (S₁ ∪ S₂).card ≤ (Nat.sqrt n + 1) * (Nat.log 2 n + 2) := by
    calc (S₁ ∪ S₂).card ≤ S₁.card + S₂.card := Finset.card_union_le S₁ S₂
      _ ≤ (Nat.sqrt n + 1) + (Nat.sqrt n + 1) * (Nat.log 2 n + 1) :=
          Nat.add_le_add hS1_card hS2_card
      _ = (Nat.sqrt n + 1) * (Nat.log 2 n + 2) := by ring
  have hcardR : ((S₁ ∪ S₂).card : ℝ) ≤
      ((Nat.sqrt n + 1 : ℕ) : ℝ) * ((Nat.log 2 n + 2 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact le_trans hsum_le (mul_le_mul_of_nonneg_right hcardR (sq_nonneg _))

private lemma polylog_bound (n : ℕ) (hn : 2304000000 ^ 8 ≤ n) :
    ((Nat.sqrt n + 1 : ℕ) : ℝ) * ((Nat.log 2 n + 2 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤
      (n : ℝ) / 1000000 := by
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow 8 2304000000 (by norm_num)) hn
  have hn_pos_nat : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  set r : ℝ := Real.sqrt (Real.sqrt (Real.sqrt (n : ℝ)))
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hr_pos : 0 < r := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn_pos))
  have hr2 : r ^ 2 = Real.sqrt (Real.sqrt (n : ℝ)) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hr4 : r ^ 4 = Real.sqrt (n : ℝ) := by
    calc r ^ 4 = (r ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (Real.sqrt (n : ℝ))) ^ 2 := by rw [hr2]
      _ = Real.sqrt (n : ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hr8 : r ^ 8 = (n : ℝ) := by
    calc r ^ 8 = (r ^ 4) ^ 2 := by ring
      _ = (Real.sqrt (n : ℝ)) ^ 2 := by rw [hr4]
      _ = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos)
  have hC8 : (2304000000 : ℝ) ^ 8 ≤ r ^ 8 := by
    rw [hr8]
    exact_mod_cast hn
  have hr_ge : (2304000000 : ℝ) ≤ r := by
    by_contra hlt
    push_neg at hlt
    have h2 : r ^ 2 < (2304000000 : ℝ) ^ 2 := by nlinarith
    have h4 : (r ^ 2) ^ 2 < ((2304000000 : ℝ) ^ 2) ^ 2 := by nlinarith [sq_nonneg r]
    have h8 : ((r ^ 2) ^ 2) ^ 2 < (((2304000000 : ℝ) ^ 2) ^ 2) ^ 2 := by
      nlinarith [sq_nonneg (r ^ 2)]
    have hr8_eq : ((r ^ 2) ^ 2) ^ 2 = r ^ 8 := by ring
    have hC8_eq : (((2304000000 : ℝ) ^ 2) ^ 2) ^ 2 = (2304000000 : ℝ) ^ 8 := by ring
    linarith
  have hr1 : (1 : ℝ) ≤ r := by linarith
  have hr4_ge1 : (1 : ℝ) ≤ r ^ 4 := by
    have h2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith
    have h4 : (1 : ℝ) ≤ (r ^ 2) ^ 2 := by nlinarith
    linarith [show (r ^ 2) ^ 2 = r ^ 4 by ring]
  have hlog_le : Real.log (n : ℝ) ≤ 8 * r := by
    rw [← hr8, Real.log_pow]
    have h1 : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hr_pos
    push_cast
    linarith
  have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hlog2_ge : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have hinv : Real.log ((2 : ℝ)⁻¹) ≤ (2 : ℝ)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    rw [Real.log_inv] at hinv
    linarith
  have hnatlog_le : (Nat.log 2 n : ℝ) ≤ 16 * r := by
    have hpow : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (Nat.ne_of_gt hn_pos_nat)
    have hpowR : (2 : ℝ) ^ Nat.log 2 n ≤ (n : ℝ) := by exact_mod_cast hpow
    have hlogpow : Real.log ((2 : ℝ) ^ Nat.log 2 n) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) hpowR
    rw [Real.log_pow] at hlogpow
    have hnatlog_nonneg : (0 : ℝ) ≤ (Nat.log 2 n : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hsqrt_le : (Nat.sqrt n : ℝ) ≤ r ^ 4 := by
    have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
    have hsqR : (Nat.sqrt n : ℝ) ^ 2 ≤ (r ^ 4) ^ 2 := by
      have : (r ^ 4) ^ 2 = (n : ℝ) := by rw [← hr8]; ring
      rw [this, sq]
      exact_mod_cast hsq
    have hsn : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) := Nat.cast_nonneg _
    have hr4n : (0 : ℝ) ≤ r ^ 4 := pow_nonneg hr_nonneg 4
    nlinarith
  have hA : ((Nat.sqrt n + 1 : ℕ) : ℝ) ≤ 2 * r ^ 4 := by
    push_cast
    linarith
  have hB : ((Nat.log 2 n + 2 : ℕ) : ℝ) ≤ 18 * r := by
    push_cast
    linarith
  have hC : (Real.log (n : ℝ)) ^ 2 ≤ 64 * r ^ 2 := by
    nlinarith
  have hprod1 : ((Nat.sqrt n + 1 : ℕ) : ℝ) * ((Nat.log 2 n + 2 : ℕ) : ℝ) ≤
      (2 * r ^ 4) * (18 * r) :=
    mul_le_mul hA hB (Nat.cast_nonneg _) (by positivity)
  have hprod2 :
      ((Nat.sqrt n + 1 : ℕ) : ℝ) * ((Nat.log 2 n + 2 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤
        ((2 * r ^ 4) * (18 * r)) * (64 * r ^ 2) :=
    mul_le_mul hprod1 hC (sq_nonneg _) (by positivity)
  have hprod3 : ((2 * r ^ 4) * (18 * r)) * (64 * r ^ 2) = 2304 * r ^ 7 := by ring
  have hprod4 : 2304 * r ^ 7 ≤ r ^ 8 / 1000000 := by
    have h1 : (2304 : ℝ) ≤ r / 1000000 := by linarith
    have h2 : 2304 * r ^ 7 ≤ (r / 1000000) * r ^ 7 :=
      mul_le_mul_of_nonneg_right h1 (pow_nonneg hr_nonneg 7)
    calc 2304 * r ^ 7 ≤ (r / 1000000) * r ^ 7 := h2
      _ = r ^ 8 / 1000000 := by ring
  calc
    _ ≤ _ := hprod2
    _ = _ := hprod3
    _ ≤ _ := hprod4
    _ = _ := by rw [hr8]

theorem Conjectures.Goldbach.PacketEnergyFromMangoldt :
  (let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let m := fun (s : Set ℝ) (f : ℝ → ℝ) => intervalIntegral (s.indicator f) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → m (B n) (fun t => ‖S n (fun k => ArithmeticFunction.vonMangoldt k) t‖^2) ≤ (n:ℝ)/640) → (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let low := fun (n k : ℕ) => if k^3≤n then w k else 0; let high := fun (n k : ℕ) => w k-low n k; let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let B := fun n : ℕ => {t : ℝ | t ∉ arcs n ∧ (1:ℝ)/2 < K n t}; let U := fun (n : ℕ) (a : ℕ → ℝ) => intervalIntegral ((B n).indicator (fun t => ‖S n a t‖^2)) (0:ℝ) 1 MeasureTheory.volume; ∃ N : ℕ, ∀ n ≥ N, Even n → U n (high n) ≤ (n:ℝ)/576) := by
  intro hM
  dsimp only at hM ⊢
  rcases hM with ⟨N₀, hN₀⟩
  refine ⟨max N₀ (2304000000 ^ 8), fun n hn heven => ?_⟩
  have hM_n :
      intervalIntegral
        ((B_aux n).indicator (fun t => ‖S_aux n (fun k => ArithmeticFunction.vonMangoldt k) t‖ ^ 2))
        (0 : ℝ) 1 MeasureTheory.volume ≤ (n : ℝ) / 640 :=
    hN₀ n (le_trans (le_max_left _ _) hn) heven
  have hn_big : 2304000000 ^ 8 ≤ n := le_trans (le_max_right _ _) hn
  have hn1 : 1 ≤ n := le_trans (Nat.one_le_pow 8 2304000000 (by norm_num)) hn_big
  have hB_meas : MeasurableSet (B_aux n) := measurableSet_B_aux n
  have hint_high :
      IntervalIntegrable ((B_aux n).indicator (fun t => ‖S_aux n (high_aux n) t‖ ^ 2))
        MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_indicator_of_continuous (continuous_norm_sq_S_aux n (high_aux n)) hB_meas
  have hint_vm :
      IntervalIntegrable
        ((B_aux n).indicator (fun t => ‖S_aux n (fun k => ArithmeticFunction.vonMangoldt k) t‖ ^ 2))
        MeasureTheory.volume (0 : ℝ) 1 :=
    intervalIntegrable_indicator_of_continuous
      (continuous_norm_sq_S_aux n (fun k => ArithmeticFunction.vonMangoldt k)) hB_meas
  have hint_diff :
      IntervalIntegrable (fun t => ‖S_aux n (diff_aux n) t‖ ^ 2)
        MeasureTheory.volume (0 : ℝ) 1 :=
    (continuous_norm_sq_S_aux n (diff_aux n)).intervalIntegrable 0 1
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (B_aux n).indicator (fun t => ‖S_aux n (high_aux n) t‖ ^ 2) t ≤
        (17 / 16 : ℝ) *
          (B_aux n).indicator (fun t => ‖S_aux n (fun k => ArithmeticFunction.vonMangoldt k) t‖ ^ 2) t +
        17 * ‖S_aux n (diff_aux n) t‖ ^ 2 := by
    intro t _
    by_cases ht : t ∈ B_aux n
    · simp only [Set.indicator, if_pos ht]
      have hS_eq : S_aux n (high_aux n) t =
          S_aux n (fun k => ArithmeticFunction.vonMangoldt k) t - S_aux n (diff_aux n) t := by
        have hsub := S_aux_sub n (fun k => ArithmeticFunction.vonMangoldt k) (high_aux n) t
        have hfun : (fun k => ArithmeticFunction.vonMangoldt k - high_aux n k) = diff_aux n := rfl
        rw [hfun] at hsub
        rw [hsub]
        ring
      have htri : ‖S_aux n (high_aux n) t‖ ≤
          ‖S_aux n (fun k => ArithmeticFunction.vonMangoldt k) t‖ + ‖S_aux n (diff_aux n) t‖ := by
        rw [hS_eq]
        exact norm_sub_le _ _
      have h1 : ‖S_aux n (high_aux n) t‖ ^ 2 ≤
          (‖S_aux n (fun k => ArithmeticFunction.vonMangoldt k) t‖ + ‖S_aux n (diff_aux n) t‖) ^ 2 := by
        nlinarith [norm_nonneg (S_aux n (high_aux n) t)]
      nlinarith [sq_nonneg (‖S_aux n (fun k => ArithmeticFunction.vonMangoldt k) t‖ / 4 -
        4 * ‖S_aux n (diff_aux n) t‖)]
    · simp only [Set.indicator, if_neg ht]
      positivity
  have hmono :
      intervalIntegral ((B_aux n).indicator (fun t => ‖S_aux n (high_aux n) t‖ ^ 2))
        (0 : ℝ) 1 MeasureTheory.volume ≤
      intervalIntegral (fun t =>
        (17 / 16 : ℝ) *
          (B_aux n).indicator (fun t => ‖S_aux n (fun k => ArithmeticFunction.vonMangoldt k) t‖ ^ 2) t +
        17 * ‖S_aux n (diff_aux n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume :=
    intervalIntegral.integral_mono_on (by norm_num) hint_high
      ((hint_vm.const_mul (17 / 16 : ℝ)).add (hint_diff.const_mul 17)) hpt
  rw [intervalIntegral.integral_add (hint_vm.const_mul (17 / 16 : ℝ)) (hint_diff.const_mul 17),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hmono
  have hdiff_int :
      intervalIntegral (fun t => ‖S_aux n (diff_aux n) t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume ≤
        (n : ℝ) / 1000000 := by
    rw [parseval_S_aux]
    exact le_trans (sum_diff_aux_sq_le n hn1) (polylog_bound n hn_big)
  refine hmono.trans ?_
  calc
    _ ≤ (17 / 16 : ℝ) * ((n : ℝ) / 640) + 17 * ((n : ℝ) / 1000000) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hM_n (by norm_num))
        (mul_le_mul_of_nonneg_left hdiff_int (by norm_num))
    _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
