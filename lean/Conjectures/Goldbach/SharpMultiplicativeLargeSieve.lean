import Mathlib

/- Sources: community proofs AnalyticLargeSieve, SelbergSharpLargeSieve and MultiplicativeLargeSieve. -/


open MeasureTheory

namespace Conjectures.Goldbach.AnalyticLargeSieve_aux

noncomputable def Ex (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma Ex_add (x y : ℝ) : Ex (x + y) = Ex x * Ex y := by
  unfold Ex
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma Ex_int (m : ℤ) : Ex (m : ℝ) = 1 := by
  unfold Ex
  have h : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I := by
    push_cast
    ring
  have h2 : (2 : ℂ) * (Real.pi : ℂ) * (m : ℂ) * Complex.I =
      (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    ring
  rw [h, h2, Complex.exp_int_mul_two_pi_mul_I]

lemma Ex_conj (x : ℝ) : (starRingEnd ℂ) (Ex x) = Ex (-x) := by
  unfold Ex
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma norm_Ex (x : ℝ) : ‖Ex x‖ = 1 := by
  unfold Ex
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_Ex : Continuous Ex := by
  unfold Ex
  fun_prop

lemma orth (m : ℤ) (a : ℝ) :
    ∫ t in a..(a + 1), Ex ((m : ℝ) * t) = if m = 0 then 1 else 0 := by
  have hrewrite : (∫ t in a..(a + 1), Ex ((m : ℝ) * t)) =
      ∫ t in a..(a + 1), Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (t : ℂ)) := by
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    unfold Ex
    congr 1
    push_cast
    ring
  rw [hrewrite]
  by_cases hm : m = 0
  · subst hm
    simp
  · have hmr : (m : ℝ) ≠ 0 := by
      intro hzero
      exact hm (by exact_mod_cast hzero)
    have h1 : (2 * Real.pi * (m : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hmr
    have hc : (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      have h2 : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
        simpa [Complex.ofReal_eq_zero] using h1
      exact mul_ne_zero h2 Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have hval : Complex.exp (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
      have h := Ex_int m
      unfold Ex at h
      exact h
    have hexp : Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * ((a + 1 : ℝ) : ℂ)) =
        Complex.exp ((((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) * (a : ℂ)) := by
      have hcast : ((a + 1 : ℝ) : ℂ) = (a : ℂ) + 1 := by
        push_cast
        ring
      rw [hcast, mul_add, Complex.exp_add, mul_one, hval, mul_one]
    rw [hexp, sub_self, zero_div]
    simp [hm]

lemma parseval (s : Finset ℕ) (z : ℕ → ℂ) (a : ℝ) :
    ∫ t in a..(a + 1), ‖∑ k ∈ s, z k * Ex ((k : ℝ) * t)‖ ^ 2 = ∑ k ∈ s, ‖z k‖ ^ 2 := by
  classical
  set S : ℝ → ℂ := fun t => ∑ k ∈ s, z k * Ex ((k : ℝ) * t) with hSdef
  set W : ℝ → ℂ := fun t => ∑ k ∈ s, ∑ j ∈ s,
    ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t) with hWdef
  have hpoint : ∀ t : ℝ, (Complex.normSq (S t) : ℂ) = W t := by
    intro t
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [hSdef, hWdef]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    simp only [map_mul, Ex_conj]
    have hmul : Ex (-((k : ℝ) * t)) * Ex ((j : ℝ) * t) = Ex (((j : ℝ) - (k : ℝ)) * t) := by
      rw [← Ex_add]
      congr 1
      ring
    calc
      ((starRingEnd ℂ) (z k) * Ex (-((k : ℝ) * t))) * (z j * Ex ((j : ℝ) * t)) =
          ((starRingEnd ℂ) (z k) * z j) * (Ex (-((k : ℝ) * t)) * Ex ((j : ℝ) * t)) := by ring
      _ = ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t) := by rw [hmul]
  have hint_single : ∀ (c : ℂ) (b : ℝ),
      IntervalIntegrable (fun t : ℝ => c * Ex (b * t)) volume a (a + 1) := by
    intro c b
    exact (continuous_const.mul (continuous_Ex.comp (by fun_prop))).intervalIntegrable _ _
  have hint_W : IntervalIntegrable W volume a (a + 1) := by
    simp only [hWdef]
    exact (continuous_finsetSum _ (fun k _ => continuous_finsetSum _
      (fun j _ => continuous_const.mul (continuous_Ex.comp (by fun_prop))))).intervalIntegrable _ _
  have hmain : (∫ t in a..(a + 1), W t) = ((∑ k ∈ s, ‖z k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [hWdef]
    have houter (k : ℕ) (hk : k ∈ s) : IntervalIntegrable (fun t : ℝ => ∑ j ∈ s,
        ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t)) volume a (a + 1) := by
      exact (continuous_finsetSum _ (fun j _ => continuous_const.mul
        (continuous_Ex.comp (by fun_prop)))).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum houter]
    have hstep : ∀ k ∈ s, (∫ t in a..(a + 1), ∑ j ∈ s,
        ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t)) = ∑ j ∈ s,
        ((starRingEnd ℂ) (z k) * z j) * (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := by
      intro k hk
      have hii : ∀ j ∈ s, IntervalIntegrable
          (fun t : ℝ => ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t))
          volume a (a + 1) := fun j hj => hint_single _ _
      rw [intervalIntegral.integral_finsetSum hii]
      apply Finset.sum_congr rfl
      intro j hj
      rw [intervalIntegral.integral_const_mul]
      have hm : ((j : ℝ) - (k : ℝ)) = (((j : ℤ) - (k : ℤ) : ℤ) : ℝ) := by
        push_cast
        ring
      have ho : (∫ t in a..(a + 1), Ex (((j : ℝ) - (k : ℝ)) * t))
          = (if ((j : ℤ) - (k : ℤ)) = 0 then (1 : ℂ) else 0) := by
        rw [hm]
        exact orth _ a
      rw [ho]
    calc
      (∑ k ∈ s, ∫ t in a..(a + 1), ∑ j ∈ s,
          ((starRingEnd ℂ) (z k) * z j) * Ex (((j : ℝ) - (k : ℝ)) * t)) =
          ∑ k ∈ s, ∑ j ∈ s, ((starRingEnd ℂ) (z k) * z j) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then 1 else 0) := Finset.sum_congr rfl hstep
      _ = ∑ k ∈ s, (starRingEnd ℂ) (z k) * z k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hdiag : ∀ j ∈ s, ((starRingEnd ℂ) (z k) * z j) *
            (if ((j : ℤ) - (k : ℤ)) = 0 then (1 : ℂ) else 0) =
            (if j = k then (starRingEnd ℂ) (z k) * z j else 0) := by
          intro j hj
          by_cases hjk : j = k
          · subst hjk
            simp
          · have hne : ((j : ℤ) - (k : ℤ)) ≠ 0 := by
              intro hz
              exact hjk (by omega)
            simp [hne, hjk]
        rw [Finset.sum_congr rfl hdiag,
          Finset.sum_eq_single k (fun b hb hbk => by simp [hbk]) (fun hk' => absurd hk hk')]
        simp
      _ = ((∑ k ∈ s, ‖z k‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        apply Finset.sum_congr rfl
        intro k hk
        have hz : (starRingEnd ℂ) (z k) * z k = ((‖z k‖ ^ 2 : ℝ) : ℂ) := by
          have h := Complex.normSq_eq_conj_mul_self (z := z k)
          rw [Complex.normSq_eq_norm_sq] at h
          exact h.symm
        rw [hz]
        push_cast
        ring
  have hre : (∫ t in a..(a + 1), (W t).re) = (∫ t in a..(a + 1), W t).re := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc,
      intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp only [show a ≤ a + 1 by linarith, ite_true, one_smul]
    exact integral_re hint_W.def'
  calc
    (∫ t in a..(a + 1), ‖S t‖ ^ 2) = ∫ t in a..(a + 1), (W t).re := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hp := congrArg Complex.re (hpoint t)
      simpa only [Complex.ofReal_re, Complex.normSq_eq_norm_sq] using hp
    _ = (∫ t in a..(a + 1), W t).re := hre
    _ = ∑ k ∈ s, ‖z k‖ ^ 2 := by rw [hmain]; exact Complex.ofReal_re _

lemma hasDerivAt_Ex (lam t : ℝ) :
    HasDerivAt (fun s : ℝ => Ex (lam * s))
      (Ex (lam * t) * (((2 * Real.pi * lam : ℝ) : ℂ) * Complex.I)) t := by
  have hreal : HasDerivAt (fun s : ℝ => 2 * Real.pi * (lam * s)) (2 * Real.pi * lam) t := by
    have h1 : HasDerivAt (fun s : ℝ => lam * s) lam t := by
      simpa using (hasDerivAt_id t).const_mul lam
    have h2 : HasDerivAt (fun s : ℝ => Real.pi * (lam * s)) (Real.pi * lam) t := by
      simpa using h1.const_mul Real.pi
    simpa [mul_assoc] using h2.const_mul 2
  have h1 : HasDerivAt (fun s : ℝ => ((2 * Real.pi * (lam * s) : ℝ) : ℂ))
      ((2 * Real.pi * lam : ℝ) : ℂ) t := hreal.ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => ((2 * Real.pi * (lam * s) : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi * lam : ℝ) : ℂ) * Complex.I) t := h1.mul_const Complex.I
  have h3 := h2.cexp
  simpa only [Ex] using h3

lemma sum_image_of_inj {α β : Type*} [DecidableEq α] [DecidableEq β] {G : Type*}
    [AddCommMonoid G] (f : α → β) (g : β → G) :
    ∀ (A : Finset α), Set.InjOn f ↑A → (∑ a ∈ A, g (f a)) = ∑ b ∈ A.image f, g b := by
  intro A
  induction A using Finset.induction_on with
  | empty => intro _; simp
  | insert a A' ha ih =>
    intro hf
    have hne : f a ∉ A'.image f := by
      intro hmem
      obtain ⟨b, hbA, hbeq⟩ := Finset.mem_image.mp hmem
      have hba : b = a :=
        hf (Finset.mem_insert_of_mem hbA) (Finset.mem_insert_self a A') hbeq
      exact ha (hba ▸ hbA)
    have hf' : Set.InjOn f ↑A' :=
      hf.mono (fun x hx => Finset.mem_insert_of_mem hx)
    rw [Finset.sum_insert ha, Finset.image_insert, Finset.sum_insert hne, ih hf']

lemma gallagher_midpoint {f f' : ℝ → ℂ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hcont : Continuous f') (x r : ℝ) (hr : 0 < r) :
    ‖f x‖ ^ 2 ≤ (1 / (2 * r)) * (∫ t in (x - r)..(x + r), ‖f t‖ ^ 2)
      + ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ := by
  let g : ℝ → ℝ := fun t => ‖f t‖ ^ 2
  let gd : ℝ → ℝ := fun t => 2 * inner ℝ (f t) (f' t)
  have hg : ∀ t, HasDerivAt g (gd t) t := by
    intro t
    simpa [g, gd] using (hf t).norm_sq
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun t => (hf t).continuousAt
  have hgc : Continuous g := by
    change Continuous (fun t : ℝ => ‖f t‖ ^ 2)
    exact (continuous_norm.comp hfc).pow 2
  have hgdc : Continuous gd := by
    change Continuous (fun t : ℝ => (2 : ℝ) * inner ℝ (f t) (f' t))
    exact continuous_const.mul (hfc.inner hcont)
  have hleftWeightC : Continuous (fun t => (t - (x - r)) * gd t) :=
    (continuous_id.sub continuous_const).mul hgdc
  have hrightWeightC : Continuous (fun t => ((x + r) - t) * gd t) :=
    (continuous_const.sub continuous_id).mul hgdc
  have hprodC : Continuous (fun t => ‖f t‖ * ‖f' t‖) :=
    (continuous_norm.comp hfc).mul (continuous_norm.comp hcont)
  have h2prodC : Continuous (fun t : ℝ => (2 : ℝ) * (‖f t‖ * ‖f' t‖)) :=
    continuous_const.mul hprodC
  have hab : x - r ≤ x := by linarith
  have hbc : x ≤ x + r := by linarith
  have hFleft : ∀ t, HasDerivAt (fun t => (t - (x - r)) * g t)
      (g t + (t - (x - r)) * gd t) t := by
    intro t
    convert ((hasDerivAt_id t).sub_const (x - r)).mul (hg t) using 1
    · funext s
      simp
    · simp
  have hFright : ∀ t, HasDerivAt (fun t => ((x + r) - t) * g t)
      (-g t + ((x + r) - t) * gd t) t := by
    intro t
    convert ((hasDerivAt_id t).const_sub (x + r)).mul (hg t) using 1
    · funext s
      simp
    · simp
  have hleftDerivC : Continuous (fun t => g t + (t - (x - r)) * gd t) :=
    hgc.add hleftWeightC
  have hrightDerivC : Continuous (fun t => -g t + ((x + r) - t) * gd t) :=
    hgc.neg.add hrightWeightC
  have h1 : (∫ t in (x - r)..x, g t + (t - (x - r)) * gd t) = r * g x := by
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hFleft t)
      (hleftDerivC.intervalIntegrable (x - r) x) using 1
    ring
  have h2 : (∫ t in x..(x + r), -g t + ((x + r) - t) * gd t) = -(r * g x) := by
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hFright t)
      (hrightDerivC.intervalIntegrable x (x + r)) using 1
    ring
  have h1split :
      (∫ t in (x - r)..x, g t + (t - (x - r)) * gd t) =
        (∫ t in (x - r)..x, g t) +
          ∫ t in (x - r)..x, (t - (x - r)) * gd t :=
    intervalIntegral.integral_add
      (hgc.intervalIntegrable (x - r) x)
      (hleftWeightC.intervalIntegrable (x - r) x)
  have h2split :
      (∫ t in x..(x + r), -g t + ((x + r) - t) * gd t) =
        -(∫ t in x..(x + r), g t) +
          ∫ t in x..(x + r), ((x + r) - t) * gd t := by
    simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using
      intervalIntegral.integral_add
        (hgc.neg.intervalIntegrable x (x + r))
        (hrightWeightC.intervalIntegrable x (x + r))
  rw [h1split] at h1
  rw [h2split] at h2
  have hleft_point : ∀ t ∈ Set.Icc (x - r) x,
      |(t - (x - r)) * gd t| ≤ r * |gd t| := by
    intro t ht
    have ht0 : 0 ≤ t - (x - r) := by linarith [ht.1]
    have htr : t - (x - r) ≤ r := by linarith [ht.2]
    rw [abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_right htr (abs_nonneg _)
  have hright_point : ∀ t ∈ Set.Icc x (x + r),
      |((x + r) - t) * gd t| ≤ r * |gd t| := by
    intro t ht
    have ht0 : 0 ≤ (x + r) - t := by linarith [ht.2]
    have htr : (x + r) - t ≤ r := by linarith [ht.1]
    rw [abs_mul, abs_of_nonneg ht0]
    exact mul_le_mul_of_nonneg_right htr (abs_nonneg _)
  have hrGdAbsC : Continuous (fun t => r * |gd t|) :=
    continuous_const.mul hgdc.abs
  have hleft_bound :
      |∫ t in (x - r)..x, (t - (x - r)) * gd t| ≤
        r * ∫ t in (x - r)..x, |gd t| := by
    calc
      |∫ t in (x - r)..x, (t - (x - r)) * gd t| ≤
          ∫ t in (x - r)..x, |(t - (x - r)) * gd t| :=
        intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ t in (x - r)..x, r * |gd t| :=
        intervalIntegral.integral_mono_on hab
          (hleftWeightC.abs.intervalIntegrable (x - r) x)
          (hrGdAbsC.intervalIntegrable (x - r) x) hleft_point
      _ = r * ∫ t in (x - r)..x, |gd t| :=
        intervalIntegral.integral_const_mul r (fun t => |gd t|)
  have hright_bound :
      |∫ t in x..(x + r), ((x + r) - t) * gd t| ≤
        r * ∫ t in x..(x + r), |gd t| := by
    calc
      |∫ t in x..(x + r), ((x + r) - t) * gd t| ≤
          ∫ t in x..(x + r), |((x + r) - t) * gd t| :=
        intervalIntegral.abs_integral_le_integral_abs hbc
      _ ≤ ∫ t in x..(x + r), r * |gd t| :=
        intervalIntegral.integral_mono_on hbc
          (hrightWeightC.abs.intervalIntegrable x (x + r))
          (hrGdAbsC.intervalIntegrable x (x + r)) hright_point
      _ = r * ∫ t in x..(x + r), |gd t| :=
        intervalIntegral.integral_const_mul r (fun t => |gd t|)
  have hgd_bound : ∀ t, |gd t| ≤ 2 * (‖f t‖ * ‖f' t‖) := by
    intro t
    dsimp [gd]
    calc
      |2 * inner ℝ (f t) (f' t)| = 2 * |inner ℝ (f t) (f' t)| := by
        rw [abs_mul]; norm_num
      _ ≤ 2 * (‖f t‖ * ‖f' t‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by norm_num)
  have hJleft :
      (∫ t in (x - r)..x, |gd t|) ≤
        2 * ∫ t in (x - r)..x, ‖f t‖ * ‖f' t‖ := by
    calc
      (∫ t in (x - r)..x, |gd t|) ≤
          ∫ t in (x - r)..x, 2 * (‖f t‖ * ‖f' t‖) :=
        intervalIntegral.integral_mono hab
          (hgdc.abs.intervalIntegrable (x - r) x)
          (h2prodC.intervalIntegrable (x - r) x)
          (fun t => hgd_bound t)
      _ = 2 * ∫ t in (x - r)..x, ‖f t‖ * ‖f' t‖ :=
        intervalIntegral.integral_const_mul 2 (fun t => ‖f t‖ * ‖f' t‖)
  have hJright :
      (∫ t in x..(x + r), |gd t|) ≤
        2 * ∫ t in x..(x + r), ‖f t‖ * ‖f' t‖ := by
    calc
      (∫ t in x..(x + r), |gd t|) ≤
          ∫ t in x..(x + r), 2 * (‖f t‖ * ‖f' t‖) :=
        intervalIntegral.integral_mono hbc
          (hgdc.abs.intervalIntegrable x (x + r))
          (h2prodC.intervalIntegrable x (x + r))
          (fun t => hgd_bound t)
      _ = 2 * ∫ t in x..(x + r), ‖f t‖ * ‖f' t‖ :=
        intervalIntegral.integral_const_mul 2 (fun t => ‖f t‖ * ‖f' t‖)
  have hleft_main :
      r * g x ≤ (∫ t in (x - r)..x, g t) +
        r * ∫ t in (x - r)..x, |gd t| := by
    have hupper : (∫ t in (x - r)..x, (t - (x - r)) * gd t) ≤
        r * ∫ t in (x - r)..x, |gd t| := (le_abs_self _).trans hleft_bound
    linarith
  have hright_main :
      r * g x ≤ (∫ t in x..(x + r), g t) +
        r * ∫ t in x..(x + r), |gd t| := by
    have hneg := neg_le_of_abs_le hright_bound
    linarith
  have hGadj :
      (∫ t in (x - r)..x, g t) + (∫ t in x..(x + r), g t) =
        ∫ t in (x - r)..(x + r), g t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hgc.intervalIntegrable (x - r) x)
      (hgc.intervalIntegrable x (x + r))
  have hJadj :
      (∫ t in (x - r)..x, |gd t|) + (∫ t in x..(x + r), |gd t|) =
        ∫ t in (x - r)..(x + r), |gd t| :=
    intervalIntegral.integral_add_adjacent_intervals
      (hgdc.abs.intervalIntegrable (x - r) x)
      (hgdc.abs.intervalIntegrable x (x + r))
  have hHadj :
      (∫ t in (x - r)..x, ‖f t‖ * ‖f' t‖) +
          (∫ t in x..(x + r), ‖f t‖ * ‖f' t‖) =
        ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ :=
    intervalIntegral.integral_add_adjacent_intervals
      (hprodC.intervalIntegrable (x - r) x)
      (hprodC.intervalIntegrable x (x + r))
  have hsum :
      2 * r * g x ≤
        ((∫ t in (x - r)..x, g t) + (∫ t in x..(x + r), g t)) +
          ((r * ∫ t in (x - r)..x, |gd t|) +
            r * ∫ t in x..(x + r), |gd t|) := by
    linarith
  have hJtotal :
      (∫ t in (x - r)..(x + r), |gd t|) ≤
        2 * ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ := by
    rw [← hJadj, ← hHadj]
    linarith
  have hJmul :
      r * (∫ t in (x - r)..(x + r), |gd t|) ≤
        r * (2 * ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖) :=
    mul_le_mul_of_nonneg_left hJtotal (le_of_lt hr)
  have hmain :
      2 * r * g x ≤ (∫ t in (x - r)..(x + r), g t) +
        2 * r * ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ := by
    calc
      2 * r * g x ≤
          ((∫ t in (x - r)..x, g t) + (∫ t in x..(x + r), g t)) +
            ((r * ∫ t in (x - r)..x, |gd t|) +
              r * ∫ t in x..(x + r), |gd t|) := hsum
      _ = (∫ t in (x - r)..(x + r), g t) +
          r * ((∫ t in (x - r)..x, |gd t|) +
            ∫ t in x..(x + r), |gd t|) := by
        rw [hGadj]
        ring
      _ = (∫ t in (x - r)..(x + r), g t) +
          r * (∫ t in (x - r)..(x + r), |gd t|) := by rw [hJadj]
      _ ≤ (∫ t in (x - r)..(x + r), g t) +
          r * (2 * ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖) :=
        by linarith
      _ = (∫ t in (x - r)..(x + r), g t) +
          2 * r * ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ := by ring
  have hden : 0 < 2 * r := mul_pos (by norm_num) hr
  have hsub :
      2 * r * (g x - ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖) ≤
        ∫ t in (x - r)..(x + r), g t := by
    nlinarith
  have hquot :
      g x - ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ ≤
        (∫ t in (x - r)..(x + r), g t) / (2 * r) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hsub)
  have hfinish :
      g x ≤ (∫ t in (x - r)..(x + r), g t) / (2 * r) +
        ∫ t in (x - r)..(x + r), ‖f t‖ * ‖f' t‖ := by
    linarith
  simpa [g, div_eq_mul_inv, one_div, mul_comm] using hfinish

lemma sum_windows_le (F : ℝ → ℝ) (hF : Continuous F) (hF0 : ∀ t, 0 ≤ F t)
    (δ : ℝ) (_hδ : 0 < δ) :
    ∀ (X : Finset ℝ) (α β : ℝ),
      (∀ u ∈ X, ∀ v ∈ X, u ≠ v → δ ≤ |u - v|) →
      (∀ u ∈ X, α + δ / 2 ≤ u ∧ u ≤ β - δ / 2) →
      α ≤ β →
      (∑ u ∈ X, ∫ t in (u - δ / 2)..(u + δ / 2), F t) ≤ ∫ t in α..β, F t := by
  classical
  intro X
  induction X using Finset.induction_on_max with
  | empty =>
      intro α β _ _ hαβ
      simpa using intervalIntegral.integral_nonneg hαβ (fun u _ => hF0 u)
  | insert a s hlt ih =>
      intro α β hsep hbd _hαβ
      have ha : a ∉ s := fun ha => lt_irrefl a (hlt a ha)
      have hmem : ∀ u ∈ s, u ∈ insert a s := fun u hu => Finset.mem_insert_of_mem hu
      have hle : ∀ u ∈ s, u ≤ a - δ := by
        intro u hu
        have h1 : δ ≤ |u - a| :=
          hsep u (hmem u hu) a (Finset.mem_insert_self a s) (ne_of_lt (hlt u hu))
        have h2 : u - a ≤ 0 := by linarith [hlt u hu]
        rw [abs_of_nonpos h2] at h1
        linarith
      have ih' : (∑ u ∈ s, ∫ t in (u - δ / 2)..(u + δ / 2), F t)
          ≤ ∫ t in α..(a - δ / 2), F t :=
        ih α (a - δ / 2)
          (fun u hu v hv huv => hsep u (hmem u hu) v (hmem v hv) huv)
          (fun u hu => ⟨(hbd u (hmem u hu)).1, by have := hle u hu; linarith⟩)
          (by have := (hbd a (Finset.mem_insert_self a s)).1; linarith)
      have hsum : (∑ u ∈ insert a s, ∫ t in (u - δ / 2)..(u + δ / 2), F t)
          = (∫ t in (a - δ / 2)..(a + δ / 2), F t)
            + ∑ u ∈ s, ∫ t in (u - δ / 2)..(u + δ / 2), F t := Finset.sum_insert ha
      have hadd : (∫ t in α..(a - δ / 2), F t) + (∫ t in (a - δ / 2)..(a + δ / 2), F t)
          = ∫ t in α..(a + δ / 2), F t :=
        intervalIntegral.integral_add_adjacent_intervals
          (hF.intervalIntegrable α (a - δ / 2)) (hF.intervalIntegrable (a - δ / 2) (a + δ / 2))
      have hfin : ∫ t in α..(a + δ / 2), F t ≤ ∫ t in α..β, F t := by
        have hb : a + δ / 2 ≤ β := by
          have := (hbd a (Finset.mem_insert_self a s)).2; linarith
        have h2 : (∫ t in α..(a + δ / 2), F t) + (∫ t in (a + δ / 2)..β, F t)
            = ∫ t in α..β, F t :=
          intervalIntegral.integral_add_adjacent_intervals
            (hF.intervalIntegrable α (a + δ / 2)) (hF.intervalIntegrable (a + δ / 2) β)
        have h3 : 0 ≤ ∫ t in (a + δ / 2)..β, F t :=
          intervalIntegral.integral_nonneg hb (fun u _ => hF0 u)
        linarith
      calc (∑ u ∈ insert a s, ∫ t in (u - δ / 2)..(u + δ / 2), F t)
          = (∫ t in (a - δ / 2)..(a + δ / 2), F t)
              + ∑ u ∈ s, ∫ t in (u - δ / 2)..(u + δ / 2), F t := hsum
        _ ≤ (∫ t in (a - δ / 2)..(a + δ / 2), F t) + ∫ t in α..(a - δ / 2), F t :=
            by linarith [ih']
        _ = (∫ t in α..(a - δ / 2), F t) + (∫ t in (a - δ / 2)..(a + δ / 2), F t) := by ring
        _ = ∫ t in α..(a + δ / 2), F t := hadd
        _ ≤ ∫ t in α..β, F t := hfin

lemma frac_sep (Q q r a b : ℕ) (hq1 : 1 ≤ q) (hr1 : 1 ≤ r) (hqQ : q ≤ Q) (hrQ : r ≤ Q)
    (hca : Nat.Coprime a q) (hcb : Nat.Coprime b r) (hne : q ≠ r ∨ a ≠ b) :
    (1 : ℝ) / (Q : ℝ) ^ 2 ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
  have hcross_ne : a * r ≠ b * q := by
    intro hcross
    have hqr : q ∣ a * r := by
      rw [hcross]
      exact dvd_mul_left q b
    have hrq : r ∣ b * q := by
      rw [← hcross]
      exact dvd_mul_left r a
    have hqdr : q ∣ r := hca.symm.dvd_of_dvd_mul_left hqr
    have hrdq : r ∣ q := hcb.symm.dvd_of_dvd_mul_left hrq
    have hqreq : q = r := Nat.dvd_antisymm hqdr hrdq
    have hab : a = b := by
      apply Nat.mul_right_cancel (show 0 < r by omega)
      calc
        a * r = b * q := hcross
        _ = b * r := by rw [hqreq]
    rcases hne with hqne | hane
    · exact hqne hqreq
    · exact hane hab
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hcross : (1 : ℝ) ≤ |(a : ℝ) * r - (b : ℝ) * q| := by
    rcases lt_or_gt_of_ne hcross_ne with h | h
    · have hstep : (a : ℝ) * r + 1 ≤ (b : ℝ) * q := by
        exact_mod_cast Nat.succ_le_of_lt h
      exact le_trans (by linarith) (neg_le_abs _)
    · have hstep : (b : ℝ) * q + 1 ≤ (a : ℝ) * r := by
        exact_mod_cast Nat.succ_le_of_lt h
      exact le_trans (by linarith) (le_abs_self _)
  have hquot : (a : ℝ) / q - (b : ℝ) / r =
      ((a : ℝ) * r - (b : ℝ) * q) / ((q : ℝ) * r) := by
    field_simp
  have hsep : (1 : ℝ) / ((q : ℝ) * r) ≤ |(a : ℝ) / q - (b : ℝ) / r| := by
    rw [hquot, abs_div, abs_of_pos (mul_pos hqR hrR)]
    exact div_le_div_of_nonneg_right hcross (mul_pos hqR hrR).le
  have hden : (q : ℝ) * r ≤ (Q : ℝ) ^ 2 := by
    calc
      (q : ℝ) * r ≤ (Q : ℝ) * Q := by exact_mod_cast Nat.mul_le_mul hqQ hrQ
      _ = (Q : ℝ) ^ 2 := by ring
  exact (one_div_le_one_div_of_le (mul_pos hqR hrR) hden).trans hsep

lemma frac_inj (q r a b : ℕ) (hq1 : 1 ≤ q) (hr1 : 1 ≤ r) (ha : a < q) (hb : b < r)
    (hca : Nat.Coprime a q) (hcb : Nat.Coprime b r)
    (heq : (a : ℝ) / q = (b : ℝ) / r) : q = r ∧ a = b := by
  have hqfacts : 0 < q ∧ 1 ≤ q := ⟨Nat.zero_lt_of_lt ha, hq1⟩
  have hrfacts : 0 < r ∧ 1 ≤ r := ⟨Nat.zero_lt_of_lt hb, hr1⟩
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hqfacts.1.ne'
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hrfacts.1.ne'
  have hcross : a * r = b * q := by
    field_simp [hqR, hrR] at heq
    have hcross' : a * r = q * b := by exact_mod_cast heq
    simpa [Nat.mul_comm] using hcross'
  have hqr : q ∣ a * r := by
    rw [hcross]
    exact dvd_mul_left q b
  have hrq : r ∣ b * q := by
    rw [← hcross]
    exact dvd_mul_left r a
  have hqdr : q ∣ r := hca.symm.dvd_of_dvd_mul_left hqr
  have hrdq : r ∣ q := hcb.symm.dvd_of_dvd_mul_left hrq
  have hqreq : q = r := Nat.dvd_antisymm hqdr hrdq
  have hab : a = b := by
    apply Nat.mul_right_cancel (show 0 < r by omega)
    calc
      a * r = b * q := hcross
      _ = b * r := by rw [hqreq]
  exact ⟨hqreq, hab⟩

lemma frac_bounds (Q q a : ℕ) (hQ : 1 ≤ Q) (hq1 : 1 ≤ q) (hqQ : q ≤ Q) (ha : a < q) :
    (0 : ℝ) ≤ (a : ℝ) / q ∧ (a : ℝ) / q ≤ 1 - 1 / (Q : ℝ) ^ 2 := by
  have hqR : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have haR : (a : ℝ) + 1 ≤ q := by
    exact_mod_cast Nat.succ_le_of_lt ha
  have hfrac : (a : ℝ) / q ≤ 1 - 1 / (q : ℝ) := by
    calc
      (a : ℝ) / q ≤ ((q : ℝ) - 1) / q :=
        div_le_div_of_nonneg_right (by linarith) hqR.le
      _ = (q : ℝ) / q - 1 / (q : ℝ) := by ring
      _ = 1 - 1 / (q : ℝ) := by rw [div_self hqR.ne']
  have hinvQ_le_one : 1 / (Q : ℝ) ≤ 1 := div_le_self zero_le_one hQone
  have hinvQ_sq : 1 / (Q : ℝ) ^ 2 ≤ 1 / (Q : ℝ) := by
    calc
      1 / (Q : ℝ) ^ 2 = (1 / (Q : ℝ)) * (1 / (Q : ℝ)) := by ring
      _ ≤ 1 / (Q : ℝ) :=
        mul_le_of_le_one_right (one_div_nonneg.mpr hQR.le) hinvQ_le_one
  have hinvQq : 1 / (Q : ℝ) ≤ 1 / (q : ℝ) :=
    one_div_le_one_div_of_le hqR hqQ'
  have hsmall : 1 / (Q : ℝ) ^ 2 ≤ 1 / (q : ℝ) := hinvQ_sq.trans hinvQq
  constructor
  · exact div_nonneg (Nat.cast_nonneg a) hqR.le
  · calc
      (a : ℝ) / q ≤ 1 - 1 / (q : ℝ) := hfrac
      _ ≤ 1 - 1 / (Q : ℝ) ^ 2 := by linarith

theorem large_sieve (M N Q : ℕ) (c : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        ‖(∑ k ∈ Finset.Ico M (M + N), c k * Ex ((k : ℝ) * ((a : ℝ) / q)))‖ ^ 2)
      ≤ (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 := by
  classical
  by_cases hQ : Q = 0
  · subst hQ
    have h1 : Finset.Icc 1 0 = (∅ : Finset ℕ) := by decide
    rw [h1, Finset.sum_empty]
    refine mul_nonneg (add_nonneg ?_ ?_) ?_
    · exact mul_nonneg Real.pi_pos.le (Nat.cast_nonneg N)
    · positivity
    · exact Finset.sum_nonneg (fun k hk => sq_nonneg _)
  by_cases hN : N = 0
  · subst hN
    have h1 : Finset.Ico M (M + 0) = (∅ : Finset ℕ) := by
      rw [Nat.add_zero, Finset.Ico_self]
    simp
  have hQ1 : 1 ≤ Q := by omega
  have hN1 : 1 ≤ N := by omega
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hQ0 : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  set s : Finset ℕ := Finset.Ico M (M + N) with hs
  set L : ℝ := (M : ℝ) + (N : ℝ) / 2 with hL
  set δ : ℝ := 1 / (Q : ℝ) ^ 2 with hδ
  have hδpos : (0 : ℝ) < δ := by
    simp only [hδ]
    positivity
  set S : ℝ → ℂ := fun t => ∑ k ∈ s, c k * Ex ((k : ℝ) * t) with hSdef
  set T : ℝ → ℂ := fun t => Ex (-(L * t)) * S t with hTdef
  set V : ℝ → ℂ := fun t => ∑ k ∈ s,
    ((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k) * Ex ((k : ℝ) * t) with hVdef
  set Td : ℝ → ℂ := fun t => Ex (-(L * t)) * V t with hTddef
  have hTS : ∀ t, ‖T t‖ = ‖S t‖ := by
    intro t
    rw [hTdef, norm_mul, norm_Ex, one_mul]
  have hTdV : ∀ t, ‖Td t‖ = ‖V t‖ := by
    intro t
    rw [hTddef, norm_mul, norm_Ex, one_mul]
  have hmulwin : ∀ (k : ℕ) (t : ℝ),
      Ex (-(L * t)) * Ex ((k : ℝ) * t) = Ex (((k : ℝ) - L) * t) := by
    intro k t
    rw [← Ex_add]
    congr 1
    ring
  have hTsum : ∀ t, T t = ∑ k ∈ s, c k * Ex (((k : ℝ) - L) * t) := by
    intro t
    simp only [hTdef, hSdef, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    calc Ex (-(L * t)) * (c k * Ex ((k : ℝ) * t))
        = c k * (Ex (-(L * t)) * Ex ((k : ℝ) * t)) := by ring
      _ = c k * Ex (((k : ℝ) - L) * t) := by rw [hmulwin k t]
  have hderivT : ∀ t, HasDerivAt T (Td t) t := by
    intro t
    have hpiece : ∀ k ∈ s, HasDerivAt
        (fun u : ℝ => c k * Ex (((k : ℝ) - L) * u))
        (c k * (Ex (((k : ℝ) - L) * t) *
          (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I))) t :=
      fun k hk => (hasDerivAt_Ex ((k : ℝ) - L) t).const_mul (c k)
    have h1 : HasDerivAt (fun u : ℝ => ∑ k ∈ s, c k * Ex (((k : ℝ) - L) * u))
        (∑ k ∈ s, c k * (Ex (((k : ℝ) - L) * t) *
          (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I))) t := by
      have key : ∀ (u : Finset ℕ),
          HasDerivAt (fun v : ℝ => ∑ k ∈ u, c k * Ex (((k : ℝ) - L) * v))
            (∑ k ∈ u, c k * (Ex (((k : ℝ) - L) * t) *
              (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I))) t := by
        intro u
        induction u using Finset.induction_on with
        | empty => simpa using (hasDerivAt_const t (0 : ℂ))
        | insert a u' ha ih =>
            have hA : HasDerivAt (fun v : ℝ => c a * Ex (((a : ℝ) - L) * v))
                (c a * (Ex (((a : ℝ) - L) * t) *
                  (((2 * Real.pi * ((a : ℝ) - L) : ℝ) : ℂ) * Complex.I))) t :=
              (hasDerivAt_Ex ((a : ℝ) - L) t).const_mul (c a)
            have hsum := hA.add ih
            have hfun : ((fun v : ℝ => c a * Ex (((a : ℝ) - L) * v))
                  + fun v : ℝ => ∑ k ∈ u', c k * Ex (((k : ℝ) - L) * v))
                = (fun v : ℝ => ∑ k ∈ insert a u', c k * Ex (((k : ℝ) - L) * v)) := by
              funext v
              rw [Finset.sum_insert ha]
              simp
            have hder : (c a * (Ex (((a : ℝ) - L) * t) *
                  (((2 * Real.pi * ((a : ℝ) - L) : ℝ) : ℂ) * Complex.I)))
                + (∑ k ∈ u', c k * (Ex (((k : ℝ) - L) * t) *
                  (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I)))
                = ∑ k ∈ insert a u', c k * (Ex (((k : ℝ) - L) * t) *
                  (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I)) := by
              rw [Finset.sum_insert ha]
            rw [hfun] at hsum
            rw [hder] at hsum
            exact hsum
      exact key s
    have h3 : (fun u : ℝ => ∑ k ∈ s, c k * Ex (((k : ℝ) - L) * u)) = T := by
      funext u
      exact (hTsum u).symm
    rw [h3] at h1
    have h4 : (∑ k ∈ s, c k * (Ex (((k : ℝ) - L) * t) *
        (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I))) = Td t := by
      simp only [hTddef, hVdef, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      calc c k * (Ex (((k : ℝ) - L) * t) *
            (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I))
          = (((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k *
              (Ex (-(L * t)) * Ex ((k : ℝ) * t)) := by rw [hmulwin k t]; ring
        _ = Ex (-(L * t)) * (((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k) *
            Ex ((k : ℝ) * t)) := by ring
    rw [h4] at h1
    exact h1
  have hcontT : Continuous T :=
    continuous_iff_continuousAt.mpr (fun t => (hderivT t).continuousAt)
  have hcontTd : Continuous Td := by
    simp only [hTddef]
    refine (continuous_Ex.comp (by fun_prop)).mul ?_
    simp only [hVdef]
    exact continuous_finsetSum _ (fun k _ =>
      continuous_const.mul (continuous_Ex.comp (by fun_prop)))
  have hab : -(δ / 2) ≤ 1 - δ / 2 := by linarith
  have hpar1 : (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ ^ 2) = ∑ k ∈ s, ‖c k‖ ^ 2 := by
    have h1 : (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ ^ 2)
        = ∫ t in (-(δ / 2))..(1 - δ / 2), ‖S t‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [hTS t]
    rw [h1]
    have h2 : (1 - δ / 2) = (-(δ / 2)) + 1 := by ring
    rw [h2]
    simpa only [hSdef] using (parseval s c (-(δ / 2)))
  have hpar2 : (∫ t in (-(δ / 2))..(1 - δ / 2), ‖Td t‖ ^ 2)
      = ∑ k ∈ s, ‖((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k)‖ ^ 2 := by
    have h1 : (∫ t in (-(δ / 2))..(1 - δ / 2), ‖Td t‖ ^ 2)
        = ∫ t in (-(δ / 2))..(1 - δ / 2), ‖V t‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [hTdV t]
    rw [h1]
    have h2 : (1 - δ / 2) = (-(δ / 2)) + 1 := by ring
    rw [h2]
    simpa only [hVdef] using
      (parseval s (fun k => ((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k))
        (-(δ / 2)))
  have hcoef : ∀ k ∈ s, ‖((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k)‖ ^ 2
      ≤ (Real.pi * (N : ℝ)) ^ 2 * ‖c k‖ ^ 2 := by
    intro k hk
    have hk1 : M ≤ k := (Finset.mem_Ico.mp (hs ▸ hk)).1
    have hk2 : k < M + N := (Finset.mem_Ico.mp (hs ▸ hk)).2
    have hk1' : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hk2' : (k : ℝ) < (M : ℝ) + (N : ℝ) := by exact_mod_cast hk2
    have hkl : |(k : ℝ) - L| ≤ (N : ℝ) / 2 := by
      rw [abs_le]
      simp only [hL]
      constructor <;> linarith
    have hsq : ((k : ℝ) - L) ^ 2 ≤ ((N : ℝ) / 2) ^ 2 := by
      nlinarith [abs_nonneg ((k : ℝ) - L)]
    have hpi : (2 * Real.pi * ((k : ℝ) - L)) ^ 2 ≤ (Real.pi * (N : ℝ)) ^ 2 := by
      have h4 : 4 * Real.pi ^ 2 * ((k : ℝ) - L) ^ 2 ≤ 4 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      calc (2 * Real.pi * ((k : ℝ) - L)) ^ 2 = 4 * Real.pi ^ 2 * ((k : ℝ) - L) ^ 2 := by ring
        _ ≤ 4 * Real.pi ^ 2 * ((N : ℝ) / 2) ^ 2 := h4
        _ = (Real.pi * (N : ℝ)) ^ 2 := by ring
    have hI : ‖(Complex.I : ℂ)‖ = 1 := by simp
    have hreal : ‖((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ)‖ ^ 2
        = (2 * Real.pi * ((k : ℝ) - L)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp
      ring
    calc ‖((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k)‖ ^ 2
        = (‖((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ)‖ * ‖(Complex.I : ℂ)‖ * ‖c k‖) ^ 2 := by
          rw [norm_mul, norm_mul]
      _ = (2 * Real.pi * ((k : ℝ) - L)) ^ 2 * ‖c k‖ ^ 2 := by
          rw [hI, mul_one, mul_pow, hreal]
      _ ≤ (Real.pi * (N : ℝ)) ^ 2 * ‖c k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hpi (by positivity)
  have hYoung : (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ * ‖Td t‖)
      ≤ Real.pi * (N : ℝ) * ∑ k ∈ s, ‖c k‖ ^ 2 := by
    have hπN : (0 : ℝ) < Real.pi * (N : ℝ) := by
      have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
      positivity
    have hpt : ∀ t, 2 * (Real.pi * (N : ℝ)) * (‖T t‖ * ‖Td t‖)
        ≤ (Real.pi * (N : ℝ)) ^ 2 * ‖T t‖ ^ 2 + ‖Td t‖ ^ 2 := by
      intro t
      nlinarith [sq_nonneg ((Real.pi * (N : ℝ)) * ‖T t‖ - ‖Td t‖)]
    have hintL : IntervalIntegrable (fun t => ‖T t‖ * ‖Td t‖) volume (-(δ / 2)) (1 - δ / 2) :=
      (hcontT.norm.mul hcontTd.norm).intervalIntegrable _ _
    have hintL' : IntervalIntegrable (fun t => 2 * (Real.pi * (N : ℝ)) * (‖T t‖ * ‖Td t‖))
        volume (-(δ / 2)) (1 - δ / 2) :=
      (continuous_const.mul (hcontT.norm.mul hcontTd.norm)).intervalIntegrable _ _
    have hintR1 : IntervalIntegrable (fun t => (Real.pi * (N : ℝ)) ^ 2 * ‖T t‖ ^ 2)
        volume (-(δ / 2)) (1 - δ / 2) :=
      (continuous_const.mul (hcontT.norm.pow 2)).intervalIntegrable _ _
    have hintR2 : IntervalIntegrable (fun t => ‖Td t‖ ^ 2) volume (-(δ / 2)) (1 - δ / 2) :=
      (hcontTd.norm.pow 2).intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono
      (f := fun t => 2 * (Real.pi * (N : ℝ)) * (‖T t‖ * ‖Td t‖))
      (g := fun t => (Real.pi * (N : ℝ)) ^ 2 * ‖T t‖ ^ 2 + ‖Td t‖ ^ 2)
      (a := -(δ / 2)) (b := 1 - δ / 2) (μ := volume) hab hintL' (hintR1.add hintR2) hpt
    have hL : (∫ t in (-(δ / 2))..(1 - δ / 2), 2 * (Real.pi * (N : ℝ)) * (‖T t‖ * ‖Td t‖))
        = 2 * (Real.pi * (N : ℝ)) * (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ * ‖Td t‖) :=
      intervalIntegral.integral_const_mul (r := 2 * (Real.pi * (N : ℝ)))
        (f := fun t => ‖T t‖ * ‖Td t‖)
    have hR : (∫ t in (-(δ / 2))..(1 - δ / 2),
        (Real.pi * (N : ℝ)) ^ 2 * ‖T t‖ ^ 2 + ‖Td t‖ ^ 2)
        = (Real.pi * (N : ℝ)) ^ 2 * (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ ^ 2)
          + (∫ t in (-(δ / 2))..(1 - δ / 2), ‖Td t‖ ^ 2) := by
      rw [intervalIntegral.integral_add
        (f := fun t => (Real.pi * (N : ℝ)) ^ 2 * ‖T t‖ ^ 2) (g := fun t => ‖Td t‖ ^ 2)
        hintR1 hintR2,
        intervalIntegral.integral_const_mul (r := (Real.pi * (N : ℝ)) ^ 2)
          (f := fun t => ‖T t‖ ^ 2)]
    rw [hL, hR, hpar1, hpar2] at hmono
    have hsumcoef : (∑ k ∈ s, ‖((((2 * Real.pi * ((k : ℝ) - L) : ℝ) : ℂ) * Complex.I) * c k)‖ ^ 2)
        ≤ (Real.pi * (N : ℝ)) ^ 2 * ∑ k ∈ s, ‖c k‖ ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun k hk => hcoef k hk)
    have hkey : 2 * (Real.pi * (N : ℝ)) * (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ * ‖Td t‖)
        ≤ 2 * (Real.pi * (N : ℝ)) * (Real.pi * (N : ℝ) * ∑ k ∈ s, ‖c k‖ ^ 2) := by
      nlinarith [hmono, hsumcoef]
    exact le_of_mul_le_mul_left hkey (by positivity : (0 : ℝ) < 2 * (Real.pi * (N : ℝ)))
  set P : Finset (Σ q : ℕ, ℕ) := (Finset.Icc 1 Q).sigma
    (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q)) with hP
  set X : Finset ℝ := P.image (fun p : (Σ q : ℕ, ℕ) => (p.2 : ℝ) / (p.1 : ℝ)) with hX
  have hfrac_inj : Set.InjOn (fun p : (Σ q : ℕ, ℕ) => (p.2 : ℝ) / (p.1 : ℝ)) ↑P := by
    intro p hp p' hp' heq
    have hmem := Finset.mem_sigma.mp hp
    have hmem' := Finset.mem_sigma.mp hp'
    have hq1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hmem.1).1
    have hq1' : 1 ≤ p'.1 := (Finset.mem_Icc.mp hmem'.1).1
    have ha : p.2 < p.1 := Finset.mem_range.mp (Finset.mem_filter.mp hmem.2).1
    have ha' : p'.2 < p'.1 := Finset.mem_range.mp (Finset.mem_filter.mp hmem'.2).1
    have hcop : Nat.Coprime p.2 p.1 := (Finset.mem_filter.mp hmem.2).2
    have hcop' : Nat.Coprime p'.2 p'.1 := (Finset.mem_filter.mp hmem'.2).2
    obtain ⟨hqq, haa⟩ := frac_inj p.1 p'.1 p.2 p'.2 hq1 hq1' ha ha' hcop hcop' heq
    exact Sigma.ext hqq (heq_of_eq haa)
  have hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → δ ≤ |x - y| := by
    intro x hx y hy hne
    rw [hX] at hx hy
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    obtain ⟨p', hp', hpy⟩ := Finset.mem_image.mp hy
    have hmem := Finset.mem_sigma.mp hp
    have hmem' := Finset.mem_sigma.mp hp'
    have hq1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hmem.1).1
    have hq1' : 1 ≤ p'.1 := (Finset.mem_Icc.mp hmem'.1).1
    have hqQ : p.1 ≤ Q := (Finset.mem_Icc.mp hmem.1).2
    have hqQ' : p'.1 ≤ Q := (Finset.mem_Icc.mp hmem'.1).2
    have hcop : Nat.Coprime p.2 p.1 := (Finset.mem_filter.mp hmem.2).2
    have hcop' : Nat.Coprime p'.2 p'.1 := (Finset.mem_filter.mp hmem'.2).2
    have hpair : p.1 ≠ p'.1 ∨ p.2 ≠ p'.2 := by
      by_contra hc
      have hqeq : p.1 = p'.1 := by
        by_contra h
        exact hc (Or.inl h)
      have haeq : p.2 = p'.2 := by
        by_contra h
        exact hc (Or.inr h)
      apply hne
      rw [← hpx, ← hpy, Sigma.ext hqeq (heq_of_eq haeq)]
    have hfs := frac_sep Q p.1 p'.1 p.2 p'.2 hq1 hq1' hqQ hqQ' hcop hcop' hpair
    rw [hδ, ← hpx, ← hpy]
    exact hfs
  have hbounds : ∀ x ∈ X, (-(δ / 2)) + δ / 2 ≤ x ∧ x ≤ (1 - δ / 2) - δ / 2 := by
    intro x hx
    rw [hX] at hx
    obtain ⟨p, hp, hpx⟩ := Finset.mem_image.mp hx
    have hmem := Finset.mem_sigma.mp hp
    have hq1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hmem.1).1
    have hqQ : p.1 ≤ Q := (Finset.mem_Icc.mp hmem.1).2
    have ha : p.2 < p.1 := Finset.mem_range.mp (Finset.mem_filter.mp hmem.2).1
    have hfb := frac_bounds Q p.1 p.2 hQ1 hq1 hqQ ha
    have hx0 : (0 : ℝ) ≤ x := by rw [← hpx]; exact hfb.1
    have hx1 : x ≤ 1 - δ := by rw [← hpx, hδ]; exact hfb.2
    constructor <;> linarith
  have hmain : (∑ q ∈ Finset.Icc 1 Q,
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖S ((a : ℝ) / q)‖ ^ 2)
      = ∑ x ∈ X, ‖S x‖ ^ 2 := by
    have h1 : (∑ q ∈ Finset.Icc 1 Q,
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖S ((a : ℝ) / q)‖ ^ 2)
        = ∑ p ∈ P, ‖S ((p.2 : ℝ) / (p.1 : ℝ))‖ ^ 2 := by
      rw [Finset.sum_sigma']
    rw [h1, hX]
    exact (sum_image_of_inj (fun p : (Σ q : ℕ, ℕ) => (p.2 : ℝ) / (p.1 : ℝ))
      (fun x : ℝ => ‖S x‖ ^ 2) P hfrac_inj)
  have hstep : ∀ x ∈ X, ‖S x‖ ^ 2 ≤ (Q : ℝ) ^ 2 *
      (∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ ^ 2)
      + ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ * ‖Td t‖ := by
    intro x hx
    have hg := gallagher_midpoint hderivT hcontTd x (δ / 2) (by linarith)
    rw [hTS x] at hg
    have h2r : (1 : ℝ) / (2 * (δ / 2)) = (Q : ℝ) ^ 2 := by
      have he : (2 : ℝ) * (δ / 2) = δ := by ring
      rw [he, hδ]
      field_simp
    rw [h2r] at hg
    exact hg
  have hsum1 : (∑ x ∈ X, ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ ^ 2)
      ≤ ∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ ^ 2 :=
    sum_windows_le (fun t => ‖T t‖ ^ 2) (hcontT.norm.pow 2) (fun t => sq_nonneg _) δ hδpos X
      (-(δ / 2)) (1 - δ / 2) hsep hbounds hab
  have hsum2 : (∑ x ∈ X, ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ * ‖Td t‖)
      ≤ ∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ * ‖Td t‖ :=
    sum_windows_le (fun t => ‖T t‖ * ‖Td t‖) (hcontT.norm.mul hcontTd.norm)
      (fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)) δ hδpos X
      (-(δ / 2)) (1 - δ / 2) hsep hbounds hab
  have hQsq : (0 : ℝ) ≤ (Q : ℝ) ^ 2 := by positivity
  calc (∑ q ∈ Finset.Icc 1 Q,
        ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖S ((a : ℝ) / q)‖ ^ 2)
      = ∑ x ∈ X, ‖S x‖ ^ 2 := hmain
    _ ≤ ∑ x ∈ X, ((Q : ℝ) ^ 2 * (∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ ^ 2)
        + ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ * ‖Td t‖) :=
      Finset.sum_le_sum (fun x hx => hstep x hx)
    _ = (Q : ℝ) ^ 2 * (∑ x ∈ X, ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ ^ 2)
        + ∑ x ∈ X, ∫ t in (x - δ / 2)..(x + δ / 2), ‖T t‖ * ‖Td t‖ := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (Q : ℝ) ^ 2 * (∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ ^ 2)
        + ∫ t in (-(δ / 2))..(1 - δ / 2), ‖T t‖ * ‖Td t‖ :=
      by exact add_le_add (mul_le_mul_of_nonneg_left hsum1 hQsq) hsum2
    _ ≤ (Q : ℝ) ^ 2 * (∑ k ∈ s, ‖c k‖ ^ 2) + Real.pi * (N : ℝ) * ∑ k ∈ s, ‖c k‖ ^ 2 := by
      rw [hpar1]
      exact add_le_add (le_refl _) hYoung
    _ = (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ s, ‖c k‖ ^ 2 := by ring

end Conjectures.Goldbach.AnalyticLargeSieve_aux

open Conjectures.Goldbach.AnalyticLargeSieve_aux

theorem Conjectures.Goldbach.AnalyticLargeSieve :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); ∀ (M N Q : ℕ) (c : ℕ → ℂ), let S (t : ℝ) := ∑ k ∈ Finset.Ico M (M + N), c k * E ((k : ℝ) * t); (∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), ‖S ((a : ℝ) / q)‖ ^ 2) ≤ (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 := by
  dsimp only
  intro M N Q c
  exact large_sieve M N Q c


namespace Conjectures.Goldbach.SelbergSharpLargeSieve_aux


/- The large-sieve, separation and reciprocal-totient steps adapt the documented sources from muxkin, goldbach-proofs contribution 1708, c56bb450d43259dd871d29020d53facb6e5de557 (Apache-2.0). Separation adapts wzhxzkk’s frontier calculation; the sharp kernel is from OpenAI, openai/math, 3344da59991ed94f9ba711217b29c1d760badfa6. -/
section

namespace GoldbachEstermann
open Finset

/-- Each divisor has totient at most that of the ambient integer. Summing over
divisors and using Gauss's identity gives a divisor-count majorant. -/
private theorem inv_totient_le_pairs (q : ℕ) (hq : 0 < q) :
    1 / (q.totient : ℝ) ≤ ∑ ab ∈ q.divisorsAntidiagonal, ((ab.1:ℝ)⁻¹ * (ab.2:ℝ)⁻¹) := by
  have hφ := Nat.totient_pos.mpr hq
  have hcount : q ≤ q.divisors.card * q.totient := by
    calc
      _ = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
      _ ≤ ∑ _ ∈ q.divisors, q.totient := sum_le_sum (fun d hd =>
        Nat.le_of_dvd hφ (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd)))
      _ = _ := by simp
  calc
    _ ≤ (q.divisors.card : ℝ) / q := (div_le_div_iff₀ (by exact_mod_cast hφ) (by exact_mod_cast hq)).mpr
      (by rw [one_mul]; exact_mod_cast hcount)
    _ = ∑ _ ∈ q.divisorsAntidiagonal, (q:ℝ)⁻¹ := by
      rw [Nat.sum_divisorsAntidiagonal (fun _ _ => (q:ℝ)⁻¹)]; simp [div_eq_mul_inv]
    _ = _ := by
      apply sum_congr rfl
      intro ab hab
      rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul, mul_inv]

/-- A finite reciprocal-totient bound with constant one. -/
theorem sum_inv_totient_le (Q : ℕ) :
    (∑ q ∈ Icc 1 Q, 1 / (q.totient : ℝ)) ≤ (1 + Real.log Q)^2 := by
  let S := Icc 1 Q
  let w := fun ab : ℕ × ℕ => (ab.1:ℝ)⁻¹ * (ab.2:ℝ)⁻¹
  have hf (q : ℕ) (hq : q ∈ S) :
      q.divisorsAntidiagonal = (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q) := by
    obtain ⟨hq0,hqQ⟩ := mem_Icc.mp hq
    ext ab
    constructor
    · intro hab
      have hf := Nat.fst_mem_divisors_of_mem_antidiagonal hab
      have hs := Nat.snd_mem_divisors_of_mem_antidiagonal hab
      have hm (a : ℕ) (ha : a ∈ q.divisors) : a ∈ S :=
        mem_Icc.mpr ⟨Nat.pos_of_mem_divisors ha,(Nat.le_of_dvd hq0 (Nat.dvd_of_mem_divisors ha)).trans hqQ⟩
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hm _ hf,hm _ hs⟩,(Nat.mem_divisorsAntidiagonal.mp hab).1⟩
    · intro hab
      exact Nat.mem_divisorsAntidiagonal.mpr ⟨(mem_filter.mp hab).2,by omega⟩
  have hsum : (∑ i ∈ S, (i:ℝ)⁻¹) ≤ 1+Real.log Q := by
    simpa only [S,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] using harmonic_le_one_add_log Q
  calc
    _ ≤ ∑ q ∈ S, ∑ ab ∈ q.divisorsAntidiagonal, w ab :=
      sum_le_sum (fun q hq => inv_totient_le_pairs q (mem_Icc.mp hq).1)
    _ = ∑ q ∈ S, ∑ ab ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2=q), w ab :=
      sum_congr rfl (fun q hq => by rw [hf q hq])
    _ = ∑ ab ∈ (S ×ˢ S).filter (fun ab : ℕ × ℕ => ab.1*ab.2 ∈ S), w ab :=
      sum_fiberwise_eq_sum_filter _ _ _ _
    _ ≤ ∑ ab ∈ S ×ˢ S, w ab := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by dsimp [w]; positivity)
    _ = (∑ i ∈ S, (i:ℝ)⁻¹)^2 := by rw [sq,sum_product,sum_mul_sum]
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg fun _ _ => by positivity) hsum 2

end GoldbachEstermann

end

section

/- The sharp separated additive large sieve and its auxiliary proofs are adapted from
OpenAI, openai/math, revision 3344da59991ed94f9ba711217b29c1d760badfa6,
lean/OAI/NumberTheory/Ostmann/Preliminaries (Apache License 2.0). -/
namespace GoldbachBDHSharp

-- Upstream module CosecantKernel
namespace OAI

/-! # The cosecant kernel in the sharp additive large sieve

The finite-kernel identity is equation (3.6) of Montgomery--Vaughan,
Hilbert's inequality, JLMS (2) 8 (1974), 73--82. The scalar majorant is
Lemma 1 there. Only these concrete trigonometric statements are used.
-/

namespace Ostmann

noncomputable def cosecantKernel (x y : ℝ) : ℝ := (Real.sin (Real.pi * (x - y)))⁻¹
noncomputable def cotangentKernel (x y : ℝ) : ℝ :=
  Real.cos (Real.pi * (x - y)) / Real.sin (Real.pi * (x - y))

@[simp] theorem cosecantKernel_self (x : ℝ) : cosecantKernel x x = 0 := by
  simp [cosecantKernel]

@[simp] theorem cotangentKernel_self (x : ℝ) : cotangentKernel x x = 0 := by
  simp [cotangentKernel]

theorem cosecantKernel_skew (x y : ℝ) : cosecantKernel x y = -cosecantKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cosecantKernel, he]

theorem cotangentKernel_skew (x y : ℝ) : cotangentKernel x y = -cotangentKernel y x := by
  have he : Real.pi * (x - y) = -(Real.pi * (y - x)) := by ring
  simp [cotangentKernel, he, div_neg]

theorem cosecantKernel_triple (x y z : ℝ)
    (hxy : Real.sin (Real.pi * (x - y)) ≠ 0)
    (hxz : Real.sin (Real.pi * (x - z)) ≠ 0)
    (hyz : Real.sin (Real.pi * (y - z)) ≠ 0) :
    cosecantKernel x y * cosecantKernel x z =
      cosecantKernel y z * (cotangentKernel x y - cotangentKernel x z) := by
  have he : Real.pi * (y - z) = Real.pi * (x - z) - Real.pi * (x - y) := by ring
  have hs := Real.sin_sub (Real.pi * (x - z)) (Real.pi * (x - y))
  rw [← he] at hs
  unfold cosecantKernel cotangentKernel
  field_simp
  nlinarith

theorem cos_quartic_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  let f : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - Real.cos t
  have hd (t : ℝ) : deriv f t = Real.sin t - t + t ^ 3 / 6 := by
    dsimp [f]
    simp (disch := fun_prop)
    ring
  have hm : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [hd]
    have ht0 : 0 ≤ t := (Set.mem_Ici.mp (interior_subset ht))
    have hs := Real.sin_ge_sub_cube ht0
    linarith
  have hh := hm (show 0 ∈ Set.Ici (0 : ℝ) by simp) hx hx
  simpa [f] using hh

theorem sine_cosecant_majorant {x : ℝ} (hx : 0 < x) (hxp : x ≤ Real.pi / 2) :
    1 / (Real.sin x) ^ 2 + 2 * |Real.cos x / (Real.sin x) ^ 2| ≤ 3 / x ^ 2 := by
  have hx2 : x < 2 := by linarith [Real.pi_lt_four]
  have hs : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos x := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hxp⟩
  have hxSq : x ^ 2 ≤ 4 := by nlinarith
  have hcube := mul_le_mul_of_nonneg_right hxSq hx.le
  have hl : 0 ≤ x - x ^ 3 / 6 := by nlinarith
  have hsin := Real.sin_ge_sub_cube hx.le
  have hsq := mul_self_le_mul_self hl hsin
  have hcos := mul_le_mul_of_nonneg_left (cos_quartic_upper hx.le) (sq_nonneg x)
  have hpoly : (1 + 2 * Real.cos x) * x ^ 2 ≤ 3 * (Real.sin x) ^ 2 := by nlinarith
  rw [abs_of_nonneg (div_nonneg hc (sq_nonneg _))]
  have he : 1 / (Real.sin x) ^ 2 + 2 * (Real.cos x / (Real.sin x) ^ 2) =
      (1 + 2 * Real.cos x) / (Real.sin x) ^ 2 := by ring
  rw [he]
  exact (div_le_div_iff₀ (sq_pos_of_pos hs) (sq_pos_of_pos hx)).mpr hpoly

end Ostmann

end OAI

-- Upstream module SieveGeometricKernel
namespace OAI

/-! # The exact finite exponential kernel for the additive large sieve -/

namespace Ostmann

open scoped BigOperators

noncomputable def sieveHalfPhase (t : ℝ) : ℂ :=
  Complex.exp (((Real.pi * t : ℝ) : ℂ) * Complex.I)

@[simp] theorem sieveHalfPhase_zero : sieveHalfPhase 0 = 1 := by simp [sieveHalfPhase]

 theorem sieveHalfPhase_add (s t : ℝ) :
    sieveHalfPhase (s + t) = sieveHalfPhase s * sieveHalfPhase t := by
  simp only [sieveHalfPhase, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

@[simp] theorem sieveHalfPhase_norm (t : ℝ) : ‖sieveHalfPhase t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

 theorem sieveHalfPhase_sine (t : ℝ) :
    (2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ) =
      sieveHalfPhase t - sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

 theorem sieveHalfPhase_two_step (s t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) * sieveHalfPhase s =
      sieveHalfPhase (s + t) - sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_sine, sieveHalfPhase_add, sub_eq_add_neg s t, sieveHalfPhase_add]
  ring

 theorem sieve_geometric_kernel_mul (M : ℕ) (J t : ℝ) :
    ((2 : ℂ) * Complex.I * (Real.sin (Real.pi * t) : ℂ)) *
      (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
        sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hs := sieveHalfPhase_two_step (2 * (J + M) * t) t
    rw [show 2 * (J + (M : ℝ)) * t + t = (2 * (J + (M + 1 : ℕ)) - 1) * t by
      push_cast; ring,
      show 2 * (J + (M : ℝ)) * t - t = (2 * (J + M) - 1) * t by ring] at hs
    rw [hs]
    ring

 theorem sieve_geometric_kernel (M : ℕ) (J t : ℝ)
    (ht : Real.sin (Real.pi * t) ≠ 0) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * t)) =
      ((sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) /
        ((2 : ℂ) * Complex.I)) * (Real.sin (Real.pi * t) : ℂ)⁻¹ := by
  have hs := sieve_geometric_kernel_mul M J t
  have htC : (Real.sin (Real.pi * t) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hfactor : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
  apply (mul_left_cancel₀ (mul_ne_zero hfactor htC))
  rw [hs, div_eq_mul_inv]
  symm
  calc
    _ = (((2 : ℂ) * Complex.I) * ((2 : ℂ) * Complex.I)⁻¹) *
        ((Real.sin (Real.pi * t) : ℂ) * (Real.sin (Real.pi * t) : ℂ)⁻¹) *
          (sieveHalfPhase ((2 * (J + M) - 1) * t) - sieveHalfPhase ((2 * J - 1) * t)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hfactor, mul_inv_cancel₀ htC]; ring

end Ostmann

end OAI

-- Upstream module SeparatedInverseSquares
namespace OAI

/-! # The one-sided inverse-square estimate for separated sample points -/

namespace Ostmann

open scoped BigOperators

 theorem ordered_separated_lower {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    ∀ i, δ * (i.val + 1) ≤ x i := by
  have hi : ∀ k : ℕ, ∀ hk : k < n, δ * ((k : ℝ) + 1) ≤ x ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; simpa using hfirst ⟨0, hk⟩
    | succ k ih =>
      intro hk
      have hp := ih (by omega)
      have hg := hgap ⟨k, by omega⟩ ⟨k + 1, hk⟩ (by simp)
      push_cast
      linarith
  intro i
  exact hi i.val i.isLt

 theorem finite_positive_inverse_squares (n : ℕ) :
    (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) ≤ Real.pi ^ 2 / 6 := by
  have he : (∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2) =
      ∑ j ∈ Finset.range (n + 1), 1 / (j : ℝ) ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) n,
      Finset.sum_range_succ']
    simp
  rw [he, ← hasSum_zeta_two.tsum_eq]
  exact hasSum_zeta_two.summable.sum_le_tsum _ (fun j _ => by positivity)

 theorem ordered_separated_inverse_squares {n : ℕ} (x : Fin n → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hfirst : ∀ i, δ ≤ x i)
    (hgap : ∀ i j, i < j → δ ≤ x j - x i) :
    (∑ i, 1 / (x i) ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  have hx := ordered_separated_lower x δ hfirst hgap
  have hb (i : Fin n) : 1 / (x i) ^ 2 ≤
      (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := by
    have hi : 0 < (i.val : ℝ) + 1 := by positivity
    have hxi : 0 < x i := lt_of_lt_of_le hδ (hfirst i)
    have hs : (δ * ((i.val : ℝ) + 1)) ^ 2 ≤ (x i) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hx i) 2
    calc
      _ ≤ 1 / (δ * ((i.val : ℝ) + 1)) ^ 2 := one_div_le_one_div_of_le (by positivity) hs
      _ = _ := by simp only [mul_pow, one_div, mul_inv]
  calc
    _ ≤ ∑ i : Fin n, (δ ^ 2)⁻¹ * (1 / ((i.val : ℝ) + 1) ^ 2) := Finset.sum_le_sum (fun i _ => hb i)
    _ = (δ ^ 2)⁻¹ * ∑ i : Fin n, 1 / ((i.val : ℝ) + 1) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (δ ^ 2)⁻¹ * (Real.pi ^ 2 / 6) :=
      mul_le_mul_of_nonneg_left (finite_positive_inverse_squares n) (by positivity)
    _ = _ := by ring

end Ostmann

end OAI

-- Upstream module SeparatedSetSquares
namespace OAI

/-! # The inverse-square row sum for a finite separated set -/

namespace Ostmann

open scoped BigOperators

 theorem positive_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ x)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (6 * δ ^ 2) := by
  classical
  let e := S.orderEmbOfFin rfl
  have he (i : Fin S.card) : e i ∈ S := S.orderEmbOfFin_mem rfl i
  have hg (i j : Fin S.card) (hij : i < j) : δ ≤ e j - e i := by
    have hij' : e i < e j := e.strictMono hij
    have hh := hsep (e j) (he j) (e i) (he i) (ne_of_gt hij')
    rwa [abs_of_pos (sub_pos.mpr hij')] at hh
  have hh := ordered_separated_inverse_squares (fun i => e i) δ hδ
    (fun i => hfirst _ (he i)) hg
  have hs : (∑ x ∈ S, 1 / x ^ 2) = ∑ i : Fin S.card, 1 / (e i) ^ 2 := by
    conv_lhs => rw [← S.image_orderEmbOfFin_univ rfl]
    rw [Finset.sum_image]
    exact fun i _ j _ hij => e.injective hij
  rwa [hs]

 theorem separated_set_inverse_squares (S : Finset ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hfirst : ∀ x ∈ S, δ ≤ |x|)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ |x - y|) :
    (∑ x ∈ S, 1 / x ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let P := S.filter (fun x => 0 < x)
  let N := S.filter (fun x => ¬0 < x)
  let R := N.image (fun x => -x)
  have hP := positive_set_inverse_squares P δ hδ
    (fun x hx => by
      have h := Finset.mem_filter.mp hx
      simpa only [abs_of_pos h.2] using hfirst x h.1)
    (fun x hx y hy hxy => hsep x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy)
  have hRfirst (x : ℝ) (hx : x ∈ R) : δ ≤ x := by
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    have hy' := Finset.mem_filter.mp hy
    simpa only [abs_of_nonpos (le_of_not_gt hy'.2)] using hfirst y hy'.1
  have hRsep (x : ℝ) (hx : x ∈ R) (y : ℝ) (hy : y ∈ R) (hxy : x ≠ y) : δ ≤ |x - y| := by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
    have hh := hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
      (fun hab => hxy (congrArg Neg.neg hab))
    simpa only [neg_sub_neg, abs_sub_comm] using hh
  have hR := positive_set_inverse_squares R δ hδ hRfirst hRsep
  have hsum : (∑ x ∈ P, 1 / x ^ 2) + (∑ x ∈ N, 1 / x ^ 2) = ∑ x ∈ S, 1 / x ^ 2 :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have he : (∑ x ∈ R, 1 / x ^ 2) = ∑ x ∈ N, 1 / x ^ 2 := by
    rw [Finset.sum_image]
    · simp
    · exact fun _ _ _ _ hab => neg_injective hab
  rw [he] at hR
  rw [← hsum]
  have hid : Real.pi ^ 2 / (3 * δ ^ 2) = 2 * (Real.pi ^ 2 / (6 * δ ^ 2)) := by ring
  rw [hid]
  linarith

end Ostmann

end OAI

-- Upstream module CosecantDistanceBound
namespace OAI

/-! # The cosecant row weight depends only on distance to an integer -/

namespace Ostmann

noncomputable def cosecantRowWeight (t : ℝ) : ℝ :=
  1 / Real.sin (Real.pi * t) ^ 2 +
    2 * |Real.cos (Real.pi * t) / Real.sin (Real.pi * t) ^ 2|

 theorem cosecantRowWeight_eq (x y : ℝ) :
    cosecantKernel x y ^ 2 + 2 * |cosecantKernel x y * cotangentKernel x y| =
      cosecantRowWeight (x - y) := by
  unfold cosecantKernel cotangentKernel cosecantRowWeight
  congr 1
  · ring
  · congr 2
    ring

 theorem cosecantRowWeight_shift (t : ℝ) (m : ℤ) :
    cosecantRowWeight (t - m) = cosecantRowWeight t := by
  have he : Real.pi * (t - m) = Real.pi * t - (m : ℝ) * Real.pi := by ring
  have hs : |Real.sin (Real.pi * (t - m))| = |Real.sin (Real.pi * t)| := by
    rw [he, Real.sin_sub_int_mul_pi, abs_mul]
    simp
  have hc : |Real.cos (Real.pi * (t - m))| = |Real.cos (Real.pi * t)| := by
    rw [he, Real.cos_sub_int_mul_pi, abs_mul]
    simp
  have hs2 := congrArg (fun x : ℝ => x ^ 2) hs
  simp only [sq_abs] at hs2
  unfold cosecantRowWeight
  rw [hs2, abs_div, abs_div, hc]

 theorem cosecantRowWeight_abs (t : ℝ) : cosecantRowWeight |t| = cosecantRowWeight t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    simp [cosecantRowWeight, Real.sin_neg, Real.cos_neg]

 theorem cosecantRowWeight_bound (t d : ℝ) (m : ℤ)
    (hd : 0 < d) (hdhalf : d ≤ 1 / 2) (he : |t - m| = d) :
    cosecantRowWeight t ≤ 3 / (Real.pi ^ 2 * d ^ 2) := by
  rw [← cosecantRowWeight_shift t m, ← cosecantRowWeight_abs, he]
  have hp : 0 < Real.pi * d := mul_pos Real.pi_pos hd
  have hh : Real.pi * d ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hb := sine_cosecant_majorant hp hh
  simpa only [cosecantRowWeight, mul_pow] using hb

end Ostmann

end OAI

-- Upstream module CircleSeparatedPoints
namespace OAI

/-! # Centering a separated finite family on the circle -/

namespace Ostmann

open scoped BigOperators

noncomputable def centeredCircleRemainder (t : ℝ) : ℝ := t - (⌊t + 1 / 2⌋ : ℤ)

def CircleSeparated {ι : Type*} (x : ι → ℝ) (δ : ℝ) : Prop :=
  ∀ s t, s ≠ t → ∀ m : ℤ, δ ≤ |x s - x t - m|

 theorem centeredCircleRemainder_bounds (t : ℝ) :
    -(1 / 2) ≤ centeredCircleRemainder t ∧ centeredCircleRemainder t < 1 / 2 := by
  have hl := Int.floor_le (t + 1 / 2)
  have hu := Int.lt_floor_add_one (t + 1 / 2)
  dsimp [centeredCircleRemainder]
  constructor <;> linarith

 theorem circleSeparated_sine_ne_zero {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hx : CircleSeparated x δ) {s t : ι} (hst : s ≠ t) :
    Real.sin (Real.pi * (x s - x t)) ≠ 0 := by
  intro hz
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hz
  have he : x s - x t - (m : ℝ) = 0 := by nlinarith [Real.pi_pos]
  have hh := hx s t hst m
  rw [he, abs_zero] at hh
  linarith

 theorem circleSeparated_remainders {ι : Type*} (x : ι → ℝ) (δ : ℝ)
    (hx : CircleSeparated x δ) (center s t : ι) (hst : s ≠ t) :
    δ ≤ |centeredCircleRemainder (x s - x center) -
      centeredCircleRemainder (x t - x center)| := by
  have hh := hx s t hst (⌊x s - x center + 1 / 2⌋ - ⌊x t - x center + 1 / 2⌋)
  push_cast at hh
  convert hh using 1; congr 1; dsimp [centeredCircleRemainder]; ring

 theorem circleSeparated_inverse_square_row {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s ∈ Finset.univ.erase center,
      1 / centeredCircleRemainder (x s - x center) ^ 2) ≤ Real.pi ^ 2 / (3 * δ ^ 2) := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  let S := F.image r
  have hfirst (s : ι) (hs : s ∈ F) : δ ≤ |r s| :=
    hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
  have hinj : Set.InjOn r F := by
    intro s hs t ht he
    by_contra hst
    have hb := circleSeparated_remainders x δ hx center s t hst
    change δ ≤ |r s - r t| at hb
    rw [he, sub_self, abs_zero] at hb
    linarith
  have hb := separated_set_inverse_squares S δ hδ (by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    exact hfirst s hs) (by
    intro y hy z hz hyz
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    exact circleSeparated_remainders x δ hx center s t (fun hst => hyz (congrArg r hst)))
  have he : (∑ y ∈ S, 1 / y ^ 2) = ∑ s ∈ F, 1 / (r s) ^ 2 := by
    exact Finset.sum_image hinj
  rwa [he] at hb

end Ostmann

end OAI

-- Upstream module CosecantRowSum
namespace OAI

/-! # The sharp row budget for the cosecant matrix -/

namespace Ostmann

open scoped BigOperators

 theorem cosecant_row_sum_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ) (center : ι) :
    (∑ s, cosecantKernel (x s) (x center) ^ 2) +
        2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| ≤
      1 / δ ^ 2 := by
  classical
  let F := Finset.univ.erase center
  let r := fun s => centeredCircleRemainder (x s - x center)
  have he (s : ι) : cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s) =
      cosecantKernel (x s) (x center) * cotangentKernel (x s) (x center) := by
    rw [cosecantKernel_skew (x center) (x s), cotangentKernel_skew (x center) (x s)]
    ring
  have hsum : (∑ s, cosecantKernel (x s) (x center) ^ 2) +
      2 * ∑ s, |cosecantKernel (x center) (x s) * cotangentKernel (x center) (x s)| =
        ∑ s ∈ F, cosecantRowWeight (x s - x center) := by
    simp_rw [he]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    simp_rw [cosecantRowWeight_eq]
    apply (Finset.sum_erase_add _ _ (Finset.mem_univ center)).symm.trans ?_
    simp [cosecantRowWeight, F]
  have hb (s : ι) (hs : s ∈ F) :
      cosecantRowWeight (x s - x center) ≤ 3 / (Real.pi ^ 2 * (r s) ^ 2) := by
    have hd := hx s center (Finset.mem_erase.mp hs).1 ⌊x s - x center + 1 / 2⌋
    change δ ≤ |r s| at hd
    have hhalf : |r s| ≤ 1 / 2 := abs_le.mpr
      ⟨(centeredCircleRemainder_bounds _).1, (centeredCircleRemainder_bounds _).2.le⟩
    have hh := cosecantRowWeight_bound (x s - x center) |r s|
      ⌊x s - x center + 1 / 2⌋ (lt_of_lt_of_le hδ hd) hhalf rfl
    simpa only [sq_abs] using hh
  rw [hsum]
  calc
    _ ≤ ∑ s ∈ F, 3 / (Real.pi ^ 2 * (r s) ^ 2) := Finset.sum_le_sum hb
    _ = (3 / Real.pi ^ 2) * ∑ s ∈ F, 1 / (r s) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ ≤ (3 / Real.pi ^ 2) * (Real.pi ^ 2 / (3 * δ ^ 2)) :=
      mul_le_mul_of_nonneg_left (circleSeparated_inverse_square_row x δ hδ hx center) (by positivity)
    _ = _ := by field_simp

end Ostmann

end OAI

-- Upstream module SkewKernelSquare
namespace OAI

/-! # A finite algebraic identity for the large-sieve kernel

This is the cancellation underlying Montgomery--Vaughan's equation (3.6).
The diagonal correction is retained explicitly before any norm estimate.
-/

namespace Ostmann

open scoped BigOperators

section
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]

 theorem skew_kernel_square_entry (h k : ι → ι → K)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (∑ r, h r s * h r t) =
      (if s = t then ∑ r, h r s ^ 2 else 0) +
        h s t * ((∑ r, k r s) - ∑ r, k r t) + 2 * h s t * k s t := by
  by_cases hst : s = t
  · subst t
    simp [hdiag, sq]
  · have he (r : ι) : h r s * h r t = h s t * (k r s - k r t) +
        (if r = s then h s t * k s t else 0) +
        (if r = t then h s t * k s t else 0) := by
      by_cases hrs : r = s
      · subst r
        simp [hdiag, kdiag, hst]
      · by_cases hrt : r = t
        · subst r
          rw [hdiag, kdiag, kskew t s]
          simp only [hrs, ↓reduceIte]
          ring
        · simp only [hrs, hrt, ↓reduceIte, add_zero]
          exact htriple r s t hrs hrt hst
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [hst, ↓reduceIte, zero_add, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    ring

end

end Ostmann

end OAI

-- Upstream module HermitianEigenvector
namespace OAI

/-! # Finite Hermitian eigenvector cancellation -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem hermitian_eigenvector_left {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) (v : ι → ℂ) :
    star u ⬝ᵥ (A *ᵥ v) = (μ : ℂ) * (star u ⬝ᵥ v) := by
  have h := hA.star_dotProduct_mulVec_comm u v
  rw [heig, dotProduct_smul] at h
  apply star_injective
  rw [h]
  simp [dotProduct, mul_comm]

theorem hermitian_eigenvector_commutator {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (D : Matrix ι ι ℂ) (u : ι → ℂ) (μ : ℝ) (heig : A *ᵥ u = (μ : ℂ) • u) :
    star u ⬝ᵥ ((D * A - A * D) *ᵥ u) = 0 := by
  rw [sub_mulVec, dotProduct_sub, ← mulVec_mulVec, ← mulVec_mulVec,
    heig, mulVec_smul, dotProduct_smul, hermitian_eigenvector_left hA u μ heig]
  simp only [smul_eq_mul, sub_self]

end Ostmann

end OAI

-- Upstream module CosecantMatrix
namespace OAI

/-! # The exact square of the finite cosecant matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def imaginaryKernelMatrix (h : ι → ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.of (fun s t => Complex.I * (h s t : ℂ))

omit [Fintype ι] [DecidableEq ι] in
 theorem imaginaryKernelMatrix_hermitian (h : ι → ι → ℝ)
    (hskew : ∀ s t, h s t = -h t s) : (imaginaryKernelMatrix h).IsHermitian := by
  ext s t
  simp only [imaginaryKernelMatrix, conjTranspose_apply, Matrix.of_apply, map_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal]
  rw [hskew t s]
  push_cast
  ring

 theorem imaginaryKernelMatrix_square_entry (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) (s t : ι) :
    (imaginaryKernelMatrix h * imaginaryKernelMatrix h) s t =
      (if s = t then ((∑ r, h r s ^ 2 : ℝ) : ℂ) else 0) +
        (h s t : ℂ) * ((∑ r, k r s : ℝ) - ∑ r, k r t) +
          2 * (h s t : ℂ) * (k s t : ℂ) := by
  have he (r : ι) : imaginaryKernelMatrix h s r * imaginaryKernelMatrix h r t =
      ((h r s * h r t : ℝ) : ℂ) := by
    dsimp [imaginaryKernelMatrix]
    rw [hskew s r]
    push_cast
    calc
      _ = -(Complex.I * Complex.I) * ((h r s : ℂ) * (h r t : ℂ)) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [Matrix.mul_apply]
  simp_rw [he]
  rw [← Complex.ofReal_sum, skew_kernel_square_entry h k hdiag kdiag kskew htriple]
  push_cast
  by_cases hst : s = t <;> simp [hst]

 theorem imaginaryKernelMatrix_square (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t)) :
    let A : Matrix ι ι ℂ := imaginaryKernelMatrix h
    let D : Matrix ι ι ℂ := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
    A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
      (Complex.I • (D * A - A * D) : Matrix ι ι ℂ) +
        (2 : ℂ) • Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ)) := by
  dsimp only
  ext s t
  rw [imaginaryKernelMatrix_square_entry h k hdiag kdiag hskew kskew htriple]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    imaginaryKernelMatrix, Matrix.of_apply]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Complex.ofReal_mul,
    ]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Ostmann

end OAI

-- Upstream module SymmetricQuadraticBound
namespace OAI

/-! # The finite quadratic bound for the cosecant row estimate -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem real_symmetric_quadratic_upper (v : ι → ι → ℝ)
    (hv : ∀ s t, v s t = v t s) (u : ι → ℂ) :
    ‖star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u)‖ ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
  have he : star u ⬝ᵥ ((fun s t => (v s t : ℂ)) *ᵥ u) =
      ∑ s, ∑ t, star (u s) * (v s t : ℂ) * u t := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, mul_assoc]
  have hswap : (∑ s, ∑ t, |v s t| * ‖u t‖ ^ 2) =
      ∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [hv t s]
  have hfactor : (∑ s, ∑ t, |v s t| * ‖u s‖ ^ 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← Finset.sum_mul, mul_comm]
  have havg : (∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2) =
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |v s t| := by
    simp_rw [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
    rw [hswap]
    rw [hfactor]
    ring
  rw [he]
  calc
    _ ≤ ∑ s, ‖∑ t, star (u s) * (v s t : ℂ) * u t‖ := norm_sum_le _ _
    _ ≤ ∑ s, ∑ t, ‖star (u s) * (v s t : ℂ) * u t‖ :=
      Finset.sum_le_sum (fun s _ => norm_sum_le _ _)
    _ = ∑ s, ∑ t, |v s t| * ‖u s‖ * ‖u t‖ := by
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ ≤ ∑ s, ∑ t, |v s t| * (‖u s‖ ^ 2 + ‖u t‖ ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro s _
      apply Finset.sum_le_sum
      intro t _
      have hh := mul_le_mul_of_nonneg_left (sq_nonneg (‖u s‖ - ‖u t‖)) (abs_nonneg (v s t))
      nlinarith
    _ = _ := havg

end Ostmann

end OAI

-- Upstream module KernelEigenvalueBound
namespace OAI

/-! # Schur's eigenvalue bound for the concrete finite kernel identity -/

namespace Ostmann

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complex_diagonal_quadratic (d : ι → ℝ) (u : ι → ℂ) :
    star u ⬝ᵥ ((Matrix.diagonal (fun s => (d s : ℂ))) *ᵥ u) =
      ((∑ s, d s * ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.ofReal_sum,
    Complex.ofReal_mul, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  rw [show star (u s) * ((d s : ℂ) * u s) = (d s : ℂ) * (star (u s) * u s) by ring,
    Complex.star_def, Complex.conj_mul']

omit [DecidableEq ι] in
 theorem complex_self_quadratic (u : ι → ℂ) :
    star u ⬝ᵥ u = ((∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [Complex.star_def] using Complex.conj_mul' (u s)

 theorem kernel_eigenvalue_bound (h k : ι → ι → ℝ)
    (hdiag : ∀ i, h i i = 0) (kdiag : ∀ i, k i i = 0)
    (hskew : ∀ i j, h i j = -h j i) (kskew : ∀ i j, k i j = -k j i)
    (htriple : ∀ r s t, r ≠ s → r ≠ t → s ≠ t →
      h r s * h r t = h s t * (k r s - k r t))
    (B μ : ℝ) (hrow : ∀ s, (∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r| ≤ B)
    (u : ι → ℂ) (hu : 0 < ∑ s, ‖u s‖ ^ 2)
    (heig : imaginaryKernelMatrix h *ᵥ u = (μ : ℂ) • u) : μ ^ 2 ≤ B := by
  let A := imaginaryKernelMatrix h
  let D := Matrix.diagonal (fun s => ((∑ r, k r s : ℝ) : ℂ))
  let V : Matrix ι ι ℂ := Matrix.of (fun s t => ((h s t * k s t : ℝ) : ℂ))
  have hA : A.IsHermitian := imaginaryKernelMatrix_hermitian h hskew
  have hcomm := hermitian_eigenvector_commutator hA D u μ heig
  have hsq : star u ⬝ᵥ ((A * A) *ᵥ u) =
      ((μ ^ 2 * ∑ s, ‖u s‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mulVec_mulVec, heig, mulVec_smul, heig, smul_smul, dotProduct_smul,
      complex_self_quadratic]
    push_cast
    simp only [smul_eq_mul, pow_two]
  have hidentity := imaginaryKernelMatrix_square h k hdiag kdiag hskew kskew htriple
  change A * A = Matrix.diagonal (fun s => ((∑ r, h r s ^ 2 : ℝ) : ℂ)) -
    Complex.I • (D * A - A * D) + (2 : ℂ) • V at hidentity
  rw [hidentity, add_mulVec, sub_mulVec, smul_mulVec, dotProduct_add, dotProduct_sub,
    dotProduct_smul, hcomm, smul_zero, sub_zero, smul_mulVec, dotProduct_smul,
    complex_diagonal_quadratic] at hsq
  have hreal := congrArg Complex.re hsq
  have htwo (z : ℂ) : ((2 : ℂ) • z).re = 2 * z.re := by simp [smul_eq_mul, Complex.mul_re]
  simp only [Complex.add_re, Complex.ofReal_re, htwo] at hreal
  have hsym : ∀ s t, h s t * k s t = h t s * k t s := by
    intro s t
    rw [hskew s t, kskew s t]
    ring
  have hv := real_symmetric_quadratic_upper (fun s t => h s t * k s t) hsym u
  have hvr : (star u ⬝ᵥ (V *ᵥ u)).re ≤
      ∑ s, ‖u s‖ ^ 2 * ∑ t, |h s t * k s t| :=
    (Complex.re_le_norm _).trans hv
  have hsum : (∑ s, (∑ r, h r s ^ 2) * ‖u s‖ ^ 2) +
      2 * (∑ s, ‖u s‖ ^ 2 * ∑ r, |h s r * k s r|) ≤
        B * ∑ s, ‖u s‖ ^ 2 := by
    calc
      _ = ∑ s, ‖u s‖ ^ 2 * ((∑ r, h r s ^ 2) + 2 * ∑ r, |h s r * k s r|) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        · apply Finset.sum_congr rfl
          intro s _
          ring
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
      _ ≤ ∑ s, ‖u s‖ ^ 2 * B := Finset.sum_le_sum (fun s _ =>
        mul_le_mul_of_nonneg_left (hrow s) (sq_nonneg _))
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have hfinal : μ ^ 2 * (∑ s, ‖u s‖ ^ 2) ≤ B * (∑ s, ‖u s‖ ^ 2) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ hu).mp hfinal

end Ostmann

end OAI

-- Upstream module HermitianNormBound
namespace OAI

/-! # Passing a finite Hermitian eigenvalue bound to its quadratic form -/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem hermitian_norm_bound {A : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (B : ℝ) (hB : 0 ≤ B) (heig : ∀ i, |hA.eigenvalues i| ≤ B) : ‖A‖ ≤ B := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  simpa only [Function.comp_apply, RCLike.ofReal_eq_complex_ofReal, Complex.norm_real,
    Real.norm_eq_abs] using heig i

 theorem matrix_quadratic_norm_bound (A : Matrix ι ι ℂ) (B : ℝ)
    (hB : ‖A‖ ≤ B) (u : ι → ℂ) :
    ‖star u ⬝ᵥ (A *ᵥ u)‖ ≤ B * ∑ i, ‖u i‖ ^ 2 := by
  let v : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let w : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm (A *ᵥ u)
  have hinner : inner ℂ v w = star u ⬝ᵥ (A *ᵥ u) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hv : ‖v‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := EuclideanSpace.norm_sq_eq v
  have hw : ‖w‖ ≤ B * ‖v‖ := (Matrix.l2_opNorm_mulVec A v).trans
    (mul_le_mul_of_nonneg_right hB (norm_nonneg v))
  rw [← hinner]
  calc
    _ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (B * ‖v‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg v)
    _ = B * ∑ i, ‖u i‖ ^ 2 := by rw [← hv]; ring

end Ostmann

end OAI

-- Upstream module CosecantHilbertBound
namespace OAI

/-! # Montgomery--Vaughan's finite unweighted Hilbert inequality

This is Theorem 1, inequality (1.2), of Montgomery--Vaughan (1974).
It is derived from the checked finite kernel cancellation and row estimate.
-/

namespace Ostmann

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def cosecantMatrix (x : ι → ℝ) : Matrix ι ι ℂ :=
  imaginaryKernelMatrix (fun s t => cosecantKernel (x s) (x t))

omit [Fintype ι] [DecidableEq ι] in
 theorem cosecantMatrix_hermitian (x : ι → ℝ) : (cosecantMatrix x).IsHermitian :=
  imaginaryKernelMatrix_hermitian _ (fun _ _ => cosecantKernel_skew _ _)

 theorem cosecant_eigenvalue_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (μ : ℝ) (u : ι → ℂ)
    (hu : 0 < ∑ s, ‖u s‖ ^ 2) (heig : cosecantMatrix x *ᵥ u = (μ : ℂ) • u) :
    μ ^ 2 ≤ 1 / δ ^ 2 := by
  exact kernel_eigenvalue_bound
    (fun s t => cosecantKernel (x s) (x t))
    (fun s t => cotangentKernel (x s) (x t))
    (fun _ => cosecantKernel_self _) (fun _ => cotangentKernel_self _)
    (fun _ _ => cosecantKernel_skew _ _) (fun _ _ => cotangentKernel_skew _ _)
    (fun r s t hrs hrt hst => cosecantKernel_triple _ _ _
      (circleSeparated_sine_ne_zero x δ hδ hx hrs)
      (circleSeparated_sine_ne_zero x δ hδ hx hrt)
      (circleSeparated_sine_ne_zero x δ hδ hx hst))
    (1 / δ ^ 2) μ (cosecant_row_sum_bound x δ hδ hx) u hu heig

 theorem cosecantMatrix_norm_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) : ‖cosecantMatrix x‖ ≤ 1 / δ := by
  apply hermitian_norm_bound (cosecantMatrix_hermitian x) (1 / δ) (by positivity)
  intro i
  let hA := cosecantMatrix_hermitian x
  have hnorm : ‖hA.eigenvectorBasis i‖ = 1 := hA.eigenvectorBasis.orthonormal.1 i
  have hu : 0 < ∑ s, ‖(hA.eigenvectorBasis i) s‖ ^ 2 := by
    rw [← EuclideanSpace.norm_sq_eq, hnorm]
    norm_num
  have hb := cosecant_eigenvalue_bound x δ hδ hx (hA.eigenvalues i)
    (hA.eigenvectorBasis i) hu (hA.mulVec_eigenvectorBasis i)
  have hinv : 0 < 1 / δ := by positivity
  have heq : 1 / δ ^ 2 = (1 / δ) ^ 2 := by ring
  rw [heq] at hb
  nlinarith [sq_abs (hA.eigenvalues i), abs_nonneg (hA.eigenvalues i)]

 theorem cosecant_hilbert_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (u : ι → ℂ) :
    ‖∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t‖ ≤
      (1 / δ) * ∑ s, ‖u s‖ ^ 2 := by
  have hb := matrix_quadratic_norm_bound (cosecantMatrix x) (1 / δ)
    (cosecantMatrix_norm_bound x δ hδ hx) u
  have he : star u ⬝ᵥ (cosecantMatrix x *ᵥ u) =
      Complex.I * (∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t) := by
    simp only [dotProduct, mulVec, Pi.star_apply, cosecantMatrix, imaginaryKernelMatrix,
      Matrix.of_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [he, norm_mul, Complex.norm_I, one_mul] at hb
  exact hb

end Ostmann

end OAI

-- Upstream module SievePhaseGram
namespace OAI

/-! # The exact finite Gram expansion of the large-sieve phase matrix -/

namespace Ostmann

open scoped BigOperators

 theorem sieveHalfPhase_star (t : ℝ) : star (sieveHalfPhase t) = sieveHalfPhase (-t) := by
  unfold sieveHalfPhase
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [mul_neg, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg,
    star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

 theorem sieveHalfPhase_difference (s t : ℝ) :
    sieveHalfPhase s * star (sieveHalfPhase t) = sieveHalfPhase (s - t) := by
  rw [sieveHalfPhase_star, ← sieveHalfPhase_add, sub_eq_add_neg]

 theorem finite_complex_norm_expansion {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ((‖∑ s, f s‖ ^ 2 : ℝ) : ℂ) = ∑ s, ∑ t, f s * star (f t) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [← Complex.star_def, star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

 theorem sieve_phase_gram {ι : Type*} [Fintype ι] (x : ι → ℝ) (b : ι → ℂ)
    (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ∑ s, ∑ t, b s * star (b t) *
        ∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t)) := by
  simp only [Complex.ofReal_sum, finite_complex_norm_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [star_mul]
  rw [show 2 * (J + (n : ℝ)) * (x s - x t) =
    2 * (J + (n : ℝ)) * x s - 2 * (J + (n : ℝ)) * x t by ring,
    ← sieveHalfPhase_difference]
  ring

 theorem twisted_cosecant_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (b : ι → ℂ) (L : ℝ) :
    ‖∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)‖ ≤ (1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  let u := fun s => star (b s * sieveHalfPhase (L * x s))
  have he : (∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
      (cosecantKernel (x s) (x t) : ℂ)) =
      ∑ s, ∑ t, star (u s) * (cosecantKernel (x s) (x t) : ℂ) * u t := by
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    simp only [u, star_star, star_mul]
    rw [show L * (x s - x t) = L * x s - L * x t by ring,
      ← sieveHalfPhase_difference]
    ring
  rw [he]
  have hb := cosecant_hilbert_bound x δ hδ hx u
  simpa only [u, norm_star, norm_mul, sieveHalfPhase_norm, mul_one] using hb

end Ostmann

end OAI

-- Upstream module SieveDualEnergy
namespace OAI

/-! # The sharp dual large-sieve estimate from the finite Hilbert inequality -/

namespace Ostmann

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def twistedCosecantSum (x : ι → ℝ) (b : ι → ℂ) (L : ℝ) : ℂ :=
  ∑ s, ∑ t, b s * star (b t) * sieveHalfPhase (L * (x s - x t)) *
    (cosecantKernel (x s) (x t) : ℂ)

omit [Fintype ι] in
 theorem sieve_pair_kernel (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (s t : ι) :
    (∑ n ∈ Finset.range M, sieveHalfPhase (2 * (J + (n : ℝ)) * (x s - x t))) =
      (if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ) := by
  by_cases hst : s = t
  · subst t
    simp
  · rw [ite_eq_right hst, zero_add]
    simpa only [cosecantKernel, Complex.ofReal_inv] using
      sieve_geometric_kernel M J (x s - x t) (circleSeparated_sine_ne_zero x δ hδ hx hst)

 theorem sieve_dual_energy_identity (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    ((∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 : ℝ) : ℂ) =
      ((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)) := by
  rw [sieve_phase_gram]
  simp_rw [sieve_pair_kernel x δ hδ hx M J]
  have he (s t : ι) : b s * star (b t) *
      ((if s = t then (M : ℂ) else 0) +
        ((sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) -
          sieveHalfPhase ((2 * J - 1) * (x s - x t))) / ((2 : ℂ) * Complex.I)) *
          (cosecantKernel (x s) (x t) : ℂ)) =
      (if s = t then (M : ℂ) * ((‖b s‖ ^ 2 : ℝ) : ℂ) else 0) +
        ((2 : ℂ) * Complex.I)⁻¹ *
          (b s * star (b t) * sieveHalfPhase ((2 * (J + M) - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ) -
            b s * star (b t) * sieveHalfPhase ((2 * J - 1) * (x s - x t)) *
              (cosecantKernel (x s) (x t) : ℂ)) := by
    by_cases hst : s = t
    · subst t
      simp only [↓reduceIte, sub_self, mul_zero, sieveHalfPhase_zero,
        cosecantKernel_self, Complex.ofReal_zero, mul_one, add_zero]
      rw [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def]
      ring
    · simp only [hst, ↓reduceIte, zero_add, div_eq_mul_inv]
      ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum,
    Complex.ofReal_sum, Complex.ofReal_natCast, Complex.ofReal_mul, twistedCosecantSum]

 theorem sieve_dual_energy_bound (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hx : CircleSeparated x δ) (b : ι → ℂ) (M : ℕ) (J : ℝ) :
    (∑ n ∈ Finset.range M, ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
  have hi := sieve_dual_energy_identity x δ hδ hx b M J
  have htop := twisted_cosecant_bound x δ hδ hx b (2 * (J + M) - 1)
  have hbottom := twisted_cosecant_bound x δ hδ hx b (2 * J - 1)
  change ‖twistedCosecantSum x b (2 * (J + M) - 1)‖ ≤ _ at htop
  change ‖twistedCosecantSum x b (2 * J - 1)‖ ≤ _ at hbottom
  have htri := norm_add_le (((M : ℝ) * ∑ s, ‖b s‖ ^ 2 : ℝ) : ℂ)
    (((2 : ℂ) * Complex.I)⁻¹ *
      (twistedCosecantSum x b (2 * (J + M) - 1) - twistedCosecantSum x b (2 * J - 1)))
  have hdiff := norm_sub_le (twistedCosecantSum x b (2 * (J + M) - 1))
    (twistedCosecantSum x b (2 * J - 1))
  rw [← hi] at htri
  have hE : 0 ≤ ∑ s, ‖b s‖ ^ 2 := Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hN : 0 ≤ ∑ n ∈ Finset.range M,
      ‖∑ s, b s * sieveHalfPhase (2 * (J + (n : ℝ)) * x s)‖ ^ 2 :=
    Finset.sum_nonneg (fun n _ => sq_nonneg _)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hN,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg M) hE),
    norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_I] at htri
  norm_num at htri
  nlinarith

end Ostmann

end OAI

-- Upstream module FiniteMatrixDuality
namespace OAI

/-! # Finite Hilbert-space duality for the large-sieve phase matrix -/

namespace Ostmann

open Matrix
open scoped BigOperators

 theorem finite_complex_cauchy_schwarz {ι : Type*} [Fintype ι] (u v : ι → ℂ) :
    ‖star u ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  let U : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm u
  let V : EuclideanSpace ℂ ι := (EuclideanSpace.equiv ι ℂ).symm v
  have hi : inner ℂ U V = star u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    exact dotProduct_comm _ _
  have hh := pow_le_pow_left₀ (norm_nonneg (inner ℂ U V)) (norm_inner_le_norm U V) 2
  rw [hi, mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hh
  exact hh

 theorem finite_matrix_duality {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : Matrix ι κ ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hdual : ∀ b : ι → ℂ, (∑ j, ‖(Fᴴ *ᵥ b) j‖ ^ 2) ≤ K * ∑ i, ‖b i‖ ^ 2)
    (c : κ → ℂ) :
    (∑ i, ‖(F *ᵥ c) i‖ ^ 2) ≤ K * ∑ j, ‖c j‖ ^ 2 := by
  let b := F *ᵥ c
  have hE : 0 ≤ ∑ i, ‖b i‖ ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hC : 0 ≤ ∑ j, ‖c j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  by_cases hzero : (∑ i, ‖b i‖ ^ 2) = 0
  · change (∑ i, ‖b i‖ ^ 2) ≤ _
    rw [hzero]
    exact mul_nonneg hK hC
  have hEpos : 0 < ∑ i, ‖b i‖ ^ 2 := lt_of_le_of_ne hE (Ne.symm hzero)
  have hid : star (Fᴴ *ᵥ b) ⬝ᵥ c = star b ⬝ᵥ b := by
    rw [star_mulVec, conjTranspose_conjTranspose, ← dotProduct_mulVec]
  have hcauchy := finite_complex_cauchy_schwarz (Fᴴ *ᵥ b) c
  rw [hid, complex_self_quadratic, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hE] at hcauchy
  have hmul := mul_le_mul_of_nonneg_right (hdual b) hC
  change (∑ i, ‖b i‖ ^ 2) ≤ _
  have hh : (∑ i, ‖b i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) ≤
      (K * ∑ j, ‖c j‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by nlinarith
  exact (mul_le_mul_iff_left₀ hEpos).mp hh

end Ostmann

end OAI

-- Upstream module SeparatedAdditiveSieve
namespace OAI

/-! # The finite additive sieve for circle-separated frequencies -/

namespace Ostmann

open Matrix
open scoped BigOperators

noncomputable def sievePhaseMatrix {ι : Type*} (x : ι → ℝ) (M : ℕ) (J : ℝ) :
    Matrix ι (Fin M) ℂ :=
  Matrix.of (fun s n => sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s))

 theorem sievePhaseMatrix_adjoint {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (M : ℕ) (J : ℝ) (b : ι → ℂ) (n : Fin M) :
    ((sievePhaseMatrix x M J)ᴴ *ᵥ b) n =
      star (∑ s, star (b s) * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)) := by
  simp only [mulVec, dotProduct, conjTranspose_apply, sievePhaseMatrix, Matrix.of_apply,
    star_sum, star_mul, star_star]

 theorem separated_additive_sieve {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (δ : ℝ) (hδ : 0 < δ) (hx : CircleSeparated x δ)
    (M : ℕ) (J : ℝ) (c : Fin M → ℂ) :
    (∑ s, ‖∑ n, c n * sieveHalfPhase (2 * (J + (n.val : ℝ)) * x s)‖ ^ 2) ≤
      ((M : ℝ) + 1 / δ) * ∑ n, ‖c n‖ ^ 2 := by
  have hdual (b : ι → ℂ) :
      (∑ n, ‖((sievePhaseMatrix x M J)ᴴ *ᵥ b) n‖ ^ 2) ≤
        ((M : ℝ) + 1 / δ) * ∑ s, ‖b s‖ ^ 2 := by
    simp only [sievePhaseMatrix_adjoint, norm_star]
    have hb := sieve_dual_energy_bound x δ hδ hx (fun s => star (b s)) M J
    rw [← Fin.sum_univ_eq_sum_range] at hb
    simpa only [norm_star] using hb
  have hK : 0 ≤ (M : ℝ) + 1 / δ := by positivity
  have h := finite_matrix_duality (sievePhaseMatrix x M J) ((M : ℝ) + 1 / δ) hK hdual c
  simpa only [mulVec, dotProduct, sievePhaseMatrix, Matrix.of_apply, mul_comm] using h

end Ostmann

end OAI


end GoldbachBDHSharp

namespace GoldbachBDHSharp

namespace OAI

namespace Ostmann

open scoped BigOperators

theorem phase_exp_two (n : ℕ) (t : ℝ) :
    sieveHalfPhase (2 * ((n : ℝ)) * t)
      = Complex.exp (((2 * Real.pi * ((n : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
  unfold sieveHalfPhase
  congr 1
  push_cast
  ring

theorem phase_exp_two_zero (n : ℕ) (t : ℝ) :
    sieveHalfPhase (2 * ((0 : ℝ) + (n : ℝ)) * t)
      = Complex.exp (((2 * Real.pi * ((n : ℝ) * t) : ℝ) : ℂ) * Complex.I) := by
  rw [zero_add, phase_exp_two]

theorem sum_fin_eq_sum_range {A : Type*} [AddCommMonoid A] (n : ℕ) (g : ℕ → A) :
    (∑ i : Fin n, g i.val) = ∑ k ∈ Finset.range n, g k := by
  exact Fin.sum_univ_eq_sum_range _ _

theorem sample_sq_le_card {N : ℕ} (a : ℕ → ℂ) (t : ℝ) :
    ‖∑ k ∈ Finset.range (N + 1),
        a k * Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ ^ 2
      ≤ ((N + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := by
  have h1 : ‖∑ k ∈ Finset.range (N + 1),
      a k * Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ k ∈ Finset.range (N + 1), ‖a k‖ := by
    calc _ ≤ ∑ k ∈ Finset.range (N + 1),
          ‖a k * Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I)‖ :=
        norm_sum_le _ _
      _ = ∑ k ∈ Finset.range (N + 1), ‖a k‖ := by
          apply Finset.sum_congr rfl
          intro k _
          rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h3 : (∑ k ∈ Finset.range (N + 1), ‖a k‖) ^ 2
      ≤ ((N + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := by
    have h4 := sq_sum_le_card_mul_sum_sq (s := Finset.range (N + 1)) (f := fun k => ‖a k‖)
    simpa using h4
  calc _ ≤ (∑ k ∈ Finset.range (N + 1), ‖a k‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h3

theorem sieve_application {M N : ℕ} (x : Fin M → ℝ) (δ : ℝ) (a : ℕ → ℂ)
    (hδ : 0 < δ) (hx : CircleSeparated x δ) :
    (∑ i : Fin M, ‖∑ k ∈ Finset.range (N + 1),
        a k * Complex.exp (((2 * Real.pi * ((k : ℝ) * x i) : ℝ) : ℂ) * Complex.I)‖ ^ 2)
      ≤ (((N + 1 : ℕ) : ℝ) + 1 / δ) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := by
  have h := separated_additive_sieve x δ hδ hx (N + 1) 0 (fun n : Fin (N + 1) => a n.val)
  have hstep : ∀ s : Fin M,
      (∑ n : Fin (N + 1), a n.val * sieveHalfPhase (2 * ((0 : ℝ) + (n.val : ℝ)) * x s))
        = ∑ k ∈ Finset.range (N + 1),
            a k * Complex.exp (((2 * Real.pi * ((k : ℝ) * x s) : ℝ) : ℂ) * Complex.I) := by
    intro s
    rw [← sum_fin_eq_sum_range (N + 1)
      (fun k => a k * Complex.exp (((2 * Real.pi * ((k : ℝ) * x s) : ℝ) : ℂ) * Complex.I))]
    apply Finset.sum_congr rfl
    intro n _
    rw [phase_exp_two_zero]
  calc (∑ i : Fin M, ‖∑ k ∈ Finset.range (N + 1),
        a k * Complex.exp (((2 * Real.pi * ((k : ℝ) * x i) : ℝ) : ℂ) * Complex.I)‖ ^ 2)
      = ∑ s : Fin M, ‖∑ n : Fin (N + 1),
          a n.val * sieveHalfPhase (2 * ((0 : ℝ) + (n.val : ℝ)) * x s)‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro s _
        rw [hstep s]
    _ ≤ (((N + 1 : ℕ) : ℝ) + 1 / δ) * ∑ n : Fin (N + 1), ‖a n.val‖ ^ 2 := h
    _ = (((N + 1 : ℕ) : ℝ) + 1 / δ) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := by
        congr 1
        exact sum_fin_eq_sum_range (N + 1) (fun k => ‖a k‖ ^ 2)

end Ostmann

end OAI

end GoldbachBDHSharp

end

end Conjectures.Goldbach.SelbergSharpLargeSieve_aux

open Conjectures.Goldbach.SelbergSharpLargeSieve_aux.GoldbachBDHSharp.OAI.Ostmann

theorem Conjectures.Goldbach.SelbergSharpLargeSieve :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I);
    ∀ (M N : ℕ) (x : Fin M → ℝ) (δ : ℝ) (a : ℕ → ℂ), 0 < δ →
      (∀ i j : Fin M, i ≠ j → δ ≤ |x i - x j - ((round (x i - x j) : ℤ) : ℝ)|) →
      (∑ i : Fin M, ‖∑ k ∈ Finset.range (N + 1), a k * E ((k : ℝ) * x i)‖ ^ 2) ≤
        ((N : ℝ) + max 1 (2 / δ)) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := by
  have key : ∀ (M N : ℕ) (x : Fin M → ℝ) (δ : ℝ) (a : ℕ → ℂ), 0 < δ →
      (∀ i j : Fin M, i ≠ j → δ ≤ |x i - x j - ((round (x i - x j) : ℤ) : ℝ)|) →
      (∑ i : Fin M, ‖∑ k ∈ Finset.range (N + 1),
          a k * Complex.exp (((2 * Real.pi * ((k : ℝ) * x i) : ℝ) : ℂ) * Complex.I)‖ ^ 2) ≤
        ((N : ℝ) + max 1 (2 / δ)) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := by
    intro M N x δ a hδ hsep
    classical
    have hnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    by_cases hδ1 : δ ≤ 1
    · have hcs : CircleSeparated x δ := by
        intro s t hst m
        have h1 : δ ≤ |x s - x t - ((round (x s - x t) : ℤ) : ℝ)| := hsep s t hst
        have h2 : |x s - x t - ((round (x s - x t) : ℤ) : ℝ)| ≤ |x s - x t - (m : ℝ)| :=
          round_le (x s - x t) m
        linarith
      have h := sieve_application (N := N) x δ a hδ hcs
      have hmax : max 1 (2 / δ) = 2 / δ := by
        apply max_eq_right
        rw [le_div_iff₀ hδ]
        linarith
      have hinv : (1 : ℝ) ≤ 1 / δ := by
        rw [le_div_iff₀ hδ]
        linarith
      calc _ ≤ (((N + 1 : ℕ) : ℝ) + 1 / δ) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := h
        _ ≤ ((N : ℝ) + max 1 (2 / δ)) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := by
            rw [hmax]
            apply mul_le_mul_of_nonneg_right _ hnn
            have htwo : (2 : ℝ) / δ = 1 / δ + 1 / δ := by ring
            rw [htwo]
            push_cast
            linarith
    · have hM : M ≤ 1 := by
        by_contra hM2
        push_neg at hM2
        obtain ⟨i, hi⟩ : ∃ i : Fin M, i.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
        obtain ⟨j, hj⟩ : ∃ j : Fin M, j.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
        have hij : i ≠ j := by
          intro hcon
          have hbad := congrArg Fin.val hcon
          omega
        have ha : |x i - x j - ((round (x i - x j) : ℤ) : ℝ)| ≤ 1 / 2 := abs_sub_round (x i - x j)
        have hb : δ ≤ |x i - x j - ((round (x i - x j) : ℤ) : ℝ)| := hsep i j hij
        linarith
      have hconst : ∀ c : ℝ, (∑ _i : Fin M, c) = (M : ℝ) * c := by
        intro c
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hpoint : ∀ i : Fin M, ‖∑ k ∈ Finset.range (N + 1),
          a k * Complex.exp (((2 * Real.pi * ((k : ℝ) * x i) : ℝ) : ℂ) * Complex.I)‖ ^ 2
          ≤ ((N + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := by
        intro i
        exact sample_sq_le_card a (x i)
      have hkey : (M : ℝ) * ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) + max 1 (2 / δ) := by
        have hM' : (M : ℝ) ≤ 1 := by exact_mod_cast hM
        have h1 : (1 : ℝ) ≤ max 1 (2 / δ) := le_max_left _ _
        have h2 : (M : ℝ) * ((N + 1 : ℕ) : ℝ) ≤ 1 * ((N + 1 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right hM' (by positivity)
        push_cast at h2
        push_cast
        linarith
      calc _ ≤ ∑ i : Fin M, ((N + 1 : ℕ) : ℝ) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 :=
            Finset.sum_le_sum (fun i _ => hpoint i)
        _ = ((M : ℝ) * ((N + 1 : ℕ) : ℝ)) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 := by
            rw [hconst]
            ring
        _ ≤ ((N : ℝ) + max 1 (2 / δ)) * ∑ k ∈ Finset.range (N + 1), ‖a k‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hkey hnn
  exact key


/-!
Montgomery--Vaughan multiplicative large sieve.

Credit: the Dirichlet-character orthogonality, Gauss-sum inversion and character Parseval
machinery below is adapted from the accepted module
`Conjectures.Goldbach.B13BilateralVaughanReduction` (namespace `BombieriVinogradov.LargeSieve`);
the additive (Farey) large sieve with the sharp constant `π N + Q²` is used through the accepted
module `Conjectures.Goldbach.AnalyticLargeSieve`.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace Conjectures.Goldbach.MultiplicativeLargeSieve_aux

open Conjectures.Goldbach.AnalyticLargeSieve_aux

noncomputable section

noncomputable local instance unitFintype (n : ℕ) : Fintype (ZMod n)ˣ := Fintype.ofFinite _

/-- The finite set of primitive complex Dirichlet characters of level `n`. -/
def primChars (n : ℕ) : Finset (DirichletCharacter ℂ n) := by
  classical
  exact Finset.univ.filter DirichletCharacter.IsPrimitive

/-- The interval character sum `S(χ) = ∑_{M ≤ k < M+N} c k χ(k)`. -/
def charSum (c : ℕ → ℂ) (M N n : ℕ) (χ : DirichletCharacter ℂ n) : ℂ :=
  ∑ k ∈ Ico M (M + N), c k * χ (k : ZMod n)

/-- The additive interval sum at the reduced residue `u` modulo `n`. -/
def addSum (c : ℕ → ℂ) (M N n : ℕ) [NeZero n] (u : (ZMod n)ˣ) : ℂ :=
  ∑ k ∈ Ico M (M + N), c k * ZMod.stdAddChar ((k : ZMod n) * (u : ZMod n))

/-- A character transform of a function on the unit group of `ZMod n`. -/
def unitCharSum {n : ℕ} (b : (ZMod n)ˣ → ℂ) (χ : DirichletCharacter ℂ n) : ℂ :=
  ∑ x : (ZMod n)ˣ, b x * χ (x : ZMod n)

/-- A nonnegative sum over primitive characters is bounded by the sum over all characters. -/
theorem primSum_le_all (n : ℕ) (f : DirichletCharacter ℂ n → ℝ) (hf : ∀ χ, 0 ≤ f χ) :
    ∑ χ ∈ primChars n, f χ ≤ ∑ χ : DirichletCharacter ℂ n, f χ := by
  classical
  exact Finset.sum_le_univ_sum_of_nonneg (s := primChars n) hf

/-- On units, complex conjugation of a character value is evaluation at the inverse. -/
theorem star_char_unit {n : ℕ} (χ : DirichletCharacter ℂ n) (x : (ZMod n)ˣ) :
    star (χ (x : ZMod n)) = χ ((x : ZMod n)⁻¹) := by
  rw [MulChar.star_apply']
  rw [MulChar.inv_apply_eq_inv']
  simp

/-- Orthogonality of all complex Dirichlet characters on the unit group. -/
theorem charOrthUnits {n : ℕ} [NeZero n] (x y : (ZMod n)ˣ) :
    (∑ χ : DirichletCharacter ℂ n, star (χ (x : ZMod n)) * χ (y : ZMod n)) =
      if x = y then (n.totient : ℂ) else 0 := by
  simp_rw [star_char_unit]
  simpa only [Units.val_inj] using
    (DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) x.isUnit (y : ZMod n))

/-- Finite Parseval identity for the Dirichlet-character transform on `(ZMod n)^*`. -/
theorem charParseval {n : ℕ} [NeZero n] (b : (ZMod n)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ n, star (unitCharSum b χ) * unitCharSum b χ) =
      (n.totient : ℂ) * ∑ x : (ZMod n)ˣ, star (b x) * b x := by
  classical
  unfold unitCharSum
  simp_rw [star_sum, star_mul, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, y]
    rw [Finset.sum_comm]
  have rearrange (χ : DirichletCharacter ℂ n) (x y : (ZMod n)ˣ) :
      star (χ (x : ZMod n)) * star (b x) * (b y * χ (y : ZMod n)) =
        (star (b x) * b y) * (star (χ (x : ZMod n)) * χ (y : ZMod n)) := by
    ring
  simp_rw [rearrange]
  simp_rw [← Finset.mul_sum]
  simp_rw [charOrthUnits]
  simp [mul_ite]
  rw [← Finset.sum_mul]
  ring

/-- Real norm-squared form of character Parseval. -/
theorem charParseval_normSq {n : ℕ} [NeZero n] (b : (ZMod n)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ n, ‖unitCharSum b χ‖ ^ 2) =
      (n.totient : ℝ) * ∑ x : (ZMod n)ˣ, ‖b x‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp_rw [← Complex.normSq_eq_norm_sq]
  push_cast
  simpa only [Complex.normSq_eq_conj_mul_self, RCLike.star_def] using (charParseval b)

/-- Discarding imprimitive characters gives the fixed-modulus primitive-character bound. -/
theorem primCharParseval_le {n : ℕ} [NeZero n] (b : (ZMod n)ˣ → ℂ) :
    ∑ χ ∈ primChars n, ‖unitCharSum b χ‖ ^ 2 ≤ (n.totient : ℝ) * ∑ x : (ZMod n)ˣ, ‖b x‖ ^ 2 := by
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ n, ‖unitCharSum b χ‖ ^ 2 :=
      primSum_le_all n _ (fun χ => sq_nonneg ‖unitCharSum b χ‖)
    _ = _ := charParseval_normSq b

/-- The Gauss sum of a primitive character has squared norm `n`. -/
theorem norm_gaussSum_sq {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (n : ℝ) := by
  rw [DirichletCharacter.norm_gaussSum_stdAddChar hχ, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- A Dirichlet-character-weighted sum over units equals the sum over all residues. -/
theorem sum_units_eq_sum_residues {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n)
    (f : ZMod n → ℂ) :
    ∑ u : (ZMod n)ˣ, χ (u : ZMod n) * f u = ∑ x : ZMod n, χ x * f x := by
  classical
  let s : Finset (ZMod n) := Finset.univ.filter IsUnit
  have hunits : (∑ u : (ZMod n)ˣ, χ (u : ZMod n) * f u) = ∑ x ∈ s, χ x * f x := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (ZMod n)ˣ)) (t := s)
      (fun u _ => (u : ZMod n))
    · intro u _
      simp [s, u.isUnit]
    · intro u _ v _ huv
      exact Units.ext huv
    · intro x hx
      have hxunit : IsUnit x := by simpa [s] using hx
      exact ⟨hxunit.unit, Finset.mem_univ _, hxunit.unit_spec⟩
    · intro u _
      rfl
  rw [hunits]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hxnot
  have hxnonunit : ¬IsUnit x := by simpa [s] using hxnot
  rw [MulChar.map_nonunit χ hxnonunit, zero_mul]

/-- Primitive Gauss-sum inversion on one residue. -/
theorem shift_eq_char_mul_gauss {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}
    (hχ : χ.IsPrimitive) (k : ℕ) :
    ∑ u : (ZMod n)ˣ, χ⁻¹ (u : ZMod n) * ZMod.stdAddChar ((k : ZMod n) * (u : ZMod n)) =
      χ (k : ZMod n) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχInv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  calc
    _ = ∑ x : ZMod n, χ⁻¹ x * ZMod.stdAddChar ((k : ZMod n) * x) :=
      sum_units_eq_sum_residues χ⁻¹ _
    _ = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (k : ZMod n)) := by
      simp only [gaussSum, AddChar.mulShift_apply]
    _ = _ := by
      simpa using (gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχInv (k : ZMod n))

/-- Primitive Gauss-sum inversion for the interval character sum. -/
theorem gauss_mul_charSum {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}
    (hχ : χ.IsPrimitive) (c : ℕ → ℂ) (M N : ℕ) :
    gaussSum χ⁻¹ ZMod.stdAddChar * charSum c M N n χ =
      unitCharSum (addSum c M N n) χ⁻¹ := by
  classical
  unfold charSum addSum unitCharSum
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    gaussSum χ⁻¹ ZMod.stdAddChar * (c k * χ (k : ZMod n)) =
        c k * (χ (k : ZMod n) * gaussSum χ⁻¹ ZMod.stdAddChar) := by ring
    _ = c k * ∑ u : (ZMod n)ˣ,
        χ⁻¹ (u : ZMod n) * ZMod.stdAddChar ((k : ZMod n) * (u : ZMod n)) := by
      rw [shift_eq_char_mul_gauss hχ k]
    _ = ∑ u : (ZMod n)ˣ,
        c k * (χ⁻¹ (u : ZMod n) * ZMod.stdAddChar ((k : ZMod n) * (u : ZMod n))) := by
      rw [Finset.mul_sum]
    _ = ∑ u : (ZMod n)ˣ,
        c k * ZMod.stdAddChar ((k : ZMod n) * (u : ZMod n)) * χ⁻¹ (u : ZMod n) := by
      apply Finset.sum_congr rfl
      intro u _
      ring

/-- Squared-norm form of primitive Gauss-sum inversion. -/
theorem n_mul_norm_charSum_sq {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}
    (hχ : χ.IsPrimitive) (c : ℕ → ℂ) (M N : ℕ) :
    (n : ℝ) * ‖charSum c M N n χ‖ ^ 2 =
      ‖unitCharSum (addSum c M N n) χ⁻¹‖ ^ 2 := by
  have hχInv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  calc
    (n : ℝ) * ‖charSum c M N n χ‖ ^ 2 =
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖charSum c M N n χ‖ ^ 2 := by
      rw [norm_gaussSum_sq hχInv]
    _ = ‖gaussSum χ⁻¹ ZMod.stdAddChar * charSum c M N n χ‖ ^ 2 := by
      rw [norm_mul]
      ring
    _ = _ := by
      rw [gauss_mul_charSum hχ c M N]

/-- Inversion permutes the finite set of primitive characters. -/
theorem sum_prim_inv (n : ℕ) (f : DirichletCharacter ℂ n → ℝ) :
    ∑ χ ∈ primChars n, f χ⁻¹ = ∑ χ ∈ primChars n, f χ := by
  classical
  apply Finset.sum_bij (s := primChars n) (t := primChars n) (fun χ _ => χ⁻¹)
  · intro χ hχ
    have hprimitive : χ.IsPrimitive := by simpa [primChars] using hχ
    have hinv : χ⁻¹.IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
      exact hprimitive
    simpa [primChars] using hinv
  · intro χ _ ψ _ heq
    simpa only [inv_inv] using congrArg Inv.inv heq
  · intro ψ hψ
    refine ⟨ψ⁻¹, ?_, ?_⟩
    · have hprimitive : ψ.IsPrimitive := by simpa [primChars] using hψ
      have hinv : ψ⁻¹.IsPrimitive := by
        rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
        exact hprimitive
      simpa [primChars] using hinv
    · simp
  · intro χ _
    rfl

/-- At a fixed positive modulus, the weight `n / φ(n)` cancels exactly against the Gauss norm
and character Parseval constants. -/
theorem weighted_le_addSum {n : ℕ} [NeZero n] (c : ℕ → ℂ) (M N : ℕ) :
    ((n : ℝ) / (n.totient : ℝ)) * ∑ χ ∈ primChars n, ‖charSum c M N n χ‖ ^ 2 ≤
      ∑ u : (ZMod n)ˣ, ‖addSum c M N n u‖ ^ 2 := by
  classical
  let b : (ZMod n)ˣ → ℂ := addSum c M N n
  let S : ℝ := ∑ χ ∈ primChars n, ‖charSum c M N n χ‖ ^ 2
  let E : ℝ := ∑ u : (ZMod n)ˣ, ‖b u‖ ^ 2
  have hscaled : (n : ℝ) * S =
      ∑ χ ∈ primChars n, ‖unitCharSum b χ⁻¹‖ ^ 2 := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    have hprimitive : χ.IsPrimitive := by simpa [primChars] using hχ
    exact n_mul_norm_charSum_sq hprimitive c M N
  have hinv :
      (∑ χ ∈ primChars n, ‖unitCharSum b χ⁻¹‖ ^ 2) =
        ∑ χ ∈ primChars n, ‖unitCharSum b χ‖ ^ 2 :=
    sum_prim_inv n (fun χ => ‖unitCharSum b χ‖ ^ 2)
  have hparseval :
      ∑ χ ∈ primChars n, ‖unitCharSum b χ‖ ^ 2 ≤ (n.totient : ℝ) * E := by
    simpa [E] using primCharParseval_le b
  have hcore : (n : ℝ) * S ≤ (n.totient : ℝ) * E := by
    rw [hscaled, hinv]
    exact hparseval
  have hphi : 0 < (n.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos n)
  change ((n : ℝ) / (n.totient : ℝ)) * S ≤ E
  calc
    ((n : ℝ) / (n.totient : ℝ)) * S = ((n : ℝ) * S) / (n.totient : ℝ) := by ring
    _ ≤ ((n.totient : ℝ) * E) / (n.totient : ℝ) :=
      (div_le_div_iff_of_pos_right hphi).2 hcore
    _ = E := by field_simp


/-- The standard additive character at a residue `k * a` is the real exponential phase at
the rational point `a / n`. -/
theorem stdAddChar_mul_eq_Ex (n a k : ℕ) [NeZero n] :
    ZMod.stdAddChar ((k : ZMod n) * (a : ZMod n)) = Ex ((k : ℝ) * ((a : ℝ) / (n : ℝ))) := by
  rw [show (k : ZMod n) * (a : ZMod n) = (((k * a : ℕ) : ℤ) : ZMod n) by push_cast; ring]
  rw [ZMod.stdAddChar_coe]
  unfold Ex
  congr 1
  push_cast
  field_simp

/-- The additive interval sum at a unit is the exponential sum at the reduced residue. -/
theorem addSum_eq_Ex (c : ℕ → ℂ) (M N n : ℕ) [NeZero n] (u : (ZMod n)ˣ) :
    addSum c M N n u =
      ∑ k ∈ Ico M (M + N), c k * Ex ((k : ℝ) * (((u.val.val : ℕ) : ℝ) / (n : ℝ))) := by
  unfold addSum
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hu : (k : ZMod n) * (u : ZMod n) = (k : ZMod n) * ((u.val.val : ℕ) : ZMod n) := by
    rw [ZMod.natCast_zmod_val]
  rw [hu, stdAddChar_mul_eq_Ex]

/-- Units of `ZMod n` are in bijection with the reduced residues `a < n`. -/
theorem sum_units_val (n : ℕ) [NeZero n] (f : ℕ → ℝ) :
    ∑ u : (ZMod n)ˣ, f u.val.val =
      ∑ a ∈ (range n).filter (fun a => Nat.Coprime a n), f a := by
  classical
  refine Finset.sum_bij (fun (u : (ZMod n)ˣ) _ => u.val.val) ?_ ?_ ?_ ?_
  · intro u _
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    rw [← ZMod.isUnit_iff_coprime]
    simpa only [ZMod.natCast_zmod_val] using u.isUnit
  · intro u _ v _ h
    exact Units.ext (ZMod.val_injective n h)
  · intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hunit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).mpr ha2
    refine ⟨hunit.unit, Finset.mem_univ _, ?_⟩
    have hval : ZMod.val (hunit.unit : ZMod n) = ZMod.val (a : ZMod n) := by
      rw [hunit.unit_spec]
    rw [hval, ZMod.val_natCast_of_lt (Finset.mem_range.mp ha1)]
  · intro u _
    rfl

/-- The fixed-modulus bound in the form used for the final summation. -/
theorem per_modulus (c : ℕ → ℂ) (M N n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) / (n.totient : ℝ)) * ∑ χ ∈ primChars n, ‖charSum c M N n χ‖ ^ 2 ≤
      ∑ a ∈ (range n).filter (fun a => Nat.Coprime a n),
        ‖∑ k ∈ Ico M (M + N), c k * Ex ((k : ℝ) * ((a : ℝ) / n))‖ ^ 2 := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  refine (weighted_le_addSum c M N).trans ?_
  rw [← sum_units_val n
    (fun a => ‖∑ k ∈ Ico M (M + N), c k * Ex ((k : ℝ) * ((a : ℝ) / n))‖ ^ 2)]
  refine Finset.sum_le_sum (fun u _ => ?_)
  rw [addSum_eq_Ex]


end
end Conjectures.Goldbach.MultiplicativeLargeSieve_aux


open Finset
open Conjectures.Goldbach.AnalyticLargeSieve_aux
open Conjectures.Goldbach.MultiplicativeLargeSieve_aux
open Conjectures.Goldbach.SelbergSharpLargeSieve_aux.GoldbachBDHSharp.OAI.Ostmann

namespace SharpMultiplicative

private lemma shift_sum {α : Type*} [AddCommMonoid α] (M L : ℕ) (f : ℕ → α) :
    ∑ i : Fin L, f (M + i.val) = ∑ k ∈ Ico M (M+L), f k := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (M+i)), Finset.sum_Ico_eq_sum_range]
  simp

private lemma circle_gap {δ x y : ℝ} (hx : 0 ≤ x ∧ x ≤ 1-δ)
    (hy : 0 ≤ y ∧ y ≤ 1-δ) (hxy : δ ≤ |x-y|) (m : ℤ) : δ ≤ |x-y-m| := by
  rcases lt_trichotomy m 0 with hm|hm|hm
  · have hh : (m:ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    exact (show δ ≤ x-y-m by linarith [hx.1,hy.2]).trans (le_abs_self _)
  · simpa [hm] using hxy
  · have hh : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    exact (show δ ≤ -(x-y-m) by linarith [hx.2,hy.1]).trans (neg_le_abs _)

theorem sharp (M L Q : ℕ) (c : ℕ → ℂ) (hQ : 1 ≤ Q) :
    (∑ q ∈ Icc 1 Q, ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
      ‖∑ k ∈ Ico M (M + L), c k * Ex ((k:ℝ) * ((a:ℝ)/q))‖ ^ 2) ≤
    ((L:ℝ)+(Q:ℝ)^2)*∑ k ∈ Ico M (M+L), ‖c k‖^2 := by
  classical
  let P := (Icc 1 Q).sigma (fun q => (range q).filter (fun a => Nat.Coprime a q))
  let x : P → ℝ := fun j => (j.val.2:ℝ)/j.val.1
  let δ : ℝ := 1/(Q:ℝ)^2
  have hQpos : (0:ℝ)<Q := by exact_mod_cast (show 0<Q by omega)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have sep : CircleSeparated x δ := by
    intro i j hn m
    obtain ⟨qi,ai⟩ := mem_sigma.mp i.property
    obtain ⟨qj,aj⟩ := mem_sigma.mp j.property
    obtain ⟨ilo,ihi⟩ := mem_Icc.mp qi
    obtain ⟨jlo,jhi⟩ := mem_Icc.mp qj
    obtain ⟨ir,ic⟩ := mem_filter.mp ai
    obtain ⟨jr,jc⟩ := mem_filter.mp aj
    have hij : i.val.1 ≠ j.val.1 ∨ i.val.2 ≠ j.val.2 := by
      by_contra! hh
      exact hn (Subtype.ext (Sigma.ext hh.1 (heq_of_eq hh.2)))
    exact circle_gap (frac_bounds Q _ _ hQ ilo ihi (mem_range.mp ir))
      (frac_bounds Q _ _ hQ jlo jhi (mem_range.mp jr))
      (frac_sep Q _ _ _ _ ilo jlo ihi jhi ic jc hij) m
  have H := separated_additive_sieve x δ hδ sep L (M:ℝ) (fun k => c (M+k.val))
  have hp (k : Fin L) (j : P) :
      sieveHalfPhase (2*((M:ℝ)+(k.val:ℝ))*x j) = Ex (((M+k.val:ℕ):ℝ)*x j) := by
    unfold sieveHalfPhase Ex
    push_cast
    congr 2
    ring
  simp_rw [hp] at H
  have hs (j : P) :
      (∑ i : Fin L, c (M+i.val) * Ex (((M+i.val:ℕ):ℝ)*x j)) =
        ∑ k ∈ Ico M (M+L), c k * Ex ((k:ℝ)*x j) :=
    shift_sum M L (fun k => c k * Ex ((k:ℝ)*x j))
  simp_rw [hs] at H
  rw [shift_sum M L (fun k => ‖c k‖^2)] at H
  have hd : 1/δ=(Q:ℝ)^2 := by simp [δ]
  rw [hd] at H
  rw [Finset.sum_sigma']
  let F := fun j : (Σ _q : ℕ, ℕ) => ‖∑ k ∈ Ico M (M+L), c k * Ex ((k:ℝ) * ((j.2:ℝ)/j.1))‖^2
  change (∑ j ∈ P, F j) ≤ _
  rw [← P.sum_coe_sort F]
  exact H

end SharpMultiplicative

theorem Conjectures.Goldbach.SharpMultiplicativeLargeSieve :
    letI := Classical.propDecidable
    ∀ (M L Q : ℕ) (a : ℕ → ℂ), ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (Nat.totient q : ℝ)) *
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
        ‖∑ n ∈ Finset.Ico M (M + L), a n * χ (n : ZMod q)‖ ^ 2 ≤
      ((L : ℝ) + (Q : ℝ)^2) * ∑ n ∈ Finset.Ico M (M + L), ‖a n‖^2 := by
  intro M L Q a
  classical
  by_cases hQ : 1 ≤ Q
  · exact (sum_le_sum (fun q hq => per_modulus a M L q (mem_Icc.mp hq).1)).trans
      (SharpMultiplicative.sharp M L Q a hQ)
  · have : Q=0 := by omega
    subst Q
    simp
    positivity

