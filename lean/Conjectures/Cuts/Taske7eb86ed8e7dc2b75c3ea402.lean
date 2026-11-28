import Mathlib

/-- 加性特征在 [0, 1] 上的正交性：频率相等时积分为 1，不等时积分为 0。 -/
private lemma integral_fourier_ortho (a b : ℕ) :
    (∫ t in (0 : ℝ)..(1 : ℝ),
      Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑a * ↑t) *
        Star.star (Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑b * ↑t))) =
    if a = b then (1 : ℂ) else 0 := by
  have hstar : ∀ t : ℝ,
      Star.star (Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑b * ↑t)) =
      Complex.exp (-((2 : ℂ) * ↑Real.pi * Complex.I * ↑b * ↑t)) := by
    intro t
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp [map_mul, map_ofNat, map_natCast, Complex.conj_ofReal, Complex.conj_I]
  have hcomb : ∀ t : ℝ,
      Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑a * ↑t) *
        Star.star (Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑b * ↑t)) =
      Complex.exp (((2 : ℂ) * ↑Real.pi * Complex.I * ((a : ℂ) - (b : ℂ))) * (t : ℂ)) := by
    intro t
    rw [hstar t, ← Complex.exp_add]
    congr 1
    ring
  simp_rw [hcomb]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [ite_eq_right (fun h => absurd h hab)]
    set c : ℂ := (2 : ℂ) * ↑Real.pi * Complex.I * ((a : ℂ) - (b : ℂ))
    have hc : c ≠ 0 := by
      have hab_c : (a : ℂ) - (b : ℂ) ≠ 0 := sub_ne_zero.mpr (Nat.cast_injective.ne hab)
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) hab_c
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)) / c)
          (Complex.exp (c * (t : ℂ))) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have h2 : HasDerivAt (fun x : ℝ => c * (x : ℂ)) (c * 1) t := h1.const_mul c
      rw [mul_one] at h2
      have h3 : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)))
          (Complex.exp (c * (t : ℂ)) * c) t := h2.cexp
      have h4 := h3.div_const c
      rwa [mul_div_cancel_right₀ _ hc] at h4
    have hint : IntervalIntegrable (fun x : ℝ => Complex.exp (c * (x : ℂ)))
        MeasureTheory.volume 0 1 :=
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    have hexp : Complex.exp c = 1 := by
      have hc_eq : c = (((a : ℤ) - (b : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [c, Int.cast_sub, Int.cast_natCast]
        push_cast
        ring
      rw [hc_eq]
      exact Complex.exp_int_mul_two_pi_mul_I ((a : ℤ) - (b : ℤ))
    simp [hexp, div_eq_mul_inv]

/-- 有限个区间可积复值函数之和在 [0, 1] 上区间可积。 -/
private lemma intervalIntegrable_finset_sum_aux {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume 0 1) :
    IntervalIntegrable (fun t => ∑ i ∈ s, f i t) MeasureTheory.volume 0 1 := by
  classical
  induction s using Finset.induction with
  | empty =>
    simpa using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) MeasureTheory.volume 0 1)
  | @insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- 有限个区间可积复值函数之和在 [0, 1] 上的积分等于逐项积分之和。 -/
private lemma integral_finset_sum_aux {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ s, IntervalIntegrable (f i) MeasureTheory.volume 0 1) :
    (∫ t in (0 : ℝ)..(1 : ℝ), ∑ i ∈ s, f i t) =
    ∑ i ∈ s, ∫ t in (0 : ℝ)..(1 : ℝ), f i t := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    have hfa : IntervalIntegrable (f a) MeasureTheory.volume 0 1 :=
      hf a (Finset.mem_insert_self a s)
    have hfs : IntervalIntegrable (fun t => ∑ i ∈ s, f i t) MeasureTheory.volume 0 1 :=
      intervalIntegrable_finset_sum_aux s f (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simp_rw [Finset.sum_insert ha]
    rw [intervalIntegral.integral_add hfa hfs, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem Conjectures.Cuts.Taske7eb86ed8e7dc2b75c3ea402 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑x1 * ↑x2); ∀ (x2 : Finset ℕ) (x3 x4 : ℕ) (x5 : Finset ℕ),   have x6 : Finset (Finset ℕ) := Finset.powersetCard x4 x2;   have x7 : Finset ℕ → ℕ := fun (x7 : Finset ℕ) => ∑ x8 ∈ x7, x3 ^ x8;   ↑{x8 ∈ x6 | x7 x8 ∈ x5}.card = (∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (∑ x9 ∈ x6, ∏ x10 ∈ x9, x1 (x3 ^ x10) x8) * Star.star (∑ x9 ∈ x5, x1 x9 x8)).re) := by
  dsimp only
  intro x2 x3 x4 x5
  let x1 : ℕ → ℝ → ℂ := fun n t => Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑n * ↑t)
  let x6 : Finset (Finset ℕ) := Finset.powersetCard x4 x2
  let x7 : Finset ℕ → ℕ := fun s => ∑ i ∈ s, x3 ^ i
  -- 将子集相位乘积合并为子集幂和对应的单个加性特征
  have hprod : ∀ (s : Finset ℕ) (t : ℝ), (∏ i ∈ s, x1 (x3 ^ i) t) = x1 (x7 s) t := by
    intro s t
    simp only [x1, x7, ← Complex.exp_sum]
    congr 1
    rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_mul]
  -- 展开被积函数为有限双和
  have hintegrand : ∀ t : ℝ,
      (∑ s ∈ x6, ∏ i ∈ s, x1 (x3 ^ i) t) * Star.star (∑ y ∈ x5, x1 y t) =
      ∑ s ∈ x6, ∑ y ∈ x5, x1 (x7 s) t * Star.star (x1 y t) := by
    intro t
    simp_rw [hprod]
    rw [star_sum, Finset.sum_mul_sum]
  -- 单项连续故区间可积
  have hint_term : ∀ (a b : ℕ),
      IntervalIntegrable (fun t : ℝ => x1 a t * Star.star (x1 b t)) MeasureTheory.volume 0 1 := by
    intro a b
    have hc1 : Continuous (fun t : ℝ => x1 a t) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    have hc2 : Continuous (fun t : ℝ => x1 b t) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    exact (hc1.mul hc2.star).intervalIntegrable 0 1
  -- 交换积分与有限双和，并逐项应用正交性
  have hint_eq :
      (∫ t in (0 : ℝ)..(1 : ℝ),
        (∑ s ∈ x6, ∏ i ∈ s, x1 (x3 ^ i) t) * Star.star (∑ y ∈ x5, x1 y t)) =
      (({s ∈ x6 | x7 s ∈ x5}.card : ℕ) : ℂ) := by
    simp_rw [hintegrand]
    rw [integral_finset_sum_aux x6 _ (fun s _ =>
      intervalIntegrable_finset_sum_aux x5 _ (fun y _ => hint_term (x7 s) y))]
    have hinner : ∀ s ∈ x6,
        (∫ t in (0 : ℝ)..(1 : ℝ), ∑ y ∈ x5, x1 (x7 s) t * Star.star (x1 y t)) =
        if x7 s ∈ x5 then (1 : ℂ) else 0 := by
      intro s _
      rw [integral_finset_sum_aux x5 _ (fun y _ => hint_term (x7 s) y)]
      have hortho : ∀ y : ℕ,
          (∫ t in (0 : ℝ)..(1 : ℝ), x1 (x7 s) t * Star.star (x1 y t)) =
          if x7 s = y then (1 : ℂ) else 0 := fun y => integral_fourier_ortho (x7 s) y
      simp_rw [hortho]
      simp [Finset.sum_ite_eq']
    rw [Finset.sum_congr rfl hinner]
    simp [Finset.sum_boole]
  change ↑{s ∈ x6 | x7 s ∈ x5}.card =
    (∫ t in (0 : ℝ)..(1 : ℝ),
      (∑ s ∈ x6, ∏ i ∈ s, x1 (x3 ^ i) t) * Star.star (∑ y ∈ x5, x1 y t)).re
  rw [hint_eq]
  simp
