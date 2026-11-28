import Mathlib

/-! Fourier coefficient extraction of the elementary symmetric sum of complex
position weights from their multiaffine phase product on the unit interval. -/

namespace Conjectures.Cuts.Task2648c5451231c368b3124e92Aux

open Finset MeasureTheory

noncomputable def phase (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑n * ↑t)

private theorem phase_continuous (n : ℕ) : Continuous (phase n) := by
  unfold phase
  fun_prop

private theorem phase_one_pow (k : ℕ) (t : ℝ) :
    phase 1 t ^ k = phase k t := by
  induction k with
  | zero =>
    simp [phase]
  | succ k ih =>
    rw [pow_succ, ih]
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring

private theorem prod_one_add_expand (s : Finset ℕ) (g : ℕ → ℂ) :
    (∏ i ∈ s, ((1 : ℂ) + g i)) = ∑ u ∈ s.powerset, ∏ i ∈ u, g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.powerset_insert]
    have hdisj : Disjoint s.powerset (s.powerset.image (insert a)) := by
      rw [Finset.disjoint_left]
      intro u hu hmem
      rcases Finset.mem_image.mp hmem with ⟨v, _, rfl⟩
      exact ha (Finset.mem_powerset.mp hu (Finset.mem_insert_self a v))
    rw [Finset.sum_union hdisj]
    have himg :
        (∑ u ∈ s.powerset.image (insert a), ∏ i ∈ u, g i) =
          g a * ∑ v ∈ s.powerset, ∏ i ∈ v, g i := by
      rw [Finset.sum_image]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        have hav : a ∉ v := fun h => ha (Finset.mem_powerset.mp hv h)
        rw [Finset.prod_insert hav]
      · intro v₁ hv₁ v₂ hv₂ heq
        have hav₁ : a ∉ v₁ := fun h => ha (Finset.mem_powerset.mp hv₁ h)
        have hav₂ : a ∉ v₂ := fun h => ha (Finset.mem_powerset.mp hv₂ h)
        simpa [Finset.erase_insert hav₁, Finset.erase_insert hav₂] using
          congrArg (fun w : Finset ℕ => w.erase a) heq
    rw [himg]
    ring

private theorem integral_sum_finset {α : Type*} (s : Finset α) (f : α → ℝ → ℂ)
    (hf : ∀ u ∈ s, Continuous (f u)) :
    (∫ t : ℝ in (0 : ℝ)..(1 : ℝ), ∑ u ∈ s, f u t) =
      ∑ u ∈ s, ∫ t : ℝ in (0 : ℝ)..(1 : ℝ), f u t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp
  | @insert a s ha ih =>
    have hfa : Continuous (f a) := hf a (Finset.mem_insert_self a s)
    have hfs : Continuous (fun t : ℝ => ∑ u ∈ s, f u t) := by
      have hsub : ∀ u ∈ s, Continuous (f u) := fun u hu => hf u (Finset.mem_insert_of_mem hu)
      clear ha ih hf hfa
      induction s using Finset.induction_on with
      | empty =>
        simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
      | @insert b t hb iht =>
        have hstep : (fun x : ℝ => ∑ u ∈ insert b t, f u x) =
            (fun x : ℝ => f b x + ∑ u ∈ t, f u x) := by
          ext x
          exact Finset.sum_insert hb
        rw [hstep]
        exact (hsub b (Finset.mem_insert_self b t)).add
          (iht (fun u hu => hsub u (Finset.mem_insert_of_mem hu)))
    have hcongr : (fun t : ℝ => ∑ u ∈ insert a s, f u t) =
        (fun t : ℝ => f a t + ∑ u ∈ s, f u t) := by
      ext t
      exact Finset.sum_insert ha
    rw [hcongr,
      intervalIntegral.integral_add (hfa.intervalIntegrable _ _) (hfs.intervalIntegrable _ _),
      ih (fun u hu => hf u (Finset.mem_insert_of_mem hu)),
      Finset.sum_insert ha]

private theorem phase_mul_star (m k : ℕ) (t : ℝ) :
    phase m t * Star.star (phase k t) =
      Complex.exp (((2 : ℂ) * ↑Real.pi * Complex.I * ((m : ℤ) - (k : ℤ) : ℤ)) * ↑t) := by
  unfold phase
  rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_natCast, map_ofNat]
  push_cast
  ring

private theorem phase_orthogonality (m k : ℕ) :
    (∫ t : ℝ in (0 : ℝ)..(1 : ℝ), phase m t * Star.star (phase k t)) =
      if m = k then (1 : ℂ) else 0 := by
  by_cases hmk : m = k
  · subst hmk
    simp only [↓reduceIte]
    have hcongr : ∀ t : ℝ, phase m t * Star.star (phase m t) = (1 : ℂ) := by
      intro t
      rw [phase_mul_star, sub_self, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero]
    simp_rw [hcongr]
    simp [intervalIntegral.integral_const]
  · simp only [hmk, ↓reduceIte]
    let d : ℤ := (m : ℤ) - (k : ℤ)
    have hd : d ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmk)
    let c : ℂ := (2 : ℂ) * ↑Real.pi * Complex.I * (d : ℂ)
    have hc : c ≠ 0 := by
      dsimp only [c]
      have h2pi : (2 : ℂ) * ↑Real.pi ≠ 0 :=
        mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
      have h2piI : (2 : ℂ) * ↑Real.pi * Complex.I ≠ 0 :=
        mul_ne_zero h2pi Complex.I_ne_zero
      exact mul_ne_zero h2piI (Int.cast_ne_zero.mpr hd)
    let F : ℝ → ℂ := fun t => Complex.exp (c * ↑t) / c
    have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) (1 : ℝ),
        HasDerivAt F (phase m t * Star.star (phase k t)) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t :=
        (hasDerivAt_id t).ofReal_comp
      have h2 : HasDerivAt (fun x : ℝ => c * (x : ℂ)) (c * 1) t :=
        h1.const_mul c
      have h3 : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)))
          (Complex.exp (c * (t : ℂ)) * (c * 1)) t :=
        h2.cexp
      have h4 : HasDerivAt F ((Complex.exp (c * (t : ℂ)) * (c * 1)) / c) t :=
        h3.div_const c
      have heq : (Complex.exp (c * (t : ℂ)) * (c * 1)) / c =
          phase m t * Star.star (phase k t) := by
        rw [mul_one, mul_div_cancel_right₀ _ hc, phase_mul_star]
      rwa [heq] at h4
    have hint : IntervalIntegrable (fun t : ℝ => phase m t * Star.star (phase k t))
        MeasureTheory.volume (0 : ℝ) (1 : ℝ) :=
      ((phase_continuous m).mul (phase_continuous k).star).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    dsimp only [F, c]
    have h1 : Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * (d : ℂ) * ↑(1 : ℝ)) = 1 := by
      have harg : (2 : ℂ) * ↑Real.pi * Complex.I * (d : ℂ) * ↑(1 : ℝ) =
          (d : ℂ) * ((2 : ℂ) * ↑Real.pi * Complex.I) := by
        push_cast
        ring
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I d
    have h0 : Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * (d : ℂ) * ↑(0 : ℝ)) = 1 := by
      simp
    rw [h1, h0, sub_self]

end Conjectures.Cuts.Task2648c5451231c368b3124e92Aux

theorem Conjectures.Cuts.Task2648c5451231c368b3124e92 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑x1 * ↑x2); ∀ (x2 : Finset ℕ) (x3 : ℕ → ℂ) (x4 : ℕ), ∫ (x5 : ℝ) in (0 : ℝ)..(1 : ℝ), (∏ x6 ∈ x2, ((1 : ℂ) + x3 x6 * x1 (1 : ℕ) x5)) * Star.star (x1 x4 x5) = ∑ x5 ∈ Finset.powersetCard x4 x2, ∏ x6 ∈ x5, x3 x6) := by
  classical
  dsimp only
  intro s w k
  let e := Conjectures.Cuts.Task2648c5451231c368b3124e92Aux.phase
  change (∫ t : ℝ in (0 : ℝ)..(1 : ℝ),
      (∏ i ∈ s, ((1 : ℂ) + w i * e 1 t)) * Star.star (e k t)) =
    ∑ u ∈ Finset.powersetCard k s, ∏ i ∈ u, w i
  have hexp : ∀ t : ℝ,
      (∏ i ∈ s, ((1 : ℂ) + w i * e 1 t)) * Star.star (e k t) =
        ∑ u ∈ s.powerset, (∏ i ∈ u, w i) * (e u.card t * Star.star (e k t)) := by
    intro t
    rw [Conjectures.Cuts.Task2648c5451231c368b3124e92Aux.prod_one_add_expand s
      (fun i => w i * e 1 t), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    rw [Finset.prod_mul_distrib, Finset.prod_const,
      Conjectures.Cuts.Task2648c5451231c368b3124e92Aux.phase_one_pow, mul_assoc]
  simp_rw [hexp]
  rw [Conjectures.Cuts.Task2648c5451231c368b3124e92Aux.integral_sum_finset s.powerset
    (fun u t => (∏ i ∈ u, w i) * (e u.card t * Star.star (e k t)))
    (fun u _ => continuous_const.mul
      ((Conjectures.Cuts.Task2648c5451231c368b3124e92Aux.phase_continuous u.card).mul
        (Conjectures.Cuts.Task2648c5451231c368b3124e92Aux.phase_continuous k).star))]
  have hterm : ∀ u ∈ s.powerset,
      (∫ t : ℝ in (0 : ℝ)..(1 : ℝ),
        (∏ i ∈ u, w i) * (e u.card t * Star.star (e k t))) =
      if u.card = k then ∏ i ∈ u, w i else 0 := by
    intro u _
    rw [intervalIntegral.integral_const_mul,
      Conjectures.Cuts.Task2648c5451231c368b3124e92Aux.phase_orthogonality]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
  have hset : s.powerset.filter (fun u => u.card = k) = Finset.powersetCard k s := by
    ext u
    simp [Finset.mem_powersetCard, Finset.mem_powerset]
  rw [hset]
