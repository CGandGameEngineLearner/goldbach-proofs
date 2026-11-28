import Mathlib

open scoped BigOperators Interval

/- Integer exponential orthogonality adapted from the Apache-2.0 repository
   module BulkSignedExceptionDensity, revision 39ddb0b8312bbed0998c87c178a978c44870cec2. -/
private theorem digit_integral_phase_int : ∀ m : ℤ,
    intervalIntegral
        (fun t : ℝ => Complex.exp ((m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
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
        HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)) / c)
          (Complex.exp (c * (t : ℂ))) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => c * (x : ℂ)) c t := by
        have := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
        simpa using this
      have h2 : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)))
          (Complex.exp (c * (t : ℂ)) * c) t := h1.cexp
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

theorem Conjectures.Cuts.Task91500b604fdcc58571ab069f : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑x1 : ℂ) * (↑x2 : ℂ)); ∀ (x2 x3 : ℕ) (x4 x5 : Finset ℕ),   have x6 : Finset (Fin x3 → ℕ) := Fintype.piFinset fun (x6 : Fin x3) => x4;   have x7 : (Fin x3 → ℕ) → ℕ := fun (x7 : Fin x3 → ℕ) => ∑ x8 : Fin x3, x7 x8 * x2 ^ (↑x8 : ℕ);   (↑{x8 ∈ x6 | x7 x8 ∈ x5}.card : ℝ) = (∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (∏ x9 : Fin x3, ∑ x10 ∈ x4, x1 (x10 * x2 ^ (↑x9 : ℕ)) x8) * Star.star (∑ x9 ∈ x5, x1 x9 x8)).re) := by
  classical
  dsimp only
  intro b k D S
  let e (j : ℕ) (t : ℝ) : ℂ :=
    Complex.exp ((2 : ℂ) * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (t : ℂ))
  let A := Fintype.piFinset (fun _ : Fin k => D)
  let v (f : Fin k → ℕ) := ∑ i : Fin k, f i * b ^ (i : ℕ)
  change ((A.filter (fun f => v f ∈ S)).card : ℝ) =
    (∫ t in (0 : ℝ)..1,
      (∏ i : Fin k, ∑ d ∈ D, e (d * b ^ (i : ℕ)) t) * star (∑ a ∈ S, e a t)).re
  have hcont (n : ℕ) : Continuous (e n) := by unfold e; fun_prop
  have hprod (f : Fin k → ℕ) (t : ℝ) :
      (∏ i : Fin k, e (f i * b ^ (i : ℕ)) t) = e (v f) t := by
    unfold e v
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [Finset.mul_sum, Finset.sum_mul]
  have hpoint (t : ℝ) :
      (∏ i : Fin k, ∑ d ∈ D, e (d * b ^ (i : ℕ)) t) * star (∑ a ∈ S, e a t) =
        ∑ f ∈ A, ∑ a ∈ S, e (v f) t * star (e a t) := by
    rw [Finset.prod_univ_sum, star_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [hprod, Finset.mul_sum]
  have hpair (j a : ℕ) :
      (∫ t in (0 : ℝ)..1, e j t * star (e a t)) = if j = a then (1 : ℂ) else 0 := by
    have he (t : ℝ) : e j t * star (e a t) =
        Complex.exp ((((j : ℤ) - (a : ℤ) : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
      simp only [e, Complex.star_def, ← Complex.exp_conj, map_mul, map_ofNat,
        Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast, ← Complex.exp_add,
        Int.cast_sub, Int.cast_natCast]
      congr 1
      ring
    simp_rw [he]
    simpa only [sub_eq_zero, Nat.cast_inj] using digit_integral_phase_int ((j : ℤ) - (a : ℤ))
  have hi (f : Fin k → ℕ) (a : ℕ) :
      Continuous (fun t : ℝ => e (v f) t * star (e a t)) := by
    exact (hcont _).mul ((hcont _).star)
  have hv (f : Fin k → ℕ) :
      (∫ t in (0 : ℝ)..1, ∑ a ∈ S, e (v f) t * star (e a t)) =
        (if v f ∈ S then (1 : ℂ) else 0) := by
    rw [intervalIntegral.integral_finsetSum (fun a _ => (hi f a).intervalIntegrable _ _)]
    simp_rw [hpair]
    by_cases h : v f ∈ S
    · rw [Finset.sum_eq_single (v f)]
      · simp [h]
      · intro a _ ha
        simp [Ne.symm ha]
      · exact fun hn => (hn h).elim
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro a ha
      have hne : v f ≠ a := fun hEq => h (hEq.symm ▸ ha)
      simp [hne]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun f _ =>
    (continuous_finsetSum S (fun a _ => hi f a)).intervalIntegrable _ _)]
  simp_rw [hv]
  rw [← Finset.sum_filter]
  simp
