import Mathlib

/-!
A cut of the square-root modulus arc-band lower bound. The first child
controls the squared error of the rational model. The second child controls
its signed Fourier coefficient. Both concern the frozen arc difference.
The finite Parseval proof is from Conjectures.Goldbach.MaskedWeightLtwo_aux,
and the Chebyshev coefficient estimate from ThreeQuartersExceptionalDirichletWindows.
-/

-- child 1 zh: 对充分大的偶数 n，冻结平方根弧带上素数指数和与固定有理模型之差的平方积分为 o(n / log n)。
-- child 1 en: On the frozen square-root band, the integrated squared error of the prime sum against the fixed rational model is o(n / log n) along the even integers.
-- child 2 zh: 对每个 ε > 0，充分大的偶数 n 的同一弧带上，固定有理模型平方的第 n 个傅里叶系数实部至少为 −ε n。
-- child 2 en: For every ε > 0, the real part of the nth Fourier coefficient of the squared rational model on this band is at least −ε n for every sufficiently large even n.

open Finset MeasureTheory Set

theorem Conjectures.Cuts.Cut20dd3f5dd921159ae64f7d6e
    (err : ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      let L := Nat.log 2 (n+2)
      let Q := ⌊Real.sqrt (n:ℝ) / ((L:ℝ)^4)⌋₊
      let C := fun (s q a : ℕ) => {t : ℝ | |t-(a:ℝ)/q| ≤ ((256*s*L^2:ℕ):ℝ)/((q:ℝ)*n)}
      let A := fun s : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ s ∧ a ≤ q ∧ Nat.Coprime a q ∧ t ∈ C s q a}
      let R := Ioc (0:ℝ) 1 ∩ (A Q \ A ⌊(n:ℝ)^(1/3:ℝ)⌋₊)
      let E := fun t : ℝ => Complex.exp (((2*Real.pi*t:ℝ):ℂ)*Complex.I)
      let M := fun t : ℝ => ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (range (q+1)).filter (Nat.Coprime · q),
        (C Q q a).indicator (fun u => (ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ) *
          (∑ k ∈ range (n+1), E ((k:ℝ)*(u-(a:ℝ)/q)) )) t;
      let S := fun t : ℝ => ∑ k ∈ range (n+1),
        ((if Nat.Prime k then Real.log (k:ℝ) else 0 : ℝ):ℂ)*E ((k:ℝ)*t)
      (∫ t in R, ‖S t-M t‖^2) ≤ d*(n:ℝ)/max 1 (Real.log n))
    (floor : ∀ d : ℝ, 0 < d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      let L := Nat.log 2 (n+2)
      let Q := ⌊Real.sqrt (n:ℝ) / ((L:ℝ)^4)⌋₊
      let C := fun (s q a : ℕ) => {t : ℝ | |t-(a:ℝ)/q| ≤ ((256*s*L^2:ℕ):ℝ)/((q:ℝ)*n)}
      let A := fun s : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ s ∧ a ≤ q ∧ Nat.Coprime a q ∧ t ∈ C s q a}
      let R := Ioc (0:ℝ) 1 ∩ (A Q \ A ⌊(n:ℝ)^(1/3:ℝ)⌋₊)
      let E := fun t : ℝ => Complex.exp (((2*Real.pi*t:ℝ):ℂ)*Complex.I)
      let M := fun t : ℝ => ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ (range (q+1)).filter (Nat.Coprime · q),
        (C Q q a).indicator (fun u => (ArithmeticFunction.moebius q:ℂ)/(q.totient:ℂ) *
          (∑ k ∈ range (n+1), E ((k:ℝ)*(u-(a:ℝ)/q)) )) t;
      ((-(d*(n:ℝ))) ≤ (∫ t in R, M t^2 * E (-(n:ℝ)*t)).re)) :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Q₂ := fun n : ℕ => ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n + 2) : ℝ) ^ 4)⌋₊; let sqrtArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q₂ n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ ((256 * Q₂ n * Q n : ℕ) : ℝ) / ((q : ℝ) * (n : ℝ))}; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (intervalIntegral (fun t => (sqrtArcs n \ wideArcs n).indicator (f n) t) (0 : ℝ) 1 MeasureTheory.volume).re := by
  classical
  let phase (x : ℝ) : ℂ :=
    Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

  let poly (n : ℕ) (a : ℕ → ℝ) (t : ℝ) : ℂ :=
    ∑ k ∈ range (n + 1), (a k : ℂ) * phase ((k : ℝ) * t)

  have parseval (n : ℕ) (a : ℕ → ℝ) :
      (∫ t in (0 : ℝ)..1, ‖poly n a t‖ ^ 2) = ∑ k ∈ range (n + 1), a k ^ 2 := by
    have hstar_E : ∀ x : ℝ, star (phase x) = Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) := by
      intro x
      dsimp only [phase]
      change (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) =
        Complex.exp (-(((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
      rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    have hE_mul_star : ∀ (j k : ℕ) (t : ℝ),
        phase ((j : ℝ) * t) * star (phase ((k : ℝ) * t)) =
        Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
      intro j k t
      rw [hstar_E]
      dsimp only [phase]
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
            have hthis := (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c
            simpa using hthis
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
        ((‖poly n a t‖ ^ 2 : ℝ) : ℂ) =
        ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          ((a j : ℂ) * (a k : ℂ)) *
            Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
      intro t
      have hns : ((‖poly n a t‖ ^ 2 : ℝ) : ℂ) = poly n a t * star (poly n a t) := by
        have hthis := Complex.mul_conj (poly n a t)
        rw [Complex.normSq_eq_norm_sq] at hthis
        exact hthis.symm
      rw [hns]
      dsimp only [poly]
      rw [star_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def]
      rw [show (a j : ℂ) * phase ((j : ℝ) * t) * ((a k : ℂ) * star (phase ((k : ℝ) * t))) =
        ((a j : ℂ) * (a k : ℂ)) * (phase ((j : ℝ) * t) * star (phase ((k : ℝ) * t))) by ring]
      rw [hE_mul_star j k t]
    have hparseval_complex :
        ((intervalIntegral (fun t => ‖poly n a t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume : ℝ) : ℂ) =
        ∑ k ∈ Finset.range (n + 1), ((a k : ℂ) * (a k : ℂ)) := by
      rw [← intervalIntegral.integral_ofReal]
      calc
        intervalIntegral (fun t => ((‖poly n a t‖ ^ 2 : ℝ) : ℂ)) (0 : ℝ) 1 MeasureTheory.volume
          = intervalIntegral
              (fun t => ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
                ((a j : ℂ) * (a k : ℂ)) *
                  Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
              (0 : ℝ) 1 MeasureTheory.volume := intervalIntegral.integral_congr fun t _ => hpoint t
        _ = ∑ j ∈ Finset.range (n + 1),
              intervalIntegral
                (fun t => ∑ k ∈ Finset.range (n + 1),
                  ((a j : ℂ) * (a k : ℂ)) *
                    Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
                (0 : ℝ) 1 MeasureTheory.volume := by
            refine intervalIntegral.integral_finsetSum fun j _ => ?_
            exact Continuous.intervalIntegrable (by fun_prop) 0 1
        _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              intervalIntegral
                (fun t => ((a j : ℂ) * (a k : ℂ)) *
                  Complex.exp ((((j : ℤ) - (k : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)))
                (0 : ℝ) 1 MeasureTheory.volume := by
            refine Finset.sum_congr rfl fun j _ => ?_
            refine intervalIntegral.integral_finsetSum fun k _ => ?_
            exact Continuous.intervalIntegrable (by fun_prop) 0 1
        _ = ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
              ((a j : ℂ) * (a k : ℂ)) * (if ((j : ℤ) - (k : ℤ)) = 0 then (1 : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
            rw [intervalIntegral.integral_const_mul, hint_exp ((j : ℤ) - (k : ℤ))]
        _ = ∑ j ∈ Finset.range (n + 1), ((a j : ℂ) * (a j : ℂ)) := by
            refine Finset.sum_congr rfl fun j hj => ?_
            rw [Finset.sum_eq_single j]
            · simp
            · intro k _ hkj
              have hne : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
              simp [hne]
            · intro hj'
              exact (hj' hj).elim
    have hparseval :
        intervalIntegral (fun t => ‖poly n a t‖ ^ 2) (0 : ℝ) 1 MeasureTheory.volume =
        ∑ k ∈ Finset.range (n + 1), (a k) ^ 2 := by
      have hre := congrArg Complex.re hparseval_complex
      rw [Complex.ofReal_re] at hre
      rw [hre, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.ofReal_mul, Complex.ofReal_re, sq]
    exact hparseval

  let primeLog (k : ℕ) : ℝ := if k.Prime then Real.log k else 0

  have primeLog_energy (n : ℕ) :
      (∑ k ∈ range (n+1),(primeLog k)^2) ≤ Real.log 4*(n:ℝ)*Real.log n := by
    have mass : (∑ k ∈ range (n+1),primeLog k) = Chebyshev.theta n := by
      unfold primeLog
      rw [←Finset.sum_filter,Chebyshev.theta_eq_sum_primesLE_log]
      congr 1
    calc
      _ ≤ ∑ k ∈ range (n+1),Real.log n*primeLog k := by
        refine sum_le_sum fun k hk => ?_
        have hn : k≤n := by have := mem_range.mp hk;omega
        by_cases hp : k.Prime
        · have hk0 : 0 < (k:ℝ) := by exact_mod_cast hp.pos
          have hu := Real.log_le_log hk0 (by exact_mod_cast hn : (k:ℝ)≤n)
          have h0 := Real.log_natCast_nonneg k
          simpa [primeLog,hp,pow_two] using mul_le_mul_of_nonneg_right hu h0
        · simp [primeLog,hp]
      _ ≤ _ := by
        rw [← mul_sum,mass]
        have := mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg n)) (Real.log_natCast_nonneg n)
        linarith only [this]

  have prime_energy (n : ℕ) :
      (∫ t in (0 : ℝ)..1, ‖poly n primeLog t‖ ^ 2) ≤ Real.log 4 * (n : ℝ) * Real.log n := by
    rw [parseval]
    exact primeLog_energy n

  let primes (n : ℕ) := poly n primeLog

  let ell (n : ℕ) := (Nat.log 2 (n+2))^2

  let oldQ (n : ℕ) := ⌊(n:ℝ)^(1/3:ℝ)⌋₊

  let newQ (n : ℕ) := ⌊Real.sqrt (n : ℝ) / ((Nat.log 2 (n+2) : ℝ)^4)⌋₊

  let width (n Q : ℕ) := 256 * Q * ell n

  let cell (n K q a : ℕ) : Set ℝ :=
    {t | |t - (a:ℝ)/q| ≤ (K:ℝ)/((q:ℝ)*n)}

  let arcs (n Q : ℕ) : Set ℝ :=
    {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q ∧ t ∈ cell n (width n Q) q a}

  let band (n : ℕ) := arcs n (newQ n) \ arcs n (oldQ n)

  let region (n : ℕ) := Set.Ioc (0:ℝ) 1 ∩ band n

  let μ (n : ℕ) : Measure ℝ := volume.restrict (region n)

  let wave (n : ℕ) (t : ℝ) := phase (-(n:ℝ)*t)

  let kernel (n : ℕ) (β : ℝ) : ℂ := ∑ k ∈ range (n+1), phase ((k:ℝ)*β)

  let localModel (n q a : ℕ) (t : ℝ) : ℂ :=
    (ArithmeticFunction.moebius q : ℂ)/(q.totient : ℂ) * kernel n (t-(a:ℝ)/q)

  let model (n : ℕ) : ℝ → ℂ := by
    classical
    exact fun t => ∑ q ∈ Finset.Icc 1 (newQ n), ∑ a ∈ (range (q+1)).filter (Nat.Coprime · q),
      (cell n (width n (newQ n)) q a).indicator (localModel n q a) t

  let energy (n : ℕ) (F : ℝ → ℂ) := ∫ t, ‖F t‖ ^ 2 ∂μ n

  let signed (n : ℕ) (F : ℝ → ℂ) := ∫ t, F t ^ 2 * wave n t ∂μ n

  have measurable_cell (n K q a : ℕ) : MeasurableSet (cell n K q a) :=
    (isClosed_le ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet

  have measurable_arcs (n Q : ℕ) : MeasurableSet (arcs n Q) := by
    classical
    let c (q a : ℕ) : Set ℝ :=
      if 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q then cell n (width n Q) q a else ∅
    have h : arcs n Q = ⋃ q, ⋃ a, c q a := by
      ext t
      simp only [arcs, Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨q,a,h1,h2,h3,h4,ht⟩
        refine ⟨q, a, ?_⟩
        unfold c
        rw [ite_eq_left ⟨h1,h2,h3,h4⟩]
        exact ht
      · rintro ⟨q,a,ht⟩
        unfold c at ht
        split_ifs at ht with hc
        · exact ⟨q,a,hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,ht⟩
        · exact ht.elim
    rw [h]
    apply MeasurableSet.iUnion
    intro q
    apply MeasurableSet.iUnion
    intro a
    dsimp [c]
    split
    · exact measurable_cell ..
    · exact MeasurableSet.empty

  have signed_eq_frozen_integral (n : ℕ) (F : ℝ → ℂ) :
      signed n F = ∫ t in (0:ℝ)..1, (band n).indicator (fun u => F u ^ 2 * wave n u) t := by
    unfold band
    rw [intervalIntegral.integral_of_le (by norm_num), setIntegral_indicator
      ((measurable_arcs n (newQ n)).diff (measurable_arcs n (oldQ n)))]

  have mem_of_cont {F : ℝ → ℂ} (n : ℕ) (h : Continuous F) : MemLp F 2 (μ n) := by
    have hi : Integrable (fun x => ‖F x‖^2) (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      ((h.norm.pow 2).intervalIntegrable 0 1).1
    exact (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).2
      (hi.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl))

  have mem_primes (n : ℕ) : MemLp (primes n) 2 (μ n) := by
    apply mem_of_cont
    unfold primes poly phase
    fun_prop

  have mem_model (n : ℕ) : MemLp (model n) 2 (μ n) := by
    classical
    unfold model
    apply memLp_finsetSum
    intro q _
    apply memLp_finsetSum
    intro a _
    apply MemLp.indicator (measurable_cell ..).nullMeasurableSet
    apply mem_of_cont
    unfold localModel kernel phase
    fun_prop

  have prime_band_energy (n : ℕ) :
      energy n (primes n) ≤ Real.log 4 * (n:ℝ) * Real.log n := by
    have hp : Continuous (primes n) := by unfold primes poly phase; fun_prop
    have hi := ((hp.norm.pow 2).intervalIntegrable (μ := volume) 0 1).1
    have h := prime_energy n
    rw [intervalIntegral.integral_of_le (by norm_num)] at h
    exact le_trans (integral_mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)
      (Filter.Eventually.of_forall (fun x => sq_nonneg ‖primes n x‖)) hi) h

  have wave_norm (n : ℕ) (t : ℝ) : ‖wave n t‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _

  have replacement (n : ℕ) (F M : ℝ → ℂ) (hF : MemLp F 2 (μ n))
      (hM : MemLp M 2 (μ n)) :
      ‖signed n F - signed n M‖ ≤
        2 * (Real.sqrt (energy n F) * Real.sqrt (energy n (F-M))) + energy n (F-M) := by
    let D := F - M
    have hD : MemLp D 2 (μ n) := hF.sub hM
    have hw : Continuous (wave n) := by unfold wave phase; fun_prop
    have hi {G : ℝ → ℂ} (hG : MemLp G 2 (μ n)) :
        Integrable (fun t => G t ^ 2 * wave n t) (μ n) := by
      have hg : Integrable (fun t => G t ^ 2) (μ n) := by
        simp_rw [sq]
        exact hG.integrable_mul hG
      exact hg.mul_bdd hw.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => (wave_norm n t).le)
    have hcross : Integrable (fun t => ‖F t‖ * ‖D t‖) (μ n) := hF.norm.integrable_mul hD.norm
    have hsq := (memLp_two_iff_integrable_sq_norm hD.aestronglyMeasurable).1 hD
    have hcs : (∫ t, ‖F t‖ * ‖D t‖ ∂μ n) ≤ Real.sqrt (energy n F) * Real.sqrt (energy n D) := by
      have hh := integral_mul_norm_le_Lp_mul_Lq (μ := μ n) Real.HolderConjugate.two_two
        (f := F) (g := D) (by simpa using hF) (by simpa using hD)
      simpa only [energy,Real.sqrt_eq_rpow,Real.rpow_two] using hh
    unfold signed
    rw [← integral_sub (hi hF) (hi hM)]
    calc
      _ ≤ ∫ t, 2 * (‖F t‖ * ‖D t‖) + ‖D t‖ ^ 2 ∂μ n := by
        apply norm_integral_le_of_norm_le ((hcross.const_mul 2).add hsq)
        apply Filter.Eventually.of_forall
        intro t
        have heq : F t ^ 2 * wave n t - M t ^ 2 * wave n t =
            (2 * (F t * D t) - D t ^ 2) * wave n t := by dsimp [D]; ring
        rw [heq,norm_mul,wave_norm,mul_one]
        exact (norm_sub_le _ _).trans_eq (by simp [norm_pow])
      _ = 2 * (∫ t, ‖F t‖ * ‖D t‖ ∂μ n) + energy n D := by
        rw [integral_add (hcross.const_mul 2) hsq, integral_const_mul]
      _ ≤ _ := by gcongr

  let logScale (n : ℕ) : ℝ := max 1 (Real.log n)

  let MeanSquareChild : Prop := ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    energy n (primes n - model n) ≤ δ * (n:ℝ) / logScale n

  let ModelFloorChild : Prop := ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    -(δ * (n:ℝ)) ≤ (signed n (model n)).re

  have scalar_transfer {P D x L η : ℝ}
      (hP₀ : 0 ≤ P) (hD₀ : 0 ≤ D) (hx : 0 ≤ x) (hL : 1 ≤ L)
      (hη₀ : 0 ≤ η) (hη : η ≤ 1)
      (hP : P ≤ 4 * x * L) (hD : D ≤ η^2 * x / L) :
      2 * (Real.sqrt P * Real.sqrt D) + D ≤ 5 * η * x := by
    have hL₀ : 0 < L := by linarith
    have hprod : P * D ≤ (2 * η * x)^2 := by
      calc
        _ ≤ (4*x*L) * (η^2*x/L) := mul_le_mul hP hD hD₀ (by positivity)
        _ = _ := by field_simp; ring
    have hcross : Real.sqrt P * Real.sqrt D ≤ 2*η*x := by
      rw [← Real.sqrt_mul hP₀]
      exact (Real.sqrt_le_iff.mpr ⟨by positivity,hprod⟩)
    have hηx : η^2*x ≤ η*x := mul_le_mul_of_nonneg_right
      (by nlinarith [mul_nonneg hη₀ (sub_nonneg.mpr hη)]) hx
    have hD' : D ≤ η*x := hD.trans ((div_le_self (by positivity) hL).trans hηx)
    linarith

  have replacement_small (err : MeanSquareChild) :
      ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        ‖signed n (primes n) - signed n (model n)‖ ≤ e * (n:ℝ) := by
    intro e he
    let η : ℝ := min 1 (e/5)
    have hη : 0 < η := lt_min (by norm_num) (by positivity)
    obtain ⟨Ne, hNe⟩ := err (η^2) (sq_pos_of_pos hη)
    refine ⟨Ne, ?_⟩
    intro n hn hEven
    have hD := hNe n hn hEven
    have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hl : 1 ≤ logScale n := le_max_left ..
    have hlog : Real.log 4 ≤ 4 := by
      have h := Real.log_le_sub_one_of_pos (show 0 < (4:ℝ) by norm_num)
      linarith
    have hP : energy n (primes n) ≤ 4 * (n:ℝ) * logScale n := by
      apply (prime_band_energy n).trans
      calc
        _ ≤ Real.log 4 * (n:ℝ) * logScale n :=
          mul_le_mul_of_nonneg_left (le_max_right ..) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlog hn₀) (by linarith)
    have hbound := (replacement n _ _ (mem_primes n) (mem_model n)).trans <|
      scalar_transfer (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
        hn₀ hl hη.le (min_le_left ..) hP hD
    refine hbound.trans (mul_le_mul_of_nonneg_right ?_ hn₀)
    have : η ≤ e/5 := min_le_right ..
    linarith

  have assemble (err : MeanSquareChild) (floor : ModelFloorChild) :
      ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        -(e * (n:ℝ)) ≤ (signed n (primes n)).re := by
    intro e he
    obtain ⟨Ne, hNe⟩ := replacement_small err (e/2) (by positivity)
    obtain ⟨Nm, hNm⟩ := floor (e/2) (by positivity)
    refine ⟨max Ne Nm, ?_⟩
    intro n hn hEven
    have hE := hNe n (le_trans (le_max_left ..) hn) hEven
    have hM := hNm n (le_trans (le_max_right ..) hn) hEven
    have hR := (abs_le.mp (Complex.abs_re_le_norm (signed n (primes n) - signed n (model n)))).1
    rw [Complex.sub_re] at hR
    linarith

  intro _ _ _ _ _ _ _ _ _ _ e he
  obtain ⟨N, hN⟩ := assemble err floor e he
  refine ⟨N, ?_⟩
  intro n hn hEven
  exact (signed_eq_frozen_integral n (primes n)) ▸ hN n hn hEven
