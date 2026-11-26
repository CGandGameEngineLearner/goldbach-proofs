import Mathlib

/-! # L-quadratic-primes-levent-cosine-orthogonality

For modulus p > 0, the sum over k ∈ [0, p) of cos(2π k (n−r)/p) is p when n ≡ r (mod p)
and 0 otherwise (complete additive character orthogonality). -/

open Complex
open scoped BigOperators

theorem PEqualNP.Outside.L_quadratic_primes_levent_cosine_orthogonality :
    let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p; ∀ p n r : ℕ, 0<p → (∑ k ∈ Finset.range p, Real.cos (angle p k ((n : ℝ)-r))) = if n%p=r%p then (p : ℝ) else 0 := by
  intro angle p n r hp
  let w : ℝ := 2 * Real.pi * ((n : ℝ) - r) / p
  let ζ : ℂ := Complex.exp (w * Complex.I)
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  let m : ℤ := (n : ℤ) - (r : ℤ)

  have hζp : ζ ^ p = 1 := by
    dsimp [ζ, w]
    rw [← Complex.exp_nsmul (((2 * Real.pi * ((n : ℝ) - r) / p : ℝ) : ℂ) * Complex.I) p]
    calc
      Complex.exp (p • (((2 * Real.pi * ((n : ℝ) - r) / p : ℝ) : ℂ) * Complex.I))
          = Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I)) := by
            congr 1
            rw [nsmul_eq_mul]
            have hscale : (p : ℝ) * (2 * Real.pi * ((n : ℝ) - r) / p) = 2 * Real.pi * ((n : ℝ) - r) := by
              field_simp [hp']
            have hcast : ((2 * Real.pi * ((n : ℝ) - r) : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi) := by
              dsimp [m]
              norm_num
              ring
            calc
              (p : ℂ) * (((2 * Real.pi * ((n : ℝ) - r) / p : ℝ) : ℂ) * Complex.I)
                  = (((p : ℝ) * (2 * Real.pi * ((n : ℝ) - r) / p) : ℝ) : ℂ) * Complex.I := by
                    push_cast
                    ring
              _ = ((2 * Real.pi * ((n : ℝ) - r) : ℝ) : ℂ) * Complex.I := by rw [hscale]
              _ = ((m : ℂ) * (2 * Real.pi)) * Complex.I := by rw [hcast]
              _ = (m : ℂ) * (2 * Real.pi * Complex.I) := by ring
      _ = 1 := Complex.exp_int_mul_two_pi_mul_I m

  have hcosk (k : ℕ) : Real.cos (angle p k ((n : ℝ) - r)) = (ζ ^ k).re := by
    dsimp [angle, ζ, w]
    have hk : (2 * Real.pi * (k : ℝ) * ((n : ℝ) - r)) / p = (k : ℝ) * (2 * Real.pi * ((n : ℝ) - r) / p) := by
      field_simp [hp']
    rw [hk]
    have hkexp : Complex.exp ((((k : ℝ) * (2 * Real.pi * ((n : ℝ) - r) / p) : ℝ) : ℂ) * Complex.I)
        = (Complex.exp (((2 * Real.pi * ((n : ℝ) - r) / p : ℝ) : ℂ) * Complex.I)) ^ k := by
      calc
        Complex.exp ((((k : ℝ) * (2 * Real.pi * ((n : ℝ) - r) / p) : ℝ) : ℂ) * Complex.I)
            = Complex.exp (k • (((2 * Real.pi * ((n : ℝ) - r) / p : ℝ) : ℂ) * Complex.I)) := by
              congr 1
              push_cast
              ring
        _ = (Complex.exp (((2 * Real.pi * ((n : ℝ) - r) / p : ℝ) : ℂ) * Complex.I)) ^ k :=
          Complex.exp_nsmul (((2 * Real.pi * ((n : ℝ) - r) / p : ℝ) : ℂ) * Complex.I) k
    rw [← hkexp, Complex.exp_mul_I]
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    ring

  have hsumζ_re : (∑ k ∈ Finset.range p, Real.cos (angle p k ((n : ℝ) - r))) =
      (∑ k ∈ Finset.range p, ζ ^ k).re := by
    rw [Finset.sum_congr rfl (fun k _ => hcosk k)]
    rw [← Complex.re_sum]

  by_cases h : n % p = r % p
  · -- ζ = 1 : every term is 1
    have hζ1 : ζ = 1 := by
      dsimp [ζ, w]
      have hm : Nat.ModEq p n r := h
      have hdiv0 : (p : ℤ) ∣ (r : ℤ) - (n : ℤ) := Nat.modEq_iff_dvd.mp hm
      have hdiv : (p : ℤ) ∣ (n : ℤ) - (r : ℤ) := by
        rw [show (n : ℤ) - (r : ℤ) = -((r : ℤ) - (n : ℤ)) by ring]
        exact dvd_neg.mpr hdiv0
      obtain ⟨mm, hmdiv⟩ := hdiv
      have hmr : ((n : ℝ) - r) / p = (mm : ℝ) := by
        have hreal : ((n : ℝ) - r) = (mm : ℝ) * p := by
          have hmdiv' : (n : ℤ) - (r : ℤ) = mm * (p : ℤ) := by
            rw [hmdiv]
            ring
          exact_mod_cast hmdiv'
        rw [hreal]
        field_simp [hp']
      have hmrc : (2 * Real.pi * ((n : ℝ) - r) / p) = 2 * Real.pi * (mm : ℝ) := by
        rw [mul_div_assoc, hmr]
      rw [hmrc]
      have harg : (↑(2 * Real.pi * (mm : ℝ)) : ℂ) * Complex.I = (mm : ℂ) * (2 * ↑Real.pi * Complex.I) := by
        push_cast
        ring
      rw [harg]
      exact Complex.exp_int_mul_two_pi_mul_I mm
    rw [hsumζ_re]
    rw [Finset.sum_congr rfl (fun k _ => by rw [hζ1, one_pow])]
    simp [h]

  · -- ζ ≠ 1 : geometric series vanishes
    have hζne : ζ ≠ 1 := by
      intro hζ1
      apply h
      have h1 := (Complex.exp_eq_one_iff).mp hζ1
      rcases h1 with ⟨ℓ, hℓ⟩
      have hsc : (2 * Real.pi * ((n : ℝ) - r) / p) = (ℓ : ℝ) * (2 * Real.pi) := by
        have hI := congrArg (fun z : ℂ => z * (-Complex.I)) hℓ
        have hIl : ((↑(2 * Real.pi * ((n : ℝ) - r) / p) : ℂ) * Complex.I) * (-Complex.I)
            = (↑(2 * Real.pi * ((n : ℝ) - r) / p) : ℂ) := by
          rw [mul_assoc, mul_neg, Complex.I_mul_I]
          norm_num
        have hIr : (↑ℓ * (2 * ↑Real.pi * Complex.I)) * (-Complex.I) = ↑ℓ * (2 * ↑Real.pi) := by
          rw [mul_assoc, mul_assoc, mul_neg, Complex.I_mul_I]
          norm_num
        dsimp [w] at hI
        rw [hIl, hIr] at hI
        exact_mod_cast hI
      have hreal : ((n : ℝ) - r) = (ℓ : ℝ) * p := by
        have h2π : (2 * Real.pi) ≠ 0 := by positivity
        have hdiv : ((n : ℝ) - r) / p = (ℓ : ℝ) := by
          apply mul_left_cancel₀ h2π
          rw [← mul_div_assoc, hsc]
          ring
        exact (div_eq_iff hp').mp hdiv
      have hdiv : (p : ℤ) ∣ (n : ℤ) - (r : ℤ) := by
        refine ⟨ℓ, ?_⟩
        have hreal' : ((n : ℝ) - r) = (p : ℝ) * (ℓ : ℝ) := by
          rw [hreal]
          ring
        exact_mod_cast hreal'
      have hm : Nat.ModEq p n r := by
        rw [Nat.modEq_iff_dvd]
        rw [show (r : ℤ) - (n : ℤ) = -((n : ℤ) - (r : ℤ)) by ring]
        exact dvd_neg.mpr hdiv
      simpa [Nat.ModEq] using hm
    have hgeom : (∑ k ∈ Finset.range p, ζ ^ k) * (ζ - 1) = ζ ^ p - 1 := by
      simpa using (geom_sum_mul ζ p)
    have hsumζ : (∑ k ∈ Finset.range p, ζ ^ k) = 0 := by
      have hzero : (∑ k ∈ Finset.range p, ζ ^ k) * (ζ - 1) = 0 := by
        rw [hgeom, hζp]
        norm_num
      have hζm1 : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζne
      exact Or.resolve_right (mul_eq_zero.mp hzero) hζm1
    rw [hsumζ_re, hsumζ, Complex.zero_re]
    simp [h]
