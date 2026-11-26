import Mathlib

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_quadratic_primes_levent_cosine_orthogonality :
    let angle := fun p k : ℕ => fun t : ℝ => 2 * Real.pi * k * t / p;
    ∀ p n r : ℕ, 0<p → (∑ k ∈ Finset.range p, Real.cos (angle p k ((n : ℝ)-r))) = if n%p = r%p then (p:ℝ) else 0 := by
  intro angle p n r hp
  have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.1 hp)
  set θ : ℝ := 2 * Real.pi * ((n:ℝ) - (r:ℝ)) / (p:ℝ) with hθ
  set ζ : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hζ
  have hpθ : (p:ℝ) * θ = 2 * Real.pi * ((n:ℝ) - (r:ℝ)) := by
    rw [hθ]; field_simp
  have hmem : ∀ k ∈ Finset.range p, Real.cos (angle p k ((n:ℝ)-r)) = (ζ^k).re := by
    intro k hk
    have hang : angle p k ((n:ℝ)-r) = θ * (k:ℝ) := by
      simp only [angle, hθ]
      field_simp
    rw [hang]
    have he : (((θ * (k:ℝ) : ℝ)) : ℂ) * Complex.I = (k:ℂ) * ((θ:ℂ) * Complex.I) := by
      push_cast; ring
    have h1 : Real.cos (θ * (k:ℝ)) = (Complex.exp (((θ*(k:ℝ) : ℝ) : ℂ) * Complex.I)).re :=
      (Complex.exp_ofReal_mul_I_re _).symm
    rw [h1, he, Complex.exp_nat_mul, hζ]
  have hre : ∀ s : Finset ℕ, (∑ k ∈ s, ζ^k).re = ∑ k ∈ s, (ζ^k).re := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [Finset.sum_insert, ha, Complex.add_re, ih]
  have hL : (∑ k ∈ Finset.range p, Real.cos (angle p k ((n:ℝ)-r))) = ((∑ k ∈ Finset.range p, ζ^k)).re := by
    rw [hre (Finset.range p)]
    exact Finset.sum_congr rfl hmem
  have hcast : ((n:ℝ) - (r:ℝ)) = (((n:ℤ)-(r:ℤ) : ℤ) : ℝ) := by push_cast; ring
  have hζp : ζ^p = 1 := by
    have key : (p:ℝ) * θ = (((n:ℤ)-(r:ℤ) : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hpθ, hcast]; ring
    have harg : (p:ℂ) * ((θ:ℂ) * Complex.I) = (((n:ℤ)-(r:ℤ) : ℤ) : ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by
      have h2 : (((p:ℝ) * θ : ℝ)) = (((n:ℤ)-(r:ℤ) : ℤ) : ℝ) * (2 * Real.pi) := key
      have h3 : ((p:ℂ) * ((θ:ℂ) * Complex.I)) = ((((p:ℝ) * θ : ℝ)) : ℂ) * Complex.I := by
        push_cast; ring
      rw [h3, h2]
      push_cast; ring
    rw [hζ, ← Complex.exp_nat_mul, harg]
    simpa using Complex.exp_int_mul_two_pi_mul_I ((n:ℤ)-(r:ℤ))
  have hdvd : (p:ℤ) ∣ ((n:ℤ) - (r:ℤ)) ↔ n % p = r % p := by
    have h := Nat.modEq_iff_dvd (n := p) (a := r) (b := n)
    have h2 : Nat.ModEq p r n ↔ n % p = r % p := by
      rw [Nat.ModEq, eq_comm]
    exact h.symm.trans h2
  have hzE : ζ = 1 ↔ n % p = r % p := by
    constructor
    · intro h1
      obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 (by rw [← hζ]; exact h1)
      have hreal : θ = (m:ℝ) * (2 * Real.pi) := by
        simpa using congrArg Complex.im hm
      have hmul : ((n:ℝ) - (r:ℝ)) = (m:ℝ) * (p:ℝ) := by
        have h1' : (p:ℝ) * θ = 2 * Real.pi * ((n:ℝ) - (r:ℝ)) := hpθ
        rw [hreal] at h1'
        have h4 : ((p:ℝ) * (m:ℝ)) * (2*Real.pi) = ((n:ℝ) - (r:ℝ)) * (2*Real.pi) := by
          have h4' := h1'
          rw [show (p:ℝ) * ((m:ℝ) * (2*Real.pi)) = ((p:ℝ)*(m:ℝ))*(2*Real.pi) from by ring,
              show (2:ℝ) * Real.pi * ((n:ℝ) - (r:ℝ)) = ((n:ℝ) - (r:ℝ)) * (2*Real.pi) from by ring] at h4'
          exact h4'
        have h2 : (2:ℝ) * Real.pi ≠ 0 := by positivity
        have h5 := mul_right_cancel₀ h2 h4
        exact h5.symm.trans (by ring)
      have hZ : ((n:ℤ) - (r:ℤ)) = m * (p:ℤ) := by
        have hc : (((n:ℤ) - (r:ℤ) : ℤ) : ℝ) = (m:ℝ) * (p:ℝ) := by
          rw [← hcast]; exact hmul
        exact_mod_cast hc
      exact hdvd.mp ⟨m, by rw [hZ]; ring⟩
    · intro hmod
      obtain ⟨m, hm⟩ := hdvd.mpr hmod
      have hreal : ((n:ℝ) - (r:ℝ)) = (p:ℝ) * (m:ℝ) := by
        have hc : (((n:ℤ) - (r:ℤ) : ℤ) : ℝ) = ((p:ℤ) * m : ℤ) := by rw [hm]
        push_cast at hc ⊢
        linarith [hc]
      have hθm : θ = (m:ℝ) * (2 * Real.pi) := by
        have h1' : (p:ℝ) * θ = 2 * Real.pi * ((n:ℝ) - (r:ℝ)) := hpθ
        rw [hreal] at h1'
        have hb : (p:ℝ) * ((m:ℝ) * (2*Real.pi)) = 2 * Real.pi * ((p:ℝ) * (m:ℝ)) := by ring
        rw [← hb] at h1'
        exact mul_left_cancel₀ hpne h1'
      rw [hζ]
      have harg : (θ:ℂ) * Complex.I = (m:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by
        rw [hθm]; push_cast; ring
      rw [harg]
      simpa using Complex.exp_int_mul_two_pi_mul_I m
  have hsum : (∑ k ∈ Finset.range p, ζ^k) = if n%p = r%p then (p:ℂ) else 0 := by
    by_cases hz : n%p = r%p
    · have h1 : ζ = 1 := hzE.mpr hz
      rw [if_pos hz]
      rw [Finset.sum_congr rfl (fun k _ => by rw [h1, one_pow])]
      simp
    · have h1 : ζ ≠ 1 := fun h => hz (hzE.mp h)
      rw [if_neg hz, geom_sum_eq h1 p, hζp]
      simp
  rw [hL, hsum]
  split_ifs <;> simp
