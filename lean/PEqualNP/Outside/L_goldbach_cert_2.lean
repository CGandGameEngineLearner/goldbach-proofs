import Mathlib

/-!
# L-goldbach-cert-2

The Ramanujan-style certificate for modulus 2: the only unit below 2 is 1, so
the character sum is exp(πi·a) = (-1)ᵃ, which is -1 exactly when a is coprime
to 2.
-/

theorem PEqualNP.Outside.L_goldbach_cert_2 :
    ∀ a:ℕ, Nat.Coprime a 2 → (∑ b ∈ (Finset.range 2).filter (fun b => Nat.Coprime b 2), Complex.exp (((2*Real.pi*(a:ℝ)*b/2:ℝ):ℂ)*Complex.I))/(1:ℂ)=(-1:ℂ)/1 := by
  intro a hca
  have ha : Odd a := Nat.coprime_two_right.mp hca
  have hfilter : (Finset.range 2).filter (fun b => Nat.Coprime b 2) = {1} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, Nat.coprime_two_right]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨m, hm⟩ := h2
      omega
    · intro hb
      subst hb
      exact ⟨by omega, ⟨0, by omega⟩⟩
  rw [hfilter, Finset.sum_singleton]
  simp only [div_one]
  push_cast
  have h : (2:ℂ) * Real.pi * ((a:ℂ)) * 1 / 2 = Real.pi * ((a:ℂ)) := by
    rw [mul_one]
    field_simp
  rw [h, show Real.pi * ((a:ℂ)) * Complex.I = ((a:ℂ)) * (Real.pi * Complex.I) from by ring,
      Complex.exp_nat_mul, Complex.exp_pi_mul_I, ha.neg_one_pow]
