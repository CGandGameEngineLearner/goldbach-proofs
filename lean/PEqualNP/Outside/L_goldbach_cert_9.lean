import Mathlib

/-!
# L-goldbach-cert-9

The Ramanujan certificate for modulus 9: 9 is not squarefree, so the character
sum vanishes. The primitive 9th root raised to a coprime power keeps the full
residue sum at zero, while the non-units 0, 3, 6 contribute 1, eta, eta-squared
for a primitive cube root, which also sums to zero; division by the totient 6
leaves 0/6.
-/

theorem PEqualNP.Outside.L_goldbach_cert_9 :
    ∀ a:ℕ, Nat.Coprime a 9 → (∑ b ∈ (Finset.range 9).filter (fun b => Nat.Coprime b 9), Complex.exp (((2*Real.pi*(a:ℝ)*b/9:ℝ):ℂ)*Complex.I))/(6:ℂ)=(0:ℂ)/6 := by
  intro a hca
  have hca3 : Nat.Coprime a 3 := hca.of_dvd_right (by norm_num : (3:ℕ) ∣ 9)
  set ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(9:ℚ))) with hξ
  set η : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(3:ℚ))) with hη
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/9:ℝ):ℂ)*Complex.I) = ξ^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/9:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(9:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hξ]
  have hprim9 : IsPrimitiveRoot ξ 9 := by
    rw [hξ]; exact Complex.isPrimitiveRoot_exp_of_coprime a 9 (by norm_num) hca
  have hprim3 : IsPrimitiveRoot η 3 := by
    rw [hη]; exact Complex.isPrimitiveRoot_exp_of_coprime a 3 (by norm_num) hca3
  have hgeo9 : ∑ b ∈ Finset.range 9, ξ^b = 0 := hprim9.geom_sum_eq_zero (by norm_num)
  have hxi3 : ξ^3 = η := by
    rw [hξ, hη, ← Complex.exp_nat_mul]
    have hc : ((3:ℕ):ℂ) * (2 * Real.pi * Complex.I * ((a:ℚ)/(9:ℚ))) = 2 * Real.pi * Complex.I * ((a:ℚ)/(3:ℚ)) := by
      push_cast
      field_simp
      ring
    rw [hc]
  have hxi6 : ξ^6 = η^2 := by
    have h6 : (6:ℕ) = 3*2 := by norm_num
    rw [h6, pow_mul, hxi3]
  have h3sum : (1:ℂ) + (η + η^2) = 0 := by
    have h := hprim3.geom_sum_eq_zero (by norm_num : 1 < 3)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at h
    rw [add_assoc] at h
    exact h
  have hnu : (Finset.range 9).filter (fun b => ¬ Nat.Coprime b 9) = {0,3,6} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      have h3b : (3:ℕ) ∣ b := by
        by_contra h3nb
        exact h2 (by rw [show (9:ℕ) = 3^2 from by norm_num]; exact Nat.Prime.coprime_pow_of_not_dvd Nat.prime_three h3nb)
      obtain ⟨k, hk⟩ := h3b
      have hk2 : k ≤ 2 := by omega
      interval_cases k
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (by omega))
    · rintro (rfl | rfl | rfl)
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨3, Nat.prime_three, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨3, Nat.prime_three, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨3, Nat.prime_three, by norm_num, by norm_num⟩⟩
  have hunits : (∑ b ∈ (Finset.range 9).filter (fun b => Nat.Coprime b 9), Complex.exp (((2*Real.pi*(a:ℝ)*b/9:ℝ):ℂ)*Complex.I)) = 0 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range 9) (p := fun b => Nat.Coprime b 9) (f := fun b => Complex.exp (((2*Real.pi*(a:ℝ)*b/9:ℝ):ℂ)*Complex.I))
    rw [hnu] at hsplit
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton,
        ] at hsplit
    rw [hterm 0, hterm 3, hterm 6, pow_zero, hxi3, hxi6] at hsplit
    have htot : ∑ b ∈ Finset.range 9, Complex.exp (((2*Real.pi*(a:ℝ)*b/9:ℝ):ℂ)*Complex.I) = 0 := by
      rw [Finset.sum_congr rfl (fun b _ => hterm b)]
      exact hgeo9
    rw [htot] at hsplit
    rw [h3sum, add_zero] at hsplit
    exact hsplit
  rw [hunits]
