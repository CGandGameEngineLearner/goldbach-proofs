import Mathlib

/-!
# L-goldbach-cert-49

The Ramanujan certificate for modulus 49: 49 = 7^2 is not squarefree, so the
character sum vanishes. The primitive 49th root raised to a coprime power keeps
the full residue sum at zero, while the non-units (multiples of 7) contribute
the powers of a primitive 7th root, which also sum to zero; division by the
totient 42 leaves 0/42.
-/

theorem PEqualNP.Outside.L_goldbach_cert_49 :
    ∀ a:ℕ, Nat.Coprime a 49 → (∑ b ∈ (Finset.range 49).filter (fun b => Nat.Coprime b 49), Complex.exp (((2*Real.pi*(a:ℝ)*b/49:ℝ):ℂ)*Complex.I))/(42:ℂ)=(0:ℂ)/42 := by
  intro a hca
  have hcap : Nat.Coprime a 7 := hca.of_dvd_right (by norm_num : (7:ℕ) ∣ 49)
  set ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(49:ℚ))) with hξ
  set η : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(7:ℚ))) with hη
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/49:ℝ):ℂ)*Complex.I) = ξ^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/49:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(49:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hξ]
  have hprimn : IsPrimitiveRoot ξ 49 := by
    rw [hξ]; exact Complex.isPrimitiveRoot_exp_of_coprime a 49 (by norm_num) hca
  have hprimp : IsPrimitiveRoot η 7 := by
    rw [hη]; exact Complex.isPrimitiveRoot_exp_of_coprime a 7 (by norm_num) hcap
  have hgeon : ∑ b ∈ Finset.range 49, ξ^b = 0 := hprimn.geom_sum_eq_zero (by norm_num)
  have hxi7 : ξ^7 = η := by
    rw [hξ, hη, ← Complex.exp_nat_mul]
    have hc : ((7:ℕ):ℂ) * (2 * Real.pi * Complex.I * ((a:ℚ)/(49:ℚ))) = 2 * Real.pi * Complex.I * ((a:ℚ)/(7:ℚ)) := by
      push_cast
      field_simp
      ring
    rw [hc]
  have hxi14 : ξ^14 = η^2 := by
    have h14 : (14:ℕ) = 7*2 := by norm_num
    rw [h14, pow_mul, hxi7]
  have hxi21 : ξ^21 = η^3 := by
    have h21 : (21:ℕ) = 7*3 := by norm_num
    rw [h21, pow_mul, hxi7]
  have hxi28 : ξ^28 = η^4 := by
    have h28 : (28:ℕ) = 7*4 := by norm_num
    rw [h28, pow_mul, hxi7]
  have hxi35 : ξ^35 = η^5 := by
    have h35 : (35:ℕ) = 7*5 := by norm_num
    rw [h35, pow_mul, hxi7]
  have hxi42 : ξ^42 = η^6 := by
    have h42 : (42:ℕ) = 7*6 := by norm_num
    rw [h42, pow_mul, hxi7]
  have hpsum : (1:ℂ) + (η + (η^2 + (η^3 + (η^4 + (η^5 + η^6))))) = 0 := by
    have h := hprimp.geom_sum_eq_zero (by norm_num : 1 < 7)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at h
    rw [add_assoc, add_assoc, add_assoc, add_assoc, add_assoc] at h
    exact h
  have hp : Nat.Prime 7 := by decide
  have hnu : (Finset.range 49).filter (fun b => ¬ Nat.Coprime b 49) = {0,7,14,21,28,35,42} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      have hpb : (7:ℕ) ∣ b := by
        by_contra hpnb
        exact h2 (by rw [show (49:ℕ) = 7^2 from by norm_num]; exact Nat.Prime.coprime_pow_of_not_dvd hp hpnb)
      obtain ⟨k, hk⟩ := hpb
      have hk2 : k ≤ 6 := by omega
      interval_cases k
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by omega)))))))
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨7, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨7, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨7, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨7, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨7, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨7, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨7, hp, by norm_num, by norm_num⟩⟩
  have hunits : (∑ b ∈ (Finset.range 49).filter (fun b => Nat.Coprime b 49), Complex.exp (((2*Real.pi*(a:ℝ)*b/49:ℝ):ℂ)*Complex.I)) = 0 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range 49) (p := fun b => Nat.Coprime b 49) (f := fun b => Complex.exp (((2*Real.pi*(a:ℝ)*b/49:ℝ):ℂ)*Complex.I))
    rw [hnu] at hsplit
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton] at hsplit
    rw [hterm 0, hterm 7, hterm 14, hterm 21, hterm 28, hterm 35, hterm 42, pow_zero, hxi7, hxi14, hxi21, hxi28, hxi35, hxi42] at hsplit
    have htot : ∑ b ∈ Finset.range 49, Complex.exp (((2*Real.pi*(a:ℝ)*b/49:ℝ):ℂ)*Complex.I) = 0 := by
      rw [Finset.sum_congr rfl (fun b _ => hterm b)]
      exact hgeon
    rw [htot, hpsum, add_zero] at hsplit
    exact hsplit
  rw [hunits]

