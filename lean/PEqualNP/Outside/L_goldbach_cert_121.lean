import Mathlib

/-!
# L-goldbach-cert-121

The Ramanujan certificate for modulus 121: 121 = 11^2 is not squarefree, so the
character sum vanishes. The primitive 121th root raised to a coprime power keeps
the full residue sum at zero, while the non-units (multiples of 11) contribute
the powers of a primitive 11th root, which also sum to zero; division by the
totient 110 leaves 0/110.
-/

theorem PEqualNP.Outside.L_goldbach_cert_121 :
    ∀ a:ℕ, Nat.Coprime a 121 → (∑ b ∈ (Finset.range 121).filter (fun b => Nat.Coprime b 121), Complex.exp (((2*Real.pi*(a:ℝ)*b/121:ℝ):ℂ)*Complex.I))/(110:ℂ)=(0:ℂ)/110 := by
  intro a hca
  have hcap : Nat.Coprime a 11 := hca.of_dvd_right (by norm_num : (11:ℕ) ∣ 121)
  set ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(121:ℚ))) with hξ
  set η : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(11:ℚ))) with hη
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/121:ℝ):ℂ)*Complex.I) = ξ^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/121:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(121:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hξ]
  have hprimn : IsPrimitiveRoot ξ 121 := by
    rw [hξ]; exact Complex.isPrimitiveRoot_exp_of_coprime a 121 (by norm_num) hca
  have hprimp : IsPrimitiveRoot η 11 := by
    rw [hη]; exact Complex.isPrimitiveRoot_exp_of_coprime a 11 (by norm_num) hcap
  have hgeon : ∑ b ∈ Finset.range 121, ξ^b = 0 := hprimn.geom_sum_eq_zero (by norm_num)
  have hxi11 : ξ^11 = η := by
    rw [hξ, hη, ← Complex.exp_nat_mul]
    have hc : ((11:ℕ):ℂ) * (2 * Real.pi * Complex.I * ((a:ℚ)/(121:ℚ))) = 2 * Real.pi * Complex.I * ((a:ℚ)/(11:ℚ)) := by
      push_cast
      field_simp
      ring
    rw [hc]
  have hxi22 : ξ^22 = η^2 := by
    have h22 : (22:ℕ) = 11*2 := by norm_num
    rw [h22, pow_mul, hxi11]
  have hxi33 : ξ^33 = η^3 := by
    have h33 : (33:ℕ) = 11*3 := by norm_num
    rw [h33, pow_mul, hxi11]
  have hxi44 : ξ^44 = η^4 := by
    have h44 : (44:ℕ) = 11*4 := by norm_num
    rw [h44, pow_mul, hxi11]
  have hxi55 : ξ^55 = η^5 := by
    have h55 : (55:ℕ) = 11*5 := by norm_num
    rw [h55, pow_mul, hxi11]
  have hxi66 : ξ^66 = η^6 := by
    have h66 : (66:ℕ) = 11*6 := by norm_num
    rw [h66, pow_mul, hxi11]
  have hxi77 : ξ^77 = η^7 := by
    have h77 : (77:ℕ) = 11*7 := by norm_num
    rw [h77, pow_mul, hxi11]
  have hxi88 : ξ^88 = η^8 := by
    have h88 : (88:ℕ) = 11*8 := by norm_num
    rw [h88, pow_mul, hxi11]
  have hxi99 : ξ^99 = η^9 := by
    have h99 : (99:ℕ) = 11*9 := by norm_num
    rw [h99, pow_mul, hxi11]
  have hxi110 : ξ^110 = η^10 := by
    have h110 : (110:ℕ) = 11*10 := by norm_num
    rw [h110, pow_mul, hxi11]
  have hpsum : (1:ℂ) + (η + (η^2 + (η^3 + (η^4 + (η^5 + (η^6 + (η^7 + (η^8 + (η^9 + η^10))))))))) = 0 := by
    have h := hprimp.geom_sum_eq_zero (by norm_num : 1 < 11)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] at h
    rw [add_assoc, add_assoc, add_assoc, add_assoc, add_assoc, add_assoc, add_assoc, add_assoc, add_assoc] at h
    exact h
  have hp : Nat.Prime 11 := by decide
  have hnu : (Finset.range 121).filter (fun b => ¬ Nat.Coprime b 121) = {0,11,22,33,44,55,66,77,88,99,110} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      have hpb : (11:ℕ) ∣ b := by
        by_contra hpnb
        exact h2 (by rw [show (121:ℕ) = 11^2 from by norm_num]; exact Nat.Prime.coprime_pow_of_not_dvd hp hpnb)
      obtain ⟨k, hk⟩ := hpb
      have hk2 : k ≤ 10 := by omega
      interval_cases k
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inr (Or.inr (Or.inl (by omega)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ((by omega)))))))))))
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨11, hp, by norm_num, by norm_num⟩⟩
  have hunits : (∑ b ∈ (Finset.range 121).filter (fun b => Nat.Coprime b 121), Complex.exp (((2*Real.pi*(a:ℝ)*b/121:ℝ):ℂ)*Complex.I)) = 0 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range 121) (p := fun b => Nat.Coprime b 121) (f := fun b => Complex.exp (((2*Real.pi*(a:ℝ)*b/121:ℝ):ℂ)*Complex.I))
    rw [hnu] at hsplit
    rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton] at hsplit
    rw [hterm 0, hterm 11, hterm 22, hterm 33, hterm 44, hterm 55, hterm 66, hterm 77, hterm 88, hterm 99, hterm 110, pow_zero, hxi11, hxi22, hxi33, hxi44, hxi55, hxi66, hxi77, hxi88, hxi99, hxi110] at hsplit
    have htot : ∑ b ∈ Finset.range 121, Complex.exp (((2*Real.pi*(a:ℝ)*b/121:ℝ):ℂ)*Complex.I) = 0 := by
      rw [Finset.sum_congr rfl (fun b _ => hterm b)]
      exact hgeon
    rw [htot, hpsum, add_zero] at hsplit
    exact hsplit
  rw [hunits]

