import Mathlib

/-!
# L-goldbach-cert-72

The Ramanujan certificate for modulus 72 = 2^3·3^2: not squarefree, so the
character sum vanishes. The coprime power of the primitive root keeps the
full residue geometric sum at zero; the non-unit residues split into the evens
(powers of a primitive 36th root) and the odd multiples of 3 (a primitive 12th root
times a unit factor), both summing to zero; division by the totient 24 leaves 0/24.
-/

set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.L_goldbach_cert_72 :
    ∀ a:ℕ, Nat.Coprime a 72 → (∑ b ∈ (Finset.range 72).filter (fun b => Nat.Coprime b 72), Complex.exp (((2*Real.pi*(a:ℝ)*b/72:ℝ):ℂ)*Complex.I))/(24:ℂ)=(0:ℂ)/24 := by
  intro a hca
  have hca1 : Nat.Coprime a 36 := hca.of_dvd_right (by norm_num : (36:ℕ) ∣ 72)
  have hca2 : Nat.Coprime a 12 := hca.of_dvd_right (by norm_num : (12:ℕ) ∣ 72)
  set ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(72:ℚ))) with hξ
  set ω1 : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(36:ℚ))) with hω1
  set ω2 : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(12:ℚ))) with hω2
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/72:ℝ):ℂ)*Complex.I) = ξ^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/72:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(72:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hξ]
  have hprimm : IsPrimitiveRoot ξ 72 := by
    rw [hξ]; exact Complex.isPrimitiveRoot_exp_of_coprime a 72 (by norm_num) hca
  have hprim1 : IsPrimitiveRoot ω1 36 := by
    rw [hω1]; exact Complex.isPrimitiveRoot_exp_of_coprime a 36 (by norm_num) hca1
  have hprim2 : IsPrimitiveRoot ω2 12 := by
    rw [hω2]; exact Complex.isPrimitiveRoot_exp_of_coprime a 12 (by norm_num) hca2
  have hxi2 : ξ^2 = ω1 := by
    rw [hξ, hω1, ← Complex.exp_nat_mul]
    have hc : ((2:ℕ):ℂ) * (2 * Real.pi * Complex.I * ((a:ℚ)/(72:ℚ))) = 2 * Real.pi * Complex.I * ((a:ℚ)/(36:ℚ)) := by
      push_cast
      field_simp
      ring
    rw [hc]
  have hxiq : ξ^6 = ω2 := by
    rw [hξ, hω2, ← Complex.exp_nat_mul]
    have hc : ((6:ℕ):ℂ) * (2 * Real.pi * Complex.I * ((a:ℚ)/(72:ℚ))) = 2 * Real.pi * Complex.I * ((a:ℚ)/(12:ℚ)) := by
      push_cast
      field_simp
      ring
    rw [hc]
  have htot : ∑ b ∈ Finset.range 72, ξ^b = 0 :=
    IsPrimitiveRoot.geom_sum_eq_zero hprimm (by norm_num)
  have hnu : (Finset.range 72).filter (fun b => ¬ Nat.Coprime b 72)
      = (Finset.range 36).image (fun k => 2*k) ∪ (Finset.range 12).image (fun k => 6*k+3) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨p, hp, hpb, hp72⟩ := Nat.Prime.not_coprime_iff_dvd.mp h2
      have hmf : p ∣ 8 * 9 := by rw [show (8:ℕ) * 9 = 72 from by norm_num]; exact hp72
      have hp23 : p = 2 ∨ p = 3 := by
        have htwo : 2 ≤ p := hp.two_le
        rcases (Nat.Prime.dvd_mul hp).mp hmf with hdu | hdv
        · have hp2 : p ∣ 2 := by
            rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 4 by rw [show (2:ℕ) * 4 = 8 from by norm_num]; exact hdu) with hL1 | hR1
            · exact hL1
            · rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 2 by rw [show (2:ℕ) * 2 = 4 from by norm_num]; exact hR1) with hL2 | hR2
              · exact hL2
              · exact hR2
          have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2
          omega
        · have hpq : p ∣ 3 := by
            rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 3 * 3 by rw [show (3:ℕ) * 3 = 9 from by norm_num]; exact hdv) with hL3 | hR3
            · exact hL3
            · exact hR3
          have hple : p ≤ 3 := Nat.le_of_dvd (by norm_num) hpq
          omega
      rcases hp23 with rfl | rfl
      · exact Or.inl ⟨b/2, by omega, by omega⟩
      · by_cases hd2 : (2:ℕ) ∣ b
        · exact Or.inl ⟨b/2, by omega, by omega⟩
        · exact Or.inr ⟨(b-3)/6, by omega, by omega⟩
    · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨2, by decide, by omega, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨3, by decide, by omega, by norm_num⟩⟩
  have hdisj : Disjoint ((Finset.range 36).image (fun k => 2*k)) ((Finset.range 12).image (fun k => 6*k+3)) := by
    rw [Finset.disjoint_right]
    intro x hx hxs
    simp only [Finset.mem_image, Finset.mem_range] at hx hxs
    obtain ⟨k2, _, rfl⟩ := hx
    obtain ⟨k1, _, hk1⟩ := hxs
    omega
  have hA : ∑ b ∈ (Finset.range 36).image (fun k => 2*k), ξ^b = 0 := by
    rw [Finset.sum_image (by intro x _ y _ h; have h' : 2 * x = 2 * y := h; omega)]
    have hh : ∀ k, ξ^(2*k) = ω1^k := by
      intro k
      rw [pow_mul, hxi2]
    simp only [hh]
    exact IsPrimitiveRoot.geom_sum_eq_zero hprim1 (by norm_num)
  have hB : ∑ b ∈ (Finset.range 12).image (fun k => 6*k+3), ξ^b = 0 := by
    rw [Finset.sum_image (by intro x _ y _ h; have h' : 6 * x + 3 = 6 * y + 3 := h; omega)]
    have h3 : ∀ k ∈ Finset.range 12, ξ^(6*k+3) = ω2^k * ξ^3 := by
      intro k _
      rw [pow_add, pow_mul, hxiq]
    have h4 : ∑ k ∈ Finset.range 12, ξ^(6*k+3) = (∑ k ∈ Finset.range 12, ω2^k) * ξ^3 := by
      rw [Finset.sum_congr rfl h3, Finset.sum_mul]
    rw [h4, IsPrimitiveRoot.geom_sum_eq_zero hprim2 (by norm_num), zero_mul]
  have hnonu : ∑ b ∈ (Finset.range 72).filter (fun b => ¬ Nat.Coprime b 72), ξ^b = 0 := by
    rw [hnu, Finset.sum_union hdisj, hA, hB, add_zero]
  have hsplit : ∑ b ∈ (Finset.range 72).filter (fun b => Nat.Coprime b 72), ξ^b
      + ∑ b ∈ (Finset.range 72).filter (fun b => ¬ Nat.Coprime b 72), ξ^b
      = ∑ b ∈ Finset.range 72, ξ^b :=
    Finset.sum_filter_add_sum_filter_not (Finset.range 72) (fun b => Nat.Coprime b 72) (fun b => ξ^b)
  rw [htot, hnonu, add_zero] at hsplit
  simp only [hterm]
  rw [hsplit, zero_div]

