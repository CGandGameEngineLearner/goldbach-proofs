import Mathlib

set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.L_goldbach_cert_18 : ∀ a:ℕ, Nat.Coprime a 18 → (∑ b ∈ (Finset.range 18).filter (fun b => Nat.Coprime b 18), Complex.exp (((2*Real.pi*(a:ℝ)*b/18:ℝ):ℂ)*Complex.I))/(6:ℂ)=(0:ℂ)/6 := by
  intro a hca
  have hca9 : Nat.Coprime a 9 := hca.of_dvd_right (by norm_num : (9:ℕ) ∣ 18)
  have hca3 : Nat.Coprime a 3 := hca.of_dvd_right (by norm_num : (3:ℕ) ∣ 18)
  set ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(18:ℚ))) with hξ
  set ω9 : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(9:ℚ))) with hω9
  set ω3 : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(3:ℚ))) with hω3
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/18:ℝ):ℂ)*Complex.I) = ξ^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/18:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(18:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hξ]
  have hprim18 : IsPrimitiveRoot ξ 18 := by
    rw [hξ]; exact Complex.isPrimitiveRoot_exp_of_coprime a 18 (by norm_num) hca
  have hprim9 : IsPrimitiveRoot ω9 9 := by
    rw [hω9]; exact Complex.isPrimitiveRoot_exp_of_coprime a 9 (by norm_num) hca9
  have hprim3 : IsPrimitiveRoot ω3 3 := by
    rw [hω3]; exact Complex.isPrimitiveRoot_exp_of_coprime a 3 (by norm_num) hca3
  have hxi2 : ξ^2 = ω9 := by
    rw [hξ, hω9, ← Complex.exp_nat_mul]
    have hc : ((2:ℕ):ℂ) * (2 * Real.pi * Complex.I * ((a:ℚ)/(18:ℚ))) = 2 * Real.pi * Complex.I * ((a:ℚ)/(9:ℚ)) := by
      push_cast
      field_simp
      ring
    rw [hc]
  have hxi6 : ξ^6 = ω3 := by
    rw [hξ, hω3, ← Complex.exp_nat_mul]
    have hc : ((6:ℕ):ℂ) * (2 * Real.pi * Complex.I * ((a:ℚ)/(18:ℚ))) = 2 * Real.pi * Complex.I * ((a:ℚ)/(3:ℚ)) := by
      push_cast
      field_simp
      ring
    rw [hc]
  have htot : ∑ b ∈ Finset.range 18, ξ^b = 0 :=
    IsPrimitiveRoot.geom_sum_eq_zero hprim18 (by norm_num)
  have hnu : (Finset.range 18).filter (fun b => ¬ Nat.Coprime b 18)
      = (Finset.range 9).image (fun k => 2*k) ∪ (Finset.range 3).image (fun k => 6*k+3) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨p, hp, hpb, hp18⟩ := Nat.Prime.not_coprime_iff_dvd.mp h2
      have h29 : p ∣ 2 * 9 := by rw [show (2:ℕ) * 9 = 18 from by norm_num]; exact hp18
      have hp23 : p = 2 ∨ p = 3 := by
        have htwo : 2 ≤ p := hp.two_le
        rcases (Nat.Prime.dvd_mul hp).mp h29 with hd | hd
        · have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
          omega
        · have hd33 : p ∣ 3 * 3 := by rw [show (3:ℕ) * 3 = 9 from by norm_num]; exact hd
          rcases (Nat.Prime.dvd_mul hp).mp hd33 with hd3 | hd3
          · have hple : p ≤ 3 := Nat.le_of_dvd (by norm_num) hd3
            omega
          · have hple : p ≤ 3 := Nat.le_of_dvd (by norm_num) hd3
            omega
      rcases hp23 with rfl | rfl
      · exact Or.inl ⟨b/2, by omega, by omega⟩
      · by_cases hd2 : (2:ℕ) ∣ b
        · exact Or.inl ⟨b/2, by omega, by omega⟩
        · have hb : b = 3 ∨ b = 9 ∨ b = 15 := by omega
          rcases hb with rfl | rfl | rfl
          · exact Or.inr ⟨0, by norm_num, by norm_num⟩
          · exact Or.inr ⟨1, by norm_num, by norm_num⟩
          · exact Or.inr ⟨2, by norm_num, by norm_num⟩
    · rintro (⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩)
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨2, by decide, by omega, by norm_num⟩⟩
      · exact ⟨by omega, Nat.Prime.not_coprime_iff_dvd.mpr ⟨3, by decide, by omega, by norm_num⟩⟩
  have hdisj : Disjoint ((Finset.range 9).image (fun k => 2*k)) ((Finset.range 3).image (fun k => 6*k+3)) := by
    rw [Finset.disjoint_right]
    intro x hx hxs
    simp only [Finset.mem_image, Finset.mem_range] at hx hxs
    obtain ⟨k2, _, rfl⟩ := hx
    obtain ⟨k1, _, hk1⟩ := hxs
    omega
  have hA : ∑ b ∈ (Finset.range 9).image (fun k => 2*k), ξ^b = 0 := by
    rw [Finset.sum_image (by intro x _ y _ h; have h' : 2 * x = 2 * y := h; omega)]
    have h9 : ∀ k, ξ^(2*k) = ω9^k := by
      intro k
      rw [pow_mul, hxi2]
    simp only [h9]
    exact IsPrimitiveRoot.geom_sum_eq_zero hprim9 (by norm_num)
  have hB : ∑ b ∈ (Finset.range 3).image (fun k => 6*k+3), ξ^b = 0 := by
    rw [Finset.sum_image (by intro x _ y _ h; have h' : 6 * x + 3 = 6 * y + 3 := h; omega)]
    have h3 : ∀ k ∈ Finset.range 3, ξ^(6*k+3) = ω3^k * ξ^3 := by
      intro k _
      rw [pow_add, pow_mul, hxi6]
    have h4 : ∑ k ∈ Finset.range 3, ξ^(6*k+3) = (∑ k ∈ Finset.range 3, ω3^k) * ξ^3 := by
      rw [Finset.sum_congr rfl h3, Finset.sum_mul]
    rw [h4, IsPrimitiveRoot.geom_sum_eq_zero hprim3 (by norm_num), zero_mul]
  have hnonu : ∑ b ∈ (Finset.range 18).filter (fun b => ¬ Nat.Coprime b 18), ξ^b = 0 := by
    rw [hnu, Finset.sum_union hdisj, hA, hB, add_zero]
  have hsplit : ∑ b ∈ (Finset.range 18).filter (fun b => Nat.Coprime b 18), ξ^b
      + ∑ b ∈ (Finset.range 18).filter (fun b => ¬ Nat.Coprime b 18), ξ^b
      = ∑ b ∈ Finset.range 18, ξ^b :=
    Finset.sum_filter_add_sum_filter_not (Finset.range 18) (fun b => Nat.Coprime b 18) (fun b => ξ^b)
  rw [htot, hnonu, add_zero] at hsplit
  simp only [hterm]
  rw [hsplit, zero_div]
