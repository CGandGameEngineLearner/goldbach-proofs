import Mathlib

/-!
# L-goldbach-cert-125

The Ramanujan certificate for modulus 125 = 5^3: not squarefree, so the
character sum vanishes. The coprime power of the primitive 125th root keeps the
full residue geometric sum at zero; the non-unit residues (multiples of 5)
run over the powers of a primitive 25th root, which also sum to zero; division
by the totient 100 leaves 0/100.
-/

set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.L_goldbach_cert_125 :
    ∀ a:ℕ, Nat.Coprime a 125 → (∑ b ∈ (Finset.range 125).filter (fun b => Nat.Coprime b 125), Complex.exp (((2*Real.pi*(a:ℝ)*b/125:ℝ):ℂ)*Complex.I))/(100:ℂ)=(0:ℂ)/100 := by
  intro a hca
  have hcam : Nat.Coprime a 25 := hca.of_dvd_right (by norm_num : (25:ℕ) ∣ 125)
  set ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(125:ℚ))) with hξ
  set η : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(25:ℚ))) with hη
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/125:ℝ):ℂ)*Complex.I) = ξ^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/125:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(125:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hξ]
  have hprimn : IsPrimitiveRoot ξ 125 := by
    rw [hξ]; exact Complex.isPrimitiveRoot_exp_of_coprime a 125 (by norm_num) hca
  have hprimm : IsPrimitiveRoot η 25 := by
    rw [hη]; exact Complex.isPrimitiveRoot_exp_of_coprime a 25 (by norm_num) hcam
  have hgeon : ∑ b ∈ Finset.range 125, ξ^b = 0 := hprimn.geom_sum_eq_zero (by norm_num)
  have hxi5 : ξ^5 = η := by
    rw [hξ, hη, ← Complex.exp_nat_mul]
    have hc : ((5:ℕ):ℂ) * (2 * Real.pi * Complex.I * ((a:ℚ)/(125:ℚ))) = 2 * Real.pi * Complex.I * ((a:ℚ)/(25:ℚ)) := by
      push_cast
      field_simp
      ring
    rw [hc]
  have hp : Nat.Prime 5 := by decide
  have hnu : (Finset.range 125).filter (fun b => ¬ Nat.Coprime b 125) = (Finset.range 25).image (fun k => 5*k) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      have hpb : (5:ℕ) ∣ b := by
        by_contra hpnb
        exact h2 (by rw [show (125:ℕ) = 5^3 from by norm_num]; exact Nat.Prime.coprime_pow_of_not_dvd hp hpnb)
      obtain ⟨k, hk⟩ := hpb
      refine ⟨k, ?_, by omega⟩
      omega
    · rintro ⟨k, hk1, rfl⟩
      refine ⟨by omega, ?_⟩
      exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨5, hp, by norm_num, by norm_num⟩
  have hinj : Set.InjOn (fun k => 5*k) (Finset.range 25) := by
    intro k1 hk1 k2 hk2 hk
    simp only [Finset.mem_coe, Finset.mem_range] at hk1 hk2
    have hk' : 5*k1 = 5*k2 := hk
    omega
  have hnonu : (∑ b ∈ (Finset.range 125).filter (fun b => ¬ Nat.Coprime b 125), Complex.exp (((2*Real.pi*(a:ℝ)*b/125:ℝ):ℂ)*Complex.I)) = 0 := by
    rw [hnu, Finset.sum_image hinj]
    have hconv : ∀ k ∈ Finset.range 25, Complex.exp (((2*Real.pi*(a:ℝ)*((5*k:ℕ):ℝ)/125:ℝ):ℂ)*Complex.I) = η^k := by
      intro k _
      rw [hterm (5*k)]
      have hpk : ξ^(5*k) = (ξ^5)^k := pow_mul ξ 5 k
      rw [hpk, hxi5]
    rw [Finset.sum_congr rfl hconv]
    exact hprimm.geom_sum_eq_zero (by norm_num : 1 < 25)
  have hunits : (∑ b ∈ (Finset.range 125).filter (fun b => Nat.Coprime b 125), Complex.exp (((2*Real.pi*(a:ℝ)*b/125:ℝ):ℂ)*Complex.I)) = 0 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range 125) (p := fun b => Nat.Coprime b 125) (f := fun b => Complex.exp (((2*Real.pi*(a:ℝ)*b/125:ℝ):ℂ)*Complex.I))
    have htot : ∑ b ∈ Finset.range 125, Complex.exp (((2*Real.pi*(a:ℝ)*b/125:ℝ):ℂ)*Complex.I) = 0 := by
      rw [Finset.sum_congr rfl (fun b _ => hterm b)]
      exact hgeon
    rw [hnonu, htot, add_zero] at hsplit
    exact hsplit
  rw [hunits, zero_div]

