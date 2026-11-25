import Mathlib

/-!
# L-goldbach-cert-64

The Ramanujan certificate for modulus 64 = 2^6: not squarefree, so the
character sum vanishes. The coprime power of the primitive 64th root keeps the
full residue geometric sum at zero; the non-unit residues (multiples of 2)
run over the powers of a primitive 32th root, which also sum to zero; division
by the totient 32 leaves 0/32.
-/

set_option maxRecDepth 8000 in
theorem PEqualNP.Outside.L_goldbach_cert_64 :
    ∀ a:ℕ, Nat.Coprime a 64 → (∑ b ∈ (Finset.range 64).filter (fun b => Nat.Coprime b 64), Complex.exp (((2*Real.pi*(a:ℝ)*b/64:ℝ):ℂ)*Complex.I))/(32:ℂ)=(0:ℂ)/32 := by
  intro a hca
  have hcam : Nat.Coprime a 32 := hca.of_dvd_right (by norm_num : (32:ℕ) ∣ 64)
  set ξ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(64:ℚ))) with hξ
  set η : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(32:ℚ))) with hη
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/64:ℝ):ℂ)*Complex.I) = ξ^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/64:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(64:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hξ]
  have hprimn : IsPrimitiveRoot ξ 64 := by
    rw [hξ]; exact Complex.isPrimitiveRoot_exp_of_coprime a 64 (by norm_num) hca
  have hprimm : IsPrimitiveRoot η 32 := by
    rw [hη]; exact Complex.isPrimitiveRoot_exp_of_coprime a 32 (by norm_num) hcam
  have hgeon : ∑ b ∈ Finset.range 64, ξ^b = 0 := hprimn.geom_sum_eq_zero (by norm_num)
  have hxi2 : ξ^2 = η := by
    rw [hξ, hη, ← Complex.exp_nat_mul]
    have hc : ((2:ℕ):ℂ) * (2 * Real.pi * Complex.I * ((a:ℚ)/(64:ℚ))) = 2 * Real.pi * Complex.I * ((a:ℚ)/(32:ℚ)) := by
      push_cast
      field_simp
      ring
    rw [hc]
  have hp : Nat.Prime 2 := by decide
  have hnu : (Finset.range 64).filter (fun b => ¬ Nat.Coprime b 64) = (Finset.range 32).image (fun k => 2*k) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      have hpb : (2:ℕ) ∣ b := by
        by_contra hpnb
        exact h2 (by rw [show (64:ℕ) = 2^6 from by norm_num]; exact Nat.Prime.coprime_pow_of_not_dvd hp hpnb)
      obtain ⟨k, hk⟩ := hpb
      refine ⟨k, ?_, by omega⟩
      omega
    · rintro ⟨k, hk1, rfl⟩
      refine ⟨by omega, ?_⟩
      exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨2, hp, by norm_num, by norm_num⟩
  have hinj : Set.InjOn (fun k => 2*k) (Finset.range 32) := by
    intro k1 hk1 k2 hk2 hk
    simp only [Finset.mem_coe, Finset.mem_range] at hk1 hk2
    have hk' : 2*k1 = 2*k2 := hk
    omega
  have hnonu : (∑ b ∈ (Finset.range 64).filter (fun b => ¬ Nat.Coprime b 64), Complex.exp (((2*Real.pi*(a:ℝ)*b/64:ℝ):ℂ)*Complex.I)) = 0 := by
    rw [hnu, Finset.sum_image hinj]
    have hconv : ∀ k ∈ Finset.range 32, Complex.exp (((2*Real.pi*(a:ℝ)*((2*k:ℕ):ℝ)/64:ℝ):ℂ)*Complex.I) = η^k := by
      intro k _
      rw [hterm (2*k)]
      have hpk : ξ^(2*k) = (ξ^2)^k := pow_mul ξ 2 k
      rw [hpk, hxi2]
    rw [Finset.sum_congr rfl hconv]
    exact hprimm.geom_sum_eq_zero (by norm_num : 1 < 32)
  have hunits : (∑ b ∈ (Finset.range 64).filter (fun b => Nat.Coprime b 64), Complex.exp (((2*Real.pi*(a:ℝ)*b/64:ℝ):ℂ)*Complex.I)) = 0 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.range 64) (p := fun b => Nat.Coprime b 64) (f := fun b => Complex.exp (((2*Real.pi*(a:ℝ)*b/64:ℝ):ℂ)*Complex.I))
    have htot : ∑ b ∈ Finset.range 64, Complex.exp (((2*Real.pi*(a:ℝ)*b/64:ℝ):ℂ)*Complex.I) = 0 := by
      rw [Finset.sum_congr rfl (fun b _ => hterm b)]
      exact hgeon
    rw [hnonu, htot, add_zero] at hsplit
    exact hsplit
  rw [hunits, zero_div]

