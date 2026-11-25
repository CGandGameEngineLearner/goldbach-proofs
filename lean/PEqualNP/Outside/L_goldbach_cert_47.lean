import Mathlib

/-!
# L-goldbach-cert-47

The Ramanujan certificate for modulus 47: raising the primitive root
exp(2πi/47) to a coprime power a keeps it primitive, so the geometric sum over
all 47 residues vanishes, and removing the non-unit residue 0 leaves
-1; dividing by the totient 46 gives -1/46.
-/

theorem PEqualNP.Outside.L_goldbach_cert_47 :
    ∀ a:ℕ, Nat.Coprime a 47 → (∑ b ∈ (Finset.range 47).filter (fun b => Nat.Coprime b 47), Complex.exp (((2*Real.pi*(a:ℝ)*b/47:ℝ):ℂ)*Complex.I))/(46:ℂ)=(-1:ℂ)/46 := by
  intro a hca
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(47:ℚ))) with hω
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/47:ℝ):ℂ)*Complex.I) = ω^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/47:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(47:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hω]
  have hprim : IsPrimitiveRoot ω 47 := by
    rw [hω]
    exact Complex.isPrimitiveRoot_exp_of_coprime a 47 (by norm_num) hca
  have hgeo : ∑ b ∈ Finset.range 47, ω^b = 0 := hprim.geom_sum_eq_zero (by norm_num)
  have hsum : ∑ b ∈ Finset.range 47, Complex.exp (((2*Real.pi*(a:ℝ)*b/47:ℝ):ℂ)*Complex.I) = 0 := by
    calc (∑ b ∈ Finset.range 47, Complex.exp (((2*Real.pi*(a:ℝ)*b/47:ℝ):ℂ)*Complex.I))
        = ∑ b ∈ Finset.range 47, ω^b := Finset.sum_congr rfl (fun b _ => hterm b)
      _ = 0 := hgeo
  have hp : Nat.Prime 47 := by decide
  have hins : (Finset.range 47) = insert 0 ((Finset.range 47).filter (fun b => Nat.Coprime b 47)) := by
    ext b
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos b with hb | hb
      · exact Or.inl hb
      · refine Or.inr ⟨h, ?_⟩
        have hndvd : ¬ ((47:ℕ) ∣ b) := by
          intro hd
          obtain ⟨k, hk⟩ := hd
          omega
        exact ((hp.coprime_iff_not_dvd).mpr hndvd).symm
    · rintro (rfl | ⟨h, -⟩)
      · omega
      · omega
  have h0n : (0:ℕ) ∉ (Finset.range 47).filter (fun b => Nat.Coprime b 47) := by
    simp [Finset.mem_filter]
  rw [hins, Finset.sum_insert h0n] at hsum
  have h0 : Complex.exp (((2*Real.pi*(a:ℝ)*((0:ℕ):ℝ)/47:ℝ):ℂ)*Complex.I) = 1 := by
    push_cast
    norm_num
  rw [h0] at hsum
  have hunits : (∑ b ∈ (Finset.range 47).filter (fun b => Nat.Coprime b 47), Complex.exp (((2*Real.pi*(a:ℝ)*b/47:ℝ):ℂ)*Complex.I)) = -1 := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hsum
  rw [hunits]

