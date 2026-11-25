import Mathlib

/-!
# L-goldbach-cert-128

The Ramanujan certificate for the modulus `128 = 2^7`, whose Möbius value is `0`.

`exp(2πi·a/128)` is a primitive `128`-th root of unity when `a` is odd, so its
`64`-th power is `-1`. Because `4 ∣ 128`, translating a unit `b` by `64` keeps it
a unit (`64` is even and carries every odd prime factor of `128`), and the
translate has the opposite sign. The units therefore cancel in pairs and the
normalized sum is `0/64`, as `μ(128) = 0` requires.
-/

theorem PEqualNP.Outside.L_goldbach_cert_128 :
    ∀ a:ℕ, Nat.Coprime a 128 → (∑ b ∈ (Finset.range 128).filter (fun b => Nat.Coprime b 128), Complex.exp (((2*Real.pi*(a:ℝ)*b/128:ℝ):ℂ)*Complex.I))/(64:ℂ)=(0:ℂ)/64 := by
  intro a ha
  set U : Finset ℕ := (Finset.range 128).filter (fun b => Nat.Coprime b 128) with hU
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(128:ℚ))) with hω
  have hprim : IsPrimitiveRoot ω 128 := by
    rw [hω]
    exact Complex.isPrimitiveRoot_exp_of_coprime a 128 (by norm_num) ha
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/128:ℝ):ℂ)*Complex.I) = ω^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/128:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(128:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hω]
  -- The half turn is `-1`: its square is `ω^128 = 1`, and it is not `1` because `64 < 128`.
  have hhalf : ω^64 = -1 := by
    have hne : ω^64 ≠ 1 := by
      intro he
      have hdvd : (128:ℕ) ∣ 64 := (hprim.pow_eq_one_iff_dvd 64).mp he
      norm_num at hdvd
    have hfac : (ω^64 - 1) * (ω^64 + 1) = 0 := by
      linear_combination hprim.pow_eq_one
    have hzero : ω^64 + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
    linear_combination hzero
  -- Split the units at the half turn, and pair each lower unit with its translate.
  set S : Finset ℕ := U.filter (fun b => b < 64) with hS
  set T : Finset ℕ := U.filter (fun b => 64 ≤ b) with hT
  have hsplit : U = S ∪ T := by
    ext b
    simp only [hS, hT, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      by_cases hc : b < 64
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, by omega⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    simp only [hS, Finset.mem_filter] at hb
    simp only [hT, Finset.mem_filter] at hb'
    omega
  have himg : T = S.image (fun b => b + 64) := by decide
  have hsumT : (∑ b ∈ T, ω^b) = ω^64 * (∑ b ∈ S, ω^b) := by
    rw [himg, Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [pow_add]
      ring
    · intro x _ y _ hxy
      exact Nat.add_right_cancel hxy
  have htotal : (∑ b ∈ U, ω^b) = 0 := by
    rw [hsplit, Finset.sum_union hdisj, hsumT, hhalf]
    ring
  have hcongr : (∑ b ∈ U, Complex.exp (((2*Real.pi*(a:ℝ)*b/128:ℝ):ℂ)*Complex.I)) = ∑ b ∈ U, ω^b :=
    Finset.sum_congr rfl (fun b _ => hterm b)
  rw [hcongr, htotal]
