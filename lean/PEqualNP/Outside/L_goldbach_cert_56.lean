import Mathlib

/-!
# L-goldbach-cert-56

The Ramanujan certificate for the modulus `56`, which is divisible by `4` and
therefore not squarefree: the expected coefficient is `μ(56) = 0`.

`exp(2πi·a/56)` is a primitive `56`-th root of unity because `a` is coprime to
`56`. Its `28`-th power (the half turn) is `-1`. Translation by the half turn
sends a unit `b < 56/2` to the unit `b + 28`, and the two summands cancel. The
normalised sum over all units is `0/24`.
-/

theorem PEqualNP.Outside.L_goldbach_cert_56 :
    ∀ a:ℕ, Nat.Coprime a 56 → (∑ b ∈ (Finset.range 56).filter (fun b => Nat.Coprime b 56), Complex.exp (((2*Real.pi*(a:ℝ)*b/56:ℝ):ℂ)*Complex.I))/(24:ℂ)=(0:ℂ)/24 := by
  intro a ha
  set U : Finset ℕ := (Finset.range 56).filter (fun b => Nat.Coprime b 56) with hU
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a:ℚ)/(56:ℚ))) with hω
  have hprim : IsPrimitiveRoot ω 56 := by
    rw [hω]
    exact Complex.isPrimitiveRoot_exp_of_coprime a 56 (by norm_num) ha
  have hterm : ∀ b:ℕ, Complex.exp (((2*Real.pi*(a:ℝ)*b/56:ℝ):ℂ)*Complex.I) = ω^b := by
    intro b
    have hb : ((2*Real.pi*(a:ℝ)*b/56:ℝ):ℂ) * Complex.I = ((b:ℂ)) * (2 * Real.pi * Complex.I * ((a:ℚ)/(56:ℚ))) := by
      push_cast
      ring_nf
    rw [hb, Complex.exp_nat_mul, hω]
  -- The half turn is `-1`: its square is `ω^56 = 1`, and it is not `1` because the half turn is smaller.
  have hhalf : ω^28 = -1 := by
    have hne : ω^28 ≠ 1 := by
      intro he
      have hdvd : (56:ℕ) ∣ 28 := (hprim.pow_eq_one_iff_dvd 28).mp he
      norm_num at hdvd
    have hfac : (ω^28 - 1) * (ω^28 + 1) = 0 := by
      linear_combination hprim.pow_eq_one
    have hzero : ω^28 + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
    linear_combination hzero
  -- Split the units at the half turn, and pair each lower unit with its translate.
  set S : Finset ℕ := U.filter (fun b => b < 28) with hS
  set T : Finset ℕ := U.filter (fun b => 28 ≤ b) with hT
  have hsplit : U = S ∪ T := by
    ext b
    simp only [hS, hT, Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      by_cases hc : b < 28
      · exact Or.inl ⟨h, hc⟩
      · exact Or.inr ⟨h, by omega⟩
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
  have hdisj : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro b hb hb'
    simp only [hS, Finset.mem_filter] at hb
    simp only [hT, Finset.mem_filter] at hb'
    omega
  have himg : T = S.image (fun b => b + 28) := by decide
  have hsumT : (∑ b ∈ T, ω^b) = ω^28 * (∑ b ∈ S, ω^b) := by
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
  have hcongr : (∑ b ∈ U, Complex.exp (((2*Real.pi*(a:ℝ)*b/56:ℝ):ℂ)*Complex.I)) = ∑ b ∈ U, ω^b :=
    Finset.sum_congr rfl (fun b _ => hterm b)
  rw [hcongr, htotal]
