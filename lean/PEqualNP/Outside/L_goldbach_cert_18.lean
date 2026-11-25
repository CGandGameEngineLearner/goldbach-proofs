import Mathlib

/-- Ramanujan sum over the units modulo `18`: for any `ω` that is a primitive `18`-th root of unity
(in practice `ω = exp (2πia/18)` with `gcd a 18 = 1`), the sum of `ω ^ b` over the unit classes
`b ∈ {1,5,7,11,13,17}` vanishes, i.e. it equals `μ(18) = 0` because `18 = 2 * 3 ^ 2` is not
squarefree.

The proof is the Möbius identity in disguise: `x ^ 9 + 1 = (x ^ 3 + 1) * Φ₁₈(x ^ 3)` with
`Φ₁₈(y) = y ^ 2 - y + 1`, so `ω ^ 6 - ω ^ 3 + 1 = 0`, together with `ω ^ 9 = -1`; the six unit
powers then collapse to `ω ^ 5 - ω ^ 2 - ω ^ 8 = 0`. -/
private lemma goldbach_cert_18_units (ω : ℂ) (h6' : ω ^ 6 = ω ^ 3 - 1) (h9 : ω ^ 9 = -1) :
    ∑ b ∈ (Finset.range 18).filter (fun b => Nat.Coprime b 18), ω ^ b = 0 := by
  -- The unit classes modulo `18` are `{1, 5, 7, 11, 13, 17}` (`φ(18) = 6`).
  have hset : (Finset.range 18).filter (fun b => Nat.Coprime b 18) = {1, 5, 7, 11, 13, 17} := by
    decide
  rw [hset]
  have hsum : ∑ b ∈ ({1, 5, 7, 11, 13, 17} : Finset ℕ), ω ^ b
      = ω + ω ^ 5 + ω ^ 7 + ω ^ 11 + ω ^ 13 + ω ^ 17 := by
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  rw [hsum]
  -- `ω ^ 9 = -1` halves the exponent range (`ω ^ (b + 9) = -ω ^ b`).
  have h11 : ω ^ 11 = -ω ^ 2 := by
    rw [show (11 : ℕ) = 2 + 9 by norm_num, pow_add, h9]
    ring
  have h13 : ω ^ 13 = -ω ^ 4 := by
    rw [show (13 : ℕ) = 4 + 9 by norm_num, pow_add, h9]
    ring
  have h17 : ω ^ 17 = -ω ^ 8 := by
    rw [show (17 : ℕ) = 8 + 9 by norm_num, pow_add, h9]
    ring
  -- `ω ^ 6 = ω ^ 3 - 1` (Möbius: `Φ₁₈(ω) = 0`) collapses the remaining powers.
  have h7 : ω ^ 7 = ω ^ 4 - ω := by
    rw [show (7 : ℕ) = 6 + 1 by norm_num, pow_add, h6']
    ring
  have h8 : ω ^ 8 = ω ^ 5 - ω ^ 2 := by
    rw [show (8 : ℕ) = 6 + 2 by norm_num, pow_add, h6']
    ring
  rw [h7, h11, h13, h17, h8]
  ring

theorem PEqualNP.Outside.L_goldbach_cert_18 :
    ∀ a:ℕ, Nat.Coprime a 18 → (∑ b ∈ (Finset.range 18).filter (fun b => Nat.Coprime b 18), Complex.exp (((2*Real.pi*(a:ℝ)*b/18:ℝ):ℂ)*Complex.I))/(6:ℂ)=(0:ℂ)/6 := by
  intro a ha
  -- `ω = exp (2πia/18)` is a primitive `18`-th root of unity, since `gcd a 18 = 1`.
  set ω : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 18)) with hωdef
  have hω : IsPrimitiveRoot ω 18 := by
    rw [hωdef]
    exact Complex.isPrimitiveRoot_exp_of_coprime a 18 (by norm_num) ha
  have h18 : ω ^ 18 = 1 := hω.pow_eq_one
  -- `ω ^ 9 = -1`, since `ω ^ 9 ≠ 1` but `(ω ^ 9) ^ 2 = ω ^ 18 = 1`.
  have h9 : ω ^ 9 = -1 := by
    have hne : ω ^ 9 ≠ 1 := by
      intro h
      have hdvd : (18 : ℕ) ∣ 9 := (hω.pow_eq_one_iff_dvd 9).mp h
      norm_num at hdvd
    have hfac : (ω ^ 9 - 1) * (ω ^ 9 + 1) = 0 := by
      linear_combination h18
    have : ω ^ 9 + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hne)
    linear_combination this
  -- `ω ^ 3 ≠ -1` (else `ω ^ 6 = 1`, i.e. `18 ∣ 6`), so `x ^ 3 + 1` does not vanish at `ω ^ 3`.
  have h3 : ω ^ 3 + 1 ≠ 0 := by
    intro h
    have h3' : ω ^ 3 = -1 := by linear_combination h
    have h6 : ω ^ 6 = 1 := by
      rw [show (6 : ℕ) = 3 + 3 by norm_num, pow_add, h3']
      ring
    have hdvd : (18 : ℕ) ∣ 6 := (hω.pow_eq_one_iff_dvd 6).mp h6
    norm_num at hdvd
  -- `Φ₁₈(ω ^ 3) = 0` from `(ω ^ 3 + 1) * (ω ^ 6 - ω ^ 3 + 1) = ω ^ 9 + 1 = 0`.
  have h6 : ω ^ 6 = ω ^ 3 - 1 := by
    have hfac : (ω ^ 3 + 1) * (ω ^ 6 - ω ^ 3 + 1) = 0 := by
      linear_combination h9
    have hphi : ω ^ 6 - ω ^ 3 + 1 = 0 := (mul_eq_zero.mp hfac).resolve_left h3
    linear_combination hphi
  -- Each summand is a power of `ω`: the frequency numerator `a` stays arbitrary.
  have hterm : ∀ b : ℕ,
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 18 : ℝ) : ℂ) * Complex.I) = ω ^ b := by
    intro b
    have harg : (((2 * Real.pi * (a : ℝ) * b / 18 : ℝ) : ℂ) * Complex.I)
        = (b : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 18)) := by
      push_cast
      ring
    rw [harg, hωdef, ← Complex.exp_nat_mul]
  simp_rw [hterm]
  rw [goldbach_cert_18_units ω h6 h9]
