import Mathlib

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_goldbach_cert_79 :
    ∀ a : ℕ, Nat.Coprime a 79 →
      (∑ b ∈ (Finset.range 79).filter (fun b => Nat.Coprime b 79),
        Complex.exp (((2 * Real.pi * (a : ℝ) * b / 79 : ℝ) : ℂ) * Complex.I)) /
        (78 : ℂ) = (-1 : ℂ) / 78 := by
  intro a ha
  let t : ℂ := (2 * Real.pi * (a : ℝ) / 79 : ℝ) * Complex.I
  let z := Complex.exp t
  have hz : z ≠ 1 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
    have hi := congrArg Complex.im hk
    simp [t, Complex.mul_im] at hi
    have hp := Real.pi_pos
    have he : (a : ℝ) = 79 * (k : ℝ) := by nlinarith
    have hei : (a : ℤ) = 79 * k := by exact_mod_cast he
    have hd : 79 ∣ a := by
      have hd' : (79 : ℤ) ∣ (a : ℤ) := ⟨k, hei⟩
      exact_mod_cast hd'
    exact (by decide : ¬ (79 : ℕ) ∣ 1) (ha.gcd_eq_one ▸ Nat.dvd_gcd hd (dvd_refl 79))
  have hz79 : z ^ 79 = 1 := by
    change Complex.exp t ^ 79 = 1
    rw [← Complex.exp_nat_mul]
    convert Complex.exp_nat_mul_two_pi_mul_I a using 2
    push_cast
    dsimp [t]
    push_cast
    ring
  have hsum : ∑ b ∈ Finset.range 79, z ^ b = 0 := by
    rw [geom_sum_eq hz, hz79, sub_self, zero_div]
  have hfilter : (Finset.range 79).filter (fun b => Nat.Coprime b 79) =
      (Finset.range 79).erase 0 := by decide
  have hzero : 0 ∈ Finset.range 79 := by decide
  have herase := Finset.sum_erase_add (Finset.range 79) (fun b => z ^ b) hzero
  rw [hsum, pow_zero] at herase
  have hpow (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 79 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    refine (congrArg Complex.exp ?_).trans (Complex.exp_nat_mul t b)
    dsimp [t]
    push_cast
    ring
  simp_rw [hpow]
  rw [hfilter, show (∑ b ∈ (Finset.range 79).erase 0, z ^ b) = -1 by linear_combination herase]
