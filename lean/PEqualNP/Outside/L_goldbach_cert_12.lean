import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_goldbach_cert_12 :
    ∀ a:ℕ, Nat.Coprime a 12 → (∑ b ∈ (Finset.range 12).filter (fun b => Nat.Coprime b 12), Complex.exp (((2*Real.pi*(a:ℝ)*b/12:ℝ):ℂ)*Complex.I))/(4:ℂ)=(0:ℂ)/4 := by
  intro a ha
  -- The Ramanujan sum modulo `12` is `∑_{b coprime to 12} exp(2*pi*I*a*b/12)`. Since
  -- `12 = 2 ^ 2 * 3` is not squarefree, its Möbius value is `0`, and the sum over the unit
  -- classes `1, 5, 7, 11` vanishes: with `w = exp(2*pi*I*a/12)` the terms are `w ^ b`, and
  -- `a` odd gives `w ^ 6 = -1`, so `w + w ^ 5 + w ^ 7 + w ^ 11 = (w + w ^ 5) * (1 + w ^ 6) = 0`.
  set w : ℂ := Complex.exp (((2*Real.pi*(a:ℝ)/12:ℝ):ℂ)*Complex.I) with hwdef
  -- `a` is odd, because `Nat.Coprime a 12` gives `Nat.Coprime a (2 ^ 2 * 3)`.
  have hodd : Odd a := by
    have ha' : Nat.Coprime a (2 ^ 2 * 3) := by
      rw [show (2:ℕ) ^ 2 * 3 = 12 by norm_num]
      exact ha
    rw [Nat.coprime_mul_iff_right] at ha'
    have h2 : Nat.Coprime a 2 := (Nat.coprime_pow_right_iff (n := 2) (by norm_num) a 2).mp ha'.1
    simpa using h2
  -- Each term of the sum is a power of `w`.
  have hterm : ∀ b : ℕ,
      Complex.exp (((2*Real.pi*(a:ℝ)*(b:ℝ)/12:ℝ):ℂ)*Complex.I) = w ^ b := by
    intro b
    have harg : ((2*Real.pi*(a:ℝ)*(b:ℝ)/12:ℝ):ℂ) * Complex.I
        = (b:ℂ) * (((2*Real.pi*(a:ℝ)/12:ℝ):ℂ) * Complex.I) := by
      push_cast
      ring
    rw [harg, Complex.exp_nat_mul, ← hwdef]
  -- `w ^ 6 = exp(pi*I*a) = (-1) ^ a = -1`.
  have hw6 : w ^ 6 = -1 := by
    rw [hwdef, ← Complex.exp_nat_mul]
    have h6 : ((6:ℕ):ℂ) * (((2*Real.pi*(a:ℝ)/12:ℝ):ℂ) * Complex.I)
        = (a:ℂ) * ((Real.pi:ℂ) * Complex.I) := by
      push_cast
      ring
    rw [h6, Complex.exp_nat_mul, Complex.exp_pi_mul_I]
    exact hodd.neg_one_pow
  -- `b` is coprime to `12 = 2 ^ 2 * 3` exactly when `b` is odd and not divisible by `3`.
  have hcop : ∀ b : ℕ, Nat.Coprime b 12 ↔ b % 2 = 1 ∧ b % 3 ≠ 0 := by
    intro b
    rw [show (12:ℕ) = 2 ^ 2 * 3 by norm_num, Nat.coprime_mul_iff_right,
      Nat.coprime_pow_right_iff (n := 2) (by norm_num), Nat.coprime_two_right, Nat.odd_iff,
      Nat.coprime_comm, Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero]
  -- The unit classes modulo `12` are exactly `1, 5, 7, 11` (`phi 12 = 4`).
  have hset : (Finset.range 12).filter (fun b => Nat.Coprime b 12) = ({1, 5, 7, 11} : Finset ℕ) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton, hcop]
    constructor
    · rintro ⟨h12, h2, h3⟩
      omega
    · rintro (rfl | rfl | rfl | rfl) <;> decide
  rw [hset, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hterm 1, hterm 5, hterm 7, hterm 11]
  -- `w + w ^ 5 + w ^ 7 + w ^ 11 = (w + w ^ 5) * (1 + w ^ 6) = 0`.
  linear_combination (1 / 4) * (w + w ^ 5) * hw6
