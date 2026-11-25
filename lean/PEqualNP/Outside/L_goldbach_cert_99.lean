import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

theorem L_goldbach_cert_99 :
    ∀ a:ℕ, Nat.Coprime a 99 → (∑ b ∈ (Finset.range 99).filter (fun b => Nat.Coprime b 99), Complex.exp (((2*Real.pi*(a:ℝ)*b/99:ℝ):ℂ)*Complex.I))/(60:ℂ)=(0:ℂ)/60 := by
  intro a ha
  let θ : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 99)
  let z := Complex.exp θ
  have hz : IsPrimitiveRoot z 99 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 99 (by decide) ha
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 99 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    calc
      Complex.exp _ = Complex.exp ((b : ℂ) * θ) := by
        apply congrArg Complex.exp
        dsimp only [θ]
        push_cast
        ring
      _ = z ^ b := Complex.exp_nat_mul θ b
  -- Both moduli have the same prime factors, so the filter is periodic modulo 33.
  have coprime_iff (b : ℕ) : Nat.Coprime b 99 ↔ Nat.Coprime b 33 := by
    change Nat.Coprime b (3 ^ 2 * 11) ↔ Nat.Coprime b (3 * 11)
    simp only [Nat.coprime_mul_iff_right, Nat.coprime_pow_right_iff (by decide : 0 < 2)]
  let f : ℕ → ℂ := fun b => if Nat.Coprime b 33 then z ^ b else 0
  have shift (k b : ℕ) : f (k * 33 + b) = z ^ (k * 33) * f b := by
    simp only [f, Nat.coprime_mul_right_add_left, pow_add, mul_ite, mul_zero]
  have shift33 (b : ℕ) : f (33 + b) = z ^ 33 * f b := shift 1 b
  have shift66 (b : ℕ) : f (66 + b) = z ^ 66 * f b := shift 2 b
  have hz3 : IsPrimitiveRoot (z ^ 33) 3 :=
    IsPrimitiveRoot.pow (a := 33) (b := 3) (by decide) hz (by decide)
  have geometric : 1 + z ^ 33 + z ^ 66 = 0 := by
    have h := hz3.geom_sum_eq_zero (by decide)
    norm_num [Finset.sum_range_succ, ← pow_mul] at h
    exact h
  simp_rw [phase]
  suffices (∑ b ∈ (Finset.range 99).filter (fun b => Nat.Coprime b 99), z ^ b) = 0 by
    rw [this]
  rw [Finset.sum_filter]
  simp_rw [coprime_iff]
  change (∑ b ∈ Finset.range 99, f b) = 0
  calc
    _ = (∑ b ∈ Finset.range 33, f b) + (∑ b ∈ Finset.range 33, f (33 + b)) +
        (∑ b ∈ Finset.range 33, f (66 + b)) :=
      (Finset.sum_range_add f 66 33).trans
        (congrArg (fun t : ℂ => t + ∑ b ∈ Finset.range 33, f (66 + b))
          (Finset.sum_range_add f 33 33))
    _ = ∑ b ∈ Finset.range 33, (f b + f (33 + b) + f (66 + b)) := by
      simp only [Finset.sum_add_distrib]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      rw [shift33, shift66]
      calc
        _ = (1 + z ^ 33 + z ^ 66) * f b := by ring
        _ = 0 := by rw [geometric, zero_mul]

end PEqualNP.Outside
