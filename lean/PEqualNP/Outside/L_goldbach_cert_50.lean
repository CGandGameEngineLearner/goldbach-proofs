import Mathlib

namespace PEqualNP.Outside

/-- The units modulo 50 form four complete five-term geometric progressions. -/
theorem L_goldbach_cert_50 :
    ∀ a:ℕ, Nat.Coprime a 50 → (∑ b ∈ (Finset.range 50).filter (fun b => Nat.Coprime b 50), Complex.exp (((2*Real.pi*(a:ℝ)*b/50:ℝ):ℂ)*Complex.I))/(20:ℂ)=(0:ℂ)/20 := by
  intro a ha
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / 50))
  have hz : IsPrimitiveRoot z 50 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 50 (by norm_num) ha
  have hz10 : IsPrimitiveRoot (z ^ 10) 5 :=
    IsPrimitiveRoot.pow (by norm_num : 0 < (50 : ℕ)) hz (by norm_num)
  have hgeom : ∑ j ∈ Finset.range 5, (z ^ 10) ^ j = 0 :=
    hz10.geom_sum_eq_zero (by norm_num)
  have hexp (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 50 : ℝ) : ℂ) * Complex.I)
        = z ^ b := by
    calc
      _ = Complex.exp ((b : ℂ) * (2 * Real.pi * Complex.I * ((a : ℂ) / 50))) := by
        apply congrArg Complex.exp
        push_cast
        ring
      _ = z ^ b := Complex.exp_nat_mul _ b
  simp_rw [hexp]
  have hfactor :
      (∑ b ∈ (Finset.range 50).filter (fun b => Nat.Coprime b 50), z ^ b)
        = (z + z ^ 3 + z ^ 7 + z ^ 9) *
          (∑ j ∈ Finset.range 5, (z ^ 10) ^ j) := by
    norm_num [Finset.sum_filter, Finset.sum_range_succ, Nat.Coprime]
    ring
  rw [hfactor, hgeom, mul_zero]

end PEqualNP.Outside
