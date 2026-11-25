import Mathlib

namespace PEqualNP.Outside

/-- Inclusion-exclusion for multiples of 3 and 19 evaluates the unit-residue sum. -/
theorem L_goldbach_cert_57 :
    ∀ a:ℕ, Nat.Coprime a 57 → (∑ b ∈ (Finset.range 57).filter (fun b => Nat.Coprime b 57), Complex.exp (((2*Real.pi*(a:ℝ)*b/57:ℝ):ℂ)*Complex.I))/(36:ℂ)=(1:ℂ)/36 := by
  intro a ha
  let z : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / 57))
  have hz : IsPrimitiveRoot z 57 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 57 (by norm_num) ha
  have hz3 : IsPrimitiveRoot (z ^ 3) 19 :=
    IsPrimitiveRoot.pow (by norm_num : 0 < (57 : ℕ)) hz (by norm_num)
  have hz19 : IsPrimitiveRoot (z ^ 19) 3 :=
    IsPrimitiveRoot.pow (by norm_num : 0 < (57 : ℕ)) hz (by norm_num)
  have hgeom : ∑ j ∈ Finset.range 57, z ^ j = 0 :=
    hz.geom_sum_eq_zero (by norm_num)
  have hgeom3 : ∑ j ∈ Finset.range 19, (z ^ 3) ^ j = 0 :=
    hz3.geom_sum_eq_zero (by norm_num)
  have hgeom19 : ∑ j ∈ Finset.range 3, (z ^ 19) ^ j = 0 :=
    hz19.geom_sum_eq_zero (by norm_num)
  have hexp (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 57 : ℝ) : ℂ) * Complex.I)
        = z ^ b := by
    calc
      _ = Complex.exp ((b : ℂ) * (2 * Real.pi * Complex.I * ((a : ℂ) / 57))) := by
        apply congrArg Complex.exp
        push_cast
        ring
      _ = z ^ b := Complex.exp_nat_mul _ b
  simp_rw [hexp]
  have hsum :
      (∑ b ∈ (Finset.range 57).filter (fun b => Nat.Coprime b 57), z ^ b)
        = (∑ j ∈ Finset.range 57, z ^ j) -
          (∑ j ∈ Finset.range 19, (z ^ 3) ^ j) -
          (∑ j ∈ Finset.range 3, (z ^ 19) ^ j) + 1 := by
    norm_num [Finset.sum_filter, Finset.sum_range_succ, Nat.Coprime]
    ring
  rw [hsum, hgeom, hgeom3, hgeom19]
  norm_num

end PEqualNP.Outside
