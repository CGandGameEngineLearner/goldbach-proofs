import Mathlib

namespace PEqualNP.Outside

private lemma app_arg (a b : ℕ) :
    (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 101 : ℝ) : ℂ) * Complex.I)
      = ((a * b : ℕ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 101) := by
  push_cast
  ring

private lemma app_term (a b : ℕ) :
    Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 101 : ℝ) : ℂ) * Complex.I)
      = Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 101) ^ (a * b) := by
  rw [app_arg a b, ← Complex.exp_nat_mul]

theorem L_goldbach_cert_101 (a : ℕ) (ha : Nat.Coprime a 101) :
    (∑ b ∈ (Finset.range 101).filter (fun b => Nat.Coprime b 101),
        Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 101 : ℝ) : ℂ) * Complex.I)) / (100 : ℂ)
      = (-1 : ℂ) / 100 := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 101)) 101 :=
    Complex.isPrimitiveRoot_exp 101 (by norm_num)
  have hfilter :
      (Finset.range 101).filter (fun b => Nat.Coprime b 101) = (Finset.range 101).erase 0 := by
    ext b
    have hP : Nat.Prime 101 := by norm_num
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    constructor
    · rintro ⟨hlt, hc⟩
      refine ⟨?_, hlt⟩
      rintro rfl
      simp at hc
    · rintro ⟨hb0, hlt⟩
      refine ⟨hlt, ?_⟩
      have hndvd : ¬ 101 ∣ b := by
        intro hd
        have hle : 101 ≤ b := Nat.le_of_dvd (by omega) hd
        omega
      exact (hP.coprime_iff_not_dvd (n := b)).mpr hndvd |>.symm
  have hzero :
      ∑ b ∈ Finset.range 101,
        Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 101) ^ (a * b) = 0 := by
    have hpr :
        IsPrimitiveRoot (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 101) ^ a) 101 :=
      (hζ.pow_iff_coprime (by norm_num) a).mpr ha
    simpa only [pow_mul] using hpr.geom_sum_eq_zero (by norm_num : 1 < 101)
  have hsum :
      ∑ b ∈ (Finset.range 101).filter (fun b => Nat.Coprime b 101),
        Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 101 : ℝ) : ℂ) * Complex.I) = -1 := by
    rw [hfilter]
    calc ∑ b ∈ (Finset.range 101).erase 0,
            Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 101 : ℝ) : ℂ) * Complex.I)
        = ∑ b ∈ (Finset.range 101).erase 0,
            Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 101) ^ (a * b) :=
          Finset.sum_congr rfl (fun b _ => app_term a b)
      _ = ∑ b ∈ Finset.range 101,
            Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 101) ^ (a * b) - 1 := by
          refine eq_sub_iff_add_eq.mpr ?_
          rw [add_comm]
          simpa using
            Finset.sum_erase_add (s := Finset.range 101)
              (f := fun b => Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 101) ^ (a * b))
              (a := 0) (by simp)
      _ = -1 := by
          rw [hzero]
          norm_num
  rw [hsum]

end PEqualNP.Outside
