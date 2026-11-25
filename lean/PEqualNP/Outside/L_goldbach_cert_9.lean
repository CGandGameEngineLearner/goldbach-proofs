import Mathlib

namespace PEqualNP.Outside

private lemma cert9_arg (a b : ℕ) :
    (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 9 : ℝ) : ℂ) * Complex.I)
      = ((a * b : ℕ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) := by
  push_cast
  ring

private lemma cert9_term (a b : ℕ) :
    Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 9 : ℝ) : ℂ) * Complex.I)
      = Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (a * b) := by
  rw [cert9_arg a b, ← Complex.exp_nat_mul]

theorem L_goldbach_cert_9 (a : ℕ) (ha : Nat.Coprime a 9) :
    (∑ b ∈ (Finset.range 9).filter (fun b => Nat.Coprime b 9),
        Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 9 : ℝ) : ℂ) * Complex.I)) / (6 : ℂ)
      = (0 : ℂ) / 6 := by
  have hζ : IsPrimitiveRoot (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9)) 9 :=
    Complex.isPrimitiveRoot_exp 9 (by norm_num)
  have ha3 : Nat.Coprime a 3 := by
    have h : Nat.Coprime a (3 ^ 2) := ha
    exact (Nat.coprime_pow_right_iff (by norm_num) a 3).mp h
  have hζ3 :
      IsPrimitiveRoot (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ 3) 3 := by
    have h := hζ.pow_of_dvd (p := 3) (by norm_num) (by norm_num : 3 ∣ 9)
    simpa using h
  have hgeom :
      ∑ j ∈ Finset.range 3,
        ((Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ 3) ^ a) ^ j = 0 := by
    have hpr3 := (hζ3.pow_iff_coprime (by norm_num) a).mpr ha3
    exact hpr3.geom_sum_eq_zero (by norm_num : 1 < 3)
  have htotal :
      ∑ b ∈ Finset.range 9,
        Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (a * b) = 0 := by
    have hpr := (hζ.pow_iff_coprime (by norm_num) a).mpr ha
    simpa only [pow_mul] using hpr.geom_sum_eq_zero (by norm_num : 1 < 9)
  have hset :
      (Finset.range 9).filter (fun b => ¬ Nat.Coprime b 9) = ({0, 3, 6} : Finset ℕ) := by
    decide
  have hnon :
      ∑ b ∈ (Finset.range 9).filter (fun b => ¬ Nat.Coprime b 9),
        Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (a * b) = 0 := by
    rw [hset]
    have hbridge : ∑ b ∈ ({0, 3, 6} : Finset ℕ),
          Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (a * b)
        = ∑ j ∈ Finset.range 3,
            ((Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ 3) ^ a) ^ j := by
      have h1 : ({0, 3, 6} : Finset ℕ) = (Finset.range 3).image (fun j => 3 * j) := by
        decide
      rw [h1, Finset.sum_image (by
        intro x hx y hy hxy
        simp only at hxy
        omega)]
      refine Finset.sum_congr rfl ?_
      intro j _
      have e1 : a * (3 * j) = (3 * a) * j := by ring
      have e2 : Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (3 * a)
          = (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ 3) ^ a := by
        rw [pow_mul]
      rw [e1, pow_mul, e2]
    rw [hbridge, hgeom]
  have hsplit :
      ∑ b ∈ (Finset.range 9).filter (fun b => Nat.Coprime b 9),
          Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (a * b)
        + ∑ b ∈ (Finset.range 9).filter (fun b => ¬ Nat.Coprime b 9),
          Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (a * b)
        = ∑ b ∈ Finset.range 9,
          Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (a * b) :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.range 9)
      (p := fun b => Nat.Coprime b 9)
      (f := fun b => Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (a * b))
  have hunits :
      ∑ b ∈ (Finset.range 9).filter (fun b => Nat.Coprime b 9),
        Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (a * b) = 0 := by
    rw [htotal, hnon] at hsplit
    simpa using hsplit
  have hfinal :
      ∑ b ∈ (Finset.range 9).filter (fun b => Nat.Coprime b 9),
        Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 9 : ℝ) : ℂ) * Complex.I) = 0 := by
    calc ∑ b ∈ (Finset.range 9).filter (fun b => Nat.Coprime b 9),
            Complex.exp (((2 * Real.pi * (a : ℝ) * (b : ℝ) / 9 : ℝ) : ℂ) * Complex.I)
        = ∑ b ∈ (Finset.range 9).filter (fun b => Nat.Coprime b 9),
            Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I / 9) ^ (a * b) :=
          Finset.sum_congr rfl (fun b _ => cert9_term a b)
      _ = 0 := hunits
  rw [hfinal]

end PEqualNP.Outside
