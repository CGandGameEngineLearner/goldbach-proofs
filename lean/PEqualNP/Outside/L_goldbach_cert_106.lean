import Mathlib

open scoped BigOperators

namespace PEqualNP.Outside

set_option maxRecDepth 8192 in
set_option maxHeartbeats 3000000 in
theorem L_goldbach_cert_106 :
    ∀ a:ℕ, Nat.Coprime a 106 → (∑ b ∈ (Finset.range 106).filter (fun b => Nat.Coprime b 106), Complex.exp (((2*Real.pi*(a:ℝ)*b/106:ℝ):ℂ)*Complex.I))/(52:ℂ)=(1:ℂ)/52 := by
  intro a ha
  let θ : ℂ := 2 * (Real.pi : ℂ) * Complex.I * ((a : ℂ) / 106)
  let z := Complex.exp θ
  have hz : IsPrimitiveRoot z 106 :=
    Complex.isPrimitiveRoot_exp_of_coprime a 106 (by decide) ha
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 106 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    calc
      Complex.exp _ = Complex.exp ((b : ℂ) * θ) := by
        apply congrArg Complex.exp
        dsimp only [θ]
        push_cast
        ring
      _ = z ^ b := Complex.exp_nat_mul θ b
  have h₅₃ : IsPrimitiveRoot (z ^ 2) 53 :=
    IsPrimitiveRoot.pow (a := 2) (b := 53) (by decide) hz (by decide)
  have h₂ : IsPrimitiveRoot (z ^ 53) 2 :=
    IsPrimitiveRoot.pow (a := 53) (b := 2) (by decide) hz (by decide)
  let odd : ℕ ↪ ℕ := ⟨fun j => 2 * j + 1, by intro j k h; omega⟩
  let odds := (Finset.range 53).map odd
  have residues : (Finset.range 106).filter (fun b => Nat.Coprime b 106) = odds.erase 53 := by
    decide
  have odds_sum : (∑ b ∈ odds, z ^ b) = 0 := by
    dsimp only [odds]
    rw [Finset.sum_map]
    simp only [odd, Function.Embedding.coeFn_mk, pow_add, pow_mul, pow_one]
    rw [← Finset.sum_mul, h₅₃.geom_sum_eq_zero (by decide), zero_mul]
  have units_sum : (∑ b ∈ odds.erase 53, z ^ b) = 1 := by
    have h := Finset.sum_erase_add odds (fun b => z ^ b) (show 53 ∈ odds by decide)
    have h' := eq_sub_of_add_eq (h.trans odds_sum)
    simpa [h₂.eq_neg_one_of_two_right] using h'
  simp_rw [phase]
  rw [residues, units_sum]

end PEqualNP.Outside
