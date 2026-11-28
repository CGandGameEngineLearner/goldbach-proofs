import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli
import DeepCompatibleNoSiegel
import PrimitiveBoxInterface

/-! A polynomial range with no primitive Dirichlet zeros in a strip of
width K / log X, including zeros of the real primitive characters. -/

namespace Goldbach.PintzClasses
open OAI.Ostmann

/-- The classical strip holds also for the primitive real characters:
the possible exceptional zero is excluded by the accepted real gap. -/
theorem primitive_zero_free_strip : ∃ c : ℝ, 0 < c ∧
    ∀ (χ : PrimitiveComplexCharacter) (T : ℝ), 2 ≤ T → ∀ i : ℕ,
    |((V1 χ).zeros i).im| ≤ T →
    ((V1 χ).zeros i).re < 1 - c / Real.log (2 * (χ.modulus:ℝ) * T) := by
  obtain ⟨c,hc,hclass⟩ := Vta.V10u
  obtain ⟨s,hs,hreal⟩ := PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero
  let u := min c s / 2
  have hu : 0 < u := by dsimp [u]; exact half_pos (lt_min hc hs)
  have huc : u < c := (half_lt_self (lt_min hc hs)).trans_le (min_le_left _ _)
  have hus : u < s := (half_lt_self (lt_min hc hs)).trans_le (min_le_right _ _)
  refine ⟨u, hu, ?_⟩
  intro χ T hT i hi
  have hq1 : 1 ≤ (χ.modulus:ℝ) := by exact_mod_cast χ.positive
  let H := Real.log (2 * (χ.modulus:ℝ) * T)
  have hH : 0 < H := zero_lt_one.trans_le (Vqr χ.modulus χ.positive T hT)
  have hS := Real.log_pos (show 1 < (χ.modulus:ℝ) + 2 by linarith)
  have hSH : Real.log ((χ.modulus:ℝ) + 2) ≤ H := by
    apply Real.log_le_log (by positivity)
    calc
      (χ.modulus:ℝ) + 2 ≤ 2 * (χ.modulus:ℝ) * 2 := by linarith
      _ ≤ 2 * (χ.modulus:ℝ) * T := mul_le_mul_of_nonneg_left hT (by positivity)
  have hclasscut := div_lt_div_of_pos_right huc hH
  have hrealcut : u / H < s / Real.log ((χ.modulus:ℝ)+2) :=
    (div_lt_div_of_pos_right hus hH).trans_le (div_le_div_of_nonneg_left hs.le hS hSH)
  by_contra! hnear
  change 1 - u/H ≤ _ at hnear
  obtain ⟨e,heq,heb,_⟩ := hclass χ.modulus χ.positive T hT χ le_rfl i hi
    (by change 1 - c / H ≤ _; linarith)
  letI : NeZero e.modulus := ⟨e.positive.ne'⟩
  have hquad : e.character.ringHomComp Complex.ofRealHom ^ 2 = 1 :=
    ((V1n2 e.character).comp Complex.ofRealHom).sq_eq_one
  apply hreal e.modulus _ e.beta hquad _ e.beta_lt_one e.zero
  rw [heq, heb]; linarith

/-- In a sufficiently small but fixed polynomial conductor and height box,
every enumerated zero lies strictly to the left of the scaled vertical line.
The exponent may depend on K but is uniform in the primitive characters. -/
theorem polynomial_zero_free_box (K : ℝ) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (X T : ℝ) (χ : PrimitiveComplexCharacter),
      1 < X → 2 ≤ T → (χ.modulus : ℝ) ≤ X ^ δ → T ≤ X ^ δ →
      ∀ i : ℕ, |((V1 χ).zeros i).im| ≤ T →
        ((V1 χ).zeros i).re < 1 - K / Real.log X := by
  obtain ⟨c,hc,hfree⟩ := primitive_zero_free_strip
  let δ := c / (3 * (K + 1))
  have hd : 0 < δ := div_pos hc (by positivity)
  have hδ : δ * (3 * (K + 1)) = c := div_mul_cancel₀ _ (by positivity)
  have hkc : K * (3 * δ) < c := by nlinarith
  refine ⟨δ, hd, ?_⟩
  intro X T χ hX hT hqX hTX i hi
  have hx := zero_lt_one.trans hX
  have hl := Real.log_pos hX
  have hq1 : 1 ≤ (χ.modulus : ℝ) := by exact_mod_cast χ.positive
  have hq := zero_lt_one.trans_le hq1
  have ht : 0 < T := by linarith
  have hlogq : Real.log χ.modulus ≤ δ * Real.log X := by
    simpa only [Real.log_rpow hx] using Real.log_le_log hq hqX
  have hlogt : Real.log T ≤ δ * Real.log X := by
    simpa only [Real.log_rpow hx] using Real.log_le_log ht hTX
  have hlog2 := Real.log_le_log (by norm_num : (0:ℝ) < 2) hT
  let H := Real.log (2 * (χ.modulus:ℝ) * T)
  have hH : 0 < H := zero_lt_one.trans_le (Vqr χ.modulus χ.positive T hT)
  have hHle : H ≤ (3 * δ) * Real.log X := by
    dsimp [H]; rw [Real.log_mul (by positivity) ht.ne', Real.log_mul (by norm_num) hq.ne']
    linarith
  have hcut : K / Real.log X < c / H := (div_lt_div_iff₀ hl hH).mpr <|
    (mul_le_mul_of_nonneg_left hHle hK.le).trans_lt
      (by simpa [mul_assoc] using mul_lt_mul_of_pos_right hkc hl)
  have hz := hfree χ T hT i hi
  change _ < 1 - c/H at hz
  linarith

/-- Every actual L-function zero in the critical strip occurs in `V1`. -/
theorem polynomial_box_nonvanishing (K : ℝ) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (X T : ℝ) (χ : PrimitiveComplexCharacter),
      1 < X → 2 ≤ T → (χ.modulus:ℝ) ≤ X^δ → T ≤ X^δ →
      ∀ z : ℂ, 0 < z.re → z.re < 1 → |z.im| ≤ T →
        1 - K / Real.log X ≤ z.re → χ.L z ≠ 0 := by
  obtain ⟨δ, hd, h⟩ := polynomial_zero_free_box K hK
  refine ⟨δ, hd, ?_⟩
  intro X T χ hX hT hq ht z hz₀ hz₁ hi hs hz
  obtain ⟨i, hi'⟩ := V1bf χ z ⟨hz₀, hz₁, hz⟩
  have hlt := h X T χ hX hT hq ht i (by simpa only [hi'] using hi)
  exact hs.not_gt (by simpa only [hi'] using hlt)

/-- In particular the multiplicity count of these low-conductor,
low-height near-one zeros vanishes identically throughout the box. -/
theorem polynomial_box_zero_count (K : ℝ) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (X T : ℝ) (χ : PrimitiveComplexCharacter),
      1 < X → 2 ≤ T → (χ.modulus:ℝ) ≤ X^δ → T ≤ X^δ →
      (V1 χ).count (1 - K/Real.log X) T = 0 := by
  obtain ⟨δ,hd,h⟩ := polynomial_zero_free_box K hK
  refine ⟨δ, hd, ?_⟩
  intro X T χ hX hT hq ht
  rw [ComplexZeroEnumeration.count, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i hi; exact not_le.mpr (h X T χ hX hT hq ht i (by simpa using hi))

end Goldbach.PintzClasses

#print axioms Goldbach.PintzClasses.polynomial_box_zero_count

namespace Goldbach.CanonicalLowConductorZeros
open OAI.Ostmann

/-- The unconditional primitive zero-free box in ordinary Dirichlet-character notation. -/
theorem primitiveBoxInput_actual (K : ℝ) (hK : 0 < K) : PrimitiveBoxInput K := by
  obtain ⟨δ,hδ,hzero⟩ := Goldbach.PintzClasses.polynomial_box_nonvanishing K hK
  refine ⟨δ,hδ,?_⟩
  intro X T d hd ψ hp hn hX hT hq ht z hz₀ hz₁ hi hstrip
  let χ : PrimitiveComplexCharacter := ⟨d, NeZero.pos d, ψ, hp, hn⟩
  exact hzero X T χ hX hT hq ht z hz₀ hz₁ hi hstrip

end Goldbach.CanonicalLowConductorZeros

#print axioms Goldbach.CanonicalLowConductorZeros.primitiveBoxInput_actual
