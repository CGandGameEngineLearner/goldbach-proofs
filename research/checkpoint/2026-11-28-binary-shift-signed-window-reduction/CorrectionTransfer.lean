import SignedResidualTerminal

open Finset Filter
namespace Goldbach.JointSignedResidual
open CanonicalDyadicPairs PrincipalZeroOffset
noncomputable section
open scoped Classical

/-- Allow any explicit simplified, signed approximation to the correction.
Each discarded term can be budgeted at the level of the coefficient. -/
def reducedPairs (B : ℕ → ℕ → ℂ) (X : ℕ) :=
  pairs X (fun Y m => (B Y m).re < -(Y:ℝ)/256)

theorem correction_le_reduced {B : ℕ → ℕ → ℂ}
    (he : ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ,
      ‖GB5Variance.modeCoeff (signedRows Y) m - B Y m‖ ≤ (Y:ℝ)/256) :
    ∀ᶠ X : ℕ in atTop, correctionPairs X ≤ reducedPairs B X := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop (4*N)] with X hx
  unfold correctionPairs reducedPairs pairs
  refine sum_le_sum (fun m hm => card_le_card ?_)
  intro Y hy
  obtain ⟨hY,hev,hneg⟩ := mem_filter.mp hy
  apply mem_filter.mpr
  refine ⟨hY,hev,?_⟩
  obtain ⟨hm₁,hm₂⟩ := mem_Icc.mp hm
  obtain ⟨hY₁,hY₂⟩ := mem_Icc.mp hY
  have he' := (Complex.abs_re_le_norm _).trans (hN Y (by omega) m)
  rw [Complex.sub_re, abs_le] at he'
  change (GB5Variance.modeCoeff (signedRows Y) m).re < -(Y:ℝ)/128 at hneg
  change (B Y m).re < -(Y:ℝ)/256
  linarith [he'.1]

theorem frozen_of_reduced_pairs {B : ℕ → ℕ → ℂ} {α C : ℝ} (hα : α < 4/5) (hC : 0 < C)
    (he : ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ,
      ‖GB5Variance.modeCoeff (signedRows Y) m - B Y m‖ ≤ (Y:ℝ)/256)
    (h : ∃ N : ℕ, ∀ X ≥ N, (reducedPairs B X : ℝ) ≤ C*(X:ℝ)^(1+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (ShiftWideArc.missed X).card^5 ≤ X^4 := by
  obtain ⟨N,hN⟩ := h
  apply frozen_of_correction_pairs hα hC
  apply eventually_atTop.mp
  filter_upwards [correction_le_reduced he,eventually_ge_atTop N] with X hle hx
  exact (Nat.cast_le.mpr hle).trans (hN X hx)

end
end Goldbach.JointSignedResidual
#print axioms Goldbach.JointSignedResidual.frozen_of_reduced_pairs
