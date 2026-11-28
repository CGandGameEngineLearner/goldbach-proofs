import CanonicalBandCount
import MeasurableCanonicalField

open Finset Filter MeasureTheory
namespace Goldbach.MiddleCanonicalModel
open ShiftWideArc
noncomputable section
open scoped Classical

/-- At each large scale, the squared corrected model approximates the actual
signed middle-band coefficient outside O(Y^(2/3)) frequencies. -/
theorem actual_exceptional_at_128 : ∀ᶠ Y : ℕ in atTop, ∀ I : Finset ℕ,
    ((I.filter (fun m => (Y:ℝ)/128 ≤ ‖coefficient (bandSet Y) Y m - fieldCoefficient Y m‖)).card:ℝ) ≤
      (18*128^2:ℝ)*(Y:ℝ)^(2/3:ℝ) := by
  obtain ⟨C,hC,h⟩ := eventual_field_bound
  filter_upwards [h,eventually_field_mem,CanonicalBandCount.exceptional_at_128 hC.le] with Y hb hm hc
  intro I
  simp_rw [coefficient_difference hm]
  exact hc (field Y) (field_stronglyMeasurable Y).aestronglyMeasurable (fun t ht => hb t ht.2) I

/-- Only the negative tail of the squared signed-zero model remains after the
unconditional per-scale approximation error has been charged. -/
theorem negative_counts : ∀ᶠ Y : ℕ in atTop, ∀ I : Finset ℕ,
    ((I.filter (fun m => (coefficient (bandSet Y) Y m).re < -(Y:ℝ)/64)).card:ℝ) ≤
      ((I.filter (fun m => (fieldCoefficient Y m).re < -(Y:ℝ)/128)).card:ℝ) +
      (18*128^2:ℝ)*(Y:ℝ)^(2/3:ℝ) := by
  filter_upwards [actual_exceptional_at_128] with Y hY
  intro I
  let A := I.filter (fun m => (coefficient (bandSet Y) Y m).re < -(Y:ℝ)/64)
  let B := I.filter (fun m => (fieldCoefficient Y m).re < -(Y:ℝ)/128)
  let E := I.filter (fun m => (Y:ℝ)/128 ≤ ‖coefficient (bandSet Y) Y m - fieldCoefficient Y m‖)
  have hsub : A ⊆ B ∪ E := by
    intro m hm
    obtain ⟨hi,ha⟩ := mem_filter.mp hm
    by_cases h : (fieldCoefficient Y m).re < -(Y:ℝ)/128
    · exact mem_union_left _ (mem_filter.mpr ⟨hi,h⟩)
    · apply mem_union_right _ (mem_filter.mpr ⟨hi,?_⟩)
      have hr := Complex.re_le_norm (fieldCoefficient Y m - coefficient (bandSet Y) Y m)
      rw [Complex.sub_re,norm_sub_rev] at hr
      linarith
  have hcount : A.card ≤ B.card+E.card := (card_le_card hsub).trans (card_union_le ..)
  change (A.card:ℝ) ≤ (B.card:ℝ) + _
  exact (show (A.card:ℝ) ≤ (B.card:ℝ)+(E.card:ℝ) by exact_mod_cast hcount).trans
    (add_le_add (le_refl _) (hY I))

end
end Goldbach.MiddleCanonicalModel
#print axioms Goldbach.MiddleCanonicalModel.actual_exceptional_at_128
#print axioms Goldbach.MiddleCanonicalModel.negative_counts
