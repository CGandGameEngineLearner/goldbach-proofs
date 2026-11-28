import CorrectionTransfer
import SignedRowOffsetRemoval

namespace Goldbach.JointSignedResidual
open SignedRowOffsetRemoval
noncomputable section

/-- Only the linear and quadratic zero-amplitude rows remain. All terms from
the zero-mode convention have been paid for uniformly at every frequency. -/
theorem frozen_of_stripped_pairs {α C : ℝ} (hα : α < 4/5) (hC : 0 < C)
    (h : ∃ N : ℕ, ∀ X ≥ N,
      (reducedPairs (fun Y m => GB5Variance.modeCoeff (strippedRows Y) m) X : ℝ)
        ≤ C*(X:ℝ)^(1+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (ShiftWideArc.missed X).card^5 ≤ X^4 := by
  apply frozen_of_reduced_pairs hα hC _ h
  filter_upwards [eventual_mode_bound (1/256) (by norm_num)] with Y hy
  intro m
  calc
    _ ≤ (1/256:ℝ)*(Y:ℝ) := hy m
    _ = _ := by ring

end
end Goldbach.JointSignedResidual
#print axioms Goldbach.JointSignedResidual.frozen_of_stripped_pairs
