import Mathlib

/-!
The difference of consecutive range sums is the new last term.  This is the
telescoping backbone for the moving-window weight accounting in the RH-guided
Goldbach track.
-/

theorem PEqualNP.Outside.L_goldbach_moving_weights_prefix_invert :
    ∀ (a : ℕ → ℂ) (k : ℕ), (∑ j ∈ Finset.range (k+1),a j)-(∑ j ∈ Finset.range k,a j)=a k := by
  intro a k
  rw [Finset.sum_range_succ]
  ring
