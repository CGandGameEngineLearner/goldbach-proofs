import Mathlib

/-!
# L-goldbach-strip-geometry-height-square

On the critical line `re s = 1/2`, the squared modulus of `s` is `1/4 + (im s)^2`:
the height alone determines the modulus.  This is the critical-strip geometry fact
behind zero-counting arguments, transplanted from the Riemann hypothesis
formalization (`ClaimStrip`).
-/

theorem PEqualNP.Outside.L_goldbach_strip_geometry_height_square :
    ∀ s : ℂ, s.re=1/2 → Complex.normSq s = 1/4+s.im^2 := by
  intro s hs
  rw [Complex.normSq_apply, hs]
  ring
