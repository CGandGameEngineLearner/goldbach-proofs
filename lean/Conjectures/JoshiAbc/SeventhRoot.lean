import Mathlib

theorem Conjectures.JoshiAbc.SeventhRoot :
    let z : ZMod 29 := 7; orderOf z = 7 ∧ z^2 ≠ 0 ∧ 1+z^2 ≠ 0 := by
  intro z
  refine ⟨orderOf_eq_prime (hp := ⟨by norm_num⟩) (by decide) (by decide), ?_, ?_⟩
  · decide
  · decide
