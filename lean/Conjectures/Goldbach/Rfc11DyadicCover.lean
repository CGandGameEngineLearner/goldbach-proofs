import Mathlib

set_option exponentiation.threshold 2000

theorem Conjectures.Goldbach.Rfc11DyadicCover :
    (2:ℕ)^597 < 10^180 ∧ (10:ℕ)^180 < 2^598 ∧
      (2:ℕ)^1049 < 10^316 ∧ (10:ℕ)^316 < 2^1050 := by
  norm_num