import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_rallis_difference_error :
    ∀ A P Q M N E e f h : ℝ, 0<A → |(P-Q)/A-4*E|≤h → |P/A-M|≤e → |Q/A-N|≤f → |4*E-(M-N)|≤e+f+h := by
  intro A P Q M N E e f h hA h1 h2 h3
  have hA0 : A ≠ 0 := ne_of_gt hA
  have key : 4*E-(M-N) = -((P-Q)/A-4*E) + (P/A-M) - (Q/A-N) := by
    field_simp
    ring
  rw [key]
  rw [abs_le]
  have h1' := abs_le.mp h1
  have h2' := abs_le.mp h2
  have h3' := abs_le.mp h3
  constructor <;> nlinarith [h1'.1, h1'.2, h2'.1, h2'.2, h3'.1, h3'.2]
