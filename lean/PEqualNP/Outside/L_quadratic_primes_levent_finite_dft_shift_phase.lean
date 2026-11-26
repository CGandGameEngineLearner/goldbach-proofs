import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_finite_dft_shift_phase :
    ∀ (N : ℕ) [NeZero N] (f : ZMod N → ℂ) (h k : ZMod N), ZMod.dft (fun n => f (n+h)) k = ZMod.stdAddChar (h*k) * ZMod.dft f k := by
  intro N _ f h k
  simp only [ZMod.dft_apply, smul_eq_mul, Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.addRight h)
  intro n
  change ZMod.stdAddChar (-(n*k)) * f (n+h) =
    ZMod.stdAddChar (h*k) * (ZMod.stdAddChar (-((n+h)*k)) * f (n+h))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring
