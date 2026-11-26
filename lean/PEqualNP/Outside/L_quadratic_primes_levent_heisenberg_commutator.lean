import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_heisenberg_commutator :
    ∀ (N : ℕ) [NeZero N] (a b : ZMod N) (f : ZMod N → ℂ), let T := fun (g : ZMod N → ℂ) n => g (n+a); let M := fun (g : ZMod N → ℂ) n => ZMod.stdAddChar (b*n)*g n; ∀ n, T (M f) n = ZMod.stdAddChar (a*b)*M (T f) n := by
  intro N _ a b f
  dsimp only
  intro n
  rw [mul_add, AddChar.map_add_eq_mul, mul_comm b a]
  ring
