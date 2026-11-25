import Mathlib

/-- The complete list of sieve roots of `n ^ 2 + 1` modulo the prime `613`:
`n ^ 2 + 1` is divisible by `613` exactly when `n` is congruent to `35` or `578`
modulo `613`. -/
theorem PEqualNP.Outside.L_quadratic_primes_cert_613 :
    ∀ n : ℕ, 613 ∣ n ^ 2 + 1 ↔ n % 613 = 35 ∨ n % 613 = 578 := by
  have hroots : ∀ k : Fin 613, (k.val ^ 2 + 1) % 613 = 0 ↔ k.val = 35 ∨ k.val = 578 := by
    set_option maxRecDepth 100000 in
    decide
  intro n
  set r := n % 613 with hr
  have hrlt : r < 613 := by
    rw [hr]
    exact Nat.mod_lt _ (by norm_num)
  have key : (r ^ 2 + 1) % 613 = 0 ↔ r = 35 ∨ r = 578 := by
    simpa using hroots ⟨r, hrlt⟩
  have hmod : (n ^ 2 + 1) % 613 = (r ^ 2 + 1) % 613 := by
    have hn : Nat.ModEq 613 n r := by
      rw [Nat.ModEq, hr, Nat.mod_mod]
    exact Nat.ModEq.add_right 1 (Nat.ModEq.pow 2 hn)
  rw [Nat.dvd_iff_mod_eq_zero, hmod, key, hr]
