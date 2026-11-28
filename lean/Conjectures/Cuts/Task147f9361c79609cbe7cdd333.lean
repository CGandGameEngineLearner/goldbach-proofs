import Mathlib

namespace Conjectures.Cuts.Task147f9361c79609cbe7cdd333_aux

/-- A central prime for `n`: a prime `p` with `n ≤ 3 * p` and `3 * p ≤ 2 * n`. -/
theorem exists_central_prime (n : ℕ) (hn : 6 ≤ n) :
    ∃ p : ℕ, Nat.Prime p ∧ 3 * p ≤ 2 * n ∧ 2 * n ≤ 6 * p := by
  have hm : n / 3 ≠ 0 := by omega
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 3) hm
  have h1 : 3 * (n / 3) + 3 > n := by omega
  have h2 : 3 * p ≥ 3 * (n / 3) + 3 := by omega
  have h3 : 6 * (n / 3) ≤ 2 * n := by omega
  refine ⟨p, hp, ?_, ?_⟩
  · omega
  · omega

end Conjectures.Cuts.Task147f9361c79609cbe7cdd333_aux

theorem Conjectures.Cuts.Task147f9361c79609cbe7cdd333 :
    ∃ (x1 : ℕ), ∀ (x2 : ℕ), x1 ≤ x2 → Even x2 → ∃ (x5 : ℕ), Nat.Prime x5 ∧ (3 : ℕ) * x5 ≤ (2 : ℕ) * x2 ∧ (2 : ℕ) * x2 ≤ (6 : ℕ) * x5 :=
  ⟨6, fun x2 hx2 _ => Conjectures.Cuts.Task147f9361c79609cbe7cdd333_aux.exists_central_prime x2 hx2⟩
