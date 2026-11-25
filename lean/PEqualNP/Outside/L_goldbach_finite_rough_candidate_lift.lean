import Mathlib

private theorem residueWitness : ∀ residue : Fin 105, ∃ prime : Fin 20,
    Nat.Prime prime.val ∧ Nat.Coprime ((2 * residue.val + 210 - prime.val) % 210) 210 := by
  decide

theorem PEqualNP.Outside.L_goldbach_finite_rough_candidate_lift :
    ∀ n : ℕ, 22 ≤ n → Even n → ∃ p : ℕ, Nat.Prime p ∧ p < n ∧ 2 ≤ n-p ∧ Nat.Coprime (n-p) 210 := by
  rintro n lower ⟨half, rfl⟩
  obtain ⟨prime, primeIsPrime, coprimeResidue⟩ := residueWitness ⟨half % 105, Nat.mod_lt _ (by decide)⟩
  have bound := prime.isLt
  refine ⟨prime.val, primeIsPrime, by omega, by omega, ?_⟩
  change Nat.Coprime ((2 * (half % 105) + 210 - prime.val) % 210) 210 at coprimeResidue
  have residueEq : (half + half - prime.val) % 210 = (2 * (half % 105) + 210 - prime.val) % 210 := by omega
  change Nat.gcd (half + half - prime.val) 210 = 1
  rwa [Nat.gcd_comm, Nat.gcd_rec, residueEq]
