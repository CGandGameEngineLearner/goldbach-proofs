import Mathlib

namespace PEqualNP.Outside

theorem L_goldbach_sieve_residue_dimension :
    ∀ n p : ℕ, p.Prime →
      ((Finset.range p).filter (fun k => k % p = 0 ∨ k % p = n % p)).card =
        if p ∣ n then 1 else 2 := by
  classical
  intro n p hp
  have hr : n % p < p := Nat.mod_lt _ hp.pos
  have hset : (Finset.range p).filter (fun k => k % p = 0 ∨ k % p = n % p) =
      ({0, n % p} : Finset ℕ) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h⟩
      simpa only [Nat.mod_eq_of_lt hk] using h
    · intro h
      have hk : k < p := by
        rcases h with rfl | rfl
        · exact hp.pos
        · exact hr
      exact ⟨hk, by simpa only [Nat.mod_eq_of_lt hk] using h⟩
  have pairCard : ({0, n % p} : Finset ℕ).card = (if p ∣ n then 1 else 2) := by
    by_cases hd : p ∣ n
    · simp [hd, Nat.mod_eq_zero_of_dvd hd]
    · have hne : 0 ≠ n % p := fun h => hd (Nat.dvd_of_mod_eq_zero h.symm)
      rw [if_neg hd]
      exact Finset.card_pair_eq_two_iff.mpr hne
  rw [hset]
  exact pairCard

end PEqualNP.Outside
