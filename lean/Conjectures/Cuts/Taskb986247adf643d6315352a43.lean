import Mathlib

theorem Conjectures.Cuts.Taskb986247adf643d6315352a43 : (have x1 : ℕ → Prop := fun (x1 : ℕ) => Nat.Prime x1 ∧ (x1 + (2 : ℕ)).primeFactorsList.length ≤ (2 : ℕ); ∀ (x2 : ℕ), (1 : ℕ) ≤ x2 → (x1 ((6 : ℕ) * x2 + (1 : ℕ)) ∧ x1 ((6 : ℕ) * x2 + (7 : ℕ)) ↔ Nat.Prime ((6 : ℕ) * x2 + (1 : ℕ)) ∧ Nat.Prime ((6 : ℕ) * x2 + (7 : ℕ)) ∧ Nat.Prime ((2 : ℕ) * x2 + (1 : ℕ)) ∧ Nat.Prime ((2 : ℕ) * x2 + (3 : ℕ)))) := by
  intro chen k hk
  have factorThree (m : ℕ) (hm : 1 < m) :
      (3 * m).primeFactorsList.length ≤ 2 ↔ Nat.Prime m := by
    have hthree : Nat.Prime 3 := by decide
    have hlen : (3 * m).primeFactorsList.length = 1 + m.primeFactorsList.length := by
      simpa [Nat.primeFactorsList_prime hthree, Nat.add_comm] using
        (Nat.perm_primeFactorsList_mul (by decide : 3 ≠ 0) (by omega : m ≠ 0)).length_eq
    constructor
    · intro h
      have hpos := List.length_pos_iff_ne_nil.mpr ((Nat.primeFactorsList_ne_nil m).mpr hm)
      obtain ⟨q, hsingle⟩ := List.length_eq_one_iff.mp (show m.primeFactorsList.length = 1 by omega)
      have hmem : q ∈ m.primeFactorsList := by rw [hsingle]; exact List.mem_singleton_self q
      have hqm : q = m := by
        simpa [hsingle] using Nat.prod_primeFactorsList (by omega : m ≠ 0)
      exact hqm ▸ Nat.prime_of_mem_primeFactorsList hmem
    · intro h
      rw [hlen, Nat.primeFactorsList_prime h]
      rfl
  have ha : (6 * k + 1 + 2).primeFactorsList.length ≤ 2 ↔ Nat.Prime (2 * k + 1) := by
    rw [show 6 * k + 1 + 2 = 3 * (2 * k + 1) by omega]
    exact factorThree _ (by omega)
  have hb : (6 * k + 7 + 2).primeFactorsList.length ≤ 2 ↔ Nat.Prime (2 * k + 3) := by
    rw [show 6 * k + 7 + 2 = 3 * (2 * k + 3) by omega]
    exact factorThree _ (by omega)
  dsimp only [chen]
  rw [ha, hb]
  constructor
  · rintro ⟨⟨hp, hq⟩, hr, hs⟩
    exact ⟨hp, hr, hq, hs⟩
  · rintro ⟨hp, hr, hq, hs⟩
    exact ⟨⟨hp, hq⟩, hr, hs⟩
