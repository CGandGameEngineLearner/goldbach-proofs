import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_triple_drop :
    ∀ a b : ℕ,
      Nat.choose (a + 1) 3 + Nat.choose b 3 + Nat.choose b 2
        = Nat.choose a 3 + Nat.choose (b + 1) 3 + Nat.choose a 2 := by
  intro a b
  rw [Nat.choose_succ_succ' a 2, Nat.choose_succ_succ' b 2]
  simp only [Nat.reduceAdd]
  omega
