import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_choose_tangent_right :
  ∀ k t m : ℕ, 1 ≤ k → t ≤ m → Nat.choose t k + (m - t) * Nat.choose t (k - 1) ≤ Nat.choose m k := by
  intro k t m hk htm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htm
  clear htm
  rw [Nat.add_sub_cancel_left]
  induction d with
  | zero => simp
  | succ d ih =>
    have hrec : Nat.choose (t + d + 1) k = Nat.choose (t + d) k + Nat.choose (t + d) (k - 1) := by
      cases k with
      | zero => omega
      | succ k' =>
        change Nat.choose (t + d + 1) (k' + 1) = Nat.choose (t + d) (k' + 1) + Nat.choose (t + d) k'
        rw [Nat.choose_succ_succ, add_comm]
    have hmono : Nat.choose t (k - 1) ≤ Nat.choose (t + d) (k - 1) :=
      Nat.choose_le_choose (k - 1) (by omega)
    calc Nat.choose t k + (d + 1) * Nat.choose t (k - 1)
        = (Nat.choose t k + d * Nat.choose t (k - 1)) + Nat.choose t (k - 1) := by ring
      _ ≤ Nat.choose (t + d) k + Nat.choose (t + d) (k - 1) := Nat.add_le_add ih hmono
      _ = Nat.choose (t + d + 1) k := hrec.symm
      _ = Nat.choose (t + (d + 1)) k := by ring_nf
