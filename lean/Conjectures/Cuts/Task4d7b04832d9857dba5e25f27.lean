import Mathlib

theorem Conjectures.Cuts.Task4d7b04832d9857dba5e25f27 : (∀ (x1 x2 : ℕ),   (2 : ℕ) ≤ x1 →     ∀ (x4 : Fin x2 → ℕ),       (∀ (x5 : Fin x2), x4 x5 < x1) →         have x6 : ℕ := ∑ x6 : Fin x2, x4 x6 * x1 ^ (↑x6 : ℕ);         x6 < x1 ^ x2 ∧ ∀ (x7 : Fin x2), x6 / x1 ^ (↑x7 : ℕ) % x1 = x4 x7) := by
  intro b k hb
  have hbpos : 0 < b := by omega
  induction k with
  | zero =>
    intro w hw
    simp
  | succ k ih =>
    intro w hw
    let tail := ∑ i : Fin k, w i.succ * b ^ (i : ℕ)
    obtain ⟨ht, hd⟩ := ih (fun i => w i.succ) (fun i => hw i.succ)
    change tail < b ^ k at ht
    change ∀ i : Fin k, tail / b ^ (i : ℕ) % b = w i.succ at hd
    have split : (∑ i : Fin (k+1), w i * b ^ (i : ℕ)) = w 0 + b * tail := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, tail,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    dsimp only
    rw [split]
    constructor
    · have h := hw 0
      have aux := Nat.mul_le_mul_left b (Nat.succ_le_of_lt ht)
      rw [pow_succ]
      nlinarith
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hw 0)]
      · simp only [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left _ _ hbpos, Nat.div_eq_of_lt (hw 0), zero_add]
        exact hd j
