import Mathlib.Algebra.BigOperators.Fin

theorem Conjectures.Cuts.Task4d7b04832d9857dba5e25f27 :
∀ (x1 x2 : ℕ),   (2 : ℕ) ≤ x1 →     ∀ (x4 : Fin x2 → ℕ),       (∀ (x5 : Fin x2), x4 x5 < x1) →         have x6 : ℕ := ∑ x6 : Fin x2, x4 x6 * x1 ^ (↑x6 : ℕ);         x6 < x1 ^ x2 ∧ ∀ (x7 : Fin x2), x6 / x1 ^ (↑x7 : ℕ) % x1 = x4 x7 := by
  intro b k hb
  induction k with
  | zero =>
    intro w _
    constructor
    · simp
    · exact fun i => i.elim0
  | succ k ih =>
    intro w hw
    let tail := ∑ i : Fin k, w i.succ * b^i.val
    obtain ⟨ht,hget⟩ := ih (fun i => w i.succ) (fun i => hw i.succ)
    change tail < b^k at ht
    change ∀ i : Fin k, tail / b^i.val % b = w i.succ at hget
    have split : (∑ i : Fin (k+1), w i * b^i.val) = w 0 + tail*b := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, ← Nat.mul_assoc]
      rw [Finset.sum_mul]
    dsimp only
    rw [split]
    constructor
    · calc
        w 0 + tail*b < b + tail*b := Nat.add_lt_add_right (hw 0) _
        _ = (tail+1)*b := by rw [Nat.add_mul,Nat.one_mul,Nat.add_comm]
        _ ≤ b^(k+1) := by rw [pow_succ]; exact Nat.mul_le_mul_right _ ht
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Nat.mod_eq_of_lt (hw 0)]
      · change (w 0 + tail*b) / b^(j.val+1) % b = w j.succ
        rw [pow_succ, Nat.mul_comm (b^j.val) b, ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_right _ _ (by omega : 0 < b), Nat.div_eq_of_lt (hw 0), Nat.zero_add]
        exact hget j
