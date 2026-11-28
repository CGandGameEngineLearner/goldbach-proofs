import Mathlib

theorem Conjectures.Cuts.Task4d7b04832d9857dba5e25f27 : (∀ (b k : ℕ), 2 ≤ b → ∀ w : Fin k → ℕ, (∀ i, w i < b) →
    let n := ∑ i : Fin k, w i*b^(i:ℕ)
    n < b^k ∧ ∀ i : Fin k, (n/b^(i:ℕ)) % b = w i) := by
  intro b k hb
  induction k with
  | zero =>
    intro w _
    simp
  | succ k ih =>
    intro w hw
    let a := ∑ i : Fin k, w i.succ * b^(i:ℕ)
    have htail := ih (fun i => w i.succ) (fun i => hw i.succ)
    change a < b^k ∧ ∀ i : Fin k, (a/b^(i:ℕ)) % b = w i.succ at htail
    have splitSum : (∑ i : Fin (k+1), w i*b^(i:ℕ)) = w 0 + b*a := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      dsimp only [a]
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by ring)
    dsimp only
    rw [splitSum]
    have h0 := hw 0
    have hpos : 0 < b := by omega
    have hdiv : (w 0 + b*a)/b = a := by simp [Nat.add_mul_div_left, hpos, Nat.div_eq_of_lt h0]
    constructor
    · rw [pow_succ']
      calc
        w 0+b*a < b+b*a := Nat.add_lt_add_right h0 _
        _ = b*(a+1) := by ring
        _ ≤ b*b^k := Nat.mul_le_mul_left _ htail.1
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Nat.add_mod, Nat.mod_eq_of_lt h0]
      · rw [Fin.val_succ, pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
        exact htail.2 j
