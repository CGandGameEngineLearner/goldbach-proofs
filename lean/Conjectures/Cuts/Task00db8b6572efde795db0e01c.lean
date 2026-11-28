import Mathlib

theorem Conjectures.Cuts.Task00db8b6572efde795db0e01c : (∀ (b k n : ℕ), 2 ≤ b → (∑ i : Fin k, ((n/b^(i:ℕ)) % b)*b^(i:ℕ)) = n % b^k) := by
  intro b k n hb
  have tel (j : ℕ) : (∑ i : Fin j, ((n/b^(i:ℕ)) % b)*b^(i:ℕ)) + (n/b^j)*b^j = n := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, pow_succ]
      rw [← Nat.div_div_eq_div_mul]
      have hd := congrArg (fun z : ℕ => z*b^j) (Nat.mod_add_div (n/b^j) b)
      nlinarith only [ih,hd]
  have ht := tel k
  have hm := Nat.mod_add_div n (b^k)
  rw [Nat.mul_comm (b^k)] at hm
  omega
