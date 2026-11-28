import Mathlib

theorem Conjectures.Cuts.Taske288f69a0908d43f9d978ed2 : (by
  classical
  exact ∀ (U : Finset ℕ) (a b : ℕ → ℕ),
    let K := fun i j : ℕ => ∑ n ∈ U, (a n).choose i*(b n).choose j
    (∑ n ∈ U, (a n*b n)^2) = K 1 1+2*K 2 1+2*K 1 2+4*K 2 2) := by
  classical
  intro U a b K
  have diag (n : ℕ) : n^2 = n+2*n.choose 2 := by
    induction n with
    | zero => decide
    | succ n ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      nlinarith
  have term (n : ℕ) : (a n*b n)^2 =
      (a n).choose 1*(b n).choose 1+2*((a n).choose 2*(b n).choose 1)
       +2*((a n).choose 1*(b n).choose 2)+4*((a n).choose 2*(b n).choose 2) := by
    rw [mul_pow,diag (a n),diag (b n)]
    simp only [Nat.choose_one_right]
    ring
  simp only [K,term,Finset.sum_add_distrib,Finset.mul_sum]
