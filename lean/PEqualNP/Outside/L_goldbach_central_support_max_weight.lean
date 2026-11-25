import Mathlib

theorem PEqualNP.Outside.L_goldbach_central_support_max_weight :
    let S := fun (n : ℕ) => (Finset.range (n+1)).filter (fun k => n<3*k ∧ 3*k<2*n); ∀ n (A:Finset ℕ) (w:ℕ→ℝ) (M:ℝ), A⊆S n → (∀ k∈A,w k≤M) → (∑ k ∈ A,w k)≤(A.card:ℝ)*M := by
  intro S n A w M hA hw
  calc ∑ k ∈ A, w k ≤ ∑ k ∈ A, M := Finset.sum_le_sum (fun k hk => hw k hk)
    _ = (A.card : ℝ) * M := by
        rw [Finset.sum_const, nsmul_eq_mul]
