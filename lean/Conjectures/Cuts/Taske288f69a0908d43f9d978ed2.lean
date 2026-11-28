import Mathlib

/-! Sum-of-squares expansion for a cut child of `L-goldbach-romanov-separated-band-support`.

The identity splits `∑ (a b)²` through the first two binomial coefficients:
`n² = n + 2 * n.choose 2`, hence `(a b)² = a b + 2 (C a 2 · b) + 2 (a · C b 2) + 4 (C a 2 · C b 2)`.
-/

namespace GoldbachCutBinomial

/-- `n ^ 2 = n + 2 * n.choose 2`. -/
theorem sq_eq_add_two_mul_choose (n : ℕ) : n ^ 2 = n + 2 * n.choose 2 := by
  have hdvd : 2 ∣ n * (n - 1) := (Nat.even_mul_pred_self n).two_dvd
  have h2 : 2 * (n * (n - 1) / 2) = n * (n - 1) := by
    rw [mul_comm 2]
    exact Nat.div_mul_cancel hdvd
  have hsq : n ^ 2 = n + n * (n - 1) := by
    cases n with
    | zero => simp
    | succ k => simp; ring
  rw [Nat.choose_two_right, h2]
  exact hsq

end GoldbachCutBinomial

theorem Conjectures.Cuts.Taske288f69a0908d43f9d978ed2 :
    ∀ (x1 : Finset ℕ) (x2 x3 : ℕ → ℕ),
      have x4 : ℕ → ℕ → ℕ := fun (x4 x5 : ℕ) => ∑ x6 ∈ x1, (x2 x6).choose x4 * (x3 x6).choose x5;
      ∑ x5 ∈ x1, (x2 x5 * x3 x5) ^ (2 : ℕ) = x4 (1 : ℕ) (1 : ℕ) + (2 : ℕ) * x4 (2 : ℕ) (1 : ℕ) + (2 : ℕ) * x4 (1 : ℕ) (2 : ℕ) + (4 : ℕ) * x4 (2 : ℕ) (2 : ℕ) := by
  intro s a b
  simp only []
  have hpt : ∀ x ∈ s, (a x * b x) ^ 2 =
      (a x).choose 1 * (b x).choose 1
        + 2 * ((a x).choose 2 * (b x).choose 1)
        + 2 * ((a x).choose 1 * (b x).choose 2)
        + 4 * ((a x).choose 2 * (b x).choose 2) := by
    intro x _
    have hA := GoldbachCutBinomial.sq_eq_add_two_mul_choose (a x)
    have hB := GoldbachCutBinomial.sq_eq_add_two_mul_choose (b x)
    simp only [Nat.choose_one_right]
    calc (a x * b x) ^ 2 = (a x) ^ 2 * (b x) ^ 2 := by ring
      _ = (a x + 2 * (a x).choose 2) * (b x + 2 * (b x).choose 2) := by rw [hA, hB]
      _ = a x * b x + 2 * ((a x).choose 2 * b x) + 2 * (a x * (b x).choose 2)
            + 4 * ((a x).choose 2 * (b x).choose 2) := by ring
  calc ∑ x ∈ s, (a x * b x) ^ 2
      = ∑ x ∈ s, ((a x).choose 1 * (b x).choose 1
          + 2 * ((a x).choose 2 * (b x).choose 1)
          + 2 * ((a x).choose 1 * (b x).choose 2)
          + 4 * ((a x).choose 2 * (b x).choose 2)) := Finset.sum_congr rfl hpt
    _ = (∑ x ∈ s, (a x).choose 1 * (b x).choose 1)
        + 2 * (∑ x ∈ s, (a x).choose 2 * (b x).choose 1)
        + 2 * (∑ x ∈ s, (a x).choose 1 * (b x).choose 2)
        + 4 * (∑ x ∈ s, (a x).choose 2 * (b x).choose 2) := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
