import Mathlib

namespace Conjectures.Cuts.Task21cd5496761c30c2261477a2_aux

private lemma ite_mul_ite_one {p q : Prop} [Decidable p] [Decidable q] :
    (if p then (1 : ℕ) else 0) * (if q then (1 : ℕ) else 0) = if p ∧ q then (1 : ℕ) else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

end Conjectures.Cuts.Task21cd5496761c30c2261477a2_aux

theorem Conjectures.Cuts.Task21cd5496761c30c2261477a2 :
    ∀ (x1 x2 : ℕ), ∑ x3 ∈ Finset.Ico x1 ((2 : ℕ) * x1), {x4 ∈ Finset.Icc (1 : ℕ) (x2 / (2 : ℕ)) | Nat.Prime (x3 - (2 : ℕ) ^ x4)}.card * {x4 ∈ Finset.Icc (x2 / (2 : ℕ) + (1 : ℕ)) x2 | Nat.Prime (x3 - (2 : ℕ) ^ x4)}.card = ∑ x3 ∈ Finset.Icc (1 : ℕ) (x2 / (2 : ℕ)), ∑ x4 ∈ Finset.Icc (x2 / (2 : ℕ) + (1 : ℕ)) x2, {x5 ∈ Finset.Ico x1 ((2 : ℕ) * x1) | Nat.Prime (x5 - (2 : ℕ) ^ x3) ∧ Nat.Prime (x5 - (2 : ℕ) ^ x4)}.card := by
  intro x1 x2
  have hL : ∑ x3 ∈ Finset.Ico x1 ((2 : ℕ) * x1),
        {x4 ∈ Finset.Icc (1 : ℕ) (x2 / (2 : ℕ)) | Nat.Prime (x3 - (2 : ℕ) ^ x4)}.card *
          {x4 ∈ Finset.Icc (x2 / (2 : ℕ) + (1 : ℕ)) x2 | Nat.Prime (x3 - (2 : ℕ) ^ x4)}.card =
      ∑ y ∈ Finset.Ico x1 ((2 : ℕ) * x1), ∑ a ∈ Finset.Icc (1 : ℕ) (x2 / (2 : ℕ)),
        ∑ b ∈ Finset.Icc (x2 / (2 : ℕ) + (1 : ℕ)) x2,
          if Nat.Prime (y - (2 : ℕ) ^ a) ∧ Nat.Prime (y - (2 : ℕ) ^ b) then (1 : ℕ) else 0 := by
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    exact Conjectures.Cuts.Task21cd5496761c30c2261477a2_aux.ite_mul_ite_one
  have hR : ∑ x3 ∈ Finset.Icc (1 : ℕ) (x2 / (2 : ℕ)),
        ∑ x4 ∈ Finset.Icc (x2 / (2 : ℕ) + (1 : ℕ)) x2,
          {x5 ∈ Finset.Ico x1 ((2 : ℕ) * x1) |
            Nat.Prime (x5 - (2 : ℕ) ^ x3) ∧ Nat.Prime (x5 - (2 : ℕ) ^ x4)}.card =
      ∑ a ∈ Finset.Icc (1 : ℕ) (x2 / (2 : ℕ)), ∑ b ∈ Finset.Icc (x2 / (2 : ℕ) + (1 : ℕ)) x2,
        ∑ y ∈ Finset.Ico x1 ((2 : ℕ) * x1),
          if Nat.Prime (y - (2 : ℕ) ^ a) ∧ Nat.Prime (y - (2 : ℕ) ^ b) then (1 : ℕ) else 0 := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.card_filter]
  rw [hL, hR, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
