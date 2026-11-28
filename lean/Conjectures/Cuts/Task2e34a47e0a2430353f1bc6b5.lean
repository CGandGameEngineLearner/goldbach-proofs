import Mathlib

open Finset

namespace FourResidueProduct

private noncomputable def model (p : ℕ) : ℝ :=
  (p : ℝ)^3 * (p - 4 : ℝ) / ((p : ℝ) - 1)^4

private theorem model_bounds (p : ℕ) (hp : 5 ≤ p) :
    0 ≤ model p ∧ model p ≤ 1 := by
  have h : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hd : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  unfold model
  constructor
  · exact div_nonneg (mul_nonneg (by positivity) (by linarith)) (by positivity)
  · apply (div_le_iff₀ (pow_pos hd 4)).2
    nlinarith [sq_nonneg ((p : ℝ) - 1)]

private theorem full_product (k : ℕ) :
    ∏ p ∈ Ico 5 (5+k), model p =
      6 * ((k : ℝ)+4)^3 / (64 * (k+1 : ℝ) * (k+2 : ℝ) * (k+3 : ℝ)) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Nat.add_succ, Finset.prod_Ico_succ_top (by omega : 5 ≤ 5+k), ih]
    unfold model
    push_cast
    rw [show (5 : ℝ) + k - 1 = (k : ℝ) + 4 by ring]
    field_simp <;> ring

private theorem lower (z : ℕ) : (6/64 : ℝ) ≤ ∏ p ∈ Ico 5 z, model p := by
  by_cases hz : 5 ≤ z
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hz
    rw [full_product]
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]
  · simp [Finset.Ico_eq_empty_of_le (by omega : z ≤ 5)] <;> norm_num

private theorem compare (p n : ℕ) (hp : 5 ≤ p) :
    model p ≤ (1 - ([(0 : ℕ), p-2, n%p, (n+2)%p].toFinset.card : ℝ) / p) /
      (1 - 1/(p : ℝ))^4 := by
  have h : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (0 : ℝ) < p := by linarith
  have h1 : (0 : ℝ) < (p : ℝ)-1 := by linarith
  have hc : ([(0 : ℕ), p-2, n%p, (n+2)%p].toFinset.card : ℝ) ≤ 4 := by
    exact_mod_cast (List.toFinset_card_le [(0 : ℕ), p-2, n%p, (n+2)%p])
  have he : model p = (1 - 4/(p : ℝ)) / (1 - 1/(p : ℝ))^4 := by
    unfold model
    rw [show 1 - 1/(p : ℝ) = ((p : ℝ)-1)/p by field_simp <;> ring]
    field_simp <;> ring
  rw [he]
  exact div_le_div_of_nonneg_right (sub_le_sub_left (div_le_div_of_nonneg_right hc h0.le) 1)
    (by positivity)

end FourResidueProduct

theorem Conjectures.Cuts.Task2e34a47e0a2430353f1bc6b5 : (have x1 : ℕ → ℕ → ℝ := fun (x1 x2 : ℕ) => (27 / 2 : ℝ) * ∏ x3 ∈ Finset.Ico (5 : ℕ) x1 with Nat.Prime x3, ((1 : ℝ) - (↑[(0 : ℕ), x3 - (2 : ℕ), x2 % x3, (x2 + (2 : ℕ)) % x3].toFinset.card : ℝ) / (↑x3 : ℝ)) / ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ)) ^ (4 : ℕ); ∀ (x2 x3 : ℕ), x3 % (6 : ℕ) = (4 : ℕ) → (81 / 64 : ℝ) ≤ x1 x2 x3) := by
  intro series z n _
  dsimp only [series]
  rw [Finset.prod_filter]
  have h := FourResidueProduct.lower z
  apply le_trans (show (81/64 : ℝ) ≤ 27/2 * (6/64) by norm_num)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine h.trans (Finset.prod_le_prod ?_ ?_)
  · intro p hp
    exact (FourResidueProduct.model_bounds p (Finset.mem_Ico.mp hp).1).1
  · intro p hp
    split_ifs
    · exact FourResidueProduct.compare p n (Finset.mem_Ico.mp hp).1
    · exact (FourResidueProduct.model_bounds p (Finset.mem_Ico.mp hp).1).2
