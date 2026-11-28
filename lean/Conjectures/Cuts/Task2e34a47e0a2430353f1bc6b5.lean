import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ChenFiniteProduct

private noncomputable def weight (t : ℝ) := ((t - 4) * t ^ 3) / (t - 1) ^ 4

private noncomputable def boundary (t : ℝ) := (t - 1)^3 / ((t - 2) * (t - 3) * (t - 4))

private lemma weight_nonneg {t : ℝ} (h : 5 ≤ t) : 0 ≤ weight t := by
  unfold weight
  exact div_nonneg (mul_nonneg (by linarith) (by positivity)) (by positivity)

private lemma weight_le_one {t : ℝ} (h : 5 ≤ t) : weight t ≤ 1 := by
  have h1 : 0 < t - 1 := by linarith
  apply (div_le_one (pow_pos h1 4)).2
  nlinarith [sq_nonneg (t - 1), mul_nonneg (show 0 ≤ t - 5 by linarith) (show 0 ≤ t by linarith)]

private lemma boundary_ge_one {t : ℝ} (h : 5 ≤ t) : 1 ≤ boundary t := by
  have h2 : 0 < t - 2 := by linarith
  have h3 : 0 < t - 3 := by linarith
  have h4 : 0 < t - 4 := by linarith
  apply (one_le_div (mul_pos (mul_pos h2 h3) h4)).2
  calc
    (t - 2) * (t - 3) * (t - 4) ≤ (t - 1) * (t - 1) * (t - 1) := by gcongr <;> nlinarith [sq_nonneg (t-1)]
    _ = (t - 1)^3 := by ring

private lemma boundary_step {t : ℝ} (h : 5 ≤ t) :
    boundary (t + 1) = boundary t * weight t := by
  have h1 : t - 1 ≠ 0 := by linarith
  have h2 : t - 2 ≠ 0 := by linarith
  have h3 : t - 3 ≠ 0 := by linarith
  have h4 : t - 4 ≠ 0 := by linarith
  unfold boundary weight
  rw [show t + 1 - 1 = t by ring, show t + 1 - 2 = t - 1 by ring,
      show t + 1 - 3 = t - 2 by ring, show t + 1 - 4 = t - 3 by ring]
  field_simp

private lemma product_lower (f : ℕ → ℝ) (hf : ∀ k : ℕ, 5 ≤ k → weight k ≤ f k)
    (P : ℕ) (hP : 5 ≤ P) :
    (3/32 : ℝ) * boundary P ≤ ∏ k ∈ Finset.Ico 5 P, f k := by
  induction P, hP using Nat.le_induction with
  | base => norm_num [boundary]
  | succ k hk ih =>
    have hk' : (5 : ℝ) ≤ k := by exact_mod_cast hk
    rw [Finset.prod_Ico_succ_top hk]
    push_cast
    rw [boundary_step hk', ← mul_assoc]
    exact mul_le_mul ih (hf k hk) (weight_nonneg hk')
      (by
        apply Finset.prod_nonneg
        intro j hj
        have hj5 := (Finset.mem_Ico.mp hj).1
        exact (weight_nonneg (by exact_mod_cast hj5)).trans (hf j hj5))

private lemma card_four (a b c d : ℕ) : ({a,b,c,d} : Finset ℕ).card ≤ 4 := by
  have h1 := Finset.card_insert_le a ({b,c,d} : Finset ℕ)
  have h2 := Finset.card_insert_le b ({c,d} : Finset ℕ)
  have h3 := Finset.card_insert_le c ({d} : Finset ℕ)
  simp only [Finset.card_singleton] at h3
  omega

theorem singular_floor (P n : ℕ) :
    (81/64 : ℝ) ≤ (27/2 : ℝ) * ∏ k ∈ (Finset.Ico 5 P).filter Nat.Prime,
      (1 - (({0, k-2, n % k, (n+2) % k} : Finset ℕ).card : ℝ)/(k : ℝ)) /
        (1 - 1/(k : ℝ))^4 := by
  classical
  by_cases hP : 5 ≤ P
  · rw [Finset.prod_filter]
    apply le_trans (b := (27/2 : ℝ) * ((3/32) * boundary P))
    · have h := boundary_ge_one (t := (P : ℝ)) (by exact_mod_cast hP)
      linarith
    · apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply product_lower _ _ _ hP
      intro k hk
      have hk' : (5 : ℝ) ≤ k := by exact_mod_cast hk
      split_ifs
      · have hk0 : (0 : ℝ) < k := by linarith
        have h1 : (0 : ℝ) < 1 - 1/(k:ℝ) := by
          have := (div_lt_one hk0).2 (show (1 : ℝ) < k by linarith)
          linarith
        have hc : (({0,k-2,n % k,(n+2) % k} : Finset ℕ).card : ℝ) ≤ 4 := by
          exact_mod_cast card_four 0 (k-2) (n % k) ((n+2) % k)
        calc weight k = (1 - 4/(k:ℝ)) / (1 - 1/(k:ℝ)) ^ 4 := by
               unfold weight
               have hk1 : (k : ℝ) - 1 ≠ 0 := by linarith
               field_simp [ne_of_gt hk0, ne_of_gt h1]
             _ ≤ _ := by
               apply div_le_div_of_nonneg_right _ (by positivity)
               exact sub_le_sub_left (div_le_div_of_nonneg_right hc hk0.le) _
      · exact weight_le_one hk'
  · rw [Finset.Ico_eq_empty_of_le (by omega : P ≤ 5)]
    norm_num

end ChenFiniteProduct


theorem Conjectures.Cuts.Task2e34a47e0a2430353f1bc6b5 : (have x1 : ℕ → ℕ → ℝ := fun (x1 x2 : ℕ) => (27 / 2 : ℝ) * ∏ x3 ∈ Finset.Ico (5 : ℕ) x1 with Nat.Prime x3, ((1 : ℝ) - (↑[(0 : ℕ), x3 - (2 : ℕ), x2 % x3, (x2 + (2 : ℕ)) % x3].toFinset.card : ℝ) / (↑x3 : ℝ)) / ((1 : ℝ) - (1 : ℝ) / (↑x3 : ℝ)) ^ (4 : ℕ); ∀ (x2 x3 : ℕ), x3 % (6 : ℕ) = (4 : ℕ) → (81 / 64 : ℝ) ≤ x1 x2 x3) := by
  dsimp only
  intro P n _
  simpa [List.toFinset_cons, List.toFinset_nil] using ChenFiniteProduct.singular_floor P n
