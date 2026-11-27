import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.DynExceptionEnergy :
    ∀ (E : Finset ℕ) (r b : ℕ → ℝ) (L : ℝ), 0 < L → (∀ n ∈ E, L ≤ b n) →
      ((E.filter (fun n => r n=0)).card:ℝ)*L^2 ≤ ∑ n ∈ E, (r n-b n)^2 := by
  intro E r b L hL hb
  set S := E.filter (fun n => r n = 0) with hS
  have h1 : (S.card : ℝ) * L^2 = ∑ n ∈ S, (L^2 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [h1]
  have hstep1 : ∑ n ∈ S, (L^2 : ℝ) ≤ ∑ n ∈ S, (r n - b n)^2 := by
    refine Finset.sum_le_sum (fun n hn => ?_)
    have hn' : n ∈ E.filter (fun n => r n = 0) := by rw [hS] at hn; exact hn
    have hn0 : r n = 0 := (Finset.mem_filter.mp hn').2
    have hbn : L ≤ b n := hb n (Finset.mem_filter.mp hn').1
    have hneg : r n - b n = -(b n) := by rw [hn0]; ring
    rw [hneg, neg_sq]
    nlinarith [hL, hbn]
  have hstep2 : ∑ n ∈ S, (r n - b n)^2 ≤ ∑ n ∈ E, (r n - b n)^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (by rw [hS]; exact Finset.filter_subset _ _)
      (fun n _ _ => by positivity)
  exact le_trans hstep1 hstep2
