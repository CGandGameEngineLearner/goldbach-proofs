import Mathlib

theorem PEqualNP.Outside.L_goldbach_theta_fiber_projection :
    ∀ (m r : ℕ) (c : Fin m → Fin r) (a : Fin m → ℝ) (b : Fin r → ℝ), let F := fun j => Finset.univ.filter (fun i => c i=j); let μ := fun j => (∑ i ∈ F j, a i)/((F j).card:ℝ); (∑ i, (a i-μ (c i))^2) ≤ ∑ i, (a i-b (c i))^2 := by
  intro m r c a b F μ
  have hfib : ∀ f : Fin m → ℝ, ∑ j : Fin r, ∑ i ∈ F j, f i = ∑ i : Fin m, f i := by
    intro f
    symm
    rw [← Finset.sum_fiberwise_of_maps_to (g := c) (t := Finset.univ)]
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext i
      simp [F]
    · intro _ _
      exact Finset.mem_univ _
  rw [← hfib (fun i => (a i - μ (c i)) ^ 2), ← hfib (fun i => (a i - b (c i)) ^ 2)]
  dsimp only
  apply Finset.sum_le_sum
  intro j _
  have hdiff : ∑ i ∈ F j, ((a i - b (c i)) ^ 2 - (a i - μ (c i)) ^ 2) =
      ∑ i ∈ F j, (2 * (μ j - b j) * (a i - μ j) + (μ j - b j) ^ 2) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [F] at hi
    have hci : c i = j := (Finset.mem_filter.mp hi).2
    rw [hci]
    ring
  have hnonneg : 0 ≤ ∑ i ∈ F j, ((a i - b (c i)) ^ 2 - (a i - μ (c i)) ^ 2) := by
    rw [hdiff, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hzero : ∑ i ∈ F j, (a i - μ j) = 0 := by
      by_cases hcard : (F j).card = 0
      · have hempty : F j = ∅ := Finset.card_eq_zero.mp hcard
        rw [hempty, Finset.sum_empty]
      · have hne : ((F j).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        dsimp only [μ]
        field_simp <;> ring
    rw [hzero, mul_zero, zero_add]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Finset.sum_sub_distrib] at hnonneg
  exact sub_nonneg.mp hnonneg
