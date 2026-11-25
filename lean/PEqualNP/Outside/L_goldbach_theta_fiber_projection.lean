import Mathlib

theorem PEqualNP.Outside.L_goldbach_theta_fiber_projection :
    ∀ (m r : ℕ) (c : Fin m → Fin r) (a : Fin m → ℝ) (b : Fin r → ℝ),
      let F := fun j => Finset.univ.filter (fun i => c i = j);
      let μ := fun j => (∑ i ∈ F j, a i)/((F j).card:ℝ);
      (∑ i, (a i-μ (c i))^2) ≤ ∑ i, (a i-b (c i))^2 := by
  classical
  intro m r c a b
  let F : Fin r → Finset (Fin m) := fun j => Finset.univ.filter (fun i => c i = j)
  let μ : Fin r → ℝ := fun j => (∑ i ∈ F j, a i)/((F j).card:ℝ)
  show (∑ i, (a i - μ (c i))^2) ≤ ∑ i, (a i - b (c i))^2
  have key : ∀ (s : Finset (Fin m)) (y : ℝ), s.card ≠ 0 →
      (∑ i ∈ s, (a i - (∑ i ∈ s, a i)/((s.card:ℝ)))^2) ≤ ∑ i ∈ s, (a i - y)^2 := by
    intro s y hs
    set S : ℝ := ∑ i ∈ s, a i with hS
    set n : ℝ := (s.card : ℝ) with hn0
    set m' : ℝ := S / n with hm'
    have hn : n ≠ 0 := by
      simp only [hn0]
      exact_mod_cast hs
    have hmean : ∑ i ∈ s, (a i - m') = 0 := by
      rw [Finset.sum_sub_distrib]
      have hconst : ∑ _i ∈ s, m' = n * m' := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hconst, hm']
      have hcancel : n * (S / n) = S := by
        rw [mul_comm]
        exact div_mul_cancel₀ S hn
      rw [hcancel, hS]
      simp
    have hY : ∑ i ∈ s, (2 * (a i - m') * (m' - y)) = 0 := by
      have hfactor : ∑ i ∈ s, (2 * (a i - m') * (m' - y)) =
          (2 * (m' - y)) * ∑ i ∈ s, (a i - m') := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hfactor, hmean, mul_zero]
    have hpt : ∀ i ∈ s, (a i - y)^2 =
        (a i - m')^2 + 2 * (a i - m') * (m' - y) + (m' - y)^2 := by
      intro i hi
      ring
    calc ∑ i ∈ s, (a i - y)^2
        = ∑ i ∈ s, ((a i - m')^2 + 2 * (a i - m') * (m' - y) + (m' - y)^2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hpt i hi]
      _ = ∑ i ∈ s, (a i - m')^2 + ∑ i ∈ s, (2 * (a i - m') * (m' - y))
            + ∑ _i ∈ s, (m' - y)^2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ∑ i ∈ s, (a i - m')^2 + 0 + n * (m' - y)^2 := by
          rw [hY]
          congr 1
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≥ ∑ i ∈ s, (a i - m')^2 := by
          have hnn : 0 ≤ n * (m' - y)^2 :=
            mul_nonneg (by simp only [hn0]; positivity) (sq_nonneg _)
          linarith
  have hL : (∑ i, (a i - μ (c i))^2) = ∑ j, ∑ i ∈ F j, (a i - μ j)^2 := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin m)) c (fun i => (a i - μ (c i))^2)]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    have hci : c i = j := by
      simpa using hi
    rw [hci]
  have hR : (∑ i, (a i - b (c i))^2) = ∑ j, ∑ i ∈ F j, (a i - b j)^2 := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin m)) c (fun i => (a i - b (c i))^2)]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    have hci : c i = j := by
      simpa using hi
    rw [hci]
  rw [hL, hR]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hc : (F j).card = 0
  · have hempty : F j = ∅ := Finset.card_eq_zero.mp hc
    simp [hempty]
  · exact key (F j) (b j) hc
