import Mathlib

/-!
# Spectral tail budget for the chosen vector

Split `∑ eigen i * w i` at the threshold `A`.  On the part with `eigen i ≤ A` the summand is at most
`A * w i`, giving at most `A * Q`.  On the tail, `eigen i ≤ B` and the tail mass is at most
`A * Q / (2 * (B + 1))`, giving at most `B * A * Q / (2 * (B + 1)) ≤ A * Q / 2` because
`B / (B + 1) ≤ 1`.  The two parts add to at most `(3 / 2) * A * Q`.  Only the mass of this one
vector enters, so no information about other vectors is used.
-/

theorem PEqualNP.Outside.L_goldbach_hardy_central_positive_tail_margin :
    ∀ {ι : Type} (s : Finset ι) (eigen w : ι → ℝ) (A B Q : ℝ), 0 ≤ A → 0 ≤ B → 0 ≤ Q → (∀ i ∈ s, 0 ≤ w i ∧ eigen i ≤ B) → (∑ i ∈ s, w i) ≤ Q → (∑ i ∈ s.filter (fun i => A < eigen i), w i) ≤ A*Q/(2*(B+1)) → (∑ i ∈ s, eigen i*w i) ≤ (3/2)*A*Q := by
  intro ι s eigen w A B Q hA hB hQ hws hwQ htail
  have hpos : ∀ i ∈ s, 0 ≤ w i ∧ eigen i ≤ B := hws
  have hsplit : (∑ i ∈ s.filter (fun i => eigen i ≤ A), eigen i * w i)
      + (∑ i ∈ s.filter (fun i => ¬ eigen i ≤ A), eigen i * w i)
      = ∑ i ∈ s, eigen i * w i := Finset.sum_filter_add_sum_filter_not s (fun i => eigen i ≤ A) _
  rw [← hsplit]
  have hmass : (∑ i ∈ s.filter (fun i => eigen i ≤ A), w i) ≤ Q := by
    refine le_trans ?_ hwQ
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ s) (fun i hi _ => (hpos i hi).1)
  have h1 : (∑ i ∈ s.filter (fun i => eigen i ≤ A), eigen i * w i) ≤ A * Q := by
    calc (∑ i ∈ s.filter (fun i => eigen i ≤ A), eigen i * w i)
        ≤ ∑ i ∈ s.filter (fun i => eigen i ≤ A), A * w i := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact mul_le_mul_of_nonneg_right (Finset.mem_filter.mp hi).2 (hpos i (Finset.mem_filter.mp hi).1).1
      _ = A * ∑ i ∈ s.filter (fun i => eigen i ≤ A), w i := by rw [Finset.mul_sum]
      _ ≤ A * Q := mul_le_mul_of_nonneg_left hmass hA
  have hcongr : s.filter (fun i => ¬ eigen i ≤ A) = s.filter (fun i => A < eigen i) :=
    Finset.filter_congr (fun i _ => not_le)
  rw [hcongr]
  have h2 : (∑ i ∈ s.filter (fun i => A < eigen i), eigen i * w i) ≤ B * (A * Q / (2 * (B + 1))) := by
    calc (∑ i ∈ s.filter (fun i => A < eigen i), eigen i * w i)
        ≤ ∑ i ∈ s.filter (fun i => A < eigen i), B * w i := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact mul_le_mul_of_nonneg_right (hpos i (Finset.mem_filter.mp hi).1).2 (hpos i (Finset.mem_filter.mp hi).1).1
      _ = B * ∑ i ∈ s.filter (fun i => A < eigen i), w i := by rw [Finset.mul_sum]
      _ ≤ B * (A * Q / (2 * (B + 1))) := mul_le_mul_of_nonneg_left htail hB
  have hB1 : (0:ℝ) < B + 1 := by linarith
  have hfrac : B / (2 * (B + 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    nlinarith
  have hq : (0:ℝ) ≤ A * Q := mul_nonneg hA hQ
  have h3 : B * (A * Q / (2 * (B + 1))) ≤ (A * Q) / 2 := by
    calc B * (A * Q / (2 * (B + 1))) = (A * Q) * (B / (2 * (B + 1))) := by ring
      _ ≤ (A * Q) * (1 / 2) := mul_le_mul_of_nonneg_left hfrac hq
      _ = (A * Q) / 2 := by ring
  linarith
