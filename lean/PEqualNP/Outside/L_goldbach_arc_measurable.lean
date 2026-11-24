import Mathlib

theorem PEqualNP.Outside.L_goldbach_arc_measurable :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; ∀ n, MeasurableSet (arcs n) := by
  classical
  intro Q arcs n
  let piece (q a : ℕ) := {t : ℝ | 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}
  have cover : arcs n = ⋃ q : ℕ, ⋃ a : ℕ, piece q a := by
    ext t
    simp only [Set.mem_iUnion] <;> rfl
  rw [cover]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨hq, hQ, ha, hc⟩ := h
    simp only [piece, hq, hQ, ha, hc, true_and]
    exact (isClosed_le (continuous_id.sub continuous_const).abs continuous_const).measurableSet
  · have empty : piece q a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro t ⟨hq, hQ, ha, hc, _⟩
      exact h ⟨hq, hQ, ha, hc⟩
    rw [empty]
    exact MeasurableSet.empty
