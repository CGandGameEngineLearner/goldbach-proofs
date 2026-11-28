import Mathlib

theorem Conjectures.Cuts.Taskb4b2d6784446336753bd135a : (by
  classical
  exact ∀ (U S : Finset ℕ) (I : ℕ → Finset ℕ),
    (∀ p ∈ U, I p ⊆ S ∧ (I p).card ≤ 1) →
    (U.filter (fun p => (I p).Nonempty)).card = ∑ r ∈ S, (U.filter (fun p => r ∈ I p)).card) := by
  classical
  intro U S I hi
  have inner (p : ℕ) (hp : p ∈ U) : (if (I p).Nonempty then 1 else 0 : ℕ) =
      ∑ r ∈ S, if r ∈ I p then 1 else 0 := by
    have eqs : S.filter (fun r => r ∈ I p) = I p := by
      ext r
      simp only [Finset.mem_filter]
      exact ⟨And.right,fun h => ⟨(hi p hp).1 h,h⟩⟩
    rw [Finset.sum_boole,eqs]
    by_cases h : (I p).Nonempty
    · have hpos := Finset.card_pos.mpr h
      have hle := (hi p hp).2
      simp [h]; omega
    · simp [Finset.not_nonempty_iff_eq_empty.mp h]
  calc
    _ = ∑ p ∈ U, if (I p).Nonempty then 1 else 0 := by simp
    _ = ∑ p ∈ U, ∑ r ∈ S, if r ∈ I p then 1 else 0 := Finset.sum_congr rfl inner
    _ = _ := by rw [Finset.sum_comm]; simp
