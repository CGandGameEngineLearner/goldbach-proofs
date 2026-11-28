import Mathlib

theorem Conjectures.Cuts.Task897953a760185a640f834ad8 : (∀ (x1 : ℕ) (x2 : Finset (ZMod (x1 + (1 : ℕ)))) (x3 : ZMod (x1 + (1 : ℕ)) → ℝ), (2 : ℕ) * x2.card ^ (2 : ℕ) ≤ x1 + (1 : ℕ) → (∀ x5 ∉ x2, x3 x5 = (0 : ℝ)) → ∃ (x6 : Finset (ZMod (x1 + (1 : ℕ)))), ↑(x1 + (1 : ℕ)) / (2 : ℝ) ≤ ↑x6.card ∧ ∀ x7 ∈ x6, ∑ x9 : ZMod (x1 + (1 : ℕ)), x3 x9 * x3 (x7 - x9) = (0 : ℝ)) := by
  classical
  intro n A f hsize hsupp
  let sums := (A ×ˢ A).image (fun ab => ab.1 + ab.2)
  have hs : sums.card ≤ A.card ^ 2 := by
    simpa [sums, Finset.card_product, pow_two] using
      (Finset.card_image_le (s := A ×ˢ A) (f := fun ab => ab.1 + ab.2))
  refine ⟨sumsᶜ, ?_, ?_⟩
  · have hc : sumsᶜ.card + sums.card = n + 1 := by
      simpa only [ZMod.card] using Finset.card_compl_add_card sums
    have hhalf : n + 1 ≤ 2 * sumsᶜ.card := by omega
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    rw [mul_comm]
    exact_mod_cast hhalf
  · intro m hm
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : x ∈ A
    · have hn : m-x ∉ A := by
        intro h
        apply (Finset.mem_compl.mp hm)
        exact Finset.mem_image.mpr ⟨(x,m-x), Finset.mem_product.mpr ⟨hx,h⟩, by simp⟩
      rw [hsupp _ hn, mul_zero]
    · rw [hsupp _ hx, zero_mul]
