import Mathlib

theorem Conjectures.Cuts.Task897953a760185a640f834ad8 :
    ∀ (x1 : ℕ) (x2 : Finset (ZMod (x1 + (1 : ℕ)))) (x3 : ZMod (x1 + (1 : ℕ)) → ℝ),
      (2 : ℕ) * x2.card ^ (2 : ℕ) ≤ x1 + (1 : ℕ) →
      (∀ x5 ∉ x2, x3 x5 = (0 : ℝ)) →
      ∃ (x6 : Finset (ZMod (x1 + (1 : ℕ)))),
        ↑(x1 + (1 : ℕ)) / (2 : ℝ) ≤ ↑x6.card ∧
        ∀ x7 ∈ x6, ∑ x9 : ZMod (x1 + (1 : ℕ)), x3 x9 * x3 (x7 - x9) = (0 : ℝ) := by
  intro x1 x2 x3 hcard hsupp
  classical
  set S : Finset (ZMod (x1 + 1)) := (x2 ×ˢ x2).image (fun p => p.1 + p.2)
  refine ⟨Sᶜ, ?_, ?_⟩
  · have hS : S.card ≤ x2.card ^ 2 := by
      calc S.card ≤ (x2 ×ˢ x2).card := Finset.card_image_le
        _ = x2.card * x2.card := Finset.card_product x2 x2
        _ = x2.card ^ 2 := by ring
    have hS' : S.card ≤ x1 + 1 := by omega
    have hcomp : (Sᶜ).card = (x1 + 1) - S.card := by
      rw [Finset.card_compl, ZMod.card]
    have hreal : (2 : ℝ) * (x2.card : ℝ) ^ 2 ≤ ((x1 + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    have hcast : (((x1 + 1) - S.card : ℕ) : ℝ) = ((x1 + 1 : ℕ) : ℝ) - (S.card : ℝ) :=
      Nat.cast_sub hS'
    have hle : (S.card : ℝ) ≤ (x2.card : ℝ) ^ 2 := by
      have h : (S.card : ℝ) ≤ ((x2.card ^ 2 : ℕ) : ℝ) := Nat.cast_le.mpr hS
      push_cast at h
      linarith
    rw [hcomp, hcast]
    linarith
  · intro x7 hx7
    have hmem : x7 ∉ S := Finset.mem_compl.mp hx7
    refine Finset.sum_eq_zero (fun x9 _ => ?_)
    by_cases h1 : x9 ∈ x2
    · by_cases h2 : x7 - x9 ∈ x2
      · exfalso
        apply hmem
        refine Finset.mem_image.mpr ⟨(x9, x7 - x9), Finset.mem_product.mpr ⟨h1, h2⟩, ?_⟩
        ring
      · rw [hsupp _ h2, mul_zero]
    · rw [hsupp _ h1, zero_mul]
