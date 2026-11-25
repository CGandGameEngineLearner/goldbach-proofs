import Mathlib

/-- The allowable starts of a triple with stride `(11, 3)` form a product of ranges. -/
theorem PEqualNP.Outside.L_no_three_in_line_cert_11_3 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+22<n ∧ z.2+6<n)).card=(n-22)*(n-6) := by
  intro n
  have h : ((Finset.range n).product (Finset.range n)).filter
      (fun z => z.1 + 22 < n ∧ z.2 + 6 < n) =
      (Finset.range (n - 22)).product (Finset.range (n - 6)) := by
    apply Finset.ext
    intro z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    constructor
    · rintro ⟨_, hx, hy⟩
      exact ⟨by omega, by omega⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  simp only [h, Finset.card_product, Finset.card_range]
