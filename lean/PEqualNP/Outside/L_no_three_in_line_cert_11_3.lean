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
    constructor
    · intro hz
      obtain ⟨_, hx, hy⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
    · intro hz
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hz
      have hx' := Finset.mem_range.mp hx
      have hy' := Finset.mem_range.mp hy
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
          by omega, by omega⟩
  rw [h]
  calc
    ((Finset.range (n - 22)).product (Finset.range (n - 6))).card =
        (Finset.range (n - 22)).card * (Finset.range (n - 6)).card :=
      Finset.card_product _ _
    _ = (n - 22) * (n - 6) := by simp only [Finset.card_range]
