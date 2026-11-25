import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_6_1 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+12<n ∧ z.2+2<n)).card=(n-12)*(n-2) := by
  intro n
  have starts :
      (((Finset.range n).product (Finset.range n)).filter
        (fun z => z.1 + 12 < n ∧ z.2 + 2 < n)) =
        (Finset.range (n - 12)).product (Finset.range (n - 2)) := by
    ext ⟨x, y⟩
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [starts, Finset.product_eq_sprod, Finset.card_product, Finset.card_range, Finset.card_range]
