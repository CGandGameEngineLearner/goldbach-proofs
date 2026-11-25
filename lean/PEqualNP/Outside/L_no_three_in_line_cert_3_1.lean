import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_3_1 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+6<n ∧ z.2+2<n)).card=(n-6)*(n-2) := by
  intro n
  have h : ((Finset.range n).product (Finset.range n)).filter
      (fun z => z.1 + 6 < n ∧ z.2 + 2 < n) =
      (Finset.range (n - 6)).product (Finset.range (n - 2)) := by
    ext z
    simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [h]
  simp only [Finset.product_eq_sprod, Finset.card_product, Finset.card_range]
