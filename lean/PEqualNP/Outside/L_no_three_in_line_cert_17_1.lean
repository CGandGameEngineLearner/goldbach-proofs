import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_17_1 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+34<n ∧ z.2+2<n)).card=(n-34)*(n-2) := by
  intro n
  have e0 : ((Finset.range n).product (Finset.range n)).filter (fun z => z.1+34<n ∧ z.2+2<n)
      = (Finset.range (n-34)).product (Finset.range (n-2)) := by
    ext z
    simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [e0]
  simp [Finset.card_product]
