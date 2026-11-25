import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_19_2 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+38<n ∧ z.2+4<n)).card=(n-38)*(n-4) := by
  intro n
  have e0 : ((Finset.range n).product (Finset.range n)).filter (fun z => z.1+38<n ∧ z.2+4<n)
      = (Finset.range (n-38)).product (Finset.range (n-4)) := by
    ext z
    simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [e0]
  simp [Finset.card_product]
