import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_14_5 :
    ∀ n:ℕ, (((Finset.range n).product (Finset.range n)).filter (fun z => z.1+28<n ∧ z.2+10<n)).card=(n-28)*(n-10) := by
  intro n
  have e0 : ((Finset.range n).product (Finset.range n)).filter (fun z => z.1+28<n ∧ z.2+10<n)
      = (Finset.range (n-28)).product (Finset.range (n-10)) := by
    ext z
    simp [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [e0]
  simp [Finset.card_product]
