import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_cert_14_5 :
    ∀ n:ℕ, (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z => z.1+28<n ∧ z.2+10<n)).card=(n-28)*(n-10) := by
  intro n
  have h : (((Finset.range n) ×ˢ (Finset.range n)).filter (fun z : ℕ × ℕ => z.1+28<n ∧ z.2+10<n))
      = (Finset.range (n-28)) ×ˢ (Finset.range (n-10)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  rw [h, Finset.card_product, Finset.card_range, Finset.card_range]
