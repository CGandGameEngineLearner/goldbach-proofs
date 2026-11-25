import Mathlib

namespace PEqualNP.Outside

theorem L_no_three_in_line_cert_5_2 (n : ℕ) :
    (((Finset.range n).product (Finset.range n)).filter
      (fun z => z.1 + 10 < n ∧ z.2 + 4 < n)).card = (n - 10) * (n - 4) := by
  have hcount (k : ℕ) :
      (Finset.range n).filter (fun x => x + k < n) = Finset.range (n - k) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range]
    omega

  have hfilter :
      ((Finset.range n).product (Finset.range n)).filter
          (fun z => z.1 + 10 < n ∧ z.2 + 4 < n) =
        ((Finset.range n).filter (fun x => x + 10 < n)).product
          ((Finset.range n).filter (fun y => y + 4 < n)) := by
    ext z
    rcases z with ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_product, Prod.mk_fst, Prod.mk_snd]
    tauto

  rw [hfilter, hcount 10, hcount 4, Finset.card_product]
  simp

end PEqualNP.Outside
