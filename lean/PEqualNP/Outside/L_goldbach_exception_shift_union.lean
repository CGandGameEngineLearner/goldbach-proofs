import Mathlib

theorem PEqualNP.Outside.L_goldbach_exception_shift_union :
    ∀ (I H : Finset ℕ) (P : ℕ → Bool),
      (I.filter (fun n => (H.filter (fun h => P (n + h) = true)).Nonempty)).card ≤
        Finset.sum H (fun h => (I.filter (fun n => P (n + h) = true)).card) := by
  intro I H P
  let hits (h : ℕ) := I.filter (fun n => P (n + h) = true)
  apply le_trans (b := (H.biUnion hits).card) _ Finset.card_biUnion_le
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hnI, h, hh⟩ := Finset.mem_filter.mp hn
  obtain ⟨hhH, hhit⟩ := Finset.mem_filter.mp hh
  exact Finset.mem_biUnion.mpr ⟨h, hhH, Finset.mem_filter.mpr ⟨hnI, hhit⟩⟩
