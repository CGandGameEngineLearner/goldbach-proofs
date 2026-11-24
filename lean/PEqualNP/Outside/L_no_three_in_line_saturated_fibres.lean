import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_saturated_fibres :
    let valid := fun (n : ℕ) (S : Finset (ℕ × ℕ)) => (∀ z ∈ S, z.1 < n ∧ z.2 < n) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠ ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))); ∀ (n : ℕ) (S : Finset (ℕ × ℕ)), valid n S → S.card = 2*n → ∀ i < n, (S.filter (fun z => z.1 = i)).card = 2 ∧ (S.filter (fun z => z.2 = i)).card = 2 := by
  dsimp only
  intro n S hvalid hcard i hi
  obtain ⟨hbound, hdet⟩ := hvalid
  have hrow : ∀ j, (S.filter (fun z => z.1 = j)).card ≤ 2 := by
    intro j
    by_contra hcon
    have h3 : 2 < (S.filter (fun z => z.1 = j)).card := by omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    have hbS : b ∈ S := (Finset.mem_filter.mp hb).1
    have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
    have ha1 : a.1 = j := (Finset.mem_filter.mp ha).2
    have hb1 : b.1 = j := (Finset.mem_filter.mp hb).2
    have hc1 : c.1 = j := (Finset.mem_filter.mp hc).2
    have hdet' := hdet a haS b hbS c hcS hab hac hbc
    simp [ha1, hb1, hc1] at hdet'
  have hcol : ∀ j, (S.filter (fun z => z.2 = j)).card ≤ 2 := by
    intro j
    by_contra hcon
    have h3 : 2 < (S.filter (fun z => z.2 = j)).card := by omega
    obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp h3
    have haS : a ∈ S := (Finset.mem_filter.mp ha).1
    have hbS : b ∈ S := (Finset.mem_filter.mp hb).1
    have hcS : c ∈ S := (Finset.mem_filter.mp hc).1
    have ha2 : a.2 = j := (Finset.mem_filter.mp ha).2
    have hb2 : b.2 = j := (Finset.mem_filter.mp hb).2
    have hc2 : c.2 = j := (Finset.mem_filter.mp hc).2
    have hdet' := hdet a haS b hbS c hcS hab hac hbc
    simp [ha2, hb2, hc2] at hdet'
  have hrowSum : S.card = ∑ j ∈ Finset.range n, (S.filter (fun z => z.1 = j)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun z : ℕ × ℕ => z.1) (t := Finset.range n)
      (fun z hz => Finset.mem_range.mpr (hbound z hz).1)
  have hcolSum : S.card = ∑ j ∈ Finset.range n, (S.filter (fun z => z.2 = j)).card :=
    Finset.card_eq_sum_card_fiberwise (f := fun z : ℕ × ℕ => z.2) (t := Finset.range n)
      (fun z hz => Finset.mem_range.mpr (hbound z hz).2)
  have hconst : (∑ j ∈ Finset.range n, 2) = n * 2 := by simp
  have hrowEq : ∀ j ∈ Finset.range n, (S.filter (fun z => z.1 = j)).card = 2 := by
    have hsum : (∑ j ∈ Finset.range n, (S.filter (fun z => z.1 = j)).card) = (∑ j ∈ Finset.range n, 2) := by
      rw [← hrowSum, hcard, hconst]
      exact Nat.mul_comm 2 n
    exact (Finset.sum_eq_sum_iff_of_le (f := fun j => (S.filter (fun z => z.1 = j)).card) (g := fun _ => 2) (fun j _ => hrow j)).mp hsum
  have hcolEq : ∀ j ∈ Finset.range n, (S.filter (fun z => z.2 = j)).card = 2 := by
    have hsum : (∑ j ∈ Finset.range n, (S.filter (fun z => z.2 = j)).card) = (∑ j ∈ Finset.range n, 2) := by
      rw [← hcolSum, hcard, hconst]
      exact Nat.mul_comm 2 n
    exact (Finset.sum_eq_sum_iff_of_le (f := fun j => (S.filter (fun z => z.2 = j)).card) (g := fun _ => 2) (fun j _ => hcol j)).mp hsum
  exact ⟨hrowEq i (Finset.mem_range.mpr hi), hcolEq i (Finset.mem_range.mpr hi)⟩
