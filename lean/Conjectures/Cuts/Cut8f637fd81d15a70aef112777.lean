import Mathlib

theorem Conjectures.Cuts.Cut8f637fd81d15a70aef112777 (h₁ : True) (h₂ : True) : (∀ (x1 : Finset (ℕ × ℕ)), (∀ (x2 : ℕ), {x3 ∈ x1 | x3.1 = x2}.card ≤ (2 : ℕ)) → (∀ (x3 : ℕ), {x4 ∈ x1 | x4.2 = x3}.card ≤ (2 : ℕ)) → ∀ x4 ∈ x1, ∀ x6 ∈ x1, ∀ x8 ∈ x1, x4.1 < x6.1 ∨ x4.1 = x6.1 ∧ x4.2 < x6.2 → x6.1 < x8.1 ∨ x6.1 = x8.1 ∧ x6.2 < x8.2 → ((↑x6.1 : ℤ) - (↑x4.1 : ℤ)) * ((↑x8.2 : ℤ) - (↑x4.2 : ℤ)) = ((↑x6.2 : ℤ) - (↑x4.2 : ℤ)) * ((↑x8.1 : ℤ) - (↑x4.1 : ℤ)) → x4.1 < x6.1 ∧ x6.1 < x8.1 ∧ x4.2 ≠ x6.2) := by
  have := h₁
  have := h₂
  intro x1 hcol hrow x4 h4 x6 h6 x8 h8 h46 h68 hdet
  have h46ne : x4 ≠ x6 := by
    rintro rfl
    rcases h46 with h | ⟨h, hy⟩ <;> omega
  have h68ne : x6 ≠ x8 := by
    rintro rfl
    rcases h68 with h | ⟨h, hy⟩ <;> omega
  have col3 : ∀ (p q r : ℕ × ℕ), p ∈ x1 → q ∈ x1 → r ∈ x1 → p.1 = q.1 → p.1 = r.1 → p ≠ q → q ≠ r → p ≠ r → False := by
    intro p q r hp hq hr hpq hpr hpqne hqrne hprne
    have hsub : ({p, q, r} : Finset (ℕ × ℕ)) ⊆ x1.filter (fun z => z.1 = p.1) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hz ⊢
      rcases hz with rfl | rfl | rfl
      · exact ⟨hp, rfl⟩
      · exact ⟨hq, hpq.symm⟩
      · exact ⟨hr, hpr.symm⟩
    have h3 : ({p, q, r} : Finset (ℕ × ℕ)).card = 3 := by
      simp [hpqne, hqrne, hprne]
    have hle := Finset.card_le_card hsub
    have hcc := hcol p.1
    omega
  have row3 : ∀ (p q r : ℕ × ℕ), p ∈ x1 → q ∈ x1 → r ∈ x1 → p.2 = q.2 → p.2 = r.2 → p ≠ q → q ≠ r → p ≠ r → False := by
    intro p q r hp hq hr hpq hpr hpqne hqrne hprne
    have hsub : ({p, q, r} : Finset (ℕ × ℕ)) ⊆ x1.filter (fun z => z.2 = p.2) := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hz ⊢
      rcases hz with rfl | rfl | rfl
      · exact ⟨hp, rfl⟩
      · exact ⟨hq, hpq.symm⟩
      · exact ⟨hr, hpr.symm⟩
    have h3 : ({p, q, r} : Finset (ℕ × ℕ)).card = 3 := by
      simp [hpqne, hqrne, hprne]
    have hle := Finset.card_le_card hsub
    have hrr := hrow p.2
    omega
  have hA : x4.1 < x6.1 := by
    rcases h46 with h | ⟨h, hlt⟩
    · exact h
    · exfalso
      have hz : ((x6.1 : ℤ) - (x4.1 : ℤ)) = 0 := by rw [← h]; simp
      rw [hz, zero_mul] at hdet
      have hne : ((x6.2 : ℤ) - (x4.2 : ℤ)) ≠ 0 := by omega
      have h8x : ((x8.1 : ℤ) - (x4.1 : ℤ)) = 0 := by
        rcases mul_eq_zero.mp hdet.symm with h' | h'
        · exact absurd h' hne
        · exact h'
      have h81 : x8.1 = x4.1 := by omega
      exact col3 x4 x6 x8 h4 h6 h8 h h81.symm h46ne h68ne (by rintro rfl; rcases h68 with h' | ⟨h', hy⟩ <;> omega)
  have hB : x6.1 < x8.1 := by
    rcases h68 with h | ⟨h, hlt⟩
    · exact h
    · exfalso
      have hcast : ((x8.1 : ℤ) - (x4.1 : ℤ)) = ((x6.1 : ℤ) - (x4.1 : ℤ)) := by rw [← h]
      rw [hcast] at hdet
      have hAne : ((x6.1 : ℤ) - (x4.1 : ℤ)) ≠ 0 := by omega
      have h3 : ((x6.1 : ℤ) - (x4.1 : ℤ)) * (((x8.2 : ℤ) - (x4.2 : ℤ)) - ((x6.2 : ℤ) - (x4.2 : ℤ))) = 0 := by
        rw [mul_sub, hdet, mul_comm ((x6.2 : ℤ) - (x4.2 : ℤ)) ((x6.1 : ℤ) - (x4.1 : ℤ)), sub_self]
      rcases mul_eq_zero.mp h3 with h' | h'
      · exact absurd h' hAne
      · omega
  have hC : x4.2 ≠ x6.2 := by
    rintro heq
    have hz : ((x6.2 : ℤ) - (x4.2 : ℤ)) = 0 := by rw [← heq]; simp
    rw [hz, zero_mul] at hdet
    have hAne : ((x6.1 : ℤ) - (x4.1 : ℤ)) ≠ 0 := by omega
    have h8y : ((x8.2 : ℤ) - (x4.2 : ℤ)) = 0 := by
      rcases mul_eq_zero.mp hdet with h' | h'
      · exact absurd h' hAne
      · exact h'
    have h82 : x8.2 = x4.2 := by omega
    exact row3 x4 x6 x8 h4 h6 h8 heq h82.symm (by rintro rfl; omega) (by rintro rfl; omega) (by rintro rfl; omega)
  exact ⟨hA, hB, hC⟩
