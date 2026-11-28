import Mathlib

theorem Conjectures.Cuts.Task7d02ba3dd0f8fea494d84e98 : (∀ (x1 : Finset (ℕ × ℕ)), (∀ (x2 : ℕ), {x3 ∈ x1 | x3.1 = x2}.card ≤ (2 : ℕ)) → (∀ (x3 : ℕ), {x4 ∈ x1 | x4.2 = x3}.card ≤ (2 : ℕ)) → ∀ x4 ∈ x1, ∀ x6 ∈ x1, ∀ x8 ∈ x1, x4.1 < x6.1 ∨ x4.1 = x6.1 ∧ x4.2 < x6.2 → x6.1 < x8.1 ∨ x6.1 = x8.1 ∧ x6.2 < x8.2 → ((↑x6.1 : ℤ) - (↑x4.1 : ℤ)) * ((↑x8.2 : ℤ) - (↑x4.2 : ℤ)) = ((↑x6.2 : ℤ) - (↑x4.2 : ℤ)) * ((↑x8.1 : ℤ) - (↑x4.1 : ℤ)) → x4.1 < x6.1 ∧ x6.1 < x8.1 ∧ x4.2 ≠ x6.2) := by
  intro T hrow hcol a ha b hb c hc hab hbc hdet
  have col3 : ∀ u v w : ℕ × ℕ, u ∈ T → v ∈ T → w ∈ T → u ≠ v → u ≠ w → v ≠ w →
      u.1 = v.1 → u.1 = w.1 → False := by
    intro u v w hu hv hw huv huw hvw h1 h2
    have hsub : ({u, v, w} : Finset (ℕ × ℕ)) ⊆ {x ∈ T | x.1 = u.1} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hu, rfl⟩
      · exact Finset.mem_filter.mpr ⟨hv, h1.symm⟩
      · exact Finset.mem_filter.mpr ⟨hw, h2.symm⟩
    have h3 : ({u, v, w} : Finset (ℕ × ℕ)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [huv, huw]),
        Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]
    have h4 := Finset.card_le_card hsub
    have h5 := hrow u.1
    omega
  have row3 : ∀ u v w : ℕ × ℕ, u ∈ T → v ∈ T → w ∈ T → u ≠ v → u ≠ w → v ≠ w →
      u.2 = v.2 → u.2 = w.2 → False := by
    intro u v w hu hv hw huv huw hvw h1 h2
    have hsub : ({u, v, w} : Finset (ℕ × ℕ)) ⊆ {x ∈ T | x.2 = u.2} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hu, rfl⟩
      · exact Finset.mem_filter.mpr ⟨hv, h1.symm⟩
      · exact Finset.mem_filter.mpr ⟨hw, h2.symm⟩
    have h3 : ({u, v, w} : Finset (ℕ × ℕ)).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [huv, huw]),
        Finset.card_insert_of_notMem (by simp [hvw]), Finset.card_singleton]
    have h4 := Finset.card_le_card hsub
    have h5 := hcol u.2
    omega
  have lexne : ∀ u v : ℕ × ℕ, (u.1 < v.1 ∨ u.1 = v.1 ∧ u.2 < v.2) → u ≠ v := by
    intro u v h he
    rw [he] at h
    omega
  have hne_ab := lexne a b hab
  have hne_bc := lexne b c hbc
  have h1 : a.1 < b.1 := by
    rcases hab with h | ⟨h, h2⟩
    · exact h
    · exfalso
      have hb1 : ((b.1 : ℤ) - (a.1 : ℤ)) = 0 := by omega
      rw [hb1, zero_mul] at hdet
      rcases mul_eq_zero.mp hdet.symm with hz | hz
      · omega
      · have hca : c.1 = a.1 := by omega
        have hac : a ≠ c := by
          intro he
          have hs : a.2 = c.2 := by rw [he]
          rcases hbc with h' | ⟨h', h''⟩ <;> omega
        exact col3 a b c ha hb hc hne_ab hac hne_bc h hca.symm
  have h2' : b.1 < c.1 := by
    rcases hbc with h | ⟨h, h2c⟩
    · exact h
    · exfalso
      have hf : ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (b.2 : ℤ)) = 0 := by
        have hc1 : ((c.1 : ℤ)) = (b.1 : ℤ) := by omega
        linear_combination hdet + ((b.2 : ℤ) - (a.2 : ℤ)) * hc1
      rcases mul_eq_zero.mp hf with hz | hz
      · omega
      · omega
  have h3 : a.2 ≠ b.2 := by
    intro he
    have hb2 : ((b.2 : ℤ) - (a.2 : ℤ)) = 0 := by omega
    rw [hb2, zero_mul] at hdet
    rcases mul_eq_zero.mp hdet with hz | hz
    · omega
    · have hca : c.2 = a.2 := by omega
      have hac : a ≠ c := by
        intro heq
        have hs : a.1 = c.1 := by rw [heq]
        omega
      exact row3 a b c ha hb hc hne_ab hac hne_bc he hca.symm
  exact ⟨h1, h2', h3⟩
