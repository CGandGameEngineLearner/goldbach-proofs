import Mathlib

/-!
`L-no-three-in-line-cut-7d02ba3dd0f8fea494d84e98` — child of the no-three-in-line density cut.

If a finite grid set has at most two points in every row and every column, then any strictly
lexicographically ordered collinear triple `a <lex b <lex c` has strictly increasing
first coordinates and `a.2 ≠ b.2`.

Proof idea: a triple sharing a first coordinate would put three points of `T` in one column,
and a triple with `a.2 = b.2` (after the first step) would put three points in one row; both
contradict the row/column bounds of two.
-/

namespace GoldbachCutNoThreeInLine

/-- Three distinct members of `T` with the same first coordinate force a column of card ≥ 3. -/
theorem card3_col {T : Finset (ℕ × ℕ)} {k : ℕ} {p q r : ℕ × ℕ}
    (hpT : p ∈ T) (hqT : q ∈ T) (hrT : r ∈ T)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : p.1 = k) (hq : q.1 = k) (hr : r.1 = k) :
    3 ≤ {x ∈ T | x.1 = k}.card := by
  have hsub : ({p, q, r} : Finset (ℕ × ℕ)) ⊆ {x ∈ T | x.1 = k} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · exact ⟨hpT, hp⟩
    · exact ⟨hqT, hq⟩
    · exact ⟨hrT, hr⟩
  have hcard : ({p, q, r} : Finset (ℕ × ℕ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
  calc (3 : ℕ) = ({p, q, r} : Finset (ℕ × ℕ)).card := hcard.symm
    _ ≤ {x ∈ T | x.1 = k}.card := Finset.card_le_card hsub

/-- Three distinct members of `T` with the same second coordinate force a row of card ≥ 3. -/
theorem card3_row {T : Finset (ℕ × ℕ)} {k : ℕ} {p q r : ℕ × ℕ}
    (hpT : p ∈ T) (hqT : q ∈ T) (hrT : r ∈ T)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hp : p.2 = k) (hq : q.2 = k) (hr : r.2 = k) :
    3 ≤ {x ∈ T | x.2 = k}.card := by
  have hsub : ({p, q, r} : Finset (ℕ × ℕ)) ⊆ {x ∈ T | x.2 = k} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_filter] at hx ⊢
    rcases hx with rfl | rfl | rfl
    · exact ⟨hpT, hp⟩
    · exact ⟨hqT, hq⟩
    · exact ⟨hrT, hr⟩
  have hcard : ({p, q, r} : Finset (ℕ × ℕ)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
  calc (3 : ℕ) = ({p, q, r} : Finset (ℕ × ℕ)).card := hcard.symm
    _ ≤ {x ∈ T | x.2 = k}.card := Finset.card_le_card hsub

end GoldbachCutNoThreeInLine

theorem Conjectures.Cuts.Task7d02ba3dd0f8fea494d84e98 :
    ∀ (x1 : Finset (ℕ × ℕ)), (∀ (x2 : ℕ), {x3 ∈ x1 | x3.1 = x2}.card ≤ (2 : ℕ)) → (∀ (x3 : ℕ), {x4 ∈ x1 | x4.2 = x3}.card ≤ (2 : ℕ)) → ∀ x4 ∈ x1, ∀ x6 ∈ x1, ∀ x8 ∈ x1, x4.1 < x6.1 ∨ x4.1 = x6.1 ∧ x4.2 < x6.2 → x6.1 < x8.1 ∨ x6.1 = x8.1 ∧ x6.2 < x8.2 → ((↑x6.1 : ℤ) - (↑x4.1 : ℤ)) * ((↑x8.2 : ℤ) - (↑x4.2 : ℤ)) = ((↑x6.2 : ℤ) - (↑x4.2 : ℤ)) * ((↑x8.1 : ℤ) - (↑x4.1 : ℤ)) → x4.1 < x6.1 ∧ x6.1 < x8.1 ∧ x4.2 ≠ x6.2 := by
  intro T hrow hcol A hA B hB C hC hAB hBC hcolin
  -- distinctness from the two strict lexicographic comparisons
  have hABne : A ≠ B := by
    rintro rfl
    rcases hAB with h | ⟨h, _⟩ <;> omega
  have hBCne : B ≠ C := by
    rintro rfl
    rcases hBC with h | ⟨h, _⟩ <;> omega
  have hACne : A ≠ C := by
    rintro rfl
    rcases hAB with h | ⟨h, _⟩ <;> rcases hBC with h' | ⟨h', _⟩ <;> omega
  -- Step 1: `A.1 < B.1`
  have step1 : A.1 < B.1 := by
    rcases hAB with h | ⟨h, hlt⟩
    · exact h
    · exfalso
      have hzero : ((↑B.1 : ℤ) - (↑A.1 : ℤ)) = 0 := by
        rw [h]; ring
      have hprod : ((↑B.2 : ℤ) - (↑A.2 : ℤ)) * ((↑C.1 : ℤ) - (↑A.1 : ℤ)) = 0 := by
        rw [hzero, zero_mul] at hcolin
        linarith [hcolin]
      have hB2ne : ((↑B.2 : ℤ) - (↑A.2 : ℤ)) ≠ 0 := by
        have : (A.2 : ℤ) < (B.2 : ℤ) := by exact_mod_cast hlt
        omega
      have hC1 : C.1 = A.1 := by
        have : ((↑C.1 : ℤ) - (↑A.1 : ℤ)) = 0 := by
          rcases mul_eq_zero.mp hprod with h' | h'
          · exact absurd h' hB2ne
          · exact h'
        have := this
        omega
      have h3 := GoldbachCutNoThreeInLine.card3_col (T := T) (k := A.1)
        hA hB hC hABne hACne hBCne rfl h.symm hC1
      have := hrow A.1
      omega
  -- Step 2: `B.1 < C.1`
  have step2 : B.1 < C.1 := by
    rcases hBC with h | ⟨h, hlt⟩
    · exact h
    · exfalso
      have hzero : ((↑C.1 : ℤ) - (↑B.1 : ℤ)) = 0 := by
        rw [h]; ring
      have hprod : ((↑B.1 : ℤ) - (↑A.1 : ℤ)) * ((↑C.2 : ℤ) - (↑A.2 : ℤ))
          = ((↑B.2 : ℤ) - (↑A.2 : ℤ)) * ((↑B.1 : ℤ) - (↑A.1 : ℤ)) := by
        rw [← h] at hcolin
        exact hcolin
      have hB1ne : ((↑B.1 : ℤ) - (↑A.1 : ℤ)) ≠ 0 := by
        have : (A.1 : ℤ) < (B.1 : ℤ) := by exact_mod_cast step1
        omega
      have hC2 : C.2 = B.2 := by
        have := hprod
        -- cancel the common nonzero factor
        have hcancel : ((↑C.2 : ℤ) - (↑A.2 : ℤ)) = ((↑B.2 : ℤ) - (↑A.2 : ℤ)) := by
          apply mul_left_cancel₀ hB1ne
          linarith [hprod]
        omega
      omega
  refine ⟨step1, step2, ?_⟩
  -- Step 3: `A.2 ≠ B.2`
  rintro hAB2
  exfalso
  have hzero : ((↑B.2 : ℤ) - (↑A.2 : ℤ)) = 0 := by
    rw [hAB2]; ring
  have hprod : ((↑B.1 : ℤ) - (↑A.1 : ℤ)) * ((↑C.2 : ℤ) - (↑A.2 : ℤ)) = 0 := by
    rw [hzero, zero_mul] at hcolin
    linarith [hcolin]
  have hB1ne : ((↑B.1 : ℤ) - (↑A.1 : ℤ)) ≠ 0 := by
    have : (A.1 : ℤ) < (B.1 : ℤ) := by exact_mod_cast step1
    omega
  have hC2 : C.2 = A.2 := by
    rcases mul_eq_zero.mp hprod with h' | h'
    · exact absurd h' hB1ne
    · omega
  have h3 := GoldbachCutNoThreeInLine.card3_row (T := T) (k := A.2)
    hA hB hC hABne hACne hBCne rfl hAB2.symm hC2
  have := hcol A.2
  omega
