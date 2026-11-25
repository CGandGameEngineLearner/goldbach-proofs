import Mathlib

/-- Difference of two even naturals (in `ℕ`) is even. -/
private lemma gb_even_sub {m n : ℕ} (hm : Even m) (hn : Even n) : Even (m - n) := by
  obtain ⟨k, hk⟩ := hm
  obtain ⟨l, hl⟩ := hn
  rw [hk, hl]
  exact ⟨k - l, by omega⟩

theorem PEqualNP.Outside.L_goldbach_minor_neighbor_odd_support : ∀ (n r a b : ℕ), 8 ≤ n → Even n → ¬ Even r → Nat.Prime a → Nat.Prime b → n < a^3 → n < b^3 → a+b ≠ n+r ∧ a+b ≠ n-r := by
  intro n r a b hn8 hne hnr ha hb ha3 hb3
  have ha2 : a ≠ 2 := by
    intro h
    rw [h] at ha3
    norm_num at ha3
    omega
  have hb2 : b ≠ 2 := by
    intro h
    rw [h] at hb3
    norm_num at hb3
    omega
  have hodd_a : Odd a := ha.odd_of_ne_two ha2
  have hodd_b : Odd b := hb.odd_of_ne_two hb2
  have heven_ab : Even (a + b) := hodd_a.add_odd hodd_b
  have hab4 : 4 ≤ a + b := by
    have h2a := ha.two_le
    have h2b := hb.two_le
    omega
  refine ⟨?_, ?_⟩
  · intro h
    have hr : Even r := by
      have hr' : r = a + b - n := by omega
      rw [hr']
      exact gb_even_sub heven_ab hne
    exact hnr hr
  · intro h
    have hr : Even r := by
      have hr' : r = n - (a + b) := by omega
      rw [hr']
      exact gb_even_sub hne heven_ab
    exact hnr hr