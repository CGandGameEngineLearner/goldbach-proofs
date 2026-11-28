import Mathlib

open Finset
open scoped BigOperators

theorem Conjectures.Cuts.Taska4d06654f086b83844140db4 : (∀ (x1 : ℕ), (0 : ℝ) < ↑{x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (13 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (13 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))}.card → ∃ (x3 : ℕ) (x4 : ℕ) (x5 : Fin (13 : ℕ) → ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ x1 = x3 + x4 + ∑ x6 : Fin (13 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ))) := by
  intro x1 hpos
  have hcard : 0 < {x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (13 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (13 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))}.card :=
    (Nat.cast_pos).mp hpos
  obtain ⟨⟨p, e⟩, hmem⟩ := Finset.card_pos.mp hcard
  rw [Finset.mem_filter] at hmem
  obtain ⟨-, hp, hq⟩ := hmem
  refine ⟨p, x1 - (p + ∑ j : Fin (13 : ℕ), (2 : ℕ) ^ (e j + (1 : ℕ))), e, hp, hq, ?_⟩
  have hne : x1 - (p + ∑ j : Fin (13 : ℕ), (2 : ℕ) ^ (e j + (1 : ℕ))) ≠ 0 := Nat.Prime.ne_zero hq
  have hlt : p + ∑ j : Fin (13 : ℕ), (2 : ℕ) ^ (e j + (1 : ℕ)) < x1 := by
    by_contra hc
    exact hne (Nat.sub_eq_zero_of_le (Nat.not_lt.mp hc))
  have h := Nat.sub_add_cancel hlt
  omega
