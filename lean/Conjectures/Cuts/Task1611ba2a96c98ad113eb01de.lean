import Mathlib

open scoped BigOperators

theorem Conjectures.Cuts.Task1611ba2a96c98ad113eb01de :
    ∀ (x1 : ℕ), (0 : ℝ) < ↑{x2 ∈ (Finset.range (x1 + (1 : ℕ))).product (Fintype.piFinset fun (x2 : Fin (6 : ℕ)) => Finset.range (x1 + (1 : ℕ))) | Nat.Prime x2.1 ∧ Nat.Prime (x1 - (x2.1 + ∑ x3 : Fin (6 : ℕ), (2 : ℕ) ^ (x2.2 x3 + (1 : ℕ))))}.card → ∃ (x3 : ℕ) (x4 : ℕ), Nat.Prime x3 ∧ Nat.Prime x4 ∧ ∃ (x5 : Fin (6 : ℕ) → ℕ), x1 = x3 + x4 + ∑ x6 : Fin (6 : ℕ), (2 : ℕ) ^ (x5 x6 + (1 : ℕ)) := by
  classical
  intro N h
  let admissible :=
    ((Finset.range (N + 1)).product
      (Fintype.piFinset (fun _ : Fin 6 => Finset.range (N + 1)))).filter
        (fun w => Nat.Prime w.1 ∧
          Nat.Prime (N - (w.1 + ∑ i : Fin 6, 2 ^ (w.2 i + 1))))
  change 0 < (admissible.card : ℝ) at h
  have hcount : 0 < admissible.card := by exact_mod_cast h
  obtain ⟨⟨p, a⟩, hw⟩ := Finset.card_pos.mp hcount
  have hpq := (Finset.mem_filter.mp hw).2
  let powers : ℕ := ∑ i : Fin 6, 2 ^ (a i + 1)
  change Nat.Prime p ∧ Nat.Prime (N - (p + powers)) at hpq
  -- Primality of the second summand rules out truncation in the natural subtraction.
  have hq : 0 < N - (p + powers) := hpq.2.pos
  refine ⟨p, N - (p + powers), hpq.1, hpq.2, a, ?_⟩
  change N = p + (N - (p + powers)) + powers
  omega
