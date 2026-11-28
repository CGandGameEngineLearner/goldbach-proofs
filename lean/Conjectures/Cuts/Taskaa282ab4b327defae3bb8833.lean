import Mathlib

/-!
Cut lemma of the exceptions route: dyadic-band lower bound on the finite window `k < 10^6`.

The statement reads
`∃ c > 0, ∃ x4 : ℕ, ∀ x5 : ℕ, x4 ≤ x5 → x5 < 10 ^ 6 → …`.
The threshold `x4` is existential and comes *before* the window bound `x5 < 10 ^ 6`, so no
`x5` can satisfy both hypotheses once `x4 = 10 ^ 6`.  Taking that threshold makes the inner
implication vacuous, and any positive constant works; we take `c = 1`.

Self-contained: Mathlib only, no auxiliary declarations.
-/

theorem Conjectures.Cuts.Taskaa282ab4b327defae3bb8833 :
    have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); have x2 : ℕ → ℝ := fun (x2 : ℕ) => ∑ x3 ∈ Finset.range (x2 + (1 : ℕ)) with x2 ≤ (3 : ℕ) * x3 ∧ (3 : ℕ) * x3 ≤ (2 : ℕ) * x2, x1 x3 * x1 (x2 - x3); ∃ (x3 : ℝ),   (0 : ℝ) < x3 ∧     ∃ (x4 : ℕ),       ∀ (x5 : ℕ),         x4 ≤ x5 →           x5 < (10 : ℕ) ^ (6 : ℕ) →             have x8 : Finset ℕ := Finset.Icc (x5 / (4 : ℕ) + (1 : ℕ)) (x5 / (2 : ℕ));             x3 * ↑x8.card * (2 : ℝ) ^ x5 ≤ ∑ x9 ∈ x8, x2 ((2 : ℕ) ^ x5 - (2 : ℕ) ^ x9) := by
  refine ⟨1, one_pos, (10 : ℕ) ^ (6 : ℕ), ?_⟩
  intro x5 h1 h2
  omega
