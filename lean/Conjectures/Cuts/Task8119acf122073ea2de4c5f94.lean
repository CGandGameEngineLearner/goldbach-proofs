import Mathlib

/-!
# `Conjectures.Cuts.Task8119acf122073ea2de4c5f94`

Elementary counting on a finite set: if a decidable predicate `x2` holds on a
subset of `x1` of cardinality at least `x4 * |x1|`, then its complement inside
`x1` has cardinality at most `(1 - x4) * |x1|`.

The proof is the partition identity
`(x1.filter x2).card + (x1.filter (¬x2)).card = x1.card`
(`Finset.card_filter_add_card_filter_not`), cast to `ℝ`, combined with the
hypothesis by linear arithmetic.  No analytic input is needed.
-/

theorem Conjectures.Cuts.Task8119acf122073ea2de4c5f94 :
    ∀ (x1 : Finset ℕ) (x2 : ℕ → Prop) [x3 : DecidablePred x2] (x4 : ℝ),
      (0 : ℝ) < x4 → x4 * ↑x1.card ≤ ↑(Finset.filter x2 x1).card →
      ↑{x7 ∈ x1 | ¬x2 x7}.card ≤ ((1 : ℝ) - x4) * ↑x1.card := by
  intro x1 x2 _ x4 _ h
  have hsplit : (Finset.filter x2 x1).card + ({x7 ∈ x1 | ¬x2 x7} : Finset ℕ).card = x1.card :=
    Finset.card_filter_add_card_filter_not (s := x1) (p := x2)
  have hsplitR : ((Finset.filter x2 x1).card : ℝ) + (({x7 ∈ x1 | ¬x2 x7} : Finset ℕ).card : ℝ) =
      (x1.card : ℝ) := by
    exact_mod_cast hsplit
  have hrw : ((1 : ℝ) - x4) * (x1.card : ℝ) = (x1.card : ℝ) - x4 * (x1.card : ℝ) := by ring
  linarith
