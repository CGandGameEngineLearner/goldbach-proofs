import Mathlib

/-!
Premise 2/3 of a cut of L-goldbach-chen-cubic-residue-summands.

Splitting an interval `[x1, x2]` by residues modulo `42`: every `n` in the interval
is `42 * (n / 42) + n % 42`, the quotient `n / 42` is at most `x2 / 42`, and the
residue `n % 42` is below `42`.  Hence the set of `n ∈ [x1, x2]` with `n % 42 ∈ x3`
and `x4 n = true` is the disjoint union over `r ∈ x3` of the images `42 * q + r` of
the quotient sets, and the cardinality identity follows.  Self-contained: Mathlib only.
-/

namespace Conjectures.Cuts.Task4f94483b395cb9bff7594f6e_aux

/-- The quotients `q` whose lift `42 * q + r` lies in `[x1, x2]` and is selected by `x4`. -/
def inner (x1 x2 : ℕ) (x4 : ℕ → Bool) (r : ℕ) : Finset ℕ :=
  {x7 ∈ Finset.range (x2 / (42 : ℕ) + (1 : ℕ)) |
    x1 ≤ (42 : ℕ) * x7 + r ∧ (42 : ℕ) * x7 + r ≤ x2 ∧ x4 ((42 : ℕ) * x7 + r) = Bool.true}

/-- The selected elements of `[x1, x2]` whose residue modulo `42` lies in `x3`. -/
def outer (x1 x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ → Bool) : Finset ℕ :=
  {x6 ∈ Finset.Icc x1 x2 | x6 % (42 : ℕ) ∈ x3 ∧ x4 x6 = Bool.true}

private lemma mod_add_mul (q r : ℕ) (hr : r < 42) : ((42 : ℕ) * q + r) % (42 : ℕ) = r := by
  have h : (42 : ℕ) * q + r = r + (42 : ℕ) * q := Nat.add_comm _ _
  rw [h, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

private lemma outer_eq_biUnion (x1 x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ → Bool)
    (hx3 : x3 ⊆ Finset.range (42 : ℕ)) :
    outer x1 x2 x3 x4 =
      x3.biUnion (fun r => (inner x1 x2 x4 r).image (fun q => (42 : ℕ) * q + r)) := by
  ext n
  simp only [outer, inner, Finset.mem_filter, Finset.mem_Icc, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨hx1n, hnx2⟩, hmod, hx4⟩
    have hn : (42 : ℕ) * (n / 42) + n % 42 = n := Nat.div_add_mod n 42
    refine ⟨n % 42, hmod, n / 42, ⟨?_, ?_, ?_, ?_⟩, hn⟩
    · have hq : n / 42 ≤ x2 / 42 := Nat.div_le_div_right hnx2
      omega
    · rw [hn]; exact hx1n
    · rw [hn]; exact hnx2
    · rw [hn]; exact hx4
  · rintro ⟨r, hr, q, ⟨hq, hx1, hx2, hx4⟩, rfl⟩
    refine ⟨⟨hx1, hx2⟩, ?_, hx4⟩
    have hr42 : r < 42 := Finset.mem_range.mp (hx3 hr)
    rw [mod_add_mul q r hr42]
    exact hr

private lemma pairwiseDisjoint (x1 x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ → Bool)
    (hx3 : x3 ⊆ Finset.range (42 : ℕ)) :
    ∀ r ∈ x3, ∀ r' ∈ x3, r ≠ r' →
      Disjoint ((inner x1 x2 x4 r).image (fun q => (42 : ℕ) * q + r))
        ((inner x1 x2 x4 r').image (fun q => (42 : ℕ) * q + r')) := by
  intro r hr r' hr' hne
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [Finset.mem_image] at hn hn'
  obtain ⟨q, _, rfl⟩ := hn
  obtain ⟨q', _, hq'⟩ := hn'
  have hr42 : r < 42 := Finset.mem_range.mp (hx3 hr)
  have hr'42 : r' < 42 := Finset.mem_range.mp (hx3 hr')
  apply hne
  rw [← mod_add_mul q r hr42, ← mod_add_mul q' r' hr'42, hq']

private lemma card_main (x1 x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ → Bool)
    (hx3 : x3 ⊆ Finset.range (42 : ℕ)) :
    (outer x1 x2 x3 x4).card = ∑ r ∈ x3, (inner x1 x2 x4 r).card := by
  rw [outer_eq_biUnion x1 x2 x3 x4 hx3,
    Finset.card_biUnion (pairwiseDisjoint x1 x2 x3 x4 hx3)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.card_image_of_injective]
  intro a b hab
  have hab' : (42 : ℕ) * a + r = (42 : ℕ) * b + r := hab
  omega

end Conjectures.Cuts.Task4f94483b395cb9bff7594f6e_aux

theorem Conjectures.Cuts.Task4f94483b395cb9bff7594f6e :
    ∀ (x1 x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ → Bool), x3 ⊆ Finset.range (42 : ℕ) → {x6 ∈ Finset.Icc x1 x2 | x6 % (42 : ℕ) ∈ x3 ∧ x4 x6 = Bool.true}.card = ∑ x6 ∈ x3, {x7 ∈ Finset.range (x2 / (42 : ℕ) + (1 : ℕ)) | x1 ≤ (42 : ℕ) * x7 + x6 ∧ (42 : ℕ) * x7 + x6 ≤ x2 ∧ x4 ((42 : ℕ) * x7 + x6) = Bool.true}.card := by
  intro x1 x2 x3 x4 hx3
  exact Conjectures.Cuts.Task4f94483b395cb9bff7594f6e_aux.card_main x1 x2 x3 x4 hx3
