import Mathlib

/-!
Premise 3/4 of a cut of L-goldbach-window-moving-prime-center.

The coefficient of `t ^ (2 * x1)` in the product of the two prime-indicator polynomials of the
windows `[x1 - x2, x1]` and `[x1, x1 + x2]` counts the pairs `(p, q)` of primes with
`p ∈ [x1 - x2, x1]`, `q ∈ [x1, x1 + x2]` and `p + q = 2 * x1`, and that set of pairs is in
bijection with the offsets `k ∈ [0, x2]` for which both `x1 - k` and `x1 + k` are prime, via
`k ↦ (x1 - k, x1 + k)` (using `x2 ≤ x1` to read the truncated subtractions back).

Step 1 (`coeff_prod`, Mathlib only): expanding `Finset.sum_mul_sum`, `monomial_mul_monomial` and
`coeff_monomial` turns the coefficient into the cardinality of
`((x4 ×ˢ x5).filter (fun pq => pq.1 + pq.2 = n))`.
Step 2: the explicit bijection above, by `Finset.card_bij`.

Self-contained: Mathlib only, one auxiliary lemma.
-/

namespace Conjectures.Cuts.Taskdc74960e65f0679d60ddc99b_aux

/-- The coefficient of a product of two sums of monomials is the number of pairs of exponents
summing to that index. -/
lemma coeff_prod (x4 x5 : Finset ℕ) (n : ℕ) :
    ((∑ p ∈ x4, (Polynomial.monomial p) (1 : ℕ)) * ∑ q ∈ x5, (Polynomial.monomial q) (1 : ℕ)).coeff n
      = ((x4 ×ˢ x5).filter (fun pq => pq.1 + pq.2 = n)).card := by
  rw [Finset.sum_mul_sum]
  have hsum : (∑ p ∈ x4, ∑ q ∈ x5, (Polynomial.monomial p) (1 : ℕ) * (Polynomial.monomial q) (1 : ℕ))
      = ∑ p ∈ x4, ∑ q ∈ x5, (Polynomial.monomial (p + q)) (1 : ℕ) := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [Polynomial.monomial_mul_monomial, mul_one]
  rw [hsum]
  simp_rw [Polynomial.finsetSum_coeff]
  have hmono : ∀ p q : ℕ,
      ((Polynomial.monomial (p + q)) (1 : ℕ)).coeff n = if p + q = n then (1 : ℕ) else 0 := by
    intro p q
    by_cases h : p + q = n
    · simp [h]
    · simp [h]
  simp_rw [hmono]
  rw [Finset.card_filter, Finset.sum_product]

end Conjectures.Cuts.Taskdc74960e65f0679d60ddc99b_aux

theorem Conjectures.Cuts.Taskdc74960e65f0679d60ddc99b :
    ∀ (x1 x2 : ℕ),   x2 ≤ x1 →     have x4 : Finset ℕ := Finset.filter Nat.Prime (Finset.Icc (x1 - x2) x1);     have x5 : Finset ℕ := Finset.filter Nat.Prime (Finset.Icc x1 (x1 + x2));     ((∑ x6 ∈ x4, (Polynomial.monomial x6) (1 : ℕ)) * ∑ x6 ∈ x5, (Polynomial.monomial x6) (1 : ℕ)).coeff ((2 : ℕ) * x1) = {x6 ∈ Finset.range (x2 + (1 : ℕ)) | Nat.Prime (x1 - x6) ∧ Nat.Prime (x1 + x6)}.card := by
  intro x1 x2 hx2x1
  dsimp only
  rw [Conjectures.Cuts.Taskdc74960e65f0679d60ddc99b_aux.coeff_prod]
  symm
  refine Finset.card_bij (fun (k : ℕ) _ => ((x1 - k, x1 + k) : ℕ × ℕ)) ?_ ?_ ?_
  · intro k hk
    obtain ⟨hkmem, hkP, hkQ⟩ := Finset.mem_filter.mp hk
    have hk2 : k ≤ x2 := by simpa using Finset.mem_range.mp hkmem
    have hk1 : k ≤ x1 := le_trans hk2 hx2x1
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hkP⟩
      · exact Nat.sub_le_sub_left hk2 x1
      · exact Nat.sub_le x1 k
    · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hkQ⟩
      · exact Nat.le_add_right x1 k
      · exact Nat.add_le_add_left hk2 x1
    · have : x1 - k + k = x1 := Nat.sub_add_cancel hk1
      omega
  · intro k₁ _ k₂ _ heq
    have h2 : x1 + k₁ = x1 + k₂ := congrArg Prod.snd heq
    omega
  · intro pq hpq
    obtain ⟨hprod, hsum⟩ := Finset.mem_filter.mp hpq
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hprod
    obtain ⟨hpI, hpP⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqI, hqP⟩ := Finset.mem_filter.mp hq
    obtain ⟨hplo, hphi⟩ := Finset.mem_Icc.mp hpI
    obtain ⟨hqlo, hqhi⟩ := Finset.mem_Icc.mp hqI
    refine ⟨x1 - pq.1, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_, ?_⟩
      · omega
      · have hsub : x1 - (x1 - pq.1) = pq.1 := by omega
        rw [hsub]
        exact hpP
      · have hadd : x1 + (x1 - pq.1) = pq.2 := by omega
        rw [hadd]
        exact hqP
    · ext
      · have hsub : x1 - (x1 - pq.1) = pq.1 := by omega
        rw [hsub]
      · have hadd : x1 + (x1 - pq.1) = pq.2 := by omega
        rw [hadd]
