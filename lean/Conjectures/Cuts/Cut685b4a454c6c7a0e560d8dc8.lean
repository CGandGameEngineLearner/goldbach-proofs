import Mathlib

/-!
# Cut of `L-goldbach-cut-04af190025ef49e8eed1805a`

The frozen task asks, for every real `ε > 1` and every sufficiently large even `n`, for primes
`p, q` and six positive binary exponents with `n = p + q + Σ_j 2^(e_j+1)`, the total shift
`Σ_j 2^(e_j+1)` being at most `n^ε`.

Two independent inputs are isolated.

* `h1` (analytic): for every `ε > 1` the number of admissible pairs `(p, e)` is positive for all
  large even `n`; here `p` is prime, every exponent is at most `n`, the complement
  `n - (p + Σ_j 2^(e_j+1))` is prime, and the shift sum is at most `n^ε`. This positivity of the
  weighted representation count is the circle-method input and the true obstruction.
* `h2` (combinatorial): a positive admissible count yields an actual witness with its exponent
  tuple. It only reads one member of a finite set and rewrites a natural-number equation.

The bridge below converts positivity into the witness.
-/

-- child 1 zh: 解析输入：对每个 ε>1，所有充分大偶数 n 的可容许 (p, e) 对数（p 素、补项 n−(p+Σ2^(e_j+1)) 为素数、偏移和 ≤ n^ε）为正。
-- child 1 en: Analytic input: for every ε>1 the number of admissible pairs (p, e) with p prime, complement n-(p+Σ2^(e_j+1)) prime and shift sum at most n^ε is positive for all large even n.
-- child 2 zh: 组合提取：可容许对数为正时取出见证 (p,q,e) 并核对 n = p+q+Σ2^(e_j+1) 及偏移和界。
-- child 2 en: Combinatorial extraction: a positive admissible count yields a witness (p,q,e) with n = p+q+Σ2^(e_j+1) and the shift-sum bound.

theorem Conjectures.Cuts.Cut685b4a454c6c7a0e560d8dc8
    (h1 : ∀ (x1 : ℝ), (1 : ℝ) < x1 → ∃ (x3 : ℕ), ∀ (x4 : ℕ), x3 ≤ x4 → Even x4 → (0 : ℕ) < {x7 ∈ (Finset.range (x4 + (1 : ℕ))).product (Fintype.piFinset fun (x7 : Fin (6 : ℕ)) => Finset.range (x4 + (1 : ℕ))) | Nat.Prime x7.1 ∧ Nat.Prime (x4 - (x7.1 + ∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7.2 x8 + (1 : ℕ)))) ∧ (↑(∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7.2 x8 + (1 : ℕ))) : ℝ) ≤ (↑x4 : ℝ) ^ x1}.card)
    (h2 : ∀ (x1 : ℝ) (x4 : ℕ), Even x4 → (0 : ℕ) < {x7 ∈ (Finset.range (x4 + (1 : ℕ))).product (Fintype.piFinset fun (x7 : Fin (6 : ℕ)) => Finset.range (x4 + (1 : ℕ))) | Nat.Prime x7.1 ∧ Nat.Prime (x4 - (x7.1 + ∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7.2 x8 + (1 : ℕ)))) ∧ (↑(∑ x8 : Fin (6 : ℕ), (2 : ℕ) ^ (x7.2 x8 + (1 : ℕ))) : ℝ) ≤ (↑x4 : ℝ) ^ x1}.card →
      ∃ (x7 : ℕ) (x8 : ℕ), Nat.Prime x7 ∧ Nat.Prime x8 ∧ ∃ (x9 : Fin (6 : ℕ) → ℕ), x4 = x7 + x8 + ∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ)) ∧ (↑(∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ))) : ℝ) ≤ (↑x4 : ℝ) ^ x1) :
    (∀ (x1 : ℝ), (1 : ℝ) < x1 → ∃ (x3 : ℕ), ∀ (x4 : ℕ), x3 ≤ x4 → Even x4 → ∃ (x7 : ℕ) (x8 : ℕ), Nat.Prime x7 ∧ Nat.Prime x8 ∧ ∃ (x9 : Fin (6 : ℕ) → ℕ), x4 = x7 + x8 + ∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ)) ∧ (↑(∑ x10 : Fin (6 : ℕ), (2 : ℕ) ^ (x9 x10 + (1 : ℕ))) : ℝ) ≤ (↑x4 : ℝ) ^ x1) := by
  intro x1 hx1
  obtain ⟨x3, hN⟩ := h1 x1 hx1
  exact ⟨x3, fun x4 hle hEven => h2 x1 x4 hEven (hN x4 hle hEven)⟩