import Mathlib

/-!
# Cut of `L-goldbach-binary-shift-cross-band-overlap`

The frozen task asks for a constant `c > 0` with `Σ_{X ≤ m < 2X} J(m) J'(m) ≥ c X`, where
`J(m)` counts the exponents `e ∈ [1, L/2]` with `m - 2^e` prime, `J'(m)` counts the exponents
`f ∈ [L/2 + 1, L]` with `m - 2^f` prime, and `L = ⌊log₂ X⌋ / 2`.  The brief names the route: expand
the product into prime pairs at the gaps `2^f - 2^e`; because the two exponent bands are
disjoint the diagonal representations `p = q` disappear, and an upper bound for a second moment
alone yields no positive lower bound.

Two independent inputs are isolated.

* `h₁` (analytic, prime pairs at binary gaps): the number of prime pairs `(p, q)` with
  `X ≤ p + 2^e < 2X` and `p + 2^e = q + 2^f`, summed over the low band `e ≤ L/2` and the high
  band `L/2 < f ≤ L` (that is, `e ≤ ⌊log₂ X⌋ / 4` and `⌊log₂ X⌋ / 4 < f ≤ ⌊log₂ X⌋ / 2`), is at
  least `c X`.  This is the open input; the diagonal is absent.
* `h₂` (combinatorial, double counting): for any two exponent bands the band product summed over
  `m ∈ [X, 2X)` equals that pair count.  It is a finite bijection `m ↦ (m - 2^e, m - 2^f)` per
  pair of exponents.

Combination: instantiate `h₂` at the two bands of the statement and read off `h₁`.
-/

-- child 1 zh: 二进间隙素数对（解析输入）：存在 c>0 与 X₀，对每个 X≥X₀，低带 e≤⌊log₂X⌋/4 与高带 ⌊log₂X⌋/4<f≤⌊log₂X⌋/2 中满足 X≤p+2^e<2X 且 p+2^e=q+2^f 的素数对 (p,q) 的总数至少为 cX。
-- child 1 en: Prime pairs at binary gaps (analytic input): there are c>0 and X0 such that for every X at least X0 the number of prime pairs (p,q) with X at most p+2^e below 2X and p+2^e = q+2^f, over the low band e at most floor(log2 X)/4 and the high band floor(log2 X)/4 below f at most floor(log2 X)/2, is at least c X.
-- child 2 zh: 双重计数恒等式（组合提取）：对任意两个指数带，Σ_{X≤m<2X} J₁(m)J₂(m) 等于满足 p+2^e=q+2^f 的素数对 (p,q) 在两带上的计数；这是每个指数对上 m↦(m−2^e, m−2^f) 的有限双射。
-- child 2 en: Double counting identity (combinatorial extraction): for any two exponent bands, the sum over X at most m below 2X of the product of the two band counts equals the count of prime pairs (p,q) with p+2^e = q+2^f over the two bands; this is the finite bijection m maps to (m-2^e, m-2^f) for each pair of exponents.

theorem Conjectures.Cuts.Cut3e9177af199258152300add5
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → c * (X:ℝ) ≤
      ((∑ e ∈ Finset.Icc 1 (Nat.log 2 X / 2 / 2), ∑ f ∈ Finset.Icc (Nat.log 2 X / 2 / 2 + 1) (Nat.log 2 X / 2),
        ∑ p ∈ Finset.range (2*X), ∑ q ∈ Finset.range (2*X),
          if Nat.Prime p ∧ Nat.Prime q ∧ X ≤ p + 2^e ∧ p + 2^e < 2*X ∧ p + 2^e = q + 2^f
          then (1:ℕ) else 0) : ℝ))
    (h₂ : ∀ (X a b c d : ℕ), ∑ m ∈ Finset.Ico X (2*X),
        (((Finset.Icc a b).filter (fun e => Nat.Prime (m - 2^e))).card : ℝ) *
        (((Finset.Icc c d).filter (fun e => Nat.Prime (m - 2^e))).card : ℝ) =
      ((∑ e ∈ Finset.Icc a b, ∑ f ∈ Finset.Icc c d, ∑ p ∈ Finset.range (2*X), ∑ q ∈ Finset.range (2*X),
        if Nat.Prime p ∧ Nat.Prime q ∧ X ≤ p + 2^e ∧ p + 2^e < 2*X ∧ p + 2^e = q + 2^f
        then (1:ℕ) else 0) : ℝ)) :
    (let J := fun (a b m : ℕ) => ((Finset.Icc a b).filter (fun e => Nat.Prime (m-2^e))).card; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2; c*(X:ℝ) ≤ ∑ m ∈ Finset.Ico X (2*X), (J 1 (L/2) m:ℝ)*(J (L/2+1) L m:ℝ)) := by
  intro J
  obtain ⟨c, hc, X₀, hX₀⟩ := h₁
  refine ⟨c, hc, X₀, fun X hX => ?_⟩
  intro L
  dsimp only [J]
  rw [h₂ X 1 (L/2) (L/2+1) L]
  dsimp only [L]
  exact hX₀ X hX
