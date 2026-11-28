import Mathlib

/-!
# Cut of `L-goldbach-dyn-ultrashort-restricted-hit`

The frozen task asks: for all large `X`, every closed window `[y, y + ⌊y^(26/1075)⌋]`
contained in `[X, 2X]` contains an even integer `n = p + q` with `p, q` prime and
`⌊√X⌋ ≤ p ≤ 2⌊√X⌋`.

The task brief suggests proving directly that a total representation count under a
nonnegative short-window weight is positive, ruling out a wholly missed window at
this scale.  Two independent inputs are isolated.

* `h₁` (analytic, positivity of the window count): for all large `X` and every window
  `[y, y + ⌊y^(26/1075)⌋] ⊆ [X, 2X]`, some even `n` in the window has a positive
  number of primes `p` in the square-root band `[⌊√X⌋, 2⌊√X⌋]` with `n - p` prime.
* `h₂` (combinatorial extraction): a positive count of such band primes yields the
  witness pair `(p, q = n - p)`; primality of `n - p` rules out truncation.

The bridge only reads one member of a finite set.
-/

-- child 1 zh: 窗内表示计数为正（解析输入）：对充分大的 X，每个完整落在 [X,2X] 的闭窗 [y, y+⌊y^(26/1075)⌋] 内有偶数 n，使平方根带 [⌊√X⌋, 2⌊√X⌋] 内满足 n−p 为素数的素数 p 的个数为正。
-- child 1 en: Positive window representation count (analytic input): for all large X, every closed window [y, y+floor(y^(26/1075))] inside [X,2X] contains an even n for which the number of primes p in the square-root band [floor(sqrt X), 2 floor(sqrt X)] with n-p prime is positive.
-- child 2 zh: 组合提取：若这样的带内素数 p 的个数为正，则取出 p 与 q = n − p，核对带条件与 p + q = n。
-- child 2 en: Combinatorial extraction: a positive count of such band primes p yields the witness p and q = n - p with the band conditions and p + q = n.

theorem Conjectures.Cuts.Cut73d114e9051345942c6b0b8e
    (h₁ : ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y →
      y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)) ≤ 2 * X →
      ∃ n : ℕ, y ≤ n ∧ n ≤ y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)) ∧ Even n ∧
        0 < {p ∈ Finset.range (X + 1) | Nat.Prime p ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧
          Nat.Prime (n - p)}.card)
    (h₂ : ∀ (X n : ℕ), Even n →
      0 < {p ∈ Finset.range (X + 1) | Nat.Prime p ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧
          Nat.Prime (n - p)}.card →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n) :
    (let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)); ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W y ≤ 2 * X → ∃ n : ℕ, y ≤ n ∧ n ≤ y + W y ∧ Even n ∧ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n)) := by
  intro W
  obtain ⟨X₀, hX₀⟩ := h₁
  refine ⟨X₀, fun X hX y hy hy2 => ?_⟩
  obtain ⟨n, hn1, hn2, hn3, hn4⟩ := hX₀ X hX y hy hy2
  obtain ⟨p, q, hp, hq, hp1, hp2, hpq⟩ := h₂ X n hn3 hn4
  exact ⟨n, hn1, hn2, hn3, ⟨p, q, hp, hq, hp1, hp2, hpq⟩⟩
