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
  `[y, y + ⌊y^(26/1075)⌋] ⊆ [X, 2X]`, some prime `p` in the square-root band
  `[⌊√X⌋, 2⌊√X⌋]` has a prime `q` with `p + q` even and lying in the window.
* `h₂` (combinatorial extraction): such a pair gives the witness `n = p + q` with all
  window, parity and band conditions read off from the finite sets.

The bridge only reads one member of a finite set and one member of a second finite set.
-/

-- child 1 zh: 窗内配对计数为正（解析输入）：对充分大的 X，每个完整落在 [X,2X] 的闭窗 [y, y+⌊y^(26/1075)⌋]，存在平方根带 [⌊√X⌋, 2⌊√X⌋] 内的素数 p 与素数 q，使 p+q 为偶数且落在该窗内。
-- child 1 en: Positive window pair count (analytic input): for all large X, every closed window [y, y+floor(y^(26/1075))] inside [X,2X] admits a prime p in the square-root band [floor(sqrt X), 2 floor(sqrt X)] and a prime q with p+q even and inside the window.
-- child 2 zh: 组合提取：若窗内存在这样的配对，则取出 n = p+q 并核对窗、奇偶与平方根带条件。
-- child 2 en: Combinatorial extraction: if such a pair exists for the window, one reads off n = p+q and checks the window, parity and square-root-band conditions.

theorem Conjectures.Cuts.Cuted43b0ad064522585ef1ff6e
    (h₁ : ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)) ≤ 2 * X →
      0 < {p ∈ Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X) | Nat.Prime p ∧
        0 < {q ∈ Finset.range (y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)) + 1) |
          Nat.Prime q ∧ Even (p + q) ∧ y ≤ p + q ∧
            p + q ≤ y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075))}.card}.card)
    (h₂ : ∀ (X y : ℕ), X ≤ y → y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)) ≤ 2 * X →
      0 < {p ∈ Finset.Icc (Nat.sqrt X) (2 * Nat.sqrt X) | Nat.Prime p ∧
        0 < {q ∈ Finset.range (y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)) + 1) |
          Nat.Prime q ∧ Even (p + q) ∧ y ≤ p + q ∧
            p + q ≤ y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075))}.card}.card →
      ∃ n : ℕ, y ≤ n ∧ n ≤ y + Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)) ∧ Even n ∧
        (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n)) :
    (let W := fun y : ℕ => Nat.floor ((y : ℝ) ^ ((26 : ℝ) / 1075)); ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W y ≤ 2 * X → ∃ n : ℕ, y ≤ n ∧ n ≤ y + W y ∧ Even n ∧ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.sqrt X ≤ p ∧ p ≤ 2 * Nat.sqrt X ∧ p + q = n)) := by
  intro W
  obtain ⟨X₀, hX₀⟩ := h₁
  refine ⟨X₀, fun X hX y hy hy2 => h₂ X y hy hy2 (hX₀ X hX y hy hy2)⟩
