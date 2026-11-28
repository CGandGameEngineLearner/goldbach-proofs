import Mathlib

/-!
# Cut of `L-goldbach-binary-shift-central-hit`

The frozen task asks, for every sufficiently large even `n`, for a nonzero shift `2^e`
with `2 ^ (2e) ≤ n` such that `n - 2^e` is a sum of two primes `p + q` lying in the
central window `q ≤ 2 * p` and `p ≤ 2 * q`.

The task brief names the obstruction: one must bound the number of missed central
windows among the `O(log n)` nonzero shifts at a single `n`, since a global exceptional
count does not control this sparse sample.  Two independent inputs are isolated.

* `h₁` (analytic, the brief's missed-window cap): for every sufficiently large even `n`,
  the number of admissible shifts `e` for which `n - 2^e` has no central prime pair is
  strictly smaller than the total number of admissible shifts.
* `h₂` (combinatorial extraction): if some admissible shift hits a central prime pair,
  one reads off the witness `(e, p, q)` and checks the natural-number equation.

The bridge is a counting argument: the admissible shift set splits disjointly into the
missed and the hitting shifts, so a missed part smaller than the whole set leaves a
hitting shift.
-/

-- child 1 zh: 未命中窗计数（解析输入）：对每个充分大的偶数 n，在满足 2^(2e) ≤ n 的非零移位 e 中，使 n − 2^e 不是中心窗内两素数之和的 e 的个数严格小于移位总数。
-- child 1 en: Missed-window cap (analytic input): for every sufficiently large even n, among the nonzero shifts e with 2^(2e) ≤ n, the number of shifts for which n - 2^e is not a sum of two primes in the central window is strictly less than the total number of such shifts.
-- child 2 zh: 组合提取：若某个可容许移位 e 使 n − 2^e 的中心素数对计数为正，则取出见证 (e, p, q) 并核对 n = p + q + 2^e 与中心窗不等式。
-- child 2 en: Combinatorial extraction: if some admissible shift e gives a positive count of central prime pairs for n - 2^e, then a witness (e, p, q) exists with n = p + q + 2^e and the central-window inequalities.

theorem Conjectures.Cuts.Cut90d4e640c6b4a94455c4ce1f
    (h₁ : ∃ N : ℕ, ∀ n ≥ N, Even n →
      ({e ∈ Finset.Icc 1 n | 1 ≤ e ∧ (2^e)^2 ≤ n ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - 2^e - p) ∧
          p + (n - 2^e - p) ≤ 3*p ∧ 3*p ≤ 2*(p + (n - 2^e - p))}.card = 0}).card <
      ({e ∈ Finset.Icc 1 n | 1 ≤ e ∧ (2^e)^2 ≤ n}).card)
    (h₂ : ∀ n : ℕ,
      0 < {e ∈ Finset.Icc 1 n | 1 ≤ e ∧ (2^e)^2 ≤ n ∧
        0 < {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - 2^e - p) ∧
          p + (n - 2^e - p) ≤ 3*p ∧ 3*p ≤ 2*(p + (n - 2^e - p))}.card}.card →
      ∃ e p q : ℕ, 1 ≤ e ∧ (2^e)^2 ≤ n ∧ Nat.Prime p ∧ Nat.Prime q ∧ n = p+q+2^e ∧
        p+q ≤ 3*p ∧ 3*p ≤ 2*(p+q)) :
    (∃ N : ℕ, ∀ n ≥ N, Even n → ∃ e p q : ℕ, 1 ≤ e ∧ (2^e)^2 ≤ n ∧ Nat.Prime p ∧
      Nat.Prime q ∧ n = p+q+2^e ∧ p+q ≤ 3*p ∧ 3*p ≤ 2*(p+q)) := by
  obtain ⟨N, hN⟩ := h₁
  refine ⟨N, fun n hn he => h₂ n ?_⟩
  have h := hN n hn he
  set S : Finset ℕ := {e ∈ Finset.Icc 1 n | 1 ≤ e ∧ (2^e)^2 ≤ n} with hS
  set c : ℕ → ℕ := fun e =>
    {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - 2^e - p) ∧
      p + (n - 2^e - p) ≤ 3*p ∧ 3*p ≤ 2*(p + (n - 2^e - p))}.card with hc
  have hsplit : S.card =
      (S.filter (fun e => c e = 0)).card + (S.filter (fun e => 0 < c e)).card := by
    have hc2 := Finset.card_filter_add_card_filter_not (s := S) (p := fun e => c e = 0)
    have hnot : S.filter (fun e => ¬ (c e = 0)) = S.filter (fun e => 0 < c e) := by
      ext e
      simp only [Finset.mem_filter, Nat.pos_iff_ne_zero]
    rw [hnot] at hc2
    exact hc2.symm
  have hmem : {e ∈ Finset.Icc 1 n | 1 ≤ e ∧ (2^e)^2 ≤ n ∧
      {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - 2^e - p) ∧
        p + (n - 2^e - p) ≤ 3*p ∧ 3*p ≤ 2*(p + (n - 2^e - p))}.card = 0} =
      S.filter (fun e => c e = 0) := by
    ext e
    simp [hS, hc, and_assoc]
  rw [hmem] at h
  have hgoal : 0 < (S.filter (fun e => 0 < c e)).card := by
    by_contra h0
    have hzero : (S.filter (fun e => 0 < c e)).card = 0 :=
      Nat.eq_zero_of_le_zero (Nat.not_lt.mp h0)
    omega
  have hmem2 : {e ∈ Finset.Icc 1 n | 1 ≤ e ∧ (2^e)^2 ≤ n ∧
      0 < {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - 2^e - p) ∧
        p + (n - 2^e - p) ≤ 3*p ∧ 3*p ≤ 2*(p + (n - 2^e - p))}.card} =
      S.filter (fun e => 0 < c e) := by
    ext e
    simp [hS, hc, and_assoc]
  rw [hmem2]
  exact hgoal
