import Mathlib

/-!
# Cut of `L-goldbach-seven-factor-product-shift`

The frozen task bounds, with an arbitrary logarithmic saving, the number of multiples of
six `n ∈ (X/2, X]` for which no prime pair `p + q = n` has `2*p*q + 1` with at most
seven prime factors.

The exceptional set splits into two causes.  Two independent inputs are isolated.

* `h₁` (almost-all Goldbach on multiples of six): multiples of six in `(X/2, X]` with no
  prime pair at all form a set of size `O(X / (log X)^A)` for every `A`.
* `h₂` (sieve input): multiples of six in `(X/2, X]` that are sums of two primes but
  none of whose prime pairs has `2*p*q + 1` with at most seven prime factors form a set
  of size `O(X / (log X)^A)` for every `A`.

Both inputs are phrased through the counting functions of the prime-pair sets, so the
statements are decidable.  The bridge is a union bound: the frozen exceptional set is
contained in the union of the two sets, and the logarithmic weight is nonnegative.
-/

-- child 1 zh: 六的倍数的几乎处处 Goldbach（解析输入）：对每个 A，(X/2, X] 中不是两素数之和的 6 的倍数集合的基数乘以 (log X)^A 不超过 X/2。
-- child 1 en: Almost-all Goldbach on multiples of six (analytic input): for every A, the multiples of six in (X/2, X] with no prime pair have count times (log X)^A at most X/2.
-- child 2 zh: 筛法输入（解析输入）：对每个 A，(X/2, X] 中是两素数之和但没有任何素数对使 2pq+1 至多七个素因子的 6 的倍数集合的基数乘以 (log X)^A 不超过 X/2。
-- child 2 en: Sieve input (analytic input): for every A, the multiples of six in (X/2, X] that have a prime pair but none with 2pq+1 having at most seven prime factors have count times (log X)^A at most X/2.

theorem Conjectures.Cuts.Cute236ab7431bb348ac536e00e
    (h₁ : ∀ A : ℕ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card = 0)).card : ℝ) *
      (Real.log (X : ℝ))^A ≤ (X : ℝ) / 2)
    (h₂ : ∀ A : ℕ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧
        0 < {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p) ∧
          (2 * p * (n - p) + 1).primeFactorsList.length ≤ 7}.card = 0)).card : ℝ) *
      (Real.log (X : ℝ))^A ≤ (X : ℝ) / 2) :
    (let bad := fun n : ℕ => 6 ∣ n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ (2*p*q+1).primeFactorsList.length ≤ 7; ∀ A : ℕ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc (X/2) X)).card : ℝ)*(Real.log (X : ℝ))^A) ≤ (X : ℝ)) := by
  intro bad A
  obtain ⟨X₁, hX₁⟩ := h₁ A
  obtain ⟨X₂, hX₂⟩ := h₂ A
  refine ⟨max X₁ X₂, fun X hX => ?_⟩
  have h1 := hX₁ X (le_trans (le_max_left X₁ X₂) hX)
  have h2 := hX₂ X (le_trans (le_max_right X₁ X₂) hX)
  have hsub : (@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc (X/2) X)) ⊆
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card = 0)) ∪
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧
        0 < {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p) ∧
          (2 * p * (n - p) + 1).primeFactorsList.length ≤ 7}.card = 0)) := by
    intro n hn
    obtain ⟨hnI, hn6, hnNo⟩ :=
      (@Finset.mem_filter ℕ bad (Classical.decPred bad) (Finset.Ioc (X/2) X) n).mp hn
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hc1 : {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card = 0
    · exact Or.inl ⟨hnI, hn6, hc1⟩
    · refine Or.inr ⟨hnI, hn6, Nat.pos_of_ne_zero hc1, ?_⟩
      by_contra hc7
      obtain ⟨p, hp⟩ := Finset.card_ne_zero.mp hc7
      obtain ⟨hp1, hp2, hp3, hp4⟩ := Finset.mem_filter.mp hp
      rw [Finset.mem_range] at hp1
      refine hnNo ⟨p, n - p, hp2, hp3, ?_, ?_⟩
      · have := Nat.Prime.ne_zero hp3
        omega
      · simpa [hp1] using hp4
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card = 0))
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧
        0 < {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p) ∧
          (2 * p * (n - p) + 1).primeFactorsList.length ≤ 7}.card = 0))
  have hsum : (@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc (X/2) X)).card ≤
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card = 0)).card +
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧
        0 < {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p) ∧
          (2 * p * (n - p) + 1).primeFactorsList.length ≤ 7}.card = 0)).card :=
    hcard.trans hunion
  have hlog : (0 : ℝ) ≤ Real.log (X : ℝ) := by
    rcases Nat.eq_zero_or_pos X with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hreal : ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc (X/2) X)).card : ℝ) ≤
      (((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card = 0)).card : ℝ) +
      (((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧
        0 < {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p) ∧
          (2 * p * (n - p) + 1).primeFactorsList.length ≤ 7}.card = 0)).card : ℝ) := by
    exact_mod_cast hsum
  have hmul := mul_le_mul_of_nonneg_left hreal (pow_nonneg hlog A)
  linarith
