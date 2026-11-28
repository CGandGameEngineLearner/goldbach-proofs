import Mathlib

/-!
# Cut of `L-goldbach-seven-factor-product-shift`

The frozen task bounds, with an arbitrary logarithmic saving, the number of multiples of
six `n ∈ (X/2, X]` for which no prime pair `p + q = n` has `2*p*q + 1` with at most
seven prime factors.

The exceptional set splits into two disjoint causes.  Two independent inputs are isolated.

* `h₁` (almost-all Goldbach on multiples of six): multiples of six in `(X/2, X]` that are
  not a sum of two primes at all form a set of size `O(X / (log X)^A)` for every `A`.
* `h₂` (sieve input): multiples of six in `(X/2, X]` that are sums of two primes but
  none of whose representations has `2*p*q + 1` with at most seven prime factors form a
  set of size `O(X / (log X)^A)` for every `A`.

The bridge is a union bound: the frozen exceptional set is contained in the union of the
two sets, and the logarithmic weight is nonnegative.
-/

-- child 1 zh: 六的倍数的几乎处处 Goldbach（解析输入）：对每个 A，(X/2, X] 中不是两素数之和的 6 的倍数集合的基数乘以 (log X)^A 不超过 X/2。
-- child 1 en: Almost-all Goldbach on multiples of six (analytic input): for every A, the multiples of six in (X/2, X] that are not a sum of two primes have count times (log X)^A at most X/2.
-- child 2 zh: 筛法输入（解析输入）：对每个 A，(X/2, X] 中是两素数之和但没有任何表示使 2pq+1 至多七个素因子的 6 的倍数集合的基数乘以 (log X)^A 不超过 X/2。
-- child 2 en: Sieve input (analytic input): for every A, the multiples of six in (X/2, X] that are a sum of two primes but have no representation with 2pq+1 having at most seven prime factors have count times (log X)^A at most X/2.

open Classical in
theorem Conjectures.Cuts.Cute236ab7431bb348ac536e00e
    (h₁ : ∀ A : ℕ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
          p+q = n)).card : ℝ) * (Real.log (X : ℝ))^A ≤ (X : ℝ) / 2)
    (h₂ : ∀ A : ℕ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
          p+q = n) ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q = n ∧
          (2*p*q+1).primeFactorsList.length ≤ 7)).card : ℝ) * (Real.log (X : ℝ))^A ≤ (X : ℝ) / 2) :
    (let bad := fun n : ℕ => 6 ∣ n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q=n ∧ (2*p*q+1).primeFactorsList.length ≤ 7; ∀ A : ℕ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → (((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc (X/2) X)).card : ℝ)*(Real.log (X : ℝ))^A) ≤ (X : ℝ)) := by
  intro bad A
  obtain ⟨X₁, hX₁⟩ := h₁ A
  obtain ⟨X₂, hX₂⟩ := h₂ A
  refine ⟨max X₁ X₂, fun X hX => ?_⟩
  have h1 := hX₁ X (le_trans (le_max_left X₁ X₂) hX)
  have h2 := hX₂ X (le_trans (le_max_right X₁ X₂) hX)
  have hsub : (@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc (X/2) X)) ⊆
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
          p+q = n)) ∪ ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧ (∃ p q : ℕ, Nat.Prime p ∧
          Nat.Prime q ∧ p+q = n) ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q = n ∧
          (2*p*q+1).primeFactorsList.length ≤ 7)) := by
    intro n hn
    obtain ⟨hnI, hn6, hnNo⟩ :=
      (@Finset.mem_filter ℕ bad (Classical.decPred bad) (Finset.Ioc (X/2) X) n).mp hn
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases hg : ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n
    · exact Or.inr ⟨hnI, hn6, hg, hnNo⟩
    · exact Or.inl ⟨hnI, hn6, hg⟩
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
          p+q = n))
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
          p+q = n) ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q = n ∧
          (2*p*q+1).primeFactorsList.length ≤ 7))
  have hsum : (@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc (X/2) X)).card ≤
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
          p+q = n)).card +
      ((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
          p+q = n) ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q = n ∧
          (2*p*q+1).primeFactorsList.length ≤ 7)).card := hcard.trans hunion
  have hlog : (0 : ℝ) ≤ Real.log (X : ℝ) := by
    rcases Nat.eq_zero_or_pos X with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  have hreal : ((@Finset.filter ℕ bad (Classical.decPred bad) (Finset.Ioc (X/2) X)).card : ℝ) ≤
      (((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
          p+q = n)).card : ℝ) +
      (((Finset.Ioc (X/2) X).filter (fun n => 6 ∣ n ∧ (∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧
          p+q = n) ∧ ¬ ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p+q = n ∧
          (2*p*q+1).primeFactorsList.length ≤ 7)).card : ℝ) := by exact_mod_cast hsum
  have hmul := mul_le_mul_of_nonneg_left hreal (pow_nonneg hlog A)
  linarith
