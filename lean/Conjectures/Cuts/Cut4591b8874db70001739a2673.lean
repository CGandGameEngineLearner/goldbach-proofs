import Mathlib

open Finset Filter

local notation "Moduli" =>
  (fun X : ℕ => Icc 1 ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊)

local notation "InProgression" =>
  (fun (X q a : ℕ) => Finset.filter (fun k => k % q = a % q) (Icc 1 X))

local notation "PrimeSum" =>
  (fun X q a : ℕ =>
    ∑ k ∈ InProgression X q a, ite (Nat.Prime k) (Real.log (k : ℝ)) 0)

local notation "SquareSum" =>
  (fun X q a : ℕ =>
    ∑ k ∈ InProgression X q a,
      ite (Nat.Prime (Nat.sqrt k) ∧ (Nat.sqrt k) ^ 2 = k) (Real.log (Nat.sqrt k : ℝ)) 0)

local notation "MangoldtSum" =>
  (fun X q a : ℕ => ∑ k ∈ InProgression X q a, ArithmeticFunction.vonMangoldt k)

private theorem powerBudget (A C β : ℝ) (hC : 0 < C) (hβ : β < 1) :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      C * (X : ℝ) ^ β ≤ (X : ℝ) / (Real.log (X : ℝ)) ^ A := by
  have h := (isLittleO_log_rpow_rpow_atTop (s := 1 - β) A (sub_pos.mpr hβ)).bound
    (show 0 < 1 / C by positivity)
  obtain ⟨R, hR⟩ := eventually_atTop.mp h
  refine ⟨⌈max 2 R⌉₊, fun X hX => ?_⟩
  have hx : max 2 R ≤ (X : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hX)
  have hx1 : (1 : ℝ) < (X : ℝ) := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hx)
  have hx0 : 0 < (X : ℝ) := by linarith
  have hlog : 0 < (Real.log (X : ℝ)) ^ A := Real.rpow_pos_of_pos (Real.log_pos hx1) _
  have hpower : 0 ≤ (X : ℝ) ^ (1 - β) := Real.rpow_nonneg hx0.le _
  have hsmall := hR (X : ℝ) ((le_max_right _ _).trans hx)
  simp only [Real.norm_eq_abs, abs_of_pos hlog, abs_of_nonneg hpower] at hsmall
  apply (le_div_iff₀ hlog).mpr
  calc
    (C * (X : ℝ) ^ β) * (Real.log (X : ℝ)) ^ A =
        (C * (Real.log (X : ℝ)) ^ A) * (X : ℝ) ^ β := by ring
    _ ≤ (C * (1 / C * (X : ℝ) ^ (1 - β))) * (X : ℝ) ^ β :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hC.le)
        (Real.rpow_nonneg hx0.le _)
    _ = (X : ℝ) ^ (1 - β) * (X : ℝ) ^ β := by
      rw [← mul_assoc C, mul_one_div_cancel hC.ne', one_mul]
    _ = (X : ℝ) := by rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one]

/-!
Separate the prime-only progression errors from the two types of proper prime
powers. Squares can be counted by reduced square roots modulo each modulus;
the higher powers are sparse even before imposing a congruence.
-/

-- child 1 zh: 在模数 q ≤ X^(3/5) 上，只对素数对数权证明任意对数幂节省的最坏互素余类误差和。
-- child 1 en: Bound the sum of maximal reduced-class errors for the prime-only Chebyshev sum at level 3/5, with arbitrary logarithmic saving.
-- child 2 zh: 在同一模数范围，证明素数平方的对数权在最坏互素余类上的质量之和为 O(X^(2/3))。
-- child 2 en: Bound the sum of maximal reduced-class prime-square masses by O(X^(2/3)) in the same modulus range.
-- child 3 zh: 扣除素数和素数平方后，证明更高素数幂在最坏互素余类上的质量之和为 O(X^(29/30))。
-- child 3 en: Bound the sum of maximal reduced-class masses of prime powers of exponent at least three by O(X^(29/30)).

theorem Conjectures.Cuts.Cut4591b8874db70001739a2673
    (hPrime : ∀ A : ℝ, 0 < A → ∃ (C : ℝ) (N : ℕ), 0 < C ∧
      ∀ X : ℕ, N ≤ X → ∃ T : ℕ → ℝ,
        (∀ q ∈ Moduli X, ∀ a : ℕ, Nat.Coprime a q →
          |PrimeSum X q a - (X : ℝ) / (q.totient : ℝ)| ≤ T q) ∧
        (∑ q ∈ Moduli X, T q) ≤ C * (X : ℝ) / (Real.log (X : ℝ)) ^ A)
    (hSquare : ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ∃ S : ℕ → ℝ,
      (∀ q ∈ Moduli X, ∀ a : ℕ, Nat.Coprime a q → |SquareSum X q a| ≤ S q) ∧
      (∑ q ∈ Moduli X, S q) ≤ C * (X : ℝ) ^ (2 / 3 : ℝ))
    (hHigher : ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ X : ℕ, N ≤ X → ∃ U : ℕ → ℝ,
      (∀ q ∈ Moduli X, ∀ a : ℕ, Nat.Coprime a q →
        |MangoldtSum X q a - PrimeSum X q a - SquareSum X q a| ≤ U q) ∧
      (∑ q ∈ Moduli X, U q) ≤ C * (X : ℝ) ^ (29 / 30 : ℝ)) :
    (∀ A : ℝ, 0 < A → ∃ (C : ℝ) (X₀ : ℕ), 0 < C ∧ ∀ X : ℕ, X₀ ≤ X → ∃ B : ℕ → ℝ, (∀ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, ∀ a : ℕ, Nat.Coprime a q → |(∑ k ∈ (Finset.Icc 1 X).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (X : ℝ) / (Nat.totient q : ℝ)| ≤ B q) ∧ (∑ q ∈ Finset.Icc 1 ⌊(X : ℝ) ^ (3 / 5 : ℝ)⌋₊, B q) ≤ C * (X : ℝ) / (Real.log (X : ℝ)) ^ A) := by
  intro A hA
  obtain ⟨C₁, N₁, hC₁, hT⟩ := hPrime A hA
  obtain ⟨C₂, N₂, hC₂, hS⟩ := hSquare
  obtain ⟨C₃, N₃, hC₃, hU⟩ := hHigher
  obtain ⟨K₂, hK₂⟩ := powerBudget A C₂ (2 / 3) hC₂ (by norm_num)
  obtain ⟨K₃, hK₃⟩ := powerBudget A C₃ (29 / 30) hC₃ (by norm_num)
  refine ⟨C₁ + 2, max N₁ (max N₂ (max N₃ (max K₂ K₃))), by linarith, ?_⟩
  intro X hX
  simp only [max_le_iff] at hX
  obtain ⟨T, hTq, hTsum⟩ := hT X hX.1
  obtain ⟨S, hSq, hSsum⟩ := hS X hX.2.1
  obtain ⟨U, hUq, hUsum⟩ := hU X hX.2.2.1
  refine ⟨fun q => T q + S q + U q, ?_, ?_⟩
  · intro q hq a ha
    let m : ℝ := (X : ℝ) / (q.totient : ℝ)
    change |MangoldtSum X q a - m| ≤ T q + S q + U q
    let t := PrimeSum X q a - m
    let s := SquareSum X q a
    let u := MangoldtSum X q a - PrimeSum X q a - s
    have heq : MangoldtSum X q a - m = t + s + u := by
      dsimp [t, u]
      ring
    rw [heq]
    calc
      |t + s + u| ≤ |t + s| + |u| := abs_add_le _ _
      _ ≤ |t| + |s| + |u| := add_le_add (abs_add_le t s) le_rfl
      _ ≤ T q + S q + U q := add_le_add
        (add_le_add (hTq q hq a ha) (hSq q hq a ha)) (hUq q hq a ha)
  · change (∑ q ∈ Moduli X, (T q + S q + U q)) ≤
      (C₁ + 2) * (X : ℝ) / (Real.log (X : ℝ)) ^ A
    let b : ℝ := (X : ℝ) / (Real.log (X : ℝ)) ^ A
    have hs : (∑ q ∈ Moduli X, S q) ≤ b := hSsum.trans (hK₂ X hX.2.2.2.1)
    have hu : (∑ q ∈ Moduli X, U q) ≤ b := hUsum.trans (hK₃ X hX.2.2.2.2)
    calc
      (∑ q ∈ Moduli X, (T q + S q + U q)) ≤
          C₁ * (X : ℝ) / (Real.log (X : ℝ)) ^ A + b + b := by
        rw [sum_add_distrib, sum_add_distrib]
        exact add_le_add (add_le_add hTsum hs) hu
      _ = _ := by dsimp [b]; ring
