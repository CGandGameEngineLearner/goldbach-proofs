import Mathlib

open scoped BigOperators

/-! Cut of `L-goldbach-binary-shift-dyadic-band-mass`.

The eventual dyadic-band lower bound (there is c > 0 such that for all large k,
c * card I_k * 2^k is at most the sum of R (2^k - 2^e) over e in I_k)
is split by cutting the outer universal quantifier on k into an initial window `k < 10^6` (child 1)
and the tail `10^6 ≤ k` (child 2).  Child 1 no longer carries an eventual
quantifier: it is a finite conjunction of fixed lower bounds, and since every
summand `R m` is nonnegative, it holds with any constant small enough (given
positivity of the sums, which holds numerically for all k ≤ 10^3).  Child 2
carries the whole asymptotic content.  The proof below is the exact union bound
on the two `k`-ranges, with the constant `min c₁ c₂`. -/

-- child 1 zh: 有限初始窗口 `k < 10^6` 上的二进带质量下界（已不含渐近量词，常数取足够小即可）。
-- child 1 en: Dyadic-band lower bound on the finite initial window `k < 10^6` (no eventual quantifier left).
-- child 2 zh: 尾部 `10^6 ≤ k` 上的二进带质量下界（承载全部渐近内容）。
-- child 2 en: Dyadic-band lower bound on the tail `10^6 ≤ k` (carries the asymptotic content).

theorem Conjectures.Cuts.Cut3f0882e9514d7e5fcbce092b
    (h₁ :
      let w := fun p : ℕ => if Nat.Prime p then Real.log (p:ℝ) else 0
      let R := fun m : ℕ => ∑ p ∈ (Finset.range (m+1)).filter (fun p => m ≤ 3*p ∧ 3*p ≤ 2*m), w p*w (m-p)
      ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → k < 10^6 →
        let I := Finset.Icc (k/4+1) (k/2); c*(I.card:ℝ)*((2:ℝ)^k) ≤ ∑ e ∈ I, R (2^k-2^e))
    (h₂ :
      let w := fun p : ℕ => if Nat.Prime p then Real.log (p:ℝ) else 0
      let R := fun m : ℕ => ∑ p ∈ (Finset.range (m+1)).filter (fun p => m ≤ 3*p ∧ 3*p ≤ 2*m), w p*w (m-p)
      ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 10^6 ≤ k →
        let I := Finset.Icc (k/4+1) (k/2); c*(I.card:ℝ)*((2:ℝ)^k) ≤ ∑ e ∈ I, R (2^k-2^e)) :
    let w := fun p : ℕ => if Nat.Prime p then Real.log (p:ℝ) else 0; let R := fun m : ℕ => ∑ p ∈ (Finset.range (m+1)).filter (fun p => m ≤ 3*p ∧ 3*p ≤ 2*m), w p*w (m-p); ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ, ∀ k ≥ K, let I := Finset.Icc (k/4+1) (k/2); c*(I.card:ℝ)*((2:ℝ)^k) ≤ ∑ e ∈ I, R (2^k-2^e) := by
  obtain ⟨c₁, hc₁, K₁, hK₁⟩ := h₁
  obtain ⟨c₂, hc₂, K₂, hK₂⟩ := h₂
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max K₁ K₂, ?_⟩
  intro k hk
  dsimp only
  by_cases h : k < 10^6
  · have h1 := hK₁ k ((le_max_left K₁ K₂).trans hk) h
    dsimp only at h1
    refine le_trans ?_ h1
    gcongr
    exact min_le_left _ _
  · have h2 := hK₂ k ((le_max_right K₁ K₂).trans hk) (le_of_not_gt h)
    dsimp only at h2
    refine le_trans ?_ h2
    gcongr
    exact min_le_right _ _
