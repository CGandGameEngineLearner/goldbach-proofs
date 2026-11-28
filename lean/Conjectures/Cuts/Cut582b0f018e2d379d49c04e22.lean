import Mathlib

-- child 1 zh: 在充分大的二次幂的奇数中央窗内，反射两端的一阶素数对数权之和经奇偶均值校正后，至少为 (2/3−ε)n，对任意 ε>0 成立。
-- child 1 en: On the odd central window of every sufficiently large power of two, the linear term after centering the prime log weights at 2 is at least (2/3−ε)n for every ε>0.
-- child 2 zh: 在同一奇数中央窗内，两端素数对数权各自减去 2 后的乘积之和，最终至少为 (−2/3+δ)n，其中 δ 是固定正数。
-- child 2 en: On the same odd central window, the sum of the products of the two prime log weights centered at 2 is eventually at least (−2/3+δ)n for some fixed δ>0.

theorem Conjectures.Cuts.Cut582b0f018e2d379d49c04e22
    (h₁ :
      let w := fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0
      ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ k ≥ K,
        let n : ℕ := 2^k
        let I := (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n ∧ p % 2 = 1)
        (2/3 - ε) * (n : ℝ) ≤ ∑ p ∈ I, (2*w p + 2*w (n-p) - 4))
    (h₂ :
      let w := fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0
      ∃ δ : ℝ, 0 < δ ∧ ∃ K : ℕ, ∀ k ≥ K,
        let n : ℕ := 2^k
        let I := (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n ∧ p % 2 = 1)
        (-2/3 + δ) * (n : ℝ) ≤ ∑ p ∈ I, (w p - 2) * (w (n-p) - 2)) : (let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, let n : ℕ := 2^k; c*(n : ℝ) ≤ ∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p)) := by
  intro w
  obtain ⟨δ, hδ, K₂, hcorr⟩ := h₂
  obtain ⟨K₁, hlin⟩ := h₁ (δ/2) (by positivity)
  refine ⟨δ/2, by positivity, max K₁ K₂, ?_⟩
  intro k hk
  let n : ℕ := 2^k
  let full := (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n)
  let I := (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n ∧ p % 2 = 1)
  have h₁k : (2/3 - δ/2) * (n : ℝ) ≤ ∑ p ∈ I, (2*w p + 2*w (n-p) - 4) :=
    hlin k ((le_max_left _ _).trans hk)
  have h₂k : (-2/3 + δ) * (n : ℝ) ≤ ∑ p ∈ I, (w p - 2) * (w (n-p) - 2) :=
    hcorr k ((le_max_right _ _).trans hk)
  have hsub : I ⊆ full := by
    intro p hp
    obtain ⟨hr, hl, hu, _⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hr, hl, hu⟩
  have hw (p : ℕ) : 0 ≤ w p := by
    dsimp [w]
    split <;> simp [Real.log_natCast_nonneg]
  calc
    δ/2 * (n : ℝ) = (2/3 - δ/2) * n + (-2/3 + δ) * n := by ring
    _ ≤ (∑ p ∈ I, (2*w p + 2*w (n-p) - 4)) + ∑ p ∈ I, (w p - 2) * (w (n-p) - 2) :=
      by linarith only [h₁k, h₂k]
    _ = ∑ p ∈ I, w p * w (n-p) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ ∑ p ∈ full, w p * w (n-p) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => mul_nonneg (hw p) (hw (n-p)))
