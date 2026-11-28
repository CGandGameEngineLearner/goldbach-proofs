import Mathlib

-- child 1 zh: 计数前提：在 n = 2^k 的中央窗口里，中心素数对 p、n-p 的个数至少为 c₁·n/(log n)²（c₁ > 0 与 k 无关）。这是本题的算术内容。
-- child 1 en: Counting premise: for n = 2^k the central window contains at least c₁·n/(log n)² prime pairs p, n-p, with c₁ > 0 uniform in k. This is the arithmetic content.
-- child 2 zh: 权重几何：当两个因子都落在窗口 [n/3, 2n/3] 内时，对数权乘积 log p · log(n-p) 至少为 (log n)²/4。这是初等的一步，与计数无关。
-- child 2 en: Weight geometry: whenever both factors lie in the window [n/3, 2n/3] the logarithmic weight product log p · log(n-p) is at least (log n)²/4. This is elementary and independent of the counting.

theorem Conjectures.Cuts.Cut04bb08500e479ae733f19637
    (h₁ : ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k →
      let n : ℕ := 2^k
      let S := (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n)
      c₁ * (n:ℝ) / (Real.log (n:ℝ))^2 ≤ ((S.filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p))).card : ℝ))
    (h₂ : ∃ k₂ : ℕ, ∀ k : ℕ, k₂ ≤ k →
      let n : ℕ := 2^k
      ∀ p : ℕ, n ≤ 3*p → 3*p ≤ 2*n → Nat.Prime p → Nat.Prime (n-p) →
        (Real.log (n:ℝ))^2/4 ≤ (if Nat.Prime p then Real.log (p:ℝ) else 0) * (if Nat.Prime (n-p) then Real.log ((n-p:ℕ):ℝ) else 0)) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0; ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k ≥ k₀, let n : ℕ := 2^k; c*(n : ℝ) ≤ ∑ p ∈ (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n), w p * w (n-p)) := by
  classical
  dsimp only
  obtain ⟨c₁, hc₁, k₁, hP₁⟩ := h₁
  obtain ⟨k₂, hP₂⟩ := h₂
  refine ⟨c₁/4, by positivity, max k₁ (max k₂ 1), ?_⟩
  intro k hk
  have hk₁ : k₁ ≤ k := le_trans (le_max_left k₁ (max k₂ 1)) hk
  have hkmid : max k₂ 1 ≤ k := le_trans (le_max_right k₁ (max k₂ 1)) hk
  have hk₂ : k₂ ≤ k := le_trans (le_max_left k₂ 1) hkmid
  have hk1 : 1 ≤ k := le_trans (le_max_right k₂ 1) hkmid
  set n : ℕ := 2^k with hn
  have hn2 : 2 ≤ n := by
    have h : (2:ℕ)^1 ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk1
    simpa [hn] using h
  have hn_gt_one : (1:ℝ) < (n:ℝ) := by
    have h1n : (1:ℕ) < n := by omega
    exact_mod_cast h1n
  have hlogpos : 0 < Real.log (n:ℝ) := Real.log_pos hn_gt_one
  have hsqpos : 0 < (Real.log (n:ℝ))^2 := by positivity
  have hsqne : (Real.log (n:ℝ))^2 ≠ 0 := ne_of_gt hsqpos
  set S : Finset ℕ := (Finset.range (n+1)).filter (fun p => n ≤ 3*p ∧ 3*p ≤ 2*n) with hS
  set T : Finset ℕ := S.filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p)) with hT
  have hTsub : T ⊆ S := by rw [hT]; exact Finset.filter_subset _ _
  have hmemT : ∀ x, x ∈ T → Nat.Prime x ∧ Nat.Prime (n-x) := by
    intro x hx
    rw [hT] at hx
    exact (Finset.mem_filter.mp hx).2
  have hmemS : ∀ x, x ∈ S → n ≤ 3*x ∧ 3*x ≤ 2*n := by
    intro x hx
    rw [hS] at hx
    exact (Finset.mem_filter.mp hx).2
  have hcard : c₁ * (n:ℝ) / (Real.log (n:ℝ))^2 ≤ (T.card : ℝ) := by
    have h := hP₁ k hk₁
    dsimp only at h
    rw [← hn] at h
    rw [← hS, ← hT] at h
    exact h
  have hsum_eq : (∑ p ∈ T, (if Nat.Prime p then Real.log (p:ℝ) else 0) * (if Nat.Prime (n-p) then Real.log ((n-p:ℕ):ℝ) else 0))
      = (∑ p ∈ S, (if Nat.Prime p then Real.log (p:ℝ) else 0) * (if Nat.Prime (n-p) then Real.log ((n-p:ℕ):ℝ) else 0)) := by
    refine Finset.sum_subset hTsub ?_
    intro x hxS hxT
    have hnp : ¬ (Nat.Prime x ∧ Nat.Prime (n-x)) := by
      intro hc
      exact hxT (by rw [hT]; exact Finset.mem_filter.mpr ⟨hxS, hc⟩)
    by_cases hpx : Nat.Prime x
    · have hnpx : ¬ Nat.Prime (n - x) := fun hcon => hnp ⟨hpx, hcon⟩
      simp [hpx, hnpx]
    · simp [hpx]
  have hpoint : ∀ x ∈ T, (Real.log (n:ℝ))^2/4 ≤
      (if Nat.Prime x then Real.log (x:ℝ) else 0) * (if Nat.Prime (n-x) then Real.log ((n-x:ℕ):ℝ) else 0) := by
    intro x hx
    obtain ⟨hpx, hnpx⟩ := hmemT x hx
    obtain ⟨hlo, hhi⟩ := hmemS x (hTsub hx)
    have h := hP₂ k hk₂
    dsimp only at h
    rw [← hn] at h
    exact h x hlo hhi hpx hnpx
  have hbound : (T.card : ℝ) * ((Real.log (n:ℝ))^2/4) ≤
      (∑ x ∈ T, (if Nat.Prime x then Real.log (x:ℝ) else 0) * (if Nat.Prime (n-x) then Real.log ((n-x:ℕ):ℝ) else 0)) := by
    have h := Finset.sum_le_sum hpoint
    simpa only [Finset.sum_const, nsmul_eq_mul] using h
  rw [← hsum_eq]
  calc c₁/4 * (n:ℝ)
      = (c₁ * (n:ℝ) / (Real.log (n:ℝ))^2) * ((Real.log (n:ℝ))^2/4) := by
        field_simp
    _ ≤ (T.card : ℝ) * ((Real.log (n:ℝ))^2/4) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (∑ x ∈ T, (if Nat.Prime x then Real.log (x:ℝ) else 0) * (if Nat.Prime (n-x) then Real.log ((n-x:ℕ):ℝ) else 0)) := hbound
