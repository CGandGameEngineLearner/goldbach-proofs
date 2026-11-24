import Mathlib

theorem PEqualNP.Outside.L_goldbach_pair_errors_swap :
    let C := fun (a b : ℕ → ℝ) (n : ℕ) => ∑ k ∈ Finset.range (n+1), a k*b (n-k); ∀ a b n,C a b n=C b a n := by
  -- zeta 展开：目标即卷积交换 ∑ k ∈ range (n+1), a k * b (n-k) = ∑ k ∈ range (n+1), b k * a (n-k)
  show ∀ (a b : ℕ → ℝ) (n : ℕ),
    ∑ k ∈ Finset.range (n+1), a k * b (n-k) = ∑ k ∈ Finset.range (n+1), b k * a (n-k)
  intro a b n
  -- 指标反射 ∑ k ∈ range (n+1), f k = ∑ k ∈ range (n+1), f (n+1-1-k)。
  -- sum_range_reflect 的陈述方向随 Mathlib 版本略有差异，两种 rw 方向任一成立都把 LHS 反射掉。
  first
  | rw [Finset.sum_range_reflect]
  | rw [← Finset.sum_range_reflect]
  -- 逐项对齐：a (n-k) * b (n-(n-k)) = b k * a (n-k)，其中 n-(n-k) = k 由 k < n+1 保证。
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : k < n + 1 := Finset.mem_range.1 hk
  have e2 : n - (n + 1 - 1 - k) = k := by omega
  have e1 : n + 1 - 1 - k = n - k := by omega
  rw [e2, e1]
  ring
