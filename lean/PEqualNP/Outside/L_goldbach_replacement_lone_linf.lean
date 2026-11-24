import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Ring

open Finset

/-- The uniform bound on each weight turns the pointwise product difference
into a sum of two weight errors. -/
theorem PEqualNP.Outside.L_goldbach_replacement_lone_linf :
    let conv := fun (u v : ℕ → ℝ) (n : ℕ) =>
      Finset.sum (Finset.range (n + 1)) (fun k => u k * v (n - k))
    ∀ (u v : ℕ → ℝ) (n : ℕ) (M : ℝ),
      (∀ k ≤ n, |u k| ≤ M ∧ |v k| ≤ M) →
      |conv u u n - conv v v n| ≤
        2 * M * Finset.sum (Finset.range (n + 1)) (fun k => |u k - v k|) := by
  intro conv u v n M hcap
  let d (k : ℕ) : ℝ := |u k - v k|
  have hreflect : (∑ k ∈ range (n + 1), d (n - k)) = ∑ k ∈ range (n + 1), d k := by
    simpa only [Nat.add_sub_cancel] using sum_range_reflect d (n + 1)
  have hterm (k : ℕ) (hk : k ∈ range (n + 1)) :
      |u k * u (n - k) - v k * v (n - k)| ≤ d k * M + M * d (n - k) := by
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
    calc
      _ = |(u k - v k) * u (n - k) + v k * (u (n - k) - v (n - k))| := by
        congr 1
        ring
      _ ≤ |(u k - v k) * u (n - k)| + |v k * (u (n - k) - v (n - k))| :=
        abs_add_le _ _
      _ ≤ _ := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_mul_of_nonneg_left (hcap (n - k) (Nat.sub_le n k)).1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right (hcap k hk').2 (abs_nonneg _))
  calc
    _ = |∑ k ∈ range (n + 1), (u k * u (n - k) - v k * v (n - k))| := by
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ range (n + 1), |u k * u (n - k) - v k * v (n - k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range (n + 1), (d k * M + M * d (n - k)) := Finset.sum_le_sum hterm
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, hreflect]
      change (∑ k ∈ range (n + 1), d k) * M + M * (∑ k ∈ range (n + 1), d k) =
        2 * M * (∑ k ∈ range (n + 1), d k)
      ring
