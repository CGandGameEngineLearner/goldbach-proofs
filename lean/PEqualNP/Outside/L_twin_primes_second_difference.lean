import Mathlib

private theorem PEqualNP.Outside.L_twin_primes_second_difference_aux.telescope (a : ℕ → ℝ) (N : ℕ) :
    (Finset.range N).sum (fun t => (a (t+2) + a (t+1) + a t)^2 - 2*(a (t+1) + a t)^2 + a t^2)
      = 2 * (Finset.range N).sum (fun t => a t * a (t+2)) + a (N+1)^2 - a 1^2
        + 2 * a (N+1) * a N - 2 * a 1 * a 0 := by
  induction N with
  | zero => simp only [Finset.sum_range_zero, Nat.zero_add]; ring
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, show N + 1 + 1 = N + 2 by ring]
    ring

theorem PEqualNP.Outside.L_twin_primes_second_difference :
    let v := fun (X n : ℕ) => if n ≤ X then ArithmeticFunction.vonMangoldt n else 0; let F := fun (X H : ℕ) => (Finset.range (X+H+1)).sum (fun t => ((Finset.range H).sum (fun j => if j ≤ t then v X (t-j) else 0))^2); let C := fun (X h : ℕ) => (Finset.range (X+1)).sum (fun n => v X n * v X (n+h)); ∀ X : ℕ, F X 3-2*F X 2+F X 1 = 2*C X 2 := by
  intro v F C X
  have ha : ∀ n, X < n → v X n = 0 := fun n hn => by
    simp only [v, ite_eq_right_iff]; intro h; omega
  have hF1 : F X 1 = (Finset.range (X+1+1)).sum (fun t => (v X t)^2) := by
    simp only [F, Finset.sum_range_one, zero_le, ↓reduceIte, Nat.sub_zero]
  have hF2 : F X 2 = (Finset.range (X+1+1)).sum (fun t => (v X (t+1) + v X t)^2) + (v X 0)^2 := by
    simp only [F]
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro t _
      simp [Finset.sum_range_succ]
    · simp
  have hF3 : F X 3 = (Finset.range (X+1+1)).sum (fun t => (v X (t+2) + v X (t+1) + v X t)^2)
      + (v X 1 + v X 0)^2 + (v X 0)^2 := by
    simp only [F]
    rw [show X + 3 + 1 = X + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ', Finset.sum_range_succ']
    congr 1
    congr 1
    · apply Finset.sum_congr rfl
      intro t _
      simp [Finset.sum_range_succ]
    · simp [Finset.sum_range_succ]
    · simp
  have hC : C X 2 = (Finset.range (X+1+1)).sum (fun t => v X t * v X (t+2)) := by
    simp only [C]
    rw [Finset.sum_range_succ (fun t => v X t * v X (t+2)) (X+1), ha (X+1+2) (by omega), mul_zero,
      add_zero]
  have T := PEqualNP.Outside.L_twin_primes_second_difference_aux.telescope (v X) (X+1+1)
  rw [ha (X+1+1+1) (by omega)] at T
  have hD : (Finset.range (X+1+1)).sum
      (fun t => (v X (t+2) + v X (t+1) + v X t)^2 - 2*(v X (t+1) + v X t)^2 + v X t^2)
      = (Finset.range (X+1+1)).sum (fun t => (v X (t+2) + v X (t+1) + v X t)^2)
        - 2 * (Finset.range (X+1+1)).sum (fun t => (v X (t+1) + v X t)^2)
        + (Finset.range (X+1+1)).sum (fun t => (v X t)^2) := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hF3, hF2, hF1, hC]
  linear_combination T - hD
