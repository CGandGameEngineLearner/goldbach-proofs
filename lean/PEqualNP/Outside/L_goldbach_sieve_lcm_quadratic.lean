import Mathlib

theorem PEqualNP.Outside.L_goldbach_sieve_lcm_quadratic :
    ∀ (x : ℕ) (m : ℕ → ℕ) (D : Finset ℕ) (w : ℕ → ℝ),
     (∑ k ∈ Finset.range x, (∑ d ∈ D.filter (fun d => d∣m k), w d)^2)
     = ∑ a ∈ D, ∑ b ∈ D, w a*w b*(((Finset.range x).filter (fun k => Nat.lcm a b∣m k)).card : ℝ) := by
  intro x m D w
  have hk : ∀ k ∈ Finset.range x,
      (∑ d ∈ D.filter (fun d => d ∣ m k), w d)^2
      = ∑ a ∈ D, ∑ b ∈ D, (if a ∣ m k ∧ b ∣ m k then w a * w b else 0) := by
    intro k _
    rw [pow_two, Finset.sum_filter, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    by_cases h1 : a ∣ m k <;> by_cases h2 : b ∣ m k <;> simp [h1, h2]
  rw [Finset.sum_congr rfl hk]
  trans (∑ a ∈ D, ∑ b ∈ D,
      ∑ k ∈ Finset.range x, (if a ∣ m k ∧ b ∣ m k then w a * w b else 0))
  · rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
  · refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [← Finset.sum_filter]
    have hf : (Finset.range x).filter (fun k => a ∣ m k ∧ b ∣ m k)
        = (Finset.range x).filter (fun k => Nat.lcm a b ∣ m k) := by
      apply Finset.filter_congr
      intro k _
      exact Nat.lcm_dvd_iff.symm
    rw [hf, Finset.sum_const, nsmul_eq_mul]
    ring