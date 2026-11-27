import Mathlib

open Finset

private theorem sum_by_divisor_and_quotient (n U B : ℕ) (f : ℕ → ℕ → ℕ → ℂ) :
    (∑ m ∈ range (n + 1), ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a),
      f m a (m / a)) =
    ∑ a ∈ Icc (U + 1) B, ∑ r ∈ Icc (U + 1) (n / a), f (a * r) a r := by
  classical
  have hfilter (m : ℕ) :
      m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a) =
        (Icc (U + 1) B).filter (fun a => a ∣ m ∧ m ≠ 0 ∧ U < m / a) := by
    ext a
    simp only [mem_filter, Nat.mem_divisors, mem_Icc]
    omega
  calc
    _ = ∑ m ∈ range (n + 1), ∑ a ∈ Icc (U + 1) B,
        if a ∣ m ∧ m ≠ 0 ∧ U < m / a then f m a (m / a) else 0 := by
      simp only [hfilter, sum_filter]
    _ = ∑ a ∈ Icc (U + 1) B, ∑ m ∈ (range (n + 1)).filter
        (fun m => a ∣ m ∧ m ≠ 0 ∧ U < m / a), f m a (m / a) := by
      simp only [sum_filter]
      exact sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro a ha
      have ha0 : 0 < a := (Nat.zero_lt_succ U).trans_le (mem_Icc.mp ha).1
      refine sum_bij (fun m _ => m / a) ?_ ?_ ?_ ?_
      · intro m hm
        have h := mem_filter.mp hm
        exact mem_Icc.mpr ⟨h.2.2.2, Nat.div_le_div_right (Nat.le_of_lt_succ (mem_range.mp h.1))⟩
      · intro m hm k hk heq
        have hm' := Nat.mul_div_cancel' (mem_filter.mp hm).2.1
        have hk' := Nat.mul_div_cancel' (mem_filter.mp hk).2.1
        rw [← hm', ← hk', heq]
      · intro r hr
        obtain ⟨hl, hh⟩ := mem_Icc.mp hr
        have hd : a * r / a = r := Nat.mul_div_cancel_left r ha0
        refine ⟨a * r, mem_filter.mpr ⟨?_, dvd_mul_right a r, ?_, ?_⟩, hd⟩
        · apply mem_range.mpr
          exact Nat.lt_succ_of_le (by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha0).mp hh)
        · exact Nat.ne_of_gt (Nat.mul_pos ha0 ((Nat.zero_lt_succ U).trans_le hl))
        · rwa [hd]
      · intro m hm
        rw [Nat.mul_div_cancel' (mem_filter.mp hm).2.1]

private theorem weighted_divisor_sum (n U B : ℕ) (c v : ℕ → ℝ) (phase : ℕ → ℂ) :
    (∑ m ∈ range (n + 1),
      ((∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a),
        c a * v (m / a) : ℝ) : ℂ) * phase m) =
    ∑ a ∈ Icc (U + 1) B, (c a : ℂ) *
      ∑ r ∈ Icc (U + 1) (n / a), (v r : ℂ) * phase (a * r) := by
  calc
    _ = ∑ m ∈ range (n + 1), ∑ a ∈ m.divisors.filter (fun a => U < a ∧ a ≤ B ∧ U < m / a),
        (c a : ℂ) * (v (m / a) : ℂ) * phase m := by
      apply sum_congr rfl
      intro m _
      rw [Complex.ofReal_sum, sum_mul]
      apply sum_congr rfl
      intro a _
      rw [Complex.ofReal_mul]
    _ = ∑ a ∈ Icc (U + 1) B, ∑ r ∈ Icc (U + 1) (n / a),
        (c a : ℂ) * (v r : ℂ) * phase (a * r) :=
      sum_by_divisor_and_quotient n U B (fun m a r => (c a : ℂ) * (v r : ℂ) * phase m)
    _ = _ := by
      apply sum_congr rfl
      intro a _
      rw [mul_sum]
      apply sum_congr rfl
      intro r _
      rw [mul_assoc]

theorem Conjectures.Goldbach.FrontierType2B1B1BilinearExpansion :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * ArithmeticFunction.vonMangoldt (m / a); ∀ (n : ℕ) (t : ℝ), S n (τ₁ n) t = ∑ a ∈ Finset.Icc (U n + 1) (B₁ n), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * ∑ r ∈ Finset.Icc (U n + 1) (n / a), ArithmeticFunction.vonMangoldt r * E (((a*r:ℕ):ℝ)*t) := by
  dsimp only
  intro n t
  exact weighted_divisor_sum n ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊ ⌊(n : ℝ) ^ (1 / 4 : ℝ)⌋₊
    (fun a => ∑ d ∈ a.divisors.filter (fun d => ⌊(n : ℝ) ^ (1 / 16 : ℝ)⌋₊ < d),
      ((ArithmeticFunction.moebius d : ℤ) : ℝ))
    ArithmeticFunction.vonMangoldt
    (fun m => Complex.exp (((2 * Real.pi * ((m : ℝ) * t) : ℝ) : ℂ) * Complex.I))
