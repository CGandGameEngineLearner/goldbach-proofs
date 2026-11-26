import Mathlib

namespace PEqualNP.Outside.L_twin_primes_mellin_tail_aux

/-- Telescoping majorant for the fifth-order tail: for `1 ≤ a ≤ y`,
`1 / y ^ 5 ≤ (2 / a ^ 3) * (1 / y - 1 / (y + 1))`.

The point is that `a ^ 3 ≤ y ^ 3` and `y + 1 ≤ 2 * y`, hence
`a ^ 3 * y * (y + 1) ≤ 2 * y ^ 5`, while `1 / y - 1 / (y + 1) = 1 / (y * (y + 1))`. -/
theorem tail_step {a y : ℝ} (ha : 1 ≤ a) (hay : a ≤ y) :
    1 / y ^ 5 ≤ 2 / a ^ 3 * (1 / y - 1 / (y + 1)) := by
  have hapos : 0 < a := by linarith
  have hypos : 0 < y := lt_of_lt_of_le hapos hay
  have hcube : a ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hapos.le hay 3
  have hkey : a ^ 3 * y * (y + 1) ≤ 2 * y ^ 5 := by
    have h1 : a ^ 3 * y ≤ y ^ 3 * y := mul_le_mul_of_nonneg_right hcube hypos.le
    have h2 : y + 1 ≤ 2 * y := by linarith
    calc a ^ 3 * y * (y + 1) ≤ y ^ 3 * y * (y + 1) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ y ^ 3 * y * (2 * y) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (pow_nonneg hypos.le 3) hypos.le)
      _ = 2 * y ^ 5 := by ring
  have hsub : (1 : ℝ) / y - 1 / (y + 1) = 1 / (y * (y + 1)) := by
    field_simp [ne_of_gt hypos, show y + 1 ≠ 0 by linarith]
    ring
  rw [hsub]
  have hrhs : 2 / a ^ 3 * (1 / (y * (y + 1))) = 2 / (a ^ 3 * y * (y + 1)) := by
    rw [div_mul_div_comm, mul_one]
    congr 1
    ring
  rw [hrhs, div_le_div_iff₀ (pow_pos hypos 5)
    (mul_pos (mul_pos (pow_pos hapos 3) hypos) (by linarith))]
  calc (1 : ℝ) * (a ^ 3 * y * (y + 1)) = a ^ 3 * y * (y + 1) := one_mul _
    _ ≤ 2 * y ^ 5 := hkey

end PEqualNP.Outside.L_twin_primes_mellin_tail_aux

open PEqualNP.Outside.L_twin_primes_mellin_tail_aux

theorem PEqualNP.Outside.L_twin_primes_mellin_tail : ∀ C : ℝ, 0 ≤ C → ∃ D : ℝ, 0 ≤ D ∧ ∀ (L : ℕ) (m : ℕ → ℝ), (∀ n, 0 ≤ m n ∧ m n ≤ C*Real.log (2+(n:ℝ))) → (∑' n : ℕ, m (L+n)/(1+(L:ℝ)+n)^6) ≤ D/(1+(L:ℝ))^4 := by
  intro C hC
  refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
  intro L m hm
  set a : ℝ := 1 + (L:ℝ) with ha
  have ha1 : 1 ≤ a := by
    rw [ha]
    have hL : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
    linarith
  have hapos : 0 < a := by linarith
  -- Pointwise domination of each summand by a telescoping step.
  have hterm : ∀ n : ℕ, m (L + n) / (a + (n:ℝ)) ^ 6
      ≤ (2 * C / a ^ 3) * (1 / (a + (n:ℝ)) - 1 / (a + ((n + 1 : ℕ) : ℝ))) := by
    intro n
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hy1 : 1 ≤ a + (n:ℝ) := by linarith
    have hypos : 0 < a + (n:ℝ) := by linarith
    -- `log z ≤ z - 1` absorbs the logarithm into one power of the distance.
    have hlog : Real.log (2 + ((L + n : ℕ) : ℝ)) ≤ a + (n:ℝ) := by
      have h0 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 + ((L + n : ℕ) : ℝ) by positivity)
      push_cast at h0 ⊢
      linarith
    have hmle : m (L + n) ≤ C * (a + (n:ℝ)) :=
      le_trans (hm (L + n)).2 (mul_le_mul_of_nonneg_left hlog hC)
    have hstep : m (L + n) / (a + (n:ℝ)) ^ 6 ≤ C / (a + (n:ℝ)) ^ 5 := by
      rw [div_le_div_iff₀ (pow_pos hypos 6) (pow_pos hypos 5)]
      calc m (L + n) * (a + (n:ℝ)) ^ 5 ≤ C * (a + (n:ℝ)) * (a + (n:ℝ)) ^ 5 :=
            mul_le_mul_of_nonneg_right hmle (pow_nonneg hypos.le 5)
        _ = C * (a + (n:ℝ)) ^ 6 := by ring
    have htel : 1 / (a + (n:ℝ)) ^ 5
        ≤ 2 / a ^ 3 * (1 / (a + (n:ℝ)) - 1 / (a + (n:ℝ) + 1)) := tail_step ha1 (by linarith)
    calc m (L + n) / (a + (n:ℝ)) ^ 6 ≤ C / (a + (n:ℝ)) ^ 5 := hstep
      _ = C * (1 / (a + (n:ℝ)) ^ 5) := by ring
      _ ≤ C * (2 / a ^ 3 * (1 / (a + (n:ℝ)) - 1 / (a + (n:ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left htel hC
      _ = (2 * C / a ^ 3) * (1 / (a + (n:ℝ)) - 1 / (a + ((n + 1 : ℕ) : ℝ))) := by
          push_cast
          ring
  -- Every partial sum telescopes and stays below `2 * C / a ^ 4`.
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, m (L + n) / (a + (n:ℝ)) ^ 6 ≤ 2 * C / a ^ 4 := by
    intro N
    have hK : (0:ℝ) ≤ 2 * C / a ^ 3 := div_nonneg (mul_nonneg (by norm_num) hC) (pow_nonneg hapos.le 3)
    have hN : (0:ℝ) ≤ 1 / (a + (N:ℝ)) :=
      div_nonneg zero_le_one (add_nonneg hapos.le (Nat.cast_nonneg N))
    calc ∑ n ∈ Finset.range N, m (L + n) / (a + (n:ℝ)) ^ 6
        ≤ ∑ n ∈ Finset.range N, (2 * C / a ^ 3) *
            (1 / (a + (n:ℝ)) - 1 / (a + ((n + 1 : ℕ) : ℝ))) :=
          Finset.sum_le_sum fun n _ => hterm n
      _ = (2 * C / a ^ 3) * ∑ n ∈ Finset.range N,
            (1 / (a + (n:ℝ)) - 1 / (a + ((n + 1 : ℕ) : ℝ))) := by
          rw [Finset.mul_sum]
      _ = (2 * C / a ^ 3) * (1 / (a + ((0:ℕ):ℝ)) - 1 / (a + (N:ℝ))) := by
          congr 1
          exact Finset.sum_range_sub' (fun i : ℕ => 1 / (a + (i:ℝ))) N
      _ ≤ (2 * C / a ^ 3) * (1 / (a + ((0:ℕ):ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          push_cast
          linarith
      _ = 2 * C / a ^ 4 := by
          rw [show (1:ℝ) / (a + ((0:ℕ):ℝ)) = 1 / a by push_cast; ring]
          rw [div_mul_div_comm, mul_one, show a ^ 3 * a = a ^ 4 by ring]
  -- The partial-sum bound gives the `tsum` bound, with no summability argument.
  exact Real.tsum_le_of_sum_range_le
    (f := fun n : ℕ => m (L + n) / (a + (n:ℝ)) ^ 6) (c := 2 * C / a ^ 4)
    (fun n => div_nonneg (hm (L + n)).1
      (pow_nonneg (add_nonneg hapos.le (Nat.cast_nonneg n)) 6))
    hpartial
