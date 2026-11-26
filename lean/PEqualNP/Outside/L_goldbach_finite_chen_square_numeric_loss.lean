import Mathlib

open Finset

/-- At this threshold the fourth root of n dominates 1000 log n. The
logarithm tangent at 2^15 gives an explicit uniform estimate. -/
private theorem log_window {n : ℕ} (hn : 4000000000000000000 ≤ n) :
    10^6 * (Real.log n)^2 ≤ Real.sqrt n := by
  let y := Real.sqrt (Real.sqrt (n:ℝ))
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hy2 : y^2 = Real.sqrt (n:ℝ) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hy4 : y^4 = (n:ℝ) := by
    rw [show (4:ℕ) = 2*2 by decide, pow_mul, hy2, Real.sq_sqrt (Nat.cast_nonneg n)]
  have hn' : (4000000000000000000:ℝ) ≤ n := by exact_mod_cast hn
  have hylo : 44000 ≤ y := by
    by_contra! h
    have h4 := pow_lt_pow_left₀ h hy (by decide : 4 ≠ 0)
    linarith only [hy4, hn', h4]
  have hyp : 0 < y := by linarith
  have hbase : Real.log (32768:ℝ) = 15*Real.log 2 := by
    rw [show (32768:ℝ) = 2^15 by norm_num, Real.log_pow]
    norm_num
  have hratio := Real.log_le_sub_one_of_pos (div_pos hyp (by norm_num : (0:ℝ)<32768))
  rw [Real.log_div hyp.ne' (by norm_num), hbase] at hratio
  have hln : 1000*Real.log n ≤ y := by
    rw [← hy4, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hratio, hylo, Real.log_two_lt_d9]
  have hpos := Real.log_nonneg (show (1:ℝ) ≤ n by linarith)
  have hsq := pow_le_pow_left₀ (show 0 ≤ 1000*Real.log n by positivity) hln 2
  nlinarith only [hsq,hy2]

theorem PEqualNP.Outside.L_goldbach_finite_chen_square_numeric_loss :
    let P := fun n : ℕ => (Finset.range (n+1)).filter (fun p =>
      Nat.Prime p ∧ Nat.Prime (Nat.sqrt (n-p)) ∧ (Nat.sqrt (n-p))^2=n-p)
    ∀ n : ℕ, 4000000000000000000 ≤ n → ((P n).card:ℝ) ≤ (n:ℝ)/(10^6*(Real.log n)^2) := by
  intro P n hn
  have hcard : (P n).card ≤ (Icc 1 (Nat.sqrt n)).card := by
    apply card_le_card_of_injOn (fun p => Nat.sqrt (n-p))
    · intro p hp
      have h := (mem_filter.mp hp).2
      exact mem_Icc.mpr ⟨h.2.1.one_le, Nat.sqrt_le_sqrt (Nat.sub_le n p)⟩
    · intro p hp q hq h
      have hp' := mem_filter.mp hp
      have hq' := mem_filter.mp hq
      have heq := congrArg (fun a : ℕ => a^2) h
      change Nat.sqrt (n-p)^2 = Nat.sqrt (n-q)^2 at heq
      rw [hp'.2.2.2,hq'.2.2.2] at heq
      have := mem_range.mp hp'.1
      have := mem_range.mp hq'.1
      omega
  have hle : (P n).card ≤ Nat.sqrt n := by simpa using hcard
  have hlin : ((P n).card:ℝ) ≤ Real.sqrt n :=
    (show ((P n).card:ℝ) ≤ (Nat.sqrt n:ℝ) by exact_mod_cast hle).trans Real.nat_sqrt_le_real_sqrt
  apply hlin.trans
  have hlog := Real.log_pos (show (1:ℝ)<n by exact_mod_cast (by omega : 1<n))
  apply (le_div_iff₀ (by positivity)).mpr
  calc
    _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left (log_window hn) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (Nat.cast_nonneg n)
