import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

-- child 1 zh: 采用小区间的常数认证和素数倒数和界，含两个端点。
-- child 1 en: Use the certified constant and reciprocal-prime bounds on the closed small range.
-- child 2 zh: 在 exp(10) 与十的十二次方之间使用中段双边估计。
-- child 2 en: Bound the reciprocal-prime sum on the middle range through ten to the twelfth.
-- child 3 zh: 在超过十的十二次方的整数处验证严格截断素数和的下界。
-- child 3 en: Give the lower tail bound at integers above the breakpoint, excluding a prime endpoint.
-- child 4 zh: 在不小于尾段起点的整数右侧验证包含端点素数的上界。
-- child 4 en: Give the upper tail bound just to the right of each integer from the breakpoint, including a prime endpoint.

theorem Conjectures.Cuts.Cut2143515b331c5320a8601cee
    (hsmall : let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); (0.261497 ≤ M0 ∧ M0 ≤ 0.261498) ∧ ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp 10 → Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + (if Real.log x > 8.9 then (1.614e-3 : ℝ) else (1 : ℝ)))
    (hmiddle : let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); ∀ x : ℝ, Real.exp 10 < x → x ≤ (10 : ℝ) ^ 12 → Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + 2 / (Real.sqrt x * Real.log x))
    (hlower : let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); ∀ k : ℕ, 10^12 < k → Real.log (Real.log (k:ℝ)) + M0 - (2.964e-6 : ℝ) / Real.log (k:ℝ) ≤ (∑ p ∈ (Finset.range k).filter Nat.Prime, (1 : ℝ) / (p : ℝ)))
    (hupper : let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); ∀ k : ℕ, 10^12 ≤ k → (∑ p ∈ (Finset.range (k+1)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log (k:ℝ)) + M0 + (6.836e-6 : ℝ) / Real.log (k:ℝ)) :
    (let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); let E_lo : ℝ → ℝ := fun x => (2.964e-6 : ℝ) / Real.log x; let E_hi : ℝ → ℝ := fun x => if x > (10 : ℝ) ^ 12 then (6.836e-6 : ℝ) / Real.log x else if Real.log x > 10 then 2 / (Real.sqrt x * Real.log x) else if Real.log x > 8.9 then (1.614e-3 : ℝ) else (1 : ℝ); (0.261497 ≤ M0 ∧ M0 ≤ 0.261498) ∧ ∀ x : ℝ, 2 ≤ x → Real.log (Real.log x) + M0 - E_lo x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + E_hi x) := by
  have tail_upper_mono {a b : ℝ} (ha : (10:ℝ)^12 ≤ a) (hab : a ≤ b) :
      Real.log (Real.log a) + (6.836e-6 : ℝ) / Real.log a ≤
      Real.log (Real.log b) + (6.836e-6 : ℝ) / Real.log b := by
    let A := Real.log a
    let B := Real.log b
    have h2a : 2 ≤ a := (by norm_num : (2 : ℝ) ≤ 10^12).trans ha
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    have h₂a := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2a
    have hc : (6.836e-6 : ℝ) ≤ A := by
      dsimp [A]
      norm_num at h2
      linarith
    have hA : 0 < A := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 6.836e-6) hc
    have hAB : A ≤ B := Real.log_le_log (by linarith) hab
    have hB : 0 < B := hA.trans_le hAB
    have hlog := Real.log_le_sub_one_of_pos (div_pos hA hB)
    rw [Real.log_div hA.ne' hB.ne'] at hlog
    have hbound : (6.836e-6 : ℝ) / A - 6.836e-6 / B ≤ 1 - A / B := by
      field_simp
      nlinarith only [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr hAB)]
    change Real.log A + _ / A ≤ Real.log B + _ / B
    linarith only [hlog, hbound]

  have tail_grid (M : ℝ) (S : ℕ → ℝ) (hs : Monotone S)
      (hm : ∀ {a b : ℝ}, (10:ℝ)^12 ≤ a → a ≤ b →
        Real.log (Real.log a) + (6.836e-6:ℝ)/Real.log a ≤
          Real.log (Real.log b) + (6.836e-6:ℝ)/Real.log b)
      (hl : ∀ k : ℕ, 10^12 < k →
        Real.log (Real.log (k:ℝ)) + M - (2.964e-6:ℝ)/Real.log k ≤ S k)
      (hu : ∀ k : ℕ, 10^12 ≤ k →
        S (k+1) ≤ Real.log (Real.log (k:ℝ)) + M + (6.836e-6:ℝ)/Real.log k)
      (x : ℝ) (hx : (10:ℝ)^12 < x) :
      Real.log (Real.log x)+M-(2.964e-6:ℝ)/Real.log x ≤ S ⌈x⌉₊ ∧
      S ⌈x⌉₊ ≤ Real.log (Real.log x)+M+(6.836e-6:ℝ)/Real.log x := by
    have hx1 : 1 < x := lt_trans (by norm_num) hx
    have hx0 : 0 < x := zero_lt_one.trans hx1
    have hc : (10:ℕ)^12 < ⌈x⌉₊ := by exact_mod_cast (hx.trans_le (Nat.le_ceil x))
    have hf : (10:ℕ)^12 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0.le).mpr (by exact_mod_cast hx.le)
    constructor
    · have hlog := Real.log_le_log hx0 (Nat.le_ceil x)
      have hpos := Real.log_pos hx1
      have hlog2 := Real.log_le_log hpos hlog
      have hdiv := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2.964e-6) hpos hlog
      linarith only [hlog2, hdiv, hl _ hc]
    · have hmono := hm (a := (⌊x⌋₊:ℝ)) (by exact_mod_cast hf) (Nat.floor_le hx0.le)
      linarith only [hmono, hs (Nat.ceil_le_floor_add_one x), hu _ hf]
  intro M ELo EHi
  refine ⟨hsmall.1, ?_⟩
  intro x hx
  by_cases ht : (10:ℝ)^12 < x
  · let S := fun k : ℕ => ∑ p ∈ (Finset.range k).filter Nat.Prime, (1:ℝ) / (p:ℝ)
    have hs : Monotone S := by
      intro i k hik
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset_filter _ (Finset.range_mono hik)
      · intro p _ _
        positivity
    simpa only [ELo, EHi, ite_eq_left ht, S] using
      (tail_grid M S hs (fun ha hab => tail_upper_mono ha hab) hlower hupper x ht)
  · by_cases hm : Real.exp 10 < x
    · have hlog : 10 < Real.log x := (Real.lt_log_iff_exp_lt (by linarith)).2 hm
      simpa only [ELo, EHi, ite_eq_right ht, ite_eq_left hlog] using hmiddle x hm (le_of_not_gt ht)
    · have hlog : ¬ 10 < Real.log x := fun hh =>
        hm ((Real.lt_log_iff_exp_lt (by linarith)).1 hh)
      simpa only [ELo, EHi, ite_eq_right ht, ite_eq_right hlog] using hsmall.2 x hx (le_of_not_gt hm)
