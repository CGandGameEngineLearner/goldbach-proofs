import Mathlib

-- child 1 zh: 认证 Meissel–Mertens 常数的上下界。
-- child 1 en: Certify the numerical lower and upper bounds for the Meissel–Mertens constant.
-- child 2 zh: 在有限整数网格上，用常数上界认证素数倒数和的下界。
-- child 2 en: Certify the lower reciprocal-prime inequality on the finite integer grid using the upper constant bound.
-- child 3 zh: 用左端点对数与常数下界，认证每个整数格对应的素数倒数和上界。
-- child 3 en: Certify the upper reciprocal-prime inequality on each grid cell using its left endpoint and the lower constant bound.

theorem Conjectures.Cuts.Cutdde1e7ef243203eb1faa06c9
    (constant :
      let M₀ : ℝ := Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))
      0.261497 ≤ M₀ ∧ M₀ ≤ 0.261498)
    (lowerGrid : ∀ n : ℕ, 2 ≤ n → n ≤ Nat.ceil (Real.exp (10 : ℝ)) →
      Real.log (Real.log (n : ℝ)) + (0.261498 : ℝ) - (2.964e-6 : ℝ) / Real.log (n : ℝ) ≤
        ∑ p ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
    (upperGrid : ∀ n : ℕ, 2 ≤ n → n ≤ Nat.ceil (Real.exp (10 : ℝ)) →
      (∑ p ∈ (Finset.range n).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
        Real.log (Real.log ((max 2 (n - 1) : ℕ) : ℝ)) + (0.261497 : ℝ) +
          if (8.9 : ℝ) < Real.log (n : ℝ) then (1.614e-3 : ℝ) else 1) :
    (let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); (0.261497 ≤ M0 ∧ M0 ≤ 0.261498) ∧ ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp 10 → Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + (if Real.log x > 8.9 then (1.614e-3 : ℝ) else (1 : ℝ))) := by
  have ceilBounds {x : ℝ} (hx : 2 ≤ x) :
      let n := Nat.ceil x
      2 ≤ n ∧ x ≤ (n : ℝ) ∧ ((max 2 (n - 1) : ℕ) : ℝ) ≤ x := by
    intro n
    have hxn : x ≤ (n : ℝ) := Nat.le_ceil x
    have hn2 : 2 ≤ n := by exact_mod_cast hx.trans hxn
    have hStrict : (n : ℝ) < x + 1 :=
      Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
    have hPrev : ((n - 1 : ℕ) : ℝ) ≤ x := by
      rw [Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one]
      linarith
    refine ⟨hn2, hxn, ?_⟩
    rw [Nat.cast_max]
    exact max_le hx hPrev

  have ceilLeExpTen {x : ℝ} (hx : x ≤ Real.exp 10) :
      Nat.ceil x ≤ Nat.ceil (Real.exp 10) :=
    Nat.ceil_mono hx

  let M₀ : ℝ := Real.eulerMascheroniConstant +
    ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))
  have hC : (0.261497 : ℝ) ≤ M₀ ∧ M₀ ≤ (0.261498 : ℝ) := constant
  refine ⟨hC, ?_⟩
  intro x hx hTop
  let n := Nat.ceil x
  obtain ⟨hn, hxN, hLeftX⟩ := ceilBounds hx
  have hnTop : n ≤ Nat.ceil (Real.exp (10 : ℝ)) := ceilLeExpTen hTop
  have hLogX : 0 < Real.log x := Real.log_pos (by linarith)
  have hLogXN : Real.log x ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by linarith) hxN
  have hLogLogXN : Real.log (Real.log x) ≤ Real.log (Real.log (n : ℝ)) :=
    Real.log_le_log hLogX hLogXN
  have hRecip : (2.964e-6 : ℝ) / Real.log (n : ℝ) ≤ (2.964e-6 : ℝ) / Real.log x := by
    have hinv := one_div_le_one_div_of_le hLogX hLogXN
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hinv (by positivity : 0 ≤ (2.964e-6 : ℝ))
  have hLeftTwo : (2 : ℝ) ≤ ((max 2 (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast (le_max_left (2 : ℕ) (n - 1))
  have hLogLeft : 0 < Real.log ((max 2 (n - 1) : ℕ) : ℝ) := Real.log_pos (by linarith)
  have hLogLogLeft : Real.log (Real.log ((max 2 (n - 1) : ℕ) : ℝ)) ≤ Real.log (Real.log x) :=
    Real.log_le_log hLogLeft (Real.log_le_log (by linarith) hLeftX)
  have hAllowance :
      (if (8.9 : ℝ) < Real.log (n : ℝ) then (1.614e-3 : ℝ) else 1) ≤
        if (8.9 : ℝ) < Real.log x then (1.614e-3 : ℝ) else 1 := by
    by_cases hxLarge : (8.9 : ℝ) < Real.log x
    · have hnLarge := hxLarge.trans_le hLogXN
      simp only [ite_eq_left hxLarge, ite_eq_left hnLarge, le_refl]
    · rw [ite_eq_right hxLarge]
      split <;> norm_num
  constructor
  · calc
      Real.log (Real.log x) + M₀ - (2.964e-6 : ℝ) / Real.log x ≤
          Real.log (Real.log (n : ℝ)) + (0.261498 : ℝ) - (2.964e-6 : ℝ) / Real.log (n : ℝ) :=
        sub_le_sub (add_le_add hLogLogXN hC.2) hRecip
      _ ≤ _ := lowerGrid n hn hnTop
  · calc
      _ ≤ Real.log (Real.log ((max 2 (n - 1) : ℕ) : ℝ)) + (0.261497 : ℝ) +
          (if (8.9 : ℝ) < Real.log (n : ℝ) then (1.614e-3 : ℝ) else 1) :=
        upperGrid n hn hnTop
      _ ≤ _ := add_le_add (add_le_add hLogLogLeft hC.1) hAllowance
