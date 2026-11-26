import Mathlib

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

theorem PEqualNP.Outside.L_goldbach_shift_normalized_support :
    ∀ (n : ℕ) (e η : ℝ) (ω : ℕ → ℝ), 0 < n → 0 < e → 0 < η → let W := (Finset.Icc n (2*n)).filter (fun m => Even m ∧ ω m ≠ 0); (∑ m ∈ W, ω m) = 1 → (∑ m ∈ W, (ω m)^2) * (n:ℝ)^(8/3+η) ≤ ((e/2)*(n:ℝ))^2 → 4*(n:ℝ)^(2/3+η) ≤ e^2*(W.card:ℝ) := by
    intro n e η ω nPositive ePositive etaPositive
    dsimp only
    intro hsum hsquare
    set W : Finset ℕ := (Icc n (2*n)).filter (fun m => Even m ∧ ω m ≠ 0) with hW
    have nonempty : W.Nonempty := by
      rcases W.eq_empty_or_nonempty with empty | ne
      · rw [empty] at hsum
        simp at hsum
      · exact ne
    have cardPositive : (0 : ℝ) < (W.card : ℝ) := by
      have := Finset.card_pos.mpr nonempty
      exact_mod_cast this
    have cauchy : (1 : ℝ) ≤ (W.card : ℝ) * ∑ m ∈ W, (ω m)^2 := by
      have := sq_sum_le_card_mul_sum_sq (s := W) (f := ω)
      rw [hsum] at this
      simpa using this
    have nSquare : (0 : ℝ) < (n : ℝ)^2 := by positivity
    have powerNonnegative : (0 : ℝ) ≤ (n : ℝ)^(2/3+η) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have split : (n : ℝ)^(8/3+η) = (n : ℝ)^(2/3+η) * (n : ℝ)^2 := by
      rw [← Real.rpow_natCast (n:ℝ) 2, ← Real.rpow_add (by positivity : (0:ℝ) < (n:ℝ))]
      congr 1
      push_cast
      ring
    have energyBound : (∑ m ∈ W, (ω m)^2) * (n : ℝ)^(2/3+η) ≤ (e/2)^2 := by
      have h := hsquare
      rw [split] at h
      rw [show ((e:ℝ)/2*(n:ℝ))^2 = (e/2)^2 * (n:ℝ)^2 by ring] at h
      by_contra contra
      push Not at contra
      have multiplied : (e/2)^2 * (n:ℝ)^2 < ((∑ m ∈ W, (ω m)^2) * (n : ℝ)^(2/3+η)) * (n:ℝ)^2 :=
        mul_lt_mul_of_pos_right contra nSquare
      nlinarith [h, multiplied]
    have step : (n : ℝ)^(2/3+η) ≤ (W.card : ℝ) * ((e/2)^2) := by
      calc
        (n : ℝ)^(2/3+η) = 1 * (n : ℝ)^(2/3+η) := by ring
        _ ≤ ((W.card : ℝ) * ∑ m ∈ W, (ω m)^2) * (n : ℝ)^(2/3+η) :=
          mul_le_mul_of_nonneg_right cauchy powerNonnegative
        _ = (W.card : ℝ) * ((∑ m ∈ W, (ω m)^2) * (n : ℝ)^(2/3+η)) := by ring
        _ ≤ (W.card : ℝ) * ((e/2)^2) :=
          mul_le_mul_of_nonneg_left energyBound (le_of_lt cardPositive)
    nlinarith [step]
