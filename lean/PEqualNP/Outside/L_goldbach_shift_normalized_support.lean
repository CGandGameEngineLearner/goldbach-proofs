import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace PEqualNP.Outside

theorem L_goldbach_shift_normalized_support :
    ∀ (n : ℕ) (e η : ℝ) (ω : ℕ → ℝ), 0 < n → 0 < e → 0 < η →
      let W := (Finset.Icc n (2*n)).filter (fun m => Even m ∧ ω m ≠ 0)
      (∑ m ∈ W, ω m) = 1 →
      (∑ m ∈ W, (ω m)^2) * (n:ℝ)^(8/3+η) ≤ ((e/2)*(n:ℝ))^2 →
      4*(n:ℝ)^(2/3+η) ≤ e^2*(W.card:ℝ) := by
  classical
  intro n e η ω hn _he _hη
  let W := (Finset.Icc n (2*n)).filter (fun m => Even m ∧ ω m ≠ 0)
  change (∑ m ∈ W, ω m) = 1 →
    (∑ m ∈ W, (ω m)^2) * (n:ℝ)^(8/3+η) ≤ ((e/2)*(n:ℝ))^2 →
    4*(n:ℝ)^(2/3+η) ≤ e^2*(W.card:ℝ)
  intro hsum hbudget
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcard : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  have hcs : (1 : ℝ) ≤ (W.card : ℝ) * ∑ m ∈ W, (ω m)^2 := by
    simpa [hsum] using
      Finset.sum_mul_sq_le_sq_mul_sq W (fun _ : ℕ => (1 : ℝ)) ω
  have hpow : (n:ℝ)^(8/3+η) = (n:ℝ)^(2/3+η) * (n:ℝ)^2 := by
    rw [show (8/3 : ℝ) + η = (2/3+η) + 2 by ring,
      Real.rpow_add hnR, Real.rpow_two]
  have hbound : (n:ℝ)^(8/3+η) ≤ (W.card:ℝ) * ((e/2)*(n:ℝ))^2 := by
    calc
      (n:ℝ)^(8/3+η) = 1 * (n:ℝ)^(8/3+η) := by rw [one_mul]
      _ ≤ ((W.card:ℝ) * ∑ m ∈ W, (ω m)^2) * (n:ℝ)^(8/3+η) :=
        mul_le_mul_of_nonneg_right hcs (Real.rpow_nonneg hnR.le _)
      _ = (W.card:ℝ) * ((∑ m ∈ W, (ω m)^2) * (n:ℝ)^(8/3+η)) := by ring
      _ ≤ (W.card:ℝ) * ((e/2)*(n:ℝ))^2 :=
        mul_le_mul_of_nonneg_left hbudget hcard
  apply le_of_mul_le_mul_right ?_ (sq_pos_of_pos hnR)
  calc
    (4*(n:ℝ)^(2/3+η)) * (n:ℝ)^2 = 4*(n:ℝ)^(8/3+η) := by rw [hpow]; ring
    _ ≤ 4*((W.card:ℝ) * ((e/2)*(n:ℝ))^2) :=
      mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = (e^2*(W.card:ℝ)) * (n:ℝ)^2 := by ring

end PEqualNP.Outside
