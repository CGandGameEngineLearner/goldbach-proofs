import Mathlib
import Conjectures.Goldbach.EstermannAlmostAllPolylog

/-!
Almost-all Goldbach on multiples of six.

The analytic input is the accepted module `Conjectures.Goldbach.EstermannAlmostAllPolylog`
(adapted from it: its `Cover.exc_polylog`): for every `A > 0` the number of even integers
`4 ≤ n ≤ X` with no two-prime representation is eventually at most `X (log X)^(-A)`.

Every multiple of six is even and at least four, and the representation count used in the
target statement is literally `Cover.myreps`.  Hence the set of multiples of six in `(X/2, X]`
without a prime pair is a subset of `Cover.exc X`, and one extra logarithm in the exponent
pays for the constant `1/2` on the right-hand side.
-/

namespace Conjectures.Cuts.Task4acd3c8c41d8e044f6b1f87f_aux

open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.Cover

def mine (X : ℕ) : Finset ℕ :=
  (Finset.Ioc (X / 2) X).filter
    (fun m => (6 : ℕ) ∣ m ∧ ((Finset.range (m + 1)).filter
      (fun p => Nat.Prime p ∧ Nat.Prime (m - p))).card = 0)

theorem mine_subset_exc (X : ℕ) : mine X ⊆ exc X := by
  intro m hm
  have hm' := Finset.mem_filter.mp hm
  have hIoc := Finset.mem_Ioc.mp hm'.1
  have hcard : (myreps m).card = 0 := hm'.2.2
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_, ?_, hcard⟩
  · have hpos : 0 < m := by omega
    obtain ⟨k, hk⟩ := hm'.2.1
    omega
  · obtain ⟨k, hk⟩ := hm'.2.1
    exact ⟨3 * k, by omega⟩

theorem card_mine_le (X : ℕ) : ((mine X).card : ℝ) ≤ ((exc X).card : ℝ) := by
  exact_mod_cast Finset.card_le_card (mine_subset_exc X)

theorem two_le_log_of_eight_le {x : ℕ} (hx : 8 ≤ x) : (2 : ℝ) ≤ Real.log (x : ℝ) := by
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have h8 : (8 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlog : Real.log (8 : ℝ) ≤ Real.log (x : ℝ) := Real.log_le_log (by norm_num) h8
  have h8eq : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
  have hl2 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [h8eq, Real.log_pow]
    norm_num
  have hd9 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  linarith

theorem main :
    ∀ (x1 : ℕ), ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 →
      ((mine x3).card : ℝ) * Real.log (x3 : ℝ) ^ x1 ≤ (x3 : ℝ) / 2 := by
  intro x1
  obtain ⟨X₀, hX₀⟩ := exc_polylog ((x1 : ℝ) + 1) (by positivity)
  refine ⟨max X₀ 8, fun x3 hx3 => ?_⟩
  have hX₀le : X₀ ≤ x3 := le_trans (le_max_left _ _) hx3
  have h8 : 8 ≤ x3 := le_trans (le_max_right _ _) hx3
  have hxpos : (0 : ℝ) < (x3 : ℝ) := by positivity
  have hlog2 : (2 : ℝ) ≤ Real.log (x3 : ℝ) := two_le_log_of_eight_le h8
  have hlogpos : (0 : ℝ) < Real.log (x3 : ℝ) := by linarith
  have hexc : ((exc x3).card : ℝ) ≤ (x3 : ℝ) * (Real.log (x3 : ℝ)) ^ (-((x1 : ℝ) + 1)) :=
    hX₀ x3 hX₀le
  have hpow : (0 : ℝ) ≤ Real.log (x3 : ℝ) ^ x1 := by positivity
  have hstep1 : ((mine x3).card : ℝ) * Real.log (x3 : ℝ) ^ x1 ≤
      ((exc x3).card : ℝ) * Real.log (x3 : ℝ) ^ x1 :=
    mul_le_mul_of_nonneg_right (card_mine_le x3) hpow
  have hstep2 : ((exc x3).card : ℝ) * Real.log (x3 : ℝ) ^ x1 ≤
      ((x3 : ℝ) * (Real.log (x3 : ℝ)) ^ (-((x1 : ℝ) + 1))) * Real.log (x3 : ℝ) ^ x1 :=
    mul_le_mul_of_nonneg_right hexc hpow
  have hrpow : Real.log (x3 : ℝ) ^ x1 = (Real.log (x3 : ℝ)) ^ ((x1 : ℝ)) := by
    rw [Real.rpow_natCast]
  have hcomb : (Real.log (x3 : ℝ)) ^ (-((x1 : ℝ) + 1)) * Real.log (x3 : ℝ) ^ x1 =
      (Real.log (x3 : ℝ)) ^ (-(1 : ℝ)) := by
    rw [hrpow, ← Real.rpow_add hlogpos]
    congr 1
    ring
  have hinv : (Real.log (x3 : ℝ)) ^ (-(1 : ℝ)) ≤ (1 : ℝ) / 2 := by
    rw [Real.rpow_neg_one]
    calc (Real.log (x3 : ℝ))⁻¹ = 1 / Real.log (x3 : ℝ) := (one_div _).symm
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hlog2
  have hfinal : ((x3 : ℝ) * (Real.log (x3 : ℝ)) ^ (-((x1 : ℝ) + 1))) *
      Real.log (x3 : ℝ) ^ x1 ≤ (x3 : ℝ) / 2 := by
    have hassoc : ((x3 : ℝ) * (Real.log (x3 : ℝ)) ^ (-((x1 : ℝ) + 1))) *
        Real.log (x3 : ℝ) ^ x1 =
        (x3 : ℝ) * ((Real.log (x3 : ℝ)) ^ (-((x1 : ℝ) + 1)) * Real.log (x3 : ℝ) ^ x1) := by
      ring
    rw [hassoc, hcomb]
    have := mul_le_mul_of_nonneg_left hinv (le_of_lt hxpos)
    linarith [this]
  linarith

end Conjectures.Cuts.Task4acd3c8c41d8e044f6b1f87f_aux

theorem Conjectures.Cuts.Task4acd3c8c41d8e044f6b1f87f :
∀ (x1 : ℕ), ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → ↑{x5 ∈ Finset.Ioc (x3 / (2 : ℕ)) x3 | (6 : ℕ) ∣ x5 ∧ {x6 ∈ Finset.range (x5 + (1 : ℕ)) | Nat.Prime x6 ∧ Nat.Prime (x5 - x6)}.card = (0 : ℕ)}.card * Real.log ↑x3 ^ x1 ≤ ↑x3 / (2 : ℝ) := by
  simpa [Conjectures.Cuts.Task4acd3c8c41d8e044f6b1f87f_aux.mine] using
    Conjectures.Cuts.Task4acd3c8c41d8e044f6b1f87f_aux.main
