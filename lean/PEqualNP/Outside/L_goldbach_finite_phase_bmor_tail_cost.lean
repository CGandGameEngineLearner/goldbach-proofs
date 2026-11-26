import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

/-- Sum the assumed pointwise progression bound over the specified late range. -/
theorem PEqualNP.Outside.L_goldbach_finite_phase_bmor_tail_cost :
    (∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 8000000000 ≤ n → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/(840 * Real.log (n:ℝ))) → let D := fun (q a n : ℕ) => (∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q=a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/(Nat.totient q:ℝ); let J := fun (q a l u : ℕ) (β : ℝ) => 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico l u, |D q a m|); let T : ℕ := 8000000000; ∀ (q a n : ℕ) (β : ℝ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → 4000000000000000000 ≤ n → |β| ≤ 105/((q:ℝ)*n) → |D q a n| + J q a T n β ≤ (n:ℝ)/(840*Real.log n) + 105*Real.pi*n/(840*(q:ℝ)*Real.log T) := by
  intro hBMOR
  dsimp only
  intro q a n β hq hqmax ha hcop hn hβ
  let T : ℕ := 8000000000
  let d (m : ℕ) : ℝ := (∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q),
    ArithmeticFunction.vonMangoldt k) - (m:ℝ)/(Nat.totient q:ℝ)
  have hlogT : 0 < Real.log (T:ℝ) := Real.log_pos (by norm_num [T])
  have hden : 0 < 840 * Real.log (T:ℝ) := by positivity
  have hnT : T ≤ n := by dsimp [T]; omega
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hqpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hHead : |d n| ≤ (n:ℝ)/(840 * Real.log (n:ℝ)) :=
    hBMOR q a n hq hqmax ha hcop hnT
  have hRange (N : ℕ) : (∑ m ∈ Finset.range N, (m:ℝ)) = (N:ℝ)*((N:ℝ)-1)/2 := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have hMass : (∑ m ∈ Finset.Ico T n, (m:ℝ)) ≤ (n:ℝ)^2/2 := by
    calc
      _ ≤ ∑ m ∈ Finset.range n, (m:ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hm).2
        · intro m _ _
          exact Nat.cast_nonneg m
      _ = (n:ℝ)*((n:ℝ)-1)/2 := hRange n
      _ ≤ _ := by nlinarith only [hnpos]
  have hTail : (∑ m ∈ Finset.Ico T n, |d m|) ≤ ((n:ℝ)^2/2)/(840*Real.log (T:ℝ)) := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico T n, (m:ℝ)/(840*Real.log (T:ℝ)) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmT := (Finset.mem_Ico.mp hm).1
        have hlog : Real.log (T:ℝ) ≤ Real.log (m:ℝ) :=
          Real.log_le_log (by norm_num [T]) (by exact_mod_cast hmT)
        exact (hBMOR q a m hq hqmax ha hcop hmT).trans
          (div_le_div_of_nonneg_left (Nat.cast_nonneg m) hden
            (mul_le_mul_of_nonneg_left hlog (by norm_num)))
      _ = (∑ m ∈ Finset.Ico T n, (m:ℝ))/(840*Real.log (T:ℝ)) := by simp only [div_eq_mul_inv, Finset.sum_mul]
      _ ≤ _ := div_le_div_of_nonneg_right hMass hden.le
  have hβ' : 2 * Real.pi * |β| ≤ 2 * Real.pi * (105 / ((q:ℝ) * (n:ℝ))) :=
    mul_le_mul_of_nonneg_left hβ (by positivity)
  have hCost : 2 * Real.pi * |β| * (∑ m ∈ Finset.Ico T n, |d m|) ≤
      105 * Real.pi * (n:ℝ) / (840 * (q:ℝ) * Real.log (T:ℝ)) := by
    calc
      _ ≤ (2 * Real.pi * ((105:ℝ) / ((q:ℝ) * (n:ℝ)))) * (((n:ℝ)^2/2)/(840*Real.log (T:ℝ))) :=
        mul_le_mul hβ' hTail (Finset.sum_nonneg (fun m _ => abs_nonneg (d m))) (by positivity)
      _ = _ := by field_simp [hqpos.ne', hnpos.ne', hlogT.ne'] <;> ring
  exact add_le_add hHead hCost
