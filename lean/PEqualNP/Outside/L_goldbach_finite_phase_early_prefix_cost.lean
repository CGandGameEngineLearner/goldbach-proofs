import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

namespace GoldbachEarlyPrefix

private theorem log_cutoff_lt : Real.log (8000000000 : ℝ) < 24 := by
  calc
    Real.log (8000000000 : ℝ) ≤ Real.log ((2 : ℝ) ^ 33) :=
      Real.log_le_log (by norm_num) (by norm_num)
    _ = 33 * Real.log 2 := by rw [Real.log_pow]; norm_num
    _ < 24 := by linarith only [Real.log_two_lt_d9]

private theorem mangoldt_prefix_abs_le (q a m : ℕ) (hq : 0 < q) (hm : m < 8000000000) :
    |(∑ k ∈ (Finset.range (m+1)).filter (fun k => k % q = a % q),
        ArithmeticFunction.vonMangoldt k) - (m : ℝ) / (Nat.totient q : ℝ)| ≤ 25 * (m : ℝ) := by
  have htotal (u : ℕ) (hu : u < 8000000000) :
      (∑ k ∈ Finset.range (u+1), ArithmeticFunction.vonMangoldt k) ≤ 24 * (u : ℝ) := by
    induction u with
    | zero => simp
    | succ u ih =>
      have hprev := ih (by omega)
      have hpos : 0 < ((u + 1 : ℕ) : ℝ) := by positivity
      have hcut : ((u + 1 : ℕ) : ℝ) ≤ 8000000000 := by exact_mod_cast hu.le
      have hterm := (ArithmeticFunction.vonMangoldt_le_log (n := u + 1)).trans
        ((Real.log_le_log hpos hcut).trans log_cutoff_lt.le)
      rw [Finset.sum_range_succ]
      push_cast at hterm ⊢
      linarith
  let I := (Finset.range (m+1)).filter (fun k => k % q = a % q)
  have hnon : 0 ≤ ∑ k ∈ I, ArithmeticFunction.vonMangoldt k :=
    Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hupper : (∑ k ∈ I, ArithmeticFunction.vonMangoldt k) ≤ 24 * (m : ℝ) :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)).trans (htotal m hm)
  have hphi : (1 : ℝ) ≤ Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hm' : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hmain : (m : ℝ) / Nat.totient q ≤ m := div_le_self hm' hphi
  have hmain₀ : (0 : ℝ) ≤ (m : ℝ) / Nat.totient q := by positivity
  change |(∑ k ∈ I, ArithmeticFunction.vonMangoldt k) - (m : ℝ) / Nat.totient q| ≤ _
  exact abs_le.mpr ⟨by linarith only [hnon, hmain, hm'],
    by linarith only [hupper, hmain₀, hm']⟩

end GoldbachEarlyPrefix

/-- The part of the phase error below the explicit progression theorem's threshold. -/
theorem PEqualNP.Outside.L_goldbach_finite_phase_early_prefix_cost :
    let D := fun (q a n : ℕ) =>
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = a % q),
        ArithmeticFunction.vonMangoldt k) - (n : ℝ) / (Nat.totient q : ℝ)
    let J := fun (q a l u : ℕ) (β : ℝ) =>
      2 * Real.pi * |β| * (∑ m ∈ Finset.Ico l u, |D q a m|)
    let T : ℕ := 8000000000
    ∀ (q a n : ℕ) (β : ℝ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q →
      4000000000000000000 ≤ n → |β| ≤ 105 / ((q : ℝ) * n) →
      J q a 0 T β ≤ (n : ℝ) / 10 ^ 12 := by
  intro D J T q a n β hq _ _ _ hn hβ
  have hprefix : (∑ m ∈ Finset.Ico 0 T, |D q a m|) ≤ (T : ℝ) * (25 * T) := by
    calc
      _ ≤ ∑ m ∈ Finset.Ico 0 T, (25 : ℝ) * T := by
        apply Finset.sum_le_sum
        intro m hm
        have hmT := (Finset.mem_Ico.mp hm).2
        exact (GoldbachEarlyPrefix.mangoldt_prefix_abs_le q a m (by omega) hmT).trans
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hmT.le) (by norm_num))
      _ = _ := by simp [nsmul_eq_mul]
  have hn' : (4000000000000000000 : ℝ) ≤ n := by exact_mod_cast hn
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hden : (4000000000000000000 : ℝ) ≤ (q : ℝ) * n :=
    hn'.trans (le_mul_of_one_le_left (Nat.cast_nonneg _) hq')
  have hphase : |β| ≤ (105 : ℝ) / 4000000000000000000 :=
    hβ.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden)
  calc
    J q a 0 T β ≤ (2 * 4) * (105 / 4000000000000000000) * ((T : ℝ) * (25 * T)) := by
      dsimp only [J]
      exact mul_le_mul (mul_le_mul
        (mul_le_mul_of_nonneg_left Real.pi_le_four (by norm_num)) hphase
        (abs_nonneg _) (by norm_num)) hprefix (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (by norm_num)
    _ ≤ (4000000000000000000 : ℝ) / 10 ^ 12 := by norm_num [T]
    _ ≤ _ := div_le_div_of_nonneg_right hn' (by norm_num)
