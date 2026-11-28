import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace GoldbachSkirtKernel

open MeasureTheory Set
open scoped Interval

noncomputable def kernel (N t : ℝ) : ℝ :=
  (Real.sin (Real.pi * (N + 1) * t) / Real.sin (Real.pi * t)) ^ 2

private theorem sine_positive {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    0 < Real.sin (Real.pi * t) := by
  apply Real.sin_pos_of_mem_Ioo
  refine ⟨mul_pos Real.pi_pos ht, ?_⟩
  calc
    Real.pi * t < Real.pi * 1 := mul_lt_mul_of_pos_left ht' Real.pi_pos
    _ = Real.pi := mul_one _

private theorem sine_left {x : ℝ} (hx : 3 / 4 ≤ x) (hx' : x ≤ 7 / 8) :
    1 / 4 ≤ |Real.sin (Real.pi * x)| := by
  have h := Real.le_sin_mul (x := 2 * (1 - x)) (by linarith) (by linarith)
  rw [show Real.pi / 2 * (2 * (1 - x)) = Real.pi - Real.pi * x by ring,
    Real.sin_pi_sub] at h
  exact (show (1 : ℝ) / 4 ≤ 2 * (1 - x) by linarith).trans (h.trans (le_abs_self _))

private theorem sine_right {x : ℝ} (hx : 5 / 4 ≤ x) (hx' : x ≤ 11 / 8) :
    1 / 4 ≤ |Real.sin (Real.pi * x)| := by
  have h := Real.le_sin_mul (x := 2 * (x - 1)) (by linarith) (by linarith)
  rw [show Real.pi / 2 * (2 * (x - 1)) = Real.pi * x - Real.pi by ring,
    Real.sin_sub_pi] at h
  exact (show (1 : ℝ) / 4 ≤ 2 * (x - 1) by linarith).trans (h.trans (neg_le_abs _))

private theorem rpow_at_least_two {N : ℝ} (hN : 64 ≤ N) :
    2 ≤ N ^ ((1 : ℝ) / 6) := by
  calc
    (2 : ℝ) = (64 : ℝ) ^ ((1 : ℝ) / 6) := by
      rw [show (64 : ℝ) = (2 : ℝ) ^ 6 by norm_num,
        ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 6]
      norm_num
    _ ≤ _ := Real.rpow_le_rpow (by norm_num) hN (by norm_num)

private theorem integrand_lower {N t : ℝ} (hN : 0 < N + 1)
    (ht : 0 < t) (ht' : t < 1) (hstop : t ≤ 3 / (2 * (N + 1)))
    (hsin : 1 / 4 ≤ |Real.sin (Real.pi * (N + 1) * t)|) :
    ((N + 1) / 24) ^ 2 ≤ kernel N t := by
  have hden := sine_positive ht ht'
  have hup : Real.sin (Real.pi * t) ≤ 6 / (N + 1) := calc
    _ ≤ Real.pi * t := Real.sin_le (by positivity)
    _ ≤ 4 * t := mul_le_mul_of_nonneg_right Real.pi_le_four ht.le
    _ ≤ 4 * (3 / (2 * (N + 1))) := by gcongr
    _ = _ := by field_simp; norm_num
  have hratio : (N + 1) / 24 ≤
      |Real.sin (Real.pi * (N + 1) * t)| / Real.sin (Real.pi * t) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ (N + 1) / 24 * (6 / (N + 1)) := by gcongr
      _ = (1 : ℝ) / 4 := by field_simp; norm_num
      _ ≤ _ := hsin
  have hsq := pow_le_pow_left₀ (show 0 ≤ (N + 1) / 24 by positivity) hratio 2
  simpa only [kernel, div_pow, sq_abs] using hsq

/-- A kernel lower bound valid for any starting point (l) in
([1/(2N),1/N)). -/
theorem lower_for_start (N l : ℝ) (hN : 64 ≤ N)
    (hl : 1 / (2 * N) ≤ l) (hl' : l < 1 / N) :
    N / 2304 ≤ 2 * (∫ t in l..l * N ^ ((1 : ℝ) / 6), kernel N t) := by
  let M := N + 1
  let H := l * N ^ ((1 : ℝ) / 6)
  have hNp : 0 < N := by linarith
  have hM : 0 < M := by dsimp [M]; linarith
  have hlp : 0 < l := (show 0 < 1 / (2 * N) by positivity).trans_le hl
  have h2l : 2 * l ≤ H := by
    dsimp [H]
    rw [mul_comm 2 l]
    exact mul_le_mul_of_nonneg_left (rpow_at_least_two hN) hlp.le
  have hH : l ≤ H := (show l ≤ 2 * l by linarith).trans h2l
  have hHlo : 1 / N ≤ H := calc
    _ = 2 * (1 / (2 * N)) := by field_simp
    _ ≤ 2 * l := by gcongr
    _ ≤ H := h2l
  have hHup : H < 1 := calc
    _ ≤ l * N := by
      apply mul_le_mul_of_nonneg_left _ hlp.le
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (show 1 ≤ N by linarith)
          (show (1 : ℝ) / 6 ≤ 1 by norm_num)
    _ < 1 := by simpa only [one_mul] using (lt_div_iff₀ hNp).mp hl'
  obtain ⟨a, b, hla, hwidth, hbH, hstop, hsin⟩ :
      ∃ a b : ℝ, l ≤ a ∧ b - a = 1 / (8 * M) ∧ b ≤ H ∧
        b ≤ 3 / (2 * M) ∧
        (∀ t ∈ Icc a b, 1 / 4 ≤ |Real.sin (Real.pi * M * t)|) := by
    by_cases hleft : l ≤ 3 / (4 * M)
    · refine ⟨3 / (4 * M), 7 / (8 * M), hleft, ?_, ?_, ?_, ?_⟩
      · field_simp
        ring
      · apply le_trans _ hHlo
        apply (div_le_div_iff₀ (by positivity) hNp).mpr
        dsimp only [M]
        linarith
      · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        linarith
      · intro t ht
        rw [mul_assoc]
        apply sine_left
        · have h := (div_le_iff₀ (show 0 < 4 * M by positivity)).mp ht.1
          linarith
        · have h := (le_div_iff₀ (show 0 < 8 * M by positivity)).mp ht.2
          linarith
    · refine ⟨5 / (4 * M), 11 / (8 * M), hl'.le.trans ?_, ?_, ?_, ?_, ?_⟩
      · apply (div_le_div_iff₀ hNp (by positivity)).mpr
        dsimp only [M]
        linarith
      · field_simp
        ring
      · apply le_trans _ ((mul_le_mul_of_nonneg_left (le_of_not_ge hleft) (by norm_num : (0 : ℝ) ≤ 2)).trans h2l)
        apply (div_le_iff₀ (show 0 < 8 * M by positivity)).mpr
        field_simp
        nlinarith
      · apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        linarith
      · intro t ht
        rw [mul_assoc]
        apply sine_right
        · have h := (div_le_iff₀ (show 0 < 4 * M by positivity)).mp ht.1
          linarith
        · have h := (le_div_iff₀ (show 0 < 8 * M by positivity)).mp ht.2
          linarith
  have hab : a ≤ b := sub_nonneg.mp (hwidth ▸ (show 0 ≤ 1 / (8 * M) by positivity))
  have hcont : ContinuousOn (kernel N) (Icc l H) := by
    unfold kernel
    refine (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => ?_)).pow 2
    exact (sine_positive (hlp.trans_le ht.1) (ht.2.trans_lt hHup)).ne'
  have hfull : IntervalIntegrable (kernel N) volume l H :=
    ContinuousOn.intervalIntegrable_of_Icc hH hcont
  have hpart : IntervalIntegrable (kernel N) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab (hcont.mono (Icc_subset_Icc hla hbH))
  have hsmall : (∫ t in a..b, (M / 24) ^ 2) ≤ ∫ t in a..b, kernel N t := by
    apply intervalIntegral.integral_mono_on hab (intervalIntegrable_const) hpart
    intro t ht
    exact integrand_lower hM (hlp.trans_le (hla.trans ht.1))
      (ht.2.trans_lt (hbH.trans_lt hHup)) (ht.2.trans hstop) (hsin t ht)
  have hlarge : (∫ t in a..b, kernel N t) ≤ ∫ t in l..H, kernel N t :=
    intervalIntegral.integral_mono_interval hla hab hbH
      (Filter.Eventually.of_forall (fun t => sq_nonneg _)) hfull
  change N / 2304 ≤ 2 * (∫ t in l..H, kernel N t)
  calc
    _ ≤ M / 2304 := by dsimp [M]; linarith
    _ = 2 * (∫ t in a..b, (M / 24) ^ 2) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, hwidth]
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hsmall.trans hlarge) (by norm_num)

/-- Uniform lower bound on the frozen denominator band. -/
theorem uniform_mass (N q : ℕ) (hN : 64 ≤ N)
    (hq₁ : (Nat.log 2 (N + 2)) ^ 2 < q)
    (hq₂ : q ≤ 2 * (Nat.log 2 (N + 2)) ^ 2) :
    let lo := (((Nat.log 2 (N + 2)) ^ 2 : ℕ) : ℝ) / ((q : ℝ) * (N : ℝ))
    (N : ℝ) / 2304 ≤
      2 * intervalIntegral
        (fun t : ℝ => (Real.sin (Real.pi * ((N : ℝ) + 1) * t) / Real.sin (Real.pi * t)) ^ 2)
        lo (lo * (N : ℝ) ^ ((1 : ℝ) / 6)) volume := by
  let Q : ℕ := (Nat.log 2 (N + 2)) ^ 2
  change Q < q at hq₁
  change q ≤ 2 * Q at hq₂
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hqp : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq₁R : (Q : ℝ) < q := by exact_mod_cast hq₁
  have hq₂R : (q : ℝ) ≤ 2 * (Q : ℝ) := by exact_mod_cast hq₂
  let l := (Q : ℝ) / ((q : ℝ) * (N : ℝ))
  have hl : 1 / (2 * (N : ℝ)) ≤ l := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hq₂R hNp.le]
  have hl' : l < 1 / (N : ℝ) := by
    apply (div_lt_div_iff₀ (by positivity) hNp).mpr
    nlinarith [mul_lt_mul_of_pos_right hq₁R hNp]
  exact lower_for_start (N : ℝ) l (by exact_mod_cast hN) hl hl'

end GoldbachSkirtKernel

theorem Conjectures.Cuts.Taskcfe270ebb99b1c588e1d1897 : (
  have x1 : ℕ → ℕ := fun (x1 : ℕ) => Nat.log (2 : ℕ) (x1 + (2 : ℕ)) ^ (2 : ℕ); have x2 : ℕ → ℕ → ℝ := fun (x2 x3 : ℕ) =>   have x4 : ℝ := ↑(x1 x2) / (↑x3 * ↑x2);   (2 : ℝ) * ∫ (x5 : ℝ) in x4..x4 * ↑x2 ^ (1 / 6 : ℝ), (Real.sin (Real.pi * (↑x2 + (1 : ℝ)) * x5) / Real.sin (Real.pi * x5)) ^ (2 : ℕ); ∃ (x3 : ℝ), (0 : ℝ) < x3 ∧ ∀ (x4 : ℕ), (64 : ℕ) ≤ x4 → ∀ (x6 : ℕ), x1 x4 < x6 → x6 ≤ (2 : ℕ) * x1 x4 → x3 * ↑x4 ≤ x2 x4 x6
) := by
  refine ⟨(1 : ℝ) / 2304, by norm_num, ?_⟩
  intro N hN q hqLower hqUpper
  simpa only [one_div_mul_eq_div] using GoldbachSkirtKernel.uniform_mass N q hN hqLower hqUpper
