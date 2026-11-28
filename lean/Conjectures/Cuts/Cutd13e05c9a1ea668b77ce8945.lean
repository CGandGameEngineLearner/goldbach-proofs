import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

-- child 1 zh: 在高度至少一百时，建立 Rosser 的重数加权闭端点零点计数界。
-- child 1 en: Prove the Rosser estimate for the multiplicity-weighted inclusive zero count at heights at least one hundred.
-- child 2 zh: 用低零点证书把三至一百的计数误差控制在一以内。
-- child 2 en: Use low-zero certificates to localize the count within one of its main term from heights three to one hundred.

theorem Conjectures.Cuts.Cutd13e05c9a1ea668b77ce8945
    (hHigh : ∀ T : ℝ, 100 ≤ T → |(∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0) - (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
        0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588)
    (hLow : ∀ T : ℝ, 3 ≤ T → T ≤ 100 → |(∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0) - (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| ≤ 1) :
    (∀ T : ℝ, 3 ≤ T → ∃ Z : Finset ℂ, (∀ s : ℂ, s ∈ Z ↔ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧ s.im ≤ T ∧ riemannZeta s = 0) ∧ |((∑ ρ ∈ Z, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) - ((T / (2 * Real.pi)) * Real.log (T / (2 * Real.pi * Real.exp 1)) + 7 / 8)| ≤ 0.2 * Real.log T + 5) := by
  classical
  have criticalStrip {z : ℂ} (hi : 0 < z.im) (hz : riemannZeta z = 0) :
      0 < z.re ∧ z.re < 1 := by
    constructor
    · by_contra! h
      obtain ⟨n, rfl⟩ := (riemannZeta_eq_zero_iff_of_re_nonpos h).mp hz
      simp at hi
    · exact lt_of_not_ge (fun h => riemannZeta_ne_zero_of_one_le_re h hz)

  have count_bridge (T : ℝ) :
      ∃ Z : Finset ℂ, (∀ s : ℂ, s ∈ Z ↔ 0 < s.re ∧ s.re < 1 ∧ 0 < s.im ∧
          s.im ≤ T ∧ riemannZeta s = 0) ∧
        ((∑ ρ ∈ Z, analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ) =
          ∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then
            ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0 := by
    classical
    let s : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im ≤ T ∧ riemannZeta z = 0}
    have hfinite : s.Finite := by
      apply ((isCompact_closedBall (0 : ℂ) (1 + T)).inter_riemannZetaZeros_finite).subset
      intro z hz
      obtain ⟨ha, hb, hc, hd, he⟩ := hz
      refine ⟨?_, he⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      calc
        ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ _ := by rw [abs_of_pos ha, abs_of_pos hc]; linarith
    refine ⟨hfinite.toFinset, fun _ => Set.Finite.mem_toFinset _, ?_⟩
    rw [tsum_eq_sum (s := hfinite.toFinset)]
    · push_cast
      apply Finset.sum_congr rfl
      intro z hz
      obtain ⟨_, _, hc, hd, _⟩ := hfinite.mem_toFinset.mp hz
      rw [ite_eq_left ⟨hc,hd⟩]
      rfl
    · intro z hz
      by_cases hi : 0 < z.im ∧ z.im ≤ T
      · rw [ite_eq_left hi]
        have hne : riemannZeta z ≠ 0 := by
          intro h
          exact hz (hfinite.mem_toFinset.mpr ⟨(criticalStrip hi.1 h).1,
            (criticalStrip hi.1 h).2, hi.1, hi.2, h⟩)
        rw [analyticOrderAt_eq_zero.mpr (Or.inr hne)]
        simp
      · simp [hi]

  have rosser_envelope (T : ℝ) (hT : 3 ≤ T) :
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 ≤
        0.2 * Real.log T + 5 := by
    have hL : 0 < Real.log T := Real.log_pos (by linarith)
    have h := Real.log_le_sub_one_of_pos (show 0 < Real.log T / 8 by positivity)
    rw [Real.log_div hL.ne' (by norm_num)] at h
    have h8 : Real.log 8 ≤ 3 := by
      rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

  have main_term (T : ℝ) (hT : 0 < T) :
      T / (2 * Real.pi) * Real.log (T / (2 * Real.pi * Real.exp 1)) + 7 / 8 =
        T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8 := by
    rw [← div_div T (2 * Real.pi) (Real.exp 1), Real.log_div (by positivity : T / (2 * Real.pi) ≠ 0) (Real.exp_ne_zero _), Real.log_exp]
    ring

  intro T hT
  obtain ⟨Z, hZ, hcard⟩ := count_bridge T
  refine ⟨Z, hZ, ?_⟩
  rw [hcard, main_term T (by linarith)]
  by_cases h100 : 100 ≤ T
  · exact (hHigh T h100).le.trans (rosser_envelope T hT)
  · apply (hLow T hT (le_of_not_ge h100)).trans
    have hlog := Real.log_pos (show 1 < T by linarith)
    linarith
