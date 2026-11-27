import ShiftWideArcMultiscale
import Conjectures.Goldbach.ThreeQuartersModelSqrtExceptions
import Conjectures.Goldbach.DeepThreeQuartersExceptionalZeroCriterion

open Filter
namespace Goldbach.MiddleCanonicalModel
noncomputable section
open ShiftWideArc

/-- The signed, corrected principal model at a reduced rational center. The
zero-denominator value makes this an ordinary function of integer indices. -/
def centerValue (Y q a : ℕ) (β : ℝ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    DeepThreeQuarters.rationalModel Y q β -
      GoldbachTwistedMellin.canonicalCorrection Y (a : ZMod q) β

/-- The defining conditions of the intermediate denominator band. -/
def bandCenter (Y : ℕ) (t : ℝ) (q a : ℕ) : Prop :=
  1 ≤ q ∧ (Nat.log 2 (Y+2))^2 < q ∧
    q ≤ min (GB6Growth.grid Y) (⌈(Y:ℝ)^(1/4:ℝ)⌉₊-1) ∧
    a ≤ q ∧ a.Coprime q ∧ |t-(a:ℝ)/q| ≤ (H Y:ℝ)/((q:ℝ)*Y)

private theorem width_le_dirichlet {Y q : ℕ} (hY : 0 < Y) (hq : 0 < q)
    (hH : (H Y : ℝ) ≤ Real.sqrt Y) :
    (H Y : ℝ) / ((q : ℝ)*Y) ≤ 1 / ((q : ℝ)*Real.sqrt Y) := by
  have hn : 0 < (Y : ℝ) := Nat.cast_pos.mpr hY
  have hqr : 0 < (q : ℝ) := Nat.cast_pos.mpr hq
  have hs : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.mpr hn
  apply (div_le_div_iff₀ (mul_pos hqr hn) (mul_pos hqr hs)).mpr
  have h := mul_le_mul_of_nonneg_right hH hs.le
  rw [← sq, Real.sq_sqrt hn.le] at h
  calc
    (H Y : ℝ) * ((q : ℝ)*Real.sqrt Y) = q * ((H Y : ℝ)*Real.sqrt Y) := by ring
    _ ≤ (q : ℝ)*Y := mul_le_mul_of_nonneg_left h hqr.le
    _ = 1*((q : ℝ)*Y) := by ring

/-- The energy estimate uses the project's larger logarithmic factor. -/
theorem logScale_le_logFactor {Y : ℕ} (hY : 0 < Y) :
    GoldbachTwistedMellin.logScale Y ≤ GB6Growth.logFactor Y := by
  have hy : 0 < (Y:ℝ) := Nat.cast_pos.mpr hY
  have h₂ : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)]
  have hYlog := Real.log_le_log hy (show (Y:ℝ) ≤ Y+2 by linarith)
  unfold GoldbachTwistedMellin.logScale GB6Growth.logFactor
  rw [Real.log_mul (by norm_num) hy.ne']
  linarith [GB6Growth.L_one Y]

/-- A single constant works on every original wide window, including every
intermediate window, at every sufficiently large scale. -/
theorem eventual_wide_center_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℕ in atTop, ∀ (q a : ℕ) (t : ℝ),
      1 ≤ q → q ≤ Q Y → a.Coprime q →
      |t-(a:ℝ)/q| ≤ (H Y:ℝ)/((q:ℝ)*Y) →
      ‖S Y t - centerValue Y q a (t-(a:ℝ)/q)‖ ≤
        C*(Y:ℝ)^(49/64:ℝ)*(GoldbachTwistedMellin.logScale Y)^4 := by
  obtain ⟨C,hC,h⟩ := GoldbachTwistedMellin.rational_canonical_model
    (d := (1/128:ℝ)) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [GB6Growth.eventual_geometry,eventually_ge_atTop (64:ℕ)] with Y hg h64
  intro q a t hq hcut hc hclose
  letI : NeZero q := ⟨by omega⟩
  have hgrid : GB6Growth.grid Y = Q Y := GB6Growth.grid_eq_floor Y
  have hheight : GB6Growth.height Y = H Y := by
    simp only [GB6Growth.height,H,hgrid]
  have hgH : Q Y ≤ H Y := by simpa only [hgrid,hheight] using hg.2.1
  have hsep : 2*(H Y)^2 < Y := by simpa only [hheight] using hg.2.2.2.2
  have hH : (H Y : ℝ) ≤ Real.sqrt Y := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast (show (H Y)^2 ≤ Y by omega)
  have hqrt : (q:ℝ) ≤ Real.sqrt Y :=
    (Nat.cast_le.mpr (hcut.trans hgH)).trans hH
  let β := t-(a:ℝ)/q
  have hb : |β| ≤ 1/((q:ℝ)*Real.sqrt Y) :=
    hclose.trans (width_le_dirichlet (by omega) hq hH)
  have he := h Y h64 a q hc hqrt β hb
  rw [show (a:ℝ)/q+β = t by dsimp [β]; ring] at he
  have hs : DeepThreeQuarters.weightedSum Y DeepThreeQuarters.primeWeight t = S Y t := rfl
  rw [hs,show (3/4+2*(1/128) : ℝ) = 49/64 by norm_num] at he
  simp only [centerValue,dif_neg (NeZero.ne q)]
  change ‖S Y t - (DeepThreeQuarters.rationalModel Y q β -
      GoldbachTwistedMellin.canonicalCorrection Y (a : ZMod q) β)‖ ≤ _
  rw [show S Y t - (DeepThreeQuarters.rationalModel Y q β -
      GoldbachTwistedMellin.canonicalCorrection Y (a : ZMod q) β) =
      S Y t - DeepThreeQuarters.rationalModel Y q β +
      GoldbachTwistedMellin.canonicalCorrection Y (a : ZMod q) β by abel]
  exact he

/-- The explicit estimate holds for any witness of membership in the
denominator band, uniformly in the numerator and point of the window. -/
theorem eventual_band_center_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Y : ℕ in atTop, ∀ (t : ℝ) (q a : ℕ),
      bandCenter Y t q a →
      ‖S Y t - centerValue Y q a (t-(a:ℝ)/q)‖ ≤
        C*(Y:ℝ)^(49/64:ℝ)*(GoldbachTwistedMellin.logScale Y)^4 := by
  obtain ⟨C,hC,h⟩ := eventual_wide_center_bound
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with Y hY
  intro t q a ⟨hq,_,hcut,_,hc,hw⟩
  have hg : q ≤ GB6Growth.grid Y := hcut.trans (min_le_left ..)
  exact hY q a t hq (hg.trans_eq (GB6Growth.grid_eq_floor Y)) hc hw

end
end Goldbach.MiddleCanonicalModel
