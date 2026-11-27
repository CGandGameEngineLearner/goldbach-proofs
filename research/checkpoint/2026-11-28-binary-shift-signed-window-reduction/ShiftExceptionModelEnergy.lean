import WideArcEnergyCriterion
import ReflectedArcModel

namespace Goldbach
open scoped Classical
open WideArcCriterion ReflectedArcModel

/-- A uniform charging inequality for the actual prime sum and the reflected
major-arc model at all interior cutoffs of a dyadic block. -/
theorem rare_model_energy :
    ∃ N : ℕ, ∀ X ≥ N, ((rare X).card:ℝ)*(X:ℝ)^3 ≤ 163840 * energy modelCoefficient X :=
  rare_energy modelCoefficient eventual_discrepancy

/-- Exact frozen target conditional on one explicit mean-square estimate. -/
theorem binary_shift_exception_union_of_model_energy
    {α K : ℝ} (ha : 0 ≤ α) (ha' : α < 4/5) (hK : 0 < K)
    (hE : ∃ N : ℕ, ∀ X ≥ N, energy modelCoefficient X ≤ K*(X:ℝ)^(3+α)) :
    let G := fun m : ℕ => ((Finset.range (m+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (m-p))).card
    ∃ X₀ : ℕ, ∀ X ≥ X₀, let L := Nat.log 2 X / 2
      let E := (Finset.Ico X (2*X)).filter (fun n => Even n ∧ 0 < ((Finset.Icc 1 L).filter (fun e => G (n-2^e)=0)).card)
      E.card^5 ≤ X^4 :=
  frozen_of_energy eventual_discrepancy ha ha' hK hE

/-- A uniformly small one-sided error in a preliminary approximation can be
absorbed in the positive model floor before estimating its residual energy. -/
theorem binary_shift_exception_union_of_corrected_energy {T : ℕ → ℕ → ℂ}
    (hT : ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      (modelCoefficient Y m).re - (T Y m).re ≤ (Y:ℝ)/32)
    {α K : ℝ} (ha : 0 ≤ α) (ha' : α < 4/5) (hK : 0 < K)
    (hE : ∃ N : ℕ, ∀ X ≥ N, energy T X ≤ K*(X:ℝ)^(3+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (ShiftWideArc.missed X).card^5 ≤ X^4 := by
  obtain ⟨NT,hT⟩ := hT
  obtain ⟨NF,hF⟩ := eventual_interior_model_floor
  have hg := ((tendsto_rpow_atTop (by norm_num : 0 < (1/24:ℝ))).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 32
  apply frozen_of_energy (M:=T) _ ha ha' hK hE
  apply Filter.eventually_atTop.mp
  filter_upwards [hg,Filter.eventually_ge_atTop (max 1 (max NT NF))] with Y hY hy
  intro m h1 h2 he z hz
  have hp : (0:ℝ)<Y := by exact_mod_cast (show 0<Y by omega)
  have hs : (Y:ℝ)^(23/24:ℝ)*(Y:ℝ)^(1/24:ℝ) = Y := by
    rw [← Real.rpow_add hp]; norm_num
  have hn : 32*‖z‖ ≤ Y := by
    rw [← hs,mul_comm (32:ℝ)]
    exact mul_le_mul hz hY (by norm_num) (by positivity)
  have hf : (Y:ℝ)/8 ≤ (modelCoefficient Y m).re := hF Y (by omega) m h1 h2 he
  have ht := hT Y (by omega) m h1 h2 he
  have hn' := Complex.re_le_norm (T Y m-z)
  rw [Complex.sub_re] at hn'
  linarith [Complex.re_le_norm z]

end Goldbach
