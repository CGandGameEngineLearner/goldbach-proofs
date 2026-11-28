import PolynomialZeroFreeBox
import PolynomialConductorDensity
import PintzConductorClasses
import Conjectures.Goldbach.ThreeQuartersModelSqrtExceptions

open Finset Filter OAI.Ostmann
namespace Goldbach.PintzClasses
noncomputable section
open scoped Classical

/-- Multiples of a large primitive conductor supporting an actual near-one
zero. Taking h=6 covers the arithmetic divisibility r ∣ 6m. -/
def divisorHits (X h : ℕ) (θ σ T : ℝ) (F : Finset PrimitiveComplexCharacter) : Finset ℕ :=
  (Icc 1 (2*X)).filter (fun m => ∃ χ ∈ F, 0 < (V1 χ).count σ T ∧
    (X:ℝ)^θ ≤ (χ.modulus:ℝ) ∧ χ.modulus ∣ h*m)

theorem divisorHits_le {X h : ℕ} (hX : 0 < X) (hh : 0 < h) (θ σ T : ℝ)
    (F : Finset PrimitiveComplexCharacter) :
    ((divisorHits X h θ σ T F).card:ℝ) ≤
      (∑ χ ∈ F, ((V1 χ).count σ T : ℝ)) * (2*h*(X:ℝ)^(1-θ)) := by
  let active := F.filter (fun χ => 0 < (V1 χ).count σ T ∧ (X:ℝ)^θ ≤ (χ.modulus:ℝ))
  let row (χ : PrimitiveComplexCharacter) := (Icc 1 (2*X)).filter (fun m => χ.modulus ∣ h*m)
  have hs : divisorHits X h θ σ T F ⊆ active.biUnion row := by
    intro m hm
    obtain ⟨hi,χ,hχ,hz,hr,hd⟩ := mem_filter.mp hm
    exact mem_biUnion.mpr ⟨χ,mem_filter.mpr ⟨hχ,hz,hr⟩,mem_filter.mpr ⟨hi,hd⟩⟩
  have hx : 0 < (X:ℝ) := by exact_mod_cast hX
  have hr (χ : PrimitiveComplexCharacter) (hc : χ ∈ active) :
      ((row χ).card:ℝ) ≤ 2*h*(X:ℝ)^(1-θ) := by
    have hm := scaled_multiples (2*X) χ.modulus h hh
    have hm' : ((row χ).card:ℝ)*(χ.modulus:ℝ) ≤ (2*(X:ℝ))*h := by exact_mod_cast hm
    apply le_of_mul_le_mul_right (a := (X:ℝ)^θ) _ (Real.rpow_pos_of_pos hx _)
    calc
      _ ≤ ((row χ).card:ℝ)*(χ.modulus:ℝ) := mul_le_mul_of_nonneg_left (mem_filter.mp hc).2.2 (by positivity)
      _ ≤ _ := hm'
      _ = (2 * (h:ℝ)) * ((X:ℝ)^(1-θ) * (X:ℝ)^θ) := by
        rw [← Real.rpow_add hx, sub_add_cancel, Real.rpow_one]; ring
      _ = _ := by ring
  have hcard : active.card ≤ ∑ χ ∈ F, (V1 χ).count σ T := by
    calc
      _ = ∑ _χ ∈ active, 1 := by simp
      _ ≤ ∑ χ ∈ active, (V1 χ).count σ T := sum_le_sum fun χ hχ => (mem_filter.mp hχ).2.1
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => Nat.zero_le _)
  have h' := (card_le_card hs).trans card_biUnion_le
  calc
    _ ≤ ∑ χ ∈ active, ((row χ).card:ℝ) := by exact_mod_cast h'
    _ ≤ ∑ _χ ∈ active, (2*h*(X:ℝ)^(1-θ)) := sum_le_sum hr
    _ = (active.card:ℝ)*(2*h*(X:ℝ)^(1-θ)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-- In polynomial conductor and height ranges, all sufficiently large
individual resonant conductor divisibilities have power-saving count, uniformly
in the chosen finite family. The bound accounts for the growing number of
characters by the actual count of near-one zeros. -/
theorem large_resonant_conductor_saving {d τ K θ ε : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ τ)
    (hK : 0 ≤ K) (hε : 0 < ε) (h : ℕ) (hh : 0 < h) :
    ∀ᶠ X : ℕ in atTop, ∀ (Q : ℕ) (T : ℝ) (F : Finset PrimitiveComplexCharacter),
      1 ≤ Q → 2 ≤ T → (Q:ℝ) ≤ (X:ℝ)^d → T ≤ (X:ℝ)^τ → (∀ χ ∈ F, χ.modulus ≤ Q) →
      ((divisorHits X h θ (1-K/Real.log X) T F).card:ℝ) ≤ (X:ℝ)^(1-θ+ε) := by
  obtain ⟨C,hC,hcount⟩ := polynomial_conductor_near_one
  let B := C*(Real.exp (3*(2*d+τ)*K)*(d+τ)^13)*(2*h)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop (2*K)
  filter_upwards [hlog,GB6Growth.polylog_le_power B hB 13 ε hε,eventually_ge_atTop (2:ℕ)] with X hL habs hX
  intro Q T F hQ hT hqX hTX hF
  have hx : 1 < (X:ℝ) := by exact_mod_cast (show 1<X by omega)
  have hx' : 0 < (X:ℝ) := by linarith
  have hfreq := divisorHits_le (show 0<X by omega) hh θ (1-K/Real.log X) T F
  have hz := hcount X d τ K T Q hx hd ht hK hL hQ hT hqX hTX F hF
  have hlog' : Real.log (X:ℝ) ≤ GB6Growth.logFactor X := by
    unfold GB6Growth.logFactor
    have h := Real.log_le_log hx' (show (X:ℝ) ≤ X+2 by linarith)
    linarith [GB6Growth.L_one X]
  have hsmall : B*(Real.log (X:ℝ))^13 ≤ (X:ℝ)^ε :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.log_nonneg hx.le) hlog' _) hB).trans habs
  calc
    _ ≤ _ := hfreq
    _ ≤ _ := mul_le_mul_of_nonneg_right hz (show 0 ≤ 2*(h:ℝ)*(X:ℝ)^(1-θ) by positivity)
    _ = (X:ℝ)^(1-θ)*(B*(Real.log (X:ℝ))^13) := by dsimp [B]; ring
    _ ≤ (X:ℝ)^(1-θ)*(X:ℝ)^ε := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = _ := (Real.rpow_add hx' _ _).symm

end
end Goldbach.PintzClasses
#print axioms Goldbach.PintzClasses.large_resonant_conductor_saving


open Finset Filter OAI.Ostmann
namespace Goldbach.PintzClasses
noncomputable section
open scoped Classical

/-- All multiples of the conductor of any primitive character with an actual
near-one low zero; no conductor lower cutoff is imposed in the definition. -/
def lowHits (X h : ℕ) (σ T : ℝ) (F : Finset PrimitiveComplexCharacter) :=
  (Icc 1 (2*X)).filter (fun m => ∃ χ ∈ F, 0 < (V1 χ).count σ T ∧ χ.modulus ∣ h*m)

/-- A fixed positive power saving for all the low-height single-conductor
incidences. Uniform over finite families up to any fixed polynomial conductor
cutoff. The lower cutoff for active conductors follows from actual zero freeness. -/
theorem low_height_incidence_saving (K : ℝ) (hK : 0 < K) (d : ℝ) (hd : 0 ≤ d)
    (h : ℕ) (hh : 0 < h) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (Q : ℕ) (T : ℝ) (F : Finset PrimitiveComplexCharacter),
      1 ≤ Q → 2 ≤ T → (Q:ℝ) ≤ (X:ℝ)^d → T ≤ (X:ℝ)^δ → (∀ χ ∈ F, χ.modulus ≤ Q) →
      ((lowHits X h (1-K/Real.log X) T F).card:ℝ) ≤ (X:ℝ)^(1-δ/2) := by
  obtain ⟨δ,hδ,hzero⟩ := polynomial_box_zero_count K hK
  refine ⟨δ,hδ,?_⟩
  have habs := large_resonant_conductor_saving (θ:=δ) hd hδ.le hK.le (show 0 < δ/2 by positivity) h hh
  filter_upwards [habs,eventually_ge_atTop (2:ℕ)] with X hcount hX
  intro Q T F hQ hT hqX htX hF
  have hx : 1 < (X:ℝ) := by exact_mod_cast (show 1<X by omega)
  have sub : lowHits X h (1-K/Real.log X) T F ⊆ divisorHits X h δ (1-K/Real.log X) T F := by
    intro m hm
    obtain ⟨hm',χ,hχ,hz,hmul⟩ := mem_filter.mp hm
    have hq : (X:ℝ)^δ ≤ (χ.modulus:ℝ) := by
      by_contra! hlt
      have hnot := hzero X T χ hx hT hlt.le htX
      rw [hnot] at hz
      exact lt_irrefl _ hz
    exact mem_filter.mpr ⟨hm',χ,hχ,hz,hq,hmul⟩
  have hb := hcount Q T F hQ hT hqX htX hF
  rw [show 1-δ+δ/2 = 1-δ/2 by ring] at hb
  exact (show ((lowHits X h (1-K/Real.log X) T F).card:ℝ) ≤ _ by exact_mod_cast card_le_card sub).trans hb

end
end Goldbach.PintzClasses
#print axioms Goldbach.PintzClasses.low_height_incidence_saving


open Finset Filter OAI.Ostmann
namespace Goldbach.PintzClasses
noncomputable section
open scoped Classical

/-- Count every scale in [1,2X] for any frequency selected by the conductor
divisibility criterion. Interior scales and even frequencies form a subset. -/
def resonantPairs (X h : ℕ) (θ σ T : ℝ) (F : Finset PrimitiveComplexCharacter) :=
  (divisorHits X h θ σ T F) ×ˢ Icc 1 (2*X)

/-- Large-conductor resonances alone have a dyadic pair exponent below 9/5
as soon as the conductor exceeds X^θ with θ>1/5. -/
theorem resonant_pair_budget {d τ K θ : ℝ} (hd : 0 ≤ d) (ht : 0 ≤ τ)
    (hK : 0 ≤ K) (hθ : 1/5 < θ) (h : ℕ) (hh : 0 < h) :
    ∃ α : ℝ, α < 4/5 ∧ ∀ᶠ X : ℕ in atTop,
      ∀ (Q : ℕ) (T : ℝ) (F : Finset PrimitiveComplexCharacter),
      1 ≤ Q → 2 ≤ T → (Q:ℝ) ≤ (X:ℝ)^d → T ≤ (X:ℝ)^τ → (∀ χ ∈ F, χ.modulus ≤ Q) →
      ((resonantPairs X h θ (1-K/Real.log X) T F).card:ℝ) ≤ 2*(X:ℝ)^(1+α) := by
  let ε := (θ-1/5)/2
  have he : 0 < ε := by dsimp [ε]; linarith
  refine ⟨1-θ+ε,by dsimp [ε]; linarith,?_⟩
  filter_upwards [large_resonant_conductor_saving (θ:=θ) hd ht hK he h hh,
    eventually_ge_atTop (1:ℕ)] with X hX hx
  intro Q T F hq hT hqX hTX hF
  have hp := hX Q T F hq hT hqX hTX hF
  have hr : 0 < (X:ℝ) := by exact_mod_cast hx
  simp only [resonantPairs, card_product, Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ ≤ (X:ℝ)^(1-θ+ε)*(2*X) := mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 2 * ((X:ℝ)^(1:ℝ)*(X:ℝ)^(1-θ+ε)) := by rw [Real.rpow_one]; ring
    _ = _ := by rw [←Real.rpow_add hr]

end
end Goldbach.PintzClasses
#print axioms Goldbach.PintzClasses.resonant_pair_budget
