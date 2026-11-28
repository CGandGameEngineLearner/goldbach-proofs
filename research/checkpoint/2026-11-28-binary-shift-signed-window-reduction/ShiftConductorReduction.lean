import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Finset Filter
namespace Goldbach.ShiftConductor
noncomputable section
open scoped Classical

def exceptional (m : ℕ) := 4 ≤ m ∧ Even m ∧
  ((range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card = 0

def missed (X : ℕ) := (Ico X (2*X)).filter (fun n => Even n ∧ 0 <
  ((Icc 1 (Nat.log 2 X/2)).filter (fun e =>
    ((range (n-2^e+1)).filter (fun p => p.Prime ∧ (n-2^e-p).Prime)).card = 0)).card)

def shifts (X : ℕ) (s : Finset ℕ) := (s ×ˢ Icc 1 (Nat.log 2 X/2)).image
  (fun me : ℕ × ℕ => me.1+2^me.2)

theorem shift_card (X : ℕ) (s : Finset ℕ) :
    (shifts X s).card ≤ s.card*(Nat.log 2 X/2) := by
  simpa [shifts] using (card_image_le (s := s ×ˢ Icc 1 (Nat.log 2 X/2))
    (f := fun me : ℕ × ℕ => me.1+2^me.2))

/-- Normalize both the dyadic dilation and the logarithmic shift multiplicity.
The factor 1/2 leaves an equal budget for the residual target set. -/
theorem shift_half_budget {α C : ℝ} (hα : α < 4/5) (hC : 0 < C) :
    ∃ N : ℕ, ∀ X ≥ N, ∀ s : Finset ℕ, (s.card:ℝ) ≤ C*(2*(X:ℝ))^α →
    ((shifts X s).card:ℝ) ≤ (X:ℝ)^(4/5:ℝ)/2 := by
  let κ := Real.log 2/(2*C*(2:ℝ)^α)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk : 0 < κ := by dsimp [κ]; positivity
  have hb := (isLittleO_log_rpow_atTop (sub_pos.mpr hα)).bound hk
  obtain ⟨Z,hZ⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hb)
  refine ⟨max 2 Z,?_⟩
  intro X hx s hs
  have hx1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hxp : 0 < (X:ℝ) := by linarith
  have h := hZ X ((le_max_right ..).trans hx)
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg hxp.le _)] at h
  have hL : ((Nat.log 2 X/2:ℕ):ℝ) ≤ Real.log X/Real.log 2 :=
    (Nat.cast_le.mpr (Nat.div_le_self ..)).trans (by simpa [Real.logb] using Real.natLog_le_logb X 2)
  calc
    _ ≤ (s.card:ℝ)*((Nat.log 2 X/2:ℕ):ℝ) := by exact_mod_cast shift_card X s
    _ ≤ (C*(2*(X:ℝ))^α)*(κ*(X:ℝ)^(4/5-α:ℝ)/Real.log 2) :=
      mul_le_mul hs (hL.trans (div_le_div_of_nonneg_right h hlog.le)) (by positivity) (by positivity)
    _ = (X:ℝ)^α*(X:ℝ)^(4/5-α:ℝ)/2 := by
      dsimp [κ]; rw [Real.mul_rpow (by norm_num) hxp.le]; field_simp
    _ = _ := by rw [← Real.rpow_add hxp]; ring_nf

theorem uncovered_shift {X n : ℕ} (hX : 8 ≤ X) (s : Finset ℕ) (hn : n ∈ missed X \ shifts X s) :
    ∃ e ∈ Icc 1 (Nat.log 2 X/2), let m := n-2^e
      X/2 ≤ m ∧ m ≤ 2*X ∧ exceptional m ∧ m ∉ s := by
  obtain ⟨hmiss,hout⟩ := mem_sdiff.mp hn
  obtain ⟨hr,heven,hpos⟩ := mem_filter.mp hmiss
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp hr
  obtain ⟨e,he⟩ := card_pos.mp hpos
  obtain ⟨hei,hzero⟩ := mem_filter.mp he
  obtain ⟨he1,he2⟩ := mem_Icc.mp hei
  have hl : 2 ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by decide) (by omega)
  have hp : 2^e * 2 ≤ X := by
    rw [← pow_succ]; exact (Nat.le_log_iff_pow_le (by decide) (by omega)).mp (by omega)
  have hpe : Even (2^e:ℕ) := Even.pow_of_ne_zero (by decide : Even 2) (by omega)
  refine ⟨e,hei,by omega,by omega,⟨by omega,(Nat.even_sub (by omega)).mpr ⟨fun _ => hpe,fun _ => heven⟩,hzero⟩,?_⟩
  intro hs
  exact hout (mem_image.mpr ⟨(n-2^e,e),mem_product.mpr ⟨hs,hei⟩,by dsimp; omega⟩)

theorem close_from_residual {X : ℕ} (s : Finset ℕ)
    (hc : ((shifts X s).card:ℝ) ≤ (X:ℝ)^(4/5:ℝ)/2)
    (hr : ((missed X \ shifts X s).card:ℝ) ≤ (X:ℝ)^(4/5:ℝ)/2) :
    (missed X).card^5 ≤ X^4 := by
  have hh := card_sdiff_add_card_inter (missed X) (shifts X s)
  have hi : ((missed X ∩ shifts X s).card:ℝ) ≤ ((shifts X s).card:ℝ) := by
    exact_mod_cast card_le_card (inter_subset_right (s₁ := missed X) (s₂ := shifts X s))
  have hw : ((missed X).card:ℝ) ≤ (X:ℝ)^(4/5:ℝ) := by
    rw [← hh, Nat.cast_add]; linarith
  have h5 := pow_le_pow_left₀ (by positivity) hw 5
  rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ (X:ℝ))] at h5
  norm_num at h5
  exact_mod_cast h5
end
end Goldbach.ShiftConductor
