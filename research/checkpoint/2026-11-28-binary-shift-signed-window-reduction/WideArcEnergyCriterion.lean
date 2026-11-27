import ShiftWideArcMultiscale
import ShiftConductorReduction

open Finset
namespace Goldbach.WideArcCriterion
open Goldbach.ShiftWideArc
noncomputable section
open scoped Classical

def rare (X : ℕ) := (Icc (X/2) (2*X)).filter
  (fun m => Even m ∧ noPair m ∧ m ∉ frequent X)

def energy (M : ℕ → ℕ → ℂ) (X : ℕ) :=
  ∑ m ∈ Icc (X/2) (2*X), ∑ Y ∈ interiorScales m,
    ‖M Y m - coefficient (arcs Y) Y m‖^2

/-- On the rare frequencies, linearly many interior cutoffs each charge a
quadratic model error. The scale X and its frequency m remain independent. -/
theorem rare_energy (M : ℕ → ℕ → ℂ)
    (hM : ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      ∀ z : ℂ, ‖z‖ ≤ (Y:ℝ)^(23/24:ℝ) → (Y:ℝ)/16 ≤ ‖M Y m-z‖) :
    ∃ N : ℕ, ∀ X ≥ N, ((rare X).card:ℝ)*(X:ℝ)^3 ≤ 163840 * energy M X := by
  classical
  obtain ⟨N,hN⟩ := hM
  refine ⟨max 512 (4*N),?_⟩
  intro X hx
  let e (m Y : ℕ) := ‖M Y m - coefficient (arcs Y) Y m‖^2
  let row (m : ℕ) := ∑ Y ∈ interiorScales m, e m Y
  have hrow (m : ℕ) (hm : m ∈ rare X) : (X:ℝ)^3 ≤ 163840 * row m := by
    obtain ⟨hi,he,hp,hf⟩ := mem_filter.mp hm
    obtain ⟨h1,h2⟩ := mem_Icc.mp hi
    let s := (interiorScales m).filter (fun Y => ‖coefficient (arcs Y) Y m‖ < (Y:ℝ)^(23/24:ℝ))
    have hc : (X:ℝ) ≤ 40*(s.card:ℝ) := by
      exact_mod_cast many_small_coefficients (show 512 ≤ X by omega) hi hp hf
    have hr (Y : ℕ) (hy : Y ∈ s) : ((X:ℝ)/64)^2 ≤ e m Y := by
      obtain ⟨hint,hs⟩ := mem_filter.mp hy
      obtain ⟨hlo,hhi⟩ := mem_Icc.mp hint
      have hd := hN Y (by omega) m (by omega) (by omega) he _ hs.le
      apply pow_le_pow_left₀ (by positivity)
      have hxy : (X:ℝ) ≤ 4*Y := by exact_mod_cast (show X ≤ 4*Y by omega)
      linarith
    have hsum : (s.card:ℝ)*((X:ℝ)/64)^2 ≤ row m := by
      calc
        _ = ∑ _Y ∈ s, ((X:ℝ)/64)^2 := by simp
        _ ≤ ∑ Y ∈ s, e m Y := sum_le_sum hr
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; exact sq_nonneg _)
    have hmul := mul_le_mul_of_nonneg_right hc (sq_nonneg ((X:ℝ)/64))
    linarith only [show (X:ℝ)*((X:ℝ)/64)^2 ≤ 40*(row m) by linarith only [hmul,hsum]]
  calc
    _ = ∑ _m ∈ rare X, (X:ℝ)^3 := by simp
    _ ≤ ∑ m ∈ rare X, 163840 * row m := sum_le_sum hrow
    _ = 163840 * (∑ m ∈ rare X, row m) := by rw [mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact sum_le_sum_of_subset_of_nonneg (filter_subset ..)
        (fun m _ _ => sum_nonneg fun Y _ => sq_nonneg _)

theorem cover (X : ℕ) (hX : 8 ≤ X) : missed X ⊆ covered X ∪ ShiftConductor.shifts X (rare X) := by
  intro n hn
  by_cases hv : n ∈ covered X
  · exact mem_union_left _ hv
  · apply mem_union_right
    have hout : n ∉ ShiftConductor.shifts X (frequent X) := hv
    obtain ⟨e,hei,hl,hh,hex,hf⟩ :=
      ShiftConductor.uncovered_shift hX (frequent X) (mem_sdiff.mpr ⟨hn,hout⟩)
    obtain ⟨h4,he,hp⟩ := hex
    have hm : n-2^e ∈ rare X := mem_filter.mpr ⟨mem_Icc.mpr ⟨hl,hh⟩,he,(noPair_iff _).mpr hp,hf⟩
    obtain ⟨hI,hEven,hpos⟩ := mem_filter.mp hn
    have hlog : 2 ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by decide) (by omega)
    have hr := (mem_Icc.mp hei).2
    have hpow : 2^e ≤ X := (Nat.le_log_iff_pow_le (by decide) (by omega)).mp (by omega)
    exact mem_image.mpr ⟨(n-2^e,e),mem_product.mpr ⟨hm,hei⟩,by dsimp; have := (mem_Ico.mp hI).1; omega⟩

/-- An averaged error budget with any exponent strictly below 3+4/5 is
sufficient. The estimate is over frequencies and interior truncations. -/
theorem frozen_of_energy {M : ℕ → ℕ → ℂ}
    (hM : ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      ∀ z : ℂ, ‖z‖ ≤ (Y:ℝ)^(23/24:ℝ) → (Y:ℝ)/16 ≤ ‖M Y m-z‖)
    {α K : ℝ} (ha : 0 ≤ α) (ha' : α < 4/5) (hK : 0<K)
    (hE : ∃ N : ℕ, ∀ X ≥ N, energy M X ≤ K*(X:ℝ)^(3+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (missed X).card^5 ≤ X^4 := by
  obtain ⟨NE,hE⟩ := hE
  obtain ⟨NR,hR⟩ := rare_energy M hM
  obtain ⟨NF,hF⟩ := frequent_bound
  obtain ⟨NA,hA⟩ := ShiftConductor.shift_half_budget (α:=37/48) (C:=300) (by norm_num) (by norm_num)
  obtain ⟨NB,hB⟩ := ShiftConductor.shift_half_budget (α:=α) (C:=163840*K) ha' (by positivity)
  refine ⟨max 8 (max NE (max NR (max NF (max NA NB)))),?_⟩
  intro X hx
  have hxpos : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hr : ((rare X).card:ℝ) ≤ (163840*K)*(2*(X:ℝ))^α := by
    have h := (hR X (by omega)).trans (mul_le_mul_of_nonneg_left (hE X (by omega)) (by norm_num))
    rw [Real.rpow_add hxpos, Real.rpow_ofNat] at h
    apply le_trans (b := (163840*K)*(X:ℝ)^α)
    · apply le_of_mul_le_mul_right (a := (X:ℝ)^3) _ (by positivity)
      linarith only [h]
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hxpos.le (by linarith : (X:ℝ) ≤ 2*X) ha) (by positivity)
  have hc := hA X (by omega) (frequent X) (hF X (by omega))
  have hb := hB X (by omega) (rare X) hr
  have hs : missed X \ ShiftConductor.shifts X (frequent X) ⊆ ShiftConductor.shifts X (rare X) := by
    intro n hn
    obtain ⟨hi,ho⟩ := mem_sdiff.mp hn
    exact (mem_union.mp (cover X (by omega) hi)).resolve_left ho
  apply ShiftConductor.close_from_residual (frequent X) hc
  exact (by exact_mod_cast card_le_card hs :
    (((missed X \ ShiftConductor.shifts X (frequent X)).card):ℝ) ≤
        ((ShiftConductor.shifts X (rare X)).card:ℝ)).trans hb

end
end Goldbach.WideArcCriterion
