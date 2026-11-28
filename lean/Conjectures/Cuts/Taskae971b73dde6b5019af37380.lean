import Conjectures.Cuts.Task474580c269b155c270797611
import Mathlib

open Filter Finset
namespace LongWindowTransfer

private theorem log_power_bound (A d : ℝ) (hd : 0 < d) :
    ∀ᶠ X : ℕ in atTop, (Real.log X)^A ≤ (X:ℝ)^d := by
  have le := (isLittleO_log_rpow_rpow_atTop A hd).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually le,
    eventually_ge_atTop (2:ℕ)] with X hX h2
  have hl := Real.log_nonneg (show (1:ℝ)≤X by exact_mod_cast (show 1≤X by omega))
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hl A),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) d),one_mul] using hX

private theorem count (X H : ℕ) :
  ({n ∈ Icc (X-H) X | Even n ∧ ¬0 < ({p ∈ range (n+1) | Nat.Prime p ∧ Nat.Prime (n-p)}).card}).card ≤
  ({n ∈ Icc (X-H) X | 4≤n ∧ Even n ∧ ∀ p ∈ range (n+1), ¬(Nat.Prime p ∧ Nat.Prime (n-p))}).card + 4 := by
  classical
  let A := {n ∈ Icc (X-H) X | 4≤n ∧ Even n ∧ ∀ p ∈ range (n+1), ¬(Nat.Prime p ∧ Nat.Prime (n-p))}
  apply le_trans _ (show (A ∪ range 4).card ≤ A.card+4 by simpa using card_union_le A (range 4))
  apply card_le_card
  intro n hn
  obtain ⟨hm,he,hp⟩ := mem_filter.mp hn
  by_cases h4 : 4≤n
  · apply mem_union_left
    apply mem_filter.mpr
    refine ⟨hm,h4,he,fun p hpm hprime => hp (card_pos.mpr ⟨p,mem_filter.mpr ⟨hpm,hprime⟩⟩)⟩
  · exact mem_union_right _ (mem_range.mpr (by omega))

end LongWindowTransfer

theorem Conjectures.Cuts.Taskae971b73dde6b5019af37380 :
∀ (x1 : ℝ), (0 : ℝ) < x1 → ∀ (x3 : ℕ), ∃ (x4 : ℝ), (0 : ℝ) < x4 ∧ ∃ (x5 : ℕ), ∀ (x6 x7 : ℕ), x5 ≤ x6 → x7 ≤ x6 → (↑x6 : ℝ) ^ ((1 / 18 : ℝ) + x1) ≤ (↑x7 : ℝ) → (↑x6 : ℝ) ^ (1 / 2 : ℝ) ≤ (↑x7 : ℝ) → (↑{x12 ∈ Finset.Icc (x6 - x7) x6 | Even x12 ∧ ¬(0 : ℕ) < {x13 ∈ Finset.range (x12 + (1 : ℕ)) | Nat.Prime x13 ∧ Nat.Prime (x12 - x13)}.card}.card : ℝ) ≤ x4 * (↑x7 : ℝ) / ((1 : ℝ) + Real.log (↑x6 : ℝ)) ^ x3 := by
  intro ε hε A
  obtain ⟨B,C,hB,hC,T,hbound⟩ :=
    Conjectures.Cuts.Task474580c269b155c270797611 ((A+1:ℕ):ℝ) (by positivity)
  refine ⟨(C+4)*2^A,by positivity,?_⟩
  have hlarge : ∀ᶠ X : ℕ in atTop, X ≥ T ∧ 1 ≤ Real.log (X:ℝ) ∧
      (Real.log X)^B ≤ (X:ℝ)^(53/120:ℝ) ∧ (Real.log X)^(A:ℝ) ≤ (X:ℝ)^(1/2:ℝ) := by
    filter_upwards [eventually_ge_atTop T,
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1,
      LongWindowTransfer.log_power_bound B (53/120) (by norm_num),
      LongWindowTransfer.log_power_bound (A:ℝ) (1/2) (by norm_num)] with X h1 h2 h3 h4
    exact ⟨h1,h2,h3,h4⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hlarge
  refine ⟨max N 2,?_⟩
  intro X H hx hHX _ hroot
  obtain ⟨ht,hl,hb,ha⟩ := hN X ((le_max_left N 2).trans hx)
  have hxpos : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hsq : X ≤ H^2 := by
    rw [←Real.sqrt_eq_rpow, Real.sqrt_le_iff] at hroot
    exact_mod_cast hroot.2
  have hpow := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hxpos.le (7/120))
  rw [←Real.rpow_add hxpos, show (7/120:ℝ)+53/120=1/2 by norm_num] at hpow
  have hs := hbound X H ht hHX hsq (hpow.trans hroot)
  rw [Real.rpow_natCast,pow_succ] at hs
  rw [Real.rpow_natCast] at ha
  have lnpos : 0<Real.log (X:ℝ) := by linarith
  have pp : 0<(Real.log (X:ℝ))^A := pow_pos lnpos A
  have pm : 0<(1+Real.log (X:ℝ))^A := by positivity
  have hshift : (1+Real.log (X:ℝ))^A ≤ 2^A*(Real.log (X:ℝ))^A := by
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) A
  have hscaled := (le_div_iff₀ (mul_pos pp lnpos)).mp hs
  have hcount := LongWindowTransfer.count X H
  have hcnt : (_:ℝ) ≤ _ := Nat.cast_le.mpr hcount
  rw [Nat.cast_add,Nat.cast_ofNat] at hcnt
  apply (le_div_iff₀ pm).mpr
  have hpos : 0 ≤ (({n ∈ Icc (X-H) X | 4≤n ∧ Even n ∧ ∀ p ∈ range (n+1), ¬(Nat.Prime p ∧ Nat.Prime (n-p))}).card:ℝ) := by positivity
  have hz := mul_le_mul_of_nonneg_left hl (mul_nonneg hpos pp.le)
  have hh := mul_le_mul_of_nonneg_right hcnt pp.le
  have h4 := ha.trans hroot
  let eCount : ℝ := (({n ∈ Icc (X-H) X | Even n ∧ ¬0 < ({p ∈ range (n+1) | Nat.Prime p ∧ Nat.Prime (n-p)}).card}).card:ℝ)
  have hbase : eCount * (Real.log (X:ℝ))^A ≤ (C+4)*(H:ℝ) := by
    dsimp only [eCount]
    linarith only [hh,hscaled,hz,h4]
  change eCount * (1+Real.log (X:ℝ))^A ≤ _
  calc
    _ ≤ eCount * (2^A*(Real.log (X:ℝ))^A) :=
      mul_le_mul_of_nonneg_left hshift (Nat.cast_nonneg _)
    _ = (2:ℝ)^A * (eCount*(Real.log (X:ℝ))^A) := mul_left_comm _ _ _
    _ ≤ 2^A * ((C+4)*(H:ℝ)) := mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = _ := by ring
