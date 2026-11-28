import Conjectures.Goldbach.EstermannAlmostAllPolylog
import PEqualNP.Outside.L_goldbach_frontier_uncond_deep_second_moment

open Finset MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.WindowBessel.ExceptionalCoefficients

namespace Goldbach.ShiftWideArc
noncomputable section
open scoped Classical
def weight (k : ℕ) : ℝ := if k.Prime then Real.log k else 0
def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
def S (X : ℕ) (t : ℝ) : ℂ := ∑ k ∈ range (X+1), (weight k:ℂ)*phase (k*t)
def integrand (X m : ℕ) (t : ℝ) := (S X t)^2 * phase (-(m:ℝ)*t)
def Q (X : ℕ) := ⌊(X:ℝ)^(1/3:ℝ)⌋₊
def H (X : ℕ) := 256 * Q X * (Nat.log 2 (X+2))^2
def arcs (X : ℕ) := {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q X ∧ a≤q ∧ a.Coprime q ∧
  |t-(a:ℝ)/q| ≤ (H X:ℝ)/((q:ℝ)*X)}
def coefficient (A : Set ℝ) (X m : ℕ) := ∫ t in (0:ℝ)..1, A.indicator (integrand X m) t
def noPair (m : ℕ) := ∀ k j : ℕ, k+j=m → ¬ (k.Prime ∧ j.Prime)
def visible (X : ℕ) := (Icc X (2*X)).filter (fun m =>
  noPair m ∧ (X:ℝ)^(23/24:ℝ) ≤ ‖coefficient (arcs X) X m‖)

theorem cancel_at_exception (X m : ℕ) (h : noPair m) :
    coefficient (arcs X) X m + coefficient (arcs X)ᶜ X m = 0 := by
  have hg : MeasurableSet (arcs X) := EffectiveArcEndpoint.frontierMeasurable _ _ _
  have hc : Continuous (integrand X m) := by unfold integrand S phase; fun_prop
  refine (indicator_integral_split hg (hc.intervalIntegrable _ _)).trans ?_
  apply zero_from_pairs weight m X
  intro k j he
  by_cases hk : k.Prime
  · have hj : ¬ j.Prime := fun hp => h k j he ⟨hk,hp⟩
    simp [weight,hj]
  · simp [weight,hk]

theorem visible_power_saving : ∃ N : ℕ, ∀ X ≥ N,
    ((visible X).card : ℝ) ≤ (X:ℝ)^(37/48:ℝ) := by
  obtain ⟨N,hN⟩ := PEqualNP.Outside.L_goldbach_frontier_uncond_deep_second_moment
    (1/48) (by norm_num)
  refine ⟨max N 1,?_⟩
  intro X hx
  have hX : 0 < (X:ℝ) := by exact_mod_cast (show 0 < X by omega)
  have he : (∑ m ∈ Icc X (2*X), ‖coefficient (arcs X)ᶜ X m‖^2) ≤
      (X:ℝ)^(8/3+1/48:ℝ) := hN X ((le_max_left ..).trans hx)
  have hsum : ((visible X).card : ℝ)*((X:ℝ)^(23/24:ℝ))^2 ≤ (X:ℝ)^(8/3+1/48:ℝ) := by
    calc
      _ = ∑ _m ∈ visible X, ((X:ℝ)^(23/24:ℝ))^2 := by simp
      _ ≤ ∑ m ∈ visible X, ‖coefficient (arcs X)ᶜ X m‖^2 := by
        apply sum_le_sum
        intro m hm
        obtain ⟨_,hp,hw⟩ := mem_filter.mp hm
        have hh := eq_neg_of_add_eq_zero_left (cancel_at_exception X m hp)
        rw [hh,norm_neg] at hw
        exact pow_le_pow_left₀ (by positivity) hw 2
      _ ≤ _ := (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (by intros; positivity)).trans he
  apply (le_of_mul_le_mul_right (a := ((X:ℝ)^(23/24:ℝ))^2) _ (by positivity))
  calc
    _ ≤ _ := hsum
    _ = _ := by rw [← Real.rpow_mul_natCast hX.le, ← Real.rpow_add hX]; congr 1; norm_num
/-- All failed shifts with a large wide-arc coefficient at their dyadic scale
are charged to one of two explicitly bounded sets of frequencies. -/
def visibleShifts (X : ℕ) : Finset ℕ :=
  (Ico X (2*X)).filter (fun n => ∃ e ∈ Icc 1 (Nat.log 2 X / 2),
    let m := n-2^e
    let Y := if m < X then X/2 else X
    noPair m ∧ (Y:ℝ)^(23/24:ℝ) ≤ ‖coefficient (arcs Y) Y m‖)

theorem visible_shift_union (X : ℕ) (hx : 8 ≤ X) :
    (visibleShifts X).card ≤ ((visible (X/2)).card + (visible X).card) *
      (Nat.log 2 X / 2) := by
  let es := Icc 1 (Nat.log 2 X / 2)
  have hsub : visibleShifts X ⊆ (((visible (X/2) ∪ visible X) ×ˢ es).image
      (fun me : ℕ × ℕ => me.1 + 2^me.2)) := by
    intro n hn
    obtain ⟨hnI,e,he,hv⟩ := mem_filter.mp hn
    obtain ⟨hlo,hhi⟩ := mem_Ico.mp hnI
    have hl : 2 ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by decide) (by omega)
    have he' := (mem_Icc.mp he).2
    have heL : e+1 ≤ Nat.log 2 X := by omega
    have hs : 2^e*2 ≤ X := by
      rw [← pow_succ]; exact (Nat.le_log_iff_pow_le (by decide) (by omega)).mp heL
    refine mem_image.mpr ⟨(n-2^e,e),mem_product.mpr ⟨?_,he⟩,by dsimp; omega⟩
    apply mem_union.mpr
    by_cases h : n-2^e < X
    · left
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,by simpa [h] using hv⟩
    · right
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,by simpa [h] using hv⟩
  calc
    _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_image_le
    _ ≤ _ := by
      rw [card_product]
      simpa [es] using Nat.mul_le_mul_right (Nat.log 2 X/2) (card_union_le (visible (X/2)) (visible X))

theorem visible_shift_power_saving : ∃ N : ℕ, ∀ X ≥ N,
    ((visibleShifts X).card:ℝ) ≤ (X:ℝ)^(19/24:ℝ) := by
  obtain ⟨N,hN⟩ := visible_power_saving
  have hlog := Real.log_pos (by norm_num : (1:ℝ) < 2)
  have hb := (isLittleO_log_rpow_atTop (by norm_num : 0 < (1/48:ℝ))).bound
    (show 0 < Real.log 2 / 2 by positivity)
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hb)
  refine ⟨max 8 (max (2*N) Z),?_⟩
  intro X hx
  have h8 : 8 ≤ X := by omega
  have hxp : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hx1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1≤X by omega)
  have hscale := hN (X/2) (by omega)
  have hscale' := hN X (by omega)
  have hmono : (((X/2:ℕ):ℝ))^(37/48:ℝ) ≤ (X:ℝ)^(37/48:ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.div_le_self X 2) (by norm_num)
  have h := hZ X (by omega)
  simp only [Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg hxp.le _)] at h
  have hL : ((Nat.log 2 X / 2:ℕ):ℝ) ≤ Real.log X / Real.log 2 :=
    (Nat.cast_le.mpr (Nat.div_le_self ..)).trans (by simpa [Real.logb] using Real.natLog_le_logb X 2)
  have hL' : ((Nat.log 2 X / 2:ℕ):ℝ) ≤ (X:ℝ)^(1/48:ℝ)/2 := by
    apply hL.trans
    apply (div_le_iff₀ hlog).mpr
    linarith only [h]
  calc
    _ ≤ (((visible (X/2)).card:ℝ)+(visible X).card)*((Nat.log 2 X/2:ℕ):ℝ) := by
      exact_mod_cast visible_shift_union X h8
    _ ≤ (2*(X:ℝ)^(37/48:ℝ))*((X:ℝ)^(1/48:ℝ)/2) :=
      mul_le_mul (by linarith only [hscale.trans hmono,hscale']) hL' (by positivity) (by positivity)
    _ = _ := by
      rw [show 2*(X:ℝ)^(37/48:ℝ)*((X:ℝ)^(1/48:ℝ)/2) =
        (X:ℝ)^(37/48:ℝ)*(X:ℝ)^(1/48:ℝ) by ring, ← Real.rpow_add hxp]
      norm_num

def missed (X : ℕ) : Finset ℕ := (Ico X (2*X)).filter (fun n => Even n ∧
  0 < ((Icc 1 (Nat.log 2 X/2)).filter (fun e =>
    ((range (n-2^e+1)).filter (fun p => p.Prime ∧ (n-2^e-p).Prime)).card = 0)).card)

theorem noPair_iff (m : ℕ) : noPair m ↔
    ((range (m+1)).filter (fun p => p.Prime ∧ (m-p).Prime)).card = 0 := by
  rw [card_eq_zero,eq_empty_iff_forall_notMem]
  constructor
  · intro h p hp
    obtain ⟨hr,hp,hq⟩ := mem_filter.mp hp
    have hh := mem_range.mp hr
    exact h p (m-p) (by omega) ⟨hp,hq⟩
  · intro h k j hk hp
    apply h k
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),hp.1,(by simpa [show m-k=j by omega] using hp.2)⟩

theorem residual_witness {X n : ℕ} (hn : n ∈ missed X \ visibleShifts X) :
    ∃ e ∈ Icc 1 (Nat.log 2 X/2), let m := n-2^e
      let Y := if m<X then X/2 else X
      noPair m ∧ ‖coefficient (arcs Y) Y m‖ < (Y:ℝ)^(23/24:ℝ) := by
  obtain ⟨hm,hv⟩ := mem_sdiff.mp hn
  obtain ⟨hr,_,hpos⟩ := mem_filter.mp hm
  obtain ⟨e,he⟩ := card_pos.mp hpos
  obtain ⟨heI,hp⟩ := mem_filter.mp he
  have hnp := (noPair_iff _).mpr hp
  refine ⟨e,heI,hnp,lt_of_not_ge ?_⟩
  intro h
  exact hv (mem_filter.mpr ⟨hr,e,heI,hnp,h⟩)

theorem missed_split : ∃ N : ℕ, ∀ X ≥ N, ((missed X).card:ℝ) ≤
    ((missed X \ visibleShifts X).card:ℝ) + (X:ℝ)^(19/24:ℝ) := by
  obtain ⟨N,hN⟩ := visible_shift_power_saving
  refine ⟨N,fun X hx => ?_⟩
  have hsub : missed X ⊆ (missed X \ visibleShifts X) ∪ visibleShifts X := by
    intro m hm
    by_cases h : m ∈ visibleShifts X
    · exact mem_union_right _ h
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hm,h⟩)
  have hc := (card_le_card hsub).trans (card_union_le ..)
  calc
    _ ≤ ((missed X \ visibleShifts X).card:ℝ) + ((visibleShifts X).card:ℝ) := by exact_mod_cast hc
    _ ≤ _ := add_le_add le_rfl (hN X hx)

/-- Interior cutoffs keep the convolution away from either end of its support. -/
def interiorScales (m : ℕ) := Icc ((2*m+2)/3) (3*m/4)

def goodScales (X m : ℕ) := ((Icc (X/4) (2*X)) ∩ interiorScales m).filter
  (fun Y => m ∈ visible Y)

def frequent (X : ℕ) := (Icc (X/2) (2*X)).filter
  (fun m => X ≤ 100*(goodScales X m).card)

theorem frequent_bound : ∃ N : ℕ, ∀ X ≥ N, ((frequent X).card:ℝ) ≤
    300 * (2*(X:ℝ))^(37/48:ℝ) := by
  classical
  obtain ⟨N,hN⟩ := visible_power_saving
  refine ⟨max 8 (4*N),?_⟩
  intro X hx
  have hpos : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  let I := Icc (X/4) (2*X)
  let F := frequent X
  let a := fun (m Y : ℕ) => if m ∈ visible Y then (1:ℝ) else 0
  have hrow (m : ℕ) (hm : m ∈ F) : (X:ℝ) ≤ 100 * ∑ Y ∈ I, a m Y := by
    have h := (mem_filter.mp hm).2
    have hsub : goodScales X m ⊆ I.filter (fun Y => m ∈ visible Y) := by
      intro Y hY
      obtain ⟨hi,hv⟩ := mem_filter.mp hY
      exact mem_filter.mpr ⟨(mem_inter.mp hi).1,hv⟩
    have h' : X ≤ 100*(I.filter (fun Y => m ∈ visible Y)).card :=
      h.trans (Nat.mul_le_mul_left 100 (card_le_card hsub))
    simpa [a,← sum_filter] using (show (X:ℝ) ≤ 100*((I.filter (fun Y => m ∈ visible Y)).card:ℝ) by exact_mod_cast h')
  have hcol (Y : ℕ) (hy : Y ∈ I) : (∑ m ∈ F, a m Y) ≤ (2*(X:ℝ))^(37/48:ℝ) := by
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hy
    have hs : F ∩ visible Y ⊆ visible Y := inter_subset_right
    have hh := (hN Y (by omega)).trans (Real.rpow_le_rpow (by positivity)
      (show (Y:ℝ) ≤ 2*(X:ℝ) by exact_mod_cast hhi) (by norm_num))
    apply le_trans _ hh
    simpa [a,← sum_filter] using (show ((F ∩ visible Y).card:ℝ) ≤ ((visible Y).card:ℝ) by exact_mod_cast card_le_card hs)
  have hsize : (I.card:ℝ) ≤ 3*X := by
    have h : I.card ≤ 3*X := by simp [I]; omega
    exact_mod_cast h
  apply le_of_mul_le_mul_right (a := (X:ℝ)) _ hpos
  change (F.card:ℝ)*X ≤ _
  calc
    _ = ∑ _m ∈ F, (X:ℝ) := by simp
    _ ≤ ∑ m ∈ F, 100*∑ Y ∈ I, a m Y := sum_le_sum hrow
    _ = 100*∑ Y ∈ I, ∑ m ∈ F, a m Y := by rw [← mul_sum, sum_comm]
    _ ≤ 100 * (I.card * (2*(X:ℝ))^(37/48:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa using sum_le_sum hcol
    _ ≤ 100 * ((3*(X:ℝ)) * (2*(X:ℝ))^(37/48:ℝ)) := by gcongr
    _ = _ := by ring

theorem many_small_coefficients {X m : ℕ} (hx : 512 ≤ X) (hm : m ∈ Icc (X/2) (2*X))
    (hn : noPair m) (hf : m ∉ frequent X) :
    X ≤ 40 * ((interiorScales m).filter (fun Y =>
      ‖coefficient (arcs Y) Y m‖ < (Y:ℝ)^(23/24:ℝ))).card := by
  classical
  obtain ⟨hmlo,hmhi⟩ := mem_Icc.mp hm
  have hrare : 100*(goodScales X m).card < X := by
    by_contra! hh
    exact hf (mem_filter.mpr ⟨hm,hh⟩)
  let small := (interiorScales m).filter (fun Y =>
      ‖coefficient (arcs Y) Y m‖ < (Y:ℝ)^(23/24:ℝ))
  have sub : interiorScales m ⊆ small ∪ goodScales X m := by
    intro Y hy
    obtain ⟨ha,hb⟩ := mem_Icc.mp hy
    by_cases hs : ‖coefficient (arcs Y) Y m‖ < (Y:ℝ)^(23/24:ℝ)
    · exact mem_union_left _ (mem_filter.mpr ⟨hy,hs⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_inter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hy⟩,
        mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hn,le_of_not_gt hs⟩⟩)
  have h := (card_le_card sub).trans (card_union_le small (goodScales X m))
  change X ≤ 40*small.card
  simp only [interiorScales,Nat.card_Icc] at h
  omega

/-- Binary translates of exceptions witnessed at a positive fraction of cutoffs. -/
def covered (X : ℕ) := ((frequent X) ×ˢ Icc 1 (Nat.log 2 X/2)).image
  (fun me : ℕ × ℕ => me.1+2^me.2)

theorem covered_bound : ∃ N : ℕ, ∀ X ≥ N, ((covered X).card:ℝ) ≤
    (300*(2:ℝ)^(37/48:ℝ)/Real.log 2) * (X:ℝ)^(37/48:ℝ) * Real.log X := by
  obtain ⟨N,hN⟩ := frequent_bound
  refine ⟨max N 2,?_⟩
  intro X hx
  have hL : ((Nat.log 2 X/2:ℕ):ℝ) ≤ Real.log X/Real.log 2 :=
    (Nat.cast_le.mpr (Nat.div_le_self ..)).trans (by simpa [Real.logb] using Real.natLog_le_logb X 2)
  have hc : (covered X).card ≤ (frequent X).card*(Nat.log 2 X/2) :=
    by simpa [covered] using (card_image_le (s := frequent X ×ˢ Icc 1 (Nat.log 2 X/2))
      (f := fun me : ℕ × ℕ => me.1+2^me.2))
  calc
    _ ≤ ((frequent X).card:ℝ) * ((Nat.log 2 X/2:ℕ):ℝ) := by exact_mod_cast hc
    _ ≤ (300*(2*(X:ℝ))^(37/48:ℝ))*(Real.log X/Real.log 2) :=
      mul_le_mul (hN X (by omega)) hL (by positivity) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring

theorem uncovered_witness {X n : ℕ} (hx : 512 ≤ X) (hn : n ∈ missed X \ covered X) :
    ∃ e ∈ Icc 1 (Nat.log 2 X/2), let m := n-2^e
      noPair m ∧ X ≤ 40 * ((interiorScales m).filter (fun Y =>
        ‖coefficient (arcs Y) Y m‖ < (Y:ℝ)^(23/24:ℝ))).card := by
  obtain ⟨hm,hc⟩ := mem_sdiff.mp hn
  obtain ⟨hi,_,hp⟩ := mem_filter.mp hm
  obtain ⟨hn1,hn2⟩ := mem_Ico.mp hi
  obtain ⟨e,he⟩ := card_pos.mp hp
  obtain ⟨heI,h0⟩ := mem_filter.mp he
  have hlog : 2 ≤ Nat.log 2 X := Nat.le_log_of_pow_le (by decide) (by omega)
  have heL := (mem_Icc.mp heI).2
  have hp2 : 2^e*2 ≤ X := by
    rw [← pow_succ]
    exact (Nat.le_log_iff_pow_le (by decide) (by omega)).mp (by omega)
  have hnp := (noPair_iff _).mpr h0
  refine ⟨e,heI,hnp,many_small_coefficients hx (mem_Icc.mpr ⟨by omega,by omega⟩) hnp ?_⟩
  intro hf
  exact hc (mem_image.mpr ⟨(n-2^e,e),mem_product.mpr ⟨hf,heI⟩,by dsimp; omega⟩)

end
end Goldbach.ShiftWideArc
