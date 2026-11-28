import Mathlib
import Conjectures.Goldbach.ReflectedMajorSharpFloor

-- The major-arc transfer and coefficient reindexing are from #4275.


namespace GoldbachReflectedBand

open Finset Filter
open scoped Topology

def cap (N : ℕ) := Nat.log 2 (N + 2)

def lower (N : ℕ) := (2*N+2)/3

def upper (N : ℕ) := (3*N)/4

def halfBand (N : ℕ) := Icc (lower N) (upper N)

def bandPred (N m : ℕ) : Prop := 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m

def band (N : ℕ) : Finset ℕ :=
  (Icc N (2*N)).filter (fun m => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m)

def double : ℕ ↪ ℕ := ⟨fun u => 2*u, by
  intro a b h
  change 2*a = 2*b at h
  omega⟩

theorem band_eq_map (N : ℕ) : band N = (halfBand N).map double := by
  ext m
  constructor
  · intro hm
    obtain ⟨_, hlo, hhi, ⟨u, hu⟩⟩ := Finset.mem_filter.mp hm
    refine Finset.mem_map.mpr ⟨u, Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · dsimp [lower]
      omega
    · dsimp [upper]
      omega
    · change 2*u = m
      omega
  · intro hm
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hm
    obtain ⟨hlo,hhi⟩ := Finset.mem_Icc.mp hu
    dsimp only [lower, upper] at hlo hhi
    change 2*u ∈ (Icc N (2*N)).filter (fun m => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, by omega, ⟨u, by omega⟩⟩

theorem lower_le_upper (N : ℕ) (hN : 24 ≤ N) : lower N ≤ upper N := by
  dsimp [lower, upper]
  omega

theorem band_card (N : ℕ) : (band N).card = (halfBand N).card := by
  rw [band_eq_map, Finset.card_map]

theorem halfBand_card_ge (N : ℕ) (hN : 24 ≤ N) : N ≤ 24 * (halfBand N).card := by
  simp only [halfBand, Nat.card_Icc, lower, upper]
  omega

theorem sum_band (N : ℕ) (f : ℕ → ℝ) :
    (∑ m ∈ band N, f m) = ∑ u ∈ halfBand N, f (2*u) := by
  rw [band_eq_map, Finset.sum_map]
  rfl

theorem cap_pos (N : ℕ) : 0 < cap N := Nat.log_pos (by decide) (by omega)

theorem eventually_cap_ge (c : ℕ) : ∀ᶠ N : ℕ in atTop, c ≤ cap N := by
  filter_upwards [eventually_ge_atTop (2^c : ℕ)] with N hN
  exact Nat.le_log_of_pow_le (by decide) (hN.trans (Nat.le_add_right N 2))

theorem log_power_over_N (d : ℕ) :
    Tendsto (fun N : ℕ => (cap N : ℝ)^d / (N : ℝ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun N : ℕ => (Real.logb 2 ((N : ℝ)+2))^d / (N : ℝ)) atTop (𝓝 0) := by
    convert (Real.tendsto_pow_logb_div_mul_add_atTop (b := 2) 1 (-2) d one_ne_zero).comp hN using 1
    ext N
    simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Filter.Eventually.of_forall (fun _ => by positivity)) ?_
  filter_upwards with N
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  simpa [cap] using Real.natLog_le_logb (N+2) 2

theorem eventually_interval_error_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      8 * (cap N : ℝ)^4 / ((halfBand N).card : ℝ) ≤ ε := by
  have hlim := (log_power_over_N 4).const_mul (192 : ℝ)
  rw [mul_zero] at hlim
  filter_upwards [eventually_ge_atTop (24 : ℕ), hlim.eventually (gt_mem_nhds hε)] with N hN h
  have hNR : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hCard : (N : ℝ) ≤ 24*((halfBand N).card : ℝ) := by
    exact_mod_cast halfBand_card_ge N hN
  have hc : 0 < ((halfBand N).card : ℝ) := by
    linarith
  calc
    _ ≤ 8*(cap N : ℝ)^4 / ((N : ℝ)/24) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hCard])
    _ = 192*((cap N : ℝ)^4/(N : ℝ)) := by ring
    _ ≤ _ := h.le

end GoldbachReflectedBand

namespace GoldbachReflectedTransfer

open Finset Filter MeasureTheory GoldbachReflectedBand
open scoped Topology
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

noncomputable section

def actual (N m : ℕ) : ℝ :=
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun n t => ∑ p ∈ (Finset.range (n+1)).filter Nat.Prime,
    (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun n => let k := cap n
    {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(n : ℝ))}
  (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t)))
    (0 : ℝ) 1 MeasureTheory.volume).re

def normalized (N m : ℕ) : ℝ := actual N m / (2*(N : ℝ)-(m : ℝ))

private theorem frozen_primeSum (N : ℕ) (t : ℝ) :
    (∑ p ∈ (Finset.range (N+1)).filter Nat.Prime,
      (Real.log (p : ℝ) : ℂ) * GoldbachMajorArc.phase ((p : ℝ)*t)) =
      GoldbachMajorArc.primeSum N t := by
  rw [Finset.sum_filter, GoldbachMajorArc.primeSum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.Prime <;> simp [GoldbachMajorArc.primeWeight, hp]

theorem actual_eq (N m : ℕ) :
    actual N m = (GoldbachBa08Approx.coefficient N m (cap N) ((cap N)^3)).re := by
  dsimp only [actual, GoldbachBa08Approx.coefficient, GoldbachBa08Approx.arcs,
    GoldbachBlockGeometry.width]
  apply congrArg Complex.re
  have hS (t : ℝ) :
      (∑ p ∈ (Finset.range (N+1)).filter Nat.Prime,
        (Real.log (p : ℝ) : ℂ) * Complex.exp (((2*Real.pi*((p : ℝ)*t) : ℝ) : ℂ)*Complex.I)) =
        GoldbachMajorArc.primeSum N t := frozen_primeSum N t
  simp only [hS]
  rfl

private theorem approximates (e : ℝ) (he : 0 < e) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ band N,
      |actual N m - (2*(N:ℝ)-(m:ℝ)+1)*SharpAssembly.row (cap N) m| ≤ e*(N:ℝ) := by
  filter_upwards [SharpArcTransfer.transfer e he] with N hN
  intro m hm
  obtain ⟨hI,_⟩ := Finset.mem_filter.mp hm
  obtain ⟨hmL,hmU⟩ := Finset.mem_Icc.mp hI
  let v : ℂ := ((2*N-m:ℕ):ℂ)+1
  let s := ∑ q ∈ Icc 1 (cap N), GoldbachMajorArc.coefficient q m
  have err : |(GoldbachBa08Approx.coefficient N m (cap N) ((cap N)^3)-v*s).re| ≤ e*(N:ℝ) :=
    (Complex.abs_re_le_norm _).trans (hN m hmL hmU)
  have hv : v = ((2*(N:ℝ)-(m:ℝ)+1 : ℝ) : ℂ) := by
    dsimp [v]
    push_cast [hmU]
    ring
  rw [hv, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at err
  rw [actual_eq]
  simpa only [SharpAssembly.row, s, Complex.re_sum] using err

private theorem abs_row_le (N m : ℕ) : |SharpAssembly.row (cap N) m| ≤ 4*(cap N : ℝ) := by
  have hk : (1 : ℝ) ≤ cap N := by exact_mod_cast Nat.succ_le_of_lt (cap_pos N)
  unfold SharpAssembly.row
  calc
    _ ≤ ∑ q ∈ Icc 1 (cap N), |(GoldbachMajorArc.coefficient q m).re| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ Icc 1 (cap N), ‖GoldbachMajorArc.coefficient q m‖ :=
      Finset.sum_le_sum fun q _ => Complex.abs_re_le_norm _
    _ ≤ 4 * Real.sqrt (cap N : ℝ) := GoldbachMajorArc.sum_norm_coefficient_le_sqrt (cap N) m
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr hk)) (by norm_num)

theorem eventually_uniform (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ band N,
      |normalized N m - SharpAssembly.row (cap N) m| ≤ ε := by
  have hlim' : Tendsto (fun N : ℕ => 4*((cap N : ℝ)/(N : ℝ))) atTop (𝓝 0) := by
    simpa only [pow_one, mul_zero] using (log_power_over_N 1).const_mul (4 : ℝ)
  filter_upwards [approximates (ε/4) (by positivity), eventually_ge_atTop (1 : ℕ),
    hlim'.eventually (gt_mem_nhds (show 0 < ε/4 by positivity))] with N hA hN hsmall
  intro m hm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  let w := 2*(N:ℝ)-(m:ℝ)
  let r := SharpAssembly.row (cap N) m
  have hband : bandPred N m := (Finset.mem_filter.mp hm).2
  have hmu : 2*(m:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hband.2.1
  have hw : (N:ℝ) ≤ 2*w := by dsimp [w]; linarith only [hmu]
  have hwpos : 0 < w := by linarith only [hw,hNpos]
  have hs : 4*(cap N : ℝ) ≤ (ε/4)*(N:ℝ) := by
    change 4*((cap N : ℝ)/(N : ℝ)) < ε/4 at hsmall
    rw [← mul_div_assoc] at hsmall
    exact ((div_lt_iff₀ hNpos).mp hsmall).le
  have hre : |actual N m - (w+1)*r| ≤ (ε/4)*(N:ℝ) := hA m hm
  change |actual N m / w - r| ≤ _
  rw [show actual N m / w - r = (actual N m-(w+1)*r+r)/w by
    field_simp [hwpos.ne']
    ring, abs_div, abs_of_pos hwpos]
  apply (div_le_iff₀ hwpos).mpr
  calc
    _ ≤ |actual N m - (w+1)*r| + |r| := abs_add_le ..
    _ ≤ ((ε/4)*(N:ℝ)) + 4*(cap N : ℝ) := add_le_add hre (abs_row_le N m)
    _ ≤ ε*w := by nlinarith only [hs, mul_le_mul_of_nonneg_left hw hε.le]

end
end GoldbachReflectedTransfer


namespace GoldbachReflectedCRT

open Finset
open scoped BigOperators Classical

noncomputable def localFactor (p n : ℕ) : ℝ :=
  if p ∣ n then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

noncomputable def squarefreeRow (primes : Finset ℕ) (n : ℕ) : ℝ :=
  ∏ p ∈ primes, localFactor p n

private noncomputable def zFactor (p : ℕ) (x : ZMod p) : ℝ :=
  if x = 0 then 1 / ((p : ℝ) - 1) else -(1 / ((p : ℝ) - 1) ^ 2)

private theorem zFactor_natCast (p n : ℕ) :
    zFactor p (n : ZMod p) = localFactor p n := by
  simp only [zFactor, localFactor, ZMod.natCast_eq_zero_iff]

private theorem sum_natCast_range_eq_zmod {L : ℕ} [NeZero L] (f : ZMod L → ℝ) :
    ∑ n ∈ range L, f (n : ZMod L) = ∑ x : ZMod L, f x := by
  apply sum_bij (s := range L) (t := (univ : Finset (ZMod L))) (fun n _ => (n : ZMod L))
  · simp
  · intro a ha b hb hab
    have hval := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp ha),
      Nat.mod_eq_of_lt (mem_range.mp hb)] using hval
  · intro x _
    exact ⟨x.val, mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
  · intro n _
    rfl

set_option maxHeartbeats 1600000 in
/-- A complete period of independent prime residues factors, even after
any starting shift. -/
private theorem crt_sum (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    [∀ p : S, NeZero (p : ℕ)] (F : ∀ p : S, ZMod (p : ℕ) → ℝ) (start : ℕ) :
    (∑ n ∈ range (∏ p ∈ S, p), ∏ p : S, F p ((start + n : ℕ) : ZMod (p : ℕ))) =
      ∏ p : S, ∑ x : ZMod (p : ℕ), F p x := by
  let L := ∏ p : S, (p : ℕ)
  have hLpos : 0 < L := prod_pos (fun p _ => (hS p p.property).pos)
  let _ : NeZero L := ⟨hLpos.ne'⟩
  have hc : Pairwise (fun p q : S => (p : ℕ).Coprime (q : ℕ)) := by
    intro p q hpq
    apply (Nat.coprime_primes (hS p p.property) (hS q q.property)).mpr
    exact fun h => hpq (Subtype.ext h)
  let e := ZMod.prodEquivPi (fun p : S => (p : ℕ)) hc
  have comp (n : ℕ) (p : S) : e (n : ZMod L) p = (n : ZMod (p : ℕ)) := by
    dsimp only [e]
    rw [ZMod.prodEquivPi_apply, map_natCast]
  have hL : L = ∏ p ∈ S, p := prod_coe_sort S id
  rw [← hL]
  calc
    _ = ∑ n ∈ range L, ∏ p : S, F p (e (n : ZMod L) p + (start : ZMod (p : ℕ))) := by
      apply sum_congr rfl
      intro n _
      apply prod_congr rfl
      intro p _
      rw [comp, Nat.cast_add, add_comm]
    _ = ∑ n : ZMod L, ∏ p : S, F p (e n p + (start : ZMod (p : ℕ))) :=
      sum_natCast_range_eq_zmod (L := L)
        (fun (n : ZMod L) => ∏ p : S, F p (e n p + (start : ZMod (p : ℕ))))
    _ = ∑ t : ∀ p : S, ZMod (p : ℕ), ∏ p : S, F p (t p + (start : ZMod (p : ℕ))) :=
      Equiv.sum_comp e.toEquiv
        (fun (t : ∀ p : S, ZMod (p : ℕ)) => ∏ p : S, F p (t p + (start : ZMod (p : ℕ))))
    _ = ∏ p : S, ∑ x : ZMod (p : ℕ), F p (x + (start : ZMod (p : ℕ))) :=
      (Fintype.prod_sum (fun (p : S) (x : ZMod (p : ℕ)) =>
        F p (x + (start : ZMod (p : ℕ))))).symm
    _ = _ := by
      apply prod_congr rfl
      intro p _
      exact Equiv.sum_comp (Equiv.addRight (start : ZMod (p : ℕ))) (F p)

private theorem sum_if_zero (p : ℕ) [NeZero p] (u v : ℝ) :
    (∑ x : ZMod p, if x = 0 then u else v) = u + ((p - 1 : ℕ) : ℝ) * v := by
  classical
  let T := (univ : Finset (ZMod p)).erase 0
  have hT : T.card = p - 1 := by
    dsimp only [T]
    rw [card_erase_of_mem (mem_univ _), card_univ, ZMod.card]
  calc
    _ = (∑ x ∈ T, if x = 0 then u else v) + u := by
      simp [T]
    _ = (∑ _x ∈ T, v) + u := by
      congr 1
      apply sum_congr rfl
      intro x hx
      exact ite_eq_right (mem_erase.mp hx).1
    _ = _ := by rw [sum_const, nsmul_eq_mul, hT, add_comm]

private theorem zFactor_first (p : ℕ) [NeZero p] (hp : p.Prime) :
    ∑ x : ZMod p, zFactor p x = 0 := by
  simp only [zFactor, sum_if_zero, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
  ring

private theorem zFactor_second (p : ℕ) [NeZero p] (hp : p.Prime) :
    (∑ x : ZMod p, zFactor p x ^ 2) = (p : ℝ) / ((p : ℝ) - 1) ^ 3 := by
  simp only [zFactor, ite_pow, sum_if_zero, Nat.cast_sub hp.one_le, Nat.cast_one]
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  field_simp [show (p : ℝ) - 1 ≠ 0 by linarith]
  ring

private theorem extend_factor (A S : Finset ℕ) (hAS : A ⊆ S) (n : ℕ) :
    (∏ p : S, if (p : ℕ) ∈ A then localFactor (p : ℕ) n else 1) = squarefreeRow A n := by
  rw [prod_coe_sort S (fun p : ℕ => if p ∈ A then localFactor p n else 1)]
  rw [← prod_filter]
  congr 1
  ext p
  simp only [mem_filter]
  exact ⟨And.right, fun hp => ⟨hAS hp, hp⟩⟩

/-- Over a complete period, squarefree denominator coefficients are
orthogonal, with exact diagonal mean `∏ (p-1)⁻³`. -/
theorem pair_period_avg (A B : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hB : ∀ p ∈ B, p.Prime) (start : ℕ) :
    let L := ∏ p ∈ A ∪ B, p
    ((∑ n ∈ range L, squarefreeRow A (start+n) * squarefreeRow B (start+n)) / (L : ℝ)) =
      if A = B then ∏ p ∈ A, 1 / ((p : ℝ) - 1) ^ 3 else 0 := by
  classical
  let S := A ∪ B
  let L := ∏ p ∈ S, p
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime := by
    exact (mem_union.mp hp).elim (hA p) (hB p)
  let _ (p : S) : NeZero (p : ℕ) := ⟨(hS p p.property).ne_zero⟩
  let F (p : S) (x : ZMod (p : ℕ)) : ℝ :=
    (if (p : ℕ) ∈ A then zFactor p x else 1) *
      (if (p : ℕ) ∈ B then zFactor p x else 1)
  have factorize (n : ℕ) :
      (∏ p : S, F p (n : ZMod (p : ℕ))) = squarefreeRow A n * squarefreeRow B n := by
    simp only [F, zFactor_natCast, prod_mul_distrib]
    rw [extend_factor A S subset_union_left, extend_factor B S subset_union_right]
  have hsum : (∑ n ∈ range L, squarefreeRow A (start+n) * squarefreeRow B (start+n)) =
      ∏ p : S, ∑ x : ZMod (p : ℕ), F p x := by
    simp_rw [← factorize]
    exact crt_sum S hS F start
  have hL : (L : ℝ) = ∏ p : S, (p : ℝ) := by
    dsimp only [L]
    rw [Nat.cast_prod]
    exact (prod_coe_sort S (fun p : ℕ => (p : ℝ))).symm
  change _ / (L : ℝ) = _
  rw [hsum, hL, ← prod_div_distrib]
  have hlocal (p : S) :
      (∑ x : ZMod (p : ℕ), F p x) / (p : ℝ) =
        if (p : ℕ) ∈ A ∧ (p : ℕ) ∈ B then 1 / ((p : ℝ) - 1) ^ 3 else 0 := by
    have hp := hS p p.property
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    by_cases ha : (p : ℕ) ∈ A <;> by_cases hb : (p : ℕ) ∈ B
    · simp only [F, ha, hb, ite_true, and_self, ← pow_two, zFactor_second _ hp]
      field_simp [hp0]
    · simp only [F, ha, hb, ite_true, ite_false, mul_one, and_false, zFactor_first _ hp, zero_div]
    · simp only [F, ha, hb, ite_true, ite_false, one_mul, false_and, zFactor_first _ hp, zero_div]
    · exact False.elim ((mem_union.mp p.property).elim ha hb)
  simp_rw [hlocal]
  by_cases hab : A = B
  · rw [ite_eq_left hab]
    have hmem (p : S) : (p : ℕ) ∈ A ∧ (p : ℕ) ∈ B := by
      have hA' : (p : ℕ) ∈ A := (mem_union.mp p.property).elim id (fun h => hab ▸ h)
      exact ⟨hA', hab ▸ hA'⟩
    simp only [hmem, true_and, ite_true]
    rw [prod_coe_sort S (fun p : ℕ => 1 / ((p : ℝ) - 1) ^ 3)]
    rw [show S = A by dsimp only [S]; rw [← hab, union_self]]
  · rw [ite_eq_right hab]
    have hdiff : ∃ q ∈ S, ¬ (q ∈ A ∧ q ∈ B) := by
      by_contra! hh
      apply hab
      ext q
      exact ⟨fun h => (hh q (mem_union_left _ h)).2, fun h => (hh q (mem_union_right _ h)).1⟩
    obtain ⟨q, hq, hdiff⟩ := hdiff
    exact prod_eq_zero (mem_univ (⟨q,hq⟩ : S)) (ite_eq_right hdiff)

private theorem abs_localFactor_le_one (p n : ℕ) (hp : p.Prime) :
    |localFactor p n| ≤ 1 := by
  have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h₁ : (1 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have h₂ : (1 : ℝ) ≤ ((p : ℝ) - 1)^2 := one_le_pow₀ h₁
  unfold localFactor
  split_ifs
  · rw [abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).mpr h₁
  · rw [abs_neg, abs_of_nonneg (by positivity)]
    exact (div_le_one (by positivity)).mpr h₂

theorem abs_squarefreeRow_le_one (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime) (n : ℕ) :
    |squarefreeRow A n| ≤ 1 := by
  rw [squarefreeRow, Finset.abs_prod]
  exact prod_le_one₀ (fun _ _ => abs_nonneg _) (fun p hp => abs_localFactor_le_one p n (hA p hp))

/-- Bridge to any multiplicative coefficient with the project's prime
values. This uses only the checked coefficient-one, coefficient-mul and
coefficient-prime identities. -/
theorem period_le_product (A B : Finset ℕ)
    (hA : ∀ p ∈ A, 0 < p) :
    (∏ p ∈ A ∪ B, p) ≤ (∏ p ∈ A, p) * (∏ p ∈ B, p) := by
  rw [← Finset.prod_union_inter]
  exact Nat.le_mul_of_pos_right _ (prod_pos fun p hp => hA p (mem_inter.mp hp).1)

/-- Complete blocks contribute their exact mean. The leftover block and
its proposed mean each cost at most its length. -/
private theorem bounded_interval_error (f : ℕ → ℝ) (μ : ℝ) (P : ℕ) (hP : 0 < P)
    (hf : ∀ n, |f n| ≤ 1) (hμ : |μ| ≤ 1)
    (hm : ∀ s, (∑ n ∈ range P, f (s+n)) = (P : ℝ)*μ) (start length : ℕ) :
    |(∑ n ∈ range length, f (start+n)) - (length : ℝ)*μ| ≤ 2*(P : ℝ) := by
  have hblock (k : ℕ) :
      (∑ n ∈ range (k*P), f (start+n)) = ((k*P : ℕ) : ℝ)*μ := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.succ_mul, sum_range_add (fun n => f (start+n)), ih]
        simp_rw [← Nat.add_assoc start (k*P)]
        rw [hm, Nat.cast_add, add_mul]
  let k := length/P
  let r := length % P
  have hL : length = k*P+r := by
    simpa only [k, r, mul_comm P] using (Nat.div_add_mod length P).symm
  have hr : r < P := Nat.mod_lt _ hP
  have hsum : |∑ n ∈ range r, f (start+(k*P+n))| ≤ (r : ℝ) := calc
    _ ≤ ∑ n ∈ range r, |f (start+(k*P+n))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ range r, (1 : ℝ) := sum_le_sum (fun _ _ => hf _)
    _ = _ := by simp
  have hrμ : |(r : ℝ)*μ| ≤ (r : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg r)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hμ (Nat.cast_nonneg r)
  calc
    _ = |(∑ n ∈ range r, f (start+(k*P+n))) - (r : ℝ)*μ| := by
      rw [hL, sum_range_add (fun n => f (start+n)), hblock, Nat.cast_add]
      apply congrArg abs
      ring
    _ ≤ |∑ n ∈ range r, f (start+(k*P+n))| + |(r : ℝ)*μ| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (∑ n ∈ range r, f (start+(k*P+n))) (-((r : ℝ)*μ))
    _ ≤ (r : ℝ) + r := add_le_add hsum hrμ
    _ ≤ _ := by
      have h : (r : ℝ) ≤ (P : ℝ) := by exact_mod_cast hr.le
      linarith only [h]

/-- The averaged complete-period formula has an endpoint error at most
twice the period when summed on an arbitrary natural interval. -/
theorem pair_interval_error (A B : Finset ℕ)
    (hA : ∀ p ∈ A, p.Prime) (hB : ∀ p ∈ B, p.Prime) (start length : ℕ) :
    let L := ∏ p ∈ A ∪ B, p
    let μ := if A = B then ∏ p ∈ A, 1 / ((p : ℝ) - 1)^3 else 0
    |(∑ n ∈ range length, squarefreeRow A (start+n) * squarefreeRow B (start+n)) -
      (length : ℝ)*μ| ≤ 2*(L : ℝ) := by
  let L : ℕ := ∏ p ∈ A ∪ B, p
  let μ : ℝ := if A = B then ∏ p ∈ A, 1 / ((p : ℝ) - 1)^3 else 0
  let f := fun n => squarefreeRow A n * squarefreeRow B n
  have hL : 0 < L := prod_pos (fun p hp => ((mem_union.mp hp).elim (hA p) (hB p)).pos)
  have hf (n : ℕ) : |f n| ≤ 1 := by
    dsimp only [f]
    rw [abs_mul, ← one_mul (1 : ℝ)]
    exact mul_le_mul (abs_squarefreeRow_le_one A hA n) (abs_squarefreeRow_le_one B hB n)
      (abs_nonneg _) zero_le_one
  have hμ : |μ| ≤ 1 := by
    unfold μ
    split_ifs
    · rw [abs_prod]
      apply prod_le_one₀ (fun _ _ => abs_nonneg _)
      intro p hp
      have hpr : (2 : ℝ) ≤ p := by exact_mod_cast (hA p hp).two_le
      have h₁ : 1 ≤ (p : ℝ) - 1 := by linarith
      rw [abs_of_nonneg (by positivity)]
      exact (div_le_one (by positivity)).mpr (one_le_pow₀ h₁)
    · norm_num
  apply bounded_interval_error f μ L hL hf hμ _ start length
  intro s
  have h := pair_period_avg A B hA hB s
  change (∑ n ∈ range L, f (s+n)) / (L : ℝ) = μ at h
  simpa only [mul_comm] using (div_eq_iff (by positivity : (L : ℝ) ≠ 0)).mp h

end GoldbachReflectedCRT

namespace GoldbachReflectedCRT

open Finset
open scoped BigOperators Classical

private theorem sum_Icc_as_range (L U : ℕ) (f : ℕ → ℝ) :
    (∑ u ∈ Icc L U, f u) = ∑ i ∈ range (Icc L U).card, f (L+i) := by
  symm
  apply sum_bij (s := range (Icc L U).card) (t := Icc L U) (fun i _ => L+i)
  · intro i hi
    rw [mem_range, Nat.card_Icc] at hi
    exact mem_Icc.mpr (by omega)
  · intro i _ j _ h
    omega
  · intro u hu
    rw [mem_Icc] at hu
    refine ⟨u-L, ?_, by omega⟩
    rw [mem_range, Nat.card_Icc]
    omega
  · intro i _
    rfl

private noncomputable def diagonal (q : ℕ) : ℝ :=
  ∏ p ∈ q.primeFactors, 1 / ((p : ℝ)-1)^3

private theorem natural_pair_Icc_error {q r k : ℕ} (hqs : Squarefree q)
    (hrs : Squarefree r) (hqk : q ≤ k) (hrk : r ≤ k) (L U : ℕ) :
    |(∑ u ∈ Icc L U, squarefreeRow q.primeFactors u * squarefreeRow r.primeFactors u) -
       ((Icc L U).card : ℝ) * (if q = r then diagonal q else 0)| ≤ 2 * (k : ℝ)^2 := by
  have hprimeq (p : ℕ) (hp : p ∈ q.primeFactors) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hprimer (p : ℕ) (hp : p ∈ r.primeFactors) : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hiff : q.primeFactors = r.primeFactors ↔ q = r := by
    constructor
    · intro heq
      rw [← Nat.prod_primeFactors_of_squarefree hqs, ← Nat.prod_primeFactors_of_squarefree hrs,
        heq]
    · exact congrArg Nat.primeFactors
  let period := ∏ p ∈ q.primeFactors ∪ r.primeFactors, p
  have hperiod : period ≤ k*k := calc
    _ ≤ (∏ p ∈ q.primeFactors, p) * (∏ p ∈ r.primeFactors, p) :=
      period_le_product _ _ (fun p hp => (hprimeq p hp).pos)
    _ = q*r := by rw [Nat.prod_primeFactors_of_squarefree hqs, Nat.prod_primeFactors_of_squarefree hrs]
    _ ≤ _ := Nat.mul_le_mul hqk hrk
  rw [sum_Icc_as_range]
  have hinterval := pair_interval_error q.primeFactors r.primeFactors hprimeq hprimer
    L (Icc L U).card
  dsimp only at hinterval
  have hreal : (period : ℝ) ≤ (k : ℝ) * (k : ℝ) := by exact_mod_cast hperiod
  calc
    _ ≤ 2 * (period : ℝ) := by simpa only [hiff, diagonal] using hinterval
    _ ≤ _ := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left hreal (by norm_num)

set_option maxHeartbeats 1200000 in
/-- The weighted row mean square is bounded by the CRT diagonal plus a uniform
bound for the incomplete-period contribution. -/
theorem weighted_square_average (Q : Finset ℕ) (w : ℕ → ℝ) (k L U : ℕ)
    (hLU : L ≤ U) (hQ : ∀ q ∈ Q, q ≤ k ∧ Squarefree q)
    (hw : ∀ q ∈ Q, |w q| ≤ 2) :
    ((∑ u ∈ Icc L U, (∑ q ∈ Q, w q * squarefreeRow q.primeFactors u)^2) /
      ((Icc L U).card : ℝ))
      ≤ (∑ q ∈ Q, (w q)^2 * ∏ p ∈ q.primeFactors, 1 / ((p : ℝ)-1)^3) +
        8 * (k : ℝ)^4 / ((Icc L U).card : ℝ) := by
  let band := Icc L U
  let count : ℝ := band.card
  let row (q u : ℕ) := squarefreeRow q.primeFactors u
  let μ (q r : ℕ) := if q = r then diagonal q else 0
  let corr (q r : ℕ) := ∑ u ∈ band, row q u * row r u
  let weight (q r : ℕ) := w q * w r
  let diag := ∑ q ∈ Q, (w q)^2 * diagonal q
  have hcount : 0 < count := by
    have hc : 0 < band.card := card_pos.mpr ⟨L, mem_Icc.mpr ⟨le_rfl, hLU⟩⟩
    change (0 : ℝ) < (band.card : ℝ)
    exact_mod_cast hc
  have hcard : Q.card ≤ k := calc
    _ ≤ (Icc 1 k).card := card_le_card (by
      intro q hq
      exact mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (hQ q hq).2.ne_zero, (hQ q hq).1⟩)
    _ = k := by rw [Nat.card_Icc]; omega
  have hpair (q : ℕ) (hq : q ∈ Q) (r : ℕ) (hr : r ∈ Q) :
      weight q r * corr q r ≤ weight q r * (count * μ q r) + 8*(k : ℝ)^2 := by
    have he := natural_pair_Icc_error (hQ q hq).2 (hQ r hr).2
      (hQ q hq).1 (hQ r hr).1 L U
    change |corr q r - count * μ q r| ≤ 2*(k : ℝ)^2 at he
    have hweight : |weight q r| ≤ 4 := by
      unfold weight
      rw [abs_mul]
      calc
        _ ≤ (2 : ℝ) * 2 := mul_le_mul (hw q hq) (hw r hr) (abs_nonneg _) (by norm_num)
        _ = _ := by norm_num
    have hdiff : weight q r * (corr q r - count * μ q r) ≤ 8*(k : ℝ)^2 := calc
      _ ≤ |_| := le_abs_self _
      _ = |weight q r| * |corr q r - count * μ q r| := abs_mul _ _
      _ ≤ 4 * (2*(k : ℝ)^2) := mul_le_mul hweight he (abs_nonneg _) (by norm_num)
      _ = _ := by ring
    rw [mul_sub] at hdiff
    linarith only [hdiff]
  have hexpand (u : ℕ) : (∑ q ∈ Q, w q * row q u)^2 =
      ∑ q ∈ Q, ∑ r ∈ Q, weight q r * (row q u * row r u) := by
    rw [pow_two, sum_mul]
    apply sum_congr rfl
    intro q _
    rw [mul_sum]
    apply sum_congr rfl
    intro r _
    unfold weight
    ring
  have hdouble :
      (∑ u ∈ band, (∑ q ∈ Q, w q * row q u)^2) =
        ∑ q ∈ Q, ∑ r ∈ Q, weight q r * corr q r := by
    simp_rw [hexpand]
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    rw [sum_comm]
    apply sum_congr rfl
    intro r _
    simp only [corr, mul_sum]
  have hdiag :
      (∑ q ∈ Q, ∑ r ∈ Q, weight q r * (count * μ q r)) = count * diag := by
    simp only [diag, mul_sum]
    apply sum_congr rfl
    intro q hq
    rw [sum_eq_single q]
    · simp only [μ, ite_eq_left rfl, weight]
      ring
    · intro r _ hrq
      simp [μ, Ne.symm hrq]
    · exact fun h => (h hq).elim
  have herror :
      (∑ q ∈ Q, ∑ r ∈ Q, 8*(k : ℝ)^2) ≤ 8*(k : ℝ)^4 := by
    have hc : (Q.card : ℝ) ≤ k := by exact_mod_cast hcard
    have hp : (Q.card : ℝ)^2 ≤ (k : ℝ)^2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 8*(k : ℝ)^2 by positivity)
    simp only [sum_const, nsmul_eq_mul]
    convert hh using 1 <;> ring
  have hsum :
      (∑ u ∈ band, (∑ q ∈ Q, w q * row q u)^2) ≤ count * diag + 8*(k : ℝ)^4 := by
    rw [hdouble]
    calc
      _ ≤ ∑ q ∈ Q, ∑ r ∈ Q, (weight q r * (count * μ q r) + 8*(k : ℝ)^2) :=
        sum_le_sum fun q hq => sum_le_sum fun r hr => hpair q hq r hr
      _ = count * diag + (∑ q ∈ Q, ∑ r ∈ Q, 8*(k : ℝ)^2) := by
        simp_rw [sum_add_distrib]
        rw [hdiag]
      _ ≤ _ := add_le_add_right herror _
  change (∑ u ∈ band, (∑ q ∈ Q, w q * row q u)^2) / count ≤
    diag + 8*(k : ℝ)^4 / count
  calc
    _ ≤ (count * diag + 8*(k : ℝ)^4) / count := div_le_div_of_nonneg_right hsum hcount.le
    _ = _ := by rw [add_div, mul_comm count diag, mul_div_cancel_right₀ _ hcount.ne']

end GoldbachReflectedCRT


namespace GoldbachReflectedEuler

open Filter Finset
open scoped Topology BigOperators

noncomputable section

private def reciprocalSquare (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

private theorem reciprocalSquare_nonneg (p : ℕ) : 0 ≤ reciprocalSquare p := by
  unfold reciprocalSquare
  positivity

/-- A telescoping majorant for the reciprocal-square tail on any finite set. -/
theorem finset_square_tail (y : ℕ) (hy : 2 ≤ y) (s : Finset ℕ)
    (hs : ∀ p ∈ s, y < p) :
    (∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2) ≤ 2 / (y : ℝ) := by
  let g := fun p : ℕ => 1 / ((p : ℝ) - 2)
  let n := max (y + 1) (s.sup id + 1)
  have hyn : y + 1 ≤ n := le_max_left _ _
  have hsubset : s ⊆ Ico (y + 1) n := by
    intro p hp
    have hsup : p ≤ s.sup id := le_sup (f := id) hp
    exact mem_Ico.mpr ⟨Nat.succ_le_of_lt (hs p hp),
      (Nat.lt_succ_of_le hsup).trans_le (le_max_right _ _)⟩
  have htelRange (k : ℕ) : (∑ p ∈ range k, (g p - g (p + 1))) = g 0 - g k := by
    calc
      _ = -(∑ p ∈ range k, (g (p + 1) - g p)) := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro p _
        ring
      _ = _ := by rw [sum_range_sub]; ring
  have htel : (∑ p ∈ Ico (y + 1) n, (g p - g (p + 1))) = g (y + 1) - g n := by
    rw [sum_Ico_eq_sub _ hyn, htelRange, htelRange]
    ring
  have hyreal : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  calc
    (∑ p ∈ s, 1 / ((p : ℝ) - 1) ^ 2) ≤
        ∑ p ∈ Ico (y + 1) n, (1 / ((p : ℝ) - 1) ^ 2) :=
      sum_le_sum_of_subset_of_nonneg hsubset (fun p _ _ => reciprocalSquare_nonneg p)
    _ ≤ ∑ p ∈ Ico (y + 1) n, (g p - g (p + 1)) := by
      apply sum_le_sum
      intro p hp
      have hp₀ : 3 ≤ p := by have := (mem_Ico.mp hp).1; omega
      have hp₁ : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp₀
      have h₂ : 0 < (p : ℝ) - 2 := by linarith
      have h₁ : 0 < (p : ℝ) - 1 := by linarith
      have hx : g p - g (p + 1) = 1 / (((p : ℝ) - 2) * ((p : ℝ) - 1)) := by
        simp only [g, Nat.cast_add, Nat.cast_one]
        rw [show (p : ℝ) + 1 - 2 = (p : ℝ) - 1 by ring]
        field_simp [h₂.ne', h₁.ne']
        ring
      rw [hx]
      apply one_div_le_one_div_of_le (mul_pos h₂ h₁)
      nlinarith only [h₁]
    _ = g (y + 1) - g n := htel
    _ ≤ 1 / ((y : ℝ) - 1) := by
      have hn : 3 ≤ n := by omega
      have hnreal : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hgn : 0 ≤ g n := by
        apply one_div_nonneg.mpr
        linarith
      have hy' : g (y + 1) = 1 / ((y : ℝ) - 1) := by
        simp only [g, Nat.cast_add, Nat.cast_one]
        congr 1
        ring
      linarith only [hgn, hy']
    _ ≤ 2 / (y : ℝ) := by
      calc
        1 / ((y : ℝ) - 1) ≤ 1 / ((y : ℝ) / 2) :=
          one_div_le_one_div_of_le (by linarith) (by linarith)
        _ = 2 / (y : ℝ) := by ring

/-- Cubic reciprocal tails are bounded by a factor of `1 / y` times the square tail. -/
def factor (p : ℕ) : ℝ := if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1

private def correction (p : ℕ) : ℝ := if Nat.Prime p ∧ 2 < p then reciprocalSquare p else 0

private theorem factor_eq (p : ℕ) : factor p = 1 - correction p := by
  by_cases h : Nat.Prime p ∧ 2 < p <;> simp [factor, correction, h, reciprocalSquare]

private theorem correction_nonneg (p : ℕ) : 0 ≤ correction p := by
  unfold correction
  split_ifs <;> first | exact reciprocalSquare_nonneg p | rfl

private theorem correction_le_one (p : ℕ) : correction p ≤ 1 := by
  unfold correction
  split_ifs with hp
  · have h : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show 3 ≤ p from hp.2)
    have hb : 1 ≤ (p : ℝ) - 1 := by linarith
    have := one_le_pow₀ hb (n := 2)
    simpa [reciprocalSquare] using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) this
  · norm_num

theorem factor_nonneg (p : ℕ) : 0 ≤ factor p := by
  rw [factor_eq]
  exact sub_nonneg.mpr (correction_le_one p)

theorem factor_le_one (p : ℕ) : factor p ≤ 1 := by
  rw [factor_eq]
  exact sub_le_self _ (correction_nonneg p)

private theorem correction_summable : Summable correction := by
  refine summable_of_sum_le (c := 1) correction_nonneg (fun s => ?_)
  rw [show (∑ p ∈ s, correction p) =
      ∑ p ∈ s.filter (fun p => Nat.Prime p ∧ 2 < p), reciprocalSquare p by simp [correction, sum_filter]]
  simpa [reciprocalSquare] using
    finset_square_tail 2 (by omega) (s.filter (fun p => Nat.Prime p ∧ 2 < p))
      (fun p hp => ((mem_filter.mp hp).2).2)

/-- Euler factors at the primes larger than the cutoff. -/
def tail (y : ℕ) : ℝ := ∏' p : ℕ, if y < p then factor p else 1

private def tailCorrection (y p : ℕ) : ℝ := if y < p then correction p else 0

private theorem tailFactor_eq (y p : ℕ) : (if y < p then factor p else 1) = 1 - tailCorrection y p := by
  by_cases h : y < p <;> simp [h, factor_eq, tailCorrection]

private theorem tailCorrection_nonneg (y p : ℕ) : 0 ≤ tailCorrection y p := by
  unfold tailCorrection
  split_ifs <;> first | exact correction_nonneg p | rfl

private theorem tailCorrection_le_one (y p : ℕ) : tailCorrection y p ≤ 1 := by
  unfold tailCorrection
  split_ifs <;> first | exact correction_le_one p | norm_num

private theorem tail_multipliable (y : ℕ) : Multipliable (fun p : ℕ => if y < p then factor p else 1) := by
  have hs : Summable (tailCorrection y) := by
    refine Summable.of_nonneg_of_le (tailCorrection_nonneg y) (fun p => ?_) correction_summable
    unfold tailCorrection
    split_ifs <;> first | rfl | exact correction_nonneg p
  simp_rw [tailFactor_eq]
  apply multipliable_one_sub_of_summable
  simpa only [Real.norm_eq_abs, abs_of_nonneg (tailCorrection_nonneg y _)] using hs

theorem tprod_factor_eq_prefix_mul_tail (y : ℕ) :
    (∏' p : ℕ, factor p) =
      (∏ p ∈ (range (y + 1)).filter (fun p => Nat.Prime p ∧ 2 < p), factor p) * tail y := by
  let S := (range (y + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)
  let f := fun p => if p ∈ S then factor p else 1
  have hf : Multipliable f := multipliable_of_ne_finset_one (s := S) (fun p hp => ite_eq_right hp)
  have hd (p : ℕ) : factor p = f p * (if y < p then factor p else 1) := by
    by_cases h : Nat.Prime p ∧ 2 < p
    · by_cases h' : y < p
      · have hn : p ∉ S := by simpa [S, h, Nat.lt_succ_iff, not_le] using h'
        simp [f, hn, h']
      · have hm : p ∈ S := by simpa [S, h, Nat.lt_succ_iff, not_lt] using h'
        simp [f, hm, h']
    · simp [f, factor, h]
  calc
    (∏' p : ℕ, factor p) = ∏' p : ℕ, f p * (if y < p then factor p else 1) := tprod_congr hd
    _ = (∏' p : ℕ, f p) * tail y := hf.tprod_mul (tail_multipliable y)
    _ = _ := by
      congr 1
      rw [tprod_eq_prod (s := S) (fun p hp => ite_eq_right hp)]
      change (∏ p ∈ S, f p) = ∏ p ∈ S, factor p
      exact prod_congr rfl (fun p hp => ite_eq_left hp)

theorem tail_nonneg (y : ℕ) : 0 ≤ tail y := by
  apply tprod_nonneg
  intro p
  split_ifs <;> first | exact factor_nonneg p | norm_num

theorem tail_le_one (y : ℕ) : tail y ≤ 1 := by
  apply le_of_tendsto' (tail_multipliable y).hasProd
  intro s
  apply prod_le_one₀
  · intro p _
    split_ifs <;> first | exact factor_nonneg p | norm_num
  · intro p _
    split_ifs <;> first | exact factor_le_one p | rfl

private theorem prod_deficit_le_sum (s : Finset ℕ) (f : ℕ → ℝ) (ha : ∀ p, 0 ≤ f p)
    (hb : ∀ p, f p ≤ 1) :
    1 - ∏ p ∈ s, (1 - f p) ≤ ∑ p ∈ s, f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [prod_insert hp, sum_insert hp]
    have hprod : ∏ q ∈ s, (1 - f q) ≤ 1 :=
      prod_le_one₀ (fun q _ => sub_nonneg.mpr (hb q)) (fun q _ => sub_le_self _ (ha q))
    nlinarith only [ih, mul_nonneg (ha p) (sub_nonneg.mpr hprod)]

theorem one_sub_tail_le (y : ℕ) (hy : 2 ≤ y) : 1 - tail y ≤ 2 / (y : ℝ) := by
  have hlim : Tendsto (fun s : Finset ℕ => 1 - ∏ p ∈ s, (if y < p then factor p else 1))
      atTop (𝓝 (1 - tail y)) := tendsto_const_nhds.sub (tail_multipliable y).hasProd
  apply le_of_tendsto' hlim
  intro s
  rw [show (∏ p ∈ s, (if y < p then factor p else 1)) =
      ∏ p ∈ s, (1 - tailCorrection y p) by simp_rw [tailFactor_eq]]
  refine (prod_deficit_le_sum s (tailCorrection y) (tailCorrection_nonneg y)
    (tailCorrection_le_one y)).trans ?_
  rw [show (∑ p ∈ s, tailCorrection y p) =
      ∑ p ∈ s.filter (fun p => y < p ∧ (Nat.Prime p ∧ 2 < p)), reciprocalSquare p by
    simp [tailCorrection, correction, sum_filter, ite_and]]
  exact finset_square_tail y hy _ (fun p hp => ((mem_filter.mp hp).2).1)

end

end GoldbachReflectedEuler


open Finset

namespace GoldbachReflectedDiagonal

noncomputable def cube (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)^3

noncomputable def weight (S : Finset ℕ) : ℝ := ∏ p ∈ S, cube p

noncomputable def diag (q : ℕ) : ℝ := weight q.primeFactors

/-- A telescoping majorant for the reciprocal cubes. -/
private lemma cube_le_step (p : ℕ) (hp : 2 ≤ p) :
    cube p ≤ 2 * (1 / ((p - 1 : ℕ) : ℝ)^2 - 1 / (p : ℝ)^2) := by
  rw [cube, Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  let x : ℝ := (p : ℝ) - 1
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hx₁ : 0 < x := by linarith
  have hx₂ : 0 < x + 1 := by linarith
  have hpx : (p : ℝ) = x + 1 := by dsimp [x]; ring
  change 1 / x^3 ≤ 2 * (1 / x^2 - 1 / (p : ℝ)^2)
  rw [hpx]
  have hD : 0 < x^3 * (x + 1)^2 := by positivity
  apply (mul_le_mul_iff_left₀ hD).mp
  have hL : 1 / x^3 * (x^3 * (x + 1)^2) = (x + 1)^2 := by
    field_simp
  have hR : (2 * (1 / x^2 - 1 / (x + 1)^2)) * (x^3 * (x + 1)^2) =
      2 * x * (2 * x + 1) := by
    field_simp
    ring
  rw [hL, hR]
  nlinarith [sq_nonneg (x - 1)]

private lemma cube_nonneg (p : ℕ) (hp : 2 ≤ p) : 0 ≤ cube p := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold cube
  have : 0 ≤ (p : ℝ) - 1 := by linarith
  positivity

private lemma cube_nonneg_on_Ioc {y k p : ℕ} (hy : 1 ≤ y) (hp : p ∈ Ioc y k) :
    0 ≤ cube p := cube_nonneg p (by have := (mem_Ioc.mp hp).1; omega)

private lemma telescoping (y k : ℕ) (hy : y ≤ k) :
    ∑ p ∈ Ioc y k, (1 / ((p - 1 : ℕ) : ℝ)^2 - 1 / (p : ℝ)^2) =
      1 / (y : ℝ)^2 - 1 / (k : ℝ)^2 := by
  induction k, hy using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Ioc_succ_top hn, ih, Nat.succ_sub_one]
    ring

/-- An arbitrary subset of the integers above y has reciprocal-cube mass at most 2/y². -/
private theorem sum_cube_le (P : Finset ℕ) (y k : ℕ) (hy : 1 ≤ y)
    (hP : P ⊆ Ioc y k) : ∑ p ∈ P, cube p ≤ 2 / (y : ℝ)^2 := by
  have hPk : P ⊆ Ioc y (max y k) :=
    fun p hp ↦ mem_Ioc.mpr
      ⟨(mem_Ioc.mp (hP hp)).1, (mem_Ioc.mp (hP hp)).2.trans (le_max_right _ _)⟩
  calc
    ∑ p ∈ P, cube p ≤ ∑ p ∈ Ioc y (max y k), cube p :=
      sum_le_sum_of_subset_of_nonneg hPk fun p hp _ ↦ cube_nonneg_on_Ioc hy hp
    _ ≤ ∑ p ∈ Ioc y (max y k), 2 * (1 / ((p - 1 : ℕ) : ℝ)^2 - 1 / (p : ℝ)^2) :=
      sum_le_sum fun p hp ↦ cube_le_step p (by have := (mem_Ioc.mp hp).1; omega)
    _ ≤ 2 / (y : ℝ)^2 := by
      rw [← mul_sum, telescoping y (max y k) (le_max_left _ _)]
      calc
        _ = 2 / (y : ℝ)^2 - 2 * (1 / ((max y k : ℕ) : ℝ)^2) := by ring
        _ ≤ _ := sub_le_self _ (by positivity)

private lemma prod_bound (P : Finset ℕ) (k : ℕ) (hP : P ⊆ Ioc 1 k) :
    ∏ p ∈ P, (1 + cube p) ≤ Real.exp 2 := by
  calc
    ∏ p ∈ P, (1 + cube p) ≤ ∏ p ∈ P, Real.exp (cube p) := by
      exact prod_le_prod₀ (fun p hp ↦ by linarith [cube_nonneg_on_Ioc (by decide) (hP hp)])
        (fun p _ ↦ by simpa [add_comm] using Real.add_one_le_exp (cube p))
    _ = Real.exp (∑ p ∈ P, cube p) := (Real.exp_sum P cube).symm
    _ ≤ Real.exp 2 := by
      apply Real.exp_le_exp.mpr
      simpa using sum_cube_le P 1 k (by decide) hP

private lemma prod_sub_one_le {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ p ∈ S, 0 ≤ f p) :
    (∏ p ∈ S, (1 + f p)) - 1 ≤ (∏ p ∈ S, (1 + f p)) * ∑ p ∈ S, f p := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have ha₀ := hf a (mem_insert_self a T)
    have hT : ∀ p ∈ T, 0 ≤ f p := fun p hp ↦ hf p (mem_insert_of_mem hp)
    have hProd : 0 ≤ ∏ p ∈ T, (1 + f p) := prod_nonneg fun p hp ↦ by linarith [hT p hp]
    have hSum : 0 ≤ f a + ∑ p ∈ T, f p :=
      (add_nonneg ha₀ (sum_nonneg hT))
    rw [prod_insert ha, sum_insert ha]
    calc
      (1 + f a) * (∏ p ∈ T, (1 + f p)) - 1 =
          (∏ p ∈ T, (1 + f p)) * f a + ((∏ p ∈ T, (1 + f p)) - 1) := by ring
      _ ≤ (∏ p ∈ T, (1 + f p)) * f a + (∏ p ∈ T, (1 + f p)) * ∑ p ∈ T, f p :=
        (add_le_add_right (ih hT) _)
      _ = (∏ p ∈ T, (1 + f p)) * (f a + ∑ p ∈ T, f p) := by ring
      _ ≤ ((1 + f a) * ∏ p ∈ T, (1 + f p)) * (f a + ∑ p ∈ T, f p) :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hProd (by linarith)) hSum

private lemma primeFactors_sum_le (Q P : Finset ℕ)
    (hQ : ∀ q ∈ Q, Squarefree q ∧ q.primeFactors ⊆ P)
    (hP : ∀ p ∈ P, 0 ≤ cube p)
    (Good : Finset ℕ → Prop) [DecidablePred Good]
    (hGood : ∀ q ∈ Q, Good q.primeFactors) :
    (∑ q ∈ Q, diag q) ≤ ∑ S ∈ P.powerset.filter Good, weight S := by
  classical
  calc
    ∑ q ∈ Q, diag q = ∑ S ∈ Q.image Nat.primeFactors, weight S := by
      symm
      refine sum_image ?_
      intro q hq m hm hqm
      have h := congrArg (fun S : Finset ℕ ↦ ∏ p ∈ S, p) hqm
      simpa only [Nat.prod_primeFactors_of_squarefree (hQ q hq).1,
        Nat.prod_primeFactors_of_squarefree (hQ m hm).1] using h
    _ ≤ ∑ S ∈ P.powerset.filter Good, weight S := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro S hS
        obtain ⟨q, hq, rfl⟩ := mem_image.mp hS
        exact mem_filter.mpr ⟨mem_powerset.mpr (hQ q hq).2, hGood q hq⟩
      · intro S hS _
        exact prod_nonneg fun p hp ↦ hP p ((mem_powerset.mp (mem_filter.mp hS).1) hp)

private lemma tailPowerset_le (P : Finset ℕ) (y k : ℕ) (hy : 1 ≤ y)
    (hP : P ⊆ Ioc 1 k) :
    (∑ S ∈ P.powerset.filter (fun S ↦ ∃ p ∈ S, y < p), weight S)
      ≤ (Real.exp 2 * 2) / (y : ℝ)^2 := by
  classical
  let bad : Finset ℕ → Prop := fun S ↦ ∃ p ∈ S, y < p
  let low := P.filter (fun p ↦ p ≤ y)
  let high := P.filter (fun p ↦ y < p)
  let W (A : Finset ℕ) := ∏ p ∈ A, (1 + cube p)
  have hP₀ : ∀ p ∈ P, 0 ≤ cube p :=
    fun p hp ↦ cube_nonneg_on_Ioc (by decide) (hP hp)
  have hLow : P.powerset.filter (fun S ↦ ¬ bad S) = low.powerset := by
    ext S
    simp only [low, bad, mem_filter, mem_powerset, not_exists, not_and, not_lt]
    constructor
    · rintro ⟨hS, hyS⟩ p hp
      exact mem_filter.mpr ⟨hS hp, hyS p hp⟩
    · intro hS
      exact ⟨fun p hp ↦ (mem_filter.mp (hS hp)).1,
        fun p hp ↦ (mem_filter.mp (hS hp)).2⟩
  have hW : W low * W high = W P := by
    simpa only [W, low, high, not_le] using
      (Finset.prod_filter_mul_prod_filter_not P (fun p ↦ p ≤ y) (fun p ↦ 1 + cube p))
  have hBal : (∑ S ∈ P.powerset.filter bad, weight S) + W low = W P := by
    have heq := sum_filter_add_sum_filter_not P.powerset bad weight
    rw [hLow] at heq
    simpa only [W, weight, ← Finset.prod_one_add] using heq
  have hLow₀ : 0 ≤ W low :=
    prod_nonneg fun p hp ↦ by linarith [hP₀ p (mem_filter.mp hp).1]
  have hHigh₀ : ∀ p ∈ high, 0 ≤ cube p := fun p hp ↦ hP₀ p (mem_filter.mp hp).1
  have hHigh : high ⊆ Ioc y k := by
    intro p hp
    exact mem_Ioc.mpr ⟨(mem_filter.mp hp).2, (mem_Ioc.mp (hP (mem_filter.mp hp).1)).2⟩
  change (∑ S ∈ P.powerset.filter bad, weight S) ≤ _
  calc
    ∑ S ∈ P.powerset.filter bad, weight S = W low * (W high - 1) := by
      linarith only [hW, hBal, mul_sub (W low) (W high) 1, mul_one (W low)]
    _ ≤ W low * (W high * ∑ p ∈ high, cube p) :=
      mul_le_mul_of_nonneg_left (prod_sub_one_le high cube hHigh₀) hLow₀
    _ = W P * ∑ p ∈ high, cube p := by rw [← mul_assoc, hW]
    _ ≤ Real.exp 2 * (2 / (y : ℝ)^2) :=
      mul_le_mul (prod_bound P k hP) (sum_cube_le high y k hy hHigh)
        (sum_nonneg hHigh₀) (by positivity)
    _ = _ := by ring

/-- Uniform diagonal mass bound for any set of squarefree denominators up to k. -/
theorem sum_diag_le (Q : Finset ℕ) (k : ℕ)
    (hQ : ∀ q ∈ Q, Squarefree q ∧ q ≤ k) :
    ∑ q ∈ Q, diag q ≤ Real.exp 2 := by
  classical
  let P := Ioc 1 k
  have hF : ∀ q ∈ Q, Squarefree q ∧ q.primeFactors ⊆ P := by
    intro q hq
    refine ⟨(hQ q hq).1, fun p hp ↦ mem_Ioc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).one_lt, ?_⟩⟩
    exact (Nat.le_of_mem_primeFactors hp).trans (hQ q hq).2
  have h := primeFactors_sum_le Q P hF
    (fun p hp ↦ cube_nonneg_on_Ioc (by decide) hp) (fun _ ↦ True) (fun _ _ ↦ trivial)
  calc
    ∑ q ∈ Q, diag q ≤ ∑ S ∈ P.powerset, weight S := by simpa using h
    _ = ∏ p ∈ P, (1 + cube p) := (Finset.prod_one_add P).symm
    _ ≤ Real.exp 2 := prod_bound P k Subset.rfl

/-- Uniform diagonal mass of nonsmooth squarefree denominators above a prime cutoff. -/
theorem sum_diag_tail_le (Q : Finset ℕ) (y k : ℕ) (hy : 1 ≤ y)
    (hQ : ∀ q ∈ Q, Squarefree q ∧ q ≤ k ∧ ∃ p ∈ q.primeFactors, y < p) :
    ∑ q ∈ Q, diag q ≤ (Real.exp 2 * 2) / (y : ℝ)^2 := by
  classical
  let P := Ioc 1 k
  have hF : ∀ q ∈ Q, Squarefree q ∧ q.primeFactors ⊆ P := by
    intro q hq
    refine ⟨(hQ q hq).1, fun p hp ↦ mem_Ioc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).one_lt, ?_⟩⟩
    exact (Nat.le_of_mem_primeFactors hp).trans (hQ q hq).2.1
  exact (primeFactors_sum_le Q P hF
    (fun p hp ↦ cube_nonneg_on_Ioc (by decide) hp) (fun S ↦ ∃ p ∈ S, y < p)
    (fun q hq ↦ (hQ q hq).2.2)).trans (tailPowerset_le P y k hy Subset.rfl)

theorem diag_nonneg (q : ℕ) : 0 ≤ diag q :=
  prod_nonneg fun p hp ↦ cube_nonneg p (Nat.prime_of_mem_primeFactors hp).two_le

/-- A uniform bound on the coefficients factors out of the diagonal energy. -/
theorem weighted_diag_le (Q : Finset ℕ) (w : ℕ → ℝ) (a : ℝ)
    (hw : ∀ q ∈ Q, |w q| ≤ a) :
    (∑ q ∈ Q, (w q)^2 * diag q) ≤ a^2 * ∑ q ∈ Q, diag q := by
  rw [mul_sum]
  exact sum_le_sum fun q hq ↦
    mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.mp (hw q hq)).1 (abs_le.mp (hw q hq)).2)
      (diag_nonneg q)

end GoldbachReflectedDiagonal


/-!
The row decomposition uses the checked
`SharpScoreReindex.score_reindex` in `ReflectedMajorSharpFloor`.
-/

namespace GoldbachReflectedRows

open Finset GoldbachReflectedCRT
open SharpScoreReindex (oddPrimes odd_characterization)
open scoped BigOperators

def oddSquarefreeUpTo (k : ℕ) : Finset ℕ := by
  classical
  exact (Icc 1 k).filter fun q => Squarefree q ∧ ¬ 2 ∣ q

theorem mem_oddSquarefreeUpTo {k q : ℕ} :
    q ∈ oddSquarefreeUpTo k ↔ 1 ≤ q ∧ q ≤ k ∧ Squarefree q ∧ ¬ 2 ∣ q := by
  classical
  simp only [oddSquarefreeUpTo, mem_filter, mem_Icc, and_assoc]

private theorem primes_product_squarefree {t : Finset ℕ} (ht : ∀ p ∈ t, p.Prime) :
    Squarefree (∏ p ∈ t, p) := by
  have h := Nat.squarefree_prod_primeFactors (∏ p ∈ t, p)
  simpa only [Nat.primeFactors_prod ht] using h

private theorem prime_of_subset_oddPrimes {k : ℕ} {t : Finset ℕ}
    (ht : t ⊆ oddPrimes k) : ∀ p ∈ t, p.Prime :=
  fun _ hp => (odd_characterization.mp (ht hp)).1

private theorem product_mem_oddSquarefreeUpTo {k y : ℕ} {t : Finset ℕ}
    (ht : t ⊆ oddPrimes y) (hle : (∏ p ∈ t, p) ≤ k) :
    (∏ p ∈ t, p) ∈ oddSquarefreeUpTo k := by
  have hprime := prime_of_subset_oddPrimes ht
  have hpos : 0 < ∏ p ∈ t, p := prod_pos fun p hp => (hprime p hp).pos
  refine mem_oddSquarefreeUpTo.mpr ⟨hpos, hle, primes_product_squarefree hprime, ?_⟩
  intro hdiv
  have hmem := Nat.prime_two.mem_primeFactors hdiv hpos.ne'
  rw [Nat.primeFactors_prod hprime] at hmem
  have hgt := (odd_characterization.mp (ht hmem)).2.1
  omega

private theorem primeFactors_subset {k q : ℕ} (hq : q ∈ oddSquarefreeUpTo k) :
    q.primeFactors ⊆ oddPrimes k := by
  obtain ⟨_, hqk, _, ho⟩ := mem_oddSquarefreeUpTo.mp hq
  intro p hp
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := fun he => ho (he ▸ Nat.dvd_of_mem_primeFactors hp)
  exact odd_characterization.mpr
    ⟨hprime, lt_of_le_of_ne hprime.two_le (Ne.symm hp2),
      (Nat.le_of_mem_primeFactors hp).trans hqk⟩

private theorem sum_oddPrimeProducts (k : ℕ) (f : ℕ → ℝ) :
    (∑ t ∈ (oddPrimes k).powerset, if (∏ p ∈ t, p) ≤ k then f (∏ p ∈ t, p) else 0) =
      ∑ q ∈ oddSquarefreeUpTo k, f q := by
  classical
  rw [← sum_filter]
  refine sum_bij' (fun t _ => ∏ p ∈ t, p) (fun q _ => q.primeFactors) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨ht, hle⟩ := mem_filter.mp ht
    exact product_mem_oddSquarefreeUpTo (mem_powerset.mp ht) hle
  · intro q hq
    obtain ⟨_, hqk, hsq, _⟩ := mem_oddSquarefreeUpTo.mp hq
    exact mem_filter.mpr ⟨mem_powerset.mpr (primeFactors_subset hq),
      by rwa [Nat.prod_primeFactors_of_squarefree hsq]⟩
  · intro t ht
    exact Nat.primeFactors_prod
      (prime_of_subset_oddPrimes (mem_powerset.mp (mem_filter.mp ht).1))
  · intro q hq
    exact Nat.prod_primeFactors_of_squarefree (mem_oddSquarefreeUpTo.mp hq).2.2.1
  · intro t ht
    rfl

noncomputable def rowWeight (k q : ℕ) : ℝ := 1 + if 2*q ≤ k then 1 else 0

theorem row_eq_sum (k u : ℕ) :
    SharpAssembly.row k (2*u) =
      ∑ q ∈ oddSquarefreeUpTo k, rowWeight k q * squarefreeRow q.primeFactors u := by
  classical
  by_cases hk : 2 ≤ k
  · have he : Even (2*u) := even_iff_two_dvd.mpr (dvd_mul_right 2 u)
    unfold SharpAssembly.row
    rw [SharpScoreReindex.score_reindex hk he]
    unfold SharpFloorComparison.score
    rw [SharpScoreReindex.partition, ← sum_add_distrib, ← sum_oddPrimeProducts]
    apply sum_congr rfl
    intro t ht
    have hsub := mem_powerset.mp ht
    have hprime := prime_of_subset_oddPrimes hsub
    have hl : (∏ p ∈ t, SharpFloorComparison.localFactor (SharpScoreReindex.good k (2*u)) p) =
        squarefreeRow t u := by
      unfold squarefreeRow
      apply prod_congr rfl
      intro p hp
      obtain ⟨hpr, htwo, _⟩ := odd_characterization.mp (hsub hp)
      have hn : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) htwo
      have hd : p ∣ 2*u ↔ p ∣ u := by rw [hpr.dvd_mul, or_iff_right hn]
      simp [SharpFloorComparison.localFactor, SharpScoreReindex.good, localFactor,
        Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc.badFactor,
        hsub hp, hd]
    rw [hl]
    rw [Nat.primeFactors_prod hprime]
    let q := ∏ p ∈ t, p
    change squarefreeRow t u * SharpScoreReindex.weight k (1*q) +
      squarefreeRow t u * SharpScoreReindex.weight k (2*q) =
        if q ≤ k then rowWeight k q * squarefreeRow t u else 0
    by_cases hq : q ≤ k
    · simp only [rowWeight, SharpScoreReindex.weight, one_mul, hq, ite_true, mul_one]
      split_ifs <;> ring
    · have h2q : ¬ 2*q ≤ k := by omega
      simp [SharpScoreReindex.weight, hq, h2q]
  · have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl
    · simp [SharpAssembly.row, oddSquarefreeUpTo]
    · have h : oddSquarefreeUpTo 1 = {1} := by
        ext q
        simp only [mem_oddSquarefreeUpTo, mem_singleton]
        constructor
        · rintro ⟨hlo, hhi, _, _⟩
          exact le_antisymm hhi hlo
        · rintro rfl
          exact ⟨le_rfl, le_rfl, squarefree_one, by decide⟩
      norm_num [SharpAssembly.row, h, rowWeight, squarefreeRow,
        Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc.coefficient_one]

def smallPrimorial (y : ℕ) : ℕ := ∏ p ∈ oddPrimes y, p

theorem smallPrimorial_pos (y : ℕ) : 0 < smallPrimorial y :=
  prod_pos fun _ hp => (odd_characterization.mp hp).1.pos

theorem model_eq_sum (y k u : ℕ) (hk : smallPrimorial y ≤ k) :
    2 * ∏ p ∈ oddPrimes y, (1 + localFactor p u) =
      ∑ q ∈ oddSquarefreeUpTo k,
        if q ∣ smallPrimorial y then 2 * squarefreeRow q.primeFactors u else 0 := by
  classical
  rw [prod_one_add, mul_sum, ← sum_filter]
  refine sum_bij' (fun t _ => ∏ p ∈ t, p) (fun q _ => q.primeFactors) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have hsub := mem_powerset.mp ht
    have hdiv : (∏ p ∈ t, p) ∣ smallPrimorial y :=
      prod_dvd_prod_of_subset _ _ id hsub
    exact mem_filter.mpr ⟨product_mem_oddSquarefreeUpTo hsub
      ((Nat.le_of_dvd (smallPrimorial_pos y) hdiv).trans hk), hdiv⟩
  · intro q hq
    have hsub := Nat.primeFactors_mono (mem_filter.mp hq).2 (smallPrimorial_pos y).ne'
    unfold smallPrimorial at hsub
    rw [Nat.primeFactors_prod (fun p hp => (odd_characterization.mp hp).1)] at hsub
    exact mem_powerset.mpr hsub
  · intro t ht
    exact Nat.primeFactors_prod (prime_of_subset_oddPrimes (mem_powerset.mp ht))
  · intro q hq
    exact Nat.prod_primeFactors_of_squarefree
      (mem_oddSquarefreeUpTo.mp (mem_filter.mp hq).1).2.2.1
  · intro t ht
    rw [Nat.primeFactors_prod (prime_of_subset_oddPrimes (mem_powerset.mp ht))]
    rfl


theorem dvd_smallPrimorial_iff {q y : ℕ} (hq : Squarefree q) :
    q ∣ smallPrimorial y ↔ q.primeFactors ⊆ oddPrimes y := by
  have h := Nat.prod_primeFactors_dvd_iff (n := q) (smallPrimorial_pos y).ne'
  rw [Nat.prod_primeFactors_of_squarefree hq] at h
  change _ ↔ q.primeFactors ⊆ (∏ p ∈ oddPrimes y, p).primeFactors at h
  rwa [Nat.primeFactors_prod (fun p hp => (odd_characterization.mp hp).1)] at h

theorem exists_large_primeFactor {q k y : ℕ} (hq : q ∈ oddSquarefreeUpTo k)
    (hn : ¬ q ∣ smallPrimorial y) : ∃ p ∈ q.primeFactors, y < p := by
  by_contra! h
  obtain ⟨_, _, hsq, hodd⟩ := mem_oddSquarefreeUpTo.mp hq
  apply hn
  rw [dvd_smallPrimorial_iff hsq]
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := fun he => hodd (he ▸ Nat.dvd_of_mem_primeFactors hp)
  exact odd_characterization.mpr
    ⟨hpr, lt_of_le_of_ne hpr.two_le (Ne.symm hp2), h p hp⟩

theorem finite_model_eq (y u : ℕ) (hu : u ≠ 0) :
    2 * ∏ p ∈ oddPrimes y, (1 + localFactor p u) =
      (2 * ∏ p ∈ oddPrimes y, (1 - 1 / ((p : ℝ) - 1)^2)) *
        ∏ p ∈ (2*u).primeFactors.filter (fun p => 2 < p ∧ p ≤ y), (1 + 1 / ((p : ℝ) - 2)) := by
  classical
  have hu₂ : 2*u ≠ 0 := Nat.mul_ne_zero (by decide) hu
  have hsets : (2*u).primeFactors.filter (fun p => 2 < p ∧ p ≤ y) =
      (oddPrimes y).filter (fun p => p ∣ u) := by
    ext p
    simp only [mem_filter, Nat.mem_primeFactors_of_ne_zero hu₂,
      odd_characterization]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨hp, hd⟩, hlt, hle⟩
      have hn : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) hlt
      exact ⟨⟨hp, hlt, hle⟩, (hp.dvd_mul.mp hd).resolve_left hn⟩
    · rintro ⟨⟨hp, hlt, hle⟩, hd⟩
      exact ⟨⟨hp, hp.dvd_mul.mpr (Or.inr hd)⟩, hlt, hle⟩
  rw [hsets, prod_filter, mul_assoc, ← prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro p hp
  by_cases h : p ∣ u
  · have hp' : (2 : ℝ) < p := by exact_mod_cast (odd_characterization.mp hp).2.1
    have h₁ : (p : ℝ) - 1 ≠ 0 := by linarith
    have h₂ : (p : ℝ) - 2 ≠ 0 := by linarith
    simp only [localFactor, h, ite_true]
    field_simp [h₁, h₂]
    ring
  · simp [localFactor, h, sub_eq_add_neg]

end GoldbachReflectedRows

namespace GoldbachReflectedMeanSquare

open Finset Filter GoldbachReflectedBand GoldbachReflectedTransfer
open GoldbachReflectedRows GoldbachReflectedEuler GoldbachReflectedDiagonal
open scoped Topology

noncomputable section

def model (y m : ℕ) : ℝ :=
  2 * (∏' p : ℕ, factor p) * ∏ p ∈ m.primeFactors.filter (fun p => 2 < p ∧ p ≤ y),
    (1+1/((p:ℝ)-2))

def differenceWeight (k y q : ℕ) : ℝ :=
  rowWeight k q - if q ∣ smallPrimorial y then 2*tail y else 0

private theorem abs_weight_le_two (k y q : ℕ) : |differenceWeight k y q| ≤ 2 := by
  have hlo := tail_nonneg y
  have hhi := tail_le_one y
  unfold differenceWeight rowWeight
  apply abs_le.mpr
  split_ifs <;> constructor <;> linarith only [hlo, hhi]

private theorem abs_weight_smooth {y k q : ℕ} (hy : 2 ≤ y)
    (hk : 2 * smallPrimorial y ≤ k) (hq : q ∣ smallPrimorial y) :
    |differenceWeight k y q| ≤ 4/(y : ℝ) := by
  have hqk := (Nat.mul_le_mul_left 2 (Nat.le_of_dvd (smallPrimorial_pos y) hq)).trans hk
  have hhi := tail_le_one y
  rw [differenceWeight, ite_eq_left hq, rowWeight, ite_eq_left hqk, abs_of_nonneg (by linarith)]
  have htail := one_sub_tail_le y hy
  linarith only [htail, show (4 : ℝ)/(y : ℝ) = 2 * (2/(y : ℝ)) by ring]

private theorem difference_eq_sum {y k u : ℕ} (hu : u ≠ 0) (hk : smallPrimorial y ≤ k) :
    SharpAssembly.row k (2*u) - model y (2*u) =
      ∑ q ∈ oddSquarefreeUpTo k, differenceWeight k y q *
        GoldbachReflectedCRT.squarefreeRow q.primeFactors u := by
  have hS : ((range (y+1)).filter (fun p => Nat.Prime p ∧ 2<p)) =
      SharpScoreReindex.oddPrimes y := by
    ext p
    simp only [mem_filter, mem_range, Nat.lt_succ_iff, SharpScoreReindex.odd_characterization]
    tauto
  have hFin : (∏ p ∈ SharpScoreReindex.oddPrimes y, factor p) =
      ∏ p ∈ SharpScoreReindex.oddPrimes y, (1 - 1 / ((p : ℝ)-1)^2) := by
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨hprime, htwo, _⟩ := SharpScoreReindex.odd_characterization.mp hp
    simp [factor, hprime, htwo]
  have hmodel : model y (2*u) = tail y *
      (2 * ∏ p ∈ SharpScoreReindex.oddPrimes y, (1 + GoldbachReflectedCRT.localFactor p u)) := by
    rw [model, tprod_factor_eq_prefix_mul_tail, hS, hFin, finite_model_eq y u hu]
    ring
  rw [row_eq_sum, hmodel, model_eq_sum y k u hk, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  unfold differenceWeight
  split_ifs <;> ring

private theorem diagonal_bound {y k : ℕ} (hy : 2 ≤ y)
    (hk : 2 * smallPrimorial y ≤ k) :
    (∑ q ∈ oddSquarefreeUpTo k, (differenceWeight k y q)^2 * diag q) ≤
      (24 * Real.exp 2) / (y : ℝ)^2 := by
  let Q := oddSquarefreeUpTo k
  let S := Q.filter (fun q => q ∣ smallPrimorial y)
  let L := Q.filter (fun q => ¬ q ∣ smallPrimorial y)
  let w := differenceWeight k y
  have hyR : 0 < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hS (q : ℕ) (hq : q ∈ S) : Squarefree q ∧ q ≤ k := by
    obtain ⟨_, hqk, hs, _⟩ := mem_oddSquarefreeUpTo.mp (Finset.mem_filter.mp hq).1
    exact ⟨hs, hqk⟩
  have hL (q : ℕ) (hq : q ∈ L) : Squarefree q ∧ q ≤ k ∧ ∃ p ∈ q.primeFactors, y < p := by
    obtain ⟨hQ, hbad⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, hqk, hsq, _⟩ := mem_oddSquarefreeUpTo.mp hQ
    exact ⟨hsq, hqk, exists_large_primeFactor hQ hbad⟩
  have hSbound : (∑ q ∈ S, (w q)^2 * diag q) ≤ (4/(y : ℝ))^2 * Real.exp 2 :=
    (weighted_diag_le S w _ (fun _ hq => abs_weight_smooth hy hk (Finset.mem_filter.mp hq).2)).trans
      (mul_le_mul_of_nonneg_left (sum_diag_le S k hS) (sq_nonneg _))
  have hLbound : (∑ q ∈ L, (w q)^2 * diag q) ≤ (2 : ℝ)^2*(Real.exp 2*2/(y : ℝ)^2) :=
    (weighted_diag_le L w _ (fun q _ => abs_weight_le_two k y q)).trans
      (mul_le_mul_of_nonneg_left (sum_diag_tail_le L y k (by omega) hL) (sq_nonneg _))
  change (∑ q ∈ Q, (w q)^2 * diag q) ≤ _
  calc
    _ = (∑ q ∈ S, (w q)^2 * diag q) + (∑ q ∈ L, (w q)^2 * diag q) :=
      (Finset.sum_filter_add_sum_filter_not Q (fun q => q ∣ smallPrimorial y)
        (fun q => (w q)^2 * diag q)).symm
    _ ≤ _ := add_le_add hSbound hLbound
    _ = _ := by field_simp [hyR.ne']; ring

theorem eventual_meanSquare (y : ℕ) (hy : 3 ≤ y) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ band N, (normalized N m-model y m)^2) / ((band N).card : ℝ) ≤
        (48*Real.exp 2+4)/(y : ℝ)^2 := by
  have hyR : 0 < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  filter_upwards [eventually_ge_atTop (24 : ℕ), eventually_cap_ge (2 * smallPrimorial y),
    eventually_interval_error_le (1/(y : ℝ)^2) (by positivity),
    eventually_uniform (1/(y : ℝ)) (by positivity)] with N hN hk herror htransfer
  let k := cap N
  let F := halfBand N
  let Q := oddSquarefreeUpTo k
  let w := differenceWeight k y
  let rr := fun u => SharpAssembly.row k (2*u) - model y (2*u)
  have hpK : smallPrimorial y ≤ k := by omega
  have hCardNat : N ≤ 24*F.card := halfBand_card_ge N hN
  have hCard : 0 < (F.card : ℝ) := by exact_mod_cast (show 0 < F.card by omega)
  have hu0 (u : ℕ) (hu : u ∈ F) : u ≠ 0 := by
    have hl := (Finset.mem_Icc.mp hu).1
    dsimp only [lower] at hl
    omega
  have hsum :
      (∑ u ∈ F, (rr u)^2) =
      ∑ u ∈ F, (∑ q ∈ Q, w q*GoldbachReflectedCRT.squarefreeRow q.primeFactors u)^2 := by
    apply Finset.sum_congr rfl
    intro u hu
    dsimp [rr]
    rw [difference_eq_sum (hu0 u hu) hpK]
  have hweighted := GoldbachReflectedCRT.weighted_square_average Q w k (lower N) (upper N)
    (lower_le_upper N hN) (fun q hq => ⟨(mem_oddSquarefreeUpTo.mp hq).2.1,
      (mem_oddSquarefreeUpTo.mp hq).2.2.1⟩)
    (fun q _ => abs_weight_le_two k y q)
  change ((∑ u ∈ F, (∑ q ∈ Q, w q*GoldbachReflectedCRT.squarefreeRow q.primeFactors u)^2) /
    (F.card : ℝ)) ≤ (∑ q ∈ Q, (w q)^2 * diag q) + 8*(k:ℝ)^4/(F.card:ℝ) at hweighted
  have hrowBound : ((∑ u ∈ F, (rr u)^2) / (F.card : ℝ)) ≤
      (24*Real.exp 2+1)/(y : ℝ)^2 := by
    rw [hsum]
    calc
      _ ≤ _ := hweighted
      _ ≤ (24*Real.exp 2)/(y : ℝ)^2 + 1/(y : ℝ)^2 :=
        (add_le_add (diagonal_bound (by omega) hk) herror)
      _ = _ := by ring
  have hterm (u : ℕ) (hu : u ∈ F) :
      (normalized N (2*u)-model y (2*u))^2 ≤ 2*(1/(y:ℝ))^2+2*(rr u)^2 := by
    have hmem : 2*u ∈ band N := by
      rw [band_eq_map]
      exact Finset.mem_map.mpr ⟨u,hu,rfl⟩
    let e := normalized N (2*u)-SharpAssembly.row k (2*u)
    have habs : |e| ≤ 1/(y:ℝ) := htransfer (2*u) hmem
    have he : e^2 ≤ (1/(y:ℝ))^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg e) habs 2
    have heq : normalized N (2*u)-model y (2*u) = e + rr u := by
      dsimp [e, rr]
      ring
    rw [heq]
    nlinarith only [he, sq_nonneg (e - rr u)]
  rw [sum_band, band_card]
  change ((∑ u ∈ F, (normalized N (2*u)-model y (2*u))^2) / (F.card : ℝ)) ≤ _
  calc
    _ ≤ (∑ u ∈ F, (2*(1/(y:ℝ))^2+2*(rr u)^2)) / (F.card : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum hterm) hCard.le
    _ = 2/(y : ℝ)^2 + 2*((∑ u ∈ F, (rr u)^2)/(F.card : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
      field_simp [hCard.ne', hyR.ne']
    _ ≤ 2/(y : ℝ)^2 + 2*((24*Real.exp 2+1)/(y : ℝ)^2) :=
      (add_le_add_right (mul_le_mul_of_nonneg_left hrowBound (by norm_num)) _)
    _ = _ := by ring

end
end GoldbachReflectedMeanSquare



namespace GoldbachReflectedShiftBand

open Finset Filter GoldbachReflectedBand
open scoped BigOperators Topology

def shiftedBand (N h : ℕ) : Finset ℕ := by
  letI (m : ℕ) : Decidable (bandPred N (m + 2*h)) := by
    unfold bandPred
    infer_instance
  exact (band N).filter fun m => bandPred N (m + 2*h)

def shiftedHalfBand (N h : ℕ) : Finset ℕ :=
  Icc (lower N) (upper N - h)

theorem mem_band_iff {N m : ℕ} : m ∈ band N ↔ bandPred N m := by
  simp only [band, bandPred, mem_filter, mem_Icc]
  constructor
  · exact And.right
  · rintro ⟨hlo, hhi, hev⟩
    exact ⟨⟨by omega, by omega⟩, hlo, hhi, hev⟩

theorem mem_shiftedBand {N h m : ℕ} :
    m ∈ shiftedBand N h ↔ m ∈ band N ∧ m + 2*h ∈ band N := by
  simp only [shiftedBand, mem_filter]
  rw [mem_band_iff (m := m + 2*h)]

theorem shiftedBand_eq_map (N h : ℕ) (hh : h ≤ upper N) :
    shiftedBand N h = (shiftedHalfBand N h).map double := by
  ext m
  simp only [shiftedBand, mem_filter]
  rw [band_eq_map N]
  constructor
  · rintro ⟨hm, hs⟩
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hm
    obtain ⟨hlo, _⟩ := mem_Icc.mp hu
    change bandPred N (2*u + 2*h) at hs
    obtain ⟨_, hhi, _⟩ := hs
    refine mem_map.mpr ⟨u, mem_Icc.mpr ⟨hlo, ?_⟩, rfl⟩
    dsimp only [upper] at hh ⊢
    omega
  · intro hm
    obtain ⟨u, hu, rfl⟩ := mem_map.mp hm
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hu
    dsimp only [upper] at hhi hh
    refine ⟨mem_map.mpr ⟨u, mem_Icc.mpr ⟨hlo, ?_⟩, rfl⟩, ?_⟩
    · dsimp only [upper]
      omega
    · change bandPred N (2*u + 2*h)
      dsimp only [bandPred, lower] at *
      exact ⟨by omega, by omega, ⟨u+h, by omega⟩⟩

theorem shiftedBand_card (N h : ℕ) (hh : h ≤ upper N) :
    (shiftedBand N h).card = (shiftedHalfBand N h).card := by
  rw [shiftedBand_eq_map N h hh, card_map]

theorem sum_shiftedBand (N h : ℕ) (hh : h ≤ upper N) (f : ℕ → ℝ) :
    (∑ m ∈ shiftedBand N h, f m) = ∑ u ∈ shiftedHalfBand N h, f (2*u) := by
  rw [shiftedBand_eq_map N h hh, sum_map]
  rfl

theorem shiftedHalfBand_members {N h u : ℕ} (hN : 0 < N) (hh : h ≤ upper N)
    (hu : u ∈ shiftedHalfBand N h) :
    u ≠ 0 ∧ u+h ≠ 0 ∧ 2*u ∈ band N ∧ 2*(u+h) ∈ band N := by
  have hm : 2*u ∈ shiftedBand N h := by
    rw [shiftedBand_eq_map N h hh]
    exact mem_map.mpr ⟨u, hu, rfl⟩
  obtain ⟨h₁, h₂⟩ := mem_shiftedBand.mp hm
  have hlo : lower N ≤ u := (mem_Icc.mp hu).1
  dsimp only [lower] at hlo
  exact ⟨by omega, by omega, h₁, by simpa only [Nat.mul_add] using h₂⟩

private theorem mul_shift_le {N h : ℕ} (hN : 384 ≤ N) (hh : h^3 ≤ N) : 48*h ≤ N := by
  by_cases hsmall : h < 8
  · omega
  · have h₈ : 8 ≤ h := by omega
    have hsq : 48 ≤ h*h :=
      (show 48 ≤ 8*8 by decide).trans (Nat.mul_le_mul h₈ h₈)
    calc
      48*h ≤ h*h*h := Nat.mul_le_mul_right h hsq
      _ = h^3 := by ring
      _ ≤ N := hh

theorem shift_le_upper {N h : ℕ} (hN : 384 ≤ N) (hh : h^3 ≤ N) : h ≤ upper N := by
  have hbound := mul_shift_le hN hh
  dsimp only [upper]
  omega

theorem halfBand_card_le_twice_shiftedHalfBand_card {N h : ℕ}
    (hN : 384 ≤ N) (hh : h^3 ≤ N) :
    (halfBand N).card ≤ 2 * (shiftedHalfBand N h).card := by
  have hbound := mul_shift_le hN hh
  have hu := shift_le_upper hN hh
  have hcard := halfBand_card_ge N (by omega)
  simp only [halfBand, shiftedHalfBand, Nat.card_Icc] at hcard ⊢
  omega

theorem band_card_le_twice_shiftedBand_card {N h : ℕ} (hN : 384 ≤ N) (hh : h^3 ≤ N) :
    (band N).card ≤ 2 * (shiftedBand N h).card := by
  rw [band_card, shiftedBand_card N h (shift_le_upper hN hh)]
  exact halfBand_card_le_twice_shiftedHalfBand_card hN hh

theorem shiftedHalfBand_nonempty {N h : ℕ} (hN : 384 ≤ N) (hh : h^3 ≤ N) :
    (shiftedHalfBand N h).Nonempty := by
  apply card_pos.mp
  have hcard := halfBand_card_ge N (by omega)
  have hcomp := halfBand_card_le_twice_shiftedHalfBand_card hN hh
  omega

theorem eventually_log_power_over_shifted_card_le (d : ℕ) {C ε : ℝ} (hC : 0 ≤ C)
    (hε : 0 < ε) : ∀ᶠ N : ℕ in atTop, ∀ h : ℕ, h^3 ≤ N →
      C * (cap N : ℝ)^d / ((shiftedHalfBand N h).card : ℝ) ≤ ε := by
  have hlim := (log_power_over_N d).const_mul (48*C)
  rw [mul_zero] at hlim
  filter_upwards [eventually_ge_atTop (384 : ℕ), hlim.eventually (gt_mem_nhds hε)] with N hN hterm
  intro h hh
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard : N ≤ 48 * (shiftedHalfBand N h).card := by
    have hfull := halfBand_card_ge N (by omega)
    have hshift := halfBand_card_le_twice_shiftedHalfBand_card hN hh
    omega
  have hcardR : (N : ℝ) ≤ 48 * ((shiftedHalfBand N h).card : ℝ) := by exact_mod_cast hcard
  calc
    _ ≤ C * (cap N : ℝ)^d / ((N : ℝ)/48) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hcardR])
    _ = (48*C) * ((cap N : ℝ)^d/(N : ℝ)) := by ring
    _ ≤ ε := hterm.le

end GoldbachReflectedShiftBand


namespace GoldbachReflectedShiftTransfer

open Finset

/-- Arithmetic mean, with value zero on an empty set. -/
noncomputable def avg {ι : Type*} (F : Finset ι) (f : ι → ℝ) : ℝ :=
  (∑ m ∈ F, f m) / (F.card : ℝ)

theorem avg_nonneg {ι : Type*} (F : Finset ι) (f : ι → ℝ)
    (hf : ∀ m ∈ F, 0 ≤ f m) : 0 ≤ avg F f :=
  div_nonneg (sum_nonneg hf) (Nat.cast_nonneg _)

/-- Finite-average Cauchy–Schwarz, also valid for the empty set. -/
theorem abs_avg_mul_le {ι : Type*} (F : Finset ι) (f g : ι → ℝ) :
    |avg F (fun m ↦ f m * g m)| ≤
      Real.sqrt (avg F (fun m ↦ (f m)^2)) * Real.sqrt (avg F (fun m ↦ (g m)^2)) := by
  have hf : 0 ≤ avg F (fun m ↦ (f m)^2) := avg_nonneg F _ fun m _ ↦ sq_nonneg (f m)
  have hg : 0 ≤ avg F (fun m ↦ (g m)^2) := avg_nonneg F _ fun m _ ↦ sq_nonneg (g m)
  have h := Finset.expect_mul_sq_le_sq_mul_sq F f g
  simp_rw [Finset.expect_eq_sum_div_card] at h
  rw [← Real.sqrt_mul hf]
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg hf hg)).2
  simpa only [sq_abs, avg] using h

private theorem abs_avg_mul_le_of_bounds {ι : Type*} (F : Finset ι) (f g : ι → ℝ)
    {a b : ℝ} (hf : avg F (fun m ↦ (f m)^2) ≤ a) (hg : avg F (fun m ↦ (g m)^2) ≤ b) :
    |avg F (fun m ↦ f m * g m)| ≤ Real.sqrt a * Real.sqrt b :=
  (abs_avg_mul_le F f g).trans
    (mul_le_mul (Real.sqrt_le_sqrt hf) (Real.sqrt_le_sqrt hg)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- A product average changes by at most twice the product of the error and comparison
norm bounds. The four functions can be chosen independently, including a shift. -/
theorem avg_product_transfer {ι : Type*} (F : Finset ι) (R R' P P' : ι → ℝ) (η K : ℝ)
    (hR : avg F (fun m ↦ (R m - P m)^2) ≤ η)
    (hR' : avg F (fun m ↦ (R' m - P' m)^2) ≤ η)
    (hP : avg F (fun m ↦ (P m)^2) ≤ K)
    (hNormR' : avg F (fun m ↦ (R' m)^2) ≤ K) :
    |avg F (fun m ↦ R m * R' m) - avg F (fun m ↦ P m * P' m)| ≤
      2 * Real.sqrt η * Real.sqrt K := by
  let a := avg F (fun m ↦ (R m - P m) * R' m)
  let b := avg F (fun m ↦ P m * (R' m - P' m))
  have heq : avg F (fun m ↦ R m * R' m) - avg F (fun m ↦ P m * P' m) = a + b := by
    unfold a b avg
    rw [← sub_div, ← add_div, ← sum_sub_distrib, ← sum_add_distrib]
    congr 1
    exact sum_congr rfl fun m _ ↦ by ring
  have ha : |a| ≤ Real.sqrt η * Real.sqrt K :=
    abs_avg_mul_le_of_bounds F (fun m ↦ R m - P m) R' hR hNormR'
  have hb : |b| ≤ Real.sqrt K * Real.sqrt η :=
    abs_avg_mul_le_of_bounds F P (fun m ↦ R' m - P' m) hP hR'
  calc
    _ = |a+b| := by rw [heq]
    _ ≤ |a| + |b| := abs_add_le _ _
    _ ≤ Real.sqrt η * Real.sqrt K + Real.sqrt K * Real.sqrt η := add_le_add ha hb
    _ = _ := by ring

/-- Derive a square moment bound for an approximated function from its error and model moments. -/
theorem avg_sq_le_of_approx {ι : Type*} (F : Finset ι) (R P : ι → ℝ) (η K : ℝ)
    (hR : avg F (fun m ↦ (R m - P m)^2) ≤ η)
    (hP : avg F (fun m ↦ (P m)^2) ≤ K) :
    avg F (fun m ↦ (R m)^2) ≤ 2 * (η + K) := by
  calc
    avg F (fun m ↦ (R m)^2) ≤ avg F (fun m ↦ 2 * ((R m - P m)^2 + (P m)^2)) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact sum_le_sum fun m _ ↦ by nlinarith [sq_nonneg (R m - 2 * P m)]
    _ = 2 * (avg F (fun m ↦ (R m - P m)^2) + avg F (fun m ↦ (P m)^2)) := by
      simp only [avg, ← mul_sum, sum_add_distrib, mul_div_assoc, add_div]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hR hP) (by norm_num)

/-- Restriction of a nonnegative average through any embedding into the original index set. -/
theorem avg_restrict_map_le {ι κ : Type*} (F : Finset ι) (B : Finset κ)
    (e : ι ↪ κ) (f : κ → ℝ) {c : ℝ}
    (hsub : F.map e ⊆ B) (hf : ∀ m ∈ B, 0 ≤ f m)
    (hcard : (B.card : ℝ) ≤ c * (F.card : ℝ)) :
    avg F (fun m ↦ f (e m)) ≤ c * avg B f := by
  classical
  by_cases hF : F = ∅
  · subst F
    have hB : B = ∅ := by
      apply card_eq_zero.mp
      have hcard' : (B.card : ℝ) ≤ 0 := by simpa using hcard
      exact Nat.eq_zero_of_le_zero (by exact_mod_cast hcard')
    simp [avg, hB]
  have hF' : 0 < F.card := card_pos.mpr (nonempty_iff_ne_empty.mpr hF)
  have hF₀ : 0 < (F.card : ℝ) := by exact_mod_cast hF'
  have hB₀ : 0 < (B.card : ℝ) := by
    have hle : F.card ≤ B.card := by simpa only [card_map] using card_le_card hsub
    exact_mod_cast hF'.trans_le hle
  apply (div_le_iff₀ hF₀).mpr
  calc
    ∑ m ∈ F, f (e m) = ∑ m ∈ F.map e, f m := (sum_map F e f).symm
    _ ≤ ∑ m ∈ B, f m := sum_le_sum_of_subset_of_nonneg hsub fun m hm _ ↦ hf m hm
    _ = avg B f * (B.card : ℝ) := (div_mul_cancel₀ _ hB₀.ne').symm
    _ ≤ avg B f * (c * (F.card : ℝ)) := mul_le_mul_of_nonneg_left hcard (avg_nonneg B f hf)
    _ = _ := by ring

/-- Restrict to a subset whose cardinality is at least half the original cardinality. -/
theorem avg_restrict {ι : Type*} (F B : Finset ι) (f : ι → ℝ)
    (hsub : F ⊆ B) (hf : ∀ m ∈ B, 0 ≤ f m) (hcard : B.card ≤ 2*F.card) :
    avg F f ≤ 2 * avg B f := by
  have hc : (B.card : ℝ) ≤ 2*(F.card : ℝ) := by exact_mod_cast hcard
  exact avg_restrict_map_le F B (Function.Embedding.refl ι) f (by simpa using hsub) hf hc

/-- Restrict a shifted nonnegative average while retaining the same factor of two. -/
theorem avg_restrict_shift (F B : Finset ℕ) (d : ℕ) (f : ℕ → ℝ)
    (hsub : ∀ m ∈ F, m + d ∈ B) (hf : ∀ m ∈ B, 0 ≤ f m)
    (hcard : B.card ≤ 2*F.card) :
    avg F (fun m ↦ f (m+d)) ≤ 2 * avg B f := by
  let e : ℕ ↪ ℕ := ⟨(· + d), fun _ _ h ↦ Nat.add_right_cancel h⟩
  have he : F.map e ⊆ B := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := mem_map.mp hx
    exact hsub m hm
  have hc : (B.card : ℝ) ≤ 2*(F.card : ℝ) := by exact_mod_cast hcard
  exact avg_restrict_map_le F B e f he hf hc

end GoldbachReflectedShiftTransfer


namespace GoldbachReflectedShiftEuler

open Filter Finset
open scoped Topology BigOperators

noncomputable section

/-- The local shifted factor from the frozen Euler product. -/
def factor (h p : ℕ) : ℝ :=
  if Nat.Prime p ∧ 2 < p then
    let u : ℝ := 1 / ((p : ℝ) - 2)
    1 + 2 * u / (p : ℝ) + (if p ∣ h then u ^ 2 / (p : ℝ) else 0)
  else 1

private def increment (h p : ℕ) : ℝ :=
  if Nat.Prime p ∧ 2 < p then
    let u : ℝ := 1 / ((p : ℝ) - 2)
    2 * u / (p : ℝ) + (if p ∣ h then u ^ 2 / (p : ℝ) else 0)
  else 0

private theorem factor_eq (h p : ℕ) : factor h p = 1 + increment h p := by
  by_cases hp : Nat.Prime p ∧ 2 < p <;> simp [factor, increment, hp, add_assoc]

private theorem increment_nonneg (h p : ℕ) : 0 ≤ increment h p := by
  unfold increment
  split_ifs with hp hh
  · have hpR : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p from hp.2)
    have hden : 0 ≤ (p : ℝ) - 2 := by linarith
    positivity
  · have hpR : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p from hp.2)
    have hden : 0 ≤ (p : ℝ) - 2 := by linarith
    positivity
  · rfl

private theorem increment_le (h p : ℕ) : increment h p ≤ 6 * (1 / ((p : ℝ) - 1) ^ 2) := by
  by_cases hp : Nat.Prime p ∧ 2 < p
  · have hpR : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p from hp.2)
    have hden : 0 < (p : ℝ) - 2 := by linarith
    have hpPos : 0 < (p : ℝ) := by linarith
    have hpOne : 0 < (p : ℝ) - 1 := by linarith
    let u : ℝ := 1 / ((p : ℝ) - 2)
    have hu : 0 ≤ u := one_div_nonneg.mpr hden.le
    have hu₁ : u ≤ 1 := by
      change 1 / ((p : ℝ) - 2) ≤ 1
      apply (div_le_iff₀ hden).mpr
      linarith
    have hu₂ : u ^ 2 ≤ u := by nlinarith only [mul_nonneg hu (sub_nonneg.mpr hu₁)]
    have hlocal : (if p ∣ h then u ^ 2 / (p : ℝ) else 0) ≤ u / (p : ℝ) := by
      split_ifs
      · exact div_le_div_of_nonneg_right hu₂ hpPos.le
      · exact div_nonneg hu hpPos.le
    have hdenCompare : ((p : ℝ) - 1) ^ 2 ≤ 2 * (((p : ℝ) - 2) * (p : ℝ)) := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hpR) (show 0 ≤ (p : ℝ) + 1 by positivity)]
    calc
      increment h p = 2 * u / (p : ℝ) + (if p ∣ h then u ^ 2 / (p : ℝ) else 0) := by
        simp [increment, hp, u]
      _ ≤ 3 * u / (p : ℝ) := by
        rw [show 3 * u = 2 * u + u by ring, add_div]
        exact add_le_add le_rfl hlocal
      _ = 3 / (((p : ℝ) - 2) * (p : ℝ)) := by
        dsimp only [u]
        field_simp [hden.ne', hpPos.ne']
      _ ≤ 6 / ((p : ℝ) - 1) ^ 2 := by
        apply (div_le_div_iff₀ (mul_pos hden hpPos) (pow_pos hpOne 2)).mpr
        linarith only [hdenCompare]
      _ = 6 * (1 / ((p : ℝ) - 1) ^ 2) := by ring
  · simp [increment, hp]
    positivity

private theorem increment_sum_tail (h y : ℕ) (hy : 2 ≤ y) (s : Finset ℕ)
    (hs : ∀ p ∈ s, y < p) :
    (∑ p ∈ s, increment h p) ≤ 12 / (y : ℝ) := by
  calc
    _ ≤ ∑ p ∈ s, 6 * (1 / ((p : ℝ) - 1) ^ 2) := sum_le_sum (fun p _ => increment_le h p)
    _ = 6 * ∑ p ∈ s, (1 / ((p : ℝ) - 1) ^ 2) := (mul_sum _ _ _).symm
    _ ≤ 6 * (2 / (y : ℝ)) :=
      mul_le_mul_of_nonneg_left (GoldbachReflectedEuler.finset_square_tail y hy s hs) (by norm_num)
    _ = _ := by ring

private theorem increment_sum_le_six (h : ℕ) (s : Finset ℕ) :
    (∑ p ∈ s, increment h p) ≤ 6 := by
  calc
    _ = ∑ p ∈ s.filter (fun p => 2 < p), increment h p := by
      rw [sum_filter]
      apply sum_congr rfl
      intro p _
      by_cases hp : 2 < p
      · simp [hp]
      · simp [increment, hp]
    _ ≤ 12 / ((2 : ℕ) : ℝ) :=
      increment_sum_tail h 2 le_rfl _ (fun p hp => (mem_filter.mp hp).2)
    _ = _ := by norm_num

private theorem factor_multipliable (h : ℕ) : Multipliable (factor h) := by
  have hs : Summable (increment h) := summable_of_sum_le (increment_nonneg h) (increment_sum_le_six h)
  rw [show factor h = (fun p => 1 + increment h p) from funext (factor_eq h)]
  exact Real.multipliable_one_add_of_summable hs

def primesUpTo (y : ℕ) : Finset ℕ := (range (y + 1)).filter (fun p => Nat.Prime p ∧ 2 < p)

theorem mem_primesUpTo {y p : ℕ} : p ∈ primesUpTo y ↔ Nat.Prime p ∧ 2 < p ∧ p ≤ y := by
  simp [primesUpTo, and_comm, and_left_comm]

def prefixProduct (y h : ℕ) : ℝ := ∏ p ∈ primesUpTo y, factor h p

def product (h : ℕ) : ℝ := ∏' p : ℕ, factor h p

private theorem finset_prod_le (h : ℕ) (s : Finset ℕ) :
    (∏ p ∈ s, factor h p) ≤ Real.exp 6 := by
  simp_rw [factor_eq]
  exact (Real.prod_one_add_le_exp_sum s (increment_nonneg h)).trans
    (Real.exp_le_exp.mpr (increment_sum_le_six h s))

theorem prefix_nonneg (y h : ℕ) : 0 ≤ prefixProduct y h := by
  unfold prefixProduct
  exact prod_nonneg fun p _ => by rw [factor_eq]; linarith only [increment_nonneg h p]

theorem prefix_le (y h : ℕ) : prefixProduct y h ≤ Real.exp 6 := finset_prod_le h (primesUpTo y)

theorem product_nonneg (h : ℕ) : 0 ≤ product h := by
  exact tprod_nonneg fun p => by rw [factor_eq]; linarith only [increment_nonneg h p]

theorem product_le (h : ℕ) : product h ≤ Real.exp 6 :=
  le_of_tendsto' (factor_multipliable h).hasProd (finset_prod_le h)

private theorem finset_prod_tail (h y : ℕ) (hy : 12 ≤ y) (s : Finset ℕ)
    (hs : ∀ p ∈ s, y < p) : |(∏ p ∈ s, factor h p) - 1| ≤ 24 / (y : ℝ) := by
  have hyR : (12 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hyP : 0 < (y : ℝ) := by linarith
  have ht₀ : 0 ≤ 12 / (y : ℝ) := by positivity
  have ht₁ : 12 / (y : ℝ) ≤ 1 := (div_le_iff₀ hyP).mpr (by linarith)
  have hExp : Real.exp (12 / (y : ℝ)) - 1 ≤ 24 / (y : ℝ) := by
    have hx := Real.abs_exp_sub_one_le (x := 12 / (y : ℝ)) (by rwa [abs_of_nonneg ht₀])
    rw [abs_of_nonneg ht₀,
      abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp ht₀))] at hx
    exact hx.trans_eq (by ring)
  simp_rw [factor_eq]
  calc
    _ ≤ Real.exp (∑ p ∈ s, ‖increment h p‖) - 1 := by
      simpa only [Real.norm_eq_abs] using s.norm_prod_one_add_sub_one_le (increment h)
    _ ≤ Real.exp (12 / (y : ℝ)) - 1 := by
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (increment_nonneg h _)]
      exact sub_le_sub_right (Real.exp_le_exp.mpr (increment_sum_tail h y (by omega) s hs)) _
    _ ≤ _ := hExp

/-- The cutoff error bound is independent of the shift, including zero. -/
theorem abs_prefix_sub_product_le (y h : ℕ) (hy : 12 ≤ y) :
    |prefixProduct y h - product h| ≤ (24 * Real.exp 6) / (y : ℝ) := by
  have hlim : Tendsto (fun s : Finset ℕ => |prefixProduct y h - ∏ p ∈ s, factor h p|)
      atTop (𝓝 |prefixProduct y h - product h|) := (tendsto_const_nhds.sub (factor_multipliable h).hasProd).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop (primesUpTo y)] with s hsub
  let L := (s \ primesUpTo y).filter (fun p => y < p)
  have htail : ∏ p ∈ L, factor h p = ∏ p ∈ s \ primesUpTo y, factor h p := by
    unfold L
    rw [prod_filter]
    apply prod_congr rfl
    intro p hp
    by_cases hy : y < p
    · exact ite_eq_left hy
    · rw [ite_eq_right hy]
      have hlocal : ¬(Nat.Prime p ∧ 2 < p) := fun hp' =>
        (mem_sdiff.mp hp).2 (mem_primesUpTo.mpr ⟨hp'.1, hp'.2, Nat.le_of_not_gt hy⟩)
      simp [factor, hlocal]
  have hsplit : (∏ p ∈ s, factor h p) = prefixProduct y h * ∏ p ∈ L, factor h p := by
    rw [htail, mul_comm]
    exact (prod_sdiff hsub).symm
  rw [hsplit, show prefixProduct y h - prefixProduct y h * (∏ p ∈ L, factor h p) =
      -(prefixProduct y h * ((∏ p ∈ L, factor h p) - 1)) by ring, abs_neg, abs_mul,
      abs_of_nonneg (prefix_nonneg y h)]
  calc
    _ ≤ Real.exp 6 * (24 / (y : ℝ)) := mul_le_mul (prefix_le y h)
      (finset_prod_tail h y hy L (fun p hp => (mem_filter.mp hp).2)) (abs_nonneg _) (Real.exp_nonneg _)
    _ = _ := by ring

/-- One cutoff works simultaneously for all shifts and all higher cutoffs. -/
theorem uniform_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℕ, 3 ≤ Y ∧ ∀ y h : ℕ, Y ≤ y → |prefixProduct y h - product h| ≤ ε := by
  obtain ⟨M, hM⟩ := exists_nat_ge ((24 * Real.exp 6) / ε)
  refine ⟨max 12 M, by omega, ?_⟩
  intro y h hy
  have hy₁ : 12 ≤ y := (le_max_left _ _).trans hy
  have hy₂ : M ≤ y := (le_max_right _ _).trans hy
  have hyP : 0 < (y : ℝ) := by exact_mod_cast (show 0 < y by omega)
  have hMy : (M : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy₂
  refine (abs_prefix_sub_product_le y h hy₁).trans ((div_le_iff₀ hyP).mpr ?_)
  have := (div_le_iff₀ hε).mp (hM.trans hMy)
  linarith

end

end GoldbachReflectedShiftEuler

namespace GoldbachReflectedShiftMain

open Finset Filter GoldbachReflectedBand GoldbachReflectedTransfer
open GoldbachReflectedShiftBand GoldbachReflectedShiftTransfer
open scoped Topology

noncomputable section

def twinConstant : ℝ := ∏' p : ℕ, GoldbachReflectedEuler.factor p

def scale : ℝ := (2*twinConstant)^2

def model (y m : ℕ) : ℝ :=
  2*twinConstant * ∏ p ∈ m.primeFactors.filter (fun p => 2 < p ∧ p ≤ y), (1+1/((p:ℝ)-2))

private theorem twin_eq_tail : twinConstant = GoldbachReflectedEuler.tail 2 := by
  unfold twinConstant GoldbachReflectedEuler.tail
  apply tprod_congr
  intro p
  by_cases hp : 2 < p
  · simp [hp]
  · simp [GoldbachReflectedEuler.factor, hp]

theorem scale_le_four : scale ≤ 4 := by
  have hlo := GoldbachReflectedEuler.tail_nonneg 2
  have hhi := GoldbachReflectedEuler.tail_le_one 2
  rw [scale, twin_eq_tail]
  exact (pow_le_pow_left₀ (by positivity) (show 2*GoldbachReflectedEuler.tail 2 ≤ 2 by linarith) 2).trans
    (by norm_num)

theorem from_meanSquare
    (hMean : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 3 ≤ y →
      ∀ᶠ N : ℕ in atTop, avg (band N) (fun m => (normalized N m-model y m)^2) ≤ C/(y:ℝ)^2)
    (hModel : ∀ y : ℕ, ∀ η : ℝ, 0 < η →
      ∀ᶠ N : ℕ in atTop, ∀ h : ℕ, h^3 ≤ N →
      |avg (shiftedBand N h) (fun m => model y m * model y (m+2*h)) -
        scale * GoldbachReflectedShiftEuler.prefixProduct y h| ≤ η)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℕ, h^3 ≤ N →
      |avg (shiftedBand N h) (fun m => normalized N m * normalized N (m+2*h)) -
        scale * GoldbachReflectedShiftEuler.product h| ≤ ε := by
  obtain ⟨C, hC, hMean⟩ := hMean
  let B₀ := 4*Real.exp 6+1
  let K := 4*(C+B₀+1)
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  let Z := Real.sqrt (2*C) * Real.sqrt K
  obtain ⟨Y₁, hY₁, hEuler⟩ :=
    GoldbachReflectedShiftEuler.uniform_approx (ε := ε/12) (by positivity)
  obtain ⟨Y₂, hY₂⟩ := exists_nat_ge (6*Z/ε)
  let y := max Y₁ Y₂
  have hYA : Y₁ ≤ y := le_max_left _ _
  have hYB : Y₂ ≤ y := le_max_right _ _
  have hy : 3 ≤ y := hY₁.trans hYA
  have hyR : 0 < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
  have hyR1 : 1 ≤ (y : ℝ) := by exact_mod_cast (by omega : 1 ≤ y)
  have hsqY : 1 ≤ (y : ℝ)^2 := by nlinarith
  have hYreal : 6*Z/ε ≤ (y : ℝ) := hY₂.trans (by exact_mod_cast hYB)
  have hZsmall : 2*Z/(y:ℝ) ≤ ε/3 := by
    apply (div_le_iff₀ hyR).mpr
    have hz := (div_le_iff₀ hε).mp hYreal
    linarith only [hz, show ε/3*(y:ℝ) = (y:ℝ)*ε/3 by ring]
  filter_upwards [eventually_ge_atTop (384 : ℕ), hMean y hy,
    hModel y 1 (by norm_num), hModel y (ε/3) (by positivity)] with N hN hL2 hB hEstimate
  intro h hlarge
  let F := shiftedBand N h
  let Amb := band N
  let R := normalized N
  let P := model y
  have hF0 : shiftedBand N 0 = Amb := by
    ext m
    simp only [mem_shiftedBand, mul_zero, add_zero, and_self, Amb]
  have hPglobal : avg Amb (fun m => (P m)^2) ≤ B₀ := by
    have h0 := (abs_le.mp (hB 0 (by simp))).2
    change avg (shiftedBand N 0) (fun m => model y m * model y (m+2*0)) -
      scale * GoldbachReflectedShiftEuler.prefixProduct y 0 ≤ 1 at h0
    rw [hF0] at h0
    have h0' : avg Amb (fun m => (P m)^2) - scale * GoldbachReflectedShiftEuler.prefixProduct y 0 ≤ 1 := by
      simpa only [mul_zero, add_zero, pow_two, P] using h0
    have hterm : scale * GoldbachReflectedShiftEuler.prefixProduct y 0 ≤ 4*Real.exp 6 := by
      calc
        _ ≤ scale * Real.exp 6 :=
          mul_le_mul_of_nonneg_left (GoldbachReflectedShiftEuler.prefix_le y 0) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_right scale_le_four (Real.exp_nonneg _)
    dsimp only [B₀]
    linarith only [h0', hterm]
  have hRglobal : avg Amb (fun m => (R m)^2) ≤ 2*(C+B₀) := by
    have hCsmall : C/(y:ℝ)^2 ≤ C := div_le_self hC.le hsqY
    have hl2 : avg Amb (fun m => (R m-P m)^2) ≤ C := hL2.trans hCsmall
    exact avg_sq_le_of_approx Amb R P C B₀ hl2 hPglobal
  have hFCard : Amb.card ≤ 2*F.card := band_card_le_twice_shiftedBand_card hN hlarge
  have hFmem (m : ℕ) (hm : m ∈ F) : m ∈ Amb := (mem_shiftedBand.mp hm).1
  have hshift (m : ℕ) (hm : m ∈ F) : m+2*h ∈ Amb := (mem_shiftedBand.mp hm).2
  have restrict (d : ℕ) (hd : ∀ m ∈ F, m+d ∈ Amb) (f : ℕ → ℝ)
      (hf : ∀ m ∈ Amb, 0 ≤ f m) :
      avg F (fun m => f (m+d)) ≤ 2*avg Amb f :=
    avg_restrict_shift F Amb d f hd hf hFCard
  have hRestrictP : avg F (fun m => (P m)^2) ≤ K := by
    have H := restrict 0 (by simpa only [add_zero] using hFmem) (fun m => (P m)^2)
      (fun _ _ => sq_nonneg _)
    simp only [add_zero] at H
    have h := mul_le_mul_of_nonneg_left hPglobal (by norm_num : 0 ≤ (2:ℝ))
    dsimp only [K]
    linarith only [H, h, hC, hB₀]
  have hRestrictR : avg F (fun m => (R (m+2*h))^2) ≤ K := by
    have H := restrict (2*h) hshift (fun m => (R m)^2) (fun _ _ => sq_nonneg _)
    have h := mul_le_mul_of_nonneg_left hRglobal (by norm_num : 0 ≤ (2:ℝ))
    dsimp only [K]
    linarith only [H, h]
  let η := 2*(C/(y : ℝ)^2)
  have hERR0 : avg F (fun m => (R m-P m)^2) ≤ η := by
    have H := restrict 0 (by simpa only [add_zero] using hFmem)
      (fun m => (R m-P m)^2) (fun _ _ => sq_nonneg _)
    simpa only [add_zero] using H.trans (mul_le_mul_of_nonneg_left hL2 (by norm_num))
  have hERR1 : avg F (fun m => (R (m+2*h)-P (m+2*h))^2) ≤ η :=
    (restrict (2*h) hshift (fun m => (R m-P m)^2) (fun _ _ => sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hL2 (by norm_num))
  have hTransfer :
      |avg F (fun m => R m * R (m+2*h)) - avg F (fun m => P m * P (m+2*h))| ≤ ε/3 := by
    have H := avg_product_transfer F R (fun m => R (m+2*h)) P (fun m => P (m+2*h)) η K
      hERR0 hERR1 hRestrictP hRestrictR
    apply H.trans
    have hSqrt : Real.sqrt η = Real.sqrt (2*C)/(y:ℝ) := by
      rw [show η = (2*C)/(y:ℝ)^2 by dsimp [η]; ring,
        Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hyR]
    rw [hSqrt]
    convert hZsmall using 1
    dsimp only [Z]
    ring
  have hprod : |scale * GoldbachReflectedShiftEuler.prefixProduct y h -
      scale * GoldbachReflectedShiftEuler.product h| ≤ ε/3 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ 4 * |GoldbachReflectedShiftEuler.prefixProduct y h - GoldbachReflectedShiftEuler.product h| :=
        mul_le_mul_of_nonneg_right scale_le_four (abs_nonneg _)
      _ ≤ 4*(ε/12) := mul_le_mul_of_nonneg_left (hEuler y h hYA) (by norm_num)
      _ = _ := by ring
  have hTriangle :=
    abs_sub_le (avg F (fun m => R m * R (m+2*h)))
      (avg F (fun m => P m * P (m+2*h)))
      (scale * GoldbachReflectedShiftEuler.product h)
  have hTriangle' :=
    abs_sub_le (avg F (fun m => P m * P (m+2*h)))
      (scale * GoldbachReflectedShiftEuler.prefixProduct y h)
      (scale * GoldbachReflectedShiftEuler.product h)
  have hFinite := hEstimate h hlarge
  change |avg F (fun m => R m * R (m+2*h)) -
    scale * GoldbachReflectedShiftEuler.product h| ≤ ε
  linarith only [hTriangle, hTriangle', hTransfer, hprod, hFinite]

end
end GoldbachReflectedShiftMain


namespace GoldbachReflectedShiftCRT

open Finset
open scoped BigOperators Classical

noncomputable def boost (p : ℕ) : ℝ := 1 / ((p : ℝ) - 2)

noncomputable def finiteScore (S : Finset ℕ) (u : ℕ) : ℝ :=
  ∏ p ∈ S, (1 + if p ∣ u then boost p else 0)

noncomputable def localMoment (p h : ℕ) : ℝ :=
  1 + 2 * boost p / (p : ℝ) + if p ∣ h then boost p ^ 2 / (p : ℝ) else 0

noncomputable def finiteMoment (S : Finset ℕ) (h : ℕ) : ℝ :=
  ∏ p ∈ S, localMoment p h

def period (S : Finset ℕ) : ℕ := ∏ p ∈ S, p

noncomputable def pairBound (S : Finset ℕ) : ℝ :=
  (∏ p ∈ S, (1 + boost p)) ^ 2

private noncomputable def bump {p : ℕ} (a : ℝ) (x : ZMod p) : ℝ :=
  if x = 0 then a else 0

private theorem sum_bump {p : ℕ} [NeZero p] (a : ℝ) :
    (∑ x : ZMod p, bump a x) = a := by
  classical
  simp [bump]

private theorem local_sum (p h : ℕ) [NeZero p] :
    (∑ x : ZMod p, (1+bump (boost p) x) * (1+bump (boost p) (x+(h : ZMod p)))) =
      (p : ℝ) * localMoment p h := by
  have hshift : (∑ x : ZMod p, bump (boost p) (x + (h : ZMod p))) = boost p :=
    (Equiv.sum_comp (Equiv.addRight (h : ZMod p)) (bump (boost p))).trans (sum_bump (boost p))
  have hcross :
      (∑ x : ZMod p, bump (boost p) x * bump (boost p) (x + (h : ZMod p))) =
        if p ∣ h then boost p ^ 2 else 0 := by
    calc
      _ = ∑ x : ZMod p, if x = 0 then boost p * bump (boost p) (x + (h : ZMod p)) else 0 := by
        apply sum_congr rfl
        intro x _
        simp only [bump, ite_mul, zero_mul]
      _ = _ := by
        simp [bump, ZMod.natCast_eq_zero_iff, mul_ite, pow_two]
  simp only [add_mul, mul_add, one_mul, mul_one, sum_add_distrib, hshift, sum_bump, hcross,
    sum_const, nsmul_eq_mul, card_univ, ZMod.card, mul_one]
  unfold localMoment
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  split_ifs <;> field_simp [hp] <;> ring

/-- Products of the two finite Euler scores average to the local pair
moments over a full period, with arbitrary starting point and shift. -/
theorem shifted_pair_period_sum (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (start h : ℕ) :
    (∑ i ∈ range (period S), finiteScore S (start+i) * finiteScore S (start+i+h)) =
      (period S : ℝ) * finiteMoment S h := by
  let _ (p : S) : NeZero (p : ℕ) := ⟨(hS p p.property).ne_zero⟩
  let F (p : S) (x : ZMod (p : ℕ)) :=
    (1+bump (boost p) x) * (1+bump (boost p) (x+(h : ZMod (p : ℕ))))
  have hl (u : ℕ) : finiteScore S u * finiteScore S (u+h) =
      ∏ p : S, F p (u : ZMod (p : ℕ)) := by
    rw [finiteScore, finiteScore, ← prod_mul_distrib]
    rw [← prod_coe_sort S (fun p : ℕ =>
      (1 + if p ∣ u then boost p else 0) * (1 + if p ∣ u+h then boost p else 0))]
    apply prod_congr rfl
    intro p _
    simp only [F, bump, ← Nat.cast_add, ZMod.natCast_eq_zero_iff]
  simp_rw [hl]
  unfold period finiteMoment
  rw [GoldbachReflectedCRT.crt_sum S hS F start]
  simp only [F, local_sum, prod_mul_distrib, Nat.cast_prod]
  rw [prod_coe_sort S (fun p : ℕ => (p : ℝ)), prod_coe_sort S (fun p : ℕ => localMoment p h)]

private theorem boost_nonneg (p : ℕ) (hp : 2 < p) : 0 ≤ boost p := by
  have hpR : (2 : ℝ) < p := by exact_mod_cast hp
  exact div_nonneg (by norm_num) (sub_nonneg.mpr hpR.le)

private theorem pairBound_pos (S : Finset ℕ) (hS : ∀ p ∈ S, 2 < p) :
    0 < pairBound S := by
  have hp : 0 < ∏ p ∈ S, (1 + boost p) :=
    prod_pos fun p hp => add_pos_of_pos_of_nonneg one_pos (boost_nonneg p (hS p hp))
  exact pow_pos hp _

private theorem abs_finiteScore_le (S : Finset ℕ) (hS : ∀ p ∈ S, 2 < p) (u : ℕ) :
    |finiteScore S u| ≤ ∏ p ∈ S, (1 + boost p) := by
  rw [finiteScore, abs_prod]
  refine prod_le_prod₀ (fun _ _ => abs_nonneg _) ?_
  intro p hp
  have hb := boost_nonneg p (hS p hp)
  split_ifs
  · exact le_of_eq (abs_of_nonneg (by positivity))
  · rw [add_zero, abs_one]
    linarith only [hb]

/-- Every interval has discrepancy bounded by twice the period times
the uniform score bound, independently of the shift. -/
theorem shifted_pair_interval_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (start length h : ℕ) :
    |(∑ i ∈ range length, finiteScore S (start+i) * finiteScore S (start+i+h)) -
      (length : ℝ) * finiteMoment S h| ≤ 2 * (period S : ℝ) * pairBound S := by
  let f (u : ℕ) := finiteScore S u * finiteScore S (u+h)
  let P := period S
  let M := pairBound S
  let μ := finiteMoment S h
  have hM : 0 < M := pairBound_pos S fun p hp => (hS p hp).2
  have hP : 0 < P := prod_pos fun p hp => (hS p hp).1.pos
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hf (u : ℕ) : |f u| ≤ M := by
    simp only [f, abs_mul, M, pairBound, pow_two]
    exact mul_le_mul
      (abs_finiteScore_le S (fun p hp => (hS p hp).2) u)
      (abs_finiteScore_le S (fun p hp => (hS p hp).2) (u+h))
      (abs_nonneg _) (prod_nonneg fun p hp => by
        have hp := boost_nonneg p (hS p hp).2
        positivity)
  have hf' (u : ℕ) : |f u / M| ≤ 1 := by
    rw [abs_div, abs_of_pos hM]
    exact (div_le_one hM).mpr (hf u)
  have hfull (s : ℕ) : (∑ i ∈ range P, f (s+i) / M) = (P : ℝ) * (μ/M) := by
    rw [← sum_div]
    change ((∑ i ∈ range (period S), finiteScore S (s+i) * finiteScore S (s+i+h)) / M) = _
    rw [shifted_pair_period_sum S (fun p hp => (hS p hp).1), mul_div_assoc]
  have hμ : |μ / M| ≤ 1 := by
    have hh : |(P : ℝ) * (μ / M)| ≤ (P : ℝ) * 1 := calc
      _ = |∑ i ∈ range P, f (0+i) / M| := congrArg abs (hfull 0).symm
      _ ≤ ∑ i ∈ range P, |f (0+i) / M| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ range P, (1 : ℝ) := sum_le_sum fun i _ => hf' _
      _ = _ := by simp
    rw [abs_mul, abs_of_pos hPR] at hh
    exact le_of_mul_le_mul_left hh hPR
  have he := GoldbachReflectedCRT.bounded_interval_error (fun u => f u / M) (μ / M)
    P hP hf' hμ hfull start length
  rw [← sum_div, ← mul_div_assoc, ← sub_div, abs_div, abs_of_pos hM] at he
  exact (div_le_iff₀ hM).mp he

theorem shifted_pair_Icc_avg_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (L U h : ℕ) (hLU : L ≤ U) :
    |(∑ u ∈ Icc L U, finiteScore S u * finiteScore S (u+h)) /
      ((Icc L U).card : ℝ) - finiteMoment S h| ≤
        2 * (period S : ℝ) * pairBound S / ((Icc L U).card : ℝ) := by
  let n := (Icc L U).card
  have hn : (0 : ℝ) < (n : ℝ) := by
    have hh : 0 < n := card_pos.mpr ⟨L, mem_Icc.mpr ⟨le_rfl, hLU⟩⟩
    exact_mod_cast hh
  rw [GoldbachReflectedCRT.sum_Icc_as_range]
  change |(∑ i ∈ range n, finiteScore S (L+i) * finiteScore S (L+i+h)) / (n : ℝ)
    - finiteMoment S h| ≤ _
  have he := shifted_pair_interval_error S hS L n h
  rw [← mul_div_cancel_left₀ (finiteMoment S h) hn.ne', ← sub_div, abs_div, abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  simpa only [mul_div_cancel_left₀ _ hn.ne'] using he

/-- With odd primes as support, the half-target score equals the finite
product over prime factors of the original even target. -/
theorem finiteScore_eq_primeFactors (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 2 < p)
    (u : ℕ) (hu : u ≠ 0) :
    finiteScore S u = ∏ p ∈ (2*u).primeFactors.filter (fun p => p ∈ S), (1 + boost p) := by
  have hnonzero : 2*u ≠ 0 := Nat.mul_ne_zero (by decide) hu
  have hsets : (2*u).primeFactors.filter (fun p => p ∈ S) = S.filter (fun p => p ∣ u) := by
    ext p
    simp only [mem_filter, Nat.mem_primeFactors_of_ne_zero hnonzero]
    constructor
    · rintro ⟨⟨_, hpdu⟩, hpS⟩
      have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (hS p hpS).2
      exact ⟨hpS, ((hS p hpS).1.dvd_mul.mp hpdu).resolve_left hp2⟩
    · rintro ⟨hpS, hpdu⟩
      exact ⟨⟨(hS p hpS).1, ((hS p hpS).1.dvd_mul.mpr (Or.inr hpdu))⟩, hpS⟩
  rw [hsets, finiteScore, prod_filter]
  apply prod_congr rfl
  intro p _
  split_ifs <;> simp

end GoldbachReflectedShiftCRT

namespace GoldbachReflectedShiftFinite

open Finset Filter GoldbachReflectedBand
open GoldbachReflectedShiftBand GoldbachReflectedShiftTransfer GoldbachReflectedShiftMain
open GoldbachReflectedShiftEuler GoldbachReflectedShiftCRT
open scoped Topology

theorem eventually_model_pair (y : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ h : ℕ, h^3 ≤ N →
      |avg (shiftedBand N h) (fun m => model y m * model y (m+2*h)) -
        scale * prefixProduct y h| ≤ η := by
  classical
  let S := primesUpTo y
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ 2 < p :=
    ⟨(mem_primesUpTo.mp hp).1, (mem_primesUpTo.mp hp).2.1⟩
  let C := 8*(period S : ℝ)*pairBound S
  have hC : 0 ≤ C := by dsimp [C, pairBound]; positivity
  filter_upwards [eventually_ge_atTop (384 : ℕ),
    eventually_log_power_over_shifted_card_le 0 hC hη] with N hN herror
  intro h hlarge
  have hh := shift_le_upper hN hlarge
  let F := shiftedHalfBand N h
  have hF : F.Nonempty := shiftedHalfBand_nonempty hN hlarge
  obtain ⟨u₀, hU⟩ := hF
  have hLU : lower N ≤ upper N-h := (Finset.mem_Icc.mp hU).1.trans (Finset.mem_Icc.mp hU).2
  have hscore (u : ℕ) (hu : u ≠ 0) : model y (2*u) = 2*twinConstant * finiteScore S u := by
    unfold model
    rw [finiteScore_eq_primeFactors S hS u hu]
    congr 1
    have hset : ((2*u).primeFactors.filter (fun p => 2 < p ∧ p ≤ y)) =
        (2*u).primeFactors.filter (fun p => p ∈ S) := by
      apply Finset.filter_congr
      intro p hp
      simp only [S, mem_primesUpTo, Nat.prime_of_mem_primeFactors hp, true_and]
    rw [hset]
    rfl
  have hmom : prefixProduct y h = finiteMoment S h := by
    apply Finset.prod_congr rfl
    intro p hp
    obtain ⟨hprime, htwo⟩ := hS p hp
    simp only [factor, hprime, htwo, and_self, ite_true, localMoment, boost]
  have hprod :
      avg (shiftedBand N h) (fun m => model y m * model y (m+2*h)) =
        scale*((∑ u ∈ F, finiteScore S u * finiteScore S (u+h))/(F.card:ℝ)) := by
    unfold avg
    rw [sum_shiftedBand N h hh, shiftedBand_card N h hh]
    have hsum :
        (∑ u ∈ F, model y (2*u) * model y (2*u+2*h)) =
          ∑ u ∈ F, scale*(finiteScore S u * finiteScore S (u+h)) := by
      apply Finset.sum_congr rfl
      intro u hu
      obtain ⟨hu0, huh0, _, _⟩ := shiftedHalfBand_members (by omega : 0 < N) hh hu
      rw [show 2*u+2*h = 2*(u+h) by omega, hscore u hu0, hscore (u+h) huh0, scale]
      ring
    change (∑ u ∈ F, model y (2*u) * model y (2*u+2*h))/(F.card:ℝ) = _
    rw [hsum, ← Finset.mul_sum, mul_div_assoc]
  have herr := shifted_pair_Icc_avg_error S hS (lower N) (upper N-h) h hLU
  rw [hprod, hmom, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ 4 * |(∑ u ∈ F, finiteScore S u * finiteScore S (u+h))/(F.card:ℝ) - finiteMoment S h| :=
      mul_le_mul_of_nonneg_right scale_le_four (abs_nonneg _)
    _ ≤ 4 * (2 * (period S : ℝ) * pairBound S / (F.card:ℝ)) :=
      mul_le_mul_of_nonneg_left herr (by norm_num)
    _ = C*(cap N : ℝ)^0/(F.card:ℝ) := by dsimp only [C]; simp; ring
    _ ≤ _ := herror h hlarge

end GoldbachReflectedShiftFinite

open Filter

theorem Conjectures.Goldbach.ReflectedShiftedPairMoment : (
by
  classical
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
  let R := fun N m : ℕ => A N m / (2*(N:ℝ)-(m:ℝ))
  let B := fun N : ℕ => (Finset.Icc N (2*N)).filter (band N)
  let avg := fun (F : Finset ℕ) (f : ℕ → ℝ) => (∑ m ∈ F, f m)/(F.card:ℝ)
  exact ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N h : ℕ, T ≤ N → h^3 ≤ N →
    let F := (B N).filter (fun m => band N (m+2*h))
    let E := (2*C₂)^2 * ∏' p : ℕ, if Nat.Prime p ∧ 2<p then (let u : ℝ := 1/((p:ℝ)-2); 1+2*u/(p:ℝ)+(if p ∣ h then u^2/(p:ℝ) else 0)) else 1
    |avg F (fun m => R N m * R N (m+2*h)) - E| ≤ ε
) := by

  classical
  dsimp only
  intro ε hε
  have hMean : ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 3 ≤ y →
      ∀ᶠ N : ℕ in Filter.atTop,
        GoldbachReflectedShiftTransfer.avg (GoldbachReflectedBand.band N)
          (fun m => (GoldbachReflectedTransfer.normalized N m-GoldbachReflectedShiftMain.model y m)^2)
            ≤ C/(y : ℝ)^2 := by
    refine ⟨48*Real.exp 2+4, by positivity, ?_⟩
    exact GoldbachReflectedMeanSquare.eventual_meanSquare
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp
    (GoldbachReflectedShiftMain.from_meanSquare hMean
      GoldbachReflectedShiftFinite.eventually_model_pair ε hε)
  exact ⟨T, fun N h hN hh => hT N hN h hh⟩
