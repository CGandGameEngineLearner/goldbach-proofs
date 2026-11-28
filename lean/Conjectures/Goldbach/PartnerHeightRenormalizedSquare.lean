import Mathlib
import Conjectures.Goldbach.PartnerLevelParseval

section HeightProductionSection1
open Filter
open scoped Topology
namespace SignedHeight

noncomputable def hh (x : ℝ) : ℝ := harmonic ⌊x⌋₊

theorem harmonic_floor (d : ℝ) (hd : 0 < d) :
    Tendsto (fun x : ℝ => hh (x/d) - Real.log x) atTop
      (𝓝 (Real.eulerMascheroniConstant - Real.log d)) := by
  have ht : Tendsto (fun x : ℝ => x/d) atTop atTop :=
    tendsto_id.atTop_div_const hd
  have hf : Tendsto (fun x : ℝ => ⌊x/d⌋₊) atTop atTop :=
    (tendsto_nat_floor_atTop (α := ℝ)).comp ht
  have hγ := Real.tendsto_harmonic_sub_log.comp hf
  have hr := (tendsto_nat_floor_div_atTop (R := ℝ)).comp ht
  have hlog := (Real.continuousAt_log (by norm_num : (1:ℝ) ≠ 0)).tendsto.comp hr
  rw [Real.log_one] at hlog
  have hl : Tendsto (fun x : ℝ => Real.log ((⌊x/d⌋₊ : ℕ) : ℝ)
      - Real.log (x/d)) atTop (𝓝 0) := by
    apply hlog.congr'
    filter_upwards [eventually_ge_atTop d] with x hx
    have hd' : (x/d) ≠ 0 := ne_of_gt (div_pos (hd.trans_le hx) hd)
    change Real.log ((⌊x/d⌋₊ : ℝ) / (x/d)) = _
    have hn : (⌊x/d⌋₊ : ℝ) ≠ 0 := by exact_mod_cast (Nat.floor_pos.mpr ((one_le_div hd).mpr hx)).ne'
    exact Real.log_div hn hd'
  have hsum := ((hγ.add hl).sub_const (Real.log d))
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop d] with x hx
  change ((harmonic ⌊x/d⌋₊ : ℚ) : ℝ) - Real.log (⌊x/d⌋₊ : ℝ)
      + (Real.log (⌊x/d⌋₊ : ℝ) - Real.log (x/d)) - Real.log d = _
  rw [Real.log_div (hd.trans_le hx).ne' hd.ne']
  simp only [hh]
  ring

theorem double_difference (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    Tendsto (fun x : ℝ => hh x - hh (x/p) - (hh (x/q) - hh (x/(p*q))))
      atTop (𝓝 0) := by
  have h := (((harmonic_floor 1 zero_lt_one).sub (harmonic_floor p hp)).sub
      ((harmonic_floor q hq).sub (harmonic_floor (p*q) (mul_pos hp hq))))
  rw [Real.log_one, Real.log_mul hp.ne' hq.ne'] at h
  convert h using 1
  · ext x
    simp only [div_one]
    ring
  · congr 1
    ring
end SignedHeight
end HeightProductionSection1

section HeightProductionSection2
open Filter
open scoped Topology
namespace SignedHeight

noncomputable def err (x : ℝ) : ℝ := hh x - Real.log x - Real.eulerMascheroniConstant

theorem err_tendsto : Tendsto err atTop (𝓝 0) := by
  unfold err
  simpa only [div_one, Real.log_one, sub_zero, sub_self] using ((harmonic_floor 1 zero_lt_one).sub_const
    Real.eulerMascheroniConstant)

theorem err_bounded_above_one : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 1, ‖err x‖ ≤ C := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (err_tendsto.eventually (Metric.ball_mem_nhds 0 zero_lt_one))
  let Z : ℝ := max T 1
  let U : ℝ := ∑ n ∈ Finset.range (⌊Z⌋₊ + 1), ‖(harmonic n : ℝ)‖
  let L : ℝ := ‖Real.log Z‖
  let G : ℝ := ‖Real.eulerMascheroniConstant‖
  let C : ℝ := 1 + (U + L + G)
  have hz : 1 ≤ Z := le_max_right _ _
  have hu : 0 ≤ U := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hc : 1 ≤ C := le_add_of_nonneg_right
    (add_nonneg (add_nonneg hu (norm_nonneg _)) (norm_nonneg _))
  refine ⟨C, by linarith, fun x hx => ?_⟩
  by_cases ht : T ≤ x
  · have h := hT x ht
    rw [dist_zero_right] at h
    exact h.le.trans hc
  · have hxZ : x ≤ Z := (le_of_not_ge ht).trans (le_max_left _ _)
    have hhx : ‖hh x‖ ≤ ∑ n ∈ Finset.range (⌊Z⌋₊ + 1), ‖(harmonic n : ℝ)‖ := by
      exact Finset.single_le_sum (f := fun n => ‖(harmonic n : ℝ)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono hxZ)))
    have hlx : ‖Real.log x‖ ≤ ‖Real.log Z‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg hx), abs_of_nonneg (Real.log_nonneg hz)]
      exact Real.log_le_log (by linarith) hxZ
    unfold err
    have hb := norm_sub_le (hh x - Real.log x) Real.eulerMascheroniConstant
    have hs := norm_sub_le (hh x) (Real.log x)
    have step : ‖hh x - Real.log x - Real.eulerMascheroniConstant‖ ≤ U + L + G :=
      hb.trans (add_le_add_left (hs.trans (add_le_add hhx hlx)) _)
    exact step.trans (le_add_of_nonneg_left zero_le_one)

theorem err_scaled_bound (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ z ≥ 1, ‖err z‖ ≤ C) (d : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    ‖err (x / (d+1 : ℕ))‖ ≤ C + ‖Real.eulerMascheroniConstant‖ + Real.log (d+1 : ℕ) := by
  have hd : (0:ℝ) < (d+1 : ℕ) := by positivity
  have hdl : 0 ≤ Real.log (d+1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_pos d)
  by_cases hp : 1 ≤ x / (d+1 : ℕ)
  · have := hb _ hp
    linarith [norm_nonneg Real.eulerMascheroniConstant]
  · have hpos : 0 < x / (d+1 : ℕ) := div_pos (by linarith) hd
    have hz : ⌊x / (d+1 : ℕ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hp)
    have hl : ‖Real.log (x / (d+1 : ℕ))‖ ≤ Real.log (d+1 : ℕ) := by
      rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos hpos.le (le_of_not_ge hp)),
        Real.log_div (by linarith : x ≠ 0) hd.ne']
      linarith [Real.log_nonneg hx]
    have h := norm_sub_le (-Real.log (x / (d+1 : ℕ))) Real.eulerMascheroniConstant
    rw [norm_neg] at h
    unfold err hh
    rw [hz, harmonic_zero, Rat.cast_zero, zero_sub]
    exact h.trans (by linarith)

theorem weighted_error_tendsto (g : ℕ → ℝ) (hs : Summable (fun d => ‖g d‖))
    (hlog : Summable (fun d => ‖g d‖ * Real.log (d+1 : ℕ))) :
    Tendsto (fun x : ℝ => ∑' d : ℕ, g d * err (x/(d+1 : ℕ))) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := err_bounded_above_one
  have hS : Summable (fun d => ‖g d‖ *
      (C + ‖Real.eulerMascheroniConstant‖ + Real.log (d+1 : ℕ))) := by
    simpa only [mul_add] using (hs.mul_right (C + ‖Real.eulerMascheroniConstant‖)).add hlog
  have hh := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun _ : ℕ => (0:ℝ))
    (f := fun (x : ℝ) (d : ℕ) => g d * err (x/(d+1 : ℕ))) hS
    (fun d => by
      have h_div : Tendsto (fun x : ℝ => x / (d+1 : ℕ)) atTop atTop :=
        tendsto_id.atTop_div_const (by positivity)
      simpa only [mul_zero, Function.comp_def] using (err_tendsto.comp h_div).const_mul (g d)) (by
      filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx d
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (err_scaled_bound C hC hb d x hx) (norm_nonneg _))
  simpa only [tsum_zero] using hh

end SignedHeight
end HeightProductionSection2

section HeightProductionSection3
open Filter
open scoped Topology

namespace SignedHeight
noncomputable def constantTerm (g : ℕ → ℝ) : ℝ :=
  ∑' d : ℕ, g d * (Real.eulerMascheroniConstant - Real.log (d + 1 : ℕ))

theorem weighted_harmonic_asymptotic (g : ℕ → ℝ) (hs : Summable (fun d => ‖g d‖))
    (hlog : Summable (fun d => ‖g d‖ * Real.log (d+1 : ℕ))) :
    Tendsto (fun x : ℝ =>
      (∑' d : ℕ, g d * hh (x / (d+1 : ℕ)))
          - (∑' d : ℕ, g d) * Real.log x - constantTerm g) atTop (𝓝 0) := by
  have hgs : Summable g := hs.of_norm
  have hgl : Summable (fun d => g d * Real.log (d+1 : ℕ)) := by
    apply hlog.of_norm_bounded
    intro d
    rw [norm_mul, Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_pos d))]
  have hb₀ : Summable (fun d => g d *
      (Real.eulerMascheroniConstant - Real.log (d+1 : ℕ))) := by
    simp_rw [mul_sub]
    exact (hgs.mul_right _).sub hgl
  apply (weighted_error_tendsto g hs hlog).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  obtain ⟨C,hC,hb⟩ := err_bounded_above_one
  have hB : Summable (fun d => ‖g d‖ *
      (C + ‖Real.eulerMascheroniConstant‖ + Real.log (d+1 : ℕ))) := by
    simp_rw [mul_add]
    exact (hs.mul_right C).add (hs.mul_right _ ) |>.add hlog
  have hErr : Summable (fun d => g d * err (x / (d+1 : ℕ))) := by
    apply hB.of_norm_bounded
    intro d
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (err_scaled_bound C hC hb d x hx) (norm_nonneg _)
  have hLog : Summable (fun d => g d * Real.log x) := hgs.mul_right _
  have eq : ∀ d : ℕ, g d * hh (x / (d+1 : ℕ)) =
      (g d * err (x / (d+1 : ℕ)) + g d * Real.log x) +
        g d * (Real.eulerMascheroniConstant - Real.log (d+1 : ℕ)) := by
    intro d
    unfold err
    rw [Real.log_div (by linarith : x ≠ 0) (by positivity :
      (d+1 : ℕ) ≠ (0:ℝ))]
    ring
  simp_rw [eq]
  rw [Summable.tsum_add (hErr.add hLog) hb₀, Summable.tsum_add hErr hLog,
    tsum_mul_right]
  unfold constantTerm
  ring
end SignedHeight
end HeightProductionSection3

section HeightProductionSection4
open Finset Filter
open scoped Topology

namespace SignedHeight

theorem sum_divisors_reindex (Y : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ Icc 1 Y, ∑ d ∈ n.divisors, f d (n/d)) =
      ∑ d ∈ Icc 1 Y, ∑ k ∈ Icc 1 (Y/d), f d k := by
  classical
  rw [sum_sigma' (Icc 1 Y) Nat.divisors (fun n d => f d (n/d)),
    sum_sigma' (Icc 1 Y) (fun d => Icc 1 (Y/d)) f]
  refine sum_bij' (fun x _ => ⟨x.2, x.1/x.2⟩)
    (fun x _ => ⟨x.1*x.2, x.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n,d⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨hn,hY⟩,hd,hn0⟩ := h
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    refine ⟨⟨hdpos, (Nat.le_of_dvd hn hd).trans hY⟩, ?_, ?_⟩
    · exact (Nat.le_div_iff_mul_le hdpos).2 (by simpa using Nat.le_of_dvd hn hd)
    · exact Nat.div_le_div_right hY
  · rintro ⟨d,k⟩ h
    simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨hd,hYd⟩,hk,hYk⟩ := h
    have hpos : 0 < d*k := Nat.mul_pos hd hk
    exact ⟨⟨hpos, by simpa [mul_comm] using (Nat.le_div_iff_mul_le hd).1 hYk⟩,
      dvd_mul_right _ _, hpos.ne'⟩
  · rintro ⟨n,d⟩ h
    have hd := (Nat.mem_divisors.mp (mem_sigma.mp h).2).1
    simp [Nat.mul_div_cancel' hd]
  · rintro ⟨d,k⟩ h
    have hd := (mem_Icc.mp (mem_sigma.mp h).1).1
    simp [Nat.mul_div_cancel_left _ hd]
  · rintro ⟨n,d⟩ h
    rfl

theorem floor_nat_div (n d : ℕ) (hd : 0 < d) :
    ⌊(n:ℝ) / (d:ℝ)⌋₊ = n/d := by
  apply Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ (n:ℝ) / (d:ℝ)) |>.mpr
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  rw [le_div_iff₀ hdR, div_lt_iff₀ hdR]
  constructor
  · exact_mod_cast Nat.div_mul_le_self n d
  · have h₁ := Nat.mod_add_div n d
    have h₂ := Nat.mod_lt n hd
    exact_mod_cast (show n < (n/d + 1)*d by nlinarith)

theorem harmonic_rearrange (Y : ℕ) (a : ℕ → ℝ) :
    (∑ n ∈ Icc 1 Y, ∑ d ∈ n.divisors, a d * ((n/d : ℕ) : ℝ)⁻¹) =
      ∑ d ∈ Icc 1 Y, a d * hh ((Y : ℝ)/(d : ℝ)) := by
  rw [sum_divisors_reindex Y (fun d k => a d * (k : ℝ)⁻¹)]
  apply sum_congr rfl
  intro d hd
  simp only [hh, floor_nat_div Y d (mem_Icc.mp hd).1, harmonic_eq_sum_Icc,
    Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, mul_sum]

end SignedHeight
end HeightProductionSection4

section HeightProductionSection5
open Filter Finset
open scoped Topology

namespace SignedHeight

theorem weighted_tsum_finite (Y : ℕ) (a : ℕ → ℝ) :
    (∑' d : ℕ, a (d+1) * hh ((Y:ℝ)/(d+1 : ℕ))) =
      ∑ d ∈ Icc 1 Y, a d * hh ((Y:ℝ)/(d:ℝ)) := by
  rw [tsum_eq_sum (s := range Y)]
  · rw [range_eq_Ico]
    have h := Finset.sum_Ico_add' (fun d : ℕ => a d * hh ((Y:ℝ)/(d:ℝ))) 0 Y (c := 1)
    have he : Icc 1 Y = Ico 1 (Y+1) := by
      ext i
      simp only [mem_Icc, mem_Ico]
      omega
    rw [he]
    simpa using h
  · intro d hd
    have hy : Y ≤ d := Nat.le_of_not_gt (fun h => hd (mem_range.mpr h))
    rw [hh, Nat.floor_eq_zero.mpr (by
      apply (div_lt_one (by positivity)).2
      exact_mod_cast (show Y < d+1 by omega)), harmonic_zero, Rat.cast_zero, mul_zero]

theorem divisor_convolution_asymptotic (a : ℕ → ℝ)
    (hs : Summable (fun d => ‖a (d+1)‖))
    (hlog : Summable (fun d => ‖a (d+1)‖ * Real.log (d+1 : ℕ))) :
    ∃ b : ℝ, Tendsto (fun Y : ℕ =>
      (∑ n ∈ Icc 1 Y, ∑ d ∈ n.divisors, a d * ((n/d : ℕ) : ℝ)⁻¹) -
        (∑' d : ℕ, a (d+1)) * Real.log (Y:ℝ) - b) atTop (𝓝 0) := by
  refine ⟨constantTerm (fun d => a (d+1)), ?_⟩
  have he := (weighted_harmonic_asymptotic (fun d => a (d+1)) hs hlog).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
  apply he.congr'
  apply Eventually.of_forall
  intro Y
  dsimp only [Function.comp_apply]
  rw [harmonic_rearrange, ← weighted_tsum_finite]

end SignedHeight
end HeightProductionSection5

section HeightProductionSection6
namespace SignedHeight

open Filter Finset DirichletCharacter
open scoped Topology Classical

noncomputable def partnersAt (d : ℕ) : Finset (DirichletCharacter ℂ d) :=
  if hd : d = 0 then ∅ else
    letI : NeZero d := ⟨hd⟩
    univ.filter IsPrimitive

theorem mem_partnersAt {d : ℕ} {χ : DirichletCharacter ℂ d} :
    χ ∈ partnersAt d ↔ d ≠ 0 ∧ χ.IsPrimitive := by
  unfold partnersAt
  by_cases hd : d = 0 <;> simp [hd]

noncomputable def partnersUpTo (Y : ℕ) : Finset (Σ s : ℕ, DirichletCharacter ℂ s) :=
  (Icc 1 Y).sigma partnersAt

theorem mem_partnersUpTo {Y : ℕ} {b : Σ s : ℕ, DirichletCharacter ℂ s} :
    b ∈ partnersUpTo Y ↔ (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ b.1 ≤ Y := by
  rw [partnersUpTo, mem_sigma, mem_Icc, mem_partnersAt]
  constructor
  · rintro ⟨⟨_,hy⟩,hn,hp⟩
    exact ⟨⟨hn,hp⟩,hy⟩
  · rintro ⟨⟨hn,hp⟩,hy⟩
    exact ⟨⟨Nat.pos_of_ne_zero hn,hy⟩,hn,hp⟩

noncomputable def massAt (w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℝ) (d : ℕ) : ℝ :=
  ∑ χ ∈ partnersAt d, w ⟨d,χ⟩

theorem sum_partnersUpTo (Y : ℕ) (w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℝ) :
    (∑ b ∈ partnersUpTo Y, w b) = ∑ d ∈ Icc 1 Y, massAt w d := by
  exact sum_sigma _ _ _

theorem assemble_from_convolution
    (w : (Σ s : ℕ, DirichletCharacter ℂ s) → ℝ) (coef : ℝ)
    (a : ℕ → ℝ)
    (hs : Summable (fun d => ‖a (d+1)‖))
    (hlog : Summable (fun d => ‖a (d+1)‖ * Real.log (d+1 : ℕ)))
    (hc : (∑' d : ℕ, a (d+1)) = coef)
    (he : ∀ n > 0, massAt w n =
      ∑ d ∈ n.divisors, a d * ((n/d : ℕ) : ℝ)⁻¹) :
    ∃ b₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T,
      ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
        (∀ b, b ∈ F ↔ (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ b.1 ≤ Y) ∧
        |(∑ b ∈ F, w b) - coef * Real.log (Y:ℝ) - b₀| ≤ ε := by
  obtain ⟨b₀,hb⟩ := divisor_convolution_asymptotic a hs hlog
  rw [hc] at hb
  refine ⟨b₀, fun ε hε => ?_⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hb.eventually (Metric.ball_mem_nhds 0 hε))
  refine ⟨T, fun Y hY => ⟨partnersUpTo Y, fun _ => mem_partnersUpTo, ?_⟩⟩
  rw [sum_partnersUpTo]
  have hsum : ∑ d ∈ Icc 1 Y, massAt w d =
      ∑ n ∈ Icc 1 Y, ∑ d ∈ n.divisors, a d * ((n/d : ℕ) : ℝ)⁻¹ :=
    sum_congr rfl (fun n hn => he n (mem_Icc.mp hn).1)
  rw [hsum]
  have h := hT Y hY
  rw [dist_zero_right, Real.norm_eq_abs] at h
  exact h.le

end SignedHeight
end HeightProductionSection6

section HeightProductionSection7
open scoped BigOperators
namespace SignedHeight

theorem frozen_from_arithmetic (h : (
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let P := (1 : DirichletCharacter ℂ 1)
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let valid := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
  exact
    ∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive →
    ∀ m : ℕ, 0 < m → Even m →
    ∃ a : ℕ → ℝ,
      Summable (fun d => ‖a (d+1)‖) ∧
      Summable (fun d => ‖a (d+1)‖ * Real.log (d+1 : ℕ)) ∧
      (∑' d : ℕ, a (d+1)) = ‖O m‖ ∧
      (∀ n > 0, SignedHeight.massAt (fun b : B => ‖S α b.2 m‖^2) n =
        ∑ d ∈ Finset.Icc 1 n with d∣n, a d * ((n/d : ℕ) : ℝ)⁻¹))) : (
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let P := (1 : DirichletCharacter ℂ 1)
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let valid := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
  exact ∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ∃ b₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T, ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ b.1 ≤ Y) ∧ |(∑ b ∈ F, ‖S α b.2 m‖^2) - ‖O m‖ * Real.log (Y:ℝ) - b₀| ≤ ε) := by
  classical
  dsimp only at h ⊢
  intro r hr α hα m hm he
  obtain ⟨a,hs,hlog,hcoef,hmass⟩ := h r α hα m hm he
  apply assemble_from_convolution _ _ a hs hlog hcoef
  intro n hn
  rw [hmass n hn]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  exact ⟨fun h => ⟨h.2, hn.ne'⟩, fun h =>
    ⟨⟨Nat.pos_of_dvd_of_pos h.1 hn, Nat.le_of_dvd hn h.1⟩, h.1⟩⟩

end SignedHeight
end HeightProductionSection7

section HeightProductionSection8
open Finset Filter
open scoped BigOperators

namespace SignedHeight



theorem summable_nonneg_of_prime_power_rows
    (f c : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (hf0 : f 0 = 0)
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m*n) = f m * f n)
    (hc : ∀ n, 0 ≤ c n) (hcs : Summable c)
    (hrows : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => f (p^k)))
    (hrows_bound : ∀ {p : ℕ}, p.Prime → (∑' k : ℕ, f (p^k)) ≤ 1+c p) :
    Summable f := by
  classical
  apply summable_of_sum_range_le (c := Real.exp (∑' p, c p)) hf
  intro N
  let A := (range N).erase 0
  have hA (n : ↥A) : n.1 ∈ N.smoothNumbers := by
    obtain ⟨hn0, hnN⟩ := mem_erase.mp n.property
    rw [Nat.mem_smoothNumbers]
    refine ⟨hn0, fun p hp => ?_⟩
    have hd := Nat.dvd_of_mem_primeFactorsList hp
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hd).trans_lt (mem_range.mp hnN)
  let emb : ↥A ↪ N.smoothNumbers :=
    ⟨fun n => ⟨n.val, hA n⟩, fun _ _ e => Subtype.ext (congrArg (fun z : N.smoothNumbers => z.1) e)⟩
  have hm := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum hf1 hmul
    (fun hp => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _)] using hrows hp) N
  have hsm : Summable fun n : N.smoothNumbers => f n := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hf _)] using hm.1
  have hSum : (∑ i ∈ range N, f i) = ∑ i ∈ A, f i := by
    by_cases h0 : 0 ∈ range N
    · rw [← sum_erase_add _ _ h0, hf0, add_zero]
    · simp only [A, erase_eq_of_notMem h0]
  calc
    _ = ∑ i ∈ A, f i := hSum
    _ = ∑ i ∈ A.attach.map emb, f (i : ℕ) := by
      rw [sum_map]
      exact (sum_attach A f).symm
    _ ≤ ∑' i : N.smoothNumbers, f i := hsm.sum_le_tsum _ (fun i _ => hf i)
    _ = ∏ p ∈ N.primesBelow, ∑' k : ℕ, f (p^k) := hm.2.tsum_eq
    _ ≤ ∏ p ∈ N.primesBelow, Real.exp (c p) := by
      apply prod_le_prod₀
      · exact fun p _ => tsum_nonneg fun k => hf (p^k)
      · intro p hp
        exact (hrows_bound (Nat.mem_primesBelow.mp hp).2).trans
          (by simpa only [add_comm (c p) 1] using Real.add_one_le_exp (c p))
    _ = Real.exp (∑ p ∈ N.primesBelow, c p) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (hcs.sum_le_tsum _ fun i _ => hc i)

end SignedHeight
end HeightProductionSection8

section HeightProductionSection9
open Finset Filter Real

namespace SignedHeight


def HeightCorrectionRows (B : ℕ) (g : ℕ → ℝ) : Prop :=
  g 0 = 0 ∧ g 1 = 1 ∧ (∀ {m n}, m.Coprime n → g (m*n) = g m * g n) ∧
  ∀ p : ℕ, p.Prime →
    g p = (if p ∣ B then -1 / (p:ℝ) else 2 / ((p:ℝ)*((p:ℝ)-2))) ∧
    g (p^2) = (if p ∣ B then 0 else -1 / ((p:ℝ)*((p:ℝ)-2))) ∧
    ∀ k : ℕ, 2 < k → g (p^k) = 0

noncomputable def heightCorrectorPrimeFactor (B p : ℕ) : ℝ :=
  (1 - 1/(p:ℝ)) * (if p ∣ B then 1 else 1 + 1/((p:ℝ)-2))

private theorem prime_correction_coeff (B : ℕ) (hB : Even B) {p : ℕ} (hp : p.Prime)
    (hn : ¬ p ∣ B) : 3 ≤ p := by
  have h2 := hp.two_le
  by_contra! H
  have e : p = 2 := by omega
  exact hn (e.symm ▸ hB.two_dvd)

theorem height_correction_euler_row {B : ℕ} (hB : Even B) {g : ℕ → ℝ}
    (hr : HeightCorrectionRows B g) {p : ℕ} (hp : p.Prime) :
    (∑' k : ℕ, g (p^k)) = heightCorrectorPrimeFactor B p := by
  obtain ⟨_h0, h1, _hmul, hg⟩ := hr
  obtain ⟨hg1,hg2,hgt⟩ := hg p hp
  rw [tsum_eq_sum (s := range 3) (fun k hk => hgt k (by simp only [mem_range] at hk; omega))]
  rw [show (range 3 : Finset ℕ) = insert 2 (insert 1 {0}) by decide, sum_insert (by decide),
    sum_insert (by decide), sum_singleton, pow_zero, pow_one, h1, hg1, hg2]
  unfold heightCorrectorPrimeFactor
  by_cases hd : p ∣ B
  · simp only [hd, ite_true]
    ring
  · have h := prime_correction_coeff B hB hp hd
    have h' : (3:ℝ) ≤ p := by exact_mod_cast h
    have hp0 : (p:ℝ) ≠ 0 := by positivity
    have h2 : (p:ℝ)-2 ≠ 0 := by linarith
    simp only [hd, ite_false]
    field_simp
    ring


theorem height_correction_reciprocal_prime {B m p : ℕ} (hem : Even m)
    (hm : m ∣ B) (hp : p.Prime) :
    heightCorrectorPrimeFactor B p *
      (if p ∣ B ∧ ¬p ∣ m then ((p:ℝ)-1)/((p:ℝ)-2) else 1) =
      (if p ∣ m then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2)⁻¹ := by
  have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p:ℝ) ≠ 0 := by positivity
  have hp1 : (p:ℝ)-1 ≠ 0 := by linarith
  by_cases hpm : p ∣ m
  · have hpB : p ∣ B := hpm.trans hm
    simp only [heightCorrectorPrimeFactor,hpm,hpB,ite_true,not_true_eq_false,and_false,ite_false]
    field_simp
  · have p3 : 3 ≤ p := by
      by_contra! h
      have pe : p = 2 := by have := hp.two_le; omega
      exact hpm (pe.symm ▸ hem.two_dvd)
    have h3 : (3:ℝ) ≤ p := by exact_mod_cast p3
    have hp2 : (p:ℝ)-2 ≠ 0 := by linarith
    by_cases hpB : p ∣ B <;>
      simp only [heightCorrectorPrimeFactor,hpm,hpB,ite_true,not_false_eq_true,and_true,
        true_and, false_and, ite_false] <;> field_simp <;> ring

end SignedHeight
end HeightProductionSection9

section HeightProductionSection10
open Finset ArithmeticFunction
open scoped BigOperators Moebius zeta

namespace SignedHeight

noncomputable def invNatWeight : ArithmeticFunction ℝ := ⟨fun n => ((n:ℝ)⁻¹), by simp⟩

@[simp] theorem invNatWeight_apply (n : ℕ) : invNatWeight n = (n:ℝ)⁻¹ := rfl

private theorem invNatWeight_mul (m n : ℕ) :
    invNatWeight (m*n) = invNatWeight m * invNatWeight n := by
  simp [Nat.cast_mul,mul_comm]

theorem invNatWeight_multiplicative : invNatWeight.IsMultiplicative :=
  ⟨by simp, fun {_ _} _ => invNatWeight_mul _ _⟩

noncomputable def invNatMoebius : ArithmeticFunction ℝ :=
  invNatWeight.pmul (μ : ArithmeticFunction ℝ)

private theorem pointwise_h_distributes (f g : ArithmeticFunction ℝ) :
    invNatWeight.pmul (f*g) = (invNatWeight.pmul f) * (invNatWeight.pmul g) := by
  ext n
  simp only [pmul_apply, ArithmeticFunction.mul_apply, mul_sum]
  apply sum_congr rfl
  intro x hx
  have h := (Nat.mem_divisorsAntidiagonal.mp hx).1
  simp only [← h, invNatWeight_mul]
  ring

private theorem pointwise_h_one : invNatWeight.pmul (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  by_cases h : n = 1
  · subst n; simp
  · simp [one_apply_ne h]

theorem invNatMoebius_mul_invNatWeight :
    invNatMoebius * invNatWeight = 1 := by
  have H := pointwise_h_distributes (μ : ArithmeticFunction ℝ) (ζ : ArithmeticFunction ℝ)
  rw [coe_moebius_mul_coe_zeta, pmul_zeta, pointwise_h_one] at H
  exact H.symm

noncomputable def heightCorrection (w : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  invNatMoebius * w

theorem height_correction_convolution (w : ArithmeticFunction ℝ) :
    heightCorrection w * invNatWeight = w := by
  simp only [heightCorrection]
  rw [mul_comm invNatMoebius w, mul_assoc, invNatMoebius_mul_invNatWeight, mul_one]

theorem height_correction_multiplicative {w : ArithmeticFunction ℝ} (hw : w.IsMultiplicative) :
    (heightCorrection w).IsMultiplicative :=
  (invNatWeight_multiplicative.pmul isMultiplicative_moebius.intCast).mul hw

private theorem invNatMoebius_apply_one : invNatMoebius 1 = 1 := by
  simp [invNatMoebius]

private theorem invNatMoebius_apply_prime {p : ℕ} (hp : p.Prime) :
    invNatMoebius p = -1/(p:ℝ) := by
  change (p:ℝ)⁻¹ * ((ArithmeticFunction.moebius p : ℤ) : ℝ) = _
  rw [moebius_apply_prime hp]
  push_cast
  ring

private theorem invNatMoebius_apply_prime_pow_large {p k : ℕ} (hp : p.Prime) (hk : 1 < k) :
    invNatMoebius (p^k) = 0 := by
  simp [invNatMoebius,moebius_apply_prime_pow hp (by omega : k ≠ 0), show k ≠ 1 by omega]

private theorem npow_div_prime {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    p^k / p = p^(k-1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [pow_succ, Nat.mul_div_cancel _ hp.pos, Nat.succ_sub_one]

theorem height_correction_at_prime_power (w : ArithmeticFunction ℝ) {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    heightCorrection w (p^k) = w (p^k) - w (p^(k-1))/(p:ℝ) := by
  rw [heightCorrection, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => invNatMoebius i * w j),
    Nat.sum_divisors_prime_pow hp]
  rw [← sum_subset (show range 2 ⊆ range (k+1) by
    intro i hi
    simp only [mem_range] at hi ⊢
    omega) (fun i hi h₂ => by
      have hgt : 1 < i := by simp only [mem_range] at h₂; omega
      rw [invNatMoebius_apply_prime_pow_large hp hgt, zero_mul])]
  rw [sum_range_succ, sum_range_one, pow_zero, pow_one, invNatMoebius_apply_one,
    invNatMoebius_apply_prime hp, npow_div_prime hp hk, Nat.div_one, one_mul]
  ring



def HeightGoodRows (B : ℕ) (w : ArithmeticFunction ℝ) : Prop :=
  w.IsMultiplicative ∧
    ∀ p : ℕ, p.Prime →
      w p = (if p ∣ B then 0 else 1/((p:ℝ)-2)) ∧
      ∀ k : ℕ, 1 < k → w (p^k) = 0

theorem height_correction_rows {B : ℕ} (heB : Even B) {w : ArithmeticFunction ℝ}
    (hw : HeightGoodRows B w) : HeightCorrectionRows B (heightCorrection w) := by
  have hm := height_correction_multiplicative hw.1
  refine ⟨(heightCorrection w).map_zero, hm.1, hm.2, ?_⟩
  intro p hp
  obtain ⟨wp, wpPow⟩ := hw.2 p hp
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨?_, ?_, ?_⟩
  · have h := height_correction_at_prime_power w hp (k := 1) (by decide)
    simp only [pow_one, Nat.reduceSub, pow_zero, hw.1.1, wp] at h
    rw [h]
    by_cases hB : p ∣ B
    · simp only [hB, ite_true, zero_sub, neg_div]
    · have hp3 : 3 ≤ p := by
        by_contra! hh
        have e : p = 2 := by have := hp.two_le; omega
        exact hB (e.symm ▸ heB.two_dvd)
      have hp3' : (3:ℝ) ≤ p := by exact_mod_cast hp3
      have hp2 : (p:ℝ)-2 ≠ 0 := by linarith
      simp only [hB, ite_false]
      field_simp
      ring
  · rw [height_correction_at_prime_power w hp (by decide), wpPow _ (by decide),
      show (2:ℕ)-1 = 1 by decide, pow_one, wp]
    by_cases hb : p ∣ B
    · simp only [hb, ite_true, zero_div, sub_zero]
    · simp only [hb, ite_false, zero_sub, div_div, neg_div]
      rw [mul_comm ((p:ℝ)-2) (p:ℝ)]
  · intro k hk
    rw [height_correction_at_prime_power w hp (by omega), wpPow _ (by omega),
      wpPow _ (by omega), zero_div, sub_zero]

end SignedHeight
end HeightProductionSection10

section HeightProductionSection11
open Finset ArithmeticFunction
open scoped BigOperators

namespace SignedHeight

noncomputable def heightGoodWeight (B : ℕ) : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n => if Squarefree n ∧ n.Coprime B then
      ∏ p ∈ n.primeFactors, 1/((p:ℝ)-2) else 0, by simp⟩

theorem heightGoodWeight_apply (B n : ℕ) :
    heightGoodWeight B n = if Squarefree n ∧ n.Coprime B then
      ∏ p ∈ n.primeFactors, 1/((p:ℝ)-2) else 0 := by
  classical
  rfl

theorem height_good_weight_rows (B : ℕ) :
    HeightGoodRows B (heightGoodWeight B) := by
  classical
  constructor
  · constructor
    · simp [heightGoodWeight_apply]
    · intro m n hmn
      simp only [heightGoodWeight_apply]
      have H : Squarefree (m*n) ∧ (m*n).Coprime B ↔
          (Squarefree m ∧ m.Coprime B) ∧ (Squarefree n ∧ n.Coprime B) := by
        rw [Nat.squarefree_mul hmn, Nat.coprime_mul_iff_left]
        tauto
      by_cases hm : Squarefree m ∧ m.Coprime B
      · by_cases hn : Squarefree n ∧ n.Coprime B
        · rw [if_pos (H.mpr ⟨hm,hn⟩), if_pos hm, if_pos hn, hmn.primeFactors_mul,
            prod_union hmn.disjoint_primeFactors]
        · rw [if_neg (fun h => hn (H.mp h).2), if_pos hm, if_neg hn, mul_zero]
      · rw [if_neg (fun h => hm (H.mp h).1), if_neg hm, zero_mul]
  · intro p hp
    constructor
    · rw [heightGoodWeight_apply, hp.primeFactors, prod_singleton]
      simp only [hp.squarefree, true_and, hp.coprime_iff_not_dvd]
      by_cases h : p ∣ B <;> simp [h]
    · intro k hk
      have hn : ¬Squarefree (p^k) := by
        rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
        exact fun e => by have := e.2; omega
      simp [heightGoodWeight_apply,hn]

end SignedHeight
end HeightProductionSection11

section HeightProductionSection12
open Finset Filter
open scoped BigOperators Topology

namespace SignedHeight

noncomputable def heightOrdinaryPrimeFactor (m p : ℕ) : ℝ :=
  if p ∣ m then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2

noncomputable def heightBadPrimeFactor (B m p : ℕ) : ℝ :=
  if p ∣ B ∧ ¬p ∣ m then ((p:ℝ)-1)/((p:ℝ)-2) else 1

theorem height_ordinary_prime_ne_zero {m p : ℕ} (he : Even m) (hp : p.Prime) :
    heightOrdinaryPrimeFactor m p ≠ 0 := by
  have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  unfold heightOrdinaryPrimeFactor
  split_ifs with hm
  · exact div_ne_zero hp0 (by linarith)
  · have pn : p ≠ 2 := fun h => hm (h.symm ▸ he.two_dvd)
    have h3 : 3 ≤ p := by have := hp.two_le; omega
    have h3' : (3:ℝ) ≤ p := by exact_mod_cast h3
    exact div_ne_zero (mul_ne_zero hp0 (by linarith)) (pow_ne_zero _ (by linarith))

theorem height_corrector_euler_product {B : ℕ} (he : Even B) {g : ℕ → ℝ}
    (hg : HeightCorrectionRows B g) (hgs : Summable (‖g ·‖)) :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, heightCorrectorPrimeFactor B p)
      atTop (𝓝 (∑' n, g n)) := by
  have H := EulerProduct.eulerProduct hg.2.1 hg.2.2.1 hgs hg.1
  apply H.congr
  intro N
  exact prod_congr rfl (fun p hp => height_correction_euler_row he hg (Nat.mem_primesBelow.mp hp).2)

private theorem height_local_products_reciprocal {B m N : ℕ} (hB : B ≠ 0)
    (hBlt : B < N) (hem : Even m) (hmB : m ∣ B) :
    ((∏ p ∈ B.primeFactors, heightBadPrimeFactor B m p) *
      (∏ p ∈ N.primesBelow, heightCorrectorPrimeFactor B p)) *
      (∏ p ∈ N.primesBelow, heightOrdinaryPrimeFactor m p) = 1 := by
  have sub : B.primeFactors ⊆ N.primesBelow := by
    intro p hp
    have div := Nat.dvd_of_mem_primeFactors hp
    refine Nat.mem_primesBelow.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hB) div).trans_lt hBlt,
      Nat.prime_of_mem_primeFactors hp⟩
  have hb : (∏ p ∈ B.primeFactors, heightBadPrimeFactor B m p) =
      ∏ p ∈ N.primesBelow, heightBadPrimeFactor B m p := by
    apply prod_subset sub
    intro p hp hnp
    have hpd : ¬p ∣ B := fun h =>
      hnp (Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesBelow.mp hp).2,h,hB⟩)
    simp [heightBadPrimeFactor,hpd]
  rw [hb, ← prod_mul_distrib, ← prod_mul_distrib]
  trans ∏ _p ∈ N.primesBelow, (1:ℝ)
  · apply prod_congr rfl
    intro p hp
    rw [mul_comm (heightBadPrimeFactor B m p)]
    have he := height_correction_reciprocal_prime (B := B) hem hmB (Nat.mem_primesBelow.mp hp).2
    change heightCorrectorPrimeFactor B p * heightBadPrimeFactor B m p =
      (heightOrdinaryPrimeFactor m p)⁻¹ at he
    rw [he, inv_mul_cancel₀ (height_ordinary_prime_ne_zero hem (Nat.mem_primesBelow.mp hp).2)]
  · simp



theorem height_normalized_mass {B m : ℕ} (hB : B ≠ 0) (hem : Even m) (hmB : m ∣ B)
    {g : ℕ → ℝ} (hg : HeightCorrectionRows B g) (hgs : Summable (‖g ·‖))
    {O : ℝ} (hO : O ≠ 0)
    (hlim : Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, heightOrdinaryPrimeFactor m p)
      atTop (𝓝 O)) :
    (∏ p ∈ B.primeFactors, heightBadPrimeFactor B m p) * (∑' n, g n) = O⁻¹ := by
  let A := ∏ p ∈ B.primeFactors, heightBadPrimeFactor B m p
  have heB : Even B := even_iff_two_dvd.mpr (hem.two_dvd.trans hmB)
  have hG := height_corrector_euler_product heB hg hgs
  have hlimit : Tendsto (fun N : ℕ => A *
          (∏ p ∈ N.primesBelow, heightCorrectorPrimeFactor B p) *
          (∏ p ∈ N.primesBelow, heightOrdinaryPrimeFactor m p))
        atTop (𝓝 (A * (∑' n, g n) * O)) :=
    (tendsto_const_nhds.mul hG).mul hlim
  have hconst : ∀ᶠ N : ℕ in atTop, A *
          (∏ p ∈ N.primesBelow, heightCorrectorPrimeFactor B p) *
          (∏ p ∈ N.primesBelow, heightOrdinaryPrimeFactor m p) = 1 :=
    (eventually_gt_atTop B).mono (fun N hN => height_local_products_reciprocal hB hN hem hmB)
  have one := tendsto_nhds_unique (hlimit.congr' hconst) (tendsto_const_nhds (x := (1:ℝ)))
  change A * (∑' n, g n) = _
  calc
    _ = (A * (∑' n, g n) * O) * O⁻¹ := by rw [mul_assoc (A * (∑' n, g n)) O, mul_inv_cancel₀ hO, mul_one]
    _ = _ := by rw [one, one_mul]



theorem primeFactors_factorial_eq_primesBelow (n : ℕ) :
    n.factorial.primeFactors = (n+1).primesBelow := by
  ext p
  constructor
  · intro hp
    have pp := Nat.prime_of_mem_primeFactors hp
    exact Nat.mem_primesBelow.mpr ⟨(pp.dvd_factorial.mp (Nat.dvd_of_mem_primeFactors hp)).trans_lt (Nat.lt_succ_self _),pp⟩
  · intro hp
    obtain ⟨hlt,pp⟩ := Nat.mem_primesBelow.mp hp
    exact Nat.mem_primeFactors.mpr ⟨pp,pp.dvd_factorial.mpr (Nat.le_of_lt_succ hlt),n.factorial_ne_zero⟩

end SignedHeight
end HeightProductionSection12

section HeightProductionSection13
open Finset Filter Real
open scoped BigOperators

namespace SignedHeight

private theorem quarter_bound_good_prime {x : ℝ} (hx : 3 ≤ x) :
    2/(x*(x-2)) * x^(1/4:ℝ) +
      1/(x*(x-2)) * (x^2)^(1/4:ℝ) ≤ 9*x^(-(3/2):ℝ) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hxp : 0 < x*(x-2) := mul_pos hx0 (by linarith)
  have hpow0 : 0 < x^2 := by positivity
  have hd : 1/(x*(x-2)) ≤ 3/x^2 := by
    apply (div_le_div_iff₀ hxp hpow0).2
    nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx)]
  have hd2 : 2/(x*(x-2)) ≤ 6/x^2 := by
    have e := mul_le_mul_of_nonneg_left hd (show 0 ≤ (2:ℝ) by norm_num)
    simpa only [← mul_div_assoc, mul_one, show (2:ℝ)*3=6 by norm_num] using e
  have he : (x^2)^(1/4:ℝ) = x^(1/2:ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
  have c1 : 6/x^2 * x^(1/4:ℝ) = 6*x^(-(7/4):ℝ) := by
    rw [show (-(7/4):ℝ) = 1/4-2 by norm_num, Real.rpow_sub hx0, Real.rpow_two]
    ring
  have c2 : 3/x^2 * x^(1/2:ℝ) = 3*x^(-(3/2):ℝ) := by
    rw [show (-(3/2):ℝ) = 1/2-2 by norm_num, Real.rpow_sub hx0, Real.rpow_two]
    ring
  have hw1 := mul_le_mul_of_nonneg_right hd2 (Real.rpow_nonneg hx0.le (1/4:ℝ))
  have hw2 := mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (sq_nonneg x) (1/4:ℝ))
  have hw3 := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx1 (show (-(7/4):ℝ) ≤ -(3/2) by norm_num))
    (show 0 ≤ (6:ℝ) by norm_num)
  rw [c1] at hw1
  rw [he,c2] at hw2
  rw [he]
  linarith

private theorem quarter_bound_bad_prime {x : ℝ} (hx : 1 ≤ x) :
    1/x * x^(1/4:ℝ) ≤ 1 := by
  have hx0 : 0 < x := by linarith
  rw [one_div, inv_mul_eq_div]
  apply (div_le_one hx0).2
  calc
    _ ≤ x^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
    _ = x := Real.rpow_one x

theorem height_correction_summable {B : ℕ} (hB : B ≠ 0) (hev : Even B)
    {g : ℕ → ℝ} (hr : HeightCorrectionRows B g) :
    Summable (fun n => ‖g n‖) ∧ Summable (fun n => ‖g n‖ * Real.log (n:ℝ)) := by
  classical
  obtain ⟨h0, h1, mulg, rows⟩ := hr
  let f (n : ℕ) : ℝ := ‖g n‖ * (n:ℝ)^(1/4:ℝ)
  let bad (n : ℕ) : ℝ := if n ∣ B then 1 else 0
  let c (n : ℕ) := bad n + 9*(n:ℝ)^(-(3/2):ℝ)
  have fpos (n : ℕ) : 0 ≤ f n := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
  have f0 : f 0 = 0 := by simp [f,h0]
  have f1 : f 1 = 1 := by simp [f,h1]
  have fmul {m n : ℕ} (h : m.Coprime n) : f (m*n) = f m * f n := by
    simp only [f, mulg h, norm_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have cpos (n : ℕ) : 0 ≤ c n := by
    have hb : 0 ≤ bad n := by simp only [bad]; split_ifs <;> norm_num
    exact add_nonneg hb (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
  have sb : Summable bad := by
    apply summable_of_ne_finset_zero (s := B.divisors)
    intro n hn
    have h : ¬n ∣ B := fun d => hn (Nat.mem_divisors.mpr ⟨d,hB⟩)
    simp [bad,h]
  have sc : Summable c := sb.add ((Real.summable_nat_rpow.mpr (by norm_num : (-(3/2):ℝ) < -1)).mul_left _)
  have rzero {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : k ∉ range 3) : f (p^k) = 0 := by
    have hk' : 2 < k := by simp only [mem_range] at hk; omega
    simp only [f,(rows p hp).2.2 _ hk',norm_zero,zero_mul]
  have frows {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => f (p^k)) :=
    summable_of_ne_finset_zero (s := range 3) (rzero hp)
  have fbounds {p : ℕ} (hp : p.Prime) : (∑' k : ℕ, f (p^k)) ≤ 1+c p := by
    rw [tsum_eq_sum (s := range 3) (rzero hp)]
    rw [show (range 3 : Finset ℕ) = insert 2 (insert 1 {0}) by decide,
      sum_insert (by decide),sum_insert (by decide),sum_singleton,pow_zero,pow_one,f1]
    obtain ⟨t1,t2,_⟩ := rows p hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    by_cases hd : p ∣ B
    · have pp : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      have hb := quarter_bound_bad_prime pp
      rw [show f p = 1/(p:ℝ) * (p:ℝ)^(1/4:ℝ) by
        simp only [f,t1,hd,ite_true,neg_div, Real.norm_eq_abs,abs_neg,abs_of_nonneg (by positivity : 0 ≤ 1/(p:ℝ))]]
      rw [show f (p^2) = 0 by simp only [f,t2,hd,ite_true,norm_zero,zero_mul]]
      have hc' : 0 ≤ 9*(p:ℝ)^(-(3/2):ℝ) := by positivity
      simp only [c,bad,hd,ite_true]
      linarith
    · have pp : 3 ≤ p := by
        by_contra! h
        have pe : p = 2 := by have := hp.two_le; omega
        exact hd (pe.symm ▸ hev.two_dvd)
      have hh : (3:ℝ) ≤ p := by exact_mod_cast pp
      have hp2 : 0 < (p:ℝ)-2 := by linarith
      have hb := quarter_bound_good_prime hh
      rw [show f p = 2/((p:ℝ)*((p:ℝ)-2)) * (p:ℝ)^(1/4:ℝ) by
        simp only [f,t1,hd,ite_false,Real.norm_eq_abs,abs_of_nonneg (by positivity :
          0 ≤ 2/((p:ℝ)*((p:ℝ)-2)))]]
      rw [show f (p^2) = 1/((p:ℝ)*((p:ℝ)-2)) * ((p:ℝ)^2)^(1/4:ℝ) by
        simp only [f,t2,hd,ite_false,neg_div,Real.norm_eq_abs,abs_neg,abs_of_nonneg (by positivity :
          0 ≤ 1/((p:ℝ)*((p:ℝ)-2))),Nat.cast_pow]]
      simp only [c,bad,hd,ite_false,zero_add]
      linarith
  have sf : Summable f :=
    summable_nonneg_of_prime_power_rows f c fpos f0 f1 fmul cpos sc frows fbounds
  constructor
  · apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ sf
    intro n
    by_cases h : n = 0
    · subst n; rw [h0,norm_zero,f0]
    · have p : (1:ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h
      have hpow := Real.one_le_rpow p (show (0:ℝ) ≤ 1/4 by norm_num)
      exact le_mul_of_one_le_right (norm_nonneg _) hpow
  · apply Summable.of_nonneg_of_le _
      (f := fun n => 4*f n) _ (sf.mul_left 4)
    · intro n
      by_cases h : n = 0
      · subst n; simp [h0]
      · exact mul_nonneg (norm_nonneg _) (Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h))
    · intro n
      have b := Real.log_le_rpow_div (Nat.cast_nonneg n) (show (0:ℝ) < 1/4 by norm_num)
      have c := mul_le_mul_of_nonneg_left b (norm_nonneg (g n))
      dsimp only [f]
      linarith only [c, show ‖g n‖ * ((n:ℝ)^(1/4:ℝ) / (1/4)) = 4*(‖g n‖*(n:ℝ)^(1/4:ℝ)) by ring]

end SignedHeight
end HeightProductionSection13

section HeightProductionSection14
open Finset Filter ArithmeticFunction
open scoped BigOperators Topology

namespace SignedHeight

noncomputable def goodHeightCorrection (B : ℕ) : ArithmeticFunction ℝ :=
  heightCorrection (heightGoodWeight B)

theorem good_height_correction_rows {B : ℕ} (heB : Even B) :
    HeightCorrectionRows B (goodHeightCorrection B) :=
  height_correction_rows heB (height_good_weight_rows B)

theorem good_height_correction_divisor_identity (B n : ℕ) :
    (∑ d ∈ n.divisors, goodHeightCorrection B d * (((n/d : ℕ):ℝ)⁻¹)) =
      heightGoodWeight B n := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n)
    (height_correction_convolution (heightGoodWeight B))
  change (goodHeightCorrection B * invNatWeight) n = _ at h
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => goodHeightCorrection B i * invNatWeight j)] at h
  simpa only [invNatWeight_apply] using h

theorem good_height_correction_sums {B : ℕ} (hB : B ≠ 0) (heB : Even B) :
    Summable (fun n => ‖goodHeightCorrection B n‖) ∧
      Summable (fun n => ‖goodHeightCorrection B n‖ * Real.log (n:ℝ)) :=
  height_correction_summable hB heB (good_height_correction_rows heB)

theorem ordinary_product_limit_of_factorial (m : ℕ) {O : ℝ}
    (h : Tendsto (fun n : ℕ => ∏ p ∈ n.factorial.primeFactors, heightOrdinaryPrimeFactor m p)
      atTop (𝓝 O)) :
    Tendsto (fun n : ℕ => ∏ p ∈ n.primesBelow, heightOrdinaryPrimeFactor m p)
      atTop (𝓝 O) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [primeFactors_factorial_eq_primesBelow] using h

theorem exact_height_correction_log_coefficient {B m : ℕ}
    (hB : B ≠ 0) (he : Even m) (hdiv : m ∣ B) {O : ℝ} (hO : O ≠ 0)
    (hOrd : Tendsto (fun n : ℕ => ∏ p ∈ n.factorial.primeFactors, heightOrdinaryPrimeFactor m p)
      atTop (𝓝 O)) :
    (∏ p ∈ B.primeFactors, heightBadPrimeFactor B m p) *
      (∑' n : ℕ, goodHeightCorrection B n) = O⁻¹ := by
  have hevB := even_iff_two_dvd.mpr (he.two_dvd.trans hdiv)
  exact height_normalized_mass hB he hdiv (good_height_correction_rows hevB)
    (good_height_correction_sums hB hevB).1 hO (ordinary_product_limit_of_factorial m hOrd)

end SignedHeight
end HeightProductionSection14

section HeightProductionSection15
open Filter Finset
open scoped BigOperators Topology

namespace SignedHeight


noncomputable def heightPrincipJacobi (q m : ℕ) [NeZero q] : ℂ :=
  ∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) ((m:ZMod q)-x)


noncomputable def heightFiniteOrdinary (q m : ℕ) [NeZero q] : ℝ :=
  (q:ℝ) * ‖heightPrincipJacobi q m‖ / (q.totient:ℝ)^2



noncomputable def heightNormalizedPrincipal (q m : ℕ) [NeZero q] : ℂ :=
  ((q:ℂ)*heightPrincipJacobi q m)/(q.totient:ℂ)^2

theorem height_norm_normalized_principal (q m : ℕ) [NeZero q] :
    ‖heightNormalizedPrincipal q m‖ = heightFiniteOrdinary q m := by
  simp only [heightNormalizedPrincipal,heightFiniteOrdinary,norm_div,norm_mul,norm_pow,Complex.norm_natCast]



theorem height_ordinary_factorial_limit
    (m : ℕ) (C : ℕ → ℂ) {S : ℂ}
    (lim : Tendsto (fun n : ℕ => ∑ d ∈ n.factorial.divisors, C d) atTop (𝓝 S))
    (ambient : ∀ q : ℕ, ∀ [NeZero q], heightNormalizedPrincipal q m = ∑ d ∈ q.divisors, C d)
    (prodOrd : ∀ q : ℕ, ∀ [NeZero q], heightFiniteOrdinary q m =
      ∏ p ∈ q.primeFactors, heightOrdinaryPrimeFactor m p) :
    Tendsto (fun n : ℕ => ∏ p ∈ n.factorial.primeFactors, heightOrdinaryPrimeFactor m p)
      atTop (𝓝 ‖S‖) := by
  apply lim.norm.congr
  intro n
  letI : NeZero n.factorial := ⟨n.factorial_ne_zero⟩
  rw [← prodOrd n.factorial, ← height_norm_normalized_principal n.factorial m, ambient n.factorial]

end SignedHeight
end HeightProductionSection15

section HeightProductionSection16
namespace SignedHeight

open Finset

theorem zero_of_equal_nonneg_subtotals {ι : Type*} [DecidableEq ι]
    {A B : Finset ι} {w : ι → ℝ} (hs : A ⊆ B) (hn : ∀ a ∈ B, 0 ≤ w a)
    (h : ∑ a ∈ A, w a = ∑ a ∈ B, w a) {a : ι} (ha : a ∈ B) (ha0 : a ∉ A) :
    w a = 0 := by
  have s := sum_sdiff hs (f := w)
  have hz : ∑ x ∈ B \ A, w x = 0 := by linarith
  have hl := single_le_sum (f := w) (s := B \ A)
    (fun x hx => hn x (mem_sdiff.mp hx).1) (mem_sdiff.mpr ⟨ha,ha0⟩)
  exact le_antisymm (hl.trans_eq hz) (hn a ha)

end SignedHeight
end HeightProductionSection16

section HeightProductionSection17
open Finset DirichletCharacter
open scoped BigOperators Classical

namespace SignedHeight


theorem conductor_mul_of_coprime {L : ℕ} [NeZero L] (A B : DirichletCharacter ℂ L)
    (h : A.conductor.Coprime B.conductor) :
    (A*B).conductor=A.conductor*B.conductor := by
  let Z := A*B
  have Aeq : Z*B⁻¹=A := by simp [Z, mul_assoc]
  have Beq : Z*A⁻¹=B := by rw [show Z = B*A from mul_comm ..]; simp [mul_assoc]
  have dA := conductor_mul_dvd_lcm_conductor Z B⁻¹
  have dB := conductor_mul_dvd_lcm_conductor Z A⁻¹
  rw [Aeq,conductor_inv] at dA
  rw [Beq,conductor_inv] at dB
  have one := h.dvd_of_dvd_mul_right (dA.trans (Nat.lcm_dvd_mul ..))
  have two := h.symm.dvd_of_dvd_mul_right (dB.trans (Nat.lcm_dvd_mul ..))
  exact Nat.dvd_antisymm ((conductor_mul_dvd_lcm_conductor A B).trans (Nat.lcm_dvd_mul ..))
    (h.mul_dvd_of_dvd_of_dvd one two)

theorem coprime_conductor_mul_match {a b u v c d : ℕ} (h : a.Coprime b)
    (hu : u ∣ a) (hv : v ∣ b) (hc : c ∣ a) (hd : d ∣ b) :
    u*v=c*d ↔ u=c ∧ v=d := by
  constructor
  · intro E
    have gcdAux {i j x y : ℕ} (H : x.Coprime y) (hi : i ∣ x) (hj : j ∣ y) :
        x.gcd (i*j) = i := by
      have hX : j.Coprime x := (H.of_dvd_right hj).symm
      rw [hX.gcd_mul_right_cancel_right, Nat.gcd_eq_right hi]
    have eu : u=c := calc
      _ = a.gcd (u*v) := (gcdAux h hu hv).symm
      _ = a.gcd (c*d) := congrArg (a.gcd) E
      _ = _ := gcdAux h hc hd
    have ev : v=d := calc
      _ = b.gcd (v*u) := (gcdAux h.symm hv hu).symm
      _ = b.gcd (d*c) := congrArg (b.gcd) (by simpa [mul_comm] using E)
      _ = _ := gcdAux h.symm hd hc
    exact ⟨eu,ev⟩
  · rintro ⟨rfl,rfl⟩
    rfl



theorem sum_exact_origin {D s : ℕ} [NeZero D] (hs : s ∣ D)
    (f : DirichletCharacter ℂ s → ℝ) (g : DirichletCharacter ℂ D → ℝ)
    (hfg : ∀ c, c.IsPrimitive → f c = g (changeLevel hs c)) :
    (∑ c : DirichletCharacter ℂ s, if c.IsPrimitive then f c else 0) =
      ∑ C : DirichletCharacter ℂ D, if C.conductor = s then g C else 0 := by
  classical
  let U : Finset (DirichletCharacter ℂ s) := univ.filter (fun c => c.IsPrimitive)
  let e : DirichletCharacter ℂ s ↪ DirichletCharacter ℂ D :=
    ⟨changeLevel hs, changeLevel_injective hs⟩
  have E : U.map e = univ.filter (fun c : DirichletCharacter ℂ D => c.conductor = s) := by
    ext c
    simp only [U, e, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact (conductor_changeLevel B hs).trans hB
    · intro hc
      have H : ∀ k : ℕ, c.conductor = k → ∀ h : k ∣ D,
          ∃ B : DirichletCharacter ℂ k, B.IsPrimitive ∧ changeLevel h B = c := by
        intro k hk hd
        subst k
        exact ⟨c.primitiveCharacter, c.primitiveCharacter_isPrimitive, changeLevel_primitiveCharacter c⟩
      exact H s hc hs
  calc
    _ = ∑ c ∈ U, f c := (Finset.sum_filter ..).symm
    _ = ∑ c ∈ U, g (e c) := Finset.sum_congr rfl fun c hc => hfg c (mem_filter.mp hc).2
    _ = ∑ c ∈ U.map e, g c := (Finset.sum_map ..).symm
    _ = _ := by rw [E, Finset.sum_filter]

end SignedHeight
end HeightProductionSection17

section HeightProductionSection18
open Finset DirichletCharacter
open scoped BigOperators Classical

namespace SignedHeight
namespace CRT

variable {a b : ℕ} (h : a.Coprime b)
include h

set_option maxHeartbeats 800000 in
noncomputable def left (χ : DirichletCharacter ℂ (a*b)) : DirichletCharacter ℂ a where
  toFun x := χ ((ZMod.chineseRemainder h).symm (x,1))
  map_one' := by
    change χ ((ZMod.chineseRemainder h).symm 1) = 1
    rw [map_one, map_one]
  map_mul' x y := by
    have E : (x*y, (1:ZMod b)) = (x,(1:ZMod b)) * (y,1) := by simp
    rw [E, map_mul, map_mul]
  map_nonunit' x hx := by
    apply χ.map_nonunit
    intro hu
    have H : IsUnit (x, (1:ZMod b)) := by
      have HH := hu.map (ZMod.chineseRemainder h).toMonoidHom
      change IsUnit ((ZMod.chineseRemainder h) ((ZMod.chineseRemainder h).symm _)) at HH
      simpa only [RingEquiv.apply_symm_apply] using HH
    exact hx (Prod.isUnit_iff.mp H).1

set_option maxHeartbeats 800000 in
noncomputable def right (χ : DirichletCharacter ℂ (a*b)) : DirichletCharacter ℂ b where
  toFun y := χ ((ZMod.chineseRemainder h).symm (1,y))
  map_one' := by
    change χ ((ZMod.chineseRemainder h).symm 1) = 1
    rw [map_one, map_one]
  map_mul' x y := by
    have E : ((1:ZMod a), x*y) = ((1:ZMod a),x) * (1,y) := by simp
    rw [E, map_mul, map_mul]
  map_nonunit' x hx := by
    apply χ.map_nonunit
    intro hu
    have H : IsUnit ((1:ZMod a), x) := by
      have HH := hu.map (ZMod.chineseRemainder h).toMonoidHom
      change IsUnit ((ZMod.chineseRemainder h) ((ZMod.chineseRemainder h).symm _)) at HH
      simpa only [RingEquiv.apply_symm_apply] using HH
    exact hx (Prod.isUnit_iff.mp H).2

noncomputable def glue (_h : a.Coprime b) (A : DirichletCharacter ℂ a) (B : DirichletCharacter ℂ b) :
    DirichletCharacter ℂ (a*b) :=
  changeLevel (dvd_mul_right a b) A * changeLevel (dvd_mul_left b a) B

theorem reassemble (χ : DirichletCharacter ℂ (a*b)) (x : ZMod (a*b)) :
    χ x = left h χ ((ZMod.chineseRemainder h) x).1 * right h χ ((ZMod.chineseRemainder h) x).2 := by
  rw [left, right]
  change χ x = χ ((ZMod.chineseRemainder h).symm (((ZMod.chineseRemainder h) x).1,1)) *
      χ ((ZMod.chineseRemainder h).symm (1,((ZMod.chineseRemainder h) x).2))
  rw [← map_mul, ← map_mul]
  have E (v : ZMod a × ZMod b) : (v.1,1)*(1,v.2) = v := by ext <;> simp
  rw [E, RingEquiv.symm_apply_apply]

variable [NeZero (a*b)]

theorem glue_apply_unit (A : DirichletCharacter ℂ a) (B : DirichletCharacter ℂ b)
    (u : (ZMod (a*b))ˣ) :
    glue h A B u = A ((ZMod.chineseRemainder h) u).1 * B ((ZMod.chineseRemainder h) u).2 := by
  rw [glue, MulChar.mul_apply, changeLevel_eq_cast_of_dvd, changeLevel_eq_cast_of_dvd]
  have hu : (((u : ZMod (a*b)).val : ℕ) : ZMod (a*b)) = (u : ZMod (a*b)) :=
    ZMod.natCast_zmod_val _
  have e1 : ZMod.cast (u : ZMod (a*b)) = ((ZMod.chineseRemainder h) u).1 := by
    rw [← hu, ZMod.cast_natCast (dvd_mul_right a b), map_natCast]
    rfl
  have e2 : ZMod.cast (u : ZMod (a*b)) = ((ZMod.chineseRemainder h) u).2 := by
    rw [← hu, ZMod.cast_natCast (dvd_mul_left b a), map_natCast]
    rfl
  rw [e1, e2]

theorem glue_apply (A : DirichletCharacter ℂ a) (B : DirichletCharacter ℂ b)
    (x : ZMod (a*b)) :
    glue h A B x = A ((ZMod.chineseRemainder h) x).1 * B ((ZMod.chineseRemainder h) x).2 := by
  by_cases hx : IsUnit x
  · exact glue_apply_unit h A B hx.unit
  · rw [(glue h A B).map_nonunit hx]
    by_cases hl : IsUnit ((ZMod.chineseRemainder h) x).1
    · have hr : ¬ IsUnit ((ZMod.chineseRemainder h) x).2 := by
        intro hy
        apply hx
        have H : IsUnit ((ZMod.chineseRemainder h) x) := Prod.isUnit_iff.mpr ⟨hl,hy⟩
        simpa using H.map (ZMod.chineseRemainder h).symm
      rw [B.map_nonunit hr, mul_zero]
    · rw [A.map_nonunit hl, zero_mul]

theorem left_glue (A : DirichletCharacter ℂ a) (B : DirichletCharacter ℂ b) :
    left h (glue h A B) = A := by
  apply MulChar.ext'
  intro x
  change glue h A B ((ZMod.chineseRemainder h).symm (x,1)) = A x
  rw [glue_apply, RingEquiv.apply_symm_apply]
  simp

theorem right_glue (A : DirichletCharacter ℂ a) (B : DirichletCharacter ℂ b) :
    right h (glue h A B) = B := by
  apply MulChar.ext'
  intro x
  change glue h A B ((ZMod.chineseRemainder h).symm (1,x)) = B x
  rw [glue_apply, RingEquiv.apply_symm_apply]
  simp

theorem glue_split (χ : DirichletCharacter ℂ (a*b)) :
    glue h (left h χ) (right h χ) = χ := by
  apply MulChar.ext'
  intro x
  rw [glue_apply, ← reassemble]

noncomputable def chEquiv : DirichletCharacter ℂ (a*b) ≃
    DirichletCharacter ℂ a × DirichletCharacter ℂ b where
  toFun χ := (left h χ, right h χ)
  invFun P := glue h P.1 P.2
  left_inv := glue_split h
  right_inv P := Prod.ext (left_glue h P.1 P.2) (right_glue h P.1 P.2)

noncomputable def J {q : ℕ} [NeZero q] (A B : DirichletCharacter ℂ q) (m : ZMod q) : ℂ :=
  ∑ x : ZMod q, A x * B (m-x)

theorem jacobi_glue [NeZero a] [NeZero b]
    (A C : DirichletCharacter ℂ a) (B D : DirichletCharacter ℂ b) (m : ℕ) :
    J (glue h A B) (glue h C D) (m : ZMod (a*b)) =
      J A C (m : ZMod a) * J B D (m : ZMod b) := by
  classical
  unfold J
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Fintype.sum_prod_type (fun x : ZMod a × ZMod b =>
    A x.1 * C ((m : ZMod a)-x.1) * (B x.2 * D ((m : ZMod b)-x.2)))]
  let E := ZMod.chineseRemainder h
  calc
    _ = ∑ x : ZMod a × ZMod b, glue h A B (E.symm x) *
          glue h C D ((m : ZMod (a*b)) - E.symm x) := (Equiv.sum_comp E.symm.toEquiv _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      simp only [glue_apply, RingEquiv.map_sub, map_natCast, E,
        RingEquiv.apply_symm_apply, Prod.fst_sub, Prod.snd_sub, Prod.fst_natCast, Prod.snd_natCast]
      ring

end CRT
end SignedHeight
end HeightProductionSection18

section HeightProductionSection19
open Finset DirichletCharacter
open scoped BigOperators Classical

namespace SignedHeight
namespace CRT

variable {a b : ℕ} (h : a.Coprime b) [NeZero a] [NeZero b] [NeZero (a*b)]
include h

theorem glue_conductor (C : DirichletCharacter ℂ a) (D : DirichletCharacter ℂ b) :
    (glue h C D).conductor = C.conductor * D.conductor := by
  unfold glue
  rw [conductor_mul_of_coprime, conductor_changeLevel, conductor_changeLevel]
  rw [conductor_changeLevel, conductor_changeLevel]
  exact h.of_dvd C.conductor_dvd_level D.conductor_dvd_level

noncomputable def weight {q : ℕ} [NeZero q] (A C : DirichletCharacter ℂ q) (m : ℕ) : ℝ :=
  ‖J A C (m : ZMod q) / J 1 1 (m : ZMod q)‖^2

theorem glue_one : glue h (1 : DirichletCharacter ℂ a) (1 : DirichletCharacter ℂ b) = 1 := by
  simp [glue]

theorem glue_left (A : DirichletCharacter ℂ a) :
    glue h A (1 : DirichletCharacter ℂ b) = changeLevel (dvd_mul_right a b) A := by
  simp [glue]

theorem weight_glue (A C : DirichletCharacter ℂ a) (B D : DirichletCharacter ℂ b) (m : ℕ) :
    weight (glue h A B) (glue h C D) m = weight A C m * weight B D m := by
  unfold weight
  rw [jacobi_glue, ← glue_one h, jacobi_glue]
  rw [mul_div_mul_comm, norm_mul, mul_pow]

noncomputable def exactRow {q : ℕ} [NeZero q] (A : DirichletCharacter ℂ q) (m c : ℕ) : ℝ :=
  ∑ C : DirichletCharacter ℂ q, if C.conductor = c then weight A C m else 0

theorem exactRow_factor (A : DirichletCharacter ℂ a) (B : DirichletCharacter ℂ b) (m c d : ℕ)
    (hc : c ∣ a) (hd : d ∣ b) :
    exactRow (glue h A B) m (c*d) = exactRow A m c * exactRow B m d := by
  unfold exactRow
  rw [← Equiv.sum_comp (chEquiv h).symm]
  have E (P : DirichletCharacter ℂ a × DirichletCharacter ℂ b) :
      (if ((chEquiv h).symm P).conductor = c*d then
        weight (glue h A B) ((chEquiv h).symm P) m else 0) =
      (if P.1.conductor = c then weight A P.1 m else 0) *
        (if P.2.conductor = d then weight B P.2 m else 0) := by
    change (if (glue h P.1 P.2).conductor = c*d then weight (glue h A B) (glue h P.1 P.2) m else 0) = _
    rw [glue_conductor, weight_glue]
    have H := coprime_conductor_mul_match h P.1.conductor_dvd_level P.2.conductor_dvd_level hc hd
    by_cases ha : P.1.conductor = c
    · by_cases hb : P.2.conductor = d
      · rw [ite_eq_left (H.mpr ⟨ha,hb⟩), ite_eq_left ha, ite_eq_left hb]
      · rw [ite_eq_right (fun e => hb (H.mp e).2), ite_eq_left ha, ite_eq_right hb, mul_zero]
    · rw [ite_eq_right (fun e => ha (H.mp e).1), ite_eq_right ha, zero_mul]
  simp_rw [E]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

end CRT
end SignedHeight
end HeightProductionSection19

section HeightProductionSection20
open Finset DirichletCharacter
open scoped BigOperators Classical

namespace SignedHeight

noncomputable def rawMass
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r : ℕ} (α : DirichletCharacter ℂ r) (m s : ℕ) : ℝ :=
  ∑ β : DirichletCharacter ℂ s, if β.IsPrimitive then ‖S α β m‖^2 else 0

theorem rawMass_nonneg
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r : ℕ} (α : DirichletCharacter ℂ r) (m s : ℕ) : 0 ≤ rawMass S α m s := by
  apply Finset.sum_nonneg
  intro β _
  split_ifs <;> positivity

def LevelFormula
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r : ℕ} (α : DirichletCharacter ℂ r) (m : ℕ) (K : ℝ) : Prop :=
  ∀ (q s : ℕ) [NeZero q] (hr : r ∣ q) (hs : s ∣ q)
      (β : DirichletCharacter ℂ s), β.IsPrimitive →
    ‖S α β m‖^2 = K * CRT.weight (changeLevel hr α) (changeLevel hs β) m

theorem rawMass_eq_row
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r : ℕ} (α : DirichletCharacter ℂ r) (m : ℕ) (K : ℝ) (hK : LevelFormula S α m K)
    (q s : ℕ) [NeZero q] (hr : r ∣ q) (hs : s ∣ q) :
    rawMass S α m s = K * CRT.exactRow (changeLevel hr α) m s := by
  unfold rawMass CRT.exactRow
  rw [Finset.mul_sum]
  simp only [mul_ite, mul_zero]
  exact sum_exact_origin hs _ _ (hK q s hr hs)



theorem rawMass_factor
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r B u b : ℕ} [NeZero B] [NeZero u] [NeZero (B*u)]
    (α : DirichletCharacter ℂ r) (m : ℕ) (K : ℝ) (hK : LevelFormula S α m K)
    (hr : r ∣ B) (hb : b ∣ B) (hc : B.Coprime u) :
    rawMass S α m (b*u) = rawMass S α m b * CRT.exactRow (1 : DirichletCharacter ℂ u) m u := by
  have rBu : r ∣ B*u := hr.trans (dvd_mul_right ..)
  have bBu : b*u ∣ B*u := Nat.mul_dvd_mul_right hb u
  have hrα : changeLevel rBu α =
      CRT.glue hc (changeLevel hr α) (1 : DirichletCharacter ℂ u) := by
    rw [CRT.glue_left, ← changeLevel_trans]
  rw [rawMass_eq_row S α m K hK (B*u) (b*u) rBu bBu, hrα,
    CRT.exactRow_factor hc _ _ _ _ _ hb (dvd_refl _), ← mul_assoc,
    ← rawMass_eq_row S α m K hK B b hr hb]

theorem sum_exactRows {q : ℕ} [NeZero q] (A : DirichletCharacter ℂ q) (m : ℕ) :
    (∑ t ∈ q.divisors, CRT.exactRow A m t) =
      ∑ β : DirichletCharacter ℂ q, CRT.weight A β m := by
  unfold CRT.exactRow
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro β _
  have H := Nat.mem_divisors.mpr ⟨β.conductor_dvd_level, NeZero.ne q⟩
  rw [Finset.sum_ite_eq, ite_eq_left H]

end SignedHeight
end HeightProductionSection20

section HeightProductionSection21
open Finset DirichletCharacter
open scoped BigOperators Classical

namespace SignedHeight

theorem level_formula_of_cross
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r : ℕ} (α : DirichletCharacter ℂ r) (m : ℕ) (O : ℂ)
    (hnz : ∀ q : ℕ, ∀ [NeZero q], CRT.J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q) ≠ 0)
    (hCross : ∀ (q s : ℕ) [NeZero q] (hr : r ∣ q) (hs : s ∣ q)
      (β : DirichletCharacter ℂ s), β.IsPrimitive →
      S α β m * CRT.J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q) =
      O * CRT.J (changeLevel hr α) (changeLevel hs β) (m : ZMod q)) :
    LevelFormula S α m (‖O‖ ^ 2) := by
  intro q s _ hr hs β hβ
  change ‖S α β m‖^2 = ‖O‖^2 * CRT.weight (changeLevel hr α) (changeLevel hs β) m
  unfold CRT.weight
  have h := (eq_div_iff (hnz q)).mpr (hCross q s hr hs β hβ)
  rw [h, mul_div_assoc, norm_mul, mul_pow]

noncomputable def primitiveFamily (I : Finset ℕ) :
    Finset (Σ s : ℕ, DirichletCharacter ℂ s) :=
  I.sigma (fun s => Finset.univ.filter (fun c : DirichletCharacter ℂ s => c.IsPrimitive))

theorem mem_primitiveFamily (I : Finset ℕ) (b : Σ s : ℕ, DirichletCharacter ℂ s) :
    b ∈ primitiveFamily I ↔ b.1 ∈ I ∧ b.2.IsPrimitive := by
  simp [primitiveFamily]

theorem sum_primitiveFamily
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r : ℕ} (α : DirichletCharacter ℂ r) (m : ℕ) (I : Finset ℕ) :
    (∑ b ∈ primitiveFamily I, ‖S α b.2 m‖^2) =
      ∑ s ∈ I, rawMass S α m s := by
  rw [primitiveFamily, Finset.sum_sigma]
  simp_rw [Finset.sum_filter]
  rfl

def LevelTotals (r : ℕ) (W : ℕ → ℝ) (m : ℕ) (U : ℝ) : Prop :=
  ∀ D : ℕ, D ≠ 0 → r ∣ D →
    (∑ x ∈ D.divisors, W x) =
      U * ∏ p ∈ D.primeFactors.filter (fun p => ¬ p ∣ m), (((p:ℝ)-1)/((p:ℝ)-2))


theorem levelTotals_of_family
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r : ℕ} (α : DirichletCharacter ℂ r) (m : ℕ) (U : ℝ)
    (hF : ∀ D : ℕ, ∀ [NeZero D], r ∣ D →
      ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
        (∀ b, b ∈ F ↔ b.1 ≠ 0 ∧ b.1 ∣ D ∧ b.2.IsPrimitive) ∧
        (∑ b ∈ F, ‖S α b.2 m‖^2) =
          U * ∏ p ∈ D.primeFactors.filter (fun p => ¬ p ∣ m), (((p:ℝ)-1)/((p:ℝ)-2))) :
    LevelTotals r (rawMass S α m) m U := by
  intro D hD hr
  let _ : NeZero D := ⟨hD⟩
  obtain ⟨F,hF,hSum⟩ := hF D hr
  have hE : F = primitiveFamily D.divisors := by
    ext b
    rw [hF, mem_primitiveFamily, Nat.mem_divisors]
    constructor
    · rintro ⟨_,h₁,h₂⟩
      exact ⟨⟨h₁,hD⟩,h₂⟩
    · rintro ⟨⟨h₁,_⟩,h₂⟩
      exact ⟨ne_zero_of_dvd_ne_zero hD h₁,h₁,h₂⟩
  rwa [hE, sum_primitiveFamily] at hSum

theorem LevelTotals.stable {r : ℕ} {W : ℕ → ℝ} {m : ℕ} {U : ℝ}
    (H : LevelTotals r W m U) (d D : ℕ) (hd : d ≠ 0) (hD : D ≠ 0) (hr : r ∣ d)
    (hdD : d ∣ D) (hPrimes : d.primeFactors = D.primeFactors) :
    (∑ x ∈ d.divisors, W x) = ∑ x ∈ D.divisors, W x := by
  rw [H d hd hr,H D hD (hr.trans hdD),hPrimes]

end SignedHeight
end HeightProductionSection21

section HeightProductionSection22
open Finset

namespace SignedHeight


def heightDilate (d : ℕ) (g : ℕ → ℝ) (n : ℕ) : ℝ :=
  if d ∣ n then g (n/d) else 0

theorem heightDilate_hasSum {d : ℕ} (hd : 0 < d) {g : ℕ → ℝ} {G : ℝ}
    (hg : HasSum g G) : HasSum (heightDilate d g) G := by
  have inj : Function.Injective (fun n : ℕ => d*n) := fun _ _ h => Nat.eq_of_mul_eq_mul_left hd h
  have supp : ∀ n ∉ Set.range (fun n : ℕ => d*n), heightDilate d g n = 0 := by
    intro n hn
    unfold heightDilate
    split_ifs with hv
    · obtain ⟨x,rfl⟩ := hv
      exact False.elim (hn ⟨x,rfl⟩)
    · rfl
  apply (inj.hasSum_iff supp).mp
  simpa [Function.comp_def, heightDilate, Nat.mul_div_cancel_left _ hd] using hg

def heightBadConv (D : Finset ℕ) (bad g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ D, bad d * heightDilate d g n

private theorem finite_hasSum {ι : Type*} {F : ι → ℕ → ℝ} {G : ι → ℝ}
    (D : Finset ι) (H : ∀ d ∈ D, HasSum (F d) (G d)) :
    HasSum (fun n => ∑ d ∈ D, F d n) (∑ d ∈ D, G d) := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | @insert d D hd ih =>
    simp only [Finset.sum_insert hd]
    exact (H d (mem_insert_self _ _)).add (ih (fun i hi => H i (mem_insert_of_mem hi)))

theorem heightBadConv_hasSum (D : Finset ℕ) (dpos : ∀ d ∈ D, 0 < d)
    (bad : ℕ → ℝ) {g : ℕ → ℝ} {G : ℝ} (hg : HasSum g G) :
    HasSum (heightBadConv D bad g) ((∑ d ∈ D, bad d) * G) := by
  rw [Finset.sum_mul]
  exact finite_hasSum D (fun d hd => (heightDilate_hasSum (dpos d hd) hg).mul_left (bad d))

theorem heightBadConv_summable (D : Finset ℕ) (dpos : ∀ d ∈ D, 0 < d)
    (bad : ℕ → ℝ) {g : ℕ → ℝ} (h0 : g 0 = 0)
    (hs : Summable (fun k => ‖g k‖))
    (hl : Summable (fun k => ‖g k‖ * Real.log (k:ℝ))) :
    Summable (fun n => ‖heightBadConv D bad g n‖) ∧
      Summable (fun n => ‖heightBadConv D bad g n‖ * Real.log (n:ℝ)) := by
  constructor
  · exact summable_norm_iff.mpr ((heightBadConv_hasSum D dpos bad hs.of_norm.hasSum).summable)
  have oneRow (d : ℕ) (hd : 0 < d) : Summable
      (fun n => ‖bad d * heightDilate d g n‖ * Real.log (n:ℝ)) := by
    let f (k : ℕ) := ‖g k‖ * (Real.log (d:ℝ) + Real.log (k:ℝ))
    have sf : Summable f := by
      simpa only [f, mul_add] using (hs.mul_right (Real.log (d:ℝ))).add hl
    have hEquiv (n : ℕ) : ‖bad d * heightDilate d g n‖ * Real.log (n:ℝ) =
        ‖bad d‖ * heightDilate d f n := by
      by_cases hdv : d ∣ n
      · obtain ⟨k,rfl⟩ := hdv
        simp only [heightDilate, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hd, f, norm_mul]
        by_cases hk : k = 0
        · simp [hk, h0]
        · rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hd.ne') (by exact_mod_cast hk)]
          ring
      · simp [heightDilate, hdv]
    simpa only [hEquiv] using ((heightDilate_hasSum hd sf.hasSum).summable.mul_left ‖bad d‖)
  have ht : Summable (fun n => ∑ d ∈ D, ‖bad d * heightDilate d g n‖ * Real.log (n:ℝ)) :=
    (finite_hasSum D (fun d hd => (oneRow d (dpos d hd)).hasSum)).summable
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (Real.log_natCast_nonneg n)) ?_ ht
  intro n
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (norm_sum_le D _) (Real.log_natCast_nonneg n)

theorem heightBadConv_eq_divisor {B : ℕ} {bad g : ℕ → ℝ}
    (hb : ∀ d ∉ B.divisors, bad d = 0) (hg : g 0 = 0) (n : ℕ) :
    heightBadConv B.divisors bad g n = ∑ d ∈ n.divisors, bad d * g (n/d) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [heightBadConv, heightDilate, hg]
  unfold heightBadConv heightDilate
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  have e : B.divisors.filter (fun d => d ∣ n) = n.divisors.filter (fun d => d ∈ B.divisors) := by
    ext d
    simp only [mem_filter, Nat.mem_divisors, hn, and_true]
    tauto
  rw [e]
  apply sum_subset (filter_subset _ _)
  intro d _ h
  have hd : d ∉ B.divisors := fun hd => h (mem_filter.mpr ⟨‹d ∈ n.divisors›,hd⟩)
  simp [hb d hd]

theorem height_bad_divisor_convolution {B : ℕ} {bad g : ℕ → ℝ}
    (hb : ∀ d ∉ B.divisors, bad d = 0) (h0 : g 0 = 0)
    (hs : Summable (fun k => ‖g k‖))
    (hl : Summable (fun k => ‖g k‖ * Real.log (k:ℝ))) :
    let a (n : ℕ) := ∑ d ∈ n.divisors, bad d * g (n/d)
    Summable (fun n => ‖a n‖) ∧ Summable (fun n => ‖a n‖ * Real.log (n:ℝ)) ∧
      (∑' n : ℕ, a n) = (∑' d : ℕ, bad d) * (∑' n : ℕ, g n) := by
  intro a
  have dpos : ∀ d ∈ B.divisors, 0 < d := fun _ h => Nat.pos_of_mem_divisors h
  have eh : heightBadConv B.divisors bad g = a := funext (heightBadConv_eq_divisor hb h0)
  have s := heightBadConv_summable B.divisors dpos bad h0 hs hl
  have h := (heightBadConv_hasSum B.divisors dpos bad hs.of_norm.hasSum).tsum_eq
  rw [eh] at s h
  rw [tsum_eq_sum hb]
  exact ⟨s.1,s.2,h⟩

end SignedHeight
end HeightProductionSection22

section HeightProductionSection23
open Finset ArithmeticFunction

namespace SignedHeight

set_option maxHeartbeats 1000000 in
theorem height_mul_eq_divisor_sum (bad g : ArithmeticFunction ℝ) (n : ℕ) :
    (bad * g) n = ∑ d ∈ n.divisors, bad d * g (n/d) := by
  rw [ArithmeticFunction.mul_apply]
  exact Nat.sum_divisorsAntidiagonal (fun x y => bad x * g y)

set_option maxHeartbeats 1000000 in
theorem height_bad_mul {B : ℕ} {bad g : ArithmeticFunction ℝ}
    (hb : ∀ d ∉ B.divisors, bad d = 0)
    (hs : Summable (fun k => ‖g k‖))
    (hl : Summable (fun k => ‖g k‖ * Real.log (k:ℝ))) :
    Summable (fun n => ‖(bad * g) (n+1)‖) ∧
      Summable (fun n => ‖(bad * g) (n+1)‖ * Real.log ((n+1 : ℕ):ℝ)) ∧
      (∑' n : ℕ, (bad*g) n) = (∑' d : ℕ, bad d) * (∑' n : ℕ, g n) := by
  have hg0 : g 0 = 0 := by simp
  have h := height_bad_divisor_convolution (B := B) (bad := fun d => bad d)
    (g := fun d => g d) hb hg0 hs hl
  let A (n : ℕ) : ℝ := ∑ d ∈ n.divisors, bad d * g (n/d)
  have eqA : A = (fun n => (bad*g) n) := funext fun n => (height_mul_eq_divisor_sum bad g n).symm
  change Summable (fun n => ‖A n‖) ∧
    Summable (fun n => ‖A n‖ * Real.log (n:ℝ)) ∧
    (∑' n : ℕ, A n) = (∑' d : ℕ, bad d) * (∑' n : ℕ, g n) at h
  rw [eqA] at h
  exact ⟨(summable_nat_add_iff (f := fun n => ‖(bad*g) n‖) 1).mpr h.1,
    (summable_nat_add_iff (f := fun n => ‖(bad*g) n‖ * Real.log (n:ℝ)) 1).mpr h.2.1,h.2.2⟩

set_option maxHeartbeats 1000000 in
theorem height_bad_mul_total {B : ℕ} {bad g : ArithmeticFunction ℝ} {C : ℝ}
    (hb : ∀ d ∉ B.divisors, bad d = 0)
    (hs : Summable (fun k => ‖g k‖))
    (hl : Summable (fun k => ‖g k‖ * Real.log (k:ℝ)))
    (hC : (∑ d ∈ B.divisors, bad d) * (∑' n, g n) = C) :
    Summable (fun n => ‖(bad * g) (n+1)‖) ∧
      Summable (fun n => ‖(bad * g) (n+1)‖ * Real.log ((n+1 : ℕ):ℝ)) ∧
      (∑' n : ℕ, (bad*g) (n+1)) = C := by
  obtain ⟨s,l,e⟩ := height_bad_mul (B := B) (bad := bad) (g := g) hb hs hl
  refine ⟨s,l,?_⟩
  have hsum : Summable (fun n => (bad*g) n) :=
    (summable_nat_add_iff (f := fun n => (bad*g) n) 1).mp s.of_norm
  have hsplit := hsum.tsum_eq_zero_add
  simp only [ArithmeticFunction.map_zero, zero_add] at hsplit
  rw [← hsplit, e, tsum_eq_sum (s := B.divisors) (f := fun d => bad d) hb]
  exact hC

end SignedHeight
end HeightProductionSection23

section HeightProductionSection24
open Finset ArithmeticFunction

namespace SignedHeight



set_option maxHeartbeats 1200000 in
theorem height_from_bad_good {B : ℕ} {bad w : ArithmeticFunction ℝ}
    (hb : ∀ d ∉ B.divisors, bad d = 0)
    (mass : (Σ s : ℕ, DirichletCharacter ℂ s) → ℝ)
    {O : ℝ} (hO : 0 < O)
    (hMass : ∀ n > 0, massAt mass n = O^2 * (bad*w) n)
    (hs : Summable (fun n => ‖heightCorrection w n‖))
    (hl : Summable (fun n => ‖heightCorrection w n‖ * Real.log (n:ℝ)))
    (hCoeff : (∑ d ∈ B.divisors, bad d) * (∑' n, heightCorrection w n) = O⁻¹) :
    ∃ b₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T,
      ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
        (∀ b, b ∈ F ↔ (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ b.1 ≤ Y) ∧
        |(∑ b ∈ F, mass b) - O * Real.log (Y:ℝ) - b₀| ≤ ε := by
  let g := heightCorrection w
  let a (d : ℕ) := O^2 * (bad*g) d
  obtain ⟨hs',hl',ht⟩ := height_bad_mul_total (g := g) hb hs hl hCoeff
  have h1 : Summable (fun n => ‖a (n+1)‖) := by
    simpa only [a, norm_mul] using hs'.mul_left ‖O^2‖
  have h2 : Summable (fun n => ‖a (n+1)‖ * Real.log ((n+1 : ℕ):ℝ)) := by
    simpa only [a, norm_mul, mul_assoc] using hl'.mul_left ‖O^2‖
  have h3 : (∑' n, a (n+1)) = O := by
    have hv := (hs'.of_norm.hasSum.mul_left (O^2)).tsum_eq
    calc
      _ = O^2 * O⁻¹ := by rw [← ht]; exact hv
      _ = O := by field_simp
  apply assemble_from_convolution mass O a h1 h2 h3
  intro n hn
  have hg : w = g * invNatWeight := (height_correction_convolution w).symm
  rw [hMass n hn, hg, ← mul_assoc, height_mul_eq_divisor_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun d _ => by simp only [a, invNatWeight_apply, mul_assoc])

end SignedHeight
end HeightProductionSection24

section HeightProductionSection25
open Finset Filter ArithmeticFunction
open scoped Topology

namespace SignedHeight

set_option maxHeartbeats 800000 in
noncomputable def badHeightWeight (B : ℕ) (W : ℕ → ℝ) (U : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun b => if b ∈ B.divisors then W b / U else 0, by simp⟩

set_option maxHeartbeats 800000 in
theorem badHeightWeight_apply (B : ℕ) (W : ℕ → ℝ) (U : ℝ) (b : ℕ) :
    badHeightWeight B W U b = if b ∈ B.divisors then W b / U else 0 := rfl

set_option maxHeartbeats 800000 in
theorem exact_mul_badHeightWeight (B : ℕ) (W : ℕ → ℝ) {U : ℝ} (hU : U ≠ 0)
    (w : ArithmeticFunction ℝ) (n : ℕ) :
    U * (badHeightWeight B W U * w) n =
      ∑ b ∈ n.divisors with b ∈ B.divisors, W b * w (n/b) := by
  rw [height_mul_eq_divisor_sum, Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  rw [badHeightWeight_apply]
  split_ifs with hb
  · field_simp
  · simp

set_option maxHeartbeats 800000 in
theorem massAt_eq_rawMass
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r : ℕ} (α : DirichletCharacter ℂ r) (m n : ℕ) (hn : n ≠ 0) :
    massAt (fun b => ‖S α b.2 m‖^2) n = rawMass S α m n := by
  simp [massAt, partnersAt, hn, rawMass, Finset.sum_filter]

set_option maxHeartbeats 800000 in
theorem finalAssembly
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r m B : ℕ} (α : DirichletCharacter ℂ r)
    (hB : B ≠ 0) (hmB : m ∣ B) (hrB : r ∣ B) (he : Even m)
    {O : ℝ} (hO : 0 < O)
    (hLevels : LevelTotals r (rawMass S α m) m (O^2))
    (hOrd : Tendsto (fun n : ℕ => ∏ p ∈ n.factorial.primeFactors, heightOrdinaryPrimeFactor m p)
      atTop (𝓝 O))
    (hMass : ∀ n > 0, rawMass S α m n =
      ∑ b ∈ n.divisors with b ∈ B.divisors,
        rawMass S α m b * heightGoodWeight B (n/b)) :
    ∃ b₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T,
      ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
        (∀ b, b ∈ F ↔ (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ b.1 ≤ Y) ∧
        |(∑ b ∈ F, ‖S α b.2 m‖^2) - O * Real.log (Y:ℝ) - b₀| ≤ ε := by
  classical
  let U := O^2
  let W := rawMass S α m
  let b := badHeightWeight B W U
  let w := heightGoodWeight B
  have hU : U ≠ 0 := pow_ne_zero _ hO.ne'
  have hb : ∀ d ∉ B.divisors, b d = 0 := by
    intro d hd
    simp [b, badHeightWeight_apply, hd]
  have hbad : (∑ d ∈ B.divisors, b d) =
      ∏ p ∈ B.primeFactors, heightBadPrimeFactor B m p := by
    calc
      _ = (∑ d ∈ B.divisors, W d) / U := by
        simp only [b, badHeightWeight_apply, Finset.sum_div]
        exact Finset.sum_congr rfl (fun d hd => ite_eq_left hd)
      _ = ∏ p ∈ B.primeFactors.filter (fun p => ¬p∣m), (((p:ℝ)-1)/((p:ℝ)-2)) := by
        rw [hLevels B hB hrB]
        simp [U, hO.ne']
      _ = _ := by
        rw [Finset.prod_filter]
        exact Finset.prod_congr rfl (fun p hp => by
          have hd := Nat.dvd_of_mem_primeFactors hp
          by_cases hm : p ∣ m <;> simp [heightBadPrimeFactor, hd, hm])
  have hs := good_height_correction_sums hB (even_iff_two_dvd.mpr (he.two_dvd.trans hmB))
  have hMassFixed : ∀ n > 0, massAt (fun b => ‖S α b.2 m‖^2) n =
      O^2 * (b*w) n := by
    intro n hn
    rw [massAt_eq_rawMass S α m n hn.ne', hMass n hn]
    exact (exact_mul_badHeightWeight B W hU w n).symm
  have hCoeff : (∑ d ∈ B.divisors, b d) * (∑' n, heightCorrection w n) = O⁻¹ := by
    rw [hbad]
    exact exact_height_correction_log_coefficient hB he hmB hO.ne' hOrd
  exact height_from_bad_good hb _ hO hMassFixed hs.1 hs.2 hCoeff

end SignedHeight
end HeightProductionSection25

section HeightProductionSection26
open scoped BigOperators ComplexConjugate
open Finset DirichletCharacter

namespace CubicLocal

private theorem conj_char {q : ℕ} (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    conj (χ (u : ZMod q)) = χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  have h := Complex.mul_conj' (χ (u : ZMod q))
  rw [χ.unit_norm_eq_one u] at h
  norm_num at h
  calc
    _ = χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) *
        (χ (u : ZMod q) * conj (χ (u : ZMod q))) := by
      rw [← mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        map_one, one_mul]
    _ = _ := by rw [h, mul_one]

theorem parseval_row {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)‖ ^ 2) =
      (q.totient : ℝ) * ∑ u, ‖f u‖ ^ 2 := by
  classical
  have orth (u v : (ZMod q)ˣ) :
      (∑ χ : DirichletCharacter ℂ q, χ (u : ZMod q) * conj (χ (v : ZMod q))) =
        if u = v then (q.totient : ℂ) else 0 := by
    simp_rw [conj_char, ← ZMod.inv_coe_unit]
    simpa only [Units.val_inj, eq_comm, mul_comm] using
      (DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) v.isUnit (u : ZMod q))
  rw [← Complex.ofReal_inj]
  push_cast
  simp_rw [← Complex.mul_conj']

  have ex (χ : DirichletCharacter ℂ q) :
      (∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)) *
        conj (∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)) =
      ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
        (f u * conj (f v)) * (χ (u : ZMod q) * conj (χ (v : ZMod q))) := by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_mul]
    ring
  simp_rw [ex]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orth, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

theorem sum_units_supported {q : ℕ} [NeZero q] (F : ZMod q → ℂ)
    (hF : ∀ x, ¬ IsUnit x → F x = 0) :
    (∑ x : ZMod q, F x) = ∑ u : (ZMod q)ˣ, F (u : ZMod q) := by
  classical
  let v : (ZMod q)ˣ ↪ ZMod q := ⟨Units.val, Units.val_injective⟩
  have hmap : (Finset.univ : Finset (ZMod q)ˣ).map v = Finset.univ.filter IsUnit := by
    ext x
    simp [v, IsUnit]
  change _ = ∑ u : (ZMod q)ˣ, F (v u)
  rw [← Finset.sum_map]
  rw [hmap, Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by
    by_cases hx : IsUnit x
    · simp [hx]
    · simpa [hx] using hF x hx

theorem isUnit_reflect_of_dvd {p e m : ℕ} [NeZero (p^e)]
    (hp : p.Prime) (he : 0 < e) (hm : p ∣ m) (x : ZMod (p^e)) :
    IsUnit ((m : ZMod (p^e)) - x) ↔ IsUnit x := by
  have hpe : p ∣ p^e := dvd_pow_self p he.ne'
  let c : ZMod (p^e) →+* ZMod p := ZMod.castHom hpe _
  have test (u : ZMod (p^e)) : IsUnit u ↔ c u ≠ 0 := by
    conv_lhs => rw [← ZMod.natCast_zmod_val u]
    conv_rhs => rw [← ZMod.natCast_zmod_val u]
    rw [map_natCast]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp he).trans
      (not_congr (ZMod.natCast_eq_zero_iff u.val p)).symm
  rw [test, test, map_sub, map_natCast, (ZMod.natCast_eq_zero_iff m p).mpr hm, zero_sub, neg_ne_zero]

theorem local_divides (p e m : ℕ) [NeZero (p ^ e)] (hp : p.Prime) (he : 0 < e)
    (_hmEven : Even m) (hm : p ∣ m)
    (a : DirichletCharacter ℂ (p^e)) (T : Finset (DirichletCharacter ℂ (p^e))) :
    let Jm := fun (A B : DirichletCharacter ℂ (p ^ e)) =>
      ∑ x : ZMod (p ^ e), A x * B ((m : ZMod (p ^ e)) - x)
    (∑ b ∈ T, ‖Jm a b / Jm 1 1‖ ^ 3) ≤ 1 := by
  classical
  let Jm := fun (A B : DirichletCharacter ℂ (p ^ e)) =>
    ∑ x : ZMod (p ^ e), A x * B ((m : ZMod (p ^ e)) - x)
  let f (a : DirichletCharacter ℂ (p^e)) (u : (ZMod (p^e))ˣ) :=
    a ((m : ZMod (p^e)) - (u : ZMod (p^e)))
  have norm_f (a : DirichletCharacter ℂ (p^e)) (u : (ZMod (p^e))ˣ) : ‖f a u‖ = 1 := by
    exact a.unit_norm_eq_one ((isUnit_reflect_of_dvd hp he hm _).mpr u.isUnit).unit
  have jj (a b : DirichletCharacter ℂ (p^e)) :
      Jm a b = ∑ u : (ZMod (p^e))ˣ, f a u * b (u : ZMod (p^e)) := by
    let k : ZMod (p^e) ≃ ZMod (p^e) :=
      ⟨fun x => (m : ZMod (p ^ e)) - x, fun x => (m : ZMod (p ^ e)) - x,
        fun x => sub_sub_cancel _ _, fun x => sub_sub_cancel _ _⟩
    unfold Jm
    rw [← Equiv.sum_comp k]
    change (∑ x : ZMod (p^e), a ((m : ZMod (p^e)) - x) *
      b ((m : ZMod (p^e)) - ((m : ZMod (p^e)) - x))) = _
    simp only [sub_sub_cancel]
    exact sum_units_supported (fun x => a ((m : ZMod (p^e)) - x) * b x) (fun x hx => by rw [b.map_nonunit hx, mul_zero])
  have den : Jm 1 1 = ((p^e).totient : ℂ) := by
    rw [jj]
    have one_on (u : (ZMod (p^e))ˣ) : f 1 u = 1 :=
      MulChar.one_apply ((isUnit_reflect_of_dvd hp he hm _).mpr u.isUnit)
    simp only [one_on, MulChar.one_apply_coe, mul_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.card_univ, ZMod.card_units_eq_totient]
  have hnormDen : ‖Jm 1 1‖ = ((p^e).totient : ℝ) := by
    rw [den, Complex.norm_natCast]
  have hpos : 0 < ((p^e).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos (p^e))
  have point (b : DirichletCharacter ℂ (p^e)) : ‖Jm a b / Jm 1 1‖ ≤ 1 := by
    rw [norm_div, hnormDen, div_le_one hpos, jj]
    refine (norm_sum_le Finset.univ (fun u : (ZMod (p^e))ˣ => f a u * b (↑u))).trans ?_
    calc
      _ = ∑ _u : (ZMod (p^e))ˣ, (1 : ℝ) := Finset.sum_congr rfl (fun u _ => by
        rw [norm_mul, norm_f, b.unit_norm_eq_one u, one_mul])
      _ = ((p^e).totient : ℝ) := by simp [ZMod.card_units_eq_totient]
      _ ≤ _ := le_rfl
  have energy : (∑ b : DirichletCharacter ℂ (p^e), ‖Jm a b‖ ^ 2) = ((p^e).totient : ℝ) ^ 2 := by
    simp_rw [jj]
    rw [parseval_row, pow_two]
    congr 1
    simp [norm_f, ZMod.card_units_eq_totient]
  have normalized_energy :
      (∑ b : DirichletCharacter ℂ (p^e), ‖Jm a b / Jm 1 1‖ ^ 2) = 1 := by
    simp_rw [norm_div, div_pow, hnormDen]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, energy, mul_inv_cancel₀ (pow_ne_zero _ hpos.ne')]
  change (∑ b ∈ T, ‖Jm a b / Jm 1 1‖ ^ 3) ≤ 1
  calc
    _ ≤ ∑ b ∈ T, ‖Jm a b / Jm 1 1‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      rw [pow_succ]
      exact mul_le_of_le_one_right (by positivity) (point b)
    _ ≤ ∑ b : DirichletCharacter ℂ (p^e), ‖Jm a b / Jm 1 1‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => pow_nonneg (norm_nonneg _) _)
    _ = _ := normalized_energy

end CubicLocal
end HeightProductionSection26

section HeightProductionSection27
open scoped BigOperators
open Finset DirichletCharacter

namespace CubicLocal

private theorem finEquiv_cast (n : ℕ) [NeZero n] (i : Fin n) :
    ZMod.finEquiv n i = (i.val : ZMod n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    apply Fin.ext
    change i.val = i.val % (n+1)
    exact (Nat.mod_eq_of_lt i.isLt).symm

theorem reduce_sum {A : Type*} [AddCommMonoid A] {d p : ℕ} [NeZero d] [NeZero p]
    [NeZero (d*p)] (f : ZMod p → A) :
    (∑ x : ZMod (d*p), f (ZMod.castHom (dvd_mul_left p d) _ x)) =
      d • ∑ z : ZMod p, f z := by
  classical
  let E : Fin d × Fin p ≃ ZMod (d*p) :=
    finProdFinEquiv.trans (ZMod.finEquiv (d*p)).toEquiv
  let c : ZMod (d*p) →+* ZMod p := ZMod.castHom (dvd_mul_left p d) _
  have he (v : Fin d × Fin p) : c (E v) = ZMod.finEquiv p v.2 := by
    change c (ZMod.finEquiv (d*p) (finProdFinEquiv v)) = ZMod.finEquiv p v.2
    rw [finEquiv_cast, finEquiv_cast, map_natCast]
    change ((v.2.val + p * v.1.val : ℕ) : ZMod p) = (v.2.val : ZMod p)
    simp
  calc
    _ = ∑ v : Fin d × Fin p, f (c (E v)) := (Equiv.sum_comp E _).symm
    _ = ∑ v : Fin d × Fin p, f (ZMod.finEquiv p v.2) := Finset.sum_congr rfl fun v _ => congrArg f (he v)
    _ = d • ∑ i : Fin p, f (ZMod.finEquiv p i) := by
      rw [Fintype.sum_prod_type]
      simp
    _ = _ := congrArg (d • ·) (Equiv.sum_comp (ZMod.finEquiv p).toEquiv f)

private theorem unit_iff_c {p j : ℕ} (hp : p.Prime)
    [NeZero p] [NeZero (p^j*p)] (x : ZMod (p^j*p)) :
    IsUnit x ↔ ZMod.castHom (dvd_mul_left p (p^j)) (ZMod p) x ≠ 0 := by
  let c : ZMod (p^j*p) →+* ZMod p := ZMod.castHom (dvd_mul_left p (p^j)) _
  change IsUnit x ↔ c x ≠ 0
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  conv_rhs => rw [← ZMod.natCast_zmod_val x]
  rw [map_natCast, ZMod.isUnit_iff_coprime]
  have C (n : ℕ) : n.Coprime (p^j*p) ↔ ¬p ∣ n := by
    rw [← pow_succ, Nat.coprime_pow_right_iff (Nat.succ_pos _), Nat.coprime_comm, hp.coprime_iff_not_dvd]
  exact (C x.val).trans (not_congr (ZMod.natCast_eq_zero_iff x.val p)).symm

private theorem count_complement_two {r : Type*} [Fintype r] [DecidableEq r]
    (a b : r) (hab : a ≠ b) :
    (∑ x : r, if x ≠ a ∧ x ≠ b then (1:ℂ) else 0) =
      (Fintype.card r : ℂ) - 2 := by
  have hs : (Finset.univ : Finset r).filter (fun x => x ≠ a ∧ x ≠ b) =
      (Finset.univ.erase a).erase b := by
    ext x
    simp [and_comm]
  have hb : b ∈ (Finset.univ : Finset r).erase a := by simp [Ne.symm hab]
  have ha : a ∈ (Finset.univ : Finset r) := Finset.mem_univ _
  have one : 1 ≤ ((Finset.univ : Finset r).erase a).card :=
    Finset.card_pos.mpr ⟨b, hb⟩
  have two : 1 ≤ (Finset.univ : Finset r).card :=
    Finset.card_pos.mpr ⟨a, ha⟩
  rw [← Finset.sum_filter, hs, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem hb, Nat.cast_sub one, Finset.card_erase_of_mem ha,
    Nat.cast_sub two, Finset.card_univ]
  push_cast
  ring


theorem ordinary_norm_pp {p j m : ℕ} (hp : p.Prime) [NeZero (p^j*p)] (hm : ¬p ∣ m) :
    ‖∑ x : ZMod (p^j*p), (1 : DirichletCharacter ℂ (p^j*p)) x *
      (1 : DirichletCharacter ℂ (p^j*p)) ((m : ZMod (p^j*p))-x)‖ =
      (p:ℝ)^j * ((p:ℝ)-2) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p^j) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let c : ZMod (p^j*p) →+* ZMod p := ZMod.castHom (dvd_mul_left p (p^j)) _
  have H (x : ZMod (p^j*p)) : IsUnit x ↔ c x ≠ 0 := unit_iff_c hp x
  have H' (x : ZMod (p^j*p)) : IsUnit ((m : ZMod (p^j*p))-x) ↔ c x ≠ (m : ZMod p) := by
    rw [H, map_sub, map_natCast]
    simp [sub_eq_zero, ne_comm]
  let f (v : ZMod p) : ℂ := if v ≠ 0 ∧ v ≠ (m : ZMod p) then 1 else 0
  have term (x : ZMod (p^j*p)) :
      (1 : DirichletCharacter ℂ (p^j*p)) x *
        (1 : DirichletCharacter ℂ (p^j*p)) ((m : ZMod (p^j*p))-x) = f (c x) := by
    by_cases xunit : IsUnit x <;> by_cases yunit : IsUnit ((m : ZMod (p^j*p))-x)
    all_goals simp [f, xunit, yunit, MulChar.one_apply, MulChar.map_nonunit, ← H, ← H']
  simp only [term]
  change ‖∑ x : ZMod (p^j*p), f (c x)‖ = _
  rw [show (∑ x : ZMod (p^j*p), f (c x)) = (p^j) • ∑ z : ZMod p, f z from reduce_sum f]
  have nz : (m : ZMod p) ≠ 0 := (not_congr (ZMod.natCast_eq_zero_iff m p)).mpr hm
  have cnt : (∑ z : ZMod p, f z) = (p : ℂ) - 2 := by
    dsimp only [f]
    simpa [ZMod.card] using count_complement_two (0 : ZMod p) (m : ZMod p) nz.symm
  rw [cnt, nsmul_eq_mul, norm_mul, Complex.norm_natCast, Nat.cast_pow]
  congr 1
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hpR)]


theorem ordinary_norm_pp_dvd {p j m : ℕ} (hp : p.Prime) [NeZero (p^j*p)] (hm : p ∣ m) :
    ‖∑ x : ZMod (p^j*p), (1 : DirichletCharacter ℂ (p^j*p)) x *
      (1 : DirichletCharacter ℂ (p^j*p)) ((m : ZMod (p^j*p))-x)‖ =
      (p:ℝ)^j * ((p:ℝ)-1) := by
  classical
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let c : ZMod (p^j*p) →+* ZMod p := ZMod.castHom (dvd_mul_left p (p^j)) _
  have H (x : ZMod (p^j*p)) : IsUnit x ↔ c x ≠ 0 := unit_iff_c hp x
  have H' (x : ZMod (p^j*p)) : IsUnit ((m : ZMod (p^j*p))-x) ↔ IsUnit x := by
    rw [H, H, map_sub, map_natCast, (ZMod.natCast_eq_zero_iff m p).mpr hm, zero_sub, neg_ne_zero]
  have E (x : ZMod (p^j*p)) :
      (1 : DirichletCharacter ℂ (p^j*p)) x *
        (1 : DirichletCharacter ℂ (p^j*p)) ((m : ZMod (p^j*p))-x) =
        (1 : DirichletCharacter ℂ (p^j*p)) x := by
    by_cases hx : IsUnit x
    · rw [MulChar.one_apply ((H' x).mpr hx), mul_one]
    · simp [MulChar.map_nonunit _ hx]
  simp_rw [E]
  rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient, Complex.norm_natCast, ← pow_succ,
    Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_one]

theorem ordinary_norm_pp_full {p j m : ℕ} (hp : p.Prime) [NeZero (p*p^j)] :
    ‖∑ x : ZMod (p*p^j), (1 : DirichletCharacter ℂ (p*p^j)) x *
      (1 : DirichletCharacter ℂ (p*p^j)) ((m : ZMod (p*p^j))-x)‖ =
      ((p^j:ℕ):ℝ) * (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2) := by
  classical
  have eq (q : ℕ) [NeZero q] (h : q = p^j*p) :
      ‖∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x *
        (1 : DirichletCharacter ℂ q) ((m : ZMod q)-x)‖ =
        ((p^j:ℕ):ℝ) * (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2) := by
    subst q
    rw [Nat.cast_pow]
    by_cases hm : p ∣ m
    · rw [ite_eq_left hm]
      exact ordinary_norm_pp_dvd hp hm
    · rw [ite_eq_right hm]
      exact ordinary_norm_pp hp hm
  exact eq (p*p^j) (mul_comm ..)

end CubicLocal
end HeightProductionSection27

section HeightProductionSection28
open scoped BigOperators ComplexConjugate
open Finset DirichletCharacter

namespace CubicMass

theorem char_parseval {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ v, ¬IsUnit v → g v = 0) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ v : ZMod q, g v * χ v‖^2) =
      (q.totient : ℝ) * ∑ v : ZMod q, ‖g v‖^2 := by
  classical
  let A (χ : DirichletCharacter ℂ q) := ∑ v : ZMod q, g v * χ v
  have orth (u v : ZMod q) (hv : IsUnit v) :
      (∑ χ : DirichletCharacter ℂ q, χ u * conj (χ v)) =
        if u = v then (q.totient:ℂ) else 0 := by
    have hvv : v * (Ring.inverse v) = 1 := Ring.mul_inverse_cancel _ hv
    have E : u * (Ring.inverse v) = 1 ↔ u = v := by
      constructor
      · intro he
        calc
          u = u * ((Ring.inverse v) * v) := by rw [mul_comm ((Ring.inverse v)) v, hvv, mul_one]
          _ = v := by rw [← mul_assoc, he, one_mul]
      · intro he
        rw [he, hvv]
    simp_rw [← Complex.star_def, MulChar.star_apply', MulChar.inv_apply, ← map_mul]
    rw [sum_characters_eq]
    simp only [E]
  have expand (χ : DirichletCharacter ℂ q) :
      A χ * conj (A χ) =
        ∑ u : ZMod q, ∑ v : ZMod q, g u * conj (g v) * (χ u * conj (χ v)) := by
    simp only [A, map_sum, map_mul]
    rw [sum_mul]
    refine sum_congr rfl (fun u _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun v _ => ?_)
    ring
  apply Complex.ofReal_injective
  push_cast
  calc
    (∑ χ : DirichletCharacter ℂ q, (‖A χ‖:ℂ)^2)
      = ∑ χ, A χ * conj (A χ) := by simp [Complex.mul_conj']
    _ = ∑ u : ZMod q, ∑ v : ZMod q, g u * conj (g v) *
        ∑ χ : DirichletCharacter ℂ q, χ u * conj (χ v) := by
      simp only [expand, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl (fun u _ => sum_comm)
    _ = ∑ u : ZMod q, (q.totient:ℂ) * (g u * conj (g u)) := by
      refine sum_congr rfl (fun u _ => ?_)
      calc
        _ = ∑ v : ZMod q, if u = v then g u * conj (g u) * (q.totient:ℂ) else 0 := by
          refine sum_congr rfl (fun v _ => ?_)
          by_cases hv : IsUnit v
          · rw [orth u v hv]
            split_ifs with h
            · subst v; rfl
            · rw [mul_zero]
          · by_cases h : u = v
            · subst v; simp [hg _ hv]
            · simp [h, hg _ hv]
        _ = _ := by simp [mul_comm]
    _ = (q.totient:ℂ) * ∑ v : ZMod q, (‖g v‖:ℂ)^2 := by
      simp [mul_sum, Complex.mul_conj']

end CubicMass

open scoped BigOperators
open Finset DirichletCharacter

namespace CubicMass

noncomputable def jacobi {q : ℕ} [NeZero q] (a b : DirichletCharacter ℂ q) (m : ZMod q) : ℂ :=
  ∑ v : ZMod q, a v * b (m-v)

theorem jacobi_row_parseval {q : ℕ} [NeZero q] (a : DirichletCharacter ℂ q) (m : ZMod q) :
    (∑ b : DirichletCharacter ℂ q, ‖jacobi a b m‖^2) =
      (q.totient : ℝ) * ‖jacobi 1 1 m‖ := by
  classical
  let g (v : ZMod q) : ℂ := if IsUnit v then a (m-v) else 0
  let h (v : ZMod q) : ℝ := if IsUnit v ∧ IsUnit (m-v) then 1 else 0
  have G (v : ZMod q) (hv : ¬IsUnit v) : g v = 0 := ite_eq_right hv
  have eqJ (b : DirichletCharacter ℂ q) :
      (∑ v : ZMod q, g v * b v) = jacobi a b m := by
    have E (v : ZMod q) : g v * b v = a (m-v) * b v := by
      by_cases hv : IsUnit v
      · simp [g, hv]
      · simp [g, hv, MulChar.map_nonunit b hv]
    simp only [E, jacobi]
    simpa only [Equiv.subLeft_apply, sub_sub_cancel] using
      Equiv.sum_comp (Equiv.subLeft m) (fun v : ZMod q => a v * b (m-v))
  have ht (v : ZMod q) : ‖g v‖^2 = h v := by
    by_cases hv : IsUnit v
    · by_cases hw : IsUnit (m-v)
      · have H : ‖a (m-v)‖ = 1 := by simpa only [hw.unit_spec] using a.unit_norm_eq_one hw.unit
        simp [g, h, hv, hw, H]
      · simp [g, h, hv, hw, MulChar.map_nonunit a hw]
    · simp [g, h, hv]
  have Lt (v : ZMod q) :
      (1 : DirichletCharacter ℂ q) v * (1 : DirichletCharacter ℂ q) (m-v) = (h v : ℂ) := by
    by_cases hv : IsUnit v <;> by_cases hw : IsUnit (m-v) <;>
      simp [h, hv, hw, MulChar.one_apply, MulChar.map_nonunit]
  have eqO : ‖jacobi (1 : DirichletCharacter ℂ q) 1 m‖ = ∑ v, h v := by
    rw [jacobi]
    simp only [Lt, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun _ _ => by dsimp [h]; split_ifs <;> norm_num))
  simpa only [eqJ, ht, ← eqO] using char_parseval g G

theorem jacobi_normalized_row_parseval {q : ℕ} [NeZero q] (a : DirichletCharacter ℂ q)
    (m : ZMod q) (ho : 0 < ‖jacobi (1 : DirichletCharacter ℂ q) 1 m‖) :
    (∑ b : DirichletCharacter ℂ q, ‖jacobi a b m / jacobi 1 1 m‖^2) =
      (q.totient : ℝ) / ‖jacobi (1 : DirichletCharacter ℂ q) 1 m‖ := by
  simp only [norm_div, div_pow, ← Finset.sum_div, jacobi_row_parseval]
  field_simp

end CubicMass
end HeightProductionSection28

section HeightProductionSection29
open scoped BigOperators
open DirichletCharacter

namespace CubicLocal

theorem square_row (p e m : ℕ) [NeZero (p^e)] (hp : p.Prime) (he : 0 < e)
    (hem : Even m) (hm : ¬p ∣ m) (A : DirichletCharacter ℂ (p^e)) :
    (∑ B : DirichletCharacter ℂ (p^e),
      ‖CubicMass.jacobi A B (m:ZMod (p^e)) / CubicMass.jacobi 1 1 (m:ZMod (p^e))‖^2) =
      ((p:ℝ)-1) / ((p:ℝ)-2) := by
  cases e with
  | zero => omega
  | succ j =>
    have h3 : 3 ≤ p := by
      have hnot : p ≠ 2 := fun h => hm (h.symm ▸ hem.two_dvd)
      have := hp.two_le
      omega
    have pR : (3:ℝ) ≤ p := by exact_mod_cast h3
    have p_pos : (0:ℝ) < p := by positivity
    have p_sub_pos : 0 < (p:ℝ)-2 := by linarith
    have oq : ∀ (q : ℕ) [NeZero q], q = p^j*p →
        ‖CubicMass.jacobi (1 : DirichletCharacter ℂ q) 1
          (m : ZMod q)‖ = (p:ℝ)^j * ((p:ℝ)-2) := by
      intro q _ E
      subst q
      exact ordinary_norm_pp hp hm
    have o := oq (p^(j+1)) (pow_succ p j)
    rw [CubicMass.jacobi_normalized_row_parseval A _ (by rw [o]; positivity), o,
      Nat.totient_prime_pow_succ hp]
    push_cast [Nat.cast_sub hp.one_lt.le]
    field_simp

end CubicLocal
end HeightProductionSection29

section HeightProductionSection30
open Finset DirichletCharacter
open scoped BigOperators Classical

namespace SignedHeight

noncomputable def goodRow (m q : ℕ) : ℝ :=
  if h : q = 0 then 0 else
    let _ : NeZero q := ⟨h⟩
    CRT.exactRow (1 : DirichletCharacter ℂ q) m q

theorem goodRow_of_ne_zero (m q : ℕ) [NeZero q] :
    goodRow m q = CRT.exactRow (1 : DirichletCharacter ℂ q) m q := by
  simp [goodRow, NeZero.ne q]

theorem goodRow_mul (m u v : ℕ) (hu : u ≠ 0) (hv : v ≠ 0) (hc : u.Coprime v) :
    goodRow m (u*v) = goodRow m u * goodRow m v := by
  let _ : NeZero u := ⟨hu⟩
  let _ : NeZero v := ⟨hv⟩
  let _ : NeZero (u*v) := ⟨mul_ne_zero hu hv⟩
  simp only [goodRow_of_ne_zero]
  rw [← CRT.glue_one hc, CRT.exactRow_factor hc _ _ _ _ _ dvd_rfl dvd_rfl]

theorem goodRow_one (m : ℕ) : goodRow m 1 = 1 := by
  rw [goodRow_of_ne_zero]
  unfold CRT.exactRow
  have H (c : DirichletCharacter ℂ 1) : c = 1 := Subsingleton.elim _ _
  simp only [H, conductor_one, ite_true]
  have J : CRT.J (1 : DirichletCharacter ℂ 1) 1 (m : ZMod 1) = 1 := by
    unfold CRT.J
    have H' (x : ZMod 1) : x = 1 := Subsingleton.elim _ _
    simp only [H', map_one, mul_one, Finset.sum_const, Finset.card_univ, ZMod.card,
      Nat.cast_one, one_nsmul]
  simp [CRT.weight, J, Finset.card_univ]

private theorem principal_weight_one {q : ℕ} [NeZero q] (m : ℕ)
    (Jnz : CRT.J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q) ≠ 0) :
    CRT.weight (1 : DirichletCharacter ℂ q) 1 m = 1 := by
  simp [CRT.weight, div_self Jnz]

theorem goodRow_prime {p m : ℕ} (hp : p.Prime) (he : Even m) (hm : ¬p ∣ m) :
    goodRow m p = ((p : ℝ)-2)⁻¹ := by
  classical
  let _ : NeZero p := ⟨hp.ne_zero⟩
  rw [goodRow_of_ne_zero]
  have h3 : 3 ≤ p := by
    have h2 : p ≠ 2 := fun hh => hm (hh ▸ he.two_dvd)
    have := hp.two_le
    omega
  have h3R : (3:ℝ) ≤ p := by exact_mod_cast h3
  have hn : 0 < (p:ℝ)-2 := by linarith
  have eqD (q : ℕ) [NeZero q] (h : q = p* p^0) :
      ‖CRT.J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖ =
      ((p:ℝ)-2) := by
    subst q
    rw [show (p:ℝ)-2 = ((p^0:ℕ):ℝ) * (if p ∣ m then (p:ℝ)-1 else (p:ℝ)-2) by simp [hm]]
    exact CubicLocal.ordinary_norm_pp_full hp
  have Jnz : CRT.J (1 : DirichletCharacter ℂ p) 1 (m : ZMod p) ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [eqD p (by simp)]
    exact hn.ne'
  have E (q : ℕ) (hq : q = p^1) [NeZero q] :
      (∑ β : DirichletCharacter ℂ q, CRT.weight 1 β m) = ((p:ℝ)-1)/((p:ℝ)-2) := by
    subst q
    exact CubicLocal.square_row p 1 m hp (Nat.succ_pos _) he hm 1
  have ES := E p (pow_one p).symm
  let w (C : DirichletCharacter ℂ p) := CRT.weight 1 C m
  have hl (C : DirichletCharacter ℂ p) :
      (if C.conductor = p then w C else 0) = if C = 1 then 0 else w C := by
    obtain H | H := (Nat.dvd_prime hp).mp C.conductor_dvd_level
    · have e := eq_one_iff_conductor_eq_one.mpr H
      subst C
      rw [ite_eq_right (fun H1 => hp.ne_one (H1.symm.trans H)), ite_eq_left rfl]
    · have hne : C ≠ 1 := fun e => hp.ne_one (H.symm.trans (eq_one_iff_conductor_eq_one.mp e))
      simp [H,hne]
  unfold CRT.exactRow
  change (∑ C : DirichletCharacter ℂ p, if C.conductor = p then w C else 0) = _
  simp_rw [hl]
  have H : (∑ C : DirichletCharacter ℂ p, if C = 1 then 0 else w C) + 1 = ∑ C, w C := by
    have hl' : ∑ C : DirichletCharacter ℂ p, (if C = 1 then 0 else w C) = ∑ C ∈ univ.erase 1, w C := by
      have hU : (univ : Finset (DirichletCharacter ℂ p)).filter (fun C => C ≠ 1) = univ.erase 1 := by
        ext C
        simp
      rw [← hU, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro C _
      by_cases hC : C = 1 <;> simp [hC]
    rw [hl', ← principal_weight_one m Jnz]
    exact Finset.sum_erase_add _ _ (Finset.mem_univ _)
  rw [ES] at H
  apply (eq_sub_of_add_eq H).trans
  field_simp
  ring

theorem goodRow_squarefree (m : ℕ) (he : Even m) :
    ∀ u : ℕ, Squarefree u → u.Coprime m →
      goodRow m u = ∏ p ∈ u.primeFactors, ((p:ℝ)-2)⁻¹ := by
  apply Nat.recOnPrimePow
  · intro hs _
    exact False.elim (hs.ne_zero rfl)
  · intro _ _
    simp [goodRow_one]
  · intro u p k hp hpu hk IH hsq hcop
    have hsqP := hsq.of_mul_left
    have hk1 : k=1 := by
      have H := hsqP.natFactorization_le_one p
      simp [hp.factorization_pow] at H
      omega
    subst k
    simp only [pow_one] at hsq hcop ⊢
    have hcu : p.Coprime u := hp.coprime_iff_not_dvd.mpr hpu
    have hcp : p.Coprime m := hcop.of_dvd_left (dvd_mul_right p u)
    have hcu' : u.Coprime m := hcop.of_dvd_left (dvd_mul_left u p)
    have usq := hsq.of_mul_right
    rw [goodRow_mul m p u hp.ne_zero usq.ne_zero hcu,
      IH usq hcu', goodRow_prime hp he (hp.coprime_iff_not_dvd.mp hcp),
      Nat.primeFactors_mul hp.ne_zero usq.ne_zero, hp.primeFactors, Finset.singleton_union,
      Finset.prod_insert (fun mem => hpu (Nat.dvd_of_mem_primeFactors mem))]

end SignedHeight
end HeightProductionSection30

section HeightProductionSection31
open Finset

namespace SignedHeight

def primeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

theorem primeKernel_dvd (n : ℕ) : primeKernel n ∣ n := Nat.prod_primeFactors_dvd n

theorem primeKernel_ne_zero (n : ℕ) : primeKernel n ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero)

theorem primeKernel_factors (n : ℕ) : (primeKernel n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod_primeFactors n



theorem conductor_mass_zero_of_not_dvd
    (r s : ℕ) (hr : r ≠ 0) (hs : s ≠ 0) (W : ℕ → ℝ)
    (nonneg : ∀ n, 0 ≤ W n)
    (stable : ∀ d D : ℕ, d ≠ 0 → D ≠ 0 → r ∣ d → d ∣ D →
      d.primeFactors = D.primeFactors →
      (∑ x ∈ d.divisors, W x) = ∑ x ∈ D.divisors, W x)
    (exclude : ¬s ∣ r.lcm (primeKernel (r.lcm s))) : W s = 0 := by
  let D := r.lcm s
  let d := r.lcm (primeKernel D)
  have hD : D ≠ 0 := Nat.lcm_ne_zero hr hs
  have hd : d ≠ 0 := Nat.lcm_ne_zero hr (primeKernel_ne_zero _)
  have hrD : r ∣ D := Nat.dvd_lcm_left _ _
  have hrd : r ∣ d := Nat.dvd_lcm_left _ _
  have hsd : s ∣ D := Nat.dvd_lcm_right _ _
  have hdD : d ∣ D := Nat.lcm_dvd hrD (primeKernel_dvd _)
  have hf : d.primeFactors = D.primeFactors := by
    apply subset_antisymm (Nat.primeFactors_mono hdD hD)
    rw [← primeKernel_factors D]
    exact Nat.primeFactors_mono (Nat.dvd_lcm_right _ _) hd
  have inc : d.divisors ⊆ D.divisors := by
    intro x hx
    exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans hdD, hD⟩
  exact zero_of_equal_nonneg_subtotals inc (fun x _ => nonneg x)
    (stable d D hd hD hrd hdD hf)
    (Nat.mem_divisors.mpr ⟨hsd, hD⟩) (fun h => exclude (Nat.mem_divisors.mp h).1)

end SignedHeight
end HeightProductionSection31

section HeightProductionSection32
open Finset

namespace SignedHeight

theorem support_split
    (r B s : ℕ) (hr : r ≠ 0) (hB : B ≠ 0) (hs : s ≠ 0) (hrB : r ∣ B) (W : ℕ → ℝ)
    (nonneg : ∀ n, 0 ≤ W n)
    (stable : ∀ d D : ℕ, d ≠ 0 → D ≠ 0 → r ∣ d → d ∣ D →
      d.primeFactors = D.primeFactors →
      (∑ x ∈ d.divisors, W x) = ∑ x ∈ D.divisors, W x)
    (hsW : W s ≠ 0) :
    ∃ b u : ℕ, b ∣ B ∧ Squarefree u ∧ B.Coprime u ∧ b*u=s := by
  classical
  let D := r.lcm s
  let T := D.primeFactors \ B.primeFactors
  let U := ∏ p ∈ T, p
  have hD : D ≠ 0 := Nat.lcm_ne_zero hr hs
  have hrD : r ∣ D := Nat.dvd_lcm_left _ _
  have hsD : s ∣ D := Nat.dvd_lcm_right _ _
  have hT (p : ℕ) (hp : p ∈ T) : p.Prime :=
    Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
  have hU : U ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun p hp => (hT p hp).ne_zero)
  have hfacU : U.primeFactors = T := Nat.primeFactors_prod hT
  have hUsq : Squarefree U := by
    have H : U ∣ primeKernel D := by
      change (∏ p ∈ T, p) ∣ ∏ p ∈ D.primeFactors, p
      exact Finset.prod_dvd_prod_of_subset _ _ id sdiff_subset
    exact (Nat.squarefree_prod_primeFactors D).squarefree_of_dvd H
  have hc : B.Coprime U := by
    apply Nat.Coprime.prod_right
    intro p hp
    apply Nat.Coprime.symm
    apply (hT p hp).coprime_iff_not_dvd.mpr
    intro hdiv
    exact (mem_sdiff.mp hp).2 (Nat.mem_primeFactors.mpr ⟨hT p hp,hdiv,hB⟩)
  let R := B*U
  have hR : R ≠ 0 := mul_ne_zero hB hU
  have dsub : D.primeFactors ⊆ R.primeFactors := by
    rw [Nat.primeFactors_mul hB hU, hfacU]
    intro p hp
    by_cases hpB : p ∈ B.primeFactors
    · exact mem_union_left _ hpB
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hp,hpB⟩)
  let d := D.gcd R
  have hd : d ≠ 0 := fun H => hD (Nat.gcd_eq_zero_iff.mp H).1
  have hrd : r ∣ d := Nat.dvd_gcd hrD (hrB.trans (dvd_mul_right B U))
  have hdD : d ∣ D := Nat.gcd_dvd_left D R
  have hf : d.primeFactors = D.primeFactors := by
    rw [Nat.primeFactors_gcd hD hR]
    exact inter_eq_left.mpr dsub
  have inc : d.divisors ⊆ D.divisors := by
    intro x hx
    exact Nat.mem_divisors.mpr ⟨(Nat.mem_divisors.mp hx).1.trans hdD, hD⟩
  have hsDiv : s ∣ d := by
    by_contra hx
    exact hsW (zero_of_equal_nonneg_subtotals inc (fun x _ => nonneg x)
      (stable d D hd hD hrd hdD hf)
      (Nat.mem_divisors.mpr ⟨hsD, hD⟩) (fun h => hx (Nat.mem_divisors.mp h).1))
  have hm : s ∣ B*U := hsDiv.trans (Nat.gcd_dvd_right D R)
  obtain ⟨b,u,hb,hu,E⟩ := Nat.dvd_mul.mp hm
  exact ⟨b,u,hb,hUsq.squarefree_of_dvd hu,hc.of_dvd_right hu,E⟩


end SignedHeight
end HeightProductionSection32

section HeightProductionSection33
open Finset DirichletCharacter
open scoped BigOperators Classical

namespace SignedHeight

theorem rawMass_good_formula
    (S : {r s : ℕ} → DirichletCharacter ℂ r → DirichletCharacter ℂ s → ℕ → ℂ)
    {r B m : ℕ} (α : DirichletCharacter ℂ r) (hr : r ≠ 0) (hB : B ≠ 0) (hrB : r ∣ B)
    (hmB : m ∣ B) (he : Even m) (K : ℝ) (hK : LevelFormula S α m K)
    (stable : ∀ d D : ℕ, d ≠ 0 → D ≠ 0 → r ∣ d → d ∣ D →
      d.primeFactors = D.primeFactors →
      (∑ x ∈ d.divisors, rawMass S α m x) = ∑ x ∈ D.divisors, rawMass S α m x) :
    ∀ s > 0, rawMass S α m s = ∑ d ∈ s.divisors with d ∈ B.divisors,
      rawMass S α m d * heightGoodWeight B (s/d) := by
  intro s hsp
  let W := rawMass S α m
  let R := s.divisors.filter (fun d => d ∈ B.divisors)
  change W s = ∑ d ∈ R, W d * heightGoodWeight B (s/d)
  have split := support_split r B s hr hB hsp.ne' hrB W (rawMass_nonneg S α m) stable
  have hh (b u : ℕ) (hb : b ∣ B) (hu : Squarefree u) (hcu : B.Coprime u) :
      W (b*u) = W b * heightGoodWeight B u := by
    let _ : NeZero B := ⟨hB⟩
    let _ : NeZero u := ⟨hu.ne_zero⟩
    let _ : NeZero (B*u) := ⟨mul_ne_zero hB hu.ne_zero⟩
    change rawMass S α m (b*u) = rawMass S α m b * heightGoodWeight B u
    rw [rawMass_factor S α m K hK hrB hb hcu, ← goodRow_of_ne_zero m u,
      goodRow_squarefree m he u hu (hcu.of_dvd_left hmB).symm, heightGoodWeight_apply]
    simp [hu,hcu.symm]
  by_cases good : ∃ b u : ℕ, b ∣ B ∧ Squarefree u ∧ B.Coprime u ∧ b*u=s
  · obtain ⟨b,u,hb,hu,hcu,hbu⟩ := good
    have hb0 : b ≠ 0 := ne_zero_of_dvd_ne_zero hB hb
    have hbs : b ∣ s := hbu ▸ dvd_mul_right b u
    have hbR : b ∈ R := mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hbs,hsp.ne'⟩,
      Nat.mem_divisors.mpr ⟨hb,hB⟩⟩
    have hsdiv : s/b = u := by rw [← hbu, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hb0)]
    rw [Finset.sum_eq_single_of_mem b hbR, hsdiv]
    · rw [← hbu]
      exact hh b u hb hu hcu
    · intro d hd hne
      have hds : d ∣ s := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
      have hdB : d ∣ B := (Nat.mem_divisors.mp (mem_filter.mp hd).2).1
      rw [heightGoodWeight_apply]
      have no : ¬ (Squarefree (s/d) ∧ (s/d).Coprime B) := by
        intro E
        have hc : B.Coprime (u*(s/d)) := hcu.mul_right E.2.symm
        have E' : d*(s/d)=b*u := (Nat.mul_div_cancel' hds).trans hbu.symm
        exact hne ((coprime_conductor_mul_match hc hdB (dvd_mul_left _ _) hb (dvd_mul_right _ _)).mp E').1
      simp [no]
  · have hsW : W s = 0 := by
      by_contra hz
      exact good (split hz)
    rw [hsW]
    symm
    apply Finset.sum_eq_zero
    intro d hd
    have hds : d ∣ s := (Nat.mem_divisors.mp (mem_filter.mp hd).1).1
    have hdB : d ∣ B := (Nat.mem_divisors.mp (mem_filter.mp hd).2).1
    have no : ¬ (Squarefree (s/d) ∧ (s/d).Coprime B) := fun E =>
      good ⟨d,s/d,hdB,E.1,E.2.symm,Nat.mul_div_cancel' hds⟩
    simp [heightGoodWeight_apply,no]

end SignedHeight
end HeightProductionSection33

section HeightProductionSection34
open Filter Finset DirichletCharacter
open scoped BigOperators Topology
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof

open SignedHeight

set_option maxHeartbeats 1200000 in
theorem Conjectures.Goldbach.PartnerHeightRenormalizedSquare : (
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let P := (1 : DirichletCharacter ℂ 1)
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let valid := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
  exact ∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ∃ b₀ : ℝ, ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T, ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ b.1 ≤ Y) ∧ |(∑ b ∈ F, ‖S α b.2 m‖^2) - ‖O m‖ * Real.log (Y:ℝ) - b₀| ≤ ε) := by
  classical
  dsimp only
  intro r hr α hα m hm he
  let S := @TwistedGoldbachLocalProduct.series
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  let B := r * m
  have hrB : r ∣ B := dvd_mul_right r m
  have hmB : m ∣ B := dvd_mul_left m r
  have hB : B ≠ 0 := mul_ne_zero (NeZero.ne r) hm.ne'
  have hO : 0 < ‖O‖ := by
    have h := TwistedGoldbachMixedPrincipal.ordinary_at_least_one m hm he
    exact zero_lt_one.trans_le (h.trans (Complex.re_le_norm O))
  have hOrd : Tendsto (fun n : ℕ => ∏ p ∈ n.factorial.primeFactors,
      heightOrdinaryPrimeFactor m p) atTop (𝓝 ‖O‖) := by
    let P : DirichletCharacter ℂ 1 := 1
    apply height_ordinary_factorial_limit m
      (TwistedGoldbachSingularSeries.coefficient P P m)
    · simpa only [one_mul, O, S, TwistedGoldbachLocalProduct.series] using TwistedGoldbachSingularSeries.partial_limit P P m hm 1 one_ne_zero
    · intro q _
      simpa only [P, map_one, heightNormalizedPrincipal, heightPrincipJacobi, TwistedGoldbachSingularSeries.normalized] using (TwistedGoldbachSingularSeries.ambient_sum
        (α := (1 : DirichletCharacter ℂ 1)) (β := (1 : DirichletCharacter ℂ 1))
        isPrimitive_one_level_one isPrimitive_one_level_one (one_dvd q) (one_dvd q) m)
    · intro q _
      exact TwistedGoldbachMixedPrincipal.ordinary_product q m
  have hLevels : LevelTotals r (rawMass S α m) m (‖O‖ ^ 2) := by
    apply levelTotals_of_family
    intro D _ hD
    exact Conjectures.Goldbach.PartnerLevelParseval D r hD α hα m hm he
  have hK : LevelFormula S α m (‖O‖ ^ 2) := by
    apply level_formula_of_cross S α m O
    · intro q _
      exact TwistedGoldbachLocalProduct.principal_ne_zero q m he
    · intro q s _ hrL hsL β hβ
      letI : NeZero s := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne q) hsL⟩
      exact TwistedGoldbachConductorRatio.conductor_identity hα hβ hrL hsL m hm
  have hMass : ∀ n > 0, rawMass S α m n =
      ∑ b ∈ n.divisors with b ∈ B.divisors,
        rawMass S α m b * heightGoodWeight B (n/b) := by
    exact rawMass_good_formula S α (NeZero.ne r) hB hrB hmB he (‖O‖^2) hK hLevels.stable
  exact finalAssembly S α hB hmB hrB he hO hLevels hOrd hMass
end HeightProductionSection34
