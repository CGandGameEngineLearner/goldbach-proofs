import ShiftExceptionModelEnergy
import Conjectures.Goldbach.ThreeQuartersModelSqrtExceptions


section
/- Source: ShiftWideTimeEnergy.lean -/
open Finset MeasureTheory
namespace Goldbach.ShiftTimeEnergy
noncomputable section
open scoped Classical
open Goldbach.ShiftWideArc GB6Growth

abbrev M (Y : ℕ) := GB6Var.G (grid Y) (height Y) Y
abbrev P (Y : ℕ) := (arcs Y).indicator (S Y)

def timeEnergy (Y : ℕ) := ∫ t in (0:ℝ)..1, ‖(M Y t)^2 - (P Y t)^2‖^2

private theorem squareTwist_int {f : ℝ → ℂ} (hf : MemLp f 2 GB5Variance.unitMeasure) (m : ℕ) :
    IntervalIntegrable (fun t => f t^2 * phase (-(m:ℝ)*t)) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
  have ha : AEStronglyMeasurable (fun t => f t^2 * phase (-(m:ℝ)*t)) GB5Variance.unitMeasure :=
    (hf.aestronglyMeasurable.pow 2).mul (by unfold phase; fun_prop)
  apply (integrable_norm_iff ha).mp
  simp only [norm_mul, norm_pow, phase, Complex.norm_exp_ofReal_mul_I, mul_one]
  exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf

private theorem prime_mem (Y : ℕ) : MemLp (P Y) 2 GB5Variance.unitMeasure :=
  (GB6Var.S_memLp Y).indicator (EffectiveArcEndpoint.frontierMeasurable _ _ _).nullMeasurableSet

theorem prime_sq_mem (Y : ℕ) : MemLp (fun t => (P Y t)^2) 2 GB5Variance.unitMeasure := by
  have hc : Continuous (fun t => (S Y t)^2) := by unfold S phase; fun_prop
  have hh : MemLp (fun t => (S Y t)^2) 2 GB5Variance.unitMeasure := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    exact ((hc.norm.pow 2).intervalIntegrable (μ := volume) 0 1).1
  have ha : MeasurableSet (arcs Y) := EffectiveArcEndpoint.frontierMeasurable _ _ _
  have heq : (fun t => (P Y t)^2) = (arcs Y).indicator (fun t => (S Y t)^2) := by
    funext t
    by_cases h : t ∈ arcs Y <;> simp [P,h]
  rw [heq]
  exact hh.indicator ha.nullMeasurableSet

private theorem kernel_sup (Y : ℕ) (u : ℝ) : ‖GB6Kernel.kernel Y u‖ ≤ (Y:ℝ)+1 := by
  unfold GB6Kernel.kernel
  apply (norm_sum_le _ _).trans_eq
  have hn (x : ℝ) : ‖GB6Kernel.phase x‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  simp only [hn,Finset.sum_const, Finset.card_range,nsmul_eq_mul,mul_one,Nat.cast_add,Nat.cast_one]

private def majorant (Y : ℕ) : ℝ := ∑ q ∈ Icc 1 (grid Y),
  ∑ a ∈ GB6Geometry.numerators q, ‖ThreeQArith.mean q a‖ * ((Y:ℝ)+1)

set_option maxHeartbeats 2000000 in
private theorem model_sup (Y : ℕ) (t : ℝ) : ‖M Y t‖ ≤ majorant Y := by
  unfold M GB6Var.G GB6Geometry.model majorant
  refine (norm_sum_le _ _).trans (sum_le_sum fun q _ => (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_))
  by_cases h : t ∈ GB6Geometry.window (height Y) Y q a
  · simp only [Set.indicator_of_mem h, norm_mul]
    exact mul_le_mul_of_nonneg_left (kernel_sup Y _) (norm_nonneg _)
  · simp only [Set.indicator_of_notMem h,norm_zero]; positivity

set_option maxHeartbeats 2000000 in
theorem model_sq_mem (Y : ℕ) : MemLp (fun t => (M Y t)^2) 2 GB5Variance.unitMeasure := by
  have hg : AEStronglyMeasurable (M Y) GB5Variance.unitMeasure :=
    (GB6Var.G_memLp (grid Y) (height Y) Y).aestronglyMeasurable
  have ha : AEStronglyMeasurable (fun t => M Y t^2) GB5Variance.unitMeasure := hg.pow 2
  apply MemLp.of_bound ha ((majorant Y)^2)
  apply Filter.Eventually.of_forall
  intro t
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (model_sup Y t) _

theorem coefficient_difference (Y m : ℕ) :
    ReflectedArcModel.modelCoefficient Y m - coefficient (arcs Y) Y m =
      GB5Variance.modeCoeff (fun t => M Y t^2 - P Y t^2) m := by
  have hi := (intervalIntegral.integral_sub (squareTwist_int (GB6Var.G_memLp (grid Y) (height Y) Y) m)
                (squareTwist_int (prime_mem Y) m)).symm
  have hp : coefficient (arcs Y) Y m = ∫ t in (0:ℝ)..1, P Y t^2*phase (-(m:ℝ)*t) := by
    apply intervalIntegral.integral_congr
    intro t _
    by_cases h : t ∈ arcs Y <;> simp [P,integrand,h]
  rw [hp]
  change (∫ t in (0:ℝ)..1, M Y t^2*phase (-(m:ℝ)*t)) - _ = _
  rw [hi]
  apply intervalIntegral.integral_congr
  intro t _
  exact (sub_mul _ _ _).symm

theorem finite_energy (Y : ℕ) (s : Finset ℕ) :
    ∑ m ∈ s, ‖ReflectedArcModel.modelCoefficient Y m - coefficient (arcs Y) Y m‖^2 ≤ timeEnergy Y := by
  simp_rw [coefficient_difference]
  exact GB5Variance.finite_bessel s _ ((model_sq_mem Y).sub (prime_sq_mem Y))

/-- Sum over the interior-scaling relation after extending to a rectangle of
cutoffs. This gives a concrete integrated error criterion for the frozen goal. -/
theorem multiscale_bessel (X : ℕ) :
    ∑ m ∈ Icc (X/2) (2*X), ∑ Y ∈ interiorScales m,
      ‖ReflectedArcModel.modelCoefficient Y m - coefficient (arcs Y) Y m‖^2 ≤
    ∑ Y ∈ Icc (X/4) (2*X), timeEnergy Y := by
  let e (m Y : ℕ) := ‖ReflectedArcModel.modelCoefficient Y m - coefficient (arcs Y) Y m‖^2
  calc
    _ ≤ ∑ m ∈ Icc (X/2) (2*X), ∑ Y ∈ Icc (X/4) (2*X), e m Y := by
      apply sum_le_sum
      intro m hm
      apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
      intro Y hY
      obtain ⟨h1,h2⟩ := mem_Icc.mp hm
      obtain ⟨h3,h4⟩ := mem_Icc.mp hY
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    _ = ∑ Y ∈ Icc (X/4) (2*X), ∑ m ∈ Icc (X/2) (2*X), e m Y := sum_comm
    _ ≤ _ := sum_le_sum fun Y _ => finite_energy Y _
/-- The square model and masked prime sum vanish off exactly the working arc cover. -/
theorem model_off_arcs (Y : ℕ) {t : ℝ} (ht : t ∉ arcs Y) : M Y t = 0 := by
  apply sum_eq_zero
  intro q hq
  apply sum_eq_zero
  intro a ha
  apply Set.indicator_of_notMem
  intro hw
  apply ht
  have hq' := mem_Icc.mp hq
  obtain ⟨ha1,ha2⟩ := mem_filter.mp ha
  have ha' := mem_range.mp ha1
  have hw' := (GB6Geometry.mem_window Y q a t).mp hw
  have hg : grid Y = Q Y := grid_eq_floor Y
  have hh : height Y = H Y := by simp only [height,H,hg]
  exact ⟨q,a,hq'.1,hq'.2.trans_eq hg,by omega,ha2,by simpa only [GB6Geometry.center,GB6Geometry.width,hh] using hw'⟩

theorem timeEnergy_eq (Y : ℕ) : timeEnergy Y = ∫ t in (0:ℝ)..1,
    (arcs Y).indicator (fun u => ‖M Y u - S Y u‖^2 * ‖M Y u + S Y u‖^2) t := by
  apply intervalIntegral.integral_congr
  intro t _
  by_cases h : t ∈ arcs Y
  · simp only [Set.indicator_of_mem h,P,sq_sub_sq,norm_mul,mul_pow]; ring
  · simp [P,h,model_off_arcs Y h]

end
end Goldbach.ShiftTimeEnergy
end


section
/- Source: TimeEnergyCriterion.lean -/
open Finset
namespace Goldbach
open ShiftTimeEnergy

/-- The remaining mean-square hypothesis expressed as a sum of positive
time-domain integrals of the actual arc discrepancy. -/
theorem binary_shift_exception_union_of_arc_integrals {α K : ℝ}
    (ha : 0 ≤ α) (ha' : α < 4/5) (hK : 0 < K)
    (hE : ∃ N : ℕ, ∀ X ≥ N,
      (∑ Y ∈ Icc (X/4) (2*X), ∫ t in (0:ℝ)..1,
        (ShiftWideArc.arcs Y).indicator
          (fun u => ‖M Y u - ShiftWideArc.S Y u‖^2 * ‖M Y u + ShiftWideArc.S Y u‖^2) t)
        ≤ K*(X:ℝ)^(3+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (ShiftWideArc.missed X).card^5 ≤ X^4 := by
  obtain ⟨N,hE⟩ := hE
  apply binary_shift_exception_union_of_model_energy ha ha' hK
  refine ⟨N,?_⟩
  intro X hx
  apply (multiscale_bessel X).trans
  simpa only [timeEnergy_eq] using hE X hx

end Goldbach
end


section
/- Source: TruncatedModelFloor.lean -/
open Filter GB6Kernel GB6Geometry GB6Growth
namespace Goldbach.ReflectedArcModel
noncomputable section

/-- Remove any collection of high denominators by lowering the denominator
cutoff, while retaining the original wide-arc width. -/
def truncatedCoefficient (r Y m : ℕ) : ℂ :=
  ∫ t in (0:ℝ)..1,
    (model r (height Y) Y ThreeQArith.mean t)^2 * phase (-(m:ℝ)*t)

theorem uniform_truncated_model_floor :
    ∃ N : ℕ, ∀ Y ≥ N, ∀ r : ℕ, 1 ≤ r → r ≤ grid Y →
    ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      (Y:ℝ)/8 ≤ (truncatedCoefficient r Y m).re := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp eventual_geometry
  refine ⟨N,?_⟩
  intro Y hy r hr hrQ m hilo hihi he
  obtain ⟨hQ,hQH,hQY,hL,hsep⟩ := hN Y hy
  have hH : (0:ℝ)<height Y := by exact_mod_cast (hQ.trans hQH)
  have hlog : (Nat.log 2 r:ℝ) ≤ L Y := by
    unfold L
    exact_mod_cast Nat.log_mono_right (b:=2) (hrQ.trans (hQY.trans (by omega)))
  have hw : (height Y:ℝ) = 256*(grid Y:ℝ)*(L Y)^2 := by simp [height,L]
  apply reflected_model_floor hsep (hrQ.trans hQH) hr hilo hihi he
  apply (div_le_iff₀ (mul_pos (by norm_num) hH)).mpr
  rw [hw]
  have hcoef : 1+(Nat.log 2 r:ℝ) ≤ 16*(L Y)^2 := by nlinarith [sq_nonneg (L Y-1)]
  have hmul := mul_le_mul (show (r:ℝ) ≤ grid Y by exact_mod_cast hrQ) hcoef (by positivity) (by positivity)
  linarith only [hmul]

/-- Choosing the greatest integer strictly below Y^(1/4) avoids double
counting when Y is a fourth power. At sufficiently large Y the minimum with
grid Y is redundant; leaving it in place makes the cutoff well-typed at 0. -/
def innerCutoff (Y : ℕ) : ℕ := min (grid Y) (⌈(Y:ℝ)^(1/4:ℝ)⌉₊-1)

theorem mem_innerCutoff {Y q : ℕ} (hq : 0<q) :
    q ≤ innerCutoff Y ↔ q ≤ grid Y ∧ (q:ℝ) < (Y:ℝ)^(1/4:ℝ) := by
  have hh : q ≤ ⌈(Y:ℝ)^(1/4:ℝ)⌉₊-1 ↔ q < ⌈(Y:ℝ)^(1/4:ℝ)⌉₊ := by omega
  rw [innerCutoff,le_min_iff,hh,Nat.lt_ceil]

theorem inner_model_floor :
    ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      (Y:ℝ)/8 ≤ (truncatedCoefficient (innerCutoff Y) Y m).re := by
  obtain ⟨N,hN⟩ := uniform_truncated_model_floor
  obtain ⟨N',hN'⟩ := eventually_atTop.mp eventual_geometry
  have hg := ((tendsto_rpow_atTop (by norm_num : 0 < (1/4:ℝ))).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop 1
  apply eventually_atTop.mp
  filter_upwards [hg,eventually_ge_atTop (max N N')] with Y hy hY
  apply hN Y (by omega) _ _ (min_le_left ..)
  apply (mem_innerCutoff (Y:=Y) (q:=1) (by decide)).mpr
  exact ⟨(hN' Y (by omega)).1,by simpa using hy⟩

end
end Goldbach.ReflectedArcModel
end


section
/- Source: OuterPrimeArcBound.lean -/
/-! Vaughan's estimate on the large-denominator part of the wide arcs.
The elementary transfer from von Mangoldt to prime weights and absorption of
logarithms adapt the corresponding steps of the accepted
L_goldbach_frontier_uncond_deep_second_moment (goldbach-proofs, Apache-2.0).
-/
open Finset Filter MeasureTheory Goldbach.ShiftWideArc
namespace Goldbach.OuterPrimeArc
noncomputable section
private theorem vaughan_denominator_terms {x q P T : ℝ} (hx : 0 < x) (hT : 0 < T)
    (hP : 0 < P) (hTsize : T ≤ Real.sqrt P) (hlow : P ≤ q) (hhigh : q ≤ x/P) :
    x / Real.sqrt q ≤ x/T ∧ Real.sqrt (x*q) ≤ x/T := by
  have hq := hP.trans_le hlow
  have hT2 : T^2 ≤ P := (Real.le_sqrt (by positivity) hP.le).mp hTsize
  constructor
  · exact div_le_div_of_nonneg_left hx.le hT (hTsize.trans (Real.sqrt_le_sqrt hlow))
  · apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    rw [div_pow, le_div_iff₀ (by positivity)]
    have hprod := (le_div_iff₀ hP).mp hhigh
    nlinarith only [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT2 hq.le) hx.le,
      mul_le_mul_of_nonneg_left hprod hx.le]

private theorem mangoldt_pointwise_bridge (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    let w := fun k : ℕ => if k.Prime then Real.log (k : ℝ) else 0
    let e := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
    ‖∑ k ∈ Finset.range (n+1), ((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ ≤
      2 * Real.sqrt n * Real.log n := by
  intro w e
  have hnon (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k - w k := by
    by_cases hk : k.Prime <;> simp [w,hk,ArithmeticFunction.vonMangoldt_apply_prime]
  calc
    _ ≤ ∑ k ∈ Finset.range (n+1), ‖((ArithmeticFunction.vonMangoldt k - w k : ℝ):ℂ) * e ((k:ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n+1), (ArithmeticFunction.vonMangoldt k - w k) := by
      simp only [norm_mul,e,Complex.norm_exp_ofReal_mul_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hnon _)]
    _ = Chebyshev.psi n - Chebyshev.theta n := by
      rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
      simp [Chebyshev.psi,Chebyshev.theta,w,Finset.sum_filter,Finset.sum_sub_distrib]
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hn)


/-- These are actual wide arcs with a reduced denominator at least Y^(1/4). -/
def outer (Y : ℕ) : Set ℝ := {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q Y ∧ a ≤ q ∧
  a.Coprime q ∧ (Y:ℝ)^(1/4:ℝ) ≤ q ∧ |t-(a:ℝ)/q| ≤ (H Y:ℝ)/((q:ℝ)*Y)}

theorem outer_subset (Y : ℕ) : outer Y ⊆ arcs Y :=
  fun _ ⟨q,a,hq,hQ,ha,hc,_,ht⟩ => ⟨q,a,hq,hQ,ha,hc,ht⟩

theorem outer_measurable (n : ℕ) : MeasurableSet (outer n) := by
  simp only [outer,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iUnion
  intro a
  by_cases h : 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧ (n:ℝ)^(1/4:ℝ) ≤ q
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
    have hmeas : MeasurableSet {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (H n:ℝ) / (q * n)} :=
      measurableSet_le (show Continuous (fun t : ℝ => |t - (a : ℝ) / (q : ℝ)|) by fun_prop).measurable
        measurable_const
    convert hmeas using 1
    ext t
    exact ⟨fun h => h.2.2.2.2.2, fun h => ⟨h₁, h₂, h₃, h₄, h₅, h⟩⟩
  · convert MeasurableSet.empty (α := ℝ) using 1
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h₁, h₂, h₃, h₄, h₅, _⟩
    exact h ⟨h₁, h₂, h₃, h₄, h₅⟩


theorem vaughan_outer_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ outer n, ‖Goldbach.ShiftWideArc.S n t‖ ≤ (n:ℝ)^(7/8+ε) := by
  let e := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)
  let w := fun k : ℕ => if k.Prime then Real.log (k:ℝ) else 0
  let S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) := ∑ k ∈ Finset.range (n+1), (u k : ℂ) * e ((k:ℝ)*t)
  have ht : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).comp_tendsto ht).bound (by norm_num : (0:ℝ)<1/100000)
  filter_upwards [eventually_ge_atTop (2:ℕ), hsmall, (Real.tendsto_log_atTop.comp ht).eventually_ge_atTop 1,
    GB6Growth.eventual_geometry, OAI.Problem337.Vaughan.eventually_vonMangoldt_sum_log_bound]
    with n hn hlogs hL hgeom hv
  intro t houter
  obtain ⟨q,a,hqp,hqQ,_,hcop,hlo,hclose⟩ := houter
  let x : ℝ := n
  let L := Real.log x
  have hx : 0 < x := Nat.cast_pos.mpr (by omega)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  change 1 ≤ L at hL
  have hlog4 : L^4 ≤ (1/100000:ℝ)*x^ε := by
    change ‖L^(4:ℝ)‖ ≤ (1/100000:ℝ)*‖x^ε‖ at hlogs
    simpa only [Real.norm_eq_abs,Real.rpow_ofNat,
      abs_of_nonneg (show 0 ≤ L^4 by positivity),abs_of_nonneg (Real.rpow_nonneg hx.le ε)] using hlogs
  have hgrid : GB6Growth.grid n = Q n := GB6Growth.grid_eq_floor n
  have hheight : GB6Growth.height n = H n := by simp only [GB6Growth.height,H,hgrid]
  obtain ⟨_,hQH,hQn,_,hsep⟩ := hgeom
  rw [hgrid, hheight] at hQH
  rw [hgrid] at hQn
  rw [hheight] at hsep
  have hqr : (0:ℝ) < q := Nat.cast_pos.mpr hqp
  have hqH : q ≤ H n := hqQ.trans hQH
  have hmult : H n*q ≤ n := (Nat.mul_le_mul_left (H n) hqH).trans (by nlinarith only [hsep])
  have hmultr : (H n:ℝ)*(q:ℝ) ≤ x := by dsimp only [x]; exact_mod_cast hmult
  have hqsec : |t-(a:ℝ)/q| ≤ 1/(q:ℝ)^2 := by
    apply hclose.trans
    apply (div_le_div_iff₀ (mul_pos hqr hx) (sq_pos_of_pos hqr)).mpr
    change (H n:ℝ)*(q:ℝ)^2 ≤ 1*((q:ℝ)*x)
    nlinarith only [mul_le_mul_of_nonneg_right hmultr hqr.le]
  have hvq := hv t (a:ℤ) q hqp hcop.isCoprime (by simpa using hqsec) (hqQ.trans hQn)
  have hsum : S n ArithmeticFunction.vonMangoldt t = OAI.Problem337.Vaughan.weightedSum
      (Finset.Ioc 0 n) (fun k => OAI.Problem337.VaughanBilinear.phase (t*k)) ArithmeticFunction.vonMangoldt := by
    dsimp [S,e,OAI.Problem337.Vaughan.weightedSum,OAI.Problem337.VaughanBilinear.phase]
    rw [Nat.range_succ_eq_Icc_zero, ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le n)]
    simp only [ArithmeticFunction.map_zero,Complex.ofReal_zero,zero_mul,zero_add,Real.fourierChar_apply]
    apply Finset.sum_congr rfl
    intro k _; rw [mul_comm t (k:ℝ)]
  have hP : 0 < x^(1/4:ℝ) := Real.rpow_pos_of_pos hx _
  have hT : 0 < x^(1/8:ℝ) := Real.rpow_pos_of_pos hx _
  have hTlow : x^(1/8:ℝ) ≤ Real.sqrt (x^(1/4:ℝ)) := by
    rw [Real.sqrt_eq_rpow, ←Real.rpow_mul hx.le]; norm_num
  have hqcube : (q:ℝ) ≤ x^(1/3:ℝ) := (by exact_mod_cast hqQ : (q:ℝ) ≤ Q n).trans
    (Nat.floor_le (Real.rpow_nonneg hx.le _))
  have hqhigh : (q:ℝ) ≤ x/(x^(1/4:ℝ)) := by
    apply (le_div_iff₀ hP).mpr
    calc _ ≤ x^(3/4:ℝ)*x^(1/4:ℝ) := mul_le_mul_of_nonneg_right
              (hqcube.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))) hP.le
         _ = _ := by rw [← Real.rpow_add hx];norm_num
  obtain ⟨hl,hr⟩ := vaughan_denominator_terms hx hT hP hTlow hlo hqhigh
  have xid : x/x^(1/8:ℝ) = x^(7/8:ℝ) := by
    apply (div_eq_iff hT.ne').mpr
    rw [←Real.rpow_add hx]; norm_num
  rw [xid] at hl hr
  have hmiddle := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (4/5:ℝ) ≤ 7/8)
  have hbound : ‖S n ArithmeticFunction.vonMangoldt t‖ ≤ 81000*L^4*x^(7/8:ℝ) := by
    rw [hsum]
    apply hvq.trans
    change 16200*L^4*(x/Real.sqrt q+x^(4/5:ℝ)+Real.sqrt (x*q)) ≤ _
    calc _ ≤ 16200*L^4*(3*x^(7/8:ℝ)) := by gcongr; linarith only [hl,hr,hmiddle]
         _ ≤ _ := by nlinarith only [mul_nonneg (show 0≤L^4 by positivity) (Real.rpow_nonneg hx.le (7/8:ℝ))]
  have herr : ‖S n ArithmeticFunction.vonMangoldt t - S n w t‖ ≤ 2*Real.sqrt x*L := by
    simpa only [S, ← Finset.sum_sub_distrib, ← sub_mul, ← Complex.ofReal_sub] using mangoldt_pointwise_bridge n (by omega) t
  have hsqrt : Real.sqrt x ≤ x^(7/8:ℝ) := by
    rw [Real.sqrt_eq_rpow];exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hlogle : L ≤ L^4 := by simpa only [pow_one] using pow_le_pow_right₀ hL (by decide : 1 ≤ 4)
  have hres : 2*Real.sqrt x*L ≤ 2*L^4*x^(7/8:ℝ) := by
    calc _ = 2*(L*Real.sqrt x) := by ring
         _ ≤ 2*(L^4*x^(7/8:ℝ)) := by gcongr
         _ = _ := by ring
  have htriangle := norm_sub_le (S n ArithmeticFunction.vonMangoldt t) (S n ArithmeticFunction.vonMangoldt t - S n w t)
  rw [sub_sub_cancel] at htriangle
  change ‖S n w t‖ ≤ x^(7/8+ε)
  rw [Real.rpow_add hx]
  have hsave := mul_le_mul_of_nonneg_right hlog4 (Real.rpow_nonneg hx.le (7/8:ℝ))
  nlinarith only [htriangle,herr,hbound,hres, hsave, mul_nonneg (show 0≤L^4 by positivity) (Real.rpow_nonneg hx.le (7/8:ℝ))]


theorem outer_sup_bound :
    ∀ᶠ n : ℕ in atTop, ∀ t ∈ outer n, ‖Goldbach.ShiftWideArc.S n t‖ ≤ (n:ℝ)^(8/9:ℝ) := by
  simpa only [show (7/8:ℝ)+1/72 = 8/9 by norm_num] using vaughan_outer_bound (1/72) (by norm_num)

end
end Goldbach.OuterPrimeArc
end


section
/- Source: OuterWindowModel.lean -/
namespace Goldbach.OuterWindowModel
open GB6Geometry GB6Kernel Finset Filter

/-- Denominator of the arc containing the point, with no restriction outside the arcs. -/
def outer (Y Q H : ℕ) (t : ℝ) : Prop :=
  ∀ i ∈ indices Q, t ∈ window H Y i.1 i.2 → (Y : ℝ) ^ (1 / 4 : ℝ) ≤ i.1

theorem model_eq_on_window {Y Q H : ℕ} (hs : 2*H^2 < Y) (hQ : Q ≤ H) {t : ℝ}
    {i : Idx} (hi : i ∈ indices Q) (ht : t ∈ window H Y i.1 i.2) :
    model Q H Y ThreeQArith.mean t =
      ThreeQArith.mean i.1 i.2 * kernel Y (t - center i.1 i.2) := by
  classical
  rw [model_sigma, sum_eq_single_of_mem i hi, Set.indicator_of_mem ht]
  intro j hj hji
  apply Set.indicator_of_notMem
  intro hwin
  exact hji ((unique_window hs hQ t) ⟨hj,hwin⟩ ⟨hi,ht⟩)

theorem norm_kernel_le (Y : ℕ) (t : ℝ) : ‖kernel Y t‖ ≤ (Y : ℝ) + 1 := by
  unfold kernel
  refine (norm_sum_le _ _).trans ?_
  have hone (u : ℝ) : ‖phase u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  simp [hone]

theorem norm_outer (Y Q H : ℕ) (hs : 2*H^2 < Y) (hQ : Q ≤ H) (hQY : Q ≤ Y)
    {t : ℝ} (ht : outer Y Q H t) :
    ‖model Q H Y ThreeQArith.mean t‖ ≤ 4 * GB6Growth.logFactor Y * (Y : ℝ)^(3/4 : ℝ) := by
  classical
  have hy : 1 ≤ Y := by omega
  have hyp : 0 < (Y : ℝ) := by exact_mod_cast hy
  have hLF := GB6Growth.logFactor_nonneg Y
  by_cases h : ∃ i ∈ indices Q, t ∈ window H Y i.1 i.2
  · obtain ⟨i, hi, hwin⟩ := h
    obtain ⟨hq, ha⟩ := mem_sigma.mp hi
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hqy : i.1 ≤ Y := (mem_Icc.mp hq).2.trans hQY
    have hqr : 0 < (i.1 : ℝ) := by exact_mod_cast hqpos
    have hφ : 0 < (i.1.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hqpos
    have hlog : (Nat.log 2 i.1 : ℝ) ≤ GB6Growth.L Y := by
      unfold GB6Growth.L
      exact_mod_cast Nat.log_mono_right (b := 2) (show i.1 ≤ Y + 2 by omega)
    have hratio := ThreeQArith.Totient.ratio_le i.1 hqpos
    have hφinv : 1 / (i.1.totient : ℝ) ≤ (2 * GB6Growth.logFactor Y) / i.1 := by
      apply (le_div_iff₀ hqr).mpr
      rw [one_div_mul_eq_div]
      linarith [GB6Growth.L_le_logFactor Y, GB6Growth.L_one Y]
    have hlow := ht i hi hwin
    have hmul : (Y : ℝ)^(1/4 : ℝ) * (Y : ℝ)^(3/4 : ℝ) = (Y : ℝ) := by
      rw [← Real.rpow_add hyp]; norm_num
    have hdiv : ((Y : ℝ)+1) / (i.1 : ℝ) ≤ 2 * (Y : ℝ)^(3/4 : ℝ) := by
      apply (div_le_iff₀ hqr).mpr
      have hmon := mul_le_mul_of_nonneg_right hlow (Real.rpow_nonneg hyp.le (3/4 : ℝ))
      rw [hmul] at hmon
      have hy' : 1 ≤ (Y : ℝ) := by exact_mod_cast hy
      linarith only [hmon, hy']
    rw [model_eq_on_window hs hQ hi hwin, norm_mul]
    calc
      _ ≤ ((2 * GB6Growth.logFactor Y) / i.1) * ((Y : ℝ)+1) :=
        mul_le_mul ((ThreeQArith.norm_mean_le (mem_filter.mp ha).2).trans hφinv)
          (norm_kernel_le Y _) (norm_nonneg _) (by positivity)
      _ = (2*GB6Growth.logFactor Y)*(((Y:ℝ)+1)/i.1) := by ring
      _ ≤ (2*GB6Growth.logFactor Y)*(2*(Y:ℝ)^(3/4:ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  · have hz : ∀ i ∈ indices Q, t ∉ window H Y i.1 i.2 := fun i hi ht => h ⟨i,hi,ht⟩
    rw [model_sigma, sum_eq_zero fun i hi => Set.indicator_of_notMem (hz i hi) _, norm_zero]
    positivity

theorem eventual_norm_outer (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ Y : ℕ in atTop, ∀ t : ℝ, outer Y (GB6Growth.grid Y) (GB6Growth.height Y) t →
      ‖GB6Var.G (GB6Growth.grid Y) (GB6Growth.height Y) Y t‖ ≤ (Y : ℝ)^(3/4 + ε : ℝ) := by
  filter_upwards [GB6Growth.eventual_geometry, GB6Growth.polylog_le_power 4 (by norm_num) 1 ε hε] with Y hgeo hlog
  intro t ht
  obtain ⟨_, hQ, hQY, _, hs⟩ := hgeo
  have hy : 0 < (Y:ℝ) := by exact_mod_cast (show 0<Y by omega)
  calc
    _ ≤ 4 * GB6Growth.logFactor Y * (Y:ℝ)^(3/4 : ℝ) := norm_outer Y _ _ hs hQ hQY ht
    _ ≤ (Y:ℝ)^ε * (Y:ℝ)^(3/4 : ℝ) :=
      mul_le_mul_of_nonneg_right (by simpa using hlog) (by positivity)
    _ = _ := by rw [← Real.rpow_add hy]; congr 1; ring


/-- The bound on the same union of rational intervals used for the prime sum. -/
theorem model_on_large_denominator_arcs :
    ∀ᶠ Y : ℕ in atTop, ∀ t : ℝ, (∃ q a : ℕ, 1 ≤ q ∧ q ≤ ShiftWideArc.Q Y ∧ a ≤ q ∧
       a.Coprime q ∧ (Y:ℝ)^(1/4:ℝ) ≤ q ∧ |t-(a:ℝ)/q| ≤ (ShiftWideArc.H Y:ℝ)/((q:ℝ)*Y)) →
      ‖GB6Var.G (GB6Growth.grid Y) (GB6Growth.height Y) Y t‖ ≤ (Y : ℝ)^(8/9 : ℝ) := by
  filter_upwards [GB6Growth.eventual_geometry, eventual_norm_outer (5/36) (by norm_num)] with Y hgeo hbound
  intro t h
  obtain ⟨q,a,hq,hQ,ha,hc,hlarge,hwin⟩ := h
  have hg : GB6Growth.grid Y = ShiftWideArc.Q Y := GB6Growth.grid_eq_floor Y
  have hh : GB6Growth.height Y = ShiftWideArc.H Y := by simp only [GB6Growth.height,ShiftWideArc.H,hg]
  let j : Idx := ⟨q,a⟩
  have hj : j ∈ indices (GB6Growth.grid Y) := mem_sigma.mpr
    ⟨mem_Icc.mpr ⟨hq, hQ.trans_eq hg.symm⟩,mem_filter.mpr ⟨mem_range.mpr (show a < q+1 from Nat.lt_succ_of_le ha),hc⟩⟩
  have hjw : t ∈ window (GB6Growth.height Y) Y j.1 j.2 :=
    (mem_window Y q a t).mpr (by simpa only [center,width,hh] using hwin)
  have ht : outer Y (GB6Growth.grid Y) (GB6Growth.height Y) t := by
    intro i hi hiw
    have hsame : i = j := unique_window hgeo.2.2.2.2 hgeo.2.1 t ⟨hi,hiw⟩ ⟨hj,hjw⟩
    simpa only [hsame] using hlarge
  simpa only [show (3/4 + 5/36 : ℝ) = 8/9 by norm_num] using hbound t ht

end Goldbach.OuterWindowModel
end


section
/- Source: OuterArcFourthMoment.lean -/
open Finset MeasureTheory Filter
namespace Goldbach.OuterArcFourthMoment
noncomputable section
open scoped Classical
open GB6Growth

abbrev model (Y : ℕ) := GB6Var.G (grid Y) (height Y) Y
abbrev primes (Y : ℕ) := GB6Var.S Y

def energy (B : Set ℝ) (Y : ℕ) : ℝ :=
  ∫ t in (0:ℝ)..1, B.indicator (fun u => ‖(model Y u)^2 - (primes Y u)^2‖^2) t

theorem energy_as_product (B : Set ℝ) (Y : ℕ) : energy B Y =
    ∫ t in (0:ℝ)..1, B.indicator (fun u =>
      ‖model Y u - primes Y u‖^2 * ‖model Y u + primes Y u‖^2) t := by
  apply intervalIntegral.integral_congr
  intro t _
  by_cases h : t ∈ B
  · simp only [Set.indicator_of_mem h,sq_sub_sq,norm_mul,mul_pow]; ring
  · simp only [Set.indicator_of_notMem h]

theorem region_bound (B : Set ℝ) (hB : MeasurableSet B) (Y : ℕ)
    (U : ℝ) (hU : 0 ≤ U)
    (hM : ∀ t ∈ Set.Icc (0:ℝ) 1 ∩ B, ‖model Y t‖ ≤ U)
    (hS : ∀ t ∈ Set.Icc (0:ℝ) 1 ∩ B, ‖primes Y t‖ ≤ U)
    (hQM : grid Y ≤ Y) (hsep : 2*(height Y)^2 < Y) (hQH : grid Y ≤ height Y) :
    energy B Y ≤ 10*U^2*((Y:ℝ)+1)*(1+Real.log ((Y:ℝ)+2))^2 := by
  let F := model Y
  let G := primes Y
  let D := B.indicator (fun t => ‖F t^2 - G t^2‖^2)
  let J := fun t => 2*U^2*(‖F t‖^2 + ‖G t‖^2)
  have hF := GB6Var.G_memLp (grid Y) (height Y) Y
  have hG := GB6Var.S_memLp Y
  have aF := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have aG := (memLp_two_iff_integrable_sq_norm hG.aestronglyMeasurable).mp hG
  have haF : IntervalIntegrable (fun t => ‖F t‖^2) volume (0:ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr aF
  have haG : IntervalIntegrable (fun t => ‖G t‖^2) volume (0:ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr aG
  have hJ : IntervalIntegrable J volume (0:ℝ) 1 := (haF.add haG).const_mul _
  have hd : AEStronglyMeasurable D GB5Variance.unitMeasure :=
    (((hF.aestronglyMeasurable.pow 2).sub (hG.aestronglyMeasurable.pow 2)).norm.pow 2).indicator hB
  have hD0 (t : ℝ) : 0 ≤ D t := by
    by_cases h : t ∈ B
    · simpa only [D,Set.indicator_of_mem h] using sq_nonneg ‖F t^2-G t^2‖
    · simp only [D,Set.indicator_of_notMem h,le_refl]
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : D t ≤ J t := by
    by_cases h : t ∈ B
    · have ha : ‖F t‖ ≤ U := hM t ⟨ht,h⟩
      have hb : ‖G t‖ ≤ U := hS t ⟨ht,h⟩
      have hn : ‖F t^2 - G t^2‖ ≤ U*(‖F t‖ + ‖G t‖) := by
        refine (norm_sub_le ..).trans ?_
        rw [norm_pow,norm_pow,mul_add,sq,sq]
        exact add_le_add (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hn 2
      simp only [D, Set.indicator_of_mem h, J]
      nlinarith only [hsq,mul_nonneg (sq_nonneg U) (sq_nonneg (‖F t‖ - ‖G t‖))]
    · simp only [D,Set.indicator_of_notMem h,J]
      positivity
  have hDi : IntervalIntegrable D volume (0:ℝ) 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    apply hJ.1.mono' hd
    apply (ae_restrict_iff' measurableSet_Ioc).2
    apply ae_of_all
    intro t ht
    rw [Real.norm_of_nonneg (hD0 t)]
    exact hbound t ⟨ht.1.le,ht.2⟩
  have hi : energy B Y ≤ ∫ t in (0:ℝ)..1, J t :=
    intervalIntegral.integral_mono_on zero_le_one hDi hJ hbound
  have hsum := add_le_add (GB6Var.G_energy hQM hsep hQH) (GB6Var.S_energy Y)
  refine hi.trans ?_
  change (∫ t in (0:ℝ)..1, (2*U^2)*(‖F t‖^2 + ‖G t‖^2)) ≤ _
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add haF haG]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 2*U^2)).trans_eq (by ring)

def admissible (B : ℕ → Set ℝ) (Y : ℕ) : Prop :=
  MeasurableSet (B Y) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1 ∩ B Y, ‖model Y t‖ ≤ (Y:ℝ)^(8/9:ℝ)) ∧
    (∀ t ∈ Set.Icc (0:ℝ) 1 ∩ B Y, ‖primes Y t‖ ≤ (Y:ℝ)^(8/9:ℝ))

theorem cutoff_power (B : ℕ → Set ℝ) :
    ∀ᶠ Y : ℕ in atTop, admissible B Y →
      energy (B Y) Y ≤ 20*(Y:ℝ)^(25/9:ℝ)*(1+Real.log ((Y:ℝ)+2))^2 := by
  filter_upwards [eventual_geometry, eventually_ge_atTop (1:ℕ)] with Y hgeom hy hB
  obtain ⟨_,hQH,hQM,_,hsep⟩ := hgeom
  obtain ⟨hB,hM,hS⟩ := hB
  have he := region_bound _ hB Y _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hM hS hQM hsep hQH
  have hy' : (1:ℝ) ≤ Y := by exact_mod_cast hy
  have hYpos : 0 < (Y:ℝ) := by linarith
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hpow : ((Y:ℝ)^(8/9:ℝ))^2*(Y:ℝ) = (Y:ℝ)^(25/9:ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _), ← Real.rpow_add_one hYpos.ne']
    norm_num
  rw [← hpow]
  nlinarith [mul_nonneg (sq_nonneg ((Y:ℝ)^(8/9:ℝ))) (sub_nonneg.mpr hy')]

theorem sum_cutoff_bounds (f : ℕ → ℝ)
    (h : ∀ᶠ Y : ℕ in atTop, f Y ≤ 20*(Y:ℝ)^(25/9:ℝ)*(1+Real.log ((Y:ℝ)+2))^2) :
    ∃ N : ℕ, ∀ X ≥ N, (∑ Y ∈ Icc (X/4) (2*X), f Y) ≤
      (3*(2:ℝ)^(279/100:ℝ))*(X:ℝ)^(3+79/100:ℝ) := by
  have hp := polylog_le_power 20 (by norm_num) 2 (11/900) (by norm_num)
  have hy : ∀ᶠ Y : ℕ in atTop, f Y ≤ (Y:ℝ)^(279/100:ℝ) := by
    filter_upwards [h,hp,eventually_ge_atTop (1:ℕ)] with Y he hl hY
    have hpos : 0 < (Y:ℝ) := by exact_mod_cast (show 0<Y by omega)
    have hl0 : 0 ≤ 1+Real.log ((Y:ℝ)+2) := by
      have := Real.log_nonneg (show 1 ≤ (Y:ℝ)+2 by linarith)
      linarith
    have hlog := pow_le_pow_left₀ hl0 (log_le_logFactor Y) 2
    calc
      _ ≤ _ := he
      _ = (Y:ℝ)^(25/9:ℝ)*(20*(1+Real.log ((Y:ℝ)+2))^2) := by ring
      _ ≤ (Y:ℝ)^(25/9:ℝ)*(Y:ℝ)^(11/900:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (mul_le_mul_of_nonneg_left hlog (by norm_num)).trans hl
      _ = _ := by rw [← Real.rpow_add hpos]; norm_num
  obtain ⟨N,hN⟩ := eventually_atTop.mp hy
  refine ⟨max (4*N) 1,?_⟩
  intro X hx
  have hxpos : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hcount : ((Icc (X/4) (2*X)).card:ℝ) ≤ 3*(X:ℝ) := by
    exact_mod_cast (show (Icc (X/4) (2*X)).card ≤ 3*X by rw [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ _Y ∈ Icc (X/4) (2*X), (2*(X:ℝ))^(279/100:ℝ) := by
      apply sum_le_sum
      intro Y hY
      obtain ⟨hl,hh⟩ := mem_Icc.mp hY
      exact (hN Y (by omega)).trans (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast hh) (by norm_num))
    _ = ((Icc (X/4) (2*X)).card:ℝ)*(2*(X:ℝ))^(279/100:ℝ) := by simp
    _ ≤ (3*(X:ℝ))*(2*(X:ℝ))^(279/100:ℝ) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hxpos.le]
      conv_rhs => rw [show (3+79/100:ℝ)=279/100+1 by norm_num, Real.rpow_add_one hxpos.ne']
      ring

theorem dyadic_power (B : ℕ → Set ℝ) (hB : ∀ᶠ Y : ℕ in atTop, admissible B Y) :
    ∃ N : ℕ, ∀ X ≥ N, (∑ Y ∈ Icc (X/4) (2*X), energy (B Y) Y) ≤
      (3*(2:ℝ)^(279/100:ℝ))*(X:ℝ)^(3+79/100:ℝ) :=
  sum_cutoff_bounds _ (by filter_upwards [cutoff_power B,hB] with Y h hb using h hb)

end
end Goldbach.OuterArcFourthMoment
end


section
/- Source: OuterArcRemoval.lean -/
open Filter Finset MeasureTheory
namespace Goldbach.OuterArcRemoval
noncomputable section
open ShiftTimeEnergy ShiftWideArc

theorem outer_dyadic_bound :
    ∃ N : ℕ, ∀ X ≥ N, (∑ Y ∈ Icc (X/4) (2*X), OuterArcFourthMoment.energy (OuterPrimeArc.outer Y) Y) ≤
      (3*(2:ℝ)^(279/100:ℝ))*(X:ℝ)^(3+79/100:ℝ) := by
  apply OuterArcFourthMoment.dyadic_power
  filter_upwards [OuterPrimeArc.outer_sup_bound, OuterWindowModel.model_on_large_denominator_arcs] with Y hs hm
  exact ⟨OuterPrimeArc.outer_measurable Y,fun t ht => hm t ht.2,fun t ht => hs t ht.2⟩

def innerArc (Y : ℕ) := arcs Y \ OuterPrimeArc.outer Y

theorem energy_split (Y : ℕ) : timeEnergy Y = OuterArcFourthMoment.energy (innerArc Y) Y +
    OuterArcFourthMoment.energy (OuterPrimeArc.outer Y) Y := by
  classical
  let F := fun t => ‖(M Y t)^2 - (P Y t)^2‖^2
  have h := (model_sq_mem Y).sub (prime_sq_mem Y)
  have hF : Integrable F GB5Variance.unitMeasure :=
    (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h
  have hi (B : Set ℝ) (hB : MeasurableSet B) : IntervalIntegrable (B.indicator F) volume (0:ℝ) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hF.indicator hB)
  have hB := OuterPrimeArc.outer_measurable Y
  have hA : MeasurableSet (arcs Y) := EffectiveArcEndpoint.frontierMeasurable _ _ _
  have hsub := OuterPrimeArc.outer_subset Y
  have hI : innerArc Y ⊆ arcs Y := Set.sdiff_subset
  have eqr (B : Set ℝ) (hb : B ⊆ arcs Y) :
      OuterArcFourthMoment.energy B Y = ∫ t in (0:ℝ)..1, B.indicator F t := by
    apply intervalIntegral.integral_congr
    intro t _
    by_cases ht : t ∈ B
    · simp only [Set.indicator_of_mem ht,F,P,Set.indicator_of_mem (hb ht)]
      rfl
    · simp only [Set.indicator_of_notMem ht]
  rw [eqr _ hI,eqr _ hsub,← intervalIntegral.integral_add (hi (innerArc Y) (hA.diff hB)) (hi _ hB)]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ho : t ∈ OuterPrimeArc.outer Y
  · simp [innerArc,ho,F]
  · by_cases ha : t ∈ arcs Y
    · simp [innerArc,ho,ha,F]
    · simp [innerArc,ho,ha,F,P,model_off_arcs Y ha]

/-- The high-denominator part is discharged unconditionally. The remaining
square-error budget is localized to denominators below Y^(1/4). -/
theorem frozen_of_inner_energy {α K : ℝ} (ha : 0 ≤ α) (ha' : α < 4/5) (hK : 0<K)
    (hE : ∃ N : ℕ, ∀ X ≥ N, (∑ Y ∈ Icc (X/4) (2*X), OuterArcFourthMoment.energy (innerArc Y) Y)
      ≤ K*(X:ℝ)^(3+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (missed X).card^5 ≤ X^4 := by
  obtain ⟨NI,hI⟩ := hE
  obtain ⟨NO,hO⟩ := outer_dyadic_bound
  let β := max α (79/100)
  let C := 3*(2:ℝ)^(279/100:ℝ)
  have hc : 0<C := by dsimp [C]; positivity
  apply binary_shift_exception_union_of_model_energy (α:=β) (K:=K+C)
    (ha.trans (le_max_left ..)) (max_lt ha' (by norm_num)) (by positivity)
  refine ⟨max 1 (max NI NO),?_⟩
  intro X hx
  have hx1 : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  apply (multiscale_bessel X).trans
  simp_rw [energy_split]
  rw [sum_add_distrib,add_mul]
  apply add_le_add
  · exact (hI X (by omega)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx1 (add_le_add (le_refl (3:ℝ)) (le_max_left ..))) hK.le)
  · exact (hO X (by omega)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx1 (add_le_add (le_refl (3:ℝ)) (le_max_right ..))) hc.le)

end
end Goldbach.OuterArcRemoval
end


section
/- Source: InnerArcCriterion.lean -/
open Finset MeasureTheory
namespace Goldbach.InnerArcCriterion
open Goldbach.ShiftWideArc
noncomputable section
open scoped Classical

def inner (B : ℕ → Set ℝ) (Y : ℕ) := arcs Y \ B Y

def outerMoment (B : ℕ → Set ℝ) (Y : ℕ) :=
  ∫ t in (0:ℝ)..1, (B Y).indicator (fun u => ‖S Y u‖^4) t

/-- Additivity of the actual prime Fourier coefficient for the disjoint
inner and outer parts of the wide arcs. -/
theorem coefficient_split (B : ℕ → Set ℝ) (Y m : ℕ) (hB : MeasurableSet (B Y))
    (hsub : B Y ⊆ arcs Y) :
    coefficient (arcs Y) Y m = coefficient (inner B Y) Y m + coefficient (B Y) Y m := by
  have ha : MeasurableSet (arcs Y) := EffectiveArcEndpoint.frontierMeasurable _ _ _
  have hc : Continuous (integrand Y m) := by unfold integrand S phase; fun_prop
  have hi (D : Set ℝ) (hD : MeasurableSet D) :
      IntervalIntegrable (D.indicator (integrand Y m)) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    exact ((hc.intervalIntegrable (μ := volume) 0 1).1).indicator hD
  unfold coefficient inner
  rw [← intervalIntegral.integral_add (hi _ (ha.diff hB)) (hi _ hB)]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ B Y
  · simp [ht,hsub ht]
  · by_cases ha' : t ∈ arcs Y <;> simp [ht,ha']

/-- Bessel's inequality for the actual masked prime square. -/
theorem outer_bessel (B : ℕ → Set ℝ) (Y : ℕ) (hB : MeasurableSet (B Y)) (s : Finset ℕ) :
    ∑ m ∈ s, ‖coefficient (B Y) Y m‖^2 ≤ outerMoment B Y := by
  let f := (B Y).indicator (fun t => (S Y t)^2)
  have hc : Continuous (fun t => (S Y t)^2) := by unfold S phase; fun_prop
  have hm : MemLp f 2 GB5Variance.unitMeasure := by
    apply MemLp.indicator hB.nullMeasurableSet
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    exact ((hc.norm.pow 2).intervalIntegrable (μ := volume) 0 1).1
  have he (m : ℕ) : coefficient (B Y) Y m = GB5Variance.modeCoeff f m := by
    apply intervalIntegral.integral_congr
    intro t _
    by_cases ht : t ∈ B Y <;> simp [f,ht,integrand]
    exact Or.inl rfl
  simp_rw [he]
  refine (GB5Variance.finite_bessel s _ hm).trans_eq ?_
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ B Y <;> simp [f,ht,norm_pow]
  ring

theorem multiscale_outer_bessel (B : ℕ → Set ℝ) (hB : ∀ Y, MeasurableSet (B Y))
    (hsub : ∀ Y, B Y ⊆ arcs Y) (X : ℕ) :
    WideArcCriterion.energy (fun Y m => coefficient (inner B Y) Y m) X ≤
      ∑ Y ∈ Icc (X/4) (2*X), outerMoment B Y := by
  have hdiff (Y m : ℕ) : coefficient (inner B Y) Y m - coefficient (arcs Y) Y m =
      -coefficient (B Y) Y m := by rw [coefficient_split B Y m (hB Y) (hsub Y)]; abel
  simp only [WideArcCriterion.energy,hdiff,norm_neg]
  calc
    _ ≤ ∑ m ∈ Icc (X/2) (2*X), ∑ Y ∈ Icc (X/4) (2*X), ‖coefficient (B Y) Y m‖^2 := by
      apply sum_le_sum
      intro m hm
      apply sum_le_sum_of_subset_of_nonneg _ (by intros; positivity)
      intro Y hY
      obtain ⟨_,_⟩ := mem_Icc.mp hm
      obtain ⟨_,_⟩ := mem_Icc.mp hY
      exact mem_Icc.mpr ⟨by omega,by omega⟩
    _ = ∑ Y ∈ Icc (X/4) (2*X), ∑ m ∈ Icc (X/2) (2*X), ‖coefficient (B Y) Y m‖^2 := sum_comm
    _ ≤ _ := sum_le_sum fun Y _ => outer_bessel B Y (hB Y) _

/-- A linear lower bound on the actual inner coefficient and an outer fourth
moment of exponent less than 3+4/5 imply the frozen exceptional-set bound. -/
theorem frozen_of_inner_floor (B : ℕ → Set ℝ) (hB : ∀ Y, MeasurableSet (B Y))
    (hsub : ∀ Y, B Y ⊆ arcs Y)
    (hfloor : ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      3*(Y:ℝ)/32 ≤ (coefficient (inner B Y) Y m).re)
    {α K : ℝ} (ha : 0 ≤ α) (ha' : α < 4/5) (hK : 0<K)
    (hmoment : ∃ N : ℕ, ∀ X ≥ N,
      (∑ Y ∈ Icc (X/4) (2*X), outerMoment B Y) ≤ K*(X:ℝ)^(3+α)) :
    ∃ N : ℕ, ∀ X ≥ N, (missed X).card^5 ≤ X^4 := by
  obtain ⟨NF,hF⟩ := hfloor
  obtain ⟨NE,hE⟩ := hmoment
  apply WideArcCriterion.frozen_of_energy (M:=fun Y m => coefficient (inner B Y) Y m)
    _ ha ha' hK ⟨NE,fun X hx => (multiscale_outer_bessel B hB hsub X).trans (hE X hx)⟩
  have hg := ((tendsto_rpow_atTop (by norm_num : 0 < (1/24:ℝ))).comp
    (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 32
  apply Filter.eventually_atTop.mp
  filter_upwards [hg,Filter.eventually_ge_atTop (max 1 NF)] with Y hY hy
  intro m h1 h2 he z hz
  have hp : (0:ℝ) < Y := by exact_mod_cast (show 0<Y by omega)
  have hs : (Y:ℝ)^(23/24:ℝ)*(Y:ℝ)^(1/24:ℝ) = Y := by
    rw [← Real.rpow_add hp]; norm_num
  have hn : 32*‖z‖ ≤ Y := by
    rw [← hs,mul_comm (32:ℝ)]
    exact mul_le_mul hz hY (by norm_num) (by positivity)
  have hlin := hF Y (by omega) m h1 h2 he
  have hn' := Complex.re_le_norm (coefficient (inner B Y) Y m-z)
  rw [Complex.sub_re] at hn'
  linarith [Complex.re_le_norm z]

end
end Goldbach.InnerArcCriterion
end


section
/- Source: ActualOuterMoment.lean -/
open Finset MeasureTheory Filter
namespace Goldbach.InnerArcCriterion
open Goldbach.ShiftWideArc
noncomputable section
open scoped Classical

theorem actual_fourth_moment (B : ℕ → Set ℝ) (Y : ℕ) (hb : MeasurableSet (B Y))
    {U : ℝ} (hu : ∀ t ∈ B Y, ‖S Y t‖ ≤ U) :
    outerMoment B Y ≤ U^2 * (((Y:ℝ)+1)*(1+Real.log ((Y:ℝ)+2))^2) := by
  have hc : Continuous (S Y) := by unfold S phase; fun_prop
  have hi : IntervalIntegrable ((B Y).indicator (fun t => ‖S Y t‖^4)) volume (0:ℝ) 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    exact (((hc.norm.pow 4).intervalIntegrable (μ:=volume) 0 1).1).indicator hb
  calc
    _ ≤ ∫ t in (0:ℝ)..1, U^2 * ‖S Y t‖^2 := by
      apply intervalIntegral.integral_mono_on zero_le_one hi
        (((hc.norm.pow 2).intervalIntegrable (μ:=volume) 0 1).const_mul _)
      intro t _
      by_cases ht : t ∈ B Y
      · rw [Set.indicator_of_mem ht,show (4:ℕ)=2+2 by decide,pow_add]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hu t ht) 2) (sq_nonneg _)
      · rw [Set.indicator_of_notMem ht]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    _ ≤ _ := by
      rw [intervalIntegral.integral_const_mul]
      exact mul_le_mul_of_nonneg_left (GB6Var.S_energy Y) (sq_nonneg _)

theorem dyadic_actual_fourth (B : ℕ → Set ℝ) (hb : ∀ Y, MeasurableSet (B Y))
    (hu : ∀ᶠ Y : ℕ in atTop, ∀ t ∈ B Y, ‖S Y t‖ ≤ (Y:ℝ)^(8/9:ℝ)) :
    ∃ N : ℕ, ∀ X ≥ N, (∑ Y ∈ Icc (X/4) (2*X), outerMoment B Y) ≤
      (3*(2:ℝ)^(279/100:ℝ))*(X:ℝ)^(3+79/100:ℝ) := by
  have hp := GB6Growth.polylog_le_power 2 (by norm_num) 2 (11/900) (by norm_num)
  have hy : ∀ᶠ Y : ℕ in atTop, outerMoment B Y ≤ (Y:ℝ)^(279/100:ℝ) := by
    filter_upwards [hu,hp,eventually_ge_atTop (1:ℕ)] with Y hU hlog hY
    have hpos : 0 < (Y:ℝ) := by exact_mod_cast (show 0<Y by omega)
    have hscale : (1:ℝ) ≤ Y := by exact_mod_cast hY
    have hl : 0 ≤ 1+Real.log ((Y:ℝ)+2) := by
      have := Real.log_nonneg (show (1:ℝ) ≤ Y+2 by linarith)
      linarith
    have hlog' := pow_le_pow_left₀ hl (GB6Growth.log_le_logFactor Y) 2
    have hpow : ((Y:ℝ)^(8/9:ℝ))^2*(Y:ℝ) = (Y:ℝ)^(25/9:ℝ) := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _),← Real.rpow_add_one hpos.ne']; norm_num
    calc
      _ ≤ _ := actual_fourth_moment B Y (hb Y) hU
      _ ≤ (Y:ℝ)^(25/9:ℝ)*(2*(1+Real.log ((Y:ℝ)+2))^2) := by
        rw [← hpow]
        nlinarith only [mul_nonneg (sq_nonneg ((Y:ℝ)^(8/9:ℝ)))
          (mul_nonneg (sub_nonneg.mpr hscale) (sq_nonneg (1+Real.log ((Y:ℝ)+2))))]
      _ ≤ (Y:ℝ)^(25/9:ℝ)*(Y:ℝ)^(11/900:ℝ) := by
        exact mul_le_mul_of_nonneg_left
          ((mul_le_mul_of_nonneg_left hlog' (by norm_num : 0 ≤ (2:ℝ))).trans hlog) (by positivity)
      _ = _ := by rw [← Real.rpow_add hpos]; norm_num
  obtain ⟨N,hN⟩ := eventually_atTop.mp hy
  refine ⟨max (4*N) 1,?_⟩
  intro X hx
  have hxpos : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hcount : ((Icc (X/4) (2*X)).card:ℝ) ≤ 3*(X:ℝ) := by
    exact_mod_cast (show (Icc (X/4) (2*X)).card ≤ 3*X by rw [Nat.card_Icc]; omega)
  calc
    _ ≤ ∑ _Y ∈ Icc (X/4) (2*X), (2*(X:ℝ))^(279/100:ℝ) := by
      apply sum_le_sum
      intro Y hY
      obtain ⟨hl,hh⟩ := mem_Icc.mp hY
      exact (hN Y (by omega)).trans (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (by exact_mod_cast hh) (by norm_num))
    _ = ((Icc (X/4) (2*X)).card:ℝ)*(2*(X:ℝ))^(279/100:ℝ) := by simp
    _ ≤ (3*(X:ℝ))*(2*(X:ℝ))^(279/100:ℝ) := mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hxpos.le]
      conv_rhs => rw [show (3+79/100:ℝ)=279/100+1 by norm_num,Real.rpow_add_one hxpos.ne']
      ring

end
end Goldbach.InnerArcCriterion
end


section
/- Source: ActualInnerArcFloor.lean -/
open Goldbach.ShiftWideArc
namespace Goldbach.InnerArcCriterion

/-- The only analytic input in this sufficient condition is a positive floor
for the actual prime coefficient on the inner part of the wide arcs. -/
theorem frozen_of_actual_inner_floor
    (hfloor : ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      3*(Y:ℝ)/32 ≤ (coefficient (inner OuterPrimeArc.outer Y) Y m).re) :
    ∃ N : ℕ, ∀ X ≥ N, (missed X).card^5 ≤ X^4 :=
  frozen_of_inner_floor OuterPrimeArc.outer OuterPrimeArc.outer_measurable
    OuterPrimeArc.outer_subset hfloor (by norm_num : 0 ≤ (79/100:ℝ)) (by norm_num) (by positivity)
    (dyadic_actual_fourth _ OuterPrimeArc.outer_measurable OuterPrimeArc.outer_sup_bound)

end Goldbach.InnerArcCriterion
end


section
/- Source: InnerArcGeometry.lean -/
open Finset GB6Geometry GB6Growth Filter
namespace Goldbach.InnerArcGeometry
open Goldbach.ShiftWideArc Goldbach.ReflectedArcModel

/-- The same widths as in the official wide arcs, cut at a smaller denominator. -/
def windowsTo (r Y : ℕ) : Set ℝ := { t | ∃ q a : ℕ, 1≤q ∧ q≤r ∧ a≤q ∧ a.Coprime q ∧
  |t-(a:ℝ)/q| ≤ (H Y:ℝ)/((q:ℝ)*Y) }

private theorem in_index {Y q a : ℕ} {t : ℝ}
    (h1 : 1≤q) (h2 : q≤Q Y) (ha : a≤q) (hc : a.Coprime q)
    (hw : |t-(a:ℝ)/q| ≤ (H Y:ℝ)/((q:ℝ)*Y)) :
    (⟨q,a⟩ : Idx) ∈ indices (grid Y) ∧ t ∈ window (height Y) Y q a := by
  have hg : grid Y = Q Y := grid_eq_floor Y
  have hh : height Y = H Y := by simp only [GB6Growth.height,H,hg]
  refine ⟨mem_sigma.mpr ⟨mem_Icc.mpr ⟨h1,h2.trans_eq hg.symm⟩,
    mem_filter.mpr ⟨mem_range.mpr (show a<q+1 by omega),hc⟩⟩,?_⟩
  exact (mem_window Y q a t).mpr (by simpa only [center,width,hh] using hw)

theorem eventual_inner_eq :
    ∀ᶠ Y : ℕ in atTop, ShiftWideArc.arcs Y \ OuterPrimeArc.outer Y = windowsTo (innerCutoff Y) Y := by
  filter_upwards [GB6Growth.eventual_geometry] with Y hY
  have hg : grid Y = Q Y := grid_eq_floor Y
  ext t
  constructor
  · rintro ⟨⟨q,a,h1,h2,ha,hc,hw⟩,hout⟩
    have hl : (q:ℝ) < (Y:ℝ)^(1/4:ℝ) := by
      by_contra! hb
      exact hout ⟨q,a,h1,h2,ha,hc,hb,hw⟩
    exact ⟨q,a,h1,(mem_innerCutoff h1).mpr ⟨h2.trans_eq hg.symm,hl⟩,ha,hc,hw⟩
  · rintro ⟨q,a,h1,h2,ha,hc,hw⟩
    obtain ⟨hgrid,hl⟩ := (mem_innerCutoff h1).mp h2
    have h2' := hgrid.trans_eq hg
    refine ⟨⟨q,a,h1,h2',ha,hc,hw⟩,?_⟩
    rintro ⟨r,b,hr1,hr2,hb,hcop,hlarge,hh⟩
    have hq := in_index h1 h2' ha hc hw
    have hr := in_index hr1 hr2 hb hcop hh
    have heq : (⟨q,a⟩ : Idx) = ⟨r,b⟩ := unique_window hY.2.2.2.2 hY.2.1 t hq hr
    have hqr : q=r := congrArg Sigma.fst heq
    subst r
    exact (not_lt_of_ge hlarge) hl

end Goldbach.InnerArcGeometry
end


section
/- Source: NarrowCoreComparison.lean -/
open Finset Filter MeasureTheory GB6Geometry GB6Kernel
namespace Goldbach.NarrowCore
noncomputable section
open scoped Classical
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc.Polylog

/-- A core with independent denominator and width parameters. -/
def core (r H Y : ℕ) : Set ℝ := {t | ∃ i ∈ indices r, t ∈ window H Y i.1 i.2}

def coreModel (r H Y m : ℕ) : ℂ := ∫ t in (0:ℝ)..1,
  (model r H Y ThreeQArith.mean t)^2 * phase (-(m:ℝ)*t)

/-- Sum on clipped windows first so that the two end arcs have the correct
length. The comparison with the full absolute-error integrals then preserves
the bound uniformly over all interior frequencies. -/
theorem coefficient_error {r H Y m : ℕ} (hsep : 2*H^2 < Y) (hr : r ≤ H) :
    ‖ShiftWideArc.coefficient (core r H Y) Y m - coreModel r H Y m‖ ≤
      totalArcError H Y m := by
  let F := ShiftWideArc.integrand Y m
  let U (i : Idx) (t : ℝ) :=
    (ThreeQArith.mean i.1 i.2 * kernel Y (t-center i.1 i.2))^2 * phase (-(m:ℝ)*t)
  let E (i : Idx) := (window H Y i.1 i.2).indicator (fun t => F t - U i t)
  have hcF : Continuous F := by unfold F ShiftWideArc.integrand ShiftWideArc.S ShiftWideArc.phase; fun_prop
  have hcU (i : Idx) : Continuous (U i) := by unfold U kernel phase; fun_prop
  have hi (i : Idx) : IntervalIntegrable (E i) volume 0 1 := by
    have hc := ((hcF.sub (hcU i)).intervalIntegrable (μ:=volume) 0 1)
    exact ⟨hc.1.indicator measurableSet_Icc,hc.2.indicator measurableSet_Icc⟩
  have hmodelI : IntervalIntegrable
      (fun t => (model r H Y ThreeQArith.mean t)^2 * phase (-(m:ℝ)*t)) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
    have hg := GB6Var.G_memLp r H Y
    have hs := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
    have ha : AEStronglyMeasurable (fun t => (model r H Y ThreeQArith.mean t)^2 * phase (-(m:ℝ)*t))
        GB5Variance.unitMeasure := (hg.aestronglyMeasurable.pow 2).mul (by unfold phase; fun_prop)
    apply (integrable_norm_iff ha).mp
    simpa only [norm_mul,norm_pow,phase,Complex.norm_exp_ofReal_mul_I,mul_one] using hs
  have hb : MeasurableSet (core r H Y) := by
    have h : core r H Y = ⋃ i ∈ (indices r : Finset Idx), window H Y i.1 i.2 := by ext t; simp [core]
    rw [h]; exact MeasurableSet.biUnion (indices r).countable_toSet (fun _ _ => measurableSet_Icc)
  have hfI : IntervalIntegrable ((core r H Y).indicator F) volume 0 1 :=
    ⟨(hcF.intervalIntegrable 0 1).1.indicator hb,(hcF.intervalIntegrable 0 1).2.indicator hb⟩
  have hpoint (t : ℝ) : (core r H Y).indicator F t -
      (model r H Y ThreeQArith.mean t)^2 * phase (-(m:ℝ)*t) = ∑ i ∈ indices r, E i t := by
    rw [model_sigma]
    by_cases ht : t ∈ core r H Y
    · obtain ⟨i,hi',hit⟩ := ht
      have ho (j : Idx) (hj : j ∈ indices r) (hne : j ≠ i) : t ∉ window H Y j.1 j.2 :=
        fun hm => hne (unique_window hsep hr t ⟨hj,hm⟩ ⟨hi',hit⟩)
      rw [sum_eq_single_of_mem i hi' (fun j hj hn => Set.indicator_of_notMem (ho j hj hn) _),
        sum_eq_single_of_mem i hi' (fun j hj hn => Set.indicator_of_notMem (ho j hj hn) _)]
      simp only [Set.indicator_of_mem (show t ∈ core r H Y from ⟨i,hi',hit⟩),Set.indicator_of_mem hit,U]
    · have ho (i : Idx) (hi : i ∈ indices r) : t ∉ window H Y i.1 i.2 := fun h => ht ⟨i,hi,h⟩
      rw [sum_eq_zero (fun i hi => Set.indicator_of_notMem (ho i hi) _),
        sum_eq_zero (fun i hi => Set.indicator_of_notMem (ho i hi) _),Set.indicator_of_notMem ht]
      simp
  have hbnd (i : Idx) (hi' : i ∈ indices r) :
      ‖∫ t in (0:ℝ)..1, E i t‖ ≤
        ∫ β in -(GB6Geometry.width H Y i.1)..GB6Geometry.width H Y i.1, modelError Y i.1 i.2 m β := by
    obtain ⟨hiq,hia⟩ := mem_sigma.mp hi'
    have hq := (mem_Icc.mp hiq).1
    have ha : i.2 ≤ i.1 := Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp hia).1)
    obtain ⟨hl,ho,hr'⟩ := clipped_order (Q:=H) (n:=Y) hq ha
    rw [show (∫ t in (0:ℝ)..1, E i t) = _ from indicator_clipped hq ha _]
    apply (intervalIntegral.norm_integral_le_integral_norm ho).trans
    have hh (β : ℝ) : ‖F (center i.1 i.2 + β) - U i (center i.1 i.2 + β)‖ = modelError Y i.1 i.2 m β := by
      simp only [U,add_sub_cancel_left]
      rfl
    simp_rw [← hh]
    exact intervalIntegral.integral_mono_interval hl ho hr' (Eventually.of_forall fun _ => norm_nonneg _)
      ((((hcF.sub (hcU i)).norm).comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
  let V (q a : ℕ) := ∫ β in -(GB6Geometry.width H Y q)..GB6Geometry.width H Y q, modelError Y q a m β
  have hV (q a : ℕ) : 0 ≤ V q a := intervalIntegral.integral_nonneg
    (by linarith [GB6Geometry.width_nonneg (Q:=H) Y q]) (fun _ _ => norm_nonneg _)
  change ‖(∫ t in (0:ℝ)..1, (core r H Y).indicator F t) - _‖ ≤ _
  unfold coreModel
  rw [← intervalIntegral.integral_sub hfI hmodelI]
  simp_rw [hpoint]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  calc
    _ ≤ ∑ i ∈ indices r, V i.1 i.2 := (norm_sum_le ..).trans (sum_le_sum hbnd)
    _ = ∑ q ∈ Icc 1 r, ∑ a ∈ numerators q, V q a := by rw [indices,sum_sigma]
    _ ≤ ∑ q ∈ Icc 1 r, ∑ a ∈ range (q+1), V q a := by
      exact sum_le_sum fun q _ => sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun a _ _ => hV q a)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hr) (fun q _ _ => sum_nonneg fun a _ => hV q a)

/-- Uniformity includes every choice of a truncated family q≤r≤H. -/
theorem uniform_core_comparison (B S : ℕ) (hB : 0 < B) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ Y : ℕ in atTop, ∀ r m : ℕ, r ≤ cutoff B Y → 2*(cutoff B Y)^2 < Y →
      (Real.log Y)^S * ‖ShiftWideArc.coefficient (core r (cutoff B Y) Y) Y m -
        coreModel r (cutoff B Y) Y m‖ < ε*Y := by
  filter_upwards [eventually_totalArcError_lt B S hB hε] with Y hy
  intro r m hr hs
  exact (mul_le_mul_of_nonneg_left (coefficient_error hs hr) (pow_nonneg (Real.log_natCast_nonneg Y) _)).trans_lt (hy m)

/-- Positive actual prime contribution on denominators through log₂(Y+2),
with widths log₂(Y+2)^3/(qY), uniformly in the even reflected range. -/
theorem positive_polylog_core :
    ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
    (7:ℝ)*Y/64 ≤ (ShiftWideArc.coefficient
      (core (Nat.log 2 (Y+2)) (cutoff 3 Y) Y) Y m).re := by
  filter_upwards [uniform_core_comparison 3 0 (by decide) (show (0:ℝ)<1/64 by norm_num),
    BulkCircle.eventually_grid 0, eventually_ge_atTop (2^32:ℕ)] with Y hcomp hgrid hY
  intro m hlo hhi he
  let r := Nat.log 2 (Y+2)
  have hr : 32 ≤ r := Nat.le_log_of_pow_le (by decide) (by omega)
  have hpos : 0<r := by omega
  have hgeom : 1000000000*r^72 ≤ Y := by
    simpa only [BulkCircle.root,GoldbachMajorArc.Polylog.cutoff, zero_add,← pow_mul] using hgrid
  have h6 : r^6 ≤ r^72 := pow_le_pow_right₀ (by omega : 1≤r) (by decide)
  have hs : 2*(cutoff 3 Y)^2 < Y := by
    change 2*(r^3)^2 < Y
    rw [←pow_mul, show (3*2:ℕ)=6 by decide]
    have h6pos := pow_pos hpos 6
    omega
  have hrH : r ≤ cutoff 3 Y := by
    change r ≤ r^3
    simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1≤r) (by decide : 1≤3)
  have hrR : (32:ℝ)≤r := by exact_mod_cast hr
  have hrr : (0:ℝ)<r := by positivity
  have hbudget : (r:ℝ)*(1+(Nat.log 2 r:ℝ))/(2*(cutoff 3 Y:ℝ)) ≤ 1/32 := by
    change (r:ℝ)*(1+(Nat.log 2 r:ℝ))/(2*((r^3:ℕ):ℝ)) ≤ 1/32
    push_cast
    apply (div_le_iff₀ (by positivity)).mpr
    have hl : (Nat.log 2 r:ℝ) ≤ r := by exact_mod_cast Nat.log_le_self 2 r
    have h1 : 1+(Nat.log 2 r:ℝ) ≤ 2*(r:ℝ) := by linarith
    have hh := mul_le_mul_of_nonneg_left h1 hrr.le
    nlinarith only [hh,mul_nonneg (sq_nonneg (r:ℝ)) (sub_nonneg.mpr hrR)]
  have hm : (Y:ℝ)/8 ≤ (coreModel r (cutoff 3 Y) Y m).re :=
    ReflectedArcModel.reflected_model_floor hs hrH (by omega) hlo hhi he hbudget
  have hd := hcomp r m hrH hs
  simp only [pow_zero,one_mul] at hd
  have ha := Complex.abs_re_le_norm
    (ShiftWideArc.coefficient (core r (cutoff 3 Y) Y) Y m - coreModel r (cutoff 3 Y) Y m)
  rw [Complex.sub_re] at ha
  linarith [(abs_le.mp (ha.trans hd.le)).1]

end
end Goldbach.NarrowCore
end


section
/- Source: SignedIntermediateArcs.lean -/
open Filter Finset MeasureTheory GB6Growth GB6Geometry
namespace Goldbach.SignedIntermediateArcs
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open ShiftWideArc InnerArcCriterion ReflectedArcModel
noncomputable section
open scoped Classical

def polylogCore (Y : ℕ) := NarrowCore.core (Nat.log 2 (Y+2)) (GoldbachMajorArc.Polylog.cutoff 3 Y) Y

def remaining (Y : ℕ) := inner OuterPrimeArc.outer Y \ polylogCore Y

theorem core_measurable (Y : ℕ) : MeasurableSet (polylogCore Y) := by
  let r := Nat.log 2 (Y+2)
  let H₀ := GoldbachMajorArc.Polylog.cutoff 3 Y
  have h : polylogCore Y = ⋃ i ∈ indices r, window H₀ Y i.1 i.2 := by ext; simp [polylogCore,NarrowCore.core,r,H₀]
  rw [h]
  exact (indices r).measurableSet_biUnion fun _ _ => measurableSet_Icc

theorem eventual_core_subset :
    ∀ᶠ Y : ℕ in atTop, polylogCore Y ⊆ inner OuterPrimeArc.outer Y := by
  filter_upwards [InnerArcGeometry.eventual_inner_eq,
    polylog_le_power 2 (by norm_num) 1 (1/4) (by norm_num),eventually_ge_atTop (2:ℕ)] with Y heq hh hY
  change polylogCore Y ⊆ ShiftWideArc.arcs Y \ OuterPrimeArc.outer Y
  rw [heq]
  let r := Nat.log 2 (Y+2)
  have hr : 1 ≤ r := Nat.le_log_of_pow_le (by decide) (by omega)
  have hL : (r:ℝ) ≤ logFactor Y := L_le_logFactor Y
  have hpos : 0 < (r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have hlt : (r:ℝ) < (Y:ℝ)^(1/4:ℝ) := by rw [pow_one] at hh; linarith
  have hrg : r ≤ grid Y := by
    rw [grid_eq_floor]
    apply Nat.le_floor
    exact hlt.le.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤Y by omega)) (by norm_num))
  have hsmall : GoldbachMajorArc.Polylog.cutoff 3 Y ≤ H Y := by
    change r^3 ≤ 256*(Q Y)*r^2
    have hrg' : r ≤ Q Y := hrg.trans_eq (grid_eq_floor Y)
    have h := Nat.mul_le_mul_left 256 hrg'
    calc
      _ = r*r^2 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  rintro t ⟨i,hi,hiw⟩
  obtain ⟨hq,ha⟩ := mem_sigma.mp hi
  obtain ⟨hl,hu⟩ := mem_Icc.mp hq
  obtain ⟨ha',hc⟩ := mem_filter.mp ha
  refine ⟨i.1,i.2,hl,(mem_innerCutoff hl).mpr ⟨hu.trans hrg, lt_of_le_of_lt (by exact_mod_cast hu) hlt⟩,?_,hc,?_⟩
  · have := mem_range.mp ha'; omega
  · exact ((mem_window Y i.1 i.2 t).mp hiw).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hsmall) (by positivity))

private theorem remaining_split {Y : ℕ} (hsub : polylogCore Y ⊆ inner OuterPrimeArc.outer Y) (m : ℕ) :
    coefficient (inner OuterPrimeArc.outer Y) Y m = coefficient (remaining Y) Y m + coefficient (polylogCore Y) Y m := by
  have ha : MeasurableSet (ShiftWideArc.arcs Y) := EffectiveArcEndpoint.frontierMeasurable _ _ _
  have hi : MeasurableSet (inner OuterPrimeArc.outer Y) := ha.diff (OuterPrimeArc.outer_measurable Y)
  have hc : Continuous (integrand Y m) := by unfold integrand S ShiftWideArc.phase; fun_prop
  have hm (D : Set ℝ) (hD : MeasurableSet D) : IntervalIntegrable (D.indicator (integrand Y m)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr ((hc.intervalIntegrable (μ:=volume) 0 1).1.indicator hD)
  unfold coefficient
  rw [← intervalIntegral.integral_add (hm (remaining Y) (hi.diff (core_measurable Y))) (hm _ (core_measurable Y))]
  apply intervalIntegral.integral_congr
  intro t _
  by_cases ht : t ∈ polylogCore Y
  · simp [remaining,ht,hsub ht]
  · by_cases hi' : t ∈ inner OuterPrimeArc.outer Y <;> simp [remaining,ht,hi']

theorem frozen_of_intermediate_floor
    (h : ∃ N : ℕ, ∀ Y ≥ N, ∀ m : ℕ, Y ≤ m → 2*m ≤ 3*Y → Even m →
      -(Y:ℝ)/64 ≤ (coefficient (remaining Y) Y m).re) :
    ∃ N : ℕ, ∀ X ≥ N, (missed X).card^5 ≤ X^4 := by
  obtain ⟨N,hN⟩ := h
  apply frozen_of_actual_inner_floor
  apply eventually_atTop.mp
  filter_upwards [eventual_core_subset,NarrowCore.positive_polylog_core,eventually_ge_atTop N] with Y hs hc hy
  intro m h1 h2 he
  rw [remaining_split hs m, Complex.add_re]
  have hf : 7*(Y:ℝ)/64 ≤ (coefficient (polylogCore Y) Y m).re := hc m h1 h2 he
  linarith [hN Y hy m h1 h2 he]

end
end Goldbach.SignedIntermediateArcs
end

#print axioms Goldbach.OuterPrimeArc.outer_sup_bound
#print axioms Goldbach.OuterArcRemoval.outer_dyadic_bound
#print axioms Goldbach.NarrowCore.positive_polylog_core
#print axioms Goldbach.SignedIntermediateArcs.frozen_of_intermediate_floor
