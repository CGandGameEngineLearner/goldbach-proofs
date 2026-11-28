import Mathlib
import Conjectures.Goldbach.PartnerPrincipalRowPhase

section HeightProductionSection1
open Filter Finset Asymptotics
open scoped Topology
namespace AmplitudeTail

theorem sum_range_real_nat (N : ℕ) :
    (∑ k ∈ range N, (k:ℝ)) = (N:ℝ)*((N:ℝ)-1)/2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring

theorem shifted_ratio_one :
    Tendsto (fun N : ℕ => ((N:ℝ)-1)/(N:ℝ)) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => (1:ℝ) - 1/(N:ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1:ℝ))).sub tendsto_one_div_atTop_nhds_zero_nat
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hn : (N:ℝ) ≠ 0 := by positivity
  field_simp

theorem sum_range_real_nat_div_sq :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, (k:ℝ))/(N:ℝ)^2) atTop (𝓝 (1/2:ℝ)) := by
  apply (shifted_ratio_one.div_const 2).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hn : (N:ℝ) ≠ 0 := by positivity
  rw [sum_range_real_nat]
  field_simp

theorem sum_range_real_nat_tendsto :
    Tendsto (fun N : ℕ => ∑ k ∈ range N, (k:ℝ)) atTop atTop := by
  have h : Tendsto (fun N : ℕ => (N:ℝ)/2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  apply tendsto_atTop_mono' atTop ?_ h
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
  have hn : (2:ℝ) ≤ N := by exact_mod_cast hN
  rw [sum_range_real_nat]
  nlinarith

theorem abel_sum_identity (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ range N, (n:ℝ)*f n) =
      ((N:ℝ)-1)*(∑ n ∈ range N, f n) -
        ∑ k ∈ range N, ∑ n ∈ range k, f n := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, Nat.cast_succ,
      show (∑ n ∈ range (N+1), f n) = (∑ n ∈ range N, f n)+f N by rw [sum_range_succ],
      show (∑ k ∈ range (N+1), ∑ n ∈ range k, f n) =
        (∑ k ∈ range N, ∑ n ∈ range k, f n) + (∑ n ∈ range N, f n) by rw [sum_range_succ]]
    ring

theorem weighted_count_limit {f : ℕ → ℝ} {c : ℝ}
    (hl : Tendsto (fun N : ℕ => (∑ n ∈ range N, f n)/(N:ℝ)) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (n:ℝ)*f n)/(N:ℝ)^2) atTop (𝓝 (c/2)) := by
  let R (N : ℕ) : ℝ := ∑ n ∈ range N, f n
  let e (N : ℕ) : ℝ := R N - c*(N:ℝ)
  have he : e =o[atTop] (fun N : ℕ => (N:ℝ)) := by
    apply isLittleO_of_tendsto'
    · filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN h
      exact False.elim ((by positivity : (N:ℝ)≠0) h)
    · have hh := hl.sub_const c
      rw [sub_self] at hh
      apply hh.congr'
      filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
      have hn : (N:ℝ) ≠ 0 := by positivity
      change R N / (N:ℝ) - c = e N / (N:ℝ)
      unfold e
      field_simp
  have hes := he.sum_range (by intro N; positivity) sum_range_real_nat_tendsto
  have hnon : ∀ᶠ N : ℕ in atTop, (∑ k ∈ range N, (k:ℝ)) ≠ 0 :=
    (sum_range_real_nat_tendsto.eventually_ge_atTop 1).mono (by intro N h; linarith)
  have hratio := (isLittleO_iff_tendsto' (hnon.mono (fun _ h h' => (h h').elim))).mp hes
  have herror := (hratio.mul sum_range_real_nat_div_sq)
  rw [zero_mul] at herror
  have herror' : Tendsto (fun N : ℕ => (∑ k ∈ range N, e k)/(N:ℝ)^2) atTop (𝓝 0) := by
    apply herror.congr'
    filter_upwards [hnon,eventually_gt_atTop (0:ℕ)] with N hne hN
    have hn : (N:ℝ) ≠ 0 := by positivity
    field_simp
  have hR : Tendsto (fun N : ℕ => (∑ k ∈ range N, R k)/(N:ℝ)^2) atTop (𝓝 (c/2)) := by
    have hh := herror'.add (sum_range_real_nat_div_sq.const_mul c)
    rw [zero_add, mul_one_div] at hh
    apply hh.congr
    intro N
    change (∑ k ∈ range N, e k)/(N:ℝ)^2 + c*((∑ k ∈ range N, (k:ℝ))/(N:ℝ)^2) = _
    simp only [e,sum_sub_distrib, ← mul_sum, sub_div, mul_div_assoc]
    ring
  have hf := (shifted_ratio_one.mul hl).sub hR
  rw [one_mul, show c-c/2=c/2 by ring] at hf
  apply hf.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hn : (N:ℝ) ≠ 0 := by positivity
  rw [abel_sum_identity]
  change (((N:ℝ)-1)/(N:ℝ))*(R N/(N:ℝ)) - (∑ k ∈ range N, R k)/(N:ℝ)^2 = _
  field_simp
  ring
end AmplitudeTail
end HeightProductionSection1

section HeightProductionSection2
namespace AmplitudeTail
open Filter Finset
open scoped Topology

theorem final_from_linear_count {B : Type*} (valid : ℕ → B → Prop)
    (a : ℕ → ℝ) (O : ℝ)
    (hCount : ∀ Y > 0, ∃ F : Finset B, (∀ b, b ∈ F ↔ valid Y b) ∧
      (F.card:ℝ) = ∑ n ∈ range Y, (n:ℝ) * a n)
    (hLean : Tendsto (fun Y : ℕ => (∑ n ∈ range Y, a n)/(Y:ℝ)) atTop (𝓝 O⁻¹)) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T, ∃ F : Finset B,
      (∀ b, b ∈ F ↔ valid Y b) ∧ |(F.card:ℝ)/(Y:ℝ)^2 - 1/(2*O)| ≤ ε := by
  have hLim := weighted_count_limit hLean
  have hconst : O⁻¹/2 = 1/(2*O) := by rw [div_eq_mul_inv, mul_comm, ← mul_inv, one_div]
  rw [hconst] at hLim
  intro ε hε
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hLim.eventually (Metric.ball_mem_nhds _ hε))
  refine ⟨max T 1, fun Y hY => ?_⟩
  obtain ⟨F,hF,hCard⟩ := hCount Y ((le_max_right _ _).trans hY)
  refine ⟨F,hF,?_⟩
  rw [hCard]
  have h := hT Y ((le_max_left _ _).trans hY)
  exact le_of_lt (by simpa only [Real.dist_eq] using h)

end AmplitudeTail
end HeightProductionSection2

section HeightProductionSection3
open Filter Set
open scoped Topology
namespace AmplitudeTail

noncomputable def regularZeta : ℂ → ℂ :=
  Function.update (fun z : ℂ => (z-1) * riemannZeta z) 1 1

theorem regularZeta_one : regularZeta 1 = 1 := by simp [regularZeta]

theorem regularZeta_of_ne {z : ℂ} (hz : z ≠ 1) :
    regularZeta z = (z-1)*riemannZeta z := by simp [regularZeta, hz]

theorem regularZeta_differentiable : Differentiable ℂ regularZeta := by
  have h := (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
    (f := regularZeta) (s := (Set.univ : Set ℂ)) (c := 1) univ_mem).mp ?_
  · exact differentiableOn_univ.mp h
  · constructor
    · intro z hz
      have hne : z ≠ 1 := hz.2
      apply DifferentiableAt.differentiableWithinAt
      apply ((differentiableAt_id.sub_const (1:ℂ)).mul (differentiableAt_riemannZeta hne)).congr_of_eventuallyEq
      filter_upwards [isOpen_ne.mem_nhds hne] with w hw
      exact regularZeta_of_ne hw
    · simpa only [regularZeta, continuousAt_update_same] using riemannZeta_residue_one

theorem subtract_pole_with_multiplier (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {z : ℂ | (3:ℝ)/4 < z.re}) :
    ∃ G : ℂ → ℂ, ContinuousOn G {z : ℂ | 1 ≤ z.re} ∧
      EqOn G (fun z => riemannZeta z * H z - H 1/(z-1)) {z : ℂ | 1 < z.re} := by
  let F := fun z => H z * regularZeta z
  have hH' : DifferentiableOn ℂ F {z : ℂ | (3:ℝ)/4 < z.re} :=
    hH.mul regularZeta_differentiable.differentiableOn
  have hN : {z : ℂ | (3:ℝ)/4 < z.re} ∈ 𝓝 (1:ℂ) := by
    apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    norm_num
  refine ⟨dslope F 1, ((Complex.differentiableOn_dslope hN).mpr hH').continuousOn.mono
    (fun z hz => (show (3:ℝ)/4 < 1 by norm_num).trans_le hz), ?_⟩
  intro z hz
  have hz' : z ≠ 1 := by
    intro eq; subst z
    have : (1:ℝ) < (1:ℂ).re := hz
    norm_num at this
  rw [dslope_of_ne _ hz', slope, smul_eq_mul, vsub_eq_sub]
  simp only [F, regularZeta_of_ne hz', regularZeta_one, mul_one]
  field_simp [sub_ne_zero.mpr hz']
  <;> ring

end AmplitudeTail
end HeightProductionSection3

section HeightProductionSection4
open Finset
open scoped BigOperators
namespace AmplitudeTail

def height (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, (p-2)

theorem height_pos {n : ℕ} (hc : n.Coprime 2) : 0 < height n := by
  unfold height
  apply Finset.prod_pos
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hn2 : p ≠ 2 := by
    intro he
    subst p
    have := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) (dvd_refl 2)
    rw [hc.gcd_eq_one] at this
    norm_num at this
  have := hpr.two_le
  omega

theorem conductor_le_three_height_sq {n : ℕ} (hs : Squarefree n) (hc : n.Coprime 2) :
    n ≤ 3 * height n ^ 2 := by
  classical
  let T := n.primeFactors.erase 3
  have hprod : ∏ p ∈ T, p ≤ ∏ p ∈ T, (p-2)^2 := by
    apply Finset.prod_le_prod
    · intro p hp
      obtain ⟨hp3, hp⟩ := Finset.mem_erase.mp hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hp2 : p ≠ 2 := by
        intro hh
        subst p
        have := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) (dvd_refl 2)
        rw [hc.gcd_eq_one] at this
        norm_num at this
      have hp4 : p ≠ 4 := by
        intro e; subst p
        exact (by decide : ¬Nat.Prime 4) hpr
      have h5 : 5 ≤ p := by have := hpr.two_le; omega
      have eq : p-2+2=p := by omega
      have hq : 3 ≤ p-2 := by omega
      nlinarith [Nat.mul_le_mul_left (p-2) hq]
  have hh : height n = ∏ p ∈ T, (p-2) := by
    unfold height
    by_cases h3 : 3 ∈ n.primeFactors
    · have e := Finset.prod_erase_mul (s := n.primeFactors) (f := fun p : ℕ => p-2) h3
      simpa [T] using e.symm
    · simp [T, Finset.erase_eq_of_notMem h3]
  have hleft : n ≤ 3 * ∏ p ∈ T, p := by
    rw [← Nat.prod_primeFactors_of_squarefree hs]
    by_cases h3 : 3 ∈ n.primeFactors
    · have e := Finset.prod_erase_mul (s := n.primeFactors) (f := fun p : ℕ => p) h3
      simpa [T, mul_comm] using e.ge
    · simp only [T, Finset.erase_eq_of_notMem h3]
      omega
  rw [hh, ← Finset.prod_pow]
  exact hleft.trans (Nat.mul_le_mul_left 3 hprod)

end AmplitudeTail
end HeightProductionSection4

section HeightProductionSection5
open Finset
open scoped BigOperators
namespace AmplitudeTail

noncomputable def ampCount (n : ℕ) : ℕ := by
  classical
  exact ((Finset.range (3*n^2+1)).filter
    (fun s => Squarefree s ∧ s.Coprime 2 ∧ height s = n)).card

noncomputable def heightCut (X N : ℕ) : Finset ℕ := by
  classical
  exact (range X).filter (fun s => Squarefree s ∧ s.Coprime 2 ∧ height s < N)

theorem mem_heightCut {X N s : ℕ} :
    s ∈ heightCut X N ↔ s < X ∧ Squarefree s ∧ s.Coprime 2 ∧ height s < N := by
  classical
  simp [heightCut]

theorem ampCount_sum_eq_heightCut (N : ℕ) :
    (∑ n ∈ range N, ampCount n) = (heightCut (3*N^2+1) N).card := by
  classical
  let M := 3*N^2+1
  let U := heightCut M N
  have eq (n : ℕ) (hn : n ∈ range N) : ampCount n = (U.filter (fun s => height s = n)).card := by
    unfold ampCount
    apply congrArg Finset.card
    ext s
    simp only [mem_filter, mem_range, U, mem_heightCut]
    constructor
    · rintro ⟨hs,hf,hc,rfl⟩
      have hN : height s < N := mem_range.mp hn
      have hh : (height s)^2 ≤ N^2 := Nat.pow_le_pow_left (Nat.le_of_lt hN) 2
      exact ⟨⟨by omega, hf,hc,hN⟩,rfl⟩
    · rintro ⟨⟨_,hf,hc,_⟩,rfl⟩
      exact ⟨Nat.lt_succ_of_le (conductor_le_three_height_sq hf hc),hf,hc,rfl⟩
  rw [Finset.sum_congr rfl eq]
  exact Finset.sum_card_fiberwise_eq_card_filter (s := U) (t := range N) (g := height) |>.trans (by
    rw [filter_true_of_mem]
    intro s hs
    exact mem_range.mpr (mem_heightCut.mp hs).2.2.2)

end AmplitudeTail
end HeightProductionSection5

section HeightProductionSection6
open Finset DirichletCharacter
open scoped BigOperators Classical

namespace AmplitudeTailCRT


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


end AmplitudeTailCRT


open Finset DirichletCharacter
open scoped BigOperators Classical

namespace AmplitudeTailCRT
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


end CRT
end AmplitudeTailCRT


open Finset DirichletCharacter
open scoped BigOperators Classical

namespace AmplitudeTailCRT
namespace CRT

variable {a b : ℕ} (h : a.Coprime b) [NeZero a] [NeZero b] [NeZero (a*b)]
include h

theorem glue_conductor (C : DirichletCharacter ℂ a) (D : DirichletCharacter ℂ b) :
    (glue h C D).conductor = C.conductor * D.conductor := by
  unfold glue
  rw [conductor_mul_of_coprime, conductor_changeLevel, conductor_changeLevel]
  rw [conductor_changeLevel, conductor_changeLevel]
  exact h.of_dvd C.conductor_dvd_level D.conductor_dvd_level


end CRT
end AmplitudeTailCRT


open Finset DirichletCharacter
open scoped BigOperators Classical

namespace AmplitudeTail

noncomputable def primitiveSet (s : ℕ) : Finset (DirichletCharacter ℂ s) :=
  Finset.univ.filter (fun χ => χ.IsPrimitive)

theorem mem_primitiveSet {s : ℕ} (χ : DirichletCharacter ℂ s) :
    χ ∈ primitiveSet s ↔ χ.IsPrimitive := by simp [primitiveSet]

noncomputable def primitiveCount (s : ℕ) : ℕ := (primitiveSet s).card

theorem primitiveCount_one : primitiveCount 1 = 1 := by
  have H (χ : DirichletCharacter ℂ 1) : χ.IsPrimitive := by
    rw [Subsingleton.elim χ (1 : DirichletCharacter ℂ 1)]
    exact isPrimitive_one_level_one
  rw [primitiveCount, primitiveSet, Finset.filter_true_of_mem (fun χ _ => H χ), Finset.card_univ]
  exact Fintype.card_unique

theorem primitiveCount_prime {p : ℕ} (hp : p.Prime) : primitiveCount p = p-2 := by
  let _ : NeZero p := ⟨hp.ne_zero⟩
  have HE : primitiveSet p = Finset.univ.erase (1 : DirichletCharacter ℂ p) := by
    ext χ
    simp only [mem_primitiveSet, mem_erase, mem_univ, and_true]
    constructor
    · intro H E
      subst χ
      exact hp.ne_one (H.symm.trans conductor_one)
    · intro hn
      rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with h | h
      · exact False.elim (hn (eq_one_iff_conductor_eq_one.mpr h))
      · exact h
  rw [primitiveCount, HE, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card, card_eq_totient_of_hasEnoughRootsOfUnity, Nat.totient_prime hp]
  omega

theorem primitiveCount_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (h : a.Coprime b) :
    primitiveCount (a*b) = primitiveCount a * primitiveCount b := by
  let _ : NeZero a := ⟨ha⟩
  let _ : NeZero b := ⟨hb⟩
  let _ : NeZero (a*b) := ⟨mul_ne_zero ha hb⟩
  let E := AmplitudeTailCRT.CRT.chEquiv h
  have H (x : DirichletCharacter ℂ a × DirichletCharacter ℂ b) :
      (E.symm x).IsPrimitive ↔ x.1.IsPrimitive ∧ x.2.IsPrimitive := by
    change (AmplitudeTailCRT.CRT.glue h x.1 x.2).conductor = a*b ↔
      x.1.conductor = a ∧ x.2.conductor = b
    rw [AmplitudeTailCRT.CRT.glue_conductor]
    exact AmplitudeTailCRT.coprime_conductor_mul_match h x.1.conductor_dvd_level
      x.2.conductor_dvd_level (dvd_refl _) (dvd_refl _)
  have he : (primitiveSet (a*b)).map E.toEmbedding = primitiveSet a ×ˢ primitiveSet b := by
    ext x
    rw [Finset.mem_product, mem_primitiveSet, mem_primitiveSet, ← H]
    constructor
    · intro hx
      obtain ⟨y,hy,hxy⟩ := Finset.mem_map.mp hx
      have hxy' : y = E.symm x := E.eq_symm_apply.mpr hxy
      simpa only [← hxy'] using (mem_primitiveSet y).mp hy
    · intro hx
      exact Finset.mem_map.mpr ⟨E.symm x, (mem_primitiveSet _).mpr hx, E.apply_symm_apply x⟩
  rw [primitiveCount, ← Finset.card_map E.toEmbedding, he, Finset.card_product]
  rfl

theorem primitiveCount_squarefree : ∀ s : ℕ, Squarefree s → primitiveCount s = height s := by
  apply Nat.recOnPrimePow
  · intro hs
    exact False.elim (hs.ne_zero rfl)
  · intro _
    simp [height,primitiveCount_one]
  · intro s p k hp hps hk IH hs
    have hsP := hs.of_mul_left
    have hk1 : k=1 := by
      have H := hsP.natFactorization_le_one p
      simp [hp.factorization_pow] at H
      omega
    subst k
    simp only [pow_one] at hs ⊢
    have hsq := hs.of_mul_right
    rw [primitiveCount_mul hp.ne_zero hsq.ne_zero (hp.coprime_iff_not_dvd.mpr hps),
      primitiveCount_prime hp, IH hsq]
    unfold height
    rw [Nat.primeFactors_mul hp.ne_zero hsq.ne_zero, hp.primeFactors, Finset.singleton_union,
      Finset.prod_insert (fun mem => hps (Nat.dvd_of_mem_primeFactors mem))]

end AmplitudeTail


open Finset DirichletCharacter
open scoped BigOperators Classical

namespace AmplitudeTail

def AtTwoPhase
    (P : {s : ℕ} → DirichletCharacter ℂ s → ℂ) (O : ℂ) : Prop :=
  ∀ (s : ℕ) [NeZero s] (β : DirichletCharacter ℂ s), β.IsPrimitive →
    P β = if Squarefree s ∧ s.Coprime 2 then
      O * ((-1 : ℂ)^s.primeFactors.card) * β (2:ZMod s) /
        (∏ p ∈ s.primeFactors, ((p : ℂ)-2)) else 0

theorem norm_phase_of_good (P : {s : ℕ} → DirichletCharacter ℂ s → ℂ)
    (O : ℂ) (hPhase : AtTwoPhase P O)
    {s : ℕ} [NeZero s] (β : DirichletCharacter ℂ s) (hβ : β.IsPrimitive)
    (hs : Squarefree s) (hc : s.Coprime 2) :
    ‖P β‖ = ‖O‖ / (height s : ℝ) := by
  have hden : (∏ p ∈ s.primeFactors, ((p : ℂ)-2)) = (height s : ℂ) := by
    unfold height
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl (fun p hp => (Nat.cast_sub
      (Nat.prime_of_mem_primeFactors hp).two_le).symm)
  have u : IsUnit (2 : ZMod s) :=
    (ZMod.isUnit_iff_coprime 2 s).mpr hc.symm
  have hn : ‖β (2 : ZMod s)‖ = 1 := β.unit_norm_eq_one u.unit
  have phase := hPhase s β hβ
  change P β = _ at phase
  rw [phase, ite_eq_left ⟨hs,hc⟩, hden, norm_div, norm_mul, norm_mul, norm_pow,
    norm_neg, norm_one, one_pow, hn, mul_one, mul_one, Complex.norm_natCast]

theorem threshold_iff (P : {s : ℕ} → DirichletCharacter ℂ s → ℂ)
    (O : ℂ) (hO : 0 < ‖O‖) (hPhase : AtTwoPhase P O)
    {s : ℕ} [NeZero s] (β : DirichletCharacter ℂ s) (hβ : β.IsPrimitive) (Y : ℕ) :
    ‖O‖ < (Y:ℝ)*‖P β‖ ↔ Squarefree s ∧ s.Coprime 2 ∧ height s < Y := by
  by_cases hgood : Squarefree s ∧ s.Coprime 2
  · have hpos : (0:ℝ) < height s := by exact_mod_cast height_pos hgood.2
    rw [norm_phase_of_good P O hPhase β hβ hgood.1 hgood.2, ← mul_div_assoc, lt_div_iff₀ hpos,
      mul_comm ‖O‖]
    constructor
    · intro H
      refine ⟨hgood.1,hgood.2,?_⟩
      exact_mod_cast (lt_of_mul_lt_mul_right H hO.le)
    · intro H
      exact mul_lt_mul_of_pos_right (by exact_mod_cast H.2.2) hO
  · have E : ¬ (Squarefree s ∧ s.Coprime 2 ∧ height s < Y) :=
      fun h => hgood ⟨h.1,h.2.1⟩
    have phase := hPhase s β hβ
    change P β = _ at phase
    rw [phase, ite_eq_right hgood,norm_zero,mul_zero]
    exact iff_of_false hO.not_gt E

def conductorSet (Y : ℕ) : Finset ℕ :=
  (Finset.range (3*Y^2+1)).filter (fun s => Squarefree s ∧ s.Coprime 2 ∧ height s < Y)

theorem mem_conductorSet (Y s : ℕ) :
    s ∈ conductorSet Y ↔ Squarefree s ∧ s.Coprime 2 ∧ height s < Y := by
  classical
  simp only [conductorSet, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro hg
    have hcut := conductor_le_three_height_sq hg.1 hg.2.1
    have e := Nat.pow_le_pow_left hg.2.2.le 2
    exact ⟨Nat.lt_succ_of_le (hcut.trans (Nat.mul_le_mul_left 3 e)),hg⟩

noncomputable def tailFamily (Y : ℕ) : Finset (Σ s : ℕ, DirichletCharacter ℂ s) :=
  (conductorSet Y).sigma primitiveSet

theorem tailFamily_card (Y : ℕ) :
    (tailFamily Y).card = ∑ s ∈ conductorSet Y, height s := by
  rw [tailFamily, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro s hs
  exact primitiveCount_squarefree s (mem_conductorSet Y s |>.mp hs).1

theorem tailFamily_exact (P : {s : ℕ} → DirichletCharacter ℂ s → ℂ)
    (O : ℂ) (hO : 0 < ‖O‖) (hPhase : AtTwoPhase P O) (Y : ℕ) :
    (∀ b : Σ s : ℕ, DirichletCharacter ℂ s,
      b ∈ tailFamily Y ↔ (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ ‖O‖ < (Y:ℝ)*‖P b.2‖) ∧
    (tailFamily Y).card = ∑ s ∈ conductorSet Y, height s := by
  refine ⟨?_,tailFamily_card Y⟩
  intro b
  obtain ⟨s,β⟩ := b
  simp only [tailFamily, Finset.mem_sigma, mem_conductorSet, mem_primitiveSet]
  constructor
  · rintro ⟨hs,hβ⟩
    let _ : NeZero s := ⟨hs.1.ne_zero⟩
    exact ⟨⟨hs.1.ne_zero,hβ⟩,(threshold_iff P O hO hPhase β hβ Y).mpr hs⟩
  · rintro ⟨⟨hs,hβ⟩,hT⟩
    let _ : NeZero s := ⟨hs⟩
    exact ⟨(threshold_iff P O hO hPhase β hβ Y).mp hT,hβ⟩

end AmplitudeTail


open Finset DirichletCharacter
open scoped BigOperators Classical

namespace AmplitudeTail

theorem card_of_height_fiber {Y n : ℕ} (hn : n < Y) :
    ((conductorSet Y).filter (fun s => height s = n)).card = ampCount n := by
  unfold ampCount
  congr 1
  ext s
  simp only [Finset.mem_filter, mem_conductorSet, Finset.mem_range]
  constructor
  · rintro ⟨⟨hs,hc,_⟩,rfl⟩
    exact ⟨Nat.lt_succ_of_le (conductor_le_three_height_sq hs hc), hs, hc, rfl⟩
  · rintro ⟨_,hs,hc,E⟩
    exact ⟨⟨hs,hc,E.symm ▸ hn⟩,E⟩

theorem tailFamily_card_grouped (Y : ℕ) :
    ((tailFamily Y).card:ℝ) = ∑ n ∈ Finset.range Y, (n:ℝ) * (ampCount n:ℝ) := by
  rw [tailFamily_card, Nat.cast_sum]
  have h (s : ℕ) (hs : s ∈ conductorSet Y) : height s ∈ Finset.range Y :=
    Finset.mem_range.mpr (mem_conductorSet Y s |>.mp hs).2.2
  rw [← Finset.sum_fiberwise_of_maps_to' h (fun n : ℕ => (n:ℝ))]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_const, card_of_height_fiber (Finset.mem_range.mp hn), nsmul_eq_mul, mul_comm]

theorem tailCount_reindexed (P : {s : ℕ} → DirichletCharacter ℂ s → ℂ)
    (O : ℂ) (hO : 0 < ‖O‖) (hPhase : AtTwoPhase P O) (Y : ℕ) :
    ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
      (∀ b, b ∈ F ↔ (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ ‖O‖ < (Y:ℝ)*‖P b.2‖) ∧
      (F.card:ℝ) = ∑ n ∈ Finset.range Y, (n:ℝ) * (ampCount n:ℝ) :=
  ⟨tailFamily Y,(tailFamily_exact P O hO hPhase Y).1,tailFamily_card_grouped Y⟩

end AmplitudeTail
end HeightProductionSection6

section HeightProductionSection7
open Filter Set Finset
open scoped Topology
namespace AmplitudeTail

theorem amplitude_linear_of_euler {a : ℕ → ℝ} {C A : ℝ} (H : ℂ → ℂ)
    (hPos : 0 ≤ a)
    (hBound : ∀ Y : ℕ, ∑ i ∈ range Y, a i ≤ C * Y)
    (hH : DifferentiableOn ℂ H {z : ℂ | (3:ℝ)/4 < z.re})
    (hAtOne : H 1 = (A : ℂ))
    (hEuler : Set.EqOn (LSeries (fun n => (a n:ℂ))) (fun z => riemannZeta z * H z)
      {z : ℂ | 1 < z.re}) :
    Tendsto (fun Y : ℕ => (∑ n ∈ range Y, a n)/(Y:ℝ)) atTop (𝓝 A) := by
  obtain ⟨G, hContinuous, hEq⟩ := subtract_pole_with_multiplier H hH
  apply WienerIkehara.tendsto_sum_range_div hBound hContinuous ?_ hPos
  intro z hz
  have h := hEq hz
  change G z = riemannZeta z * H z - H 1 / (z-1) at h
  change G z = LSeries (fun n => (a n:ℂ)) z - (A:ℂ) / (z-1)
  rw [h, hEuler hz, hAtOne]

end AmplitudeTail
end HeightProductionSection7

section HeightProductionSection8
open Finset Filter Set
open scoped Topology
namespace AmplitudeTail

theorem full_of_euler_data
    (P : {s : ℕ} → DirichletCharacter ℂ s → ℂ)
    (O : ℂ) (hO : 0 < ‖O‖) (hPhase : AtTwoPhase P O)
    (C : ℝ) (hBound : ∀ Y : ℕ, ∑ n ∈ range Y, (ampCount n:ℝ) ≤ C * Y)
    (H : ℂ → ℂ) (hH : DifferentiableOn ℂ H {z : ℂ | (3:ℝ)/4 < z.re})
    (hAtOne : H 1 = ((‖O‖⁻¹ : ℝ) : ℂ))
    (hEuler : Set.EqOn (LSeries (fun n => (ampCount n : ℂ)))
      (fun z => riemannZeta z * H z) {z : ℂ | 1 < z.re}) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T,
      ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
        (∀ b, b ∈ F ↔ (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ ‖O‖ < (Y:ℝ)*‖P b.2‖) ∧
        |(F.card:ℝ)/(Y:ℝ)^2 - 1/(2*‖O‖)| ≤ ε := by
  have hEuler' : Set.EqOn (LSeries (fun n => ((ampCount n : ℝ) : ℂ)))
      (fun z => riemannZeta z * H z) {z : ℂ | 1 < z.re} := by
    simpa only [Complex.ofReal_natCast] using hEuler
  exact final_from_linear_count
    (fun Y (b : Σ s : ℕ, DirichletCharacter ℂ s) =>
      (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ ‖O‖ < (Y:ℝ)*‖P b.2‖)
    (fun n => (ampCount n:ℝ)) ‖O‖ (fun Y _ => tailCount_reindexed P O hO hPhase Y)
    (amplitude_linear_of_euler H (fun n => Nat.cast_nonneg _) hBound hH hAtOne hEuler')

end AmplitudeTail
end HeightProductionSection8

section HeightProductionSection9
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
end HeightProductionSection9

section HeightProductionSection10
open Finset ArithmeticFunction
open scoped BigOperators

namespace AmplitudeTail

noncomputable def divisorWeight : ArithmeticFunction ℝ := by
  classical
  exact ⟨fun n => if Squarefree n then ∏ p ∈ n.primeFactors, 24/(p:ℝ) else 0, by simp⟩

theorem divisorWeight_nonneg (n : ℕ) : 0 ≤ divisorWeight n := by
  classical
  change 0 ≤ if Squarefree n then ∏ p ∈ n.primeFactors, 24/(p:ℝ) else 0
  split_ifs
  · exact Finset.prod_nonneg (fun _ _ => by positivity)
  · exact le_rfl

theorem divisorWeight_mult : divisorWeight.IsMultiplicative := by
  classical
  refine ⟨by simp [divisorWeight], fun {m n} h => ?_⟩
  change (if Squarefree (m*n) then ∏ p ∈ (m*n).primeFactors, 24/(p:ℝ) else 0) =
    (if Squarefree m then ∏ p ∈ m.primeFactors, 24/(p:ℝ) else 0) *
      (if Squarefree n then ∏ p ∈ n.primeFactors, 24/(p:ℝ) else 0)
  simp only [Nat.squarefree_mul h]
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n <;> simp only [hm,hn,true_and,false_and,and_false,ite_true,ite_false,zero_mul,mul_zero]
  rw [Nat.primeFactors_mul hm.ne_zero hn.ne_zero, ← Finset.prod_union h.disjoint_primeFactors]

theorem divisorWeight_at_prime {p : ℕ} (hp : p.Prime) :
    divisorWeight p = 24/(p:ℝ) := by
  classical
  simp [divisorWeight, hp.squarefree, hp.primeFactors]

theorem divisorWeight_at_gt_one {p k : ℕ} (hp : p.Prime) (hk : 1 < k) :
    divisorWeight (p^k) = 0 := by
  classical
  change (if Squarefree (p^k) then _ else _) = _
  have hn := (Nat.squarefree_pow_iff hp.ne_one (by omega : k ≠ 0))
  simp [hn, show k ≠ 1 by omega]

noncomputable def dividedWeight (n : ℕ) : ℝ := divisorWeight n / (n:ℝ)

theorem dividedWeight_nonneg (n : ℕ) : 0 ≤ dividedWeight n :=
  div_nonneg (divisorWeight_nonneg n) (Nat.cast_nonneg n)

theorem dividedWeight_summable : Summable dividedWeight := by
  refine SignedHeight.summable_nonneg_of_prime_power_rows dividedWeight
    (fun n => 24/(n:ℝ)^2) dividedWeight_nonneg (by simp [dividedWeight])
    (by simp [dividedWeight,divisorWeight]) ?_ (fun _ => by positivity) ?_ ?_ ?_
  · intro m n c
    rw [dividedWeight,dividedWeight,dividedWeight, divisorWeight_mult.2 c, Nat.cast_mul, mul_div_mul_comm]
  · have H := (Real.summable_nat_rpow.mpr (by norm_num : (-2:ℝ) < -1)).mul_left 24
    simpa only [div_eq_mul_inv, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two] using H
  · intro p hp
    apply summable_of_ne_finset_zero (s := range 2)
    intro k hk
    rw [dividedWeight, divisorWeight_at_gt_one hp (by simp only [mem_range, not_lt] at hk; omega), zero_div]
  · intro p hp
    rw [tsum_eq_sum (s := range 2)]
    · simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one]
      have hp0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      simp [dividedWeight,divisorWeight_at_prime hp,divisorWeight_mult.1,pow_two,div_div]
    · intro k hk
      rw [dividedWeight, divisorWeight_at_gt_one hp (by simp only [mem_range, not_lt] at hk; omega), zero_div]

private theorem prime_ratio_sq {x : ℝ} (hx : 3 ≤ x) : (x/(x-2))^2 ≤ 1 + 24/x := by
  have h1 : 0 < x-2 := by linarith
  have h2 : 0 < x := by linarith
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos h1)).2
  rw [add_mul, one_mul, div_mul_eq_mul_div]
  have H : (x^2-(x-2)^2) * x ≤ 24*(x-2)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ x-3 by linarith) (show 0 ≤ 20*x-32 by linarith)]
  have H' := (le_div_iff₀ h2).2 H
  linarith

theorem ratio_sq_le_divisor_sum {s : ℕ} (hs : Squarefree s) (ho : s.Coprime 2) :
    ((s:ℝ)/(height s:ℝ))^2 ≤ ∑ d ∈ s.divisors, divisorWeight d := by
  classical
  rw [← divisorWeight_mult.prodPrimeFactors_one_add_of_squarefree hs]
  have hS : (s:ℝ) = ∏ p ∈ s.primeFactors, (p:ℝ) := by
    have H := congrArg (fun n : ℕ => (n:ℝ)) (Nat.prod_primeFactors_of_squarefree hs).symm
    simpa only [Nat.cast_prod] using H
  have hH : (height s:ℝ) = ∏ p ∈ s.primeFactors, ((p:ℝ)-2) := by
    unfold height
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).two_le]
    rfl
  rw [hS,hH,← Finset.prod_div_distrib, ← Finset.prod_pow]
  apply Finset.prod_le_prod₀ (fun _ _ => sq_nonneg _)
  intro p hp
  have pp := Nat.prime_of_mem_primeFactors hp
  have p2 : p ≠ 2 := by
    intro h
    subst p
    have k := Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) (dvd_refl 2)
    simpa [ho.gcd_eq_one] using k
  have p3 : 3 ≤ p := by have := pp.two_le; omega
  rw [divisorWeight_at_prime pp]
  exact prime_ratio_sq (by exact_mod_cast p3)

end AmplitudeTail
end HeightProductionSection10

section HeightProductionSection11
open Finset
open scoped BigOperators

namespace AmplitudeTail

private theorem card_dvd_le_div {X d : ℕ} (hd : 0 < d) (S : Finset ℕ)
    (hs : ∀ n ∈ S, 0 < n ∧ n < X ∧ d ∣ n) : S.card ≤ X/d := by
  let T := Icc 1 (X/d)
  have le : S.card ≤ T.card := by
    apply Finset.card_le_card_of_injOn (f := fun n => n/d)
    · intro n hn
      obtain ⟨h1,h2,h3⟩ := hs n hn
      apply mem_Icc.mpr
      refine ⟨?_, Nat.div_le_div_right h2.le⟩
      exact Nat.div_pos (Nat.le_of_dvd h1 h3) hd
    · intro n hn m hm h
      change n/d = m/d at h
      rw [← Nat.div_mul_cancel (hs n hn).2.2, ← Nat.div_mul_cancel (hs m hm).2.2, h]
  simpa [T, Nat.card_Icc] using le


theorem ratio_sq_sum_le (X : ℕ) :
    (∑ n ∈ (range X).filter (fun n => Squarefree n ∧ n.Coprime 2),
      ((n:ℝ)/(height n:ℝ))^2) ≤ (∑' d : ℕ, dividedWeight d) * X := by
  classical
  let U := (range X).filter (fun n => Squarefree n ∧ n.Coprime 2)
  have hU (n : ℕ) (hn : n ∈ U) : n < X ∧ Squarefree n ∧ n.Coprime 2 := by
    simpa [U] using hn
  have eq (n : ℕ) (hn : n ∈ U) :
      (∑ d ∈ n.divisors, divisorWeight d) =
        ∑ d ∈ range X, if d ∣ n then divisorWeight d else 0 := by
    rw [← sum_filter]
    apply sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, mem_filter, mem_range]
    exact ⟨fun h => ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero (hU n hn).2.1.ne_zero) h.1).trans_lt
      (hU n hn).1,h.1⟩, fun h => ⟨h.2,(hU n hn).2.1.ne_zero⟩⟩
  change (∑ n ∈ U, _) ≤ _
  calc
    _ ≤ ∑ n ∈ U, ∑ d ∈ n.divisors, divisorWeight d :=
      sum_le_sum (fun n hn => ratio_sq_le_divisor_sum (hU n hn).2.1 (hU n hn).2.2)
    _ = ∑ n ∈ U, ∑ d ∈ range X, if d ∣ n then divisorWeight d else 0 := sum_congr rfl eq
    _ = ∑ d ∈ range X, ∑ n ∈ U, if d ∣ n then divisorWeight d else 0 := sum_comm
    _ ≤ ∑ d ∈ range X, dividedWeight d * X := by
      apply sum_le_sum
      intro d hd
      rw [← sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      by_cases hd0 : d = 0
      · simp [hd0, dividedWeight]
      have hdpos := Nat.pos_of_ne_zero hd0
      have hc := card_dvd_le_div hdpos (U.filter (fun n => d ∣ n)) (by
        intro n hn
        obtain ⟨hn,hdvd⟩ := mem_filter.mp hn
        exact ⟨Nat.pos_of_ne_zero (hU n hn).2.1.ne_zero,(hU n hn).1,hdvd⟩)
      have hX : (((X/d : ℕ) : ℝ)) ≤ (X:ℝ)/(d:ℝ) := by
        apply (le_div_iff₀ (by exact_mod_cast hdpos)).2
        exact_mod_cast Nat.div_mul_le_self X d
      calc
        _ ≤ ((X/d : ℕ):ℝ) * divisorWeight d :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (divisorWeight_nonneg d)
        _ ≤ ((X:ℝ)/(d:ℝ)) * divisorWeight d :=
          mul_le_mul_of_nonneg_right hX (divisorWeight_nonneg d)
        _ = dividedWeight d * X := by rw [dividedWeight]; ring
    _ = (∑ d ∈ range X, dividedWeight d) * X := (sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (dividedWeight_summable.sum_le_tsum _ (fun n _ => dividedWeight_nonneg n))
      (Nat.cast_nonneg X)

end AmplitudeTail
end HeightProductionSection11

section HeightProductionSection12
open Finset
open scoped BigOperators

namespace AmplitudeTail

private noncomputable def heightShell (X Y N : ℕ) : Finset ℕ := by
  classical
  exact (heightCut Y N).filter fun s => X ≤ s

private theorem heightCut_card_le_add (X Y N : ℕ) :
    (heightCut Y N).card ≤ (heightCut X N).card + (heightShell X Y N).card := by
  classical
  have hsub : heightCut Y N ⊆ heightCut X N ∪ heightShell X Y N := by
    intro s hs
    by_cases h : s < X
    · exact mem_union.mpr (.inl (mem_heightCut.mpr ⟨h,(mem_heightCut.mp hs).2⟩))
    · exact mem_union.mpr (.inr (mem_filter.mpr ⟨hs, le_of_not_gt h⟩))
  exact (card_le_card hsub).trans (card_union_le _ _)

noncomputable def ratioMomentConstant : ℝ := ∑' d : ℕ, dividedWeight d

theorem ratioMomentConstant_nonneg : 0 ≤ ratioMomentConstant :=
  tsum_nonneg dividedWeight_nonneg

private theorem shell_bound (N q : ℕ) (hq : 0 < q) :
    ((heightShell (q*N) (q*2*N) N).card : ℝ) ≤ 2*ratioMomentConstant*N/q := by
  classical
  let U := heightShell (q*N) (q*2*N) N
  have hu (n : ℕ) (hn : n ∈ U) : q*N ≤ n ∧ n < q*2*N ∧
      Squarefree n ∧ n.Coprime 2 ∧ height n < N := by
    change n ∈ (heightCut (q*2*N) N).filter _ at hn
    exact ⟨(mem_filter.mp hn).2,mem_heightCut.mp (mem_filter.mp hn).1⟩
  have hz : (0:ℝ) < q := by exact_mod_cast hq
  have hprod : (U.card : ℝ) * (q:ℝ)^2 ≤
      ratioMomentConstant * ((q*2*N : ℕ):ℝ) := by
    calc
      _ = ∑ _n ∈ U, (q:ℝ)^2 := by simp [nsmul_eq_mul]
      _ ≤ ∑ n ∈ U, ((n:ℝ)/(height n:ℝ))^2 := by
        apply sum_le_sum
        intro n hn
        have H := hu n hn
        have hs : (0:ℝ) < height n := by exact_mod_cast height_pos H.2.2.2.1
        have D : (q:ℝ) ≤ (n:ℝ)/(height n:ℝ) := by
          apply (le_div_iff₀ hs).2
          have H₁ : (q:ℝ)*(N:ℝ) ≤ (n:ℝ) := by exact_mod_cast H.1
          have H₂ : (height n:ℝ) ≤ N := by exact_mod_cast H.2.2.2.2.le
          exact (mul_le_mul_of_nonneg_left H₂ hz.le).trans H₁
        exact (sq_le_sq₀ hz.le (div_nonneg (Nat.cast_nonneg _) hs.le)).mpr D
      _ ≤ ∑ n ∈ (range (q*2*N)).filter (fun n => Squarefree n ∧ n.Coprime 2),
            ((n:ℝ)/(height n:ℝ))^2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn; exact mem_filter.mpr ⟨mem_range.mpr (hu n hn).2.1,(hu n hn).2.2.1,(hu n hn).2.2.2.1⟩
        · intro _ _ _; exact sq_nonneg _
      _ ≤ _ := ratio_sq_sum_le _
  change (U.card : ℝ) ≤ _
  have hh := (le_div_iff₀ (sq_pos_of_pos hz)).2 hprod
  calc
    _ ≤ ratioMomentConstant * ((q*2*N : ℕ):ℝ) / (q:ℝ)^2 := hh
    _ = _ := by push_cast; field_simp

private theorem heightCut_dyadic_growth (N k : ℕ) :
    ((heightCut (2^k*N) N).card : ℝ) ≤
      N + 4*ratioMomentConstant*N * (1 - 1/(2:ℝ)^k) := by
  induction k with
  | zero =>
    simp only [pow_zero,one_mul,div_one,sub_self,mul_zero,add_zero]
    have h : (heightCut N N).card ≤ N := by
      classical
      have hsub : heightCut N N ⊆ range N := fun _ hs => mem_range.mpr (mem_heightCut.mp hs).1
      simpa only [card_range] using card_le_card hsub
    exact_mod_cast h
  | succ k ih =>
    have step := heightCut_card_le_add (2^k*N) (2^k*2*N) N
    have er : 2^(k+1)*N = 2^k*2*N := by rw [pow_succ]
    rw [er]
    have hstep : ((heightCut (2^k*2*N) N).card : ℝ) ≤
        ((heightCut (2^k*N) N).card : ℝ) + ((heightShell (2^k*N) (2^k*2*N) N).card : ℝ) := by
      exact_mod_cast step
    apply le_trans hstep
    apply le_trans (add_le_add ih (shell_bound N (2^k) (by positivity)))
    push_cast
    rw [pow_succ]
    have hp : (0:ℝ) < 2^k := by positivity
    field_simp
    <;> ring_nf <;> exact le_rfl


theorem ampCount_linear_growth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, (∑ n ∈ range N, (ampCount n:ℝ)) ≤ C * N := by
  classical
  refine ⟨1+4*ratioMomentConstant, by linarith [ratioMomentConstant_nonneg], ?_⟩
  intro N
  by_cases hN : N = 0
  · simp [hN]
  let k := 3*N^2+1
  have hk : k ≤ 2^k*N := by
    exact (Nat.lt_two_pow_self (n := k)).le.trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hN))
  have hsub : heightCut k N ⊆ heightCut (2^k*N) N := by
    intro s hs
    obtain ⟨h1,h2⟩ := mem_heightCut.mp hs
    exact mem_heightCut.mpr ⟨h1.trans_le hk,h2⟩
  rw [← Nat.cast_sum, ampCount_sum_eq_heightCut N]
  change ((heightCut k N).card : ℝ) ≤ _
  have hcast : ((heightCut k N).card : ℝ) ≤ ((heightCut (2^k*N) N).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  apply hcast.trans ((heightCut_dyadic_growth N k).trans _)
  have ht : 1-1/(2:ℝ)^k ≤ 1 := sub_le_self _ (by positivity)
  have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 4*ratioMomentConstant*N from
    mul_nonneg (mul_nonneg (by norm_num) ratioMomentConstant_nonneg) (Nat.cast_nonneg N))
  linarith

end AmplitudeTail
end HeightProductionSection12

section HeightProductionSection13
open scoped BigOperators
open Complex

namespace AmplitudeTail

noncomputable def powTerm (x : ℝ) (z : ℂ) : ℂ := (x:ℂ)^(-z)

noncomputable def localCorr (p : ℕ) (z : ℂ) : ℂ :=
  if p = 2 then -powTerm 2 z else if p.Prime then
    (1 - powTerm (p:ℝ) z) * (1 + powTerm ((p:ℝ)-2) z) - 1
    else 0

noncomputable def ampCorr (z : ℂ) : ℂ := ∏' p : ℕ, (1 + localCorr p z)

theorem powTerm_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (z : ℂ) :
    powTerm (x*y) z = powTerm x z * powTerm y z := by
  unfold powTerm
  simp only [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos hx hy).ne'),
    ← Complex.ofReal_log hx.le, ← Complex.ofReal_log hy.le,
    ← Complex.ofReal_log (mul_pos hx hy).le, Real.log_mul hx.ne' hy.ne',
    Complex.ofReal_add, add_mul, Complex.exp_add]

theorem powTerm_differentiable {x : ℝ} (hx : x ≠ 0) :
    Differentiable ℂ (powTerm x) := by
  have h : powTerm x = fun z => Complex.exp (Complex.log (x:ℂ) * (-z)) := by
    funext z
    rw [powTerm, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx)]
  rw [h]
  fun_prop

theorem powTerm_norm {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ‖powTerm x z‖ = x ^ (-z.re) := by
  simp only [powTerm, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]

private theorem corr_log_bound {x : ℝ} (hx : 3 ≤ x) :
    0 ≤ Real.log (x/(x-2)) ∧ Real.log (x/(x-2)) ≤ 6/x := by
  have x0 : 0 < x := by linarith
  have xm : 0 < x-2 := by linarith
  have i : 1 ≤ x/(x-2) := (le_div_iff₀ xm).2 (by linarith)
  have H := Real.log_le_sub_one_of_pos (div_pos x0 xm)
  have divEq : x/(x-2)-1 = 2/(x-2) := by field_simp; ring
  rw [divEq] at H
  refine ⟨Real.log_nonneg i, H.trans ?_⟩
  exact (div_le_div_iff₀ xm x0).2 (by linarith)

private theorem corr_pow_difference {x : ℝ} (hx : 3 ≤ x) (z : ℂ) :
    powTerm (x-2) z - powTerm x z =
      powTerm x z * (Complex.exp (z * (Real.log (x/(x-2)) : ℂ)) - 1) := by
  have x0 : 0 < x := by linarith
  have xm : 0 < x-2 := by linarith
  have ex : powTerm (x-2) z =
      powTerm x z * Complex.exp (z * (Real.log (x/(x-2)) : ℂ)) := by
    unfold powTerm
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr xm.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr x0.ne'),
      ← Complex.ofReal_log x0.le, ← Complex.ofReal_log xm.le, Real.log_div x0.ne' xm.ne',
      Complex.ofReal_sub, ← Complex.exp_add]
    congr 1
    ring
  rw [ex]
  ring

private theorem corr_two_pow_bound {x : ℝ} (hx : 3 ≤ x) {z : ℂ} (hz : 3/4 ≤ z.re) :
    ‖powTerm x z‖ * ‖powTerm (x-2) z‖ ≤ 3*x^(-(3/2):ℝ) := by
  have x0 : 0 < x := by linarith
  have x1 : 1 ≤ x := by linarith
  have x2 : 0 < x-2 := by linarith
  have x2' : 1 ≤ x-2 := by linarith
  have x3 : 0 < x/3 := by positivity
  rw [powTerm_norm x0,powTerm_norm x2]
  have b1 := Real.rpow_le_rpow_of_exponent_le x1 (show -z.re ≤ -(3/4:ℝ) by linarith)
  have b2 := Real.rpow_le_rpow_of_exponent_le x2' (show -z.re ≤ -(3/4:ℝ) by linarith)
  have b3 : (x-2)^(-(3/4):ℝ) ≤ (x/3)^(-(3/4):ℝ) :=
    Real.rpow_le_rpow_of_nonpos x3 (show x/3 ≤ x-2 by linarith) (by norm_num)
  have b4 : (x/3)^(-(3/4):ℝ) ≤ 3*x^(-(3/4):ℝ) := by
    rw [Real.div_rpow x0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3), div_inv_eq_mul,
      mul_comm (x^(-(3/4):ℝ))]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg x0.le _)
    calc
      _ ≤ (3:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = _ := Real.rpow_one _
  calc
    _ ≤ x^(-(3/4):ℝ) * (3*x^(-(3/4):ℝ)) :=
      mul_le_mul b1 (b2.trans (b3.trans b4)) (Real.rpow_nonneg x2.le _) (Real.rpow_nonneg x0.le _)
    _ = 3*x^(-(3/2):ℝ) := by
      rw [mul_left_comm, ← Real.rpow_add x0]
      congr 2
      norm_num

private theorem corr_diff_bound {x M : ℝ} (hx : 3 ≤ x) (hM : 0 ≤ M)
    (hpM : 6*M ≤ x) {z : ℂ} (hz : 3/4 ≤ z.re) (hzM : ‖z‖ ≤ M) :
    ‖powTerm (x-2) z - powTerm x z‖ ≤ (12*M)*x^(-(3/2):ℝ) := by
  have x0 : 0 < x := by linarith
  have x1 : 1 ≤ x := by linarith
  have hlog := corr_log_bound hx
  have zlog : ‖z * (Real.log (x/(x-2)):ℂ)‖ ≤ 6*M/x := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog.1]
    calc
      _ ≤ M*(6/x) := mul_le_mul hzM hlog.2 hlog.1 hM
      _ = _ := by ring
  have zle : ‖z * (Real.log (x/(x-2)):ℂ)‖ ≤ 1 := zlog.trans ((div_le_one x0).2 hpM)
  have b := (Complex.norm_exp_sub_one_le zle).trans (mul_le_mul_of_nonneg_left zlog (by norm_num))
  rw [corr_pow_difference hx,norm_mul,powTerm_norm x0]
  have b1 := Real.rpow_le_rpow_of_exponent_le x1 (show -z.re ≤ -(3/4:ℝ) by linarith)
  calc
    _ ≤ x^(-(3/4):ℝ) * (2*(6*M/x)) :=
      mul_le_mul b1 b (norm_nonneg _) (Real.rpow_nonneg x0.le _)
    _ = (12*M) * x^(-(7/4):ℝ) := by
      rw [show (-(7/4):ℝ) = -(3/4)-1 by norm_num, Real.rpow_sub x0, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le x1 (by norm_num)) (by positivity)

theorem local_corr_bound {p : ℕ} (hp : 3 ≤ p) {M : ℝ} (hM : 0 ≤ M) (hpM : 6*M ≤ p)
    {z : ℂ} (hz : 3/4 ≤ z.re) (hzM : ‖z‖ ≤ M) :
    ‖localCorr p z‖ ≤ (12*M+3)*(p:ℝ)^(-(3/2):ℝ) := by
  have px : (3:ℝ) ≤ p := by exact_mod_cast hp
  by_cases hP : p.Prime
  · have hn : p ≠ 2 := by omega
    simp only [localCorr,hn,hP,ite_true,ite_false]
    let A := powTerm ((p:ℝ)-2) z
    let B := powTerm (p:ℝ) z
    have e : (1-B)*(1+A)-1=(A-B)-B*A := by ring
    rw [e]
    exact (norm_sub_le _ _).trans (by
      rw [norm_mul]
      have h1 := corr_diff_bound px hM hpM hz hzM
      have h2 := corr_two_pow_bound px hz
      change ‖A-B‖ + ‖B‖*‖A‖ ≤ _
      rw [add_mul]
      exact add_le_add h1 h2)
  · have hn : p ≠ 2 := by omega
    simp only [localCorr,hn,hP,ite_false,norm_zero]
    positivity

theorem local_corr_differentiable (p : ℕ) : Differentiable ℂ (localCorr p) := by
  by_cases hp2 : p = 2
  · have e : localCorr p = fun z => -powTerm 2 z := by
      funext z
      simp [localCorr,hp2]
    rw [e]
    exact (powTerm_differentiable (by norm_num : (2:ℝ) ≠ 0)).neg
  by_cases hp : p.Prime
  · have h3 : 3 ≤ p := by have := hp.two_le; omega
    have h3R : (3:ℝ) ≤ p := by exact_mod_cast h3
    have h0 : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h2 : (p:ℝ)-2 ≠ 0 := by linarith
    have e : localCorr p = fun z => (1-powTerm (p:ℝ) z)*(1+powTerm ((p:ℝ)-2) z)-1 := by
      funext z
      simp [localCorr,hp2,hp]
    rw [e]
    exact (((differentiable_const (1:ℂ)).sub (powTerm_differentiable h0)).mul
      ( (differentiable_const (1:ℂ)).add (powTerm_differentiable h2))).sub (differentiable_const (1:ℂ))
  · have e : localCorr p = fun _ => 0 := by funext z; simp [localCorr,hp2,hp]
    rw [e]
    exact differentiable_const (0:ℂ)

end AmplitudeTail
end HeightProductionSection13

section HeightProductionSection14
open scoped Topology BigOperators
open Filter Finset Complex

namespace AmplitudeTail

def corrDomain : Set ℂ := {z | 3/4 < z.re}

theorem corrDomain_open : IsOpen corrDomain :=
  isOpen_lt continuous_const Complex.continuous_re

theorem ampCorr_hasProdLocally :
    HasProdLocallyUniformlyOn (fun p z => 1 + localCorr p z) ampCorr corrDomain := by
  apply hasProdLocallyUniformlyOn_of_forall_compact corrDomain_open
  intro K hK hKc
  obtain ⟨M₀,hM₀⟩ := hKc.exists_bound_of_continuousOn (f := (id : ℂ → ℂ)) continuous_id.continuousOn
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hMd (z : ℂ) (hz : z ∈ K) : ‖z‖ ≤ M := (hM₀ z hz).trans (le_max_left _ _)
  have hu : Summable (fun p : ℕ => (12*M+3)*(p:ℝ)^(-(3/2):ℝ)) := by
    exact (Real.summable_nat_rpow.mpr (by norm_num : (-(3/2):ℝ)< -1)).mul_left _
  refine hu.hasProdUniformlyOn_nat_one_add hKc ?_
    (fun p => (local_corr_differentiable p).continuous.continuousOn)
  obtain ⟨N,hN⟩ := exists_nat_gt (6*M)
  filter_upwards [eventually_ge_atTop (max N 3)] with p hp z hz
  have hpN : N ≤ p := (le_max_left _ _).trans hp
  have hp3 : 3 ≤ p := (le_max_right _ _).trans hp
  have hh : 6*M ≤ p := hN.le.trans (by exact_mod_cast hpN)
  exact local_corr_bound hp3 hM hh (le_of_lt (hK hz)) (hMd z hz)

theorem ampCorr_differentiableOn : DifferentiableOn ℂ ampCorr corrDomain := by
  refine TendstoLocallyUniformlyOn.differentiableOn ampCorr_hasProdLocally
    (Eventually.of_forall fun s => ?_) corrDomain_open
  simpa [Finset.prod_fn] using
    (DifferentiableOn.finsetProd (u := s) (fun i _ =>
      ((differentiable_const (1:ℂ)).add (local_corr_differentiable i)).differentiableOn))

theorem ampCorr_eulerCut {z : ℂ} (hz : 3/4 < z.re) :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow, (1 + localCorr p z))
      atTop (𝓝 (ampCorr z)) := by
  have H := (ampCorr_hasProdLocally.hasProd hz).tendsto_prod_nat
  apply H.congr
  intro N
  symm
  apply Finset.prod_subset (fun p hp => Finset.mem_range.mpr (Nat.mem_primesBelow.mp hp).1)
  intro p hp hp'
  have nP : ¬p.Prime := fun he => hp' (Nat.mem_primesBelow.mpr ⟨Finset.mem_range.mp hp,he⟩)
  have n2 : p ≠ 2 := fun he => nP (he ▸ Nat.prime_two)
  simp [localCorr,nP,n2]

noncomputable def zetaResidue (z : ℂ) : ℂ :=
  Function.update (fun s : ℂ => (s-1)*riemannZeta s) 1 1 z

theorem zetaResidue_one : zetaResidue 1 = 1 := Function.update_self _ _ _

theorem zetaResidue_off_one {z : ℂ} (hz : z ≠ 1) : zetaResidue z = (z-1)*riemannZeta z :=
  Function.update_of_ne hz ..

theorem zetaResidue_differentiable : Differentiable ℂ zetaResidue := by
  apply differentiableOn_univ.mp
  apply (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (s := Set.univ)
    (c := (1:ℂ)) (by simp)).mp
  constructor
  · have h : DifferentiableOn ℂ (fun z : ℂ => (z-1)*riemannZeta z) (Set.univ \ {(1:ℂ)}) := by
      apply (differentiableOn_id.sub_const _).mul
      intro z hz
      exact (differentiableAt_riemannZeta hz.2).differentiableWithinAt
    exact h.congr (fun z hz => zetaResidue_off_one hz.2)
  · change ContinuousAt (Function.update (fun s : ℂ => (s-1)*riemannZeta s) 1 1) 1
    rw [continuousAt_update_same]
    exact riemannZeta_residue_one

noncomputable def ampHolomorphicPoleSubtraction : ℂ → ℂ :=
  dslope (fun z => zetaResidue z * ampCorr z) 1

theorem ampHolomorphicPoleSubtraction_continuousOn :
    ContinuousOn ampHolomorphicPoleSubtraction {z | 1 ≤ z.re} := by
  have h1 : (1:ℂ) ∈ corrDomain := by norm_num [corrDomain]
  have hs : corrDomain ∈ 𝓝 (1:ℂ) := corrDomain_open.mem_nhds h1
  have hd : DifferentiableOn ℂ (fun z => zetaResidue z * ampCorr z) corrDomain :=
    zetaResidue_differentiable.differentiableOn.mul ampCorr_differentiableOn
  exact ((continuousOn_dslope hs).2 ⟨hd.continuousOn, hd.differentiableAt hs⟩).mono
    (fun z hz => (by norm_num : (3/4:ℝ) < 1).trans_le hz)

theorem ampHolomorphicPoleSubtraction_eq {z : ℂ} (hz : z ≠ 1) :
    ampHolomorphicPoleSubtraction z = riemannZeta z * ampCorr z - ampCorr 1/(z-1) := by
  rw [ampHolomorphicPoleSubtraction, dslope_of_ne _ hz, slope_def_field,
    zetaResidue_off_one hz, zetaResidue_one, one_mul]
  field_simp [sub_ne_zero.mpr hz] <;> ring

end AmplitudeTail
end HeightProductionSection14

section HeightProductionSection15
open scoped BigOperators Topology
open Finset Filter Complex

namespace AmplitudeTail

theorem height_mul {d e : ℕ} (h : d.Coprime e) :
    height (d*e) = height d * height e := by
  simp only [height]
  rw [h.primeFactors_mul, Finset.prod_union h.disjoint_primeFactors]

noncomputable def conductorTerm (z : ℂ) (s : ℕ) : ℂ :=
  if Squarefree s ∧ s.Coprime 2 then powTerm (height s : ℝ) z else 0

theorem conductor_term_zero (z : ℂ) : conductorTerm z 0 = 0 := by simp [conductorTerm]

theorem conductor_term_one (z : ℂ) : conductorTerm z 1 = 1 := by
  simp [conductorTerm,height,powTerm]

theorem conductor_term_mul (z : ℂ) {d e : ℕ} (h : d.Coprime e) :
    conductorTerm z (d*e) = conductorTerm z d * conductorTerm z e := by
  classical
  unfold conductorTerm
  have H : Squarefree (d*e) ∧ (d*e).Coprime 2 ↔
      (Squarefree d ∧ d.Coprime 2) ∧ (Squarefree e ∧ e.Coprime 2) := by
    rw [Nat.squarefree_mul h,Nat.coprime_mul_iff_left]
    tauto
  by_cases hd : Squarefree d ∧ d.Coprime 2
  · by_cases he : Squarefree e ∧ e.Coprime 2
    · rw [ite_eq_left (H.mpr ⟨hd,he⟩),ite_eq_left hd,ite_eq_left he,
        height_mul h, Nat.cast_mul]
      exact powTerm_mul (by exact_mod_cast height_pos hd.2) (by exact_mod_cast height_pos he.2) z
    · rw [ite_eq_right (fun t => he (H.mp t).2),ite_eq_left hd,ite_eq_right he,mul_zero]
  · rw [ite_eq_right (fun t => hd (H.mp t).1),ite_eq_right hd,zero_mul]

theorem conductor_term_prime {p : ℕ} (hp : p.Prime) (z : ℂ) :
    conductorTerm z p = if p = 2 then 0 else powTerm ((p:ℝ)-2) z := by
  unfold conductorTerm
  by_cases h : p = 2
  · subst p
    have hn : ¬(2:ℕ).Coprime 2 := by decide
    simp [hn]
  · have hc : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr fun he =>
      h ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp he)
    rw [ite_eq_left ⟨hp.squarefree,hc⟩,ite_eq_right h,height,hp.primeFactors,prod_singleton,
      Nat.cast_sub hp.two_le,Nat.cast_ofNat]

theorem conductor_term_large_pow {p k : ℕ} (hp : p.Prime) (hk : 1 < k) (z : ℂ) :
    conductorTerm z (p^k) = 0 := by
  have ns : ¬Squarefree (p^k) := by
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
    intro h
    have := h.2
    omega
  simp [conductorTerm,ns]

theorem conductor_term_euler_row {p : ℕ} (hp : p.Prime) (z : ℂ) :
    (∑' k : ℕ, conductorTerm z (p^k)) = 1 + (if p = 2 then 0 else powTerm ((p:ℝ)-2) z) := by
  rw [tsum_eq_sum (s := range 2) (fun k hk => conductor_term_large_pow hp (by
    simp only [mem_range] at hk
    omega) z),sum_range_succ,sum_range_one,pow_zero,pow_one,conductor_term_one,conductor_term_prime hp]

private theorem conductor_term_prime_norm_le {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : 1 < z.re) :
    ‖conductorTerm z p‖ ≤ (3:ℝ)^z.re * (p:ℝ)^(-z.re) := by
  rw [conductor_term_prime hp]
  split_ifs with h2
  · exact norm_zero.le.trans (by positivity)
  · have h3 : 3 ≤ p := by have := hp.two_le; omega
    have pr : (3:ℝ) ≤ p := by exact_mod_cast h3
    have h0 : (0:ℝ) < p := by linarith
    have h2 : (0:ℝ) < (p:ℝ)-2 := by linarith
    have h3' : (0:ℝ) < (p:ℝ)/3 := by positivity
    rw [powTerm_norm h2]
    calc
      _ ≤ ((p:ℝ)/3)^(-z.re) := Real.rpow_le_rpow_of_nonpos h3' (by linarith) (by linarith)
      _ = _ := by
        rw [Real.div_rpow h0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 3),
          div_inv_eq_mul, mul_comm]

theorem conductor_term_summable_norm {z : ℂ} (hz : 1 < z.re) :
    Summable (fun s => ‖conductorTerm z s‖) := by
  let f (s : ℕ) := ‖conductorTerm z s‖
  let c (p : ℕ) := (3:ℝ)^z.re * (p:ℝ)^(-z.re)
  have cs : Summable c := (Real.summable_nat_rpow.mpr (by linarith : -z.re < -1)).mul_left _
  have zero {p : ℕ} (hp : p.Prime) (k : ℕ) (hk : k ∉ range 2) : f (p^k) = 0 := by
    have hK : 1 < k := by simp only [mem_range] at hk; omega
    simp [f,conductor_term_large_pow hp hK]
  refine SignedHeight.summable_nonneg_of_prime_power_rows f c (fun _ => norm_nonneg _) ?_
    ?_ ?_ (fun _ => by dsimp [c]; positivity) cs ?_ ?_
  · simp [f,conductor_term_zero]
  · simp [f,conductor_term_one]
  · intro d e h
    simp only [f,conductor_term_mul z h,norm_mul]
  · exact fun hp => summable_of_ne_finset_zero (s := range 2) (zero hp)
  · intro p hp
    rw [tsum_eq_sum (s := range 2) (zero hp),sum_range_succ,sum_range_one,pow_zero,pow_one]
    change ‖conductorTerm z 1‖ + ‖conductorTerm z p‖ ≤ _
    rw [conductor_term_one,norm_one]
    have H := conductor_term_prime_norm_le hp hz
    dsimp only [c]
    linarith

private theorem ampSeries_fiber_sum (z : ℂ) (n : ℕ) :
    (∑' s : height ⁻¹' ({n} : Set ℕ), conductorTerm z s) =
      (ampCount n:ℂ) * powTerm (n:ℝ) z := by
  classical
  rw [tsum_subtype (height ⁻¹' ({n} : Set ℕ)) (conductorTerm z)]
  let w := powTerm (n:ℝ) z
  have ps (s : ℕ) : (height ⁻¹' ({n} : Set ℕ)).indicator (conductorTerm z) s =
      if Squarefree s ∧ s.Coprime 2 ∧ height s = n then w else 0 := by
    by_cases h : height s = n
    · simp [Set.indicator, conductorTerm, h,w]
    · simp [Set.indicator, h]
  simp_rw [ps]
  rw [tsum_eq_sum (s := range (3*n^2+1))]
  · rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    rfl
  · intro s hs
    split_ifs with h
    · have hb := conductor_le_three_height_sq h.1 h.2.1
      rw [h.2.2] at hb
      exact False.elim (hs (mem_range.mpr (by omega)))
    · rfl

theorem conductor_series_eq_amp_LSeries {z : ℂ} (hz : 1 < z.re) :
    (∑' s : ℕ, conductorTerm z s) = LSeries (fun n => (ampCount n:ℂ)) z := by
  have hf := (conductor_term_summable_norm hz).of_norm
  have H := hf.hasSum.tsum_fiberwise height
  have h0 : ((ampCount 0:ℕ):ℂ) = 0 := by
    suffices ampCount 0 = 0 by simpa
    unfold ampCount
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro s hs hg
    exact (height_pos hg.2.1).ne' hg.2.2
  rw [← H.tsum_eq, LSeries]
  apply tsum_congr
  intro n
  rw [ampSeries_fiber_sum]
  symm
  exact LSeries.term_def₀ (f := fun n => (ampCount n:ℂ)) h0 z n

theorem conductor_series_eulerCut {z : ℂ} (hz : 1 < z.re) :
    Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow,
      (1 + (if p = 2 then 0 else powTerm ((p:ℝ)-2) z)))
      atTop (𝓝 (LSeries (fun n => (ampCount n:ℂ)) z)) := by
  rw [← conductor_series_eq_amp_LSeries hz]
  apply (EulerProduct.eulerProduct (conductor_term_one z) (conductor_term_mul z)
    (conductor_term_summable_norm hz) (conductor_term_zero z)).congr
  intro N
  exact Finset.prod_congr rfl (fun p hp => conductor_term_euler_row (Nat.mem_primesBelow.mp hp).2 z)

end AmplitudeTail
end HeightProductionSection15

section HeightProductionSection16
open Filter Finset Complex
open scoped Topology BigOperators

namespace AmplitudeTail

private theorem inv_zeta_factor_nonzero {p : ℕ} (hp : p.Prime) {z : ℂ} (hz : 1 < z.re) :
    1 - powTerm (p:ℝ) z ≠ 0 := by
  have x : (1:ℝ) < p := by exact_mod_cast hp.one_lt
  have hn := Real.rpow_lt_one_of_one_lt_of_neg x (by linarith : -z.re < 0)
  intro H
  have h := congrArg (fun v : ℂ => ‖v‖) (sub_eq_zero.mp H)
  rw [norm_one,powTerm_norm (by linarith)] at h
  linarith

theorem amp_LSeries_eq_zeta_mul {z : ℂ} (hz : 1 < z.re) :
    LSeries (fun n => (ampCount n:ℂ)) z = riemannZeta z * ampCorr z := by
  have hs := conductor_series_eulerCut hz
  have hzeta := riemannZeta_eulerProduct hz
  have hc := ampCorr_eulerCut (lt_trans (by norm_num : (3/4:ℝ)<1) hz)
  have hc' := hzeta.mul hc
  apply tendsto_nhds_unique hs
  apply hc'.congr
  intro N
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := (Nat.mem_primesBelow.mp hp).2
  have hnz := inv_zeta_factor_nonzero hp' hz
  change (1 - powTerm (p:ℝ) z)⁻¹ * (1+localCorr p z) = _
  by_cases h : p = 2
  · subst p
    simp only [localCorr,ite_true,add_zero,← sub_eq_add_neg]
    exact inv_mul_cancel₀ hnz
  · simp only [localCorr,h,hp',ite_false,ite_true]
    field_simp [hnz]
    <;> ring

theorem ampPoleSubtraction_eqOn {O : ℝ} (hO : ampCorr 1 = ((O⁻¹:ℝ):ℂ)) :
    Set.EqOn ampHolomorphicPoleSubtraction
      (fun z => LSeries (fun n => (ampCount n:ℂ)) z - ((O⁻¹:ℝ):ℂ)/(z-1))
      {z | 1 < z.re} := by
  intro z hz
  have hn : z ≠ 1 := by
    intro he
    subst z
    norm_num at hz
  change ampHolomorphicPoleSubtraction z = LSeries (fun n => (ampCount n:ℂ)) z - ((O⁻¹:ℝ):ℂ)/(z-1)
  rw [ampHolomorphicPoleSubtraction_eq hn,amp_LSeries_eq_zeta_mul hz,hO]

end AmplitudeTail
end HeightProductionSection16

section HeightProductionSection17
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
end HeightProductionSection17

section HeightProductionSection18
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
end HeightProductionSection18

section HeightProductionSection19
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
end HeightProductionSection19

section HeightProductionSection20
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
end HeightProductionSection20

section HeightProductionSection21
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
end HeightProductionSection21

section HeightProductionSection22
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
end HeightProductionSection22

section HeightProductionSection23
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
end HeightProductionSection23

section HeightProductionSection24
open Filter Finset
open scoped Topology
namespace AmplitudeTail

theorem local_corr_one_eq_inv {p : ℕ} (hp : p.Prime) :
    1 + localCorr p 1 = ((SignedHeight.heightOrdinaryPrimeFactor 2 p)⁻¹ : ℝ) := by
  by_cases h2 : p = 2
  · subst p
    norm_num [localCorr, powTerm, Complex.cpow_neg, SignedHeight.heightOrdinaryPrimeFactor]
  · have hn : ¬p∣2 := fun h => h2 ((Nat.dvd_prime Nat.prime_two).1 h |>.resolve_left hp.ne_one)
    have hgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
    have hreal : (2:ℝ) < p := by exact_mod_cast hgt
    have h0 : (p:ℝ) ≠ 0 := by positivity
    have h1 : (p:ℝ)-1 ≠ 0 := by linarith
    have hsub : (p:ℝ)-2 ≠ 0 := by linarith
    have h : (1-(p:ℝ)⁻¹)*(1+((p:ℝ)-2)⁻¹) =
        (SignedHeight.heightOrdinaryPrimeFactor 2 p)⁻¹ := by
      rw [SignedHeight.heightOrdinaryPrimeFactor, if_neg hn, inv_div]
      field_simp
      <;> ring
    have hC := congrArg (fun v : ℝ => (v:ℂ)) h
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_inv,
      Complex.ofReal_one, Complex.ofReal_natCast] at hC
    rw [localCorr, if_neg h2, if_pos hp]
    rw [show 1 + ((1-powTerm (p:ℝ) 1) * (1+powTerm ((p:ℝ)-2) 1)-1) =
        (1-powTerm (p:ℝ) 1) * (1+powTerm ((p:ℝ)-2) 1) by ring]
    simpa only [powTerm, Complex.cpow_neg, Complex.cpow_one,
      Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_inv] using hC

theorem ampCorr_one_of_limits {O : ℝ} (hO : O ≠ 0)
    (hOrd : Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow,
      SignedHeight.heightOrdinaryPrimeFactor 2 p) atTop (𝓝 O))
    (hCorr : Tendsto (fun N : ℕ => ∏ p ∈ N.primesBelow,
      (1 + localCorr p 1)) atTop (𝓝 (ampCorr 1))) :
    ampCorr 1 = ((O⁻¹:ℝ):ℂ) := by
  apply tendsto_nhds_unique hCorr
  have h := Complex.continuous_ofReal.continuousAt.tendsto.comp (hOrd.inv₀ hO)
  apply h.congr
  intro N
  change (((∏ p ∈ N.primesBelow, SignedHeight.heightOrdinaryPrimeFactor 2 p)⁻¹ : ℝ) : ℂ) = _
  rw [← Finset.prod_inv_distrib, Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun p hp => (local_corr_one_eq_inv (Nat.mem_primesBelow.mp hp).2).symm)

end AmplitudeTail
end HeightProductionSection24

section HeightProductionSection25
open Filter Finset DirichletCharacter
open scoped BigOperators Topology
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open AmplitudeTail

set_option maxHeartbeats 1200000 in
theorem Conjectures.Goldbach.PartnerPrincipalAmplitudeTail : (
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
  exact ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T, ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ ‖O 2‖ < (Y:ℝ)*‖S P b.2 2‖) ∧ |(F.card:ℝ)/(Y:ℝ)^2 - 1/(2*‖O 2‖)| ≤ ε) := by
  classical
  dsimp only
  let P₀ : DirichletCharacter ℂ 1 := 1
  let S := @TwistedGoldbachLocalProduct.series
  let P : {s : ℕ} → DirichletCharacter ℂ s → ℂ := fun {_} β => S P₀ β 2
  let O := S P₀ P₀ 2
  have hO : 0 < ‖O‖ := by
    have h := TwistedGoldbachMixedPrincipal.ordinary_at_least_one 2 (by decide) (by decide)
    exact zero_lt_one.trans_le (h.trans (Complex.re_le_norm O))
  have hPhase : AtTwoPhase P O := by
    intro s _ β hβ
    exact Conjectures.Goldbach.PartnerPrincipalRowPhase s β hβ 2 (by decide) (by decide)
  have hOrdFact : Tendsto (fun n : ℕ => ∏ p ∈ n.factorial.primeFactors,
      SignedHeight.heightOrdinaryPrimeFactor 2 p) atTop (𝓝 ‖O‖) := by
    apply SignedHeight.height_ordinary_factorial_limit 2
      (TwistedGoldbachSingularSeries.coefficient P₀ P₀ 2)
    · simpa only [one_mul, O, S, TwistedGoldbachLocalProduct.series] using
        TwistedGoldbachSingularSeries.partial_limit P₀ P₀ 2 (by decide) 1 one_ne_zero
    · intro q _
      simpa only [P₀, map_one, SignedHeight.heightNormalizedPrincipal,
        SignedHeight.heightPrincipJacobi, TwistedGoldbachSingularSeries.normalized] using
        (TwistedGoldbachSingularSeries.ambient_sum
          (α := (1 : DirichletCharacter ℂ 1)) (β := (1 : DirichletCharacter ℂ 1))
          isPrimitive_one_level_one isPrimitive_one_level_one (one_dvd q) (one_dvd q) 2)
    · intro q _
      exact TwistedGoldbachMixedPrincipal.ordinary_product q 2
  have hCoeff : ampCorr 1 = ((‖O‖⁻¹ : ℝ) : ℂ) :=
    ampCorr_one_of_limits hO.ne' (SignedHeight.ordinary_product_limit_of_factorial 2 hOrdFact)
      (ampCorr_eulerCut (by norm_num))
  obtain ⟨C,_,hBound⟩ := ampCount_linear_growth
  exact full_of_euler_data P O hO hPhase C hBound ampCorr
    ampCorr_differentiableOn hCoeff (fun _ hz => amp_LSeries_eq_zeta_mul hz)
end HeightProductionSection25
