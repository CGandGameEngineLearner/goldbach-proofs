import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
Adapted from the accepted OC-0103 explicit-formula assembly in
`Conjectures.Goldbach.DyadicCellShortPrimeFloor`, with the pointwise
window exponent specialized from `3/4` to `18/25`.
-/
open Finset Filter
open scoped Topology BigOperators Classical

namespace Conjectures.Goldbach.DynBlockFirstMass_aux

open Vx V7e V86 V1e V6i

structure PointwiseBudgets18 (D L H X : ℝ) : Prop where
  scale_ge_four : 4 ≤ X
  log_ge_one : 1 ≤ Real.log X
  smoothing_ge_one : 1 ≤ X^(2/3 : ℝ)
  smoothing_le_half : X^(2/3 : ℝ) ≤ X/2
  split_ge_two : 2 ≤ X^(5/16 : ℝ)
  split_le_scale : X^(5/16 : ℝ) ≤ X
  low_budget : 2*L/(Real.log X)^4 ≤ 1/16
  high_budget :
    576*H*X^2*(Real.log X)^14/
      (X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2) ≤ X^(18/25 : ℝ)/16
  residual_budget :
    D*(X^(2/3 : ℝ)*Real.log X +
      Real.sqrt X*Real.log X/X^(2/3 : ℝ) +
      X^2*Real.log X/(X^(2/3 : ℝ)*X)) ≤ X^(18/25 : ℝ)/16

theorem eventual_pointwise_budgets18 (D L H : ℝ) (hD : 0 ≤ D) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → PointwiseBudgets18 D L H X := by
  have hd := GoldbachOC103.eventually_power_log_bound (2/3) 1 2 1 0
    (by norm_num) (by norm_num)
  have hr := GoldbachOC103.eventually_power_log_bound (2/3) (18/25) (3*D) (1/16) 1
    (by norm_num) (by norm_num)
  have hh := GoldbachOC103.eventually_power_log_bound (17/24) (18/25) (576*H) (1/16) 14
    (by norm_num) (by norm_num)
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5/16)).eventually_ge_atTop 2
  have he : ∀ᶠ X : ℝ in atTop, PointwiseBudgets18 D L H X := by
    filter_upwards [hd, hr, hh, ht, eventually_ge_atTop (4 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (32*L))]
      with X hδ hres hhi hV hX hlog
    have hX1 : 1 ≤ X := by linarith
    have hXp : 0 < X := by linarith
    have hL1 : 1 ≤ Real.log X := (le_max_left _ _).trans hlog
    have hL32 : 32*L ≤ Real.log X := (le_max_right _ _).trans hlog
    have hLp : 0 < Real.log X := by linarith
    refine ⟨hX, hL1, Real.one_le_rpow hX1 (by norm_num), ?_, hV, ?_, ?_, ?_, ?_⟩
    · have h := hδ.2
      norm_num only [pow_zero, mul_one, Real.rpow_one, one_mul] at h
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by
        simpa only [mul_comm] using h)
    · exact (Real.rpow_le_rpow_of_exponent_le hX1
        (by norm_num : (5/16 : ℝ) ≤ 1)).trans_eq (Real.rpow_one X)
    · apply (div_le_iff₀ (pow_pos hLp 4)).mpr
      have hp : Real.log X ≤ (Real.log X)^4 := by
        simpa using pow_le_pow_right₀ hL1 (by norm_num : 1 ≤ 4)
      nlinarith
    · have hid := GoldbachOC103.high_packet_power_identity X hXp
      have heq : 576*H*X^2*(Real.log X)^14/
          (X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2)=
            576*H*X^(17/24 : ℝ)*(Real.log X)^14 := by
        calc
          _ = (576*H)*(X^2/(X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2))*(Real.log X)^14 := by ring
          _ = _ := by rw [hid]
      rw [heq]
      simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using hhi.2
    · calc
        _ ≤ D*(3*X^(2/3 : ℝ)*Real.log X) :=
          mul_le_mul_of_nonneg_left (GoldbachOC103.smoothing_residual_le X hX1) hD
        _ ≤ X^(18/25 : ℝ)/16 := by
          simpa only [pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using hres.2
  exact eventually_atTop.mp he

theorem actual_principal_window18_of_zero_weights
    (hzero : GoldbachOC103.ActualZeroWeightBounds) :
    ∃ X₀ : ℝ, X₀ ≤ X₀ ∧ ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(18/25 : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/4 := by
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets18 D C C hD.le
  refine ⟨max Xz Xb, le_rfl, ?_⟩
  intro X hX h hlower hupper
  have hbud := hb X ((le_max_right _ _).trans hX)
  have hX4 := hbud.scale_ge_four
  have hXpos : 0 < X := by linarith
  have hδ : 0 < X^(2/3 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hV : 0 < X^(5/16 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  obtain ⟨hlo, hcount⟩ := hz X ((le_max_left _ _).trans hX) hX4
    hbud.log_ge_one hbud.split_ge_two hbud.split_le_scale
  let S := V3b X
  let A := S.filter (fun c => |c.val.1.im| ≤ X^(5/16 : ℝ))
  let R := S.filter (fun c => ¬ |c.val.1.im| ≤ X^(5/16 : ℝ))
  let K := C*(Real.log X)^14/(X^(5/16 : ℝ)*Real.sqrt (X^(5/16 : ℝ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hS : ∀ c ∈ S, |c.val.1.im| ≤ X := by
    intro c hc
    exact (V5l X c).mp hc
  have hlow : (∑ c ∈ A, X^(c.val.1.re-1)) ≤ C/(Real.log X)^4 :=
    hlo A (fun c hc => (mem_filter.mp hc).2)
  have hhigh : ∀ v : ℝ, X^(5/16 : ℝ) ≤ v →
      (∑ c ∈ R.filter (fun c => |c.val.1.im| ≤ v), X^(c.val.1.re-1)) ≤
        K*v*Real.sqrt v := by
    intro v hv
    exact GoldbachOC103.weight_count_clamp R X (X^(5/16 : ℝ)) K v hV
      hbud.split_le_scale hK hv (fun c hc => hS c (mem_filter.mp hc).1) hcount
  have hpacket := GoldbachOC103.smoothed_packet_of_weight_bounds S (fun c => c.val.1)
    X X h (X^(2/3 : ℝ)) (X^(5/16 : ℝ)) (C/(Real.log X)^4) K
    (by linarith) le_rfl (by linarith) hh hupper hδ hbud.smoothing_le_half hV hK
    (fun c _ => c.property.1.1) (fun c _ => c.property.1.2.1.le) hlow hhigh
  have hLowBudget : 2*(h : ℝ)*(C/(Real.log X)^4) ≤ (h : ℝ)/16 := by
    calc
      _ = (h : ℝ)*(2*C/(Real.log X)^4) := by ring
      _ ≤ (h : ℝ)*(1/16) := mul_le_mul_of_nonneg_left hbud.low_budget hh
      _ = _ := by ring
  have hHighBudget : 576*X^2*K/(X^(2/3 : ℝ)*Real.sqrt (X^(5/16 : ℝ))) ≤
      (h : ℝ)/16 := by
    dsimp only [K]
    rw [GoldbachOC103.high_coefficient_normalization C X (X^(5/16 : ℝ))
      (X^(2/3 : ℝ)) hV hδ]
    exact hbud.high_budget.trans (div_le_div_of_nonneg_right hlower (by norm_num))
  have hPacketBudget :
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
        (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/8 := by
    linarith
  have hres := hpoint X X (X^(2/3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have hResidualBudget :
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/16 := by
    exact hres.trans (hbud.residual_budget.trans
      (div_le_div_of_nonneg_right hlower (by norm_num)))
  have hnorm : ‖V42 h X‖ ≤
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ +
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ := by
    simpa only [add_sub_cancel_right] using
      norm_sub_le (V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
        (V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X)
  linarith

end Conjectures.Goldbach.DynBlockFirstMass_aux

namespace Conjectures.Goldbach.DynBlockFirstMass_aux

open Finset Filter
open scoped Topology BigOperators Classical

theorem uniform_nat_psi_short_error18 :
    ∃ M : ℕ, ∀ x h : ℕ, M ≤ x →
      (x : ℝ)^(18/25 : ℝ) ≤ (h : ℝ) → h ≤ x →
      |(Chebyshev.psi ((x : ℝ) + (h : ℝ)) - Chebyshev.psi (x : ℝ)) -
        (h : ℝ)| ≤ (h : ℝ)/4 := by
  obtain ⟨X₀, _, hX₀⟩ :=
    actual_principal_window18_of_zero_weights GoldbachOC103.actual_zero_weight_bounds
  obtain ⟨M, hM⟩ := exists_nat_ge X₀
  refine ⟨M, ?_⟩
  intro x h hx hlower hupper
  have hxR : X₀ ≤ (x : ℝ) := hM.trans (by exact_mod_cast hx)
  have he := hX₀ (x : ℝ) hxR h hlower (by exact_mod_cast hupper)
  rw [GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi] at he
  exact he

theorem eventually_sqrt_error18 (C : ℝ) :
    ∀ᶠ z : ℝ in atTop,
      |C| * Real.sqrt (2*z) ≤ z^(18/25 : ℝ)/4 := by
  have hp := GoldbachOC103.eventually_power_log_bound
    (1/2) (18/25) (2*|C|) (1/4) 0 (by norm_num) (by norm_num)
  filter_upwards [hp] with z hz
  have hzp : 0 < z := hz.1
  have hsqrt : Real.sqrt (2*z) ≤ 2*Real.sqrt z := by
    calc
      Real.sqrt (2*z) ≤ Real.sqrt (4*z) := Real.sqrt_le_sqrt (by linarith)
      _ = 2*Real.sqrt z := by
        rw [Real.sqrt_mul (by norm_num)]
        norm_num
  have hpow : (2*|C|)*z^(1/2 : ℝ) ≤ z^(18/25 : ℝ)/4 := by
    convert hz.2 using 1 <;> ring
  calc
    |C| * Real.sqrt (2*z) ≤ |C| * (2*Real.sqrt z) :=
      mul_le_mul_of_nonneg_left hsqrt (abs_nonneg C)
    _ = (2*|C|)*z^(1/2 : ℝ) := by rw [Real.sqrt_eq_rpow]; ring
    _ ≤ z^(18/25 : ℝ)/4 := hpow

theorem uniform_nat_theta_short_floor18 :
    ∃ M : ℕ, ∀ z h : ℕ, M ≤ z →
      (z : ℝ)^(18/25 : ℝ) ≤ (h : ℝ) → h ≤ z →
      (h : ℝ)/2 ≤ Chebyshev.theta ((z : ℝ)+(h : ℝ)) -
        Chebyshev.theta (z : ℝ) := by
  obtain ⟨Mψ, hψ⟩ := uniform_nat_psi_short_error18
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have he := eventually_sqrt_error18 C
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp he
  obtain ⟨M, hM⟩ := exists_nat_ge (max (Mψ : ℝ) Z)
  refine ⟨M, ?_⟩
  intro z h hz hlower hupper
  have hzR : (M : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
  have hzM : max (Mψ : ℝ) Z ≤ (z : ℝ) := hM.trans hzR
  have hzψ : Mψ ≤ z := by
    exact_mod_cast (le_max_left (Mψ : ℝ) Z).trans hzM
  have hzZ : Z ≤ (z : ℝ) := (le_max_right (Mψ : ℝ) Z).trans hzM
  have herr := hψ z h hzψ hlower hupper
  have hpsiLow : (3/4 : ℝ)*(h : ℝ) ≤
      Chebyshev.psi ((z : ℝ)+(h : ℝ)) - Chebyshev.psi (z : ℝ) := by
    have := (abs_le.mp herr).1
    linarith
  have hzp : 0 ≤ (z : ℝ) := Nat.cast_nonneg z
  have hzh : (z : ℝ) + (h : ℝ) ≤ 2*(z : ℝ) := by
    exact_mod_cast (show z+h ≤ 2*z by omega)
  have hsqrt : Real.sqrt ((z : ℝ)+(h : ℝ)) ≤ Real.sqrt (2*(z : ℝ)) :=
    Real.sqrt_le_sqrt hzh
  have hpp0 := hC ((z : ℝ)+(h : ℝ))
  have hpp : Chebyshev.psi ((z : ℝ)+(h : ℝ)) -
      Chebyshev.theta ((z : ℝ)+(h : ℝ)) ≤ (h : ℝ)/4 := by
    calc
      _ ≤ C * Real.sqrt ((z : ℝ)+(h : ℝ)) := hpp0
      _ ≤ |C| * Real.sqrt ((z : ℝ)+(h : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
      _ ≤ |C| * Real.sqrt (2*(z : ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrt (abs_nonneg C)
      _ ≤ (z : ℝ)^(18/25 : ℝ)/4 := hZ (z : ℝ) hzZ
      _ ≤ (h : ℝ)/4 := by gcongr
  have hbase := Chebyshev.theta_le_psi (z : ℝ)
  linarith

theorem prime_card_lower_of_theta
    (z h U : ℕ) (hU : 2 ≤ U) (hupper : z+h ≤ U)
    (htheta : (h : ℝ)/2 ≤ Chebyshev.theta ((z : ℝ)+(h : ℝ)) -
      Chebyshev.theta (z : ℝ)) :
    (h : ℝ)/2 ≤
      (((Finset.Ioc z (z+h)).filter Nat.Prime).card : ℝ) * Real.log (U : ℝ) := by
  let Q := (Finset.Ioc z (z+h)).filter Nat.Prime
  have hsum := GoldbachDyadicBridge.theta_nat_add_sub z h
  rw [hsum] at htheta
  have hlogQ : ∀ p ∈ Q, Real.log (p : ℝ) ≤ Real.log (U : ℝ) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpI := Finset.mem_Ioc.mp hp'.1
    have hpU : p ≤ U := hpI.2.trans hupper
    exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast hpU)
  have hcard :
      (∑ p ∈ Finset.Ioc z (z+h), GoldbachDyadicBridge.primeLog p) ≤
        (Q.card : ℝ) * Real.log (U : ℝ) := by
    calc
      _ = ∑ p ∈ Q, Real.log (p : ℝ) := by
        simp only [GoldbachDyadicBridge.primeLog, Q, Finset.sum_filter]
      _ ≤ ∑ p ∈ Q, Real.log (U : ℝ) := Finset.sum_le_sum hlogQ
      _ = (Q.card : ℝ) * Real.log (U : ℝ) := by simp
  exact htheta.trans hcard

end Conjectures.Goldbach.DynBlockFirstMass_aux

namespace Conjectures.Goldbach.DynBlockFirstMass_aux

open Finset Filter
open scoped Topology BigOperators Classical

def blockWidth (X : ℕ) : ℕ := Nat.sqrt X * Nat.sqrt (Nat.sqrt X)

def middlePrimes (X : ℕ) : Finset ℕ :=
  (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime

def localPrimes (X y p : ℕ) : Finset ℕ :=
  (Finset.Ioc (y-p) (y-p + (blockWidth X - 1))).filter Nat.Prime

theorem sqrt_floor_lower (X : ℕ) (hX : 16 ≤ X) :
    Real.sqrt (X : ℝ)/2 ≤ (Nat.sqrt X : ℝ) := by
  let s := Nat.sqrt X
  have hs4 : 4 ≤ s := by
    exact Nat.le_sqrt.mpr (by omega)
  have hss : s*s ≤ X := Nat.sqrt_le X
  have hsl : X < (s+1)*(s+1) := Nat.lt_succ_sqrt X
  have hs4R : (4 : ℝ) ≤ s := by exact_mod_cast hs4
  have hssR : (s : ℝ)*(s : ℝ) ≤ (X : ℝ) := by exact_mod_cast hss
  have hslR : (X : ℝ) < ((s : ℝ)+1)*((s : ℝ)+1) := by exact_mod_cast hsl
  have hXR : 0 ≤ (X : ℝ) := by exact_mod_cast (by omega : 0 ≤ X)
  have hrr := Real.mul_self_sqrt hXR
  nlinarith

theorem fourth_root_floor_lower (s : ℕ) (hs : 4 ≤ s) :
    Real.sqrt (s : ℝ)/2 ≤ (Nat.sqrt s : ℝ) := by
  let r := Nat.sqrt s
  have hr2 : 2 ≤ r := by
    exact Nat.le_sqrt.mpr hs
  have hrr : r*r ≤ s := Nat.sqrt_le s
  have hsl : s < (r+1)*(r+1) := Nat.lt_succ_sqrt s
  have hr2R : (2 : ℝ) ≤ r := by exact_mod_cast hr2
  have hrrR : (r : ℝ)*(r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrr
  have hslR : (s : ℝ) < ((r : ℝ)+1)*((r : ℝ)+1) := by exact_mod_cast hsl
  have hsR : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  have hroot := Real.mul_self_sqrt hsR
  nlinarith

theorem blockWidth_lower (X : ℕ) (hX : 16 ≤ X) :
    (X : ℝ)^(3/4 : ℝ)/16 ≤ (blockWidth X : ℝ) := by
  let s := Nat.sqrt X
  let r := Nat.sqrt s
  have hs4 : 4 ≤ s := by
    exact Nat.le_sqrt.mpr (by omega)
  have hsLower := sqrt_floor_lower X hX
  have hrLower := fourth_root_floor_lower s hs4
  have hXR : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
  have hsqrtStep : Real.sqrt (Real.sqrt (X : ℝ))/4 ≤
      Real.sqrt (s : ℝ) := by
    have hinside : Real.sqrt (X : ℝ)/16 ≤ (s : ℝ) := by linarith
    calc
      Real.sqrt (Real.sqrt (X : ℝ))/4 =
          Real.sqrt (Real.sqrt (X : ℝ)/16) := by
            rw [Real.sqrt_div (by norm_num)]
            norm_num
      _ ≤ Real.sqrt (s : ℝ) := Real.sqrt_le_sqrt hinside
  have hrTarget : Real.sqrt (Real.sqrt (X : ℝ))/8 ≤ (r : ℝ) := by
    calc
      _ = (Real.sqrt (Real.sqrt (X : ℝ))/4)/2 := by ring
      _ ≤ Real.sqrt (s : ℝ)/2 := by gcongr
      _ ≤ (r : ℝ) := hrLower
  have hprodLower : Real.sqrt (X : ℝ)/2 *
      (Real.sqrt (Real.sqrt (X : ℝ))/8) ≤ (s : ℝ)*(r : ℝ) := by
    exact mul_le_mul hsLower hrTarget (by positivity) (by positivity)
  have hprodEq : Real.sqrt (X : ℝ) *
      Real.sqrt (Real.sqrt (X : ℝ)) = (X : ℝ)^(3/4 : ℝ) := by
    have h1 : Real.sqrt (X : ℝ) = (X : ℝ)^(1/2 : ℝ) := Real.sqrt_eq_rpow _
    have h2 : Real.sqrt (Real.sqrt (X : ℝ)) = (X : ℝ)^(1/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, h1, ← Real.rpow_mul hXR.le]
      norm_num
    rw [h2, h1, ← Real.rpow_add hXR]
    norm_num
  calc
    (X : ℝ)^(3/4 : ℝ)/16 =
        (Real.sqrt (X : ℝ)/2)*(Real.sqrt (Real.sqrt (X : ℝ))/8) := by
          rw [← hprodEq]; ring
    _ ≤ (s : ℝ)*(r : ℝ) := hprodLower
    _ = (blockWidth X : ℝ) := by simp [blockWidth, s, r]

theorem eventually_blockWidth_power :
    ∀ᶠ X : ℕ in atTop,
      2*(2*(X : ℝ))^(18/25 : ℝ) ≤ (blockWidth X : ℝ) := by
  have hp := GoldbachOC103.eventually_power_log_bound
    (18/25) (3/4) (32*(2 : ℝ)^(18/25 : ℝ)) (1/16) 0
    (by norm_num) (by norm_num)
  have hpNat := hp.natCast_atTop
  filter_upwards [hpNat, eventually_ge_atTop (16 : ℕ)] with X hpX hX16
  have hXp : 0 < (X : ℝ) := hpX.1
  have hmul : (2 : ℝ)^(18/25 : ℝ)*(X : ℝ)^(18/25 : ℝ) =
      (2*(X : ℝ))^(18/25 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hXp.le]
  have hcore : 32*(2 : ℝ)^(18/25 : ℝ)*(X : ℝ)^(18/25 : ℝ) ≤
      (X : ℝ)^(3/4 : ℝ) := by
    have h := hpX.2
    norm_num only [pow_zero, mul_one] at h
    have hpow0 : 0 ≤ (X : ℝ)^(3/4 : ℝ) := Real.rpow_nonneg hXp.le _
    nlinarith
  calc
    2*(2*(X : ℝ))^(18/25 : ℝ) =
        (1/16)*(32*(2 : ℝ)^(18/25 : ℝ)*(X : ℝ)^(18/25 : ℝ)) := by
          rw [← hmul]; ring
    _ ≤ (X : ℝ)^(3/4 : ℝ)/16 := by nlinarith
    _ ≤ (blockWidth X : ℝ) := blockWidth_lower X hX16

end Conjectures.Goldbach.DynBlockFirstMass_aux

namespace Conjectures.Goldbach.DynBlockFirstMass_aux

open Finset Filter
open scoped Topology BigOperators Classical

theorem localPrimes_lower
    (M X y p : ℕ)
    (htheta : ∀ z h : ℕ, M ≤ z →
      (z : ℝ)^(18/25 : ℝ) ≤ (h : ℝ) → h ≤ z →
      (h : ℝ)/2 ≤ Chebyshev.theta ((z : ℝ)+(h : ℝ)) -
        Chebyshev.theta (z : ℝ))
    (hX16 : 16 ≤ X) (hX2M : 2*M ≤ X)
    (hscale : 2*(2*(X : ℝ))^(18/25 : ℝ) ≤ (blockWidth X : ℝ))
    (hyX : X ≤ y) (hyW : y + blockWidth X ≤ 2*X)
    (hp : p ∈ middlePrimes X) :
    (blockWidth X : ℝ)/(8*Real.log (X : ℝ)) ≤
      (localPrimes X y p).card := by
  let s := Nat.sqrt X
  let r := Nat.sqrt s
  let W := blockWidth X
  let z := y-p
  let h := W-1
  have hs4 : 4 ≤ s := by
    exact Nat.le_sqrt.mpr (by omega)
  have hr2 : 2 ≤ r := by
    exact Nat.le_sqrt.mpr hs4
  have hrr : r*r ≤ s := Nat.sqrt_le s
  have h2r : 2*r ≤ s := by nlinarith
  have hss : s*s ≤ X := Nat.sqrt_le X
  have h2W : 2*W ≤ X := by
    dsimp [W, blockWidth, s, r]
    calc
      2*(Nat.sqrt X * Nat.sqrt (Nat.sqrt X)) =
          Nat.sqrt X * (2*Nat.sqrt (Nat.sqrt X)) := by ring
      _ ≤ Nat.sqrt X * Nat.sqrt X := Nat.mul_le_mul_left _ h2r
      _ ≤ X := hss
  have h4s : 4*s ≤ X := by nlinarith
  have hWplus : W+2*s ≤ X := by omega
  have hp' := Finset.mem_filter.mp hp
  have hpI := Finset.mem_Icc.mp hp'.1
  have hpUpper : p ≤ 2*s := hpI.2
  have hzW : W ≤ z := by
    dsimp [z]
    omega
  have hzHalf : X/2 ≤ z := by
    dsimp [z]
    omega
  have hzM : M ≤ z := by omega
  have hW2 : 2 ≤ W := by
    have hmul : 4*2 ≤ s*r := Nat.mul_le_mul hs4 hr2
    have hmulW : 4*2 ≤ W := by simpa [W, blockWidth, s, r] using hmul
    omega
  have hhW : W/2 ≤ h := by dsimp [h]; omega
  have hhz : h ≤ z := by dsimp [h]; omega
  have hz2X : z ≤ 2*X := by
    dsimp [z]
    omega
  have hz0R : 0 ≤ (z : ℝ) := Nat.cast_nonneg z
  have hz2XR : (z : ℝ) ≤ 2*(X : ℝ) := by exact_mod_cast hz2X
  have hzPower : (z : ℝ)^(18/25 : ℝ) ≤
      (2*(X : ℝ))^(18/25 : ℝ) :=
    Real.rpow_le_rpow hz0R hz2XR (by norm_num)
  have hWR : 0 ≤ (W : ℝ) := Nat.cast_nonneg W
  have hhWR : (W : ℝ)/2 ≤ (h : ℝ) := by
    have hnat : W ≤ 2*h := by dsimp [h]; omega
    have hreal : (W : ℝ) ≤ 2*(h : ℝ) := by exact_mod_cast hnat
    linarith
  have hhLower : (z : ℝ)^(18/25 : ℝ) ≤ (h : ℝ) := by
    calc
      _ ≤ (2*(X : ℝ))^(18/25 : ℝ) := hzPower
      _ ≤ (W : ℝ)/2 := by linarith
      _ ≤ (h : ℝ) := hhWR
  have hzUpper : z+h ≤ 2*X := by
    dsimp [z, h]
    omega
  have htheta' := htheta z h hzM hhLower hhz
  have hcard := prime_card_lower_of_theta z h (2*X) (by omega) hzUpper htheta'
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hlog2X : Real.log (2*(X : ℝ)) ≤ 2*Real.log (X : ℝ) := by
    have hXp : 0 < (X : ℝ) := by exact_mod_cast (by omega : 0 < X)
    rw [Real.log_mul (by norm_num) (ne_of_gt hXp)]
    have hlog2 : Real.log 2 ≤ Real.log (X : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : (2 : ℕ) ≤ X))
    linarith
  have hQ0 : (0 : ℝ) ≤ (localPrimes X y p).card := Nat.cast_nonneg _
  change (W : ℝ)/(8*Real.log (X : ℝ)) ≤ (localPrimes X y p).card
  push_cast at hcard
  change (h : ℝ)/2 ≤ (localPrimes X y p).card * Real.log (2*(X : ℝ)) at hcard
  have hcard' := hcard.trans (mul_le_mul_of_nonneg_left hlog2X hQ0)
  apply (div_le_iff₀ (by positivity : 0 < 8*Real.log (X : ℝ))).2
  nlinarith

theorem middlePrimes_lower
    (M X : ℕ)
    (htheta : ∀ z h : ℕ, M ≤ z →
      (z : ℝ)^(18/25 : ℝ) ≤ (h : ℝ) → h ≤ z →
      (h : ℝ)/2 ≤ Chebyshev.theta ((z : ℝ)+(h : ℝ)) -
        Chebyshev.theta (z : ℝ))
    (hX16 : 16 ≤ X) (hMsq : M*M ≤ X) :
    Real.sqrt (X : ℝ)/(4*Real.log (X : ℝ)) ≤ (middlePrimes X).card := by
  let s := Nat.sqrt X
  have hsM : M ≤ s := Nat.le_sqrt.mpr hMsq
  have hs4 : 4 ≤ s := Nat.le_sqrt.mpr (by omega)
  have hss : s*s ≤ X := Nat.sqrt_le X
  have h2s : 2*s ≤ X := by nlinarith
  have hs1R : (1 : ℝ) ≤ s := by exact_mod_cast (by omega : 1 ≤ s)
  have hsPower : (s : ℝ)^(18/25 : ℝ) ≤ (s : ℝ) := by
    calc
      _ ≤ (s : ℝ)^(1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hs1R (by norm_num)
      _ = (s : ℝ) := Real.rpow_one _
  have htheta' := htheta s s hsM hsPower le_rfl
  have hcard := prime_card_lower_of_theta s s X (by omega) (by omega) htheta'
  let P0 := (Finset.Ioc s (s+s)).filter Nat.Prime
  have hsub : P0 ⊆ middlePrimes X := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqI := Finset.mem_Ioc.mp hq'.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hq'.2⟩
  have hcardP : (P0.card : ℝ) ≤ (middlePrimes X).card := by
    exact_mod_cast Finset.card_le_card hsub
  have hroot := sqrt_floor_lower X hX16
  have hL : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  apply (div_le_iff₀ (by positivity : 0 < 4*Real.log (X : ℝ))).2
  have hmul := mul_le_mul_of_nonneg_right hcardP hL.le
  change (s : ℝ)/2 ≤ (P0.card : ℝ)*Real.log (X : ℝ) at hcard
  nlinarith

end Conjectures.Goldbach.DynBlockFirstMass_aux

namespace Conjectures.Goldbach.DynBlockFirstMass_aux

open Finset Filter
open scoped Topology BigOperators Classical

def evenRange (X : ℕ) : Finset ℕ :=
  (Finset.Icc X (2*X)).filter (fun n => Even n)

def arrivals (X n : ℕ) : ℕ :=
  ((middlePrimes X).filter
    (fun p => p ≤ n ∧ Nat.Prime (n-p))).card

def targetBlock (X y : ℕ) : Finset ℕ :=
  (evenRange X).filter (fun n => y ≤ n ∧ n < y + blockWidth X)

private theorem localPrimes_card_le_arrivals
    (X y p : ℕ) (hX : 16 ≤ X) (hy : X ≤ y)
    (hyW : y + blockWidth X ≤ 2*X) (hp : p ∈ middlePrimes X) :
    (localPrimes X y p).card ≤
      ((targetBlock X y).filter
        (fun n => p ≤ n ∧ Nat.Prime (n-p))).card := by
  have hp' := Finset.mem_filter.mp hp
  have hpI := Finset.mem_Icc.mp hp'.1
  have hpPrime := hp'.2
  let s := Nat.sqrt X
  have hs4 : 4 ≤ s := Nat.le_sqrt.mpr (by omega)
  have hss : s*s ≤ X := Nat.sqrt_le X
  have h4s : 4*s ≤ X := by nlinarith
  have hpX : p ≤ X := by omega
  have hpy : p ≤ y := hpX.trans hy
  have hpTwo : p ≠ 2 := by omega
  have hpOdd : Odd p := hpPrime.odd_of_ne_two hpTwo
  refine Finset.card_le_card_of_injOn (fun q => p+q) ?_ ?_
  · intro q hq
    have hq' := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
    have hqI := Finset.mem_Ioc.mp hq'.1
    have hqPrime := hq'.2
    have hqThree : 3 ≤ q := by omega
    have hqTwo : q ≠ 2 := by omega
    have hqOdd : Odd q := hqPrime.odd_of_ne_two hqTwo
    have hnLower : X ≤ p+q := by omega
    have hnUpper : p+q ≤ 2*X := by omega
    have hnEven : Even (p+q) := hpOdd.add_odd hqOdd
    have hnE : p+q ∈ evenRange X := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hnLower, hnUpper⟩, hnEven⟩
    have hnB : p+q ∈ targetBlock X y := by
      exact Finset.mem_filter.mpr ⟨hnE, by omega⟩
    have hpq : p ≤ p+q := Nat.le_add_right p q
    have hsub : p+q-p = q := by omega
    exact Finset.mem_coe.mpr
      (Finset.mem_filter.mpr ⟨hnB, hpq, by simpa [hsub] using hqPrime⟩)
  · intro q₁ _ q₂ _ h
    exact Nat.add_left_cancel h

private theorem sum_arrivals_eq_sum_primes (X y : ℕ) :
    ∑ n ∈ targetBlock X y, arrivals X n =
      ∑ p ∈ middlePrimes X,
        ((targetBlock X y).filter
          (fun n => p ≤ n ∧ Nat.Prime (n-p))).card := by
  simp only [arrivals, Finset.card_filter]
  rw [Finset.sum_comm]

theorem sum_localPrimes_le_arrivals
    (X y : ℕ) (hX : 16 ≤ X) (hy : X ≤ y)
    (hyW : y + blockWidth X ≤ 2*X) :
    ∑ p ∈ middlePrimes X, (localPrimes X y p).card ≤
      ∑ n ∈ targetBlock X y, arrivals X n := by
  rw [sum_arrivals_eq_sum_primes]
  refine Finset.sum_le_sum (s := middlePrimes X) (fun p hp => ?_)
  exact localPrimes_card_le_arrivals X y p hX hy hyW hp

end Conjectures.Goldbach.DynBlockFirstMass_aux

namespace Conjectures.Goldbach.DynBlockFirstMass_aux

open Finset Filter
open scoped Topology BigOperators Classical

theorem main_ineq :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ,
      X ≤ y → y + blockWidth X ≤ 2*X →
      c*(blockWidth X : ℝ)*(Real.sqrt (X : ℝ)/(Real.log (X : ℝ))^2) ≤
        ∑ n ∈ targetBlock X y, (arrivals X n : ℝ) := by
  obtain ⟨M, htheta⟩ := uniform_nat_theta_short_floor18
  obtain ⟨N, hN⟩ := eventually_atTop.mp eventually_blockWidth_power
  let X₀ := max (max N 16) (max (2*M) (M*M))
  refine ⟨1/40, by norm_num, X₀, ?_⟩
  intro X hX y hy hyW
  have hXN : N ≤ X := (le_max_left N 16).trans
    ((le_max_left (max N 16) (max (2*M) (M*M))).trans hX)
  have hX16 : 16 ≤ X := (le_max_right N 16).trans
    ((le_max_left (max N 16) (max (2*M) (M*M))).trans hX)
  have hX2M : 2*M ≤ X := (le_max_left (2*M) (M*M)).trans
    ((le_max_right (max N 16) (max (2*M) (M*M))).trans hX)
  have hMsq : M*M ≤ X := (le_max_right (2*M) (M*M)).trans
    ((le_max_right (max N 16) (max (2*M) (M*M))).trans hX)
  have hscale := hN X hXN
  have hP := middlePrimes_lower M X htheta hX16 hMsq
  have hsumNat := sum_localPrimes_le_arrivals X y hX16 hy hyW
  have hsum : Finset.sum (middlePrimes X)
      (fun p => ((localPrimes X y p).card : ℝ)) ≤
      Finset.sum (targetBlock X y) (fun n => (arrivals X n : ℝ)) := by
    calc
      _ = ((∑ p ∈ middlePrimes X, (localPrimes X y p).card : ℕ) : ℝ) := by norm_cast
      _ ≤ ((∑ n ∈ targetBlock X y, arrivals X n : ℕ) : ℝ) := by exact_mod_cast hsumNat
      _ = _ := by norm_cast
  let L := Real.log (X : ℝ)
  let W := blockWidth X
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hlocal : ∀ p ∈ middlePrimes X,
      (W : ℝ)/(8*L) ≤ (localPrimes X y p).card := by
    intro p hp
    exact localPrimes_lower M X y p htheta hX16 hX2M hscale hy hyW hp
  have hsumLocal :
      ((middlePrimes X).card : ℝ) * ((W : ℝ)/(8*L)) ≤
        Finset.sum (middlePrimes X)
          (fun p => ((localPrimes X y p).card : ℝ)) := by
    calc
      _ = Finset.sum (middlePrimes X) (fun _ => ((W : ℝ)/(8*L))) := by simp
      _ ≤ _ := by
        refine Finset.sum_le_sum fun p hp => hlocal p hp
  have hP' : Real.sqrt (X : ℝ)/(4*L) ≤ (middlePrimes X).card := by
    simpa [L] using hP
  have hprod :
      Real.sqrt (X : ℝ)/(4*L) * ((W : ℝ)/(8*L)) ≤
        Finset.sum (middlePrimes X)
          (fun p => ((localPrimes X y p).card : ℝ)) := by
    exact (mul_le_mul_of_nonneg_right hP' (by positivity)).trans hsumLocal
  have hWR : 0 ≤ (W : ℝ) := Nat.cast_nonneg W
  have hroot : 0 ≤ Real.sqrt (X : ℝ) := Real.sqrt_nonneg _
  have hcoeff :
      (1/40 : ℝ)*(W : ℝ)*(Real.sqrt (X : ℝ)/L^2) ≤
        Real.sqrt (X : ℝ)/(4*L) * ((W : ℝ)/(8*L)) := by
    field_simp [ne_of_gt hL]
    nlinarith [mul_nonneg hWR hroot]
  have hmain := hcoeff.trans (hprod.trans hsum)
  simpa [W, L] using hmain

end Conjectures.Goldbach.DynBlockFirstMass_aux

theorem Conjectures.Goldbach.DynBlockFirstMass :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) := by
  intro E P H W B M
  exact Conjectures.Goldbach.DynBlockFirstMass_aux.main_ineq
