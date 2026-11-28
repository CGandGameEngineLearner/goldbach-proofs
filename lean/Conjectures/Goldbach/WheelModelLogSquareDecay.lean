import Mathlib
import Conjectures.Goldbach.PacketWheelMinorLeakage
import Conjectures.Goldbach.PacketShortWheelError
import Conjectures.Goldbach.PacketLagEnergyIdentity
import Conjectures.Goldbach.PacketProgressionLeakage

/- The grid-envelope and short-mask estimates use the verified wheel and mask
   modules imported above. The finite residue lift follows WaterKing201030's
   Apache-2.0 proof in Refute77da5b6d927d911e39958318 (#4136). -/
open MeasureTheory
open Conjectures.Goldbach.PacketShortWheelError_aux

namespace QuantitativeWheelCorrelation
noncomputable section

abbrev WQ := Conjectures.Goldbach.PacketWheelMinorLeakage_aux.gridQ
abbrev WA := Conjectures.Goldbach.PacketWheelMinorLeakage_aux.arcs
abbrev spec := Conjectures.Goldbach.PacketWheelMinorLeakage_aux.spec
def scale (n : ℕ) := (n:ℝ)/(Real.log (n:ℝ))^2
def energy (n : ℕ) (a : ℕ → ℝ) :=
  ∫ t in (0:ℝ)..1, (GoldbachPacket.resonant n).indicator (fun u => ‖spec n a u‖^2) t
def long (n : ℕ) (a : ℕ → ℝ) :=
  2*∑ h ∈ Finset.Icc ((GoldbachPacket.length n)^2+1) n,
      GoldbachPacket.correlation n h a * GoldbachPacket.cosineMoment n h

theorem energy_eq (n : ℕ) (a : ℕ → ℝ) :
    energy n a = GoldbachPacket.shortPart n a + long n a :=
  Conjectures.Goldbach.PacketLagEnergyIdentity n a

theorem energy_nonneg (n : ℕ) (a : ℕ → ℝ) : 0 ≤ energy n a :=
  intervalIntegral.integral_nonneg (by norm_num)
    (fun t _ => Set.indicator_nonneg (fun x _ => sq_nonneg _) t)

theorem grid_scale {n : ℕ} (hn : 64 ≤ n) :
    30 ≤ WQ n ∧ (n:ℝ)/(WQ n:ℝ) ≤ 4*scale n := by
  let v := Nat.log 2 (n+2)
  have hv : 6 ≤ v := Nat.le_log_of_pow_le (by decide) (by change 64 ≤ n+2; omega)
  have hQ : WQ n = v^2 := rfl
  have hN : (n:ℝ) < (2:ℝ)^(v+1) := by
    exact_mod_cast (show n < 2^(v+1) from
      lt_of_le_of_lt (by omega : n ≤ n+2) (Nat.lt_pow_succ_log_self (by decide) (n+2)))
  have hl : Real.log (n:ℝ) ≤ 2*(v:ℝ) := by
    have upper := Real.log_le_log (by exact_mod_cast (by omega : 0<n)) hN.le
    rw [Real.log_pow] at upper
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have u := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (v+1) (α:=ℝ))
    push_cast at upper u
    have v' : (6:ℝ) ≤ v := by exact_mod_cast hv
    linarith
  have hlpos := Real.log_pos (by exact_mod_cast (by omega : 1<n) : (1:ℝ)<n)
  have hsq := pow_le_pow_left₀ hlpos.le hl 2
  have hden : (Real.log (n:ℝ))^2/4 ≤ (WQ n:ℝ) := by
    rw [hQ, Nat.cast_pow]
    linarith
  refine ⟨by rw [hQ]; nlinarith, ?_⟩
  calc
    _ ≤ (n:ℝ)/((Real.log (n:ℝ))^2/4) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hden
    _ = 4*scale n := by unfold scale; ring

theorem mask_measurable (n : ℕ) : MeasurableSet (GoldbachPacket.resonant n) := by
  have hc : Continuous (fun t => GoldbachPacket.packet (GoldbachPacket.length n) t /
      (GoldbachPacket.length n:ℝ)) := by unfold GoldbachPacket.packet; fun_prop
  exact (GoldbachBudget.measurableArcs n).compl.inter
    (isOpen_lt (continuous_const : Continuous (fun _ : ℝ => (1:ℝ)/2)) hc).measurableSet

theorem compare_masks {n : ℕ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg₀ : ∀ t, 0 ≤ g t) (hle : ∀ t, f t ≤ g t) :
    (∫ t in (0:ℝ)..1, (GoldbachPacket.resonant n).indicator f t) ≤
    ∫ t in (0:ℝ)..1, (WA n)ᶜ.indicator g t := by
  have integ {s : Set ℝ} {u : ℝ → ℝ} (hs : MeasurableSet s) (hu : Continuous u) :
      IntervalIntegrable (s.indicator u) volume (0:ℝ) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact hu.integrableOn_Icc.indicator hs
  apply intervalIntegral.integral_mono_on zero_le_one (integ (mask_measurable n) hf)
    (integ (Conjectures.Goldbach.PacketWheelMinorLeakage_aux.measurableArcs n).compl hg)
  intro t _
  by_cases ht : t ∈ GoldbachPacket.resonant n
  · have hm : t ∈ (WA n)ᶜ := ht.1
    simpa only [Set.indicator_of_mem ht, Set.indicator_of_mem hm] using hle t
  · rw [Set.indicator_of_notMem ht]
    exact Set.indicator_nonneg (fun x _ => hg₀ x) t

theorem short_scale : ∃ N : ℕ, ∀ n ≥ N, ∀ a : ℕ → ℝ, (∀ k ≤ n, |a k| ≤ 4) →
    |GoldbachPacket.shortPart n a| ≤ 288*scale n := by
  obtain ⟨N, hN⟩ := GoldbachPacket.maskLogDecay 6 1 zero_lt_one
  refine ⟨max 2 N, ?_⟩
  intro n hn a ha
  have two : 2 ≤ n := (le_max_left ..).trans hn
  have hl : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1<n))
  have u := GoldbachPacket.shortAtLogScale n (by omega) a
    (fun k hk => (ha k hk).trans (by linarith))
  have mass := hN n ((le_max_right ..).trans hn)
  rw [← GoldbachPacket.zeroMoment] at mass
  have nn : 0 ≤ GoldbachPacket.cosineMoment n 0 := by
    rw [GoldbachPacket.zeroMoment]
    exact intervalIntegral.integral_nonneg zero_le_one (fun t _ =>
      Set.indicator_nonneg (fun _ _ => zero_le_one) t)
  let z := 1+Real.log (n:ℝ)
  have scales : (Real.log (n:ℝ))^2 ≤ z^2 := by
    apply pow_le_pow_left₀ hl.le _ 2
    dsimp [z]; linarith
  change z^6 * _ ≤ 1 at mass
  change _ ≤ 288*(n:ℝ)*z^4*GoldbachPacket.cosineMoment n 0 at u
  unfold scale
  rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos hl)]
  calc
    _ ≤ (288*(n:ℝ)*z^4*GoldbachPacket.cosineMoment n 0)*z^2 :=
      mul_le_mul u scales (sq_nonneg _) (by dsimp [z]; positivity)
    _ = (288*(n:ℝ))*(z^6*GoldbachPacket.cosineMoment n 0) := by ring
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left mass (by positivity : 0 ≤ 288*(n:ℝ))

open Conjectures.Goldbach.PacketWheelMinorLeakage_aux in
theorem wheel_energy {n : ℕ} (hn : 64 ≤ n) :
    energy n GoldbachPacket.wheel ≤ (3616*1860*Real.pi*4)*scale n := by
  obtain ⟨hq,hscale⟩ := grid_scale hn
  have hs : Continuous (fun t => ‖QuantitativeWheelCorrelation.spec n wheel t‖^2) := by
    unfold QuantitativeWheelCorrelation.spec Conjectures.Goldbach.PacketWheelMinorLeakage_aux.spec phase; fun_prop
  have hg : Continuous (gridEnvelope n) := by
    unfold gridEnvelope gridDistance phase
    fun_prop (disch := intro t; positivity)
  have cmp := compare_masks (n:=n) hs (continuous_const.mul hg)
    (fun t => by dsimp [gridEnvelope]; positivity) (wheelEnvelope n)
  change energy n GoldbachPacket.wheel ≤ ∫ t in (0:ℝ)..1, (WA n)ᶜ.indicator
      (fun u => 3616*gridEnvelope n u) t at cmp
  have pull : (WA n)ᶜ.indicator (fun u => 3616*gridEnvelope n u) =
      fun t => 3616*((WA n)ᶜ.indicator (gridEnvelope n) t) := by
    funext t
    by_cases h : t ∈ (WA n)ᶜ <;> simp [Set.indicator, h]
  rw [pull, intervalIntegral.integral_const_mul] at cmp
  have grid := gridTailQuantitative n (by omega) hq
  rw [mul_div_assoc] at grid
  have grid' := grid.trans (mul_le_mul_of_nonneg_left hscale (by positivity))
  linarith only [cmp, mul_le_mul_of_nonneg_left grid' (by norm_num : (0:ℝ)≤3616)]

theorem wheel_long :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n ≥ N, |long n GoldbachPacket.wheel| ≤ C*scale n := by
  obtain ⟨N,hs⟩ := short_scale
  refine ⟨3616*1860*Real.pi*4+288, by positivity, max 64 N, ?_⟩
  intro n hn
  have sh := hs n ((le_max_right ..).trans hn) GoldbachPacket.wheel (by
    intro k hk; unfold GoldbachPacket.wheel; split <;> norm_num)
  have lo := energy_nonneg n GoldbachPacket.wheel
  have hi := wheel_energy ((le_max_left ..).trans hn)
  have E := energy_eq n GoldbachPacket.wheel
  have t₀ : 0 ≤ (3616*1860*Real.pi*4)*scale n := by unfold scale; positivity
  rw [abs_le] at sh ⊢
  constructor <;> linarith [sh.1,sh.2]


open Conjectures.Goldbach.PacketProgressionLeakage_aux
open Conjectures.Goldbach.PacketWheelMinorLeakage_aux (phase)

def row (n d r k : ℕ) : ℝ := if k < n ∧ k%d=r then 1 else 0

theorem row_packet {n d r : ℕ} (hd : 0<d) (hr : r<d) (hrn : r<n) (t : ℝ) :
    ‖spec n (row n d r) t‖ = ‖Pf d ((n-1-r)/d+1) t‖ := by
  let M := (n-1-r)/d+1
  let z := Ef ((d:ℝ)*t)
  let F := (Finset.range (n+1)).filter (fun k => k<n ∧ k%d=r)
  have hz : ‖z‖ = 1 := Ef_norm _
  have bound (j : ℕ) : j < M ↔ r+d*j<n := by
    dsimp [M]
    rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd, Nat.mul_comm j d]
    omega
  have addE (x y : ℝ) : Ef (x+y) = Ef x * Ef y := by
    unfold Ef
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  have power (j : ℕ) : Ef ((d:ℝ)*(j:ℝ)*t) = z^j := by
    dsimp [z,Ef]
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have expr : spec n (row n d r) t = Ef ((r:ℝ)*t) * ∑ j ∈ Finset.range M, z^j := by
    calc
      _ = ∑ k ∈ F, Ef ((k:ℝ)*t) := by
        unfold spec Conjectures.Goldbach.PacketWheelMinorLeakage_aux.spec
        dsimp [F]
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro k _
        by_cases h : k<n ∧ k%d=r <;> simp [row,h,Ef,phase]
      _ = ∑ j ∈ Finset.range M, Ef ((r:ℝ)*t) * z^j := by
        apply Finset.sum_nbij' (fun k : ℕ => k / d) (fun j : ℕ => r+d*j)
        · intro k hk
          obtain ⟨_,hk,heq⟩ := Finset.mem_filter.mp hk
          have eq := Nat.mod_add_div k d
          rw [heq] at eq
          exact Finset.mem_range.mpr ((bound _).mpr (eq.symm ▸ hk))
        · intro j hj
          have lt := (bound j).mp (Finset.mem_range.mp hj)
          refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), lt, ?_⟩
          simp [Nat.add_mod, Nat.mod_eq_of_lt hr]
        · intro k hk
          have heq := (Finset.mem_filter.mp hk).2.2
          rw [← heq]
          exact Nat.mod_add_div k d
        · intro j _
          simp [Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr]
        · intro k hk
          obtain ⟨_,_,heq⟩ := Finset.mem_filter.mp hk
          have eq := Nat.mod_add_div k d
          rw [heq] at eq
          have er : (r:ℝ)+(d:ℝ)*((k/d:ℕ):ℝ) = k := by exact_mod_cast eq
          rw [← power, ← addE]
          congr 1
          linear_combination -t * er
      _ = _ := (Finset.mul_sum ..).symm
  have shift : Pf d M t = (∑ j ∈ Finset.range M, z^j)*z := by
    simp only [Pf,z,pow_succ, Finset.sum_mul]
  change _ = ‖Pf d M t‖
  rw [expr,shift,norm_mul,norm_mul,Ef_norm,hz,one_mul,mul_one]

theorem row_energy {n d r : ℕ} (hn : 64 ≤ n) (hd : 0<d) (hd30 : d ∣ 30) (hr : r<d) :
    energy n (row n d r) ≤ (8*Real.pi)*scale n := by
  have dl : d ≤ 30 := Nat.le_of_dvd (by decide) hd30
  let M := (n-1-r)/d+1
  have eq (t : ℝ) := row_packet hd hr (by omega : r<n) t
  have sp : Continuous (fun t => ‖spec n (row n d r) t‖^2) := by
    unfold spec Conjectures.Goldbach.PacketWheelMinorLeakage_aux.spec phase
    fun_prop
  have cmp := compare_masks (n:=n) sp (Pf_cont d M) (fun _ => sq_nonneg _)
    (fun t => le_of_eq (congrArg (fun u : ℝ => u^2) (eq t)))
  have budget := main_bound n d M (by omega) hd (dl.trans (grid_scale hn).1)
  change energy n (row n d r) ≤ _ at cmp
  have goal := cmp.trans budget
  rw [mul_div_assoc] at goal
  have final := goal.trans (mul_le_mul_of_nonneg_left (grid_scale hn).2 (by positivity))
  linarith only [final]

theorem residue_long :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ, d ∣ 30 →
    |∑ r ∈ Finset.range d, long n (row n d r)| ≤ (d:ℝ)*(C*scale n) := by
  obtain ⟨N,hs⟩ := short_scale
  refine ⟨8*Real.pi+288, by positivity, max 64 N, ?_⟩
  intro n hn d hd
  have dp : 0<d := Nat.pos_of_dvd_of_pos hd (by decide)
  have single (r : ℕ) (hr : r ∈ Finset.range d) :
      |long n (row n d r)| ≤ (8*Real.pi+288)*scale n := by
    have sh := hs n ((le_max_right ..).trans hn) (row n d r) (by
      intro k _; unfold row; split <;> norm_num)
    have en := row_energy ((le_max_left ..).trans hn) dp hd (Finset.mem_range.mp hr)
    have nn := energy_nonneg n (row n d r)
    have id := energy_eq n (row n d r)
    have t₀ : 0 ≤ 8*Real.pi*scale n := by unfold scale; positivity
    rw [abs_le] at sh ⊢
    constructor <;> linarith [sh.1,sh.2]
  calc
    _ ≤ ∑ r ∈ Finset.range d, |long n (row n d r)| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _r ∈ Finset.range d, (8*Real.pi+288)*scale n := Finset.sum_le_sum single
    _ = _ := by simp

end
end QuantitativeWheelCorrelation

namespace QuantitativeWheelProfile
open Finset

private def corr (n h : ℕ) (a : ℕ → ℝ) :=
  ∑ k ∈ Finset.range (n+1-h), a k*a (k+h)

def resWeight (n d r k : ℕ) : ℝ :=
  if k < n ∧ k % d = r then 1 else 0

private theorem residue_pair_sum (n d h k : ℕ) (hd : 0 < d) :
    (∑ r ∈ Finset.range d, resWeight n d r k * resWeight n d r (k+h)) =
      if k+h < n ∧ d ∣ h then (1:ℝ) else 0 := by
  by_cases hk : k+h < n
  · have hk' : k < n := by omega
    have hkd : k % d ∈ Finset.range d := Finset.mem_range.mpr (Nat.mod_lt _ hd)
    have hkd' : (k+h) % d ∈ Finset.range d := Finset.mem_range.mpr (Nat.mod_lt _ hd)
    have hmod : k % d = (k+h) % d ↔ d ∣ h := by
      simpa only [Nat.ModEq] using (Nat.left_modEq_add_iff : k ≡ k+h [MOD d] ↔ d ∣ h)
    simp [resWeight, hk, hk', hkd', hmod]
  · simp [resWeight, hk]

theorem sum_autocorr (n d h : ℕ) (hd : 0 < d) (hh : h ≤ n) :
    (∑ r ∈ Finset.range d, corr n h (resWeight n d r)) =
      if d ∣ h then (n:ℝ)-h else 0 := by
  simp only [corr]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (by
    intro k hk
    exact residue_pair_sum n d h k hd)]
  by_cases dh : d ∣ h
  · simp only [dh, and_true, ite_true]
    have hiff (k : ℕ) : k+h < n ↔ k < n-h := by omega
    simp_rw [hiff]
    calc
      (∑ k ∈ Finset.range (n+1-h), if k < n-h then (1:ℝ) else 0) =
          ∑ k ∈ (Finset.range (n+1-h)).filter (· < n-h), (1:ℝ) := by
        rw [Finset.sum_filter]
      _ = ∑ k ∈ Finset.range (n-h), (1:ℝ) := by
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
      _ = (n:ℝ)-h := by simp [Nat.cast_sub hh]
  · simp [dh]

private theorem lift (n d : ℕ) (hd : 0 < d) (H : Finset ℕ) (v : ℕ → ℝ)
    (hn : ∀ h ∈ H, h ≤ n) :
    (∑ r ∈ Finset.range d, 2*∑ h ∈ H, corr n h (resWeight n d r) * v h) =
      2*∑ h ∈ H, (if d ∣ h then (n:ℝ)-h else 0) * v h := by
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.sum_mul, sum_autocorr n d h hd (hn h hh)]

end QuantitativeWheelProfile

open QuantitativeWheelProfile in
private theorem weighted_profile :
(by
  classical
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let rho : ℕ → ℝ := fun h => (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) * (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))
  exact ∀ (n : ℕ) (H : Finset ℕ) (v : ℕ → ℝ), (∀ h ∈ H, h ≤ n) →
    let R := fun d : ℕ => ∑ r ∈ Finset.range d, 2*∑ h ∈ H,
      A n h (fun k => if k<n ∧ k%d=r then 1 else 0) * v h
    2*(∑ h ∈ H, (((n:ℝ)-h)*((15:ℝ)/32)*rho h)*v h) =
      (15/32:ℝ)*(3*R 1+3*R 3+R 5+R 15)) := by
  classical
  intro _ _ n H v hh
  let R := fun d : ℕ => ∑ r ∈ Finset.range d, 2*∑ h ∈ H, corr n h (resWeight n d r)*v h
  let p := fun h : ℕ => (2:ℝ)^(if 3∣h then 1 else 0 : ℕ) *
    (3*(if 5∣h then 0 else 1)+4*(if 5∣h then 1 else 0))
  change 2*(∑ h ∈ H, (((n:ℝ)-h)*(15/32)*p h)*v h) =
    (15/32)*(3*R 1+3*R 3+R 5+R 15)
  dsimp only [R]
  rw [lift n 1 (by decide) H v hh, lift n 3 (by decide) H v hh,
    lift n 5 (by decide) H v hh, lift n 15 (by decide) H v hh]
  simp only [one_dvd, ite_true, mul_add, Finset.mul_sum, ←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h _
  have hd : 15∣h ↔ 3∣h ∧ 5∣h := by omega
  by_cases h3 : 3∣h <;> by_cases h5 : 5∣h <;> simp [p,hd,h3,h5] <;> ring

private theorem combined_wheel_bounds
    (h₁ : by
  classical
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let model : ℕ → ℝ := fun k => if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0
  let J := fun (n : ℕ) (a : ℕ → ℝ) => 2*∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h
  exact ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n ≥ N, |J n model| ≤ C*((n:ℝ)/(Real.log (n:ℝ))^2))
    (h₂ : by
  classical
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let J := fun (n : ℕ) (a : ℕ → ℝ) => 2*∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h
  let D := fun n d : ℕ => ∑ r ∈ Finset.range d, J n (fun k => if k<n ∧ k%d=r then 1 else 0)
  exact ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ d : ℕ, d ∣ 30 → |D n d| ≤ (d:ℝ)*(C*((n:ℝ)/(Real.log (n:ℝ))^2)))
    (h₃ : by
  classical
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let rho : ℕ → ℝ := fun h => (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) * (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))
  exact ∀ (n : ℕ) (H : Finset ℕ) (v : ℕ → ℝ), (∀ h ∈ H, h ≤ n) →
    let R := fun d : ℕ => ∑ r ∈ Finset.range d, 2*∑ h ∈ H,
      A n h (fun k => if k<n ∧ k%d=r then 1 else 0) * v h
    2*(∑ h ∈ H, (((n:ℝ)-h)*((15:ℝ)/32)*rho h)*v h) =
      (15/32:ℝ)*(3*R 1+3*R 3+R 5+R 15)) :
(by
  classical
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let model : ℕ → ℝ := fun k => if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0
  let rho : ℕ → ℝ := fun h => (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) * (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))
  let Q : ℕ → ℝ := fun n => 2 * (∑ h ∈ Finset.Icc ((L n) ^ 2 + 1) n, ((n - h : ℝ) * ((15 : ℝ) / 32) * rho h - A n h model) * V n h)
  exact ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → Even n → |Q n| ≤ C * (n : ℝ) / (Real.log (n : ℝ))^2) := by
  classical
  obtain ⟨a,ha,A₀,hA⟩ := h₁
  obtain ⟨b,hb,B₀,hB⟩ := h₂
  refine ⟨a+15*b, by positivity, max 2 (max A₀ B₀), le_max_left .., ?_⟩
  intro n hn _
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let model : ℕ → ℝ := fun k => if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0
  let rho : ℕ → ℝ := fun h => (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) * (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))
  let Q : ℕ → ℝ := fun n => 2 * (∑ h ∈ Finset.Icc ((L n) ^ 2 + 1) n, ((n - h : ℝ) * ((15 : ℝ) / 32) * rho h - A n h model) * V n h)
  let J := fun (n : ℕ) (a : ℕ → ℝ) => 2*∑ h ∈ Finset.Icc ((L n)^2+1) n, A n h a * V n h
  let D := fun n d : ℕ => ∑ r ∈ Finset.range d, J n (fun k => if k<n ∧ k%d=r then 1 else 0)
  let t := ((n:ℝ)/(Real.log (n:ℝ))^2)
  have na : A₀ ≤ n := by omega
  have nb : B₀ ≤ n := by omega
  have hw : |J n model| ≤ a*t := hA n na
  have hd (d : ℕ) (h : d ∣ 30) : |D n d| ≤ (d:ℝ)*(b*t) := hB n nb d h
  let H := Finset.Icc ((L n)^2+1) n
  have eq := h₃ n H (V n) (fun h hh => (Finset.mem_Icc.mp hh).2)
  change 2*(∑ h ∈ H, (((n:ℝ)-h)*(15/32)*rho h)*V n h) = (15/32)*(3*D n 1+3*D n 3+D n 5+D n 15) at eq
  have he : Q n = (15/32:ℝ)*(3*D n 1+3*D n 3+D n 5+D n 15)-J n model := by
    rw [← eq]
    change 2*(∑ h ∈ H, (_-_)*V n h) = 2*(∑ h ∈ H, _)-2*(∑ h ∈ H, _)
    simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
  have h1 := abs_le.mp (hd 1 (by decide))
  have h3 := abs_le.mp (hd 3 (by decide))
  have h5 := abs_le.mp (hd 5 (by decide))
  have h15 := abs_le.mp (hd 15 (by decide))
  norm_num at h1 h3 h5 h15
  rcases abs_le.mp hw with ⟨hw₁,hw₂⟩
  change |Q n| ≤ (a+15*b)*(n:ℝ)/(Real.log (n:ℝ))^2
  rw [mul_div_assoc]
  change |Q n| ≤ (a+15*b)*t
  rw [he, abs_le]
  constructor <;> linarith [h1.1,h1.2,h3.1,h3.2,h5.1,h5.2,h15.1,h15.2]

theorem Conjectures.Goldbach.WheelModelLogSquareDecay :
(by
  classical
  let Qn : ℕ → ℕ := fun n => (Nat.log 2 (n + 2)) ^ 2
  let arcs : ℕ → Set ℝ := fun n => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qn n ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a : ℝ) / (q : ℝ)| ≤ (Qn n : ℝ) / ((q : ℝ) * (n : ℝ))}
  let L : ℕ → ℕ := fun n => max 1 (Nat.log 2 n / 2)
  let K : ℕ → ℝ → ℝ := fun n t => (∑ j ∈ Finset.range (L n), Real.cos (2 * Real.pi * (2 : ℝ) ^ (j + 1) * t)) / (L n : ℝ)
  let B : ℕ → Set ℝ := fun n => {t : ℝ | t ∉ arcs n ∧ (1 : ℝ) / 2 < K n t}
  let V : ℕ → ℕ → ℝ := fun n h => intervalIntegral ((B n).indicator (fun t => Real.cos (2 * Real.pi * (h : ℝ) * t))) (0 : ℝ) 1 MeasureTheory.volume
  let A : ℕ → ℕ → (ℕ → ℝ) → ℝ := fun n h a => ∑ k ∈ Finset.range (n + 1 - h), a k * a (k + h)
  let model : ℕ → ℝ := fun k => if Nat.Coprime k 30 then (30 : ℝ) / 8 else 0
  let rho : ℕ → ℝ := fun h => (2 : ℝ) ^ (if 3 ∣ h then 1 else 0) * (3 * (if 5 ∣ h then (0 : ℝ) else 1) + 4 * (if 5 ∣ h then (1 : ℝ) else 0))
  let Q : ℕ → ℝ := fun n => 2 * (∑ h ∈ Finset.Icc ((L n) ^ 2 + 1) n, ((n - h : ℝ) * ((15 : ℝ) / 32) * rho h - A n h model) * V n h)
  exact ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → Even n → |Q n| ≤ C * (n : ℝ) / (Real.log (n : ℝ))^2) := combined_wheel_bounds QuantitativeWheelCorrelation.wheel_long QuantitativeWheelCorrelation.residue_long weighted_profile
