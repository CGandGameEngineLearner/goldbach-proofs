import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
The zero-weight assembly below is adapted from LogTruSoul's OC-0103 proof
(goldbach-proofs PR #3746, Apache-2.0). Multiplying only the high-zero and
residual budget constants by 64 permits windows down to x^(3/4)/64.
-/

namespace Goldbach.LocalPrimeMass
noncomputable section
open Finset GoldbachOC103 Vx V7e V86 V1e V6i
open scoped BigOperators Classical

private theorem scaled_principal_window
    (hzero : ActualZeroWeightBounds) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(3/4 : ℝ) ≤ 64*(h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/4 := by
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets (64*D) C (64*C) (by positivity)
  refine ⟨max Xz Xb, ?_⟩
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
    exact weight_count_clamp R X (X^(5/16 : ℝ)) K v hV hbud.split_le_scale hK hv
      (fun c hc => hS c (mem_filter.mp hc).1) hcount
  have hpacket := smoothed_packet_of_weight_bounds S (fun c => c.val.1)
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
    rw [high_coefficient_normalization C X (X^(5/16 : ℝ)) (X^(2/3 : ℝ)) hV hδ]
    calc
      _ = (576*(64*C)*X^2*(Real.log X)^14 /
          (X^(2/3:ℝ)*(X^(5/16:ℝ))^2))/64 := by ring
      _ ≤ (X^(3/4:ℝ)/16)/64 := div_le_div_of_nonneg_right hbud.high_budget (by norm_num)
      _ ≤ _ := by linarith only [hlower]
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
    apply hres.trans
    linarith only [hbud.residual_budget, hlower]
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


private theorem short_theta : ∃ N : ℕ, ∀ y ≥ N, ∀ h : ℕ,
    (y:ℝ)^(3/4:ℝ) ≤ 64*(h:ℝ) → 64*h ≤ y →
    (h:ℝ)/2 ≤ Chebyshev.theta ((y+h:ℕ):ℝ) - Chebyshev.theta (y:ℝ) := by
  obtain ⟨Y,hY⟩ := scaled_principal_window actual_zero_weight_bounds
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let D := max C 0
  have hD : 0 ≤ D := le_max_right ..
  obtain ⟨N,hN⟩ := exists_nat_ge (max Y (GoldbachPrimeBridge.primePowerCutoff (64*D)))
  refine ⟨N, ?_⟩
  intro y hy h hscale hhy
  have hx : max Y (GoldbachPrimeBridge.primePowerCutoff (64*D)) ≤ (y:ℝ) :=
    hN.trans (by exact_mod_cast hy)
  have hh : (0:ℝ) ≤ h := Nat.cast_nonneg _
  have hcap : 64*(h:ℝ) ≤ y := by exact_mod_cast hhy
  have hev := hY y ((le_max_left ..).trans hx) h hscale (by linarith)
  rw [GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi] at hev
  have hpp := GoldbachPrimeBridge.prime_power_error_small (64*D) y (64*(h:ℝ))
    ((le_max_right ..).trans hx) hscale hcap
  have hsq := Real.sqrt_le_sqrt (show (y:ℝ)+h ≤ y+64*h by linarith)
  have herr := (hC ((y:ℝ)+h)).trans (mul_le_mul
    (le_max_left C 0) hsq (Real.sqrt_nonneg _) hD)
  have hbase := Chebyshev.theta_le_psi (y:ℝ)
  push_cast
  linarith only [(abs_le.mp hev).1,herr,hpp,hbase]

end
end Goldbach.LocalPrimeMass


namespace Goldbach.LocalPrimeMass
open Finset Filter
open scoped Topology

private def small (X : ℕ) := (Icc X.sqrt (2*X.sqrt)).filter Nat.Prime
private def width (X : ℕ) := X.sqrt * X.sqrt.sqrt
private def block (X y : ℕ) := ((Icc X (2*X)).filter Even).filter (fun n => y≤n ∧ n<y+width X)
private def length (X : ℕ) := width X / 2
private def large (X y : ℕ) := (Ioc y (y+length X)).filter Nat.Prime

/- The following two Chebyshev estimates are adapted from the project's
   `DynFirstMass` proof (Apache-2.0). -/
private theorem theta_bounds : ∃ K : ℕ, ∀ n ≥ K,
    (19/20 : ℝ) * n < Chebyshev.theta n ∧ Chebyshev.theta n < (21/20 : ℝ) * n := by
  have limN : Tendsto (fun n : ℕ ↦ Chebyshev.theta n / (n : ℝ)) atTop (𝓝 1) :=
    Chebyshev.tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop
  apply Filter.eventually_atTop.mp
  filter_upwards [limN.eventually_const_lt (show (19/20 : ℝ) < 1 by norm_num),
    limN.eventually_lt_const (show (1 : ℝ) < 21/20 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hlo hhi hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ⟨(lt_div_iff₀ hn').mp hlo, (div_lt_iff₀ hn').mp hhi⟩

private theorem window_le (a b : ℕ) (hab : a ≤ b) :
    Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) ≤
      (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) * Real.log b := by
  have expand (n : ℕ) : Chebyshev.theta (n : ℝ) =
      ∑ p ∈ Ioc 0 n, (if p.Prime then Real.log (p:ℝ) else 0) := by
    simp [Chebyshev.theta, sum_filter]
  have split := Finset.sum_union (f := fun p : ℕ => if p.Prime then Real.log (p:ℝ) else 0)
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (b := a) (c := a) (d := b) le_rfl)
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hab] at split
  have h1 : Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ) := by
    rw [expand, expand, split, sum_filter]
    ring
  rw [h1]
  calc ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ)
      ≤ ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (b:ℝ) := by
        refine sum_le_sum fun p hp => ?_
        have hp' := mem_filter.mp hp
        have h2 := (mem_Ioc.mp hp'.1)
        exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast h2.2)
    _ = _ := by simp

private theorem box {X y : ℕ} (hs : 3 ≤ X.sqrt) (hxy : X≤y)
    (hcap : y+width X ≤ 2*X) (hmargin : 2*X.sqrt + length X < width X) :
    (small X).card * (large X y).card ≤ ∑ n ∈ block X y,
      ((small X).filter fun p => p≤n ∧ (n-p).Prime).card := by
  have hX : 3 ≤ X := by have := Nat.sqrt_le' X; nlinarith
  have key : (∑ n ∈ block X y, ((small X).filter fun p => p≤n ∧ (n-p).Prime).card) =
      (((block X y) ×ˢ (small X)).filter (fun z => z.2 ≤ z.1 ∧ (z.1-z.2).Prime)).card := by
    rw [card_filter, sum_product]
    apply sum_congr rfl
    intro n _
    rw [card_filter]
  rw [key, ← card_product]
  apply card_le_card_of_injOn (fun z : ℕ × ℕ => (z.1+z.2,z.1))
  · rintro z hz
    obtain ⟨hp,hq⟩ := mem_product.mp hz
    obtain ⟨hpI,hpr⟩ := mem_filter.mp hp
    obtain ⟨hqI,hqr⟩ := mem_filter.mp hq
    obtain ⟨hp₁,hp₂⟩ := mem_Icc.mp hpI
    obtain ⟨hq₁,hq₂⟩ := mem_Ioc.mp hqI
    have he := (hpr.odd_of_ne_two (by omega)).add_odd (hqr.odd_of_ne_two (by omega))
    change (z.1+z.2,z.1) ∈ _
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨?_,hp⟩, by omega, by simpa using hqr⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,he⟩,by omega,by omega⟩
  · rintro ⟨p,q⟩ _ ⟨r,s⟩ _ heq
    simp only [Prod.mk.injEq] at heq ⊢
    omega

private theorem scales {X y : ℕ} (ht : 64 ≤ X.sqrt.sqrt) (hxy : X ≤ y) (hy : y ≤ 2*X) :
    (y:ℝ)^(3/4:ℝ) ≤ 64*(length X:ℝ) ∧ 64*length X ≤ y ∧
      2*X.sqrt+length X < width X ∧ width X ≤ 3*length X := by
  let s := X.sqrt
  let t := s.sqrt
  change 64 ≤ t at ht
  have hts : t^2 ≤ s := Nat.sqrt_le' s
  have hss : s^2 ≤ X := Nat.sqrt_le' X
  have hst : s < (t+1)^2 := Nat.lt_succ_sqrt' s
  have hxs : X < (s+1)^2 := Nat.lt_succ_sqrt' X
  have hs : 4 ≤ s := by nlinarith
  have hyt : y ≤ 8*s^2 := by nlinarith
  have hst' : s ≤ 4*t^2 := by nlinarith
  have h64 : 64*t ≤ s := (by nlinarith [Nat.mul_le_mul_right t ht] : 64*t ≤ t^2).trans hts
  have hW64 : 64*width X ≤ X := by
    calc 64*width X = s*(64*t) := by dsimp [width,s,t]; ring
         _ ≤ s*s := Nat.mul_le_mul_left s h64
         _ ≤ X := Nat.sqrt_le X
  have hW4 : 4*s ≤ width X := by
    change 4*s ≤ s*t
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left s (show 4 ≤ t by omega)
  have hlen : width X ≤ 3*length X := by dsimp only [length]; omega
  have hn : y^3 ≤ (64*length X)^4 := by
    calc y^3 ≤ (8*s^2)^3 := Nat.pow_le_pow_left hyt _
         _ = 512*s^4*s^2 := by ring
         _ ≤ 512*s^4*(4*t^2)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hst' _)
         _ ≤ (16*width X)^4 := by change _ ≤ (16*(s*t))^4; ring_nf; omega
         _ ≤ (64*length X)^4 := Nat.pow_le_pow_left (by omega) _
  have hscale : (y:ℝ)^(3/4:ℝ) ≤ 64*(length X:ℝ) := by
    apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by positivity) _) (by positivity) (by decide : 4 ≠ 0)).mp
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg y)]
    norm_num
    exact_mod_cast hn
  refine ⟨hscale, ?_, ?_, hlen⟩
  · exact (Nat.mul_le_mul_left 64 (Nat.div_le_self _ 2)).trans (hW64.trans hxy)
  · change 2*s + width X / 2 < width X
    have hW8 : 8*s ≤ width X := by
      change 8*s ≤ s*t
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left s (show 8 ≤ t by omega)
    omega

private theorem small_count {K X : ℕ} (hK : ∀ n ≥ K,
    (19/20:ℝ)*n < Chebyshev.theta n ∧ Chebyshev.theta n < (21/20:ℝ)*n)
    (hsK : K ≤ X.sqrt) (hs : 4 ≤ X.sqrt) :
    Real.sqrt X / 4 ≤ ((small X).card:ℝ) * Real.log X := by
  let s := X.sqrt
  have hs₄ : 4 ≤ s := hs
  have hnat : 2*s ≤ X := by have h : s^2 ≤ X := Nat.sqrt_le' _; nlinarith
  have hsR : Real.sqrt (X:ℝ) ≤ 2*(s:ℝ) := by
    have h : X < (s+1)^2 := Nat.lt_succ_sqrt' X
    apply (Real.sqrt_le_left (by positivity)).mpr
    exact_mod_cast (by nlinarith : X ≤ (2*s)^2)
  have hbound := window_le s (2*s) (by omega)
  have hsub : ((Ioc s (2*s)).filter Nat.Prime).card ≤ (small X).card := by
    apply card_le_card
    intro p hp
    obtain ⟨hi,hp⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Ioc.mp hi).1.le,(mem_Ioc.mp hi).2⟩,hp⟩
  have hlog : Real.log ((2*s:ℕ):ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast (show 0<2*s by omega)) (by exact_mod_cast hnat)
  have hmul := mul_le_mul (by exact_mod_cast hsub : ((((Ioc s (2*s)).filter Nat.Prime).card:ℝ)) ≤ (small X).card)
    hlog (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
  have ha := (hK s hsK).2
  have hb := (hK (2*s) (by omega)).1
  push_cast at hbound hmul hb
  linarith

private theorem mass_of_short (input : ∃ N : ℕ, ∀ y ≥ N, ∀ h : ℕ,
    (y:ℝ)^(3/4:ℝ) ≤ 64*(h:ℝ) → 64*h ≤ y →
    (h:ℝ)/2 ≤ Chebyshev.theta ((y+h:ℕ):ℝ) - Chebyshev.theta (y:ℝ)) :
    ∃ c : ℝ, 0<c ∧ ∃ N : ℕ, ∀ X ≥ N, ∀ y : ℕ, X≤y → y+width X≤2*X →
      c*(width X:ℝ)*(Real.sqrt X/(Real.log X)^2) ≤ ∑ n ∈ block X y,
        (((small X).filter fun p => p ≤ n ∧ (n-p).Prime).card:ℝ) := by
  obtain ⟨N,hN⟩ := input
  obtain ⟨K,hK⟩ := theta_bounds
  refine ⟨1/48, by norm_num, max N ((max K (64*64))^2), ?_⟩
  intro X hX y hxy hcap
  have hNX := (le_max_left ..).trans hX
  have hs := Nat.le_sqrt'.mpr ((le_max_right ..).trans hX)
  have hsK : K ≤ X.sqrt := (le_max_left ..).trans hs
  have hs64 : 64*64 ≤ X.sqrt := (le_max_right ..).trans hs
  have ht : 64 ≤ X.sqrt.sqrt := Nat.le_sqrt.mpr hs64
  obtain ⟨hscale, hhy, hmargin, hlen⟩ := scales ht hxy (by omega : y ≤ 2*X)
  have hx₂ : 2 ≤ X := by have := Nat.sqrt_le' X; nlinarith
  have hlog : 0 < Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hlow := hN y (hNX.trans hxy) (length X) hscale hhy
  have hlarge := window_le y (y+length X) (by omega)
  change _ ≤ (large X y).card * Real.log ((y+length X:ℕ):ℝ) at hlarge
  have hlength : length X ≤ width X := Nat.div_le_self _ _
  have hendpoint : y + length X ≤ X^2 := by
    have : 2*X ≤ X^2 := by nlinarith
    omega
  have hlogend : Real.log ((y+length X:ℕ):ℝ) ≤ 2*Real.log X := by
    have h := Real.log_le_log (by exact_mod_cast (show 0<y+length X by omega)) (by exact_mod_cast hendpoint : ((y+length X:ℕ):ℝ) ≤ (X:ℝ)^2)
    simpa [Real.log_pow] using h
  have hbig : (width X:ℝ)/12 ≤ (large X y).card * Real.log X := by
    have hl : (width X:ℝ) ≤ 3*(length X:ℝ) := by exact_mod_cast hlen
    have hu := mul_le_mul_of_nonneg_left hlogend (Nat.cast_nonneg (α:=ℝ) (large X y).card)
    linarith only [hl,hlow,hlarge,hu]
  have hsmall := small_count hK hsK (by omega)
  have both := mul_le_mul hsmall hbig (by positivity : (0:ℝ) ≤ (width X:ℝ)/12)
    (mul_nonneg (Nat.cast_nonneg _) hlog.le)
  have hrect := box (X:=X) (y:=y) (by omega) hxy hcap hmargin
  have hrectR : ((small X).card:ℝ)*(large X y).card ≤ ∑ n ∈ block X y,
      (((small X).filter fun p => p≤n ∧ (n-p).Prime).card:ℝ) := by exact_mod_cast hrect
  refine le_trans ?_ hrectR
  rw [← mul_div_assoc, div_le_iff₀ (sq_pos_of_pos hlog)]
  linarith only [both]


theorem _root_.Conjectures.Goldbach.DynBlockFirstMass :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) := by
  exact mass_of_short short_theta

end Goldbach.LocalPrimeMass
