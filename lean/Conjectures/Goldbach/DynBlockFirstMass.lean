import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

open Finset Filter
open scoped Topology

namespace DynBlockSmallPrimeAux

/- Adapted from the verified DynFirstMass module. -/

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

theorem dyn_small_prime_mass : ∃ X₀ : ℕ, ∀ X ≥ X₀,
    Real.sqrt (X:ℝ) / (4 * Real.log (X:ℝ)) ≤
      (((Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime).card : ℝ) := by
  obtain ⟨K,hK⟩ := theta_bounds
  refine ⟨(K+16)^2, fun X hX => ?_⟩
  have hX16 : 16 ≤ X := by nlinarith [Nat.zero_le K]
  set s := Nat.sqrt X with hs
  have hsK : K ≤ s := by
    rw [hs]; exact le_trans (by omega) (Nat.le_sqrt.mpr (by nlinarith [hX] : (K+16)*(K+16) ≤ X))
  have hs4 : 4 ≤ s := by
    rw [hs]; exact Nat.le_sqrt.mpr (by omega)
  have hss : s * s ≤ X := Nat.sqrt_le X
  have hsl : X < (s+1)*(s+1) := Nat.lt_succ_sqrt X
  have h4s : 4 * s ≤ X := by nlinarith
  set P := (Ioc s (2 * s)).filter Nat.Prime
  have hx16 : (16:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX16
  set r := Real.sqrt (X:ℝ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r * r = (X:ℝ) := Real.mul_self_sqrt (by linarith)
  have hsr : (s:ℝ) * (s:ℝ) ≤ (X:ℝ) := by exact_mod_cast hss
  have hsl' : (X:ℝ) < ((s:ℝ)+1)*((s:ℝ)+1) := by exact_mod_cast hsl
  have hs4' : (4:ℝ) ≤ s := by exact_mod_cast hs4
  have hsle : (s:ℝ) ≤ r := by nlinarith
  have hrs : r ≤ (s:ℝ) + 1 := by nlinarith
  have hr2 : r ≤ 2 * (s:ℝ) := by linarith
  have hL : 0 < Real.log (X:ℝ) := Real.log_pos (by linarith)
  set L := Real.log (X:ℝ) with hLdef
  -- P count
  have hP1 := window_le s (2*s) (by omega)
  have hbs := hK s hsK
  have hb2s := hK (2*s) (by omega)
  push_cast at hb2s hP1
  have hlog2s : Real.log (2 * (s:ℝ)) ≤ L := by
    apply Real.log_le_log (by linarith)
    have : (4 * s : ℝ) ≤ (X:ℝ) := by exact_mod_cast h4s
    linarith
  have hPc : (0:ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hP2 : (17/20 : ℝ) * s ≤ (P.card : ℝ) * L := by
    have h1 : (P.card : ℝ) * Real.log (2 * (s:ℝ)) ≤ (P.card : ℝ) * L :=
      mul_le_mul_of_nonneg_left hlog2s hPc
    linarith [hbs.2, hb2s.1]
  have hsub : P ⊆ (Icc s (2*s)).filter Nat.Prime := by
    intro p hp
    have ⟨h,hprime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Ioc.mp h).1.le, (mem_Ioc.mp h).2⟩,hprime⟩
  have hcard : (P.card : ℝ) ≤ (((Icc s (2*s)).filter Nat.Prime).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  apply le_trans _ hcard
  apply (div_le_iff₀ (by positivity : 0 < 4 * L)).mpr
  nlinarith [hP2]
end DynBlockSmallPrimeAux

namespace GoldbachBlockMass

/-- Every small prime and every large prime in the first half of the block
produce a representation counted in that same block. -/
theorem interior_box :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n)
    let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime
    let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card
    let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X)
    let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X)
    ∀ X y : ℕ, 256 ≤ X → X ≤ y → y + W X ≤ 2*X →
      (P X).card * ((Finset.Ico y (y + W X / 2)).filter Nat.Prime).card ≤
        ∑ n ∈ B X y, H X n := by
  intro E P H W B X y hX hXy hEnd
  have hs : 16 ≤ Nat.sqrt X := (Nat.le_sqrt).2 (by omega)
  have ht : 4 ≤ Nat.sqrt (Nat.sqrt X) := (Nat.le_sqrt).2 (by omega)
  have hWidth : 4 * Nat.sqrt X ≤ W X := by
    simpa [W, Nat.mul_comm] using Nat.mul_le_mul_right (Nat.sqrt X) ht
  have count : ∑ n ∈ B X y, H X n =
      (((B X y) ×ˢ (P X)).filter (fun z => z.2 ≤ z.1 ∧ Nat.Prime (z.1 - z.2))).card := by
    rw [Finset.card_filter, Finset.sum_product]
    exact Finset.sum_congr rfl (fun n _ => by dsimp [H]; rw [Finset.card_filter])
  rw [count, ← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun z => (z.2 + z.1, z.1))
  · intro z hz
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_Ico, Finset.mem_product, P, B, E] at hz ⊢
    obtain ⟨⟨⟨hpLo, hpHi⟩, hp⟩, ⟨⟨hqLo, hqHi⟩, hq⟩⟩ := hz
    have hEven : Even (z.2 + z.1) :=
      (hq.odd_of_ne_two (by omega)).add_odd (hp.odd_of_ne_two (by omega))
    refine ⟨⟨⟨⟨⟨by omega, by omega⟩, hEven⟩, by omega, by omega⟩,
      ⟨⟨hpLo, hpHi⟩, hp⟩⟩, by omega, ?_⟩
    simpa using hq
  · intro a _ b _ eq
    simp only [Prod.mk.injEq] at eq
    ext <;> omega

end GoldbachBlockMass

namespace GoldbachBlockMass

/-- Uniform lower bound for large primes in the first half of each eligible block. -/
def ShortPrimeMass : Prop :=
  let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X)
  ∃ k : ℝ, 0 < k ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X →
    k * (W X : ℝ) / Real.log (X : ℝ) ≤
      (((Finset.Ico y (y + W X / 2)).filter Nat.Prime).card : ℝ)

theorem block_first_mass_of_short_primes (hshort : ShortPrimeMass) :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) := by
  intro E P H W B M
  obtain ⟨k, hk, X₁, hw⟩ := hshort
  obtain ⟨X₂, hsmall⟩ := DynBlockSmallPrimeAux.dyn_small_prime_mass
  refine ⟨k/4, by positivity, max 256 (max X₁ X₂), ?_⟩
  intro X hX y hy hEnd
  have h256 : 256 ≤ X := by omega
  have hlog : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  let Q := (Finset.Ico y (y + W X / 2)).filter Nat.Prime
  have hsm : Real.sqrt (X : ℝ) / (4 * Real.log (X : ℝ)) ≤ ((P X).card : ℝ) :=
    hsmall X (by omega)
  have hlg : k * (W X : ℝ) / Real.log (X : ℝ) ≤ (Q.card : ℝ) :=
    hw X (by omega) y hy hEnd
  have hprod := mul_le_mul hsm hlg
    (show 0 ≤ k * (W X : ℝ) / Real.log (X : ℝ) by positivity)
    (show 0 ≤ ((P X).card : ℝ) by positivity)
  calc
    k / 4 * (W X : ℝ) * M X =
        (Real.sqrt (X : ℝ) / (4 * Real.log (X : ℝ))) *
          (k * (W X : ℝ) / Real.log (X : ℝ)) := by
      dsimp [M]
      ring
    _ ≤ ((P X).card : ℝ) * (Q.card : ℝ) := hprod
    _ ≤ ∑ n ∈ B X y, (H X n : ℝ) := by
      exact_mod_cast interior_box X y h256 hy hEnd

end GoldbachBlockMass

/- A bandwidth variant of LogTruSoul's pointwise estimate (goldbach-proofs
PR #3746, Apache-2.0). We run the existing absolute error budgets at 128
 times the two original constants, retaining the original low-zero budget. -/
noncomputable section
open Finset
open scoped BigOperators Classical
namespace GoldbachBlockCompact
open GoldbachOC103 Vx V7e V86 V1e V6i
private theorem fractional_window :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(3/4 : ℝ) ≤ 128*(h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/4 := by
  obtain ⟨C, hC, Xz, hz⟩ := actual_zero_weight_bounds
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets (128*D) C (128*C) (by positivity)
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
    have hhig := hbud.high_budget
    calc
      _ = (1/128:ℝ) * (576*(128*C)*X^2*(Real.log X)^14 /
          (X^(2/3:ℝ)*(X^(5/16:ℝ))^2)) := by ring
      _ ≤ (1/128:ℝ) * (X^(3/4:ℝ)/16) := mul_le_mul_of_nonneg_left hhig (by norm_num)
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
    have hresid := hbud.residual_budget
    exact hres.trans (by linarith only [hresid, hlower])
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

private theorem theta_window :
    ∃ T : ℝ, ∀ y h : ℕ, T ≤ (y:ℝ) → (y:ℝ)^(3/4:ℝ) ≤ 128*(h:ℝ) → h ≤ y →
      (h:ℝ)/2 ≤ ∑ p ∈ Ioc y (y+h), GoldbachDyadicBridge.primeLog p := by
  obtain ⟨M, hM⟩ := fractional_window
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max 1 (max M (GoldbachPrimeBridge.primePowerCutoff (128*|C|))), ?_⟩
  intro y h hy hl hu
  have hy1 := (le_max_left _ _).trans hy
  have hyM := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
  have hycut := (le_max_right _ _).trans ((le_max_right _ _).trans hy)
  have hp : (y:ℝ)^(3/4:ℝ) ≤ y := (Real.rpow_le_rpow_of_exponent_le hy1
    (by norm_num : (3/4:ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  let H := max (h:ℝ) ((y:ℝ)^(3/4:ℝ))
  have hr : (h:ℝ) ≤ H := le_max_left _ _
  have hhu : H ≤ y := max_le (by exact_mod_cast hu) hp
  have hh128 : H ≤ 128*(h:ℝ) := max_le (by linarith only [Nat.cast_nonneg (α:=ℝ) h]) hl
  have hc := GoldbachPrimeBridge.prime_power_error_small (128*|C|) (y:ℝ) H hycut (le_max_right _ _) hhu
  have hc1 : C * Real.sqrt ((y:ℝ)+h) ≤ (h:ℝ)/4 := by
    calc
      _ ≤ |C| * Real.sqrt ((y:ℝ)+H) := mul_le_mul (le_abs_self C) (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _) (abs_nonneg _)
      _ ≤ _ := by linarith only [hc,hh128]
  have herr := hM y hyM h hl (by exact_mod_cast hu)
  rw [GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi] at herr
  have hbound := (hC ((y:ℝ)+h)).trans hc1
  rw [← GoldbachDyadicBridge.theta_nat_add_sub]
  linarith only [(abs_le.mp herr).1, hbound, Chebyshev.theta_le_psi (y:ℝ)]

private theorem start_scale (X y : ℕ) (hX : 65536 ≤ X) (hy : y ≤ 2*X) :
    (y:ℝ)^(3/4:ℝ) ≤ 128*((X.sqrt*X.sqrt.sqrt/4:ℕ):ℝ) := by
  let s := X.sqrt
  let t := s.sqrt
  let w := s*t
  have hs : 256 ≤ s := Nat.le_sqrt.mpr (by simpa [pow_two] using hX)
  have ht : 16 ≤ t := Nat.le_sqrt.mpr (by simpa [pow_two] using hs)
  have hw : 8 ≤ w := le_trans (by decide : 8 ≤ 256*16) (Nat.mul_le_mul hs ht)
  have hys : y ≤ 8*s^2 := by
    have hh := Nat.lt_succ_sqrt X
    have hmul := Nat.mul_le_mul (by omega : s+1 ≤ 2*s) (by omega : s+1 ≤ 2*s)
    nlinarith only [hy,hh,hmul]
  have hst : s ≤ 4*t^2 := by
    have hh := Nat.lt_succ_sqrt s
    have hmul := Nat.mul_le_mul (by omega : t+1 ≤ 2*t) (by omega : t+1 ≤ 2*t)
    nlinarith only [hh,hmul]
  have hpow : y^3 ≤ (128*(w/4))^4 := calc
    _ ≤ (8*s^2)^3 := Nat.pow_le_pow_left hys _
    _ = 512*s^4*s^2 := by ring
    _ ≤ 512*s^4*(4*t^2)^2 := by gcongr
    _ = 8192*w^4 := by dsimp [w]; ring
    _ ≤ 8192*(8*(w/4))^4 := by gcongr; omega
    _ ≤ (128*(w/4))^4 := by ring_nf; omega
  apply le_of_pow_le_pow_left₀ (by decide : (4:ℕ) ≠ 0) (by positivity)
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
  norm_num
  exact_mod_cast hpow

theorem local_prime_mass :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y →
      y + X.sqrt*X.sqrt.sqrt ≤ 2*X →
      c * ((X.sqrt*X.sqrt.sqrt:ℕ):ℝ) / Real.log (X:ℝ) ≤
        (((Ico y (y + X.sqrt*X.sqrt.sqrt/2)).filter Nat.Prime).card:ℝ) := by
  obtain ⟨T, hT⟩ := theta_window
  refine ⟨1/32, by norm_num, max ⌈T⌉₊ 65536, ?_⟩
  intro X hX y hy hend
  let w := X.sqrt*X.sqrt.sqrt
  let h := w/4
  have xlarge := (le_max_right _ _).trans hX
  have hwy : w ≤ y := by dsimp [w]; omega
  have hs : 256 ≤ X.sqrt := Nat.le_sqrt.mpr (by omega)
  have ht : 16 ≤ X.sqrt.sqrt := Nat.le_sqrt.mpr (by omega)
  have hw8 : 8 ≤ w := le_trans (by decide : 8 ≤ 256*16) (Nat.mul_le_mul hs ht)
  have hx2 : 2 ≤ X := by omega
  have hyT : T ≤ (y:ℝ) := (Nat.le_ceil T).trans (by exact_mod_cast ((le_max_left _ _).trans hX).trans hy)
  have hd := hT y h hyT (start_scale X y xlarge (by omega)) (by dsimp [h]; omega)
  let P := (Ico y (y+w/2)).filter Nat.Prime
  have hice : ((Ioc y (y+h)).filter Nat.Prime) ⊆ P := by
    intro p hp
    obtain ⟨hpI,hpP⟩ := mem_filter.mp hp
    rw [mem_Ioc] at hpI
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hpI.1.le, by dsimp [h] at hpI; omega⟩,hpP⟩
  have hposX : 1 < (X:ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hlogX : 0 < Real.log (X:ℝ) := Real.log_pos hposX
  have hlog {p : ℕ} (hp : p ∈ Ioc y (y+h)) : Real.log (p:ℝ) ≤ 2*Real.log X := by
    have hi := (mem_Ioc.mp hp).2
    have hp0 : 0 < p := (Nat.zero_le y).trans_lt (mem_Ioc.mp hp).1
    have hpn : p ≤ X^2 := by
      have : p ≤ 2*X := by dsimp [h,w] at hi; omega
      nlinarith only [this,Nat.mul_le_mul_right X hx2]
    rw [show 2*Real.log (X:ℝ)= Real.log ((X:ℝ)^2) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by exact_mod_cast hp0) (by exact_mod_cast hpn)
  have hup : (∑ p ∈ Ioc y (y+h), GoldbachDyadicBridge.primeLog p) ≤
      (P.card:ℝ)*(2*Real.log X) := calc
    _ = ∑ p ∈ (Ioc y (y+h)).filter Nat.Prime, Real.log (p:ℝ) := by
      simp [Finset.sum_filter,GoldbachDyadicBridge.primeLog]
    _ ≤ ∑ p ∈ (Ioc y (y+h)).filter Nat.Prime, 2*Real.log X :=
      sum_le_sum fun k hk => hlog (mem_filter.mp hk).1
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_le_card hice)) (by positivity)
  have hsize : (w:ℝ) ≤ 8*(h:ℝ) := by exact_mod_cast (by dsimp [h]; omega : w ≤ 8*h)
  apply (div_le_iff₀ hlogX).mpr
  change 1/32*(w:ℝ) ≤ (P.card:ℝ)*Real.log (X:ℝ)
  linarith only [hsize,hd,hup]

end GoldbachBlockCompact
end

theorem Conjectures.Goldbach.DynBlockFirstMass :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) := by
  apply GoldbachBlockMass.block_first_mass_of_short_primes
  exact GoldbachBlockCompact.local_prime_mass
