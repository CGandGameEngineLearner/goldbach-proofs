import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-! Counts prime paths by selecting an interior box in each moving block.
The finite injection and long-prime-window estimate are adapted from
Conjectures.Goldbach.DynFirstMass and DynInteriorBox. The short-window
argument uses LogTruSoul's DyadicCellShortPrimeFloor (upstream PR #3746).
Its smoothed explicit formula is specialized below to a constant multiple
of the three-quarter power scale. -/
open Finset Filter
open scoped Topology
namespace Goldbach.MovingFirstMass
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

private theorem count_nat (X y h : ℕ) (hX : 16 ≤ X) (hy : X ≤ y) (hyend : y + X.sqrt * X.sqrt.sqrt ≤ 2*X) (hh : h + 2*X.sqrt < X.sqrt * X.sqrt.sqrt) :
    (((Ioc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).card *
      ((Ioc y (y+h)).filter Nat.Prime).card) ≤
    ∑ n ∈ ((Icc X (2 * X)).filter Even).filter (fun n => y ≤ n ∧ n < y + X.sqrt * X.sqrt.sqrt),
      (((Icc (Nat.sqrt X) (2 * Nat.sqrt X)).filter Nat.Prime).filter
        (fun p => p ≤ n ∧ Nat.Prime (n - p))).card := by
  set s := Nat.sqrt X with hs
  have hs4 : 4 ≤ s := by
    rw [hs]; exact Nat.le_sqrt.mpr (by omega)
  have hss : s * s ≤ X := Nat.sqrt_le X
  have h4s : 4 * s ≤ X := by nlinarith
  set P := (Ioc s (2 * s)).filter Nat.Prime
  set Q := (Ioc y (y+h)).filter Nat.Prime
  have hcard : P.card * Q.card = (P ×ˢ Q).card := by rw [card_product]
  rw [hcard]
  simp_rw [card_filter]
  rw [← sum_product' (f := fun n p => if p ≤ n ∧ Nat.Prime (n - p) then 1 else 0)]
  have := Finset.sum_le_sum_of_injOn
    (s := P ×ˢ Q) (t := (((Icc X (2 * X)).filter Even).filter (fun n => y ≤ n ∧ n < y + X.sqrt * X.sqrt.sqrt)) ×ˢ ((Icc s (2 * s)).filter Nat.Prime))
    (e := fun z : ℕ × ℕ => (z.1 + z.2, z.1))
    (f := fun _ => 1)
    (g := fun z : ℕ × ℕ => if z.2 ≤ z.1 ∧ Nat.Prime (z.1 - z.2) then 1 else 0)
    ?_ ?_ ?_ ?_
  · simpa using this
  · intro z _ v _ he
    have h1 : z.1 = v.1 := congrArg Prod.snd he
    have h2 : z.1 + z.2 = v.1 + v.2 := congrArg Prod.fst he
    exact Prod.ext h1 (by omega)
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    obtain ⟨hp, hq⟩ := mem_product.mp hz
    obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
    obtain ⟨hp3, hp4⟩ := mem_Ioc.mp hp1
    obtain ⟨hq3, hq4⟩ := mem_Ioc.mp hq1
    have hpodd : Odd z.1 := hp2.odd_of_ne_two (by omega)
    have hqodd : Odd z.2 := hq2.odd_of_ne_two (by omega)
    refine mem_product.mpr ⟨?_, ?_⟩
    · subst s
      dsimp only at hp3 hp4 hq3 hq4 ⊢
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hpodd.add_odd hqodd⟩,by omega,by omega⟩
    · exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hp2⟩
  · intro z hz
    obtain ⟨hp, hq⟩ := mem_product.mp hz
    obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    obtain ⟨hq1, hq2⟩ := mem_filter.mp hq
    obtain ⟨hp3, hp4⟩ := mem_Ioc.mp hp1
    obtain ⟨hq3, hq4⟩ := mem_Ioc.mp hq1
    have h1 : z.1 ≤ z.1 + z.2 := by omega
    have h2 : z.1 + z.2 - z.1 = z.2 := by omega
    simp [h1, h2, hq2]
  · intro a _ _
    exact Nat.zero_le _

private theorem scale {X y : ℕ} (hy : y ≤ 2*X) (ht : 8 ≤ X.sqrt.sqrt) :
    (y : ℝ)^(3/4 : ℝ) ≤ 32*(X.sqrt * (X.sqrt.sqrt-3) : ℕ) := by
  let s := X.sqrt
  let t := s.sqrt
  have hs : 1 ≤ s := by have := Nat.sqrt_le s; change 8 ≤ t at ht; dsimp [t] at ht; nlinarith
  have ht' : 8 ≤ t := ht
  have hy' : y ≤ 8*s^2 := by
    have hX := Nat.lt_succ_sqrt X
    change X < (s+1)*(s+1) at hX
    have := Nat.mul_le_mul (show s+1 ≤ 2*s by omega) (show s+1 ≤ 2*s by omega)
    nlinarith
  have hs' : s ≤ 4*t^2 := by
    have h := Nat.lt_succ_sqrt s
    change s < (t+1)*(t+1) at h
    have := Nat.mul_le_mul (show t+1 ≤ 2*t by omega) (show t+1 ≤ 2*t by omega)
    nlinarith
  have hb : y^3 ≤ (32*(s*(t-3)))^4 := calc
    y^3 ≤ (8*s^2)^3 := Nat.pow_le_pow_left hy' _
    _ = 512*s^4*s^2 := by ring
    _ ≤ 512*s^4*(4*t^2)^2 := by gcongr
    _ = 8192*(s*t)^4 := by ring
    _ ≤ 8192*(s*(2*(t-3)))^4 := by gcongr; omega
    _ ≤ (32*(s*(t-3)))^4 := by ring_nf; omega
  have hb' : (y:ℝ)^3 ≤ (32*(s*(t-3)) : ℕ)^4 := by exact_mod_cast hb
  calc
    _ = ((y:ℝ)^3)^(1/4:ℝ) := by rw [← Real.rpow_natCast_mul (Nat.cast_nonneg y)]; norm_num
    _ ≤ (((32*(s*(t-3)) : ℕ):ℝ)^4)^(1/4:ℝ) := Real.rpow_le_rpow (by positivity) hb' (by norm_num)
    _ = _ := by rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _)]; norm_num [s,t]

def WindowInput := ∃ M : ℕ, ∀ y h : ℕ, M ≤ y →
  (y:ℝ)^(3/4:ℝ) ≤ 32*(h:ℝ) → h ≤ y →
  (h:ℝ)/2 ≤ Chebyshev.theta ((y+h:ℕ):ℝ) - Chebyshev.theta (y:ℝ)

theorem from_window (hinput : WindowInput) :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) := by
  intro E P' H W B M'
  obtain ⟨K,hK⟩ := theta_bounds
  obtain ⟨M,hM⟩ := hinput
  refine ⟨1/40, by norm_num, max M ((K+100)^2), ?_⟩
  intro X hX y hy hyend
  change y + X.sqrt * X.sqrt.sqrt ≤ 2*X at hyend
  have hbig : (K+100)^2 ≤ X := by omega
  have hX16 : 16 ≤ X := by nlinarith [Nat.zero_le K]
  let s := X.sqrt
  let t := s.sqrt
  let h := s*(t-3)
  have hs100 : K+100 ≤ s := Nat.le_sqrt.mpr (by simpa [pow_two] using hbig)
  have ht8 : 8 ≤ t := Nat.le_sqrt.mpr (by omega)
  have hlen : h + 2*s < s*t := by dsimp [h]; have := Nat.sub_add_cancel (show 3 ≤ t by omega); nlinarith [congrArg (s * ·) this]
  have hhalf : s*t ≤ 2*h := by dsimp [h]; have := Nat.mul_le_mul_left s (show t ≤ 2*(t-3) by omega); nlinarith
  have hhy : h ≤ y := by change y + s*t ≤ 2*X at hyend; omega
  have hQ := hM y h (by omega) (scale (by omega) ht8) hhy
  have hnat := count_nat X y h hX16 hy hyend hlen
  let P := (Ioc s (2*s)).filter Nat.Prime
  let Q := (Ioc y (y+h)).filter Nat.Prime
  change (1/40:ℝ)*(s*t:ℕ)*(Real.sqrt X / (Real.log X)^2) ≤ _
  have hcast : ((P.card*Q.card : ℕ):ℝ) ≤ ((∑ n ∈ B X y, H X n : ℕ):ℝ) := by exact_mod_cast hnat
  push_cast at hcast
  refine le_trans ?_ hcast
  have hx16 : (16:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX16
  set r := Real.sqrt (X:ℝ) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r * r = (X:ℝ) := Real.mul_self_sqrt (by linarith)
  have hss : s*s ≤ X := Nat.sqrt_le X
  have hsl : X < (s+1)*(s+1) := Nat.lt_succ_sqrt X
  have hs4 : 4 ≤ s := by omega
  have h4s : 4*s ≤ X := by nlinarith
  have hsK : K ≤ s := by omega
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
  have hcount := window_le y (y+h) (by omega)
  have hlogQ : Real.log ((y+h:ℕ):ℝ) ≤ 2*L := by
    have h2 : y+h ≤ X*X := by change y + s*t ≤ 2*X at hyend; nlinarith
    have he := Real.log_le_log (show (0:ℝ)<((y+h:ℕ):ℝ) by exact_mod_cast (show 0 < y+h by omega)) (show ((y+h:ℕ):ℝ) ≤ (X:ℝ)*X by exact_mod_cast h2)
    rwa [Real.log_mul (by linarith) (by linarith), ← two_mul] at he
  have hqnon : (0:ℝ) ≤ Q.card := Nat.cast_nonneg _
  have hq2 := mul_le_mul_of_nonneg_left hlogQ hqnon
  change _ ≤ (Q.card:ℝ)*_ at hcount
  have hhreal : (s:ℝ)*t ≤ 2*h := by exact_mod_cast hhalf
  have hQ2 : (s:ℝ)*t/8 ≤ (Q.card:ℝ)*L := by linarith
  have key := mul_le_mul hP2 hQ2 (by positivity) (mul_nonneg hPc hL.le)
  have hsprod := mul_le_mul_of_nonneg_right hr2 (show 0 ≤ (s:ℝ)*t by positivity)
  push_cast
  rw [show (1/40:ℝ)*((s:ℝ)*t)*(r/L^2) = ((1/40:ℝ)*s*t*r)/L^2 by ring, div_le_iff₀ (by positivity)]
  nlinarith only [key,hsprod,show 0 ≤ (s:ℝ)*(s*t) by positivity]
end Goldbach.MovingFirstMass


/- The smoothing argument is adapted from GoldbachOC103 in PR #3746. Inflating
the high-zero and residual constants by 32 accommodates floors and shifts. -/
namespace Goldbach.MovingFirstMass
open GoldbachOC103 Vx V7e V86 V1e V6i
open scoped Classical
theorem scaled_principal_window
    (hzero : ActualZeroWeightBounds) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(3/4 : ℝ) ≤ 32*(h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/4 := by
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets (32*D) C (32*C) (by positivity)
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
    have he := hbud.high_budget
    have hid : 576*(32*C)*X^2*(Real.log X)^14/(X^(2/3:ℝ)*(X^(5/16:ℝ))^2) =
        32*(576*C*X^2*(Real.log X)^14/(X^(2/3:ℝ)*(X^(5/16:ℝ))^2)) := by ring
    rw [hid] at he
    linarith
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
    have he := hbud.residual_budget
    rw [mul_assoc] at he
    linarith
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


private theorem window : WindowInput := by
  obtain ⟨A,hA⟩ := scaled_principal_window actual_zero_weight_bounds
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨N,hN⟩ := exists_nat_ge (max (max A 1) (GoldbachPrimeBridge.primePowerCutoff (32*|C|)))
  refine ⟨N, fun y h hy hlen hhy => ?_⟩
  have hNy : (N:ℝ) ≤ y := by exact_mod_cast hy
  have hbound := hN.trans hNy
  have h1 := ((le_max_right A 1).trans (le_max_left _ _)).trans hbound
  have hψ := hA y (((le_max_left A 1).trans (le_max_left _ _)).trans hbound) h hlen (by exact_mod_cast hhy)
  rw [GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi] at hψ
  let z := max ((y:ℝ)^(3/4:ℝ)) (h:ℝ)
  have hz : z ≤ (y:ℝ) := max_le (by simpa using Real.rpow_le_rpow_of_exponent_le h1 (show (3/4:ℝ) ≤ 1 by norm_num)) (by exact_mod_cast hhy)
  have hz32 : z ≤ 32*(h:ℝ) := max_le hlen (by linarith [Nat.cast_nonneg (α:=ℝ) h])
  have he := GoldbachPrimeBridge.prime_power_error_small (32*|C|) (y:ℝ) z
    ((le_max_right _ _).trans hbound) (le_max_left _ _) hz
  have hs : Real.sqrt ((y:ℝ)+h) ≤ Real.sqrt ((y:ℝ)+z) :=
    Real.sqrt_le_sqrt (add_le_add_right (le_max_right _ _) _)
  have hC' := (hC ((y:ℝ)+h)).trans (mul_le_mul (le_abs_self C) hs (Real.sqrt_nonneg _) (abs_nonneg _))
  have hb := Chebyshev.theta_le_psi (y:ℝ)
  push_cast
  rw [mul_assoc] at he
  linarith [(abs_le.mp hψ).1]
end Goldbach.MovingFirstMass

theorem Conjectures.Goldbach.DynBlockFirstMass :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) :=
  Goldbach.MovingFirstMass.from_window Goldbach.MovingFirstMass.window
