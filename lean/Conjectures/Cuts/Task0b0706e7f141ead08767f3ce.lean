import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-! The analytic assembly below adapts GoldbachOC103.actual_principal_window_of_zero_weights
from the verified DyadicCellShortPrimeFloor module (Apache-2.0). Applying its
eventual budgets to 100 times each constant yields a one-percent bound.
The endpoint reflection uses the indexing from DyadicCellWindowTransfer. -/
noncomputable section
open Finset
open scoped BigOperators Classical
namespace GoldbachDyadicCellUpper
open GoldbachOC103 Vx V7e V86 V1e V6i
private theorem window_one_percent
    (hzero : ActualZeroWeightBounds) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(3/4 : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/100 := by
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets (100*D) (100*C) (100*C) (by positivity)
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
  have hlow' : 100*(2*C/(Real.log X)^4) ≤ 1/16 := by
    convert hbud.low_budget using 1; ring
  have hhigh' : 100*(576*C*X^2*(Real.log X)^14/(X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2)) ≤ X^(3/4 : ℝ)/16 := by
    convert hbud.high_budget using 1; ring
  have hres' : 100*(D*(X^(2/3 : ℝ)*Real.log X + Real.sqrt X*Real.log X/X^(2/3 : ℝ)
      +X^2*Real.log X/(X^(2/3 : ℝ)*X))) ≤ X^(3/4 : ℝ)/16 := by
    convert hbud.residual_budget using 1; ring
  have hLowBudget : 2*(h : ℝ)*(C/(Real.log X)^4) ≤ (h : ℝ)/1600 := by
    calc
      _ = (h : ℝ)*(2*C/(Real.log X)^4) := by ring
      _ ≤ (h : ℝ)*(1/1600) := mul_le_mul_of_nonneg_left (by linarith only [hlow']) hh
      _ = _ := by ring
  have hHighBudget : 576*X^2*K/(X^(2/3 : ℝ)*Real.sqrt (X^(5/16 : ℝ))) ≤
      (h : ℝ)/1600 := by
    dsimp only [K]
    rw [high_coefficient_normalization C X (X^(5/16 : ℝ)) (X^(2/3 : ℝ)) hV hδ]
    linarith only [hhigh', hlower]
  have hPacketBudget :
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
        (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/800 := by
    linarith
  have hres := hpoint X X (X^(2/3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have hResidualBudget :
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/1600 := by
    exact hres.trans (by linarith only [hres', hlower])
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


private theorem central_bound :
    ∃ K : ℕ, ∀ k ≥ K, ∀ x : ℕ, 2^k ≤ 3*x → 3*x ≤ 2*2^k →
      let H : ℕ := 2^(k-k/4)
      (∑ t ∈ Finset.range H, GoldbachDyadicBridge.primeLog (x+t)) ≤ 101*(H:ℝ)/100 := by
  obtain ⟨X₀, hX₀⟩ := window_one_percent actual_zero_weight_bounds
  obtain ⟨M,hM⟩ := exists_nat_ge X₀
  refine ⟨4*(M+1)+12, ?_⟩
  intro k hk x hleft hright
  let H : ℕ := 2^(k-k/4)
  have ⟨hx,hpower,hlen⟩ :=
    GoldbachDyadicBridge.central_start_scales (M+1) k x hk hleft hright
  have h8 := GoldbachDyadicBridge.eight_mul_length_le_dyadic k (by omega)
  have hHp : 0 < H := pow_pos (by decide) _
  have hle : H ≤ x-1 := by dsimp [H]; omega
  have hy : M ≤ x-1 := by omega
  have hpow : (x-1)^3 ≤ H^4 := (pow_le_pow_left' (Nat.sub_le x 1) 3).trans hpower
  have he := hX₀ (x-1 : ℕ) (hM.trans (by exact_mod_cast hy)) H
    (GoldbachDyadicBridge.rpow_three_quarters_le_of_cube_le_fourth _ _ hpow)
    (by exact_mod_cast hle)
  rw [GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi,
      GoldbachPrimeBridge.psi_nat_add_sub] at he
  change (∑ t ∈ Finset.range H, GoldbachDyadicBridge.primeLog (x+t)) ≤ _
  rw [← GoldbachDyadicBridge.sum_Ioc_pred_eq_range _ _ _ (by omega : 1 ≤ x)]
  have hdom : ∀ i : ℕ, GoldbachDyadicBridge.primeLog i ≤ ArithmeticFunction.vonMangoldt i := by
    intro i
    simp only [GoldbachDyadicBridge.primeLog]
    split_ifs with hp
    · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
    · exact ArithmeticFunction.vonMangoldt_nonneg
  exact (Finset.sum_le_sum (fun i _ => hdom i)).trans (by linarith only [(abs_le.mp he).2])

end GoldbachDyadicCellUpper

theorem Conjectures.Cuts.Task0b0706e7f141ead08767f3ce :
have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); ∃ (x2 : ℕ),   ∀ x3 ≥ x2,     have x5 : ℕ := (2 : ℕ) ^ x3;     have x6 : ℕ := (2 : ℕ) ^ (x3 - x3 / (4 : ℕ));     have x7 : ℕ := (2 : ℕ) ^ (x3 / (4 : ℕ) - (3 : ℕ));     have x8 : ℕ → ℕ → ℕ := fun (x8 x9 : ℕ) => x5 / (2 : ℕ) + x8 * x6 + x9;     have x9 : ℕ → ℕ → ℝ := fun (x9 x10 : ℕ) => x1 (x8 x9 x10);     have x10 : ℕ → ℕ → ℝ := fun (x10 x11 : ℕ) => x1 (x5 - x8 x10 x11);     ∀ x11 ∈ Finset.range x7, ((0 : ℝ) ≤ ∑ x13 ∈ Finset.range x6, x9 x11 x13 ∧ ∑ x13 ∈ Finset.range x6, x9 x11 x13 ≤ (101 : ℝ) * ↑x6 / (100 : ℝ)) ∧ (0 : ℝ) ≤ ∑ x13 ∈ Finset.range x6, x10 x11 x13 ∧ ∑ x13 ∈ Finset.range x6, x10 x11 x13 ≤ (101 : ℝ) * ↑x6 / (100 : ℝ) := by
  obtain ⟨K,hK⟩ := GoldbachDyadicCellUpper.central_bound
  refine ⟨max K 12, ?_⟩
  intro k hk
  have hk12 : 12 ≤ k := (le_max_right _ _).trans hk
  set n : ℕ := 2^k with hn
  set H : ℕ := 2^(k-k/4) with hH
  set B : ℕ := 2^(k/4-3) with hB
  dsimp only
  intro j hj
  have hjlt := Finset.mem_range.mp hj
  have hprod : B*H*8 = n := by
    rw [hB,hH,hn,←pow_add,show (8:ℕ)=2^3 by decide,←pow_add]
    congr 1
    omega
  have hHpos : 0 < H := by rw [hH]; positivity
  have hblock : j*H+H ≤ B*H := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right H hjlt
  let start := n/2+j*H
  let back := n-(start+(H-1))
  have hf := hK k ((le_max_left _ _).trans hk) start
      (by change n ≤ 3*(n/2+j*H); omega)
      (by change 3*(n/2+j*H) ≤ 2*n; omega)
  have hb := hK k ((le_max_left _ _).trans hk) back
      (by change n ≤ 3*(n-(n/2+j*H+(H-1))); omega)
      (by change 3*(n-(n/2+j*H+(H-1))) ≤ 2*n; omega)
  let w := GoldbachDyadicBridge.primeLog
  have hw (i : ℕ) : 0 ≤ w i := by
    simp only [w,GoldbachDyadicBridge.primeLog]
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
    · exact le_rfl
  have hreflect : (∑ t ∈ Finset.range H, w (n-(start+t))) =
      ∑ t ∈ Finset.range H, w (back+t) := by
    calc
      _ = ∑ t ∈ Finset.range H, w (back+(H-1-t)) := by
        apply Finset.sum_congr rfl
        intro t ht
        have htr := Finset.mem_range.mp ht
        congr 1
        dsimp [back,start]
        omega
      _ = _ := Finset.sum_range_reflect (fun t => w (back+t)) H
  change (0 ≤ ∑ t ∈ Finset.range H, w (start+t) ∧ _ ) ∧
    0 ≤ ∑ t ∈ Finset.range H, w (n-(start+t)) ∧
    (∑ t ∈ Finset.range H, w (n-(start+t))) ≤ _
  exact ⟨⟨Finset.sum_nonneg (fun i _ => hw _),hf⟩,
    Finset.sum_nonneg (fun i _ => hw _),hreflect.trans_le hb⟩
