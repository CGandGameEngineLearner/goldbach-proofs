import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
The explicit formula estimates are from LogTruSoul's Goldbach PR #3746,
revision ef8ddfa37003c69f326f69188c774106953d3969 (Apache-2.0).
The argument below uses the gap between the error exponent 17/24 and
the window exponent 3/4 to handle the rounded window and all its starts.
-/

namespace GoldbachDynBlockFirstMass
open Finset Filter
open scoped Topology BigOperators Classical

noncomputable section

open GoldbachOC103 Vx V7e V86 V1e V6i in
private theorem principal_window :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(35/48 : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/4 := by
  obtain ⟨C, hC, Xz, hz⟩ := actual_zero_weight_bounds
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets D C C hD.le
  have high := eventually_power_log_bound (17/24) (35/48) (576*C) (1/16) 14
    (by norm_num) (by norm_num)
  have residual := eventually_power_log_bound (2/3) (35/48) (3*D) (1/16) 1
    (by norm_num) (by norm_num)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop Xz, eventually_ge_atTop Xb, high, residual]
    with X hXz hXb hhighPower hresidualPower
  intro h hlower hupper
  have hbud := hb X hXb
  have hX4 := hbud.scale_ge_four
  have hXpos : 0 < X := by linarith
  have hδ : 0 < X^(2/3 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hV : 0 < X^(5/16 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  obtain ⟨hlo, hcount⟩ := hz X hXz hX4
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
    have heq :
        576*C*X^2*(Real.log X)^14/(X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2) =
          (576*C)*X^(17/24 : ℝ)*(Real.log X)^14 := by
      calc
        _ = (576*C)*(X^2/(X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2))*(Real.log X)^14 := by ring
        _ = _ := by rw [high_packet_power_identity X hXpos]
    rw [heq]
    linarith only [hhighPower.2, hlower]
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
    refine hres.trans ((mul_le_mul_of_nonneg_left
      (smoothing_residual_le X (by linarith)) hD.le).trans ?_)
    have hb' : D*(3*X^(2/3 : ℝ)*Real.log X) ≤ X^(35/48 : ℝ)/16 := by
      simpa only [pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul]
        using hresidualPower.2
    exact hb'.trans (div_le_div_of_nonneg_right hlower (by norm_num))
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

private theorem short_theta_floor :
    ∃ N : ℕ, ∀ x h : ℕ, N ≤ x →
      (x : ℝ)^(35/48 : ℝ) ≤ h → h ≤ x →
      (h : ℝ)/2 ≤ Chebyshev.theta ((x : ℝ)+h) - Chebyshev.theta x := by
  obtain ⟨T, hT⟩ := principal_window
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have herr := GoldbachOC103.eventually_power_log_bound (1/2) (35/48) (2 * |C|) (1/4) 0
    (by norm_num) (by norm_num)
  obtain ⟨R, hR⟩ := eventually_atTop.mp herr
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (max T R))
  refine ⟨N, ?_⟩
  intro x h hx hlower hupper
  have hxN : (max 1 (max T R)) ≤ (x : ℝ) := hN.trans (by exact_mod_cast hx)
  have hxT := (le_max_left T R).trans ((le_max_right _ _).trans hxN)
  have hxR := (le_max_right T R).trans ((le_max_right _ _).trans hxN)
  have hupper' : (h : ℝ) ≤ x := by exact_mod_cast hupper
  have hpsi := hT x hxT h hlower hupper'
  rw [GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi] at hpsi
  have hsqrt : Real.sqrt ((x : ℝ)+h) ≤ 2*Real.sqrt x := by
    calc
      _ ≤ Real.sqrt (4*(x : ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
        congr 1
        exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have hpp := hC ((x : ℝ)+h)
  have hpp' : C*Real.sqrt ((x : ℝ)+h) ≤ (h : ℝ)/4 := by
    calc
      _ ≤ |C| * (2*Real.sqrt x) :=
        mul_le_mul (le_abs_self C) hsqrt (Real.sqrt_nonneg _) (abs_nonneg _)
      _ = (2 * |C|)*(x : ℝ)^(1/2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        ring
      _ ≤ (x : ℝ)^(35/48 : ℝ)/4 := by
        simpa only [pow_zero, mul_one, one_mul, div_eq_mul_inv, one_div, mul_comm]
          using (hR x hxR).2
      _ ≤ _ := by linarith
  have hbase := Chebyshev.theta_le_psi (x : ℝ)
  linarith [(abs_le.mp hpsi).1]

private theorem theta_interval_le_card (a b : ℕ) (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta a ≤
      (((Ioc a b).filter Nat.Prime).card : ℝ) * Real.log b := by
  have hexpand (n : ℕ) : Chebyshev.theta (n : ℝ) =
      ∑ p ∈ Ioc 0 n, (if p.Prime then Real.log (p : ℝ) else 0) := by
    simp [Chebyshev.theta, sum_filter]
  let w := fun p : ℕ => if p.Prime then Real.log (p : ℝ) else 0
  have hsplit := Finset.sum_Ioc_consecutive w (Nat.zero_le a) hab
  have heq : Chebyshev.theta (b : ℝ) - Chebyshev.theta a =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p : ℝ) := by
    rw [hexpand, hexpand, sum_filter]
    change (∑ p ∈ Ioc 0 b, w p) - (∑ p ∈ Ioc 0 a, w p) = ∑ p ∈ Ioc a b, w p
    linarith
  rw [heq]
  calc
    _ ≤ ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (b : ℝ) := by
      refine sum_le_sum fun p hp => ?_
      have ⟨hpab, hpprime⟩ := mem_filter.mp hp
      exact Real.log_le_log (by exact_mod_cast hpprime.pos)
        (by exact_mod_cast (mem_Ioc.mp hpab).2)
    _ = _ := by simp

private theorem prime_window_card (N : ℕ)
    (hN : ∀ x h : ℕ, N ≤ x → (x : ℝ)^(35/48 : ℝ) ≤ h → h ≤ x →
      (h : ℝ)/2 ≤ Chebyshev.theta ((x : ℝ)+h) - Chebyshev.theta x)
    {X x h : ℕ} (hX : 2 ≤ X) (hx : N ≤ x)
    (hshort : (x : ℝ)^(35/48 : ℝ) ≤ h) (hlong : h ≤ x) (hend : x+h ≤ 2*X) :
    (h : ℝ) / (4*Real.log X) ≤ (((Ioc x (x+h)).filter Nat.Prime).card : ℝ) := by
  have hmass := hN x h hx hshort hlong
  have hcount := theta_interval_le_card x (x+h) (Nat.le_add_right _ _)
  rw [Nat.cast_add] at hcount
  have hX' : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos hX'
  have hlogend : Real.log ((x : ℝ)+h) ≤ 2*Real.log X := by
    by_cases hzero : x+h = 0
    · have hzero' : (x : ℝ)+h = 0 := by exact_mod_cast hzero
      rw [hzero', Real.log_zero]
      positivity
    · have hpos : 0 < (x : ℝ)+h := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      have hle : (x : ℝ)+h ≤ 2*(X : ℝ) := by exact_mod_cast hend
      have hX'' : (2 : ℝ) ≤ X := by exact_mod_cast hX
      calc
        _ ≤ Real.log ((X : ℝ)^2) := Real.log_le_log hpos (by nlinarith)
        _ = _ := by rw [Real.log_pow]; norm_num
  have hle := mul_le_mul_of_nonneg_left hlogend
    (Nat.cast_nonneg (α := ℝ) ((Ioc x (x+h)).filter Nat.Prime).card)
  apply (div_le_iff₀ (by positivity : 0 < 4*Real.log (X : ℝ))).mpr
  nlinarith

private theorem sqrt_cast_lower (x : ℕ) (hx : 1 ≤ x) :
    Real.sqrt (x : ℝ)/2 ≤ (Nat.sqrt x : ℝ) := by
  have hr : 1 ≤ Nat.sqrt x := Nat.le_sqrt.mpr (by simpa using hx)
  have ht := Nat.lt_floor_add_one (Real.sqrt (x : ℝ))
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt] at ht
  have hr' : (1 : ℝ) ≤ Nat.sqrt x := by exact_mod_cast hr
  linarith

private theorem block_scales :
    ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
      let s := Nat.sqrt X
      let W := s * Nat.sqrt s
      let h := W / 2
      3 ≤ s ∧ 2 ≤ X ∧ 2*s+h < W ∧ (W : ℝ)/3 ≤ h ∧
        ∀ y : ℕ, X ≤ y → y + W ≤ 2*X → (y : ℝ)^(35/48 : ℝ) ≤ h ∧ h ≤ y := by
  have hpower := GoldbachOC103.eventually_power_log_bound (35/48) (3/4) 2 (1/32) 0
    (by norm_num) (by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp hpower
  obtain ⟨N, hN⟩ := exists_nat_ge T
  refine ⟨max N 2401, ?_⟩
  intro X hX s W h
  have hXbig : 2401 ≤ X := (le_max_right _ _).trans hX
  have hs : 49 ≤ s := Nat.le_sqrt.mpr (by omega)
  have ht : 7 ≤ Nat.sqrt s := Nat.le_sqrt.mpr (by omega)
  have hW : 7*s ≤ W := by
    simpa only [W, Nat.mul_comm 7 s] using Nat.mul_le_mul_left s ht
  have hsmall : 2*s+h < W := by dsimp [h]; omega
  have hh : (W : ℝ)/3 ≤ h := by
    have hnat : W ≤ h*3 := by dsimp [h]; omega
    exact (div_le_iff₀ (by norm_num)).2 (by exact_mod_cast hnat)
  refine ⟨by omega, by omega, hsmall, hh, ?_⟩
  intro y hy hend
  have hXR : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hsR : Real.sqrt (X : ℝ)/2 ≤ (s : ℝ) := sqrt_cast_lower X (by omega)
  have htR : Real.sqrt (s : ℝ)/2 ≤ (Nat.sqrt s : ℝ) := sqrt_cast_lower s (by omega)
  have hroot : Real.sqrt (Real.sqrt (X : ℝ))/2 ≤ Real.sqrt (s : ℝ) := by
    rw [← Real.sqrt_sq (show 0 ≤ Real.sqrt (Real.sqrt (X : ℝ))/2 by positivity)]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg (X : ℝ))]
  have hWreal : (X : ℝ)^(3/4 : ℝ)/8 ≤ (W : ℝ) := by
    have heq : (X : ℝ)^(3/4 : ℝ) =
        Real.sqrt (X : ℝ) * Real.sqrt (Real.sqrt (X : ℝ)) := by
      simp only [Real.sqrt_eq_rpow, ← Real.rpow_mul hXR.le, ← Real.rpow_add hXR]
      norm_num
    have ht' : Real.sqrt (Real.sqrt (X : ℝ))/4 ≤ (Nat.sqrt s : ℝ) := by linarith
    have hm := mul_le_mul hsR ht' (by positivity)
      (Nat.cast_nonneg (α := ℝ) s)
    rw [heq]
    unfold W
    push_cast
    linarith
  have hscale : 2*(X : ℝ)^(35/48 : ℝ) ≤ (X : ℝ)^(3/4 : ℝ)/32 := by
    have hTX : T ≤ (X : ℝ) := hN.trans (by exact_mod_cast (le_max_left N 2401 |>.trans hX))
    simpa only [pow_zero, mul_one, one_mul, div_eq_mul_inv, one_div, mul_comm]
      using (hT X hTX).2
  have hy_le : (y : ℝ) ≤ 2*(X : ℝ) := by exact_mod_cast (show y ≤ 2*X by omega)
  have htwo : (2 : ℝ)^(35/48 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (35/48 : ℝ) ≤ 1)
  constructor
  · calc
      _ ≤ (2*(X : ℝ))^(35/48 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hy_le (by norm_num)
      _ ≤ 2*(X : ℝ)^(35/48 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) hXR.le]
        exact mul_le_mul_of_nonneg_right htwo (by positivity)
      _ ≤ (h : ℝ) := by linarith
  · dsimp [h]
    omega

end
end GoldbachDynBlockFirstMass

open Finset

open GoldbachDynBlockFirstMass in
theorem Conjectures.Goldbach.DynBlockFirstMass :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n); let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime; let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card; let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X); let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X); let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2; ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X → c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) := by
  intro E P H W B M
  obtain ⟨N, hN⟩ := short_theta_floor
  obtain ⟨K, hK⟩ := block_scales
  refine ⟨1/100, by norm_num, max K ((N+1)^2), ?_⟩
  intro X hX y hy hend
  let s := Nat.sqrt X
  let h := W X / 2
  have hXK := (le_max_left _ _).trans hX
  have hXN := (le_max_right _ _).trans hX
  obtain ⟨hs, hX2, hfit, hh, hscale⟩ := hK X hXK
  change 3 ≤ s at hs
  change 2*s+h < W X at hfit
  change (W X : ℝ)/3 ≤ (h : ℝ) at hh
  obtain ⟨hshort, hlong⟩ := hscale y hy hend
  change (y : ℝ)^(35/48 : ℝ) ≤ (h : ℝ) at hshort
  change h ≤ y at hlong
  have hsN : N ≤ s := by
    have hs1 : N+1 ≤ s := Nat.le_sqrt.mpr (by simpa [pow_two] using hXN)
    omega
  have hNy : N ≤ y := by
    have hsX := Nat.sqrt_le_self X
    change s ≤ X at hsX
    omega
  have hsX : s ≤ X := Nat.sqrt_le_self X
  let R := (Ioc y (y+h)).filter Nat.Prime
  have hsh : (s : ℝ)^(35/48 : ℝ) ≤ (s : ℝ) := by
    have h1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le h1
      (by norm_num : (35/48 : ℝ) ≤ 1)
  have hpcount := prime_window_card N hN hX2 hsN hsh le_rfl (show s+s ≤ 2*X by omega)
  have hqcount : (h : ℝ)/(4*Real.log X) ≤ (R.card : ℝ) :=
    prime_window_card N hN hX2 hNy hshort hlong (by omega)
  have hsmallset : (Ioc s (s+s)).filter Nat.Prime ⊆ P X := by
    intro p hp
    obtain ⟨hpwin, hpprime⟩ := mem_filter.mp hp
    obtain ⟨hpl, hpu⟩ := mem_Ioc.mp hpwin
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpl.le, by omega⟩, hpprime⟩
  have hpcard : (s : ℝ)/(4*Real.log X) ≤ ((P X).card : ℝ) :=
    hpcount.trans (by exact_mod_cast card_le_card hsmallset)
  -- The two prime windows form a rectangle of ordered representations inside the block.
  have hincidence :
      (P X).card * R.card ≤ ∑ n ∈ B X y, H X n := by
    let A := ((B X y ×ˢ P X).filter (fun np =>
      np.2 ≤ np.1 ∧ Nat.Prime (np.1 - np.2)))
    have hA : A.card = ∑ n ∈ B X y, H X n := by
      dsimp only [A]
      rw [card_filter, sum_product]
      refine sum_congr rfl fun n _ => ?_
      exact (card_filter _ _).symm
    rw [← hA, ← card_product]
    apply card_le_card_of_injOn (fun pq : ℕ × ℕ => (pq.1 + pq.2, pq.1))
    · rintro ⟨p,q⟩ hpq
      change (p,q) ∈ P X ×ˢ R at hpq
      obtain ⟨hp,hq⟩ := mem_product.mp hpq
      have ⟨hpwin,hpprime⟩ := mem_filter.mp hp
      have ⟨hpl,hpu⟩ := mem_Icc.mp hpwin
      change s ≤ p at hpl
      change p ≤ 2*s at hpu
      have ⟨hqwin,hqprime⟩ := mem_filter.mp hq
      have ⟨hql,hqu⟩ := mem_Ioc.mp hqwin
      have hpodd := hpprime.odd_of_ne_two (by omega)
      have hqodd := hqprime.odd_of_ne_two (by omega)
      have hn : p+q < y + W X := by omega
      have hnB : p+q ∈ B X y := mem_filter.mpr
        ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, hpodd.add_odd hqodd⟩,
          by omega, hn⟩
      change (p+q,p) ∈ A
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hnB,hp⟩, by omega, by simpa using hqprime⟩
    · rintro ⟨p,q⟩ _ ⟨p',q'⟩ _ he
      simp only [Prod.mk.injEq] at he
      exact Prod.ext he.2 (by omega)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hslow := sqrt_cast_lower X (by omega)
  change Real.sqrt (X : ℝ)/2 ≤ (s : ℝ) at hslow
  have hpbound : Real.sqrt (X : ℝ)/(8*Real.log X) ≤ ((P X).card : ℝ) := by
    apply le_trans _ hpcard
    rw [show (8:ℝ)*Real.log X = 2*(4*Real.log X) by ring, ← div_div]
    exact div_le_div_of_nonneg_right hslow (by positivity)
  have hqbound : (W X : ℝ)/(12*Real.log X) ≤ (R.card : ℝ) := by
    apply le_trans _ hqcount
    rw [show (12:ℝ)*Real.log X = 3*(4*Real.log X) by ring, ← div_div]
    exact div_le_div_of_nonneg_right hh (by positivity)
  have hprod := mul_le_mul hpbound hqbound
    (by positivity : 0 ≤ (W X : ℝ)/(12*Real.log X)) (Nat.cast_nonneg _)
  have hin : (((P X).card : ℝ) * (R.card : ℝ)) ≤ ∑ n ∈ B X y, (H X n : ℝ) := by
    exact_mod_cast hincidence
  refine le_trans ?_ (hprod.trans hin)
  dsimp only [M]
  have hpos := mul_nonneg (Nat.cast_nonneg (α := ℝ) (W X)) (Real.sqrt_nonneg (X : ℝ))
  field_simp [hlog.ne']
  nlinarith
