import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor

/-!
# Premise 1/2 of a cut of `L-goldbach-dyadic-cell-reflected-cancellation`

Every dyadic cell of length `2 ^ (k - k / 4)` in the central blocks
`[2^k / 2, 5 * 2^k / 8)` and its reflection `(3 * 2^k / 8, 2^k / 2]` carries
prime logarithmic weight between `0` and `101 / 100` times its length.

The analytic input is a *retuned* version of the pointwise short-interval
explicit formula of `Conjectures.Goldbach.DyadicCellShortPrimeFloor`: the same
zero-weight budgets, but with `1 / 400` in place of `1 / 16`, which gives
`|psi(x + h) - psi(x) - h| <= h / 100` for `x ^ (3 / 4) <= h <= x`.
The budgets hold eventually because every exponent is strictly inside the
available range (`17 / 24 < 3 / 4`, `2 / 3 < 3 / 4`).
-/

open Filter Finset
open scoped BigOperators Classical Topology

namespace Conjectures.Cuts.Task0b0706e7f141ead08767f3ce_aux

open GoldbachOC103
open Vx V7e V86 V1e V6i

/-! ## Retuned pointwise budget (adapted from `Conjectures.Goldbach.DyadicCellShortPrimeFloor`) -/

structure TightBudgets (D L H X : ℝ) : Prop where
  scale_ge_four : 4 ≤ X
  log_ge_one : 1 ≤ Real.log X
  smoothing_ge_one : 1 ≤ X^(2/3 : ℝ)
  smoothing_le_half : X^(2/3 : ℝ) ≤ X/2
  split_ge_two : 2 ≤ X^(5/16 : ℝ)
  split_le_scale : X^(5/16 : ℝ) ≤ X
  low_budget : 2*L/(Real.log X)^4 ≤ 1/400
  high_budget :
    576*H*X^2*(Real.log X)^14/
      (X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2) ≤ X^(3/4 : ℝ)/400
  residual_budget :
    D*(X^(2/3 : ℝ)*Real.log X +
      Real.sqrt X*Real.log X/X^(2/3 : ℝ) +
      X^2*Real.log X/(X^(2/3 : ℝ)*X)) ≤ X^(3/4 : ℝ)/400

theorem eventual_tight_budgets (D L H : ℝ) (hD : 0 ≤ D) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → TightBudgets D L H X := by
  have hd := eventually_power_log_bound (2/3) 1 2 1 0 (by norm_num) (by norm_num)
  have hr := eventually_power_log_bound (2/3) (3/4) (3*D) (1/400) 1
    (by norm_num) (by norm_num)
  have hh := eventually_power_log_bound (17/24) (3/4) (576*H) (1/400) 14
    (by norm_num) (by norm_num)
  have ht := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5/16)).eventually_ge_atTop 2
  have he : ∀ᶠ X : ℝ in atTop, TightBudgets D L H X := by
    filter_upwards [hd, hr, hh, ht, eventually_ge_atTop (4 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (800*L))]
      with X hδ hres hhi hV hX hlog
    have hX1 : 1 ≤ X := by linarith
    have hXp : 0 < X := by linarith
    have hL1 : 1 ≤ Real.log X := (le_max_left _ _).trans hlog
    have hL800 : 800*L ≤ Real.log X := (le_max_right _ _).trans hlog
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
      have h2 : 2 * L ≤ (1/400 : ℝ) * Real.log X := by linarith
      calc
        2 * L ≤ (1/400 : ℝ) * Real.log X := h2
        _ ≤ (1/400 : ℝ) * (Real.log X)^4 :=
          mul_le_mul_of_nonneg_left hp (by norm_num)
    · have hid := high_packet_power_identity X hXp
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
          mul_le_mul_of_nonneg_left (smoothing_residual_le X hX1) hD
        _ ≤ X^(3/4 : ℝ)/400 := by
          simpa only [pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul]
            using hres.2
  exact eventually_atTop.mp he

theorem tight_principal_window (hzero : ActualZeroWeightBounds) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(3/4 : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/100 := by
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_tight_budgets D C C hD.le
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
  have hLowBudget : 2*(h : ℝ)*(C/(Real.log X)^4) ≤ (h : ℝ)/400 := by
    calc
      _ = (h : ℝ)*(2*C/(Real.log X)^4) := by ring
      _ ≤ (h : ℝ)*(1/400) := mul_le_mul_of_nonneg_left hbud.low_budget hh
      _ = _ := by ring
  have hHighBudget : 576*X^2*K/(X^(2/3 : ℝ)*Real.sqrt (X^(5/16 : ℝ))) ≤
      (h : ℝ)/400 := by
    dsimp only [K]
    rw [high_coefficient_normalization C X (X^(5/16 : ℝ)) (X^(2/3 : ℝ)) hV hδ]
    exact hbud.high_budget.trans (div_le_div_of_nonneg_right hlower (by norm_num))
  have hPacketBudget :
      ‖V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
        (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/200 := by
    linarith
  have hres := hpoint X X (X^(2/3 : ℝ)) X h hX4
    ⟨le_rfl, by linarith⟩ hupper hbud.smoothing_ge_one hbud.smoothing_le_half
    (by linarith)
  have hResidualBudget :
      ‖V42 h X +
        V3q (fun u => ∑ c ∈ S, Ve u (h : ℝ) c.val.1)
          (X^(2/3 : ℝ)) X‖ ≤ (h : ℝ)/400 := by
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

theorem uniform_nat_window_tight :
    ∃ M : ℕ, ∀ x h : ℕ, M ≤ x →
      (x : ℝ)^(3/4 : ℝ) ≤ (h : ℝ) → h ≤ x →
      ‖V42 h (x : ℝ)‖ ≤ (h : ℝ)/100 := by
  obtain ⟨X₀, hX₀⟩ := tight_principal_window actual_zero_weight_bounds
  obtain ⟨M, hM⟩ := exists_nat_ge X₀
  refine ⟨M, ?_⟩
  intro x h hx hlower hupper
  exact hX₀ x (hM.trans (by exact_mod_cast hx)) h hlower (by exact_mod_cast hupper)

/-! ## From the smoothed window to `psi` -/

theorem tight_psi_window :
    ∃ M : ℕ, ∀ x h : ℕ, M ≤ x →
      (x : ℝ)^(3/4 : ℝ) ≤ (h : ℝ) → h ≤ x →
      |(Chebyshev.psi ((x : ℝ) + (h : ℝ)) - Chebyshev.psi (x : ℝ)) - (h : ℝ)| ≤
        (h : ℝ)/100 := by
  obtain ⟨M, hM⟩ := uniform_nat_window_tight
  refine ⟨M, fun x h hx hl hu => ?_⟩
  rw [← GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi]
  exact hM x h hx hl hu

/-! ## Prime logarithmic weight inside a window -/

noncomputable def w (p : ℕ) : ℝ := if Nat.Prime p then Real.log (p : ℝ) else 0

theorem w_nonneg (p : ℕ) : 0 ≤ w p := by
  dsimp [w]
  split_ifs
  · exact Real.log_natCast_nonneg p
  · exact le_refl 0

theorem w_le_mangoldt (p : ℕ) : w p ≤ (ArithmeticFunction.vonMangoldt p : ℝ) := by
  dsimp [w]
  by_cases hp : Nat.Prime p
  · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime]
  · simp [hp]

theorem cell_upper (M : ℕ)
    (hwin : ∀ x h : ℕ, M ≤ x → (x : ℝ)^(3/4 : ℝ) ≤ (h : ℝ) → h ≤ x →
      |(Chebyshev.psi ((x : ℝ) + (h : ℝ)) - Chebyshev.psi (x : ℝ)) - (h : ℝ)| ≤
        (h : ℝ)/100)
    {a H : ℕ} (hM : M ≤ a) (hpow : (a : ℝ)^(3/4 : ℝ) ≤ (H : ℝ)) (hH : H ≤ a) :
    ∑ p ∈ Finset.Ioc a (a + H), w p ≤ 101 * (H : ℝ) / 100 := by
  have hb := hwin a H hM hpow hH
  rw [GoldbachPrimeBridge.psi_nat_add_sub] at hb
  have h1 : ∑ p ∈ Finset.Ioc a (a + H), w p ≤
      ∑ p ∈ Finset.Ioc a (a + H), (ArithmeticFunction.vonMangoldt p : ℝ) :=
    Finset.sum_le_sum (fun p _ => w_le_mangoldt p)
  have h2 := (abs_le.mp hb).2
  linarith

end Conjectures.Cuts.Task0b0706e7f141ead08767f3ce_aux

open Conjectures.Cuts.Task0b0706e7f141ead08767f3ce_aux

theorem Conjectures.Cuts.Task0b0706e7f141ead08767f3ce :
    (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log ↑x1 else (0 : ℝ); ∃ (x2 : ℕ),   ∀ x3 ≥ x2,     have x5 : ℕ := (2 : ℕ) ^ x3;     have x6 : ℕ := (2 : ℕ) ^ (x3 - x3 / (4 : ℕ));     have x7 : ℕ := (2 : ℕ) ^ (x3 / (4 : ℕ) - (3 : ℕ));     have x8 : ℕ → ℕ → ℕ := fun (x8 x9 : ℕ) => x5 / (2 : ℕ) + x8 * x6 + x9;     have x9 : ℕ → ℕ → ℝ := fun (x9 x10 : ℕ) => x1 (x8 x9 x10);     have x10 : ℕ → ℕ → ℝ := fun (x10 x11 : ℕ) => x1 (x5 - x8 x10 x11);     ∀ x11 ∈ Finset.range x7, ((0 : ℝ) ≤ ∑ x13 ∈ Finset.range x6, x9 x11 x13 ∧ ∑ x13 ∈ Finset.range x6, x9 x11 x13 ≤ (101 : ℝ) * ↑x6 / (100 : ℝ)) ∧ (0 : ℝ) ≤ ∑ x13 ∈ Finset.range x6, x10 x11 x13 ∧ ∑ x13 ∈ Finset.range x6, x10 x11 x13 ≤ (101 : ℝ) * ↑x6 / (100 : ℝ)) := by
  obtain ⟨M, hwin⟩ := tight_psi_window
  refine ⟨M + 20, ?_⟩
  intro k hk
  dsimp only
  intro j hj
  set X : ℕ := 2 ^ k
  set H : ℕ := 2 ^ (k - k / 4)
  set C : ℕ := 2 ^ (k / 4 - 3)
  have hk20 : 20 ≤ k := by omega
  have hjC : j < C := Finset.mem_range.mp hj
  have hk4 : 3 ≤ k / 4 := by omega
  change ((0 : ℝ) ≤ ∑ x13 ∈ Finset.range H, w (X / 2 + j * H + x13) ∧
      ∑ x13 ∈ Finset.range H, w (X / 2 + j * H + x13) ≤ 101 * (H : ℝ) / 100) ∧
    ((0 : ℝ) ≤ ∑ x13 ∈ Finset.range H, w (X - (X / 2 + j * H + x13)) ∧
      ∑ x13 ∈ Finset.range H, w (X - (X / 2 + j * H + x13)) ≤ 101 * (H : ℝ) / 100)
  have hCH : C * H = 2 ^ (k - 3) := by
    dsimp [C, H]
    rw [← pow_add]
    congr 1
    omega
  have hXdef : X = 2 * 2 ^ (k - 1) := by
    dsimp [X]
    have hk1 : k = (k - 1) + 1 := by omega
    conv_lhs => rw [hk1]
    rw [pow_succ']
  have hXhalf : X / 2 = 2 ^ (k - 1) := by
    rw [hXdef]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hXeven : X = 2 * (X / 2) := by rw [hXhalf]; exact hXdef
  have h8H : 8 * H ≤ X := GoldbachDyadicBridge.eight_mul_length_le_dyadic k (by omega)
  have hk3 : 2 ^ (k - 1) = 4 * 2 ^ (k - 3) := by
    have hk1 : k - 1 = (k - 3) + 2 := by omega
    rw [hk1, pow_add]
    ring
  have hP1 : 1 ≤ 2 ^ (k - 3) := Nat.one_le_two_pow
  have hMP : M < 2 ^ (k - 3) := by
    have hMlt : M < 2 ^ M := Nat.lt_two_pow_self
    calc M < 2 ^ M := hMlt
      _ ≤ 2 ^ (k - 3) := pow_le_pow_right' (by decide) (by omega)
  have hCHle : C * H ≤ X / 2 := by
    rw [hCH, hXhalf, hk3]
    omega
  have hjH : j * H ≤ C * H := Nat.mul_le_mul_right H (le_of_lt hjC)
  have hjHle : j * H ≤ X / 2 := le_trans hjH hCHle
  have hAH : j * H + H ≤ C * H := by
    have h1 : j * H + H = (j + 1) * H := by ring
    rw [h1]
    exact Nat.mul_le_mul_right H (by omega)
  have hAHle : j * H + H ≤ X / 2 := le_trans hAH hCHle
  have hH1 : 1 ≤ H := Nat.one_le_two_pow
  -- the forward cell
  have hx0 : 1 ≤ X / 2 + j * H := by omega
  have hx0le : X / 2 + j * H ≤ X := by omega
  have hS1 : (∑ x13 ∈ Finset.range H, w (X / 2 + j * H + x13))
      = ∑ p ∈ Finset.Ioc (X / 2 + j * H - 1) (X / 2 + j * H - 1 + H), w p :=
    (GoldbachDyadicBridge.sum_Ioc_pred_eq_range w (X / 2 + j * H) H hx0).symm
  have hM1 : M ≤ X / 2 + j * H - 1 := by omega
  have hHle1 : H ≤ X / 2 + j * H - 1 := by omega
  have hpow1 : ((X / 2 + j * H - 1 : ℕ) : ℝ)^(3/4 : ℝ) ≤ (H : ℝ) :=
    GoldbachDyadicBridge.rpow_three_quarters_le_of_cube_le_fourth _ _
      ((pow_le_pow_left' (by omega : X / 2 + j * H - 1 ≤ X) 3).trans
        (GoldbachDyadicBridge.dyadic_cube_le_length_fourth k))
  have hU1 : (∑ x13 ∈ Finset.range H, w (X / 2 + j * H + x13)) ≤
      101 * (H : ℝ) / 100 := by
    rw [hS1]
    exact cell_upper M hwin hM1 hpow1 hHle1
  -- the reflected cell
  have hm : H ≤ X / 2 - j * H := by omega
  have hS2 : (∑ x13 ∈ Finset.range H, w (X - (X / 2 + j * H + x13)))
      = ∑ p ∈ Finset.Ioc (X / 2 - j * H - H + 1 - 1)
          (X / 2 - j * H - H + 1 - 1 + H), w p := by
    calc
      (∑ x13 ∈ Finset.range H, w (X - (X / 2 + j * H + x13)))
          = ∑ t ∈ Finset.range H, w (X / 2 - j * H - t) := by
            refine Finset.sum_congr rfl (fun t ht => ?_)
            have ht' : t < H := Finset.mem_range.mp ht
            have hAt : j * H + t ≤ X / 2 := by omega
            congr 1
            omega
      _ = ∑ s ∈ Finset.range H, w (X / 2 - j * H - H + 1 + s) := by
            rw [← Finset.sum_range_reflect (fun s => w (X / 2 - j * H - H + 1 + s)) H]
            refine Finset.sum_congr rfl (fun t ht => ?_)
            have ht' : t < H := Finset.mem_range.mp ht
            congr 1
            omega
      _ = ∑ p ∈ Finset.Ioc (X / 2 - j * H - H + 1 - 1)
            (X / 2 - j * H - H + 1 - 1 + H), w p :=
            (GoldbachDyadicBridge.sum_Ioc_pred_eq_range w
              (X / 2 - j * H - H + 1) H (by omega)).symm
  have hM2 : M ≤ X / 2 - j * H - H + 1 - 1 := by omega
  have hHle2 : H ≤ X / 2 - j * H - H + 1 - 1 := by omega
  have hpow2 : ((X / 2 - j * H - H + 1 - 1 : ℕ) : ℝ)^(3/4 : ℝ) ≤ (H : ℝ) :=
    GoldbachDyadicBridge.rpow_three_quarters_le_of_cube_le_fourth _ _
      ((pow_le_pow_left' (by omega : X / 2 - j * H - H + 1 - 1 ≤ X) 3).trans
        (GoldbachDyadicBridge.dyadic_cube_le_length_fourth k))
  have hU2 : (∑ x13 ∈ Finset.range H, w (X - (X / 2 + j * H + x13))) ≤
      101 * (H : ℝ) / 100 := by
    rw [hS2]
    exact cell_upper M hwin hM2 hpow2 hHle2
  exact ⟨⟨Finset.sum_nonneg (fun t _ => w_nonneg _), hU1⟩,
    ⟨Finset.sum_nonneg (fun t _ => w_nonneg _), hU2⟩⟩
