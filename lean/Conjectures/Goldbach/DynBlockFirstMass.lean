import Mathlib
import Conjectures.Goldbach.DyadicCellShortPrimeFloor
import Conjectures.Goldbach.DynShiftFactorMean

namespace FirstMass

open Finset Filter GoldbachOC103 Vx V7e V86 V1e V6i
open scoped BigOperators Classical

noncomputable section

/-- The high packet and smoothing errors have strict power slack at exponent
35/48. The other pointwise budgets depend only on the smoothing parameters. -/
private theorem short_error_budgets (D H : ℝ) (hD : 0 ≤ D) :
    ∀ᶠ X : ℝ in atTop,
      576 * H * X^2 * (Real.log X)^14 /
          (X^(2/3 : ℝ) * (X^(5/16 : ℝ))^2) ≤ X^(35/48 : ℝ)/16 ∧
      D * (X^(2/3 : ℝ) * Real.log X +
        Real.sqrt X * Real.log X / X^(2/3 : ℝ) +
        X^2 * Real.log X / (X^(2/3 : ℝ) * X)) ≤ X^(35/48 : ℝ)/16 := by
  have hres := eventually_power_log_bound (2/3) (35/48) (3*D) (1/16) 1
    (by norm_num) (by norm_num)
  have hhi := eventually_power_log_bound (17/24) (35/48) (576*H) (1/16) 14
    (by norm_num) (by norm_num)
  filter_upwards [hres, hhi, eventually_ge_atTop (1 : ℝ)] with X hres hhi hX
  refine ⟨?_, ?_⟩
  · have hid := high_packet_power_identity X hhi.1
    calc
      _ = (576*H)*(X^2/(X^(2/3 : ℝ)*(X^(5/16 : ℝ))^2))*(Real.log X)^14 := by ring
      _ = 576*H*X^(17/24 : ℝ)*(Real.log X)^14 := by rw [hid]
      _ ≤ _ := by simpa only [div_eq_mul_inv, mul_comm, one_mul] using hhi.2
  · calc
      _ ≤ D*(3*X^(2/3 : ℝ)*Real.log X) :=
        mul_le_mul_of_nonneg_left (smoothing_residual_le X hX) hD
      _ ≤ _ := by
        simpa only [pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, one_mul] using hres.2

private theorem principal_window
    (hzero : ActualZeroWeightBounds) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ h : ℕ,
      X^(35/48 : ℝ) ≤ (h : ℝ) → (h : ℝ) ≤ X →
      ‖V42 h X‖ ≤ (h : ℝ)/4 := by
  obtain ⟨C, hC, Xz, hz⟩ := hzero
  obtain ⟨D, hD, hpoint⟩ := V10s
  obtain ⟨Xb, hb⟩ := eventual_pointwise_budgets D C C hD.le
  obtain ⟨Xa, ha⟩ := eventually_atTop.mp (short_error_budgets D C hD.le)
  refine ⟨max (max Xz Xb) Xa, ?_⟩
  intro X hX h hlower hupper
  have hXzb := (le_max_left _ _).trans hX
  have hbud := hb X ((le_max_right _ _).trans hXzb)
  obtain ⟨hhighBudget, hresidualBudget⟩ := ha X ((le_max_right _ _).trans hX)
  have hX4 := hbud.scale_ge_four
  have hXpos : 0 < X := by linarith
  have hδ : 0 < X^(2/3 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hV : 0 < X^(5/16 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  obtain ⟨hlo, hcount⟩ := hz X ((le_max_left _ _).trans hXzb) hX4
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
    exact hhighBudget.trans (div_le_div_of_nonneg_right hlower (by norm_num))
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
    exact hres.trans (hresidualBudget.trans
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

/-- A uniform short-interval floor for prime logarithmic weights. -/
theorem short_prime_weight : ∃ N : ℕ, ∀ z h : ℕ, N ≤ z →
    (z : ℝ) ^ (35/48 : ℝ) ≤ (h : ℝ) → h ≤ z →
    (h : ℝ) / 2 ≤ ∑ q ∈ Finset.Ioc z (z+h), (if Nat.Prime q then Real.log (q : ℝ) else 0) := by
  obtain ⟨X₀, hwindow⟩ := principal_window actual_zero_weight_bounds
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  obtain ⟨Y₀, herror⟩ := eventually_atTop.mp
    (eventually_power_log_bound (1/2) (35/48) (2*|C|) (1/4) 0 (by norm_num) (by norm_num))
  obtain ⟨N, hN⟩ := exists_nat_ge (max X₀ Y₀)
  refine ⟨N, ?_⟩
  intro z h hz hlo hhi
  have hzmax : max X₀ Y₀ ≤ (z : ℝ) := hN.trans (by exact_mod_cast hz)
  have hhiz : (h : ℝ) ≤ z := by exact_mod_cast hhi
  have hψ := hwindow z ((le_max_left ..).trans hzmax) h hlo hhiz
  rw [GoldbachR11WindowBridge.norm_actual_principal_window_eq_abs_psi] at hψ
  have hψlo := (abs_le.mp hψ).1
  have hsqrt : Real.sqrt ((z : ℝ) + h) ≤ 2 * Real.sqrt z := by
    calc
      _ ≤ Real.sqrt (4 * (z : ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have hpower := (herror z ((le_max_right ..).trans hzmax)).2
  rw [← Real.sqrt_eq_rpow] at hpower
  norm_num only [pow_zero, mul_one] at hpower
  have hpp : Chebyshev.psi ((z : ℝ) + h) - Chebyshev.theta ((z : ℝ) + h) ≤ (h : ℝ)/4 := by
    calc
      _ ≤ C * Real.sqrt ((z : ℝ) + h) := hC _
      _ ≤ |C| * (2 * Real.sqrt z) :=
        mul_le_mul (le_abs_self C) hsqrt (Real.sqrt_nonneg _) (abs_nonneg _)
      _ ≤ (h : ℝ)/4 := by linarith only [hpower, hlo]
  have hbase := Chebyshev.theta_le_psi (z : ℝ)
  have htheta : (h : ℝ)/2 ≤ Chebyshev.theta ((z : ℝ) + h) - Chebyshev.theta z := by linarith
  rw [GoldbachDyadicBridge.theta_nat_add_sub] at htheta
  simpa only [GoldbachDyadicBridge.primeLog] using htheta

end
end FirstMass

namespace FirstMass

open Filter

private theorem sqrt_half_le_floor (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) / 2 ≤ (n.sqrt : ℝ) := by
  have hn' : (1 : ℝ) ≤ n.sqrt := by
    exact_mod_cast Nat.le_sqrt.mpr (by simpa using hn : 1 * 1 ≤ n)
  have h := Nat.lt_floor_add_one (Real.sqrt (n : ℝ))
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt] at h
  linarith only [h, hn']

/-- The large-prime window fits inside the block and retains a fixed fraction of its length. -/
private theorem scales :
    ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ,
      let s := X.sqrt
      let W := s*s.sqrt
      let h := W - 2*s - 1
      X ≤ y → y + W ≤ 2*X →
        3 ≤ s ∧ (y : ℝ)^(35/48 : ℝ) ≤ (h : ℝ) ∧ h ≤ y ∧
          (W : ℝ)/2 ≤ (h : ℝ) ∧ Real.sqrt (X : ℝ)/2 ≤ (s : ℝ) := by
  have hrpow : ∀ᶠ n : ℕ in atTop, (32 : ℝ) ≤ (n : ℝ)^(1/48 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/48)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 32
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (1296 : ℕ), hrpow] with X hX hpower
  intro y
  let s := X.sqrt
  let W := s*s.sqrt
  let h := W - 2*s - 1
  change X ≤ y → y + W ≤ 2*X →
    3 ≤ s ∧ (y : ℝ)^(35/48 : ℝ) ≤ (h : ℝ) ∧ h ≤ y ∧
      (W : ℝ)/2 ≤ (h : ℝ) ∧ Real.sqrt (X : ℝ)/2 ≤ (s : ℝ)
  intro hxy hyW
  have hs : 36 ≤ s := Nat.le_sqrt.mpr (by norm_num; exact hX)
  have ht : 6 ≤ s.sqrt := Nat.le_sqrt.mpr (by norm_num; exact hs)
  have hWle : W ≤ X :=
    (Nat.mul_le_mul_left s (Nat.sqrt_le_self s)).trans (Nat.sqrt_le X)
  have hWge : 6*s ≤ W := by
    simpa only [Nat.mul_comm 6 s] using Nat.mul_le_mul_left s ht
  have hhalf : (W : ℝ)/2 ≤ (h : ℝ) := by
    have hf : W ≤ 2*h := by dsimp only [h]; omega
    have hf' : (W : ℝ) ≤ 2*(h : ℝ) := by exact_mod_cast hf
    linarith only [hf']
  have hsmall : Real.sqrt (X : ℝ)/2 ≤ (s : ℝ) := sqrt_half_le_floor X (by omega)
  have hlarge : Real.sqrt (s : ℝ)/2 ≤ (s.sqrt : ℝ) := sqrt_half_le_floor s (by omega)
  refine ⟨by omega, ?_, (show h ≤ W by dsimp [h]; omega).trans (hWle.trans hxy),
    hhalf, hsmall⟩
  have hn : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hS : (X : ℝ)^(1/2 : ℝ)/2 ≤ (s : ℝ) := by
    rwa [← Real.sqrt_eq_rpow]
  have hTaux : Real.sqrt (Real.sqrt (X : ℝ))/2 ≤ Real.sqrt (s : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, Real.sq_sqrt (Real.sqrt_nonneg (X : ℝ))]
    linarith only [hsmall, Real.sqrt_nonneg (X : ℝ)]
  have hT : (X : ℝ)^(1/4 : ℝ)/4 ≤ (s.sqrt : ℝ) := by
    have he : Real.sqrt (Real.sqrt (X : ℝ)) = (X : ℝ)^(1/4 : ℝ) := by
      rw [Real.sqrt_eq_rpow (Real.sqrt _), Real.sqrt_eq_rpow (X : ℝ),
        ← Real.rpow_mul hn.le, show (1/2 : ℝ)*(1/2) = 1/4 by norm_num]
    linarith only [hTaux, hlarge, he]
  have hgrow : (X : ℝ)^(3/4 : ℝ)/8 ≤ (W : ℝ) := by
    rw [show (3/4 : ℝ) = 1/2+1/4 by norm_num, Real.rpow_add hn]
    calc
      _ = ((X : ℝ)^(1/2 : ℝ)/2) * ((X : ℝ)^(1/4 : ℝ)/4) := by ring
      _ ≤ (s : ℝ)*(s.sqrt : ℝ) := mul_le_mul hS hT (by positivity) (by positivity)
      _ = _ := by simp [W]
  have hlen : (X : ℝ)^(3/4 : ℝ)/16 ≤ (h : ℝ) := by
    linarith only [hgrow, hhalf]
  have hy : (y : ℝ) ≤ 2*(X : ℝ) := by exact_mod_cast (show y ≤ 2*X by omega)
  calc
    (y : ℝ)^(35/48 : ℝ) ≤ (2*(X : ℝ))^(35/48 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hy (by norm_num)
    _ ≤ 2*(X : ℝ)^(35/48 : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn.le]
      have htwo : (2 : ℝ)^(35/48 : ℝ) ≤ 2 := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (by norm_num : (35/48 : ℝ) ≤ 1)
      exact mul_le_mul_of_nonneg_right htwo (by positivity)
    _ ≤ (X : ℝ)^(3/4 : ℝ)/16 := by
      rw [show (3/4 : ℝ) = 35/48+1/48 by norm_num, Real.rpow_add hn]
      have he := mul_le_mul_of_nonneg_left hpower
        (Real.rpow_nonneg hn.le (35/48 : ℝ))
      linarith only [he]
    _ ≤ (h : ℝ) := hlen

end FirstMass

namespace FirstMass

open Finset
noncomputable section

private def primeBand (X : ℕ) := (Icc X.sqrt (2 * X.sqrt)).filter Nat.Prime

private def blockLength (X : ℕ) := X.sqrt * X.sqrt.sqrt

private def block (X y : ℕ) :=
  ((Icc X (2 * X)).filter Even).filter (fun n => y ≤ n ∧ n < y + blockLength X)

private def largePrimes (y h : ℕ) := (Ioc y (y + h)).filter Nat.Prime

/-- A pair in the interior rectangle determines an endpoint and its small prime. -/
private theorem arrivals {X y h : ℕ} (hs : 3 ≤ X.sqrt) (hy : X ≤ y)
    (hwindow : y + blockLength X ≤ 2 * X) (hfit : h + 2 * X.sqrt < blockLength X) :
    (primeBand X).card * (largePrimes y h).card ≤
      ∑ n ∈ block X y, ((primeBand X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card := by
  let T := ((block X y) ×ˢ (primeBand X)).filter
    (fun x => x.2 ≤ x.1 ∧ Nat.Prime (x.1 - x.2))
  have count_eq : T.card = ∑ n ∈ block X y,
      ((primeBand X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card := by
    dsimp only [T]
    rw [card_filter, sum_product]
    exact sum_congr rfl (fun n _ => (card_filter _ _).symm)
  rw [← count_eq, ← card_product]
  apply card_le_card_of_injOn (fun x : ℕ × ℕ => (x.2 + x.1, x.1))
  · rintro ⟨p, q⟩ hpq
    change (p, q) ∈ primeBand X ×ˢ largePrimes y h at hpq
    obtain ⟨hp, hq⟩ := mem_product.mp hpq
    obtain ⟨hpI, hpPrime⟩ := mem_filter.mp hp
    obtain ⟨hqI, hqPrime⟩ := mem_filter.mp hq
    obtain ⟨hps, hpmax⟩ := mem_Icc.mp hpI
    obtain ⟨hqy, hqmax⟩ := mem_Ioc.mp hqI
    have hX9 : 9 ≤ X := Nat.le_sqrt.mp hs
    have heven : Even (q + p) := (hqPrime.odd_of_ne_two (by omega)).add_odd
      (hpPrime.odd_of_ne_two (by omega))
    have hnp : q + p - p = q := by omega
    have hn : q + p ∈ block X y := mem_filter.mpr
      ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, heven⟩, by omega, by omega⟩
    change (q + p, p) ∈ T
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hn, hp⟩, by omega, by simpa only [hnp] using hqPrime⟩
  · rintro ⟨p, q⟩ _ ⟨p', q'⟩ _ he
    change (q + p, p) = (q' + p', p') at he
    obtain ⟨hSum, hp⟩ := Prod.mk.inj he
    exact Prod.ext hp (by omega)

/-- Upper bounding each prime weight transfers the short-interval lower bound to a count. -/
private theorem large_prime_count {X y h : ℕ} (hX : 2 ≤ X) (hmax : y + h ≤ 2 * X)
    (hmass : (h : ℝ)/2 ≤ ∑ q ∈ Ioc y (y+h), if Nat.Prime q then Real.log (q : ℝ) else 0) :
    (h : ℝ)/4 ≤ ((largePrimes y h).card : ℝ) * Real.log (X : ℝ) := by
  have hXR : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith only [hXR]
  have hlog2 : Real.log (2 * (X : ℝ)) ≤ 2 * Real.log (X : ℝ) := by
    rw [Real.log_mul (by norm_num) hXpos.ne']
    linarith only [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hXR]
  rw [← sum_filter] at hmass
  change (h : ℝ)/2 ≤ ∑ q ∈ largePrimes y h, Real.log (q : ℝ) at hmass
  have hb : (∑ q ∈ largePrimes y h, Real.log (q : ℝ)) ≤
      ((largePrimes y h).card : ℝ) * (2 * Real.log (X : ℝ)) := by
    calc
      _ ≤ ∑ _q ∈ largePrimes y h, 2 * Real.log (X : ℝ) := by
        refine sum_le_sum (fun q hq => ?_)
        obtain ⟨hI, hp⟩ := mem_filter.mp hq
        have hqmax := (mem_Ioc.mp hI).2.trans hmax
        exact (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hqmax)).trans hlog2
      _ = _ := by simp
  linarith only [hmass, hb]

private theorem first_mass_of_inputs
    (small : ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      (17/40 : ℝ) * s ≤ (((Icc s (2*s)).filter Nat.Prime).card : ℝ) * Real.log s)
    (short : ∃ N : ℕ, ∀ y h : ℕ, N ≤ y → (y : ℝ)^(35/48:ℝ) ≤ (h : ℝ) → h ≤ y →
      (h : ℝ)/2 ≤ ∑ q ∈ Ioc y (y+h), if Nat.Prime q then Real.log (q : ℝ) else 0)
    (scale : ∃ N : ℕ, ∀ X ≥ N, ∀ y : ℕ,
      let s := X.sqrt
      let W := s * s.sqrt
      let h := W - 2*s - 1
      X ≤ y → y + W ≤ 2*X → 3 ≤ s ∧ (y : ℝ)^(35/48:ℝ) ≤ (h : ℝ) ∧ h ≤ y ∧
        (W : ℝ)/2 ≤ (h : ℝ) ∧ Real.sqrt (X : ℝ)/2 ≤ (s : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ,
      X ≤ y → y + blockLength X ≤ 2*X →
      c * (blockLength X : ℝ) * (Real.sqrt (X : ℝ) / (Real.log (X : ℝ))^2) ≤
        ∑ n ∈ block X y, (((primeBand X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) := by
  obtain ⟨Nₛ, hsmall⟩ := small
  obtain ⟨Nₐ, hshort⟩ := short
  obtain ⟨N₀, hscale⟩ := scale
  refine ⟨17/640, by norm_num, max (Nₛ*Nₛ) (max Nₐ N₀), ?_⟩
  intro X hX y hy hwindow
  let s := X.sqrt
  let W := blockLength X
  let h := W - 2*s - 1
  change y + W ≤ 2*X at hwindow
  have hsX : s ≤ X := Nat.sqrt_le_self X
  have hN₀ : N₀ ≤ X := (le_max_right Nₐ N₀).trans ((le_max_right (Nₛ*Nₛ) _).trans hX)
  obtain ⟨hs3, hshortsize, hhy, hhalf, hsroot⟩ := hscale X hN₀ y hy hwindow
  change (W : ℝ)/2 ≤ (h : ℝ) at hhalf
  change Real.sqrt (X : ℝ)/2 ≤ (s : ℝ) at hsroot
  have hsN : Nₛ ≤ s := Nat.le_sqrt.mpr ((le_max_left _ _).trans hX)
  have hyN : Nₐ ≤ y := (le_max_left Nₐ N₀).trans (((le_max_right (Nₛ*Nₛ) _).trans hX).trans hy)
  have hX2 : 2 ≤ X := by omega
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hshortmass := hshort y h hyN hshortsize hhy
  have hfit : h + 2 * s < W := by
    have hpositive : 0 < h := by
      have hypos : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
      have hpos := (Real.rpow_pos_of_pos hypos (35/48 : ℝ)).trans_le hshortsize
      exact_mod_cast hpos
    dsimp [h] at hpositive ⊢
    omega
  have hlarge := large_prime_count hX2 (show y + h ≤ 2*X by omega) hshortmass
  have hlarge' : (W : ℝ)/8 ≤ ((largePrimes y h).card : ℝ) * Real.log (X : ℝ) := by
    linarith only [hlarge, hhalf]
  have hband : (17/80 : ℝ) * Real.sqrt (X : ℝ) ≤ ((primeBand X).card : ℝ) * Real.log (X : ℝ) := by
    have hb := hsmall s hsN
    change (17/40 : ℝ) * s ≤ ((primeBand X).card : ℝ) * Real.log (s : ℝ) at hb
    have hlogS : Real.log (s : ℝ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < s by omega)) (by exact_mod_cast hsX)
    have ht := hb.trans (mul_le_mul_of_nonneg_left hlogS (by positivity : 0 ≤ ((primeBand X).card : ℝ)))
    linarith only [ht, hsroot]
  have hprod := mul_le_mul hband hlarge' (by positivity : 0 ≤ (W : ℝ)/8)
    (by positivity : 0 ≤ ((primeBand X).card : ℝ) * Real.log (X : ℝ))
  have hprod' : (17/640 : ℝ) * (W : ℝ) * Real.sqrt (X : ℝ) ≤
      ((primeBand X).card : ℝ) * ((largePrimes y h).card : ℝ) * (Real.log (X : ℝ))^2 := by
    nlinarith only [hprod]
  have hfinite := arrivals hs3 hy hwindow hfit
  have hfiniteR : ((primeBand X).card : ℝ) * ((largePrimes y h).card : ℝ) ≤
      ∑ n ∈ block X y, (((primeBand X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card : ℝ) := by
    exact_mod_cast hfinite
  apply le_trans _ hfiniteR
  rw [← mul_div_assoc]
  exact (div_le_iff₀ (pow_pos hlog 2)).2 hprod'

end
end FirstMass

/-- Every sufficiently large admissible block has the stated lower bound on prime arrivals. -/
theorem Conjectures.Goldbach.DynBlockFirstMass :
    let E := fun X : ℕ => (Finset.Icc X (2*X)).filter (fun n => Even n);
    let P := fun X : ℕ => (Finset.Icc (Nat.sqrt X) (2*Nat.sqrt X)).filter Nat.Prime;
    let H := fun (X n : ℕ) => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card;
    let W := fun X : ℕ => Nat.sqrt X * Nat.sqrt (Nat.sqrt X);
    let B := fun (X y : ℕ) => (E X).filter (fun n => y ≤ n ∧ n < y + W X);
    let M := fun X : ℕ => Real.sqrt (X:ℝ) / (Real.log (X:ℝ))^2;
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ y : ℕ, X ≤ y → y + W X ≤ 2*X →
      c*(W X:ℝ)*M X ≤ ∑ n ∈ B X y, (H X n:ℝ) :=
  FirstMass.first_mass_of_inputs MeanCond.card_lower FirstMass.short_prime_weight FirstMass.scales
