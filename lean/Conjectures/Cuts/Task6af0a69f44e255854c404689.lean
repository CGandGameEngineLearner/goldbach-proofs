import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_skirt_polylog_moduli
import Conjectures.Goldbach.WideSignedRemainderBridge

section
open Filter Finset MeasureTheory
open scoped Topology Interval BigOperators Classical

private noncomputable def sqNarrow (n : ℕ) : ℕ := V20.narrow n ^ 2

private noncomputable def ringIdx (n : ℕ) : Finset (ℕ × ℕ) :=
  Vdq.indices (V20.narrow n) (sqNarrow n)

private noncomputable def start₂ (n : ℕ) : ℕ :=
  ⌈(n : ℝ) / (Real.log (n : ℝ)) ^ 13⌉₊

private noncomputable def fullIntegral₂ (n : ℕ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (V19.cap n (sqNarrow n) (V20.width n) \
      V19.cap n (V20.narrow n) (V20.width n)).indicator (V8k.V13w n) t

private noncomputable def modelIntegral₂ (n : ℕ) : ℂ :=
  ∑ i ∈ ringIdx n,
    ∫ t in V19.cell n (V20.narrow n) (V20.width n) i,
      Va2.model n i t ^ 2 * V31.phase (-(n : ℝ) * t)

private noncomputable def modelEnergy₂ (n : ℕ) : ℝ :=
  ∑ i ∈ ringIdx n,
    ∫ t in V19.cell n (V20.narrow n) (V20.width n) i, ‖Va2.model n i t‖ ^ 2

private noncomputable def approxError₂ (n : ℕ) : ℝ :=
  ∑ i ∈ ringIdx n,
    ∫ t in V19.cell n (V20.narrow n) (V20.width n) i,
      ‖V31.Vi3 n t - Va2.model n i t‖ ^ 2

private structure Geom₂ (n : ℕ) : Prop where
  n_ge_two : 2 ≤ n
  log_ge_one : 1 ≤ Real.log (n : ℝ)
  narrow_pos : 1 ≤ V20.narrow n
  narrow_le_sq : V20.narrow n ≤ sqNarrow n
  sq_le_cutoff : sqNarrow n ≤ V20.cutoff n
  cutoff_le_n : V20.cutoff n ≤ n
  width_pos : 0 < V20.width n
  width_small : 24 * V20.width n ≤ n
  budget_sq : 2 * V20.width n * sqNarrow n < n
  narrow_le_width : V20.narrow n ≤ V20.width n
  narrow_log : (V20.narrow n : ℝ) ≤ 16 * (Real.log (n : ℝ)) ^ 2
  sq_log : (sqNarrow n : ℝ) ≤ 256 * (Real.log (n : ℝ)) ^ 4
  start_ge_two : 2 ≤ start₂ n
  start_le_n : start₂ n ≤ n
  start_upper : (start₂ n : ℝ) ≤ 2 * (n : ℝ) / (Real.log (n : ℝ)) ^ 13
  start_log : Real.log (n : ℝ) / 2 ≤ Real.log (start₂ n : ℝ)
  start_lower : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (start₂ n : ℝ)
  q_props : ∀ q ∈ Ioc (V20.narrow n) (sqNarrow n),
    2 ≤ q ∧ q ≤ n ∧
    0 < V19.radius n (V20.width n) q ∧
    V19.radius n (V20.width n) q ≤ 1 / 24 ∧
    1 ≤ ((n + 1 : ℕ) : ℝ) * V19.radius n (V20.width n) q ∧
    0 < V8i.V15 n q ∧
    V8i.V15 n q ≤ start₂ n ∧
    (V8i.V15 n q : ℝ) ≤ (n : ℝ) ^ (3 / 4 : ℝ) ∧
    (q : ℝ) ^ 2 * (n : ℝ) ^ (7 / 12 : ℝ) ≤ (V8i.V15 n q : ℝ)

private theorem narrow_log_bound (n : ℕ) (hn : 2 ≤ n) :
    (Nat.log 2 (n + 2) : ℝ) ≤ 4 * Real.log (n : ℝ) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ (Nat.log 2 (n + 2)) ≤ ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : n + 2 ≠ 0)
  have hraw := Real.log_le_log (by positivity) hpow
  have hin : ((n + 2 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
    push_cast
    nlinarith only [hnR, sq_nonneg ((n : ℝ) - 2)]
  have hlog := Real.log_le_log (by positivity) hin
  rw [Real.log_pow] at hraw hlog
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hm := mul_le_mul_of_nonneg_left hl2 (Nat.cast_nonneg (Nat.log 2 (n + 2)) : 0 ≤ (_ : ℝ))
  push_cast at hlog hraw
  linarith only [hm, hraw, hlog]

private theorem geom_ev : ∀ᶠ n : ℕ in atTop, Geom₂ n := by
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [V20.Vhd, eventually_ge_atTop (2 : ℕ),
    hloglim.eventually (eventually_ge_atTop (1 : ℝ)),
    V20.V90 13 (1 / 4) 1 (by norm_num) (by norm_num),
    V20.V90 6 (1 / 12) (1 / 25165824) (by norm_num) (by norm_num),
    V20.V90 4 (1 / 3) (1 / 512) (by norm_num) (by norm_num),
    V20.V90 2 (1 / 12) 1 (by norm_num) (by norm_num),
    V20.V90 0 (1 / 12) (1 / 2) (by norm_num) (by norm_num)] with
      n hhd hn hL hlog13 hlog6 hlog4 hlog2 hpow12
  obtain ⟨_, hQ1, hQU, hUn, hHn, hbudget⟩ := hhd
  let x : ℝ := n
  let L := Real.log x
  have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < n by omega)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  change 1 ≤ L at hL
  have hL0 : 0 < L := by linarith
  have hL13 : 0 < L ^ 13 := pow_pos hL0 _
  have h13 : L ^ 13 ≤ x ^ (1 / 4 : ℝ) := by simpa only [one_mul] using hlog13
  have h6 : 25165824 * L ^ 6 ≤ x ^ (1 / 12 : ℝ) := by
    change L ^ 6 ≤ (1 / 25165824 : ℝ) * x ^ (1 / 12 : ℝ) at hlog6
    linarith
  have h4 : 512 * L ^ 4 ≤ x ^ (1 / 3 : ℝ) := by
    change L ^ 4 ≤ (1 / 512 : ℝ) * x ^ (1 / 3 : ℝ) at hlog4
    linarith
  have h2 : L ^ 2 ≤ x ^ (1 / 12 : ℝ) := by simpa only [one_mul] using hlog2
  have hp12 : 2 ≤ x ^ (1 / 12 : ℝ) := by
    change L ^ 0 ≤ (1 / 2 : ℝ) * x ^ (1 / 12 : ℝ) at hpow12
    norm_num only [pow_zero] at hpow12
    linarith
  have hp34 : 1 ≤ x ^ (3 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hp34two : 2 ≤ x ^ (3 / 4 : ℝ) := hp12.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hp13two : 2 ≤ x ^ (1 / 3 : ℝ) := hp12.trans (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have hQsq : V20.narrow n ≤ sqNarrow n := by
    unfold sqNarrow
    exact Nat.le_self_pow (by decide) _
  have hNlog : (V20.narrow n : ℝ) ≤ 16 * L ^ 2 := by
    calc (V20.narrow n : ℝ)
        = (Nat.log 2 (n + 2) : ℝ) ^ 2 := by simp [V20.narrow]
      _ ≤ (4 * L) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (narrow_log_bound n hn) _
      _ = 16 * L ^ 2 := by ring
  have hSqlog : (sqNarrow n : ℝ) ≤ 256 * L ^ 4 := by
    calc (sqNarrow n : ℝ)
        = (V20.narrow n : ℝ) ^ 2 := by simp [sqNarrow]
      _ ≤ (16 * L ^ 2) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNlog _
      _ = 256 * L ^ 4 := by ring
  have hSqCut : sqNarrow n ≤ V20.cutoff n := by
    apply Nat.le_floor
    exact hSqlog.trans (by nlinarith only [h4, pow_nonneg hL0.le 4])
  have hUH : V20.cutoff n ≤ V20.width n := V20.Vrx n hQ1
  have hWidthPos : 0 < V20.width n := hQ1.trans (hQU.trans hUH)
  have hQH : V20.narrow n ≤ V20.width n := hQU.trans hUH
  have hBudgetSq : 2 * V20.width n * sqNarrow n < n :=
    (Nat.mul_le_mul_left (2 * V20.width n) hSqCut).trans_lt hbudget
  have hRlo : x ^ (1 / 3 : ℝ) / 2 ≤ (V20.cutoff n : ℝ) := by
    have hf := Nat.lt_floor_add_one (x ^ (1 / 3 : ℝ))
    change x ^ (1 / 3 : ℝ) < (V20.cutoff n : ℝ) + 1 at hf
    linarith only [hf, hp13two]
  have hRup : (V20.cutoff n : ℝ) ≤ x ^ (1 / 3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg hx.le _)
  have hYraw : x ^ (3 / 4 : ℝ) ≤ x / L ^ 13 := by
    apply (le_div_iff₀ hL13).2
    calc x ^ (3 / 4 : ℝ) * L ^ 13
        ≤ x ^ (3 / 4 : ℝ) * x ^ (1 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left h13 (Real.rpow_nonneg hx.le _)
      _ = x := by rw [← Real.rpow_add hx]; norm_num
  have hYceil : x / L ^ 13 ≤ (start₂ n : ℝ) := Nat.le_ceil _
  have hYlower : x ^ (3 / 4 : ℝ) ≤ (start₂ n : ℝ) := hYraw.trans hYceil
  have hY2 : 2 ≤ start₂ n := by exact_mod_cast hp34two.trans hYlower
  have hYn : start₂ n ≤ n := by
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hL13).2
    exact le_mul_of_one_le_right hx.le (one_le_pow₀ hL)
  have hYupper : (start₂ n : ℝ) ≤ 2 * x / L ^ 13 := by
    have h1 : 1 ≤ x / L ^ 13 := hp34.trans hYraw
    have hc := Nat.ceil_lt_add_one (show 0 ≤ x / L ^ 13 by positivity)
    change (start₂ n : ℝ) < x / L ^ 13 + 1 at hc
    calc (start₂ n : ℝ) ≤ 2 * (x / L ^ 13) := by linarith
      _ = 2 * x / L ^ 13 := by ring
  have hYlog : L / 2 ≤ Real.log (start₂ n : ℝ) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hx (3 / 4 : ℝ)) hYlower
    rw [Real.log_rpow hx] at hh
    change (3 / 4 : ℝ) * L ≤ Real.log (start₂ n : ℝ) at hh
    linarith
  have hwidthR : (V20.width n : ℝ) = 256 * (V20.cutoff n : ℝ) * (V20.narrow n : ℝ) := by
    simp [V20.width]
  refine ⟨hn, hL, hQ1, hQsq, hSqCut, hUn, hWidthPos, hHn, hBudgetSq, hQH, hNlog, hSqlog,
    hY2, hYn, hYupper, hYlog, hYlower, ?_⟩
  intro q hq
  obtain ⟨hqQ, hqSq⟩ := mem_Ioc.mp hq
  have hq2 : 2 ≤ q := by omega
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hqpos : 0 < (q : ℝ) := by linarith
  have hqCut : q ≤ V20.cutoff n := hqSq.trans hSqCut
  have hqn : q ≤ n := hqCut.trans hUn
  have hqH : q ≤ V20.width n := hqCut.trans hUH
  have hrpos : 0 < V19.radius n (V20.width n) q := by unfold V19.radius; positivity
  have hHnR : 24 * (V20.width n : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hHn
  have hrSmall : V19.radius n (V20.width n) q ≤ 1 / 24 := by
    unfold V19.radius
    apply (div_le_iff₀ (mul_pos hqpos hx)).2
    have hqx := mul_le_mul_of_nonneg_right hq1R hx.le
    nlinarith only [hqx, hHnR]
  have hrLarge : 1 ≤ ((n + 1 : ℕ) : ℝ) * V19.radius n (V20.width n) q := by
    have hqHR : (q : ℝ) ≤ (V20.width n : ℝ) := by exact_mod_cast hqH
    have hprod := mul_le_mul_of_nonneg_right hqHR hx.le
    have hnon : 0 ≤ (V20.width n : ℝ) := by positivity
    unfold V19.radius
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (mul_pos hqpos hx)).2
    push_cast
    nlinarith only [hprod, hnon]
  have hrec : 1 / (12 * V19.radius n (V20.width n) q) =
      (q : ℝ) * x / (12 * (V20.width n : ℝ)) := by
    unfold V19.radius
    change 1 / (12 * ((V20.width n : ℝ) / ((q : ℝ) * x))) = _
    field_simp
  have hhup : (V8i.V15 n q : ℝ) ≤ (q : ℝ) * x / (12 * (V20.width n : ℝ)) := by
    rw [V8i.V15, hrec]
    exact Nat.floor_le (by positivity)
  have hhfloor : (q : ℝ) * x / (12 * (V20.width n : ℝ)) < (V8i.V15 n q : ℝ) + 1 := by
    rw [V8i.V15, hrec]
    exact Nat.lt_floor_add_one _
  have hNposR : 0 < (V20.narrow n : ℝ) := by exact_mod_cast (show 0 < V20.narrow n by omega)
  have hRposR : 0 < (V20.cutoff n : ℝ) := by exact_mod_cast (show 0 < V20.cutoff n by omega)
  have hqSqR : (q : ℝ) ≤ (V20.narrow n : ℝ) ^ 2 := by
    exact_mod_cast hqSq.trans (by rfl : sqNarrow n ≤ V20.narrow n ^ 2)
  have hProd34 : x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ) = x := by
    rw [← Real.rpow_add hx]; norm_num
  have hProd12 : x ^ (1 / 12 : ℝ) * x ^ (2 / 3 : ℝ) = x ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hx]; norm_num
  have hhscale : (V8i.V15 n q : ℝ) ≤ x ^ (3 / 4 : ℝ) := by
    apply hhup.trans
    apply (div_le_iff₀ (show 0 < 12 * (V20.width n : ℝ) by positivity)).2
    have hqN : (q : ℝ) ≤ 16 * L ^ 2 * (V20.narrow n : ℝ) := by
      calc (q : ℝ) ≤ (V20.narrow n : ℝ) * (V20.narrow n : ℝ) := by simpa [pow_two] using hqSqR
        _ ≤ (16 * L ^ 2) * (V20.narrow n : ℝ) :=
          mul_le_mul_of_nonneg_right hNlog hNposR.le
    calc (q : ℝ) * x
        ≤ (16 * L ^ 2 * (V20.narrow n : ℝ)) * (x ^ (1 / 3 : ℝ) * x ^ (2 / 3 : ℝ)) := by
          rw [hProd34]
          exact mul_le_mul_of_nonneg_right hqN hx.le
      _ ≤ (16 * x ^ (1 / 12 : ℝ) * (V20.narrow n : ℝ)) *
            ((2 * (V20.cutoff n : ℝ)) * x ^ (2 / 3 : ℝ)) := by
          have h1 : 16 * L ^ 2 * (V20.narrow n : ℝ) ≤ 16 * x ^ (1 / 12 : ℝ) * (V20.narrow n : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) hNposR.le
          have h2' : x ^ (1 / 3 : ℝ) ≤ 2 * (V20.cutoff n : ℝ) := by linarith only [hRlo]
          exact mul_le_mul h1 (mul_le_mul_of_nonneg_right h2' (Real.rpow_nonneg hx.le _))
            (by positivity) (by positivity)
      _ = 32 * (V20.cutoff n : ℝ) * (V20.narrow n : ℝ) * (x ^ (1 / 12 : ℝ) * x ^ (2 / 3 : ℝ)) := by
          ring
      _ ≤ (12 * (256 * (V20.cutoff n : ℝ) * (V20.narrow n : ℝ))) * x ^ (3 / 4 : ℝ) := by
          rw [hProd12]
          have hnon : 0 ≤ (V20.cutoff n : ℝ) * (V20.narrow n : ℝ) * x ^ (3 / 4 : ℝ) := by positivity
          nlinarith only [hnon]
      _ = (12 * (V20.width n : ℝ)) * x ^ (3 / 4 : ℝ) := by rw [hwidthR]
      _ = x ^ (3 / 4 : ℝ) * (12 * (V20.width n : ℝ)) := by ring
  have hcritical : 24 * (V20.width n : ℝ) * (q : ℝ) * x ^ (7 / 12 : ℝ) ≤ x := by
    have hq4 : (q : ℝ) ≤ 256 * L ^ 4 := (Nat.cast_le (α := ℝ).mpr hqSq).trans hSqlog
    calc 24 * (V20.width n : ℝ) * (q : ℝ) * x ^ (7 / 12 : ℝ)
        = 24 * 256 * (V20.cutoff n : ℝ) * (V20.narrow n : ℝ) * (q : ℝ) * x ^ (7 / 12 : ℝ) := by
          rw [hwidthR]; ring
      _ ≤ 24 * 256 * x ^ (1 / 3 : ℝ) * (16 * L ^ 2) * (256 * L ^ 4) * x ^ (7 / 12 : ℝ) := by
          gcongr
      _ = (25165824 * L ^ 6) * (x ^ (1 / 3 : ℝ) * x ^ (7 / 12 : ℝ)) := by ring
      _ = (25165824 * L ^ 6) * x ^ (11 / 12 : ℝ) := by
          rw [← Real.rpow_add hx]; norm_num
      _ ≤ x ^ (1 / 12 : ℝ) * x ^ (11 / 12 : ℝ) :=
          mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hx.le _)
      _ = x := by rw [← Real.rpow_add hx]; norm_num
  have htarget : 2 * ((q : ℝ) ^ 2 * x ^ (7 / 12 : ℝ)) ≤
      (q : ℝ) * x / (12 * (V20.width n : ℝ)) := by
    apply (le_div_iff₀ (show 0 < 12 * (V20.width n : ℝ) by positivity)).2
    have hh := mul_le_mul_of_nonneg_left hcritical hqpos.le
    convert hh using 1; ring
  have htarget1 : 1 ≤ (q : ℝ) ^ 2 * x ^ (7 / 12 : ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hq1R) (Real.one_le_rpow hx1 (by norm_num))
  have hhcritical : (q : ℝ) ^ 2 * x ^ (7 / 12 : ℝ) ≤ (V8i.V15 n q : ℝ) := by linarith
  have hhpos : 0 < V8i.V15 n q := by
    have : (0 : ℝ) < (V8i.V15 n q : ℝ) := by linarith
    exact_mod_cast this
  have hhY : V8i.V15 n q ≤ start₂ n := by exact_mod_cast hhscale.trans hYlower
  exact ⟨hq2, hqn, hrpos, hrSmall, hrLarge, hhpos, hhY, hhscale, hhcritical⟩

private theorem region_eq_iUnion {n Q U H : ℕ} (hQU : Q ≤ U) (hbudget : 2 * H * U < n) :
    (⋃ i ∈ Vdq.indices Q U, V19.cell n Q H i) =
      (V19.cap n U H \ V19.cap n Q H) ∩ Set.Ioc 0 1 := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_sdiff]
  constructor
  · rintro ⟨i, hi, hti⟩
    obtain ⟨hiU, hiQ⟩ := Vdq.V1ku.mp hi
    refine ⟨⟨V19.mem_cap.mpr ⟨i, hiU, hti.1.1⟩, ?_⟩, hti.2⟩
    intro hnot
    obtain ⟨j, hj, htj⟩ := V19.mem_cap.mp hnot
    have he := V19.Vtg hbudget hiU (V19.V1w1 hQU hj) hti.1.1 htj
    subst j
    have hjQ := (V19.Vcx.mp hj).2.1
    omega
  · rintro ⟨⟨htU, htnotQ⟩, htIoc⟩
    obtain ⟨i, hi, hit⟩ := V19.mem_cap.mp htU
    have hiQ : Q < i.1 := by
      by_contra! hle
      apply htnotQ
      obtain ⟨h1, _, h3, h4⟩ := V19.Vcx.mp hi
      exact V19.mem_cap.mpr ⟨i, V19.Vcx.mpr ⟨h1, hle, h3, h4⟩, hit⟩
    refine ⟨i, Vdq.V1ku.mpr ⟨hi, hiQ⟩, ⟨⟨hit, ?_⟩, htIoc⟩⟩
    simp [not_le.mpr hiQ]

private theorem integral_eq_sum_ringIdx {n Q U H : ℕ} (hQU : Q ≤ U) (hbudget : 2 * H * U < n)
    (F : ℝ → ℂ) (hF : Continuous F) :
    (∫ t in (0 : ℝ)..1, (V19.cap n U H \ V19.cap n Q H).indicator F t) =
      ∑ i ∈ Vdq.indices Q U, ∫ t in V19.cell n Q H i, F t := by
  have hm : MeasurableSet (V19.cap n U H \ V19.cap n Q H) :=
    (V19.Vpr n U H).diff (V19.Vpr n Q H)
  have hint : IntegrableOn F (Set.Ioc (0 : ℝ) 1) volume :=
    (hF.intervalIntegrable (0 : ℝ) 1).1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), setIntegral_indicator hm,
    Set.inter_comm, ← region_eq_iUnion hQU hbudget]
  exact integral_biUnion_finset (Vdq.indices Q U) (fun i _ => V19.V20h n Q H i)
    ((V19.V1yk hbudget).subset (Finset.coe_subset.mpr Finset.sdiff_subset))
    (fun i _ => hint.mono_set Set.inter_subset_right)

private theorem coprime_filter_succ {q : ℕ} (hq : 2 ≤ q) :
    (range (q + 1)).filter (fun a => a.Coprime q) =
      (range q).filter (fun a => Nat.Coprime a q) := by
  ext a
  simp only [mem_filter, mem_range]
  constructor
  · rintro ⟨haq, hcop⟩
    have hne : a ≠ q := by
      intro heq
      subst a
      have h : q = 1 := by simpa [Nat.Coprime] using hcop
      omega
    exact ⟨lt_of_le_of_ne (Nat.lt_succ_iff.mp haq) hne, hcop⟩
  · rintro ⟨haq, hcop⟩
    exact ⟨haq.trans (Nat.lt_succ_self q), hcop⟩

private theorem modelIntegral₂_re {n : ℕ} (hQ1 : 1 ≤ V20.narrow n)
    (hQH : V20.narrow n ≤ V20.width n) (hHn : V20.width n ≤ n) :
    (modelIntegral₂ n).re =
      ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
        (Vr.V3f q n).re * V24.mass n (V19.radius n (V20.width n) q) := by
  unfold modelIntegral₂ ringIdx
  rw [Vdq.V20s, Complex.re_sum]
  refine sum_congr rfl fun q hq => ?_
  obtain ⟨hqQ, _⟩ := mem_Ioc.mp hq
  have hq2 : 2 ≤ q := by omega
  have hnot : ¬ q ≤ V20.narrow n := by omega
  rw [coprime_filter_succ hq2]
  have hsum :
      (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ∫ t in V19.cell n (V20.narrow n) (V20.width n) (q, a),
          Va2.model n (q, a) t ^ 2 * V31.phase (-(n : ℝ) * t)) =
      Vr.V3f q n * (V24.mass n (V19.radius n (V20.width n) q) : ℂ) := by
    calc (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ t in V19.cell n (V20.narrow n) (V20.width n) (q, a),
            Va2.model n (q, a) t ^ 2 * V31.phase (-(n : ℝ) * t))
        = ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            V4o.Vc5 n q a *
              Complex.ofReal (∫ t in V19.cell n (V20.narrow n) (V20.width n) (q, a),
                ‖V24.kernel n (t - V19.center (q, a))‖ ^ 2) := by
          refine sum_congr rfl fun a _ => ?_
          exact V4o.V1he n (V20.narrow n) (V20.width n) q a
      _ = ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
            V4o.Vc5 n q a * Complex.ofReal (V24.mass n (V19.radius n (V20.width n) q)) := by
          refine sum_congr rfl fun a ha => ?_
          obtain ⟨haq, hcop⟩ := mem_filter.mp ha
          rw [V4g.V1ei hQH hHn hq2 (mem_range.mp haq).le hcop, ite_eq_right hnot, sub_zero]
      _ = (∑ a ∈ (range q).filter (fun a => Nat.Coprime a q), V4o.Vc5 n q a) *
            Complex.ofReal (V24.mass n (V19.radius n (V20.width n) q)) := (Finset.sum_mul _ _ _).symm
      _ = Vr.V3f q n * Complex.ofReal (V24.mass n (V19.radius n (V20.width n) q)) := by
          rw [V4o.V1bq n q]
  rw [hsum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private theorem signed_model_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Even n → -(ε * (n : ℝ)) ≤ (modelIntegral₂ n).re := by
  obtain ⟨K₀, hK₀⟩ := V1s.Vr9 (ε / 4) (by positivity)
  filter_upwards [geom_ev, V72.Vdi K₀,
    V72.Vdi (Nat.ceil (2 * Vm.V2i / (256 * ε)) + 1)] with n hgeo hQK₀ hQbig hEven
  have hQposR : 0 < (V20.narrow n : ℝ) := by exact_mod_cast hgeo.narrow_pos
  have hn2 : 2 ≤ n := hgeo.n_ge_two
  have hWsmall : 24 * V20.width n ≤ n := hgeo.width_small
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hHn : V20.width n ≤ n := by omega
  rw [modelIntegral₂_re hgeo.narrow_pos hgeo.narrow_le_width hHn]
  let full : ℝ := ((n : ℝ) + 1) / (n : ℝ)
  have hfull_nonneg : 0 ≤ full := by dsimp [full]; positivity
  have hfull_le : full ≤ 2 := by
    dsimp [full]
    apply (div_le_iff₀ hnpos).2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have hS : -(ε / 4) ≤ ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q n).re := by
    have heq :
        (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q n).re) =
          ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), Vm.F n q / (q : ℝ) := by
      refine sum_congr rfl fun q hq => ?_
      have hqQ := (mem_Ioc.mp hq).1
      have hQpos := hgeo.narrow_pos
      exact V1s.Vlv n q (by omega)
    rw [heq]
    exact hK₀ (V20.narrow n) hQK₀ n (sqNarrow n) hEven hgeo.narrow_le_sq
  have hmain_term : -(ε / 2) ≤
      full * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q n).re) := by
    by_cases hnon : 0 ≤ ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q n).re
    · have : 0 ≤ full * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q n).re) :=
        mul_nonneg hfull_nonneg hnon
      linarith
    · push Not at hnon
      have h1 : 2 * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q n).re) ≤
          full * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q n).re) := by
        nlinarith only [hfull_le, hnon]
      linarith only [h1, hS]
  have herr_term :
      |∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
        (Vr.V3f q n).re * (full - V72.normalized n (V20.width n) q)| ≤ ε / 2 := by
    have hterm (q : ℕ) (hq : q ∈ Ioc (V20.narrow n) (sqNarrow n)) :
        |(Vr.V3f q n).re * (full - V72.normalized n (V20.width n) q)| ≤
          |Vm.F n q| / (2 * (V20.width n : ℝ)) := by
      have hq1 : 1 ≤ q := by
        have := (mem_Ioc.mp hq).1
        have := hgeo.narrow_pos
        omega
      have hqpos : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
      have hdy := V72.Vdy n (V20.width n) q (by omega) hgeo.width_pos hgeo.width_small
      rw [max_eq_right hq1] at hdy
      change 0 ≤ full - V72.normalized n (V20.width n) q ∧
        full - V72.normalized n (V20.width n) q ≤ (q : ℝ) / (2 * (V20.width n : ℝ)) at hdy
      rw [abs_mul, V1s.Vlv n q (by omega), abs_div, abs_of_pos hqpos, abs_of_nonneg hdy.1]
      calc (|Vm.F n q| / (q : ℝ)) * (full - V72.normalized n (V20.width n) q)
          ≤ (|Vm.F n q| / (q : ℝ)) * ((q : ℝ) / (2 * (V20.width n : ℝ))) :=
            mul_le_mul_of_nonneg_left hdy.2 (by positivity)
        _ = |Vm.F n q| / (2 * (V20.width n : ℝ)) := by field_simp
    have hsub : Ioc (V20.narrow n) (sqNarrow n) ⊆ Icc 1 (sqNarrow n) := by
      intro q hq
      obtain ⟨h1, h2⟩ := mem_Ioc.mp hq
      have := hgeo.narrow_pos
      exact mem_Icc.mpr ⟨by omega, h2⟩
    have hsumF : (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), |Vm.F n q|) ≤
        Vm.V2i * (sqNarrow n : ℝ) := by
      calc (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), |Vm.F n q|)
          ≤ ∑ q ∈ Icc 1 (sqNarrow n), |Vm.F n q| :=
            sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
        _ ≤ Vm.V2i * (sqNarrow n : ℝ) := V1s.Vq3 n (sqNarrow n)
    have hwidthEq : (V20.width n : ℝ) = 256 * (V20.cutoff n : ℝ) * (V20.narrow n : ℝ) := by
      simp [V20.width]
    have hcutPos : 0 < (V20.cutoff n : ℝ) := by
      exact_mod_cast (hgeo.narrow_pos.trans (hgeo.narrow_le_sq.trans hgeo.sq_le_cutoff))
    have hsqCutR : (sqNarrow n : ℝ) ≤ (V20.cutoff n : ℝ) := by exact_mod_cast hgeo.sq_le_cutoff
    have hQlarge : 2 * Vm.V2i / (256 * ε) ≤ (V20.narrow n : ℝ) := by
      have h1 : (Nat.ceil (2 * Vm.V2i / (256 * ε)) : ℝ) ≤ (V20.narrow n : ℝ) := by
        exact_mod_cast (Nat.le_of_succ_le hQbig)
      exact (Nat.le_ceil _).trans h1
    calc |∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
            (Vr.V3f q n).re * (full - V72.normalized n (V20.width n) q)|
        ≤ ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
            |(Vr.V3f q n).re * (full - V72.normalized n (V20.width n) q)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), |Vm.F n q| / (2 * (V20.width n : ℝ)) :=
          sum_le_sum hterm
      _ = (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), |Vm.F n q|) / (2 * (V20.width n : ℝ)) := by
          rw [← Finset.sum_div]
      _ ≤ (Vm.V2i * (sqNarrow n : ℝ)) / (2 * (V20.width n : ℝ)) :=
          div_le_div_of_nonneg_right hsumF (by positivity)
      _ ≤ (Vm.V2i * (V20.cutoff n : ℝ)) / (2 * (256 * (V20.cutoff n : ℝ) * (V20.narrow n : ℝ))) := by
          rw [← hwidthEq]
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsqCutR (Real.exp_pos _).le) (by positivity)
      _ = Vm.V2i / (512 * (V20.narrow n : ℝ)) := by field_simp; ring
      _ ≤ ε / 2 := by
          apply (div_le_iff₀ (by positivity : 0 < 512 * (V20.narrow n : ℝ))).2
          have hmul := mul_le_mul_of_nonneg_right hQlarge (show (0 : ℝ) ≤ 256 * ε by positivity)
          have hVm : Vm.V2i ≤ (2 * Vm.V2i / (256 * ε)) * (256 * ε) := by
            have heq1 : (2 * Vm.V2i / (256 * ε)) * (256 * ε) = 2 * Vm.V2i := by field_simp
            have hV : 0 ≤ Vm.V2i := (Real.exp_pos _).le
            rw [heq1]
            linarith only [hV]
          calc Vm.V2i ≤ (V20.narrow n : ℝ) * (256 * ε) := hVm.trans hmul
            _ = ε / 2 * (512 * (V20.narrow n : ℝ)) := by ring
  have hnorm_sum : -(ε * (n : ℝ)) ≤
      (n : ℝ) * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
        (Vr.V3f q n).re * V72.normalized n (V20.width n) q) := by
    have hsplit :
        (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
          (Vr.V3f q n).re * V72.normalized n (V20.width n) q) =
        full * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q n).re) -
        ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
          (Vr.V3f q n).re * (full - V72.normalized n (V20.width n) q) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine sum_congr rfl fun q _ => by ring
    have herr_lo := (abs_le.mp herr_term).1
    have hcomb : -ε ≤ ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
        (Vr.V3f q n).re * V72.normalized n (V20.width n) q := by
      linarith only [hsplit, hmain_term, (abs_le.mp herr_term).2]
    nlinarith [mul_le_mul_of_nonneg_left hcomb hnpos.le]
  refine hnorm_sum.trans_eq ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun q hq => ?_
  have hqQ := (mem_Ioc.mp hq).1
  have hQpos := hgeo.narrow_pos
  have hq1 : 1 ≤ q := by omega
  unfold V72.normalized
  rw [max_eq_right hq1]
  field_simp

private theorem abel_identity (S : ℕ → ℝ) (h0 : S 0 = 0) :
    ∀ m : ℕ, 1 ≤ m →
      (∑ q ∈ Icc 1 m, (S q - S (q - 1)) / (q : ℝ)) =
        S m / (m : ℝ) + ∑ q ∈ Icc 1 (m - 1), S q * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => simp [h0]
  | succ m hm ih =>
    have hm1 : 1 ≤ m + 1 := by omega
    rw [Finset.sum_Icc_succ_top hm1, ih]
    have hsuc : m + 1 - 1 = m := by omega
    rw [hsuc]
    have hsplit :
        (∑ q ∈ Icc 1 m, S q * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ))) =
          (∑ q ∈ Icc 1 (m - 1), S q * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ))) +
            S m * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) := by
      have hm_eq : m = (m - 1) + 1 := by omega
      conv_lhs => rw [hm_eq, Finset.sum_Icc_succ_top (by omega)]
      rw [← hm_eq]
    rw [hsplit]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have hm1R : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    ring

private theorem abel_sum_div_le (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ q, 0 ≤ a q) (hsum : ∀ X, (∑ q ∈ Icc 1 X, a q) ≤ C * (X : ℝ)) (U : ℕ) :
    (∑ q ∈ Icc 1 U, a q / (q : ℝ)) ≤ C * (2 + Real.log ((max 1 U : ℕ) : ℝ)) := by
  by_cases hU : U = 0
  · subst hU
    rw [Icc_eq_empty (by omega)]
    simp only [sum_empty]
    positivity
  · have hU1 : 1 ≤ U := Nat.pos_of_ne_zero hU
    rw [max_eq_right hU1]
    let S : ℕ → ℝ := fun m => ∑ q ∈ Icc 1 m, a q
    have hS0 : S 0 = 0 := by simp [S]
    have hSnonneg : ∀ m, 0 ≤ S m := fun m => sum_nonneg fun q _ => ha q
    have hSdiff : ∀ q ∈ Icc 1 U, a q = S q - S (q - 1) := by
      intro q hq
      have hq1 := (mem_Icc.mp hq).1
      have := Finset.sum_Icc_succ_top (f := a) (a := 1) (b := q - 1) (by omega)
      rw [show q - 1 + 1 = q by omega] at this
      dsimp [S]
      linarith
    have hid : (∑ q ∈ Icc 1 U, a q / (q : ℝ)) =
        S U / (U : ℝ) + ∑ q ∈ Icc 1 (U - 1), S q * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) := by
      rw [← abel_identity S hS0 U hU1]
      refine sum_congr rfl fun q hq => ?_
      rw [hSdiff q hq]
    have hhead : S U / (U : ℝ) ≤ C := by
      have hUR : 0 < (U : ℝ) := by exact_mod_cast hU1
      apply (div_le_iff₀ hUR).2
      simpa only [S] using hsum U
    have htail : (∑ q ∈ Icc 1 (U - 1), S q * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ))) ≤
        C * (1 + Real.log (U : ℝ)) := by
      have hterm : ∀ q ∈ Icc 1 (U - 1),
          S q * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) ≤ C * (1 / ((q + 1 : ℕ) : ℝ)) := by
        intro q hq
        have hq1 : 1 ≤ q := (mem_Icc.mp hq).1
        have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
        have hq1R : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
        have hdif : 0 ≤ 1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ) := by
          rw [sub_nonneg]
          apply one_div_le_one_div_of_le hqR
          exact_mod_cast (Nat.le_succ q)
        have hsq : S q ≤ C * (q : ℝ) := hsum q
        calc S q * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ))
            ≤ (C * (q : ℝ)) * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_right hsq hdif
          _ = C * (1 / ((q + 1 : ℕ) : ℝ)) := by
              push_cast
              field_simp [hqR.ne', hq1R.ne']
              ring
      have hreidx : (∑ q ∈ Icc 1 (U - 1), 1 / ((q + 1 : ℕ) : ℝ)) ≤
          ∑ k ∈ Icc 1 U, 1 / (k : ℝ) := by
        have hsub : (Icc 1 (U - 1)).image Nat.succ ⊆ Icc 1 U := by
          intro k hk
          rcases mem_image.mp hk with ⟨q, hq, rfl⟩
          rw [mem_Icc] at hq ⊢
          omega
        calc (∑ q ∈ Icc 1 (U - 1), 1 / ((q + 1 : ℕ) : ℝ))
            = ∑ k ∈ (Icc 1 (U - 1)).image Nat.succ, 1 / (k : ℝ) := by
              rw [Finset.sum_image]
              intro a _ b _ h
              exact Nat.succ.inj h
          _ ≤ ∑ k ∈ Icc 1 U, 1 / (k : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      calc (∑ q ∈ Icc 1 (U - 1), S q * (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)))
          ≤ ∑ q ∈ Icc 1 (U - 1), C * (1 / ((q + 1 : ℕ) : ℝ)) := sum_le_sum hterm
        _ = C * ∑ q ∈ Icc 1 (U - 1), 1 / ((q + 1 : ℕ) : ℝ) := (Finset.mul_sum _ _ _).symm
        _ ≤ C * ∑ k ∈ Icc 1 U, 1 / (k : ℝ) := mul_le_mul_of_nonneg_left hreidx hC
        _ ≤ C * (1 + Real.log (U : ℝ)) := mul_le_mul_of_nonneg_left (V20.V233 U) hC
    linarith only [hid, hhead, htail]

private theorem modelEnergy₂_bound :
    ∃ C_M : ℝ, 0 < C_M ∧
      ∀ᶠ n : ℕ in atTop,
        modelEnergy₂ n ≤ C_M * (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) := by
  refine ⟨2 * Vm.V2i * (10 + Real.log 256), by
    have hV : 0 < Vm.V2i := Real.exp_pos _
    have h256 : 0 < Real.log 256 := Real.log_pos (by norm_num)
    positivity, ?_⟩
  filter_upwards [geom_ev] with n hgeo
  have hn2 := hgeo.n_ge_two
  have hQpos := hgeo.narrow_pos
  have hWsmall := hgeo.width_small
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hHn : V20.width n ≤ n := by omega
  have hL : 1 ≤ Real.log (n : ℝ) := hgeo.log_ge_one
  have hL0 : 0 < Real.log (n : ℝ) := by linarith
  have hstep1 : modelEnergy₂ n ≤
      ((n : ℝ) + 1) * ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q 0).re := by
    have heq : modelEnergy₂ n =
        ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
          (Vr.V3f q 0).re * V24.mass n (V19.radius n (V20.width n) q) := by
      unfold modelEnergy₂ ringIdx
      rw [Vdq.V20s]
      refine sum_congr rfl fun q hq => ?_
      have hqQ := (mem_Ioc.mp hq).1
      have hq2 : 2 ≤ q := by omega
      have hnot : ¬ q ≤ V20.narrow n := by omega
      rw [coprime_filter_succ hq2, ← Vmk.V21g q, Finset.sum_mul]
      refine sum_congr rfl fun a ha => ?_
      obtain ⟨haq, hcop⟩ := mem_filter.mp ha
      rw [Vmk.V1p2, V4g.V1ei hgeo.narrow_le_width hHn hq2 (mem_range.mp haq).le hcop,
        ite_eq_right hnot, sub_zero]
    rw [heq, Finset.mul_sum]
    refine sum_le_sum fun q hq => ?_
    have hqQ := (mem_Ioc.mp hq).1
    have hq1 : 1 ≤ q := by omega
    have hdy := (V72.Vdy n (V20.width n) q (by omega) hgeo.width_pos hgeo.width_small).1
    unfold V72.normalized at hdy
    rw [max_eq_right hq1] at hdy
    have hmass : V24.mass n (V19.radius n (V20.width n) q) ≤ (n : ℝ) + 1 := by
      apply (div_le_div_iff_of_pos_right hnpos).mp
      linarith only [hdy]
    rw [mul_comm ((n : ℝ) + 1)]
    exact mul_le_mul_of_nonneg_left hmass (Vmk.V11l q)
  have hsub : Ioc (V20.narrow n) (sqNarrow n) ⊆ Icc 1 (sqNarrow n) := by
    intro q hq
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hq
    exact mem_Icc.mpr ⟨by omega, h2⟩
  have hsum_F :
      (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q 0).re) ≤
        Vm.V2i * (2 + Real.log ((max 1 (sqNarrow n) : ℕ) : ℝ)) := by
    calc (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (Vr.V3f q 0).re)
        = ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), Vm.F 0 q / (q : ℝ) := by
          refine sum_congr rfl fun q hq => ?_
          have hq1 := (mem_Ioc.mp hq).1
          exact V1s.Vlv 0 q (by omega)
      _ ≤ ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), |Vm.F 0 q| / (q : ℝ) := by
          refine sum_le_sum fun q _ => ?_
          exact div_le_div_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)
      _ ≤ ∑ q ∈ Icc 1 (sqNarrow n), |Vm.F 0 q| / (q : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ Vm.V2i * (2 + Real.log ((max 1 (sqNarrow n) : ℕ) : ℝ)) :=
          abel_sum_div_le (fun q => |Vm.F 0 q|) Vm.V2i (Real.exp_pos _).le
            (fun _ => abs_nonneg _) (fun X => V1s.Vq3 0 X) (sqNarrow n)
  have hsq1 : 1 ≤ sqNarrow n := hgeo.narrow_pos.trans hgeo.narrow_le_sq
  have hsq_posR : 0 < (sqNarrow n : ℝ) := by exact_mod_cast (show 0 < sqNarrow n by omega)
  have hsqrt_pos : 0 < Real.sqrt (Real.log (n : ℝ)) := Real.sqrt_pos.mpr hL0
  have hsqrt1 : 1 ≤ Real.sqrt (Real.log (n : ℝ)) := Real.one_le_sqrt.mpr hL
  have hlogL : Real.log (Real.log (n : ℝ)) ≤ 2 * Real.sqrt (Real.log (n : ℝ)) := by
    have hsq : Real.sqrt (Real.log (n : ℝ)) ^ 2 = Real.log (n : ℝ) := Real.sq_sqrt hL0.le
    calc Real.log (Real.log (n : ℝ))
        = Real.log (Real.sqrt (Real.log (n : ℝ)) ^ 2) := by rw [hsq]
      _ = 2 * Real.log (Real.sqrt (Real.log (n : ℝ))) := by rw [Real.log_pow]; ring
      _ ≤ 2 * (Real.sqrt (Real.log (n : ℝ)) - 1) :=
          mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hsqrt_pos) (by norm_num)
      _ ≤ 2 * Real.sqrt (Real.log (n : ℝ)) := by linarith
  have hlogSq : 2 + Real.log ((max 1 (sqNarrow n) : ℕ) : ℝ) ≤
      (10 + Real.log 256) * Real.sqrt (Real.log (n : ℝ)) := by
    rw [max_eq_right hsq1]
    have hl : Real.log (sqNarrow n : ℝ) ≤ Real.log (256 * (Real.log (n : ℝ)) ^ 4) :=
      Real.log_le_log hsq_posR hgeo.sq_log
    rw [Real.log_mul (by norm_num) (pow_ne_zero 4 hL0.ne'), Real.log_pow] at hl
    push_cast at hl
    have h10 : 2 + Real.log 256 ≤ (2 + Real.log 256) * Real.sqrt (Real.log (n : ℝ)) :=
      le_mul_of_one_le_right (by have := Real.log_pos (by norm_num : (1 : ℝ) < 256); linarith) hsqrt1
    linarith only [hl, hlogL, h10]
  have hn1 : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    linarith
  have hVpos : 0 ≤ Vm.V2i := (Real.exp_pos _).le
  calc modelEnergy₂ n
      ≤ ((n : ℝ) + 1) * (Vm.V2i * (2 + Real.log ((max 1 (sqNarrow n) : ℕ) : ℝ))) :=
        hstep1.trans (mul_le_mul_of_nonneg_left hsum_F (by positivity))
    _ ≤ (2 * (n : ℝ)) * (Vm.V2i * ((10 + Real.log 256) * Real.sqrt (Real.log (n : ℝ)))) :=
        mul_le_mul hn1 (mul_le_mul_of_nonneg_left hlogSq hVpos) (by positivity) (by positivity)
    _ = 2 * Vm.V2i * (10 + Real.log 256) * (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) := by ring

private theorem sum_q_ring_le {n : ℕ} (hgeo : Geom₂ n) :
    (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (q : ℝ)) ≤ 65536 * (Real.log (n : ℝ)) ^ 8 := by
  have hQpos := hgeo.narrow_pos
  have hsub : Ioc (V20.narrow n) (sqNarrow n) ⊆ Icc 1 (sqNarrow n) := by
    intro q hq
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hq
    exact mem_Icc.mpr ⟨by omega, h2⟩
  calc (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (q : ℝ))
      ≤ ∑ q ∈ Icc 1 (sqNarrow n), (q : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ (sqNarrow n : ℝ) ^ 2 := V9i.V1os (sqNarrow n)
    _ ≤ (256 * (Real.log (n : ℝ)) ^ 4) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hgeo.sq_log _
    _ = 65536 * (Real.log (n : ℝ)) ^ 8 := by ring

private theorem approx_rem_bound :
    ∀ᶠ n : ℕ in atTop,
      (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
        (8 * (q : ℝ) * ((n + 1 + V8i.V15 n q : ℕ) : ℝ) / (V8i.V15 n q : ℝ) ^ 2) *
          (Real.log (q : ℝ)) ^ 2) ≤ (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
  filter_upwards [geom_ev,
    V20.V90 3 (1 / 6) 1 (by norm_num) (by norm_num),
    V20.V90 9 (1 / 6) (1 / (221184 * 4096 ^ 2)) (by norm_num) (by positivity)] with
      n hgeo hlog3 hremRaw
  let L := Real.log (n : ℝ)
  have hn2 := hgeo.n_ge_two
  have hQpos := hgeo.narrow_pos
  have hL : 1 ≤ L := hgeo.log_ge_one
  have hLpos : 0 < L := by linarith
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hsub_n : Ioc (V20.narrow n) (sqNarrow n) ⊆ Icc 1 n := by
    intro q hq
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hq
    exact mem_Icc.mpr ⟨by omega, h2.trans (hgeo.sq_le_cutoff.trans hgeo.cutoff_le_n)⟩
  have hqrem (q : ℕ) (hq : q ∈ Ioc (V20.narrow n) (sqNarrow n)) :
      (8 * (q : ℝ) * ((n + 1 + V8i.V15 n q : ℕ) : ℝ) / (V8i.V15 n q : ℝ) ^ 2) *
        (Real.log (q : ℝ)) ^ 2 ≤ 18432 * (V20.width n : ℝ) ^ 2 / (q : ℝ) * L ^ 2 := by
    obtain ⟨hq2, hqn, hrpos, hrSmall, hrLarge, _, _, _, _⟩ := hgeo.q_props q hq
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have hqpos : 0 < (q : ℝ) := by linarith
    obtain ⟨_, _, hhN, hinv⟩ := V8i.Vo6 (n + 1) (V19.radius n (V20.width n) q) hrpos hrSmall hrLarge
    change (V8i.V15 n q : ℝ) ≤ ((n + 1 : ℕ) : ℝ) at hhN
    change 1 / (V8i.V15 n q : ℝ) ^ 2 ≤ (24 * V19.radius n (V20.width n) q) ^ 2 at hinv
    have hsum : ((n + 1 + V8i.V15 n q : ℕ) : ℝ) ≤ 4 * (n : ℝ) := by
      push_cast at hhN ⊢
      have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hgeo.n_ge_two
      linarith
    have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqR
    have hlogqn : Real.log (q : ℝ) ≤ L := Real.log_le_log hqpos (by exact_mod_cast hqn)
    have hinvn : 1 / (n : ℝ) ≤ 1 := by
      have h1n : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      exact (div_le_iff₀ hnpos).2 (by linarith)
    calc _ = (8 * (q : ℝ) * ((n + 1 + V8i.V15 n q : ℕ) : ℝ)) *
            (1 / (V8i.V15 n q : ℝ) ^ 2) * (Real.log (q : ℝ)) ^ 2 := by ring
      _ ≤ (8 * (q : ℝ) * (4 * (n : ℝ))) * (24 * V19.radius n (V20.width n) q) ^ 2 * L ^ 2 := by
          gcongr
      _ = (18432 * (V20.width n : ℝ) ^ 2 / (q : ℝ) * L ^ 2) * (1 / (n : ℝ)) := by
          unfold V19.radius; field_simp; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hinvn
  have hhar : (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), 1 / (q : ℝ)) ≤ 3 * L := by
    calc (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), 1 / (q : ℝ))
        ≤ ∑ q ∈ Icc 1 n, 1 / (q : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub_n (fun _ _ _ => by positivity)
      _ ≤ 1 + Real.log (n : ℝ) := V20.V233 n
      _ ≤ 3 * L := by dsimp [L]; linarith
  have hrem56 : 221184 * (V20.width n : ℝ) ^ 2 * L ^ 5 ≤ (n : ℝ) ^ (5 / 6 : ℝ) := by
    have hcutR : (V20.cutoff n : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (Real.rpow_nonneg hnpos.le _)
    have hwidth_le : (V20.width n : ℝ) ≤ 4096 * (n : ℝ) ^ (1 / 3 : ℝ) * L ^ 2 := by
      unfold V20.width
      push_cast
      calc (256 : ℝ) * (V20.cutoff n : ℝ) * (V20.narrow n : ℝ)
          ≤ 256 * (n : ℝ) ^ (1 / 3 : ℝ) * (16 * L ^ 2) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hcutR (by norm_num)) hgeo.narrow_log
              (Nat.cast_nonneg _) (by positivity)
        _ = 4096 * (n : ℝ) ^ (1 / 3 : ℝ) * L ^ 2 := by ring
    have hsq13 : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 2 = (n : ℝ) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]; norm_num
    calc 221184 * (V20.width n : ℝ) ^ 2 * L ^ 5
        ≤ 221184 * (4096 * (n : ℝ) ^ (1 / 3 : ℝ) * L ^ 2) ^ 2 * L ^ 5 := by gcongr
      _ = (n : ℝ) ^ (2 / 3 : ℝ) * (221184 * 4096 ^ 2 * L ^ 9) := by rw [← hsq13]; ring
      _ ≤ (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 6 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hmul := mul_le_mul_of_nonneg_left hremRaw (show (0 : ℝ) ≤ 221184 * 4096 ^ 2 by positivity)
          calc 221184 * 4096 ^ 2 * L ^ 9
              ≤ 221184 * 4096 ^ 2 * (1 / (221184 * 4096 ^ 2) * (n : ℝ) ^ (1 / 6 : ℝ)) := hmul
            _ = (n : ℝ) ^ (1 / 6 : ℝ) := by ring
      _ = (n : ℝ) ^ (5 / 6 : ℝ) := by rw [← Real.rpow_add hnpos]; norm_num
  have hrem_n56 :
      (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
        (8 * (q : ℝ) * ((n + 1 + V8i.V15 n q : ℕ) : ℝ) / (V8i.V15 n q : ℝ) ^ 2) *
          (Real.log (q : ℝ)) ^ 2) ≤ (n : ℝ) ^ (5 / 6 : ℝ) := by
    calc _ ≤ ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
            18432 * (V20.width n : ℝ) ^ 2 / (q : ℝ) * L ^ 2 := sum_le_sum hqrem
      _ = (18432 * (V20.width n : ℝ) ^ 2 * L ^ 2) *
            (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), 1 / (q : ℝ)) := by
          rw [Finset.mul_sum]; refine sum_congr rfl fun q _ => by ring
      _ ≤ (18432 * (V20.width n : ℝ) ^ 2 * L ^ 2) * (3 * L) :=
          mul_le_mul_of_nonneg_left hhar (by positivity)
      _ = 55296 * (V20.width n : ℝ) ^ 2 * L ^ 3 := by ring
      _ ≤ 55296 * (V20.width n : ℝ) ^ 2 * (4 * L ^ 5) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 : (1 : ℝ) ≤ 4 * L ^ 2 := by nlinarith
          have h2 := mul_le_mul_of_nonneg_right h1 (pow_nonneg hLpos.le 3)
          nlinarith
      _ = 221184 * (V20.width n : ℝ) ^ 2 * L ^ 5 := by ring
      _ ≤ (n : ℝ) ^ (5 / 6 : ℝ) := hrem56
  apply hrem_n56.trans
  apply (le_div_iff₀ (pow_pos hLpos 3)).2
  calc (n : ℝ) ^ (5 / 6 : ℝ) * L ^ 3
      ≤ (n : ℝ) ^ (5 / 6 : ℝ) * (1 * (n : ℝ) ^ (1 / 6 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog3 (Real.rpow_nonneg hnpos.le _)
    _ = (n : ℝ) := by rw [one_mul, ← Real.rpow_add hnpos]; norm_num

private theorem approx_bulk_bound :
    ∃ C_B : ℝ, 0 ≤ C_B ∧
      ∀ᶠ n : ℕ in atTop,
        8 * (1 + Real.log (n : ℝ)) *
          (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), V9i.V98 n (start₂ n) q) ≤
            C_B * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
  have hMean : Vbi.Vv8 := Vie.V1ew (V7e.Vzg (V6h.Vz5 30))
  obtain ⟨C, hC, X₀, hmean⟩ := hMean
  refine ⟨8589934592 * C, by positivity, ?_⟩
  have hpowStart : Tendsto start₂ atTop atTop := by
    have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 4 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
    apply tendsto_atTop.2
    intro b
    filter_upwards [geom_ev, hpow.eventually (eventually_ge_atTop (b : ℝ))] with n hgeo hb
    exact_mod_cast hb.trans hgeo.start_lower
  filter_upwards [geom_ev, hpowStart.eventually_ge_atTop X₀] with n hgeo hX₀
  let L := Real.log (n : ℝ)
  have hQpos := hgeo.narrow_pos
  have hL : 1 ≤ L := hgeo.log_ge_one
  have hLpos : 0 < L := by linarith
  have hqbulk (q : ℕ) (hq : q ∈ Ioc (V20.narrow n) (sqNarrow n)) :
      V9i.V98 n (start₂ n) q ≤ 8192 * C * (q : ℝ) * (n : ℝ) / L ^ 12 := by
    obtain ⟨hq2, _, _, _, _, hh, hhY, _, hscale⟩ := hgeo.q_props q hq
    let : NeZero q := ⟨by omega⟩
    apply V1ub.V1zb q n (start₂ n) C hh
    exact Vbi.V1tv q n (V8i.V15 n q) (start₂ n) X₀ C hC.le
      hgeo.start_ge_two hgeo.start_le_n hX₀ hh hhY hLpos hgeo.start_log hscale
      (fun X hXX₀ hX2 hhX hXs => hmean q X (V8i.V15 n q) hXX₀ hX2 hh hhX hXs)
  have h1L : 8 * (1 + L) ≤ 16 * L := by linarith
  have hV98_nonneg : ∀ q ∈ Ioc (V20.narrow n) (sqNarrow n), 0 ≤ V9i.V98 n (start₂ n) q := by
    intro q _
    unfold V9i.V98
    split_ifs with hq0
    · exact le_rfl
    · let : NeZero q := ⟨hq0⟩
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => V3z.Vtd _ _)
  have hsum_q_L : (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (q : ℝ)) ≤ 65536 * L ^ 8 :=
    sum_q_ring_le hgeo
  calc 8 * (1 + L) * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), V9i.V98 n (start₂ n) q)
      ≤ (16 * L) * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), 8192 * C * (q : ℝ) * (n : ℝ) / L ^ 12) :=
        mul_le_mul h1L (sum_le_sum hqbulk) (sum_nonneg hV98_nonneg) (by positivity)
    _ = (16 * L) * (8192 * C * (n : ℝ) / L ^ 12) *
          (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (q : ℝ)) := by
        have hs : (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), 8192 * C * (q : ℝ) * (n : ℝ) / L ^ 12) =
            (8192 * C * (n : ℝ) / L ^ 12) *
              (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (q : ℝ)) := by
          rw [Finset.mul_sum]; refine sum_congr rfl fun q _ => by ring
        rw [hs]; ring
    _ ≤ (16 * L) * (8192 * C * (n : ℝ) / L ^ 12) * (65536 * L ^ 8) :=
        mul_le_mul_of_nonneg_left hsum_q_L (by positivity)
    _ = 8589934592 * C * (n : ℝ) / L ^ 3 := by field_simp; ring

private theorem approx_boundary_bound :
    ∀ᶠ n : ℕ in atTop,
      8 * (1 + Real.log (n : ℝ)) *
        (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), V9i.Vb1 n (start₂ n) q) ≤
          8388608 * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
  filter_upwards [geom_ev, V20.V90 13 (1 / 4) 1 (by norm_num) (by norm_num)] with n hgeo hlog13
  let L := Real.log (n : ℝ)
  have hn2 := hgeo.n_ge_two
  have hQpos := hgeo.narrow_pos
  have hL : 1 ≤ L := hgeo.log_ge_one
  have hLpos : 0 < L := by linarith
  have hL13 : 0 < L ^ 13 := pow_pos hLpos _
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn34_div : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (n : ℝ) / L ^ 13 := by
    apply (le_div_iff₀ hL13).2
    calc (n : ℝ) ^ (3 / 4 : ℝ) * L ^ 13
        ≤ (n : ℝ) ^ (3 / 4 : ℝ) * (1 * (n : ℝ) ^ (1 / 4 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlog13 (Real.rpow_nonneg hnpos.le _)
      _ = (n : ℝ) := by rw [one_mul, ← Real.rpow_add hnpos]; norm_num
  have hqbnd (q : ℕ) (hq : q ∈ Ioc (V20.narrow n) (sqNarrow n)) :
      V9i.Vb1 n (start₂ n) q ≤ (q : ℝ) * (4 * ((n : ℝ) / L ^ 13)) * (1 + L) := by
    obtain ⟨hq2, _, _, _, _, hh, _, hh34, _⟩ := hgeo.q_props q hq
    let : NeZero q := ⟨by omega⟩
    have hhh := V9i.V1hh n (start₂ n) q (by omega) hh
    have hsumR : ((start₂ n + 2 * V8i.V15 n q : ℕ) : ℝ) ≤ 4 * ((n : ℝ) / L ^ 13) := by
      push_cast
      have h1 : (start₂ n : ℝ) ≤ 2 * (n : ℝ) / L ^ 13 := hgeo.start_upper
      have h2 : (V8i.V15 n q : ℝ) ≤ (n : ℝ) / L ^ 13 := hh34.trans hn34_div
      calc (start₂ n : ℝ) + 2 * (V8i.V15 n q : ℝ)
          ≤ 2 * (n : ℝ) / L ^ 13 + 2 * ((n : ℝ) / L ^ 13) :=
            (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by norm_num)))
        _ = 4 * ((n : ℝ) / L ^ 13) := by ring
    exact hhh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsumR (Nat.cast_nonneg _)) (by linarith))
  have hsum_q_L : (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (q : ℝ)) ≤ 65536 * L ^ 8 :=
    sum_q_ring_le hgeo
  have h1Lsq : 8 * (1 + L) ^ 2 ≤ 32 * L ^ 2 := by nlinarith
  have hcomb : (8 * (1 + L) ^ 2) * (4 * ((n : ℝ) / L ^ 13)) *
      (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (q : ℝ)) ≤
      (32 * L ^ 2) * (4 * ((n : ℝ) / L ^ 13)) * (65536 * L ^ 8) :=
    mul_le_mul (mul_le_mul_of_nonneg_right h1Lsq (by positivity)) hsum_q_L
      (sum_nonneg fun _ _ => Nat.cast_nonneg _) (by positivity)
  calc 8 * (1 + L) * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), V9i.Vb1 n (start₂ n) q)
      ≤ 8 * (1 + L) * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
          (q : ℝ) * (4 * ((n : ℝ) / L ^ 13)) * (1 + L)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hqbnd) (by positivity)
    _ = (8 * (1 + L) ^ 2) * (4 * ((n : ℝ) / L ^ 13)) *
          (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (q : ℝ)) := by
        have hs : (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
            (q : ℝ) * (4 * ((n : ℝ) / L ^ 13)) * (1 + L)) =
            (4 * ((n : ℝ) / L ^ 13)) * (1 + L) *
              (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), (q : ℝ)) := by
          rw [Finset.mul_sum]; refine sum_congr rfl fun q _ => by ring
        rw [hs]; ring
    _ ≤ (32 * L ^ 2) * (4 * ((n : ℝ) / L ^ 13)) * (65536 * L ^ 8) := hcomb
    _ = 8388608 * (n : ℝ) / L ^ 3 := by field_simp; ring

private theorem approxError₂_bound :
    ∃ C_E : ℝ, 0 < C_E ∧
      ∀ᶠ n : ℕ in atTop, approxError₂ n ≤ C_E * (n : ℝ) / (Real.log (n : ℝ)) ^ 3 := by
  obtain ⟨C_B, hCB, hbulk_ev⟩ := approx_bulk_bound
  refine ⟨1 + C_B + 8388608, by positivity, ?_⟩
  filter_upwards [geom_ev, approx_rem_bound, hbulk_ev, approx_boundary_bound] with
      n hgeo hrem hbulk hboundary
  let L := Real.log (n : ℝ)
  have hn2 := hgeo.n_ge_two
  have hQpos := hgeo.narrow_pos
  have hqerr (q : ℕ) (hq : q ∈ Ioc (V20.narrow n) (sqNarrow n)) :
      (∑ a ∈ (range (q + 1)).filter (fun a => a.Coprime q),
        ∫ t in V19.cell n (V20.narrow n) (V20.width n) (q, a),
          ‖V31.Vi3 n t - Va2.model n (q, a) t‖ ^ 2) ≤
        8 * V8i.Vph n q +
          (8 * (q : ℝ) * ((n + 1 + V8i.V15 n q : ℕ) : ℝ) / (V8i.V15 n q : ℝ) ^ 2) *
            (Real.log (q : ℝ)) ^ 2 := by
    obtain ⟨hq2, _, hrpos, hrSmall, hrLarge, _, _, _, _⟩ := hgeo.q_props q hq
    let : NeZero q := ⟨by omega⟩
    obtain ⟨hh, hw, _, _⟩ := V8i.Vo6 (n + 1) (V19.radius n (V20.width n) q) hrpos hrSmall hrLarge
    have hfreq := V73.V106 (q := q) (n + 1) (V8i.V15 n q) (V19.radius n (V20.width n) q) hh hrpos.le hw
    apply (V8i.V160 n q (by omega) hgeo.width_pos).trans
    apply (mul_le_mul_of_nonneg_left hfreq (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    simp only [V8i.Vph, dite_eq_right (NeZero.ne q)]
    ring
  have herr_split : approxError₂ n ≤
      8 * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), V8i.Vph n q) +
      ∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
        (8 * (q : ℝ) * ((n + 1 + V8i.V15 n q : ℕ) : ℝ) / (V8i.V15 n q : ℝ) ^ 2) *
          (Real.log (q : ℝ)) ^ 2 := by
    unfold approxError₂ ringIdx
    rw [Vdq.V20s]
    apply (Finset.sum_le_sum hqerr).trans_eq
    rw [sum_add_distrib, Finset.mul_sum]
  have hph_bound (q : ℕ) (hq : q ∈ Ioc (V20.narrow n) (sqNarrow n)) :
      V8i.Vph n q ≤
        (1 + L) * (V9i.V98 n (start₂ n) q + V9i.Vb1 n (start₂ n) q) := by
    obtain ⟨hq2, _, _, _, _, hh, _, _, _⟩ := hgeo.q_props q hq
    let : NeZero q := ⟨by omega⟩
    rw [← V9i.V1st n (start₂ n) q]
    exact V3z.V1uh (by omega) hh
  have hph_sum : 8 * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), V8i.Vph n q) ≤
      (C_B + 8388608) * (n : ℝ) / L ^ 3 := by
    calc 8 * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), V8i.Vph n q)
        ≤ 8 * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n),
            (1 + L) * (V9i.V98 n (start₂ n) q + V9i.Vb1 n (start₂ n) q)) :=
          mul_le_mul_of_nonneg_left (sum_le_sum hph_bound) (by norm_num)
      _ = 8 * (1 + L) * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), V9i.V98 n (start₂ n) q) +
          8 * (1 + L) * (∑ q ∈ Ioc (V20.narrow n) (sqNarrow n), V9i.Vb1 n (start₂ n) q) := by
          simp_rw [mul_add, sum_add_distrib, ← Finset.mul_sum]
          ring
      _ ≤ C_B * (n : ℝ) / L ^ 3 + 8388608 * (n : ℝ) / L ^ 3 := add_le_add hbulk hboundary
      _ = (C_B + 8388608) * (n : ℝ) / L ^ 3 := by ring
  calc approxError₂ n
      ≤ (C_B + 8388608) * (n : ℝ) / L ^ 3 + (n : ℝ) / L ^ 3 :=
        herr_split.trans (add_le_add hph_sum hrem)
    _ = (1 + C_B + 8388608) * (n : ℝ) / L ^ 3 := by ring

private theorem full_sub_model_bound (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ‖fullIntegral₂ n - modelIntegral₂ n‖ ≤ ε * (n : ℝ) := by
  obtain ⟨C_M, hCM, hM_ev⟩ := modelEnergy₂_bound
  obtain ⟨C_E, hCE, hE_ev⟩ := approxError₂_bound
  have hloglim : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  let B : ℝ := max (Real.sqrt (4 * C_E / ε)) ((2 * C_M / ε) ^ 2) + 2
  filter_upwards [geom_ev, hM_ev, hE_ev, hloglim.eventually (eventually_ge_atTop B)] with
      n hgeo hM hE hLbig
  let L := Real.log (n : ℝ)
  have hL1 : 1 ≤ L := hgeo.log_ge_one
  have hLpos : 0 < L := by linarith
  have hη : 0 < 1 / L := by positivity
  have hLbig' : max (Real.sqrt (4 * C_E / ε)) ((2 * C_M / ε) ^ 2) ≤ L := by
    dsimp [L]
    linarith only [hLbig]
  have hL_err : Real.sqrt (4 * C_E / ε) ≤ L := (le_max_left _ _).trans hLbig'
  have hL_mod : (2 * C_M / ε) ^ 2 ≤ L := (le_max_right _ _).trans hLbig'
  have hErr_part : (1 + 1 / (1 / L)) * approxError₂ n ≤ (ε / 2) * (n : ℝ) := by
    have hLsq : 4 * C_E / ε ≤ L ^ 2 := by
      have h1 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hL_err 2
      rw [Real.sq_sqrt (by positivity)] at h1
      exact h1
    have hnpos : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    calc (1 + 1 / (1 / L)) * approxError₂ n
        = (1 + L) * approxError₂ n := by field_simp
      _ ≤ (2 * L) * (C_E * (n : ℝ) / L ^ 3) :=
          mul_le_mul (by linarith) hE
            (sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _) (by positivity)
      _ = (2 * C_E / L ^ 2) * (n : ℝ) := by field_simp
      _ ≤ (ε / 2) * (n : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hnpos
          apply (div_le_iff₀ (sq_pos_of_pos hLpos)).2
          have h2 := (div_le_iff₀ hε).1 hLsq
          linarith only [h2]
  have hMod_part : (1 / L) * modelEnergy₂ n ≤ (ε / 2) * (n : ℝ) := by
    have hsqrt : 2 * C_M / ε ≤ Real.sqrt L := by
      have h1 := Real.sqrt_le_sqrt hL_mod
      rwa [Real.sqrt_sq (by positivity)] at h1
    have hnpos : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hLsqrt : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hLpos.le
    calc (1 / L) * modelEnergy₂ n
        ≤ (1 / L) * (C_M * (n : ℝ) * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hM hη.le
      _ = (C_M / Real.sqrt L) * (n : ℝ) := by
          have hspos : (Real.sqrt L) ≠ 0 := (Real.sqrt_pos.mpr hLpos).ne'
          have h1 : (1 / L) * (C_M * (n : ℝ) * Real.sqrt L) =
              (C_M * (n : ℝ) * Real.sqrt L) / (Real.sqrt L * Real.sqrt L) := by
            rw [hLsqrt]; ring
          rw [h1]
          field_simp [hspos]
      _ ≤ (ε / 2) * (n : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hnpos
          apply (div_le_iff₀ (Real.sqrt_pos.mpr hLpos)).2
          have h2 := (div_le_iff₀ hε).1 hsqrt
          linarith only [h2]
  let osc : ℝ → ℂ := fun t => V31.phase (-(n : ℝ) * t)
  have hOsc : Continuous osc := by unfold osc V31.phase; fun_prop
  have hS : Continuous (V31.Vi3 n) := by unfold V31.Vi3 V31.phase; fun_prop
  have hF : Continuous (V8k.V13w n) := (hS.pow 2).mul hOsc
  unfold fullIntegral₂ modelIntegral₂ ringIdx
  rw [integral_eq_sum_ringIdx hgeo.narrow_le_sq hgeo.budget_sq _ hF, ← Finset.sum_sub_distrib]
  have hsplit (i : ℕ × ℕ) :
      (∫ t in V19.cell n (V20.narrow n) (V20.width n) i, V8k.V13w n t) -
        (∫ t in V19.cell n (V20.narrow n) (V20.width n) i, Va2.model n i t ^ 2 * osc t) =
      ∫ t in V19.cell n (V20.narrow n) (V20.width n) i,
        (V31.Vi3 n t ^ 2 - Va2.model n i t ^ 2) * osc t := by
    have hpart : V19.cell n (V20.narrow n) (V20.width n) i ⊆ Set.Ioc (0 : ℝ) 1 :=
      Set.inter_subset_right
    have h₁ : IntegrableOn (V8k.V13w n) (V19.cell n (V20.narrow n) (V20.width n) i) volume :=
      (hF.intervalIntegrable 0 1).1.mono_set hpart
    have hm : Continuous (fun t => Va2.model n i t ^ 2 * osc t) :=
      ((Va2.Ve5 n i).pow 2).mul hOsc
    have h₂ : IntegrableOn (fun t => Va2.model n i t ^ 2 * osc t)
        (V19.cell n (V20.narrow n) (V20.width n) i) volume :=
      (hm.intervalIntegrable 0 1).1.mono_set hpart
    rw [← integral_sub h₁ h₂]
    simp [V8k.V13w, osc, sub_mul]
  dsimp only [osc] at hsplit
  simp_rw [hsplit]
  apply (norm_sum_le _ _).trans
  apply (V8j.Vvf (ringIdx n) (V19.cell n (V20.narrow n) (V20.width n))
    (fun _ _ => Set.inter_subset_right)
    (V31.Vi3 n) (Va2.model n) osc hS (fun i _ => Va2.Ve5 n i) hOsc
    (fun t => le_of_eq (Complex.norm_exp_ofReal_mul_I (2 * Real.pi * (-(n : ℝ) * t)))) hη).trans
  change (1 + 1 / (1 / L)) * approxError₂ n + (1 / L) * modelEnergy₂ n ≤ ε * (n : ℝ)
  linarith only [hErr_part, hMod_part]

private theorem cap_sq_eq_min {n : ℕ} (h : sqNarrow n ≤ V20.cutoff n) :
    V19.cap n (sqNarrow n) (V20.width n) =
      V19.cap n (Min.min (V20.cutoff n) (sqNarrow n)) (V20.width n) := by
  rw [min_eq_right h]

end

theorem Conjectures.Cuts.Task6af0a69f44e255854c404689 : (have x1 : ℕ → ℕ := fun (x1 : ℕ) => Nat.log (2 : ℕ) (x1 + (2 : ℕ)) ^ (2 : ℕ); have x2 : ℕ → ℕ := fun (x2 : ℕ) => ⌊(↑x2 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x3 : ℕ → ℕ := fun (x3 : ℕ) => (256 : ℕ) * x2 x3 * x1 x3; have x4 : ℕ → ℕ := fun (x4 : ℕ) => Min.min (x2 x4) (x1 x4 ^ (2 : ℕ)); have x5 : ℕ → ℕ → ℕ → Set ℝ := fun (x5 x6 x7 : ℕ) => {x8 : ℝ | ∃ (x9 : ℕ) (x10 : ℕ), (1 : ℕ) ≤ x9 ∧ x9 ≤ x6 ∧ x10 ≤ x9 ∧ x10.Coprime x9 ∧ |x8 - (↑x10 : ℝ) / (↑x9 : ℝ)| ≤ (↑x7 : ℝ) / ((↑x9 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ := fun (x6 : ℕ) => if Nat.Prime x6 then Real.log (↑x6 : ℝ) else (0 : ℝ); have x7 : ℝ → ℂ := fun (x7 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x7) : ℂ) * Complex.I); have x8 : ℕ → ℝ → ℂ := fun (x8 : ℕ) (x9 : ℝ) => (∑ x10 ∈ Finset.range (x8 + (1 : ℕ)), (↑(x6 x10) : ℂ) * x7 ((↑x10 : ℝ) * x9)) ^ (2 : ℕ) * x7 (-(↑x8 : ℝ) * x9); ∀ (x9 : ℝ), (0 : ℝ) < x9 → ∃ (x11 : ℕ), ∀ (x12 : ℕ), x11 ≤ x12 → Even x12 → -(x9 * (↑x12 : ℝ)) ≤ (∫ (x15 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x12 (x4 x12) (x3 x12) \ x5 x12 (x1 x12) (x3 x12)).indicator (x8 x12) x15).re) := by
  dsimp only
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((geom_ev.and (full_sub_model_bound (ε / 2) (by positivity))).and
      (signed_model_lower (ε / 2) (by positivity)))
  refine ⟨N, fun n hn hEven => ?_⟩
  obtain ⟨⟨hgeo, hErr⟩, hModel⟩ := hN n hn
  have hb := (abs_le.mp ((Complex.abs_re_le_norm _).trans hErr)).1
  rw [Complex.sub_re] at hb
  have hM : -(ε / 2 * (n : ℝ)) ≤ (modelIntegral₂ n).re := hModel hEven
  have hsum := add_le_add hb hM
  rw [sub_add_cancel] at hsum
  have htarget : -(ε * (n : ℝ)) ≤ (fullIntegral₂ n).re := by linarith only [hsum]
  refine htarget.trans_eq ?_
  unfold fullIntegral₂
  rw [cap_sq_eq_min hgeo.sq_le_cutoff]
  rfl
