import Mathlib

open scoped Topology

/-!
L-goldbach-power-box-vanishing: the power-box weight
`sqrt n * log₂ n * (log (n+1))^2 / n` tends to zero, hence is below every positive `ε`
for all sufficiently large `n`.
-/

theorem PEqualNP.Outside.L_goldbach_power_box_vanishing :
    ∀ ε : ℝ, 0<ε → ∃ X : ℕ, ∀ n≥X, ((Nat.sqrt n:ℝ)*(Nat.log 2 n:ℝ))*Real.log ((n+1:ℕ):ℝ)^2/(n:ℝ)<ε := by
  intro ε hε
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- step 1: `(log x)^3 / sqrt x → 0`
  have hsmall : Filter.Tendsto (fun x : ℝ => Real.log x ^ 3 / Real.sqrt x)
      Filter.atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop 3 (s := (1/2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
    refine h.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with x hx
    simp [Real.sqrt_eq_rpow]
  -- step 2: `4/log 2` times that still tends to zero
  have hU : Filter.Tendsto
      (fun x : ℝ => (4/Real.log 2) * (Real.log x ^ 3 / Real.sqrt x)) Filter.atTop (𝓝 0) := by
    simpa using hsmall.const_mul (4/Real.log 2)
  -- step 3: squeeze the real envelope
  have hG : Filter.Tendsto
      (fun x : ℝ => Real.sqrt x * (Real.log x / Real.log 2) * (Real.log (x+1))^2 / x)
      Filter.atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop (2:ℝ)] with x hx
      have hx0 : (0:ℝ) < x := by linarith
      have hlx : (0:ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
      have h1 : (0:ℝ) ≤ Real.sqrt x * (Real.log x / Real.log 2) :=
        mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hlx (le_of_lt hlog2))
      have h2 : (0:ℝ) ≤ (Real.log (x+1))^2 := sq_nonneg _
      exact div_nonneg (mul_nonneg h1 h2) (le_of_lt hx0)
    · filter_upwards [Filter.eventually_ge_atTop (2:ℝ)] with x hx
      have hx0 : (0:ℝ) < x := by linarith
      have hlx : (0:ℝ) < Real.log x := Real.log_pos (by linarith)
      have hsqrtpos : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have hsqx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (le_of_lt hx0)
      have hlogx1 : Real.log (x+1) ≤ 2 * Real.log x := by
        have h1 : Real.log (x+1) ≤ Real.log (2*x) := by
          apply Real.log_le_log (by linarith)
          linarith
        have h2 : Real.log (2*x) = Real.log 2 + Real.log x :=
          Real.log_mul (by norm_num) (ne_of_gt hx0)
        have h3 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) (by linarith)
        rw [h2] at h1
        linarith
      have hsq : (Real.log (x+1))^2 ≤ 4 * (Real.log x)^2 := by
        nlinarith [hlogx1, Real.log_nonneg (by linarith : (1:ℝ) ≤ x+1)]
      have hbase : (Real.log x / Real.log 2) * (Real.log (x+1))^2 ≤ (4/Real.log 2) * (Real.log x)^3 := by
        have hmono : (Real.log x / Real.log 2) * (Real.log (x+1))^2
            ≤ (Real.log x / Real.log 2) * (4 * (Real.log x)^2) :=
          mul_le_mul_of_nonneg_left hsq (div_nonneg (le_of_lt hlx) (le_of_lt hlog2))
        have heq : (Real.log x / Real.log 2) * (4 * (Real.log x)^2)
            = (4/Real.log 2) * (Real.log x)^3 := by
          field_simp
        rw [heq] at hmono
        exact hmono
      have hGform : Real.sqrt x * (Real.log x / Real.log 2) * (Real.log (x+1))^2 / x
          = (Real.log x / Real.log 2) * (Real.log (x+1))^2 / Real.sqrt x := by
        rw [div_eq_div_iff (ne_of_gt hx0) (ne_of_gt hsqrtpos)]
        calc Real.sqrt x * (Real.log x / Real.log 2) * (Real.log (x+1))^2 * Real.sqrt x
            = (Real.log x / Real.log 2) * (Real.log (x+1))^2 * (Real.sqrt x * Real.sqrt x) := by
              ring
          _ = (Real.log x / Real.log 2) * (Real.log (x+1))^2 * x := by rw [hsqx]
      rw [hGform]
      calc (Real.log x / Real.log 2) * (Real.log (x+1))^2 / Real.sqrt x
          ≤ ((4/Real.log 2) * (Real.log x)^3) / Real.sqrt x :=
            div_le_div_of_nonneg_right hbase (le_of_lt hsqrtpos)
        _ = (4/Real.log 2) * (Real.log x ^ 3 / Real.sqrt x) := by ring
  -- step 4: transport along `ℕ → ℝ`
  have hcomp : Filter.Tendsto
      (fun n : ℕ => Real.sqrt (n:ℝ) * (Real.log (n:ℝ) / Real.log 2) * (Real.log ((n:ℝ)+1))^2 / (n:ℝ))
      Filter.atTop (𝓝 0) := hG.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt (n:ℝ) * (Real.log (n:ℝ) / Real.log 2) * (Real.log ((n:ℝ)+1))^2 / (n:ℝ) < ε :=
    hcomp.eventually (Iio_mem_nhds hε)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max X 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hXn : X ≤ n := le_trans (le_max_left _ _) hn
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcast : ((n+1:ℕ):ℝ) = (n:ℝ) + 1 := by push_cast; ring
  have hsqrt_nat : ((Nat.sqrt n : ℕ):ℝ) ≤ Real.sqrt (n:ℝ) := by
    have hsqn : ((Nat.sqrt n : ℕ):ℝ)^2 ≤ (n:ℝ) := by
      have h := Nat.sqrt_le' n
      exact_mod_cast h
    rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ ((Nat.sqrt n : ℕ):ℝ))]
    exact Real.sqrt_le_sqrt hsqn
  have hlog_nat : (Nat.log 2 n:ℝ) ≤ Real.log (n:ℝ) / Real.log 2 := by
    have hpow : (2:ℝ)^(Nat.log 2 n) ≤ (n:ℝ) := by
      have h := Nat.pow_log_le_self 2 (by omega : n ≠ 0)
      exact_mod_cast h
    have hlogpow : (Nat.log 2 n:ℝ) * Real.log 2 ≤ Real.log (n:ℝ) := by
      have h := Real.log_le_log (by positivity : (0:ℝ) < (2:ℝ)^(Nat.log 2 n)) hpow
      rwa [Real.log_pow] at h
    rw [le_div_iff₀ hlog2]
    exact hlogpow
  have hA : (Nat.sqrt n:ℝ) * (Nat.log 2 n:ℝ)
      ≤ Real.sqrt (n:ℝ) * (Real.log (n:ℝ) / Real.log 2) :=
    mul_le_mul hsqrt_nat hlog_nat (by positivity) (Real.sqrt_nonneg _)
  rw [hcast]
  calc ((Nat.sqrt n:ℝ) * (Nat.log 2 n:ℝ)) * (Real.log ((n:ℝ)+1))^2 / (n:ℝ)
      ≤ (Real.sqrt (n:ℝ) * (Real.log (n:ℝ) / Real.log 2)) * (Real.log ((n:ℝ)+1))^2 / (n:ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA (sq_nonneg _)) (le_of_lt hn0)
    _ < ε := hX n hXn
