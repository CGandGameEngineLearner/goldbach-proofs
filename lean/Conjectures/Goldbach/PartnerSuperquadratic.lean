import Mathlib
import Conjectures.Goldbach.PrimitivePartnerCubicMass

/-!
对所有实指数 `t > 2`，一致控制跨导子原始搭档的 `t` 次矩。
复用已合并社区模块 `Conjectures.Goldbach.PrimitivePartnerCubicMass`（PR #4245）
与 `Conjectures.Goldbach.SharpSingularSeriesRatios` 中的局部 Plancherel 等式、
素数幂逐点界与全局乘积分解。
-/

namespace SuperquadraticPartnerResearch
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open CubicPartnerResearch
open scoped BigOperators Classical

/-- 有限非负实数乘积的实数幂等于各因子实数幂的乘积。 -/
private theorem prod_rpow_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) (t : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ^ t = ∏ i ∈ s, (f i) ^ t := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have ha0 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hs0 : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [Real.mul_rpow ha0 hs0, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

/-- 对 `[0, 1]` 中的数，`t ≥ 2` 时 `x ^ t ≤ x ^ 2`。 -/
private theorem rpow_le_sq_of_mem_unit {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (ht : 2 ≤ t) :
    x ^ t ≤ x ^ 2 := by
  rcases eq_or_lt_of_le hx0 with rfl | hxpos
  · have htpos : (0 : ℝ) < t := by linarith
    rw [Real.zero_rpow htpos.ne', zero_pow (by norm_num)]
  · calc
      x ^ t ≤ x ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hxpos hx1 ht
      _ = x ^ 2 := Real.rpow_two x

/-- 对 `x ≥ 0` 与 `δ > 0`，`x ^ (2 + δ) = x ^ 2 * x ^ δ`。 -/
private theorem rpow_two_add {x δ : ℝ} (hx : 0 ≤ x) (hδ : 0 < δ) :
    x ^ (2 + δ) = x ^ 2 * x ^ δ := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · have h2δ : (0 : ℝ) < 2 + δ := by linarith
    rw [Real.zero_rpow h2δ.ne', zero_pow (by norm_num), zero_mul]
  · rw [Real.rpow_add hxpos, Real.rpow_two]

/-- 依赖于超额指数 `δ = t - 2 > 0` 的大素数截断阈值。 -/
private noncomputable def thresh (δ : ℝ) : ℕ :=
  max 5 (Nat.ceil ((2 * (2 : ℝ) ^ (1 / δ)) ^ 2))

/-- 单个素数位置处的局部包络函数。 -/
private noncomputable def env (δ : ℝ) (p : ℕ) : ℝ :=
  if p < thresh δ then 2 else 1 + 1 / ((p : ℝ) - 2) ^ (1 + δ)

/-- 全局一致常数 `C(δ) > 0`。 -/
private noncomputable def globalConst (δ : ℝ) : ℝ :=
  (2 : ℝ) ^ (thresh δ) * Real.exp (∑' n : ℕ, 1 / ((n : ℝ) ^ (1 + δ)))

private theorem globalConst_pos (δ : ℝ) : 0 < globalConst δ := by
  unfold globalConst
  positivity

private theorem one_le_env {δ : ℝ} (p : ℕ) : 1 ≤ env δ p := by
  unfold env
  split_ifs with h
  · norm_num
  · have hp5 : (5 : ℝ) ≤ p := by
      have hge : thresh δ ≤ p := Nat.le_of_not_lt h
      have h5 : 5 ≤ p := le_trans (le_max_left _ _) hge
      exact_mod_cast h5
    have hd : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    have hterm : 0 ≤ 1 / ((p : ℝ) - 2) ^ (1 + δ) := by positivity
    linarith

/-- 对任意大素数 `p ≥ thresh δ`，非平凡行收缩界不超过 `1`。 -/
private theorem nonprincipal_contraction {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hp : thresh δ ≤ p) :
    (Real.sqrt p / ((p : ℝ) - 2)) ^ δ * (((p : ℝ) - 1) / ((p : ℝ) - 2)) ≤ 1 := by
  have hp5_nat : 5 ≤ p := le_trans (le_max_left _ _) hp
  have hp5 : (5 : ℝ) ≤ p := by exact_mod_cast hp5_nat
  have hp0 : (0 : ℝ) < p := by linarith
  have hd : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  let R : ℝ := (2 : ℝ) ^ (1 / δ)
  have hRpos : 0 < R := by dsimp only [R]; positivity
  have hRpow : R ^ δ = 2 := by
    dsimp only [R]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div_mul_cancel hδ.ne', Real.rpow_one]
  have hceil : (2 * R) ^ 2 ≤ (p : ℝ) := by
    have hle : Nat.ceil ((2 * R) ^ 2) ≤ p := le_trans (le_max_right _ _) hp
    exact (Nat.le_ceil _).trans (by exact_mod_cast hle)
  have hsqrt_ge : 2 * R ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by positivity) hp0.le]
    exact hceil
  have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hhalf : (p : ℝ) / 2 ≤ (p : ℝ) - 2 := by linarith
  have hstep1 : Real.sqrt p / ((p : ℝ) - 2) ≤ 2 / Real.sqrt p := by
    have hdiv : Real.sqrt p / ((p : ℝ) - 2) ≤ Real.sqrt p / ((p : ℝ) / 2) :=
      div_le_div_of_nonneg_left hsqrt_pos.le (by linarith) hhalf
    have heq : Real.sqrt p / ((p : ℝ) / 2) = 2 / Real.sqrt p := by
      have hsq : Real.sqrt p * Real.sqrt p = (p : ℝ) := Real.mul_self_sqrt hp0.le
      field_simp [hsqrt_pos.ne', hp0.ne']
      linarith
    exact hdiv.trans_eq heq
  have hstep2 : 2 / Real.sqrt p ≤ 1 / R := by
    rw [div_le_div_iff₀ hsqrt_pos hRpos]
    linarith
  have hcap : Real.sqrt p / ((p : ℝ) - 2) ≤ 1 / R := hstep1.trans hstep2
  have hpow_le : (Real.sqrt p / ((p : ℝ) - 2)) ^ δ ≤ 1 / 2 := by
    calc
      (Real.sqrt p / ((p : ℝ) - 2)) ^ δ ≤ (1 / R) ^ δ :=
        Real.rpow_le_rpow (by positivity) hcap hδ.le
      _ = 1 / R ^ δ := by rw [Real.div_rpow (by norm_num) hRpos.le, Real.one_rpow]
      _ = 1 / 2 := by rw [hRpow]
  have hratio_le : ((p : ℝ) - 1) / ((p : ℝ) - 2) ≤ 2 := by
    rw [div_le_iff₀ hd]
    linarith
  have hratio_nn : 0 ≤ ((p : ℝ) - 1) / ((p : ℝ) - 2) :=
    div_nonneg (by linarith) hd.le
  calc
    (Real.sqrt p / ((p : ℝ) - 2)) ^ δ * (((p : ℝ) - 1) / ((p : ℝ) - 2))
      ≤ (1 / 2) * 2 := mul_le_mul hpow_le hratio_le hratio_nn (by norm_num)
    _ = 1 := by norm_num

/-- 整除情形（`p ∣ m`）下的局部 `t` 次矩不超过 `1`。 -/
private theorem divisible_row_rpow {p : ℕ} [Fact p.Prime] (e m : ℕ) (hp : p ∣ m)
    (A : DirichletCharacter ℂ (p * p ^ e)) {t : ℝ} (ht : 2 ≤ t) :
    let q := p * p ^ e
    let W := ‖J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖
    (∑ B : DirichletCharacter ℂ q, (‖J A B (m : ZMod q)‖ / W) ^ t) ≤ 1 := by
  intro q W
  have ph : p.Prime := Fact.out
  have ordinary : W = (q.totient : ℝ) := by
    dsimp only [W, q]
    rw [ordinary_prime_power, ite_eq_left hp, ← pow_succ', Nat.totient_prime_pow_succ ph]
    push_cast [Nat.cast_sub ph.one_le]
    ring
  have qpos : 0 < q := Nat.mul_pos ph.pos (pow_pos ph.pos e)
  have wp : 0 < W := by
    rw [ordinary]
    exact_mod_cast Nat.totient_pos.mpr qpos
  have hsum2 : (∑ B : DirichletCharacter ℂ q, (‖J A B (m : ZMod q)‖ / W) ^ 2) = 1 := by
    simp_rw [div_pow, ← sum_div]
    rw [row_plancherel]
    change (q.totient : ℝ) * W / W ^ 2 = 1
    rw [← ordinary]
    field_simp [wp.ne']
  calc
    (∑ B : DirichletCharacter ℂ q, (‖J A B (m : ZMod q)‖ / W) ^ t)
      ≤ ∑ B : DirichletCharacter ℂ q, (‖J A B (m : ZMod q)‖ / W) ^ 2 := by
        apply Finset.sum_le_sum
        intro B _
        apply rpow_le_sq_of_mem_unit (div_nonneg (norm_nonneg _) wp.le) _ ht
        exact (div_le_one wp).2 (TwistedGoldbachSingularSeries.chars_le_units A B _)
    _ = 1 := hsum2

/-- 互素情形（`¬ p ∣ m`，奇素数 `p ≥ 3`）下的局部 `t` 次矩不超过 `env (t - 2) p`。 -/
private theorem unit_row_rpow {p : ℕ} [Fact p.Prime] (odd : 3 ≤ p) (e m : ℕ) (mp : ¬ p ∣ m)
    (A : DirichletCharacter ℂ (p * p ^ e)) {t : ℝ} (ht : 2 < t) :
    let q := p * p ^ e
    let W := ‖J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖
    (∑ B : DirichletCharacter ℂ q, (‖J A B (m : ZMod q)‖ / W) ^ t) ≤ env (t - 2) p := by
  intro q W
  let δ : ℝ := t - 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have ht_eq : t = 2 + δ := by dsimp only [δ]; ring
  let X (B : DirichletCharacter ℂ q) : ℝ := ‖J A B (m : ZMod q)‖ / W
  have hp : p.Prime := Fact.out
  have pp : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have ge3 : (3 : ℝ) ≤ p := by exact_mod_cast odd
  have dpos : 0 < (p : ℝ) - 2 := by linarith
  have we : W = (p : ℝ) ^ e * ((p : ℝ) - 2) := by
    dsimp only [W, q]
    rw [ordinary_prime_power, ite_eq_right mp, Nat.cast_pow]
  have wp : 0 < W := we ▸ mul_pos (pow_pos pp e) dpos
  have phie : (q.totient : ℝ) = (p : ℝ) ^ e * ((p : ℝ) - 1) := by
    dsimp only [q]
    rw [← pow_succ', Nat.totient_prime_pow_succ hp]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  have hXnn : ∀ B, 0 ≤ X B := fun B => div_nonneg (norm_nonneg _) wp.le
  have hXle1 : ∀ B, X B ≤ 1 := fun B =>
    (div_le_one wp).2 (TwistedGoldbachSingularSeries.chars_le_units A B _)
  have hmass : (∑ B : DirichletCharacter ℂ q, (X B) ^ 2) = ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
    simp only [X, div_pow, ← sum_div, row_plancherel]
    change (q.totient : ℝ) * W / W ^ 2 = _
    rw [phie, we]
    field_simp [dpos.ne', pp.ne']
  by_cases hsmall : p < thresh δ
  · -- 小素数直接退回到二次矩并由 `2` 控制
    change (∑ B : DirichletCharacter ℂ q, (X B) ^ t) ≤ env δ p
    rw [env, ite_eq_left hsmall]
    calc
      (∑ B : DirichletCharacter ℂ q, (X B) ^ t)
        ≤ ∑ B : DirichletCharacter ℂ q, (X B) ^ 2 :=
          Finset.sum_le_sum (fun B _ => rpow_le_sq_of_mem_unit (hXnn B) (hXle1 B) ht.le)
      _ = ((p : ℝ) - 1) / ((p : ℝ) - 2) := hmass
      _ ≤ 2 := by rw [div_le_iff₀ dpos]; linarith
  · -- 大素数区分首特征是否局部平凡
    have hlarge : thresh δ ≤ p := Nat.le_of_not_lt hsmall
    change (∑ B : DirichletCharacter ℂ q, (X B) ^ t) ≤ env δ p
    rw [env, ite_eq_right hsmall]
    have cap (B : DirichletCharacter ℂ q) (h : ¬ (A = 1 ∧ B = 1)) :
        X B ≤ (if A = 1 ∨ B = 1 then 1 else Real.sqrt p) / ((p : ℝ) - 2) := by
      apply (div_le_iff₀ wp).2
      rw [we]
      convert unit_pointwise e m mp A B h using 1
      field_simp [dpos.ne']
    by_cases hA : A = 1
    · -- 首特征局部平凡：分离 `B = 1`，对其余项使用 `1 / (p - 2)` 上界
      have hX1 : X 1 = 1 := by
        dsimp only [X]
        rw [hA]
        exact div_self wp.ne'
      let c : ℝ := (1 / ((p : ℝ) - 2)) ^ δ
      have hterm (B : DirichletCharacter ℂ q) :
          (X B) ^ t ≤ c * (X B) ^ 2 + if B = 1 then 1 - c else 0 := by
        by_cases hB : B = 1
        · subst hB
          simp only [hX1, Real.one_rpow, one_pow, mul_one, ↓reduceIte]
          linarith
        · rw [ite_eq_right hB, add_zero, ht_eq, rpow_two_add (hXnn B) hδ, mul_comm]
          have hBcap : X B ≤ 1 / ((p : ℝ) - 2) := by
            simpa [hA] using cap B (by tauto)
          have hBpow : (X B) ^ δ ≤ c :=
            Real.rpow_le_rpow (hXnn B) hBcap hδ.le
          exact mul_le_mul_of_nonneg_right hBpow (sq_nonneg _)
      calc
        (∑ B : DirichletCharacter ℂ q, (X B) ^ t)
          ≤ ∑ B : DirichletCharacter ℂ q, (c * (X B) ^ 2 + if B = 1 then 1 - c else 0) :=
            Finset.sum_le_sum (fun B _ => hterm B)
        _ = c * (∑ B : DirichletCharacter ℂ q, (X B) ^ 2) + (1 - c) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            simp
        _ = 1 + c * (1 / ((p : ℝ) - 2)) := by
            rw [hmass]
            field_simp [dpos.ne']
            ring
        _ = 1 + 1 / ((p : ℝ) - 2) ^ (1 + δ) := by
            dsimp only [c]
            have hinv : (1 / ((p : ℝ) - 2)) ^ δ * (1 / ((p : ℝ) - 2)) =
                1 / ((p : ℝ) - 2) ^ (1 + δ) := by
              rw [Real.div_rpow (by norm_num) dpos.le, Real.one_rpow,
                  Real.rpow_add dpos, Real.rpow_one]
              field_simp [dpos.ne', (Real.rpow_pos_of_pos dpos δ).ne']
            rw [hinv]
    · -- 首特征局部非平凡：对二次矩提取最大值的 `δ` 次幂
      have hcap_all (B : DirichletCharacter ℂ q) : X B ≤ Real.sqrt p / ((p : ℝ) - 2) := by
        have h := cap B (by tauto)
        by_cases hB : B = 1
        · subst hB
          simp only [or_true, ↓reduceIte] at h
          have h1p : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_le
          exact h.trans (div_le_div_of_nonneg_right (Real.one_le_sqrt.mpr h1p) dpos.le)
        · simpa [hA, hB] using h
      calc
        (∑ B : DirichletCharacter ℂ q, (X B) ^ t)
          ≤ ∑ B : DirichletCharacter ℂ q, (Real.sqrt p / ((p : ℝ) - 2)) ^ δ * (X B) ^ 2 := by
            apply Finset.sum_le_sum
            intro B _
            rw [ht_eq, rpow_two_add (hXnn B) hδ, mul_comm]
            exact mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow (hXnn B) (hcap_all B) hδ.le) (sq_nonneg _)
        _ = (Real.sqrt p / ((p : ℝ) - 2)) ^ δ * (((p : ℝ) - 1) / ((p : ℝ) - 2)) := by
            rw [← Finset.mul_sum, hmass]
        _ ≤ 1 := nonprincipal_contraction hδ hlarge
        _ ≤ 1 + 1 / ((p : ℝ) - 2) ^ (1 + δ) := by
            have hterm : 0 ≤ 1 / ((p : ℝ) - 2) ^ (1 + δ) := by positivity
            linarith

/-- 单个素数幂处的局部 `t` 次矩包络界。 -/
private theorem local_budget_super {p q : ℕ} [Fact p.Prime] [NeZero q] (k m : ℕ)
    (eqQ : q = p * p ^ k) (he : Even m) (A : DirichletCharacter ℂ q) {t : ℝ} (ht : 2 < t) :
    (∑ B : DirichletCharacter ℂ q,
      ‖J A B (m : ZMod q) / J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)‖ ^ t) ≤
      env (t - 2) p := by
  subst q
  have hp : p.Prime := Fact.out
  simp only [norm_div]
  by_cases pm : p ∣ m
  · exact (divisible_row_rpow k m pm A ht.le).trans (one_le_env p)
  · have odd : 3 ≤ p := by
      have h2 := hp.two_le
      by_contra! small
      exact pm ((show p = 2 by omega) ▸ (even_iff_two_dvd.mp he))
    exact unit_row_rpow odd k m pm A ht

/-- 任意有限素数集上的局部包络乘积均被 `globalConst δ` 一致控制。 -/
private theorem product_budget_super {δ : ℝ} (hδ : 0 < δ) (S : Finset ℕ) :
    (∏ p ∈ S, env δ p) ≤ globalConst δ := by
  let S₁ := S.filter (fun p => p < thresh δ)
  let S₂ := S.filter (fun p => ¬ p < thresh δ)
  have hsplit : (∏ p ∈ S, env δ p) = (∏ p ∈ S₁, env δ p) * (∏ p ∈ S₂, env δ p) :=
    (Finset.prod_filter_mul_prod_filter_not S (fun p => p < thresh δ) (env δ)).symm
  have h1 : (∏ p ∈ S₁, env δ p) ≤ (2 : ℝ) ^ (thresh δ) := by
    have hval : (∏ p ∈ S₁, env δ p) = (2 : ℝ) ^ S₁.card := by
      calc
        (∏ p ∈ S₁, env δ p) = ∏ _p ∈ S₁, (2 : ℝ) := by
          apply Finset.prod_congr rfl
          intro p hp
          exact ite_eq_left (Finset.mem_filter.mp hp).2
        _ = (2 : ℝ) ^ S₁.card := by simp
    have hsub : S₁ ⊆ Finset.range (thresh δ) := by
      intro p hp
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    have hcard : S₁.card ≤ thresh δ := by
      simpa [Finset.card_range] using Finset.card_le_card hsub
    rw [hval]
    exact pow_le_pow_right₀ (by norm_num) hcard
  have h2_nn : 0 ≤ ∏ p ∈ S₂, env δ p :=
    Finset.prod_nonneg (fun p _ => zero_le_one.trans (one_le_env p))
  have h2 : (∏ p ∈ S₂, env δ p) ≤ Real.exp (∑' n : ℕ, 1 / ((n : ℝ) ^ (1 + δ))) := by
    have hexp_le : (∏ p ∈ S₂, env δ p) ≤
        ∏ p ∈ S₂, Real.exp (1 / ((p : ℝ) - 2) ^ (1 + δ)) := by
      apply Finset.prod_le_prod₀
      · intro p _
        exact zero_le_one.trans (one_le_env p)
      · intro p hp
        have hnot : ¬ p < thresh δ := (Finset.mem_filter.mp hp).2
        rw [env, ite_eq_right hnot, add_comm]
        exact Real.add_one_le_exp _
    rw [← Real.exp_sum] at hexp_le
    apply hexp_le.trans
    apply Real.exp_le_exp.mpr
    let g : ℕ → ℝ := fun n => 1 / ((n : ℝ) ^ (1 + δ))
    have hshift : (∑ p ∈ S₂, 1 / ((p : ℝ) - 2) ^ (1 + δ)) = ∑ p ∈ S₂, g (p - 2) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hge : thresh δ ≤ p := Nat.le_of_not_lt (Finset.mem_filter.mp hp).2
      have h2le : 2 ≤ p := le_trans (by omega : 2 ≤ 5) (le_trans (le_max_left _ _) hge)
      dsimp only [g]
      rw [Nat.cast_sub h2le]
      norm_num
    have hinj : Set.InjOn (fun p : ℕ => p - 2) (S₂ : Set ℕ) := by
      intro a ha b hb hab
      have ha2 : 2 ≤ a :=
        le_trans (by omega : 2 ≤ 5) (le_trans (le_max_left _ _) (Nat.le_of_not_lt (Finset.mem_filter.mp ha).2))
      have hb2 : 2 ≤ b :=
        le_trans (by omega : 2 ≤ 5) (le_trans (le_max_left _ _) (Nat.le_of_not_lt (Finset.mem_filter.mp hb).2))
      dsimp only at hab
      omega
    have hsum_img : (∑ p ∈ S₂, g (p - 2)) = ∑ n ∈ S₂.image (fun p => p - 2), g n :=
      (Finset.sum_image (f := g) hinj).symm
    have hsummable : Summable g :=
      Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 1 + δ)
    rw [hshift, hsum_img]
    exact hsummable.sum_le_tsum (S₂.image (fun p => p - 2)) (fun n _ => by dsimp only [g]; positivity)
  rw [hsplit, globalConst]
  exact mul_le_mul h1 h2 h2_nn (by positivity)

/-- 组装全局 `t` 次矩一致上界。 -/
private theorem assemble_superquadratic {t : ℝ} (ht : 2 < t)
    {r : ℕ} [NeZero r] (α : DirichletCharacter ℂ r) (hα : α.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s))
    (hf : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive) :
    (∑ b ∈ F, ‖series α b.2 m‖ ^ t) ≤
      globalConst (t - 2) * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ t := by
  classical
  have hδ : 0 < t - 2 := by linarith
  let L := r * ∏ b ∈ F, b.1
  have lpos : 0 < L :=
    Nat.mul_pos (NeZero.pos r) (prod_pos (fun b hb => Nat.pos_of_ne_zero (hf b hb).1))
  let : NeZero L := ⟨lpos.ne'⟩
  let I := ↥L.primeFactors
  let Q (i : I) := (i : ℕ) ^ L.factorization i
  let (i : I) : NeZero (Q i) := ⟨(Nat.ordProj_pos L i).ne'⟩
  let e := ZMod.equivPi L lpos.ne'
  let hr : r ∣ L := dvd_mul_right r _
  have divides (b : F) : b.val.1 ∣ L :=
    (dvd_prod_of_mem (fun z : Σ s : ℕ, DirichletCharacter ℂ s => z.1) b.property).trans
      (dvd_mul_left _ r)
  let B (b : F) := changeLevel (divides b) b.val.2
  let loc (b : F) (i : I) := component e (B b) i
  have inj : Function.Injective loc := by
    intro b c eq
    have same : B b = B c := by
      apply MulChar.ext
      intro u
      rw [reassemble e (B b) (u : ZMod L), reassemble e (B c) (u : ZMod L)]
      exact prod_congr rfl (fun i _ =>
        congrArg (fun χ : DirichletCharacter ℂ (Q i) => χ (e u i)) (congrFun eq i))
    have core {s u : ℕ} (a : DirichletCharacter ℂ s) (b' : DirichletCharacter ℂ u)
        (hs : s ∣ L) (hu : u ∣ L) (ha : a.IsPrimitive) (hb : b'.IsPrimitive)
        (h : changeLevel hs a = changeLevel hu b') :
        (⟨s, a⟩ : Σ n : ℕ, DirichletCharacter ℂ n) = ⟨u, b'⟩ := by
      have eqsu := congrArg DirichletCharacter.conductor h
      rw [conductor_changeLevel, conductor_changeLevel, ha, hb] at eqsu
      subst u
      exact congrArg (Sigma.mk s) (changeLevel_injective hs h)
    exact Subtype.ext (core _ _ _ _ (hf _ b.property).2 (hf _ c.property).2 same)
  let A (i : I) := component e (changeLevel hr α) i
  let W (i : I) (b : DirichletCharacter ℂ (Q i)) : ℝ :=
    ‖J (A i) b (m : ZMod (Q i)) / J (1 : DirichletCharacter ℂ (Q i)) 1 (m : ZMod (Q i))‖ ^ t
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ ^ t
  have on_b (b : F) : ‖series α b.val.2 m‖ ^ t = O * (∏ i, W i (loc b i)) := by
    let : NeZero b.val.1 := ⟨(hf _ b.property).1⟩
    rw [full_product e hα (hf _ b.property).2 hr (divides b) m hm he, norm_mul, norm_prod,
        Real.mul_rpow (norm_nonneg _) (prod_nonneg (fun _ _ => norm_nonneg _)),
        prod_rpow_nonneg _ _ t (fun _ _ => norm_nonneg _)]
  have nn (f : ∀ i, DirichletCharacter ℂ (Q i)) : 0 ≤ ∏ i, W i (f i) :=
    prod_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  have totals : (∑ b : F, ∏ i, W i (loc b i)) ≤ ∏ i, ∑ c, W i c := by
    rw [Fintype.prod_sum]
    let g (f : ∀ i, DirichletCharacter ℂ (Q i)) := ∏ i, W i (f i)
    change (∑ b : F, g (loc b)) ≤ ∑ f, g f
    rw [← sum_image (f := g) inj.injOn]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun f _ _ => nn f)
  have each (i : I) : (∑ c, W i c) ≤ env (t - 2) i := by
    have h := Nat.mem_primeFactors.mp i.property
    let : Fact (i : ℕ).Prime := ⟨h.1⟩
    obtain ⟨a, ha⟩ : ∃ a, L.factorization i = a + 1 := by
      have := (h.1.dvd_iff_one_le_factorization lpos.ne').mp h.2.1
      exact ⟨L.factorization i - 1, by omega⟩
    exact local_budget_super (p := (i : ℕ)) (q := Q i) a m
      (by change (i : ℕ) ^ L.factorization i = _; rw [ha, pow_succ']) he (A i) ht
  have bound : (∏ i, ∑ c, W i c) ≤ globalConst (t - 2) := calc
    (∏ i, ∑ c, W i c)
      ≤ ∏ i : I, env (t - 2) i :=
        prod_le_prod₀ (fun i _ => sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _))
          (fun i _ => each i)
    _ = ∏ j ∈ L.primeFactors, env (t - 2) j := prod_coe_sort _ _
    _ ≤ globalConst (t - 2) := product_budget_super hδ _
  rw [← sum_coe_sort F]
  calc
    (∑ b : F, ‖series α b.val.2 m‖ ^ t)
      = O * ∑ b : F, ∏ i, W i (loc b i) := by
        rw [mul_sum]
        exact sum_congr rfl (fun b _ => on_b b)
    _ ≤ O * globalConst (t - 2) :=
        mul_le_mul_of_nonneg_left (totals.trans bound) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = globalConst (t - 2) * O := mul_comm _ _

end SuperquadraticPartnerResearch

theorem Conjectures.Goldbach.PartnerSuperquadratic :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  exact ∀ t : ℝ, 2 < t → ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive →
    ∀ m : ℕ, 0 < m → Even m →
    ∀ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
    (∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive) →
    (∑ b ∈ F, ‖S α b.2 m‖ ^ t) ≤ C * ‖O m‖ ^ t := by
  classical
  dsimp only
  intro t ht
  refine ⟨SuperquadraticPartnerResearch.globalConst (t - 2),
    SuperquadraticPartnerResearch.globalConst_pos (t - 2), ?_⟩
  intro r inst α hα m hm he F hF
  exact SuperquadraticPartnerResearch.assemble_superquadratic ht α hα m hm he F hF
