import Mathlib
import Conjectures.Goldbach.ReflectedShortProgressionMean

/-!
在反射带 `B N` 上证明：以不超过 `y` 的奇素因子截断的局部模型 `P m` 逼近归一化大弧系数 `R N m` 时，
均方误差满足一致的 `O(y⁻²)` 上界（常数 `C` 独立于 `y`）。

主要思路：
1. 复用已验证社区模块 `Conjectures.Goldbach.ReflectedShortProgressionMean`（PR #4354）与
   `Conjectures.Goldbach.ReflectedMajorSharpFloor`（PR #4275）中的大弧一致性转移定理，
   将 `R N m` 归约为有限前缀和 `coefficientPrefix k m`（`k = ⌊log₂(N+2)⌋`）。
2. 引入由不超过 `y` 的所有素数连乘 `D_y` 生成的截断模型 `Q_y m = ∑_{q ∣ D_y} c(q, m)`，
   将其展开为 Euler 乘积并与 `P m` 比较，利用 `|C₂(y) - C₂| ≤ 2/y` 和 `C₂(y) ≥ 1/2`
   将 `|Q_y m - P m|` 控为 `(4/y) |Q_y m|`。
3. 对任意有限分母集 `S ⊆ [1, k]`，把 `∑_{q ∈ S} c(q, m)` 合并为奇数无平方因子分母和，
   利用中国剩余定理证明奇数无平方因子分母间的精确正交性（对角均值 `1/φ(r)³`，非对角为 `0`），
   并用步长为 `2` 的等差数列完整周期切分控制余项为 `O(k⁴ / |B N|)`。
4. 通过 `∏ (1 + 1/(p-1)³) ≤ exp(1) ≤ 3` 与裂项求和 `∑_{n ≥ y} 1/n³ ≤ 4/y²` 统一估计主项与尾项。
-/

namespace ReflectedMeanSquareEulerTail

open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc ReflectedShortProgression
open scoped BigOperators Classical Topology

noncomputable section

/-! ### 通用基础辅助引理 -/

private theorem odd_of_dvd_odd {a b : ℕ} (hb : Odd b) (hdvd : a ∣ b) : Odd a := by
  by_contra h
  exact hb.not_two_dvd_nat ((even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h)).trans hdvd)

private theorem sum_zmod_eq_sum_range {n : ℕ} [NeZero n] (f : ℕ → ℝ) :
    (∑ x : ZMod n, f x.val) = ∑ k ∈ range n, f k := by
  cases n with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ m => exact Fin.sum_univ_eq_sum_range f (m + 1)

/-! ### 第一部分：有限与无穷孪生素数常数 `C₂` 的尾估计 -/

/-- 不超过 `y` 的奇素数集合。 -/
def oddPrimesUpTo (y : ℕ) : Finset ℕ :=
  (Icc 3 y).filter Nat.Prime

/-- `C₂` 截断到 `y` 的有限乘积。 -/
def C2Prefix (y : ℕ) : ℝ :=
  ∏ p ∈ oddPrimesUpTo y, (1 - 1 / ((p : ℝ) - 1) ^ 2)

/-- 单个局部因子落在 `[0, 1]` 区间内。 -/
private theorem factor_bounds (p : ℕ) :
    0 ≤ SharpBaseLimit.factor p ∧ SharpBaseLimit.factor p ≤ 1 := by
  unfold SharpBaseLimit.factor
  split_ifs with h
  · have hp : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    have h1 : (2 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have hsq : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    constructor
    · have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hsq
      linarith
    · have : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
      linarith
  · exact ⟨by norm_num, le_rfl⟩

/-- 对任意落在 `[0, 1]` 内的有限乘积，有 `1 - ∏ f ≤ ∑ (1 - f)`。 -/
private theorem one_sub_prod_le_sum {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ x ∈ s, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ ∏ x ∈ s, f x ∧ ∏ x ∈ s, f x ≤ 1 ∧ 1 - ∏ x ∈ s, f x ≤ ∑ x ∈ s, (1 - f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hfa := hf a (mem_insert_self a s)
    obtain ⟨h0, h1, hsub⟩ := ih (fun x hx => hf x (mem_insert_of_mem hx))
    rw [prod_insert ha, sum_insert ha]
    refine ⟨mul_nonneg hfa.1 h0, ?_, ?_⟩
    · calc f a * ∏ x ∈ s, f x ≤ 1 * 1 := mul_le_mul hfa.2 h1 h0 (by norm_num)
        _ = 1 := one_mul 1
    · have hmul : f a * (1 - ∏ x ∈ s, f x) ≤ 1 * (1 - ∏ x ∈ s, f x) :=
        mul_le_mul_of_nonneg_right hfa.2 (by linarith)
      linarith

/-- 裂项上界：`∑_{n=a}^{b} 1/(n-1)² ≤ 1/(a-2)`（当 `4 ≤ a`）。 -/
private theorem sum_inv_sq_sub_one_le {a : ℕ} (ha : 4 ≤ a) :
    ∀ b : ℕ, ∑ n ∈ Icc a b, (1 : ℝ) / ((n : ℝ) - 1) ^ 2 ≤
      1 / ((a : ℝ) - 2) - if a ≤ b then 1 / ((b : ℝ) - 1) else 0 := by
  have haR : (4 : ℝ) ≤ a := by exact_mod_cast ha
  have ha2 : (0 : ℝ) < (a : ℝ) - 2 := by linarith
  have ha1 : (0 : ℝ) < (a : ℝ) - 1 := by linarith
  intro b
  induction b with
  | zero =>
    have hemp : Icc a 0 = ∅ := Icc_eq_empty (by omega)
    rw [hemp, sum_empty, ite_eq_right (by omega : ¬ a ≤ 0), sub_zero]
    positivity
  | succ b ih =>
    by_cases hlt : b + 1 < a
    · have hemp : Icc a (b + 1) = ∅ := Icc_eq_empty (by omega)
      rw [hemp, sum_empty, ite_eq_right (by omega : ¬ a ≤ b + 1), sub_zero]
      positivity
    · by_cases heq : b + 1 = a
      · rw [heq, Icc_self, sum_singleton, ite_eq_left (le_refl a)]
        rw [div_sub_div _ _ ha2.ne' ha1.ne']
        have hnum : (1 : ℝ) * ((a : ℝ) - 1) - ((a : ℝ) - 2) * 1 = 1 := by ring
        rw [hnum]
        apply one_div_le_one_div_of_le (mul_pos ha2 ha1)
        nlinarith
      · have hab : a ≤ b := by omega
        have hab1 : a ≤ b + 1 := by omega
        rw [ite_eq_left hab] at ih
        rw [ite_eq_left hab1, sum_Icc_succ_top hab1]
        have hbR : (3 : ℝ) ≤ b := by exact_mod_cast (show 3 ≤ b by omega)
        have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by linarith
        have hb0 : (0 : ℝ) < (b : ℝ) := by linarith
        have hcast : (((b + 1 : ℕ) : ℝ) - 1) = (b : ℝ) := by push_cast; ring
        have hstep : (1 : ℝ) / (b : ℝ) ^ 2 ≤ 1 / ((b : ℝ) - 1) - 1 / (b : ℝ) := by
          rw [div_sub_div _ _ hb1.ne' hb0.ne']
          have hnum : (1 : ℝ) * (b : ℝ) - ((b : ℝ) - 1) * 1 = 1 := by ring
          rw [hnum]
          apply one_div_le_one_div_of_le (mul_pos hb1 hb0)
          nlinarith
        rw [hcast]
        linarith

/-- `C2Prefix y` 等价于 `range (y + 1)` 上 `SharpBaseLimit.factor` 的乘积。 -/
private theorem C2Prefix_eq_prod_range (y : ℕ) :
    C2Prefix y = ∏ p ∈ range (y + 1), SharpBaseLimit.factor p := by
  unfold C2Prefix oddPrimesUpTo SharpBaseLimit.factor
  rw [← prod_filter]
  apply prod_congr
  · ext p
    simp only [mem_filter, mem_Icc, mem_range]
    constructor
    · rintro ⟨⟨h3, hy⟩, hp⟩
      exact ⟨by omega, hp, by omega⟩
    · rintro ⟨hy, hp, h2⟩
      exact ⟨⟨by omega, by omega⟩, hp⟩
  · intro _ _; rfl

/-- 对所有 `y ≥ 3`，截断乘积满足下界 `1/2 ≤ C2Prefix y`。 -/
theorem half_le_C2Prefix {y : ℕ} (hy : 3 ≤ y) : (1 : ℝ) / 2 ≤ C2Prefix y := by
  have h3mem : 3 ∈ oddPrimesUpTo y :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hy⟩, Nat.prime_three⟩
  unfold C2Prefix
  rw [← mul_prod_erase _ _ h3mem]
  have h3val : (1 : ℝ) - 1 / (((3 : ℕ) : ℝ) - 1) ^ 2 = 3 / 4 := by norm_num
  rw [h3val]
  let S := (oddPrimesUpTo y).erase 3
  have hSsub : S ⊆ Icc 5 y := by
    intro p hp
    have hne : p ≠ 3 := (mem_erase.mp hp).1
    have hmem := mem_filter.mp (mem_erase.mp hp).2
    have hp4 : p ≠ 4 := by
      intro h4; subst h4; exact absurd hmem.2 (by decide)
    exact mem_Icc.mpr ⟨by have := (mem_Icc.mp hmem.1).1; omega, (mem_Icc.mp hmem.1).2⟩
  have hSbnd : ∀ p ∈ S, 0 ≤ (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 ∧
      (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
    intro p hp
    have hp' := mem_filter.mp (mem_erase.mp hp).2
    have hgt : 2 < p := by have := (mem_Icc.mp hp'.1).1; omega
    simpa [SharpBaseLimit.factor, hp'.2, hgt] using factor_bounds p
  have hprod := (one_sub_prod_le_sum S (fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2) hSbnd).2.2
  have hsum : ∑ p ∈ S, (1 - (1 - 1 / ((p : ℝ) - 1) ^ 2)) ≤ 1 / 3 := by
    calc ∑ p ∈ S, (1 - (1 - 1 / ((p : ℝ) - 1) ^ 2))
        = ∑ p ∈ S, (1 : ℝ) / ((p : ℝ) - 1) ^ 2 := by
          apply sum_congr rfl; intro p _; ring
      _ ≤ ∑ n ∈ Icc 5 y, (1 : ℝ) / ((n : ℝ) - 1) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg hSsub (fun n _ _ => by positivity)
      _ ≤ 1 / ((5 : ℝ) - 2) - if 5 ≤ y then 1 / ((y : ℝ) - 1) else 0 := by
          simpa using sum_inv_sq_sub_one_le (a := 5) (by decide) y
      _ ≤ 1 / 3 := by
          split_ifs with h5
          · have hyR : (5 : ℝ) ≤ y := by exact_mod_cast h5
            have hy1 : (0 : ℝ) < (y : ℝ) - 1 := by linarith
            have : (0 : ℝ) ≤ 1 / ((y : ℝ) - 1) := by positivity
            linarith
          · norm_num
  have htail : (2 : ℝ) / 3 ≤ ∏ p ∈ S, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by linarith
  linarith

/-- 无穷乘积 `SharpBaseLimit.factor` 可乘（直接复用 `SharpBaseLimit` 中的 Euler 乘积结果）。 -/
private theorem hasProd_factor :
    HasProd SharpBaseLimit.factor (∏' p : ℕ, SharpBaseLimit.factor p) := by
  have eul := EulerProduct.eulerProduct_hasProd_mulIndicator
    SharpBaseLimit.base_one (fun {_ _} h => SharpBaseLimit.base_mul h)
    SharpBaseLimit.abs_summable SharpBaseLimit.base_zero
  have half : HasProd (fun p : ℕ => if p = 2 then (1 / 2 : ℝ) else 1) (1 / 2) := by
    simpa only [eq_comm] using (hasProd_ite_eq (2 : ℕ) (1 / 2 : ℝ))
  have product := half.mul eul
  have hlocal : ∀ p : ℕ, p.Prime →
      (∑' e : ℕ, SharpBaseLimit.base (p ^ e)) = 1 + SharpBaseLimit.base p := by
    intro p hp
    rw [tsum_eq_sum (s := {0, 1})]
    · simp [SharpBaseLimit.base_one]
    · intro e he
      have h2 : 2 ≤ e := by
        by_contra! hlt
        interval_cases e <;> simp_all
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h2
      rw [add_comm]
      simp [SharpBaseLimit.base, coefficient_higher_power hp]
  have same : (fun p : ℕ => (if p = 2 then (1 / 2 : ℝ) else 1) *
      Set.mulIndicator {p : ℕ | p.Prime} (fun p => ∑' e : ℕ, SharpBaseLimit.base (p ^ e)) p) =
      SharpBaseLimit.factor := by
    funext p
    by_cases hp : p.Prime
    · rw [Set.mulIndicator_of_mem hp, hlocal p hp]
      have hbp : SharpBaseLimit.base p = if p = 2 then 1 else -(1 / ((p : ℝ) - 1) ^ 2) := by
        unfold SharpBaseLimit.base
        rw [coefficient_prime hp, Complex.ofReal_re]
        by_cases h2 : p = 2
        · subst p; norm_num [localCoefficient]
        · have nd : ¬ p ∣ 2 := fun d =>
            h2 ((Nat.dvd_prime Nat.prime_two).mp d |>.resolve_left hp.ne_one)
          simp [localCoefficient, h2, nd]
      rw [hbp]
      by_cases h2 : p = 2
      · subst p; norm_num [SharpBaseLimit.factor]
      · have hgt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm h2)
        simp [SharpBaseLimit.factor, hp, h2, hgt, sub_eq_add_neg]
    · have h2 : p ≠ 2 := by rintro rfl; exact hp Nat.prime_two
      rw [Set.mulIndicator_of_notMem hp]
      simp [SharpBaseLimit.factor, hp, h2]
  change HasProd (fun p : ℕ => (if p = 2 then (1 / 2 : ℝ) else 1) *
      Set.mulIndicator {p : ℕ | p.Prime} (fun p => ∑' e : ℕ, SharpBaseLimit.base (p ^ e)) p) _
      at product
  rw [same] at product
  rwa [product.tprod_eq]

/-- 截断误差上界：对所有 `y ≥ 3`，`|C2Prefix y - C₂| ≤ 2 / y`。 -/
theorem abs_C2Prefix_sub_C2_le {y : ℕ} (hy : 3 ≤ y) :
    |C2Prefix y - ∏' p : ℕ, SharpBaseLimit.factor p| ≤ 2 / (y : ℝ) := by
  let C₂ := ∏' p : ℕ, SharpBaseLimit.factor p
  have htend : Tendsto (fun M : ℕ => ∏ p ∈ range (M + 1), SharpBaseLimit.factor p)
      atTop (𝓝 C₂) := by
    have hrange : Tendsto (fun M : ℕ => range (M + 1)) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro s
      refine ⟨s.sup id, fun M hM => ?_⟩
      intro x hx
      rw [mem_range]
      have hle : x ≤ s.sup id := le_sup (f := id) hx
      omega
    exact hasProd_factor.comp hrange
  have hdiff_tend : Tendsto (fun M : ℕ => C2Prefix y - ∏ p ∈ range (M + 1), SharpBaseLimit.factor p)
      atTop (𝓝 (C2Prefix y - C₂)) :=
    tendsto_const_nhds.sub htend
  have hge0 : ∀ᶠ M : ℕ in atTop, 0 ≤ C2Prefix y - ∏ p ∈ range (M + 1), SharpBaseLimit.factor p := by
    filter_upwards [eventually_ge_atTop y] with M hM
    have hdisj : Disjoint (range (y + 1)) (Icc (y + 1) M) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [mem_range] at hp1; rw [mem_Icc] at hp2; omega
    have hunion : range (M + 1) = range (y + 1) ∪ Icc (y + 1) M := by
      ext p; simp only [mem_union, mem_range, mem_Icc]; omega
    rw [C2Prefix_eq_prod_range y, hunion, prod_union hdisj]
    have hP := one_sub_prod_le_sum (range (y + 1)) SharpBaseLimit.factor (fun p _ => factor_bounds p)
    have hT := one_sub_prod_le_sum (Icc (y + 1) M) SharpBaseLimit.factor (fun p _ => factor_bounds p)
    have : (∏ p ∈ range (y + 1), SharpBaseLimit.factor p) *
        (∏ p ∈ Icc (y + 1) M, SharpBaseLimit.factor p) ≤
        (∏ p ∈ range (y + 1), SharpBaseLimit.factor p) * 1 :=
      mul_le_mul_of_nonneg_left hT.2.1 hP.1
    linarith
  have hle2 : ∀ᶠ M : ℕ in atTop,
      C2Prefix y - ∏ p ∈ range (M + 1), SharpBaseLimit.factor p ≤ 2 / (y : ℝ) := by
    filter_upwards [eventually_ge_atTop y] with M hM
    have hdisj : Disjoint (range (y + 1)) (Icc (y + 1) M) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rw [mem_range] at hp1; rw [mem_Icc] at hp2; omega
    have hunion : range (M + 1) = range (y + 1) ∪ Icc (y + 1) M := by
      ext p; simp only [mem_union, mem_range, mem_Icc]; omega
    rw [C2Prefix_eq_prod_range y, hunion, prod_union hdisj]
    have hP := one_sub_prod_le_sum (range (y + 1)) SharpBaseLimit.factor (fun p _ => factor_bounds p)
    have hT := one_sub_prod_le_sum (Icc (y + 1) M) SharpBaseLimit.factor (fun p _ => factor_bounds p)
    have h1 : (∏ p ∈ range (y + 1), SharpBaseLimit.factor p) -
        (∏ p ∈ range (y + 1), SharpBaseLimit.factor p) *
          (∏ p ∈ Icc (y + 1) M, SharpBaseLimit.factor p) =
        (∏ p ∈ range (y + 1), SharpBaseLimit.factor p) *
          (1 - ∏ p ∈ Icc (y + 1) M, SharpBaseLimit.factor p) := by ring
    rw [h1]
    have h2 : (∏ p ∈ range (y + 1), SharpBaseLimit.factor p) *
        (1 - ∏ p ∈ Icc (y + 1) M, SharpBaseLimit.factor p) ≤
        1 * (∑ p ∈ Icc (y + 1) M, (1 - SharpBaseLimit.factor p)) :=
      mul_le_mul hP.2.1 hT.2.2 (by linarith [hT.2.1]) (by norm_num)
    have h3 : ∑ p ∈ Icc (y + 1) M, (1 - SharpBaseLimit.factor p) ≤
        ∑ n ∈ Icc (y + 1) M, (1 : ℝ) / ((n : ℝ) - 1) ^ 2 := by
      apply sum_le_sum
      intro p _
      unfold SharpBaseLimit.factor
      split_ifs
      · linarith
      · rw [sub_self]; positivity
    have h4 := sum_inv_sq_sub_one_le (a := y + 1) (by omega) M
    have h5 : 1 / (((y + 1 : ℕ) : ℝ) - 2) -
        (if y + 1 ≤ M then 1 / ((M : ℝ) - 1) else 0) ≤ 2 / (y : ℝ) := by
      have hyR : (3 : ℝ) ≤ y := by exact_mod_cast hy
      have hsub : ((y + 1 : ℕ) : ℝ) - 2 = (y : ℝ) - 1 := by push_cast; ring
      rw [hsub]
      have htail0 : 0 ≤ if y + 1 ≤ M then (1 : ℝ) / ((M : ℝ) - 1) else 0 := by
        split_ifs with hlt
        · have hMR : (4 : ℝ) ≤ M := by exact_mod_cast (show 4 ≤ M by omega)
          have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
          positivity
        · exact le_rfl
      have hcmp : (1 : ℝ) / ((y : ℝ) - 1) ≤ 2 / (y : ℝ) := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        linarith
      linarith
    linarith
  have hnonneg : 0 ≤ C2Prefix y - C₂ := ge_of_tendsto hdiff_tend hge0
  have hupper : C2Prefix y - C₂ ≤ 2 / (y : ℝ) := le_of_tendsto hdiff_tend hle2
  rw [abs_of_nonneg hnonneg]
  exact hupper

/-! ### 第二部分：素数连乘截断模型 `Q_y` 与目标模型 `P_y` 的关系 -/

/-- 不超过 `y` 的所有素数的连乘 `D_y`。 -/
def primorial (y : ℕ) : ℕ :=
  ∏ p ∈ (Icc 2 y).filter Nat.Prime, p

private theorem primorial_pos (y : ℕ) : 0 < primorial y := by
  unfold primorial
  exact prod_pos (fun p hp => (mem_filter.mp hp).2.pos)

private theorem prime_dvd_finset_prod {q : ℕ} (hq : q.Prime) (s : Finset ℕ)
    (hdvd : q ∣ ∏ p ∈ s, p) : ∃ p ∈ s, q ∣ p := by
  induction s using Finset.induction_on with
  | empty =>
    rw [prod_empty] at hdvd
    exact absurd hdvd hq.not_dvd_one
  | @insert a s ha ih =>
    rw [prod_insert ha] at hdvd
    rcases hq.dvd_mul.mp hdvd with h1 | h2
    · exact ⟨a, mem_insert_self a s, h1⟩
    · obtain ⟨p, hp, hqp⟩ := ih h2
      exact ⟨p, mem_insert_of_mem hp, hqp⟩

private theorem primeFactors_primorial (y : ℕ) :
    (primorial y).primeFactors = (Icc 2 y).filter Nat.Prime := by
  ext q
  simp only [Nat.mem_primeFactors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hq, hdvd, _⟩
    unfold primorial at hdvd
    obtain ⟨p, hp, hqp⟩ := prime_dvd_finset_prod hq _ hdvd
    have hp' := mem_filter.mp hp
    have heq : q = p := (Nat.dvd_prime hp'.2).mp hqp |>.resolve_left hq.ne_one
    subst heq
    exact ⟨mem_Icc.mp hp'.1, hp'.2⟩
  · rintro ⟨⟨h2, hy⟩, hq⟩
    refine ⟨hq, ?_, (primorial_pos y).ne'⟩
    exact dvd_prod_of_mem _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨h2, hy⟩, hq⟩)

/-- 由 `D_y` 的全部约数构成的有限截断和 `Q_y(m)`。 -/
def QModel (y m : ℕ) : ℝ :=
  ∑ q ∈ (primorial y).divisors, (coefficient q m).re

/-- `Q_y(m)` 的精确 Euler 乘积展开。 -/
theorem QModel_eq_euler {y m : ℕ} (hy : 3 ≤ y) (hm0 : 0 < m) (hm : Even m) :
    QModel y m = 2 * C2Prefix y *
      ∏ p ∈ m.primeFactors.filter (fun p => 2 < p ∧ p ≤ y), (1 + 1 / ((p : ℝ) - 2)) := by
  unfold QModel
  rw [sum_divisors_coefficient_eq_euler m (primorial_pos y).ne', primeFactors_primorial]
  have hsplit : (Icc 2 y).filter Nat.Prime = insert 2 (oddPrimesUpTo y) := by
    ext p
    simp only [mem_insert, mem_filter, mem_Icc, oddPrimesUpTo]
    constructor
    · rintro ⟨⟨h2, hy'⟩, hp⟩
      by_cases h : p = 2
      · left; exact h
      · right; exact ⟨⟨by omega, hy'⟩, hp⟩
    · rintro (rfl | ⟨⟨h3, hy'⟩, hp⟩)
      · exact ⟨⟨le_rfl, by omega⟩, Nat.prime_two⟩
      · exact ⟨⟨by omega, hy'⟩, hp⟩
  have h2not : 2 ∉ oddPrimesUpTo y := by
    simp [oddPrimesUpTo]
  rw [hsplit, prod_insert h2not]
  have hloc2 : 1 + localCoefficient 2 m = 2 := by
    norm_num [localCoefficient, even_iff_two_dvd.mp hm]
  rw [hloc2]
  have hfactor : ∀ p ∈ oddPrimesUpTo y,
      1 + localCoefficient p m =
        (1 - 1 / ((p : ℝ) - 1) ^ 2) * (if p ∣ m then 1 + 1 / ((p : ℝ) - 2) else 1) := by
    intro p hp
    have hmem := mem_filter.mp hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (mem_Icc.mp hmem.1).1
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
    unfold localCoefficient
    by_cases hdvd : p ∣ m
    · rw [ite_eq_left hdvd, ite_eq_left hdvd]
      field_simp [h1, h2]
      ring
    · rw [ite_eq_right hdvd, ite_eq_right hdvd]
      ring
  rw [prod_congr rfl hfactor, prod_mul_distrib]
  change 2 * (C2Prefix y * ∏ p ∈ oddPrimesUpTo y, if p ∣ m then 1 + 1 / ((p : ℝ) - 2) else 1) = _
  rw [← mul_assoc]
  congr 1
  rw [← prod_filter]
  apply prod_congr
  · ext p
    simp only [mem_filter, oddPrimesUpTo, mem_Icc, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨⟨h3, hy'⟩, hp⟩, hdvd⟩
      exact ⟨⟨hp, hdvd, hm0.ne'⟩, by omega, hy'⟩
    · rintro ⟨⟨hp, hdvd, _⟩, h2, hy'⟩
      exact ⟨⟨⟨by omega, hy'⟩, hp⟩, hdvd⟩
  · intro _ _; rfl

/-- `Q_y(m)` 与目标模型 `P_y(m)` 的平方差上界。 -/
theorem QModel_sub_target_sq_le {y m : ℕ} (hy : 3 ≤ y) (hm0 : 0 < m) (hm : Even m) :
    let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1
    let P := 2 * C₂ * ∏ p ∈ m.primeFactors.filter (fun p => 2 < p ∧ p ≤ y), (1 + 1 / ((p : ℝ) - 2))
    (QModel y m - P) ^ 2 ≤ (16 / (y : ℝ) ^ 2) * (QModel y m) ^ 2 := by
  intro C₂ P
  let F := ∏ p ∈ m.primeFactors.filter (fun p => 2 < p ∧ p ≤ y), (1 + 1 / ((p : ℝ) - 2))
  have hQ : QModel y m = 2 * C2Prefix y * F := QModel_eq_euler hy hm0 hm
  have hP : P = 2 * C₂ * F := rfl
  have hF0 : 0 ≤ F := by
    apply prod_nonneg
    intro p hp
    have h2 : 2 < p := (mem_filter.mp hp).2.1
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
    have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
    positivity
  have hC2half : (1 : ℝ) / 2 ≤ C2Prefix y := half_le_C2Prefix hy
  have hdiff : |C2Prefix y - C₂| ≤ 2 / (y : ℝ) := abs_C2Prefix_sub_C2_le hy
  have habs : |QModel y m - P| ≤ (4 / (y : ℝ)) * QModel y m := by
    rw [hQ, hP, show 2 * C2Prefix y * F - 2 * C₂ * F = (C2Prefix y - C₂) * (2 * F) by ring,
      abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * F)]
    have h2F : 2 * F ≤ 2 * (2 * C2Prefix y * F) := by nlinarith
    have hy0 : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
    calc |C2Prefix y - C₂| * (2 * F)
        ≤ (2 / (y : ℝ)) * (2 * F) := mul_le_mul_of_nonneg_right hdiff (by positivity)
      _ ≤ (2 / (y : ℝ)) * (2 * (2 * C2Prefix y * F)) :=
          mul_le_mul_of_nonneg_left h2F (by positivity)
      _ = (4 / (y : ℝ)) * (2 * C2Prefix y * F) := by ring
  have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs, mul_pow] at hsq
  calc (QModel y m - P) ^ 2 ≤ (4 / (y : ℝ)) ^ 2 * (QModel y m) ^ 2 := hsq
    _ = (16 / (y : ℝ) ^ 2) * (QModel y m) ^ 2 := by ring

/-! ### 第三部分：实系数 `c(q, m)` 的无平方因子化简与乘性展开 -/

/-- 大弧奇异级数单分母实系数。 -/
def cCoeff (q m : ℕ) : ℝ :=
  (coefficient q m).re

private theorem cCoeff_one (m : ℕ) : cCoeff 1 m = 1 := by
  simp [cCoeff, coefficient_one]

private theorem cCoeff_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hcop : a.Coprime b) (m : ℕ) :
    cCoeff (a * b) m = cCoeff a m * cCoeff b m := by
  simp [cCoeff, coefficient_mul ha hb hcop, Complex.mul_re, coefficient_im_zero m ha,
    coefficient_im_zero m hb]

private theorem cCoeff_prime {p : ℕ} (hp : p.Prime) (m : ℕ) :
    cCoeff p m = localCoefficient p m := by
  simp [cCoeff, coefficient_prime hp]

private theorem cCoeff_eq_zero_of_not_squarefree {q : ℕ} (hq : 0 < q) (hns : ¬ Squarefree q)
    (m : ℕ) : cCoeff q m = 0 := by
  rw [Nat.squarefree_iff_prime_squarefree] at hns
  push Not at hns
  obtain ⟨p, hp, hpp⟩ := hns
  have hpe : 2 ≤ q.factorization p := by
    have hpow : p ^ 2 ∣ q := by simpa [sq] using hpp
    exact (hp.pow_dvd_iff_le_factorization hq.ne').mp hpow
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hpe
  let a := p ^ q.factorization p
  let b := q / a
  have ha0 : 0 < a := pow_pos hp.pos _
  have hab : a * b = q := Nat.ordProj_mul_ordCompl_eq_self q p
  have hb0 : 0 < b := by
    by_contra! hb
    have hb' : b = 0 := Nat.eq_zero_of_le_zero hb
    rw [hb', mul_zero] at hab
    exact hq.ne' hab.symm
  have hcop : a.Coprime b := (Nat.coprime_ordCompl hp hq.ne').pow_left _
  rw [← hab, cCoeff_mul ha0 hb0 hcop]
  have hzero : cCoeff a m = 0 := by
    dsimp only [a]
    rw [hk, add_comm, cCoeff, coefficient_higher_power hp k m, Complex.zero_re]
  rw [hzero, zero_mul]

private theorem cCoeff_two_mul_of_even {r m : ℕ} (hr : Odd r) (hm : Even m) :
    cCoeff (2 * r) m = cCoeff r m := by
  have hr0 : 0 < r := by have := Nat.odd_iff.mp hr; omega
  have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hr
  rw [cCoeff_mul (by decide) hr0 hcop, cCoeff_prime Nat.prime_two]
  have hloc : localCoefficient 2 m = 1 := by
    norm_num [localCoefficient, even_iff_two_dvd.mp hm]
  rw [hloc, one_mul]

private theorem cCoeff_eq_prod_primeFactors {r : ℕ} (hr0 : 0 < r) (hsf : Squarefree r) (m : ℕ) :
    cCoeff r m = ∏ p ∈ r.primeFactors, localCoefficient p m := by
  induction r using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => simp [cCoeff_one]
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero =>
        rw [pow_one, cCoeff_prime hp, hp.primeFactors, prod_singleton]
      | succ k =>
        exfalso
        have hsq : p * p ∣ p ^ (k + 2) := by
          rw [show p ^ (k + 2) = p * p * p ^ k by ring]
          exact dvd_mul_right _ _
        exact (Nat.squarefree_iff_prime_squarefree.mp hsf p hp) hsq
  | coprime a b ha hb hcop iha ihb =>
    have ha0 : 0 < a := by omega
    have hb0 : 0 < b := by omega
    have hsf_a : Squarefree a := hsf.squarefree_of_dvd (dvd_mul_right a b)
    have hsf_b : Squarefree b := hsf.squarefree_of_dvd (dvd_mul_left b a)
    have hdisj : Disjoint a.primeFactors b.primeFactors := by
      rw [Finset.disjoint_left]
      intro p hpa hpb
      have hpa' := Nat.mem_primeFactors.mp hpa
      have hpb' := Nat.mem_primeFactors.mp hpb
      have hdvd : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa'.2.1 hpb'.2.1
      rw [hcop.gcd_eq_one] at hdvd
      exact hpa'.1.not_dvd_one hdvd
    rw [cCoeff_mul ha0 hb0 hcop, Nat.primeFactors_mul ha0.ne' hb0.ne',
      prod_union hdisj, iha ha0 hsf_a, ihb hb0 hsf_b]

private theorem abs_localCoefficient_le_one {p : ℕ} (hp : p.Prime) (m : ℕ) :
    |localCoefficient p m| ≤ 1 := by
  unfold localCoefficient
  by_cases h2 : p = 2
  · subst p; split_ifs <;> norm_num
  · have hp3 : (3 : ℝ) ≤ p := by
      have := hp.two_le
      exact_mod_cast (show 3 ≤ p by omega)
    have h1 : (2 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    split_ifs
    · rw [abs_of_nonneg (by positivity)]
      exact (div_le_one (by linarith)).mpr (by linarith)
    · rw [abs_neg, abs_of_nonneg (by positivity)]
      have hsq : (4 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
      exact (div_le_one (by linarith)).mpr (by linarith)

private theorem abs_cCoeff_le_one {r : ℕ} (hr0 : 0 < r) (hsf : Squarefree r) (m : ℕ) :
    |cCoeff r m| ≤ 1 := by
  rw [cCoeff_eq_prod_primeFactors hr0 hsf, abs_prod]
  exact (one_sub_prod_le_sum r.primeFactors (fun p => |localCoefficient p m|)
    (fun p hp => ⟨abs_nonneg _, abs_localCoefficient_le_one (Nat.mem_primeFactors.mp hp).1 m⟩)).2.1

private theorem cCoeff_mod_eq {r m₁ m₂ : ℕ} (hr0 : 0 < r) (hsf : Squarefree r)
    (hmod : m₁ % r = m₂ % r) : cCoeff r m₁ = cCoeff r m₂ := by
  rw [cCoeff_eq_prod_primeFactors hr0 hsf, cCoeff_eq_prod_primeFactors hr0 hsf]
  apply prod_congr rfl
  intro p hp
  have hpr : p ∣ r := (Nat.mem_primeFactors.mp hp).2.1
  have hiff : p ∣ m₁ ↔ p ∣ m₂ := by
    rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero,
      ← Nat.mod_mod_of_dvd m₁ hpr, ← Nat.mod_mod_of_dvd m₂ hpr, hmod]
  simp [localCoefficient, hiff]

/-! ### 第四部分：中国剩余定理下的精确正交性 -/

/-- 对两两互素的素数集合 `S`，按模 `∏ p ∈ S, p` 求和可完全分解为各素模之和的乘积。 -/
private theorem sum_zmod_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (f : ℕ → ℕ → ℝ) (hmod : ∀ p ∈ S, ∀ x y : ℕ, x % p = y % p → f p x = f p y) :
    ∑ x ∈ range (∏ p ∈ S, p), (∏ p ∈ S, f p x) =
      ∏ p ∈ S, ∑ u ∈ range p, f p u := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    have hprime : p.Prime := hS p (mem_insert_self p s)
    have hrest : ∀ q ∈ s, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    let M := ∏ q ∈ s, q
    have hM0 : 0 < M := prod_pos (fun q hq => (hrest q hq).pos)
    have hp0 : 0 < p := hprime.pos
    have hcop : Nat.Coprime p M := by
      refine Nat.Coprime.prod_right (fun q hq => ?_)
      exact (Nat.coprime_primes hprime (hrest q hq)).mpr (fun h => hp (h ▸ hq))
    have : NeZero p := ⟨hp0.ne'⟩
    have : NeZero M := ⟨hM0.ne'⟩
    have : NeZero (p * M) := ⟨(Nat.mul_pos hp0 hM0).ne'⟩
    rw [prod_insert hp, prod_insert hp]
    let e := ZMod.chineseRemainder hcop
    let g₁ : ZMod p → ℝ := fun u => f p u.val
    let g₂ : ZMod M → ℝ := fun v => ∏ q ∈ s, f q v.val
    have he1 : ∀ x : ZMod (p * M), (e x).1 = (x.val : ZMod p) := by
      intro x
      have hcast : e (x.val : ZMod (p * M)) = ((x.val : ZMod p), (x.val : ZMod M)) := by
        rw [map_natCast]; rfl
      rw [ZMod.natCast_zmod_val] at hcast
      exact congrArg Prod.fst hcast
    have he2 : ∀ x : ZMod (p * M), (e x).2 = (x.val : ZMod M) := by
      intro x
      have hcast : e (x.val : ZMod (p * M)) = ((x.val : ZMod p), (x.val : ZMod M)) := by
        rw [map_natCast]; rfl
      rw [ZMod.natCast_zmod_val] at hcast
      exact congrArg Prod.snd hcast
    have hL : (∑ x ∈ range (p * M), ∏ q ∈ insert p s, f q x) =
        ∑ x : ZMod (p * M), g₁ (e x).1 * g₂ (e x).2 := by
      rw [← sum_zmod_eq_sum_range (n := p * M)]
      apply sum_congr rfl
      intro x _
      rw [prod_insert hp]
      congr 1
      · dsimp only [g₁]
        apply hmod p (mem_insert_self p s)
        rw [he1 x, ZMod.val_natCast, Nat.mod_mod]
      · dsimp only [g₂]
        apply prod_congr rfl
        intro q hq
        have hqM : q ∣ M := dvd_prod_of_mem _ hq
        apply hmod q (mem_insert_of_mem hq)
        rw [he2 x, ZMod.val_natCast, Nat.mod_mod_of_dvd _ hqM]
    rw [hL]
    have hCRT : (∑ x : ZMod (p * M), g₁ (e x).1 * g₂ (e x).2) =
        ∑ z : ZMod p × ZMod M, g₁ z.1 * g₂ z.2 :=
      Equiv.sum_comp e.toEquiv (fun z : ZMod p × ZMod M => g₁ z.1 * g₂ z.2)
    rw [hCRT, Fintype.sum_prod_type, ← Fintype.sum_mul_sum]
    dsimp only [g₁, g₂]
    rw [sum_zmod_eq_sum_range (n := p),
      sum_zmod_eq_sum_range (n := M) (f := fun v => ∏ q ∈ s, f q v)]
    rw [← ih hrest (fun q hq => hmod q (mem_insert_of_mem hq))]

/-- 单个奇素数处一次局部系数之和为零。 -/
private theorem sum_localCoefficient_zero {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∑ u ∈ range p, localCoefficient p u = 0 := by
  have hp0 : 0 < p := hp.pos
  have h0mem : 0 ∈ range p := mem_range.mpr hp0
  rw [← add_sum_erase _ _ h0mem]
  have h0 : localCoefficient p 0 = 1 / ((p : ℝ) - 1) := by
    simp [localCoefficient]
  have hrest : ∀ u ∈ (range p).erase 0, localCoefficient p u = -(1 / ((p : ℝ) - 1) ^ 2) := by
    intro u hu
    have hu0 : u ≠ 0 := (mem_erase.mp hu).1
    have hult : u < p := mem_range.mp (mem_erase.mp hu).2
    have hnd : ¬ p ∣ u := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hu0) hult
    simp [localCoefficient, hnd]
  rw [h0, sum_congr rfl hrest, sum_const, card_erase_of_mem h0mem, card_range, nsmul_eq_mul]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  field_simp [h1]
  ring

/-- 单个奇素数处局部系数平方和为 `p / (p - 1)³`。 -/
private theorem sum_localCoefficient_sq {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    ∑ u ∈ range p, (localCoefficient p u) ^ 2 = (p : ℝ) / ((p : ℝ) - 1) ^ 3 := by
  have hp0 : 0 < p := hp.pos
  have h0mem : 0 ∈ range p := mem_range.mpr hp0
  rw [← add_sum_erase _ _ h0mem]
  have h0 : (localCoefficient p 0) ^ 2 = 1 / ((p : ℝ) - 1) ^ 2 := by
    simp [localCoefficient]
  have hrest : ∀ u ∈ (range p).erase 0,
      (localCoefficient p u) ^ 2 = 1 / ((p : ℝ) - 1) ^ 4 := by
    intro u hu
    have hu0 : u ≠ 0 := (mem_erase.mp hu).1
    have hult : u < p := mem_range.mp (mem_erase.mp hu).2
    have hnd : ¬ p ∣ u := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hu0) hult
    simp only [localCoefficient, ite_eq_right hnd, neg_sq, div_pow, one_pow]
    ring
  rw [h0, sum_congr rfl hrest, sum_const, card_erase_of_mem h0mem, card_range, nsmul_eq_mul]
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [Nat.cast_sub hp.one_le, Nat.cast_one]
  field_simp [h1]
  ring

/-- 两个奇数无平方因子分母在最小公倍数周期上的精确内积。 -/
theorem sum_cCoeff_mul_lcm {r₁ r₂ : ℕ} (ho₁ : Odd r₁) (hsf₁ : Squarefree r₁)
    (ho₂ : Odd r₂) (hsf₂ : Squarefree r₂) :
    let M := Nat.lcm r₁ r₂
    ∑ x ∈ range M, cCoeff r₁ x * cCoeff r₂ x =
      if r₁ = r₂ then (M : ℝ) / (r₁.totient : ℝ) ^ 3 else 0 := by
  intro M
  have hr₁0 : 0 < r₁ := by have := Nat.odd_iff.mp ho₁; omega
  have hr₂0 : 0 < r₂ := by have := Nat.odd_iff.mp ho₂; omega
  have hM0 : 0 < M := Nat.lcm_pos hr₁0 hr₂0
  have hMsf : Squarefree M := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpp
    have hdvd : p ^ 2 ∣ M := by simpa [sq] using hpp
    have hor : p ^ 2 ∣ r₁ ∨ p ^ 2 ∣ r₂ := by
      have hfac := (hp.pow_dvd_iff_le_factorization hM0.ne').mp hdvd
      rw [Nat.factorization_lcm hr₁0.ne' hr₂0.ne', Finsupp.sup_apply] at hfac
      rcases le_sup_iff.mp hfac with h1 | h2
      · left; exact (hp.pow_dvd_iff_le_factorization hr₁0.ne').mpr h1
      · right; exact (hp.pow_dvd_iff_le_factorization hr₂0.ne').mpr h2
    rcases hor with h1 | h2
    · exact Nat.squarefree_iff_prime_squarefree.mp hsf₁ p hp (by simpa [sq] using h1)
    · exact Nat.squarefree_iff_prime_squarefree.mp hsf₂ p hp (by simpa [sq] using h2)
  have hMprod : ∏ p ∈ M.primeFactors, p = M := Nat.prod_primeFactors_of_squarefree hMsf
  have hPeq : M.primeFactors = r₁.primeFactors ∪ r₂.primeFactors := by
    ext p
    simp only [mem_union, Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hdvd, _⟩
      rcases hp.dvd_mul.mp (hdvd.trans (Nat.lcm_dvd_mul r₁ r₂)) with h1 | h2
      · left; exact ⟨hp, h1, hr₁0.ne'⟩
      · right; exact ⟨hp, h2, hr₂0.ne'⟩
    · rintro (⟨hp, h1, _⟩ | ⟨hp, h2, _⟩)
      · exact ⟨hp, h1.trans (Nat.dvd_lcm_left r₁ r₂), hM0.ne'⟩
      · exact ⟨hp, h2.trans (Nat.dvd_lcm_right r₁ r₂), hM0.ne'⟩
  have hPprimes : ∀ p ∈ M.primeFactors, p.Prime := fun p hp => (Nat.mem_primeFactors.mp hp).1
  have hPodd : ∀ p ∈ M.primeFactors, 3 ≤ p := by
    intro p hp
    have hpr := (Nat.mem_primeFactors.mp hp).1
    have h2ne : p ≠ 2 := by
      intro h2; subst h2
      rw [hPeq, mem_union] at hp
      rcases hp with h1 | h2
      · exact ho₁.not_two_dvd_nat (Nat.mem_primeFactors.mp h1).2.1
      · exact ho₂.not_two_dvd_nat (Nat.mem_primeFactors.mp h2).2.1
    have := hpr.two_le; omega
  let f : ℕ → ℕ → ℝ := fun p x =>
    (if p ∣ r₁ then localCoefficient p x else 1) *
    (if p ∣ r₂ then localCoefficient p x else 1)
  have hfmod : ∀ p ∈ M.primeFactors, ∀ x y : ℕ, x % p = y % p → f p x = f p y := by
    intro p _ x y hxy
    have hiff : p ∣ x ↔ p ∣ y := by rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, hxy]
    simp [f, localCoefficient, hiff]
  have hrew : ∀ x : ℕ, cCoeff r₁ x * cCoeff r₂ x = ∏ p ∈ M.primeFactors, f p x := by
    intro x
    rw [cCoeff_eq_prod_primeFactors hr₁0 hsf₁, cCoeff_eq_prod_primeFactors hr₂0 hsf₂]
    dsimp only [f]
    rw [prod_mul_distrib]
    congr 1
    · rw [← prod_filter]
      apply prod_congr
      · ext p
        simp only [mem_filter, hPeq, mem_union, Nat.mem_primeFactors]
        constructor
        · rintro ⟨hp, hdvd, _⟩; exact ⟨Or.inl ⟨hp, hdvd, hr₁0.ne'⟩, hdvd⟩
        · rintro ⟨h1 | h2, hdvd⟩
          · exact h1
          · exact ⟨h2.1, hdvd, hr₁0.ne'⟩
      · intro _ _; rfl
    · rw [← prod_filter]
      apply prod_congr
      · ext p
        simp only [mem_filter, hPeq, mem_union, Nat.mem_primeFactors]
        constructor
        · rintro ⟨hp, hdvd, _⟩; exact ⟨Or.inr ⟨hp, hdvd, hr₂0.ne'⟩, hdvd⟩
        · rintro ⟨h1 | h2, hdvd⟩
          · exact ⟨h1.1, hdvd, hr₂0.ne'⟩
          · exact h2
      · intro _ _; rfl
  simp_rw [hrew]
  have hcrt := sum_zmod_prod_primes M.primeFactors hPprimes f hfmod
  rw [hMprod] at hcrt
  rw [hcrt]
  by_cases heq : r₁ = r₂
  · subst r₂
    rw [ite_eq_left rfl]
    have hMr : M = r₁ := Nat.lcm_self r₁
    have hMprod' : ∏ p ∈ r₁.primeFactors, (p : ℝ) = (r₁ : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf₁]
    have htot : (r₁.totient : ℝ) = ∏ p ∈ r₁.primeFactors, ((p : ℝ) - 1) := by
      have hid := Nat.totient_mul_prod_primeFactors r₁
      have hcast : (r₁.totient : ℝ) * ∏ p ∈ r₁.primeFactors, (p : ℝ) =
          (r₁ : ℝ) * ∏ p ∈ r₁.primeFactors, ((p : ℝ) - 1) := by
        have h0 := congrArg (fun n : ℕ => (n : ℝ)) hid
        simp only [Nat.cast_mul, Nat.cast_prod] at h0
        rw [h0]
        congr 1
        apply prod_congr rfl
        intro p hp
        rw [Nat.cast_sub (Nat.mem_primeFactors.mp hp).1.one_le, Nat.cast_one]
      rw [hMprod'] at hcast
      have hr1R : (r₁ : ℝ) ≠ 0 := by exact_mod_cast hr₁0.ne'
      exact mul_left_cancel₀ hr1R (by linarith)
    have hterm : ∀ p ∈ M.primeFactors,
        (∑ u ∈ range p, f p u) = (p : ℝ) / ((p : ℝ) - 1) ^ 3 := by
      intro p hp
      have hdvd : p ∣ r₁ := by
        rw [hMr] at hp; exact (Nat.mem_primeFactors.mp hp).2.1
      have hsimp : ∀ u, f p u = (localCoefficient p u) ^ 2 := by
        intro u; simp [f, hdvd, sq]
      simp_rw [hsimp]
      exact sum_localCoefficient_sq (hPprimes p hp) (hPodd p hp)
    rw [prod_congr rfl hterm, prod_div_distrib, hMr, hMprod', htot, prod_pow]
  · rw [ite_eq_right heq]
    have hPne : r₁.primeFactors ≠ r₂.primeFactors := by
      intro h
      have h1 := Nat.prod_primeFactors_of_squarefree hsf₁
      have h2 := Nat.prod_primeFactors_of_squarefree hsf₂
      rw [h] at h1
      exact heq (h1.symm.trans h2)
    have hex : ∃ p ∈ M.primeFactors, (p ∣ r₁ ∧ ¬ p ∣ r₂) ∨ (¬ p ∣ r₁ ∧ p ∣ r₂) := by
      by_contra hnone
      push Not at hnone
      apply hPne
      ext p
      simp only [Nat.mem_primeFactors]
      constructor
      · rintro ⟨hp, h1, _⟩
        have hpm : p ∈ M.primeFactors := by
          rw [hPeq, mem_union]; left; exact Nat.mem_primeFactors.mpr ⟨hp, h1, hr₁0.ne'⟩
        exact ⟨hp, (hnone p hpm).1 h1, hr₂0.ne'⟩
      · rintro ⟨hp, h2, _⟩
        have hpm : p ∈ M.primeFactors := by
          rw [hPeq, mem_union]; right; exact Nat.mem_primeFactors.mpr ⟨hp, h2, hr₂0.ne'⟩
        by_contra h1
        have hnd1 : ¬ p ∣ r₁ := fun hd => h1 ⟨hp, hd, hr₁0.ne'⟩
        exact (hnone p hpm).2 hnd1 h2
    obtain ⟨p, hpM, hcase⟩ := hex
    apply prod_eq_zero hpM
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hsimp : ∀ u, f p u = localCoefficient p u := by intro u; simp [f, h1, h2]
      simp_rw [hsimp]
      exact sum_localCoefficient_zero (hPprimes p hpM) (hPodd p hpM)
    · have hsimp : ∀ u, f p u = localCoefficient p u := by intro u; simp [f, h1, h2]
      simp_rw [hsimp]
      exact sum_localCoefficient_zero (hPprimes p hpM) (hPodd p hpM)

/-! ### 第五部分：步长为 `2` 的等差数列完整周期平均误差 -/

/-- 对任意奇数周期 `M` 的周期函数，沿步长为 `2` 的等差数列取连续 `M` 项恰遍历全部剩余类。 -/
private theorem sum_step_two_block {M : ℕ} (hM : Odd M) (g : ℕ → ℝ)
    (hper : ∀ x y : ℕ, x % M = y % M → g x = g y) (b s : ℕ) :
    ∑ j ∈ range M, g (b + 2 * (s + j)) = ∑ x ∈ range M, g x := by
  have hM0 : 0 < M := by have := Nat.odd_iff.mp hM; omega
  have : NeZero M := ⟨hM0.ne'⟩
  have hcop : Nat.Coprime 2 M := Nat.coprime_two_left.mpr hM
  let u2 : (ZMod M)ˣ := ZMod.unitOfCoprime 2 hcop
  let c0 : ZMod M := ((b + 2 * s : ℕ) : ZMod M)
  let ψ : ZMod M ≃ ZMod M := {
    toFun := fun t => c0 + (u2 : ZMod M) * t
    invFun := fun t => ((u2⁻¹ : (ZMod M)ˣ) : ZMod M) * (t - c0)
    left_inv := fun t => by
      have hinv : ((u2⁻¹ : (ZMod M)ˣ) : ZMod M) * (u2 : ZMod M) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      calc ((u2⁻¹ : (ZMod M)ˣ) : ZMod M) * (c0 + (u2 : ZMod M) * t - c0)
          = (((u2⁻¹ : (ZMod M)ˣ) : ZMod M) * (u2 : ZMod M)) * t := by ring
        _ = t := by rw [hinv, one_mul]
    right_inv := fun t => by
      have hinv : (u2 : ZMod M) * ((u2⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc c0 + (u2 : ZMod M) * (((u2⁻¹ : (ZMod M)ˣ) : ZMod M) * (t - c0))
          = c0 + ((u2 : ZMod M) * ((u2⁻¹ : (ZMod M)ˣ) : ZMod M)) * (t - c0) := by ring
        _ = t := by rw [hinv, one_mul]; ring
  }
  have h1 : (∑ j ∈ range M, g (b + 2 * (s + j))) = ∑ t : ZMod M, g (ψ t).val := by
    rw [← sum_zmod_eq_sum_range (n := M)]
    apply sum_congr rfl
    intro t _
    apply hper
    have hψ : ψ t = ((b + 2 * (s + t.val) : ℕ) : ZMod M) := by
      change c0 + (u2 : ZMod M) * t = _
      have hu2 : (u2 : ZMod M) = (2 : ZMod M) := ZMod.coe_unitOfCoprime 2 hcop
      have ht : t = (t.val : ZMod M) := (ZMod.natCast_zmod_val t).symm
      dsimp only [c0]
      rw [hu2]
      conv_lhs => rw [ht]
      push_cast
      ring
    rw [hψ, ZMod.val_natCast, Nat.mod_mod]
  rw [h1, Equiv.sum_comp ψ (fun t : ZMod M => g t.val), sum_zmod_eq_sum_range (n := M)]

/-- 步长为 `2` 的有限等差数列求和与周期均值的偏差至多为 `2 M`。 -/
theorem progression_step_two_error {M : ℕ} (hM : Odd M) (g : ℕ → ℝ)
    (hper : ∀ x y : ℕ, x % M = y % M → g x = g y)
    (hbnd : ∀ x : ℕ, |g x| ≤ 1) (b K : ℕ) :
    |(∑ j ∈ range K, g (b + 2 * j)) - ((K : ℝ) / (M : ℝ)) * ∑ x ∈ range M, g x| ≤
      2 * (M : ℝ) := by
  have hM0 : 0 < M := by have := Nat.odd_iff.mp hM; omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
  let q := K / M
  let rem := K % M
  have hKeq : K = q * M + rem := (Nat.div_add_mod' K M).symm
  have hrem_lt : rem < M := Nat.mod_lt K hM0
  have hblocks : ∀ t : ℕ, ∑ j ∈ range (t * M), g (b + 2 * j) =
      (t : ℝ) * ∑ x ∈ range M, g x := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul, sum_range_add, ih, sum_step_two_block hM g hper b (t * M)]
      push_cast; ring
  have hsplit : ∑ j ∈ range K, g (b + 2 * j) =
      (q : ℝ) * (∑ x ∈ range M, g x) + ∑ j ∈ range rem, g (b + 2 * (q * M + j)) := by
    conv_lhs => rw [hKeq]
    rw [sum_range_add, hblocks q]
  have hKdiv : (K : ℝ) / (M : ℝ) = (q : ℝ) + (rem : ℝ) / (M : ℝ) := by
    have hKcast : (K : ℝ) = (q : ℝ) * (M : ℝ) + (rem : ℝ) := by exact_mod_cast hKeq
    rw [hKcast]
    field_simp [hMR.ne']
  rw [hsplit, hKdiv,
    show (q : ℝ) * (∑ x ∈ range M, g x) + (∑ j ∈ range rem, g (b + 2 * (q * M + j))) -
      ((q : ℝ) + (rem : ℝ) / (M : ℝ)) * (∑ x ∈ range M, g x) =
      (∑ j ∈ range rem, g (b + 2 * (q * M + j))) -
        ((rem : ℝ) / (M : ℝ)) * (∑ x ∈ range M, g x) by ring]
  have hrem_sum : |∑ j ∈ range rem, g (b + 2 * (q * M + j))| ≤ (rem : ℝ) := by
    calc |∑ j ∈ range rem, g (b + 2 * (q * M + j))|
        ≤ ∑ j ∈ range rem, |g (b + 2 * (q * M + j))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ range rem, (1 : ℝ) := sum_le_sum (fun j _ => hbnd _)
      _ = (rem : ℝ) := by simp
  have hM_sum : |∑ x ∈ range M, g x| ≤ (M : ℝ) := by
    calc |∑ x ∈ range M, g x|
        ≤ ∑ x ∈ range M, |g x| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x ∈ range M, (1 : ℝ) := sum_le_sum (fun x _ => hbnd _)
      _ = (M : ℝ) := by simp
  have hrem_le : (rem : ℝ) ≤ (M : ℝ) := by exact_mod_cast hrem_lt.le
  have hratio_nn : 0 ≤ (rem : ℝ) / (M : ℝ) := div_nonneg (Nat.cast_nonneg rem) hMR.le
  calc |(∑ j ∈ range rem, g (b + 2 * (q * M + j))) - ((rem : ℝ) / (M : ℝ)) * ∑ x ∈ range M, g x|
      ≤ |∑ j ∈ range rem, g (b + 2 * (q * M + j))| +
          |((rem : ℝ) / (M : ℝ)) * ∑ x ∈ range M, g x| := abs_sub _ _
    _ = |∑ j ∈ range rem, g (b + 2 * (q * M + j))| +
          ((rem : ℝ) / (M : ℝ)) * |∑ x ∈ range M, g x| := by
        rw [abs_mul, abs_of_nonneg hratio_nn]
    _ ≤ (rem : ℝ) + ((rem : ℝ) / (M : ℝ)) * (M : ℝ) :=
        add_le_add hrem_sum (mul_le_mul_of_nonneg_left hM_sum hratio_nn)
    _ = 2 * (rem : ℝ) := by field_simp [hMR.ne']; ring
    _ ≤ 2 * (M : ℝ) := by linarith

/-! ### 第六部分：任意有限分母集 `S ⊆ [1, k]` 的反射带均方主引理 -/

/-- 反射带 `B N` 与 `ReflectedShortProgression.window 1 0 L (R - L)` 一致，且长度至少为 `N/12`。 -/
private theorem band_eq_window {N : ℕ} (hN : 48 ≤ N) :
    let L := (4 * N + 2) / 3
    let U := (3 * N) / 2
    ((Icc N (2 * N)).filter (fun m => 4 * N ≤ 3 * m ∧ 2 * m ≤ 3 * N ∧ Even m)) =
      window 1 0 L (U - L) ∧ 2 ≤ U - L ∧ (N : ℝ) / 12 ≤ ((U - L : ℕ) : ℝ) := by
  intro L U
  have hLU : L ≤ U := by dsimp [L, U]; omega
  refine ⟨?_, by dsimp [L, U]; omega, ?_⟩
  · ext m
    simp only [window, mem_filter, mem_Icc, Nat.mod_one, and_true]
    constructor
    · rintro ⟨⟨_, _⟩, h1, h2, he⟩
      exact ⟨⟨by dsimp [L]; omega, by dsimp [L, U]; omega⟩, he⟩
    · rintro ⟨⟨h1, h2⟩, he⟩
      exact ⟨⟨by dsimp [L] at h1; omega, by dsimp [L, U] at h2; omega⟩,
        by dsimp [L] at h1; omega, by dsimp [L, U] at h2; omega, he⟩
  · have hnat : N ≤ 12 * (U - L) := by dsimp [L, U]; omega
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 12)]
    exact_mod_cast (by linarith : N ≤ (U - L) * 12)

/-- 把 `S ⊆ [1, k]` 上的系数和改写为奇数无平方因子分母上的加权和（权重 `∈ {0, 1, 2}`）。 -/
private theorem sum_cCoeff_eq_odd_sf {k : ℕ} (S : Finset ℕ) (hS : S ⊆ Icc 1 k)
    {m : ℕ} (hm : Even m) :
    let S_odd := (Icc 1 k).filter (fun r => Odd r ∧ Squarefree r ∧ (r ∈ S ∨ 2 * r ∈ S))
    let w : ℕ → ℝ := fun r => (if r ∈ S then 1 else 0) + (if 2 * r ∈ S then 1 else 0)
    (∑ q ∈ S, cCoeff q m) = ∑ r ∈ S_odd, w r * cCoeff r m := by
  intro S_odd w
  have hsf : (∑ q ∈ S, cCoeff q m) = ∑ q ∈ S.filter Squarefree, cCoeff q m := by
    rw [← sum_filter_add_sum_filter_not S Squarefree]
    have hzero : ∑ q ∈ S.filter (fun q => ¬ Squarefree q), cCoeff q m = 0 := by
      apply sum_eq_zero
      intro q hq
      have hq1 : 1 ≤ q := (mem_Icc.mp (hS (mem_filter.mp hq).1)).1
      exact cCoeff_eq_zero_of_not_squarefree (by omega) (mem_filter.mp hq).2 m
    rw [hzero, add_zero]
  rw [hsf, ← sum_filter_add_sum_filter_not (S.filter Squarefree) Odd]
  have hpart1 : ∑ q ∈ (S.filter Squarefree).filter Odd, cCoeff q m =
      ∑ r ∈ S_odd, (if r ∈ S then (1 : ℝ) else 0) * cCoeff r m := by
    have hset : (S.filter Squarefree).filter Odd = S_odd.filter (fun r => r ∈ S) := by
      ext r
      simp only [S_odd, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hrS, hsf⟩, hodd⟩
        exact ⟨⟨mem_Icc.mp (hS hrS), hodd, hsf, Or.inl hrS⟩, hrS⟩
      · rintro ⟨⟨_, hodd, hsf, _⟩, hrS⟩
        exact ⟨⟨hrS, hsf⟩, hodd⟩
    rw [hset, sum_filter]
    apply sum_congr rfl
    intro r _
    split_ifs <;> ring
  have hpart2 : ∑ q ∈ (S.filter Squarefree).filter (fun q => ¬ Odd q), cCoeff q m =
      ∑ r ∈ S_odd, (if 2 * r ∈ S then (1 : ℝ) else 0) * cCoeff r m := by
    have hset : (S.filter Squarefree).filter (fun q => ¬ Odd q) =
        (S_odd.filter (fun r => 2 * r ∈ S)).image (fun r => 2 * r) := by
      ext q
      simp only [S_odd, mem_image, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨hqS, hsfq⟩, hnotodd⟩
        have hqeven : Even q := Nat.not_odd_iff_even.mp hnotodd
        obtain ⟨r, rfl⟩ := even_iff_exists_two_mul.mp hqeven
        have hqIcc := mem_Icc.mp (hS hqS)
        have hsf_r : Squarefree r := hsfq.squarefree_of_dvd (dvd_mul_left r 2)
        have hodd_r : Odd r := by
          by_contra hne
          obtain ⟨t, rfl⟩ := even_iff_exists_two_mul.mp (Nat.not_odd_iff_even.mp hne)
          have h4 : 2 * 2 ∣ 2 * (2 * t) := ⟨t, by ring⟩
          exact Nat.squarefree_iff_prime_squarefree.mp hsfq 2 Nat.prime_two h4
        refine ⟨r, ⟨⟨⟨by omega, by omega⟩, hodd_r, hsf_r, Or.inr hqS⟩, hqS⟩, rfl⟩
      · rintro ⟨r, ⟨⟨_, hodd_r, hsf_r, _⟩, h2rS⟩, rfl⟩
        have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hodd_r
        have hsf2r : Squarefree (2 * r) :=
          Nat.squarefree_mul_iff.mpr ⟨hcop, Nat.prime_two.squarefree, hsf_r⟩
        have hnotodd : ¬ Odd (2 * r) := Nat.not_odd_iff_even.mpr (even_two_mul r)
        exact ⟨⟨h2rS, hsf2r⟩, hnotodd⟩
    rw [hset, sum_image (fun a _ b _ h => by omega), sum_filter]
    apply sum_congr rfl
    intro r hr
    have hodd_r : Odd r := (mem_filter.mp hr).2.1
    split_ifs
    · rw [one_mul, cCoeff_two_mul_of_even hodd_r hm]
    · rw [zero_mul]
  rw [hpart1, hpart2, ← sum_add_distrib]
  apply sum_congr rfl
  intro r _
  dsimp only [w]
  ring

/-- 反射带上的均方主引理：任意 `S ⊆ [1, k]` 的系数和平方均值被对角 `4 ∑ 1/φ(r)³` 加 `8 k⁴ / |B N|` 控制。 -/
theorem band_avg_sq_sum_le {N k : ℕ} (hN : 48 ≤ N) (S : Finset ℕ) (hS : S ⊆ Icc 1 k) :
    let B := (Icc N (2 * N)).filter (fun m => 4 * N ≤ 3 * m ∧ 2 * m ≤ 3 * N ∧ Even m)
    let S_odd := (Icc 1 k).filter (fun r => Odd r ∧ Squarefree r ∧ (r ∈ S ∨ 2 * r ∈ S))
    (∑ m ∈ B, (∑ q ∈ S, cCoeff q m) ^ 2) / (B.card : ℝ) ≤
      4 * (∑ r ∈ S_odd, 1 / (r.totient : ℝ) ^ 3) + 8 * (k : ℝ) ^ 4 / (B.card : ℝ) := by
  intro B S_odd
  let L := (4 * N + 2) / 3
  let U := (3 * N) / 2
  obtain ⟨hBeq, hgap2, _⟩ := band_eq_window hN
  obtain ⟨b, K, _, _, hKpos, hwin, hinj, hcard, _, _⟩ :=
    window_progression (d := 1) (a := 0) (x := L) (H := U - L) odd_one (by decide) (by omega)
  have hBcard : B.card = K := by dsimp only [B]; rw [hBeq, hcard]
  have hBimg : B = (range K).image (fun j => b + 2 * j) := by
    dsimp only [B]; rw [hBeq, hwin]
  have hinj2 : Function.Injective (fun j : ℕ => b + 2 * j) := by
    simpa only [mul_one] using hinj
  have hKposR : (0 : ℝ) < K := by exact_mod_cast hKpos
  let w : ℕ → ℝ := fun r => (if r ∈ S then 1 else 0) + (if 2 * r ∈ S then 1 else 0)
  have hw0 : ∀ r, 0 ≤ w r := fun r => by dsimp [w]; split_ifs <;> norm_num
  have hw2 : ∀ r, w r ≤ 2 := fun r => by dsimp [w]; split_ifs <;> norm_num
  have hrew : ∑ m ∈ B, (∑ q ∈ S, cCoeff q m) ^ 2 =
      ∑ r₁ ∈ S_odd, ∑ r₂ ∈ S_odd,
        (w r₁ * w r₂) * ∑ j ∈ range K, cCoeff r₁ (b + 2 * j) * cCoeff r₂ (b + 2 * j) := by
    have h1 : ∑ m ∈ B, (∑ q ∈ S, cCoeff q m) ^ 2 =
        ∑ m ∈ B, ∑ r₁ ∈ S_odd, ∑ r₂ ∈ S_odd, (w r₁ * w r₂) * (cCoeff r₁ m * cCoeff r₂ m) := by
      apply sum_congr rfl
      intro m hm
      have hev : Even m := (mem_filter.mp hm).2.2.2
      rw [sum_cCoeff_eq_odd_sf S hS hev, sq, sum_mul]
      apply sum_congr rfl
      intro r₁ _
      rw [mul_sum]
      apply sum_congr rfl
      intro r₂ _
      ring
    rw [h1, sum_comm]
    apply sum_congr rfl
    intro r₁ _
    rw [sum_comm]
    apply sum_congr rfl
    intro r₂ _
    rw [← mul_sum, hBimg, sum_image (fun _ _ _ _ h => hinj2 h)]
  have hpair : ∀ r₁ ∈ S_odd, ∀ r₂ ∈ S_odd,
      (w r₁ * w r₂) * (∑ j ∈ range K, cCoeff r₁ (b + 2 * j) * cCoeff r₂ (b + 2 * j)) ≤
        (if r₁ = r₂ then (K : ℝ) * (4 / (r₁.totient : ℝ) ^ 3) else 0) + 8 * (k : ℝ) ^ 2 := by
    intro r₁ hr₁ r₂ hr₂
    obtain ⟨hr₁Icc, ho₁, hsf₁, _⟩ := mem_filter.mp hr₁
    obtain ⟨hr₂Icc, ho₂, hsf₂, _⟩ := mem_filter.mp hr₂
    have hr₁0 : 0 < r₁ := (mem_Icc.mp hr₁Icc).1
    have hr₂0 : 0 < r₂ := (mem_Icc.mp hr₂Icc).1
    have hr₁k : r₁ ≤ k := (mem_Icc.mp hr₁Icc).2
    have hr₂k : r₂ ≤ k := (mem_Icc.mp hr₂Icc).2
    let M := Nat.lcm r₁ r₂
    have hM0 : 0 < M := Nat.lcm_pos hr₁0 hr₂0
    have hModd : Odd M := odd_of_dvd_odd (ho₁.mul ho₂) (Nat.lcm_dvd_mul r₁ r₂)
    have hMle : (M : ℝ) ≤ (k : ℝ) ^ 2 := by
      have h1 : M ≤ r₁ * r₂ := Nat.le_of_dvd (Nat.mul_pos hr₁0 hr₂0) (Nat.lcm_dvd_mul r₁ r₂)
      have h2 : r₁ * r₂ ≤ k * k := Nat.mul_le_mul hr₁k hr₂k
      have h3 : M ≤ k ^ 2 := by rw [sq]; exact h1.trans h2
      exact_mod_cast h3
    let g : ℕ → ℝ := fun x => cCoeff r₁ x * cCoeff r₂ x
    have hgper : ∀ x y : ℕ, x % M = y % M → g x = g y := by
      intro x y hxy
      dsimp only [g]
      have h1 : x % r₁ = y % r₁ := by
        rw [← Nat.mod_mod_of_dvd x (Nat.dvd_lcm_left r₁ r₂),
          ← Nat.mod_mod_of_dvd y (Nat.dvd_lcm_left r₁ r₂), hxy]
      have h2 : x % r₂ = y % r₂ := by
        rw [← Nat.mod_mod_of_dvd x (Nat.dvd_lcm_right r₁ r₂),
          ← Nat.mod_mod_of_dvd y (Nat.dvd_lcm_right r₁ r₂), hxy]
      rw [cCoeff_mod_eq hr₁0 hsf₁ h1, cCoeff_mod_eq hr₂0 hsf₂ h2]
    have hgbnd : ∀ x : ℕ, |g x| ≤ 1 := by
      intro x
      dsimp only [g]
      rw [abs_mul]
      calc |cCoeff r₁ x| * |cCoeff r₂ x| ≤ 1 * 1 :=
            mul_le_mul (abs_cCoeff_le_one hr₁0 hsf₁ x) (abs_cCoeff_le_one hr₂0 hsf₂ x)
              (abs_nonneg _) (by norm_num)
        _ = 1 := one_mul 1
    have herr := progression_step_two_error hModd g hgper hgbnd b K
    have havg := sum_cCoeff_mul_lcm ho₁ hsf₁ ho₂ hsf₂
    have hupper : ∑ j ∈ range K, g (b + 2 * j) ≤
        ((K : ℝ) / (M : ℝ)) * (∑ x ∈ range M, g x) + 2 * (M : ℝ) := by
      linarith [(abs_le.mp herr).2]
    have hww0 : 0 ≤ w r₁ * w r₂ := mul_nonneg (hw0 r₁) (hw0 r₂)
    have hww4 : w r₁ * w r₂ ≤ 4 := by
      calc w r₁ * w r₂ ≤ 2 * 2 := mul_le_mul (hw2 r₁) (hw2 r₂) (hw0 r₂) (by norm_num)
        _ = 4 := by norm_num
    have hMR : (0 : ℝ) < M := by exact_mod_cast hM0
    have hmain : (w r₁ * w r₂) * (((K : ℝ) / (M : ℝ)) * ∑ x ∈ range M, g x) ≤
        if r₁ = r₂ then (K : ℝ) * (4 / (r₁.totient : ℝ) ^ 3) else 0 := by
      rw [show (∑ x ∈ range M, g x) = if r₁ = r₂ then (M : ℝ) / (r₁.totient : ℝ) ^ 3 else 0 from havg]
      split_ifs with heq
      · have hcancel : ((K : ℝ) / (M : ℝ)) * ((M : ℝ) / (r₁.totient : ℝ) ^ 3) =
            (K : ℝ) / (r₁.totient : ℝ) ^ 3 := by
          field_simp [hMR.ne']
        rw [hcancel]
        have hpos : 0 ≤ (K : ℝ) / (r₁.totient : ℝ) ^ 3 := by positivity
        calc (w r₁ * w r₂) * ((K : ℝ) / (r₁.totient : ℝ) ^ 3)
            ≤ 4 * ((K : ℝ) / (r₁.totient : ℝ) ^ 3) := mul_le_mul_of_nonneg_right hww4 hpos
          _ = (K : ℝ) * (4 / (r₁.totient : ℝ) ^ 3) := by ring
      · simp
    have herr_term : (w r₁ * w r₂) * (2 * (M : ℝ)) ≤ 8 * (k : ℝ) ^ 2 := by
      calc (w r₁ * w r₂) * (2 * (M : ℝ))
          ≤ 4 * (2 * (k : ℝ) ^ 2) := mul_le_mul hww4 (by linarith) (by positivity) (by norm_num)
        _ = 8 * (k : ℝ) ^ 2 := by ring
    calc (w r₁ * w r₂) * (∑ j ∈ range K, g (b + 2 * j))
        ≤ (w r₁ * w r₂) * (((K : ℝ) / (M : ℝ)) * (∑ x ∈ range M, g x) + 2 * (M : ℝ)) :=
          mul_le_mul_of_nonneg_left hupper hww0
      _ = (w r₁ * w r₂) * (((K : ℝ) / (M : ℝ)) * (∑ x ∈ range M, g x)) +
            (w r₁ * w r₂) * (2 * (M : ℝ)) := mul_add _ _ _
      _ ≤ _ := add_le_add hmain herr_term
  have hcard_le : (S_odd.card : ℝ) ≤ (k : ℝ) := by
    have hsub : S_odd ⊆ Icc 1 k := filter_subset _ _
    have hc : S_odd.card ≤ k := (card_le_card hsub).trans (by simp)
    exact_mod_cast hc
  have htotal : ∑ m ∈ B, (∑ q ∈ S, cCoeff q m) ^ 2 ≤
      (K : ℝ) * (4 * ∑ r ∈ S_odd, 1 / (r.totient : ℝ) ^ 3) + 8 * (k : ℝ) ^ 4 := by
    rw [hrew]
    calc ∑ r₁ ∈ S_odd, ∑ r₂ ∈ S_odd,
            (w r₁ * w r₂) * ∑ j ∈ range K, cCoeff r₁ (b + 2 * j) * cCoeff r₂ (b + 2 * j)
        ≤ ∑ r₁ ∈ S_odd, ∑ r₂ ∈ S_odd,
            ((if r₁ = r₂ then (K : ℝ) * (4 / (r₁.totient : ℝ) ^ 3) else 0) + 8 * (k : ℝ) ^ 2) :=
          sum_le_sum (fun r₁ hr₁ => sum_le_sum (fun r₂ hr₂ => hpair r₁ hr₁ r₂ hr₂))
      _ = (∑ r₁ ∈ S_odd, ∑ r₂ ∈ S_odd,
            if r₁ = r₂ then (K : ℝ) * (4 / (r₁.totient : ℝ) ^ 3) else 0) +
          (∑ _r₁ ∈ S_odd, ∑ _r₂ ∈ S_odd, 8 * (k : ℝ) ^ 2) := by
          simp_rw [sum_add_distrib]
      _ = (K : ℝ) * (4 * ∑ r ∈ S_odd, 1 / (r.totient : ℝ) ^ 3) +
            (S_odd.card : ℝ) * ((S_odd.card : ℝ) * (8 * (k : ℝ) ^ 2)) := by
          congr 1
          · rw [mul_sum, mul_sum]
            apply sum_congr rfl
            intro r₁ hr₁
            rw [sum_ite_eq S_odd r₁, ite_eq_left hr₁]
            ring
          · simp only [sum_const, nsmul_eq_mul]
      _ ≤ (K : ℝ) * (4 * ∑ r ∈ S_odd, 1 / (r.totient : ℝ) ^ 3) + 8 * (k : ℝ) ^ 4 := by
          refine add_le_add le_rfl ?_
          have hsq : (S_odd.card : ℝ) * (S_odd.card : ℝ) ≤ (k : ℝ) * (k : ℝ) :=
            mul_le_mul hcard_le hcard_le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
          nlinarith [sq_nonneg (k : ℝ)]
  rw [hBcard, div_le_iff₀ hKposR]
  calc ∑ m ∈ B, (∑ q ∈ S, cCoeff q m) ^ 2
      ≤ (K : ℝ) * (4 * ∑ r ∈ S_odd, 1 / (r.totient : ℝ) ^ 3) + 8 * (k : ℝ) ^ 4 := htotal
    _ = (4 * ∑ r ∈ S_odd, 1 / (r.totient : ℝ) ^ 3 + 8 * (k : ℝ) ^ 4 / (K : ℝ)) * (K : ℝ) := by
        field_simp [hKposR.ne']

/-! ### 第七部分：`∑ 1/φ(r)³` 的一致总界与尾界 -/

/-- 裂项界：`∑_{n=2}^{M} 1/n³ ≤ 1`。 -/
private theorem sum_inv_cube_from_two_le (M : ℕ) :
    ∑ n ∈ Icc 2 M, (1 : ℝ) / (n : ℝ) ^ 3 ≤ 1 := by
  have haux : ∀ m : ℕ, ∑ n ∈ Icc 2 m, (1 : ℝ) / (n : ℝ) ^ 3 ≤
      1 - if 2 ≤ m then 1 / (m : ℝ) else 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      by_cases h1 : m + 1 < 2
      · have hemp : Icc 2 (m + 1) = ∅ := Icc_eq_empty (by omega)
        rw [hemp, sum_empty, ite_eq_right (by omega : ¬ 2 ≤ m + 1)]; norm_num
      · by_cases h2 : m + 1 = 2
        · rw [h2, Icc_self, sum_singleton, ite_eq_left le_rfl]; norm_num
        · have hm2 : 2 ≤ m := by omega
          have hm2' : 2 ≤ m + 1 := by omega
          rw [ite_eq_left hm2] at ih
          rw [ite_eq_left hm2', sum_Icc_succ_top hm2']
          have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm2
          have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
            push_cast
            have hm0 : (0 : ℝ) < m := by linarith
            have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
            rw [div_sub_div _ _ hm0.ne' hm1.ne']
            have hnum : (1 : ℝ) * ((m : ℝ) + 1) - (m : ℝ) * 1 = 1 := by ring
            rw [hnum]
            apply one_div_le_one_div_of_le (mul_pos hm0 hm1)
            have hsq : (m : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith
            nlinarith
          linarith
  have h := haux M
  split_ifs at h with h2
  · have : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
    linarith
  · linarith

/-- 裂项尾界：对 `y ≥ 3`，`∑_{n=y}^{M} 1/n³ ≤ 4 / y²`。 -/
private theorem sum_inv_cube_tail_le {y : ℕ} (hy : 3 ≤ y) (M : ℕ) :
    ∑ n ∈ Icc y M, (1 : ℝ) / (n : ℝ) ^ 3 ≤ 4 / (y : ℝ) ^ 2 := by
  have hyR : (3 : ℝ) ≤ y := by exact_mod_cast hy
  have hy1 : (0 : ℝ) < (y : ℝ) - 1 := by linarith
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have haux : ∀ m : ℕ, ∑ n ∈ Icc y m, (1 : ℝ) / (n : ℝ) ^ 3 ≤
      1 / ((y : ℝ) - 1) ^ 2 - if y ≤ m then 1 / (m : ℝ) ^ 2 else 0 := by
    intro m
    induction m with
    | zero =>
      rw [Icc_eq_empty (by omega), sum_empty, ite_eq_right (by omega : ¬ y ≤ 0), sub_zero]
      positivity
    | succ m ih =>
      by_cases hlt : m + 1 < y
      · rw [Icc_eq_empty (by omega), sum_empty, ite_eq_right (by omega : ¬ y ≤ m + 1), sub_zero]
        positivity
      · by_cases heq : m + 1 = y
        · rw [heq, Icc_self, sum_singleton, ite_eq_left le_rfl]
          have h1 : (0 : ℝ) < ((y : ℝ) - 1) ^ 2 := by positivity
          have h2 : (0 : ℝ) < (y : ℝ) ^ 2 := by positivity
          rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (mul_pos h1 h2)]
          have hsq : ((y : ℝ) - 1) ^ 2 ≤ (y : ℝ) * (2 * (y : ℝ) - 1) := by nlinarith
          nlinarith [sq_nonneg (y : ℝ)]
        · have hmy : y ≤ m := by omega
          have hmy1 : y ≤ m + 1 := by omega
          rw [ite_eq_left hmy] at ih
          rw [ite_eq_left hmy1, sum_Icc_succ_top hmy1]
          have hmR : (3 : ℝ) ≤ m := by exact_mod_cast (show 3 ≤ m by omega)
          have hm0' : (0 : ℝ) < m := by linarith
          have hm1' : (0 : ℝ) < (m : ℝ) + 1 := by linarith
          have hstep : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 3 ≤
              1 / (m : ℝ) ^ 2 - 1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
            push_cast
            have hm0 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
            have hm1 : (0 : ℝ) < ((m : ℝ) + 1) ^ 2 := by positivity
            rw [div_sub_div _ _ hm0.ne' hm1.ne', div_le_div_iff₀ (by positivity) (mul_pos hm0 hm1)]
            have hsq : (m : ℝ) ^ 2 ≤ ((m : ℝ) + 1) * (2 * (m : ℝ) + 1) := by nlinarith
            nlinarith [sq_nonneg ((m : ℝ) + 1)]
          linarith
  have h := haux M
  have hnonneg : (0 : ℝ) ≤ if y ≤ M then 1 / (M : ℝ) ^ 2 else 0 := by
    split_ifs <;> positivity
  have hcmp : (1 : ℝ) / ((y : ℝ) - 1) ^ 2 ≤ 4 / (y : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- 对任意有限奇数无平方因子数集 `R`，总有 `∑_{r ∈ R} 1/φ(r)³ ≤ 3`。 -/
theorem sum_odd_sf_inv_totient_cube_le_three (R : Finset ℕ)
    (hR : ∀ r ∈ R, Odd r ∧ Squarefree r) :
    ∑ r ∈ R, (1 : ℝ) / (r.totient : ℝ) ^ 3 ≤ 3 := by
  let P := R.biUnion Nat.primeFactors
  have hPprime : ∀ p ∈ P, p.Prime ∧ 3 ≤ p := by
    intro p hp
    obtain ⟨r, hrR, hpr⟩ := mem_biUnion.mp hp
    have hprime := (Nat.mem_primeFactors.mp hpr).1
    have h2ne : p ≠ 2 := by
      intro h2; subst h2
      exact (hR r hrR).1.not_two_dvd_nat (Nat.mem_primeFactors.mp hpr).2.1
    exact ⟨hprime, by have := hprime.two_le; omega⟩
  have htot_eq : ∀ r ∈ R, (1 : ℝ) / (r.totient : ℝ) ^ 3 =
      ∏ p ∈ r.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) ^ 3 := by
    intro r hr
    have hsf := (hR r hr).2
    have hr0 : 0 < r := by have := Nat.odd_iff.mp (hR r hr).1; omega
    have htot : (r.totient : ℝ) = ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
      have hid := Nat.totient_mul_prod_primeFactors r
      have hprod : ∏ p ∈ r.primeFactors, (p : ℝ) = (r : ℝ) := by
        rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]
      have hcast : (r.totient : ℝ) * ∏ p ∈ r.primeFactors, (p : ℝ) =
          (r : ℝ) * ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
        have h0 := congrArg (fun n : ℕ => (n : ℝ)) hid
        simp only [Nat.cast_mul, Nat.cast_prod] at h0
        rw [h0]
        congr 1
        apply prod_congr rfl
        intro p hp
        rw [Nat.cast_sub (Nat.mem_primeFactors.mp hp).1.one_le, Nat.cast_one]
      rw [hprod] at hcast
      have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr0.ne'
      exact mul_left_cancel₀ hrR (by linarith)
    rw [htot, ← prod_pow, one_div, ← prod_inv_distrib]
    apply prod_congr rfl
    intro p _; rw [one_div]
  have hinj : Set.InjOn Nat.primeFactors (R : Set ℕ) := by
    intro a ha b hb hab
    have h1 := Nat.prod_primeFactors_of_squarefree (hR a ha).2
    have h2 := Nat.prod_primeFactors_of_squarefree (hR b hb).2
    rw [hab] at h1
    exact h1.symm.trans h2
  have hsub : R.image Nat.primeFactors ⊆ P.powerset := by
    intro t ht
    obtain ⟨r, hr, rfl⟩ := mem_image.mp ht
    rw [mem_powerset]
    exact subset_biUnion_of_mem Nat.primeFactors hr
  have hsumP_le : ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) ^ 3 ≤ 1 := by
    let M := P.sup id
    let f_sub : ℕ → ℕ := fun p => p - 1
    have himg_sub : P.image f_sub ⊆ Icc 2 M := by
      intro n hn
      obtain ⟨p, hpP, rfl⟩ := mem_image.mp hn
      have h3 := (hPprime p hpP).2
      have hle : p ≤ M := le_sup (f := id) hpP
      exact mem_Icc.mpr ⟨by dsimp [f_sub]; omega, by dsimp [f_sub]; omega⟩
    have himg_inj : Set.InjOn f_sub (P : Set ℕ) := by
      intro a ha b hb hab
      have ha3 := (hPprime a ha).2
      have hb3 := (hPprime b hb).2
      dsimp only [f_sub] at hab
      omega
    calc ∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) ^ 3
        = ∑ p ∈ P, (1 : ℝ) / ((f_sub p : ℕ) : ℝ) ^ 3 := by
          apply sum_congr rfl
          intro p hp
          dsimp only [f_sub]
          rw [Nat.cast_sub (hPprime p hp).1.one_le, Nat.cast_one]
      _ = ∑ n ∈ P.image f_sub, (1 : ℝ) / (n : ℝ) ^ 3 :=
          (sum_image (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3)
            (fun a ha b hb h => himg_inj ha hb h)).symm
      _ ≤ ∑ n ∈ Icc 2 M, (1 : ℝ) / (n : ℝ) ^ 3 :=
          sum_le_sum_of_subset_of_nonneg himg_sub (fun _ _ _ => by positivity)
      _ ≤ 1 := sum_inv_cube_from_two_le M
  calc ∑ r ∈ R, (1 : ℝ) / (r.totient : ℝ) ^ 3
      = ∑ r ∈ R, ∏ p ∈ r.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) ^ 3 := sum_congr rfl htot_eq
    _ = ∑ t ∈ R.image Nat.primeFactors, ∏ p ∈ t, (1 : ℝ) / ((p : ℝ) - 1) ^ 3 :=
        (sum_image (f := fun t : Finset ℕ => ∏ p ∈ t, (1 : ℝ) / ((p : ℝ) - 1) ^ 3)
          (fun a ha b hb h => hinj ha hb h)).symm
    _ ≤ ∑ t ∈ P.powerset, ∏ p ∈ t, (1 : ℝ) / ((p : ℝ) - 1) ^ 3 :=
        sum_le_sum_of_subset_of_nonneg hsub (fun t ht _ =>
          prod_nonneg (fun p hp => by
            have hpP : p ∈ P := (mem_powerset.mp ht) hp
            have : (3 : ℝ) ≤ p := by exact_mod_cast (hPprime p hpP).2
            have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
            positivity))
    _ = ∏ p ∈ P, (1 + (1 : ℝ) / ((p : ℝ) - 1) ^ 3) := by
        rw [Finset.prod_one_add]
    _ ≤ ∏ p ∈ P, Real.exp ((1 : ℝ) / ((p : ℝ) - 1) ^ 3) := by
        apply Finset.prod_le_prod₀
        · intro p hp
          have : (3 : ℝ) ≤ p := by exact_mod_cast (hPprime p hp).2
          have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
          positivity
        · intro p _
          rw [add_comm]
          exact Real.add_one_le_exp _
    _ = Real.exp (∑ p ∈ P, (1 : ℝ) / ((p : ℝ) - 1) ^ 3) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hsumP_le
    _ ≤ 3 := by linarith [Real.exp_one_lt_d9]

/-- 若 `R` 中每个奇数无平方因子数均含大于 `y` 的素因子，则 `∑_{r ∈ R} 1/φ(r)³ ≤ 12 / y²`。 -/
theorem sum_odd_sf_tail_inv_totient_cube_le {y : ℕ} (hy : 3 ≤ y) (R : Finset ℕ)
    (hR : ∀ r ∈ R, Odd r ∧ Squarefree r ∧ ∃ p ∈ r.primeFactors, y < p) :
    ∑ r ∈ R, (1 : ℝ) / (r.totient : ℝ) ^ 3 ≤ 12 / (y : ℝ) ^ 2 := by
  let P_tail := (R.biUnion Nat.primeFactors).filter (fun p => y < p)
  have hPprime : ∀ p ∈ P_tail, p.Prime ∧ y < p := by
    intro p hp
    obtain ⟨hbi, hgt⟩ := mem_filter.mp hp
    obtain ⟨r, _, hpr⟩ := mem_biUnion.mp hbi
    exact ⟨(Nat.mem_primeFactors.mp hpr).1, hgt⟩
  have hcover : ∀ r ∈ R, (1 : ℝ) / (r.totient : ℝ) ^ 3 ≤
      ∑ p ∈ P_tail, if p ∣ r then (1 : ℝ) / (r.totient : ℝ) ^ 3 else 0 := by
    intro r hr
    obtain ⟨_, _, p, hpr, hgt⟩ := hR r hr
    have hp_mem : p ∈ P_tail :=
      mem_filter.mpr ⟨mem_biUnion.mpr ⟨r, hr, hpr⟩, hgt⟩
    have hpdvd : p ∣ r := (Nat.mem_primeFactors.mp hpr).2.1
    calc (1 : ℝ) / (r.totient : ℝ) ^ 3
        = if p ∣ r then (1 : ℝ) / (r.totient : ℝ) ^ 3 else 0 := (ite_eq_left hpdvd).symm
      _ ≤ ∑ q ∈ P_tail, if q ∣ r then (1 : ℝ) / (r.totient : ℝ) ^ 3 else 0 :=
          single_le_sum (f := fun q => if q ∣ r then (1 : ℝ) / (r.totient : ℝ) ^ 3 else 0)
            (fun q _ => by split_ifs <;> positivity) hp_mem
  have hinner : ∀ p ∈ P_tail,
      (∑ r ∈ R, if p ∣ r then (1 : ℝ) / (r.totient : ℝ) ^ 3 else 0) ≤
        3 / ((p : ℝ) - 1) ^ 3 := by
    intro p hp
    obtain ⟨hprime, hgt⟩ := hPprime p hp
    rw [← sum_filter]
    let Rp := R.filter (fun r => p ∣ r)
    let R' := Rp.image (fun r => r / p)
    have hR' : ∀ r' ∈ R', Odd r' ∧ Squarefree r' := by
      intro r' hr'
      obtain ⟨r, hrp, rfl⟩ := mem_image.mp hr'
      obtain ⟨hrR, hpdvd⟩ := mem_filter.mp hrp
      have hmul : p * (r / p) = r := Nat.mul_div_cancel' hpdvd
      refine ⟨?_, ?_⟩
      · exact odd_of_dvd_odd (hR r hrR).1 ⟨p, by linarith⟩
      · exact (hR r hrR).2.1.squarefree_of_dvd ⟨p, by linarith⟩
    have hinj : Set.InjOn (fun r => r / p) (Rp : Set ℕ) := by
      intro a ha b hb hab
      dsimp only at hab
      have hda : p ∣ a := (mem_filter.mp ha).2
      have hdb : p ∣ b := (mem_filter.mp hb).2
      rw [← Nat.mul_div_cancel' hda, ← Nat.mul_div_cancel' hdb, hab]
    have hfac : ∀ r ∈ Rp, (1 : ℝ) / (r.totient : ℝ) ^ 3 =
        (1 / ((p : ℝ) - 1) ^ 3) * (1 / ((r / p).totient : ℝ) ^ 3) := by
      intro r hrp
      obtain ⟨hrR, hpdvd⟩ := mem_filter.mp hrp
      have hsf := (hR r hrR).2.1
      have hmul : p * (r / p) = r := Nat.mul_div_cancel' hpdvd
      have hcop : p.Coprime (r / p) := by
        rw [hprime.coprime_iff_not_dvd]
        intro hd
        have hpp : p * p ∣ r := by
          obtain ⟨t, ht⟩ := hd
          exact ⟨t, by rw [← hmul, ht]; ring⟩
        exact Nat.squarefree_iff_prime_squarefree.mp hsf p hprime hpp
      have htot_nat : r.totient = (p - 1) * (r / p).totient := by
        conv_lhs => rw [← hmul]
        rw [Nat.totient_mul hcop, Nat.totient_prime hprime]
      have htot : (r.totient : ℝ) = ((p : ℝ) - 1) * ((r / p).totient : ℝ) := by
        rw [htot_nat, Nat.cast_mul, Nat.cast_sub hprime.one_le, Nat.cast_one]
      rw [htot, mul_pow, div_mul_div_comm, one_mul]
    have hpR : (4 : ℝ) ≤ p := by exact_mod_cast (show 4 ≤ p by omega)
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    calc ∑ r ∈ Rp, (1 : ℝ) / (r.totient : ℝ) ^ 3
        = ∑ r ∈ Rp, (1 / ((p : ℝ) - 1) ^ 3) * (1 / ((r / p).totient : ℝ) ^ 3) :=
          sum_congr rfl hfac
      _ = (1 / ((p : ℝ) - 1) ^ 3) * ∑ r ∈ Rp, (1 / ((r / p).totient : ℝ) ^ 3) :=
          (mul_sum _ _ _).symm
      _ = (1 / ((p : ℝ) - 1) ^ 3) * ∑ r' ∈ R', (1 / (r'.totient : ℝ) ^ 3) := by
          rw [sum_image (fun a ha b hb h => hinj ha hb h)]
      _ ≤ (1 / ((p : ℝ) - 1) ^ 3) * 3 :=
          mul_le_mul_of_nonneg_left (sum_odd_sf_inv_totient_cube_le_three R' hR') (by positivity)
      _ = 3 / ((p : ℝ) - 1) ^ 3 := by ring
  let M := P_tail.sup id
  let f_sub : ℕ → ℕ := fun p => p - 1
  have himg_sub : P_tail.image f_sub ⊆ Icc y M := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hn
    have hgt := (hPprime p hp).2
    have hle : p ≤ M := le_sup (f := id) hp
    exact mem_Icc.mpr ⟨by dsimp [f_sub]; omega, by dsimp [f_sub]; omega⟩
  have himg_inj : Set.InjOn f_sub (P_tail : Set ℕ) := by
    intro a ha b hb hab
    have ha' := (hPprime a ha).2
    have hb' := (hPprime b hb).2
    dsimp only [f_sub] at hab
    omega
  have hsum_tail : ∑ p ∈ P_tail, (1 : ℝ) / ((p : ℝ) - 1) ^ 3 ≤ 4 / (y : ℝ) ^ 2 := by
    calc ∑ p ∈ P_tail, (1 : ℝ) / ((p : ℝ) - 1) ^ 3
        = ∑ p ∈ P_tail, (1 : ℝ) / ((f_sub p : ℕ) : ℝ) ^ 3 := by
          apply sum_congr rfl
          intro p hp
          dsimp only [f_sub]
          rw [Nat.cast_sub (hPprime p hp).1.one_le, Nat.cast_one]
      _ = ∑ n ∈ P_tail.image f_sub, (1 : ℝ) / (n : ℝ) ^ 3 :=
          (sum_image (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 3)
            (fun a ha b hb h => himg_inj ha hb h)).symm
      _ ≤ ∑ n ∈ Icc y M, (1 : ℝ) / (n : ℝ) ^ 3 :=
          sum_le_sum_of_subset_of_nonneg himg_sub (fun _ _ _ => by positivity)
      _ ≤ 4 / (y : ℝ) ^ 2 := sum_inv_cube_tail_le hy M
  calc ∑ r ∈ R, (1 : ℝ) / (r.totient : ℝ) ^ 3
      ≤ ∑ r ∈ R, ∑ p ∈ P_tail, if p ∣ r then (1 : ℝ) / (r.totient : ℝ) ^ 3 else 0 :=
        sum_le_sum hcover
    _ = ∑ p ∈ P_tail, ∑ r ∈ R, if p ∣ r then (1 : ℝ) / (r.totient : ℝ) ^ 3 else 0 := sum_comm
    _ ≤ ∑ p ∈ P_tail, 3 / ((p : ℝ) - 1) ^ 3 := sum_le_sum hinner
    _ = 3 * ∑ p ∈ P_tail, (1 : ℝ) / ((p : ℝ) - 1) ^ 3 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p _; ring
    _ ≤ 3 * (4 / (y : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hsum_tail (by norm_num)
    _ = 12 / (y : ℝ) ^ 2 := by ring

/-! ### 第八部分：对数四次幂与 `N` 的渐近压制及最终拼装 -/

/-- 对任意正数 `c`，充分大的 `N` 满足 `(Nat.log 2 (N + 2))⁴ ≤ c * N`。 -/
private theorem eventually_log_fourth_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (Nat.log 2 (N + 2) : ℝ) ^ 4 ≤ c * (N : ℝ) := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := ((isLittleO_log_rpow_rpow_atTop (4 : ℝ) (show (0 : ℝ) < 1 by norm_num)).comp_tendsto ht).bound
    (show 0 < c / 256 by positivity)
  filter_upwards [hl, eventually_ge_atTop (2 : ℕ)] with N hN h2
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  change ‖(Real.log (N : ℝ)) ^ (4 : ℝ)‖ ≤ (c / 256) * ‖(N : ℝ) ^ (1 : ℝ)‖ at hN
  have hpow : (Real.log (N : ℝ)) ^ (4 : ℝ) = (Real.log (N : ℝ)) ^ (4 : ℕ) :=
    Real.rpow_natCast _ 4
  rw [hpow, Real.rpow_one,
    Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg h1) _),
    Real.norm_of_nonneg (Nat.cast_nonneg N)] at hN
  calc (Nat.log 2 (N + 2) : ℝ) ^ 4
      ≤ (4 * Real.log (N : ℝ)) ^ 4 := by
        simpa only [GoldbachMajorArc.Polylog.cutoff, Nat.cast_pow] using
          GoldbachMajorArc.Polylog.cutoff_le_log 4 h2
    _ = 256 * (Real.log (N : ℝ)) ^ 4 := by ring
    _ ≤ 256 * ((c / 256) * (N : ℝ)) := mul_le_mul_of_nonneg_left hN (by norm_num)
    _ = c * (N : ℝ) := by ring

/-- 三项和的平方不等式。 -/
private theorem add_three_sq_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

/-- 主定理内部版本：固定 `C = 800`，对任意 `y ≥ 3` 均存在阈值 `T` 使均方误差至多 `800 / y²`。 -/
theorem main_bound :
    ∀ y : ℕ, 3 ≤ y → ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1
      let B := (Icc N (2 * N)).filter (fun m => 4 * N ≤ 3 * m ∧ 2 * m ≤ 3 * N ∧ Even m)
      let P := fun m : ℕ => 2 * C₂ *
        ∏ p ∈ m.primeFactors.filter (fun p => 2 < p ∧ p ≤ y), (1 + 1 / ((p : ℝ) - 2))
      (∑ m ∈ B, (normalized N m - P m) ^ 2) / (B.card : ℝ) ≤ 800 / (y : ℝ) ^ 2 := by
  intro y hy
  have hyR : (0 : ℝ) < y := by exact_mod_cast (show 0 < y by omega)
  let D := primorial y
  have hDpos : 0 < D := primorial_pos y
  have hev : ∀ᶠ N : ℕ in atTop,
      48 ≤ N ∧
      D ≤ Nat.log 2 (N + 2) ∧
      (∀ m : ℕ, 4 * N ≤ 3 * m → 2 * m ≤ 3 * N →
        |normalized N m - coefficientPrefix (Nat.log 2 (N + 2)) m| ≤ 1 / (y : ℝ)) ∧
      (Nat.log 2 (N + 2) : ℝ) ^ 4 ≤ (1 / (384 * (y : ℝ) ^ 2)) * (N : ℝ) := by
    filter_upwards [
      eventually_ge_atTop (48 : ℕ),
      eventually_ge_atTop (2 ^ D),
      eventually_normalized_transfer (show (0 : ℝ) < 1 / (y : ℝ) by positivity),
      eventually_log_fourth_le (show (0 : ℝ) < 1 / (384 * (y : ℝ) ^ 2) by positivity)
    ] with N h48 h2D hTrans hLog4
    refine ⟨h48, ?_, hTrans, hLog4⟩
    exact Nat.le_log_of_pow_le (by decide) (h2D.trans (Nat.le_add_right N 2))
  obtain ⟨T, hT⟩ := eventually_atTop.mp hev
  refine ⟨T, fun N hNT => ?_⟩
  obtain ⟨h48, hDk, hTrans, hLog4⟩ := hT N hNT
  intro C₂ B P
  let k := Nat.log 2 (N + 2)
  let L := (4 * N + 2) / 3
  let U := (3 * N) / 2
  obtain ⟨hBeq, hgap2, hgapN⟩ := band_eq_window h48
  obtain ⟨_, K, _, _, hKpos, _, _, hcard, _, hKlen⟩ :=
    window_progression (d := 1) (a := 0) (x := L) (H := U - L) odd_one (by decide) (by omega)
  have hBcard : B.card = K := by dsimp only [B]; rw [hBeq, hcard]
  have hBpos : (0 : ℝ) < (B.card : ℝ) := by rw [hBcard]; exact_mod_cast hKpos
  have hBlen : (N : ℝ) / 48 ≤ (B.card : ℝ) := by
    rw [hBcard]
    calc (N : ℝ) / 48 = ((N : ℝ) / 12) / (4 * (1 : ℝ)) := by ring
      _ ≤ ((U - L : ℕ) : ℝ) / (4 * ((1 : ℕ) : ℝ)) := by
          simpa using div_le_div_of_nonneg_right hgapN (by norm_num : (0 : ℝ) ≤ 4)
      _ ≤ (K : ℝ) := hKlen
  have herr_k4 : 8 * (k : ℝ) ^ 4 / (B.card : ℝ) ≤ 1 / (y : ℝ) ^ 2 := by
    rw [div_le_iff₀ hBpos]
    have h1 : 8 * (k : ℝ) ^ 4 ≤ (1 / (48 * (y : ℝ) ^ 2)) * (N : ℝ) := by
      calc 8 * (k : ℝ) ^ 4 ≤ 8 * ((1 / (384 * (y : ℝ) ^ 2)) * (N : ℝ)) :=
            mul_le_mul_of_nonneg_left hLog4 (by norm_num)
        _ = (1 / (48 * (y : ℝ) ^ 2)) * (N : ℝ) := by ring
    calc 8 * (k : ℝ) ^ 4 ≤ (1 / (48 * (y : ℝ) ^ 2)) * (N : ℝ) := h1
      _ = (1 / (y : ℝ) ^ 2) * ((N : ℝ) / 48) := by ring
      _ ≤ (1 / (y : ℝ) ^ 2) * (B.card : ℝ) :=
          mul_le_mul_of_nonneg_left hBlen (by positivity)
  have hDsub : D.divisors ⊆ Icc 1 k := by
    intro q hq
    obtain ⟨hqD, _⟩ := Nat.mem_divisors.mp hq
    exact mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hqD hDpos, (Nat.le_of_dvd hDpos hqD).trans hDk⟩
  let S_tail := (Icc 1 k) \ D.divisors
  have hS_tail_sub : S_tail ⊆ Icc 1 k := sdiff_subset
  have hpoint : ∀ m ∈ B,
      (normalized N m - P m) ^ 2 ≤
        3 * (1 / (y : ℝ) ^ 2) +
        3 * (∑ q ∈ S_tail, cCoeff q m) ^ 2 +
        3 * ((16 / (y : ℝ) ^ 2) * (QModel y m) ^ 2) := by
    intro m hm
    obtain ⟨hmIcc, hlo, hhi, hev⟩ := mem_filter.mp hm
    have hm0 : 0 < m := by have := (mem_Icc.mp hmIcc).1; omega
    let a := normalized N m - coefficientPrefix k m
    let b := coefficientPrefix k m - QModel y m
    let c := QModel y m - P m
    have hsplit : normalized N m - P m = a + b + c := by dsimp only [a, b, c]; ring
    have h3 : (normalized N m - P m) ^ 2 ≤ 3 * a ^ 2 + 3 * b ^ 2 + 3 * c ^ 2 := by
      rw [hsplit]; exact add_three_sq_le a b c
    have ht1 : a ^ 2 ≤ 1 / (y : ℝ) ^ 2 := by
      have habs : |a| ≤ 1 / (y : ℝ) := hTrans m hlo hhi
      have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
      simpa only [sq_abs, one_div, inv_pow] using hsq
    have ht2 : b = ∑ q ∈ S_tail, cCoeff q m := by
      dsimp only [b, S_tail, D]
      unfold coefficientPrefix QModel cCoeff
      rw [sum_sdiff_eq_sub hDsub]
    have ht3 : c ^ 2 ≤ (16 / (y : ℝ) ^ 2) * (QModel y m) ^ 2 :=
      QModel_sub_target_sq_le hy hm0 hev
    rw [ht2] at h3
    linarith
  have havg_point : (∑ m ∈ B, (normalized N m - P m) ^ 2) / (B.card : ℝ) ≤
      3 / (y : ℝ) ^ 2 +
      3 * ((∑ m ∈ B, (∑ q ∈ S_tail, cCoeff q m) ^ 2) / (B.card : ℝ)) +
      (48 / (y : ℝ) ^ 2) * ((∑ m ∈ B, (∑ q ∈ D.divisors, cCoeff q m) ^ 2) / (B.card : ℝ)) := by
    have hsum_le : ∑ m ∈ B, (normalized N m - P m) ^ 2 ≤
        (B.card : ℝ) * (3 / (y : ℝ) ^ 2) +
        3 * (∑ m ∈ B, (∑ q ∈ S_tail, cCoeff q m) ^ 2) +
        (48 / (y : ℝ) ^ 2) * (∑ m ∈ B, (∑ q ∈ D.divisors, cCoeff q m) ^ 2) := by
      calc ∑ m ∈ B, (normalized N m - P m) ^ 2
          ≤ ∑ m ∈ B, (3 * (1 / (y : ℝ) ^ 2) +
              3 * (∑ q ∈ S_tail, cCoeff q m) ^ 2 +
              3 * ((16 / (y : ℝ) ^ 2) * (QModel y m) ^ 2)) := sum_le_sum hpoint
        _ = (∑ _m ∈ B, 3 * (1 / (y : ℝ) ^ 2)) +
            (∑ m ∈ B, 3 * (∑ q ∈ S_tail, cCoeff q m) ^ 2) +
            (∑ m ∈ B, (48 / (y : ℝ) ^ 2) * (∑ q ∈ D.divisors, cCoeff q m) ^ 2) := by
            simp_rw [sum_add_distrib]
            congr 1
            apply sum_congr rfl
            intro m _
            unfold QModel cCoeff
            ring
        _ = _ := by
            rw [sum_const, nsmul_eq_mul, ← mul_sum, ← mul_sum]
            ring
    rw [div_le_iff₀ hBpos]
    calc ∑ m ∈ B, (normalized N m - P m) ^ 2
        ≤ (B.card : ℝ) * (3 / (y : ℝ) ^ 2) +
          3 * (∑ m ∈ B, (∑ q ∈ S_tail, cCoeff q m) ^ 2) +
          (48 / (y : ℝ) ^ 2) * (∑ m ∈ B, (∑ q ∈ D.divisors, cCoeff q m) ^ 2) := hsum_le
      _ = (3 / (y : ℝ) ^ 2 +
          3 * ((∑ m ∈ B, (∑ q ∈ S_tail, cCoeff q m) ^ 2) / (B.card : ℝ)) +
          (48 / (y : ℝ) ^ 2) * ((∑ m ∈ B, (∑ q ∈ D.divisors, cCoeff q m) ^ 2) / (B.card : ℝ))) *
          (B.card : ℝ) := by
          rw [add_mul, add_mul, mul_assoc, div_mul_cancel₀ _ hBpos.ne',
            mul_assoc, div_mul_cancel₀ _ hBpos.ne']
          ring
  -- 估计主模型均方（常数界 13）
  have hQ_bound : (∑ m ∈ B, (∑ q ∈ D.divisors, cCoeff q m) ^ 2) / (B.card : ℝ) ≤ 13 := by
    let R_main := (Icc 1 k).filter (fun r => Odd r ∧ Squarefree r ∧ (r ∈ D.divisors ∨ 2 * r ∈ D.divisors))
    have h1 := band_avg_sq_sum_le h48 D.divisors hDsub
    have h2 : ∑ r ∈ R_main, (1 : ℝ) / (r.totient : ℝ) ^ 3 ≤ 3 :=
      sum_odd_sf_inv_totient_cube_le_three R_main (fun r hr =>
        ⟨(mem_filter.mp hr).2.1, (mem_filter.mp hr).2.2.1⟩)
    have h3 : 8 * (k : ℝ) ^ 4 / (B.card : ℝ) ≤ 1 := by
      have hy1 : (1 : ℝ) ≤ (y : ℝ) ^ 2 := by
        have : (3 : ℝ) ≤ y := by exact_mod_cast hy
        nlinarith
      exact herr_k4.trans ((div_le_one (by positivity)).mpr hy1)
    change (∑ m ∈ B, (∑ q ∈ D.divisors, cCoeff q m) ^ 2) / (B.card : ℝ) ≤
        4 * (∑ r ∈ R_main, 1 / (r.totient : ℝ) ^ 3) + 8 * (k : ℝ) ^ 4 / (B.card : ℝ) at h1
    linarith
  -- 估计尾项均方（49 / y²）
  have hTail_bound : (∑ m ∈ B, (∑ q ∈ S_tail, cCoeff q m) ^ 2) / (B.card : ℝ) ≤
      49 / (y : ℝ) ^ 2 := by
    let R_tail := (Icc 1 k).filter (fun r => Odd r ∧ Squarefree r ∧ (r ∈ S_tail ∨ 2 * r ∈ S_tail))
    have h1 := band_avg_sq_sum_le h48 S_tail hS_tail_sub
    have hR_tail : ∀ r ∈ R_tail, Odd r ∧ Squarefree r ∧ ∃ p ∈ r.primeFactors, y < p := by
      intro r hr
      obtain ⟨_, hodd, hsf, hor⟩ := mem_filter.mp hr
      refine ⟨hodd, hsf, ?_⟩
      by_contra hall
      push Not at hall
      have hrD : r ∣ D := by
        have hprod := Nat.prod_primeFactors_of_squarefree hsf
        rw [← hprod]
        have hsub : r.primeFactors ⊆ (Icc 2 y).filter Nat.Prime := by
          intro p hp
          have hpr := (Nat.mem_primeFactors.mp hp).1
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hpr.two_le, hall p hp⟩, hpr⟩
        exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
      rcases hor with hrS | h2rS
      · exact (mem_sdiff.mp hrS).2 (Nat.mem_divisors.mpr ⟨hrD, hDpos.ne'⟩)
      · have h2D : 2 ∣ D :=
          dvd_prod_of_mem _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, by omega⟩, Nat.prime_two⟩)
        have h2rD : 2 * r ∣ D := (Nat.coprime_two_left.mpr hodd).mul_dvd_of_dvd_of_dvd h2D hrD
        exact (mem_sdiff.mp h2rS).2 (Nat.mem_divisors.mpr ⟨h2rD, hDpos.ne'⟩)
    have h2 : ∑ r ∈ R_tail, (1 : ℝ) / (r.totient : ℝ) ^ 3 ≤ 12 / (y : ℝ) ^ 2 :=
      sum_odd_sf_tail_inv_totient_cube_le hy R_tail hR_tail
    change (∑ m ∈ B, (∑ q ∈ S_tail, cCoeff q m) ^ 2) / (B.card : ℝ) ≤
        4 * (∑ r ∈ R_tail, 1 / (r.totient : ℝ) ^ 3) + 8 * (k : ℝ) ^ 4 / (B.card : ℝ) at h1
    have h49 : 4 * (12 / (y : ℝ) ^ 2) + 1 / (y : ℝ) ^ 2 = 49 / (y : ℝ) ^ 2 := by ring
    linarith
  have h48pos : (0 : ℝ) ≤ 48 / (y : ℝ) ^ 2 := by positivity
  have hQ_scaled := mul_le_mul_of_nonneg_left hQ_bound h48pos
  have hinv_nonneg : (0 : ℝ) ≤ 1 / (y : ℝ) ^ 2 := by positivity
  have h774 : 3 / (y : ℝ) ^ 2 + 3 * (49 / (y : ℝ) ^ 2) + 48 / (y : ℝ) ^ 2 * 13 =
      774 * (1 / (y : ℝ) ^ 2) := by ring
  have h800 : 800 / (y : ℝ) ^ 2 = 800 * (1 / (y : ℝ) ^ 2) := by ring
  linarith

end

end ReflectedMeanSquareEulerTail

theorem Conjectures.Goldbach.ReflectedMeanSquareEulerTail : (by
  classical
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
  let R := fun N m : ℕ => A N m / (2*(N:ℝ)-(m:ℝ))
  let B := fun N : ℕ => (Finset.Icc N (2*N)).filter (band N)
  let avg := fun (F : Finset ℕ) (f : ℕ → ℝ) => (∑ m ∈ F, f m)/(F.card:ℝ)
  exact ∃ C : ℝ, 0 < C ∧ ∀ y : ℕ, 3 ≤ y → ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
    let P := fun m : ℕ => 2*C₂ * ∏ p ∈ m.primeFactors.filter (fun p => 2 < p ∧ p ≤ y), (1+1/((p:ℝ)-2))
    avg (B N) (fun m => (R N m-P m)^2) ≤ C/(y:ℝ)^2) := by
  classical
  dsimp only
  refine ⟨800, by norm_num, ?_⟩
  intro y hy
  obtain ⟨T, hT⟩ := ReflectedMeanSquareEulerTail.main_bound y hy
  refine ⟨T, fun N hN => ?_⟩
  simpa only [ReflectedShortProgression.normalized,
    ReflectedShortProgression.coefficient_eq_frozen] using hT N hN
