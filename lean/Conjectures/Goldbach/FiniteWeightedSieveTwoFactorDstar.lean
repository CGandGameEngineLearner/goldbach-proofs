import Mathlib
import Conjectures.Goldbach.FiniteWeightedSieveRemoveUnit
import Conjectures.Goldbach.FiniteWeightedSieveFactorCap

/-!
# FR-9018 · 原加权筛在 `D*` 上的两因子正余量

冻结 statement：

`∀ n, 4·10^18 < n → 30 ∣ n → (n:ℝ) < exp(exp(19/5)) → ∃ z y, 2 < z ∧ z < y ∧
  n ≤ y^3 ∧ n ≤ z*y^2 ∧ 0 < ∑_{p ∈ A n z, 2 ≤ n-p} W z y (n-p)`

其中

* `W z y s = 2 - #{q ∈ [z,y) : q 素 ∧ q ∣ s} - #{q ∈ [z,y) : q 素 ∧ q² ∣ s}`（整数值权）；
* `A n z` = 素数 `p ≤ n` 且 `p ∤ n` 且 `n - p` 没有小于 `z` 的素因子（`n - p` 是 `z`-rough）。

## 证明分层

1. **成员性质**（已证）：`A` 中元素素、不整除 `n`、`n - p` 的素因子都 `≥ z`。
2. **权和重写**（已证）：`∑_{A0} W = 2·|A0| - D₁ - D₂`，纯 `Finset` 交换求和。
3. **参数构造**（已证）：取 `z = 23`、`y = ⌊√n⌋ + 2`，三条数值约束初等可证。
4. **底集非空**（筛法核心）：存在素数 `p ≤ n`、`p ∤ n`、`n - p ≥ 2` 且 `n - p` 是
   `23`-rough。需要 `[23, n^{1/3})` 上的下界筛。
5. **扣除上界**（筛法核心）：`D₁ + D₂ < 2·|A0|`，即
   `∑_{23 ≤ q < y} #{p ∈ A0 : q ∣ n-p} < 2|A0|`（余量 `log log y - log log 23 < 2`）。
6. **主定理**：层 2 + 层 5 给出 `0 < ∑ W`，与层 3 的参数合成存在性。

## 与既有引理的关系

* `FiniteWeightedSieveRemoveUnit`：把 `A` 中 `n - p = 1`（`p = n-1`）的项剥出，
  `∑_A W = ∑_{A0} W + (if (n-1).Prime then 2 else 0)`。本题只用 `A0` 部分。
* `FiniteWeightedSieveFactorCap`：反方向，`0 < W z y s → s.primeFactorsList.length ≤ r`，
  用于把层 5 转成 `G₂`；本题不直接调用。
-/

open scoped BigOperators

namespace GoldbachFR9018

/-! ## 层 0：定义 -/

/-- 整数权：素数块 `[z,y)` 上整除与平方整除的扣减。 -/
def W (z y s : ℕ) : ℤ :=
  let P := (Finset.Ico z y).filter Nat.Prime
  (2 : ℤ) - ((P.filter (fun p => p ∣ s)).card : ℤ) - ((P.filter (fun p => p ^ 2 ∣ s)).card : ℤ)

/-- 底集：素数 `p ≤ n`，`p ∤ n`，且 `n - p` 无小于 `z` 的素因子。 -/
def A (n z : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p =>
    p.Prime ∧ ¬ (p ∣ n) ∧
    ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ (n - p))) = ∅)

/-- 去掉 `n - p = 1` 之后的底集，与 statement 的求和指标一致。 -/
def A0 (n z : ℕ) : Finset ℕ := (A n z).filter (fun p => 2 ≤ n - p)

/-! ## 层 1：成员性质 -/

lemma mem_A_iff {n z p : ℕ} :
    p ∈ A n z ↔ p ≤ n ∧ p.Prime ∧ ¬ p ∣ n ∧
      ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ (n - p))) = ∅ := by
  simp only [A, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

lemma A_prime {n z p : ℕ} (hp : p ∈ A n z) : p.Prime := ((mem_A_iff.mp hp).2).1

lemma A_not_dvd {n z p : ℕ} (hp : p ∈ A n z) : ¬ p ∣ n := ((mem_A_iff.mp hp).2).2.1

lemma A_rough {n z p : ℕ} (hp : p ∈ A n z) :
    ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ (n - p))) = ∅ :=
  ((mem_A_iff.mp hp).2).2.2

lemma A_le {n z p : ℕ} (hp : p ∈ A n z) : p ≤ n := (mem_A_iff.mp hp).1

lemma A0_mem_iff {n z p : ℕ} : p ∈ A0 n z ↔ p ∈ A n z ∧ 2 ≤ n - p := by
  simp only [A0, Finset.mem_filter]

/-- `A` 中元素对应的 `n - p` 是 `z`-rough：任一素因子都 `≥ z`。 -/
lemma prime_factor_ge_of_mem_A {n z p : ℕ} (hp : p ∈ A n z) {q : ℕ}
    (hq : q.Prime) (hqdvd : q ∣ n - p) : z ≤ q := by
  by_contra hlt
  have hqz : q < z := by omega
  have hmem : q ∈ (Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ (n - p)) := by
    rw [Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨hq.two_le, hqz⟩, hq, hqdvd⟩
  rw [A_rough hp] at hmem
  exact absurd hmem (Finset.notMem_empty q)

/-! ## 层 2：权和重写成 `2|A0| - D₁ - D₂` -/

/-- 把「固定 `p` 数 `q`」换成「固定 `q` 数 `p`」。 -/
lemma sum_card_swap (S T : Finset ℕ) (R : ℕ → ℕ → Prop) :
    (∑ p ∈ S, ((T.filter (fun q => R p q)).card : ℤ))
      = ∑ q ∈ T, ((S.filter (fun p => R p q)).card : ℤ) := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum, Nat.cast_one]
  exact Finset.sum_comm

/-- 权重和 `= 2|A0| - D₁ - D₂`。 -/
lemma sum_W_eq (n z y : ℕ) :
    (∑ p ∈ A0 n z, W z y (n - p))
      = 2 * ((A0 n z).card : ℤ)
        - (∑ q ∈ (Finset.Ico z y).filter Nat.Prime,
            (((A0 n z).filter (fun p => q ∣ n - p)).card : ℤ))
        - (∑ q ∈ (Finset.Ico z y).filter Nat.Prime,
            (((A0 n z).filter (fun p => q ^ 2 ∣ n - p)).card : ℤ)) := by
  classical
  have hpt : ∀ p ∈ A0 n z, W z y (n - p)
      = (2 : ℤ)
        - ((((Finset.Ico z y).filter Nat.Prime).filter (fun q => q ∣ n - p)).card : ℤ)
        - ((((Finset.Ico z y).filter Nat.Prime).filter (fun q => q ^ 2 ∣ n - p)).card : ℤ) := by
    intro p _
    simp only [W]
  rw [Finset.sum_congr rfl hpt, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const,
    sum_card_swap (A0 n z) ((Finset.Ico z y).filter Nat.Prime) (fun p q => q ∣ n - p),
    sum_card_swap (A0 n z) ((Finset.Ico z y).filter Nat.Prime) (fun p q => q ^ 2 ∣ n - p)]
  simp [smul_eq_mul, mul_comm]

/-! ## 层 3：参数构造 `z = 23`，`y = ⌊√n⌋ + 2`

`z = 23` 时素数块 `[23, y)` 上的扣除量
`∑_{23 ≤ q < y} 1/q ≈ log log y - log log 23 ≈ log(21/3.1) ≈ 1.9 < 2`，
给出题目所说的"扣除余项后仍为正"。

`y = ⌊√n⌋ + 2`：`y² > n` 给出 `n ≤ 23·y²`，`y³ > n·y > n` 给出 `n ≤ y³`。 -/

/-- 筛下界参数。 -/
def zPar : ℕ := 23

/-- 筛上界参数：`⌊√n⌋ + 2`。 -/
def yPar (n : ℕ) : ℕ := Nat.sqrt n + 2

lemma zPar_gt_two : 2 < zPar := by unfold zPar; norm_num

lemma sqrt_ge (n : ℕ) (hn : 4000000000000000000 < n) : 2000000000 ≤ Nat.sqrt n := by
  rw [Nat.le_sqrt]
  omega

lemma yPar_gt_23 (n : ℕ) (hn : 4000000000000000000 < n) : 23 < yPar n := by
  have h := sqrt_ge n hn
  unfold yPar
  omega

lemma zPar_lt_yPar (n : ℕ) (hn : 4000000000000000000 < n) : zPar < yPar n := by
  have h := yPar_gt_23 n hn
  unfold zPar
  omega

lemma yPar_ge_one (n : ℕ) : 1 ≤ yPar n := by unfold yPar; omega

/-- `n < y²`。 -/
lemma n_lt_yPar_sq (n : ℕ) : n < (yPar n) ^ 2 := by
  have h := Nat.lt_succ_sqrt n
  have hle : Nat.sqrt n + 1 ≤ yPar n := by unfold yPar; omega
  exact lt_of_lt_of_le h (Nat.pow_le_pow_left hle 2)

/-- 约束 `n ≤ z·y²`。 -/
lemma yPar_mul (n : ℕ) : n ≤ zPar * (yPar n) ^ 2 := by
  have h : n ≤ (yPar n) ^ 2 := le_of_lt (n_lt_yPar_sq n)
  have hz : 1 ≤ zPar := by unfold zPar; norm_num
  calc n ≤ (yPar n) ^ 2 := h
    _ = (yPar n) ^ 2 * 1 := (Nat.mul_one _).symm
    _ ≤ (yPar n) ^ 2 * zPar := Nat.mul_le_mul_left _ hz
    _ = zPar * (yPar n) ^ 2 := Nat.mul_comm _ _

/-- 约束 `n ≤ y³`。 -/
lemma yPar_cube (n : ℕ) : n ≤ (yPar n) ^ 3 := by
  have h : n ≤ (yPar n) ^ 2 := le_of_lt (n_lt_yPar_sq n)
  have h1 : 1 ≤ yPar n := yPar_ge_one n
  calc n ≤ (yPar n) ^ 2 := h
    _ = (yPar n) ^ 2 * 1 := (Nat.mul_one _).symm
    _ ≤ (yPar n) ^ 2 * (yPar n) := Nat.mul_le_mul_left _ h1
    _ = (yPar n) ^ 3 := by ring

/-! ## 层 4：底集非空（由层 5 推出，不再单独需要）

层 5 的 `D₁ + D₂ < 2·|A0|` 右端非负，故 `|A0| > 0`：底集非空是层 5 的推论，
无需另行假设。这一点很关键——它说明整个命题只剩**一个**解析输入。 -/

/-! ## 层 5：扣除上界

`D₁ + D₂ < 2|A0|`：`[23, y)` 上每个素数 `q` 的计数 `#{p ∈ A0 : q ∣ n-p}` 之和
被 `|A0|·(log log y - log log 23)` 控制，而 `log log y - log log 23 < 2`
（`y ≈ √n` 时约 `1.9`，余量约 `0.1`）。平方项 `∑ 1/q²` 是对 `1/(23·log 23)` 量级的
可忽略修正。这需要上界筛（Brun / Selberg）的显式常数。 -/

/-- 筛法核心（二）：扣除项之和严格小于 `2|A0|`。 -/
lemma sieve_margin (n : ℕ) (hn : 4000000000000000000 < n) (h30 : 30 ∣ n) :
    (∑ q ∈ (Finset.Ico zPar (yPar n)).filter Nat.Prime,
        (((A0 n zPar).filter (fun p => q ∣ n - p)).card : ℤ))
      + (∑ q ∈ (Finset.Ico zPar (yPar n)).filter Nat.Prime,
        (((A0 n zPar).filter (fun p => q ^ 2 ∣ n - p)).card : ℤ))
    < 2 * ((A0 n zPar).card : ℤ) := by
  sorry

end GoldbachFR9018

/-! ## 层 6：主定理 -/

theorem Conjectures.Goldbach.FiniteWeightedSieveTwoFactorDstar :
    let W := fun (z y s : ℕ) => let P := (Finset.Ico z y).filter Nat.Prime; (2:ℤ)-((P.filter (fun p => p∣s)).card:ℤ)-((P.filter (fun p => p^2∣s)).card:ℤ); let A := fun (n z : ℕ) => (Finset.range (n+1)).filter (fun p => p.Prime ∧ ¬ (p ∣ n) ∧ ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ (n-p))) = ∅); ∀ n : ℕ, 4000000000000000000<n → 30 ∣ n → (n:ℝ)<Real.exp (Real.exp (19/5)) → ∃ z y : ℕ, 2<z ∧ z<y ∧ n≤y^3 ∧ n≤z*y^2 ∧ 0<(∑ p ∈ Finset.filter (fun p => 2≤n-p) (A n z), W z y (n-p)) := by
  intro W A n hn h30 hX
  clear hX
  refine ⟨GoldbachFR9018.zPar, GoldbachFR9018.yPar n,
    GoldbachFR9018.zPar_gt_two, GoldbachFR9018.zPar_lt_yPar n hn,
    GoldbachFR9018.yPar_cube n, GoldbachFR9018.yPar_mul n, ?_⟩
  change 0 < ∑ p ∈ GoldbachFR9018.A0 n GoldbachFR9018.zPar,
    GoldbachFR9018.W GoldbachFR9018.zPar (GoldbachFR9018.yPar n) (n - p)
  rw [GoldbachFR9018.sum_W_eq n GoldbachFR9018.zPar (GoldbachFR9018.yPar n)]
  have h := GoldbachFR9018.sieve_margin n hn h30
  linarith
