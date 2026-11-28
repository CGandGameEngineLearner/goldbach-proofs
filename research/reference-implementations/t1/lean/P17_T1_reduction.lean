import Mathlib
import M8a
import T1
import T1_zeta

/-!
# P17 · 闭合 T1 的**装配步**：`T1' ⟹ T1`（机器可检）

`dg/T1.lean` 只把目标写成两个 `Prop`（`T1` 与 `T1'`），从没证明过"`T1'` 够用"。
本文件把它补上：**`DgTargetT1.T1' ⟹ DgTargetT1.T1`，常数全部显式、无 `sorry`。**

于是整个项目的剩余输入**只有一条**：`T1'`（每特征的经典误差界）。ζ 侧、修正项、常数吸收、
阈值搬运全部在这次装配里闭合。

## 装配用到的三块（都已在仓库里）

| 块 | 出处 | 内容 |
|---|---|---|
| `ap_error_of_per_character` | `dg/M8a.lean` | `hpsi + hcorr + hchi ⟹` AP 误差 `≤ 3·E n` |
| `psi_classical_error` | `dg/T1_zeta.lean` | **无条件**：`∃ C c X, ∀ x ≥ X, \|ψ x − x\| ≤ C·x·e^{−c√log x}`（来自 PNT+ 的 `StrongPNT`） |
| `E0_le_classical` | `dg/M8a.lean` | **无条件**：`3 ≤ q ≤ 105`、`x ≥ e¹⁶` 时 `E₀ ≤ x·e^{−√log x}` |

## 常数怎么合

记 ζ 侧为 `(C_ψ, c_ψ)`、每特征为 `(C_χ, c_χ)`。取

```
c := min c_ψ (min c_χ 1)        C := max C_ψ (max C_χ 1)
X := max (max X_ψ X_χ) (max 1 (e¹⁶))        E x := C·|x|·e^{−c√(log|x|)}
```

* `c ≤ c_ψ, c ≤ c_χ` ⟹ 两个指数界都被 `E` 支配（`e^{−c√L}` 更大）；
* `c ≤ 1` 专门给 `E₀` 那条：`6 log n ≤ n e^{−√log n} ≤ n e^{−c√log n}`；
* `1 ≤ C` 同理给 `E₀`；
* `X ≥ e¹⁶` 供 `E0_le_classical`；`X ≥ 1` 供 `log n ≥ 0`（`Real.exp` 的单调性要用）；
* `E` 里写 `|x|` 是为了 `hEpos : ∀ x, 0 ≤ E x`（`M8a` 要求**所有**实数，包括负的）。

最后由 `ap_error_of_per_character` 得 `≤ 3·E n = (3C)·n·e^{−c√log n}`，即 `T1` 的形状。
-/

open scoped BigOperators

namespace DgBmorP17

/-- **吸收引理**：`A ≤ Atot`、`atot ≤ a`、`x ≥ 0`、`L ≥ 0` ⟹
`A·x·e^{−a√L} ≤ Atot·x·e^{−atot√L}`。这是常数合并的全部内容。 -/
theorem mul_exp_le_of_le {A Atot a atot x L : ℝ}
    (_hA0 : 0 ≤ A) (hAtot0 : 0 ≤ Atot) (hA : A ≤ Atot) (ha : atot ≤ a)
    (hx : 0 ≤ x) (_hL : 0 ≤ L) :
    A * x * Real.exp (-(a * Real.sqrt L)) ≤ Atot * x * Real.exp (-(atot * Real.sqrt L)) := by
  have hs : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have he : Real.exp (-(a * Real.sqrt L)) ≤ Real.exp (-(atot * Real.sqrt L)) := by
    apply Real.exp_le_exp.mpr
    have h : atot * Real.sqrt L ≤ a * Real.sqrt L := mul_le_mul_of_nonneg_right ha hs
    linarith
  have hexpnn : (0 : ℝ) ≤ Real.exp (-(a * Real.sqrt L)) := (Real.exp_pos _).le
  have hexpnn' : (0 : ℝ) ≤ Real.exp (-(atot * Real.sqrt L)) := (Real.exp_pos _).le
  calc A * x * Real.exp (-(a * Real.sqrt L))
      = (A * x) * Real.exp (-(a * Real.sqrt L)) := by ring
    _ ≤ (Atot * x) * Real.exp (-(a * Real.sqrt L)) := by
        refine mul_le_mul_of_nonneg_right ?_ hexpnn
        exact mul_le_mul_of_nonneg_right hA hx
    _ ≤ (Atot * x) * Real.exp (-(atot * Real.sqrt L)) := by
        refine mul_le_mul_of_nonneg_left he ?_
        exact mul_nonneg hAtot0 hx
    _ = Atot * x * Real.exp (-(atot * Real.sqrt L)) := by ring

/-- **装配步（主定理）**：给定每特征的经典误差界（阈值 `X` 可以是正数），
则 `T1` 成立。所有常数显式。 -/
theorem T1_of_per_character
    (hchi : ∃ (C c X : ℝ), 0 < C ∧ 0 < c ∧ 0 < X ∧
      ∀ (m : ℕ) [NeZero m], 3 ≤ m → m ≤ 105 →
        ∀ χ : DirichletCharacter ℂ m, χ ≠ 1 → ∀ x : ℝ, X ≤ x →
          ‖DgBmorM8a.psiChiR χ x‖ ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x)))) :
    DgTargetT1.T1 := by
  -- ζ 侧：无条件
  obtain ⟨Cψ, cψ, Xψ, hCψ0, hcψ0, hXψ0, hpsiZ⟩ := psi_classical_error
  obtain ⟨Cχ, cχ, Xχ, hCχ0, hcχ0, hXχ0, hchiL⟩ := hchi
  -- 合并常数
  set C : ℝ := max Cψ (max Cχ 1) with hC_def
  set c : ℝ := min cψ (min cχ 1) with hc_def
  set X : ℝ := max (max Xψ Xχ) (max 1 (Real.exp 16)) with hX_def
  -- 大小关系
  have hCψ_le : Cψ ≤ C := le_max_left _ _
  have hCχ_le : Cχ ≤ C :=
    le_trans (le_max_left Cχ 1) (le_max_right Cψ (max Cχ 1))
  have h1C : (1 : ℝ) ≤ C :=
    le_trans (le_max_right Cχ 1) (le_max_right Cψ (max Cχ 1))
  have hC0 : 0 < C := lt_of_lt_of_le one_pos h1C
  have hc_le_cψ : c ≤ cψ := min_le_left _ _
  have hc_le_cχ : c ≤ cχ :=
    le_trans (min_le_right cψ (min cχ 1)) (min_le_left cχ 1)
  have hc_le_1 : c ≤ 1 :=
    le_trans (min_le_right cψ (min cχ 1)) (min_le_right cχ 1)
  have hc0 : 0 < c := lt_min hcψ0 (lt_min hcχ0 one_pos)
  have hXψ_le : Xψ ≤ X :=
    le_trans (le_max_left Xψ Xχ) (le_max_left (max Xψ Xχ) (max 1 (Real.exp 16)))
  have hXχ_le : Xχ ≤ X :=
    le_trans (le_max_right Xψ Xχ) (le_max_left (max Xψ Xχ) (max 1 (Real.exp 16)))
  have hX1 : (1 : ℝ) ≤ X :=
    le_trans (le_max_left 1 (Real.exp 16)) (le_max_right (max Xψ Xχ) (max 1 (Real.exp 16)))
  have hXe16 : Real.exp 16 ≤ X :=
    le_trans (le_max_right 1 (Real.exp 16)) (le_max_right (max Xψ Xχ) (max 1 (Real.exp 16)))
  have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
  -- 误差函数
  set E : ℝ → ℝ := fun x => C * |x| * Real.exp (-(c * Real.sqrt (Real.log |x|))) with hE_def
  have hEpos : ∀ x : ℝ, 0 ≤ E x := by
    intro x
    have h1 : (0 : ℝ) ≤ C * |x| := mul_nonneg hC0.le (abs_nonneg x)
    have h2 : (0 : ℝ) ≤ Real.exp (-(c * Real.sqrt (Real.log |x|))) := (Real.exp_pos _).le
    rw [hE_def]
    exact mul_nonneg h1 h2
  -- ζ 侧输入
  have hpsi' : ∀ x : ℝ, X ≤ x → |Chebyshev.psi x - x| ≤ E x := by
    intro x hx
    have hxX : Xψ ≤ x := le_trans hXψ_le hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hX0 hx
    have hLnn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hzx : |x| = x := abs_of_pos hx0
    have h1 := hpsiZ x hxX
    rw [hE_def]
    simp only [hzx]
    exact h1.trans (mul_exp_le_of_le hCψ0.le hC0.le hCψ_le hc_le_cψ hx0.le hLnn)
  -- 每特征输入
  have hchi' : ∀ (m : ℕ) [NeZero m], 3 ≤ m → m ≤ 105 →
      ∀ (χ : DirichletCharacter ℂ m), χ ≠ 1 → ∀ x : ℝ, X ≤ x →
        ‖DgBmorM8a.psiChiR χ x‖ ≤ E x := by
    intro m _ hm3 hm105 χ hχ x hx
    have hxX : Xχ ≤ x := le_trans hXχ_le hx
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le hX0 hx
    have hLnn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have hzx : |x| = x := abs_of_pos hx0
    have h1 := hchiL m hm3 hm105 χ hχ x hxX
    rw [hE_def]
    simp only [hzx]
    exact h1.trans (mul_exp_le_of_le hCχ0.le hC0.le hCχ_le hc_le_cχ hx0.le hLnn)
  -- 修正项输入（无条件）
  have hcorr' : ∀ (m n : ℕ), 3 ≤ m → m ≤ 105 → ⌈X⌉₊ ≤ n → DgBmorM8a.E0 m n ≤ E n := by
    intro m n hm3 hm105 hXn
    have hnR : X ≤ (n : ℝ) := Nat.ceil_le.mp hXn
    have hne16 : Real.exp 16 ≤ (n : ℝ) := le_trans hXe16 hnR
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := le_trans hX1 hnR
    have hLnn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
    have h1 := DgBmorM8a.E0_le_classical m n hm3 hm105 hne16
    have h2 : (n : ℝ) * Real.exp (-(Real.sqrt (Real.log (n : ℝ))))
        ≤ E (n : ℝ) := by
      have h3 : (1 : ℝ) * (n : ℝ) * Real.exp (-((1 : ℝ) * Real.sqrt (Real.log (n : ℝ))))
          ≤ C * (n : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n : ℝ)))) :=
        mul_exp_le_of_le zero_le_one hC0.le h1C hc_le_1 (Nat.cast_nonneg n) hLnn
      rw [hE_def]
      simpa using h3
    linarith
  -- 主装配
  refine ⟨3 * C, c, X, by positivity, hc0, hX0, ?_⟩
  intro q a n hq hq105 ha hcop hXn
  have hmain := DgBmorM8a.ap_error_of_per_character E X hEpos hpsi' hcorr' hchi'
    q a n hq hq105 ha hcop hXn
  have hEeq : E (n : ℝ) = C * (n : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n : ℝ)))) := by
    rw [hE_def]
    simp only [Nat.abs_cast]
  calc |(∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = a % q),
        (ArithmeticFunction.vonMangoldt k : ℝ)) - (n : ℝ) / (Nat.totient q : ℝ)|
      ≤ 3 * E (n : ℝ) := hmain
    _ = 3 * C * (n : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n : ℝ)))) := by
        rw [hEeq]; ring

/-- **主定理**：`T1' ⟹ T1`（`T1.lean` 里的两个 `Prop` 之间第一次被机器验证的蕴含）。 -/
theorem T1_of_T1' (h : DgTargetT1.T1') : DgTargetT1.T1 := by
  obtain ⟨C, c, X, hC, hc, hX, hb⟩ := h
  refine T1_of_per_character ⟨C, c, X, hC, hc, hX, ?_⟩
  intro m _ hm3 hm105 χ hχ x hx
  have hEq : DgTargetT1.psiChiR χ x = DgBmorM8a.psiChiR χ x := rfl
  rw [← hEq]
  exact hb m hm3 hm105 χ hχ x hx

end DgBmorP17
