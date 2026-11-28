import Mathlib

/-!
# 目标 T1（正式陈述，机器可检）：无条件、经典误差形状的显式 PNT-in-AP

## 背景（见 `PLAN.md` §0）

冻结陈述（`1/3360`、`n ≥ 8·10⁹`）在现有 Mathlib 生态下不可达（M6 的 certified numerics 缺口，
见 §5.3），因此**正式目标改为 T1**：无条件、误差形状放宽为 `C·x·exp(−c√log x)`。

本文件只**陈述**目标（`def … : Prop`），不证明。它把「项目到底在追什么」变成机器可检的对象，
避免后续工作优化到错误的目标形状上。

## 关系

- `T1'`（每特征 `‖ψ_χ(x)‖ ≤ C x exp(−c√log x)`）是 T1 的**充分输入**：
  加上显式 PNT（`|ψ(x) − x| ≤ E x`）与已证的 `E₀` 修正（`M3c.E0_le_budget` 的 `E` 版本），
  经 M4b 的装配（`E`-抽象版本）即得 T1。
- 冻结陈述则是 T1 在 `E x = x/(3360 log x)`、`X = 8·10⁹` 处的特化，且**不能**由 T1 推出
  （两者的 `X` 门槛差若干个数量级：`exp(−c√log x)` 要压到 `1/(3360 log x)` 需要 `x ≳ e^{3000}`）。
-/

open scoped BigOperators

namespace DgTargetT1

variable {q : ℕ} [NeZero q]

/-- `ψ_χ(x) = Σ_{k ≤ x} χ(k)Λ(k)`（自 `dg/M4.lean` 复制的同名定义）。 -/
noncomputable def psiChiR (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (⌊x⌋₊ + 1), χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)

/-- **T1（主目标）**：无条件、经典误差形状的显式 PNT-in-AP。 -/
def T1 : Prop :=
  ∃ (C c X : ℝ), 0 < C ∧ 0 < c ∧ 0 < X ∧
    ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → ⌈X⌉₊ ≤ n →
      |(∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = a % q),
          ArithmeticFunction.vonMangoldt k)
        - (n : ℝ) / (Nat.totient q : ℝ)|
        ≤ C * (n : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (n : ℝ))))

/-- **T1'（每特征输入）**：T1 的充分条件——M4b `hchi` 的经典误差版本。 -/
def T1' : Prop :=
  ∃ (C c X : ℝ), 0 < C ∧ 0 < c ∧ 0 < X ∧
    ∀ (m : ℕ) [NeZero m], 3 ≤ m → m ≤ 105 →
      ∀ χ : DirichletCharacter ℂ m, χ ≠ 1 → ∀ x : ℝ, X ≤ x →
        ‖psiChiR χ x‖ ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x)))

end DgTargetT1
