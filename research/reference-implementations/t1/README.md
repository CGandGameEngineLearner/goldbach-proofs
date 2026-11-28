# T1 reference implementation（参考实现，非提交物）

本目录是 PR #4032 所说的"解析部分已被机器闭合"的**参考实现**：把
`L-goldbach-fixed-ap-bmor-classical`（BMOR 特化的经典误差形状）在本仓库环境
（Lean `v4.36.0` + 本仓锁定的 Mathlib）里证完的完整依赖树。

> ⚠️ 这是**参考实现**，不是按"单文件 ≤ 2 MiB"规则整理过的提交物：
> 完整依赖闭包是 **730 个模块 / 2.87 MiB 源码**（2 MiB 上限的 1.44 倍）。
> 放在这里是为了让 reviewer 能实际重编、审计公理；如果维护者只想要任务条目，
> 本目录可以整体删除，保留 `research/problems/.../L-goldbach-fixed-ap-bmor-classical.json` 即可。

## 主定理

```lean
theorem DgBmorP33.T1_discharged : DgTargetT1.T1 :=
  DgBmorP17.T1_of_per_character DgBmorP33.per_character_siegelWalfisz
-- #print axioms DgBmorP33.T1_discharged
--   'DgBmorP33.T1_discharged' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`DgTargetT1.T1` 即 `lean/T1.lean` 里的形状：存在 `C c X > 0`，使
`3 ≤ q ≤ 105`、`a < q`、`Coprime a q`、`⌈X⌉₊ ≤ n` 时
`|Σ_{k≤n, k≡a (q)} Λ k − n/φ(q)| ≤ C·n·exp(−c·√(log n))`。

## 依赖（三层）

1. **本项目装配层**（`lean/`，5 个文件）：
   `P33_sw_implies_hchi.lean`（把每特征 Siegel–Walfisz 接到 `T1`）、`P17_T1_reduction.lean`
   （`T1' ⟹ T1`：ζ 侧用 PNT+ 的 `StrongPNT`，修正项 `E₀ ≤ 6 log n`，常数合并全显式）、
   `M8a.lean`、`T1.lean`、`T1_zeta.lean`。
2. **Siegel–Walfisz 形式化**（`vendor/bv/`）：来自
   [`kimihiro64/bombieri-vinogradov`](https://github.com/kimihiro64/bombieri-vinogradov)
   （Apache-2.0），我们把它从 Lean `v4.33.1` 移植到 `v4.36.0`。
   关键定理：`BombieriVinogradov.SiegelWalfisz.siegel_walfisz`（每特征
   `‖Σ_{n≤x} χ(n)Λ(n)‖ ≤ C·x·exp(−a√log x)`，模数 `N ≤ (log x)^A`）。
   子目录 `vendor/bv/extra/` 是从作者 fork 与 `Robin1984` 取来、或本地重写的两个模块。
3. **PNT+**（`vendor/pnt-work/`，只含我们**新增**的 2 个文件；其余请用
   [`PrimeNumberTheoremAnd`](https://github.com/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd)
   在当前 Mathlib 上编译得到的 olean）：
   `Tactic/AdditiveCombination.lean`（本地重写，只依赖 `Mathlib.Tactic.Abel`）、
   `Mathlib/NumberTheory/LSeries/RiemannXiDivisorZeros.lean`。

## 重编（按依赖序，或用固定点迭代）

```powershell
$env:PATH = "E:\ai-math\toolchains\lean-4.36.0-windows\bin;" + $env:PATH
# LEAN_PATH = 本仓 Mathlib oleans + vendor/pnt-work/{src,lib} + vendor/bv/{src,extra} + lean 的 oleans
lean.exe -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 `
         -DmaxHeartbeats=4000000 -DmaxRecDepth=10000 -o <file>.olean <file>.lean
```

移植过程中修掉的 10 类 API 漂移（含"本快照里 `Set` 是 structure"这一最大类）见
`PORT_NOTES.md`。

## 许可证

`vendor/bv/**` 与 `vendor/bv/extra/**` 来自 Apache-2.0 的
`kimihiro64/bombieri-vinogradov`（含其 `LICENSE`），改动仅为 API 适配；
`vendor/pnt-work/**` 中的 2 个文件来自 Apache-2.0 的 `PrimeNumberTheoremAnd` 或本地重写。
本目录其余文件（`lean/`、`README.md`、`PORT_NOTES.md`）与本仓库其他内容同许可。

## 状态与保留

* 全部 olean 均新于源文件；**尚未做从零全量重编**（干净环境下需按依赖序全量编译一遍）。
* 冻结题 `L-goldbach-fixed-ap-bmor-psi`（`1/840`、`n ≥ 8·10⁹`）**仍然不可达**：
  它需要约 `5.3·10⁹` 条零点位置的数值证书，信息量下界是 2 MiB 的 ~313 倍
  （见 Discussion #3817 与 #3914 的独立评估）。本 PR 只主张"解析部分已拆封"。
