# T1 reference implementation（参考实现，非提交物）

本目录是 PR #4032 所说的"解析部分已被机器闭合"的**参考实现**：把
`L-goldbach-fixed-ap-bmor-classical`（BMOR 特化的经典误差形状）在本仓环境
（Lean `v4.36.0` + 本仓锁定的 Mathlib）里证完的完整依赖树。

> ⚠️ 这是**参考实现**，不是按"单文件 ≤ 2 MiB"规则整理过的提交物。

## 两种形态

| 形态 | 路径 | 状态 |
|---|---|---|
| **A. 多模块树**（权威） | `vendor/` + `lean/`（656 个文件 / 1.61 MB） | ✅ **730/730 模块全部编译**（本仓 4.36.0 环境） |
| **B. 单文件 bundle** | `T1SingleFile.lean`（2.66 MiB，auto-assembled） | ⚠️ **尚未编过**：机械拼接后有 **93 处**（82 条不同）elaboration 差异，见下 |

### B 的做法与残留问题（诚实记录）

`T1SingleFile.lean` 是把 730 个模块按**拓扑序**拼接：去掉每块的 `module`/`import`/`public section`
头，每块包在 `section … end` 里（这样 `open`/`variable` 不泄漏），顶部只留 `import Mathlib`。

编译（18 分钟一轮）后残留 **93 条错误 / 82 类**，全部是**全局副作用泄漏**，不是数学问题：

| 类 | 条数 | 原因 |
|---|---|---|
| `tauto` failed | 12 | 上文的 `instance`/`attribute` 泄漏改变了假设集与 simp 集 |
| unsolved goals | 9 | 同上（局部 `simp` 现在更能/更少地关闭目标） |
| Ambiguous term | 8 | 多块同时 `open Finset` 与 `open Set`，`insert_Icc_add_one_left_eq_Icc` 等出现双解 |
| Application type mismatch | 8 | 隐式参数解析受泄漏实例影响 |
| heartbeat timeout | 9 | 单文件上下文过大（whnf/isDefEq） |
| `rewrite` pattern not found / linarith / positivity / mod_cast | 24 | simp 引理库与 norm_num 行为被跨块改变 |

**结论**：单文件**不是**忠实可拼接的——多模块的 `attribute`、`instance`、`@[simp]` 注册是全局的、
不会随 `section` 回收，所以拼接会改变后续块的 elaboration。要收敛这 82 类需要逐点修补，
且每轮编译 18 分钟；本 PR 不做这件事。**形态 A 是权威、可复编的版本。**

## 主定理

```lean
theorem DgBmorP33.T1_discharged : DgTargetT1.T1 :=
  DgBmorP17.T1_of_per_character DgBmorP33.per_character_siegelWalfisz
-- #print axioms DgBmorP33.T1_discharged
--   'DgBmorP33.T1_discharged' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`DgTargetT1.T1`：存在 `C c X > 0`，使 `3 ≤ q ≤ 105`、`a < q`、`Coprime a q`、`⌈X⌉₊ ≤ n` 时
`|Σ_{k≤n, k≡a (q)} Λ k − n/φ(q)| ≤ C·n·exp(−c·√(log n))`。

## 依赖（三层）

1. **本项目装配层**（`lean/`，5 个文件）：`P33_sw_implies_hchi.lean`、`P17_T1_reduction.lean`
   （`T1' ⟹ T1`：ζ 侧用 PNT+ 的 `StrongPNT`，修正项 `E₀ ≤ 6 log n`，常数合并全显式）、
   `M8a.lean`、`T1.lean`、`T1_zeta.lean`。
2. **Siegel–Walfisz 形式化**（`vendor/bv/`）：来自
   [`kimihiro64/bombieri-vinogradov`](https://github.com/kimihiro64/bombieri-vinogradov)（Apache-2.0），
   从 Lean `v4.33.1` 移植到 `v4.36.0`；关键定理
   `BombieriVinogradov.SiegelWalfisz.siegel_walfisz`。`vendor/bv/extra/` 是从作者 fork 与
   `Robin1984` 取来、或本地重写的模块。
3. **PNT+**（`vendor/pnt-work/`，只含我们**新增**的 2 个文件）：`Tactic/AdditiveCombination.lean`
   （本地重写，只依赖 `Mathlib.Tactic.Abel`）、`Mathlib/NumberTheory/LSeries/RiemannXiDivisorZeros.lean`。

## 重编（形态 A）

```powershell
$env:PATH = "E:\ai-math\toolchains\lean-4.36.0-windows\bin;" + $env:PATH
# LEAN_PATH = 本仓 Mathlib oleans + vendor/pnt-work/{src,lib} + vendor/bv/{src,extra} + lean 的 oleans
lean.exe -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 `
         -DmaxHeartbeats=4000000 -DmaxRecDepth=10000 -o <file>.olean <file>.lean
```

移植中修掉的 10 类 API 漂移（含"本快照里 `Set` 是 structure"这一最大类）见 `PORT_NOTES.md`。

## 许可证

`vendor/bv/**` 与 `vendor/bv/extra/**` 来自 Apache-2.0 的 `kimihiro64/bombieri-vinogradov`
（含其 `LICENSE`），改动仅为 API 适配；`vendor/pnt-work/**` 中的 2 个文件来自 Apache-2.0 的
`PrimeNumberTheoremAnd` 或本地重写。本目录其余文件（`lean/`、`T1SingleFile.lean`、`README.md`、
`PORT_NOTES.md`）与本仓库其他内容同许可。

## 状态与保留

* 形态 A 的 730 个模块全部编译；**尚未做从零全量重编**（olean 均新于源文件，但未清空重来）。
* 冻结题 `L-goldbach-fixed-ap-bmor-psi`（`1/840`、`n ≥ 8·10⁹`）**仍然不可达**：需约 `5.3·10⁹`
  条零点位置的数值证书，信息量下界是 2 MiB 的 ~313 倍（见 #3817、#3914）。
  本 PR 只主张"解析部分已拆封"。
