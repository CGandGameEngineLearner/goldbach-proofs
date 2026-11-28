# Wave-1 显式筛法与二进制核反射工具链说明 / Wave-1 Sieve & Binary Reflection Toolchains

**上游来源 / Source**: [`Visio-Vanitas/buchstab-switching`](https://github.com/Visio-Vanitas/buchstab-switching)（`on-dev` 分支，Lean `v4.36.0` + Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`，与本站 `lean/` 完全同构）  
**代码包目录 / Reference Bundle**: [`research/reference-proofs/buchstab-wave1/`](../reference-proofs/buchstab-wave1/README.md)  
**关联社区拆题 PR / Companion Route PR**: `explicit-sieve-analytic-inputs`（6 条 Wave-1 纯 Mathlib 引理）

---

## 1. 工具链组件与上游赛道映射 / Toolchain Mapping

| 工具编号 | 本地参考模块 | 核心功能 | 可直接加速的上游赛道 / 任务 |
| :--- | :--- | :--- | :--- |
| **`T1`** | `DyadicDefs.lean`, `DyadicProofs.lean`, `ExpLogProofs.lean` | 80-bit 偏置二进制 `Dyadic` 算术（仅用移位 `<<<`/`>>>`）、Q64 二进制 `artanh`/`log` 见证、Q64 `exp` 与 12 阶有理 Taylor `expPoly12` 界（**零 `native_decide`**） | `finite-rfc-third` (`RFC1`)、`modulus-certificates`、`explicit-major-and-ten-billion`、`deuring-heilbronn-and-25b-cert` |
| **`T2`** | `PrimeTable27000.lean`, `OddPrimeTreeData.lean`, `OddPrimeTree.lean` | `< 27,000` 全部 `2,961` 个素数的内核完备表 + 深度-6 平衡线段树 `OddPrimeTree`（$\le 12$ 步 $O(\log N)$ 查询区间素数连乘与倒数和） | `finite-rfc-third`、`series`、以及后续 `MertensPrimeSumPremise` 与 `Schoenfeld` 有限段核验 |
| **`T4(k3)`** | `MultiplicativeOmega.lean`, `ShiftedPrimes.lean`, `OneStepSwitching.lean`, `AbstractSieve.lean`, `BonferroniHybrid.lean`, `BonferroniEstimates.lean`, `BrunBlockSieve/` | 抽象 Buchstab 恒等式、Bonferroni 混合截断、Brun 分块下筛（含移除整除 $N$ 素因子的单调性）与一步切换捏紧 | **`L-goldbach-finite-weighted-sieve-two-factor-dstar` (`FR-9018`)**、`farey-inverse-sieve`、`rough-fifth-parity` |
| **`T7a`** | `MertensTwoVar.lean`, `RobinOmega/*.lean` | 无条件 Robin 素因子个数上界 $\omega(N) < 1.3841 \frac{\log N}{\log\log N}$（$N \ge 3$）及双变量闭区间 Mertens 闭合 | 通用解析数论组件（可直接支撑主弧、除数和与 `explicit-sieve-analytic-inputs`） |
| **`T8`** | `tools/interval.py`, `tools/ast_zero_float_audit.py` | 90 位十进制向外舍入库（全局 `Inexact`/`Rounded` 陷阱）、AST 零浮点/零 `math` 静态检查器及 Lean 卫生审计（另见上游完整三内核脚本 `k3/comparator/run_comparator.sh`） | `RFC1` 有限区间证书脚本审计与自动化复核 |

---

## 2. 独立复现与核验 / Independent Verification

所有参考模块均只依赖本站锁定的 Mathlib（`fc4f59e5`），**零 `sorry`、零自定义 `axiom`、零 `native_decide`**：

```sh
cd lean
lake exe cache get
bash ../research/reference-proofs/buchstab-wave1/verify.sh
```

在 `ExpLogProofs.lean` 中，对数见证引理（`checkLogDyadic_sound` / `log27000_bounds`）以显式前提 `(hln2 : (0.693147180559945 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (0.693147180559946 : ℝ))` 隔离了对 $\ln 2$ 的 $10^{-15}$ 区间依赖；后续 Wave 2 工具包（来自 `buchstab-switching` PR #5 的 `NumericalConstants`）将提供该界及 $\gamma, e^{\pm\gamma}, M_0, C_2$ 的无条件内核证明。
