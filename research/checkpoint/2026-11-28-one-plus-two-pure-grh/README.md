# 纯 GRH 下的高区显式 1+2 射线 · 上游固定快照与独立复核指南

**提交者**　千早爱音（[Visio-Vanitas](https://github.com/Visio-Vanitas)）。[中间命题提交稿](proof.md)

本目录提交纯 GRH 下高区显式 `1+2`（陈氏定理）射线与无条件筛法内核成果的上游固定版本索引及复现命令，供仓库维护者与同行独立复核。本分支**完全不含任何超越 $\sqrt{N}$ 分布或亚 $\sqrt{N}$ 模抵消猜想**，且零 `native_decide`。本提交**不包含自证结论**；所有 90 位区间证书、Lean 4 编译、公理白名单、三内核 `comparator` 导出及显式声明的解析前提接口均以维护者独立重放和数学审定结果为准。

---

## 1. 上游仓库与固定版本信息

- **上游仓库**：[`https://github.com/Visio-Vanitas/buchstab-switching`](https://github.com/Visio-Vanitas/buchstab-switching)（分支 `feat/k2-pure-grh-v436`，子目录 `k2/`）
- **固定提交 SHA**：[`f197b0557bbec1c1e87b3bf4827df6a26e72dfc1`](https://github.com/Visio-Vanitas/buchstab-switching/tree/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2)（基于已对齐 `v4.36.0` 的父提交 `4b30430bd556fdaa8cfae00b7bcc285eae469d60`）
- **Lean 工具链与依赖锁**（与 `goldbach-proofs` 生产工具链逐字对齐）：
  - [`k2/lean-toolchain`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/lean-toolchain)：`leanprover/lean4:v4.36.0`
  - [`k2/lake-manifest.json`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/lake-manifest.json)：Mathlib `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`
  - **公理约束**：全库零 `sorry`（`Challenge.lean` 与 `comparator/ChallengeK2Reduction.lean` 挑战签名文件除外）、零自定义 `axiom`、零 `native_decide`，仅依赖 `[propext, Classical.choice, Quot.sound]`（可判定 `RayCert.valid` 检验仅依赖 `[propext]`）。
- **GRH 声明对齐目标**：[`k2/Challenge.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/Challenge.lean) 与 [`k2/BuchstabSwitchingK2/External/CitedPremisesK2.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/External/CitedPremisesK2.lean) 中的 `DirichletLNonvanishingRightOfHalf` 与 [`lsernau/grh-lean@72fead102f663d5c7a407964a13dc0cf9d977207`](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Statements.lean) 逐字对应，并由 [`k2/AxiomsCheckK2.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/AxiomsCheckK2.lean) 通过 5 条 `Iff.rfl` 检查定义一致。

### 关键存档文件 SHA-256（以 `git clone -c core.autocrlf=false` 检出为准）

| 相对路径 | SHA-256 | 说明 |
|---|---|---|
| [`k2/scripts/certify_pure_grh_1p2.py`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/scripts/certify_pure_grh_1p2.py) | `e426cf8d5ec0bfdac7aebfdd5b796a5b42e20a66e867262fa7ea3f0b002a24d3` | 90 位零浮点向外区间认证脚本（保守 Parzen 常权、变权与二次 LP） |
| [`k2/scripts/data/certified_pure_grh_frontier.json`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/scripts/data/certified_pure_grh_frontier.json) | `64342df758a53a637cc9eb63cd0ad892750cc3978a76e9b8b024458b81443ded` | 保守 `Parzen`（`10^390` / `10^320` / `10^316`）前沿证书数据 |
| [`k2/scripts/data/pure_grh_quad_lp_witness.json`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/scripts/data/pure_grh_quad_lp_witness.json) | `8ef7e90b0de4bdb9cea444d49a9f78a55ce359f0591d7f6a9c49fc3c286e4afe` | 18 条带精确有理数变权与二次切换 LP 权重见证 |
| [`k2/BuchstabSwitchingK2/PureGRHShowcaseK2.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/PureGRHShowcaseK2.lean) | `d88545879fae814c2d738e5f38abe0e6a41d4545234fe5010266575e849ff988` | 纯 GRH 切换引擎、`RayCert` 与顶层射线定理 |
| [`k2/AxiomsCheckK2.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/AxiomsCheckK2.lean) | `cc3dd296687c013fb012ef720f33075acdf1dbc746eccc0c43dbc1f2c069419f` | 全套公理白名单与 `Challenge.lean` 定义一致检查 |

---

## 2. 供维护者独立执行的复核命令（POSIX shell）

```sh
git clone -c core.autocrlf=false https://github.com/Visio-Vanitas/buchstab-switching.git
cd buchstab-switching
git fetch origin f197b0557bbec1c1e87b3bf4827df6a26e72dfc1
git checkout --detach FETCH_HEAD

cd k2

# 1. 快速审计（AST 零浮点/零 math 检查、B1/B2 零泄漏扫描、JSON 与 Lean RayCert 逐字一致、全库零 sorry/axiom/native_decide）
python3 -I scripts/quick_verify.py

# 2. 重新运行 90 位向外有向区间算术与全多重集精确 Fraction 认证（可选）
python3 -I scripts/certify_pure_grh_1p2.py

# 3. Lean 4.36.0 独立编译与公理白名单检查
lake exe cache get
lake build Challenge BuchstabSwitchingK2
lake env lean AxiomsCheckK2.lean

# 4. Comparator 独立多内核导出核验（需环境已安装 comparator / leanchecker-paranoid / nanoda_bin）
bash comparator/run_comparator.sh
```

---

## 3. 核心源码与审计入口索引

- **总览文档**：[`k2/README.md`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/README.md)
- **纯 GRH 顶层定理与三套切换引擎**：[`k2/BuchstabSwitchingK2/PureGRHShowcaseK2.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/PureGRHShowcaseK2.lean)
- **组合切换、权迁移与奇偶障碍定理**：
  - [`k2/BuchstabSwitchingK2/Sieve/RealToRatBridge.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/Sieve/RealToRatBridge.lean)（含 `Barriers.adversarial_*_balance_nonpos`）
  - [`k2/BuchstabSwitchingK2/Sieve/WeightedSmoothedSwitching.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/Sieve/WeightedSmoothedSwitching.lean)
  - [`k2/BuchstabSwitchingK2/Sieve/WeightedQuadraticSwitching.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/Sieve/WeightedQuadraticSwitching.lean)
- **GRH 等价性与 1D 本原特征围道归约**：[`k2/BuchstabSwitchingK2/External/CitedPremisesK2.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/External/CitedPremisesK2.lean)
- **Comparator 归约挑战与参考日志**：[`k2/comparator/ChallengeK2Reduction.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/comparator/ChallengeK2Reduction.lean) · [`k2/comparator/run_comparator.sh`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/comparator/run_comparator.sh) · [`k2/comparator_output.txt`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/comparator_output.txt)
