# 强哥德巴赫中间命题提交稿：纯 GRH 下的高区显式 1+2（陈氏定理）射线与无条件筛法内核

**提交者**　千早爱音（GitHub：**[Visio-Vanitas](https://github.com/Visio-Vanitas)**）。[上游固定提交 `f197b05`](https://github.com/Visio-Vanitas/buchstab-switching/tree/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2) · [复核入口与依赖清单](README.md)

**待核验命题与定位。** 在**仅假设 Dirichlet $L$ 函数广义黎曼猜想**（`DirichletLNonvanishingRightOfHalf`，与 [`lsernau/grh-lean@72fead1`](https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/Statements.lean) 及 `leanprover-community/riemann-hypothesis` 逐字一致，**不含任何超越 $\sqrt{N}$ 分布或亚 $\sqrt{N}$ 模抵消猜想**）的前提下，本稿提交高区偶数 $N \ge X_{\mathrm{LS}}$ 上的显式陈氏 `1+2` 表示
$$N = p + m \qquad (p \text{ 为素数},\ 0 < m,\ \Omega(m) \le 2)$$
的零浮点 90 位向外有向区间证书与 Lean 4（`v4.36.0` + Mathlib `fc4f59e5`）形式化归约，同时交付若干无条件 Lean 4 筛法内核定理与奇偶不可区分障碍证明，请求维护者与同行对数值证书、Lean 源码及显式声明的解析前提接口进行独立复核与审定。

与 [1+4 中间命题](../2026-11-26-one-plus-four/proof.md) 及 [1+3 中间命题](../2026-11-27-one-plus-three/proof.md) 覆盖全体偶数 $N \ge 4$ 不同，本稿聚焦于**纯 GRH 下显著压低显式陈氏 `1+2` 的生效阈值**（直接缩小 [RFC1](../../RFC1-小偶数上的Goldbach.md) 中 `1+2` 的有限区间空白），并精确界定纯 GRH 线性/二次切换筛锥体在低区 $[4 \cdot 10^{18}, 10^{316})$ 处的硬障碍。强哥德巴赫猜想（ $K = 1$ ）以及低区 $[4 \cdot 10^{18}, 10^{316})$ 内的 `1+2` 封闭仍开放。

---

## 1. 文献背景与阈值推进总览

在 GRH 下的显式陈氏 `1+2` 路线上，公开文献中已发表纪录为 Bordignon–Starichkova（*Ramanujan J.* **64**(4) (2024), 1213–1242，[DOI](https://doi.org/10.1007/s11139-024-00866-x)）最终版给出的 $N > \exp(\exp(14)) \approx 10^{522{,}265}$ （早期预印本 [`arXiv:2211.08844v1`](https://arxiv.org/abs/2211.08844) 为 $\exp(\exp(15.85)) \approx 10^{3.33 \times 10^6}$ ）；2026 年 10 月预印本参数重优化（Hubbard, 2026）将其推进至 $\exp(\exp(13.375)) \approx 10^{279{,}695}$ 。

本分支在**零新分布猜想、零硬件浮点（90 位 `Decimal` 陷阱 + 精确 `Fraction`）**与 **Lean `v4.36.0` 无 `native_decide`** 约束下，通过平滑显式公式、无条件双线性色散以及三类加权/二次切换筛架构，将纯 GRH 高区 `1+2` 射线阈值压缩超过 50 万个数量级：

| 方案与误差模型 | 切换架构 | 认证阈值（ $N \ge 10^E$ ） | 90 位认证主项 / 误差 / 净余量 | 对应 Lean 4 定理（[`PureGRHShowcaseK2.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/PureGRHShowcaseK2.lean)） |
|---|---|---|---|---|
| **文献纪录（2024）** | BS24 1-步 $(1/8, 1/3)$ | $\exp(\exp(14)) \approx 10^{522{,}265}$ | — | Bordignon–Starichkova (2024) |
| **文献纪录（2026）** | Hubbard 参数重优化 | $\exp(\exp(13.375)) \approx 10^{279{,}695}$ | — | Hubbard (Oct 2026) |
| **尖锐截断 Perron 射线**（无平滑前提） | 1-步加权 + S6 递归 | $N \ge 10^{1668}$ | `11.118411` / `11.111613` / **`+0.006798`** | `chen_above_1e1668_sharp_grh` |
| **保守 `Parzen` 核**（ $\delta = 1/25$ ， $\kappa_1 = 4$ ， $\kappa_0 = 11$ ，标准显式公式前提） | 1-步常权（ $\beta = 9/100$ ） | $N \ge 10^{390}$ | `11.097755` / `11.097437` / **`+0.000318`** | `chen_above_1e390_parzen_smooth_pure_grh` |
| **保守 `Parzen` 核**（ $\delta = 1/25$ ， $\kappa_1 = 4$ ， $\kappa_0 = 11$ ） | 1-步变权 LP（ $\beta = 1/11$ ， $J = 18$ ） | $N \ge 10^{320}$ | `10.984537` / `10.977388` / **`+0.007149`** | `chen_above_parzen_varWeight_smooth_pure_grh` |
| **保守 `Parzen` 核**（ $\delta = 1/25$ ， $\kappa_1 = 4$ ， $\kappa_0 = 11$ ） | 2-步二次切换 LP（ $\beta = 20/223$ ， $J = 18$ ） | $N \ge 10^{316}$ | `11.220374` / `11.219123` / **`+0.001251`** | `chen_above_parzen_quad_smooth_pure_grh` |

*注记*：本提交仅纳入保守 `Parzen` 核与尖锐截断 Perron 射线结果（不含仍在核校中的实验性台地核分支）。变权 LP 与二次切换 LP 的完整有理见证固化于 [`k2/scripts/data/pure_grh_quad_lp_witness.json`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/scripts/data/pure_grh_quad_lp_witness.json) 与 [`k2/scripts/data/certified_pure_grh_frontier.json`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/scripts/data/certified_pure_grh_frontier.json)，在 $J = 18$ 条带、互素模分离常数 $c_{\mathrm{mult}} = 1$ 下以精确 `Fraction` 检验全部 `7,864` 组无平方因子多重集与 `3,735` 组非无平方因子多重集（变权 LP 为 `7,863` / `3,734` 组），且相应射线证书的有理分子与 `PureGRHShowcaseK2.lean` 中的 `RayCert` 逐字对齐。

---

## 2. Lean 4 内核无条件证明板块

在 `BuchstabSwitchingK2` 中，以下五大核心板块已在 Lean `v4.36.0` 内核中无条件证完（库代码零 `sorry`、零自定义 `axiom`、零 `native_decide`，仅依赖 `[propext, Classical.choice, Quot.sound]`）：

1. **上游 GRH 等价性与挑战同构（[`CitedPremisesK2.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/External/CitedPremisesK2.lean)、[`AxiomsCheckK2.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/AxiomsCheckK2.lean)）**：
   - 从 Mathlib 欧拉乘积与本原特征诱导关系直接证明 `LFunction_eq_zero_iff_primitiveCharacter`、`upstreamGRH_iff_dirichletLZerosOnLine`、`upstreamGRH_iff_primitiveDirichletLZerosOnLine` 与 `upstreamGRH_imp_riemannZetaZerosOnLine`；
   - 通过 5 条 `Iff.rfl` 核验 `Challenge.lean` 与内部模块在 `AllEvenPrimePlusAlmostPrime` 及四条零点命题上的定义等价。
2. **本原特征一维围道归约与可容许光滑核构造（`CitedPremisesK2.lean`、`PureGRHShowcaseK2.lean`）**：
   - `smoothExplicitFormula_of_primitiveBounds` 将合数模 $q \le \sqrt{N}$ 的光滑显式公式余项归约至主特征一维光滑素数定理前提（`PrincipalSmoothPNTPremise`）与一维本原特征围道界（`PrimitiveSmoothExplicitFormulaPremise`），从而支撑通用推论 `chen_above_varWeight_of_primitive_contour_grh` 与 `chen_above_quad_of_primitive_contour_grh`；
   - `exists_boundedSmoothedKernel_one_fiftieth` 无条件构造了 $\delta = 1/50$ 的非空有界光滑核见证。
3. **无条件解析、色散与组合筛装配（[`SelbergL1Cancellation.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/Sieve/SelbergL1Cancellation.lean)、`KernelSieveAssemblyK2.lean`）**：
   - 证明无条件乘性大筛 `multiplicativeLargeSieve`、平滑双线性色散 `smoothedBilinearDispersion`（在 $N \ge 10^{50}$ 以上无条件消除 $B_N$ 奇偶分支误差）、Selberg $\Lambda^2$ 权和界 `sum_abs_selbergLam_eq`、上下筛组合余项界 `abs_combined_rem_le_of_smoothEF` 以及平方整除谐波上界 `sum_midPrimes_squareDivisible_le`。
4. **三类切换引擎与 $\mathbb{R} \to \mathbb{Q}$ 权稠密迁移（[`RealToRatBridge.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/Sieve/RealToRatBridge.lean)、[`WeightedSmoothedSwitching.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/Sieve/WeightedSmoothedSwitching.lean)、[`WeightedQuadraticSwitching.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/BuchstabSwitchingK2/Sieve/WeightedQuadraticSwitching.lean)、`PureGRHShowcaseK2.lean`）**：
   - 将非负实值平滑素数权 $W : \mathbb{N} \to \mathbb{R}_{\ge 0}$ 上的严格正平衡下界，经有理逼近迁移至 1-步常权（`switchingBalance1p2`）、1-步变权（`varWeightSwitchingBalance1p2`）与 2-步二次角色反转（`quadAbstractBalance`）组合平衡量，严格推出 $N = p + m$ 且 $\Omega(m) \le 2$。
5. **内核奇偶不可区分障碍定理（`RealToRatBridge.lean` 中 `BuchstabSwitchingK2.Barriers`）**：
   - `adversarial_richert_balance_nonpos`、`adversarial_switchingWithS4_balance_nonpos` 与 `adversarial_quad_balance_nonpos` 无条件证明：对满足常规 $\beta$-筛可容许条件但集中在奇数个素因子上的奇偶反转敌手测度，上述三类加权/二次切换筛的净平衡量恒非正（ $\le 0$ ）。

---

## 3. 显式前提边界与待封闭低区说明

为便于维护者准确审查当前完成度与尚未机械化的边界，现将高区射线定理显式接收的全部前提分类列明：

1. **GRH 零点前提**：`UpstreamGRHPremise`（与 `lsernau/grh-lean@72fead1` 的 `DirichletLNonvanishingRightOfHalf` 逐字一致）。
2. **光滑显式公式文献前提**：保守 `Parzen` 射线接收标准文献前提 `SmoothExplicitFormulaLiteraturePremise Φ X₀ 4 11`（也可经 `smoothExplicitFormula_of_primitiveBounds` 拆为 1D 主特征 PNT + 1D 本原特征围道界）；尖锐截断射线 `chen_above_1e1668_sharp_grh` 不需要任何光滑核前提。
3. **解析主项与筛装配接口**：`PureGRHConstSieveLemmas`、`PureGRHVarWeightSieveLemmas`、`PureGRHQuadSieveLemmas`（及尖锐截断射线的 `RayExternalPremisesK2`）将 Python 90 位有向区间认证脚本 [`certify_pure_grh_1p2.py`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f197b0557bbec1c1e87b3bf4827df6a26e72dfc1/k2/scripts/certify_pure_grh_1p2.py) 核定的主项与误差常数以显式结构体接入 Lean 切换引擎；这些解析求和与线性筛主项下界目前在 90 位零浮点区间算术中完成认证，尚未如 `k3` 那样在 Lean 内核内完成二进反射实例化。
4. **低区有限空白 $[4 \cdot 10^{18}, 10^{316})$ 与高区独立性**：
   - 本文全部高区 `1+2` 射线定理**仅作用于 $N \ge X_{\mathrm{LS}}$ ，完全不依赖** `[4, 4×10^{18})` 有限偶数计算验证前提；
   - 结合第 2 节内核奇偶障碍定理与 90 位对偶 LP 不可行证明（在无预筛 Parzen 线性筛锥体下， $N \le 10^{143}$ 存在显式认证伪测度使对偶泛函上界严格为负，且全多重集正向 LP 构造边界落在 `10^{316}`），在拆除任何新分布猜想后，低区有限空档 $[4 \cdot 10^{18}, 10^{316})$ 在纯 GRH + 线性/二次切换锥体内仍保持开放。
