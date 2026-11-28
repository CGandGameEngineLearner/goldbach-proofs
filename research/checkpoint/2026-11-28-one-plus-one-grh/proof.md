# 中间命题提交稿：GRH 下全范围显式 1+1 例外集、短区间与 Linnik 二幂偏移表示（$K = 22$）

**提交者**　千早爱音（[Visio-Vanitas](https://github.com/Visio-Vanitas)） · [上游源码快照（`f878d4a`）](https://github.com/Visio-Vanitas/buchstab-switching/tree/f878d4a20513f020e5c4e857fd5d0aae2e644bdb/1%2B1) · [复核指南](README.md)

**定位与诚实边界。** 本提交稿在**仅假设 Dirichlet $L$ 函数广义黎曼猜想**（`DirichletLNonvanishingRightOfHalf`，与 `lean/PEqualNP/GRH.lean` 及 `lsernau/grh-lean@72fead1` 逐字一致）与**已发表强哥德巴赫经验验证界** $E(4\cdot 10^{18}) = 0$（Oliveira e Silva–Herzog–Pardi, 2014）的前提下，给出围绕强哥德巴赫（`1+1`）猜想的三组**全体偶数/全实数起点（$N_0 = 4$ / $N_0 = 48$）**显式定量推进、零浮点计算证书及 Lean `v4.36.0` 条件归约。对任意 $N > 4\cdot 10^{18}$ 的无条件逐点 `1+1`（$K = 1, s = 0$）依然开放。

---

## 1. 认证命题总览

| 编号 | 定理名称（`OnePlusOne.Main`） | 假设条件 | 显式结论（无渐近大 $O$ 隐含常数） | 全范围起点 |
|---|---|---|---|---|
| **1A** | `theorem_1A_all_even_exceptional_set` | GRH + $E(4\cdot 10^{18}) = 0$ | $E(X) \le 12731 \sqrt{X} (\log X)^3$ | **全体 $X \ge 4$** |
| **1B** | `theorem_1B_all_even_short_interval` | RH（$\zeta(s)$） + $E(4\cdot 10^{18}) = 0$ | $[X,\ X + 6281 (\log X)^2]$ 必含偶数 $N = p_1 + p_2$ | **全体 $X \ge 4$** |
| **3A** | `theorem_3A_all_even_exact_linnik_22` | GRH + $E(4\cdot 10^{18}) = 0$ | $N = p_1 + p_2 + \sum_{i=1}^{22} 2^{k_i}$（$k_i \ge 1$，精确 **22** 个幂） | **全体偶数 $N \ge 48$** |
| **3** | `theorem_3_all_even_linnik_goldbach` | GRH + $E(4\cdot 10^{18}) = 0$ | $N = p_1 + p_2 + \sum_{j=1}^s 2^{k_j}$（$s \le 22$） | **全体偶数 $N \ge 4$** |

---

## 2. 关键技术推进与全范围闭合机制

### 2.1 Laplace 光滑 Parseval 引擎（定理 1A 与 1B）

- 选取加法完全乘性的 Laplace 素数权 $e^{-n/Y}$，保证 $\int_{-1/2}^{1/2} S(\alpha)^2 e(-N\alpha)\,d\alpha = e^{-N/Y} R_\Lambda(N)$ 精确还原未加权哥德巴赫表示数，同时令临界线 Mellin 核 $\Gamma(\frac{1}{2}+i\gamma) z^{-\frac{1}{2}-i\gamma}$ 沿虚轴呈指数衰减 $\exp(-|\gamma|/A)$。
- **定理 1A**：在 `[4 * 10^18, 10^10000]` 切分 15 个向外有向区间细胞及单调渐近尾段 $[10^{10000}, \infty)$（80 位 `Decimal` 武装 `FloatOperation` 陷阱，见 [`scripts/certify_exceptional_short.py`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f878d4a20513f020e5c4e857fd5d0aae2e644bdb/1%2B1/scripts/certify_exceptional_short.py)），测得二进增量上界 $E(Y) - E(Y/2) \le 3728.72 \sqrt{Y}(\log Y)^3$（最弱细胞为 $[4\cdot 10^{18}, 10^{19}]$ 处的 `3728.7125092`，尾段压至 `1565.0661354`）；Lean 4 内 [`Exceptional.exceptional_all_range_of_dyadic`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f878d4a20513f020e5c4e857fd5d0aae2e644bdb/1%2B1/OnePlusOne/Exceptional/DyadicClosure.lean) 无条件证明叠缩因子 $< 2 + \sqrt{2}$ 并结合 $(2+\sqrt{2}) \cdot 3728.72 < 12731$ 收口至全部 $X \ge 4$。
- **定理 1B**：利用 $-\frac{1}{2}$ 线 $\zeta(s)$ 显式公式配 Fejér 紧支撑窗（无需非主 Dirichlet 特征，高区仅需普通 RH），认证 $C_{\mathrm{Sel}} \le 78.0389 \implies C_1 = 6281$；Lean 4 内 [`ShortInterval.short_interval_small_range`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f878d4a20513f020e5c4e857fd5d0aae2e644bdb/1%2B1/OnePlusOne/ShortInterval/FejerReduction.lean) 无条件证明 $[4, 4\cdot 10^{18})$ 内任意长 $\ge 6281(\log X)^2 \ge 2$ 的区间必命中偶数并由 $E(4\cdot 10^{18})=0$ 闭合。

### 2.2 构造性二进制桥梁 + 圈法压低全范围 Linnik–Goldbach 到 $K = 22$（定理 3 / 3A）

- **直接强推圆法的瓶颈**：不带二进制桥梁直接在 $N = 4\cdot 10^{18}$ 运行显式圈法需要 $r_{\mathrm{dir}} = 52$（`maj_net = 0.5302 > minor = 0.4839`），而文献渐近 GRH 的 $K = 7$（脚本亦复现：`minor <= 1.7909 < Maj >= 1.9204`）不含显式小 $N$ 起点。
- **二进制哥德巴赫桥梁（已全量形式化进 Lean 内核，零外部计算依赖）**：设桥梁上界
  $$N_{\mathrm{br}}(22) := (2^{23} - 2)\cdot 2^{61} + 4\cdot 10^{18} \approx 1.93428 \cdot 10^{25}.$$
  因 $2^{61} \le 4\cdot 10^{18} - 4$，对任意偶数 $N \in [48, N_{\mathrm{br}}(22)]$，区间 $[N - 4\cdot 10^{18}, N - 4]$ 内必存在 $M\cdot 2^{61}$（$1 \le M \le 2^{23} - 2$）；$M$ 的二进制展开最多含 22 个 1 比特，若不足 22 个则利用 $2^e = 2^{e-1} + 2^{e-1}$ 从 $\ge 61$ 的指数反复拆分成恰好 22 个正指数 $k_i \ge 1$，使余数 $N - M\cdot 2^{61} \in [4, 4\cdot 10^{18}]$ 命中已知哥德巴赫表。该构造在 [`OnePlusOne/Linnik/Reduction.lean`](https://github.com/Visio-Vanitas/buchstab-switching/blob/f878d4a20513f020e5c4e857fd5d0aae2e644bdb/1%2B1/OnePlusOne/Linnik/Reduction.lean) 的 `binary_goldbach_bridge_22` 中 **100% 无条件证完**。
- **高区圈法接棒（$N > N_{\mathrm{br}}(22)$，对应 $L = \lfloor \log_2(N/16) \rfloor \ge 79$）**：
  - 高斯窗 Mellin–Plancherel 主弧 $L^2$ 界 $C_{E_2} \le 38.6184 < 40$ + 奇异级数 $T_D(X) \ge 1.172$ 截断保正；
  - 精确 1D Selberg 素数筛（$C_{\mathrm{Sel}} \le 5.499$ at $L=79$，$C_{\mathrm{Sel}} \le 9.1412$ for $L \ge 140$）+ mod $105$ / Pintz–Ruzsa $P_{15}$ 均值表（$\bar{\mathfrak{S}}_2 \le 2.600769$）+ $B=8$ 状态 Bessel-$I_0$ 转移矩阵（$M_\phi = 32$）；
  - $r = 21$ 在 $L = 78$ 失败（`1.6486 < 1.7909`），**$r = 22$ 在 $L = 79$ 首次跨越（`1.6429 > 1.4393`，余量 `+0.2036`）**，覆盖全部 $L \in [79, 139]$（最差余量 `+0.1008` at $L=83$），并在 $L \ge 140$ 由 Collatz–Wielandt 步长衰减因子 `0.910613 < 1` 统一收口（`maj_net >= 1.7553 > minor <= 0.9813`，余量 `+0.7740`）。

---

## 3. Lean 4 形式化信任边界与宿主机复核实测结果

在 64 核 `GoldBach` 宿主机（容器外，使用与本仓库 CI 一致的 Lean `v4.36.0`、Mathlib `fc4f59e5` 及 `autoImplicit = false`、`relaxedAutoImplicit = false`、`maxSynthPendingDepth = 3`、`maxHeartbeats = 4000000`）已实测通过全部检查：

1. **Lean 无条件证明范围**：
   - `Arithmetic.major_arcs_disjoint`、`ratio_2p_sub_1_le_pow_eighth`、`twin_prime_partial_product_ge`（`> 0.65928`）、`totient_sq_ge_half`、`dyadic_geom_sum_lt`（`< 2 + √2`）；
   - `Exceptional.exceptional_all_range_of_dyadic`、`dyadic_multiplier_le_12731`、`dyadic_of_parseval_bounds`；
   - `ShortInterval.one_lt_log_four`、`short_interval_small_range`、`exists_goldbach_of_weighted_pos`、`short_interval_all_range`；
   - `Linnik.binary_goldbach_bridge_22`（$48 \le N \le 1.93428\cdot 10^{25}$ 全体偶数）、`Linnik.all_even_exact_linnik_22`、`Linnik.all_even_linnik_22`；
   - `Certificates.certifiedCells_valid`（15 行）、`Certificates.linnikCheckpointCells_valid`（6 个关键节点）由纯内核 `by decide` / `norm_num` 检验（零 `native_decide`）。
2. **显式隔离的外部解析接口（`OnePlusOne/External/Premises.lean`，零 `axiom`）**：
   - `EmpiricalGoldbachBase`（$E(4\cdot 10^{18}) = 0$）、`DyadicLaplaceCirclePremise`（定理 1A 高区 Parseval–Laplace 界）、`FejerShortIntervalPositivityPremise`（定理 1B 高区 Fejér–Mellin 正性）、`LinnikCircleAboveBridgePremise`（定理 3 高于 $N_{\mathrm{br}}(22)$ 处的圈法正性）。
3. **验证实测摘要**：
   - `python3 -I scripts/quick_verify.py`：4 项检查全过（两套 Python 脚本 AST 零浮点/`import math` 泄漏、精确重放比对、`Data.lean` 数据吻合、Lean 源码零禁词）。
   - `lake build OnePlusOne`：7,412 jobs **0 错误、0 警告**。
   - `lake env lean AxiomsCheckOnePlusOne.lean`：30 条导出声明全部严格仅依赖 `[propext, Classical.choice, Quot.sound]` 及其子集。
   - `bash comparator/run_comparator.sh`（14 个导出目标）：`leanchecker-paranoid`、`nanoda_bin` 与 Lean 默认内核均接受解模块（`exit 0`），且含 `sorryAx` 的自挑战被正确拒斥（`exit 1`）。
