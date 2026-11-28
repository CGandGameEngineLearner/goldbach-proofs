# 小二次幂移位的哥德巴赫例外集

这份阶段成果供维护者复核 `L-goldbach-binary-shift-exception-union` 的计数归约、主弧显式公式和近 1 零点估计。[Lean 源码](BinaryShiftExceptionUnion.lean)

记 $E(Y)$ 为 $4$ 至 $Y$ 中无法表示成两素数之和的偶数个数。记 $S(X)$ 为区间 $[X,2X)$ 中至少有一个移位 $n-2^e$ 无法表示成两素数之和的偶数个数，其中 $1\le e\le \lfloor(\log_2 X)/2\rfloor$。

## Lean 核验结果

- 当 $X\ge 8$ 时，$S(X)\le\lfloor(\log_2 X)/2\rfloor E(2X)$。把每个失败目标写成 $m+2^e$，其中 $m$ 是普通例外。当 $X\ge 4$ 时，$[X-2,2X-2)$ 中的每个普通例外都通过 $e=1$ 注入移位例外集。
- 对每个固定的 $A>0$，当 $X$ 充分大时，$S(X)\le (2/\log 2)X(\log X)^{-A}$。证明把普通例外集的 $A+1$ 阶对数节省传给移位例外集。[已验收的 Estermann 界](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3615)
- 若 $E(Y)=O(Y^\alpha)$ 对某个 $\alpha<4/5$ 成立，则 $S(X)^5\le X^4$ 对充分大的 $X$ 成立。仓库中以 Dirichlet GRH 为前提的已验收估计取 $\varepsilon=1/4$ 就给出 $\alpha=3/4$。源码显式保留这个前提。[已验收的 GRH 条件界](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/82)

对题单引用的 Pintz 定理，取 $Y=2X$ 可得 $E(2X)<(2X)^{18/25}$。对充分大的 $X$，每个允许的移位满足 $2^e\le\sqrt X$，所以失败的 $n-2^e$ 是 $[4,2X]$ 内的普通例外。固定指数 $e$ 和例外 $m$ 就唯一确定 $n=m+2^e$。于是

$$
S(X)\le \frac{2^{18/25}}{2\log 2}X^{18/25}\log X.
$$

由于 $4/5-18/25=2/25>0$，右边与 $X^{4/5}$ 的比值趋于零。取五次方即得原题。Lean 已核对从这个普通例外界到冻结声明的推导，普通例外界本身是这里援引的文献定理。[Pintz，定理 1](https://arxiv.org/html/1804.09084v2#S1)

## 主弧上的近 1 零点

令 $q\le Q$ 遍历本原特征的导子。固定 $H,T\ge0$，对充分大的 $Q$ 以及所有 $X\ge Q$，把显式公式中满足 $\operatorname{Re}\rho\ge1-H/\log X$、$|\operatorname{Im}\rho|\le T$ 的零点放入一个表中，同一零点按其解析重数计入。表的总重数有一个只依赖 $H,T$ 的上界。Lean 声明是 `nearOne_zero_multiplicity_bounded`。证明使用两组有限 Selberg 筛权。不同本原特征的交叉项由周期性控制，同一特征的交叉项由虚部间距控制，一个小矩形内的重数由对数导数估计控制。[筛权的已验收实现](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/1734) · [Pintz 的零点密度方法](https://arxiv.org/abs/1804.05552)

令 $X=m+2$。在 $X^{11/40}\le P\le X^{3/10}$ 中可以选取同一个截断位置，使表内所有导子最小公倍数不超过 $P$ 的零点对都适用同一幂次节省。每一对的有限主弧积分等于扭曲奇异级数乘以 Beta 主项，再加一个误差。极点也参加配对。把这些配对按带符号的解析重数加总后，误差至多为普通奇异级数乘以 $C_{H,T}X^{1-\kappa_{H,T}}$，其中 $\kappa_{H,T}>0$。Lean 声明是 `nearOneCatalogue_summed_power_saving`。[有理弧显式公式与奇异级数的方法](https://arxiv.org/abs/1804.05561) · [复用的显式公式证明](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3316) · [复用的零点区域与算术引理](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3782)

## 哪些零点对仍会影响主项

在正偶数目标 $n$ 处，设 $L$ 是两个本原导子的最小公倍数，$R=L/\gcd(n,L)$。扭曲奇异级数的绝对值与普通奇异级数之比至多为 $56^3 R^{-1/4}$。若两个提升后的特征的乘积导子不整除 $R$，该比值为零。对任意固定比例 $\delta>0$，因此可以选一个与特征和目标无关的整数 $K$，使比值达到 $\delta$ 的每一对都满足 $L\mid Kn$，乘积导子也整除 $K$。Lean 声明是 `relative_order_decay` 和 `large_series_forces_levels`。对一个完整周期求平方和还给出了 `largePairTargets_power`。当 $X^a\le L\le X$ 时，至多 $O_{\delta,\varepsilon}(X^{1-a+\varepsilon})$ 个正偶数目标达到该比例。[Pintz 的奇异级数估计，第 7 节](https://arxiv.org/html/1804.05561v1)

极点与单个零点的配对在每个正偶数上都有幂次节省。结合零点总重数界，在 $X/2\le n\le X$ 内，表内主弧贡献等于普通主项加上满足上述整除条件的零点对总和，误差至多为普通主项的任意给定比例。除至多 $O(X^{3/4})$ 个目标外，这些零点所涉及的导子共用一个小于 $X^{1/4}$ 的模数 $q$。在这个模数上按小导子特征分类，每个零点的权重为其重数乘以 $n^{\operatorname{Re}\rho-1}$。若各类的总权重平方之和至多为 $1-\eta$，则表内主弧部分的实部至少为普通主项的 $\eta/2$ 倍。Lean 声明是 `nearOne_related_formula` 和 `nearOne_class_energy_floor`。[Pintz 的零点分类，第 2 节](https://arxiv.org/html/1804.09084v2)

## 导子、筛权与例外指数

`primitive_zero_prefix_square_root` 用 Pólya–Vinogradov 特征和界缩短了检测零点所需的有限求和区间。给定 $H,T,a\ge 0$ 和任意 $\delta,\eta>0$，当 $VW\le Q^a$、$Y\ge Q^{1/2+a+\delta}$ 且 $Q$ 充分大时，每个导子不超过 $Q$ 的本原非主特征在所选零点处的加权前缀绝对值至多为 $\eta$。`primitive_nearOne_quantitative` 给出间隔零点族关于条带宽度的显式指数上界。同一小导子特征类中，`class_sieve_correlation` 把不同本原特征之间的筛权内积归结到导子整除固定整数 $K$ 的相关特征。[已验收的 Pólya–Vinogradov 估计](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3771)

`nearOne_most_targets` 证明，对任意固定矩形 $H,T$ 和任意相对误差 $\varepsilon>0$，除 $O_{H,T,\varepsilon}(X^{1-a})$ 个目标外，矩形内实际零点与极点的主弧贡献和普通主项的差至多为普通主项的 $\varepsilon$ 倍，其中 $a>0$。`nearOne_class_energy_floor_at` 可将共同模数截在 $X^\theta$，按此筛掉的目标数至多为 $O(X^{1-\theta})$。取 $\theta=5/24$，得到 $19/24<4/5$。此时 `nearOne_energy_exponential_weight` 将分类权重控制在解析重数乘 $e^{-(24/5)(1-\beta)\log q}$ 的任意小相对损失内。Zhao 的定理给出了这类权重的平方和上界。[Zhao，定理 1.2](https://arxiv.org/html/2511.05631v1)

## 从增长高度的零点计数到原题

`nearOne_all_power_height` 将实际零点表的计数推广到 $|\operatorname{Im}\rho|\le Q^b$。对每个固定的 $0\le b<1$ 和条带宽度 $H\ge0$，所有导子不超过 $Q$ 的本原特征在 $\operatorname{Re}\rho\ge 1-H/\log X$ 中的零点总重数有统一上界，对所有 $X\ge Q$ 成立。这包括导子为 1 的主特征。证明在 Abel 求和中保留主特征的极点项。两组筛权引入的最小公倍数倒数之和至多为 $(1+\log Y)^4$；零点自由区域迫使主特征的相关零点有足够大的虚部，从而抵消这项损失。[Pintz 的零点密度方法](https://arxiv.org/abs/1804.05552)

`coefficient_sub_retained` 逐个分母写出完整主弧模型减去所选矩形的精确余项。求和保留每个至少有一个零点落在矩形外的配对的符号、解析重数、Gauss 因子与有限弧积分。在两个虚部接近互为相反数时，`beta_opposite_ordinates` 给出 Beta 因子的指数衰减。具体地，若 $|\gamma|\ge16$、$|\gamma+\gamma'|\le |\gamma|/2$ 且两实部在 $[5/8,1]$，则衰减因子至多为 $(3/4)^{\lfloor |\gamma|/8\rfloor}$，乘以常数 $B(5/8,5/8)$。[Pintz 关于高零点的主弧估计](https://arxiv.org/html/1804.05561v1#S10)

对任意符号的虚部，`beta_uniform_height` 给出一致衰减率 $O(\max(|\gamma|,|\gamma'|)^{-1/16})$。这比 Pintz 在公式 (10.25) 中给出的 $-1/2$ 指数弱，但足以做固定高度截断。具体地，对每个 $0<b<1$ 和任意 $\varepsilon>0$，可先选取与 $Q$ 无关的高度 $T$，使 $Q^b$ 与 $T$ 两张表的带符号 Beta 主项之差至多为 $\varepsilon\mathfrak S(n)n$。该界对全部正整数目标和所有分母截断值同时成立。Lean 声明为 `polynomial_catalogue_beta_truncation`。这个估计控制的是完成 Fourier 反演后的 Beta 主项；原题中的有限主弧余项还需要单独控制。[Pintz I，公式 (10.24) 至 (10.27)](https://arxiv.org/html/1804.05561v1#S10)

`binaryShiftExceptionUnion_of_catalogue_estimates` 已按注册表中原题的完整类型核对。若能选定矩形 $H,T$ 和 $0<\eta\le1$，使共同模数上的指数加权分类平方和至多为 $1-\eta$，并使余项实部至少为 $-\eta X/16$，即可推出 $S(X)^5\le X^4$。两项估计分别允许 $O(X^{19/24})$ 个例外。它们仍是待证的解析输入。[Zhao 的零点分类估计](https://arxiv.org/html/2511.05631v1) · [Pintz 的显式公式](https://arxiv.org/abs/1804.05561)

## 复现

使用仓库锁定的 Lean 4.36.0 和 Mathlib 提交 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`，从仓库根目录运行以下命令。

```sh
cd lean
lake exe cache get
lake build +Conjectures.Goldbach.B13BilateralVaughanReduction:olean \
  +Conjectures.Goldbach.EstermannAlmostAllPolylog:olean \
  +Conjectures.Goldbach.MaskedPrimeCutoffLoss:olean \
  +Conjectures.Goldbach.RoughFifthMass:olean \
  +PEqualNP.Outside.L_goldbach_central_positive_density:olean \
  +PEqualNP.Outside.L_goldbach_continuous_parseval:olean \
  +PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero:olean \
  +PEqualNP.Outside.L_goldbach_frontier_uncond_deep_second_moment:olean \
  +PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density:olean
lake env lean -j2 -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxHeartbeats=4000000 \
  ../research/checkpoint/2026-11-27-binary-shift-exceptions/BinaryShiftExceptionUnion.lean
```
