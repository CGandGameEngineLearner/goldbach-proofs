# 小二次幂移位的哥德巴赫例外集

这份阶段成果供维护者复核 `L-goldbach-binary-shift-exception-union` 的计数归约、主弧显式公式和近 1 零点估计。[Lean 源码](BinaryShiftExceptionUnion.lean)

记 $E(Y)$ 为 $4$ 至 $Y$ 中无法表示成两素数之和的偶数个数。记 $S(X)$ 为区间 $[X,2X)$ 中至少有一个移位 $n-2^e$ 无法表示成两素数之和的偶数个数，其中 $1\le e\le \lfloor(\log_2 X)/2\rfloor$。

## Lean 核验结果

- 当 $X\ge 8$ 时，$S(X)\le\lfloor(\log_2 X)/2\rfloor E(2X)$。把每个失败目标写成 $m+2^e$，其中 $m$ 是普通例外。当 $X\ge 4$ 时，$[X-2,2X-2)$ 中的每个普通例外都通过 $e=1$ 注入移位例外集。
- 对每个固定的 $A>0$，当 $X$ 充分大时，$S(X)\le (2/\log 2)X(\log X)^{-A}$。证明把普通例外集的 $A+1$ 阶对数节省传给移位例外集。[已验收的 Estermann 界](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3615)
- 若 $E(Y)=O(Y^\alpha)$ 对某个 $\alpha<4/5$ 成立，则 $S(X)^5\le X^4$ 对充分大的 $X$ 成立。仓库中以 Dirichlet GRH 为前提的已验收估计取 $\varepsilon=1/4$ 就给出 $\alpha=3/4$。源码显式保留这个前提。[已验收的 GRH 条件界](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/82)

## 主弧上的近 1 零点

令 $q\le Q$ 遍历本原特征的导子。固定 $H,T\ge0$，对充分大的 $Q$ 以及所有 $X\ge Q$，把显式公式中满足 $\operatorname{Re}\rho\ge1-H/\log X$、$|\operatorname{Im}\rho|\le T$ 的零点放入一个表中，同一零点按其解析重数计入。表的总重数有一个只依赖 $H,T$ 的上界。Lean 声明是 `nearOne_zero_multiplicity_bounded`。证明使用两组有限 Selberg 筛权。不同本原特征的交叉项由周期性控制，同一特征的交叉项由虚部间距控制，一个小矩形内的重数由对数导数估计控制。[筛权的已验收实现](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/1734) · [Pintz 的零点密度方法](https://arxiv.org/abs/1804.05552)

令 $X=m+2$。在 $X^{11/40}\le P\le X^{3/10}$ 中可以选取同一个截断位置，使表内所有导子最小公倍数不超过 $P$ 的零点对都适用同一幂次节省。每一对的有限主弧积分等于扭曲奇异级数乘以 Beta 主项，再加一个误差。极点也参加配对。把这些配对按带符号的解析重数加总后，误差至多为普通奇异级数乘以 $C_{H,T}X^{1-\kappa_{H,T}}$，其中 $\kappa_{H,T}>0$。Lean 声明是 `nearOneCatalogue_summed_power_saving`。[有理弧显式公式与奇异级数的方法](https://arxiv.org/abs/1804.05561) · [复用的显式公式证明](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3316) · [复用的零点区域与算术引理](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3782)

## 哪些零点对仍会影响主项

在正偶数目标 $n$ 处，设 $L$ 是两个本原导子的最小公倍数，$R=L/\gcd(n,L)$。扭曲奇异级数的绝对值与普通奇异级数之比至多为 $56^3 R^{-1/4}$。若两个提升后的特征的乘积导子不整除 $R$，该比值为零。对任意固定比例 $\delta>0$，因此可以选一个与特征和目标无关的整数 $K$，使比值达到 $\delta$ 的每一对都满足 $L\mid Kn$，乘积导子也整除 $K$。Lean 声明是 `relative_order_decay` 和 `large_series_forces_levels`。对一个完整周期求平方和还给出了 `largePairTargets_power`。当 $X^a\le L\le X$ 时，至多 $O_{\delta,\varepsilon}(X^{1-a+\varepsilon})$ 个正偶数目标达到该比例。[Pintz 的奇异级数估计，第 7 节](https://arxiv.org/html/1804.05561v1)

极点与单个零点的配对在每个正偶数上都有幂次节省。结合零点总重数界，在 $X/2\le n\le X$ 内，表内主弧贡献等于普通主项加上满足上述整除条件的零点对总和，误差至多为普通主项的任意给定比例。除至多 $O(X^{3/4})$ 个目标外，这些零点所涉及的导子共用一个小于 $X^{1/4}$ 的模数 $q$。在这个模数上按小导子特征分类，每个零点的权重为其重数乘以 $n^{\operatorname{Re}\rho-1}$。若各类的总权重平方之和至多为 $1-\eta$，则表内主弧部分的实部至少为普通主项的 $\eta/2$ 倍。Lean 声明是 `nearOne_related_formula` 和 `nearOne_class_energy_floor`。[Pintz 的零点分类，第 2 节](https://arxiv.org/html/1804.09084v2)

要推出冻结声明 $S(X)^5\le X^4$，还须估计近 1 矩形以外的贡献，并为实际零点的分类权重证明上述严格小于 1 的界。源码在 `binaryShiftExceptionUnion_of_zeroCorrections` 中保留了足以推出原题的条件。另一条计数归约可直接使用 Pintz 发表的普通例外集 $Y^{18/25}$ 界，项目允许导入的 Lean 依赖还缺这条无条件界。[Pintz 的普通例外集定理](https://arxiv.org/abs/1804.09084)

## 复现

使用仓库锁定的 Lean 4.36.0 和 Mathlib 提交 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`，从仓库根目录运行以下命令。

```sh
cd lean
lake exe cache get
lake build +Conjectures.Goldbach.B13BilateralVaughanReduction:olean \
  +Conjectures.Goldbach.EstermannAlmostAllPolylog:olean \
  +Conjectures.Goldbach.MaskedPrimeCutoffLoss:olean \
  +PEqualNP.Outside.L_goldbach_central_positive_density:olean \
  +PEqualNP.Outside.L_goldbach_continuous_parseval:olean \
  +PEqualNP.Outside.L_goldbach_frontier_no_siegel_zero:olean \
  +PEqualNP.Outside.L_goldbach_frontier_uncond_deep_second_moment:olean \
  +PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density:olean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxHeartbeats=4000000 \
  ../research/checkpoint/2026-11-27-binary-shift-exceptions/BinaryShiftExceptionUnion.lean
```
