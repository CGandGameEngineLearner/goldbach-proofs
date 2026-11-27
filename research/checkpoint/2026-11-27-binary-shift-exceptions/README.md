# 小二次幂移位的哥德巴赫例外集

这份阶段成果供维护者复核 `L-goldbach-binary-shift-exception-union` 的计数归约和无条件对数节省。[Lean 源码](BinaryShiftExceptionUnion.lean)

记 $E(Y)$ 为 $4$ 至 $Y$ 中无法表示成两素数之和的偶数个数。记 $S(X)$ 为区间 $[X,2X)$ 中至少有一个移位 $n-2^e$ 无法表示成两素数之和的偶数个数，其中 $1\le e\le \lfloor(\log_2 X)/2\rfloor$。

## Lean 核验结果

- 当 $X\ge 8$ 时，$S(X)\le\lfloor(\log_2 X)/2\rfloor E(2X)$。把每个失败目标写成 $m+2^e$，其中 $m$ 是普通例外。当 $X\ge 4$ 时，$[X-2,2X-2)$ 中的每个普通例外都通过 $e=1$ 注入移位例外集。
- 对每个固定的 $A>0$，当 $X$ 充分大时，$S(X)\le (2/\log 2)X(\log X)^{-A}$。证明把普通例外集的 $A+1$ 阶对数节省传给移位例外集。[已验收的 Estermann 界](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/3615)
- 若 $E(Y)=O(Y^\alpha)$ 对某个 $\alpha<4/5$ 成立，则 $S(X)^5\le X^4$ 对充分大的 $X$ 成立。仓库中以 Dirichlet GRH 为前提的已验收估计取 $\varepsilon=1/4$ 就给出 $\alpha=3/4$。源码显式保留这个前提。[已验收的 GRH 条件界](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/82)

正式验收仍需用当前允许的 Lean 依赖给出所需的幂次界。Pintz 给出的 $E(Y)=O(Y^{18/25})$ 在数学上足以完成这一步。研究台当前暂停导入仓库中的 GRH 证明。[Pintz 的论文](https://arxiv.org/abs/1804.09084) · [参与指南](https://www.movan.tech/goldbach/join-zh.txt)

## 复现

使用仓库锁定的 Lean 4.36.0 和 Mathlib 提交 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`，从仓库根目录运行以下命令。

```sh
cd lean
lake exe cache get
lake build +Conjectures.Goldbach.EstermannAlmostAllPolylog:olean \
  +PEqualNP.Outside.L_goldbach_grh_goldbach_exception_density:olean
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxHeartbeats=4000000 \
  ../research/checkpoint/2026-11-27-binary-shift-exceptions/BinaryShiftExceptionUnion.lean
```
