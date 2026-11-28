# 逐点哥德巴赫相关下界的阶段核验记录

目标是研究台的 `L-goldbach-dyadic-correlation-floor`。令素数上的权重为自然对数，其他自然数上的权重为零。所研究的量为有序素数对的加权和

$$
\operatorname{corr}(n)=\sum_{p=0}^{n}w(p)w(n-p).
$$

冻结引理要求存在固定正数 $c$，使每个充分大的偶数 $n$ 都有 $\operatorname{corr}(n)\ge c n$。下文记录已完成的量化结果，原引理的逐点证明仍待完成。

## 两条无条件结论

1. 存在固定的 $K>0$，对每个充分大的 $X$，区间 $[X,2X)$ 中满足 $\operatorname{corr}(n)< n/36$ 的偶数至多有 $KX/(\log X)^3$ 个。证明对区间中的目标使用同一组主弧，估计真实素数指数和在次弧上的大小，再由 Bessel 不等式计数例外。该界仍允许个别偶数例外。[Lean 定理](https://github.com/Karma-s3/goldbach-proofs/blob/7cdb6007d553da645bdebf1217925a2e9761333f/research/checkpoint/2026-11-26-dyadic-correlation/VerifiedGenuineGoldbachCubicExceptions.lean#L60)
2. 每个充分大的偶数 $n$，至少有 $n/(25\,165\,824(\log n)^2)$ 个不同的素数 $p$ 满足 $n/4<p\le n/2$，其补数 $n-p$ 无平方因子，且按重数计至多有七个素因子。该结论对每个目标都成立，第二个加数的素性仍待证明。[Lean 定理](https://github.com/Karma-s3/goldbach-proofs/blob/7cdb6007d553da645bdebf1217925a2e9761333f/research/checkpoint/2026-11-26-dyadic-correlation/VerifiedSevenFactorGoldbach.lean#L11) · [筛集定义](https://github.com/Karma-s3/goldbach-proofs/blob/7cdb6007d553da645bdebf1217925a2e9761333f/research/checkpoint/2026-11-26-dyadic-correlation/VerifiedBoundedFactorBrun.lean#L11)

## 剩余的奇偶估计

令 $m=n-p$。在 $p$ 为素数、$m\ge2$、$m$ 至多有两个素因子且每个素因子均不小于 $z$ 的候选中，令 $W$ 为 $\log p\log m$ 的和，令 $E$ 为加上符号 $(-1)^{\Omega(m)}$ 后的和。$W-E$ 恰好等于筛限内真素数对加权和的两倍；素数平方在此差中也抵消。当 $z\le\sqrt n$ 时，删去的真素数对质量至多为 $z(\log n)^2=o(n)$。已证明冻结目标等价于对所有充分大的偶数给出 $W-E$ 的正线性下界。在 $n\le z^{11}$ 的范围内，还得到 $W\le 500n^2/\varphi(n)$，并控制了素因子指数处于移动窄区间时的质量。[等价定理](https://github.com/Karma-s3/goldbach-proofs/blob/7cdb6007d553da645bdebf1217925a2e9761333f/research/checkpoint/2026-11-26-dyadic-correlation/VerifiedRoughP2ParityGap.lean#L117) · [总质量上界](https://github.com/Karma-s3/goldbach-proofs/blob/7cdb6007d553da645bdebf1217925a2e9761333f/research/checkpoint/2026-11-26-dyadic-correlation/VerifiedRoughP2SingularUpper.lean#L139) · [窄区间估计](https://github.com/Karma-s3/goldbach-proofs/blob/7cdb6007d553da645bdebf1217925a2e9761333f/research/checkpoint/2026-11-26-dyadic-correlation/VerifiedRoughP2ExponentNoAtom.lean#L65)

从陈氏量级的候选计数推出冻结下界的定理显式要求带符号估计。阶段成果没有给出对所有偶数的这一估计。外部陈氏粗筛加权下界的原工具链全依赖重放也未完成。[条件归约](https://github.com/Karma-s3/goldbach-proofs/blob/7cdb6007d553da645bdebf1217925a2e9761333f/research/checkpoint/2026-11-26-dyadic-correlation/VerifiedRoughP2WeightedTransfer.lean#L76)

## 复验与审查

源码固定于 `7cdb6007d553da645bdebf1217925a2e9761333f`，工具链为 Lean 4.36.0，mathlib 固定于 `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`。两条主要结论已分别在本地通过独立 `leanchecker` 重放。打包时以已编译依赖重跑汇总入口，八条声明的公理输出均为 `propext`、`Classical.choice`、`Quot.sound`。归档包含源码、依赖锁、复验命令和源码校验清单。此次未从空缓存重建全包。[源码与复验说明](https://github.com/Karma-s3/goldbach-proofs/blob/7cdb6007d553da645bdebf1217925a2e9761333f/research/checkpoint/2026-11-26-dyadic-correlation/README.md) · [公理输出](https://github.com/Karma-s3/goldbach-proofs/blob/7cdb6007d553da645bdebf1217925a2e9761333f/research/checkpoint/2026-11-26-dyadic-correlation/axioms.txt) · [校验清单](https://github.com/Karma-s3/goldbach-proofs/blob/7cdb6007d553da645bdebf1217925a2e9761333f/research/checkpoint/2026-11-26-dyadic-correlation/SOURCE-SHA256.txt)

提交者为 Karma-s3，使用 Codex。建议独立复核时分别检查例外集合的量词、七因子筛集的定义，以及奇偶估计接口中的显式假设。本记录供研究审查，冻结引理的权威验证仍待完整证明。
