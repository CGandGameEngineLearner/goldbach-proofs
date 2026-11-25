# 强哥德巴赫研究路线 / Binary Goldbach roadmap

2026-11-24 · [English](#english) · [实时研究台](https://www.movan.tech/goldbach/#lemmas) · [冻结命题](gaps.json)

对每个偶数 $n\ge4$，要证明存在素数 $p,q$ 使 $p+q=n$。取素数权 $w(p)=\log p$，非素数处令 $w=0$。定义 $R(n)=\sum_{p=0}^n w(p)w(n-p)$。每项非负，每个真正的素数对贡献严格正值，故目标精确地等价于 $R(n)>0$。这给出了所有分析任务共用的终点。[强哥德巴赫命题](strong-goldbach.lean)

## 2026-11-25 · 两条可检验的新路线 / Two proposed routes

**Theta 反射。** 令真实素数权在区间外为零，区间内取反射 k ↦ N−k。先证明能量差恒等式、傅里叶相位公式和支撑截断公式。下一关是显式构造两组 theta 测试数据，使其对应同一个素数权的正、负反射组合，并核对局部因子、测度与共同的正归一化。仅有某个提升非零无法推出这两个指定范数之差为正。算术匹配误差、两侧谱误差与污染项扣除后仍须有严格正裕量。测试数据和谱界目前都未构造；应先提交定义与匹配证明，再冻结相应分析命题。[Rallis 内积相关 Lean 源文件](https://github.com/leanprover-community/riemann-hypothesis/blob/dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/BigThetaNormEqRallisInnerProduct.lean)

**奇特征交叉项。** 对每个偶模数 N 使用中心对称光滑权及除以 N 的 Mangoldt 卷积。固定奇特征的原始诱导特征，截取导子 d⁴>N³ 和高度 |γ|≤log(2N)，按索引删去对角；相同零点的不同副本仍需计数。每项保留频差乘 log N 的相位，以及权 W(γⱼ) 与 W(γₗ) 的共轭乘积。整个和取实部并乘 2/φ(N)。第一批任务锁定指标、相位及分母。研究瓶颈是按给定权函数推导 Kφ(N)，在所有充分大的偶数上一致证明截断交叉项 ≤ Kφ(N)−2κ，其中 κ>0 固定，并独立控制截断误差和素数幂污染。涉及 GRH 的公式须保留假设。二次幂的中心素数质量是可独立攻关的无限子族；一般偶数和小于有效阈值的输入仍需覆盖。若使用分析稿的圆法分解，主弧取圆周距离、分母上限 Q=⌊N^(1/40)⌋、宽度 Q/N，须另证与所用积分的匹配。

**优先领取的中间里程碑：中心表示质量的正密度。** 对 x≤n≤2x 的偶数，C(n) 只累计 n/3≤p≤2n/3 的真素数对数权。先把 [x/2,2x/3] 的一维素数质量平方，按两素数的和重排，得到 ∑C(n) ≥ c x²。另一支用上界筛得到 C(n) ≤ K n S(n)，并按平方自由因子展开证明 ∑S(n)² ≤ K′x，推出 ∑C(n)² ≤ K″x³。两支通过二阶矩法汇合，可得至少 bx 个偶数满足 C(n) ≥ ax。这个里程碑测量质量是否集中；它允许剩余偶数全部落在例外集，不能替代逐个偶数的证明。可先独立攻一维素数块、上界筛、局部因子均值三路。对照任务 TH 编号，按任务标题和依赖 ID 接续。

**Intermediate milestone.** Seek linear central prime mass on a positive proportion of even targets in each sufficiently large dyadic interval. An interior prime block supplies the first moment; an upper-bound sieve and the mean square of the local factor control the second. The remaining exceptional set needs a separate pointwise argument.

**奇特征路线可先完成一个不依赖 GRH 的算术里程碑。** 给定偶数 N>2，把每个奇特征的 log(N/dχ) 按 N 的素因子和缺失的导子层展开。在商模 N/pʲ>2 时，通过提升双射计算该层的奇特征数；商模为 1 或 2 时该层为空。交换两个有限和，即得到一般偶模数的平均导子修正。这个量决定零点截断舍弃了多少低导子特征。进一步控制这些特征所承载的零点振幅仍需独立估计。可同时领取素数层展开、低导子提升计数、二幂塔独立复核三组任务。

**如何评价进展。** 领题者应能说清命题削弱了哪个量词、隔离了哪个误差，或把哪个谱量化为可计算的算术量。首页路线中的配套恒等式服务于这些里程碑。正比例结果、零密度例外集和指定偶数的正性分别统计和解释。经典哥德巴赫例外集论文可用于审读均值方法；本台中心窗、权重和量词须在 Lean 中另行核对。[Montgomery–Vaughan 原论文](https://doi.org/10.4064/aa-27-1-353-370)

**模数增大后，局部信息能看见什么？** TH-0059 起比较两种精度。固定 h 后，对 q≤(log n)ʰ 要求逐模数控制；在 Q=⌊n/⌊log₂ n⌋⁸⌋ 的区间 Q<q≤2Q 上则只要求模数平均。两边共用按真实余类大小加权的误差传递公式。后一分支可借鉴等差数列素数方差估计，同时要处理非单位类、真素数幂和端点取整。[等差数列中素数分布的方差研究](https://personal.science.psu.edu/rcv4/personal/Publications/vrprapg.pdf)

即使对每个大偶数 n，都能在大多数模数上看到正投影质量，这个信号仍可能完全来自和为 n±hq 的其他素数对。任务要求算清原目标的权重、剥离所有非零偏移，并利用互补除数将其变成可审计的邻和表达式。逐点谱隙目前仍是待证的核心输入。

**Growing moduli.** Seek uniform control in the logarithmic range and mean-square control in a larger dyadic block. Separate exact target sums from neighboring aliases before interpreting the model's positive mass as arithmetic evidence.

**一组可单独验收的测试窗。** 先构造支撑于 [1/3,2/3]、在 [5/12,7/12] 恒为 1 的对称光滑窗。这样对角权积分至少为 1/6，参与者不能用零窗完成归一化。固定版本 Mathlib 的最高阶 ContDiff 表示实解析；本组命题显式量化每个有限微分阶。对数坐标下支撑长度为 log 2，平移恰好 log 2 时仅可能在端点相交。证明端点的自相关积分也消失，才能严格消去显式公式中素数 2 的贡献。[固定版本 Mathlib 的微分阶定义](https://github.com/leanprover-community/mathlib4/blob/fc4f59e577feb1a4956671bc04ac18aaaf8cd842/Mathlib/Analysis/Calculus/ContDiff/Defs.lean)

**提交顺序。** 两组有限恒等式可并行领取；条件性误差合成任务可同步进行。随后提交具体测试向量或零点权的 Lean 定义及其算术解释，最后再攻逐偶数估计。终点始终要求每个偶数 n≥4 都是两个可相同素数之和，包含 4=2+2。目录 CI 将冻结终点与该自然数陈述的等价证明一同交给 Lean 检查。

**English.** The theta track requires a common normalized realization of both reflected vectors and a strict spectral gap after all errors. The character track keeps indexed multiplicities, phases and the full odd-character denominator. Its open analytic input is a uniform one-sided margin after conductor and height truncation. A dyadic result or a GRH-conditional estimate would be an intermediate result.

## 从莱文特的 Lean 工程学什么

### 新任务如何接回二元素数相关

读上游时先区分两种贡献。零点实部、从非本原特征降到本原特征以及反射有具体的上游声明；把逐块输入分别证明再合并，是可借用的证明组织方法。任务里的链接固定在同一上游提交。提交说明应写出实际使用的声明、对应的前提，以及尚缺的解析估计。

| 上游入口或现有输入 | 可并行的任务轨道 | 要交给下一步的量 |
| --- | --- | --- |
| `ClaimStrip.prim_zero`、`prim_reflect`、`strip` | 临界带反射；有限欧拉因子的损失 | 反射后零点的高度和分母界，改变模数时的乘积误差 |
| `Main.lean` 的 `LFunction_eq_zero_re` | 带重数的有限零点块 | 截断和的质量与配对剩余误差。转为完整显式公式还需尾项和零点计数 |
| 本站 `L-goldbach-grh-progression-error` | GRH 窗口估计；剩余类重组；离散换权 | 对指定区间和模数的误差，供主弧的有理相位求和使用 |
| `everyCharacter_of_row` 的分块合并方法 | 二元卷积误差；中央配对支撑 | 在同一个偶数处拆开线性误差、自相关误差和中心项，列明逐点正性尚需的下界 |

一个可单独复核的里程碑是：在显式 Dirichlet GRH 前提下，对所有充分大的 $X$、所有 $q^4\le X$ 的正模数和所有单位类，证明二进区间内的冯·曼戈尔特权至少为 $X/(2\varphi(q))$。这只控制一个素数变量；把它和反射变量组成素数对仍需逐点二元相关估计。优先攻克能控制这项相关误差的任务。

上游固定在提交 `dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9`。下面的依赖说明来自读取源码。Andrew Sutherland 公布的独立编译、标准公理审查和内核回放对应上游 Lean/Mathlib 4.33.1。本项目使用 Lean 4.36.0，目录中的解析任务显式写出所用 RH 或 Dirichlet GRH 前提。发布无条件版本须按本项目工具链验证相应依赖。[独立核验记录](https://math.mit.edu/~drew/grh/) · [作者公告](https://alpo.ge/remark.pdf)

| 源码入口 | 实际作用 | 我们怎样借用 |
| --- | --- | --- |
| [Statements.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9/src/Statements.lean) 与 [Main.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9/src/Main.lean#L40-L53) | 上游对所有正模数和特征证明右半临界带非消失，主特征在 1 的极点有单独条件。顶层将这个结论交给 zeta 和 strip。 | 先冻结每个接口的量词、特殊点与误差，再让不同团队独立证明输入。 |
| [ClaimStrip.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9/src/Development/AutomorphicArithmetic/CharacterBoxes/ClaimStrip.lean) | prim_zero 经变模与欧拉因子化到原始特征；gamma_ne_zero 与 prim_reflect 用函数方程，把左半条带的零点反射至逆特征的右侧。 | 项目先取最小输出。有限零点和任务只用零点实部；算术级数任务还需要显式公式、截断尾项、非原始特征修正和统一常数。 |
| [MainConclusion.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L973-L995) | everyCharacter_of_row 显式接收局部到整体相容性，再同 vwin_of_row 一起送入汇总定理；everyCharacter 最后填入已证输入。 | 把“若主弧超过次弧则存在素数对”与“本问题的主次弧确实满足此界”分别冻结。前一条通过后，后一条仍然开放。 |
| [EveryCharacterOfLiteratureOfVWin.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/ThirdPlaceSeries/EveryCharacterOfLiteratureOfVWin.lean#L1739-L1745) 与 [VwinOfRow.lean](https://github.com/leanprover-community/riemann-hypothesis/blob/dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9/src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean#L1669-L1671) | 深层合并了 theta 积分、局部匹配、自守输入和窗口估计。 | 可迁移的是定位与验证关键输入的方法。要把任何特定估计用于哥德巴赫，需要写出两边函数、参数范围和常数间的数学桥梁。 |

## 有限范围与充分大偶数的并行拆分

有限范围以 $4\le n<\exp(\exp 50)$ 为目标，先用原型网格核对已发表验证端点和显式陈氏阈值。领取者可分别推进局部见证、粗数因子预算、有理相位的显式误差或例外集覆盖。每个区域须留下素数对或逐点严格正余量，才能计入 $G_1$ 覆盖。充分大偶数部分同时拆出四窗谱截断和反射除数、冻结高段 Vaughan 误差的独立输入。实际有符号次弧和远频差的逐点节省仍开放。[小偶数 RFC](RFC1-小偶数上的Goldbach.md) · [充分大偶数进度审计](<checkpoint/进度审计1(2026-11-25).md>)

## 研究顺序

1. **先连通目标。** 领 `L-goldbach-prime-weight-extraction` 或 `L-goldbach-log-correlation-iff`。前者对任意支撑在素数上的实权成立，后者固定对数权并给出双向等价。随后证明 `L-goldbach-circle-coefficient`。令 $S_n(t)=\sum_{k\le n}w(k)e^{2\pi i kt}$，应提取 $S_n(t)^2$ 的第 $n$ 个系数。展开后留下 $k+j=n$；绝对值平方的展开给出 $k-j=n$，对应另一个计数。
2. **把零点信息送至主弧。** 先做有限 ζ 零点和，再审查 Dirichlet GRH 下模 $q$ 的 Chebyshev 误差。提交时写明对哪些 $q,a,X$ 同时有效。和主弧公式对接时固定分母上限、弧宽、权函数及误差相加后的量级。若用冯·芒戈尔特权，要证明并扣掉真素数幂项。短区间论文可作条件估计的复现练习，其结论只保证区间内存在一个满足条件的整数。[算术级数中的显式估计](https://arxiv.org/abs/2003.01925v4) · [主弧公式](https://arxiv.org/abs/2607.27282v2) · [Chirre–Hagen 第 5 节](https://arxiv.org/html/2512.23534v1#S5)
3. **集中攻逐点的加法相关。** 固定同一个偶数 $n$，用平滑截断 $u$ 和 $1-u$ 将上述系数分成主弧 $A_n$ 与次弧 $B_n$。接口任务先证 $\Re A_n>\lVert B_n\rVert$ 足以提取素数对。研究时也可直接给有符号的 $\Re B_n$ 下界。第一次交叉审查应列出主项下界和每项误差如何依赖 $n$。例如，对整个频率区间先取绝对值只剩 $\int |S_n|^2=\sum w(k)^2$，在对数素数权下为 $n\log n$ 量级，会丢掉抵消。另一条独立路线用反射平方差表示同一个卷积，随后需要对实际素数权给出严格余量。逐点正性和二倍区间内的线性下界均是开放攻关目标。
4. **量化例外，审查剩余缺口。** 可并行复现条件例外数结果；$E(X)\ll_\varepsilon X^{1/2+\varepsilon}$ 允许无穷多个稀疏例外。二阶矩路线要再证明真实误差在每个待判定点邻域中的振荡和能量预算。若结果只对充分大 $n$ 成立，必须列出阈值，并为余下范围提供统一数学论证。本轮任务台只发一般性定理。[例外集预印本](https://arxiv.org/html/2610.15559v1)

## 如何并行与验收

任务台优先覆盖空闲题。标记 parallel 的任务允许不同团队独立试证。新增的 100 条子命题分属十组。主弧下界与次弧逐点下界使用同一截断，合起来覆盖充分大偶数；阈值以下仍须证明。例外集的密度界独立列出。每组任务及其用途见[可领取的研究路线](https://www.goldbach.tech/?lang=zh#roadmap)。每份尝试有自己的工作目录、租约、分支和 PR；PR 说明写清采用的估计、常数依赖和仍需的假设。题目公开、命题类型检查通过和证明获得权威 ACCEPTED 是三个不同的状态。贡献者另行复核中英文陈述与 Lean 量词，原始核验日志给出证据清单。旧区间题的运行和署名继续保存在历史记录里。[旧目录](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/ac48ffd/research/gaps.json) · [验证日志](https://www.movan.tech/goldbach/#records)

## English

The target is pointwise positivity of the convolution of the prime-supported logarithmic weight at every even $n\ge4$. The active catalogue consists of two foundations, three RH/GRH tasks, six correlation tasks and four tasks on exceptions. Six research problems admit parallel independent approaches. Each frozen proposition has an English brief, a Chinese brief, and a source. The strongest entries are open problems. [Task catalogue](gaps.json)

- **Finite-range work.** Verify local covers using prime witnesses or an explicit pointwise margin. Keep rough-factor bounds and the Chen threshold as separate milestones. The large-even branch can independently verify the four-scale, divisor-switching, and high-segment error estimates. A signed pointwise bound is still needed. [Finite-range proposal](RFC1-小偶数上的Goldbach.md)

- **Read the upstream proof from the conclusion backwards.** Follow the nonvanishing theorem from Main through the reduction to primitive characters and reflection. Follow everyCharacter_of_row into the local-to-global and window inputs. Sutherland’s audit covers the published 4.33.1 project. Our conditional estimates expose their hypotheses until we can check the required dependencies under our own pinned toolchain. [Upstream statements](https://github.com/leanprover-community/riemann-hypothesis/blob/dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9/src/Statements.lean) · [Dependency closure](https://github.com/leanprover-community/riemann-hypothesis/blob/dc76b2788ef7ad0a6d2d4575ca3320a677c72cd9/src/Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean#L973-L995) · [Independent audit](https://math.mit.edu/~drew/grh/)
- **Build the interfaces first.** Extract a pair from a positive prime-weighted convolution. Prove the equivalence for logarithmic weights and the Fourier identity for the square of the exponential sum. Check that the frequency selects a sum of two primes. Prove the proper-prime-power correction whenever the argument uses von Mangoldt weights.
- **Work toward cancellation at each frequency.** A GRH estimate for primes in a progression can supply a major-arc input after the range of moduli and accumulated errors are justified. Split the coefficient at the same even integer into major and minor contributions. Prove a positive margin, or bound the real signed remainder directly. An absolute-value estimate over the full circle loses the cancellation. The alternative reflection and energy tasks expose different bounds on the same correlation. [Major-arc formula](https://arxiv.org/abs/2607.27282v2)
- **Track every remaining quantifier.** A short-interval existence theorem and an exceptional-set bound each leave a pointwise gap. For an energy approach, bound oscillation of the actual correlation and its local energy. Record any threshold and the argument extending below it. Each submission is checked against its own frozen statement in GitHub Actions. [Conditional short intervals](https://arxiv.org/html/2512.23534v1#S5) · [Exceptional-set estimates](https://arxiv.org/html/2610.15559v1)

## 核验预算 / Verification budget

按 2,000 runner 分钟作预算，只计纯检查且每次分别固定 75、250、848 秒，可做 1,600、480、141 次。设三个独立并行槽并同时收到 300 份等时提交，清空用时分别为 2 小时 5 分、6 小时 56 分 40 秒、23 小时 33 分 20 秒。实际容量取决于完整 job 时长、队列、缓存和 runner 并发。These scenarios use fixed service times, and do not estimate the mean from a median or percentile.
