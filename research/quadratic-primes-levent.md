# 用 Levent 工程的方法研究近平方素数 / Levent methods for primes of the form n²+1

问题是对任意自然数界 B，找到 n>B 使 n²+1 为素数。本次沿两条路径拆题。第一条为现有的大素因子指数 1.32301 寻找中段节省。第二条直接在 n²+1 上估计 von Mangoldt 权 Λ，再去掉真素数幂。第一条路径留下的余因子可能大于 1，第二条路径把得到真正素数值所需的额外估计单独列为 QP-0069。

For every bound B, seek n>B with n²+1 prime. One path targets a fixed saving for the existing large-prime-factor exponent 1.32301. A second path estimates the von Mangoldt weight Λ on the quadratic values and removes proper powers. A large prime factor may leave a cofactor greater than one. QP-0069 records the additional lower bound that would yield prime values.

## 研究台盘点 / Desk snapshot

2026-11-26 00:46（UTC+8）从备用入口取得权威快照，部署修订为 `4c2190575625a6193ee5dbba0c3960e07cd3ce94`。209 条题的 ID 和声明与 PR 基线 `998680d8a74fbfe1becc177ce656a88294a58e1e` 逐条相符。`proved` 显示 201 条已证、8 条开放，`desk.assignments` 为空。主域名当时直连和走代理都在 TLS 握手阶段中断。备用入口经同一个代理成功返回了完整数据。[权威快照入口 / Live API](https://www.movan.tech/goldbach/problems/quadratic-primes/api/status?view=web-gzip) · [冻结清单 / Frozen catalogue](https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/998680d8a74fbfe1becc177ce656a88294a58e1e/research/problems.json)

The alternate endpoint returned the production snapshot at 16:46 UTC on November 25. All 209 statement strings matched the PR base. The desk recorded 201 accepted tasks, eight open tasks and zero current assignments. The two early merged proof PRs cover parity and residue invariance. The live verdicts also cover all 168 local root certificates, the prime-power root bound, the interval count, log factorization, the repeated-factor bound, and the transfer from a middle saving to exponent 1.32301. [Parity PR](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/8) · [Residue invariance PR](https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/12) · [Prime-power roots](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45383712361) · [Interval count](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45385911327) · [Repeated-factor bound](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45604173391) · [Exponent transfer](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45388387378)

快照中开放的全部 ID 使用前缀 `L-quadratic-primes-`。The following suffixes identify all eight open tasks at sampling time.

| ID 后缀 / suffix | 冻结目标 / frozen target |
| --- | --- |
| `dyadic-prime-divisor` | 倍增尺度 x 上有 p>x^1.3231 / dyadic witness with p>x^1.3231 |
| `lpf-baseline` | p>n^1.323 的本站声明 / desk statement for the external 1.323 baseline |
| `lpf-first-increment` | p>n^1.32301，在无界 n 上 / on unbounded n |
| `lpf-next` | p>n^1.324，在无界 n 上 / on unbounded n |
| `lpf-endpoint` | p>n² 且 p 整除 n²+1，故 p=n²+1 / a divisor above n² equals the whole value |
| `middle-prime-saving` | 中段赋值质量小于全额预算一个固定比例 / fixed proportional saving in the middle band |
| `mid-small-uniform` | 在所有充分大尺度给 1.15 以下的子带分配 0.46 / eventual lower-band allowance 0.46 |
| `mid-high-recurrent` | 在无界尺度给 1.15 以上的子带分配 0.53 / recurrent upper-band allowance 0.53 |

平台纪录中的 1.323 来自外部工作。已核验的 `mid-compatible` 可合并旧的 0.46 与 0.53 预算。下面的分解从同一个中段父题出发，按 Fourier 频率组织估计。The published 1.323 record is external. The accepted `mid-compatible` combines the two older prime bands. The new reduction instead resolves the middle mass by Fourier frequency. [External record](https://github.com/CGandGameEngineLearner/landau-fourth-problem-1.323/blob/42cd8945093d9c82379dc9193b2e5fb6c8758c78/README.md) · [Band compatibility](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45547196206)

## 中段父题 / The middle-mass parent

令 Iₓ=(x,2x]∩ℕ，Bₓ=x log x。对每个素数 p>x，用 Wₓ,ₚ 保留 Iₓ 中满足 p¹⁰⁰⁰⁰⁰≤n¹³²³⁰¹ 的 n，用 Rₐ,ₚ 表示 r²+a≡0 mod p 的标准代表。父题的 Mₓ 逐次计算 p 在 n²+1 中的赋值，以 log p 为权。把每个首次整除事件计为一次，记总质量为 I，余下的额外赋值记为 E。零频 Z 的每个 p 项为 |Wₓ,ₚ|·|R₁,ₚ|·log(p)/p。非零频的实系数是对每对 (n,r) 求 cos(2πk(n−r)/p) 后除以 p。按 min(k,p−k)≤⌊√p⌋ 与其补集分成 L、H，保留符号并乘 log p。

Write Bₓ=x log x. For p>x take precisely the integers x<n≤2x satisfying p¹⁰⁰⁰⁰⁰≤n¹³²³⁰¹. The zero mode Z is the expected incidence from the size of this window and the actual number of roots modulo p. The low and high sums L and H split the signed nonzero Fourier coefficients at min(k,p−k)=⌊√p⌋. E charges valuations above one. All four quantities use the same x, window and logarithmic weight.

| 输入 / input | 声明内容 / obligation | 量词 / scale |
| --- | --- | --- |
| QP-0009 | Z ≤ (2/5) Bₓ | 最终一致 / eventual |
| QP-0019 | I = Z + L + H | 每个 x / every x |
| QP-0030 | E ≤ Bₓ/100 | 最终一致 / eventual |
| QP-0040 | L ≤ Bₓ/5 | 最终一致 / eventual |
| QP-0052 | H ≤ (19/50) Bₓ | 无界多个 x / unbounded x |
| QP-0062 | M = I + E，对每个固定 a>0 成立 / for each fixed a>0 | 取 a=1 / specialize at one |

**QP-0063 的组合。** 给定任意下界，取它与三个最终阈值的最大值，调用 QP-0052 选 x。用两个恒等式代换并相加，Mₓ≤(40+20+38+1)Bₓ/100。因此可以把同一个 δ=1/100 交给 `middle-prime-saving`。困难集中在 QP-0038、0039 的低频抵消和 QP-0052 的高频单侧界。这些预算是供证明或反驳的研究目标。

**QP-0063 combines the inputs.** Choose a high-mode witness beyond the requested bound and all three eventual thresholds. Substitute the two identities. The allowances sum to 99/100 of Bₓ, so δ=1/100 works for that witness and for every requested bound. The unproved estimates concern cancellation in two low-frequency prime ranges and a one-sided high-frequency bound. The existing `mass-to-increment` also needs the accepted small-prime estimate. [Middle parent](https://www.movan.tech/goldbach/problems/quadratic-primes/?lemma=L-quadratic-primes-middle-prime-saving#roadmap)

<a id="levent-grh-inputs-and-scales"></a>
### QP-0001–0009 · 零点与零频 / Zeros and the zero mode

QP-0001、0002 保留 RH 或全体 Dirichlet 特征的零点假设，QP-0005 估计模 4 的 ψ。QP-0007 只处理截断高度引入的误差项。QP-0008 的无条件入口是固定模 4 的素数定理和分部求和。根数在分裂素数处为二；除以 log x 后，从 x 到 (2x)^1.32301 的根加权调和和趋于 0.32301，留下取 2/5 的空间。

The pinned project supplies precise zero-location and explicit-formula statements. The character line and the square-root truncation are separately claimable. For the unconditional zero-mode budget, use the prime number theorem in the fixed progression 1 mod 4 and partial summation. The 4.36.0 desk types state all conditional analytic inputs explicitly. [Zero locations](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Main.lean#L43) · [Dirichlet quantifiers](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Statements.lean#L14) · [Truncated formula](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/TruncatedExplicitFormula.lean#L607)

<a id="levent-quadratic-roots-and-crt"></a>
### QP-0010–0019 · 局部根与完全正交 / Local roots and orthogonality

从已证 ± 根配对出发，构造保留代表的双射、唯一 Hensel 提升数字、互素模数的 CRT 坐标，以及带有 p=2 因子的局部密度。QP-0017 估计移动端点造成的误差；QP-0019 对原窗口完全反演。

Start with the accepted sign pairing. The new tasks transport root labels through CRT, compute the local survival density including the factor at two, and keep both endpoints when the exponent cuts the window. Applying complete additive orthogonality to this moving window recovers the first-incidence mass exactly. [Accepted sign pairing](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45392209574)

<a id="levent-factor-mass-and-sieve"></a>
### QP-0020–0030 · 重复赋值 / Excess valuations

QP-0021–0023 用逐层赋值与 x<p 排除中段立方整除。QP-0027 把已证的区间重数界限制到原指数窗口，QP-0028 将单点对数损失吸收入任意正预算。QP-0024 的 GRH 估计针对作为自变量的 n 的 Λ 权。

Restrict the accepted repeated-factor bound to the actual middle band and absorb the resulting O(log x) error into εx log x. The auxiliary progression tasks weight the variable n by Λ(n). The prime-value tasks below study Λ(n²+1), which requires separate arithmetic input. [Repeated-factor bound](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45604173391)

<a id="levent-explicit-correlation"></a>
### QP-0031–0040 · 带符号低频和 / Signed low modes

QP-0031 和 0034 分别处理平滑 Mellin 窗及按重数计的零点尾。QP-0033 把根窗系数写成两个相位和的乘积。QP-0038、0039 在 p⁵≤x⁶ 和 p⁵>x⁶ 两段寻求 3/25 与 2/25 的最终一致上界。单个线性特征的 GRH 仍留下跨素数的二次根相位相关。

The short geometric sum and its second moment give independent tests for the low modes. Bounds of 3/25 and 2/25 on the two disjoint prime ranges would give 1/5 beyond the larger threshold. The pinned unit-window zero count provides a model for the truncation estimate. Cancellation between the actual root phases as p varies remains an open input. [Unit-window zero-count statement](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AbelianVarietyTheory/PublishedTheorems/AutomorphicForms₂/ZeroCount.lean#L51)

<a id="levent-theta-prescribed-test"></a>
### QP-0041–0052 · 指定 Θ 测试 / Prescribed theta tests

取 u 为确切整数窗口的相位和、v 为全体二次根的相位和。频率 k 上的能量差 ‖u+v‖²−‖u−v‖² 给出 4 Re(u·conj v)。按 log(p)/(4p) 加权、在高频求和，得到 QP-0051 的算术匹配。若要进一步使用自守 Θ 提升，必须在同一加性特征、测度与归一化下实现这两支指定测试，并压住两次范数比较和匹配误差。

The finite transform, chirp translation, Gauss norm and polarization specify the tests before estimating them. QP-0051 identifies the finite difference of energies. Using the upstream theta kernel or Petersson norm at this point would also require concrete local and global data and compatible measures for both signs. QP-0052 asks for a bound on the actual arithmetic high modes at unbounded scales. [Heisenberg translates](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaKernelSplitPlacesEqJetClassicalThetaStatement.lean#L1335) · [Theta kernel](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ThetaKernelSplitPlacesEqJetClassicalThetaStatement.lean#L1625) · [Rallis hypotheses](https://github.com/leanprover-community/riemann-hypothesis/blob/fcb6eac7534875d32d68030967e2deae6d686151/src/Development/AutomorphicArithmetic/ThetaCorrespondence/ThetaPairLifts/LocalTypeDictionary/ThetaLiftPeterssonNormEqRallisIntegral.lean#L972)

<a id="levent-natural-quadratic-extensions"></a>
### QP-0053–0062 · 固定二次式 / Fixed quadratics

固定 a>0。对与 2a 互素的素数建立逐层根数恒等式，对 pᵏ|a 的初始坏层另计根数。平移结果式给出 h²(h²+4a) 的整除约束。QP-0062 的质量分解对所有正 a 成立，故可特化到父题。

For each positive a the valuation identity separates first incidences and repeats. The local tasks isolate singular primes and count the first singular layers. QP-0059 includes the reduced-class condition and the number of admissible roots in both the progression main term and the error.

<a id="levent-endpoint-bridge"></a>
### QP-0063 · 组合 / Middle-mass bridge

六个输入、统一尺度的选择和预算见上表。The six inputs, the choice of scale and the budget appear in the middle-mass table above.

<a id="levent-prime-values"></a>
### QP-0064–0071 · 无穷多个素数值 / Infinitely many prime values

在 (x,2x] 中，n²+1 位于相邻平方之间。复合的 Mangoldt 支撑只能来自 pᵏ，k 为不小于 3 的奇数。因此底数为 O(x^{2/3})，每个底数对应 O(log x) 个指数，每个 (p,k) 至多对应一个 n。由此可尝试证明真幂质量为 O(x^{2/3}log²x)=o(x)。剩余的 QP-0069 要求某个固定 c>0 使得无界多个 x 满足 ΣΛ(n²+1)≥cx。QP-0071 取 ε=c/2，便能在同一窗口提取素数值 n²+1。由于每个素数项权重至多 log(4x²+1)，这个输入甚至给出这些窗口中至少 cx/[2 log(4x²+1)] 个素数值。

A composite prime power on the quadratic sequence must have odd exponent at least three. Bounding its base and exponent gives a route to negligible proper-power mass. If QP-0069 supplies a linear Mangoldt lower bound along unbounded windows, take ε=c/2 in QP-0067 and use QP-0068 and QP-0070 to select a prime value. Each prime term weighs at most log(4x²+1), so such a window contains at least cx/[2 log(4x²+1)] prime values. Any one yields p=n²+1 in the frozen exponent-two endpoint. [Prime-value endpoint](https://www.movan.tech/goldbach/problems/quadratic-primes/?lemma=L-quadratic-primes-lpf-endpoint#roadmap) · [Accepted endpoint equivalence](https://github.com/CGandGameEngineLearner/goldbach-proofs/actions/runs/45360591435)

## 逻辑强度与领取 / Logical strength and task selection

QP-0069 蕴含父题 `lpf-endpoint`。它在无界多个窗口内给出量级 $x/\log x$ 的素数值，已退出默认派发。中段节省则是大素因子路线。QP-0038、0039 的低频界、合计 QP-0040 和高频界 QP-0052 均须显式领取。已知其余项时，高频项逐点等于 $M-Z-L-E$，所以高频预算正是该分解下留给总质量的剩余预算。新输入需要对实际二次根与移动窗口跨素数求和，或构造同归一化的两支 Θ 测试并控制误差。QP-0008 用固定模 4 的素数定理，QP-0009 用窗口长度界，两条仍可按配套引理领取。

QP-0069 implies the prime-value endpoint and gives at least a constant times $x/\log x$ prime values on unbounded windows. It requires explicit selection. The middle saving concerns large prime factors. The low-mode bounds QP-0038 and QP-0039, their aggregate QP-0040, and the high-mode bound QP-0052 also require explicit selection. With the other terms specified, the high mode equals $M-Z-L-E$ pointwise. An estimate requires cancellation across primes for the actual quadratic roots and moving windows, or two theta tests with a common normalization and a bound on their errors. QP-0008 follows from the prime number theorem modulo four, and QP-0009 uses the window length. Both stay in the supporting queue.

[Lean 参考证明 / Lean reference proofs](quadratic-primes-bridges.lean) 覆盖 QP-0063 和 QP-0071 的条件组合。两条编号留作路线引用，其证明收录在研究资料中。任意平移公式 QP-0042 和归一误差界 QP-0050 分别涵盖孪生素数路线的 TP-0049、0047。QP-0034 引用 TP-0022 的统一尾界。

The Lean reference proofs cover the conditional reductions QP-0063 and QP-0071. The route uses these identifiers to refer to the proofs. The catalogue offers the remaining inputs as tasks. The general shift formula QP-0042 and error bound QP-0050 cover TP-0049 and TP-0047, respectively. QP-0034 is a specialization of the uniform tail bound TP-0022.
