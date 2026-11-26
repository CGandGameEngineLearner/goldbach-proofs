# 研究路线提案：共轭轨道仿射筛与 RH 方法接口

Research proposal: a conjugacy-orbit affine sieve and possible interfaces to RH methods.

**状态：探索提案，供维护者审查。** 本文列出 36 条自然语言候选（A 组 8 条、B 组 12 条、C 组 16 条），尚未冻结 Lean 类型，未运行 Lean 编译或权威验证。编号仅用于本文，不是研究台已登记的任务 ID。本文不声称路线已成立、解决 Goldbach 或具有文献首创性。

## 动机、范围和交付目标

拟研究能否将 RH 证明内部的 theta 提升、相对迹公式等方法，与仿射筛的轨道分布工具连接，为二元 Goldbach 提供额外的带符号估计。这里尚未提取或适配任何这样的 RH 桥接定理。下列 36 条候选均为不依赖 RH 的代数、计数及局部乘积任务。

与已有 theta 反射和奇特征路线相比，本提案的具体对象是一个明确的整数矩阵共轭轨道，以及由定向二元二次型描述的纤维。这里没有构造 theta 测试向量、没有取得新谱界，也没有用 Dirichlet GRH 代替任意自守 L 函数的假设。

目标是先建立可审查的数学接口，识别哪些计数和局部公式适用。维护者确认路线及颗粒度后，再为保留的候选编写双语说明、固定 Lean 类型和正式依赖；若 Mathlib 或现有任务已有同强度结果，应直接复用。

## 统一定义

令整数 $N\ge4$，并定义
$$
A_N=\begin{pmatrix}0&-1\\1&N\end{pmatrix},
\qquad O_N=\{gA_Ng^{-1}:g\in SL_2(\mathbb Z)\}.
$$
对整数 $2\le t\le N-2$，记
$$
r=t(N-t)-1>0,\qquad k=N-2t,\qquad \Delta=N^2-4.
$$
令 $D(r)$ 为 $r$ 的正整数除数集合。对 $d\in D(r)$，定义
$$
B_d=\begin{pmatrix}t&r/d\\d&N-t\end{pmatrix},
\qquad q_d(u,v)=du^2+kuv-(r/d)v^2.
$$
$W_N(t)$ 为 $O_N$ 中对角元为 $t,N-t$、两个非对角元均为正的矩阵数。$W_N(t;H)$ 另要求两个非对角元均不超过整数 $H\ge1$。$\tau(r)=\#D(r)$；$\Omega$ 按重数计算正整数的素因子个数。

区分三个对象：完整的迹／行列式曲面、单个共轭轨道、给同一轨道点的群元素。它们的计数不能互换。

## A. 共轭覆盖、大小限制与计数对象（8 条）

| 编号 | 候选命题 | 依赖及证明入口 |
|---|---|---|
| A01 共轭坐标公式 | 若 $g=\begin{pmatrix}a&b\\c&d\end{pmatrix}$ 且 $ad-bc=1$，则 $gA_Ng^{-1}$ 的四个元素依次是 $ac+bd-Nbc$、$Nab-a^2-b^2$、$c^2+d^2-Ncd$、$Nad-ac-bd$。 | 矩阵乘法；给轨道坐标提供统一公式。 |
| A02 规范覆盖 | 对所有整数 $t$，$U_t=\begin{pmatrix}1&t\\0&1\end{pmatrix}$ 满足 $U_tA_NU_t^{-1}=\begin{pmatrix}t&t(N-t)-1\\1&N-t\end{pmatrix}$。特别每个正窗口纤维非空。 | A01；显式见证。 |
| A03 判别式与不可约性 | $(N-1)^2<\Delta<N^2$，故 $\Delta$ 非整数平方，$X^2-NX+1$ 在 $\mathbb Q$ 上不可约。 | 连续平方比较及二次判别式。 |
| A04 正窗口高度界 | 任意迹为 $N$、行列式为 1、两对角元至少为 2 的整数矩阵，其非对角元乘积为正，全部元素的绝对值不超过 $\lfloor N^2/4\rfloor$。该窗口有限，超过此高度后不再增加矩阵。 | $bc=t(N-t)-1$ 及 $t(N-t)\le N^2/4$；非零整数因子界。 |
| A05 中央化子的范数描述 | $XA_N=A_NX$ 当且仅当 $X=xI+yA_N$，此时 $\det X=x^2+Nxy+y^2$。 | 逐元素比较；供定向共轭审计使用。 |
| A06 群参数去重 | 若 $B=g_0A_Ng_0^{-1}$，所有给出 $B$ 的群元素恰为无限右陪集 $g_0C_{SL_2(\mathbb Z)}(A_N)$；$A_N$ 的非负整数次幂互异。 | A03、A05；轨道—稳定子关系及迹的递推增长。不能把群元素数直接当作轨道点数。 |
| A07 素数点目标校准 | $N$ 是两个正素数之和，当且仅当 $O_N$ 的正窗口中存在两个对角元均为素数的矩阵。 | A02、A04；正向构造，反向取迹。属于校准引理，不是分析突破。 |
| A08 准确饱和度边界 | 对正整数 $x,y\ge2$，$\Omega(xy)\le2$ 当且仅当 $x,y$ 均为素数。 | 素因子分解与 $\Omega$ 的乘法加性；一般的大 $R$ 几乎素数结论不能替代此边界。 |

## B. 整数纤维、定向判别与权重（12 条）

| 编号 | 候选命题 | 依赖及证明入口 |
|---|---|---|
| B01 完整正纤维参数化 | $d\mapsto B_d$ 是 $D(r)$ 到完整正纤维的双射，其大小为 $\tau(r)$；这里不要求属于 $O_N$。 | A04；从矩阵取下方非对角元作为逆。 |
| B02 有界纤维截断 | 两个非对角元均不超过 $H$ 的完整纤维大小为 $\#\{d\in D(r):d\le H,\ r\le Hd\}$。 | B01；$r/d\le H$ 的无除法改写。 |
| B03 定向循环向量判据 | 在任意交换环 $R$ 中，若 $B$ 的迹为 $n$、行列式为 1，则 $B$ 属于 $A_n$ 的 $SL_2(R)$ 共轭轨道，当且仅当存在 $z\in R^2$ 满足 $\det[z,Bz]=1$。整数纤维中这等价于 $q_d(u,v)=1$ 有整数解。 | Cayley–Hamilton；取 $g=[z,Bz]$。必须是行列式 $+1$，不能改为绝对值 1。 |
| B04 二次型的保定向等价 | 对迹为 $N$、行列式为 1 的整数矩阵 $B$，令 $q_B(z)=\det[z,Bz]$。则 $B\in O_N$ 当且仅当存在 $g\in SL_2(\mathbb Z)$ 使所有 $z$ 满足 $q_B(gz)=q_{A_N}(z)$。$q_{A_N}(u,v)=u^2+Nuv+v^2$，各纤维型的判别式均为 $\Delta$。 | B03；行列式协变及固定迹后的单射性。 |
| B05 带整除条件的 Pell 判据 | $B_d\in O_N$ 当且仅当存在整数 $z,v$，使 $z^2-\Delta v^2=4d$ 且 $2d\mid z-kv$。 | B03；$4dq_d=(2du+kv)^2-\Delta v^2$。整除条件不可省略。 |
| B06 单轨道权重公式 | $W_N(t)=\sum_{d\in D(r)}1_{\{\exists u,v\in\mathbb Z,\ q_d(u,v)=1\}}$。高度截断权重再乘 B02 的窗口指标。 | B01、B03；将成员判别放到有限除数集合上。 |
| B07 本原性过滤与容量 | 表示 1 必须满足 $\gcd(d,r/d,k)=1$。若 $r=\prod p^{e_p}$，满足此必要条件的除数数为 $C_t=\prod_{p\mid r,\ p\mid k}2\prod_{p\mid r,\ p\nmid k}(e_p+1)$，故 $W_N(t)\le C_t$。 | B03、B06；按每个素数在除数中的指数计数。 |
| B08 局部排除证书 | 对有限个两两互素的整数 $m_i\ge2$，$q_d=1$ 模 $\prod_i m_i$ 可解，当且仅当逐模可解；$W_N(t)$ 不超过通过全部测试的 $d\in D(r)$ 数量。 | B06、CRT；仅为排除和上界，不是整数可解性的充分条件。 |
| B09 好素数测试的局限 | 若奇素数 $p\nmid\Delta$，则每个 $q_d=1$ 模 $p$ 的解数为 $p-\chi_p(\Delta)>0$，并可提升至任意 $p^a$，$a\ge1$。 | B04、C04–C05；非退化二次型计数、非零梯度提升。这些好素数不能排除某个整数轨道候选。 |
| B10 反射权重对称 | $W_N(t)=W_N(N-t)$，且 $W_N(t;H)=W_N(N-t;H)$。 | B03、B06；$k$ 变号对应 $u$ 变号。此反射不是交换两个非对角元。 |
| B11 负范数单位不存在 | 对所有 $N\ge4$，$x^2+Nxy+y^2=-1$ 没有整数解。 | Vieta 下降：化为 $a^2+b^2+1=Nab$，$1\le a\le b$；$a=1$ 迫使 $N=3$，否则 $b'=(a^2+1)/b$ 为正整数且小于 $a$。 |
| B12 转置分离与半容量界 | $B\in O_N$ 蕴含 $B^T\notin O_N$。故互补除数 $d,r/d$ 至多一个属于本轨道，固定点也不属于，从而 $2W_N(t)\le C_t\le\tau(r)$。 | A05、B07、B11；若转置仍在本轨道，会产生行列式为 $-1$ 的中央化子。 |

A02 和 B12 给出的结构性预算为
$$1\le W_N(t)\le C_t/2\le\tau(r)/2.$$
这没有估计 $W_N(t)$ 与素数位置的相关性。尤其不能把完整曲面的 $\tau(r)$ 直接用作单轨道权重。

## C. 有限域轨道、筛密度与局部乘积（16 条）

对素数 $p$，令 $n=N\bmod p$，
$$
S_p(n)=\{B\in M_2(\mathbb F_p):\operatorname{tr}B=n,\det B=1\},
\quad O_p(n)=\{gA_ng^{-1}:g\in SL_2(\mathbb F_p)\}.
$$
对奇素数，$\chi_p$ 为二次特征，约定 $\chi_p(0)=0$。令
$$
\beta_p(N)=
\frac{\#\{B\in O_p(n):B_{11}B_{22}=0\}}{\#O_p(n)}.
$$

| 编号 | 候选命题 | 依赖及证明入口 |
|---|---|---|
| C01 完整曲面的局部纤维数 | 任意素数 $p$ 下，固定对角 $t,n-t$ 的完整纤维大小为 $p-1+p\,1_{t(n-t)=1}$。 | $bc=t(n-t)-1$；非零右端有 $p-1$ 解，零右端有 $2p-1$ 解。 |
| C02 退化对角位置数 | 奇素数 $p$ 下，$\#\{t:t(n-t)=1\}=1+\chi_p(n^2-4)$，包括判别式为零的情形。 | 配方 $(2t-n)^2=n^2-4$。 |
| C03 完整曲面点数 | 奇素数 $p$ 下，$\#S_p(n)=p(p+\chi_p(n^2-4))$。 | C01、C02，按对角位置求和。 |
| C04 正则中央化子的行列式满射 | 奇素数 $p\nmid\Delta$ 下，$A_n$ 在 $GL_2(\mathbb F_p)$ 中的中央化子的行列式映射满射到 $\mathbb F_p^\times$。 | 分裂情形用乘积；非分裂情形用有限域 $\mathbb F_{p^2}$ 的范数。 |
| C05 好素数处曲面等于单轨道 | 奇素数 $p\nmid\Delta$ 下，$S_p(n)=O_p(n)$。 | 相同可分特征多项式给出 $GL_2$ 共轭，再用 C04 修正行列式。 |
| C06 坏判别式处单轨道计数 | 奇素数 $p\mid\Delta$ 下，令 $\lambda=n/2$。单轨道 $O_p(n)$ 中 $t\ne\lambda$ 的纤维大小为 $(p-1)/2$，$t=\lambda$ 的纤维大小为 $p-1$，总数为 $(p^2-1)/2$。 | B03 的有限域版本；退化二次型的平方类判别。不是完整曲面计数。 |
| C07 模二轨道 | $N$ 偶时单轨道有 3 点，其中对角乘积为零的有 1 点；$N$ 奇时单轨道有 2 点，两点均为坏点。 | 枚举 $SL_2(\mathbb F_2)$ 的六个元素；这是必要的特殊局部因子。 |
| C08 所有素数的坏点密度 | 证明下列四分支 $\beta_p(N)$ 公式。 | C05–C07；坏点对应 $t=0$ 或 $t=n$，当 $n=0$ 时只计一次。 |
| C09 二维筛密度误差 | 奇素数 $p\nmid N$ 时 $0\le2/p-\beta_p\le4/[p(p+1)]$；奇素数 $p\mid N$ 时 $0\le1/p-\beta_p\le2/[p(p+1)]$。 | C08 分情况化简。 |
| C10 平方自由模数的群提升 | 对平方自由整数 $q\ge2$，$SL_2(\mathbb Z)\to\prod_{p\mid q}SL_2(\mathbb F_p)$ 满射。 | 初等矩阵生成和 CRT 提升参数；无需深层强逼近定理。 |
| C11 单轨道的 CRT 分解 | 对平方自由 $q\ge2$，模 $q$ 的共轭轨道与 $\prod_{p\mid q}O_p(N\bmod p)$ 双射，且等于 $O_N$ 的模 $q$ 像。 | C10、CRT；坏素数处仍使用单轨道。 |
| C12 筛事件乘法性 | 对上述模 $q$ 轨道，$q\mid B_{11}B_{22}$ 的比例为 $\prod_{p\mid q}\beta_p$；对角乘积与 $q$ 互素的比例为 $\prod_{p\mid q}(1-\beta_p)$。 | C11；区分“所有素数都整除”和“所有素数都不整除”。 |
| C13 有限模可容许性 | 对平方自由 $q\ge2$，存在轨道点使对角乘积与 $q$ 互素，当且仅当 $N$ 偶或 $q$ 奇。故所有平方自由模数均无障碍，当且仅当 $N$ 偶。 | C08、C12，或规范参数 $t$ 的 CRT。没有正窗口或高度保证。 |
| C14 归一化局部因子 | 定义 $\sigma_p=(1-\beta_p)/(1-1/p)^2$，证明下方精确公式；奇素数 $p\mid N$ 时 $\sigma_p\ge p/(p-1)>1$。 | C08；逐项比较接口。 |
| C15 截断乘积统一正下界 | 对每个偶数 $N\ge4$ 和任意有限奇素数集合 $P$，$(8/3)\prod_{p\in P}\sigma_p(N)>4/3$。 | C14；$\sigma_p\ge1-(p-1)^{-2}$，补齐整数因子后用 $\prod_{k=2}^{M}(1-k^{-2})=(M+1)/(2M)>1/2$。 |
| C16 固定目标的完整乘积 | 对每个固定偶数 $N\ge4$，按素数大小取极限的 $\mathfrak S_{\mathrm{orb}}(N)=\prod_p\sigma_p(N)$ 收敛到有限正数，且至少为 $4/3$。 | C14–C15；$p\nmid N$ 时 $\lvert\sigma_p-1\rvert\le8/p^2$，而 $p\mid N$ 只有有限多个。不声称关于 $N$ 的统一上界。 |

C08 的准确公式：
$$
\beta_p(N)=
\begin{cases}
\dfrac{(2-1_{p\mid N})(p-1)}{p(p+\chi_p(\Delta))},
& p\text{ 奇},\ p\nmid\Delta,\\
\dfrac2{p+1},&p\text{ 奇},\ p\mid\Delta,\\
\dfrac13,&p=2,\ N\text{ 偶},\\
1,&p=2,\ N\text{ 奇}.
\end{cases}
$$
C14 中，偶数 $N$ 有 $\sigma_2=8/3$。对奇素数 $p\nmid N$：
$$
\sigma_p=
\begin{cases}
1-\dfrac1{(p-1)^2},&\chi_p(\Delta)=-1,\\
1+\dfrac{3p-1}{(p+1)(p-1)^2},&\chi_p(\Delta)=1,\\
\dfrac{p^2}{p^2-1},&\chi_p(\Delta)=0.
\end{cases}
$$
奇素数 $p\mid N$ 时使用 $\sigma_p\ge p/(p-1)>1$。有限乘积严格下界与无限乘积的非严格下界分别陈述。

## 发布建议、复用与仍然开放的输入

建议优先审查 A02、A04、B03、B05、B07、B11、B12、C01、C06、C07、C08、C11，共 12 条；其余按依赖推进。B09 需要 C04–C05，并非按编号机械顺序发布。C02 可并入 C03，C04 可与 C05 合并；最终颗粒度请维护者裁定。

现有任务 L-goldbach-sieve-residue-dimension、L-goldbach-sieve-residue-crt、L-goldbach-unit-crt-product、L-goldbach-series-uniform-floor 提供可复用的局部根数、CRT 或乘积比较思路。必须比较正式类型后才确定实际依赖；它们的经典局部密度不能直接替换本文的轨道密度。此文不修改任何已发布任务、冻结声明或在途租约。

三项尚缺的实质输入：

1. 对正窗口内的实际整数轨道点建立随 $N$ 一致的分布定理，说明局部模型的适用范围、权重和误差。
2. 从 RH 新证明中定位具体定理，证明其测试对象、归一化和参数范围适用于本轨道权重或有符号相关项。
3. 获得越过筛法奇偶障碍的估计，区分素数与半素数；一般几乎素数结论不能完成 A08 所需的最小饱和度。

特别需要保持：坏判别式处完整曲面不等于单轨道；局部可容许性不提供固定正窗口内的幸存点；正局部乘积还不是已证明的素数计数渐近主项。群参数重复和固定 $N$ 的有限正窗口也阻止直接套用不受限轨道的高度渐近式。

## 文献与核验范围

以下文献提供方法动机和背景，不是对本文 36 条命题的外部验证，也不表示已有论文证明了这条 Goldbach 路线。

- Bourgain–Gamburd–Sarnak, *Affine linear sieve, expanders, and sum-product*: https://www.math.ias.edu/files/Bourgain_Gamburd_Sarnak_Affine.pdf
- Salehi Golsefidy–Sarnak, *Affine Sieve*: https://arxiv.org/abs/1109.6432
- Salehi Golsefidy–Varjú, *Expansion in perfect groups*: https://arxiv.org/abs/1108.4900
- Bourgain–Kontorovich, *On representations of integers in thin subgroups of SL2(Z)*: https://www.math.ias.edu/files/avi/Bourgain_Kontorovich.pdf
- RH 证明方法公告（theta 提升、相对迹公式等动机）：https://alpo.ge/remark.pdf
- RH/Dirichlet GRH 的公开核验范围：https://math.mit.edu/~drew/grh/ 。该范围不等于任意自守 L 函数的 GRH。

请维护者审查是否独立立项、命题颗粒度、数学表述和依赖。后续正式登记仍需逐题比对双语说明与 Lean 类型，并完成项目要求的声明检查。本 PR 仅为文档型路线提案。
