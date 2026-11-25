# 新研究支线提案：小偶数上的哥德巴赫猜想

此处的小偶数是相对于"充分大偶数"假设的小，不代表这些偶数具有可被枚举验证的现实可能性。在本提案中，我们提议研究的范围是 $2 < n < e^{e^{50}}$ .

## 优势
* 该支线不会失败：最坏的情况下我们至少也可以移除掉陈氏定理的大偶数假设。根据[An explicit version of Chen's theorem](https://arxiv.org/abs/2207.09452)的2025年的最新结论，每一个大于$e^{e^{32.7}} \approx 1.4 \cdot 10^{69057979807814}$ 的偶数是一个素数及一个不超过两个素数乘积之和。
* 该支线必然存在创新性：如上所述，$e^{e^{50}}$不具有可被枚举验证的现实可能性，必然是已知数论的有效突破。

## 劣势
该支线不会直接证明完整哥德巴赫。

## 任务分拆考量

一个是按照双重对数尺度一口气拆分1000个任务，可以确保下游不堵塞。
另一个更聪明的做法是根据不同的估计方法的能力极限，设定拆分切口。

## 有限范围与两个验收目标

记 $X(a)=\exp(\exp a)$，$C=4\cdot10^{18}$，$T=X(327/10)$。对正整数 $s\ge2$，用 $\Omega(s)$ 表示按重数计的素因子个数。令

$$
G_r(n)\quad\Longleftrightarrow\quad
\exists\,p,s\in\mathbb N,\quad p\text{ 为素数},\quad 2\le s,\quad
p+s=n,\quad \Omega(s)\le r .
$$

**主目标是对每个 $4\le n<X(50)$ 的偶数证明 $G_1(n)$。** 两个素数可以相同，首个见证是 $4=2+2$。**陈氏定理的有限范围目标是对 $C<n\le T$ 的每个偶数证明 $G_2(n)$。** 完成后就能把陈氏结论延伸到所有偶数 $n\ge4$。[愿景原文](../../NumberTheory/docs/愿景-证明小偶数哥德巴赫猜想.md) · [全体偶数的 Lean 命题](strong-goldbach.lean)

| 偶数范围 | 已经可以引用的结论 | 本支线还需要的交付 |
| --- | --- | --- |
| $4\le n\le C$ | Oliveira e Silva、Herzog、Pardi 的已发表计算验证覆盖每个偶数，包含右端点 | 数学论证可引用该结果。若交付 Lean 定理，要有能在项目中核验的同范围证明或计算证书。[原论文](https://doi.org/10.1090/S0025-5718-2013-02787-1) |
| $C<n\le T$ | Bordignon、Johnston、Starichkova 的定理 5 对所有偶数给出 $\Omega(n-p)\le\lfloor e^{29.3}\rfloor$ 的表示 | 分区把因子数上界降至 2 可交付陈氏目标，降至 1 可交付该区的哥德巴赫目标。[定理 5](https://arxiv.org/html/2207.09452v6#Thmtheorem5) |
| $T<n<X(50)$ | 同文定理 3 给出显式 $p+P_2$ 计数下界，推论 4 还可取第二项平方自由 | 仍须逐个 $n$ 证明能取到素数。平方自由的第二项仍可能是两个不同素数之积。[定理 3](https://arxiv.org/html/2207.09452v6#Thmtheorem3) · [推论 4](https://arxiv.org/html/2207.09452v6#Thmtheorem4) |

## 双对数分区与实际切口

用愿景中的 1000 个半开区间作共同坐标。从 0 编号，令

$$
I_j=\{\,n\in\mathbb N:4\le n,\ 2\mid n,\ j/20\le\log\log n<(j+1)/20\,\},
\qquad 0\le j<1000 .
$$

目标中的每个 $n$ 恰好落入 $I_j$，其中 $j=\lfloor20\log\log n\rfloor$。$4$ 落在 $I_6$，$X(50)$ 是最后一带排除的右端点。分区的完备性只用实数的顺序和取整性质。计算一段具体的偶数时，再用有理上下界证明这段的整数端点。

| 切口 | 在网格中的位置 | 怎样分工 |
| --- | --- | --- |
| 计算验证端点 $C$ | $3.75<\log\log C<3.80$，故 $C\in I_{75}$ | 将这一带按 $n\le C$ 和 $n>C$ 切开。首个超出该验证范围的偶数是 $C+2$。 |
| 原型上界 $X(5)$ | $I_{99}$ 的右端点 | 首轮取 $4\le n<X(5)$。扣除文献覆盖后只涉及编号 75 至 99 的 25 带，第 75 带只取后段。 |
| 陈氏阈值 $T$ | $32.7=654/20$，正好是 $I_{654}$ 的左端点 | 在该带使用定理 3 时保留严格条件 $n>T$。条件 $n\le T$ 交给下侧任务，端点的归属无需判定 $T$ 的整数性。 |

用方法的有效范围决定第二层切口。比如以 $d=\gcd(n,105)$ 把一带分成至多八类，$d\mid 105=3\cdot5\cdot7$。对一个同时覆盖多个 $d$ 或多个 $j$ 的估计，只需交付一次，注明参数范围。$d=1$ 的类包含二次幂，须和其余各类一样交代去向。

令 $C_2=\prod_{p>2}(1-(p-1)^{-2})$，$\mathfrak S(n)=2C_2\prod_{p\mid n,\ p>2}(p-1)/(p-2)$，其中 $p$ 取素数。保留 $3,5,7$ 对应的三个因子，余下乘积由 $\prod_{m=7}^{\infty}(1-m^{-2})=6/7$ 从下方控制，故

$$
2C_2\ \ge\ 2\cdot\frac34\cdot\frac{15}{16}\cdot\frac{35}{36}\cdot\frac67
=\frac{75}{64},\qquad
15\mid n\ \Longrightarrow\ \mathfrak S(n)\ge\frac{75}{64}\cdot2\cdot\frac43=\frac{25}{8}.
$$

因此可把 $D_*=\{n\in I_{75}:n>C,\ 15\mid n\}$ 交给圆法组先算。这里已知的是奇异级数的下界。要报告覆盖了 $D_*$，还需把它代入同一套主弧、次弧和素数幂估计，算出严格正余量。[研究台的圆法与素数权](ROADMAP.md)

## 一个可以复算的有限范围结果

取五个候选素数 $P=(3,5,7,11,19)$。模 $210$ 的 105 个偶剩余类中，每一类 $a$ 都有一个 $p\in P$ 使 $\gcd(a-p,210)=1$。按上述次序取首个可用的 $p$，它们分别覆盖 $48,33,18,4,2$ 个此前未盖的类。整个计算只涉及模 $210$ 的整数。

~~~python
from math import gcd

remaining = set(range(0, 210, 2))
counts = []
for p in (3, 5, 7, 11, 19):
    covered = {a for a in remaining if gcd(a - p, 210) == 1}
    counts.append(len(covered))
    remaining -= covered
assert counts == [48, 33, 18, 4, 2] and not remaining
~~~

对任意偶数 $n\ge22$，按其剩余类取上述 $p$。此时 $s=n-p\ge3$，且 $s$ 的每个素因子至少为 11，所以 $11^{\Omega(s)}\le s<n$。由 $e^{3.8}<45<19\log11$ 和 $e^5<297/2<62\log11$，得到以下两个因子数上界。对 $4$ 到 $20$ 的偶数，依次取 $2+2,3+3,3+5,3+7,5+7,3+11,3+13,5+13,3+17$。

指数比较也可用有理数复算。对 $x=19/5,5,2397/1000$，在 $e^x$ 的第 24 次项后用 $\frac{x^{25}}{25!}(1-x/26)^{-1}$ 界定余项，依次得到 $e^x<45,\,297/2,\,11$。最后一式给出 $\log 11>2397/1000$。

| 范围 | 每个偶数均可取得的表示 |
| --- | --- |
| $4\le n<X(3.8)$ | $G_{18}(n)$ |
| $4\le n<X(5)$ | $G_{61}(n)$ |

在 $n=124$ 处，首个候选给出 $124-3=121=11^2$，它确实与 $210$ 互素。同一点的真素数见证是 $124=11+113$。从 $G_{18}$ 或 $G_{61}$ 推进到整片区域的 $G_1$，需要能为每个偶数选出素数余项的论证。

## 每份局部结果如何接回主目标

记 $w(k)=\log k$ 当 $k$ 为素数，其余取零，$R(n)=\sum_{k=0}^n w(k)w(n-k)$。目录中的 `L-goldbach-log-correlation-iff` 给出逐个 $n$ 的等价式 $R(n)>0\iff G_1(n)$。一份覆盖证明由两个引理组成。一条证明每个目标偶数属于某个已列区域 $D_i$，另一条对每个 $i$ 证明 $\forall n\in D_i,\ G_1(n)$。区域可重叠。已有局部结论 $G_r$ 也按 $r$ 记载，以便接手者知道仍要去掉几个素因子。[冻结声明](gaps.json)

| 交付方法 | 足以关闭一个区域 $D$ 的条件 |
| --- | --- |
| **主次弧的逐点余量** | 对同一权、同一弧划分及每个 $n\in D$，给主弧实部下界 $A(n)$、次弧实部下界 $-B(n)$。若采用 Mangoldt 权，另给至少一侧为高次素数幂的贡献上界 $P(n)$。证明 $A(n)-B(n)-P(n)>0$。采用真素数权时 $P(n)=0$。 |
| **例外数严格小于 1** | 取显式模型 $m(n)\ge b>0$。区域内每个例外点 $R(n)=0$ 都向 $\sum_{n\in D}\lvert R(n)-m(n)\rvert^2$ 贡献至少 $b^2$。证明全和 $<b^2$ 即可关闭 $D$。若只能控制例外数目，还可给出一个包含所有例外的可判定集合 $U$，再对 $U$ 中每个数证明 $G_1$。[现有二阶矩引理](gaps.json) |
| **陈氏候选中的素数** | 对固定 $n$ 取 $\mathcal C_n=\{p\text{ 素}:n-p\ge2,\ \Omega(n-p)\le2\}$。用同一非负权 $h_n(p)$ 定义 $D_h=\sum_{p\in\mathcal C_n}h_n(p)$、$J_h=\sum_{p\in\mathcal C_n}h_n(p)(-1)^{\Omega(n-p)}$。则 $D_h-J_h=2\sum_{p\in\mathcal C_n,\ n-p\ {\rm prime}}h_n(p)$。开放输入是逐点严格正的差值。若分别估计两项，两个界都须针对所选权重。[大偶数审计中的同类分拆](<checkpoint/进度审计1(2026-11-25).md#group-w>) |
| **有限见证或分块证书** | 给出已证明包含全部待查数的区间或剩余类。每个置位的偶数须对应一个 $p$、一个 $q$、二者的素性证明及 $p+q=n$。用各个见证集合的并覆盖整块，核对首尾偶数。若有剩余，把剩余集合及其完整性证明交给下一组。 |

解析估计随题给出适用端点、模数、权、误差常数和严格余量。含 GRH 等前提的结果，在兑现前提后计入无条件覆盖。复用主线形如“存在阈值”的引理时，还须证明指定的 $I_j$ 落在有效范围内。[主线的阈值任务](gaps.json) · [显式估计与有限验证的衔接](../../NumberTheory/docs/彻底证明Goldbach的分析.md#finite)

## 首批可并行的研究任务

以下 15 项是本 RFC 的建议任务，其中 11 项可从文献、已有声明或题面定义直接起步。解析组先在 $D_*$ 取 $Q=105$，以既约的 $a/q$、$1\le q\le Q$ 为中心，取圆周半宽 $Q/(qn)$。圆周 $\mathbb R/\mathbb Z$ 的测度总量取 1。两组共同使用 $S_n(\alpha)=\sum_{k=1}^n\Lambda(k)e^{2\pi i k\alpha}$，估计 $S_n(\alpha)^2e^{-2\pi i n\alpha}$ 在各自弧段的积分实部。

一个可供两组独立尝试的目标是 $A(n)\ge n$、$B(n)\le n/2$。在 $D_*$ 上有 $\log n<45$、$\sqrt n>2\cdot10^9$、$n^{2/3}>10^{12}$ 及 $\log_2 n<90$。代入第 05 题的计数式即得 $P(n)/n\le 2\cdot45^2(1/(2\cdot10^9)+90/10^{12})<10^{-5}$。因此两组也可各交付有理常数 $a,b$ 及证明 $A(n)\ge an,\ B(n)\le bn$，只要 $a-b>10^{-5}$ 就获得 $D_*$ 的真素数对。

| 编号 | 可单独验收的交付 | 本批输入 |
| --- | --- | --- |
| 01 | 证明 $j=\lfloor20\log\log n\rfloor$ 唯一选中目标带。用有理上下界核验 $4,C,T,X(5)$ 四处切口，给出第 75 带的两个互补部分。 | 可起步 |
| 02 | 对有限区域族证明覆盖合并引理。若每轮只在剩余集合 $U_i$ 中证明 $S_i$ 上的 $G_1$，证明 $U_{i+1}=U_i\setminus S_i$ 保留了所有尚可能的例外。以 $U_k=\varnothing$ 验收整块。 | 可起步 |
| 03 | 证明素数见证对分块位图的每一次置位都有效。以 $4\le n<100$ 完整回放。候选 $p=2,3,5,7$ 依次盖住 47 个偶数，余下 $98=19+79$，用试除即可核验全部素性。 | 可起步 |
| 04 | 将 $d=\gcd(n,105)$ 的八种情况制成有理下界表，证明每行的 $\mathfrak S(n)$ 下界。允许同一条证明一次交付八行，包含 $d=1$。 | 可起步 |
| 05 | 在未归一化卷积上证明 $P(n)\le 2(\lfloor\sqrt n\rfloor+\lfloor\log_2 n\rfloor\lfloor\sqrt[3]n\rfloor)\log^2n$。指定哪一侧为 $p^a,\ a\ge2$，再按指数 2 与指数至少 3 分开计数。 | 可起步 |
| 06 | 取 $\psi(x;q,a)=\sum_{k\le x,\ k\equiv a\bmod q}\Lambda(k)$。为 $1\le q\le105$、单位类 $a$、$2\le x\le X(3.8)$ 交付显式界 $\lvert\psi(x;q,a)-x/\varphi(q)\rvert\le E_q(x)$。给出所引定理的起点、常数及起点以下的界。 | 可起步 |
| 07 | 对 $D_*$ 算出主弧下界 $A(n)$。保留 $q\le105$ 截断、非单位类、弧宽和逐项求和的误差，给出该带上 $A(n)/n$ 的有理下界。 | 04、06 |
| 08 | 对 $D_*$ 的同一 Mangoldt 和，用 Vaughan 分块估计带相位 $e^{-2\pi i n\alpha}$ 的次弧积分实部。交付显式损失 $B(n)$，供 07 同尺度比较。这是逐点消去的开放题。 | 可起步 |
| 09 | 对愿景提出的 $p-1$ 辅助权，推导 $d\mid n-p,\ e\mid p-1$ 的相容条件 $\gcd(d,e)\mid n-1$。在模 $\operatorname{lcm}(d,e)$ 上重写相容项，单列素数 $p$ 整除该模数的项，供后续估计使用。 | 可起步 |
| 10 | 在 $I_{654}\cap\{n>T,\ 15\mid n\}$ 对真实陈氏候选证明 $D_h(n)-J_h(n)>0$。可试显式权 $\lvert\sum_{d\mid n-p,\ d\le u}\lambda_d\rvert^2\lvert\sum_{e\mid p-1,\ e\le v}\nu_e\rvert^2$。定理 3 给原计数的下界是 $2\cdot10^{-4}e^{-\gamma}\mathfrak S(n)n/(\log n)^2$，其中 $\gamma$ 为欧拉常数。使用新权重时需要相应的算术估计。[定理 3 的归一化](https://arxiv.org/html/2207.09452v6#Thmtheorem3) | 09 |
| 11 | 对 $I_{75}\cap\{n>C,\ \gcd(n,105)=1\}$ 选择模型 $m$，证明可计算的 $b>0$ 和方差上界 $V$，交付例外个数上界 $\lfloor V/b^2\rfloor$。该数为零即可报告此类覆盖。 | 可起步 |
| 12 | 在 $C<n<X(5)$ 上给出可判定的剩余集合 $U$，证明所有未获解析保证的偶数都落在所列区间或剩余类中。把每一类交给另一项估计或 03 的见证核验，交接时列出仍开放的类。 | 02，可接 07、08 或 11 |
| 13 | 将模 $210$ 的计算推广到给定平方自由模数 $M$ 和候选素数表。若每个小于 $y$ 的素数都整除 $M$，证明对表中素数 $p$，条件 $2\le n-p<y^{r+1}$ 与 $\gcd(n-p,M)=1$ 推出 $G_r(n)$，其中 $y\ge2,\ r\ge1$。以本 RFC 的 18、61 和 105 个剩余类校验整条推导。 | 可起步 |
| 14 | 在 $C<n\le T$ 选一片未获 $G_2$ 的区域，交付该片的显式陈氏筛下界或更小的因子数上界。优先试 $I_{75}$ 超过 $C$ 的部分，将已算出的 18 与新上界逐项比较。 | 可起步，可接 13 |
| 15 | 为 $4\le n<X(5)$ 汇总实际通过的 $G_1$ 区域及剩余集合。对 $D_*$ 检查 $A-B-P$ 的符号，对其他区域接入见证或例外定理。原型的完成条件是该范围内的每个偶数都有依据。 | 01、02 及所用区域的证明 |

原型之后，一项估计若同时适用于相邻带，直接合并这些带的覆盖。遇到新的有效端点或只能处理一部分余类时，再沿该处拆题。整条支线的交付条件是覆盖 $4\le n<X(50)$ 的每个偶数。若大偶数主线另行给出从整数 $N_0$ 起的真素数对定理，只须证明 $N_0\le 2\lceil X(50)/2\rceil$ 即可相接。右侧是第一个达到或超过本支线上界的偶数。[研究台的阈值拼接声明](gaps.json)

## 本轮目录拆分

本轮从 RFC 提取 31 项独立 Lean 声明，关联强哥德巴赫父题。先并行核验双对数端点、素数表、八类穷尽、主弧适用的显式等差数列误差，以及双除数探针的相容条件。再把已经有素数见证的目标从局部能量预算中扣掉。一个上界能证明多少覆盖，由它的实际范围和正余量决定。

粗数覆盖可沿三种模数独立验证。模 210 保留原型中的 18 和 61 两个上界。模 2310 的七个候选可得到 13 粗余项。模 30030 的十个候选可得到 17 粗余项，配合小于 200 的素数见证，以及 $e^{3.8}<16\log17$ 和 $e^5<53\log17$，分别给出 15 和 52 个素因子的待形式化上界。沿用上文的有理余项界可验证 $e^{141/50}<17$、$e^{3.8}<16(141/50)$ 和 $e^5<53(141/50)$。固定候选表的 CRT 反例也是单独任务，其结论是任意有限素数表在无界范围内都有遗漏。

有限范围的真实逐点正性仍依赖局部次弧、半素数消去或覆盖全部剩余类的见证。陈氏后备目标 $G_2$ 也须证明其阈值以下的剩余区域。粗数因子上界以各自的整数记录，真素数对才计入主目标覆盖。[研究台冻结目录](gaps.json)

| 研究台任务 | 交付 |
| --- | --- |
| [L-goldbach-finite-loglog-band-unique](https://www.goldbach.tech/?lemma=L-goldbach-finite-loglog-band-unique) | 双对数网格的唯一覆盖 |
| [L-goldbach-finite-loglog-published-boundary](https://www.goldbach.tech/?lemma=L-goldbach-finite-loglog-published-boundary) | 已发表计算端点位于第 75 带 |
| [L-goldbach-finite-even-ceiling-handoff](https://www.goldbach.tech/?lemma=L-goldbach-finite-even-ceiling-handoff) | 有限端点与大偶数阈值的拼接 |
| [L-goldbach-finite-residue-rough-210](https://www.goldbach.tech/?lemma=L-goldbach-finite-residue-rough-210) | 模 210 的粗数候选覆盖 |
| [L-goldbach-finite-rough-factor-power](https://www.goldbach.tech/?lemma=L-goldbach-finite-rough-factor-power) | 粗数门槛给素因子个数界 |
| [L-goldbach-finite-rough-candidate-lift](https://www.goldbach.tech/?lemma=L-goldbach-finite-rough-candidate-lift) | 把剩余类候选提升到每个实际偶数 |
| [L-goldbach-finite-rough-prototype-constants](https://www.goldbach.tech/?lemma=L-goldbach-finite-rough-prototype-constants) | 原型的 18 和 61 因子界所需比较 |
| [L-goldbach-finite-rough-prototype-18](https://www.goldbach.tech/?lemma=L-goldbach-finite-rough-prototype-18) | 第 75 带末端前的十八因子表示 |
| [L-goldbach-finite-rough-prototype-61](https://www.goldbach.tech/?lemma=L-goldbach-finite-rough-prototype-61) | 原型全域的六十一因子表示 |
| [L-goldbach-finite-radical-cells-lower](https://www.goldbach.tech/?lemma=L-goldbach-finite-radical-cells-lower) | 原型小素因子类型的八类穷尽 |
| [L-goldbach-finite-singular-product-lower](https://www.goldbach.tech/?lemma=L-goldbach-finite-singular-product-lower) | 奇异级数底乘积的有理下界 |
| [L-goldbach-finite-sieve-probe-crt](https://www.goldbach.tech/?lemma=L-goldbach-finite-sieve-probe-crt) | p−1 辅助权的广义 CRT |
| [L-goldbach-finite-sieve-probe-nonunit](https://www.goldbach.tech/?lemma=L-goldbach-finite-sieve-probe-nonunit) | 辅助权中的非单位素数 |
| [L-goldbach-finite-weighted-liouville-selector](https://www.goldbach.tech/?lemma=L-goldbach-finite-weighted-liouville-selector) | 陈氏权重的奇偶选择恒等式 |
| [L-goldbach-finite-exception-witness-cover](https://www.goldbach.tech/?lemma=L-goldbach-finite-exception-witness-cover) | 在已验证见证之外使用局部能量 |
| [L-goldbach-finite-exception-cover-refinement](https://www.goldbach.tech/?lemma=L-goldbach-finite-exception-cover-refinement) | 剩余集合逐轮收紧 |
| [L-goldbach-finite-witness-translate-bitset](https://www.goldbach.tech/?lemma=L-goldbach-finite-witness-translate-bitset) | 平移位图的素数见证与覆盖 |
| [L-goldbach-finite-witness-translate-through-98](https://www.goldbach.tech/?lemma=L-goldbach-finite-witness-translate-through-98) | 验证小样本位图并保留第 98 点 |
| [L-goldbach-finite-power-contamination-budget](https://www.goldbach.tech/?lemma=L-goldbach-finite-power-contamination-budget) | 第 75 带的显式真素数幂预算 |
| [L-goldbach-finite-power-count-via-exponent](https://www.goldbach.tech/?lemma=L-goldbach-finite-power-count-via-exponent) | 按平方与高次幂计污染支撑 |
| [L-goldbach-finite-band-fixed-loss-bridge](https://www.goldbach.tech/?lemma=L-goldbach-finite-band-fixed-loss-bridge) | 局部主弧余量与污染预算的严格拼接 |
| [L-goldbach-finite-fixed-progression-unit-error](https://www.goldbach.tech/?lemma=L-goldbach-finite-fixed-progression-unit-error) | 原型小模数上无条件的等差数列误差 |
| [L-goldbach-finite-fixed-nonunit-mangoldt](https://www.goldbach.tech/?lemma=L-goldbach-finite-fixed-nonunit-mangoldt) | 主弧非单位类的显式总质量 |
| [L-goldbach-finite-fixed-chi-constant-mode](https://www.goldbach.tech/?lemma=L-goldbach-finite-fixed-chi-constant-mode) | 真单位类的有理相位常数项 |
| [L-goldbach-finite-fixed-progression-phase-loss](https://www.goldbach.tech/?lemma=L-goldbach-finite-fixed-progression-phase-loss) | 显式等差数列误差传到邻近相位 |
| [L-goldbach-finite-fixed-prime-table-crt-obstruction](https://www.goldbach.tech/?lemma=L-goldbach-finite-fixed-prime-table-crt-obstruction) | 固定候选素数表存在任意大的遗漏 |
| [L-goldbach-finite-factor-window-switch](https://www.goldbach.tech/?lemma=L-goldbach-finite-factor-window-switch) | 半素数按最小因子交给双线性组 |
| [L-goldbach-finite-residue-rough-2310](https://www.goldbach.tech/?lemma=L-goldbach-finite-residue-rough-2310) | 七个候选覆盖模 2310 的偶数类 |
| [L-goldbach-finite-residue-rough-30030](https://www.goldbach.tech/?lemma=L-goldbach-finite-residue-rough-30030) | 十个候选覆盖模 30030 的偶数类 |
| [L-goldbach-finite-rough-prototype-15](https://www.goldbach.tech/?lemma=L-goldbach-finite-rough-prototype-15) | 将第 75 带的因子上界降至十五 |
| [L-goldbach-finite-rough-prototype-52](https://www.goldbach.tech/?lemma=L-goldbach-finite-rough-prototype-52) | 将原型全域因子上界降至五十二 |
