# 强哥德巴赫中间命题：每个偶数的素数加四殆素数表示

**核心贡献者（原证明稿与计算证书）**　千早爱音，GitHub 账号 **Visio-Vanitas**。上游说明推导和脚本主要由作者指导 AI 辅助完成。本项目负责整理证明、复现证书和下文的替代尾段检验。[贡献者主页](https://github.com/Visio-Vanitas) · [作者说明及固定版本](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/README.md)

**命题。** 假设 Dirichlet $L$ 函数的广义黎曼猜想。对每个偶数 $N\ge4$，存在素数 $p$ 和正整数 $m$，使 $N=p+m$ 且 $\Omega(m)\le4$。这里 $\Omega$ 按重数计素因子，$\Omega(1)=0$。

**审阅状态（2026-11-26）。** 收录作者的条件证明稿。权重引理和带解析前提的归约已在 Lean 重建。58 段证书、两套尾段参数和一次直接用定义级数的尾段检验均给出正下界。本轮在下列复核范围内未发现足以推翻结论的错误。核心筛不等式仍需独立审定。[本机公理检查](lean-axioms-a5c1fa9.txt) · [历次核验记录](README.md)

## 从正权重得到四殆素数

对 $N>4\cdot10^{18}$，令 $A=\{N-p:p\le N,\ p\text{ 为素数},\ p\nmid N\}$。取 $2<z<y$，使 $zy^4\ge N$ 且 $y^5>N$。对没有小于 $z$ 的素因子的 $a\in A$ 定义

$$w(a)=1-\tfrac12\sum_{z\le q<y,\ q\mid a}1-\tfrac12\sum_{z\le q<y,\ q^2\mid a}1,$$

两处的 $q$ 都遍历素数。如果 $w(a)>0$，两个计数之和至多为一。若没有中段素因子，五个因子的积至少为 $y^5$；若有一个，它只能以一次幂出现，另四个因子的积至少为 $y^4$。两种情形都与 $a=N-p<N$ 矛盾，故 $\Omega(a)\le4$。若这些 $a$ 的权重和为正，就存在所需的 $p$。[权重引理](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/lean/AllEvenOnePlusFour/AllEvenOnePlusFour/Weights.lean)

## 三段证明及其依据

| 偶数范围 | 如何得到存在性 |
|---|---|
| $4\le N\le4\cdot10^{18}$ | Oliveira e Silva、Herzog、Pardi 的计算给出两个素数的表示，第二项已满足要求。[原验证项目](https://sweet.ua.pt/tos/goldbach.html) |
| $4\cdot10^{18}\le N<10^{500}$ | 在 58 个连续区间分别对 $A$ 下筛、对被中段素数 $q$ 整除的项上筛，再扣除平方整除项。作者的 Brun 引理给出主项和余项估计；用 GRH 下的逐模数估计控制算术误差。最小记录净下界大于 0.0016796。[分块筛推导](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/notes/block-sieve/brun-block-sieve.md) · [逐模数估计，引理 5.1](https://arxiv.org/html/2208.01229v3#S5.SS1) |
| $N\ge10^{500}$ | 先去掉指定的小素数，再在余下素数集上使用闭素数区间的乘积界和修订线性筛。两套参数分别使权重和的归一化下界大于 0.07522、0.03909。该步使用 S1–S4 的解析估计，由下述替代计算交叉检验。[线性筛各节](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/notes/linear-sieve/README.md) · [各区间回放](replay-a5c1fa9.txt) |

因此，若作者给出的解析下界在所述范围内成立，则三段覆盖全部偶数并推出命题。Lean 中仍须显式传入这些正性假设。[归约定理](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/lean/AllEvenOnePlusFour/AllEvenOnePlusFour/Reduction.lean)

## 再次检查可能使下界失效的环节

**模数、重数和余项。** 预筛时每个模数唯一写为 $ed$，其中 $e\mid Q$，而 $d$ 的素因子与 $Q$ 不相交。其系数绝对值至多为一。上筛 $A_q$ 时，$q\ge z$，$ed$ 的素因子均小于 $z$；从 $qed$ 的最大素因子可唯一恢复 $q$。因此在这一族求和中，同一个算术余项只计一次，支撑界 $ed<QD/q$ 给出 $qed<QD\le H$。若取 $|A_q|$ 作基准，展开式还包含 $-r(q)/\varphi(ed)$，且主项回代产生另一个含 $r(q)$ 的误差；程序分别以 `R2` 和 `rq` 扣除。平方整除项另扣 `q2`。中段最坏模数的平方在所有 58 段均不超过各段下端。[预筛定理及余项](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/notes/linear-sieve/S2-presieve-and-fundamental-identity.md) · [尾段实现](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/certificate/all_even_1p4_ext/tail_x31.py) · [中段精确检查](check_ladder.py)

**有限扫描与无限区间。** S3 定理 D 将跨越 $10^7$ 的素数区间在该处切开。同一端点处把 $p<x$ 改为 $p\le x$ 时，取 $x$ 从右趋向该素数；下端为素数且计入时则要加回 $1/a$。正文第 5 步保留了这项，并用奇整数上的望远镜和控制 $2/[p(p-2)]$。闭区间条件删去整除 $N$ 的素数后仍成立。该审查使用原论文所给的 Mertens 界。[S3 定理 D](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/notes/linear-sieve/S3-hypothesis-for-application.md) · [JS 引理 3.2](https://arxiv.org/html/2208.01229v3#S3)

**奇数层的低水平归纳。** 对奇数层 $n\ge3$ 和 $1\le s<3$，第一素因子必须小于 $W=D^{1/3}<z$。对 $p<W$ 有 $\log(D/p)/\log p>2$，因而可调用偶数层归纳。S1 的闭区间假设蕴含所有实端点区间的乘积界，先在 $W$ 使用分部求和，再用 $V(W)/V(z)\le K\log z/\log W=3K/s$。这两次使用乘积界合起来给积分项的系数 $K^2/s$；上游第 13 步确实保留了两次的因子。仅控制顶端 $z$ 不能直接完成第一步。本次还重跑了 `certificate/linear_sieve/core_checks.py` 中的核心常数检查。[S1 第 10–13 步](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/notes/linear-sieve/S1-core-theorem-and-induction.md#L259-L313)

**用定义级数替换筛函数表。** S1 定理 C 直接给出 $\tilde f=1-\sum_{n\ {\rm even}}f_n$、$\tilde F=1+\sum_{n\ {\rm odd}}f_n$。设 $M_n=\sup_s f_n(s)/(2e^2h(s))$。对 $2\le n\le160$ 重新生成上游 S4 网格上界；其后用 S1 第 8 步的 $M_n\le0.9607^{n-1}$，把整个几何尾和分别计入两种奇偶性的误差。得到偶数项系数和至多 $68/125$，从 $n=3$ 开始的奇数项系数和至多 $81/250$。两套上筛参数均有 $s_{\min}>3$，故 $f_1=0$。以这两个系数和直接界定上下筛函数，逐片重算上筛和误差预算，结果如下。[S1 定理 C 与通项界](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/notes/linear-sieve/S1-core-theorem-and-induction.md) · [替代计算脚本](check_tail_series.py)

| 递推 | 主项下界 | 总误差上界 | 净下界 |
|---|---:|---:|---:|
| 旧递推，$M=24$ | 0.03429439915 | 0.001323157243 | 0.03297124190 |
| 新递推，$M=22$ | 0.06752331134 | 0.001443439189 | 0.06607987215 |

净下界从完整精度向下取整，各列单独舍入。复现时运行 `python -I check_tail_series.py <上游固定版本目录>`。这条检验绕过了经典筛函数的识别和原函数表；与原证明共用 S1 定理 A、S4 的数值包络、预筛假设、逐模数估计及部分区间算术代码。即便只采用旧递推，仍得到正余量。进一步的独立审定应聚焦这些共用的推导，尤其是 S1 在奇数层 $1\le s<3$ 的归纳以及 S4 对所有网格单元的向上包络。
