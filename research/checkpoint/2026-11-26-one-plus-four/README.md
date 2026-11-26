# 每个偶数的 1+4 表示 · 外部结果核验记录

**核心贡献者**　千早爱音（Visio-Vanitas）。[中间命题证明稿、署名与最终复核](proof.md)

2026-11-26。上游为 **Visio-Vanitas/buchstab-switching**。首轮固定提交为 `251538f165a382d0251b7e6ef983730e581ecba4`。目标是在 Dirichlet $L$ 函数的 GRH 前提下，对每个偶数 $N\ge4$ 找到素数 $p$ 和正整数 $m$，使 $N=p+m$ 且 $\Omega(m)\le4$。素因子计重数，允许 $m=1$。上游随后在 `a5c1fa9cee34de526915481f93cadeb1ea16014b` 补齐正文。当前结论为**计算可复现，完整解析论证待独立审定**。强哥德巴赫要求第二个加数也是素数。[上游固定版本](https://github.com/Visio-Vanitas/buchstab-switching/tree/251538f165a382d0251b7e6ef983730e581ecba4) · [证明路线图](https://github.com/Visio-Vanitas/buchstab-switching/blob/251538f165a382d0251b7e6ef983730e581ecba4/notes/proof-map.md)

## 首轮快照的关键证明文件缺失

用 `git ls-tree -r -l HEAD notes` 直接检查提交对象，`block-sieve/brun-block-sieve.md`、`linear-sieve/README.md` 和 `linear-sieve/S1…S6` 全部指向同一个 **0 字节**的 Git blob `e69de29bb2d1d6434b8b29ae775ad8c2e48c5391`。检查当时公开分支的历史，这些路径只在该次提交出现。可读的框架笔记保留了公共权重论证，并明确标出其旧尾段推导已被取代。现有源码和路线图给出了公式，但无法逐行核验作者引用的分块筛引理 A–F、预筛后的线性筛归纳、无限尾段的估计，也无法据此确认对 BJS 定理 6 的勘误。下节记录补件后的复查。[Git 对象清单](proof-files.txt) · [框架笔记](https://github.com/Visio-Vanitas/buchstab-switching/blob/251538f165a382d0251b7e6ef983730e581ecba4/notes/frame-weighted-inequality.md)

## 补件复核 · a5c1fa9

补件提交的 Git 对象包含 Brun 正文（26,247 字节）和线性筛 S1–S6（每份 15,864–42,254 字节），Lean 的归约现以 $10^{500}$ 分段。独立脚本复查了新版全部 58 段，得到与首轮相同的精确最小余量。新版预筛输入仍是相同的 SHA-256，递推 JSON 改了格式，所用两行的有理数分子和分母逐一与本次重算一致。[补件差异](https://github.com/Visio-Vanitas/buchstab-switching/compare/251538f165a382d0251b7e6ef983730e581ecba4...a5c1fa9cee34de526915481f93cadeb1ea16014b)

补件后抽查了以下论证。

- Brun 引理 D 把每个边界对赋给首个超出上限的分块。最小素因子唯一确定该对，其余素因子都落在同一个上段；因此按大小为 $m_i+1$ 的子集计数给出上界。把基本对称和用 $S_i^{m_i+1}/(m_i+1)!$ 控制，再除以该上段的筛积，就得到脚本使用的误差式。删去整除 $N$ 的素数使分子上界减小、筛积增大。同一组参数由此可以覆盖区间内不同的 $N$。[Brun 正文，第 7 步](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/notes/block-sieve/brun-block-sieve.md#L95-L103)
- S5 命题 N 的三素数算例取 $53,829,10007$。逐个半开区间的乘积均望远镜消去。重新计算得 $10007^2=100140049<829\cdot53^3=123419033$，唯一三元组满足计数条件。用 60 位十进制对数代入得到 $T_3/V(z)\approx0.5192631307193342$，与正文相符。这只核对该算例的左侧及半开假设，整个修订定理还需要审阅 S1 的归纳、S2 的预筛恒等式、S3 的无限尾部与 S4 的递推界。[S5 算例](https://github.com/Visio-Vanitas/buchstab-switching/blob/a5c1fa9cee34de526915481f93cadeb1ea16014b/notes/linear-sieve/S5-half-open-hypothesis-fails.md#L105-L123)

两次项目构建均使用 Lean 4.37.0-rc1 和 Mathlib `31ce06ea`。首轮的公理输出保存在 [首轮公理检查](lean-axioms.txt)。两版的 GRH 命题在项目中都作为输入，未重新构建 Alpöge 上游。

新版完整回放末行同样为 `ALL PASS`。直接运行 `lake build` 和 `lake env lean AxiomsCheck.lean` 均成功，权重引理和带输入的归约只列出 `propext`、`Classical.choice`、`Quot.sound`。挑战声明另列 `sorryAx`。这是本机生成的输出，不能据此消除归约定理的解析前提。[新版公理检查](lean-axioms-a5c1fa9.txt) · [新版逐段回放](replay-a5c1fa9.txt)

复查补件时，检出 `a5c1fa9cee34de526915481f93cadeb1ea16014b`，将下文回放命令的两个输入前缀改为 `data/certificate/`，预筛日志及递推常数的前缀改为 `data/linear_sieve_inputs/`。对递推常数按 `C1_num`、`C1_den`、`C2_num`、`C2_den` 四个整数字段比较。Lean 命令在上游 `lean/AllEvenOnePlusFour` 目录运行。

## 两版共用的数值结果

| 范围或检查 | 本次结果 | 核验边界 |
|---|---|---|
| $4\le N\le4\cdot10^{18}$ | 核对 Oliveira e Silva、Herzog、Pardi 的公开验证范围 | 引用已发表计算，未重新枚举 |
| $4\cdot10^{18}\le N<10^{500}$ | 上游程序重新计算 58 段；每段的 $z,y$ 和净下界都与存档一致 | 已收到正文，检查了分块误差与最大模数，完整解析论证待独立审定 |
| 两套尾段参数 | 新递推下界 **0.07522339468**，旧递推 **0.03909653631** | 二者共用线性筛和误差估计，不能视为两个独立证明 |
| 预筛，`k=80` | 单独重跑至 $10^7$，664578 个奇素数，最大 9999991；输出逐行与已提交日志一致。闭素数区间最差对为 (83,83)，总上界 0.01238550780，小于 1/80 | 超过扫描界采用上游解析估计 |
| 递推常数 | 从网格重新生成 `80:old`、`80:new`，两条记录逐字段相等，包括四组有理数的分子、分母 | 证实常数计算可复现；递推适用性仍需证明 |
| 回归测试 | Python 3.12.10，开启完整回归后 **29 passed** | 测试集中也保留旧方案，最终版本另跑上述 58 段与尾段 |

本项目另用标准库整数和有理数写了交叉检查，逐段验证端点连续、权重的两个幂次条件、分块端点与奇偶性、上下筛的最大模数平方不超过区间下端、三个已记录误差上界之和以及净下界的舍入方向。58 段全部通过。最小记录下界是 **0.0016796250582272578…**，位于 $[10^{390},10^{400})$。路线图中的“≥ 0.00168”向上取整了，严格不等式可写成“> 0.0016796”。旧尾段的“≥ 0.03910”同理可写成“> 0.03909”。两处均保留严格正余量。[独立检查脚本](check_ladder.py) · [本机回放日志](replay.txt) · [小范围验证来源](https://sweet.ua.pt/tos/goldbach.html)

## 数学接口与首轮 Lean 分界

筛去 $z$ 以下的素因子后，正权重只允许 $[z,y)$ 内出现至多一个素因子，且只能出现一次；平方整除会再扣半个单位的权重。若有五个素因子，乘积至少为 $y^5$ 或 $zy^4$，与 $m=N-p<N$ 及所选参数矛盾。这一步把任务化为证明每个偶数的加权和为正。

对照 Johnston–Starichkova 引理 5.1，显式等差数列误差的条件为 $x\ge X_2\ge4\cdot10^{18}$、$3\le d\le\sqrt{x}$ 且余类与模数互素。逐段独立检查了上下筛模数上界，筛集排除了整除 $N$ 的素数，$d=1$ 的余项为零。中段源码分别扣除下筛的模数余项、上筛 $A_q$ 的余项与平方整除项。分项的数值均已计入；其解析上界是否对区间内每个 $N$ 统一成立，仍是补件后要审的核心。[原论文引理 5.1](https://arxiv.org/html/2208.01229v3#S5.SS1) · [中段计算](https://github.com/Visio-Vanitas/buchstab-switching/blob/251538f165a382d0251b7e6ef983730e581ecba4/certificate/all_even_1p4_ext/regime2_brun.py)

Lean 的目标声明以 `sorry` 占位。归约定理额外接收 `ConditionalInputs`，其中包含有限范围的 Goldbach 输入，以及在 GRH 下两段筛和为正的输入；首轮归约以 $10^{170}$ 分段。实际证书在 $10^{500}$ 切换，拼接时需把两个数值区间对应到归约前提。作者提及的后续 comparator 输出及 1+3 不在本次固定版本核验范围。[归约源码](https://github.com/Visio-Vanitas/buchstab-switching/blob/251538f165a382d0251b7e6ef983730e581ecba4/lean/AllEvenOnePlusFour/AllEvenOnePlusFour/Reduction.lean)

就文献基准而言，Johnston–Starichkova 给出 GRH 下的 31，Johnston 学位论文将其降到 16。与后者相比，1+4 声称在保持“每个偶数”量词的同时，将第二项的素因子数从 16 降为 4。[Johnston 学位论文摘要，定理 2](https://www.cambridge.org/core/journals/bulletin-of-the-australian-mathematical-society/article/new-explicit-and-asymptotic-results-in-sieve-theory/A9B64147E850C2262594DA5439FC45A9)

## 复现首轮快照

下面是 POSIX shell 命令。Windows 首次运行时，Git 的 CRLF 转换改变了尾段输入的 SHA-256。以 `core.autocrlf=false` 检出固定版本可保留原始字节。回放脚本有些失败路径只打印结果，验收应检查完整输出（58 行分段 PASS、2 行尾段 PASS、端点检查及末行 ALL PASS）。本机实际使用的输入哈希在回放日志首两行。

```sh
git clone -c core.autocrlf=false https://github.com/Visio-Vanitas/buchstab-switching
cd buchstab-switching
git checkout --detach 251538f165a382d0251b7e6ef983730e581ecba4
git ls-tree -r -l HEAD notes
python -m venv ../audit-env
. ../audit-env/bin/activate
python -m pip install pytest
ALL_EVEN_1P4_FULL=1 python -m pytest -q certificate/all_even_1p4/tests
python -I certificate/all_even_1p4_ext/replay.py data/x32_brun_integrated/ladder_4e18_500_all.json data/x32_brun_integrated/tail/tail_at_500.json
python -I certificate/linear_sieve/hstar_rows.py 10000000 20000 > ../hstar-fresh.txt
diff --strip-trailing-cr data/x31_tail_n3/logs/hstar.log ../hstar-fresh.txt
python -I certificate/linear_sieve/run_cn.py 80
python -c "import json; row=json.load(open('cn_rows_80.json')); ref=json.load(open('data/x31_tail_n3/cn_rows_all.json')); assert all(row[k]==ref[k] for k in ('80:new','80:old'))"
```

独立脚本从本核验目录运行，以 `ladder_4e18_500_all.json` 的实际路径作唯一参数。它独立检查上述整数条件与误差加总，使用上游给出的分项界。
