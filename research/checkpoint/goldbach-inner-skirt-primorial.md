# 宽弧内层的模型项与算术障碍

父题为 `L-goldbach-wide-remainder-inner-floor`。本记录审查 [#3806 的模型项推导](https://github.com/CGandGameEngineLearner/goldbach-proofs/discussions/3806#discussioncomment-19967400)。频率核可对照 `L-goldbach-skirt-paired-annulus-kernel`。以下推导处理按分母求和的模型，实际弧集合的重叠及素数和与模型之差另需控制。

设 $Q=(\lfloor\log_2(n+2)\rfloor)^2$，$B=\lfloor n^{1/3}\rfloor$，$J_q$ 为该评论中两个宽度间的非负 Fejér 核积分。模型项为 $\sum_{Q<q\le B}\mu(q)^2c_q(n)J_q/\varphi(q)^2$。

## 为什么去掉符号会丢掉主量

取 $n=\prod_{p\le y}p$。由 Chebyshev 估计，$\log n\asymp y$，故 $Q\asymp y^2$。取三个互异素数 $p_i\in(y^{4/5},y]$ 并令 $q=p_1p_2p_3$。则 $y^{12/5}<q\le y^3$，充分大时全部落在 $(Q,B]$。因 $q\mid n$，每个既约分子给出的相位均为 1，故 $c_q(n)=\varphi(q)$。

这些分母贡献的无权绝对系数和有正的常数下界。确实，按素数的 Mertens 定理，$\sum_{y^{4/5}<p\le y}1/p\to\log(5/4)$。展开三次方，含重合素数的总贡献趋零；无序的互异三元组给出极限 $\log(5/4)^3/6$，且 $1/\varphi(q)\ge1/q$。

核权也不能消去这一障碍。对上述所有 $q$，内宽乘以 $n$ 为 $Q/q=o(1)$，外宽乘以 $n$ 为 $Qn^{1/6}/q\to\infty$，两者都一致。因此区间 $[1/(8n),1/(4n)]$ 最终全落在环带中。在这段上，$|K_n(\beta)|=|\sin(\pi(n+1)\beta)/\sin(\pi\beta)|\gg n$，所以 $J_q\gg n$。沿这列偶数，绝对值加权和至少是 $cn$，其中 $c>0$ 与 $y$ 无关。这个正贡献有利于父题的单侧下界。它排除了用全和绝对值为 $o(n)$ 来获得该下界的办法。

## 可检验的替代方向

对平方自由的 $q$ 令 $g=(q,n)$、$r=q/g$。则 $g\mid\operatorname{rad}(n)$，$(r,n)=1$，按素因子分解有 $c_q(n)=\varphi(g)\mu(r)$。模型项可按 $g$ 分组，内和权重为 $\mu(r)J_{gr}/(\varphi(g)\varphi(r)^2)$。只取 $Q<gr\le B$。这里必须保留 $r=1$ 的正项，也要计入 $g\le Q$ 时由截断造成的缺项。

可先检验一个较弱的中间命题：对于每个固定 $0<\eta<1$，限制 $g\le Q^{1-\eta}$ 的部分为 $o(n)$，并要求对充分大的所有偶数一致。此范围有 $r>Q^\eta$；利用 $J_q\le n+1$ 及 $1/\varphi(r)^2\ll_\delta r^{-2+\delta}$，余尾可获幂次节省。外和 $\sum_{g\mid\operatorname{rad}(n)}1/\varphi(g)=n/\varphi(n)\ll\log\log n$。故这一段可作为组合证明中的已知工具推论。真正需要研究的是 $g>Q^{1-\eta}$ 时保留符号的下界，尤其是 $g$ 在 $Q$ 两侧时的截断误差。它推进的是模型项；其余频段、几何重叠和素数和误差仍须单独估计。

以上为数学草案，未取得 Lean 裁决，也未计入新发布任务。
