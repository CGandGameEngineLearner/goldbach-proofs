# 研究路线提案：Goldbach 例外集的局部能量与 zeta 零点谱相关
#Zhexin Jiang#

**建议路线 ID**：`goldbach-exceptional-local-energy-zero-spectrum`  
**研究方向**：Goldbach exceptional set / local additive energy / zeta-zero Gram operator  
**目标**：建立一套从 Goldbach 例外点的局部加法缺陷出发，经由 zeta 零点谱相关估计，最终控制例外集的定量框架；在足够强的点态刚性估计成立时，进一步排除所有例外点。  
**状态**：新研究路线提案。文中标注为 *Open Challenge* 的命题均待证，不作为已知输入。

---

## 1. 研究动机与核心问题

令
\[
w(n)=
\begin{cases}
\log n,&n\text{ 为素数},\\
0,&\text{否则},
\end{cases}
\qquad
R(N)=\sum_{k=0}^{N}w(k)w(N-k).
\]
则
\[
R(N)>0
\iff
N=p+q\quad(p,q\text{ 均为素数}).
\]
强哥德巴赫猜想等价于
\[
\forall N\ge4,\quad 2\mid N\Longrightarrow R(N)>0.
\tag{G}
\]

定义 dyadic 区间中的例外集
\[
\mathcal E_X=
\{N\in[X,2X]\cap2\mathbb Z:R(N)=0\},
\qquad E(X)=|\mathcal E_X|.
\]

经典工作已经证明 Goldbach 例外集具有幂次节省型稀疏性，并在若干尺度上控制其局部集中程度；RH 下的短区间理论也能保证长度 \(C\log^2x\) 的区间中至少存在一个 Goldbach 数。这些结果说明例外集很小，却不能排除孤立例外或无限多个稀疏例外。

本路线希望进一步研究：

> 一个固定的 Goldbach 例外点，是否必然造成一个可量化的局部加法相关缺陷？这些局部缺陷能否通过显式公式转化为 zeta 零点 Gram 算子中的能量下界，再与全局谱能量预算比较？

拟研究的逻辑链为
\[
\boxed{
\text{Goldbach 例外}
\Longrightarrow
\text{固定加法纤维上的局部相关缺陷}
\Longrightarrow
\text{零点谱能量下界}
\Longrightarrow
\text{全局能量预算约束}.
}
\]
如果最后的预算足以排除任何非空例外集，就得到逐点 Goldbach；如果只能得到幂次节省或零密度例外，则作为独立的中间成果。

## 2. 主线 B：例外集的局部结构与加法能量

### 2.1 局部例外计数

对偶数 \(N\) 和窗口长度 \(H\)，定义
\[
E(N;H)=
\#\{m\in\mathcal E_X:|m-N|\le H\}.
\]
研究目标是建立局部例外数上界，例如在明确的尺度范围内证明
\[
E(N;H)\le C H^{1-\delta}(\log N)^A,
\]
或证明例外集在指定短窗中的局部重数有界。这里的尺度、常数依赖和 RH 等条件必须在正式定理中明确给出。

局部计数不仅用于改进例外集上界，也为后续的窗口重叠估计提供组合输入。

### 2.2 例外集的加法能量

定义
\[
A_{\mathcal E}(H)=
\#\{(a,b,c,d)\in\mathcal E_X^4:
a+b=c+d,\ |a-b|\le H\},
\]
以及平移相关
\[
C_{\mathcal E}(h)=
|\mathcal E_X\cap(\mathcal E_X-h)|.
\]

令
\[
F_{\mathcal E_X}(\alpha)
=
\sum_{N\in\mathcal E_X}e(-N\alpha),
\qquad e(t)=e^{2\pi it}.
\]
通过 Fourier 正交，适当加权的四次矩
\[
\int_0^1|F_{\mathcal E_X}(\alpha)|^4K_H(\alpha)\,d\alpha
\]
可以表示成带位移权的加法能量，其中 \(K_H\) 是选定的非负短窗核。

这部分的第一目标是建立严格的有限 Fourier 恒等式；第二目标才是利用已有局部集中结果，证明 \(A_{\mathcal E}(H)\) 或 \(C_{\mathcal E}(h)\) 的定量上界。

### 2.3 固定目标的反射相关缺陷

Goldbach 方程有一个特殊结构：固定偶数 \(N\) 后，两个加数由反射配对
\[
n\longleftrightarrow N-n
\]
联系。

选取明确的平滑权 \(a_{N,H}(n)\)，定义局部反射相关
\[
C_N(H)=\sum_{n\in\mathbb Z}
a_{N,H}(n)a_{N,H}(N-n).
\]
再通过模数、频率或尺度分解，寻求精确恒等式
\[
C_N(H)=M_N(H)+D_N(H)+T_N(H),
\tag{2.1}
\]
其中：

- \(M_N(H)\) 是局部主项；
- \(D_N(H)\) 是需要由谱方法控制的有符号双线性缺陷；
- \(T_N(H)\) 是截断、边界和换权误差。

所有权函数、支撑、归一化及三项的具体表达必须在 Lean 声明中冻结。不能只把 \(D_N=C_N-M_N-T_N\) 作为定义，再把估计 \(D_N\) 当成已解决的分析问题。

如果主项有正下界且尾项足够小，那么 \(R(N)=0\) 会迫使 \(D_N(H)\) 达到主项量级。这是一个条件性归约，真正的开放问题是证明所需主项下界、尾项估计，并找到一个可由零点谱控制的缺陷表达式。

### 2.4 例外集 Fourier 恒等式

令
\[
S_Y(\alpha)=
\sum_{p\le Y}(\log p)e(p\alpha).
\]
若 \(Y\ge2X\)，则对 \(N\in[X,2X]\)，
\[
R(N)=\int_0^1S_Y(\alpha)^2e(-N\alpha)\,d\alpha.
\]
因此
\[
0=\sum_{N\in\mathcal E_X}R(N)
=
\int_0^1S_Y(\alpha)^2F_{\mathcal E_X}(\alpha)\,d\alpha.
\tag{2.2}
\]
这是精确恒等式。它把例外集的存在转化为素数指数和与例外集 Fourier 变换之间的抵消关系。

进一步分解主弧和次弧后，若能证明主弧贡献有与 \(E(X)\) 成比例的正主项，并对次弧给出足够强的预算，就可得到例外集上界。主弧正性和次弧预算必须分别证明，不能仅由恒等式推出。

---

## 3. 主线 C：zeta 零点 Gram 矩阵与多尺度谱相关

### 3.1 从显式公式到零点响应核

短区间素数误差可以通过显式公式表示为 zeta 零点贡献加上截断、端点和素数幂误差。为便于控制端点，固定一个非负或适当正则的紧支撑平滑函数
\[
\eta\in C_c^\infty((0,\infty)).
\]
在 RH 下写 \(\rho=\tfrac12+i\gamma\)，定义平滑零点响应
\[
F_\rho(y;H)=
\int_0^\infty
\eta(t/H)(y+t)^{\rho-1}\,dt.
\]
取非负窗口权 \(W_X(y)\)，定义有限零点集合
\[
\mathcal Z_T=\{\rho:|\operatorname{Im}\rho|\le T\},
\]
并令
\[
K_{\rho,\rho'}(X,H)=
\int W_X(y)
F_\rho(y;H)\overline{F_{\rho'}(y;H)}\,dy.
\]

对任意复数系数 \(a_\rho\)，
\[
\sum_{\rho,\rho'\in\mathcal Z_T}
a_\rho\overline{a_{\rho'}}K_{\rho,\rho'}
=
\int W_X(y)
\left|\sum_{\rho\in\mathcal Z_T}a_\rho F_\rho(y;H)\right|^2dy
\ge0.
\]
因此 \(K\) 是有限 Gram 矩阵，自动半正定。这是本路线的有限维 Hilbert 空间基础。

显式公式中实际出现的系数、零点重数和截断余项必须准确纳入 \(a_\rho\)，不能把上述抽象 Gram 核直接等同于完整的素数均方。

### 3.2 对角、近对角与远对角贡献

按零点虚部差分解：
\[
K=K_{\mathrm{diag}}+K_{\mathrm{near}}+K_{\mathrm{far}}.
\]
研究内容为：

- 对角项：利用零点计数和核的大小给出显式估计；
- 近对角项：利用局部零点计数、平滑核衰减和相邻频率结构控制；
- 远对角项：研究实际加权总和的有符号抵消，争取优于逐项取绝对值的估计。

Gram 半正定性本身不提供远对角节省。RH 也不自动给出足够的零点间距或交叉项抵消。若需要额外的零点相关假设、零点间距假设或平均定理，必须显式写入相应定理的前提。

### 3.3 多尺度 Gram 算子

选取尺度 \(H_1,\ldots,H_m\) 和非负系数 \(c_j\)，定义
\[
K^{\mathrm{multi}}_{\rho,\rho'}=
\sum_{j=1}^m c_j
\int W_{X,j}(y)
F_\rho(y;H_j)\overline{F_{\rho'}(y;H_j)}\,dy.
\]
它仍然是半正定 Gram 矩阵。

开放问题是：能否选择尺度和权重，使不同零点频率在多个尺度上的响应不能同时相干叠加，从而得到比单尺度更强的均方误差上界？这需要具体的谱估计，不是半正定性的直接推论。

---

## 4. B 与 C 的合流：同一个局部能量的下界和上界

为避免两条路线仅在术语上相似，必须先固定一个共同的局部素数误差对象。选定平滑函数 \(\eta\)，定义
\[
\Delta_{H,\eta}(y)=
\sum_{n\ge1}\Lambda(n)
\eta\!\left(\frac{n-y}{H}\right)
-
H\int_0^\infty\eta(t)\,dt.
\]
对每个目标 \(N\)，选定非负窗口权 \(W_N(y)\)，定义
\[
V_N(H)=
\int W_N(y)|\Delta_{H,\eta}(y)|^2dy.
\]
窗口中心、支撑、归一化和重叠次数必须明确冻结。

B 路线希望证明：Goldbach 例外点迫使一个固定加法纤维上的双线性缺陷达到正下界，并在合适的反射／平滑转换下转化为 \(V_N(H)\) 或相关二次型的下界。

C 路线希望通过显式公式和 Gram 矩阵证明
\[
\sum_{N\in\mathcal E_X}V_N(H)
\le \mathcal U(X,H,T).
\]
若每个例外贡献至少 \(\mathcal L(X,H)\)，则
\[
E(X)\mathcal L(X,H)\le\mathcal U(X,H,T).
\]
这给出例外集的定量上界。若要推出例外集为空，还需证明在目标尺度上
\[
\mathcal U(X,H,T)<\mathcal L(X,H).
\]
如果最终只能得到 \(E(X)\ll X^{1-\delta}\)，这仍是重要的例外集成果，但不等于证明强哥德巴赫。

**核心开放挑战**：从固定 \(N\) 的 Goldbach 缺失推出一个足够强的局部双线性缺陷下界；以及用零点 Gram 结构得到足够小的全局预算。

---

# 5. 待证 Lean 引理与依赖

以下任务分为组合恒等式、有限维谱基础和真正的分析挑战。所有命题均需冻结量词、参数范围、权函数、常数依赖及 RH 等假设。

## Phase B1 — 例外集与局部加法结构

| ID | 待证内容 | 依赖 |
|---|---|---|
| `gb-exception-set-definition` | 定义有限 dyadic 区间内的偶数例外集及其基数。 | 现有 \(R(N)\) |
| `gb-local-exception-count` | 定义 \(E(N;H)\)，证明窗口包含关系和重叠计数恒等式。 | B1 |
| `gb-exception-shift-correlation` | 定义 \(C_{\mathcal E}(h)\)，证明其与例外集交集计数的关系。 | B1 |
| `gb-exception-additive-energy-identity` | 定义例外集加法能量，证明其与有限 Fourier 四次矩的精确恒等式。 | B1–B3 |
| `gb-target-reflection-correlation` | 定义固定 \(N\) 的反射相关，证明权重、支撑与端点公式。 | 现有卷积接口 |
| `gb-target-main-defect-tail-decomposition` | 对冻结的平滑权和尺度分割，证明 \(C_N=M_N+D_N+T_N\) 的精确恒等式。 | B5 |
| `gb-global-to-local-correlation-transfer` | 证明真实 \(R(N)\) 与局部相关 \(C_N(H)\) 的差等于明确的边界／截断项，并给出上界。 | B5–B6 |
| `gb-exception-forces-defect` | 在主项下界、尾项上界和全局到局部转换条件下，由 \(R(N)=0\) 推出 \(|D_N|\) 的点态下界。 | B6–B7；条件性归约 |
| `gb-exception-defect-global-energy` | 将不同 \(N\) 的缺陷写成共同 Fourier／算子对象，并控制窗口重叠。 | B8 |
| `gb-exception-pointwise-elimination-criterion` | 证明若每个例外的缺陷下界与全局预算不相容，则例外集为空。 | B8–B9；逻辑归约 |

## Phase C1 — 有限零点与 Gram 基础

| ID | 待证内容 | 依赖 |
|---|---|---|
| `gb-zero-finite-truncation` | 定义有限高度零点多重集，证明截断集合有限并保留重数。 | zeta 零点基础 |
| `gb-zero-smooth-kernel` | 定义平滑零点响应 \(F_\rho(y;H)\)，证明连续性、可测性和所需可积性。 | C1 |
| `gb-zero-gram-kernel` | 定义 \(K_{\rho,\rho'}\)，证明其与积分内积一致。 | C2 |
| `gb-zero-gram-positive-semidefinite` | 证明有限 Gram 矩阵半正定。 | C3 |
| `gb-zero-conjugate-pairing` | 处理共轭零点配对、重数和实值表达式。 | C1–C4 |
| `gb-zero-diagonal-near-far-split` | 按虚部差分解对角、近对角和远对角项并证明恒等式。 | C3 |
| `gb-zero-diagonal-bound` | 对角贡献给出明确上界。 | C6 |
| `gb-zero-near-diagonal-bound` | 对近对角零点对给出统一上界。 | C6；分析挑战 |
| `gb-zero-far-offdiagonal-cancellation` | 对实际加权远对角总和证明有符号节省。 | C6；核心开放挑战 |
| `gb-zero-multiscale-gram-positive` | 构造多尺度 Gram 矩阵并证明半正定。 | C2–C5 |
| `gb-zero-multiscale-spectral-saving` | 证明多尺度组合产生比单尺度更强的均方误差上界。 | C7–C10；核心开放挑战 |
| `gb-zero-explicit-formula-energy-transfer` | 将截断显式公式的零点二次型与短区间 \(\psi\) 均方联系，支付截断、端点和其他误差。 | C1–C11 |

## Phase BC — 两条主线的合流

| ID | 待证内容 | 依赖 |
|---|---|---|
| `gb-common-smoothed-prime-error` | 冻结 \(\eta,W_N,\Delta_{H,\eta},V_N(H)\) 的定义、支撑和可积性。 | B6、C2 |
| `gb-exception-to-bilinear-defect` | 将 \(R(N)=0\) 转化为固定 \(N\) 的反射相关缺陷恒等式。 | B5–B7 |
| `gb-bilinear-defect-to-local-energy` | 在明确平滑权和截断误差条件下，把二元缺陷下界转为 \(V_N(H)\) 或对应双线性能量下界。 | B8、共同定义；核心挑战 |
| `gb-summed-local-energy-overlap` | 对不同目标窗口求和，精确控制窗口重叠重数。 | 共同定义 |
| `gb-gram-global-energy-budget` | 通过显式公式与 Gram 核给出局部能量总和上界。 | C12 |
| `gb-exception-count-energy-inequality` | 合并局部下界与全局预算，推出例外集定量上界。 | BC 下界、上界 |
| `gb-pointwise-exception-rigidity` | 在指定尺度和明确假设下证明例外集为空。 | BC 前述任务；最高难度 |

---

# 6. 完整依赖路径

```text
B：例外集局部结构
B1 例外集定义
 -> B2 局部计数
 -> B3 平移相关
 -> B4 加法能量与 Fourier 四次矩
 -> B5 固定目标反射相关
 -> B6 主项／缺陷／尾项分解
 -> B7 全局相关到局部相关的转换
 -> B8 例外 => 点态缺陷下界（开放）
 -> B9 缺陷的全局能量表达
                         \
                          \
                           -> 共同局部能量：点态下界 + 全局预算
                          /
C：零点 Gram 谱相关       /
C1 有限零点截断
 -> C2 平滑核
 -> C3 Gram 核
 -> C4 半正定
 -> C5 共轭配对
 -> C6 对角／近／远分解
 -> C7 对角估计
 -> C8 近对角估计（开放）
 -> C9 远对角有符号抵消（开放）
 -> C10 多尺度 Gram
 -> C11 多尺度谱节省（开放）
 -> C12 显式公式能量预算
                         |
                         v
               例外集定量上界／点态刚性
                         |
             +-----------+-----------+
             |                       |
        稀疏例外集界              例外集为空
             |                       |
             v                       v
        改进短区间理论          逐点 Goldbach
```

## 7. 逻辑闭合标准

本路线有两个层次的成果：

**中间成果**：证明 \(E(X)\ll X^{1-\delta}\)、局部例外数幂次节省，或更强的局部集中性。这些结果可以独立验收，但不推出强哥德巴赫。

**最终成果**：对每个充分大 dyadic 区间证明 \(\mathcal E_X=\varnothing\)，再对分析阈值以下的偶数给出有限素数见证或严格正性证书。只有这样才能推出 (G)。

若均方分析使用 \(\Lambda\) 或 \(\psi\)，必须处理素数幂污染。令
\[
r(n)=\Lambda(n)-w(n),
\]
则
\[
R_\Lambda(N)=R(N)+2(w*r)(N)+(r*r)(N).
\]
因此从 \(R_\Lambda(N)\) 的正下界得到 \(R(N)>0\) 时，必须显式扣除后两项；不能把 \(\Lambda\)-Goldbach 正性直接等同于两个素数的表示。

---

# 8. 建议的首轮工作台任务

**第一批：可直接形式化的结构性基础**
1. `gb-exception-set-definition`
2. `gb-local-exception-count`
3. `gb-exception-shift-correlation`
4. `gb-exception-additive-energy-identity`
5. `gb-target-reflection-correlation`
6. `gb-zero-finite-truncation`
7. `gb-zero-gram-kernel`
8. `gb-zero-gram-positive-semidefinite`

**第二批：冻结真正的分析对象**
1. `gb-target-main-defect-tail-decomposition`
2. `gb-global-to-local-correlation-transfer`
3. `gb-zero-diagonal-near-far-split`
4. `gb-common-smoothed-prime-error`
5. `gb-summed-local-energy-overlap`

**第三批：核心数学挑战**
1. `gb-exception-forces-defect`
2. `gb-zero-far-offdiagonal-cancellation`
3. `gb-zero-multiscale-spectral-saving`
4. `gb-bilinear-defect-to-local-energy`
5. `gb-gram-global-energy-budget`
6. `gb-pointwise-exception-rigidity`

每个任务需冻结完整量词、参数范围、常数依赖、权函数归一化、零点截断以及 RH 等假设。Lean 的有限恒等式验收不能被描述为解析估计已经解决。

---

# 9. 参考文献与阅读顺序

1. H. L. Montgomery and R. C. Vaughan, “The exceptional set in Goldbach's problem,” *Acta Arith.* 27 (1975), 353–370. DOI: https://doi.org/10.4064/aa-27-1-353-370
2. B. Saffari and R. C. Vaughan, “On the fractional parts of \(x/n\) and related sequences II,” *Ann. Inst. Fourier* (1977).（平均化方法）
3. A. Languasco and A. Perelli, “On Linnik's theorem on Goldbach numbers in short intervals and related problems” (1994).（短区间 Goldbach 的另一类方法）
4. J. Pintz, “Landau's problems on primes,” *J. Théor. Nombres Bordeaux* 21 (2009), 357–404. https://numdam.org/item/10.5802/jtnb.676.pdf
5. J. Pintz, “A new explicit formula in the additive theory of primes with applications II. The exceptional set in Goldbach's problem” (2018). https://arxiv.org/abs/1804.09084
6. A. Chirre and M. V. Hagen, “On Goldbach numbers in short intervals” (2026).（RH 下显式短区间结果；正式引用时核对最终出版版本和定理条件）
7. Cully-Hugill and A. Dudek, “Goldbach numbers in short intervals.”（RH 下显式均方方法；引用时核对作者全名、版本、常数和适用范围）
8. E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed., revised by D. R. Heath-Brown.（显式公式与零点基础）

---

## 10. 项目核心问题

本路线拟向工作台提出的核心数学问题是：

> 能否证明每一个 Goldbach 例外点都迫使一个明确的固定加法纤维相关缺陷达到正下界；再将这些缺陷通过 zeta 零点 Gram 矩阵组织成全局能量预算，并证明该预算不足以容纳任何例外点？

**主攻顺序**：先冻结固定目标反射相关的精确分解与有限零点 Gram 核；随后研究例外点是否必然产生点态双线性缺陷，以及远对角零点对是否存在足够强的有符号抵消。只有当这两项得到定量估计，B 与 C 才能形成通向逐点 Goldbach 的完整证明链。
