/-
L-goldbach-frontier-type2-b1-b1
==============================

目标（与 research/gaps.json 原文逐字一致）：

  Type-II 矩阵格点 (1,1)：双因子均处于平衡前缘带 (n^(1/16), n^(1/4)] 时，
  深次弧积分范数为 o(n)。

记号（命题内联定义）：
  S n u t = ∑_{k ≤ n} u k · e(k t)；
  τ₁ n m  = ∑_{a | m, n^(1/16) < a ≤ n^(1/4), n^(1/16) < m/a} (∑_{d | a, d > n^(1/16)} μ d) · Λ(m/a)；
  wideArcs n = 有理点 a/q（q ≤ n^(1/3), (a,q)=1）半径 H/(q n)、H = 256·n^(1/3)·(log₂(n+2))² 的并；
  Jdeep n u v = ∫_0^1 1_{(wideArcs n)ᶜ}(t) · S n u t · S n v t · e(−n t) dt。

证明计划（本轮尝试记录）
------------------------

1. 展开积分。由 ∫_0^1 e((a+b−n)t) dt = [a+b=n] 得
     ∫_0^1 S n u t · S n v t · e(−n t) dt = ∑_{a+b=n} u a · v b,
   故 Jdeep n u v = (∑_{a+b=n} τ₁ a τ₁ b) − ∫_{wideArcs n} S τ₁ · S τ₁ · e(−n ·) .
   目标等价于：主弧段的贡献把表示数主项吸收干净，余项 o(n)。

2. 朴素绝对界（已知，不够）。由 Cauchy–Schwarz 与 Parseval，
     ‖Jdeep n τ₁ τ₁‖ ≤ ∫_{(wideArcs n)ᶜ} |S τ₁|² ≤ ∑_{k≤n} τ₁(k)² ,
   而 τ₁ 是除数型函数，∑ τ₁² = n^{1+o(1)}，只给出 n^{1+o(1)}，比目标弱 n^{o(1)}。
   单点界 sup|S τ₁| ≪ n^{15/16+o(1)}（带内因子 ≤ n^(1/4)，Weyl/van der Corput）
   与 L² 界相乘同样越界。

3. 本轮未能跨过的缺口（严格陈述）：
     需要证明存在 δ > 0，使对深次弧上的双线性型
       B(t) = ∑_{n^(1/16) < a ≤ n^(1/4)} ∑_{n^(1/16) < b, ab ≤ n} α_a β_b e(ab t),  |α_a|,|β_b| ≤ log n,
     有   ∫_{(wideArcs n)ᶜ} |B(t)|² dt ≪ n^{1−δ}.
   这在 b₁ 带（两侧都远离 √n）上应当是经典 Type-II 双线性估计的适用范围，
   但需要在积分内同步使用两侧的交叉保存；只做单侧 Parseval 会退回 n^{1+o(1)}。

4. 已证兄弟引理给出的可复用机器：b1-b4 / b2-b4 / b3-b4 / b4-b4（PR #2489、#2492、#2494）
   各自 8k+ 行、仅依赖 Mathlib，含几何和、Ramanujan 和展开与特征大筛的分块估计；
   b4 侧用的是“因子很大 ⇒ 短几何和直接给出幂节省”，b1 侧没有这一便利，必须真做双线性。

结论：本文件给出命题原文与上述归约。核心双线性积分估计本轮尚未完成，证明处以 sorry 占位；
      这是一次公开的攻坚记录，权威内核会以 AXIOMS 一类拒绝，缺口本身仍然开放。
-/
import Mathlib


theorem PEqualNP.Outside.L_goldbach_frontier_type2_b1_b1 :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let Λ := ArithmeticFunction.vonMangoldt; let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ); let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊; let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊; let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a); let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₁ n)‖ ≤ e * (n : ℝ) := by
  -- 归约见文件头：核心缺口是深次弧上 b₁ 带双线性型的 L² 界 ∫ |B|² ≪ n^{1−δ}。
  -- 该估计尚未给出，故此处无法闭合。
  sorry
