import Mathlib

/-!
# 按模数的奇偶性拆分显式等差数列误差的窗口段后半

父题断言：对每个模数 q（3 ≤ q ≤ 105）、每个与 q 互素的剩余类 a 以及每个
10¹⁰ ≤ x ≤ 10¹²，冯·芒戈尔特函数在该剩余类上的和与 x/φ(q) 之差不超过
4·√x + log x（一段长度约为 10¹² 的有限计算）。

本文件把父题拆成两个互不依赖的闭合命题：

* 奇模数 q 的同一误差界；
* 偶模数 q 的同一误差界。

组合方式是平凡的分类：模数要么是奇数要么是偶数（用 Nat.even_or_odd 分类），
两种情形分别由对应前提直接给出。

这样拆分的理由：q 为偶数时，与 q 互素的剩余类只含奇数。以 q = 2m（m 为奇数）为例，
模 2m 的类 a 恰是模 m 的类 a 中的奇数，而模 m 的类 a 里的偶数写成 n = 2k 之后
对应模 m 的类 2⁻¹a，所以
ψ(x; 2m, a) = ψ(x; m, a) − ψ(x/2; m, 2⁻¹a)，
其中 x/2 处取整。也就是说偶模数上的和可以化成奇模数上的和（点 x 与点 x/2），
4 整除 q 时同理按 2 的幂逐层化归；奇模数的情形才是需要直接处理的 core。
同一路线的窗口段前半（8·10⁹ ≤ x ≤ 10¹⁰）与尾段（x ≥ 10¹²）各有一套按奇偶拆分的文件，
三处合起来覆盖整条路线上的全部模数。
-/

-- child 1 zh: 奇模数：3 ≤ q ≤ 105 为奇数、a 与 q 互素、10¹⁰ ≤ x ≤ 10¹² 时，误差不超过 4√x + log x。
-- child 1 en: Odd modulus: for odd q with 3 ≤ q ≤ 105, a coprime to q and 1e10 <= x <= 1e12, the error is at most 4 sqrt x + log x.
-- child 2 zh: 偶模数：3 ≤ q ≤ 105 为偶数、a 与 q 互素、10¹⁰ ≤ x ≤ 10¹² 时，误差不超过 4√x + log x。
-- child 2 en: Even modulus: for even q with 3 ≤ q ≤ 105, a coprime to q and 1e10 <= x <= 1e12, the error is at most 4 sqrt x + log x.

theorem Conjectures.Cuts.Cut8c8c40403c2e0b29e5a525f1
    (hOdd : (∀ (x1 x2 x3 : ℕ), (3 : ℕ) ≤ x1 → x1 ≤ (105 : ℕ) → Odd x1 → x2 < x1 → x2.Coprime x1 → (10 : ℕ) ^ (10 : ℕ) ≤ x3 → x3 ≤ (10 : ℕ) ^ (12 : ℕ) → |∑ x10 ∈ Finset.range (x3 + (1 : ℕ)) with x10 % x1 = x2 % x1, ArithmeticFunction.vonMangoldt x10 - ↑x3 / ↑x1.totient| ≤ (4 : ℝ) * √↑x3 + Real.log ↑x3))
    (hEven : (∀ (x1 x2 x3 : ℕ), (3 : ℕ) ≤ x1 → x1 ≤ (105 : ℕ) → Even x1 → x2 < x1 → x2.Coprime x1 → (10 : ℕ) ^ (10 : ℕ) ≤ x3 → x3 ≤ (10 : ℕ) ^ (12 : ℕ) → |∑ x10 ∈ Finset.range (x3 + (1 : ℕ)) with x10 % x1 = x2 % x1, ArithmeticFunction.vonMangoldt x10 - ↑x3 / ↑x1.totient| ≤ (4 : ℝ) * √↑x3 + Real.log ↑x3))
    : (∀ (x1 x2 x3 : ℕ), (3 : ℕ) ≤ x1 → x1 ≤ (105 : ℕ) → x2 < x1 → x2.Coprime x1 → (10 : ℕ) ^ (10 : ℕ) ≤ x3 → x3 ≤ (10 : ℕ) ^ (12 : ℕ) → |∑ x10 ∈ Finset.range (x3 + (1 : ℕ)) with x10 % x1 = x2 % x1, ArithmeticFunction.vonMangoldt x10 - ↑x3 / ↑x1.totient| ≤ (4 : ℝ) * √↑x3 + Real.log ↑x3) := by
  intro x1 x2 x3 h3 h105 hlt hcopr hlo hhi
  rcases Nat.even_or_odd x1 with hq | hq
  · exact hEven x1 x2 x3 h3 h105 hq hlt hcopr hlo hhi
  · exact hOdd x1 x2 x3 h3 h105 hq hlt hcopr hlo hhi
