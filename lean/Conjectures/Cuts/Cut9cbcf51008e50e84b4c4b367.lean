import Mathlib

/-!
# 按模数的奇偶性拆分显式等差数列误差尾界

父题断言：对每个模数 q（3 ≤ q ≤ 105）、每个与 q 互素的剩余类 a 以及每个 x ≥ 10¹²，
冯·芒戈尔特函数在该剩余类上的和与 x/φ(q) 之差不超过 x/(3360·log x)。

本文件把父题拆成两个互不依赖的闭合命题：

* 奇模数 q 的同一误差界；
* 偶模数 q 的同一误差界。

组合方式是平凡的分类：模数要么是奇数要么是偶数（用 Nat.even_or_odd 分类），
两种情形分别由对应前提直接给出。

这样拆分的理由：q 为偶数时，与 q 互素的剩余类只含奇数；把变量按 2 的幂分层
（n = 2^j·u，u 为奇数）之后，偶模数上的和可以用奇模数上的和表示，
这是显式等差数列素数定理里常用的一步化归；奇模数的情形才是需要直接处理的 core。
父题的讨论（研究台讨论区第 3817 帖）指出真正的卡点是数值零点证书的体量，
而不是解析尾界的形状；按奇偶分开后，奇模数的特征与偶模数的特征
（模 2 的幂的特征与奇模数特征的乘积）可以分开核验。
-/

-- child 1 zh: 奇模数：3 ≤ q ≤ 105 为奇数、a 与 q 互素、x ≥ 10¹² 时，误差不超过 x/(3360 log x)。
-- child 1 en: Odd modulus: for odd q with 3 ≤ q ≤ 105, a coprime to q and x ≥ 10¹², the error is at most x/(3360 log x).
-- child 2 zh: 偶模数：3 ≤ q ≤ 105 为偶数、a 与 q 互素、x ≥ 10¹² 时，误差不超过 x/(3360 log x)。
-- child 2 en: Even modulus: for even q with 3 ≤ q ≤ 105, a coprime to q and x ≥ 10¹², the error is at most x/(3360 log x).

theorem Conjectures.Cuts.Cut9cbcf51008e50e84b4c4b367
    (hOdd : (∀ (x1 x2 x3 : ℕ), (3 : ℕ) ≤ x1 → x1 ≤ (105 : ℕ) → Odd x1 → x2 < x1 → x2.Coprime x1 → (10 : ℕ) ^ (12 : ℕ) ≤ x3 → |∑ x9 ∈ Finset.range (x3 + (1 : ℕ)) with x9 % x1 = x2 % x1, ArithmeticFunction.vonMangoldt x9 - ↑x3 / ↑x1.totient| ≤ ↑x3 / ((3360 : ℝ) * Real.log ↑x3)))
    (hEven : (∀ (x1 x2 x3 : ℕ), (3 : ℕ) ≤ x1 → x1 ≤ (105 : ℕ) → Even x1 → x2 < x1 → x2.Coprime x1 → (10 : ℕ) ^ (12 : ℕ) ≤ x3 → |∑ x9 ∈ Finset.range (x3 + (1 : ℕ)) with x9 % x1 = x2 % x1, ArithmeticFunction.vonMangoldt x9 - ↑x3 / ↑x1.totient| ≤ ↑x3 / ((3360 : ℝ) * Real.log ↑x3)))
    : (∀ (x1 x2 x3 : ℕ), (3 : ℕ) ≤ x1 → x1 ≤ (105 : ℕ) → x2 < x1 → x2.Coprime x1 → (10 : ℕ) ^ (12 : ℕ) ≤ x3 → |∑ x9 ∈ Finset.range (x3 + (1 : ℕ)) with x9 % x1 = x2 % x1, ArithmeticFunction.vonMangoldt x9 - ↑x3 / ↑x1.totient| ≤ ↑x3 / ((3360 : ℝ) * Real.log ↑x3)) := by
  intro x1 x2 x3 h3 h105 hlt hcopr h12
  rcases Nat.even_or_odd x1 with hq | hq
  · exact hEven x1 x2 x3 h3 h105 hq hlt hcopr h12
  · exact hOdd x1 x2 x3 h3 h105 hq hlt hcopr h12
