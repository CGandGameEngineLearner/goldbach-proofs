import BombieriVinogradov.Assembly.SiegelWalfisz.Main
import M8a
import P17_T1_reduction

/-!
# P33 · 从 vendored `siegel_walfisz` 到 `T1'`（每特征 Siegel–Walfisz）

`vendor/bv` 里 `kimihiro64/bombieri-vinogradov` 的机器可检定理

```lean
theorem BombieriVinogradov.SiegelWalfisz.siegel_walfisz :
    ∃ a : ℝ, 0 < a ∧ ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧
      ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → ∀ {x : ℕ}, 2 ≤ x →
        (N : ℝ) ≤ (Real.log x) ^ A →
          ‖characterChebyshevSum x χ‖ ≤ C * ((x : ℝ) * Real.exp (-(a * Real.sqrt (Real.log x))))
```

给出的是**自然端点**上的界，而我们的 `DgBmorM8a.psiChiR χ x` 是
`Σ_{k ≤ ⌊x⌋₊} χ(k)Λ(k)`（实端点，`range (⌊x⌋₊+1)`）。本文件把两者接起来：

* `characterChebyshevSum n χ = psiChi χ n`（都是 `Σ_{k∈Icc 1 n} Λ k · χ k`，只是因子次序）；
* `psiChiR χ x = psiChi χ ⌊x⌋₊`（定义上相等）；
* 实端点 `x` 与整数端点 `n = ⌊x⌋₊` 之间：`n ≤ x`、`n ≥ x/2`（`x ≥ 2`），
  故 `log n ≥ log x / 4`（`x ≥ e^{10}`），于是 `√(log x)/2 ≤ √(log n)`，
  指数因子放大为 `exp(-(a/2)·√log x)`——**速率减半，常数不变**；
* `N ≤ 105 ≤ 5^5 ≤ (log n)^5`（因 `n ≥ e^9`，取 `A = 5`）；
* 取 `X = exp 10`。

最后经 `DgBmorP17.T1_of_per_character` 得 `DgTargetT1.T1`。
-/

open scoped BigOperators

namespace DgBmorP33

open ArithmeticFunction (vonMangoldt)

/-! ## 1. 端点形状转换 -/

/-- `psiChi`（`range (n+1)`，特征在前）等于 `Σ_{k ∈ Icc 1 n} Λ k · χ k`
（vendored 开发使用的形状）。 -/
theorem psiChi_eq_sum_Icc {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    DgBmorM8a.psiChi χ n
      = ∑ k ∈ Finset.Icc 1 n, (vonMangoldt k : ℂ) * χ (k : ZMod q) := by
  have hrange : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : χ ((0 : ℕ) : ZMod q) * (vonMangoldt 0 : ℂ) = 0 := by simp
  rw [DgBmorM8a.psiChi, hrange, Finset.sum_insert (by simp), h0, zero_add]
  exact Finset.sum_congr rfl fun k (_ : k ∈ Finset.Icc 1 n) => mul_comm _ _

/-- vendored 的 `characterChebyshevSum` 与我们的 `psiChi` 完全一致。 -/
theorem characterChebyshevSum_eq_psiChi {m : ℕ} [NeZero m]
    (χ : DirichletCharacter ℂ m) (n : ℕ) :
    BombieriVinogradov.SiegelWalfisz.characterChebyshevSum n χ = DgBmorM8a.psiChi χ n := by
  rw [psiChi_eq_sum_Icc]
  rfl

/-- 实端点的 `psiChiR` 只依赖 `⌊x⌋₊`（定义上相等）。 -/
theorem psiChiR_eq_psiChi_floor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    DgBmorM8a.psiChiR χ x = DgBmorM8a.psiChi χ ⌊x⌋₊ := rfl

/-! ## 2. 初等估计 -/

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

theorem sqrt_div_four {u : ℝ} (hu : 0 ≤ u) : Real.sqrt (u / 4) = Real.sqrt u / 2 := by
  have h : (Real.sqrt u / 2) ^ 2 = u / 4 := by
    rw [div_pow, Real.sq_sqrt hu]
    norm_num
  rw [← h, Real.sqrt_sq (by positivity)]

theorem sqrt_half_le {u v : ℝ} (h : u / 4 ≤ v) (hu : 0 ≤ u) :
    Real.sqrt u / 2 ≤ Real.sqrt v := by
  have h1 : Real.sqrt (u / 4) ≤ Real.sqrt v := Real.sqrt_le_sqrt h
  rwa [sqrt_div_four hu] at h1

/-! ## 3. 实端点搬运（速率减半，常数不变） -/

/-- 自然端点的每特征界 ⟹ 实端点的每特征界（`c ↦ c/2`，`X = e^{10}`）。 -/
theorem psiChiR_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C) (hq105 : q ≤ 105)
    (hbound : ∀ n : ℕ, 2 ≤ n → (q : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 →
      ‖DgBmorM8a.psiChi χ n‖ ≤
        C * (n : ℝ) * Real.exp (-(a * Real.sqrt (Real.log (n : ℝ)))))
    {x : ℝ} (hx : Real.exp 10 ≤ x) :
    ‖DgBmorM8a.psiChiR χ x‖ ≤ C * x * Real.exp (-((a / 2) * Real.sqrt (Real.log x))) := by
  set n : ℕ := ⌊x⌋₊ with hn_def
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 10) hx
  have hexp10_2 : (2 : ℝ) ≤ Real.exp 10 := by
    have h := Real.add_one_le_exp (10 : ℝ)
    linarith
  have hexp9_2 : (2 : ℝ) ≤ Real.exp 9 := by
    have h := Real.add_one_le_exp (9 : ℝ)
    linarith
  have hn_le : (n : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hn_gt : x - 1 < (n : ℝ) := by
    have h := Nat.lt_floor_add_one x
    linarith
  have hn_ge_half : x / 2 ≤ (n : ℝ) := by linarith
  have hn_exp9 : Real.exp 9 ≤ (n : ℝ) := by
    have h1 : Real.exp 10 / 2 ≤ (n : ℝ) := by linarith
    have h2 : Real.exp 9 ≤ Real.exp 10 / 2 := by
      have h3 : Real.exp 10 = Real.exp 9 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      have h4 : (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1 : ℝ)
        linarith
      nlinarith [Real.exp_pos 9]
    linarith
  have hlog9 : 9 ≤ Real.log (n : ℝ) := by
    have h1 : Real.log (Real.exp 9) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (Real.exp_pos 9) hn_exp9
    simpa using h1
  have hlogx9 : 9 ≤ Real.log x := by
    have h1 : Real.log (Real.exp 10) ≤ Real.log x := Real.log_le_log (Real.exp_pos 10) hx
    have h2 : Real.log (Real.exp 10) = 10 := Real.log_exp 10
    linarith
  have hlog_lower : Real.log x / 4 ≤ Real.log (n : ℝ) := by
    have hlog2 : Real.log 2 ≤ 1 := log_two_le_one
    have h1 : Real.log x / 4 ≤ Real.log x - Real.log 2 := by nlinarith
    have h2 : Real.log x - Real.log 2 = Real.log (x / 2) := by
      rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0)]
    have h3 : Real.log (x / 2) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) hn_ge_half
    linarith
  have hsqrt : Real.sqrt (Real.log x) / 2 ≤ Real.sqrt (Real.log (n : ℝ)) :=
    sqrt_half_le hlog_lower (by linarith)
  have hexp_le : Real.exp (-(a * Real.sqrt (Real.log (n : ℝ)))) ≤
      Real.exp (-((a / 2) * Real.sqrt (Real.log x))) := by
    apply Real.exp_le_exp.mpr
    have h : a * (Real.sqrt (Real.log x) / 2) ≤ a * Real.sqrt (Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hsqrt ha.le
    linarith
  have hN : (q : ℝ) ≤ (Real.log (n : ℝ)) ^ 5 := by
    have h5 : (5 : ℝ) ≤ Real.log (n : ℝ) := by linarith
    have hp : (5 : ℝ) ^ 5 ≤ (Real.log (n : ℝ)) ^ 5 := pow_le_pow_left₀ (by norm_num) h5 5
    have hq : (q : ℝ) ≤ 105 := by exact_mod_cast hq105
    linarith
  have hn2 : 2 ≤ n := by
    have h : (2 : ℝ) ≤ (n : ℝ) := le_trans hexp9_2 hn_exp9
    exact_mod_cast h
  have hb := hbound n hn2 hN
  calc ‖DgBmorM8a.psiChiR χ x‖ = ‖DgBmorM8a.psiChi χ n‖ := by
        rw [psiChiR_eq_psiChi_floor]
    _ ≤ C * (n : ℝ) * Real.exp (-(a * Real.sqrt (Real.log (n : ℝ)))) := hb
    _ ≤ C * x * Real.exp (-(a * Real.sqrt (Real.log (n : ℝ)))) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left hn_le hC
    _ ≤ C * x * Real.exp (-((a / 2) * Real.sqrt (Real.log x))) := by
        apply mul_le_mul_of_nonneg_left hexp_le
        exact mul_nonneg hC hxpos.le

/-! ## 4. 主结论：`T1'` 的每特征输入 -/

/-- **每特征 Siegel–Walfisz（我们的 `T1'` 形状）**，由 vendored `siegel_walfisz` 得到。 -/
theorem per_character_siegelWalfisz :
    ∃ C c X : ℝ, 0 < C ∧ 0 < c ∧ 0 < X ∧
      ∀ (m : ℕ) [NeZero m], 3 ≤ m → m ≤ 105 →
        ∀ χ : DirichletCharacter ℂ m, χ ≠ 1 → ∀ x : ℝ, X ≤ x →
          ‖DgBmorM8a.psiChiR χ x‖ ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x))) := by
  obtain ⟨a, ha, hA⟩ := BombieriVinogradov.SiegelWalfisz.siegel_walfisz
  obtain ⟨C, hC, hbound⟩ := hA 5 (by norm_num)
  refine ⟨C, a / 2, Real.exp 10, hC, by linarith, Real.exp_pos 10, ?_⟩
  intro m _ _ hm105 χ hχ x hx
  refine psiChiR_bound χ ha hC.le hm105 ?_ hx
  intro n hn2 hN
  rw [← characterChebyshevSum_eq_psiChi]
  have hN' : (m : ℝ) ≤ Real.log (n : ℝ) ^ ((5 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    exact hN
  simpa [mul_assoc] using hbound χ hχ hn2 hN'

/-- **`T1`（无条件）**：`T1'` 的每特征输入已由 vendored Siegel–Walfisz 提供。 -/
theorem T1_discharged : DgTargetT1.T1 :=
  DgBmorP17.T1_of_per_character per_character_siegelWalfisz

end DgBmorP33
