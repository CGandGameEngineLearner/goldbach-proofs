import Mathlib

/-!
# BMOR 路线 · M8a：`E`-抽象的装配层（把 M4b 的常数形状换成一般误差 `E`）

`dg/M4b.lean` 的主定理

```
frozen_statement_of_per_character (hpsi) (hcorr) (hchi) :
  |ψ(q,a,n) − n/φ(q)| ≤ n/(840 log n)
```

三个输入都写死成 `x/(3360 log x)`。我们的正式目标 **T1** 用的是**经典误差形状**
`E x = C·x·exp(−c√(log x))`，因此需要一个抽象版。

本文件做两件事：

1. **抽象装配**（`ap_error_of_per_character`）：把 `M4b` 的证明照抄，但把常数
   `F = n/(3360 log n)` 换成任意 `E n`。常数核算与 `M4b` 完全一致：
   `1/φ·(2E + φE) = (2/φ + 1)·E ≤ 3E`（`φ ≥ 1`）。
   注意 `M4b` 最后的 `3F ≤ 4F = n/(840 log n)` 那一步**只对 `1/3360` 这个具体常数成立**
   （因为 `840 = 3360/4`）；抽象版只能给 `≤ 3·E n`，另附一条 `≤ 4·E n` 的弱化推论。
2. **修正项的无条件经典形状**（`E0_le_classical`）：由 `E₀ ≤ ω(q)·log n ≤ 6·log n`
   与 `6·log n ≤ n·exp(−√(log n))`（`n ≥ e¹⁶`）得到 `E₀ ≤ n·exp(−√log n)`，
   即 `hcorr` 的 `E` 形式**无条件成立**（`C₀ = c₀ = 1`，阈值 `e¹⁶ ≈ 8.89·10⁶`）。

## 复制说明

§0–§2 的引理是 `dg/M4b.lean` 的**逐字副本**（存档文件互不 import，项目惯例）；
§4 的 `nonunit_mangoldt_le` / `E0_le_card_mul_log` / `card_primeFactors_le_six`
是 `dg/M3c.lean` 的副本。内容均未改动。
-/

open scoped BigOperators

namespace DgBmorM8a

open ArithmeticFunction (vonMangoldt)

/-- 非互素修正项 `E₀(n) = Σ_{k≤n, (k,q)>1} Λ(k)`（与 `M4b`/`M3c` 同名定义）。 -/
noncomputable def E0 (q n : ℕ) : ℝ :=
  ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime k q),
    (vonMangoldt k : ℝ)

variable {q : ℕ} [NeZero q]

/-! ## 0. 定义与分解（M4b 副本） -/

/-- 等差数列上的 von Mangoldt 和（复数）。 -/
noncomputable def psiAP (q a n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    if (k : ZMod q) = (a : ZMod q) then (vonMangoldt k : ℂ) else 0

/-- 特征扭结的 von Mangoldt 和。 -/
noncomputable def psiChi (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), χ (k : ZMod q) * (vonMangoldt k : ℂ)

/-- 实变量版本（与 `dg/M4.lean` 的 `psiChiR` 一致）。 -/
noncomputable def psiChiR (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (⌊x⌋₊ + 1), χ (k : ZMod q) * (vonMangoldt k : ℂ)

omit [NeZero q] in
theorem psiChiR_natCast (χ : DirichletCharacter ℂ q) (n : ℕ) :
    psiChiR χ (n : ℝ) = psiChi χ n := by
  simp [psiChiR, psiChi, Nat.floor_natCast]

/-- 正交性（M1）。 -/
theorem indicator_eq_sum_char {a : ZMod q} (ha : IsUnit a) (k : ZMod q) :
    (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ k)
      = if a = k then ((Nat.totient q : ℂ)) else 0 :=
  DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha k

/-- 特征分解（M2）。 -/
theorem psiAP_eq_sum_char (hn : 0 < q) (a n : ℕ) (ha : Nat.Coprime a q) :
    psiAP q a n
      = (1 / (Nat.totient q : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q))⁻¹ * psiChi χ n := by
  have hφ : (Nat.totient q : ℂ) ≠ 0 := by
    have hpos : 0 < Nat.totient q := Nat.totient_pos.mpr hn
    exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
  have haunit : IsUnit ((a : ZMod q)) := (ZMod.isUnit_iff_coprime a q).mpr ha
  have hswap :
      (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q))⁻¹ * psiChi χ n)
        = ∑ k ∈ Finset.range (n + 1),
            (vonMangoldt k : ℂ) *
              (∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q))⁻¹ * χ (k : ZMod q)) := by
    simp only [psiChi, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  have hmul :
      (Nat.totient q : ℂ) * psiAP q a n
        = ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q))⁻¹ * psiChi χ n := by
    rw [hswap, psiAP, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [indicator_eq_sum_char haunit]
    by_cases hk : (a : ZMod q) = (k : ZMod q)
    · rw [ite_eq_left hk, ite_eq_left hk.symm]
      ring
    · rw [ite_eq_right (fun h => hk h.symm), ite_eq_right hk]
      ring
  calc psiAP q a n
      = (1 / (Nat.totient q : ℂ)) * ((Nat.totient q : ℂ) * psiAP q a n) := by
        field_simp
    _ = (1 / (Nat.totient q : ℂ)) *
          ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q))⁻¹ * psiChi χ n := by
        rw [hmul]

/-- 冻结陈述左边的实数求和 = `psiAP` 的实部（M0 桥接）。 -/
theorem frozen_lhs_eq (q a n : ℕ) :
    (psiAP q a n).re
      = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % q = a % q),
          (vonMangoldt k : ℝ) := by
  rw [psiAP, Complex.re_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : k % q = a % q
  · rw [ite_eq_left ((ZMod.natCast_eq_natCast_iff' k a q).mpr h), ite_eq_left h]
    simp
  · rw [ite_eq_right (fun hh => h ((ZMod.natCast_eq_natCast_iff' k a q).mp hh)), ite_eq_right h]
    simp

/-! ## 1. 主特征的精确恒等式（M3 的缺块，M4b 副本） -/

/-- 主特征取值：`χ₀(k) = 1` 当 `(k,q)=1`，否则 `0`。 -/
theorem one_apply_eq (k : ℕ) :
    (1 : DirichletCharacter ℂ q) (k : ZMod q) = if Nat.Coprime k q then 1 else 0 := by
  by_cases hk : IsUnit (k : ZMod q)
  · rw [ite_eq_left ((ZMod.isUnit_iff_coprime k q).mp hk), MulChar.one_apply hk]
  · rw [ite_eq_right (fun h => hk ((ZMod.isUnit_iff_coprime k q).mpr h)),
      MulChar.map_nonunit _ hk]

omit [NeZero q] in
/-- `Chebyshev.psi n` 就是 `Λ` 在 `[0,n]` 上的和。 -/
theorem psi_eq_sum_vonMangoldt (n : ℕ) :
    (Chebyshev.psi (n : ℝ) : ℂ) = ∑ k ∈ Finset.range (n + 1), (vonMangoldt k : ℂ) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast, Nat.range_succ_eq_Icc_zero]
  push_cast
  rfl

/-- **主特征恒等式**：`ψ_{χ₀}(n) = ψ(n) − E₀(n)`。 -/
theorem psiChi_one_eq (n : ℕ) :
    psiChi (1 : DirichletCharacter ℂ q) n
      = (Chebyshev.psi (n : ℝ) : ℂ) - (E0 q n : ℂ) := by
  have hsum : psiChi (1 : DirichletCharacter ℂ q) n
      = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => Nat.Coprime k q),
          (vonMangoldt k : ℂ) := by
    rw [psiChi]
    simp only [one_apply_eq, ite_mul, one_mul, zero_mul]
    exact (Finset.sum_filter (fun k => Nat.Coprime k q) (fun k => (vonMangoldt k : ℂ))).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
    (fun k => Nat.Coprime k q) (fun k => (vonMangoldt k : ℂ))
  have hE : (E0 q n : ℂ)
      = ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ Nat.Coprime k q),
          (vonMangoldt k : ℂ) := by
    rw [E0]
    push_cast
    rfl
  rw [hsum, psi_eq_sum_vonMangoldt, hE, eq_sub_iff_add_eq]
  exact hsplit

/-! ## 2. 实部求和的一般估计（M4b 副本） -/

/-- `|Σ Re f| ≤ Σ ‖f‖`。 -/
theorem abs_sum_re_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    |∑ i ∈ s, (f i).re| ≤ ∑ i ∈ s, ‖f i‖ := by
  calc
    |∑ i ∈ s, (f i).re| = |(∑ i ∈ s, f i).re| := by rw [Complex.re_sum]
    _ ≤ ‖∑ i ∈ s, f i‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le s f

/-- 特征的和式：每个 `‖ψ_χ‖` 都被 `F` 控制，特征个数不超过 `φ(q)`。 -/
theorem abs_sum_re_le_totient (a n : ℕ) {F : ℝ} (hF : 0 ≤ F)
    (hchi : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ‖psiChi χ n‖ ≤ F) :
    |(∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (χ ((a : ZMod q))⁻¹ * psiChi χ n).re)| ≤ (Nat.totient q : ℝ) * F := by
  have h1 : |(∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      (χ ((a : ZMod q))⁻¹ * psiChi χ n).re)|
      ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ‖χ ((a : ZMod q))⁻¹ * psiChi χ n‖ := abs_sum_re_le _ _
  have h2 : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ‖χ ((a : ZMod q))⁻¹ * psiChi χ n‖)
      ≤ ∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), F := by
    refine Finset.sum_le_sum fun χ hχ => ?_
    have hne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    calc
      ‖χ ((a : ZMod q))⁻¹ * psiChi χ n‖
          = ‖χ ((a : ZMod q))⁻¹‖ * ‖psiChi χ n‖ := norm_mul _ _
      _ ≤ 1 * ‖psiChi χ n‖ := by
        refine mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _) (norm_nonneg _)
      _ = ‖psiChi χ n‖ := one_mul _
      _ ≤ F := hchi χ hne
  have h3 : (∑ _χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), F)
      = ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ) * F := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h4 : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).card : ℝ)
      ≤ (Nat.totient q : ℝ) := by
    have hcard : (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card ≤ Nat.totient q := by
      calc
        (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card
            ≤ Fintype.card (DirichletCharacter ℂ q) := by
          rw [← Finset.card_univ]
          exact Finset.card_le_card (Finset.erase_subset _ _)
        _ = Nat.totient q := by
          rw [← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    exact_mod_cast hcard
  calc
    |(∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        (χ ((a : ZMod q))⁻¹ * psiChi χ n).re)| ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h3
    _ ≤ (Nat.totient q : ℝ) * F := mul_le_mul_of_nonneg_right h4 hF

/-! ## 3. 抽象装配：`E` 代替 `x/(3360 log x)` -/

/-- **M8a 主定理（`E`-抽象装配）**：给定任意误差函数 `E`（非负）与阈值 `X`，若
每特征的 `ψ_χ`（`χ ≠ 1`）、ζ 的 `ψ(x) − x`、以及修正项 `E₀` 都被 `E` 控制，
则等差数列上的误差被 `3·E n` 控制。

常数 `3` 与 `M4b` 的算术完全一致：`1/φ·(2E + φE) = (2/φ + 1)·E ≤ 3E`。
（`M4b` 里多出的 `3F ≤ 4F` 一步只对 `1/3360` 这个具体常数成立，见下面的弱化推论。） -/
theorem ap_error_of_per_character
    (E : ℝ → ℝ) (X : ℝ)
    (hEpos : ∀ x, 0 ≤ E x)
    (hpsi : ∀ x : ℝ, X ≤ x → |Chebyshev.psi x - x| ≤ E x)
    (hcorr : ∀ (m n : ℕ), 3 ≤ m → m ≤ 105 → ⌈X⌉₊ ≤ n → E0 m n ≤ E n)
    (hchi : ∀ (m : ℕ) [NeZero m], 3 ≤ m → m ≤ 105 →
      ∀ (χ : DirichletCharacter ℂ m), χ ≠ 1 → ∀ x : ℝ, X ≤ x → ‖psiChiR χ x‖ ≤ E x) :
    ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → ⌈X⌉₊ ≤ n →
      |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
          (vonMangoldt k : ℝ)) - (n:ℝ)/Nat.totient q|
        ≤ 3 * E n := by
  intro q a n hq hle _ha hcop hXn
  haveI : NeZero q := ⟨by omega⟩
  have hqpos : 0 < q := by omega
  have hXnR : X ≤ (n : ℝ) := Nat.ceil_le.mp hXn
  set F : ℝ := E n with hFdef
  have hFnn : 0 ≤ F := hEpos n
  have hFpsi : |Chebyshev.psi (n : ℝ) - (n : ℝ)| ≤ F := hpsi (n : ℝ) hXnR
  have hFcorr : E0 q n ≤ F := hcorr q n hq hle hXn
  have hE0nn : 0 ≤ E0 q n :=
    Finset.sum_nonneg fun k _ => ArithmeticFunction.vonMangoldt_nonneg
  have hφpos_nat : 0 < Nat.totient q := Nat.totient_pos.mpr hqpos
  have hφpos : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast hφpos_nat
  -- 特征分解
  have hdec := psiAP_eq_sum_char hqpos a n hcop
  set S : ℂ := ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
    χ ((a : ZMod q))⁻¹ * psiChi χ n with hSdef
  have hone_apply : (1 : DirichletCharacter ℂ q) ((a : ZMod q))⁻¹ = 1 := by
    have hu : IsUnit (((a : ℤ) : ZMod q)) := by
      simpa using (ZMod.isUnit_iff_coprime a q).mpr hcop
    have hu' : IsUnit ((((a : ℤ) : ZMod q))⁻¹) := ZMod.isUnit_inv hu
    simpa using MulChar.one_apply (x := (((a : ℤ) : ZMod q))⁻¹) hu'
  have hsplit : (∑ χ : DirichletCharacter ℂ q,
        χ ((a : ZMod q))⁻¹ * psiChi χ n)
      = psiChi (1 : DirichletCharacter ℂ q) n + S := by
    rw [hSdef]
    rw [← Finset.add_sum_erase Finset.univ
      (fun χ : DirichletCharacter ℂ q => χ ((a : ZMod q))⁻¹ * psiChi χ n)
      (Finset.mem_univ (1 : DirichletCharacter ℂ q))]
    rw [hone_apply, one_mul]
  have hmulre : ∀ (r : ℝ) (z : ℂ), ((r : ℂ) * z).re = r * z.re := by
    intro r z
    simp [Complex.mul_re]
  have hre : (psiAP q a n).re
      = (1 / (Nat.totient q : ℝ)) *
          (Chebyshev.psi (n : ℝ) - E0 q n + S.re) := by
    have hcoef : (1 : ℂ) / (Nat.totient q : ℂ) = ((1 / (Nat.totient q : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hdec, hsplit, hcoef, hmulre, psiChi_one_eq]
    simp [Complex.add_re, Complex.sub_re]
  -- 特征和式的界
  have hchi' : ∀ (χ : DirichletCharacter ℂ q), χ ≠ 1 → ‖psiChi χ n‖ ≤ F := by
    intro χ hχ
    rw [← psiChiR_natCast χ n]
    exact hchi q hq hle χ hχ (n : ℝ) hXnR
  have hS : |S.re| ≤ (Nat.totient q : ℝ) * F := by
    rw [hSdef, Complex.re_sum]
    exact abs_sum_re_le_totient a n hFnn hchi'
  -- 数值核算
  have hφne : (Nat.totient q : ℝ) ≠ 0 := hφpos.ne'
  have hkey : |(psiAP q a n).re - (n : ℝ) / (Nat.totient q : ℝ)|
      ≤ (1 / (Nat.totient q : ℝ)) * (F + F + (Nat.totient q : ℝ) * F) := by
    have hE : (psiAP q a n).re - (n : ℝ) / (Nat.totient q : ℝ)
        = (1 / (Nat.totient q : ℝ)) *
            ((Chebyshev.psi (n : ℝ) - (n : ℝ)) - E0 q n + S.re) := by
      rw [hre]
      field_simp
      ring
    rw [hE, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (Nat.totient q : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hA : |(Chebyshev.psi (n : ℝ) - (n : ℝ)) - E0 q n|
        ≤ |Chebyshev.psi (n : ℝ) - (n : ℝ)| + |E0 q n| := by
      have habs := abs_add_le (Chebyshev.psi (n : ℝ) - (n : ℝ)) (-(E0 q n))
      rwa [abs_neg, ← sub_eq_add_neg] at habs
    calc
      |(Chebyshev.psi (n : ℝ) - (n : ℝ)) - E0 q n + S.re|
          ≤ |(Chebyshev.psi (n : ℝ) - (n : ℝ)) - E0 q n| + |S.re| := abs_add_le _ _
      _ ≤ (|Chebyshev.psi (n : ℝ) - (n : ℝ)| + |E0 q n|) + |S.re| := by linarith
      _ ≤ (F + F) + (Nat.totient q : ℝ) * F := by
        have hE0abs : |E0 q n| = E0 q n := abs_of_nonneg hE0nn
        rw [hE0abs]
        linarith [hFpsi, hFcorr, hS]
  rw [← frozen_lhs_eq q a n]
  calc
    |(psiAP q a n).re - (n : ℝ) / (Nat.totient q : ℝ)|
        ≤ (1 / (Nat.totient q : ℝ)) * (F + F + (Nat.totient q : ℝ) * F) := hkey
    _ = (2 / (Nat.totient q : ℝ) + 1) * F := by
      field_simp
      ring
    _ ≤ 3 * F := by
      have hφ1 : (1 : ℝ) ≤ (Nat.totient q : ℝ) := by exact_mod_cast hφpos_nat
      have h2 : 2 / (Nat.totient q : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hφpos]
        linarith
      nlinarith [hFnn]
    _ = 3 * E n := by rw [hFdef]

/-- `ap_error_of_per_character` 的弱化版：结论用 `4·E n`（对应 `M4b` 里 `3F ≤ 4F` 那一步的
常数位置），便于与 `M4b` 的 `n/(840 log n)` 形状对照。 -/
theorem ap_error_of_per_character_four
    (E : ℝ → ℝ) (X : ℝ)
    (hEpos : ∀ x, 0 ≤ E x)
    (hpsi : ∀ x : ℝ, X ≤ x → |Chebyshev.psi x - x| ≤ E x)
    (hcorr : ∀ (m n : ℕ), 3 ≤ m → m ≤ 105 → ⌈X⌉₊ ≤ n → E0 m n ≤ E n)
    (hchi : ∀ (m : ℕ) [NeZero m], 3 ≤ m → m ≤ 105 →
      ∀ (χ : DirichletCharacter ℂ m), χ ≠ 1 → ∀ x : ℝ, X ≤ x → ‖psiChiR χ x‖ ≤ E x) :
    ∀ (q a n : ℕ), 3 ≤ q → q ≤ 105 → a < q → Nat.Coprime a q → ⌈X⌉₊ ≤ n →
      |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
          (vonMangoldt k : ℝ)) - (n:ℝ)/Nat.totient q|
        ≤ 4 * E n := by
  have h3 := ap_error_of_per_character E X hEpos hpsi hcorr hchi
  intro q a n hq hle ha hcop hXn
  have h := h3 q a n hq hle ha hcop hXn
  have hnn : 0 ≤ E n := hEpos n
  linarith

/-! ## 4. `E₀` 的无条件经典形状：`E₀ ≤ n·exp(−√log n)`（`n ≥ e¹⁶`）

`M3c` 已经证明 `E₀ ≤ ω(q)·log n ≤ 6·log n`。这里把 `6 log n` 换成 `n·exp(−√log n)`。
关键初等估计（`L = log x`）：

* `√L ≤ L/4`（`L ≥ 16`）；
* `log 6 ≤ 3 ≤ L/4`，故 `log 6 ≤ L/2 − √L`；
* `log L ≤ L/2`（由 `log(L/2) ≤ L/2 − 1` 与 `log 2 ≤ 1`），即 `L ≤ exp(L/2)`。

于是 `6L ≤ 6·exp(L/2) = exp(log 6 + L/2) ≤ exp(L − √L) = x·exp(−√L)`。
-/

/-- `L ≥ 16 ⟹ 6L ≤ x·exp(−√L)`，其中 `L = log x`。 -/
theorem six_log_le_classical (x : ℝ) (hx : Real.exp 16 ≤ x) :
    6 * Real.log x ≤ x * Real.exp (-(Real.sqrt (Real.log x))) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 16) hx
  have hL : 16 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 16) hx
    rwa [Real.log_exp] at h
  have hL0 : 0 < Real.log x := by linarith
  have hsqrt_le : Real.sqrt (Real.log x) ≤ Real.log x / 4 := by
    have hsqr : Real.sqrt (Real.log x) ^ 2 = Real.log x := Real.sq_sqrt (le_of_lt hL0)
    have hnn : (0 : ℝ) ≤ Real.sqrt (Real.log x) := Real.sqrt_nonneg _
    nlinarith [hsqr, hnn, hL, hL0, sq_nonneg (Real.log x - 16)]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hlog6 : Real.log 6 ≤ 3 := by
    have h1 : Real.log 6 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
    have h2 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hgap : Real.log 6 ≤ Real.log x / 2 - Real.sqrt (Real.log x) := by
    nlinarith [hlog6, hsqrt_le, hL]
  -- `log L ≤ L/2`，即 `L ≤ exp (L/2)`
  have hLle : Real.log x ≤ Real.exp (Real.log x / 2) := by
    refine (Real.log_le_iff_le_exp (x := Real.log x) (y := Real.log x / 2) hL0).mp ?_
    have hsplit : Real.log (Real.log x) = Real.log (Real.log x / 2) + Real.log 2 := by
      have hpos : (0:ℝ) < Real.log x / 2 := by linarith
      rw [← Real.log_mul hpos.ne' (by norm_num : (2:ℝ) ≠ 0)]
      congr 1
      field_simp
    have hsub : Real.log (Real.log x / 2) ≤ Real.log x / 2 - 1 :=
      Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < Real.log x / 2)
    rw [hsplit]
    linarith
  calc 6 * Real.log x ≤ 6 * Real.exp (Real.log x / 2) := by linarith
    _ = Real.exp (Real.log 6 + Real.log x / 2) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ) < 6)]
    _ ≤ Real.exp (Real.log x - Real.sqrt (Real.log x)) :=
        Real.exp_le_exp.mpr (by linarith)
    _ = x * Real.exp (-(Real.sqrt (Real.log x))) := by
        rw [Real.exp_sub, Real.exp_log hx0, Real.exp_neg, div_eq_mul_inv]

/-- 非互素 `von Mangoldt` 质量的总界（`dg/M3c.lean` 副本：
`E₀ ≤ ω(q)·log n`，其中 `ω(q) = #q.primeFactors`）。 -/
theorem nonunit_mangoldt_le (q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    (∑ k ∈ (Finset.range (n+1)).filter (fun k => ¬ Nat.Coprime k q),
        ArithmeticFunction.vonMangoldt k) ≤ (q.primeFactors.card : ℝ) * Real.log n := by
  let K := (Finset.range (n+1)).filter (fun k => ¬k.Coprime q)
  let T := K.filter IsPrimePow
  let E (p : ℕ) := (Finset.Icc 1 (Nat.log p n))
  have repr {k : ℕ} (hk : k ∈ T) :
      k.minFac ∈ q.primeFactors ∧ ∃ a ∈ E k.minFac, k.minFac^a = k := by
    obtain ⟨hkK,hpp⟩ := Finset.mem_filter.mp hk
    obtain ⟨hkN,hbad⟩ := Finset.mem_filter.mp hkK
    obtain ⟨p,a,hp,ha,rfl⟩ := (isPrimePow_nat_iff k).1 hpp
    rw [Nat.pow_minFac ha.ne',hp.minFac_eq]
    have hd : p ∣ q := by
      by_contra h
      exact hbad ((hp.coprime_iff_not_dvd.2 h).pow_left a)
    refine ⟨Nat.mem_primeFactors.mpr ⟨hp,hd,by omega⟩,a,Finset.mem_Icc.mpr ⟨ha,?_⟩,rfl⟩
    exact Nat.le_log_of_pow_le hp.one_lt (by have := Finset.mem_range.mp hkN; omega)
  have fiber (p : ℕ) (hp : p ∈ q.primeFactors) :
      (∑ k ∈ T.filter (fun k => k.minFac=p), ArithmeticFunction.vonMangoldt k) ≤ Real.log n := by
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hsub : T.filter (fun k => k.minFac=p) ⊆ (E p).image (fun a => p^a) := by
      intro k hk
      obtain ⟨hkT,hbase⟩ := Finset.mem_filter.mp hk
      have hrep := (repr hkT).2
      rw [hbase] at hrep
      exact Finset.mem_image.mpr hrep
    have hc : (T.filter (fun k => k.minFac=p)).card ≤ Nat.log p n := by
      have := (Finset.card_le_card hsub).trans Finset.card_image_le
      simpa [E,Nat.card_Icc] using this
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpprime.one_le)
    calc
      _ = ∑ _k ∈ T.filter (fun k => k.minFac=p), Real.log (p:ℝ) := by
        apply Finset.sum_congr rfl
        intro k hk
        obtain ⟨hkT,hbase⟩ := Finset.mem_filter.mp hk
        rw [ArithmeticFunction.vonMangoldt_apply,ite_eq_left (Finset.mem_filter.mp hkT).2,hbase]
      _ ≤ (Nat.log p n:ℝ)*Real.log p := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hlog
      _ = Real.log ((p:ℝ)^(Nat.log p n)) := (Real.log_pow _ _).symm
      _ ≤ Real.log n := Real.log_le_log (by exact_mod_cast pow_pos hpprime.pos _)
        (by exact_mod_cast Nat.pow_log_le_self p (by omega))
  change (∑ k ∈ K, ArithmeticFunction.vonMangoldt k) ≤ _
  calc
    _ = ∑ k ∈ T, ArithmeticFunction.vonMangoldt k := by
      symm
      exact Finset.sum_subset (Finset.filter_subset _ _) (fun k hk hout =>
        ArithmeticFunction.vonMangoldt_eq_zero_iff.2 (fun h => hout (Finset.mem_filter.mpr ⟨hk,h⟩)))
    _ = ∑ p ∈ q.primeFactors, ∑ k ∈ T.filter (fun k => k.minFac=p), ArithmeticFunction.vonMangoldt k :=
      (Finset.sum_fiberwise_of_maps_to (fun k hk => (repr hk).1) _).symm
    _ ≤ ∑ _p ∈ q.primeFactors, Real.log n := Finset.sum_le_sum fiber
    _ = _ := by simp

/-- `E₀(q,n) ≤ ω(q)·log n`（`dg/M3c.lean` 副本）。 -/
theorem E0_le_card_mul_log (q n : ℕ) (hq : 1 ≤ q) (hn : 1 ≤ n) :
    E0 q n ≤ (q.primeFactors.card : ℝ) * Real.log n := by
  rw [E0]
  exact nonunit_mangoldt_le q n hq hn

/-- 素因子个数：`q ≤ 105` 且 `3 ≤ q` 时 `ω(q) ≤ 6`（`dg/M3c.lean` 副本）。 -/
theorem card_primeFactors_le_six (q : ℕ) (hq3 : 3 ≤ q) (hq : q ≤ 105) :
    q.primeFactors.card ≤ 6 := by
  have hq0 : 0 < q := by omega
  have h2prod : (2 : ℕ) ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).two_le
  have hle : (2 : ℕ) ^ q.primeFactors.card ≤ q :=
    h2prod.trans (Nat.le_of_dvd hq0 (Nat.prod_primeFactors_dvd q))
  have hlt : (2 : ℕ) ^ q.primeFactors.card < 2 ^ 7 := by
    have h128 : (2 : ℕ) ^ 7 = 128 := by norm_num
    omega
  have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
  omega

/-- **`E₀` 的无条件经典形状**：`3 ≤ q ≤ 105`、`n ≥ e¹⁶` 时
`E₀(q,n) ≤ n·exp(−√(log n))`。

即 `hcorr` 的 `E` 形式**无条件成立**，常数 `C₀ = c₀ = 1`，阈值 `e¹⁶ ≈ 8.89·10⁶`。 -/
theorem E0_le_classical (q n : ℕ) (hq3 : 3 ≤ q) (hq : q ≤ 105)
    (hn : Real.exp 16 ≤ (n : ℝ)) :
    E0 q n ≤ (n : ℝ) * Real.exp (-(Real.sqrt (Real.log (n : ℝ)))) := by
  have hn1 : 1 ≤ n := by
    have h1 : (1 : ℝ) ≤ (n : ℝ) :=
      (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 16)).trans hn
    exact_mod_cast h1
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn1)
  have hE := E0_le_card_mul_log q n (by omega) hn1
  have hcard : (q.primeFactors.card : ℝ) ≤ 6 := by
    exact_mod_cast card_primeFactors_le_six q hq3 hq
  calc
    E0 q n ≤ (q.primeFactors.card : ℝ) * Real.log (n : ℝ) := hE
    _ ≤ 6 * Real.log (n : ℝ) := by nlinarith [hcard, hlog0]
    _ ≤ (n : ℝ) * Real.exp (-(Real.sqrt (Real.log (n : ℝ)))) :=
        six_log_le_classical (n : ℝ) hn

end DgBmorM8a
