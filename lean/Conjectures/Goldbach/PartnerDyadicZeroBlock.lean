import Mathlib
import Conjectures.Goldbach.PrimitivePartnerCubicMass

/-!
# 全导子双线性 ℓ^(6/5) 估计与 Pintz 二进零点块衰减

本文件证明 `L-goldbach-partner-dyadic-zero-block`：
1. 复用已验证社区模块 `Conjectures.Goldbach.PrimitivePartnerCubicMass`（PR #4245）给出的全导子行三次矩界，
   结合奇异级数核的对称性与两次 Hölder 不等式，得到全导子双线性 `ℓ^(6/5)` 界；
2. 利用 `Complex.Gamma_mul_Gamma_eq_betaIntegral` 将 Pintz 显式公式中的 Gamma 核化为复 Beta 积分，
   通过端点尾估计、复共轭约化与光滑分部积分（按同号/异号分别处理驻点与非驻点区间），
   证明在二进高度块 `T ≤ |Im z| ≤ 2T`、`1/2 ≤ Re z ≤ 1` 上有 `‖Γ(z₁)Γ(z₂)/Γ(z₁+z₂)‖ ≤ 64 / √T`，
   再按本原特征纤维合并权值并套用第一部分完成主定理。
-/

namespace PartnerDyadicZeroBlockProof

open Finset MeasureTheory intervalIntegral
open scoped BigOperators Classical ComplexConjugate

-- ============================================================================
-- 第一部分：奇异级数核定义、对称性与双线性 ℓ^(6/5) 估计
-- ============================================================================

/-- 奇异级数核 `S(α, β; m)`，与冻结命题定义完全一致。 -/
private noncomputable def S {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m : ℕ) : ℂ :=
  ∑' q : ℕ, if hq : q ≠ 0 then
    let _ : NeZero q := ⟨hq⟩
    if h : r ∣ q ∧ s ∣ q then
      let A := DirichletCharacter.changeLevel h.1 α
      let B := DirichletCharacter.changeLevel h.2 β
      gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
        gaussSum (A * B)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod q))) / (q.totient : ℂ) ^ 2
    else 0
  else 0

/-- 经典奇异级数 `O(m) = S(1, 1; m)`。 -/
private noncomputable def O (m : ℕ) : ℂ :=
  S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m

/-- 特征对类型与本原条件。 -/
private abbrev CharPack := Σ s : ℕ, DirichletCharacter ℂ s

private def IsPrimPack (b : CharPack) : Prop :=
  b.1 ≠ 0 ∧ b.2.IsPrimitive

/-- `ℓ^(6/5)` 范数。 -/
private noncomputable def norm65 (F : Finset CharPack) (w : CharPack → ℝ) : ℝ :=
  (∑ b ∈ F, |w b| ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ)

/-- 奇异级数核关于两个特征对称：`S α β m = S β α m`。 -/
private lemma S_symm {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m : ℕ) : S α β m = S β α m := by
  unfold S
  apply tsum_congr
  intro q
  split_ifs with hq1 h1 h2 h3
  · let _ : NeZero q := ⟨hq1⟩
    dsimp only
    set A := DirichletCharacter.changeLevel h1.1 α
    set B := DirichletCharacter.changeLevel h1.2 β
    have hmul : A * B = B * A := mul_comm A B
    rw [hmul, mul_comm (gaussSum A ZMod.stdAddChar) (gaussSum B ZMod.stdAddChar)]
  · exfalso; exact h2 ⟨h1.2, h1.1⟩
  · exfalso; exact h1 ⟨h3.2, h3.1⟩
  · rfl
  · rfl

/-- 行三次矩界：直接调用已验证社区定理 `Conjectures.Goldbach.PrimitivePartnerCubicMass`。 -/
private lemma row_cubic_bound (m : ℕ) (hm : 0 < m) (he : Even m) (F : Finset CharPack)
    (hF : ∀ b ∈ F, IsPrimPack b) {a : CharPack} (ha : IsPrimPack a) :
    (∑ b ∈ F, ‖S a.2 b.2 m‖ ^ 3) ≤ 3 * ‖O m‖ ^ 3 := by
  have hmain := Conjectures.Goldbach.PrimitivePartnerCubicMass
  dsimp only at hmain
  let _ : NeZero a.1 := ⟨ha.1⟩
  exact hmain a.1 a.2 ha.2 m hm he F hF

/-- 列三次矩界：由对称性化为行三次矩界。 -/
private lemma col_cubic_bound (m : ℕ) (hm : 0 < m) (he : Even m) (F : Finset CharPack)
    (hF : ∀ b ∈ F, IsPrimPack b) {b : CharPack} (hb : IsPrimPack b) :
    (∑ a ∈ F, ‖S a.2 b.2 m‖ ^ 3) ≤ 3 * ‖O m‖ ^ 3 := by
  have hconv : (∑ a ∈ F, ‖S a.2 b.2 m‖ ^ 3) = ∑ a ∈ F, ‖S b.2 a.2 m‖ ^ 3 := by
    apply Finset.sum_congr rfl
    intro a _
    rw [S_symm]
  rw [hconv]
  exact row_cubic_bound m hm he F hF hb

/-- 全导子双线性 `ℓ^(6/5)` 界（定理第一部分）。 -/
private lemma bilinear_bound (m : ℕ) (hm : 0 < m) (he : Even m) (F : Finset CharPack)
    (hF : ∀ b ∈ F, IsPrimPack b) (u v : CharPack → ℝ) :
    (∑ a ∈ F, ∑ b ∈ F, |u a| * ‖S a.2 b.2 m‖ * |v b|)
      ≤ (3 : ℝ) ^ (1 / 3 : ℝ) * ‖O m‖ * norm65 F u * norm65 F v := by
  let U : CharPack → ℝ := fun a => |u a|
  let V : CharPack → ℝ := fun b => |v b|
  let K : CharPack → CharPack → ℝ := fun a b => ‖S a.2 b.2 m‖
  let A : ℝ := ∑ a ∈ F, U a ^ (6 / 5 : ℝ)
  let Bsum : ℝ := ∑ b ∈ F, V b ^ (6 / 5 : ℝ)
  let M : ℝ := 3 * ‖O m‖ ^ 3
  have hU_nn : ∀ a, 0 ≤ U a := fun a => abs_nonneg _
  have hV_nn : ∀ b, 0 ≤ V b := fun b => abs_nonneg _
  have hK_nn : ∀ a b, 0 ≤ K a b := fun a b => norm_nonneg _
  have hA_nn : 0 ≤ A := Finset.sum_nonneg fun a _ => Real.rpow_nonneg (hU_nn a) _
  have hB_nn : 0 ≤ Bsum := Finset.sum_nonneg fun b _ => Real.rpow_nonneg (hV_nn b) _
  have hM_nn : 0 ≤ M := by dsimp only [M]; positivity
  -- 第一次 Hölder：在 `F ×ˢ F` 上取 `(p, q) = (3, 3/2)`
  have hConj1 : Real.HolderConjugate (3 : ℝ) (3 / 2 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  let f1 : CharPack × CharPack → ℝ := fun x =>
    U x.1 ^ (1 / 5 : ℝ) * V x.2 ^ (1 / 5 : ℝ) * K x.1 x.2
  let g1 : CharPack × CharPack → ℝ := fun x =>
    U x.1 ^ (4 / 5 : ℝ) * V x.2 ^ (4 / 5 : ℝ)
  have hf1_nn : ∀ x ∈ F ×ˢ F, 0 ≤ f1 x := fun x _ => by
    dsimp only [f1]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (hU_nn x.1) _) (Real.rpow_nonneg (hV_nn x.2) _))
      (hK_nn x.1 x.2)
  have hg1_nn : ∀ x ∈ F ×ˢ F, 0 ≤ g1 x := fun x _ => by
    dsimp only [g1]
    exact mul_nonneg (Real.rpow_nonneg (hU_nn x.1) _) (Real.rpow_nonneg (hV_nn x.2) _)
  have hprod1 : ∀ x : CharPack × CharPack, f1 x * g1 x = U x.1 * K x.1 x.2 * V x.2 := by
    intro x
    dsimp only [f1, g1]
    have hu1 : U x.1 ^ (1 / 5 : ℝ) * U x.1 ^ (4 / 5 : ℝ) = U x.1 := by
      rw [← Real.rpow_add' (hU_nn x.1) (by norm_num)]
      norm_num
    have hv1 : V x.2 ^ (1 / 5 : ℝ) * V x.2 ^ (4 / 5 : ℝ) = V x.2 := by
      rw [← Real.rpow_add' (hV_nn x.2) (by norm_num)]
      norm_num
    calc
      U x.1 ^ (1 / 5 : ℝ) * V x.2 ^ (1 / 5 : ℝ) * K x.1 x.2 *
          (U x.1 ^ (4 / 5 : ℝ) * V x.2 ^ (4 / 5 : ℝ))
          = (U x.1 ^ (1 / 5 : ℝ) * U x.1 ^ (4 / 5 : ℝ)) * K x.1 x.2 *
            (V x.2 ^ (1 / 5 : ℝ) * V x.2 ^ (4 / 5 : ℝ)) := by ring
      _ = U x.1 * K x.1 x.2 * V x.2 := by rw [hu1, hv1]
  have hf1_pow : ∀ x : CharPack × CharPack,
      f1 x ^ (3 : ℝ) = U x.1 ^ (3 / 5 : ℝ) * V x.2 ^ (3 / 5 : ℝ) * K x.1 x.2 ^ 3 := by
    intro x
    dsimp only [f1]
    rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg (hU_nn x.1) _) (Real.rpow_nonneg (hV_nn x.2) _))
          (hK_nn x.1 x.2),
        Real.mul_rpow (Real.rpow_nonneg (hU_nn x.1) _) (Real.rpow_nonneg (hV_nn x.2) _),
        ← Real.rpow_mul (hU_nn x.1), ← Real.rpow_mul (hV_nn x.2)]
    have hk3 : K x.1 x.2 ^ (3 : ℝ) = K x.1 x.2 ^ (3 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (K x.1 x.2) 3
    rw [hk3]
    norm_num
  have hg1_pow : ∀ x : CharPack × CharPack,
      g1 x ^ (3 / 2 : ℝ) = U x.1 ^ (6 / 5 : ℝ) * V x.2 ^ (6 / 5 : ℝ) := by
    intro x
    dsimp only [g1]
    rw [Real.mul_rpow (Real.rpow_nonneg (hU_nn x.1) _) (Real.rpow_nonneg (hV_nn x.2) _),
        ← Real.rpow_mul (hU_nn x.1), ← Real.rpow_mul (hV_nn x.2)]
    norm_num
  have hsum_g1 : (∑ x ∈ F ×ˢ F, g1 x ^ (3 / 2 : ℝ)) = A * Bsum := by
    simp_rw [hg1_pow]
    rw [Finset.sum_product, Finset.sum_mul_sum]
  have hHolder1 := Real.inner_le_Lp_mul_Lq_of_nonneg (s := F ×ˢ F) hConj1 hf1_nn hg1_nn
  have hlhs1 : (∑ a ∈ F, ∑ b ∈ F, U a * K a b * V b) = ∑ x ∈ F ×ˢ F, f1 x * g1 x := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    exact (hprod1 (a, b)).symm
  -- 第二次 Hölder：在 `F ×ˢ F` 上取 `(p, q) = (2, 2)` 估计 `∑ f1^3`
  have hConj2 : Real.HolderConjugate (2 : ℝ) (2 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  let f2 : CharPack × CharPack → ℝ := fun x => U x.1 ^ (3 / 5 : ℝ) * K x.1 x.2 ^ (3 / 2 : ℝ)
  let g2 : CharPack × CharPack → ℝ := fun x => V x.2 ^ (3 / 5 : ℝ) * K x.1 x.2 ^ (3 / 2 : ℝ)
  have hf2_nn : ∀ x ∈ F ×ˢ F, 0 ≤ f2 x := fun x _ =>
    mul_nonneg (Real.rpow_nonneg (hU_nn x.1) _) (Real.rpow_nonneg (hK_nn x.1 x.2) _)
  have hg2_nn : ∀ x ∈ F ×ˢ F, 0 ≤ g2 x := fun x _ =>
    mul_nonneg (Real.rpow_nonneg (hV_nn x.2) _) (Real.rpow_nonneg (hK_nn x.1 x.2) _)
  have hprod2 : ∀ x : CharPack × CharPack, f2 x * g2 x = f1 x ^ (3 : ℝ) := by
    intro x
    rw [hf1_pow]
    dsimp only [f2, g2]
    have hk : K x.1 x.2 ^ (3 / 2 : ℝ) * K x.1 x.2 ^ (3 / 2 : ℝ) = K x.1 x.2 ^ 3 := by
      rw [← Real.rpow_add' (hK_nn x.1 x.2) (by norm_num)]
      have h3 : (3 / 2 : ℝ) + 3 / 2 = (3 : ℕ) := by norm_num
      rw [h3, Real.rpow_natCast]
    calc
      U x.1 ^ (3 / 5 : ℝ) * K x.1 x.2 ^ (3 / 2 : ℝ) *
          (V x.2 ^ (3 / 5 : ℝ) * K x.1 x.2 ^ (3 / 2 : ℝ))
          = U x.1 ^ (3 / 5 : ℝ) * V x.2 ^ (3 / 5 : ℝ) *
            (K x.1 x.2 ^ (3 / 2 : ℝ) * K x.1 x.2 ^ (3 / 2 : ℝ)) := by ring
      _ = U x.1 ^ (3 / 5 : ℝ) * V x.2 ^ (3 / 5 : ℝ) * K x.1 x.2 ^ 3 := by rw [hk]
  have hf2_sq : ∀ x : CharPack × CharPack, f2 x ^ (2 : ℝ) = U x.1 ^ (6 / 5 : ℝ) * K x.1 x.2 ^ 3 := by
    intro x
    dsimp only [f2]
    rw [Real.mul_rpow (Real.rpow_nonneg (hU_nn x.1) _) (Real.rpow_nonneg (hK_nn x.1 x.2) _),
        ← Real.rpow_mul (hU_nn x.1), ← Real.rpow_mul (hK_nn x.1 x.2)]
    have h65 : (3 / 5 : ℝ) * 2 = 6 / 5 := by norm_num
    have h3 : (3 / 2 : ℝ) * 2 = (3 : ℕ) := by norm_num
    rw [h65, h3, Real.rpow_natCast]
  have hg2_sq : ∀ x : CharPack × CharPack, g2 x ^ (2 : ℝ) = V x.2 ^ (6 / 5 : ℝ) * K x.1 x.2 ^ 3 := by
    intro x
    dsimp only [g2]
    rw [Real.mul_rpow (Real.rpow_nonneg (hV_nn x.2) _) (Real.rpow_nonneg (hK_nn x.1 x.2) _),
        ← Real.rpow_mul (hV_nn x.2), ← Real.rpow_mul (hK_nn x.1 x.2)]
    have h65 : (3 / 5 : ℝ) * 2 = 6 / 5 := by norm_num
    have h3 : (3 / 2 : ℝ) * 2 = (3 : ℕ) := by norm_num
    rw [h65, h3, Real.rpow_natCast]
  have hsum_f2 : (∑ x ∈ F ×ˢ F, f2 x ^ (2 : ℝ)) ≤ A * M := by
    simp_rw [hf2_sq]
    rw [Finset.sum_product]
    calc
      (∑ a ∈ F, ∑ b ∈ F, U a ^ (6 / 5 : ℝ) * K a b ^ 3)
          = ∑ a ∈ F, U a ^ (6 / 5 : ℝ) * (∑ b ∈ F, K a b ^ 3) := by
            apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]
      _ ≤ ∑ a ∈ F, U a ^ (6 / 5 : ℝ) * M := by
            apply Finset.sum_le_sum
            intro a ha
            exact mul_le_mul_of_nonneg_left (row_cubic_bound m hm he F hF (hF a ha))
              (Real.rpow_nonneg (hU_nn a) _)
      _ = A * M := by rw [← Finset.sum_mul]
  have hsum_g2 : (∑ x ∈ F ×ˢ F, g2 x ^ (2 : ℝ)) ≤ Bsum * M := by
    simp_rw [hg2_sq]
    rw [Finset.sum_product_right]
    calc
      (∑ b ∈ F, ∑ a ∈ F, V b ^ (6 / 5 : ℝ) * K a b ^ 3)
          = ∑ b ∈ F, V b ^ (6 / 5 : ℝ) * (∑ a ∈ F, K a b ^ 3) := by
            apply Finset.sum_congr rfl; intro b _; rw [Finset.mul_sum]
      _ ≤ ∑ b ∈ F, V b ^ (6 / 5 : ℝ) * M := by
            apply Finset.sum_le_sum
            intro b hb
            exact mul_le_mul_of_nonneg_left (col_cubic_bound m hm he F hF (hF b hb))
              (Real.rpow_nonneg (hV_nn b) _)
      _ = Bsum * M := by rw [← Finset.sum_mul]
  have hsum_f1_le : (∑ x ∈ F ×ˢ F, f1 x ^ (3 : ℝ)) ≤ M * A ^ (1 / 2 : ℝ) * Bsum ^ (1 / 2 : ℝ) := by
    have hHolder2 := Real.inner_le_Lp_mul_Lq_of_nonneg (s := F ×ˢ F) hConj2 hf2_nn hg2_nn
    have hsf2_nn : 0 ≤ ∑ x ∈ F ×ˢ F, f2 x ^ (2 : ℝ) :=
      Finset.sum_nonneg fun x hx => Real.rpow_nonneg (hf2_nn x hx) _
    have hsg2_nn : 0 ≤ ∑ x ∈ F ×ˢ F, g2 x ^ (2 : ℝ) :=
      Finset.sum_nonneg fun x hx => Real.rpow_nonneg (hg2_nn x hx) _
    have hstep1 : (∑ x ∈ F ×ˢ F, f1 x ^ (3 : ℝ))
        ≤ (A * M) ^ (1 / 2 : ℝ) * (Bsum * M) ^ (1 / 2 : ℝ) := by
      calc
        (∑ x ∈ F ×ˢ F, f1 x ^ (3 : ℝ)) = ∑ x ∈ F ×ˢ F, f2 x * g2 x := by
          apply Finset.sum_congr rfl; intro x _; exact (hprod2 x).symm
        _ ≤ (∑ x ∈ F ×ˢ F, f2 x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
            (∑ x ∈ F ×ˢ F, g2 x ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hHolder2
        _ ≤ (A * M) ^ (1 / 2 : ℝ) * (Bsum * M) ^ (1 / 2 : ℝ) := by
          exact mul_le_mul
            (Real.rpow_le_rpow hsf2_nn hsum_f2 (by norm_num))
            (Real.rpow_le_rpow hsg2_nn hsum_g2 (by norm_num))
            (Real.rpow_nonneg hsg2_nn _)
            (Real.rpow_nonneg (mul_nonneg hA_nn hM_nn) _)
    refine hstep1.trans_eq ?_
    rw [Real.mul_rpow hA_nn hM_nn, Real.mul_rpow hB_nn hM_nn]
    have hMM : M ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) = M := by
      rw [← Real.rpow_add' hM_nn (by norm_num)]
      norm_num
    calc
      A ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ) * (Bsum ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ))
          = (M ^ (1 / 2 : ℝ) * M ^ (1 / 2 : ℝ)) * A ^ (1 / 2 : ℝ) * Bsum ^ (1 / 2 : ℝ) := by ring
      _ = M * A ^ (1 / 2 : ℝ) * Bsum ^ (1 / 2 : ℝ) := by rw [hMM]
  -- 合并两次 Hölder 结果
  have hsf1_nn : 0 ≤ ∑ x ∈ F ×ˢ F, f1 x ^ (3 : ℝ) :=
    Finset.sum_nonneg fun x hx => Real.rpow_nonneg (hf1_nn x hx) _
  have hM_rpow : M ^ (1 / 3 : ℝ) = (3 : ℝ) ^ (1 / 3 : ℝ) * ‖O m‖ := by
    dsimp only [M]
    rw [Real.mul_rpow (by norm_num) (pow_nonneg (norm_nonneg _) 3)]
    have hO3 : (‖O m‖ ^ (3 : ℕ)) ^ (1 / 3 : ℝ) = ‖O m‖ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
      norm_num
    rw [hO3]
  have hpow_merge :
      (M * A ^ (1 / 2 : ℝ) * Bsum ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) * (A * Bsum) ^ (1 / (3 / 2 : ℝ))
        = (3 : ℝ) ^ (1 / 3 : ℝ) * ‖O m‖ * norm65 F u * norm65 F v := by
    have h23 : (1 / (3 / 2 : ℝ)) = (2 / 3 : ℝ) := by norm_num
    rw [h23, Real.mul_rpow (mul_nonneg hM_nn (Real.rpow_nonneg hA_nn _)) (Real.rpow_nonneg hB_nn _),
        Real.mul_rpow hM_nn (Real.rpow_nonneg hA_nn _),
        Real.mul_rpow hA_nn hB_nn,
        ← Real.rpow_mul hA_nn, ← Real.rpow_mul hB_nn, hM_rpow]
    have hA_exp : A ^ ((1 / 2 : ℝ) * (1 / 3 : ℝ)) * A ^ (2 / 3 : ℝ) = A ^ (5 / 6 : ℝ) := by
      rw [← Real.rpow_add' hA_nn (by norm_num)]
      norm_num
    have hB_exp : Bsum ^ ((1 / 2 : ℝ) * (1 / 3 : ℝ)) * Bsum ^ (2 / 3 : ℝ) = Bsum ^ (5 / 6 : ℝ) := by
      rw [← Real.rpow_add' hB_nn (by norm_num)]
      norm_num
    dsimp only [norm65, A, Bsum, U, V]
    calc
      (3 : ℝ) ^ (1 / 3 : ℝ) * ‖O m‖ * A ^ ((1 / 2 : ℝ) * (1 / 3 : ℝ)) *
          Bsum ^ ((1 / 2 : ℝ) * (1 / 3 : ℝ)) * (A ^ (2 / 3 : ℝ) * Bsum ^ (2 / 3 : ℝ))
          = (3 : ℝ) ^ (1 / 3 : ℝ) * ‖O m‖ *
            (A ^ ((1 / 2 : ℝ) * (1 / 3 : ℝ)) * A ^ (2 / 3 : ℝ)) *
            (Bsum ^ ((1 / 2 : ℝ) * (1 / 3 : ℝ)) * Bsum ^ (2 / 3 : ℝ)) := by ring
      _ = (3 : ℝ) ^ (1 / 3 : ℝ) * ‖O m‖ * A ^ (5 / 6 : ℝ) * Bsum ^ (5 / 6 : ℝ) := by
            rw [hA_exp, hB_exp]
  calc
    (∑ a ∈ F, ∑ b ∈ F, |u a| * ‖S a.2 b.2 m‖ * |v b|)
        = ∑ x ∈ F ×ˢ F, f1 x * g1 x := hlhs1
    _ ≤ (∑ x ∈ F ×ˢ F, f1 x ^ (3 : ℝ)) ^ (1 / 3 : ℝ) *
        (∑ x ∈ F ×ˢ F, g1 x ^ (3 / 2 : ℝ)) ^ (1 / (3 / 2 : ℝ)) := hHolder1
    _ = (∑ x ∈ F ×ˢ F, f1 x ^ (3 : ℝ)) ^ (1 / 3 : ℝ) * (A * Bsum) ^ (1 / (3 / 2 : ℝ)) := by
        rw [hsum_g1]
    _ ≤ (M * A ^ (1 / 2 : ℝ) * Bsum ^ (1 / 2 : ℝ)) ^ (1 / 3 : ℝ) *
        (A * Bsum) ^ (1 / (3 / 2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hsf1_nn hsum_f1_le (by norm_num))
          (Real.rpow_nonneg (mul_nonneg hA_nn hB_nn) _)
    _ = (3 : ℝ) ^ (1 / 3 : ℝ) * ‖O m‖ * norm65 F u * norm65 F v := hpow_merge

-- ============================================================================
-- 第二部分：复 Beta 积分衰减 `‖Γ(z₁)Γ(z₂)/Γ(z₁+z₂)‖ ≤ 64 / √T`
-- ============================================================================

/-- Beta 被积函数 `x^(z₁ - 1) * (1 - x)^(z₂ - 1)`。 -/
private noncomputable def betaFn (z₁ z₂ : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)

/-- 实部在 `[1/2, 1]` 时，开区间 `(0, 1)` 上 `‖betaFn z₁ z₂ x‖ ≤ x^(-1/2) * (1 - x)^(-1/2)`。 -/
private lemma norm_betaFn_le {z₁ z₂ : ℂ} (h1 : 1 / 2 ≤ z₁.re) (h2 : 1 / 2 ≤ z₂.re)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ‖betaFn z₁ z₂ x‖ ≤ x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) := by
  have h1x : 0 < 1 - x := by linarith
  have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
  dsimp only [betaFn]
  rw [norm_mul, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      Complex.norm_cpow_eq_rpow_re_of_pos h1x]
  have he1 : (-1 / 2 : ℝ) ≤ (z₁ - 1).re := by simp; linarith
  have he2 : (-1 / 2 : ℝ) ≤ (z₂ - 1).re := by simp; linarith
  exact mul_le_mul
    (Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le he1)
    (Real.rpow_le_rpow_of_exponent_ge h1x (by linarith) he2)
    (Real.rpow_nonneg h1x.le _)
    (Real.rpow_nonneg hx0.le _)

/-- 辅助：`(1/2)^(-1/2) ≤ 2`。 -/
private lemma half_rpow_neg_half_le_two : (1 / 2 : ℝ) ^ (-1 / 2 : ℝ) ≤ 2 := by
  have hsq : ((1 / 2 : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 = 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (-1 / 2 : ℝ)]

/-- 左端点尾估计：当 `0 < δ ≤ 1/2` 时，`‖∫ x in 0..δ, betaFn z₁ z₂ x‖ ≤ 4 * √δ`。 -/
private lemma left_tail_bound {z₁ z₂ : ℂ} (h1 : 1 / 2 ≤ z₁.re) (h2 : 1 / 2 ≤ z₂.re)
    {δ : ℝ} (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ‖∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x‖ ≤ 4 * Real.sqrt δ := by
  have hbound_ae : ∀ᵐ x ∂volume.restrict (Set.uIoc (0 : ℝ) δ),
      ‖betaFn z₁ z₂ x‖ ≤ (2 : ℝ) * x ^ (-1 / 2 : ℝ) := by
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    rw [Set.uIoc_of_le hδ0.le] at hx
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 (by linarith)
    have h1x_ge : (1 / 2 : ℝ) ≤ 1 - x := by linarith [hx.2]
    have h1x_pow : (1 - x) ^ (-1 / 2 : ℝ) ≤ 2 := by
      refine (Real.rpow_le_rpow_of_nonpos (by norm_num) h1x_ge (by norm_num)).trans
        half_rpow_neg_half_le_two
    calc
      ‖betaFn z₁ z₂ x‖ ≤ x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) :=
        norm_betaFn_le h1 h2 hx0 hx1
      _ ≤ x ^ (-1 / 2 : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left h1x_pow (Real.rpow_nonneg hx0.le _)
      _ = 2 * x ^ (-1 / 2 : ℝ) := mul_comm _ _
  have hint : IntervalIntegrable (fun x : ℝ => (2 : ℝ) * x ^ (-1 / 2 : ℝ)) volume 0 δ :=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul 2
  have hle := intervalIntegral.norm_integral_le_abs_of_norm_le hbound_ae hint
  have hval : (∫ x in (0 : ℝ)..δ, (2 : ℝ) * x ^ (-1 / 2 : ℝ)) = 4 * Real.sqrt δ := by
    rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
    have hexp : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
    rw [hexp, Real.zero_rpow (by norm_num), sub_zero, ← Real.sqrt_eq_rpow]
    ring
  rw [hval, abs_of_nonneg (by positivity)] at hle
  exact hle

/-- 右端点尾估计：由对称换元 `x ↦ 1 - x` 直接归结为左端点尾估计。 -/
private lemma right_tail_bound {z₁ z₂ : ℂ} (h1 : 1 / 2 ≤ z₁.re) (h2 : 1 / 2 ≤ z₂.re)
    {δ : ℝ} (hδ0 : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ‖∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x‖ ≤ 4 * Real.sqrt δ := by
  have hsymm : (∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x) = ∫ u in (0 : ℝ)..δ, betaFn z₂ z₁ u := by
    have hcomp := intervalIntegral.integral_comp_sub_left (fun u : ℝ => betaFn z₂ z₁ u) (1 : ℝ)
      (a := 1 - δ) (b := 1)
    have hsub1 : (1 : ℝ) - 1 = 0 := by ring
    have hsub2 : (1 : ℝ) - (1 - δ) = δ := by ring
    rw [hsub1, hsub2] at hcomp
    rw [← hcomp]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [betaFn]
    have h1 : (1 - ((1 - x : ℝ) : ℂ)) = (x : ℂ) := by push_cast; ring
    have h2 : ((1 - x : ℝ) : ℂ) = 1 - (x : ℂ) := by push_cast; ring
    rw [h1, h2, mul_comm]
  rw [hsymm]
  exact left_tail_bound h2 h1 hδ0 hδhalf

/-- 全局粗界：`‖betaIntegral z₁ z₂‖ ≤ 8`（用于 `1 ≤ T ≤ 64` 情形）。 -/
private lemma betaIntegral_norm_le_eight {z₁ z₂ : ℂ} (h1 : 1 / 2 ≤ z₁.re) (h2 : 1 / 2 ≤ z₂.re) :
    ‖Complex.betaIntegral z₁ z₂‖ ≤ 8 := by
  have hz1 : 0 < z₁.re := by linarith
  have hz2 : 0 < z₂.re := by linarith
  have hint : IntervalIntegrable (betaFn z₁ z₂) volume 0 1 :=
    Complex.betaIntegral_convergent hz1 hz2
  have hleft_int : IntervalIntegrable (betaFn z₁ z₂) volume 0 (1 / 2) :=
    hint.mono_set (by rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]; intro x hx; exact ⟨hx.1, by linarith [hx.2]⟩)
  have hright_int : IntervalIntegrable (betaFn z₁ z₂) volume (1 / 2) 1 :=
    hint.mono_set (by rw [Set.uIcc_of_le (by norm_num), Set.uIcc_of_le (by norm_num)]; intro x hx; exact ⟨by linarith [hx.1], hx.2⟩)
  have hsplit : Complex.betaIntegral z₁ z₂ =
      (∫ x in (0 : ℝ)..(1 / 2), betaFn z₁ z₂ x) + ∫ x in (1 / 2 : ℝ)..1, betaFn z₁ z₂ x := by
    unfold Complex.betaIntegral
    exact (intervalIntegral.integral_add_adjacent_intervals hleft_int hright_int).symm
  rw [hsplit]
  have hL := left_tail_bound h1 h2 (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
  have hR : ‖∫ x in (1 / 2 : ℝ)..1, betaFn z₁ z₂ x‖ ≤ 4 * Real.sqrt (1 / 2) := by
    have hR0 := right_tail_bound h1 h2 (by norm_num : (0 : ℝ) < 1 / 2) le_rfl
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hR0
    exact hR0
  have hsqrt_le : Real.sqrt (1 / 2 : ℝ) ≤ 1 := by
    rw [Real.sqrt_le_one]; norm_num
  calc
    ‖(∫ x in (0 : ℝ)..(1 / 2), betaFn z₁ z₂ x) + ∫ x in (1 / 2 : ℝ)..1, betaFn z₁ z₂ x‖
        ≤ ‖∫ x in (0 : ℝ)..(1 / 2), betaFn z₁ z₂ x‖ +
          ‖∫ x in (1 / 2 : ℝ)..1, betaFn z₁ z₂ x‖ := norm_add_le _ _
    _ ≤ 4 * Real.sqrt (1 / 2) + 4 * Real.sqrt (1 / 2) := add_le_add hL hR
    _ ≤ 4 * 1 + 4 * 1 := by linarith
    _ = 8 := by norm_num

/-- 复共轭不变性：`‖betaIntegral (conj z₁) (conj z₂)‖ = ‖betaIntegral z₁ z₂‖`。 -/
private lemma norm_betaIntegral_conj {z₁ z₂ : ℂ} (hz1 : 0 < z₁.re) (hz2 : 0 < z₂.re) :
    ‖Complex.betaIntegral (starRingEnd ℂ z₁) (starRingEnd ℂ z₂)‖ =
      ‖Complex.betaIntegral z₁ z₂‖ := by
  have hint : IntervalIntegrable (betaFn z₁ z₂) volume 0 1 :=
    Complex.betaIntegral_convergent hz1 hz2
  have hconj : starRingEnd ℂ (Complex.betaIntegral z₁ z₂) =
      Complex.betaIntegral (starRingEnd ℂ z₁) (starRingEnd ℂ z₂) := by
    change Complex.conjCLE.toContinuousLinearMap (∫ x in (0 : ℝ)..1, betaFn z₁ z₂ x) =
      ∫ x in (0 : ℝ)..1, betaFn (starRingEnd ℂ z₁) (starRingEnd ℂ z₂) x
    rw [← Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hint]
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    have hx0 : 0 < x := hx.1
    have h1x : 0 < 1 - x := by linarith [hx.2]
    have hcpow_conj : ∀ (r : ℝ) (hr : 0 < r) (w : ℂ),
        starRingEnd ℂ ((r : ℂ) ^ w) = (r : ℂ) ^ (starRingEnd ℂ w) := by
      intro r hr w
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
          Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
          ← Complex.ofReal_log hr.le, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
    change starRingEnd ℂ ((x : ℂ) ^ (z₁ - 1) * (1 - (x : ℂ)) ^ (z₂ - 1)) = _
    have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, map_mul, hcpow_conj x hx0 (z₁ - 1), hcpow_conj (1 - x) h1x (z₂ - 1)]
    dsimp only [betaFn]
    rw [hcast, map_sub, map_sub, map_one]
  rw [← hconj, Complex.norm_conj]

/-- 辅助：`∫ x in a..b, (x^(-1/2) + (1 - x)^(-1/2)) ≤ 4`（对 `0 < a ≤ b < 1`）。 -/
private lemma integral_inv_sqrt_pair_le_four {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ x in a..b, (x ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ))) ≤ 4 := by
  have hint1 : IntervalIntegrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hint2 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ)) volume a b := by
    have hcont : ContinuousOn (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ)) (Set.uIcc a b) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have h1x_pos : 0 < 1 - x := by linarith [hx.2]
      exact ((continuousAt_const.sub continuousAt_id).rpow_const
        (Or.inl h1x_pos.ne')).continuousWithinAt
    exact hcont.intervalIntegrable
  rw [intervalIntegral.integral_add hint1 hint2]
  have hI1 : (∫ x in a..b, x ^ (-1 / 2 : ℝ)) ≤ 2 := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
    have hexp : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
    rw [hexp]
    have hb1 : b ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (by linarith) hb.le (by norm_num)
    have ha0 : 0 ≤ a ^ (1 / 2 : ℝ) := Real.rpow_nonneg ha.le _
    linarith
  have hI2 : (∫ x in a..b, (1 - x) ^ (-1 / 2 : ℝ)) ≤ 2 := by
    rw [intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ (-1 / 2 : ℝ)) (1 : ℝ),
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
    have hexp : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
    rw [hexp]
    have ha1 : (1 - a) ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) (by norm_num)
    have hb0 : 0 ≤ (1 - b) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    linarith
  linarith

/-- 核心分部积分引理：在任意无驻点闭子区间 `[a, b] ⊂ (0, 1)` 上，若 `|D x| ≥ M_D > 0`，则
    `‖∫ x in a..b, betaFn z₁ z₂ x‖ ≤ 6 / M_D + ∫ x in a..b, |t₁ + t₂| / (D x)^2`。 -/
private lemma betaFn_ibp_bound {z₁ z₂ : ℂ}
    (h1l : 1 / 2 ≤ z₁.re) (h1u : z₁.re ≤ 1) (h2l : 1 / 2 ≤ z₂.re) (h2u : z₂.re ≤ 1)
    {a b M_D : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (hM : 0 < M_D)
    (hD_ge : ∀ x ∈ Set.Icc a b, M_D ≤ |z₁.im - (z₁.im + z₂.im) * x|) :
    ‖∫ x in a..b, betaFn z₁ z₂ x‖
      ≤ 6 / M_D + ∫ x in a..b, |z₁.im + z₂.im| / (z₁.im - (z₁.im + z₂.im) * x) ^ 2 := by
  set σ₁ : ℝ := z₁.re
  set σ₂ : ℝ := z₂.re
  set t₁ : ℝ := z₁.im
  set t₂ : ℝ := z₂.im
  let D : ℝ → ℝ := fun x => t₁ - (t₁ + t₂) * x
  let N : ℝ → ℝ := fun x => x ^ σ₁ * (1 - x) ^ σ₂
  let N' : ℝ → ℝ := fun x =>
    σ₁ * x ^ (σ₁ - 1) * (1 - x) ^ σ₂ - σ₂ * x ^ σ₁ * (1 - x) ^ (σ₂ - 1)
  let q : ℝ → ℝ := fun x => N x / D x
  let q' : ℝ → ℝ := fun x => (N' x * D x + (t₁ + t₂) * N x) / (D x) ^ 2
  let θ : ℝ → ℝ := fun x => t₁ * Real.log x + t₂ * Real.log (1 - x)
  let E : ℝ → ℂ := fun x => Complex.exp (Complex.I * (θ x : ℂ))
  let G : ℝ → ℂ := fun x => ((q x : ℂ) / Complex.I) * E x
  let R : ℝ → ℂ := fun x => ((q' x : ℂ) / Complex.I) * E x
  have hD_ne : ∀ x ∈ Set.Icc a b, D x ≠ 0 := by
    intro x hx h0
    have h := hD_ge x hx
    change M_D ≤ |D x| at h
    rw [h0, abs_zero] at h
    linarith
  -- 第一步：验证 `x ∈ [a, b]` 上 `betaFn z₁ z₂ x = (x^(σ₁-1)*(1-x)^(σ₂-1) : ℂ) * E x`
  have hbeta_eq : ∀ x ∈ Set.Icc a b,
      betaFn z₁ z₂ x = ((x ^ (σ₁ - 1) * (1 - x) ^ (σ₂ - 1) : ℝ) : ℂ) * E x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1x : 0 < 1 - x := by linarith [hx.2]
    have hsplit : ∀ (r : ℝ) (hr : 0 < r) (w : ℂ),
        (r : ℂ) ^ (w - 1) =
          ((r ^ (w.re - 1) : ℝ) : ℂ) * Complex.exp (Complex.I * ((w.im * Real.log r : ℝ) : ℂ)) := by
      intro r hr w
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
          ← Complex.ofReal_log hr.le, Real.rpow_def_of_pos hr, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      have hw : w - 1 = ((w.re - 1 : ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [hw]
      push_cast
      ring
    have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    dsimp only [betaFn, E, θ]
    rw [hcast, hsplit x hx0 z₁, hsplit (1 - x) h1x z₂]
    push_cast
    calc
      ((x ^ (σ₁ - 1) : ℝ) : ℂ) * Complex.exp (Complex.I * ((t₁ : ℂ) * (Real.log x : ℂ))) *
          ((((1 - x) ^ (σ₂ - 1) : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((t₂ : ℂ) * (Real.log (1 - x) : ℂ))))
          = ((x ^ (σ₁ - 1) : ℝ) : ℂ) * (((1 - x) ^ (σ₂ - 1) : ℝ) : ℂ) *
            (Complex.exp (Complex.I * ((t₁ : ℂ) * (Real.log x : ℂ))) *
             Complex.exp (Complex.I * ((t₂ : ℂ) * (Real.log (1 - x) : ℂ)))) := by ring
      _ = ((x ^ (σ₁ - 1) : ℝ) : ℂ) * (((1 - x) ^ (σ₂ - 1) : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((t₁ : ℂ) * (Real.log x : ℂ) +
            (t₂ : ℂ) * (Real.log (1 - x) : ℂ))) := by
            rw [← Complex.exp_add]; congr 2; ring
  -- 第二步：验证 `G'(x) = betaFn z₁ z₂ x + R x`
  have hG_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt G (betaFn z₁ z₂ x + R x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1x : 0 < 1 - x := by linarith [hx.2]
    have hDx : D x ≠ 0 := hD_ne x hx
    -- 实值函数 `N, D, q, θ` 的导数
    have hd_xσ₁ : HasDerivAt (fun y : ℝ => y ^ σ₁) (σ₁ * x ^ (σ₁ - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx0.ne')
    have hd_1x : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
      have h := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
      change HasDerivAt (fun y : ℝ => 1 - y) (0 - 1) x at h
      convert h using 1
      ring
    have hd_1xσ₂ : HasDerivAt (fun y : ℝ => (1 - y) ^ σ₂) (-(σ₂ * (1 - x) ^ (σ₂ - 1))) x := by
      have hcomp := (Real.hasDerivAt_rpow_const (x := 1 - x) (p := σ₂) (Or.inl h1x.ne')).comp x hd_1x
      change HasDerivAt (fun y : ℝ => (1 - y) ^ σ₂) _ x at hcomp
      convert hcomp using 1
      ring
    have hd_N : HasDerivAt N (N' x) x := by
      have hmul := hd_xσ₁.mul hd_1xσ₂
      change HasDerivAt N _ x at hmul
      convert hmul using 1
      dsimp only [N']
      ring
    have hd_D : HasDerivAt D (-(t₁ + t₂)) x := by
      have h := (hasDerivAt_const x t₁).sub ((hasDerivAt_id x).const_mul (t₁ + t₂))
      change HasDerivAt D _ x at h
      convert h using 1
      ring
    have hd_q : HasDerivAt q (q' x) x := by
      have hdiv := hd_N.div hd_D hDx
      change HasDerivAt q _ x at hdiv
      convert hdiv using 1
      dsimp only [q']
      ring
    have hd_θ : HasDerivAt θ (D x / (x * (1 - x))) x := by
      have h1 := (Real.hasDerivAt_log hx0.ne').const_mul t₁
      have h2 := ((Real.hasDerivAt_log h1x.ne').comp x hd_1x).const_mul t₂
      have hsum := h1.add h2
      change HasDerivAt θ _ x at hsum
      convert hsum using 1
      dsimp only [D]
      field_simp [hx0.ne', h1x.ne']
      ring
    -- 提升到 `ℂ`
    have hd_qC : HasDerivAt (fun y : ℝ => ((q y : ℂ) / Complex.I)) ((q' x : ℂ) / Complex.I) x := by
      exact (hd_q.ofReal_comp).div_const Complex.I
    have hd_θC : HasDerivAt (fun y : ℝ => Complex.I * (θ y : ℂ))
        (Complex.I * ((D x / (x * (1 - x)) : ℝ) : ℂ)) x := by
      exact (hd_θ.ofReal_comp).const_mul Complex.I
    have hd_E : HasDerivAt E (Complex.exp (Complex.I * (θ x : ℂ)) *
        (Complex.I * ((D x / (x * (1 - x)) : ℝ) : ℂ))) x :=
      hd_θC.cexp
    have hd_G := hd_qC.mul hd_E
    -- 化简导数表达式
    have hrpow_x : x ^ σ₁ / x = x ^ (σ₁ - 1) := by
      rw [Real.rpow_sub hx0, Real.rpow_one]
    have hrpow_1x : (1 - x) ^ σ₂ / (1 - x) = (1 - x) ^ (σ₂ - 1) := by
      rw [Real.rpow_sub h1x, Real.rpow_one]
    have hcancel_real : q x * (D x / (x * (1 - x))) = x ^ (σ₁ - 1) * (1 - x) ^ (σ₂ - 1) := by
      dsimp only [q, N]
      calc
        x ^ σ₁ * (1 - x) ^ σ₂ / D x * (D x / (x * (1 - x)))
            = (x ^ σ₁ / x) * ((1 - x) ^ σ₂ / (1 - x)) := by
              field_simp [hDx, hx0.ne', h1x.ne']
        _ = x ^ (σ₁ - 1) * (1 - x) ^ (σ₂ - 1) := by rw [hrpow_x, hrpow_1x]
    convert hd_G using 1
    rw [hbeta_eq x hx]
    dsimp only [R, E]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    calc
      ((x ^ (σ₁ - 1) * (1 - x) ^ (σ₂ - 1) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ x : ℂ)) +
          ((q' x : ℂ) / Complex.I) * Complex.exp (Complex.I * (θ x : ℂ))
          = ((q' x : ℂ) / Complex.I) * Complex.exp (Complex.I * (θ x : ℂ)) +
            ((q x * (D x / (x * (1 - x))) : ℝ) : ℂ) * Complex.exp (Complex.I * (θ x : ℂ)) := by
            rw [hcancel_real, add_comm]
      _ = ((q' x : ℂ) / Complex.I) * Complex.exp (Complex.I * (θ x : ℂ)) +
          ((q x : ℂ) / Complex.I) * (Complex.exp (Complex.I * (θ x : ℂ)) *
            (Complex.I * ((D x / (x * (1 - x)) : ℝ) : ℂ))) := by
            push_cast
            field_simp [hI]
  -- 第三步：在闭区间 `[a, b]` 上证明连续性（进而区间可积）
  have hbeta_cont : ContinuousOn (betaFn z₁ z₂) (Set.uIcc a b) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1x : 0 < 1 - x := by linarith [hx.2]
    have h1c : ContinuousAt (fun y : ℝ => (y : ℂ) ^ (z₁ - 1)) x :=
      Complex.continuousAt_ofReal_cpow_const x (z₁ - 1) (Or.inr hx0.ne')
    have h2c : ContinuousAt (fun y : ℝ => ((1 - y : ℝ) : ℂ) ^ (z₂ - 1)) x :=
      (Complex.continuousAt_ofReal_cpow_const (1 - x) (z₂ - 1) (Or.inr h1x.ne')).comp
        (continuousAt_const.sub continuousAt_id)
    have heq : betaFn z₁ z₂ =
        fun y : ℝ => (y : ℂ) ^ (z₁ - 1) * ((1 - y : ℝ) : ℂ) ^ (z₂ - 1) := by
      ext y; dsimp only [betaFn]; push_cast; rfl
    rw [heq]
    exact (h1c.mul h2c).continuousWithinAt
  have hR_cont : ContinuousOn R (Set.uIcc a b) := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h1x : 0 < 1 - x := by linarith [hx.2]
    have hDx : D x ≠ 0 := hD_ne x hx
    have hcN : ContinuousAt N x :=
      (continuousAt_id.rpow_const (Or.inl hx0.ne')).mul
        ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl h1x.ne'))
    have hcN' : ContinuousAt N' x := by
      have h1 := ((continuousAt_id.rpow_const (p := σ₁ - 1) (Or.inl hx0.ne')).const_mul σ₁).mul
        ((continuousAt_const.sub continuousAt_id).rpow_const (p := σ₂) (Or.inl h1x.ne'))
      have h2 := ((continuousAt_id.rpow_const (p := σ₁) (Or.inl hx0.ne')).const_mul σ₂).mul
        ((continuousAt_const.sub continuousAt_id).rpow_const (p := σ₂ - 1) (Or.inl h1x.ne'))
      exact h1.sub h2
    have hcD : ContinuousAt D x := continuousAt_const.sub (continuousAt_id.const_mul (t₁ + t₂))
    have hcq' : ContinuousAt q' x :=
      ((hcN'.mul hcD).add (hcN.const_mul (t₁ + t₂))).div (hcD.pow 2) (pow_ne_zero 2 hDx)
    have hcθ : ContinuousAt θ x :=
      ((Real.continuousAt_log hx0.ne').const_mul t₁).add
        (((Real.continuousAt_log h1x.ne').comp (continuousAt_const.sub continuousAt_id)).const_mul t₂)
    have hcE : ContinuousAt E x :=
      (Complex.continuous_exp.continuousAt).comp
        (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hcθ))
    exact (((Complex.continuous_ofReal.continuousAt.comp hcq').div_const Complex.I).mul hcE).continuousWithinAt
  have hbeta_int : IntervalIntegrable (betaFn z₁ z₂) volume a b := hbeta_cont.intervalIntegrable
  have hR_int : IntervalIntegrable R volume a b := hR_cont.intervalIntegrable
  -- 第四步：应用微积分基本定理
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hG_deriv (hbeta_int.add hR_int)
  rw [intervalIntegral.integral_add hbeta_int hR_int] at hFTC
  have hIntEq : (∫ x in a..b, betaFn z₁ z₂ x) = G b - G a - ∫ x in a..b, R x := by
    exact eq_sub_of_add_eq hFTC
  -- 第五步：模长估计
  have hE_norm : ∀ x : ℝ, ‖E x‖ = 1 := by
    intro x
    dsimp only [E]
    rw [Complex.norm_exp]
    simp
  have hN_le : ∀ x ∈ Set.Icc a b, 0 ≤ N x ∧ N x ≤ 1 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hb
    have h1x : 0 < 1 - x := by linarith
    refine ⟨mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.rpow_nonneg h1x.le _), ?_⟩
    have h1 : x ^ σ₁ ≤ 1 := Real.rpow_le_one hx0.le hx1.le (by linarith)
    have h2 : (1 - x) ^ σ₂ ≤ 1 := Real.rpow_le_one h1x.le (by linarith) (by linarith)
    nlinarith [Real.rpow_nonneg hx0.le σ₁, Real.rpow_nonneg h1x.le σ₂]
  have hG_le : ∀ x ∈ Set.Icc a b, ‖G x‖ ≤ 1 / M_D := by
    intro x hx
    have hDx : M_D ≤ |D x| := hD_ge x hx
    have hN := hN_le x hx
    dsimp only [G, q]
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_I, div_one, hE_norm, mul_one,
        Real.norm_eq_abs, abs_div, abs_of_nonneg hN.1]
    calc
      N x / |D x| ≤ 1 / |D x| := div_le_div_of_nonneg_right hN.2 (abs_nonneg _)
      _ ≤ 1 / M_D := one_div_le_one_div_of_le hM hDx
  have hR_le : ∀ x ∈ Set.Icc a b,
      ‖R x‖ ≤ (1 / M_D) * (x ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ)) +
        |t₁ + t₂| / (D x) ^ 2 := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have hx1 : x < 1 := lt_of_le_of_lt hx.2 hb
    have h1x : 0 < 1 - x := by linarith
    have hDx_ne : D x ≠ 0 := hD_ne x hx
    have hDx_ge : M_D ≤ |D x| := hD_ge x hx
    have hN := hN_le x hx
    have hN'_le : |N' x| ≤ x ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ) := by
      dsimp only [N']
      have h1 : |σ₁ * x ^ (σ₁ - 1) * (1 - x) ^ σ₂| ≤ x ^ (-1 / 2 : ℝ) := by
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _))
          (Real.rpow_nonneg h1x.le _))]
        have ha1 : x ^ (σ₁ - 1) ≤ x ^ (-1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hx0 hx1.le (by linarith)
        have ha2 : (1 - x) ^ σ₂ ≤ 1 := Real.rpow_le_one h1x.le (by linarith) (by linarith)
        calc
          σ₁ * x ^ (σ₁ - 1) * (1 - x) ^ σ₂ ≤ 1 * x ^ (-1 / 2 : ℝ) * 1 := by
            refine mul_le_mul (mul_le_mul h1u ha1 (Real.rpow_nonneg hx0.le _) (by norm_num))
              ha2 (Real.rpow_nonneg h1x.le _) (by positivity)
          _ = x ^ (-1 / 2 : ℝ) := by ring
      have h2 : |σ₂ * x ^ σ₁ * (1 - x) ^ (σ₂ - 1)| ≤ (1 - x) ^ (-1 / 2 : ℝ) := by
        rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg hx0.le _))
          (Real.rpow_nonneg h1x.le _))]
        have hb1 : x ^ σ₁ ≤ 1 := Real.rpow_le_one hx0.le hx1.le (by linarith)
        have hb2 : (1 - x) ^ (σ₂ - 1) ≤ (1 - x) ^ (-1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge h1x (by linarith) (by linarith)
        calc
          σ₂ * x ^ σ₁ * (1 - x) ^ (σ₂ - 1) ≤ 1 * 1 * (1 - x) ^ (-1 / 2 : ℝ) := by
            refine mul_le_mul (mul_le_mul h2u hb1 (Real.rpow_nonneg hx0.le _) (by norm_num))
              hb2 (Real.rpow_nonneg h1x.le _) (by positivity)
          _ = (1 - x) ^ (-1 / 2 : ℝ) := by ring
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    have hq'_split : q' x = N' x / D x + (t₁ + t₂) * N x / (D x) ^ 2 := by
      dsimp only [q']
      field_simp [hDx_ne]
    dsimp only [R]
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_I, div_one, hE_norm, mul_one,
        Real.norm_eq_abs, hq'_split]
    calc
      |N' x / D x + (t₁ + t₂) * N x / (D x) ^ 2|
          ≤ |N' x / D x| + |(t₁ + t₂) * N x / (D x) ^ 2| := abs_add_le _ _
      _ = |N' x| / |D x| + |t₁ + t₂| * N x / (D x) ^ 2 := by
          rw [abs_div, abs_div, abs_mul, abs_of_nonneg hN.1, abs_of_nonneg (sq_nonneg (D x))]
      _ ≤ (x ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ)) / M_D + |t₁ + t₂| * 1 / (D x) ^ 2 := by
          refine add_le_add ?_ ?_
          · calc
              |N' x| / |D x| ≤ (x ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ)) / |D x| :=
                div_le_div_of_nonneg_right hN'_le (abs_nonneg _)
              _ ≤ (x ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ)) / M_D :=
                div_le_div_of_nonneg_left (by positivity) hM hDx_ge
          · exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hN.2 (abs_nonneg _)) (sq_nonneg _)
      _ = (1 / M_D) * (x ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ)) +
          |t₁ + t₂| / (D x) ^ 2 := by ring
  -- 整合积分估计
  have hint_pair : IntervalIntegrable (fun x : ℝ =>
      (1 / M_D) * (x ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ))) volume a b := by
    have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-1 / 2 : ℝ)) volume a b :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h2 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ)) volume a b := by
      have hc : ContinuousOn (fun x : ℝ => (1 - x) ^ (-1 / 2 : ℝ)) (Set.uIcc a b) := by
        intro x hx
        rw [Set.uIcc_of_le hab] at hx
        have h1x_pos : 0 < 1 - x := by linarith [hx.2]
        exact ((continuousAt_const.sub continuousAt_id).rpow_const
          (Or.inl h1x_pos.ne')).continuousWithinAt
      exact hc.intervalIntegrable
    exact (h1.add h2).const_mul (1 / M_D)
  have hint_D2 : IntervalIntegrable (fun x : ℝ => |t₁ + t₂| / (D x) ^ 2) volume a b := by
    have hc : ContinuousOn (fun x : ℝ => |t₁ + t₂| / (D x) ^ 2) (Set.uIcc a b) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have hcD : ContinuousAt D x := continuousAt_const.sub (continuousAt_id.const_mul (t₁ + t₂))
      exact (continuousAt_const.div (hcD.pow 2) (pow_ne_zero 2 (hD_ne x hx))).continuousWithinAt
    exact hc.intervalIntegrable
  have hIntR_le : ‖∫ x in a..b, R x‖ ≤
      4 / M_D + ∫ x in a..b, |t₁ + t₂| / (D x) ^ 2 := by
    calc
      ‖∫ x in a..b, R x‖ ≤ ∫ x in a..b, ‖R x‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, ((1 / M_D) * (x ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ)) +
            |t₁ + t₂| / (D x) ^ 2) :=
        intervalIntegral.integral_mono_on hab hR_int.norm (hint_pair.add hint_D2) hR_le
      _ = (1 / M_D) * (∫ x in a..b, (x ^ (-1 / 2 : ℝ) + (1 - x) ^ (-1 / 2 : ℝ))) +
          ∫ x in a..b, |t₁ + t₂| / (D x) ^ 2 := by
        rw [intervalIntegral.integral_add hint_pair hint_D2, intervalIntegral.integral_const_mul]
      _ ≤ (1 / M_D) * 4 + ∫ x in a..b, |t₁ + t₂| / (D x) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left (integral_inv_sqrt_pair_le_four ha hab hb) (by positivity)) le_rfl
      _ = 4 / M_D + ∫ x in a..b, |t₁ + t₂| / (D x) ^ 2 := by ring
  have hGb := hG_le b ⟨hab, le_rfl⟩
  have hGa := hG_le a ⟨le_rfl, hab⟩
  rw [hIntEq]
  calc
    ‖G b - G a - ∫ x in a..b, R x‖
        ≤ ‖G b - G a‖ + ‖∫ x in a..b, R x‖ := norm_sub_le _ _
    _ ≤ (‖G b‖ + ‖G a‖) + ‖∫ x in a..b, R x‖ := add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (1 / M_D + 1 / M_D) + (4 / M_D + ∫ x in a..b, |t₁ + t₂| / (D x) ^ 2) :=
        add_le_add (add_le_add hGb hGa) hIntR_le
    _ = 6 / M_D + ∫ x in a..b, |t₁ + t₂| / (D x) ^ 2 := by ring

/-- 辅助：`∫ x in a..b, (t₁ + t₂) / (t₁ - (t₁ + t₂) * x)^2 = (D b)⁻¹ - (D a)⁻¹`。 -/
private lemma integral_inv_D_sq {t₁ t₂ a b : ℝ} (hab : a ≤ b)
    (hD_ne : ∀ x ∈ Set.Icc a b, t₁ - (t₁ + t₂) * x ≠ 0) :
    (∫ x in a..b, (t₁ + t₂) / (t₁ - (t₁ + t₂) * x) ^ 2)
      = (t₁ - (t₁ + t₂) * b)⁻¹ - (t₁ - (t₁ + t₂) * a)⁻¹ := by
  let D : ℝ → ℝ := fun x => t₁ - (t₁ + t₂) * x
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y => (D y)⁻¹) ((t₁ + t₂) / (D x) ^ 2) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have hdD : HasDerivAt D (-(t₁ + t₂)) x := by
      have h := (hasDerivAt_const x t₁).sub ((hasDerivAt_id x).const_mul (t₁ + t₂))
      change HasDerivAt D _ x at h
      convert h using 1; ring
    have hinv := hdD.inv (hD_ne x hx)
    change HasDerivAt (fun y => (D y)⁻¹) _ x at hinv
    convert hinv using 1
    ring
  have hint : IntervalIntegrable (fun x : ℝ => (t₁ + t₂) / (D x) ^ 2) volume a b := by
    have hc : ContinuousOn (fun x : ℝ => (t₁ + t₂) / (D x) ^ 2) (Set.uIcc a b) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have hcD : ContinuousAt D x := continuousAt_const.sub (continuousAt_id.const_mul (t₁ + t₂))
      exact (continuousAt_const.div (hcD.pow 2) (pow_ne_zero 2 (hD_ne x hx))).continuousWithinAt
    exact hc.intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

/-- 当 `T ≥ 64` 且 `t₁ = z₁.im ∈ [T, 2T]` 时的 Beta 积分衰减界 `‖betaIntegral z₁ z₂‖ ≤ 64 / √T`。 -/
private lemma betaIntegral_decay_pos_im {z₁ z₂ : ℂ} {T : ℝ} (hT64 : 64 ≤ T)
    (h1l : 1 / 2 ≤ z₁.re) (h1u : z₁.re ≤ 1) (h2l : 1 / 2 ≤ z₂.re) (h2u : z₂.re ≤ 1)
    (ht1l : T ≤ z₁.im) (ht1u : z₁.im ≤ 2 * T)
    (ht2l : T ≤ |z₂.im|) (ht2u : |z₂.im| ≤ 2 * T) :
    ‖Complex.betaIntegral z₁ z₂‖ ≤ 64 / Real.sqrt T := by
  have hTpos : 0 < T := by linarith
  have hsqrtT_ge : 8 ≤ Real.sqrt T := by
    have h64 : (8 : ℝ) = Real.sqrt 64 := by norm_num
    rw [h64]
    exact Real.sqrt_le_sqrt hT64
  have hsqrtT_pos : 0 < Real.sqrt T := by linarith
  have hint_full : IntervalIntegrable (betaFn z₁ z₂) volume 0 1 :=
    Complex.betaIntegral_convergent (by linarith) (by linarith)
  have hsub_int : ∀ (u v : ℝ), 0 ≤ u → u ≤ v → v ≤ 1 →
      IntervalIntegrable (betaFn z₁ z₂) volume u v := by
    intro u v hu huv hv
    exact hint_full.mono_set (by
      rw [Set.uIcc_of_le huv, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      intro x hx; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  -- 端点截断 `δ = 1 / T^2`
  set δ : ℝ := 1 / T ^ 2
  have hδ0 : 0 < δ := by positivity
  have hδ_small : δ ≤ 1 / 4096 := by
    dsimp only [δ]
    have hT2 : (4096 : ℝ) ≤ T ^ 2 := by nlinarith
    exact one_div_le_one_div_of_le (by norm_num) hT2
  have hδ_half : δ ≤ 1 / 2 := by linarith
  have hsqrtδ : Real.sqrt δ = 1 / T := by
    dsimp only [δ]
    rw [Real.sqrt_div zero_le_one, Real.sqrt_one, Real.sqrt_sq hTpos.le]
  have htail_bound : 4 * Real.sqrt δ ≤ 4 / Real.sqrt T := by
    rw [hsqrtδ]
    have h1 : 1 / T ≤ 1 / Real.sqrt T := by
      apply one_div_le_one_div_of_le hsqrtT_pos
      nlinarith [Real.sq_sqrt hTpos.le]
    calc
      4 * (1 / T) ≤ 4 * (1 / Real.sqrt T) := by linarith
      _ = 4 / Real.sqrt T := by ring
  have hLtail : ‖∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x‖ ≤ 4 / Real.sqrt T :=
    (left_tail_bound h1l h2l hδ0 hδ_half).trans htail_bound
  have hRtail : ‖∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x‖ ≤ 4 / Real.sqrt T :=
    (right_tail_bound h1l h2l hδ0 hδ_half).trans htail_bound
  -- 按 `z₂.im` 的符号分情形
  rcases le_or_gt 0 z₂.im with ht2_nn | ht2_neg
  · -- 情形 B：同号 `T ≤ z₂.im ≤ 2T`，存在驻点 `c = t₁ / (t₁ + t₂) ∈ [1/3, 2/3]`
    have ht2_ge : T ≤ z₂.im := by rwa [abs_of_nonneg ht2_nn] at ht2l
    have ht2_le : z₂.im ≤ 2 * T := by rwa [abs_of_nonneg ht2_nn] at ht2u
    set St : ℝ := z₁.im + z₂.im
    have hSt_ge : 2 * T ≤ St := by dsimp only [St]; linarith
    have hSt_pos : 0 < St := by linarith
    set c : ℝ := z₁.im / St
    have hc_ge : 1 / 3 ≤ c := by
      dsimp only [c, St]
      rw [le_div_iff₀ hSt_pos]
      linarith
    have hc_le : c ≤ 2 / 3 := by
      dsimp only [c, St]
      rw [div_le_iff₀ hSt_pos]
      linarith
    set h : ℝ := 1 / Real.sqrt T
    have hh_pos : 0 < h := by positivity
    have hh_le : h ≤ 1 / 8 := by
      dsimp only [h]
      exact one_div_le_one_div_of_le (by norm_num) hsqrtT_ge
    set p : ℝ := c - h
    set q_pt : ℝ := c + h
    have hp_ge : 1 / 6 ≤ p := by dsimp only [p]; linarith
    have hq_le : q_pt ≤ 5 / 6 := by dsimp only [q_pt]; linarith
    have hδ_lt_p : δ ≤ p := by linarith
    have hp_le_q : p ≤ q_pt := by dsimp only [p, q_pt]; linarith
    have hq_le_1δ : q_pt ≤ 1 - δ := by linarith
    -- 将 `[0, 1]` 拆为 5 段
    have hsplit5 : Complex.betaIntegral z₁ z₂ =
        (∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x) +
        (∫ x in δ..p, betaFn z₁ z₂ x) +
        (∫ x in p..q_pt, betaFn z₁ z₂ x) +
        (∫ x in q_pt..(1 - δ), betaFn z₁ z₂ x) +
        (∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x) := by
      change (∫ x in (0 : ℝ)..1, betaFn z₁ z₂ x) = _
      have h12 := intervalIntegral.integral_add_adjacent_intervals
        (hsub_int 0 δ le_rfl hδ0.le (by linarith)) (hsub_int δ p hδ0.le hδ_lt_p (by linarith))
      have h123 := intervalIntegral.integral_add_adjacent_intervals
        (hsub_int 0 p le_rfl (by linarith) (by linarith)) (hsub_int p q_pt (by linarith) hp_le_q (by linarith))
      have h1234 := intervalIntegral.integral_add_adjacent_intervals
        (hsub_int 0 q_pt le_rfl (by linarith) (by linarith)) (hsub_int q_pt (1 - δ) (by linarith) hq_le_1δ (by linarith))
      have h12345 := intervalIntegral.integral_add_adjacent_intervals
        (hsub_int 0 (1 - δ) le_rfl (by linarith) (by linarith)) (hsub_int (1 - δ) 1 (by linarith) (by linarith) le_rfl)
      rw [← h12345, ← h1234, ← h123, ← h12]
    -- 中段 `[p, q_pt]` 界：`≤ 12 / √T`
    have hMid : ‖∫ x in p..q_pt, betaFn z₁ z₂ x‖ ≤ 12 / Real.sqrt T := by
      have hconst : ∀ x ∈ Set.uIoc p q_pt, ‖betaFn z₁ z₂ x‖ ≤ 6 := by
        intro x hx
        rw [Set.uIoc_of_le hp_le_q] at hx
        have hx_ge : (1 / 6 : ℝ) ≤ x := by linarith [hx.1]
        have h1x_ge : (1 / 6 : ℝ) ≤ 1 - x := by linarith [hx.2]
        have hx0 : 0 < x := by linarith
        have hx1 : x < 1 := by linarith
        have ha : x ^ (-1 / 2 : ℝ) ≤ (1 / 6 : ℝ) ^ (-1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hx_ge (by norm_num)
        have hb : (1 - x) ^ (-1 / 2 : ℝ) ≤ (1 / 6 : ℝ) ^ (-1 / 2 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) h1x_ge (by norm_num)
        have h6 : (1 / 6 : ℝ) ^ (-1 / 2 : ℝ) * (1 / 6 : ℝ) ^ (-1 / 2 : ℝ) = 6 := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 6)]
          norm_num
        calc
          ‖betaFn z₁ z₂ x‖ ≤ x ^ (-1 / 2 : ℝ) * (1 - x) ^ (-1 / 2 : ℝ) :=
            norm_betaFn_le h1l h2l hx0 hx1
          _ ≤ (1 / 6 : ℝ) ^ (-1 / 2 : ℝ) * (1 / 6 : ℝ) ^ (-1 / 2 : ℝ) :=
            mul_le_mul ha hb (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by norm_num) _)
          _ = 6 := h6
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const hconst
      have hlen : |q_pt - p| = 2 / Real.sqrt T := by
        have hqp : q_pt - p = 2 / Real.sqrt T := by dsimp only [p, q_pt, h]; ring
        rw [hqp, abs_of_pos (by positivity)]
      rw [hlen] at hle
      exact hle.trans_eq (by ring)
    -- 左段 `[δ, p]` 界：`≤ 4 / √T`
    have hLeftMid : ‖∫ x in δ..p, betaFn z₁ z₂ x‖ ≤ 4 / Real.sqrt T := by
      have hD_pos : ∀ x ∈ Set.Icc δ p, 2 * Real.sqrt T ≤ z₁.im - St * x := by
        intro x hx
        have hident : z₁.im - St * x = St * (c - x) := by
          dsimp only [c]; field_simp [hSt_pos.ne']
        have hcx : h ≤ c - x := by dsimp only [p] at hx; linarith [hx.2]
        have hSh : 2 * Real.sqrt T ≤ St * h := by
          dsimp only [h]
          rw [show (2 : ℝ) * Real.sqrt T = 2 * T * (1 / Real.sqrt T) by
                field_simp [hsqrtT_pos.ne']; rw [Real.sq_sqrt hTpos.le]]
          exact mul_le_mul_of_nonneg_right hSt_ge (by positivity)
        rw [hident]
        exact hSh.trans (mul_le_mul_of_nonneg_left hcx hSt_pos.le)
      have hD_abs : ∀ x ∈ Set.Icc δ p, 2 * Real.sqrt T ≤ |z₁.im - (z₁.im + z₂.im) * x| := by
        intro x hx
        have hge := hD_pos x hx
        rw [abs_of_nonneg (by linarith)]
        exact hge
      have hD_ne : ∀ x ∈ Set.Icc δ p, z₁.im - (z₁.im + z₂.im) * x ≠ 0 := fun x hx => by
        have := hD_pos x hx; linarith
      have hibp := betaFn_ibp_bound h1l h1u h2l h2u hδ0 hδ_lt_p (by linarith)
        (by positivity : 0 < 2 * Real.sqrt T) hD_abs
      have hrem : (∫ x in δ..p, |z₁.im + z₂.im| / (z₁.im - (z₁.im + z₂.im) * x) ^ 2)
          ≤ 1 / (2 * Real.sqrt T) := by
        rw [abs_of_pos hSt_pos, integral_inv_D_sq hδ_lt_p hD_ne]
        have hDp : 2 * Real.sqrt T ≤ z₁.im - (z₁.im + z₂.im) * p := hD_pos p ⟨hδ_lt_p, le_rfl⟩
        have hDδ : 0 < z₁.im - (z₁.im + z₂.im) * δ := by
          have := hD_pos δ ⟨le_rfl, hδ_lt_p⟩; linarith
        have h1 : (z₁.im - (z₁.im + z₂.im) * p)⁻¹ ≤ (2 * Real.sqrt T)⁻¹ :=
          inv_anti₀ (by positivity) hDp
        have h2 : 0 ≤ (z₁.im - (z₁.im + z₂.im) * δ)⁻¹ := inv_nonneg.mpr hDδ.le
        rw [one_div]
        linarith
      have h6 : 6 / (2 * Real.sqrt T) + 1 / (2 * Real.sqrt T) ≤ 4 / Real.sqrt T := by
        have hpos : 0 < Real.sqrt T := hsqrtT_pos
        rw [show 6 / (2 * Real.sqrt T) + 1 / (2 * Real.sqrt T) = 3.5 / Real.sqrt T by ring]
        exact div_le_div_of_nonneg_right (by norm_num) hpos.le
      linarith
    -- 右段 `[q_pt, 1 - δ]` 界：`≤ 4 / √T`
    have hRightMid : ‖∫ x in q_pt..(1 - δ), betaFn z₁ z₂ x‖ ≤ 4 / Real.sqrt T := by
      have hD_neg : ∀ x ∈ Set.Icc q_pt (1 - δ), z₁.im - St * x ≤ -(2 * Real.sqrt T) := by
        intro x hx
        have hident : z₁.im - St * x = -(St * (x - c)) := by
          dsimp only [c]; field_simp [hSt_pos.ne']; ring
        have hxc : h ≤ x - c := by dsimp only [q_pt] at hx; linarith [hx.1]
        have hSh : 2 * Real.sqrt T ≤ St * h := by
          dsimp only [h]
          rw [show (2 : ℝ) * Real.sqrt T = 2 * T * (1 / Real.sqrt T) by
                field_simp [hsqrtT_pos.ne']; rw [Real.sq_sqrt hTpos.le]]
          exact mul_le_mul_of_nonneg_right hSt_ge (by positivity)
        rw [hident]
        linarith [hSh.trans (mul_le_mul_of_nonneg_left hxc hSt_pos.le)]
      have hD_abs : ∀ x ∈ Set.Icc q_pt (1 - δ),
          2 * Real.sqrt T ≤ |z₁.im - (z₁.im + z₂.im) * x| := by
        intro x hx
        have hle := hD_neg x hx
        rw [abs_of_nonpos (by linarith)]
        linarith
      have hD_ne : ∀ x ∈ Set.Icc q_pt (1 - δ), z₁.im - (z₁.im + z₂.im) * x ≠ 0 := fun x hx => by
        have := hD_neg x hx; linarith
      have hibp := betaFn_ibp_bound h1l h1u h2l h2u (by linarith) hq_le_1δ (by linarith)
        (by positivity : 0 < 2 * Real.sqrt T) hD_abs
      have hrem : (∫ x in q_pt..(1 - δ), |z₁.im + z₂.im| / (z₁.im - (z₁.im + z₂.im) * x) ^ 2)
          ≤ 1 / (2 * Real.sqrt T) := by
        rw [abs_of_pos hSt_pos, integral_inv_D_sq hq_le_1δ hD_ne]
        have hDq : z₁.im - (z₁.im + z₂.im) * q_pt ≤ -(2 * Real.sqrt T) :=
          hD_neg q_pt ⟨le_rfl, hq_le_1δ⟩
        have hD1δ : z₁.im - (z₁.im + z₂.im) * (1 - δ) < 0 := by
          have := hD_neg (1 - δ) ⟨hq_le_1δ, le_rfl⟩; linarith
        have h1 : (z₁.im - (z₁.im + z₂.im) * (1 - δ))⁻¹ ≤ 0 := inv_nonpos.mpr hD1δ.le
        have h2 : -((z₁.im - (z₁.im + z₂.im) * q_pt)⁻¹) ≤ (2 * Real.sqrt T)⁻¹ := by
          rw [← inv_neg]
          exact inv_anti₀ (by positivity) (by linarith)
        rw [one_div]
        linarith
      have h6 : 6 / (2 * Real.sqrt T) + 1 / (2 * Real.sqrt T) ≤ 4 / Real.sqrt T := by
        rw [show 6 / (2 * Real.sqrt T) + 1 / (2 * Real.sqrt T) = 3.5 / Real.sqrt T by ring]
        exact div_le_div_of_nonneg_right (by norm_num) hsqrtT_pos.le
      linarith
    -- 汇总 5 段：`4 + 4 + 12 + 4 + 4 = 28 ≤ 64`
    rw [hsplit5]
    have htri :
        ‖(∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x) + (∫ x in δ..p, betaFn z₁ z₂ x) +
          (∫ x in p..q_pt, betaFn z₁ z₂ x) + (∫ x in q_pt..(1 - δ), betaFn z₁ z₂ x) +
          (∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x)‖
        ≤ ‖∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x‖ + ‖∫ x in δ..p, betaFn z₁ z₂ x‖ +
          ‖∫ x in p..q_pt, betaFn z₁ z₂ x‖ + ‖∫ x in q_pt..(1 - δ), betaFn z₁ z₂ x‖ +
          ‖∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x‖ := by
      calc
        _ ≤ ‖(∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x) + (∫ x in δ..p, betaFn z₁ z₂ x) +
              (∫ x in p..q_pt, betaFn z₁ z₂ x) + (∫ x in q_pt..(1 - δ), betaFn z₁ z₂ x)‖ +
            ‖∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x‖ := norm_add_le _ _
        _ ≤ ‖(∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x) + (∫ x in δ..p, betaFn z₁ z₂ x) +
              (∫ x in p..q_pt, betaFn z₁ z₂ x)‖ + ‖∫ x in q_pt..(1 - δ), betaFn z₁ z₂ x‖ +
            ‖∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ ‖(∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x) + (∫ x in δ..p, betaFn z₁ z₂ x)‖ +
            ‖∫ x in p..q_pt, betaFn z₁ z₂ x‖ + ‖∫ x in q_pt..(1 - δ), betaFn z₁ z₂ x‖ +
            ‖∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x‖ := by
            gcongr; exact norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    have hsum28 : 4 / Real.sqrt T + 4 / Real.sqrt T + 12 / Real.sqrt T +
        4 / Real.sqrt T + 4 / Real.sqrt T ≤ 64 / Real.sqrt T := by
      have hpos := hsqrtT_pos
      rw [show 4 / Real.sqrt T + 4 / Real.sqrt T + 12 / Real.sqrt T +
            4 / Real.sqrt T + 4 / Real.sqrt T = 28 / Real.sqrt T by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hpos.le
    exact htri.trans ((by linarith : _ ≤ 4 / Real.sqrt T + 4 / Real.sqrt T +
      12 / Real.sqrt T + 4 / Real.sqrt T + 4 / Real.sqrt T).trans hsum28)
  · -- 情形 A：异号 `-2T ≤ z₂.im ≤ -T`，整个 `[δ, 1 - δ]` 无驻点
    have ht2_le : z₂.im ≤ -T := by rw [abs_of_neg ht2_neg] at ht2l; linarith
    have ht2_ge : -2 * T ≤ z₂.im := by rw [abs_of_neg ht2_neg] at ht2u; linarith
    have hδ_le_1δ : δ ≤ 1 - δ := by linarith
    have hsplit3 : Complex.betaIntegral z₁ z₂ =
        (∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x) +
        (∫ x in δ..(1 - δ), betaFn z₁ z₂ x) +
        (∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x) := by
      change (∫ x in (0 : ℝ)..1, betaFn z₁ z₂ x) = _
      have h12 := intervalIntegral.integral_add_adjacent_intervals
        (hsub_int 0 δ le_rfl hδ0.le (by linarith)) (hsub_int δ (1 - δ) hδ0.le hδ_le_1δ (by linarith))
      have h123 := intervalIntegral.integral_add_adjacent_intervals
        (hsub_int 0 (1 - δ) le_rfl (by linarith) (by linarith))
        (hsub_int (1 - δ) 1 (by linarith) (by linarith) le_rfl)
      rw [← h123, ← h12]
    have hD_ge : ∀ x ∈ Set.Icc δ (1 - δ), T ≤ |z₁.im - (z₁.im + z₂.im) * x| := by
      intro x hx
      have hval : T ≤ z₁.im - (z₁.im + z₂.im) * x := by
        have hx0 : 0 ≤ x := by linarith [hx.1]
        have h1x : 0 ≤ 1 - x := by linarith [hx.2]
        have hrewrite : z₁.im - (z₁.im + z₂.im) * x = z₁.im * (1 - x) + (-z₂.im) * x := by ring
        rw [hrewrite]
        nlinarith
      rw [abs_of_nonneg (by linarith)]
      exact hval
    have hibp := betaFn_ibp_bound h1l h1u h2l h2u hδ0 hδ_le_1δ (by linarith) hTpos hD_ge
    have hrem_le : (∫ x in δ..(1 - δ), |z₁.im + z₂.im| / (z₁.im - (z₁.im + z₂.im) * x) ^ 2)
        ≤ 1 / T := by
      have habs_st : |z₁.im + z₂.im| ≤ T := abs_le.mpr ⟨by linarith, by linarith⟩
      have hpt : ∀ x ∈ Set.Icc δ (1 - δ),
          |z₁.im + z₂.im| / (z₁.im - (z₁.im + z₂.im) * x) ^ 2 ≤ 1 / T := by
        intro x hx
        have hDsq : T ^ 2 ≤ (z₁.im - (z₁.im + z₂.im) * x) ^ 2 := by
          have h1 := hD_ge x hx
          have h2 : |z₁.im - (z₁.im + z₂.im) * x| ^ 2 = (z₁.im - (z₁.im + z₂.im) * x) ^ 2 :=
            sq_abs _
          nlinarith
        calc
          |z₁.im + z₂.im| / (z₁.im - (z₁.im + z₂.im) * x) ^ 2
              ≤ T / (z₁.im - (z₁.im + z₂.im) * x) ^ 2 :=
            div_le_div_of_nonneg_right habs_st (sq_nonneg _)
          _ ≤ T / T ^ 2 := div_le_div_of_nonneg_left hTpos.le (pow_pos hTpos 2) hDsq
          _ = 1 / T := by field_simp [hTpos.ne']
      have hint_lhs : IntervalIntegrable
          (fun x : ℝ => |z₁.im + z₂.im| / (z₁.im - (z₁.im + z₂.im) * x) ^ 2) volume δ (1 - δ) := by
        have hc : ContinuousOn
            (fun x : ℝ => |z₁.im + z₂.im| / (z₁.im - (z₁.im + z₂.im) * x) ^ 2)
            (Set.uIcc δ (1 - δ)) := by
          intro x hx
          rw [Set.uIcc_of_le hδ_le_1δ] at hx
          have hne : z₁.im - (z₁.im + z₂.im) * x ≠ 0 := by
            have := hD_ge x hx; intro h0; rw [h0, abs_zero] at this; linarith
          have hcD : ContinuousAt (fun y : ℝ => z₁.im - (z₁.im + z₂.im) * y) x :=
            continuousAt_const.sub (continuousAt_id.const_mul _)
          exact (continuousAt_const.div (hcD.pow 2) (pow_ne_zero 2 hne)).continuousWithinAt
        exact hc.intervalIntegrable
      have hmono := intervalIntegral.integral_mono_on hδ_le_1δ hint_lhs
        intervalIntegrable_const hpt
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      calc
        (∫ x in δ..(1 - δ), |z₁.im + z₂.im| / (z₁.im - (z₁.im + z₂.im) * x) ^ 2)
            ≤ (1 - δ - δ) * (1 / T) := hmono
        _ ≤ 1 * (1 / T) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 1 / T := one_mul _
    have hMidA : ‖∫ x in δ..(1 - δ), betaFn z₁ z₂ x‖ ≤ 7 / Real.sqrt T := by
      have h1T : 1 / T ≤ 1 / Real.sqrt T := by
        apply one_div_le_one_div_of_le hsqrtT_pos
        nlinarith [Real.sq_sqrt hTpos.le]
      calc
        ‖∫ x in δ..(1 - δ), betaFn z₁ z₂ x‖ ≤ 6 / T + 1 / T := by linarith
        _ = 7 * (1 / T) := by ring
        _ ≤ 7 * (1 / Real.sqrt T) := by linarith
        _ = 7 / Real.sqrt T := by ring
    rw [hsplit3]
    have htri :
        ‖(∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x) + (∫ x in δ..(1 - δ), betaFn z₁ z₂ x) +
          (∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x)‖
        ≤ ‖∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x‖ + ‖∫ x in δ..(1 - δ), betaFn z₁ z₂ x‖ +
          ‖∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x‖ := by
      calc
        _ ≤ ‖(∫ x in (0 : ℝ)..δ, betaFn z₁ z₂ x) + (∫ x in δ..(1 - δ), betaFn z₁ z₂ x)‖ +
            ‖∫ x in (1 - δ)..(1 : ℝ), betaFn z₁ z₂ x‖ := norm_add_le _ _
        _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
    have hsum15 : 4 / Real.sqrt T + 7 / Real.sqrt T + 4 / Real.sqrt T ≤ 64 / Real.sqrt T := by
      rw [show 4 / Real.sqrt T + 7 / Real.sqrt T + 4 / Real.sqrt T = 15 / Real.sqrt T by ring]
      exact div_le_div_of_nonneg_right (by norm_num) hsqrtT_pos.le
    exact htri.trans ((by linarith : _ ≤ 4 / Real.sqrt T + 7 / Real.sqrt T +
      4 / Real.sqrt T).trans hsum15)

/-- 统一的 Gamma/Beta 核二进高度衰减界：`‖Γ(z₁)Γ(z₂)/Γ(z₁+z₂)‖ ≤ 64 / √T`。 -/
private lemma gamma_ratio_decay {z₁ z₂ : ℂ} {T : ℝ} (hT : 1 ≤ T)
    (h1l : 1 / 2 ≤ z₁.re) (h1u : z₁.re ≤ 1) (h2l : 1 / 2 ≤ z₂.re) (h2u : z₂.re ≤ 1)
    (ht1l : T ≤ |z₁.im|) (ht1u : |z₁.im| ≤ 2 * T)
    (ht2l : T ≤ |z₂.im|) (ht2u : |z₂.im| ≤ 2 * T) :
    ‖Complex.Gamma z₁ * Complex.Gamma z₂ / Complex.Gamma (z₁ + z₂)‖ ≤ 64 / Real.sqrt T := by
  have hz1 : 0 < z₁.re := by linarith
  have hz2 : 0 < z₂.re := by linarith
  have hz12 : 0 < (z₁ + z₂).re := by simp; linarith
  have hGne : Complex.Gamma (z₁ + z₂) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz12
  have hEq : Complex.Gamma z₁ * Complex.Gamma z₂ / Complex.Gamma (z₁ + z₂) =
      Complex.betaIntegral z₁ z₂ := by
    rw [Complex.Gamma_mul_Gamma_eq_betaIntegral hz1 hz2, mul_div_cancel_left₀ _ hGne]
  rw [hEq]
  by_cases hT64 : 64 ≤ T
  · rcases le_or_gt 0 z₁.im with hpos | hneg
    · exact betaIntegral_decay_pos_im hT64 h1l h1u h2l h2u
        (by rwa [abs_of_nonneg hpos] at ht1l)
        (by rwa [abs_of_nonneg hpos] at ht1u) ht2l ht2u
    · rw [← norm_betaIntegral_conj hz1 hz2]
      exact betaIntegral_decay_pos_im hT64
        (by simpa using h1l) (by simpa using h1u)
        (by simpa using h2l) (by simpa using h2u)
        (by rw [Complex.conj_im]; rw [abs_of_neg hneg] at ht1l; linarith)
        (by rw [Complex.conj_im]; rw [abs_of_neg hneg] at ht1u; linarith)
        (by simpa using ht2l) (by simpa using ht2u)
  · push Not at hT64
    have hsqrt_le : Real.sqrt T ≤ 8 := by
      have h64 : Real.sqrt 64 = (8 : ℝ) := by norm_num
      rw [← h64]
      exact Real.sqrt_le_sqrt hT64.le
    have hsqrt_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
    calc
      ‖Complex.betaIntegral z₁ z₂‖ ≤ 8 := betaIntegral_norm_le_eight h1l h2l
      _ ≤ 64 / Real.sqrt T := by
        rw [le_div_iff₀ hsqrt_pos]
        linarith

-- ============================================================================
-- 第三部分：二进零点块按本原特征归并与主定理组装
-- ============================================================================

/-- 辅助常数界：`64 * 3^(1/3) ≤ 128`。 -/
private lemma const_64_cbrt3_le_128 : 64 * (3 : ℝ) ^ (1 / 3 : ℝ) ≤ 128 := by
  have hcbrt : (3 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
    have h2 : (2 : ℝ) = (8 : ℝ) ^ (1 / 3 : ℝ) := by
      have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
      rw [h8, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h2]
    exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  linarith

/-- 二进零点块主估计（定理第二部分，取 `C = 128`）。 -/
private lemma dyadic_zero_block_bound (m : ℕ) (T : ℝ) (hm : 0 < m) (he : Even m) (hT : 1 ≤ T)
    (n : ℕ) (χ : Fin n → CharPack) (z u v : Fin n → ℂ)
    (hχz : ∀ i, IsPrimPack (χ i) ∧
      (if h : (χ i).1 ≠ 0 then
        letI : NeZero (χ i).1 := ⟨h⟩
        DirichletCharacter.LFunction (χ i).2 (z i) = 0
      else False) ∧
      1 / 2 ≤ (z i).re ∧ (z i).re ≤ 1 ∧ T ≤ |(z i).im| ∧ |(z i).im| ≤ 2 * T) :
    let F := Finset.univ.image χ
    let W := fun (w : Fin n → ℂ) (b : CharPack) =>
      ∑ i ∈ Finset.univ.filter (fun i => χ i = b), ‖w i‖ * (m : ℝ) ^ ((z i).re - 1)
    let K := fun i j : Fin n => Complex.Gamma (z i) * Complex.Gamma (z j) /
      Complex.Gamma (z i + z j) * (m : ℂ) ^ (z i + z j - 1)
    ‖∑ i : Fin n, ∑ j : Fin n, u i * v j * S (χ i).2 (χ j).2 m * K i j‖
      ≤ 128 * (m : ℝ) * ‖O m‖ / Real.sqrt T * norm65 F (W u) * norm65 F (W v) := by
  intro F W K
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
  -- 核函数 `K i j` 的逐点界
  have hK_bound : ∀ i j : Fin n,
      ‖K i j‖ ≤ (64 * (m : ℝ) / Real.sqrt T) *
        ((m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1)) := by
    intro i j
    have hi := hχz i
    have hj := hχz j
    have hgamma := gamma_ratio_decay hT hi.2.2.1 hi.2.2.2.1 hj.2.2.1 hj.2.2.2.1
      hi.2.2.2.2.1 hi.2.2.2.2.2 hj.2.2.2.2.1 hj.2.2.2.2.2
    have hmcpow : ‖(m : ℂ) ^ (z i + z j - 1)‖ =
        (m : ℝ) * (m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1) := by
      have hcast : (m : ℂ) = ((m : ℝ) : ℂ) := by norm_cast
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hm_pos]
      have hexp : (z i + z j - 1).re = 1 + ((z i).re - 1) + ((z j).re - 1) := by
        simp; ring
      rw [hexp, Real.rpow_add hm_pos, Real.rpow_add hm_pos, Real.rpow_one]
    dsimp only [K]
    rw [norm_mul, hmcpow]
    calc
      ‖Complex.Gamma (z i) * Complex.Gamma (z j) / Complex.Gamma (z i + z j)‖ *
          ((m : ℝ) * (m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1))
          ≤ (64 / Real.sqrt T) *
            ((m : ℝ) * (m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1)) :=
        mul_le_mul_of_nonneg_right hgamma (by positivity)
      _ = (64 * (m : ℝ) / Real.sqrt T) *
          ((m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1)) := by ring
  -- 展开三角不等式并提取公因子 `64 * m / √T`
  let aW : Fin n → ℝ := fun i => ‖u i‖ * (m : ℝ) ^ ((z i).re - 1)
  let bW : Fin n → ℝ := fun j => ‖v j‖ * (m : ℝ) ^ ((z j).re - 1)
  have htri :
      ‖∑ i : Fin n, ∑ j : Fin n, u i * v j * S (χ i).2 (χ j).2 m * K i j‖
        ≤ (64 * (m : ℝ) / Real.sqrt T) *
          ∑ i : Fin n, ∑ j : Fin n, aW i * ‖S (χ i).2 (χ j).2 m‖ * bW j := by
    calc
      ‖∑ i : Fin n, ∑ j : Fin n, u i * v j * S (χ i).2 (χ j).2 m * K i j‖
          ≤ ∑ i : Fin n, ‖∑ j : Fin n, u i * v j * S (χ i).2 (χ j).2 m * K i j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖u i * v j * S (χ i).2 (χ j).2 m * K i j‖ :=
        Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ∑ j : Fin n,
          (64 * (m : ℝ) / Real.sqrt T) * (aW i * ‖S (χ i).2 (χ j).2 m‖ * bW j) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        simp only [norm_mul]
        calc
          ‖u i‖ * ‖v j‖ * ‖S (χ i).2 (χ j).2 m‖ * ‖K i j‖
              ≤ ‖u i‖ * ‖v j‖ * ‖S (χ i).2 (χ j).2 m‖ *
                ((64 * (m : ℝ) / Real.sqrt T) *
                  ((m : ℝ) ^ ((z i).re - 1) * (m : ℝ) ^ ((z j).re - 1))) :=
            mul_le_mul_of_nonneg_left (hK_bound i j) (by positivity)
          _ = (64 * (m : ℝ) / Real.sqrt T) * (aW i * ‖S (χ i).2 (χ j).2 m‖ * bW j) := by
            dsimp only [aW, bW]; ring
      _ = (64 * (m : ℝ) / Real.sqrt T) *
          ∑ i : Fin n, ∑ j : Fin n, aW i * ‖S (χ i).2 (χ j).2 m‖ * bW j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
  -- 按本原特征纤维归并双重和
  have hfiber :
      (∑ i : Fin n, ∑ j : Fin n, aW i * ‖S (χ i).2 (χ j).2 m‖ * bW j)
        = ∑ a ∈ F, ∑ b ∈ F, |W u a| * ‖S a.2 b.2 m‖ * |W v b| := by
    have hW_nn : ∀ (w : Fin n → ℂ) (b : CharPack), 0 ≤ W w b := fun w b =>
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hm_pos.le _)
    have houter :
        (∑ i : Fin n, ∑ j : Fin n, aW i * ‖S (χ i).2 (χ j).2 m‖ * bW j)
          = ∑ a ∈ F, ∑ i ∈ Finset.univ.filter (fun i => χ i = a),
              ∑ j : Fin n, aW i * ‖S (χ i).2 (χ j).2 m‖ * bW j := by
      exact (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := F) (g := χ)
        (fun i hi => Finset.mem_image_of_mem χ hi) _).symm
    rw [houter]
    apply Finset.sum_congr rfl
    intro a _
    have hinner_a :
        (∑ i ∈ Finset.univ.filter (fun i => χ i = a),
            ∑ j : Fin n, aW i * ‖S (χ i).2 (χ j).2 m‖ * bW j)
          = ∑ i ∈ Finset.univ.filter (fun i => χ i = a),
              ∑ b ∈ F, ∑ j ∈ Finset.univ.filter (fun j => χ j = b),
                aW i * ‖S a.2 b.2 m‖ * bW j := by
      apply Finset.sum_congr rfl
      intro i hi
      have hia : χ i = a := (Finset.mem_filter.mp hi).2
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := F) (g := χ)
        (fun j hj => Finset.mem_image_of_mem χ hj)]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro j hj
      have hjb : χ j = b := (Finset.mem_filter.mp hj).2
      rw [hia, hjb]
    rw [hinner_a, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [abs_of_nonneg (hW_nn u a), abs_of_nonneg (hW_nn v b)]
    dsimp only [W, aW, bW]
    calc
      (∑ i ∈ Finset.univ.filter (fun i => χ i = a),
          ∑ j ∈ Finset.univ.filter (fun j => χ j = b),
            (‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖S a.2 b.2 m‖ *
              (‖v j‖ * (m : ℝ) ^ ((z j).re - 1)))
          = ∑ i ∈ Finset.univ.filter (fun i => χ i = a),
              ((‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖S a.2 b.2 m‖) *
                (∑ j ∈ Finset.univ.filter (fun j => χ j = b),
                  ‖v j‖ * (m : ℝ) ^ ((z j).re - 1)) := by
            apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
      _ = (∑ i ∈ Finset.univ.filter (fun i => χ i = a),
              ‖u i‖ * (m : ℝ) ^ ((z i).re - 1)) * ‖S a.2 b.2 m‖ *
            (∑ j ∈ Finset.univ.filter (fun j => χ j = b),
              ‖v j‖ * (m : ℝ) ^ ((z j).re - 1)) := by
            rw [← Finset.sum_mul, ← Finset.sum_mul]
  -- 套用第一部分的双线性 `ℓ^(6/5)` 界
  have hF_prim : ∀ b ∈ F, IsPrimPack b := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨i, _, rfl⟩
    exact (hχz i).1
  have hbilin := bilinear_bound m hm he F hF_prim (W u) (W v)
  have hN_nn : ∀ w, 0 ≤ norm65 F w := fun w =>
    Real.rpow_nonneg (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (abs_nonneg _) _) _
  calc
    ‖∑ i : Fin n, ∑ j : Fin n, u i * v j * S (χ i).2 (χ j).2 m * K i j‖
        ≤ (64 * (m : ℝ) / Real.sqrt T) *
          (∑ a ∈ F, ∑ b ∈ F, |W u a| * ‖S a.2 b.2 m‖ * |W v b|) := by
      rw [← hfiber]; exact htri
    _ ≤ (64 * (m : ℝ) / Real.sqrt T) *
          ((3 : ℝ) ^ (1 / 3 : ℝ) * ‖O m‖ * norm65 F (W u) * norm65 F (W v)) :=
      mul_le_mul_of_nonneg_left hbilin (by positivity)
    _ = (64 * (3 : ℝ) ^ (1 / 3 : ℝ)) *
          ((m : ℝ) * ‖O m‖ / Real.sqrt T * norm65 F (W u) * norm65 F (W v)) := by ring
    _ ≤ 128 * ((m : ℝ) * ‖O m‖ / Real.sqrt T * norm65 F (W u) * norm65 F (W v)) :=
      mul_le_mul_of_nonneg_right const_64_cbrt3_le_128
        (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hm_pos.le (norm_nonneg _)) hsqrtT_pos.le)
          (hN_nn (W u))) (hN_nn (W v)))
    _ = 128 * (m : ℝ) * ‖O m‖ / Real.sqrt T * norm65 F (W u) * norm65 F (W v) := by ring

end PartnerDyadicZeroBlockProof

/-- 冻结主定理：`L-goldbach-partner-dyadic-zero-block`。 -/
theorem Conjectures.Goldbach.PartnerDyadicZeroBlock :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let primitive := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
  let zeroAt := fun (b : B) (z : ℂ) => if h : b.1 ≠ 0 then
    letI : NeZero b.1 := ⟨h⟩
    DirichletCharacter.LFunction b.2 z = 0
    else False
  let N := fun (F : Finset B) (w : B → ℝ) => (∑ b ∈ F, |w b| ^ (6/5 : ℝ)) ^ (5/6 : ℝ)
  exact
    (∀ m : ℕ, 0 < m → Even m → ∀ F : Finset B, (∀ b ∈ F, primitive b) →
      ∀ u v : B → ℝ, (∑ a ∈ F, ∑ b ∈ F, |u a| * ‖S a.2 b.2 m‖ * |v b|)
        ≤ (3 : ℝ)^(1/3 : ℝ) * ‖O m‖ * N F u * N F v) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (T : ℝ), 0 < m → Even m → 1 ≤ T →
      ∀ (n : ℕ) (χ : Fin n → B) (z u v : Fin n → ℂ),
      (∀ i, primitive (χ i) ∧ zeroAt (χ i) (z i) ∧
        1/2 ≤ (z i).re ∧ (z i).re ≤ 1 ∧ T ≤ |(z i).im| ∧ |(z i).im| ≤ 2*T) →
      let F := Finset.univ.image χ
      let W := fun (w : Fin n → ℂ) (b : B) =>
        ∑ i ∈ Finset.univ.filter (fun i => χ i = b), ‖w i‖ * (m : ℝ)^((z i).re-1)
      let K := fun i j : Fin n => Complex.Gamma (z i) * Complex.Gamma (z j) /
        Complex.Gamma (z i + z j) * (m : ℂ)^(z i + z j - 1)
      ‖∑ i : Fin n, ∑ j : Fin n, u i * v j * S (χ i).2 (χ j).2 m * K i j‖
        ≤ C * (m : ℝ) * ‖O m‖ / Real.sqrt T * N F (W u) * N F (W v) := by
  classical
  dsimp only
  refine ⟨?_, 128, by norm_num, ?_⟩
  · intro m hm he F hF u v
    exact PartnerDyadicZeroBlockProof.bilinear_bound m hm he F hF u v
  · intro m T hm he hT n χ z u v hχz
    exact PartnerDyadicZeroBlockProof.dyadic_zero_block_bound m T hm he hT n χ z u v hχz
