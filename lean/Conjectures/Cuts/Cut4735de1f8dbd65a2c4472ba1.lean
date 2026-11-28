import Mathlib

/-!
# 拆题：`L-goldbach-romanov-short-window-density` 按窗长两段

父题要求：在每个长度 $H\ge\sqrt X$ 的窗口里，至少 13% 的整数是"奇数且至少有一个
$n-2^e$ 为素数"的形式（分母为全部整数）。

拆法按窗口与前段的相对长度分成两段，两段的矩估计形状不同：

* `h₁` 短窗段：$2H\le X$，窗口不超过起点的一半，可对每个 $H$ 用一次固定的筛法误差；
* `h₂` 长窗段：$X<2H$，窗口超过起点的一半，反射的配对会把窗口两端混在一起，需要另做。

两段合起来覆盖全部情形（$\mathbb N$ 上 $2H\le X$ 与 $X<2H$ 二分），故前提足够推出父题。
-/

-- child 1 zh: 短窗段：2H ≤ X 时，窗口里至少 13% 的整数是"奇数且至少一个 n−2^e 为素数"。
-- child 2 zh: 长窗段：X < 2H 时，同一密度下界成立。

theorem Conjectures.Cuts.Cut4735de1f8dbd65a2c4472ba1
    (h₁ : (by
      classical
      exact let R := fun n : ℕ => ((Finset.Icc 1 (Nat.log 2 n)).filter (fun e => Nat.Prime (n-2^e))).card; ∃ T : ℕ, ∀ X H : ℕ, T ≤ X → X ≤ H^2 → H ≤ X → 2*H ≤ X → 13*H ≤ 100*((Finset.Ico X (X+H)).filter (fun n => Odd n ∧ 0 < R n)).card))
    (h₂ : (by
      classical
      exact let R := fun n : ℕ => ((Finset.Icc 1 (Nat.log 2 n)).filter (fun e => Nat.Prime (n-2^e))).card; ∃ T : ℕ, ∀ X H : ℕ, T ≤ X → X ≤ H^2 → H ≤ X → X < 2*H → 13*H ≤ 100*((Finset.Ico X (X+H)).filter (fun n => Odd n ∧ 0 < R n)).card))
    : (by
      classical
      exact let R := fun n : ℕ => ((Finset.Icc 1 (Nat.log 2 n)).filter (fun e => Nat.Prime (n-2^e))).card; ∃ T : ℕ, ∀ X H : ℕ, T ≤ X → X ≤ H^2 → H ≤ X → 13*H ≤ 100*((Finset.Ico X (X+H)).filter (fun n => Odd n ∧ 0 < R n)).card) := by
  obtain ⟨T₁, hT₁⟩ := h₁
  obtain ⟨T₂, hT₂⟩ := h₂
  refine ⟨max T₁ T₂, ?_⟩
  intro X H hX hXH hHX
  have hX₁ : T₁ ≤ X := le_trans (le_max_left _ _) hX
  have hX₂ : T₂ ≤ X := le_trans (le_max_right _ _) hX
  by_cases h : 2 * H ≤ X
  · exact hT₁ X H hX₁ hXH hHX h
  · have h' : X < 2 * H := by omega
    exact hT₂ X H hX₂ hXH hHX h'
