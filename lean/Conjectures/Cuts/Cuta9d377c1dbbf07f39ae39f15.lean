import Mathlib

/-- Decomposition of L-square-packing-seventeen-lower-4661.
child 1 zh: 外部最优性结果的平台原生理性形式：任何 17 个可自由旋转单位正方形的装填，其外框边长至少 4.67553。
child 1 en: Rational form of the published n=17 optimality result: any packing of seventeen freely rotatable unit squares needs container side at least 4.67553.
child 2 zh: 基本有理数比较 4661/1000 < 467553/100000。
child 2 en: The elementary rational comparison 4661/1000 < 467553/100000.
-/

theorem Conjectures.Cuts.Cuta9d377c1dbbf07f39ae39f15
    (h₁ : ∀ (L : ℝ),
      (∃ x y a b : Fin 17 → ℝ,
        (∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2*x i ∧ |a i| + |b i| ≤ 2*(L-x i) ∧
          |a i| + |b i| ≤ 2*y i ∧ |a i| + |b i| ≤ 2*(L-y i)) ∧
        (∀ i j, i ≠ j → ∀ X Y : ℝ,
          (|a i*(X-x i)+b i*(Y-y i)| < 1/2 ∧ |(-b i)*(X-x i)+a i*(Y-y i)| < 1/2) →
          ¬ (|a j*(X-x j)+b j*(Y-y j)| < 1/2 ∧ |(-b j)*(X-x j)+a j*(Y-y j)| < 1/2)))
      → (467553/100000 : ℝ) ≤ L)
    (h₂ : (4661/1000 : ℝ) < 467553/100000)
    :
(let inside := fun (x y a b X Y : ℝ) => |a*(X-x)+b*(Y-y)| < 1/2 ∧ |(-b)*(X-x)+a*(Y-y)| < 1/2; let fits := fun (n : ℕ) (s : ℝ) => 0 ≤ s ∧ ∃ x y a b : Fin n → ℝ, (∀ i, a i ^ 2 + b i ^ 2 = 1 ∧ |a i| + |b i| ≤ 2*x i ∧ |a i| + |b i| ≤ 2*(s-x i) ∧ |a i| + |b i| ≤ 2*y i ∧ |a i| + |b i| ≤ 2*(s-y i)) ∧ (∀ i j, i ≠ j → ∀ X Y : ℝ, inside (x i) (y i) (a i) (b i) X Y → ¬ inside (x j) (y j) (a j) (b j) X Y); ¬ fits 17 (4661/1000)) := by
  classical
  dsimp only
  intro hf
  obtain ⟨-, hpack⟩ := hf
  have hlow : (467553/100000 : ℝ) ≤ (4661/1000 : ℝ) := h₁ _ hpack
  exact absurd h₂ (not_lt.mpr hlow)
