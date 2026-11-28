import Mathlib

set_option maxHeartbeats 2000000

/-!
# Cut of `L-goldbach-dyadic-cell-reflected-cancellation`

方法继承自仓库里 `research/reference-proofs/` 的几份自足证明：**先把带符号的双和改写成恒等式**，
再判断剩下的到底是什么量。这里内层双和满足

  ∑_{s<H} ∑_{t<H} (a_s − a_t)(b_s − b_t) = 2H · ∑_s a_s b_s − 2 · (∑_s a_s)(∑_t b_t),

所以"反射块内差分的带符号单侧界"整体上是一个**协方差下界**：

  ∑_j (对角质量_j − 两侧质量_j / H) ≥ −n/64,

其中 对角质量_j = ∑_s a_j s · b_j s，两侧质量_j = (∑_s a_j s)(∑_t b_j t)。
于是把困难整体交给两条**正向**计数：一条下界（对角），一条上界（两侧之积）。
两者都比原来的带符号抵消弱：符号问题已被恒等式吃掉，剩下的是
"有多少反射对同时落在素数上" 与 "两侧的素数权总量有多大" 两个计数。
-/

namespace CutDyadic

/-- 双和恒等式：块内差分的乘积和 = 2H·对角质量 − 2·两侧质量之积。 -/
private lemma pair_id (H : ℕ) (a b : ℕ → ℝ) :
    (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a s - a t) * (b s - b t))
      = 2 * (H : ℝ) * (∑ s ∈ Finset.range H, a s * b s)
        - 2 * ((∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t)) := by
  have key : ∀ s t : ℕ, (a s - a t) * (b s - b t)
      = (a s * b s + a t * b t) - (a s * b t + a t * b s) := by
    intro s t
    ring
  have hA : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a s * b s)
      = (H : ℝ) * (∑ s ∈ Finset.range H, a s * b s) := by
    rw [Finset.sum_comm, Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have hB : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a t * b t)
      = (H : ℝ) * (∑ s ∈ Finset.range H, a s * b s) := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  have hC : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a s * b t)
      = (∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t) := by
    rw [Finset.sum_mul_sum]
  have hD : (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, a t * b s)
      = (∑ s ∈ Finset.range H, a s) * (∑ t ∈ Finset.range H, b t) := by
    rw [Finset.sum_comm, Finset.sum_mul_sum]
  simp only [key]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hA, hB, hC, hD]
  ring

/-- 归约引理：两条正向计数推出带符号单侧界。与素数无关，纯有限和代数。 -/
private lemma main_cut (n H B : ℕ) (a b : ℕ → ℕ → ℝ) (hH : (0 : ℝ) < (H : ℝ))
    (h₁ : (n : ℝ) / 8 ≤ ∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H, a j s * b j s)
    (h₂ : (∑ j ∈ Finset.range B,
          ((∑ s ∈ Finset.range H, a j s) * (∑ t ∈ Finset.range H, b j t)) / (H : ℝ))
        ≤ (n : ℝ) / 8 + (n : ℝ) / 64) :
    -(n : ℝ) / 64 ≤
      ∑ j ∈ Finset.range B,
        (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s - a j t) * (b j s - b j t)) /
          (2 * (H : ℝ)) := by
  have hterm : ∀ j : ℕ,
      (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s - a j t) * (b j s - b j t)) /
          (2 * (H : ℝ))
        = (∑ s ∈ Finset.range H, a j s * b j s)
          - ((∑ s ∈ Finset.range H, a j s) * (∑ t ∈ Finset.range H, b j t)) / (H : ℝ) := by
    intro j
    rw [pair_id H (a j) (b j)]
    have h2H : (2 * (H : ℝ)) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib]
  linarith

end CutDyadic

theorem Conjectures.Cuts.Cut7eced11f9e0bb31c1a838cea
    (h₁ : ∃ K : ℕ, ∀ k ≥ K,
      let n : ℕ := 2 ^ k
      let H : ℕ := 2 ^ (k - k / 4)
      let B : ℕ := 2 ^ (k / 4 - 3)
      let p : ℕ → ℕ → ℕ := fun j t => n / 2 + j * H + t
      let a : ℕ → ℕ → ℝ := fun j t => if Nat.Prime (p j t) then Real.log ((p j t : ℕ) : ℝ) else 0
      let b : ℕ → ℕ → ℝ :=
        fun j t => if Nat.Prime (n - p j t) then Real.log (((n - p j t : ℕ)) : ℝ) else 0
      (n : ℝ) / 8 ≤ ∑ j ∈ Finset.range B, ∑ s ∈ Finset.range H, a j s * b j s)
    (h₂ : ∃ K : ℕ, ∀ k ≥ K,
      let n : ℕ := 2 ^ k
      let H : ℕ := 2 ^ (k - k / 4)
      let B : ℕ := 2 ^ (k / 4 - 3)
      let p : ℕ → ℕ → ℕ := fun j t => n / 2 + j * H + t
      let a : ℕ → ℕ → ℝ := fun j t => if Nat.Prime (p j t) then Real.log ((p j t : ℕ) : ℝ) else 0
      let b : ℕ → ℕ → ℝ :=
        fun j t => if Nat.Prime (n - p j t) then Real.log (((n - p j t : ℕ)) : ℝ) else 0
      (∑ j ∈ Finset.range B,
          ((∑ s ∈ Finset.range H, a j s) * (∑ t ∈ Finset.range H, b j t)) / (H : ℝ))
        ≤ (n : ℝ) / 8 + (n : ℝ) / 64)
    : (let w := fun p : ℕ => if Nat.Prime p then Real.log (p : ℝ) else 0; ∃ K : ℕ, ∀ k ≥ K, let n : ℕ := 2^k; let H : ℕ := 2^(k-k/4); let B : ℕ := 2^(k/4-3); let p := fun j t : ℕ => n/2+j*H+t; let a := fun j t : ℕ => w (p j t); let b := fun j t : ℕ => w (n-p j t); -(n:ℝ)/64 ≤ (∑ j ∈ Finset.range B, (∑ s ∈ Finset.range H, ∑ t ∈ Finset.range H, (a j s-a j t)*(b j s-b j t)) / (2*(H:ℝ)))) := by
  obtain ⟨K₁, hK₁⟩ := h₁
  obtain ⟨K₂, hK₂⟩ := h₂
  refine ⟨max K₁ K₂, ?_⟩
  intro k hk
  have hk1 : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K₂ ≤ k := le_trans (le_max_right _ _) hk
  have H1 := hK₁ k hk1
  have H2 := hK₂ k hk2
  dsimp only at H1 H2 ⊢
  exact CutDyadic.main_cut (2 ^ k) (2 ^ (k - k / 4)) (2 ^ (k / 4 - 3)) _ _ (by positivity) H1 H2
