import Mathlib

/-!
# 模 64 主弧系数证书（L-goldbach-cert-64）

对任意与 64 互素的 `a`，Ramanujan 和
`∑ b ∈ (Finset.range 64).filter (fun b => Nat.Coprime b 64), exp (2πi a b / 64)` 为零：
这是一般恒等式 `c_q(a) = μ(q) / φ(q)` 在 `q = 64 = 2 ^ 6`（`φ(64) = 32`，`μ(64) = 0`）处的特例。

这里不引用一般恒等式，直接配对。`Finset.range 64 = range 32 ∪ (range 32) + 32`，
而与 64 互素等价于奇数，在 `b ↦ b + 32` 下不变；
又 `exp (2πi a (b + 32) / 64) = exp (2πi a b / 64) * exp (πi a)`，`a` 为奇数时 `exp (πi a) = -1`，
所以配对的两项逐项相消。
-/

theorem PEqualNP.Outside.L_goldbach_cert_64 :
    ∀ a:ℕ, Nat.Coprime a 64 → (∑ b ∈ (Finset.range 64).filter (fun b => Nat.Coprime b 64), Complex.exp (((2*Real.pi*(a:ℝ)*b/64:ℝ):ℂ)*Complex.I))/(32:ℂ)=(0:ℂ)/32 := by
  intro a ha
  -- 与 64 = 2 ^ 6 互素 ⇔ 与 2 互素 ⇔ 奇数
  have hc : ∀ b : ℕ, Nat.Coprime b 64 ↔ Odd b := by
    intro b
    rw [show (64 : ℕ) = 2 ^ 6 from by norm_num, Nat.coprime_pow_right_iff (by norm_num)]
    simp
  have ha_odd : Odd a := (hc a).mp ha
  -- a 为奇数时 exp (πi a) = -1：写 a = 2k + 1，2kπi 的部分由周期性消去
  have hexp : Complex.exp (((Real.pi * (a:ℝ) : ℝ) : ℂ) * Complex.I) = -1 := by
    obtain ⟨k, rfl⟩ := ha_odd
    have h3 : (((Real.pi * ((2 * k + 1 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I
        = (k:ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h3, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul]
    rw [Complex.exp_pi_mul_I]
  -- 配对：b + 32 处的项恰是 b 处的项的相反数
  have hpair : ∀ b : ℕ,
      Complex.exp (((2 * Real.pi * (a:ℝ) * ((32 + b : ℕ) : ℝ) / 64 : ℝ) : ℂ) * Complex.I)
        = -Complex.exp (((2 * Real.pi * (a:ℝ) * b / 64 : ℝ) : ℂ) * Complex.I) := by
    intro b
    have h1 : (2 * Real.pi * (a:ℝ) * ((32 + b : ℕ) : ℝ) / 64 : ℝ)
        = (2 * Real.pi * (a:ℝ) * (b:ℝ) / 64 : ℝ) + Real.pi * (a:ℝ) := by
      push_cast
      field_simp
      ring
    have h2 : (((2 * Real.pi * (a:ℝ) * (b:ℝ) / 64 + Real.pi * (a:ℝ) : ℝ)) : ℂ) * Complex.I
        = ((2 * Real.pi * (a:ℝ) * (b:ℝ) / 64 : ℝ) : ℂ) * Complex.I
          + ((Real.pi * (a:ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h1, h2, Complex.exp_add, hexp]
    ring
  -- 按 b < 32 与 b ≥ 32 两段求和，两段逐项相消
  have key : (∑ b ∈ (Finset.range 64).filter (fun b => Nat.Coprime b 64),
      Complex.exp (((2*Real.pi*(a:ℝ)*b/64:ℝ):ℂ)*Complex.I)) = 0 := by
    have hpart : Finset.range 64
        = Finset.range 32 ∪ (Finset.range 32).map (addLeftEmbedding 32) :=
      Finset.range_add 32 32
    have hb : ∀ b : ℕ, Nat.Coprime (32 + b) 64 ↔ Nat.Coprime b 64 := by
      intro b
      rw [hc, hc, Nat.odd_iff, Nat.odd_iff]
      omega
    rw [Finset.sum_filter, hpart,
      Finset.sum_union (Finset.disjoint_range_addLeftEmbedding 32 (Finset.range 32))]
    simp only [Finset.sum_map, addLeftEmbedding_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [hb b, hpair b]
    split_ifs <;> ring
  rw [key]
