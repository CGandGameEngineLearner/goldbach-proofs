import Mathlib

/-!
新路线 · Levent GRH 与自然扩张 · QP-0046 · 两个有限位置上的纯张量配对

所用的恒等式：对乘积群 ZMod p × ZMod q 的和先按第一个坐标、再按第二个坐标逐项求和（有限和交换次序），
再把两个坐标上的和各自认成离散傅里叶变换 ZMod.dft 的定义式。
量词与假设：p、q 是任意非零自然数，u、v 分别是 ZMod p、ZMod q 上的任意复值函数，k、j 是任意频率。
-/

theorem PEqualNP.Outside.L_quadratic_primes_levent_tensor_fourier_test :
    ∀ (p q : ℕ) [NeZero p] [NeZero q] (u : ZMod p → ℂ) (v : ZMod q → ℂ) (k : ZMod p) (j : ZMod q), (∑ z : ZMod p × ZMod q, (ZMod.stdAddChar (-(z.1*k))*u z.1) * (ZMod.stdAddChar (-(z.2*j))*v z.2)) = ZMod.dft u k * ZMod.dft v j := by
  intro p _ q _ u v k j
  rw [ZMod.dft_apply, ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
