import Mathlib

theorem Conjectures.JoshiAbc.NormalizedProduct :
    ∀ (d e : ℕ) (x y : ℝ), 0 < d → 0 < e → 0 < x → 0 < y → Real.log (x^e*y^d)/((d:ℝ)*e) = Real.log x/d + Real.log y/e := by
  intro d e x y hd he hx hy
  have hd0 : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he0 : (e:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Real.log_mul (pow_ne_zero _ hx.ne') (pow_ne_zero _ hy.ne'), Real.log_pow, Real.log_pow]
  field_simp
