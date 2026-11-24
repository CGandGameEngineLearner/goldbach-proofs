import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_hyperbola_secants :
    ∀ (p : ℕ) [Fact (Nat.Prime p)] (k x y z : ZMod p), k ≠ 0 → x ≠ 0 → y ≠ 0 → z ≠ 0 → x ≠ y → x ≠ z → y ≠ z → (y-x)*(k/z-k/x) ≠ (z-x)*(k/y-k/x) := by
  intro p hp k x y z hk hx hy hz hxy hxz hyz habs
  have hxyz : x * y * z ≠ 0 := mul_ne_zero (mul_ne_zero hx hy) hz
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hzx : x - z ≠ 0 := sub_ne_zero.mpr hxz
  have hzy : y - z ≠ 0 := sub_ne_zero.mpr hyz
  have hkey : (y - x) * (k / z - k / x) - (z - x) * (k / y - k / x)
      = k * (y - x) * (x - z) * (y - z) / (x * y * z) := by
    field_simp
    ring
  have hnum : k * (y - x) * (x - z) * (y - z) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · exact hk
        · exact hyx
      · exact hzx
    · exact hzy
  have hne : k * (y - x) * (x - z) * (y - z) / (x * y * z) ≠ 0 :=
    div_ne_zero hnum hxyz
  exact hne (by rw [← hkey, habs, sub_self])
