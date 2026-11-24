import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_ordered_product :
    ∀ a b c x y z : ℤ, a≤b → b≤c → x≤y → y≤z → a+b+c=0 → x+y+z=0 → a^2+a*b+b^2=x^2+x*y+y^2 → c<z → a*b*c<x*y*z := by
  intro a b c x y z hab hbc hxy hyz hsum hsum2 hnorm hcz
  have hc0 : 0 ≤ c := by nlinarith [hab, hbc, hsum]
  have hz0 : 0 ≤ z := by linarith
  have hb : b = -(c + a) := by linarith
  have hS_le : a ^ 2 + a * b + b ^ 2 ≤ 3 * c ^ 2 := by
    have h1 : 0 ≤ c - a := by linarith
    have h2 : 0 ≤ 2 * c + a := by linarith
    have h3 : 0 ≤ (c - a) * (2 * c + a) := mul_nonneg h1 h2
    rw [hb]
    nlinarith [h3]
  have hab' : a * b = c ^ 2 - (a ^ 2 + a * b + b ^ 2) := by
    have hc : c = -(a + b) := by linarith
    rw [hc]
    ring
  have hxy' : x * y = z ^ 2 - (x ^ 2 + x * y + y ^ 2) := by
    have hz : z = -(x + y) := by linarith
    rw [hz]
    ring
  have habc : a * b * c = c * (c ^ 2 - (a ^ 2 + a * b + b ^ 2)) := by
    linear_combination c * hab'
  have hxyz : x * y * z = z * (z ^ 2 - (x ^ 2 + x * y + y ^ 2)) := by
    linear_combination z * hxy'
  rw [habc, hxyz, ← hnorm]
  have hgt : 0 < z - c := by linarith
  have hzz : 0 < (z - c) * (z + 2 * c) := mul_pos hgt (by linarith)
  have hpos : 0 < z ^ 2 + z * c + c ^ 2 - (a ^ 2 + a * b + b ^ 2) := by
    nlinarith [hzz, hS_le]
  have hdiff : z * (z ^ 2 - (a ^ 2 + a * b + b ^ 2)) - c * (c ^ 2 - (a ^ 2 + a * b + b ^ 2))
      = (z - c) * (z ^ 2 + z * c + c ^ 2 - (a ^ 2 + a * b + b ^ 2)) := by
    ring
  nlinarith [hdiff, mul_pos hgt hpos]
