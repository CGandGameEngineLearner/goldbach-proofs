import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cap_certificate :
    ∀ (m B S z : ℤ), (∃ x y : ℤ, x ≤ y ∧ y ≤ z ∧ x + y + z = 0 ∧ x ^ 2 + x * y + y ^ 2 = S ∧ 0 ≤ (m + x) ∧ (m + z) ≤ B) ↔ ((m + z) ≤ B ∧ ∃ d : ℤ, 0 ≤ d ∧ d ≤ 3 * z ∧ z + d ≤ 2 * m ∧ (2 : ℤ) ∣ (z + d) ∧ d ^ 2 + 3 * z ^ 2 = 4 * S) := by
  intro m B S z
  constructor
  · -- (⇒) 从零和有序三元组 (x, y, z) 提取证书 d := y - x = 2 * y + z
    rintro ⟨x, y, hxy, hyz, hsum, hnorm, hmx, hmzB⟩
    -- 由 x + y + z = 0 得 x = -y - z，消去 x
    have hx : x = -y - z := by omega
    subst hx
    -- 此时 d := y - x = 2 * y + z
    refine ⟨hmzB, 2 * y + z, ?_, ?_, ?_, ?_, ?_⟩
    · -- 0 ≤ d ：由 x ≤ y（即 -y - z ≤ y）
      omega
    · -- d ≤ 3 * z ：由 y ≤ z
      omega
    · -- z + d ≤ 2 * m ：由 0 ≤ m + x
      omega
    · -- (2 : ℤ) ∣ (z + d) ：z + d = 2 * (y + z)
      exact ⟨y + z, by omega⟩
    · -- d ^ 2 + 3 * z ^ 2 = 4 * S ：范数恒等式 4 * (x^2 + x*y + y^2) = d^2 + 3 * z^2
      have h4 : (2 * y + z) ^ 2 + 3 * z ^ 2
          = 4 * ((-y - z) ^ 2 + (-y - z) * y + y ^ 2) := by
        ring
      linarith
  · -- (⇐) 从证书重构零和有序三元组
    rintro ⟨hmzB, d, hd0, hd3, hzdm, h2dvd, hdnorm⟩
    -- 由 2 ∣ (z + d) 取整数 t := (z + d) / 2，避免除法：携带 z + d = 2 * t
    have ht_ex : ∃ t : ℤ, z + d = 2 * t := h2dvd
    obtain ⟨t, ht⟩ := ht_ex
    -- 重构 x := -t, y := t - z
    refine ⟨-t, t - z, ?_, ?_, ?_, ?_, ?_, hmzB⟩
    · -- x ≤ y ：即 z ≤ 2 * t = z + d，由 0 ≤ d
      omega
    · -- y ≤ z ：即 2 * t ≤ 4 * z，由 d ≤ 3 * z
      omega
    · -- x + y + z = 0
      ring
    · -- x ^ 2 + x * y + y ^ 2 = S ：4 * (x^2 + x*y + y^2) = (2*t - z)^2 + 3*z^2 = d^2 + 3*z^2 = 4 * S
      have h2t : 2 * t - z = d := by omega
      have h4 : (2 * t - z) ^ 2 + 3 * z ^ 2
          = 4 * ((-t) ^ 2 + (-t) * (t - z) + (t - z) ^ 2) := by
        ring
      rw [h2t] at h4
      linarith
    · -- 0 ≤ m + x ：即 2 * t ≤ 2 * m，由 z + d ≤ 2 * m
      omega
