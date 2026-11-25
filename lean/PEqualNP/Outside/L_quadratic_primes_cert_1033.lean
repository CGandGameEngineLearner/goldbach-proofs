import Mathlib

/-!
模 1033 的平方剩余判定：1033 是素数且除以 4 余 1 时，一个数的平方加 1 被 1033 整除，
当且仅当这个数除以 1033 的余数是 355 或 678，其中 678 正好等于 1033 减 355。
先用有限枚举确认 0 到 1033 之间的整数里只有 355 与 678 这两个余数让 1033 整除平方加 1，
再用模运算把任意自然数的平方约化到它的余数上，于是结论对全部自然数成立。
-/

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_quadratic_primes_cert_1033 :
    ∀ n:ℕ, 1033∣n^2+1 ↔ n % 1033= 355 ∨ n % 1033= 678 := by
  intro n
  have key : ∀ r < 1033, (1033 ∣ r ^ 2 + 1) ↔ (r = 355 ∨ r = 678) := by
    decide
  have hsq : (n ^ 2) % 1033 = ((n % 1033) ^ 2) % 1033 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod]
  have hmod : (n ^ 2 + 1) % 1033 = ((n % 1033) ^ 2 + 1) % 1033 := by
    calc (n ^ 2 + 1) % 1033
        = (n ^ 2 % 1033 + 1 % 1033) % 1033 := Nat.add_mod _ _ _
      _ = ((n % 1033) ^ 2 % 1033 + 1 % 1033) % 1033 := by rw [hsq]
      _ = ((n % 1033) ^ 2 + 1) % 1033 := by rw [Nat.mod_add_mod]
  have h2 := key (n % 1033) (Nat.mod_lt _ (by norm_num))
  rw [Nat.dvd_iff_mod_eq_zero] at h2
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact h2
