import Mathlib

/-!
模 1181 的平方剩余判定：1181 是素数且除以 4 余 1 时，一个数的平方加 1 被 1181 整除，
当且仅当这个数除以 1181 的余数是 243 或 938，其中 938 正好等于 1181 减 243。
先用有限枚举确认 0 到 1181 之间的整数里只有 243 与 938 这两个余数让 1181 整除平方加 1，
再用模运算把任意自然数的平方约化到它的余数上，于是结论对全部自然数成立。
-/

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_quadratic_primes_cert_1181 :
    ∀ n:ℕ, 1181∣n^2+1 ↔ n % 1181= 243 ∨ n % 1181= 938 := by
  intro n
  have key : ∀ r < 1181, (1181 ∣ r ^ 2 + 1) ↔ (r = 243 ∨ r = 938) := by
    decide
  have hsq : (n ^ 2) % 1181 = ((n % 1181) ^ 2) % 1181 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod]
  have hmod : (n ^ 2 + 1) % 1181 = ((n % 1181) ^ 2 + 1) % 1181 := by
    calc (n ^ 2 + 1) % 1181
        = (n ^ 2 % 1181 + 1 % 1181) % 1181 := Nat.add_mod _ _ _
      _ = ((n % 1181) ^ 2 % 1181 + 1 % 1181) % 1181 := by rw [hsq]
      _ = ((n % 1181) ^ 2 + 1) % 1181 := by rw [Nat.mod_add_mod]
  have h2 := key (n % 1181) (Nat.mod_lt _ (by norm_num))
  rw [Nat.dvd_iff_mod_eq_zero] at h2
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact h2
