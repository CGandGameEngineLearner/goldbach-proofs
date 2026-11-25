import Mathlib

/-!
模 1301 的平方剩余判定：1301 是素数且除以 4 余 1 时，一个数的平方加 1 被 1301 整除，
当且仅当这个数除以 1301 的余数是 51 或 1250，其中 1250 正好等于 1301 减 51。
先用有限枚举确认 0 到 1301 之间的整数里只有 51 与 1250 这两个余数让 1301 整除平方加 1，
再用模运算把任意自然数的平方约化到它的余数上，于是结论对全部自然数成立。
-/

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_quadratic_primes_cert_1301 :
    ∀ n:ℕ, 1301∣n^2+1 ↔ n % 1301= 51 ∨ n % 1301= 1250 := by
  intro n
  have key : ∀ r < 1301, (1301 ∣ r ^ 2 + 1) ↔ (r = 51 ∨ r = 1250) := by
    decide
  have hsq : (n ^ 2) % 1301 = ((n % 1301) ^ 2) % 1301 := by
    rw [Nat.pow_two, Nat.pow_two, Nat.mul_mod]
  have hmod : (n ^ 2 + 1) % 1301 = ((n % 1301) ^ 2 + 1) % 1301 := by
    calc (n ^ 2 + 1) % 1301
        = (n ^ 2 % 1301 + 1 % 1301) % 1301 := Nat.add_mod _ _ _
      _ = ((n % 1301) ^ 2 % 1301 + 1 % 1301) % 1301 := by rw [hsq]
      _ = ((n % 1301) ^ 2 + 1) % 1301 := by rw [Nat.mod_add_mod]
  have h2 := key (n % 1301) (Nat.mod_lt _ (by norm_num))
  rw [Nat.dvd_iff_mod_eq_zero] at h2
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact h2
