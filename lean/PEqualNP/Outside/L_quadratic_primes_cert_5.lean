import Mathlib

namespace PEqualNP.Outside

/-- 模 5 的两条筛根及其完整性：`5 ∣ n ^ 2 + 1` 当且仅当 `n ≡ 2` 或 `n ≡ 3` (mod 5)。 -/
theorem L_quadratic_primes_cert_5 :
    ∀ n : ℕ, 5 ∣ n ^ 2 + 1 ↔ n % 5 = 2 ∨ n % 5 = 3 := by
  intro n
  set r := n % 5 with hr
  have hr5 : r < 5 := by
    rw [hr]
    exact Nat.mod_lt n (by norm_num)
  -- n = 5 * (n / 5) + r
  have hdecomp : n = 5 * (n / 5) + r := by
    rw [hr]
    have h := Nat.div_add_mod n 5
    omega
  -- 引入 k = n / 5，此后不再出现除法
  obtain ⟨k, hk⟩ : ∃ k, n = 5 * k + r := ⟨n / 5, hdecomp⟩
  rw [hk]
  -- 把 (5 * k + r) 的模 5 化简为 r
  have hmodn : (5 * k + r) % 5 = r := by
    have h1 : 5 * k + r = r + k * 5 := by ring
    rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr5]
  -- 平方展开：没有除法，ring 可以直接收
  have hsq : (5 * k + r) ^ 2 + 1 = 5 * (5 * k ^ 2 + 2 * k * r) + (r ^ 2 + 1) := by
    ring
  -- 模 5 下只看 r ^ 2 + 1
  have hmod : ((5 * k + r) ^ 2 + 1) % 5 = (r ^ 2 + 1) % 5 := by
    rw [hsq]
    have hcomm :
        5 * (5 * k ^ 2 + 2 * k * r) + (r ^ 2 + 1)
          = (r ^ 2 + 1) + (5 * k ^ 2 + 2 * k * r) * 5 := by
      ring
    rw [hcomm, Nat.add_mul_mod_self_left]
  rw [Nat.dvd_iff_mod_eq_zero, hmod, hmodn]
  interval_cases r <;> decide

end PEqualNP.Outside
