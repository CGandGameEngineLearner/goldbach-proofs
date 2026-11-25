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
  -- 把 n 写成 5 * (n / 5) + r，于是 n ^ 2 + 1 = 5 * (...) + (r ^ 2 + 1)
  have hdecomp : n = 5 * (n / 5) + r := by
    rw [hr, Nat.mul_comm 5 (n / 5)]
    exact (Nat.div_add_mod n 5).symm
  have hsq : n ^ 2 + 1 = 5 * (5 * (n / 5) ^ 2 + 2 * (n / 5) * r) + (r ^ 2 + 1) := by
    rw [hdecomp]
    ring
  -- 只需看 r ^ 2 + 1 模 5
  have hmod : (n ^ 2 + 1) % 5 = (r ^ 2 + 1) % 5 := by
    rw [hsq]
    have hcomm :
        5 * (5 * (n / 5) ^ 2 + 2 * (n / 5) * r) + (r ^ 2 + 1)
          = (r ^ 2 + 1) + (5 * (n / 5) ^ 2 + 2 * (n / 5) * r) * 5 := by
      ring
    rw [hcomm, Nat.add_mul_mod_self_left]
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  interval_cases r <;> decide

end PEqualNP.Outside
