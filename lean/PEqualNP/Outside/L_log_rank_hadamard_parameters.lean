import Mathlib

theorem PEqualNP.Outside.L_log_rank_hadamard_parameters :
    ∀ t : ℕ, 3 ≤ t → let n := 2^t-1; let k := 2^(t-1)-1; n^2*(n-1) < 8*k*(n-k)*(n-2) := by
  intro t ht
  intro n k
  have hp : 2 ^ t = 2 * 2 ^ (t - 1) := by
    conv_lhs => rw [show t = (t - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have h1 : 1 ≤ 2 ^ (t - 1) := Nat.one_le_two_pow
  have hn : n = 2 * k + 1 := by
    show 2 ^ t - 1 = 2 * (2 ^ (t - 1) - 1) + 1
    omega
  have hk2 : 2 ≤ k := by
    show 2 ≤ 2 ^ (t - 1) - 1
    have h4 : 4 ≤ 2 ^ (t - 1) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (t - 1) := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    omega
  have e1 : (2 * k + 1) - 1 = 2 * k := by omega
  have e2 : (2 * k + 1) - k = k + 1 := by omega
  have e3 : (2 * k + 1) - 2 = 2 * k - 1 := by omega
  rw [hn, e1, e2, e3]
  obtain ⟨j, hj⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  rw [hj]
  have e4 : 2 * (j + 2) - 1 = 2 * j + 3 := by omega
  rw [e4]
  have hcast : ((2 * (j + 2) + 1) ^ 2 * (2 * (j + 2)) : ℤ) < ((8 * (j + 2) * (j + 2 + 1) * (2 * j + 3) : ℕ) : ℤ) := by
    push_cast
    nlinarith
  exact_mod_cast hcast
