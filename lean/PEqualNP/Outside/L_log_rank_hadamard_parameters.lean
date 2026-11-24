import Mathlib

theorem PEqualNP.Outside.L_log_rank_hadamard_parameters :
    ∀ t : ℕ, 3 ≤ t → let n := 2^t-1; let k := 2^(t-1)-1; n^2*(n-1) < 8*k*(n-k)*(n-2) := by
  intro t ht
  dsimp only
  have h2t : 2^t = 2 * 2^(t - 1) := by
    calc 2^t = 2^(t - 1 + 1) := by congr 1; omega
    _ = 2^(t - 1) * 2 := by rw [Nat.pow_succ]
    _ = 2 * 2^(t - 1) := by rw [Nat.mul_comm]
  have hX : 4 ≤ 2^(t - 1) := by
    have hle : 2^2 ≤ 2^(t - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact hle
  set Y := 2^(t - 1) - 4
  have hY : 2^(t - 1) = Y + 4 := by omega
  have hn_eq : 2^t - 1 = 2 * Y + 7 := by rw [h2t, hY]; omega
  have hk_eq : 2^(t - 1) - 1 = Y + 3 := by rw [hY]; omega
  rw [hn_eq, hk_eq]
  have h1 : 2 * Y + 7 - 1 = 2 * (Y + 3) := by omega
  have h2 : 2 * Y + 7 - (Y + 3) = Y + 4 := by omega
  have h3 : 2 * Y + 7 - 2 = 2 * Y + 5 := by omega
  rw [h1, h2, h3]
  have h_lhs : (2 * Y + 7)^2 * (2 * (Y + 3)) = 2 * (Y + 3) * (2 * Y + 7)^2 := by
    ring
  have h_rhs : 8 * (Y + 3) * (Y + 4) * (2 * Y + 5) = 2 * (Y + 3) * (4 * (Y + 4) * (2 * Y + 5)) := by
    ring
  have h_poly : 4 * (Y + 4) * (2 * Y + 5) = (2 * Y + 7)^2 + 4 * Y^2 + 24 * Y + 31 := by
    ring
  have h_ineq : (2 * Y + 7)^2 < 4 * (Y + 4) * (2 * Y + 5) := by
    rw [h_poly]
    omega
  have hpos : 0 < 2 * (Y + 3) := by omega
  calc
    (2 * Y + 7)^2 * (2 * (Y + 3)) = 2 * (Y + 3) * (2 * Y + 7)^2 := h_lhs
    _ < 2 * (Y + 3) * (4 * (Y + 4) * (2 * Y + 5)) := Nat.mul_lt_mul_of_pos_left h_ineq hpos
    _ = 8 * (Y + 3) * (Y + 4) * (2 * Y + 5) := h_rhs.symm
