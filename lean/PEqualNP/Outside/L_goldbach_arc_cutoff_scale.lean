import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Basic

theorem PEqualNP.Outside.L_goldbach_arc_cutoff_scale :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; ∃ N : ℕ, ∀ n : ℕ, N≤n → 2*(Q n)^2<n := by
  intro Q arcs
  have aux : ∀ k : ℕ, 20 ≤ k → 2 * k ^ 4 + 2 < 2 ^ k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have h1 : (k+1)^4 ≤ 2 * k^4 := by
        have h3 : 20 * k ^ 3 ≤ k ^ 4 := by
          have : k ^ 4 = k * k ^ 3 := by ring
          rw [this]
          exact Nat.mul_le_mul_right _ hk
        have h2 : 20 * k ^ 2 ≤ k ^ 3 := by
          have : k ^ 3 = k * k ^ 2 := by ring
          rw [this]
          exact Nat.mul_le_mul_right _ hk
        have h4 : 20 * k ≤ k ^ 2 := by nlinarith
        nlinarith
      have h5 : 2 ^ (k+1) = 2 * 2 ^ k := by ring
      rw [h5]
      omega
  refine ⟨2 ^ 20, fun n hn => ?_⟩
  show 2 * (Nat.log 2 (n+2) ^ 2) ^ 2 < n
  have hk : 20 ≤ Nat.log 2 (n+2) := by
    apply Nat.le_log_of_pow_le (by norm_num)
    have : 2 ^ 20 ≤ n := hn
    omega
  have hp : 2 ^ Nat.log 2 (n+2) ≤ n + 2 := Nat.pow_log_le_self 2 (by omega)
  have := aux _ hk
  have e : (Nat.log 2 (n+2) ^ 2) ^ 2 = Nat.log 2 (n+2) ^ 4 := by ring
  rw [e]
  omega
