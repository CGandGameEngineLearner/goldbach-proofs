import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

theorem Conjectures.Goldbach.ArcDisjointExplicitCutoff :
    ∀ n : ℕ, 1000000 ≤ n → 2 * ((Nat.log 2 (n + 2)) ^ 2) ^ 2 < n := by
  intro n hn
  set k : ℕ := Nat.log 2 (n + 2) with hk
  have h2 : (2 : ℕ) ^ 19 ≤ n + 2 := by
    have hc : (2 : ℕ) ^ 19 = 524288 := by norm_num
    rw [hc]
    exact le_trans (by norm_num : 524288 ≤ 1000000)
      (le_trans hn (Nat.le_add_right n 2))
  have hk19 : 19 ≤ k := Nat.le_log_of_pow_le (by norm_num) h2
  have hpow : 2 ^ k ≤ n + 2 := by
    rw [hk]
    exact Nat.pow_log_le_self 2 (by positivity)
  have key : ∀ k : ℕ, 19 ≤ k → 2 * k ^ 4 + 3 ≤ 2 ^ k := by
    intro k hkk
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hkk
    rw [hm]
    have main : ∀ m : ℕ, 2 * (19 + m) ^ 4 + 3 ≤ 2 ^ (19 + m) := by
      intro m
      induction m with
      | zero => norm_num
      | succ m ih =>
          have hstep : 2 * (19 + (m + 1)) ^ 4 + 3 ≤ 2 * (2 * (19 + m) ^ 4 + 3) := by
            have hZ : (2 * ((19 + (m + 1) : ℕ) : ℤ) ^ 4 + 3 : ℤ) ≤
                2 * (2 * ((19 + m : ℕ) : ℤ) ^ 4 + 3) := by
              have hcast : ((19 + (m + 1) : ℕ) : ℤ) = ((19 + m : ℕ) : ℤ) + 1 := by
                push_cast; ring
              rw [hcast]
              have hpos : (0 : ℤ) ≤
                  2 * (2 * ((19 + m : ℕ) : ℤ) ^ 4 + 3) -
                    (2 * (((19 + m : ℕ) : ℤ) + 1) ^ 4 + 3) := by
                have hexp : 2 * (2 * ((19 + m : ℕ) : ℤ) ^ 4 + 3) -
                    (2 * (((19 + m : ℕ) : ℤ) + 1) ^ 4 + 3)
                    = 2 * (m : ℤ) ^ 4 + 144 * (m : ℤ) ^ 3 + 3864 * (m : ℤ) ^ 2
                        + 45744 * (m : ℤ) + 201287 := by
                  have ht : ((19 + m : ℕ) : ℤ) = 19 + (m : ℤ) := by push_cast; ring
                  rw [ht]; ring
                rw [hexp]
                positivity
              linarith
            exact_mod_cast hZ
          calc 2 * (19 + (m + 1)) ^ 4 + 3 ≤ 2 * (2 * (19 + m) ^ 4 + 3) := hstep
            _ ≤ 2 * 2 ^ (19 + m) := by linarith
            _ = 2 ^ (19 + (m + 1)) := by
                rw [show 19 + (m + 1) = 19 + m + 1 by ring, pow_succ]; ring
    exact main m
  have hkey : 2 * k ^ 4 + 3 ≤ 2 ^ k := key k hk19
  have h1 : 2 * k ^ 4 + 3 ≤ n + 2 := le_trans hkey hpow
  have h1Z : (2 * (k : ℤ) ^ 4 + 3 : ℤ) ≤ (n : ℤ) + 2 := by exact_mod_cast h1
  have hltZ : (2 * (k : ℤ) ^ 4 : ℤ) < (n : ℤ) := by linarith
  have hlt : 2 * k ^ 4 < n := by exact_mod_cast hltZ
  calc 2 * ((Nat.log 2 (n + 2)) ^ 2) ^ 2 = 2 * k ^ 4 := by
        rw [← hk]
        ring
    _ < n := hlt
