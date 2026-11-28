import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Linarith

/-! Finite transport by n -> n - 2^e.
This is the combinatorial premise of accepted PR #4501.
It uses only Mathlib power monotonicity, parity, and finite-set injectivity. -/

theorem Conjectures.Cuts.Taskbcaf8df9b0b666726ac67f09 : (
∀ (x1 x2 : ℕ), (4 : ℕ) ≤ x1 → x2 ∈ Finset.Icc (1 : ℕ) (Nat.log (2 : ℕ) x1 / (2 : ℕ)) → ∀ (x5 : ℕ → Prop) [x6 : DecidablePred x5], {x7 ∈ Finset.Ico x1 ((2 : ℕ) * x1) | Even x7 ∧ x5 (x7 - (2 : ℕ) ^ x2)}.card ≤ {x7 ∈ Finset.Ico (x1 / (2 : ℕ)) ((2 : ℕ) * x1) | Even x7 ∧ x5 x7}.card
) := by
  classical
  intro X e hX he P hP
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
  have heLog : e * 2 ≤ Nat.log 2 X :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mp (Finset.mem_Icc.mp he).2
  have hk2 : 2 ≤ 2^e := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) he1
  have hsq : (2^e)^2 ≤ X := by
    rw [← pow_mul]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) heLog).trans
      (Nat.pow_log_le_self 2 (by omega))
  have hk : 2 * 2^e ≤ X := by nlinarith
  have hEvenK : Even (2^e) := (by decide : Even (2:ℕ)).pow_of_ne_zero (by omega)
  apply Finset.card_le_card_of_injOn (fun n : ℕ => n - 2^e)
  · intro n hn
    change n - 2^e ∈ ((Finset.Ico (X/2) (2*X)).filter (fun m => Even m ∧ P m))
    obtain ⟨hnI, hnEven, hnP⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ico.mp hnI
    have hkn : 2^e ≤ n := by omega
    refine Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_, hnP⟩
    exact (Nat.even_sub hkn).mpr (iff_of_true hnEven hEvenK)
  · intro a ha b hb hab
    change a - 2^e = b - 2^e at hab
    have haX := (Finset.mem_Ico.mp (Finset.mem_filter.mp ha).1).1
    have hbX := (Finset.mem_Ico.mp (Finset.mem_filter.mp hb).1).1
    omega
