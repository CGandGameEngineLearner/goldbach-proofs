import Mathlib

/-! Self-contained proof of `L-goldbach-beaumont-quotient-obstruction`. -/

namespace PEqualNP.Outside

theorem L_goldbach_beaumont_quotient_obstruction :
    ∀ m : ℕ, 1 < m → ∃ a b : ℕ, a ≠ b ∧ a % m = b % m ∧
      Nat.Prime a ∧ ¬ Nat.Prime b := by
  intro m hm
  refine ⟨2, 2 * (m + 1), ?_, ?_, by norm_num, ?_⟩
  · omega
  · have hb : 2 * (m + 1) = 2 + 2 * m := by ring
    rw [hb]
    exact (Nat.add_mul_mod_self_right 2 2 m).symm
  · intro hp
    have hEven : Even (2 * (m + 1)) := even_iff_two_dvd.mpr ⟨m + 1, rfl⟩
    have hne : 2 * (m + 1) ≠ 2 := by omega
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact hne h2
    · have hbmod : (2 * (m + 1)) % 2 = 0 := by
        exact Nat.mul_mod_right 2 (m + 1)
      omega

end PEqualNP.Outside
