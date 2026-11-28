import Mathlib
import Conjectures.Cuts.Taske279f058a85d26bca8e383a7
import Conjectures.Cuts.Taska4d06654f086b83844140db4

/-- A bounded tuple counted at an even target gives an exact thirteen-power representation. -/
theorem Conjectures.Goldbach.BinaryShiftThirteen : (∃ N : ℕ, ∀ n ≥ N, Even n → ∃ (p q : ℕ) (e : Fin 13 → ℕ), Nat.Prime p ∧ Nat.Prime q ∧ n = p+q+∑ j, 2^(e j+1)) := by
  obtain ⟨N, hN⟩ := Conjectures.Cuts.Taske279f058a85d26bca8e383a7
  exact ⟨N, fun n hn hEven => Conjectures.Cuts.Taska4d06654f086b83844140db4 n (hN n hn hEven)⟩
