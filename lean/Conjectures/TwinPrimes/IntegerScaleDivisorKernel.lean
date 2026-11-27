import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Basic

theorem Conjectures.TwinPrimes.IntegerScaleDivisorKernel :
    ∀ Y p d : ℕ, (Finset.Ico Y (2*Y)).filter (fun X => X<p ∧ 50*p<51*X ∧ X<d^3) = Finset.Ico (max Y (50*p/51+1)) (min (2*Y) (min p (d^3))) := by
  intro Y p d
  ext X
  have key : (50*p/51 < X) ↔ (50*p < X * 51) := Nat.div_lt_iff_lt_mul (by norm_num)
  simp only [Finset.mem_Ico, Finset.mem_filter]
  constructor
  · intro h
    obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := h
    have hk : 50*p/51 + 1 ≤ X := by
      rw [Nat.add_one_le_iff]
      exact key.mpr (by omega)
    simp only [max_le_iff, lt_min_iff]
    exact ⟨⟨h1, hk⟩, h2, h3, h5⟩
  · intro h
    simp only [max_le_iff, lt_min_iff] at h
    obtain ⟨⟨h1, hk⟩, h2, h3, h5⟩ := h
    refine ⟨⟨h1, h2⟩, h3, ?_, h5⟩
    have hk' := key.mp (by omega)
    omega
