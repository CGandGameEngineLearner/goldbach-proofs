import Mathlib

theorem PEqualNP.Outside.L_goldbach_characters_diagonal_correction : ∀ (n : ℕ) [NeZero n], 2<n → ∀ w : ℕ → ℝ, (∑ a : (ZMod n)ˣ, w (a : ZMod n).val * w ((-a : (ZMod n)ˣ) : ZMod n).val) = ∑ k ∈ (Finset.range n).filter (fun k => k.Coprime n), w k*w (n-k) := by
  intro n _ hn w
  let : Fact (1 < n) := ⟨by omega⟩
  refine Finset.sum_bij (fun (a : (ZMod n)ˣ) _ => (a : ZMod n).val) ?_ ?_ ?_ ?_
  · intro a _
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ZMod.val_coe_unit_coprime a⟩
  · intro a _ b _ hab
    exact Units.ext (ZMod.val_injective n hab)
  · intro k hk
    obtain ⟨hkn, hcop⟩ := Finset.mem_filter.mp hk
    refine ⟨ZMod.unitOfCoprime k hcop, Finset.mem_univ _, ?_⟩
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hkn)
  · intro a _
    change w (a : ZMod n).val * w (-(a : ZMod n)).val = _
    rw [ZMod.neg_val, ite_eq_right a.ne_zero]
