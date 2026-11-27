import Mathlib

namespace Conjectures.Goldbach

theorem BeaumontMarginalObstruction :
    ∀ m : ℕ, 2 ≤ m → ∃ a b : Fin m → ZMod m,
      Function.Bijective a ∧ Function.Bijective b ∧ ∀ t, a t ≠ b t := by
  intro m hm
  have hne : m ≠ 0 := by omega
  have hlt : 1 < m := by omega
  letI : NeZero m := ⟨hne⟩
  letI : Fact (1 < m) := ⟨hlt⟩
  refine ⟨fun t => ZMod.finEquiv m t, fun t => ZMod.finEquiv m t + 1,
    (ZMod.finEquiv m).bijective, ?_, ?_⟩
  · constructor
    · intro s t h
      exact (ZMod.finEquiv m).injective (add_right_cancel h)
    · intro y
      refine ⟨(ZMod.finEquiv m).symm (y - 1), ?_⟩
      show ZMod.finEquiv m ((ZMod.finEquiv m).symm (y - 1)) + 1 = y
      rw [RingEquiv.apply_symm_apply, sub_add_cancel]
  · intro t
    show ZMod.finEquiv m t ≠ ZMod.finEquiv m t + 1
    intro h
    have h1 : (0 : ZMod m) = 1 := add_left_cancel (show ZMod.finEquiv m t + 0 = ZMod.finEquiv m t + 1 by
      rw [add_zero]
      exact h)
    exact one_ne_zero h1.symm

end Conjectures.Goldbach
