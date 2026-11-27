import Mathlib

theorem Conjectures.Goldbach.BeaumontMarginalObstruction :
  ∀ m : ℕ, 2 ≤ m → ∃ a b : Fin m → ZMod m, Function.Bijective a ∧ Function.Bijective b ∧ ∀ t, a t ≠ b t := by
  intro m hm
  haveI : NeZero m := ⟨by omega⟩
  haveI : Fact (1 < m) := ⟨by omega⟩
  let e : Fin m ≃ ZMod m :=
    Fintype.equivOfCardEq ((Fintype.card_fin m).trans (ZMod.card m).symm)
  refine ⟨e, e.trans (Equiv.addRight (1 : ZMod m)), e.bijective,
    (e.trans (Equiv.addRight (1 : ZMod m))).bijective, ?_⟩
  intro t h
  have h0 : e t + 0 = e t + 1 := by
    rw [add_zero]
    exact h
  exact zero_ne_one (add_left_cancel h0)