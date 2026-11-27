import Mathlib

/-!
# JA-0021: the three prescribed 29-adic jets span the three-dimensional quotient

With `z = 7` in `ZMod 29` the three jets of the local model are

* `(1, 0, 0)`,
* `(1 + z^2) * (0, 1, 0) = 21 * (0, 1, 0)`,
* `(1, 0, 0) + (z^2) * (0, 0, 1) = (1, 0, 0) + 20 * (0, 0, 1)`.

The first jet is already a coordinate vector; subtracting it from the third leaves `20` in the
last slot; and `21 * 18 = 1`, `20 * 16 = 1` in `ZMod 29`.  Hence the three jets recover the
standard basis and their span is the whole three-dimensional quotient.

All numerical facts below are decided in `ZMod 29` (`21 = 1 + 7^2`, `20 = 7^2`), so the
argument is elementary integer arithmetic, with no `p`-adic or analytic input.
-/

namespace Conjectures.JoshiAbc

theorem ThreeJetSpan :
    let z : ZMod 29 := 7
    let v : Fin 3 → Fin 3 → ZMod 29 := ![![1,0,0],![0,1+z^2,0],![1,0,z^2]]
    Submodule.span (ZMod 29) (Set.range v) = ⊤ := by
  have main : Submodule.span (ZMod 29)
      (Set.range (![![1,0,0],![0,(1:ZMod 29)+(7:ZMod 29)^2,0],![1,0,(7:ZMod 29)^2]] :
        Fin 3 → Fin 3 → ZMod 29)) = ⊤ := by
    set w : Fin 3 → Fin 3 → ZMod 29 :=
      ![![1,0,0],![0,(1:ZMod 29)+(7:ZMod 29)^2,0],![1,0,(7:ZMod 29)^2]] with hw
    have hw0 : w 0 = (Pi.single (0 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29) := by
      rw [hw]
      funext i
      fin_cases i <;> simp
    have hw1 : w 1 = ((1:ZMod 29)+(7:ZMod 29)^2) •
        (Pi.single (1 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29) := by
      rw [hw]
      funext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
    have hw2 : w 2 = (Pi.single (0 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29)
        + ((7:ZMod 29)^2) • (Pi.single (2 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29) := by
      rw [hw]
      funext i
      fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul]
    have m0 : (Pi.single (0 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29) ∈
        Submodule.span (ZMod 29) (Set.range w) := by
      have h : w 0 ∈ Submodule.span (ZMod 29) (Set.range w) :=
        Submodule.subset_span (Set.mem_range_self (0 : Fin 3))
      rw [hw0] at h
      exact h
    have m1' : ((1:ZMod 29)+(7:ZMod 29)^2) •
        (Pi.single (1 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29) ∈
        Submodule.span (ZMod 29) (Set.range w) := by
      rw [← hw1]
      exact Submodule.subset_span (Set.mem_range_self (1 : Fin 3))
    have h18 : ((18 : ZMod 29) * ((1:ZMod 29)+(7:ZMod 29)^2)) = 1 := by decide
    have m1 : (Pi.single (1 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29) ∈
        Submodule.span (ZMod 29) (Set.range w) := by
      have h := Submodule.smul_mem (Submodule.span (ZMod 29) (Set.range w)) (18 : ZMod 29) m1'
      rwa [smul_smul, h18, one_smul] at h
    have m2' : (Pi.single (0 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29)
        + ((7:ZMod 29)^2) • (Pi.single (2 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29) ∈
        Submodule.span (ZMod 29) (Set.range w) := by
      rw [← hw2]
      exact Submodule.subset_span (Set.mem_range_self (2 : Fin 3))
    have m2sub : ((7:ZMod 29)^2) • (Pi.single (2 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29) ∈
        Submodule.span (ZMod 29) (Set.range w) := by
      have h := Submodule.sub_mem _ m2' m0
      rwa [add_sub_cancel_left] at h
    have h16 : ((16 : ZMod 29) * ((7:ZMod 29)^2)) = 1 := by decide
    have m2 : (Pi.single (2 : Fin 3) (1 : ZMod 29) : Fin 3 → ZMod 29) ∈
        Submodule.span (ZMod 29) (Set.range w) := by
      have h := Submodule.smul_mem (Submodule.span (ZMod 29) (Set.range w)) (16 : ZMod 29) m2sub
      rwa [smul_smul, h16, one_smul] at h
    refine Submodule.eq_top_iff'.mpr ?_
    intro x
    have hx : x = ∑ i : Fin 3, x i • (Pi.single i (1 : ZMod 29) : Fin 3 → ZMod 29) := by
      simpa [Pi.basisFun_repr, Pi.basisFun_apply] using
        ((Pi.basisFun (ZMod 29) (Fin 3)).sum_repr x).symm
    rw [hx]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    fin_cases i
    · simpa using Submodule.smul_mem _ (x 0) m0
    · simpa using Submodule.smul_mem _ (x 1) m1
    · simpa using Submodule.smul_mem _ (x 2) m2
  dsimp only
  exact main

end Conjectures.JoshiAbc
