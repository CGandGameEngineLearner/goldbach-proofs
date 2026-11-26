import Mathlib.Basic.Complex.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp

namespace PEqualNP.Outside

open Finset

/- The elementary inverse-character Jacobi identity below is adapted from
Mathlib.NumberTheory.JacobiSum.Basic.jacobiSum_nontrivial_inv, Mathlib revision
fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
Copyright (c) 2024 Michael Stoll; released under the Apache 2.0 license.
Its proof is reproduced here to keep the dependency closure elementary. -/
private theorem inverse_character_sum (p : ℕ) [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    (∑ x : ZMod p, χ x * χ⁻¹ (1 - x)) = -χ (-1) := by
  classical
  conv => enter [1, 2, x]; rw [MulChar.inv_apply', ← map_mul, ← div_eq_mul_inv]
  rw [sum_eq_sum_sdiff_singleton_add (mem_univ (1 : ZMod p)), sub_self,
    div_zero, χ.map_zero, add_zero]
  have : ∑ x ∈ univ \ {1}, χ (x / (1 - x)) = ∑ x ∈ univ \ {-1}, χ x := by
    refine sum_bij' (fun a _ ↦ a / (1 - a)) (fun b _ ↦ b / (1 + b)) (fun x hx ↦ ?_)
      (fun y hy ↦ ?_) (fun x hx ↦ ?_) (fun y hy ↦ ?_) (fun _ _ ↦ rfl)
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx ⊢
      rw [div_eq_iff <| sub_ne_zero.mpr ((ne_eq ..).symm ▸ hx).symm, mul_sub, mul_one,
        neg_one_mul, sub_neg_eq_add, right_eq_add, neg_eq_zero]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy ⊢
      rw [div_eq_iff fun h ↦ hy <| eq_neg_of_add_eq_zero_right h, one_mul, right_eq_add]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx
      rw [eq_comm, ← sub_eq_zero] at hx
      simp [field]
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy
      rw [eq_comm, neg_eq_iff_eq_neg, ← sub_eq_zero, sub_neg_eq_add] at hy
      simp [field]
  rw [this, ← add_eq_zero_iff_eq_neg, ← sum_eq_sum_sdiff_singleton_add (mem_univ (-1 : ZMod p))]
  exact MulChar.sum_eq_zero_of_ne_one hχ

theorem L_goldbach_exceptional_prime_jacobi :
    ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p), χ ≠ 1 → χ^2 = 1 → ∀ t : ZMod p, t ≠ 0 → (∑ a : ZMod p, χ a * χ (t-a)) = -χ (-1) := by
  intro p hp χ hχ hχ₂ t ht
  classical
  have hinv : χ⁻¹ = χ :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hχ₂)
  have hsq : χ t * χ t = 1 := by
    rw [← pow_two, ← MulChar.pow_apply' χ two_ne_zero, hχ₂]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)
  calc
    (∑ a : ZMod p, χ a * χ (t - a)) =
        ∑ u : ZMod p, χ (t * u) * χ (t - t * u) :=
      (Equiv.sum_comp (Equiv.mulLeft₀ t ht) _).symm
    _ = ∑ u : ZMod p, χ u * χ (1 - u) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [show t - t * u = t * (1 - u) by rw [mul_sub, mul_one], map_mul, map_mul]
      calc
        χ t * χ u * (χ t * χ (1 - u)) =
            (χ t * χ t) * (χ u * χ (1 - u)) := by ac_rfl
        _ = χ u * χ (1 - u) := by rw [hsq, one_mul]
    _ = -χ (-1) := by
      simpa only [hinv] using inverse_character_sum p χ hχ

end PEqualNP.Outside
