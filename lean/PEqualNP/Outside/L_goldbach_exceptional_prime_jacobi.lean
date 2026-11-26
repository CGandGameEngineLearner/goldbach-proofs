import Mathlib

theorem PEqualNP.Outside.L_goldbach_exceptional_prime_jacobi :
    ∀ (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p), χ ≠ 1 → χ^2 = 1 →
      ∀ t : ZMod p, t ≠ 0 → (∑ a : ZMod p, χ a * χ (t-a)) = -χ (-1) := by
  intro p _ χ hχ hquad t ht
  have htχ : χ t * χ t = 1 := by
    rw [← sq, ← MulChar.pow_apply' χ (by decide : 2 ≠ 0), hquad, MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)]
  have hinv : χ = χ⁻¹ := eq_inv_iff_mul_eq_one.mpr (by simpa [sq] using hquad)
  calc
    _ = ∑ u : ZMod p, χ (t*u) * χ (t-t*u) :=
      (Equiv.sum_comp (Equiv.mulLeft₀ t ht) (fun a => χ a * χ (t-a))).symm
    _ = jacobiSum χ χ := by
      apply Finset.sum_congr rfl
      intro u _
      rw [show t-t*u = t*(1-u) by ring, map_mul, map_mul, mul_mul_mul_comm, htχ, one_mul]
    _ = -χ (-1) := by
      calc
        jacobiSum χ χ = jacobiSum χ χ⁻¹ := congrArg (jacobiSum χ) hinv
        _ = _ := jacobiSum_nontrivial_inv hχ
