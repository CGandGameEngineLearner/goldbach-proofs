import Mathlib

open RCLike

theorem PEqualNP.Outside.L_quadratic_primes_levent_finite_polarization :
    ∀ (S : Finset ℕ) (u v : ℕ → ℂ),
      (∑ k ∈ S, ‖u k + v k‖ ^ 2) - (∑ k ∈ S, ‖u k - v k‖ ^ 2) =
        4 * ∑ k ∈ S, (u k * star (v k)).re := by
  intro S u v
  classical
  have hinner (a b : ℂ) : re ⟪a, b⟫ = (a * star b).re := by
    simpa only [RCLike.inner_apply] using (inner_re_symm a b)
  have hpoint (a b : ℂ) :
      ‖a + b‖ ^ 2 - ‖a - b‖ ^ 2 = 4 * (a * star b).re := by
    rw [norm_add_sq, norm_sub_sq, hinner]
    ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpoint]
  rw [← Finset.mul_sum]