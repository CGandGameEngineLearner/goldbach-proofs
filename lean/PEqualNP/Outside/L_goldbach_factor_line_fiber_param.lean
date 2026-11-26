import Mathlib.Data.Int.GCD
import Mathlib.Tactic.LinearCombination

theorem PEqualNP.Outside.L_goldbach_factor_line_fiber_param :
    ∀ (a b N r₀ s₀ : ℤ), 0 < a → 0 < b → a*r₀+b*s₀=N → let g := (Int.gcd a b : ℤ); ∀ r s : ℤ, a*r+b*s=N ↔ ∃ j : ℤ, r=r₀+(b/g)*j ∧ s=s₀-(a/g)*j := by
  intro a b N r₀ s₀ ha _ h₀
  let g : ℤ := Int.gcd a b
  change ∀ r s : ℤ, a*r+b*s=N ↔ ∃ j : ℤ, r=r₀+(b/g)*j ∧ s=s₀-(a/g)*j
  have hg : g ≠ 0 := Int.natCast_ne_zero.mpr (Int.gcd_ne_zero_left (Int.ne_of_gt ha))
  have hA : g * (a/g) = a := by
    rw [mul_comm]; exact Int.ediv_mul_cancel (Int.gcd_dvd_left ..)
  have hB : g * (b/g) = b := by
    rw [mul_comm]; exact Int.ediv_mul_cancel (Int.gcd_dvd_right ..)
  have bez : g = a * Int.gcdA a b + b * Int.gcdB a b := Int.gcd_eq_gcd_ab a b
  intro r s
  constructor
  · intro h
    let j := Int.gcdB a b * (r-r₀) - Int.gcdA a b * (s-s₀)
    refine ⟨j, ?_, ?_⟩
    · apply Int.eq_of_mul_eq_mul_left hg
      rw [mul_add, ← mul_assoc g (b/g) j, hB, bez]
      dsimp [j]
      linear_combination (Int.gcdA a b) * (h - h₀)
    · apply Int.eq_of_mul_eq_mul_left hg
      rw [mul_sub, ← mul_assoc g (a/g) j, hA, bez]
      dsimp [j]
      linear_combination (Int.gcdB a b) * (h - h₀)
  · rintro ⟨j, rfl, rfl⟩
    have hcross : a*(b/g) = b*(a/g) := calc
      a*(b/g) = (g*(a/g))*(b/g) := congrArg (fun z => z*(b/g)) hA.symm
      _ = (g*(b/g))*(a/g) := by ac_rfl
      _ = b*(a/g) := by rw [hB]
    linear_combination h₀ + j * hcross
