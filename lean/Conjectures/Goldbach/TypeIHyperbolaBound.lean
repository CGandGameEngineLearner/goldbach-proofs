import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Positivity

/-!
Type I estimate with an exact product cutoff and a separate resonant case.
The geometric-series argument follows Montgomery and Vaughan,
Multiplicative Number Theory II, Lemma 16.4, pp. 5-6:
https://personal.science.psu.edu/rcv4/Vol2/Vol2.pdf
Only the two-ended bound 2 / norm(1 - exp(2 pi i x)) is needed here.
-/


namespace TypeIGeometric

/-- A length-`H` geometric prefix on the unit circle is bounded by either its
trivial length bound or the two-ended distance-to-one estimate. -/
theorem geom_prefix_norm_le (z : ℂ) (H : ℕ) (hz : ‖z‖ = 1) :
    ‖∑ j ∈ Finset.range H, z ^ (j + 1)‖ ≤
      if z = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - z‖) := by
  split_ifs with hz1
  · subst z
    simp
  · refine le_min ?_ ?_
    · calc
        ‖∑ j ∈ Finset.range H, z ^ (j + 1)‖
            ≤ ∑ j ∈ Finset.range H, ‖z ^ (j + 1)‖ := norm_sum_le _ _
        _ = ∑ _j ∈ Finset.range H, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _hj
          simp [norm_pow, hz]
        _ = (H : ℝ) := by simp
    · have hsub : 1 - z ≠ 0 := by
        intro h
        apply hz1
        linear_combination -h
      have hden : 0 < ‖1 - z‖ := norm_pos_iff.mpr hsub
      have hshift :
          (∑ j ∈ Finset.range H, z ^ (j + 1)) =
            z * ∑ j ∈ Finset.range H, z ^ j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [pow_succ]
        ring
      have hgeom := geom_sum_mul_neg z H
      have hprod :
          (∑ j ∈ Finset.range H, z ^ (j + 1)) * (1 - z) =
            z - z ^ (H + 1) := by
        rw [hshift, mul_assoc, hgeom, mul_sub, mul_one, pow_succ]
        ring
      have hnum : ‖z - z ^ (H + 1)‖ ≤ 2 := by
        calc
          ‖z - z ^ (H + 1)‖ ≤ ‖z‖ + ‖z ^ (H + 1)‖ := norm_sub_le _ _
          _ = 2 := by
            rw [norm_pow, hz, one_pow]
            norm_num
      apply (le_div_iff₀ hden).mpr
      calc
        ‖∑ j ∈ Finset.range H, z ^ (j + 1)‖ * ‖1 - z‖
            = ‖(∑ j ∈ Finset.range H, z ^ (j + 1)) * (1 - z)‖ := by
              rw [norm_mul]
        _ = ‖z - z ^ (H + 1)‖ := by rw [hprod]
        _ ≤ 2 := hnum

end TypeIGeometric


namespace TypeIProof

noncomputable def E (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

theorem norm_E (x : ℝ) : ‖E x‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem E_nat_mul (x : ℝ) (k : ℕ) : E ((k : ℝ)*x) = (E x)^k := by
  dsimp only [E]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem row_as_geom (d H : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.Icc 1 H, E ((d : ℝ)*(k : ℝ)*t)) =
      ∑ j ∈ Finset.range H, (E ((d : ℝ)*t))^(j+1) := by
  refine Finset.sum_bij' (fun k _ => k-1) (fun j _ => j+1) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    exact Finset.mem_range.mpr (by omega)
  · intro j hj
    have := Finset.mem_range.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  · intro k hk
    have := (Finset.mem_Icc.mp hk).1
    omega
  · intro j hj
    omega
  · intro k hk
    have hk1 := (Finset.mem_Icc.mp hk).1
    have hsub : k-1+1=k := by omega
    rw [hsub, ← E_nat_mul]
    congr 1
    ring

end TypeIProof

theorem Conjectures.Goldbach.TypeIHyperbolaBound :
    let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let cap (H : ℕ) (x : ℝ) := if E x = 1 then (H : ℝ) else min (H : ℝ) (2 / ‖1 - E x‖); ∀ (N D : ℕ) (a : ℕ → ℂ) (t : ℝ), ‖∑ d ∈ Finset.Icc 1 D, a d * ∑ k ∈ Finset.Icc 1 (N / d), E ((d : ℝ) * (k : ℝ) * t)‖ ≤ ∑ d ∈ Finset.Icc 1 D, ‖a d‖ * cap (N / d) ((d : ℝ) * t) := by
  intro E cap N D a t
  have hrow (d : ℕ) :
      ‖∑ k ∈ Finset.Icc 1 (N/d), E ((d : ℝ)*(k : ℝ)*t)‖ ≤ cap (N/d) ((d : ℝ)*t) := by
    change ‖∑ k ∈ Finset.Icc 1 (N/d), TypeIProof.E ((d : ℝ)*(k : ℝ)*t)‖ ≤
      if TypeIProof.E ((d : ℝ)*t)=1 then ((N/d : ℕ) : ℝ)
      else min ((N/d : ℕ) : ℝ) (2/‖1-TypeIProof.E ((d : ℝ)*t)‖)
    rw [TypeIProof.row_as_geom]
    exact TypeIGeometric.geom_prefix_norm_le _ _ (TypeIProof.norm_E _)
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 D,
        ‖a d * ∑ k ∈ Finset.Icc 1 (N/d), E ((d : ℝ)*(k : ℝ)*t)‖ := norm_sum_le _ _
    _ = ∑ d ∈ Finset.Icc 1 D,
        ‖a d‖ * ‖∑ k ∈ Finset.Icc 1 (N/d), E ((d : ℝ)*(k : ℝ)*t)‖ := by
      apply Finset.sum_congr rfl
      intro d _
      exact norm_mul _ _
    _ ≤ _ := Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left (hrow d) (norm_nonneg _))
