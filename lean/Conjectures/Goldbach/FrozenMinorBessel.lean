import Mathlib

open scoped BigOperators
open MeasureTheory

namespace Conjectures.Goldbach.FrozenMinorBessel_aux

/-- Finite Bessel step: for a continuous `H` and a measurable mask `A`, the number of
integer frequencies in `F` whose masked Fourier coefficient of `H^2` has real part `≤ -T`,
times `T^2`, is bounded by the `L^4` energy of `H` on `A`. -/
theorem key (H : ℝ → ℂ) (hH : Continuous H) (A : Set ℝ) (hA : MeasurableSet A)
    (F : Finset ℤ) (T : ℝ) (hT : 0 < T) :
    (((F.filter fun j =>
          (fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1)
            (A.indicator (fun t => H t ^ 2)) j).re ≤ -T).card : ℝ) * T ^ 2)
      ≤ intervalIntegral (A.indicator (fun t => ‖H t‖ ^ 4)) 0 1 MeasureTheory.volume := by
  have hab : (0 : ℝ) < 1 := zero_lt_one
  have hsignal : Continuous (fun t : ℝ => H t ^ 2) := by fun_prop
  have hLp : MemLp (A.indicator (fun t : ℝ => H t ^ 2)) 2
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    refine MemLp.indicator hA.nullMeasurableSet ?_
    rw [memLp_two_iff_integrable_sq_norm hsignal.aestronglyMeasurable]
    exact ((hsignal.norm.pow 2).intervalIntegrable 0 1).1
  have henergy (t : ℝ) :
      ‖A.indicator (fun s : ℝ => H s ^ 2) t‖ ^ 2
        = A.indicator (fun s : ℝ => ‖H s‖ ^ 4) t := by
    by_cases ht : t ∈ A
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, norm_pow, ← pow_mul]
    · simp [Set.indicator, ht]
  set S : Finset ℤ :=
    F.filter fun j =>
      (fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j).re ≤ -T with hSdef
  have hstep : ∀ j ∈ S, T ^ 2 ≤ ‖fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j‖ ^ 2 := by
    intro j hj
    have hre : (fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j).re ≤ -T := by
      rw [hSdef] at hj; exact (Finset.mem_filter.mp hj).2
    have habs : T ≤ |(fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j).re| := by
      rw [abs_of_nonpos (by linarith)]; linarith
    have hn : |(fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j).re|
        ≤ ‖fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j‖ :=
      Complex.abs_re_le_norm _
    nlinarith [mul_self_le_mul_self hT.le (habs.trans hn)]
  have hBessel : ∑ j ∈ F, ‖fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j‖ ^ 2
      ≤ intervalIntegral (fun x => ‖A.indicator (fun t : ℝ => H t ^ 2) x‖ ^ 2) 0 1 volume := by
    have h := sum_le_hasSum F (fun i _ => sq_nonneg _)
      (hasSum_sq_fourierCoeffOn hab hLp)
    simpa using h
  have hcard : ((S.card : ℝ) * T ^ 2) = ∑ j ∈ S, T ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hsubS : S ⊆ F := by
    rw [hSdef]
    exact Finset.filter_subset _ _
  have hsub : ∑ j ∈ S, ‖fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j‖ ^ 2
      ≤ ∑ j ∈ F, ‖fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubS (fun i _ _ => sq_nonneg _)
  calc ((S.card : ℝ) * T ^ 2) = ∑ j ∈ S, T ^ 2 := hcard
    _ ≤ ∑ j ∈ S, ‖fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j‖ ^ 2 :=
        Finset.sum_le_sum hstep
    _ ≤ ∑ j ∈ F, ‖fourierCoeffOn hab (A.indicator (fun t : ℝ => H t ^ 2)) j‖ ^ 2 := hsub
    _ ≤ intervalIntegral (fun x => ‖A.indicator (fun t : ℝ => H t ^ 2) x‖ ^ 2) 0 1 volume := hBessel
    _ = intervalIntegral (A.indicator (fun t => ‖H t‖ ^ 4)) 0 1 MeasureTheory.volume := by
        apply intervalIntegral.integral_congr
        intro t _
        exact henergy t

end Conjectures.Goldbach.FrozenMinorBessel_aux

theorem Conjectures.Goldbach.FrozenMinorBessel :
∀ (x : ℕ) (b : ℕ → ℝ) (A : Set ℝ), MeasurableSet A → let H := fun t : ℝ => ∑ k ∈ Finset.range (x+1), (b k : ℂ) * Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I); let f := A.indicator (fun t => H t ^ 2); let c := fun j : ℤ => fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) f j; ∀ (F : Finset ℤ) (T : ℝ), 0 < T → (((F.filter fun j => (c j).re ≤ -T).card : ℝ) * T ^ 2) ≤ intervalIntegral (A.indicator (fun t => ‖H t‖^4)) 0 1 MeasureTheory.volume := by
  intro x b A hA H f c F T hT
  refine Conjectures.Goldbach.FrozenMinorBessel_aux.key
    (fun t : ℝ => ∑ k ∈ Finset.range (x + 1), (b k : ℂ) *
      Complex.exp (((2 * Real.pi * ((k : ℝ) * t) : ℝ) : ℂ) * Complex.I)) ?_ A hA F T hT
  fun_prop
