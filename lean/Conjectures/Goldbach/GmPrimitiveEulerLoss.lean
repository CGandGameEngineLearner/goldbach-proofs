import Mathlib
import PEqualNP.Outside.L_goldbach_finite_fixed_nonunit_mangoldt

/-!
Credit: the non-coprime von Mangoldt mass bound used below comes from the accepted module
`PEqualNP.Outside.L_goldbach_finite_fixed_nonunit_mangoldt`; the per-term estimate follows the
pattern of the accepted module `PEqualNP.Outside.L_goldbach_primitive_induced_discrepancy`.
-/

namespace Conjectures.Goldbach.GmPrimitiveEulerLoss_aux

private lemma noncoprime_Icc_le (q N : ℕ) (hq : 1 ≤ q) (hN : 1 ≤ N) :
    (∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q),
      ArithmeticFunction.vonMangoldt n) ≤ (q.primeFactors.card : ℝ) * Real.log (N : ℝ) := by
  have h := PEqualNP.Outside.L_goldbach_finite_fixed_nonunit_mangoldt q N hq hN
  have hsub : (Finset.Icc 1 N).filter (fun n => ¬ Nat.Coprime n q) ⊆
      (Finset.range (N + 1)).filter (fun n => ¬ Nat.Coprime n q) := by
    intro n hn
    obtain ⟨hn1, hbad⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := Finset.mem_Icc.mp hn1; omega), hbad⟩
  calc
    _ ≤ ∑ n ∈ (Finset.range (N + 1)).filter (fun n => ¬ Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    _ ≤ _ := h

end Conjectures.Goldbach.GmPrimitiveEulerLoss_aux

theorem Conjectures.Goldbach.GmPrimitiveEulerLoss :
    ∀ (q d : ℕ) [NeZero q] [NeZero d] (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ d), d ∣ q → (∀ n : ℕ, Nat.Coprime n q → χ (n : ZMod q) = χ' (n : ZMod d)) → ∀ x : ℝ, 1 ≤ x → ‖(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) - (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ' (n : ZMod d))‖ ≤ (q.primeFactors.card : ℝ) * Real.log x := by
  intro q d _ _ χ χ' _ hagree x hx
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hN1 : 1 ≤ ⌊x⌋₊ := by
    exact_mod_cast (Nat.le_floor (by linarith : (1 : ℝ) ≤ x))
  have estimate (n : ℕ) :
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) - χ' (n : ZMod d))‖ ≤
        if ¬ Nat.Coprime n q then ArithmeticFunction.vonMangoldt n else 0 := by
    by_cases hc : Nat.Coprime n q
    · have heq : χ (n : ZMod q) = χ' (n : ZMod d) := hagree n hc
      simp [heq, hc]
    · have hz : χ (n : ZMod q) = 0 := by
        simpa using (χ.apply_eq_zero_iff (n : ℤ)).2
          (fun h => hc (Nat.isCoprime_iff_coprime.mp h))
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      rw [ite_eq_left hc, hz, zero_sub, norm_mul, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg hΛ]
      calc
        _ ≤ ArithmeticFunction.vonMangoldt n * 1 := by
          gcongr
          exact χ'.norm_le_one _
        _ = _ := by ring
  have hdiff :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) -
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ' (n : ZMod d)) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) - χ' (n : ZMod d)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => by ring)
  rw [hdiff]
  have h1 : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        ‖(ArithmeticFunction.vonMangoldt n : ℂ) * (χ (n : ZMod q) - χ' (n : ZMod d))‖) ≤
      ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => ¬ Nat.Coprime n q),
        ArithmeticFunction.vonMangoldt n := by
    calc
      _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          (if ¬ Nat.Coprime n q then ArithmeticFunction.vonMangoldt n else 0) :=
        Finset.sum_le_sum (fun n _ => estimate n)
      _ = _ := (Finset.sum_filter _ _).symm
  refine (norm_sum_le _ _).trans (h1.trans ?_)
  refine (Conjectures.Goldbach.GmPrimitiveEulerLoss_aux.noncoprime_Icc_le q ⌊x⌋₊ hq1 hN1).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.log_le_log (by exact_mod_cast hN1) (Nat.floor_le (by linarith)))
    (Nat.cast_nonneg _)
