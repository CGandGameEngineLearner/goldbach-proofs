import Mathlib

-- child 1 zh: 六次矩上界（Hua 引理）：支撑集上相位和的六次积分至多 C M^ε N^3。
-- child 1 en: Sixth-moment bound (Hua lemma): the sixth power of the phase sum integrates to at most C M^ε N^3.
-- child 2 zh: 逐点控制：六次矩超出支撑大小平方乘二次矩的正部不超过六次矩。
-- child 2 en: Pointwise domination: the positive excess of the sixth power over N^2 times the second power is at most the sixth power itself.

open MeasureTheory

noncomputable def phaseSum (P : Polynomial ℤ) (A : Finset ℕ) (t : ℝ) : ℂ :=
  ∑ x : ↥A, Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑(P.eval (↑↑x)) * ↑t)

theorem Conjectures.Cuts.Cute6b3e900ca5ed89efa0b2966
    (h₁ : ∀ (P : Polynomial ℤ), 3 ≤ P.natDegree → ∀ (ε : ℝ), 0 < ε →
      ∃ (C : ℝ), 0 < C ∧ ∀ (M : ℕ), 2 ≤ M → ∀ (A : Finset ℕ), A ⊆ Finset.Icc 1 M →
        ∫ t in (0 : ℝ)..1, ‖phaseSum P A t‖ ^ (6 : ℕ) ≤
          C * (M : ℝ) ^ ε * (A.card : ℝ) ^ (3 : ℕ))
    (h₂ : ∀ (z : ℂ) (N : ℝ), 0 ≤ N →
      Max.max (0 : ℝ) (‖z‖ ^ (6 : ℕ) - N ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ)) ≤ ‖z‖ ^ (6 : ℕ)) :
    (have x1 : Polynomial ℤ → Finset ℕ → ℝ → ℂ := fun (x1 : Polynomial ℤ) (x2 : Finset ℕ) (x3 : ℝ) => ∑ x4 : ↥x2, Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑(Polynomial.eval (↑↑x4) x1) * ↑x3); ∀ (x2 : Polynomial ℤ), (3 : ℕ) ≤ x2.natDegree → ∀ (x4 : ℝ), (0 : ℝ) < x4 → ∃ (x6 : ℝ), (0 : ℝ) < x6 ∧ ∀ (x7 : ℕ), (2 : ℕ) ≤ x7 → ∀ x9 ⊆ Finset.Icc (1 : ℕ) x7, ∫ (x11 : ℝ) in (0 : ℝ)..(1 : ℝ), Max.max (0 : ℝ) (‖x1 x2 x9 x11‖ ^ (6 : ℕ) - ↑x9.card ^ (2 : ℕ) * ‖x1 x2 x9 x11‖ ^ (2 : ℕ)) ≤ x6 * ↑x7 ^ x4 * ↑x9.card ^ (3 : ℕ)) := by
  intro x1 P hdeg eps heps
  dsimp only [x1] at *
  obtain ⟨C, hCpos, hC⟩ := h₁ P hdeg eps heps
  refine ⟨C, hCpos, ?_⟩
  intro M hM A hA
  have hcont6 : Continuous fun t : ℝ => ‖phaseSum P A t‖ ^ (6 : ℕ) := by
    unfold phaseSum
    fun_prop
  have hcontMax : Continuous fun t : ℝ =>
      Max.max (0 : ℝ) (‖phaseSum P A t‖ ^ (6 : ℕ) - (A.card : ℝ) ^ (2 : ℕ) * ‖phaseSum P A t‖ ^ (2 : ℕ)) := by
    unfold phaseSum
    fun_prop
  have hmono :
      (∫ t in (0 : ℝ)..1,
          Max.max (0 : ℝ) (‖phaseSum P A t‖ ^ (6 : ℕ) - (A.card : ℝ) ^ (2 : ℕ) * ‖phaseSum P A t‖ ^ (2 : ℕ)))
        ≤ ∫ t in (0 : ℝ)..1, ‖phaseSum P A t‖ ^ (6 : ℕ) := by
    apply intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := (1 : ℝ)) (by norm_num)
    · exact hcontMax.intervalIntegrable 0 1
    · exact hcont6.intervalIntegrable 0 1
    · intro t _
      exact h₂ (phaseSum P A t) (A.card : ℝ) (by positivity)
  change (∫ t in (0 : ℝ)..1,
      Max.max (0 : ℝ) (‖phaseSum P A t‖ ^ (6 : ℕ) - (A.card : ℝ) ^ (2 : ℕ) * ‖phaseSum P A t‖ ^ (2 : ℕ)))
    ≤ C * (M : ℝ) ^ eps * (A.card : ℝ) ^ (3 : ℕ)
  exact le_trans hmono (hC M hM A hA)
