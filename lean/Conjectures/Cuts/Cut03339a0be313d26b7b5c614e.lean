import Mathlib

-- child 1 zh: 用 Euler 乘积消去低阶项，并认证截断在素数 100 以下时的尾项。
-- child 1 en: Cancel the low-order prime contributions with Euler products and bound the tail beyond 100.
-- child 2 zh: 认证 Euler–Mascheroni 常数的数值区间。
-- child 2 en: Certify the numerical enclosure of the Euler–Mascheroni constant.
-- child 3 zh: 认证 ζ(3) 的对数的数值区间。
-- child 3 en: Certify the numerical enclosure of the logarithm of zeta at 3.
-- child 4 zh: 认证有限素数余项与 ζ(2) 对数贡献之和的数值区间。
-- child 4 en: Certify the finite prime correction together with the logarithmic zeta-at-2 contribution.

theorem Conjectures.Cuts.Cut03339a0be313d26b7b5c614e
    (tail :
      let M₀ : ℝ := Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ))
      let Z₃ : ℝ := ∑' j : ℕ, (1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ 3)
      let F (p : ℕ) : ℝ :=
        Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) -
          Real.log (1 - 1 / (p : ℝ) ^ 2) / 2 - Real.log (1 - 1 / (p : ℝ) ^ 3) / 3
      let C : ℝ := -(Real.log (Real.pi ^ 2 / 6) / 2) +
        ∑ p ∈ (Finset.range 101).filter Nat.Prime, F p
      |M₀ - (Real.eulerMascheroniConstant - Real.log Z₃ / 3 + C)| ≤ (8e-9 : ℝ))
    (gamma :
      (0.57721562 : ℝ) ≤ Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant ≤ (0.57721571 : ℝ))
    (zetaThree :
      let Z₃ : ℝ := ∑' j : ℕ, (1 : ℝ) / (((j + 1 : ℕ) : ℝ) ^ 3)
      (0.18403413 : ℝ) ≤ Real.log Z₃ ∧ Real.log Z₃ ≤ (0.18403422 : ℝ))
    (finiteCorrection :
      let F (p : ℕ) : ℝ :=
        Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) -
          Real.log (1 - 1 / (p : ℝ) ^ 2) / 2 - Real.log (1 - 1 / (p : ℝ) ^ 3) / 3
      let C : ℝ := -(Real.log (Real.pi ^ 2 / 6) / 2) +
        ∑ p ∈ (Finset.range 101).filter Nat.Prime, F p
      (-0.25437377 : ℝ) ≤ C ∧ C ≤ (-0.25437368 : ℝ)) :
    (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / ↑↑x1) + (1 : ℝ) / ↑↑x1); 0.261497 ≤ x1 ∧ x1 ≤ 0.261498) := by
  dsimp only at tail zetaThree finiteCorrection ⊢
  obtain ⟨hTailLower, hTailUpper⟩ := abs_le.mp tail
  constructor
  · linarith only [hTailLower, gamma.1, zetaThree.2, finiteCorrection.1]
  · linarith only [hTailUpper, gamma.2, zetaThree.1, finiteCorrection.2]
