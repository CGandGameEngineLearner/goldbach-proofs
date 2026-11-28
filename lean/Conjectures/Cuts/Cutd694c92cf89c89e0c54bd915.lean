import Mathlib

-- child 1 zh: Meissel–Mertens 常数 M₀ = γ + Σ_p (log(1−1/p) + 1/p) 落在闭区间 [0.261497, 0.261498] 内。
-- child 1 en: The Meissel–Mertens constant M₀ lies in the closed interval [0.261497, 0.261498].
-- child 2 zh: 对区间 [2, e^10] 上的每个实数 x，素数倒数和相对 log log x + M₀ 满足带显式误差项的双边界。
-- child 2 en: For every real x in [2, e^10] the prime reciprocal sum obeys the explicit two-sided bound relative to log log x + M₀.

theorem Conjectures.Cuts.Cutd694c92cf89c89e0c54bd915
    (h₁ : let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); (0.261497 ≤ M0 ∧ M0 ≤ 0.261498))
    (h₂ : let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp 10 → Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + (if Real.log x > 8.9 then (1.614e-3 : ℝ) else (1 : ℝ))) :
    (let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ)); (0.261497 ≤ M0 ∧ M0 ≤ 0.261498) ∧ ∀ x : ℝ, 2 ≤ x → x ≤ Real.exp 10 → Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧ (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤ Real.log (Real.log x) + M0 + (if Real.log x > 8.9 then (1.614e-3 : ℝ) else (1 : ℝ))) := by
  dsimp only
  exact ⟨h₁, h₂⟩
