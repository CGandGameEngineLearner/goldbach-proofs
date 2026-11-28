import Mathlib

-- child 1 zh: 独立证明中区间内倒数素数和的显式下界。
-- child 1 en: Prove the explicit lower reciprocal-prime bound on the mid-range.
-- child 2 zh: 独立证明中区间内倒数素数和的显式上界。
-- child 2 en: Prove the explicit upper reciprocal-prime bound on the mid-range.

theorem Conjectures.Cuts.Cut4d6274e0106f84ce7a8891de
    (h₁ : let M0 : ℝ := Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ));
      ∀ x : ℝ, Real.exp 10 < x → x ≤ (10 : ℝ) ^ 12 →
        Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤
          ∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ))
    (h₂ : let M0 : ℝ := Real.eulerMascheroniConstant +
        ∑' p : Nat.Primes, (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ));
      ∀ x : ℝ, Real.exp 10 < x → x ≤ (10 : ℝ) ^ 12 →
        (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
          Real.log (Real.log x) + M0 + 2 / (Real.sqrt x * Real.log x)) :
    (let M0 : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes,
      (Real.log (1 - 1 / (p.1 : ℝ)) + 1 / (p.1 : ℝ));
    ∀ x : ℝ, Real.exp 10 < x → x ≤ (10 : ℝ) ^ 12 →
      Real.log (Real.log x) + M0 - (2.964e-6 : ℝ) / Real.log x ≤
        (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ∧
      (∑ p ∈ (Finset.range (Nat.ceil x)).filter Nat.Prime, (1 : ℝ) / (p : ℝ)) ≤
        Real.log (Real.log x) + M0 + 2 / (Real.sqrt x * Real.log x)) := by
  dsimp only at h₁ h₂ ⊢
  intro x hx hupper
  exact ⟨h₁ x hx hupper, h₂ x hx hupper⟩
