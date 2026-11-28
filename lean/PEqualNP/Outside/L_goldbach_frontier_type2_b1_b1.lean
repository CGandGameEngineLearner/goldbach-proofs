import Mathlib

namespace PEqualNP.Outside

/-- Type-II cell (1,1): deep-minor integral of τ₁ × τ₁ is o(n). -/
theorem goldbach_frontier_type2_b1_b1 :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t))
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2
    let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊
    let H := fun n : ℕ => 256 * Q₁ n * Q n
    let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}
    let Λ := ArithmeticFunction.vonMangoldt
    let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ)
    let U := fun n : ℕ => ⌊(n:ℝ)^(1/16:ℝ)⌋₊
    let B₁ := fun n : ℕ => ⌊(n:ℝ)^(1/4:ℝ)⌋₊
    let τ₁ := fun (n m : ℕ) => ∑ a ∈ (Nat.divisors m).filter (fun a => U n < a ∧ a ≤ B₁ n ∧ U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a)
    let Jdeep := fun (n : ℕ) (u v : ℕ → ℝ) => intervalIntegral (fun t => (wideArcs n)ᶜ.indicator (fun x => S n u x * S n v x * E (-(n:ℝ)*x)) t) (0:ℝ) 1 MeasureTheory.volume
    ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ‖Jdeep n (τ₁ n) (τ₁ n)‖ ≤ e * (n : ℝ) := by
  sorry

end PEqualNP.Outside
