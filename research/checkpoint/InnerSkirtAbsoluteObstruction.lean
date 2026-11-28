import Mathlib

/-- Absolute model mass along an unbounded sequence of even targets. -/
noncomputable def InnerSkirtAbsoluteObstruction : Prop :=
  let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
  let Q (n : ℕ) := (Nat.log 2 (n + 2)) ^ 2
  let width (n q : ℕ) := (Q n : ℝ) / ((q : ℝ) * n)
  let K (n : ℕ) (β : ℝ) := ∑ k ∈ Finset.range (n + 1), E ((k : ℝ) * β)
  let ram (q h : ℕ) := ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), E ((h : ℝ) * a / q)
  let kernelMass (n : ℕ) (b : ℝ) := intervalIntegral (fun β => ‖K n β‖ ^ 2) (-b) b MeasureTheory.volume
  let mass (n q : ℕ) := kernelMass n (width n q * (n : ℝ)^(1/6 : ℝ)) - kernelMass n (width n q)
  let tail (n : ℕ) := ∑ q ∈ Finset.Icc (Q n + 1) (Nat.floor ((n : ℝ)^(1/3 : ℝ))), ‖(ram q 1 / (q.totient : ℂ))^2 * (starRingEnd ℂ) (ram q n)‖ * mass n q
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ Even n ∧ c * (n : ℝ) ≤ tail n
