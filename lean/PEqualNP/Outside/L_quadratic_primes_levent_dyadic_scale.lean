import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_dyadic_scale :
    let psi := fun (q a x : ℕ) => ∑ n ∈ (Finset.Icc 1 x).filter (fun n => n % q = a % q),
      ArithmeticFunction.vonMangoldt n
    ∀ (E : ℕ → ℝ) (x : ℕ),
      |psi 4 1 x - (x : ℝ) / 2| ≤ E x →
      |psi 4 1 (2 * x) - (2 * x : ℕ) / (2 : ℝ)| ≤ E (2 * x) →
      |(psi 4 1 (2 * x) - psi 4 1 x) - (x : ℝ) / 2| ≤ E (2 * x) + E x := by
  intro E x h1 h2
  have hx2 : ((2 * x : ℕ) : ℝ) = 2 * (x : ℝ) := by push_cast; ring
  have hx : ((2 * x : ℕ) : ℝ) / (2 : ℝ) = (x : ℝ) := by rw [hx2]; ring
  rw [hx] at h2
  have key : (psi 4 1 (2 * x) - psi 4 1 x) - (x : ℝ) / 2 =
      (psi 4 1 (2 * x) - (x : ℝ)) - (psi 4 1 x - (x : ℝ) / 2) := by ring
  rw [key]
  have hle : |(psi 4 1 (2 * x) - (x : ℝ)) - (psi 4 1 x - (x : ℝ) / 2)| ≤
      |psi 4 1 (2 * x) - (x : ℝ)| + |psi 4 1 x - (x : ℝ) / 2| := by
    simpa using abs_add (psi 4 1 (2 * x) - (x : ℝ)) (-(psi 4 1 x - (x : ℝ) / 2))
  linarith
