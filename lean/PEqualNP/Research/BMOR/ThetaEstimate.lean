import Mathlib

/-!
# The theta estimate of Bennett, Martin, O'Bryant and Rechnitzer

Reference: "Explicit bounds for primes in arithmetic progressions", Theorem 1.2,
with the upper bounds in equations (1.10) and (1.11).
https://arxiv.org/abs/1802.00085

Theorem1_2 is the proposition to be proved. The lemma below derives the
constant used by FR-7022 from an explicit hypothesis of that type.
-/

namespace BMOR

/-- Integers a are represented by their least nonnegative residue modulo q. -/
noncomputable def theta (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p % q = a % q),
    if p.Prime then Real.log p else 0

/-- Upper bound for the error coefficient from equation (1.10). -/
noncomputable def c₀ (q : ℕ) : ℝ := if q ≤ 10^4 then 1 / 840 else 1 / 160

/-- Upper bound for the starting point from equation (1.11). -/
noncomputable def x₀ (q : ℕ) : ℝ :=
  if q ≤ 10^5 then 8 * 10^9 else
    Real.exp ((3 / 100 : ℝ) * Real.sqrt q * (Real.log q)^3)

/-- Numerical statement of Theorem 1.2. The witnesses depend only on q.
The paper additionally tabulates sharper witnesses for small q. -/
def Theorem1_2 : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∃ c xStart : ℝ,
    0 < c ∧ c ≤ c₀ q ∧ 0 < xStart ∧ xStart ≤ x₀ q ∧
    ∀ a : ℕ, a < q → a.Coprime q → ∀ x : ℝ, xStart ≤ x →
      |theta q a x - x / q.totient| < c * (x / Real.log x)

/-- Specialization to the moduli used by FR-7022, retaining the paper's real x. -/
theorem small_moduli (h : Theorem1_2) {q a : ℕ} (hq : 3 ≤ q) (hq' : q ≤ 105)
    (ha : a < q) (hc : a.Coprime q) {x : ℝ} (hx : 8 * 10^9 ≤ x) :
    |theta q a x - x / q.totient| < x / (840 * Real.log x) := by
  obtain ⟨c, xStart, _, hcoef, _, hstart, hest⟩ := h q hq
  simp only [c₀, show q ≤ 10^4 by omega, ↓reduceIte] at hcoef
  simp only [x₀, show q ≤ 10^5 by omega, ↓reduceIte] at hstart
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  calc
    _ < c * (x / Real.log x) := hest a ha hc x (hstart.trans hx)
    _ ≤ (1 / 840) * (x / Real.log x) := mul_le_mul_of_nonneg_right hcoef
      (div_nonneg (by linarith) hlog.le)
    _ = x / (840 * Real.log x) := by ring

end BMOR
