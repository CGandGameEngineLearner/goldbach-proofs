import Mathlib
import Conjectures.Goldbach.ExceptionFourSeventhsCountingBridge

/-!
# Minor-arc negative energy: complete complex energy, then the negative part

The sibling cut on the same bridge module keeps the major-arc floor as a premise and asks for the
minor-arc mean square directly in the windowed, trimmed form the bridge consumes. This cut removes
the major-arc input and instead separates the analytic content of the minor-arc step into two
independent propositions:

* premise 1: the **complete** complex energy of the coarse coefficient over the whole dyadic window
  `[X, 2X]` -- no real part, no `Even` filter, no sign trimming -- is `O(X^(18/7+eps))`;
* premise 2: over that window, the squared **negative part** of the same coefficient on the even
  targets is dominated by the complete complex energy plus the same `X^(18/7+eps)` budget
  (Cauchy-Schwarz `(max 0 (-re z))^2 ≤ ‖z‖^2` summed, with the even sub-window controlled by the
  window itself).

Both are statements about one single integral coefficient `x7 n = ∫_0^1 1_{arcs n} f n`; the split is
pointwise in `n` and needs no input on the major arcs. The combination substitutes premise 1 into
premise 2, so the parent's `O(X^(18/7+eps))` constant is `C₂(C₁+1)`, and the exponents agree because
both premises use `18/7 + eps` with the same `eps`.
-/

-- child 1 zh: 完整复能量：对每个 eps>0，粗系数在二进窗口 [X,2X] 上的完整复系数模平方和不超过常数乘以 X 的 18/7+eps 次幂；不取实部、不筛偶数、不截掉正值部分。
-- child 1 en: Complete complex energy: for every eps>0 the squared moduli of the coarse coefficient, summed over the whole dyadic window [X,2X], are at most a constant times X^(18/7+eps); no real part, no Even filter and no trimming of the positive part.
-- child 2 zh: 负能量归约：对每个 eps>0，同一窗口上偶数目标的负部平方和不超过常数乘以（完整复能量 + X 的 18/7+eps 次幂）。
-- child 2 en: Negative-part reduction: for every eps>0 the squared negative part on the even targets of the same window is at most a constant times the complete complex energy plus X^(18/7+eps).

set_option maxHeartbeats 1000000 in
theorem Conjectures.Cuts.Cut39823c707ccf500689b833a3
    (h₁ : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (x6 x8) x9).re; ∀ (e : ℝ), (0 : ℝ) < e → ∃ (C : ℝ) (N : ℕ), (0 : ℝ) < C ∧ ∀ (X : ℕ), N ≤ X → ∑ n ∈ Finset.Icc X ((2 : ℕ) * X), ‖x7 n‖ ^ (2 : ℕ) ≤ C * (↑X : ℝ) ^ ((18 / 7 : ℝ) + e)))
    (h₂ : (have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (x6 x8) x9).re; ∀ (e : ℝ), (0 : ℝ) < e → ∃ (C : ℝ), (0 : ℝ) < C ∧ ∀ (X : ℕ), ∑ n ∈ Finset.Icc X ((2 : ℕ) * X) with Even n, Max.max (0 : ℝ) (-x8 n) ^ (2 : ℕ) ≤ C * (∑ n ∈ Finset.Icc X ((2 : ℕ) * X), ‖x7 n‖ ^ (2 : ℕ) + (↑X : ℝ) ^ ((18 / 7 : ℝ) + e))))
    : have x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ); have x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I); have x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) => ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5); have x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ); have x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧ x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}; have x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7); have x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (x6 x8) x9).re; ∀ (x9 : ℝ), (0 : ℝ) < x9 → ∃ (x11 : ℝ) (x12 : ℕ), (0 : ℝ) < x11 ∧ ∀ (x13 : ℕ), x12 ≤ x13 → ∑ x15 ∈ Finset.Icc x13 ((2 : ℕ) * x13) with Even x15, Max.max (0 : ℝ) (-x8 x15) ^ (2 : ℕ) ≤ x11 * (↑x13 : ℝ) ^ ((18 / 7 : ℝ) + x9) := by
  classical
  -- Reuse the statement's own abbreviations, so that the hypotheses, the goal and the estimates
  -- below speak of the same integral coefficient.
  let x1 : ℕ → ℝ := fun (x1 : ℕ) => if Nat.Prime x1 then Real.log (↑x1 : ℝ) else (0 : ℝ)
  let x2 : ℝ → ℂ := fun (x2 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x2) : ℂ) * Complex.I)
  let x3 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x3 : ℕ) (x4 : ℕ → ℝ) (x5 : ℝ) =>
    ∑ x6 ∈ Finset.range (x3 + (1 : ℕ)), (↑(x4 x6) : ℂ) * x2 ((↑x6 : ℝ) * x5)
  let x4 : ℕ → ℕ := fun (x4 : ℕ) => Nat.log (2 : ℕ) (x4 + (2 : ℕ)) ^ (2 : ℕ)
  let x5 : ℕ → Set ℝ := fun (x5 : ℕ) => {x6 : ℝ | ∃ (x7 : ℕ) (x8 : ℕ), (1 : ℕ) ≤ x7 ∧ x7 ≤ x4 x5 ∧
    x8 ≤ x7 ∧ x8.Coprime x7 ∧ |x6 - (↑x8 : ℝ) / (↑x7 : ℝ)| ≤ (↑(x4 x5) : ℝ) / ((↑x7 : ℝ) * (↑x5 : ℝ))}
  let x6 : ℕ → ℝ → ℂ := fun (x6 : ℕ) (x7 : ℝ) => x3 x6 x1 x7 ^ (2 : ℕ) * x2 (-(↑x6 : ℝ) * x7)
  let x7 : ℕ → ℂ := fun (x7 : ℕ) => ∫ (x8 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x7).indicator (x6 x7) x8
  let x8 : ℕ → ℝ := fun (x8 : ℕ) =>
    (∫ (x9 : ℝ) in (0 : ℝ)..(1 : ℝ), (x5 x8)ᶜ.indicator (x6 x8) x9).re
  change ∀ (e : ℝ), (0 : ℝ) < e → ∃ (C : ℝ) (N : ℕ), (0 : ℝ) < C ∧
    ∀ (X : ℕ), N ≤ X → ∑ n ∈ Finset.Icc X ((2 : ℕ) * X) with Even n,
      Max.max (0 : ℝ) (-x8 n) ^ (2 : ℕ) ≤ C * (↑X : ℝ) ^ ((18 / 7 : ℝ) + e)
  intro e he
  obtain ⟨C₁, N₁, hC₁, hEnergy⟩ := h₁ e he
  obtain ⟨C₂, hC₂, hReduce⟩ := h₂ e he
  refine ⟨C₂ * (C₁ + 1), N₁, by positivity, fun X hX => ?_⟩
  -- Substitute the complete energy bound into the negative-part reduction.
  have hstep : (∑ n ∈ Finset.Icc X ((2 : ℕ) * X), ‖x7 n‖ ^ (2 : ℕ)) + (↑X : ℝ) ^ ((18 / 7 : ℝ) + e)
      ≤ (C₁ + 1) * (↑X : ℝ) ^ ((18 / 7 : ℝ) + e) := by
    have := hEnergy X hX
    linarith
  calc ∑ n ∈ Finset.Icc X ((2 : ℕ) * X) with Even n,
        Max.max (0 : ℝ) (-x8 n) ^ (2 : ℕ)
      ≤ C₂ * ((∑ n ∈ Finset.Icc X ((2 : ℕ) * X), ‖x7 n‖ ^ (2 : ℕ)) +
          (↑X : ℝ) ^ ((18 / 7 : ℝ) + e)) := hReduce X
    _ ≤ C₂ * ((C₁ + 1) * (↑X : ℝ) ^ ((18 / 7 : ℝ) + e)) :=
        mul_le_mul_of_nonneg_left hstep hC₂.le
    _ = (C₂ * (C₁ + 1)) * (↑X : ℝ) ^ ((18 / 7 : ℝ) + e) := by ring
