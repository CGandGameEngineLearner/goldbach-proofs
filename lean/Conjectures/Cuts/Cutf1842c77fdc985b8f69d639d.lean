import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

set_option autoImplicit false

open scoped BigOperators Filter Topology

noncomputable section

/-!
# Cut for `L-twin-primes-window-surplus`

Reduces the frozen statement

  `∀ K B, ∃ X > B, K * e X < M X`

to two independent, closed premises:

* **child 1** — the twin part of the gap-two window has a positive lower bound
  along infinitely many scales;
* **child 2** — the error term `e X = log(2+X)^3 / sqrt X` is eventually below
  any prescribed positive multiple.

The already verified module `SharpWindowContamination` bounds the complementary
part `Epart`, and `M = Epart + Twin` is an elementary filter decomposition.
-/

theorem Conjectures.Cuts.Cutf1842c77fdc985b8f69d639d
    (h₁ : ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧
      c ≤ (((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)).filter
            (fun n => n.Prime ∧ (n+2).Prime)).sum
          (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) / (X : ℝ))
    (h₂ : ∀ C : ℝ, 0 < C → ∀ K : ℝ, ∃ B₀ : ℕ, ∀ X : ℕ, B₀ ≤ X →
      K * (Real.log (2+(X:ℝ))^3 / Real.sqrt X) < C) :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) := by
  -- 取出已证的污染界
  obtain ⟨C, hC, hbound⟩ := Conjectures.TwinPrimes.SharpWindowContamination
  obtain ⟨c, hc, hTwin⟩ := h₁
  -- 用 show 显式展开 let，再 intro
  show ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧
    K * (Real.log (2+(X:ℝ))^3 / Real.sqrt X) <
      (((Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)).sum
        (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))) / (X:ℝ)
  intro Kk Bb
  obtain ⟨B₀, hB₀⟩ := h₂ c hc Kk
  obtain ⟨X, hXB, hXc⟩ := hTwin (max Bb B₀)
  have hB' : Bb < X := lt_of_le_of_lt (le_max_left _ _) hXB
  have hX0 : B₀ ≤ X := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hXB)
  have hK : Kk * (Real.log (2+(X:ℝ))^3 / Real.sqrt X) < c := hB₀ X hX0
  refine ⟨X, hB', ?_⟩
  -- M = Epart + Twin
  set S := (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X) with hS
  set f := (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2)) with hf
  set P := (fun n => n.Prime ∧ (n+2).Prime) with hP
  have hT : ∑ n ∈ S, f n = ∑ n ∈ S.filter P, f n + ∑ n ∈ S.filter (fun n => ¬ P n), f n :=
    (Finset.sum_filter_add_sum_filter_not S P f).symm
  have hsplit : (∑ n ∈ S, f n) / (X:ℝ)
      = (∑ n ∈ S.filter (fun n => ¬ P n), f n) / (X:ℝ) + (∑ n ∈ S.filter P, f n) / (X:ℝ) := by
    rw [hT, add_div]
    ring_nf
  have hE0 : 0 ≤ (∑ n ∈ S.filter (fun n => ¬ P n), f n) / (X:ℝ) := by
    apply div_nonneg _ (Nat.cast_nonneg X)
    apply Finset.sum_nonneg
    intro n _
    apply mul_nonneg <;> exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg
  linarith [hsplit]
