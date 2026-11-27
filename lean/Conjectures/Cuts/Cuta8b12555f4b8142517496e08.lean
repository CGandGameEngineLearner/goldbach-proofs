import Mathlib
import Conjectures.TwinPrimes.SharpWindowContamination

set_option autoImplicit false

open scoped BigOperators Filter Topology

noncomputable section

/-!
# Cut for `L-twin-primes-window-surplus`

We reduce the frozen statement

  `∀ K B, ∃ X > B, K * e X < M X`

to two independent, closed premises:

* **child 1** — the twin part of the gap-two window has a positive lower bound
  along infinitely many scales;
* **child 2** — the error term `e X = log(2+X)^3 / sqrt X` is eventually below
  any prescribed positive multiple.

The already verified module `SharpWindowContamination` bounds the complementary
part `Epart`, and `M = Epart + Twin` is an elementary filter decomposition.
-/

namespace CutW

/-- The gap-two window `{X < n ∧ 50 n < 51 X}`. -/
def w (X : ℕ) : Finset ℕ := (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)

/-- Weighted gap-two sum divided by the scale. -/
def M (X : ℕ) : ℝ :=
  ((w X).sum (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))) / (X : ℝ)

/-- The power error used by the frozen statement. -/
def e (X : ℕ) : ℝ := Real.log (2+(X:ℝ))^3 / Real.sqrt X

/-- Weight of the actual twin primes in the window. -/
def Twin (X : ℕ) : ℝ :=
  (((w X).filter (fun n => n.Prime ∧ (n+2).Prime)).sum
     (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))) / (X : ℝ)

/-- Weight of the remaining indices. -/
def Epart (X : ℕ) : ℝ :=
  (((w X).filter (fun n => ¬ (n.Prime ∧ (n+2).Prime))).sum
     (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))) / (X : ℝ)

theorem M_eq (X : ℕ) : M X = Epart X + Twin X := by
  unfold M Epart Twin
  rw [← add_div, add_comm]
  congr 1
  exact (Finset.sum_filter_add_sum_filter_not (w X) (fun n => n.Prime ∧ (n+2).Prime) _).symm

theorem Epart_nonneg (X : ℕ) : 0 ≤ Epart X := by
  unfold Epart
  apply div_nonneg _ (Nat.cast_nonneg X)
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg <;> exact_mod_cast ArithmeticFunction.vonMangoldt_nonneg

/-- The verified contamination bound, restated for the local definitions. -/
theorem contamination : ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X → Epart X ≤ C * e X := by
  obtain ⟨C, hC, hb⟩ := Conjectures.TwinPrimes.SharpWindowContamination
  refine ⟨C, hC, fun X hX => ?_⟩
  have hb' := hb X hX
  simp only [w, e, Epart] at hb' ⊢
  calc _ ≤ C * Real.log (2 + (X:ℝ)) ^ 3 / Real.sqrt X := hb'
       _ = C * (Real.log (2 + (X:ℝ)) ^ 3 / Real.sqrt X) := by ring

/-- child 1 zh: 孪生部分在无穷多个尺度上具有正下界。
child 1 en: The twin part of the window has a positive lower bound along infinitely many scales. -/
def Premise1 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ B : ℕ, ∃ X : ℕ, B < X ∧ c ≤ Twin X

/-- child 2 zh: 误差项 K·e X 最终小于任意给定正数。
child 2 en: For every positive target the error term K·e X is eventually smaller. -/
def Premise2 : Prop :=
  ∀ C : ℝ, 0 < C → ∀ K : ℝ, ∃ B₀ : ℕ, ∀ X : ℕ, B₀ ≤ X → K * e X < C

theorem cut_main (h1 : Premise1) (h2 : Premise2) :
    ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X := by
  obtain ⟨c, hc, hTwin⟩ := h1
  intro K B
  obtain ⟨B₀, hB₀⟩ := h2 c hc K
  obtain ⟨X, hXB, hXc⟩ := hTwin (max B B₀)
  have hB' : B < X := lt_of_le_of_lt (le_max_left _ _) hXB
  have hX0 : B₀ ≤ X := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hXB)
  have hK : K * e X < c := hB₀ X hX0
  refine ⟨X, hB', ?_⟩
  rw [M_eq X]
  have hE0 : 0 ≤ Epart X := Epart_nonneg X
  linarith

end CutW

theorem Conjectures.Cuts.Cuta8b12555f4b8142517496e08
    (h₁ : CutW.Premise1) (h₂ : CutW.Premise2) :
    (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let v := fun (n : ℕ) => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2); let M := fun (X : ℕ) => (w X).sum v / (X : ℝ); let e := fun (X : ℕ) => Real.log (2+(X:ℝ))^3 / Real.sqrt X; ∀ (K : ℝ) (B : ℕ), ∃ X : ℕ, B < X ∧ K * e X < M X) := by
  simpa only [CutW.M, CutW.e, CutW.w] using CutW.cut_main h₁ h₂
