import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

open Finset MeasureTheory
open scoped ComplexConjugate
namespace RationalArcReflection

def arcs (Q : ℕ) (radius : ℕ → ℝ) : Set ℝ :=
  {t | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ a.Coprime q ∧
    |t - (a:ℝ)/q| ≤ radius q}

private theorem reflect_mem {Q r t} (ht : t ∈ arcs Q r) : 1-t ∈ arcs Q r := by
  obtain ⟨q,a,hq,hQ,ha,hc,hr⟩ := ht
  refine ⟨q,q-a,hq,hQ,Nat.sub_le _ _,(Nat.coprime_self_sub_left ha).2 hc,?_⟩
  rw [Nat.cast_sub ha]
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  rw [show 1-t-((q:ℝ)-a)/q = -(t-(a:ℝ)/q) by field_simp; ring, abs_neg]
  exact hr

noncomputable def phase (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
noncomputable def exponentialSum (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ range (n+1), (u k:ℂ)*phase ((k:ℝ)*t)

private theorem phase_reflect (k : ℤ) (t : ℝ) :
    phase ((k:ℝ)*(1-t)) = conj (phase ((k:ℝ)*t)) := by
  unfold phase
  rw [← Complex.exp_conj]
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat]
  rw [show (2*(Real.pi:ℂ)*((k:ℂ)*(1-(t:ℂ))))*Complex.I =
    (k:ℂ)*(2*Real.pi*Complex.I) + 2*Real.pi*((k:ℂ)*t)*(-Complex.I) by ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

private theorem sum_reflect (n : ℕ) (u : ℕ → ℝ) (t : ℝ) :
    exponentialSum n u (1-t) = conj (exponentialSum n u t) := by
  unfold exponentialSum
  rw [map_sum]
  apply sum_congr rfl
  intro k _
  simpa using congrArg (fun z : ℂ => (u k:ℂ)*z) (phase_reflect (k:ℤ) t)

theorem imaginary_part_zero (Q n : ℕ) (r : ℕ → ℝ) (u v : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1, (arcs Q r)ᶜ.indicator
      (fun x => exponentialSum n u x * exponentialSum n v x * phase (-(n:ℝ)*x)) t).im = 0 := by
  let F := (arcs Q r)ᶜ.indicator
      (fun x => exponentialSum n u x * exponentialSum n v x * phase (-(n:ℝ)*x))
  have hf (t : ℝ) : F (1-t) = conj (F t) := by
    have hm : 1-t ∈ arcs Q r ↔ t ∈ arcs Q r :=
      ⟨fun h => by simpa using reflect_mem h, reflect_mem⟩
    by_cases ht : t ∈ arcs Q r
    · simp [F, ht, hm]
    · have hn := phase_reflect (-(n:ℤ)) t
      push_cast at hn
      simpa [F, ht, hm, sum_reflect] using congrArg
        (fun z : ℂ => conj (exponentialSum n u t) * conj (exponentialSum n v t) * z) hn
  let J := ∫ t in (0:ℝ)..1, F t
  have hJ : J = conj J := by
    calc
      J = ∫ t in (0:ℝ)..1, F (1-t) := by
        simp [J, intervalIntegral.integral_comp_sub_left]
      _ = ∫ t in (0:ℝ)..1, conj (F t) := by simp_rw [hf]
      _ = conj J := by simp [J, intervalIntegral, integral_conj]
  change J.im = 0
  have hh := congrArg Complex.im hJ
  simpa using (show J.im = 0 by simp at hh; linarith)
end RationalArcReflection


theorem Conjectures.Cuts.Task1ebcbc34ab48b907b922baf3 : (have x1 : ℝ → ℂ := fun (x1 : ℝ) => Complex.exp ((↑((2 : ℝ) * Real.pi * x1) : ℂ) * Complex.I); have x2 : ℕ → (ℕ → ℝ) → ℝ → ℂ := fun (x2 : ℕ) (x3 : ℕ → ℝ) (x4 : ℝ) => ∑ x5 ∈ Finset.range (x2 + (1 : ℕ)), (↑(x3 x5) : ℂ) * x1 ((↑x5 : ℝ) * x4); have x3 : ℕ → ℕ := fun (x3 : ℕ) => Nat.log (2 : ℕ) (x3 + (2 : ℕ)) ^ (2 : ℕ); have x4 : ℕ → ℕ := fun (x4 : ℕ) => ⌊(↑x4 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x5 : ℕ → ℕ := fun (x5 : ℕ) => (256 : ℕ) * x4 x5 * x3 x5; have x6 : ℕ → Set ℝ := fun (x6 : ℕ) => {x7 : ℝ | ∃ (x8 : ℕ) (x9 : ℕ), (1 : ℕ) ≤ x8 ∧ x8 ≤ x4 x6 ∧ x9 ≤ x8 ∧ x9.Coprime x8 ∧ |x7 - (↑x9 : ℝ) / (↑x8 : ℝ)| ≤ (↑(x5 x6) : ℝ) / ((↑x8 : ℝ) * (↑x6 : ℝ))}; have x7 : ArithmeticFunction ℝ := ArithmeticFunction.vonMangoldt; have x8 : ℕ → ℝ := fun (x8 : ℕ) => (↑((ArithmeticFunction.moebius : ℕ → ℤ) x8) : ℝ); have x9 : ℕ → ℕ := fun (x9 : ℕ) => ⌊(↑x9 : ℝ) ^ (1 / 16 : ℝ)⌋₊; have x10 : ℕ → ℕ := fun (x10 : ℕ) => ⌊(↑x10 : ℝ) ^ (1 / 4 : ℝ)⌋₊; have x11 : ℕ → ℕ := fun (x11 : ℕ) => ⌊(↑x11 : ℝ) ^ (1 / 3 : ℝ)⌋₊; have x12 : ℕ → ℕ := fun (x12 : ℕ) => ⌊(↑x12 : ℝ) ^ (2 / 3 : ℝ)⌋₊; have x13 : ℕ → ℕ → ℝ := fun (x13 x14 : ℕ) => ∑ x15 ∈ x14.divisors with x10 x13 < x15 ∧ x15 ≤ x11 x13 ∧ x9 x13 < x14 / x15, (∑ x16 ∈ x15.divisors with x9 x13 < x16, x8 x16) * (x7 : ℕ → ℝ) (x14 / x15); have x14 : ℕ → ℕ → ℝ := fun (x14 x15 : ℕ) => ∑ x16 ∈ x15.divisors with x11 x14 < x16 ∧ x16 ≤ x12 x14 ∧ x9 x14 < x15 / x16, (∑ x17 ∈ x16.divisors with x9 x14 < x17, x8 x17) * (x7 : ℕ → ℝ) (x15 / x16); have x15 : ℕ → (ℕ → ℝ) → (ℕ → ℝ) → ℂ := fun (x15 : ℕ) (x16 x17 : ℕ → ℝ) => ∫ (x18 : ℝ) in (0 : ℝ)..(1 : ℝ), (x6 x15)ᶜ.indicator (fun (x19 : ℝ) => x2 x15 x16 x19 * x2 x15 x17 x19 * x1 (-(↑x15 : ℝ) * x19)) x18; ∀ (x16 : ℝ), (0 : ℝ) < x16 → ∃ (x18 : ℕ), ∀ (x19 : ℕ), x18 ≤ x19 → Even x19 → |(x15 x19 (x13 x19) (x14 x19)).im| ≤ x16 * (↑x19 : ℝ) / (2 : ℝ)) := by
  intro E S Q Q₁ H wide Λ μ U B₁ B₂ B₃ τ₂ τ₃ J ε hε
  refine ⟨0, fun n _ _ => ?_⟩
  have hz : (J n (τ₂ n) (τ₃ n)).im = 0 :=
    RationalArcReflection.imaginary_part_zero (Q₁ n) n
      (fun q => (H n : ℝ) / ((q:ℝ)*n)) (τ₂ n) (τ₃ n)
  rw [hz, abs_zero]
  positivity
