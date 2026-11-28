import Mathlib

open MeasureTheory

-- child 1 zh: 在冻结裙边内，落入分母至多 min(Q₁, Q⁴) 的宽弧的部分，其带相位积分实部最终至少为 −εn。
-- child 1 en: On the part of the frozen skirt in a wide arc of denominator at most min(Q₁, Q⁴), the phased integral has eventual real part at least −εn.
-- child 2 zh: 在冻结裙边内，扣除上述低分母宽弧后的部分，其带相位积分实部最终至少为 −εn。
-- child 2 en: On the remaining frozen skirt outside those lower-denominator wide arcs, the phased integral has eventual real part at least −εn.
theorem GoldbachResearch.mediumSkirtModulusSplit
    (hLower : let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
      let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
      let f := fun (n : ℕ) (t : ℝ) =>
        (∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t)
      let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
      let U := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
      let H := fun n : ℕ => 256 * U n * Q n
      let A := fun (n D R : ℕ) => {t : ℝ | ∃ q a : ℕ,
        1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (R : ℝ) / ((q : ℝ) * (n : ℝ))}
      let band := fun n : ℕ => (A n (U n) (H n) \ A n (U n) (Q n)) \
        (A n (Q n) (H n) \ A n (Q n) (Q n))
      let lower := fun n : ℕ => A n (min (U n) ((Q n) ^ 4)) (H n)
      ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤
        (intervalIntegral ((band n ∩ lower n).indicator (f n)) (0 : ℝ) 1 MeasureTheory.volume).re)
    (hUpper : let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
      let E := fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
      let f := fun (n : ℕ) (t : ℝ) =>
        (∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t)) ^ 2 * E (-(n : ℝ) * t)
      let Q := fun n : ℕ => (Nat.log 2 (n + 2)) ^ 2
      let U := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
      let H := fun n : ℕ => 256 * U n * Q n
      let A := fun (n D R : ℕ) => {t : ℝ | ∃ q a : ℕ,
        1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧
          |t - (a : ℝ) / (q : ℝ)| ≤ (R : ℝ) / ((q : ℝ) * (n : ℝ))}
      let band := fun n : ℕ => (A n (U n) (H n) \ A n (U n) (Q n)) \
        (A n (Q n) (H n) \ A n (Q n) (Q n))
      let lower := fun n : ℕ => A n (min (U n) ((Q n) ^ 4)) (H n)
      ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤
        (intervalIntegral ((band n \ lower n).indicator (f n)) (0 : ℝ) 1 MeasureTheory.volume).re) :
    (let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let midArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let remSkirt := fun n : ℕ => intervalIntegral (fun t => ((wideArcs n \ midArcs n) \ (lowWideArcs n \ arcs n)).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume; ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n : ℝ)) ≤ (remSkirt n).re) := by
  intro w E S Q arcs f U H midArcs wideArcs lowWideArcs remSkirt
  let A (n D R : ℕ) : Set ℝ := {t : ℝ | ∃ q a : ℕ,
    1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t - (a : ℝ) / q| ≤ (R : ℝ) / ((q : ℝ) * (n : ℝ))}
  let band (n : ℕ) := (A n (U n) (H n) \ A n (U n) (Q n)) \
    (A n (Q n) (H n) \ A n (Q n) (Q n))
  let lower (n : ℕ) := A n (min (U n) ((Q n) ^ 4)) (H n)
  let J (n : ℕ) (B : Set ℝ) :=
    (intervalIntegral (B.indicator (f n)) (0 : ℝ) 1 volume).re
  change (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    -(e * (n : ℝ)) ≤ J n (band n ∩ lower n)) at hLower
  change (∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    -(e * (n : ℝ)) ≤ J n (band n \ lower n)) at hUpper
  change ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
    -(e * (n : ℝ)) ≤ J n (band n)
  have hm (n D R : ℕ) : MeasurableSet (A n D R) := by
    have hUnion : A n D R = ⋃ q : ℕ, ⋃ a : ℕ,
        {t : ℝ | 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧ Nat.Coprime a q} ∩
        {t : ℝ | |t - (a : ℝ) / q| ≤ (R : ℝ) / ((q : ℝ) * (n : ℝ))} := by
      ext t
      simp only [A, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, and_assoc]
    rw [hUnion]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a =>
      (MeasurableSet.const _).inter (measurableSet_le (by fun_prop) (by fun_prop))
  have hPart (n : ℕ) : J n (band n) = J n (band n ∩ lower n) + J n (band n \ lower n) := by
    have hBand : MeasurableSet (band n) :=
      ((hm _ _ _).diff (hm _ _ _)).diff ((hm _ _ _).diff (hm _ _ _))
    have hLowerMeas : MeasurableSet (lower n) := hm _ _ _
    have hf : Continuous (f n) := by
      dsimp only [f, S, E]
      fun_prop
    have hIntegrable (B : Set ℝ) (hB : MeasurableSet B) :
        IntervalIntegrable (B.indicator (f n)) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact ((hf.intervalIntegrable (μ := volume) 0 1).1).indicator hB
    have hSplit : (band n).indicator (f n) =
        (band n ∩ lower n).indicator (f n) + (band n \ lower n).indicator (f n) := by
      classical
      funext t
      by_cases hb : t ∈ band n <;> by_cases hl : t ∈ lower n <;>
        simp [Set.indicator, hb, hl]
    unfold J
    rw [hSplit]
    exact congrArg Complex.re (intervalIntegral.integral_add
      (hIntegrable _ (hBand.inter hLowerMeas)) (hIntegrable _ (hBand.diff hLowerMeas)))
  intro e he
  obtain ⟨M, hM⟩ := hLower (e / 2) (by positivity)
  obtain ⟨N, hN⟩ := hUpper (e / 2) (by positivity)
  refine ⟨max M N, fun n hn hEven => ?_⟩
  rw [hPart]
  have h₁ := hM n ((le_max_left M N).trans hn) hEven
  have h₂ := hN n ((le_max_right M N).trans hn) hEven
  linarith only [h₁, h₂]
