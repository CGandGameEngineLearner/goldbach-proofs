import Mathlib

open Finset

theorem PEqualNP.Outside.L_goldbach_four_window_two_tail_budget
    {ι : Type} [DecidableEq ι] (s t : Finset ι) (w : ι → ℝ)
    (hts : t ⊆ s) (hw : ∀ i, 0 ≤ w i) :
    (∑ ij ∈ (s.product s).filter (fun ij => ij.1 ∈ t ∨ ij.2 ∈ t), w ij.1 * w ij.2)
      ≤ 2 * (∑ i ∈ s, w i) * (∑ i ∈ t, w i) := by
  have hprod : (∑ p ∈ s.product s, (if (p.1 ∈ t ∨ p.2 ∈ t) then w p.1 * w p.2 else 0))
      = ∑ i ∈ s, ∑ j ∈ s, (if (i ∈ t ∨ j ∈ t) then w i * w j else 0) :=
    Finset.sum_product' s s (fun a b => if (a ∈ t ∨ b ∈ t) then w a * w b else 0)
  have hkey : ∀ i ∈ s, ∀ j ∈ s,
      (if (i ∈ t ∨ j ∈ t) then w i * w j else 0)
        ≤ (if i ∈ t then w i else 0) * w j + w i * (if j ∈ t then w j else 0) := by
    intro i _ j _
    have hi : 0 ≤ w i := hw i
    have hj : 0 ≤ w j := hw j
    by_cases h1 : i ∈ t <;> by_cases h2 : j ∈ t <;> simp [h1, h2] <;> nlinarith [hi, hj]
  have hfil : s.filter (fun i => i ∈ t) = t := by
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨-, hx⟩
      exact hx
    · intro hx
      exact ⟨hts hx, hx⟩
  have hB : (∑ i ∈ s, (if i ∈ t then w i else 0)) = ∑ i ∈ t, w i := by
    rw [← Finset.sum_filter, hfil]
  have hstep : (∑ i ∈ s, ∑ j ∈ s,
        ((if i ∈ t then w i else 0) * w j + w i * (if j ∈ t then w j else 0)))
      = (∑ i ∈ s, (if i ∈ t then w i else 0)) * (∑ j ∈ s, w j)
        + (∑ i ∈ s, w i) * (∑ j ∈ s, (if j ∈ t then w j else 0)) := by
    simp only [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_mul_sum]
    · rw [Finset.sum_mul_sum]
  calc (∑ ij ∈ (s.product s).filter (fun ij => ij.1 ∈ t ∨ ij.2 ∈ t), w ij.1 * w ij.2)
      = ∑ i ∈ s, ∑ j ∈ s, (if (i ∈ t ∨ j ∈ t) then w i * w j else 0) := by
        rw [Finset.sum_filter]
        exact hprod
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
          ((if i ∈ t then w i else 0) * w j + w i * (if j ∈ t then w j else 0)) :=
        Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hkey i hi j hj))
    _ = 2 * (∑ i ∈ s, w i) * (∑ i ∈ t, w i) := by
        rw [hstep, hB]
        ring
