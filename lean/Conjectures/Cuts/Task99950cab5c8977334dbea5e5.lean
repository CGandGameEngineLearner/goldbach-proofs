import Mathlib

namespace Goldbach.ResidueCorrelation

open Finset

private def pairWeight (w : ℕ → ℝ) (q i j : ℕ) : ℝ :=
  if i % q = j % q then w i * w j else 0

private theorem expandResidues (w : ℕ → ℝ) (X q : ℕ) (hq : 0 < q) :
    (∑ r ∈ range q, (∑ i ∈ range X with i % q = r, w i) ^ 2) =
      ∑ i ∈ range X, ∑ j ∈ range X, pairWeight w q i j := by
  let mass : ℕ → ℝ := fun r => ∑ j ∈ range X with j % q = r, w j
  calc
    _ = ∑ r ∈ range q, ∑ i ∈ range X, if i % q = r then w i * mass r else 0 := by
      refine sum_congr rfl fun r _ => ?_
      change mass r ^ 2 = _
      rw [pow_two]
      change (∑ j ∈ range X with j % q = r, w j) * mass r = _
      rw [sum_mul, sum_filter]
    _ = ∑ i ∈ range X, ∑ r ∈ range q, if i % q = r then w i * mass r else 0 :=
      sum_comm
    _ = _ := by
      refine sum_congr rfl fun i _ => ?_
      rw [sum_eq_single_of_mem (i % q) (mem_range.mpr (Nat.mod_lt i hq))]
      · rw [ite_eq_left rfl]
        unfold mass
        rw [mul_sum, sum_filter]
        refine sum_congr rfl fun j _ => ?_
        by_cases he : i % q = j % q
        · simp [pairWeight, he]
        · simp [pairWeight, he, Ne.symm he]
      · intro r _ hr
        exact ite_eq_right (Ne.symm hr)

private theorem splitSymmetric (X : ℕ) (f : ℕ → ℕ → ℝ) (hf : ∀ i j, f i j = f j i) :
    (∑ i ∈ range X, ∑ j ∈ range X, f i j) =
      (∑ i ∈ range X, f i i) + 2 * (∑ j ∈ range X, ∑ i ∈ range j, f i j) := by
  induction X with
  | zero => simp
  | succ X ih =>
      simp only [sum_range_succ, sum_add_distrib, ih]
      have h : (∑ j ∈ range X, f X j) = ∑ i ∈ range X, f i X :=
        sum_congr rfl fun i _ => hf X i
      rw [h]
      ring

private theorem strictPairs (w : ℕ → ℝ) (X q : ℕ) (hq : 0 < q) :
    (∑ j ∈ range X, ∑ i ∈ range j, pairWeight w q i j) =
      ∑ h ∈ Icc 1 ((X - 1) / q), ∑ i ∈ range (X - q * h), w i * w (i + q * h) := by
  let P := ((range X).sigma (fun j => range j)).filter
    (fun z => z.2 % q = z.1 % q)
  let D := (Icc 1 ((X - 1) / q)).sigma (fun h => range (X - q * h))
  have hrepr {j i : ℕ} (hij : i < j) (hmod : i % q = j % q) :
      q * ((j - i) / q) = j - i :=
    Nat.mul_div_cancel' ((Nat.modEq_iff_dvd' hij.le).mp hmod)
  calc
    _ = ∑ z ∈ P, w z.2 * w z.1 := by simp [P, sum_filter, sum_sigma, pairWeight]
    _ = ∑ z ∈ D, w z.2 * w (z.2 + q * z.1) := by
      symm
      refine sum_nbij' (fun z => ⟨z.2 + q * z.1, z.2⟩)
        (fun z => ⟨(z.1 - z.2) / q, z.2⟩) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨h, i⟩ hz
        obtain ⟨hh, hi⟩ := mem_sigma.mp hz
        obtain ⟨hh, _⟩ := mem_Icc.mp hh
        have hi := mem_range.mp hi
        change 1 ≤ h at hh
        change i < X - q * h at hi
        have hpos : 0 < q * h := Nat.mul_pos hq (by omega)
        have hj : i + q * h < X := by omega
        have hij : i < i + q * h := by omega
        exact mem_filter.mpr ⟨mem_sigma.mpr ⟨mem_range.mpr hj,
          mem_range.mpr hij⟩, (Nat.add_mul_mod_self_left i q h).symm⟩
      · rintro ⟨j, i⟩ hz
        obtain ⟨hP, hmod⟩ := mem_filter.mp hz
        obtain ⟨hj, hij⟩ := mem_sigma.mp hP
        have hj := mem_range.mp hj
        have hij := mem_range.mp hij
        change j < X at hj
        change i < j at hij
        change i % q = j % q at hmod
        have he := hrepr hij hmod
        have hpos : 1 ≤ (j - i) / q := by
          apply Nat.pos_of_ne_zero
          intro hz
          rw [hz, mul_zero] at he
          omega
        have hcap : (j - i) / q ≤ (X - 1) / q := (Nat.le_div_iff_mul_le hq).mpr (by
          rw [Nat.mul_comm, he]
          omega)
        have hi : i < X - q * ((j - i) / q) := by omega
        exact mem_sigma.mpr ⟨mem_Icc.mpr ⟨hpos, hcap⟩, mem_range.mpr hi⟩
      · rintro ⟨h, i⟩ _
        exact Sigma.ext (by simp [Nat.mul_div_cancel_left h hq]) (by rfl)
      · rintro ⟨j, i⟩ hz
        obtain ⟨hP, hmod⟩ := mem_filter.mp hz
        have hij := mem_range.mp (mem_sigma.mp hP).2
        change i < j at hij
        change i % q = j % q at hmod
        have he := hrepr hij hmod
        exact Sigma.ext (by change i + q * ((j - i) / q) = j; omega) (by rfl)
      · intro z _
        rfl
    _ = _ := sum_sigma ..

end Goldbach.ResidueCorrelation

open Goldbach.ResidueCorrelation in
theorem Conjectures.Cuts.Task99950cab5c8977334dbea5e5 : (have x1 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x1 : ℕ → ℝ) (x2 x3 : ℕ) => ∑ x4 ∈ Finset.range x3, (∑ x5 ∈ Finset.range x2 with x5 % x3 = x4, x1 x5) ^ (2 : ℕ); have x2 : (ℕ → ℝ) → ℕ → ℕ → ℝ := fun (x2 : ℕ → ℝ) (x3 x4 : ℕ) => ∑ x5 ∈ Finset.Icc (1 : ℕ) ((x3 - (1 : ℕ)) / x4), ∑ x6 ∈ Finset.range (x3 - x4 * x5), x2 x6 * x2 (x6 + x4 * x5); ∀ (x3 : ℕ → ℝ) (x4 x5 : ℕ), (0 : ℕ) < x5 → x1 x3 x4 x5 = ∑ x7 ∈ Finset.range x4, x3 x7 ^ (2 : ℕ) + (2 : ℝ) * x2 x3 x4 x5) := by
  intro residues corr w X q hq
  dsimp only [residues, corr]
  rw [expandResidues w X q hq]
  rw [splitSymmetric X (pairWeight w q) (fun i j => by
    by_cases h : i % q = j % q
    · simp [pairWeight, h, mul_comm]
    · simp [pairWeight, h, Ne.symm h])]
  rw [strictPairs w X q hq]
  simp [pairWeight, pow_two]
