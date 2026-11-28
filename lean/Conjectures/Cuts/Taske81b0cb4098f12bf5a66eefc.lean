import Mathlib

/-!
Premise 2/4 of a cut of L-goldbach-window-moving-prime-center.

The elements `x2 ≤ x1` with `2 * x2 ^ 4 ≤ x1 ^ 3` are exactly the elements of
`range (min x1 (x1 ^ 3 / 2).sqrt.sqrt + 1)`:

* `Nat.le_div_iff_mul_le` turns `2 * x2 ^ 4 ≤ x1 ^ 3` into `x2 ^ 4 ≤ x1 ^ 3 / 2`;
* two applications of `Nat.le_sqrt'` turn `x2 ≤ (x1 ^ 3 / 2).sqrt.sqrt` into
  `(x2 ^ 2) ^ 2 = x2 ^ 4 ≤ x1 ^ 3 / 2`.

The bound `x2 ≤ x1` is supplied on the left by membership in `range (x1 + 1)` and on the right
by the `min`.  Self-contained: Mathlib only, no auxiliary declarations.
-/

theorem Conjectures.Cuts.Taske81b0cb4098f12bf5a66eefc :
    ∀ (x1 : ℕ), {x2 ∈ Finset.range (x1 + (1 : ℕ)) | (2 : ℕ) * x2 ^ (4 : ℕ) ≤ x1 ^ (3 : ℕ)} = Finset.range (Min.min x1 (x1 ^ (3 : ℕ) / (2 : ℕ)).sqrt.sqrt + (1 : ℕ)) := by
  intro x1
  ext x2
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hx1, hle⟩
    have hdiv : x2 ^ (4 : ℕ) ≤ x1 ^ (3 : ℕ) / (2 : ℕ) :=
      (Nat.le_div_iff_mul_le (by norm_num)).mpr (by linarith)
    have hsq : x2 ^ (2 : ℕ) ≤ (x1 ^ (3 : ℕ) / (2 : ℕ)).sqrt := by
      rw [Nat.le_sqrt']
      have : x2 ^ (4 : ℕ) = (x2 ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      omega
    have hsqrt : x2 ≤ (x1 ^ (3 : ℕ) / (2 : ℕ)).sqrt.sqrt := Nat.le_sqrt'.mpr hsq
    have hmin : x2 ≤ Min.min x1 (x1 ^ (3 : ℕ) / (2 : ℕ)).sqrt.sqrt :=
      le_min (by omega) hsqrt
    omega
  · intro h
    have hmin : x2 ≤ Min.min x1 (x1 ^ (3 : ℕ) / (2 : ℕ)).sqrt.sqrt := by omega
    have hx1 : x2 ≤ x1 := le_trans hmin (min_le_left _ _)
    have hsqrt : x2 ≤ (x1 ^ (3 : ℕ) / (2 : ℕ)).sqrt.sqrt := le_trans hmin (min_le_right _ _)
    have hsq : x2 ^ (2 : ℕ) ≤ (x1 ^ (3 : ℕ) / (2 : ℕ)).sqrt := Nat.le_sqrt'.mp hsqrt
    have hdiv : x2 ^ (4 : ℕ) ≤ x1 ^ (3 : ℕ) / (2 : ℕ) := by
      have : x2 ^ (4 : ℕ) = (x2 ^ (2 : ℕ)) ^ (2 : ℕ) := by ring
      rw [this]
      exact Nat.le_sqrt'.mp hsq
    have hmul : x2 ^ (4 : ℕ) * (2 : ℕ) ≤ x1 ^ (3 : ℕ) :=
      (Nat.le_div_iff_mul_le (by norm_num)).mp hdiv
    have hle : (2 : ℕ) * x2 ^ (4 : ℕ) ≤ x1 ^ (3 : ℕ) := by
      have : (2 : ℕ) * x2 ^ (4 : ℕ) = x2 ^ (4 : ℕ) * (2 : ℕ) := by ring
      omega
    exact ⟨by omega, hle⟩
