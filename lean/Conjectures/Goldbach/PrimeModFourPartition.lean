import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
A small exact bridge needed when translating arithmetic-progressions estimates
at modulus four into the modulus two and modulus one cases.
-/

namespace Conjectures.Goldbach

/-- Every odd residue is exactly one of the two odd classes modulo four. -/
theorem odd_class_split (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 2 = 1), f k) =
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 4 = 1), f k) +
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 4 = 3), f k) := by
  classical
  simp only [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h1 : k % 4 = 1
  · have hodd : k % 2 = 1 := by omega
    have h3 : k % 4 ≠ 3 := by omega
    simp [h1, hodd]
  · by_cases h3 : k % 4 = 3
    · have hodd : k % 2 = 1 := by omega
      simp [h3, hodd]
    · have heven : k % 2 ≠ 1 := by omega
      simp [h1, h3, heven]

/-- Any real-valued weight supported on primes splits into the two odd
    residue classes and the exceptional prime two. -/
theorem PrimeModFourPartition (f : ℕ → ℝ)
    (hf : ∀ k : ℕ, ¬ k.Prime → f k = 0) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), f k) =
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 4 = 1), f k) +
      (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k % 4 = 3), f k) +
      (if 2 ≤ n then f 2 else 0) := by
  classical
  have hsplit (k : ℕ) :
      f k = (if k % 4 = 1 then f k else 0) +
        (if k % 4 = 3 then f k else 0) + (if k = 2 then f k else 0) := by
    by_cases hp : k.Prime
    · rcases hp.eq_two_or_odd with h2 | hodd
      · subst k
        norm_num
      · have hr : k % 4 = 1 ∨ k % 4 = 3 := by omega
        rcases hr with h1 | h3
        · have h3 : k % 4 ≠ 3 := by omega
          have h2 : k ≠ 2 := by omega
          simp [h1, h2]
        · have h1 : k % 4 ≠ 1 := by omega
          have h2 : k ≠ 2 := by omega
          simp [h3, h2]
    · simp [hf k hp]
  calc
    (∑ k ∈ Finset.range (n + 1), f k) =
      ∑ k ∈ Finset.range (n + 1),
        ((if k % 4 = 1 then f k else 0) +
        (if k % 4 = 3 then f k else 0) + (if k = 2 then f k else 0)) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hsplit k
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp [Finset.sum_ite_eq', Finset.mem_range, Nat.lt_add_one_iff]
      split_ifs <;> simp

end Conjectures.Goldbach
