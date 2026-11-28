import Mathlib

theorem Conjectures.Cuts.Taskbd367fa3aeb676e8acffa6f7 : (have x1 : Finset ℕ := {(1 : ℕ), (5 : ℕ), (11 : ℕ), (13 : ℕ), (17 : ℕ)}; have x2 : ℕ → ℕ → ℕ := fun (x2 x3 : ℕ) => {x4 ∈ Finset.range ((18 : ℕ) * x3) | x4 % (18 : ℕ) ∈ x1 ∧ (x2 % (18 : ℕ) + (18 : ℕ) - x4 % (18 : ℕ)) % (18 : ℕ) ∈ x1}.card; ∀ (x3 x4 : ℕ), Even x3 → x4 ≤ x2 x3 x4 ∧ x2 x3 x4 = x4 * x2 x3 (1 : ℕ)) := by
  classical
  dsimp only
  intro N K hN
  let A : Finset ℕ := {1, 5, 11, 13, 17}
  let count : ℕ → ℕ := fun k => ((Finset.range (18 * k)).filter
    (fun x => x % 18 ∈ A ∧ (N % 18 + 18 - x % 18) % 18 ∈ A)).card
  change K ≤ count K ∧ count K = K * count 1
  have hstep (k : ℕ) : count (k + 1) = count k + count 1 := by
    simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.mul_add,
      Nat.mul_one, Finset.sum_range_add]
    apply congrArg (fun t : ℕ => (∑ x ∈ Finset.range (18 * k),
      if x % 18 ∈ A ∧ (N % 18 + 18 - x % 18) % 18 ∈ A then 1 else 0) + t)
    apply Finset.sum_congr rfl
    intro r hr
    simp [Nat.add_mod]
  have hcount (k : ℕ) : count k = k * count 1 := by
    induction k with
    | zero => simp [count]
    | succ k ih =>
      rw [hstep, ih, Nat.add_mul, one_mul]
  have hpositive : 1 ≤ count 1 := by
    have heven : (N % 18) % 2 = 0 := by
      obtain ⟨t, ht⟩ := hN
      omega
    have hfinite : ∀ r : ℕ, r < 18 → r % 2 = 0 →
        1 ≤ ((Finset.range 18).filter
          (fun x => x % 18 ∈ A ∧ (r + 18 - x % 18) % 18 ∈ A)).card := by
      intro r hr he
      interval_cases r <;> norm_num at he <;> decide
    simpa only [count, Nat.mul_one] using
      hfinite (N % 18) (Nat.mod_lt N (by decide)) heven
  constructor
  · rw [hcount]
    simpa using Nat.mul_le_mul_left K hpositive
  · exact hcount K
