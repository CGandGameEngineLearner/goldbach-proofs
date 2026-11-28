import Mathlib

theorem Conjectures.Cuts.Task21cd5496761c30c2261477a2 : (∀ (x1 x2 : ℕ), ∑ x3 ∈ Finset.Ico x1 ((2 : ℕ) * x1), {x4 ∈ Finset.Icc (1 : ℕ) (x2 / (2 : ℕ)) | Nat.Prime (x3 - (2 : ℕ) ^ x4)}.card * {x4 ∈ Finset.Icc (x2 / (2 : ℕ) + (1 : ℕ)) x2 | Nat.Prime (x3 - (2 : ℕ) ^ x4)}.card = ∑ x3 ∈ Finset.Icc (1 : ℕ) (x2 / (2 : ℕ)), ∑ x4 ∈ Finset.Icc (x2 / (2 : ℕ) + (1 : ℕ)) x2, {x5 ∈ Finset.Ico x1 ((2 : ℕ) * x1) | Nat.Prime (x5 - (2 : ℕ) ^ x3) ∧ Nat.Prime (x5 - (2 : ℕ) ^ x4)}.card) := by
  classical
  intro X L
  -- Expand each filtered cardinality as a sum of indicators.
  have cardfilt : ∀ (s : Finset ℕ) (p : ℕ → Prop) [DecidablePred p],
      (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
    intro s p _
    have h : (s.filter p).card = ∑ x ∈ s.filter p, (1 : ℕ) := by
      rw [Finset.sum_const]; simp
    rw [h, Finset.sum_filter]
  -- Expand a product of two finite sums into a double sum.
  have mulsum : ∀ (A B : Finset ℕ) (f g : ℕ → ℕ),
      (∑ a ∈ A, f a) * (∑ b ∈ B, g b) = ∑ a ∈ A, ∑ b ∈ B, f a * g b := by
    intro A B f g
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.mul_sum B g (f a)
  -- The pointwise product of indicators is the indicator of the conjunction.
  have andmul : ∀ (m a b : ℕ),
      (if Nat.Prime (m - 2 ^ a) then (1 : ℕ) else 0) *
        (if Nat.Prime (m - 2 ^ b) then (1 : ℕ) else 0)
        = if Nat.Prime (m - 2 ^ a) ∧ Nat.Prime (m - 2 ^ b) then (1 : ℕ) else 0 := by
    intro m a b
    by_cases h1 : Nat.Prime (m - 2 ^ a) <;> by_cases h2 : Nat.Prime (m - 2 ^ b) <;>
      simp [h1, h2]
  -- The LHS is the triple sum over (m, a, b) of the joint indicator.
  have lhs :
      ∑ m ∈ Finset.Ico X (2 * X),
        {a ∈ Finset.Icc 1 (L / 2) | Nat.Prime (m - 2 ^ a)}.card *
          {b ∈ Finset.Icc (L / 2 + 1) L | Nat.Prime (m - 2 ^ b)}.card
      = ∑ m ∈ Finset.Ico X (2 * X),
          ∑ a ∈ Finset.Icc 1 (L / 2), ∑ b ∈ Finset.Icc (L / 2 + 1) L,
            (if Nat.Prime (m - 2 ^ a) ∧ Nat.Prime (m - 2 ^ b) then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [cardfilt (Finset.Icc 1 (L / 2)) (fun a => Nat.Prime (m - 2 ^ a)),
      cardfilt (Finset.Icc (L / 2 + 1) L) (fun b => Nat.Prime (m - 2 ^ b)), mulsum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => andmul m a b
  -- The RHS is the same triple sum.
  have rhs :
      ∑ a ∈ Finset.Icc 1 (L / 2), ∑ b ∈ Finset.Icc (L / 2 + 1) L,
          {m ∈ Finset.Ico X (2 * X) | Nat.Prime (m - 2 ^ a) ∧ Nat.Prime (m - 2 ^ b)}.card
      = ∑ a ∈ Finset.Icc 1 (L / 2), ∑ b ∈ Finset.Icc (L / 2 + 1) L,
          ∑ m ∈ Finset.Ico X (2 * X),
            (if Nat.Prime (m - 2 ^ a) ∧ Nat.Prime (m - 2 ^ b) then (1 : ℕ) else 0) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    exact cardfilt _ _
  -- Exchange summation order twice: (m, a, b) → (a, m, b) → (a, b, m).
  have swap : ∀ (f : ℕ → ℕ → ℕ → ℕ),
      ∑ m ∈ Finset.Ico X (2 * X), ∑ a ∈ Finset.Icc 1 (L / 2),
        ∑ b ∈ Finset.Icc (L / 2 + 1) L, f m a b
      = ∑ a ∈ Finset.Icc 1 (L / 2), ∑ b ∈ Finset.Icc (L / 2 + 1) L,
          ∑ m ∈ Finset.Ico X (2 * X), f m a b := by
    intro f
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [lhs, rhs]
  exact swap _
