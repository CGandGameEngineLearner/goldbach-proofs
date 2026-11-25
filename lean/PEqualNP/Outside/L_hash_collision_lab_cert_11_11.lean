import Mathlib

/-- Order-11 occupancy support bound at load 11.

Each bucket contributes at least the discrete supporting line
`1 + 11 * load ≤ choose load 11 + 121`, which touches the binomial
coefficient at loads 11 and 12 and stays below it afterwards.
Summing this per-bucket inequality over all buckets gives the stated bound. -/
theorem PEqualNP.Outside.L_hash_collision_lab_cert_11_11 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 1) + 11 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 11) + q * 121 := by
  intro q b
  -- From load 11 on, `choose · 10` never drops below 11; the recurrence
  -- `choose (k+1) 10 = choose k 9 + choose k 10` makes this monotone.
  have hlow : ∀ k : ℕ, 11 ≤ k → 11 ≤ Nat.choose k 10 := by
    intro k hk
    refine Nat.le_induction ?low_base ?low_step k hk
    · decide
    · intro n _ ih
      have hrec : Nat.choose (n + 1) 10 = Nat.choose n 9 + Nat.choose n 10 :=
        Nat.choose_succ_succ n 9
      rw [hrec]
      omega
  -- The per-bucket supporting-line inequality.
  have hterm : ∀ m : ℕ, 1 + 11 * m ≤ Nat.choose m 11 + 121 := by
    intro m
    rcases Nat.lt_or_ge m 11 with hm | hm
    · interval_cases m <;> decide
    · refine Nat.le_induction ?term_base ?term_step m hm
      · decide
      · intro k hk ih
        have hrec : Nat.choose (k + 1) 11 = Nat.choose k 10 + Nat.choose k 11 :=
          Nat.choose_succ_succ k 10
        have h10 : 11 ≤ Nat.choose k 10 := hlow k hk
        rw [hrec]
        omega
  calc
    (q * 1) + 11 * (∑ i, b i) = ∑ i : Fin q, (1 + 11 * b i) := by
      rw [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_add_distrib]
      simp
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 11 + 121) :=
      Finset.sum_le_sum (fun i _ => hterm (b i))
    _ = (∑ i : Fin q, Nat.choose (b i) 11) + q * 121 := by
      rw [Finset.sum_add_distrib]
      simp
