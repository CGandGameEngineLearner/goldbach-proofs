import Mathlib

/-- Order-13 occupancy support bound at load 13.

Each bucket contributes at least the discrete supporting line
`1 + 13 * load ≤ choose load 13 + 169`, which touches the binomial
coefficient at load 13 and stays below it afterwards. Monotonicity of
`choose · 12` beyond load 13 drives the induction step. Summing this
per-bucket inequality over all buckets gives the stated bound. -/
theorem PEqualNP.Outside.L_hash_collision_lab_cert_13_13 :
    ∀ (q : ℕ) (b : Fin q → ℕ),
      (q * 1) + 13 * (∑ i, b i) ≤ (∑ i, Nat.choose (b i) 13) + q * 169 := by
  intro q b
  -- From load 13 on, `choose · 12` never drops below 13; the recurrence
  -- `choose (k+1) 12 = choose k 11 + choose k 12` makes this monotone.
  have hlow : ∀ k : ℕ, 13 ≤ k → 13 ≤ Nat.choose k 12 := by
    intro k hk
    refine Nat.le_induction ?low_base ?low_step k hk
    · decide
    · intro n _ ih
      have hrec : Nat.choose (n + 1) 12 = Nat.choose n 11 + Nat.choose n 12 :=
        Nat.choose_succ_succ n 11
      rw [hrec]
      omega
  -- The per-bucket supporting-line inequality.
  have hterm : ∀ m : ℕ, 1 + 13 * m ≤ Nat.choose m 13 + 169 := by
    intro m
    rcases Nat.lt_or_ge m 13 with hm | hm
    · interval_cases m <;> decide
    · refine Nat.le_induction ?term_base ?term_step m hm
      · decide
      · intro k hk ih
        have hrec : Nat.choose (k + 1) 13 = Nat.choose k 12 + Nat.choose k 13 :=
          Nat.choose_succ_succ k 12
        have h12 : 13 ≤ Nat.choose k 12 := hlow k hk
        rw [hrec]
        omega
  calc
    (q * 1) + 13 * (∑ i, b i) = ∑ i : Fin q, (1 + 13 * b i) := by
      rw [Finset.mul_sum]
      conv_rhs => rw [Finset.sum_add_distrib]
      simp
    _ ≤ ∑ i : Fin q, (Nat.choose (b i) 13 + 169) :=
      Finset.sum_le_sum (fun i _ => hterm (b i))
    _ = (∑ i : Fin q, Nat.choose (b i) 13) + q * 169 := by
      rw [Finset.sum_add_distrib]
      simp
