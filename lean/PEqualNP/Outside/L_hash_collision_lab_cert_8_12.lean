import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_8_12
    (q : ℕ) (b : Fin q → ℕ) :
    q * 495 + 792 * (∑ i, b i) ≤
      (∑ i, Nat.choose (b i) 8) + q * 9504 := by
  have hsingle (n : ℕ) : 495 + 792 * n ≤ Nat.choose n 8 + 9504 := by
    have hlarge (m : ℕ) (hm : 12 ≤ m) :
        792 * m ≤ Nat.choose m 8 + 9009 := by
      induction m, hm using Nat.le_induction with
      | base => norm_num [Nat.choose]
      | succ k hk ih =>
          have hchoose : 792 ≤ Nat.choose k 7 := by
            calc
              792 = Nat.choose 12 7 := by norm_num [Nat.choose]
              _ ≤ Nat.choose k 7 := Nat.choose_le_choose 7 hk
          have hstep :
              792 * k + 792 ≤ Nat.choose k 8 + 9009 + Nat.choose k 7 := by
            omega
          calc
            792 * (k + 1) = 792 * k + 792 := by omega
            _ ≤ Nat.choose k 8 + 9009 + Nat.choose k 7 := hstep
            _ = Nat.choose (k + 1) 8 + 9009 := by
              rw [Nat.choose_succ_succ]
              omega
    by_cases hn : n ≤ 12
    · interval_cases n <;> norm_num [Nat.choose]
    · have h := hlarge n (by omega)
      omega
  have hsum :
      (∑ i : Fin q, (495 + 792 * b i)) ≤
        ∑ i : Fin q, (Nat.choose (b i) 8 + 9504) :=
    Finset.sum_le_sum (fun i _ => hsingle (b i))
  simpa [Finset.sum_add_distrib, Finset.mul_sum] using hsum
