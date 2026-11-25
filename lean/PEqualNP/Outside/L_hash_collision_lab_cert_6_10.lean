import Mathlib

theorem PEqualNP.Outside.L_hash_collision_lab_cert_6_10
    (q : ℕ) (b : Fin q → ℕ) :
    q * 210 + 252 * (∑ i, b i) ≤
      (∑ i, Nat.choose (b i) 6) + q * 2520 := by
  have hsingle (n : ℕ) : 210 + 252 * n ≤ Nat.choose n 6 + 2520 := by
    have hlarge (m : ℕ) (hm : 10 ≤ m) :
        252 * m ≤ Nat.choose m 6 + 2310 := by
      induction m, hm using Nat.le_induction with
      | base => norm_num [Nat.choose]
      | succ k hk ih =>
          have hchoose : 252 ≤ Nat.choose k 5 := by
            calc
              252 = Nat.choose 10 5 := by norm_num [Nat.choose]
              _ ≤ Nat.choose k 5 := Nat.choose_le_choose 5 hk
          have hstep :
              252 * k + 252 ≤ Nat.choose k 6 + 2310 + Nat.choose k 5 := by
            omega
          calc
            252 * (k + 1) = 252 * k + 252 := by omega
            _ ≤ Nat.choose k 6 + 2310 + Nat.choose k 5 := hstep
            _ = Nat.choose (k + 1) 6 + 2310 := by
              rw [Nat.choose_succ_succ]
              rw [show Nat.succ 5 = 6 from rfl]
              omega
    by_cases hn : n ≤ 10
    · interval_cases n <;> norm_num [Nat.choose]
    · have h := hlarge n (by omega)
      omega
  have hsum :
      (∑ i : Fin q, (210 + 252 * b i)) ≤
        ∑ i : Fin q, (Nat.choose (b i) 6 + 2520) :=
    Finset.sum_le_sum (fun i _ => hsingle (b i))
  simpa [Finset.sum_add_distrib, Finset.mul_sum] using hsum
