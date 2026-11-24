import Mathlib.Data.Nat.Factorization.Basic

theorem PEqualNP.Outside.L_quadratic_primes_middle_simple :
    ∀ p n : ℕ, Nat.Prime p → p ∣ n ^ 2 + 1 → n ^ 2 + 1 < p ^ 2 →
      (n ^ 2 + 1).factorization p = 1 := by
  intro p n hp hdiv hlt
  have hn0 : n ^ 2 + 1 ≠ 0 := by
    exact Nat.succ_ne_zero _
  have hfacpos : 1 ≤ (n ^ 2 + 1).factorization p :=
    (hp.dvd_iff_one_le_factorization hn0).mp hdiv
  have hfacle : (n ^ 2 + 1).factorization p ≤ 1 := by
    by_contra hnot
    have hltfac : 1 < (n ^ 2 + 1).factorization p := Nat.lt_of_not_ge hnot
    have htwo : 2 ≤ (n ^ 2 + 1).factorization p := hltfac
    have hp2dvd : p ^ 2 ∣ n ^ 2 + 1 :=
      (hp.pow_dvd_iff_le_factorization hn0).2 htwo
    have hp2le : p ^ 2 ≤ n ^ 2 + 1 := Nat.le_of_dvd (Nat.zero_lt_succ _) hp2dvd
    exact (Nat.not_lt_of_ge hp2le) hlt
  exact Nat.le_antisymm hfacle hfacpos
