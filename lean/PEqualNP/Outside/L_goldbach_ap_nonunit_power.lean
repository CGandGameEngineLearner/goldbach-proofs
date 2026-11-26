import Mathlib

theorem PEqualNP.Outside.L_goldbach_ap_nonunit_power :
    ∀ q k : ℕ, ¬ Nat.Coprime k q → ArithmeticFunction.vonMangoldt k ≠ 0 →
      ∃ p j : ℕ, Nat.Prime p ∧ p ∣ q ∧ 0 < j ∧ k = p ^ j := by
  intro q k hnc hvm
  obtain ⟨p, j, hp, hj, hpow⟩ :=
    (isPrimePow_nat_iff k).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hvm)
  refine ⟨p, j, hp, (hp.dvd_iff_not_coprime).2 ?_, hj, hpow.symm⟩
  intro hc
  apply hnc
  rw [← hpow]
  exact (Nat.coprime_pow_left_iff hj p q).2 hc
