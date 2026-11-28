import PEqualNP.Research.BMOR.ThetaEstimate
import PEqualNP.Research.BMOR.PrimeError
import PEqualNP.Research.BMOR.PrimePowerError

namespace BMOR

private theorem theta_nat (q a n : ℕ) :
    PEqualNP.Outside.FixedAP.theta q a n = theta q a n := by
  unfold PEqualNP.Outside.FixedAP.theta theta
  rw [Nat.floor_natCast]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k.Prime <;> simp [hk, ArithmeticFunction.vonMangoldt_apply_prime]

/-- The published theta estimate suffices for the bound of FR-7022, including
moduli 1 and 2. The conclusion holds without an upper cutoff on n. -/
theorem fr7022_of_theorem1_2 (h : Theorem1_2) (q a n : ℕ) (hq : 1 ≤ q)
    (hmax : q ≤ 105) (ha : a.Coprime q) (hn : 10^16 ≤ n) :
    |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q),
      ArithmeticFunction.vonMangoldt k) - (n : ℝ) / q.totient| ≤ n / 100 := by
  have hn' : (10 : ℝ)^16 ≤ n := by exact_mod_cast hn
  have hprime := PEqualNP.Outside.FixedAP.prime_error_of_bmor n hn (by
    intro m r hm hm' _ hr hunit
    rw [theta_nat]
    exact (small_moduli h hm hm' hr hunit (by linarith)).le) q a hq hmax ha
  obtain ⟨hlo, hhi⟩ := abs_le.mp hprime
  change -(↑n / 14000 : ℝ) ≤ _ at hlo
  unfold PEqualNP.Outside.FixedAP.theta at hlo hhi
  apply FixedAPPrimePowerError.progression_bound_of_prime_interval q a n hn
  · linarith
  · linarith

end BMOR
