import Mathlib

theorem PEqualNP.Outside.L_goldbach_fixed_ap_theta_reduction :
    (∀ (q a n : ℕ), 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n → (n:ℝ) < Real.exp (Real.exp (19/5)) → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), (if k.Prime then ArithmeticFunction.vonMangoldt k else 0)) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/200) → (∀ n : ℕ, 10^16 ≤ n → (∑ k ∈ Finset.range (n+1), (if k.Prime then 0 else ArithmeticFunction.vonMangoldt k)) ≤ (n:ℝ)/200) → (∀ (q a n : ℕ), 1 ≤ q → q ≤ 105 → Nat.Coprime a q → 10^16 ≤ n → (n:ℝ) < Real.exp (Real.exp (19/5)) → |(∑ k ∈ (Finset.range (n+1)).filter (fun k => k % q = a % q), ArithmeticFunction.vonMangoldt k) - (n:ℝ)/Nat.totient q| ≤ (n:ℝ)/100) := by
  intro hprime hpower q a n hq hq' ha hn hn'
  let S := (Finset.range (n+1)).filter (fun k => k % q = a % q)
  let P (k : ℕ) : ℝ := if k.Prime then ArithmeticFunction.vonMangoldt k else 0
  let R (k : ℕ) : ℝ := if k.Prime then 0 else ArithmeticFunction.vonMangoldt k
  have hR (k : ℕ) : 0 ≤ R k := by
    dsimp [R]
    split <;> first | exact le_rfl | exact ArithmeticFunction.vonMangoldt_nonneg
  have hsplit : (∑ k ∈ S, ArithmeticFunction.vonMangoldt k) =
      (∑ k ∈ S, P k) + ∑ k ∈ S, R k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.Prime <;> simp [P, R, hk]
  have hupper : (∑ k ∈ S, R k) ≤ (n : ℝ)/200 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun k _ _ => hR k)).trans
      (hpower n hn)
  have hlower : 0 ≤ ∑ k ∈ S, R k := Finset.sum_nonneg (fun k _ => hR k)
  have hp : |(∑ k ∈ S, P k) - (n : ℝ)/Nat.totient q| ≤ (n : ℝ)/200 :=
    hprime q a n hq hq' ha hn hn'
  change |(∑ k ∈ S, ArithmeticFunction.vonMangoldt k) - _| ≤ _
  rw [hsplit, abs_le]
  rw [abs_le] at hp
  constructor <;> linarith [hp.1, hp.2, (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
