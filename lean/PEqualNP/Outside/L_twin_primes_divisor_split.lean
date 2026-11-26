import Mathlib

private lemma mangoldt_aux (n : ℕ) :
    ArithmeticFunction.vonMangoldt n = n.divisors.sum (fun d => -(ArithmeticFunction.moebius d : ℝ)*Real.log d) := by
  have h := ArithmeticFunction.sum_moebius_mul_log_eq (n := n)
  simp only [ArithmeticFunction.log_apply] at h
  simp only [neg_mul, Finset.sum_neg_distrib, h, neg_neg]

theorem PEqualNP.Outside.L_twin_primes_divisor_split :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let primes := fun X => (w X).filter Nat.Prime; let c := fun (d : ℕ) => -(ArithmeticFunction.moebius d : ℝ)*Real.log d; let short := fun (X D : ℕ) => (primes X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => d ≤ D)).sum c))/(X:ℝ); let long := fun (X D : ℕ) => (primes X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => D < d)).sum c))/(X:ℝ); ∀ X D : ℕ, short X D + long X D = (primes X).sum (fun p => Real.log p*ArithmeticFunction.vonMangoldt (p+2))/(X:ℝ) := by
  intro w primes c short long X D
  show (primes X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => d ≤ D)).sum c))/(X:ℝ)
      + (primes X).sum (fun p => Real.log p * (((p+2).divisors.filter (fun d => D < d)).sum c))/(X:ℝ) = _
  rw [← add_div, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← mul_add]
  congr 1
  have hf : (p+2).divisors.filter (fun d => D < d) = (p+2).divisors.filter (fun d => ¬ (d ≤ D)) :=
    Finset.filter_congr (fun d _ => not_le.symm)
  rw [hf, Finset.sum_filter_add_sum_filter_not]
  exact (mangoldt_aux (p+2)).symm
