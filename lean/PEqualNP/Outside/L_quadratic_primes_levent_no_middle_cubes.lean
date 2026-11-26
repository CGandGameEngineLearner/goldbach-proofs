import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_no_middle_cubes :
    let block := fun x : ℕ => Finset.Ioc x (2 * x)
    ∀ x n p : ℕ, 5 ≤ x → n ∈ block x → x < p → ¬ p ^ 3 ∣ n ^ 2 + 1 := by
  intro x n p hx hn hp hdvd
  rw [Finset.mem_Ioc] at hn
  obtain ⟨hn1, hn2⟩ := hn
  have hpos : 0 < n ^ 2 + 1 := by positivity
  have hbig : n ^ 2 + 1 < p ^ 3 := by nlinarith
  have hle : p ^ 3 ≤ n ^ 2 + 1 := Nat.le_of_dvd hpos hdvd
  omega
