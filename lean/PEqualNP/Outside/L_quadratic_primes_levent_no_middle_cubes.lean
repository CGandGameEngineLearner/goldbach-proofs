import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_no_middle_cubes :
    let block := fun x : ℕ => Finset.Ioc x (2*x); ∀ x n p : ℕ, 5≤x → n ∈ block x → x<p → ¬ p^3 ∣ n^2+1 := by
  dsimp only
  intro x n p hx hn hxp h
  rw [Finset.mem_Ioc] at hn
  obtain ⟨hnx, hn2x⟩ := hn
  have hp6 : 6 ≤ p := by omega
  have h1 : n^2 ≤ (2*x)^2 := Nat.pow_le_pow_left hn2x 2
  have hlt2x : 2*x < 2*p := by omega
  have h3 : (2*x)^2 < (2*p)^2 := Nat.pow_lt_pow_left hlt2x (by norm_num)
  have h4 : n^2 + 1 < (2*p)^2 + 1 := by omega
  have h5 : (2*p)^2 + 1 < p^3 := by nlinarith [hp6]
  have hlt : n^2 + 1 < p^3 := by omega
  have hpos : 0 < n^2+1 := by positivity
  have := Nat.le_of_dvd hpos h
  omega
