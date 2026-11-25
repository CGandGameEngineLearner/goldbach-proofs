import Mathlib

theorem PEqualNP.Outside.L_goldbach_conductor_average_split :
    ∀ (n m : ℕ) (d : Fin m → ℕ) (u : Fin m → ℝ), (2/(Nat.totient n : ℝ))*(∑ j, u j) = (2/(Nat.totient n : ℝ))*(∑ j ∈ Finset.univ.filter (fun j => n^3 < (d j)^4), u j) + (2/(Nat.totient n : ℝ))*(∑ j ∈ Finset.univ.filter (fun j => (d j)^4 ≤ n^3), u j) := by
  intro n m d u
  have hcongr : Finset.univ.filter (fun j : Fin m => ¬ n^3 < (d j)^4)
      = Finset.univ.filter (fun j : Fin m => (d j)^4 ≤ n^3) := by
    apply Finset.filter_congr
    intro j _
    exact not_lt
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun j : Fin m => n^3 < (d j)^4) u
  rw [hcongr] at hsplit
  rw [← hsplit, mul_add]
