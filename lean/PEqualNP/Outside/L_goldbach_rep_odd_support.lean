import Mathlib

theorem PEqualNP.Outside.L_goldbach_rep_odd_support :
    ∀ n : ℕ, Even n → 4<n → let reps := fun n : ℕ => (Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n-p)); ∀ p ∈ reps n, Odd p ∧ Odd (n-p) := by
  intro n hev h4
  dsimp only
  intro p hp
  obtain ⟨hpn, hpp, hpq⟩ := Finset.mem_filter.mp hp
  have hple : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hpn)
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp hev
  have hpne2 : p ≠ 2 := by
    rintro rfl
    have hq2 : n - 2 = 2 :=
      (Nat.Prime.even_iff hpq).mp (even_iff_two_dvd.mpr (Nat.dvd_sub h2dvd (dvd_refl 2)))
    omega
  have hqne2 : n - p ≠ 2 := by
    intro hq2
    have hpeq : p = n - 2 := by omega
    have hp2dvd : 2 ∣ p := by
      rw [hpeq]
      exact Nat.dvd_sub h2dvd (dvd_refl 2)
    have hp2 : p = 2 := (Nat.Prime.even_iff hpp).mp (even_iff_two_dvd.mpr hp2dvd)
    omega
  exact ⟨hpp.eq_two_or_odd'.resolve_left hpne2, hpq.eq_two_or_odd'.resolve_left hqne2⟩
