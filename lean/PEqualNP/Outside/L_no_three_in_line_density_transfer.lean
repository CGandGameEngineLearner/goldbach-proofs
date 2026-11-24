import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_density_transfer :
    let valid := fun (n : ℕ) (S : Finset (ℕ × ℕ)) => (∀ z ∈ S, z.1 < n ∧ z.2 < n) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠ ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))); (∀ p : ℕ, Nat.Prime p → 2 < p → ∃ S : Finset (ℕ × ℕ), valid (2*p) S ∧ 3*(p-1) ≤ S.card) → ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ S : Finset (ℕ × ℕ), valid n S ∧ (3/2-e)*(n:ℝ) ≤ (S.card:ℝ) := by
  intro valid hprem e he
  by_cases hbig : (3 / 2 : ℝ) ≤ e
  · refine ⟨0, fun n _ => ?_⟩
    refine ⟨∅, ?_, ?_⟩
    · simp [valid]
    · have hle : (3 / 2 - e) * (n : ℝ) ≤ 0 := by
        have h1 : (3 / 2 - e) ≤ 0 := by linarith
        calc (3 / 2 - e) * (n : ℝ) ≤ 0 * (n : ℝ) :=
              mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n)
          _ = 0 := by ring
      simpa using hle
  · push_neg at hbig
    set d : ℝ := e / 3 with hd
    have hdpos : 0 < d := by rw [hd]; linarith
    have hdhalf : d < 1 / 2 := by rw [hd]; linarith
    have hd3 : 3 * d = e := by rw [hd]; ring
    have hgap := Nat.eventually_exists_prime_mem_Ioc_sub hdpos
    rw [Filter.eventually_atTop] at hgap
    obtain ⟨X, hX⟩ := hgap
    obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * X) (max (6 / e) 10) + 1)
    refine ⟨N, fun n hn => ?_⟩
    have hnN : ((N : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hNX : 2 * X < ((N : ℕ) : ℝ) := by
      have hle : 2 * X ≤ max (2 * X) (max (6 / e) 10) := le_max_left _ _
      linarith
    have h6e : 6 / e < (n : ℝ) := by
      have hle : 6 / e ≤ max (2 * X) (max (6 / e) 10) :=
        (le_max_left (6 / e) 10).trans (le_max_right (2 * X) (max (6 / e) 10))
      linarith
    have hxX : X ≤ (n : ℝ) / 2 := by linarith
    obtain ⟨p, hpp, hpIoc⟩ := hX ((n : ℝ) / 2) hxX
    obtain ⟨hpgt, hple⟩ := hpIoc
    have h10 : (10 : ℝ) < (n : ℝ) := by
      have hle : 10 ≤ max (2 * X) (max (6 / e) 10) :=
        (le_max_right (6 / e) 10).trans (le_max_right (2 * X) (max (6 / e) 10))
      linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
    have hn5 : (5 : ℝ) < (n : ℝ) / 2 := by linarith
    have h2p : 2 * p ≤ n := by
      have hcast : ((2 * p : ℕ) : ℝ) ≤ (n : ℝ) := by
        push_cast
        linarith
      exact_mod_cast hcast
    have hp2 : 2 < p := by
      have h1md : (1 / 2 : ℝ) < 1 - d := by linarith
      have hpR : (2 : ℝ) < (p : ℝ) := by nlinarith
      exact_mod_cast hpR
    obtain ⟨S, hSv, hSc⟩ := hprem p hpp hp2
    refine ⟨S, ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hSv
      exact ⟨fun z hz => ⟨lt_of_lt_of_le (h1 z hz).1 h2p, lt_of_lt_of_le (h1 z hz).2 h2p⟩, h2⟩
    · have hScR : ((3 * (p - 1) : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hSc
      have hpc : ((3 * (p - 1) : ℕ) : ℝ) = 3 * ((p : ℝ) - 1) := by
        have hp1 : 1 ≤ p := by omega
        rw [Nat.cast_mul, Nat.cast_sub hp1]
        norm_num
      have hn6 : (6 : ℝ) < e * (n : ℝ) := by
        have := (div_lt_iff₀ he).mp h6e
        nlinarith
      have hkey : (3 / 2 - e) * (n : ℝ) ≤ 3 * ((p : ℝ) - 1) := by
        have h1 : 3 * ((1 - d) * ((n : ℝ) / 2)) < 3 * (p : ℝ) := by linarith
        have h2 : 3 * ((1 - d) * ((n : ℝ) / 2)) = 3 / 2 * (n : ℝ) - e * (n : ℝ) / 2 := by
          rw [hd]
          ring
        nlinarith
      calc (3 / 2 - e) * (n : ℝ) ≤ 3 * ((p : ℝ) - 1) := hkey
        _ = ((3 * (p - 1) : ℕ) : ℝ) := by rw [hpc]
        _ ≤ (S.card : ℝ) := hScR
