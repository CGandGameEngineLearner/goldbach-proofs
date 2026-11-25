import Mathlib

theorem PEqualNP.Outside.L_goldbach_theta_coset_factor :
    ∀ (p n : ℕ), p.Prime → ((Finset.range p).filter (fun k => k%p≠0 ∧ k%p≠n%p)).card = if p∣n then p-1 else p-2 := by
  intro p n hp
  have hzero : 0 ∈ Finset.range p := Finset.mem_range.mpr hp.pos
  have hs : (Finset.range p).filter (fun k => k % p ≠ 0 ∧ k % p ≠ n % p) =
      ((Finset.range p).erase 0).erase (n % p) := by
    ext k
    by_cases hk : k < p
    · simp [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, hk,
        Nat.mod_eq_of_lt hk, and_comm, and_left_comm, and_assoc]
    · simp [Finset.mem_erase, Finset.mem_filter, Finset.mem_range, hk]
  rw [hs]
  by_cases h : p ∣ n
  · rw [if_pos h, Nat.mod_eq_zero_of_dvd h, Finset.erase_idem,
      Finset.card_erase_of_mem hzero, Finset.card_range]
  · have hr : n % p ≠ 0 := by
      intro hr
      exact h (Nat.dvd_of_mod_eq_zero hr)
    have hmem : n % p ∈ (Finset.range p).erase 0 :=
      Finset.mem_erase.mpr ⟨hr, Finset.mem_range.mpr (Nat.mod_lt n hp.pos)⟩
    rw [if_neg h, Finset.card_erase_of_mem hmem,
      Finset.card_erase_of_mem hzero, Finset.card_range]
    omega
