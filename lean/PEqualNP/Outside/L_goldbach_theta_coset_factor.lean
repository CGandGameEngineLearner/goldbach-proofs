import Mathlib

theorem PEqualNP.Outside.L_goldbach_theta_coset_factor :
    ∀ (p n : ℕ), p.Prime → ((Finset.range p).filter (fun k => k%p≠0 ∧ k%p≠n%p)).card = if p∣n then p-1 else p-2 := by
  intro p n hp
  simp [Finset.mem_filter, Finset.mem_erase]
