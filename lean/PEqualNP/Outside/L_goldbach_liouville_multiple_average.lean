import Mathlib

theorem PEqualNP.Outside.L_goldbach_liouville_multiple_average :
    let L := fun n : ℕ => if n=0 then (0:ℝ) else (-1:ℝ)^n.primeFactorsList.length; let C := fun n : ℕ => (∑ t ∈ Finset.range n, L t * L (n-t))/(n:ℝ); ∀ (N p : ℕ), 0 < N → Nat.Prime p → p ∣ N → (∑ t ∈ (Finset.range N).filter (fun t => p ∣ t), L t * L (N-t))/((N/p:ℕ):ℝ)=C (N/p) := by
  intro L C N p hN hp hpN
  have hp0 : 0 < p := hp.pos
  have hpne : p ≠ 0 := hp.pos.ne'
  set M : ℕ := N / p with hM
  have hNp : N = p * M := by
    rw [hM, mul_comm]
    exact (Nat.div_mul_cancel hpN).symm
  have hL0 : L 0 = 0 := by
    dsimp only [L]
    simp
  have hLp : ∀ s : ℕ, s ≠ 0 → L (p * s) = - L s := by
    intro s hs
    dsimp only [L]
    rw [if_neg (by positivity : ¬ p * s = 0), if_neg hs]
    have hperm := Nat.perm_primeFactorsList_mul (a := p) (b := s) hpne hs
    rw [Nat.primeFactorsList_prime hp] at hperm
    have hlen : (p * s).primeFactorsList.length = s.primeFactorsList.length + 1 := by
      have h1 : ([p] ++ s.primeFactorsList).length = s.primeFactorsList.length + 1 := by simp
      rw [← h1]
      exact hperm.length_eq
    rw [hlen, pow_succ]
    ring
  have hreindex : (∑ t ∈ (Finset.range N).filter (fun t => p ∣ t), L t * L (N - t))
      = ∑ s ∈ Finset.range M, L (p * s) * L (N - p * s) := by
    refine Finset.sum_bij' (fun t _ => t / p) (fun s _ => p * s) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_range] at ht
      obtain ⟨htN, hpt⟩ := ht
      obtain ⟨s, rfl⟩ := hpt
      have hdiv : p * s / p = s := by
        rw [mul_comm p s]
        exact Nat.mul_div_left s hp0
      rw [hdiv]
      rw [hNp] at htN
      exact Finset.mem_range.mpr ((Nat.mul_lt_mul_left hp0).mp htN)
    · intro s hs
      have hsM : s < M := Finset.mem_range.mp hs
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ⟨s, rfl⟩⟩
      rw [hNp]
      exact Nat.mul_lt_mul_of_pos_left hsM hp0
    · intro t ht
      simp only [Finset.mem_filter] at ht
      exact Nat.mul_div_cancel' ht.2
    · intro s hs
      show p * s / p = s
      rw [mul_comm p s]
      exact Nat.mul_div_left s hp0
    · intro t ht
      simp only [Finset.mem_filter] at ht
      rw [Nat.mul_div_cancel' ht.2]
  have hterm : ∀ s ∈ Finset.range M, L (p * s) * L (N - p * s) = L s * L (M - s) := by
    intro s hs
    have hsM : s < M := Finset.mem_range.mp hs
    by_cases hs0 : s = 0
    · subst hs0
      simp only [mul_zero, Nat.sub_zero]
      rw [hL0]
      ring
    · have hMs : M - s ≠ 0 := by omega
      have h1 := hLp s hs0
      have hsub : N - p * s = p * (M - s) := by
        rw [hNp]
        exact (Nat.mul_sub_left_distrib p M s).symm
      have h2 : L (N - p * s) = - L (M - s) := by
        rw [hsub]
        exact hLp (M - s) hMs
      rw [h1, h2]
      ring
  have hS : (∑ s ∈ Finset.range M, L (p * s) * L (N - p * s))
      = ∑ s ∈ Finset.range M, L s * L (M - s) := Finset.sum_congr rfl hterm
  rw [hreindex, hS]
