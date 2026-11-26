import Mathlib

theorem PEqualNP.Outside.L_twin_primes_hermitian_pairs :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℂ), (∀ i j, A j i = star (A i j)) → ((Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2) |>.sum (fun z => A z.1 z.2)).im = 0 := by
  intro n A hA
  set s := (Finset.univ : Finset (Fin n × Fin n)).filter (fun z => z.1 ≠ z.2) with hs
  have h1 : s.sum (fun z => A z.1 z.2) = s.sum (fun z => A z.2 z.1) := by
    apply Finset.sum_equiv (Equiv.prodComm _ _)
    · intro z
      simp [hs, ne_comm]
    · intro z _
      simp
  have h2 : (s.sum (fun z => A z.2 z.1)).im = -(s.sum (fun z => A z.1 z.2)).im := by
    rw [Complex.im_sum, Complex.im_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z _
    rw [hA z.1 z.2]
    simp
  have h3 : (s.sum (fun z => A z.1 z.2)).im = -(s.sum (fun z => A z.1 z.2)).im := by
    calc (s.sum (fun z => A z.1 z.2)).im = (s.sum (fun z => A z.2 z.1)).im := by rw [h1]
      _ = -(s.sum (fun z => A z.1 z.2)).im := h2
  linarith
