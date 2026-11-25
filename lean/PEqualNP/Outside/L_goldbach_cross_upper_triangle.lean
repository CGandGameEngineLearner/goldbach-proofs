import Mathlib

theorem PEqualNP.Outside.L_goldbach_cross_upper_triangle :
    ∀ (m : ℕ) (u : Fin m → ℂ), (∑ i, ∑ j ∈ Finset.univ.erase i, (u i*star (u j)).re) = 2*∑ i, ∑ j ∈ Finset.univ.filter (fun j => i<j), (u i*star (u j)).re := by
  intro m u
  have hsym : ∀ i j : Fin m, (u j * star (u i)).re = (u i * star (u j)).re := by
    intro i j
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hsplit : ∀ i : Fin m,
      (∑ j ∈ Finset.univ.erase i, (u i * star (u j)).re)
        = (∑ j ∈ Finset.univ.filter (fun j => i < j), (u i * star (u j)).re)
          + (∑ j ∈ Finset.univ.filter (fun j => j < i), (u i * star (u j)).re) := by
    intro i
    have herase : Finset.univ.erase i = Finset.univ.filter (fun j : Fin m => j ≠ i) := by
      ext j
      simp [Finset.mem_erase]
    rw [herase]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy j i with h | h | h
    · have h2 : ¬ i < j := not_lt.mpr h.le
      have hne : j ≠ i := ne_of_lt h
      simp [h, h2, hne]
    · simp [h]
    · have h2 : ¬ j < i := not_lt.mpr h.le
      have hne : j ≠ i := ne_of_gt h
      simp [h, h2, hne]
  have hBT : (∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => j < i), (u i * star (u j)).re)
      = ∑ i : Fin m, ∑ j ∈ Finset.univ.filter (fun j => i < j), (u i * star (u j)).re := by
    simp only [Finset.sum_filter]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : j < i
    · simp [h]
      ring
    · simp [h]
  calc (∑ i, ∑ j ∈ Finset.univ.erase i, (u i*star (u j)).re)
      = ∑ i, ((∑ j ∈ Finset.univ.filter (fun j => i < j), (u i*star (u j)).re) + (∑ j ∈ Finset.univ.filter (fun j => j < i), (u i*star (u j)).re)) := Finset.sum_congr rfl (fun i _ => hsplit i)
    _ = (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (u i*star (u j)).re) + (∑ i, ∑ j ∈ Finset.univ.filter (fun j => j < i), (u i*star (u j)).re) := Finset.sum_add_distrib
    _ = (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (u i*star (u j)).re) + (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (u i*star (u j)).re) := by rw [hBT]
    _ = 2 * (∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), (u i*star (u j)).re) := by ring
