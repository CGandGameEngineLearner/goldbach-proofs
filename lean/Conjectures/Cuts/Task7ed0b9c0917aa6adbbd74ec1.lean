import Mathlib
import Conjectures.JoshiAbc.HeightBridge

theorem Conjectures.Cuts.Task7ed0b9c0917aa6adbbd74ec1 : (have x1 : ℕ → ℕ := fun (x1 : ℕ) => x1.primeFactors.prod id; ∀ (x2 x3 : ℕ), (0 : ℕ) < x2 → (0 : ℕ) < x3 → x2.Coprime x3 → x2 ≠ x3 → ∃ (x8 : ℕ) (x9 : ℕ), (0 : ℕ) < x8 ∧ x8 < x9 ∧ x8.Coprime x9 ∧ (x2 + x3) ^ (2 : ℕ) ≤ (4 : ℕ) * x9 ^ (2 : ℕ) ∧ x1 (x8 ^ (2 : ℕ) * (x9 ^ (2 : ℕ) - x8 ^ (2 : ℕ)) * x9 ^ (2 : ℕ)) ≤ (4 : ℕ) * (x2 + x3) * x1 (x2 * x3 * (x2 + x3))) := by
  show ∀ x2 x3 : ℕ, 0 < x2 → 0 < x3 → x2.Coprime x3 → x2 ≠ x3 →
    ∃ x8 x9 : ℕ, 0 < x8 ∧ x8 < x9 ∧ x8.Coprime x9 ∧
      (x2 + x3) ^ (2 : ℕ) ≤ 4 * x9 ^ (2 : ℕ) ∧
      (x8 ^ (2 : ℕ) * (x9 ^ (2 : ℕ) - x8 ^ (2 : ℕ)) * x9 ^ (2 : ℕ)).primeFactors.prod id ≤
        4 * (x2 + x3) * (x2 * x3 * (x2 + x3)).primeFactors.prod id
  intro x2 x3 h2 h3 hcop hne
  have rad_mul_le : ∀ m n : ℕ, 0 < m → 0 < n →
      (m * n).primeFactors.prod id ≤ m.primeFactors.prod id * n.primeFactors.prod id := by
    intro m n hm hn
    rw [Nat.primeFactors_mul (by omega) (by omega)]
    have hunion := Finset.prod_union_inter (s₁ := m.primeFactors) (s₂ := n.primeFactors)
      (f := id)
    have hposm : 0 < m.primeFactors.prod id :=
      Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    have hposn : 0 < n.primeFactors.prod id :=
      Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
    exact Nat.le_of_dvd (mul_pos hposm hposn) ⟨_, hunion.symm⟩
  have rad_le_self : ∀ k : ℕ, 0 < k → k.primeFactors.prod id ≤ k := by
    intro k hk
    exact Nat.le_of_dvd hk (Nat.prod_primeFactors_dvd k)
  have claim : ∀ u v : ℕ, 0 < u → 0 < v →
      (u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors.prod id ≤
        4 * (u + v) * (u * v * (u + v)).primeFactors.prod id := by
    intro u v hu hv
    have hM : (u + v) ^ 2 - u ^ 2 = v * (u + v + u) := by
      have h1 : (u + v) ^ 2 = u ^ 2 + v * (u + v + u) := by ring
      omega
    have hsub : (u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors ⊆
        (u * v * (u + v) * (u + v + u)).primeFactors := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      obtain ⟨hpp, hpd, -⟩ := hp
      rw [Nat.mem_primeFactors]
      refine ⟨hpp, ?_, (by positivity : 0 < u * v * (u + v) * (u + v + u)).ne'⟩
      rcases hpp.dvd_mul.mp hpd with h1 | h2
      · rcases hpp.dvd_mul.mp h1 with h1' | h1''
        · have hpu : p ∣ u := hpp.dvd_of_dvd_pow h1'
          exact ((hpu.mul_right v).mul_right (u + v)).mul_right (u + v + u)
        · rw [hM] at h1''
          rcases hpp.dvd_mul.mp h1'' with h | h
          · exact ((h.mul_left u).mul_right (u + v)).mul_right (u + v + u)
          · exact h.mul_left (u * v * (u + v))
      · have hpc : p ∣ u + v := hpp.dvd_of_dvd_pow h2
        exact (hpc.mul_left (u * v)).mul_right (u + v + u)
    have h1 : (u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors.prod id ≤
        (u * v * (u + v) * (u + v + u)).primeFactors.prod id := by
      have hsplit := Finset.union_sdiff_of_subset hsub
      have hdisj : Disjoint (u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors
          ((u * v * (u + v) * (u + v + u)).primeFactors \
            (u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors) :=
        Finset.disjoint_sdiff
      calc (u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors.prod id
          ≤ (u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors.prod id *
              ((u * v * (u + v) * (u + v + u)).primeFactors \
                (u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors).prod id := by
            apply Nat.le_mul_of_pos_right
            apply Finset.prod_pos
            intro p hp
            exact (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).pos
        _ = ((u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors ∪
              ((u * v * (u + v) * (u + v + u)).primeFactors \
                (u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors)).prod id :=
            (Finset.prod_union hdisj).symm
        _ = (u * v * (u + v) * (u + v + u)).primeFactors.prod id := by rw [hsplit]
    have h2 : (u * v * (u + v) * (u + v + u)).primeFactors.prod id ≤
        (u * v * (u + v)).primeFactors.prod id * (u + v + u) := by
      calc (u * v * (u + v) * (u + v + u)).primeFactors.prod id
          ≤ (u * v * (u + v)).primeFactors.prod id * (u + v + u).primeFactors.prod id :=
            rad_mul_le _ _ (by positivity) (by omega)
        _ ≤ (u * v * (u + v)).primeFactors.prod id * (u + v + u) :=
            mul_le_mul_right (rad_le_self _ (by omega)) _
    have h3 : u + v + u ≤ 4 * (u + v) := by omega
    calc (u ^ 2 * ((u + v) ^ 2 - u ^ 2) * (u + v) ^ 2).primeFactors.prod id
        ≤ (u * v * (u + v)).primeFactors.prod id * (u + v + u) := le_trans h1 h2
      _ ≤ (u * v * (u + v)).primeFactors.prod id * (4 * (u + v)) := mul_le_mul_right h3 _
      _ = 4 * (u + v) * (u * v * (u + v)).primeFactors.prod id := by ring
  rcases le_total x2 x3 with h | h
  · refine ⟨x2, x2 + x3, h2, by omega, ?_, Nat.le_mul_of_pos_left _ (by norm_num), ?_⟩
    · rw [Nat.coprime_self_add_right]
      exact hcop
    · exact claim x2 x3 h2 h3
  · refine ⟨x3, x2 + x3, h3, by omega, ?_, Nat.le_mul_of_pos_left _ (by norm_num), ?_⟩
    · rw [Nat.add_comm x2 x3, Nat.coprime_self_add_right]
      exact hcop.symm
    · have hclaim := claim x3 x2 h3 h2
      rw [Nat.add_comm x3 x2, mul_comm x3 x2] at hclaim
      exact hclaim
