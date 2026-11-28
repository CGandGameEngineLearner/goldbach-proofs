import Mathlib

private theorem recoverFactors {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ^ 4 ≤ b) :
    (a * b).minFac = a ∧ (a * b) / (a * b).minFac = b := by
  have hle : a ≤ b := (Nat.le_self_pow (by decide : 4 ≠ 0) a).trans hab
  have hmin : (a * b).minFac = a := by
    have hn : a * b ≠ 1 := by have := ha.two_le; have := hb.two_le; nlinarith
    have h := Nat.minFac_prime hn
    have hu := Nat.minFac_le_of_dvd ha.two_le (dvd_mul_right a b)
    rcases h.dvd_mul.mp (Nat.minFac_dvd (a * b)) with hd | hd
    · exact (Nat.prime_dvd_prime_iff_eq h ha).mp hd
    · have := (Nat.prime_dvd_prime_iff_eq h hb).mp hd
      omega
  exact ⟨hmin, by rw [hmin, Nat.mul_div_cancel_left _ ha.pos]⟩

theorem Conjectures.Cuts.Task22a1f2e8c464aa2148d56f42 : (∀ (x1 : ℕ) (x2 : ℕ → Polynomial ℕ),   have x3 : Finset ℕ :=     {x3 ∈ Finset.range (x1 + (1 : ℕ)) |       Nat.Prime x3 ∧         have x4 : ℕ := (x3 + (2 : ℕ)).minFac;         have x5 : ℕ := (x3 + (2 : ℕ)) / x4;         Nat.Prime x5 ∧ x4 ^ (4 : ℕ) ≤ x5 ∧ x5 ≤ x4 ^ (5 : ℕ)};   have x4 : Finset (ℕ × ℕ) := {x4 ∈ (Finset.range (x1 + (3 : ℕ))).product (Finset.range (x1 + (3 : ℕ))) | Nat.Prime x4.1 ∧ Nat.Prime x4.2 ∧ x4.1 ^ (4 : ℕ) ≤ x4.2 ∧ x4.2 ≤ x4.1 ^ (5 : ℕ) ∧ x4.1 * x4.2 ≤ x1 + (2 : ℕ) ∧ Nat.Prime (x4.1 * x4.2 - (2 : ℕ))};   ∑ x5 ∈ x3, x2 (x5 + (2 : ℕ)) = ∑ x5 ∈ x4, x2 (x5.1 * x5.2)) := by
  classical
  intro N W
  let pair (p : ℕ) : ℕ × ℕ := ((p + 2).minFac, (p + 2) / (p + 2).minFac)
  have product (p : ℕ) : (pair p).1 * (pair p).2 = p + 2 :=
    Nat.mul_div_cancel' (Nat.minFac_dvd (p + 2))
  have undo (a b : ℕ) (ha : a.Prime) (hb : b.Prime) (hab : a ^ 4 ≤ b) :
      pair (a * b - 2) = (a, b) := by
    have h2 : 2 ≤ a * b := by have := ha.two_le; have := hb.two_le; nlinarith
    obtain ⟨h₁, h₂⟩ := recoverFactors ha hb hab
    apply Prod.ext <;> simp only [pair, Nat.sub_add_cancel h2] <;> assumption
  apply Finset.sum_nbij' pair (fun v : ℕ × ℕ => v.1 * v.2 - 2)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hlt, hprime, hq, hlo, hhi⟩ := hp
    have hmin : (pair p).1.Prime := Nat.minFac_prime (by omega : p + 2 ≠ 1)
    have hq' : (pair p).2.Prime := hq
    have hprod := product p
    have hfst := Nat.le_mul_of_pos_right (pair p).1 hq'.pos
    have hsnd := Nat.le_mul_of_pos_left (pair p).2 hmin.pos
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
      hmin, hq', hlo, hhi, by omega, by simpa [hprod] using hprime⟩
  · rintro ⟨a, b⟩ hv
    simp only [Finset.mem_filter, Finset.mem_range] at hv ⊢
    obtain ⟨_, ha, hb, hlo, hhi, hbound, hp⟩ := hv
    have h2 : 2 ≤ a * b := by have := ha.two_le; have := hb.two_le; nlinarith
    obtain ⟨h₁, _⟩ := recoverFactors ha hb hlo
    refine ⟨by omega, hp, ?_⟩
    simpa only [Nat.sub_add_cancel h2, h₁, Nat.mul_div_cancel_left _ ha.pos] using
      (show b.Prime ∧ a ^ 4 ≤ b ∧ b ≤ a ^ 5 from ⟨hb, hlo, hhi⟩)
  · intro p _
    rw [product]
    omega
  · rintro ⟨a, b⟩ hv
    obtain ⟨_, ha, hb, hlo, _⟩ := Finset.mem_filter.mp hv
    exact undo a b ha hb hlo
  · intro p _
    rw [product]
