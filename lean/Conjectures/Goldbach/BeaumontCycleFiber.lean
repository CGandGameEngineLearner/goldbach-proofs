import Mathlib

open Finset

theorem Conjectures.Goldbach.BeaumontCycleFiber :
    ∀ (m a : ℕ), 0 < m →
      ((Finset.range m).filter (fun k => (a * k) % m = 0)).card = Nat.gcd m a := by
  intro m a hm
  let g := Nat.gcd m a
  let p := m / g
  have hg : 0 < g := by
    simpa only [g] using Nat.gcd_pos_of_pos_left a hm
  have hm_eq : m = g * p := by
    simpa only [g, p] using (Nat.mul_div_cancel' (Nat.gcd_dvd_left m a)).symm
  have ha_eq : a = g * (a / g) := by
    simpa only [g] using (Nat.mul_div_cancel' (Nat.gcd_dvd_right m a)).symm
  have hp : 0 < p := by
    by_contra! hp0
    have hpzero : p = 0 := Nat.eq_zero_of_le_zero hp0
    rw [hpzero, mul_zero] at hm_eq
    omega
  have hcop : Nat.Coprime p (a / g) := by
    simpa only [Nat.Coprime, g, p] using
      (Nat.gcd_div_gcd_div_gcd_of_pos_left (n := m) (m := a) hm)
  have hmod (k : ℕ) : (a * k) % m = 0 ↔ p ∣ k := by
    constructor
    · intro hk
      have hmk : m ∣ a * k := Nat.dvd_of_mod_eq_zero hk
      have hmg : g * p ∣ g * ((a / g) * k) := by
        calc
          g * p = m := hm_eq.symm
          _ ∣ a * k := hmk
          _ = g * ((a / g) * k) := by
            nth_rewrite 1 [ha_eq]
            ring
      have hpdiv : p ∣ (a / g) * k :=
        (Nat.mul_dvd_mul_iff_left hg).mp hmg
      exact hcop.dvd_of_dvd_mul_left hpdiv
    · intro hpk
      obtain ⟨t, rfl⟩ := hpk
      have hpmul : p ∣ (a / g) * (p * t) := by
        refine ⟨(a / g) * t, ?_⟩
        ring
      have hgdiv : g * p ∣ g * ((a / g) * (p * t)) :=
        (Nat.mul_dvd_mul_iff_left hg).mpr hpmul
      have hmdiv : m ∣ a * (p * t) := by
        rw [hm_eq]
        nth_rewrite 1 [ha_eq]
        simpa only [mul_assoc] using hgdiv
      exact Nat.mod_eq_zero_of_dvd hmdiv
  have hfilter :
      ((Finset.range m).filter (fun k => (a * k) % m = 0)).card =
        ((Finset.range m).filter (fun k => p ∣ k)).card := by
    congr 1
    ext k
    simp only [mem_filter, mem_range]
    rw [hmod k]
  have hmul_eq : m = p * g := by
    simpa only [mul_comm] using hm_eq
  have himage :
      (Finset.range m).filter (fun k => p ∣ k) =
        (Finset.range g).image (fun j => p * j) := by
    ext k
    constructor
    · intro hk
      have hk' := mem_filter.mp hk
      have hkm : k < m := mem_range.mp hk'.1
      obtain ⟨j, hj⟩ := hk'.2
      refine mem_image.mpr ⟨j, mem_range.mpr ?_, hj.symm⟩
      rw [hj, hmul_eq] at hkm
      nlinarith only [hp, hkm]
    · intro hk
      obtain ⟨j, hj, hjk⟩ := mem_image.mp hk
      have hjlt : j < g := mem_range.mp hj
      refine mem_filter.mpr ⟨mem_range.mpr ?_, ⟨j, hjk.symm⟩⟩
      rw [← hjk]
      rw [hmul_eq]
      nlinarith only [hp, hjlt]
  have hinj : Function.Injective (fun j : ℕ => p * j) := by
    intro x y hxy
    exact Nat.eq_of_mul_eq_mul_left hp hxy
  rw [hfilter, himage, card_image_of_injective _ hinj]
  simp only [card_range]
  change g = Nat.gcd m a
  rfl
