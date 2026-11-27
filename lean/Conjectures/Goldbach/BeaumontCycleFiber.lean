import Mathlib

open scoped BigOperators

theorem Conjectures.Goldbach.BeaumontCycleFiber :
    ∀ (m a : ℕ), 0 < m → ((Finset.range m).filter (fun k => (a*k)%m=0)).card = Nat.gcd m a := by
  intro m a hm
  set g : ℕ := Nat.gcd m a with hg
  have hgpos : 0 < g := by
    rw [hg]
    exact Nat.gcd_pos_of_pos_left a hm
  have hgm : g ∣ m := by
    rw [hg]
    exact Nat.gcd_dvd_left m a
  have hga : g ∣ a := by
    rw [hg]
    exact Nat.gcd_dvd_right m a
  set md : ℕ := m / g with hmd
  set ad : ℕ := a / g with had
  have hm_eq : m = g * md := by
    rw [hmd]
    exact (Nat.mul_div_cancel' hgm).symm
  have ha_eq : a = g * ad := by
    rw [had]
    exact (Nat.mul_div_cancel' hga).symm
  have hcop : Nat.Coprime md ad := by
    rw [hmd, had, hg]
    exact Nat.coprime_div_gcd_div_gcd hgpos
  have hkey : ∀ k : ℕ, m ∣ a * k ↔ md ∣ k := by
    intro k
    constructor
    · intro h
      have h1 : g * md ∣ g * (ad * k) := by
        rw [hm_eq, ha_eq, mul_assoc] at h
        exact h
      have h2 : md ∣ ad * k := (Nat.mul_dvd_mul_iff_left hgpos).mp h1
      exact (hcop.dvd_mul_left (n := k)).mp h2
    · intro h
      have h1 : md ∣ ad * k := dvd_mul_of_dvd_right h ad
      have h2 : g * md ∣ g * (ad * k) := (Nat.mul_dvd_mul_iff_left hgpos).mpr h1
      simpa [hm_eq, ha_eq, mul_assoc] using h2
  have hmd_pos : 0 < md := by
    rw [hmd]
    exact Nat.div_pos (Nat.le_of_dvd hm hgm) hgpos
  have hcount : ((Finset.range m).filter (fun k => md ∣ k)).card = g := by
    have himage :
        (Finset.range m).filter (fun k => md ∣ k)
          = (Finset.range g).image (fun j => md * j) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hk, j, rfl⟩
        refine ⟨j, ?_, rfl⟩
        have hlt : md * j < md * g := by
          rw [mul_comm md g, ← hm_eq]
          exact hk
        exact (Nat.mul_lt_mul_left hmd_pos).mp hlt
      · rintro ⟨j, hj, rfl⟩
        refine ⟨?_, dvd_mul_right md j⟩
        have hlt : md * j < md * g := (Nat.mul_lt_mul_left hmd_pos).mpr hj
        rwa [mul_comm md g, ← hm_eq] at hlt
    rw [himage, Finset.card_image_of_injective _ (fun x y hxy => Nat.mul_left_cancel hmd_pos hxy),
      Finset.card_range]
  have hfilter :
      (Finset.range m).filter (fun k => (a*k)%m=0)
        = (Finset.range m).filter (fun k => md ∣ k) := by
    apply Finset.filter_congr
    intro k _
    rw [← Nat.dvd_iff_mod_eq_zero]
    exact hkey k
  rw [hfilter, hcount]
