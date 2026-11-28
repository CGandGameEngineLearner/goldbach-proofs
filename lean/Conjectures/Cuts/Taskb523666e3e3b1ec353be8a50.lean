import Mathlib

theorem Conjectures.Cuts.Taskb523666e3e3b1ec353be8a50 : (∀ (x1 x2 : ℕ), (0 : ℕ) < x1 → (0 : ℕ) < x2 → x1.Coprime x2 → (x1 * x2 * (x1 + x2)).primeFactors.prod id = x1.primeFactors.prod id * x2.primeFactors.prod id * (x1 + x2).primeFactors.prod id) := by
  intro a b ha hb hcop
  have rad_mul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n →
      (m * n).primeFactors.prod id = m.primeFactors.prod id * n.primeFactors.prod id := by
    intro m n hm hn hmn
    rw [Nat.primeFactors_mul hm hn]
    apply Finset.prod_union
    rw [Finset.disjoint_left]
    intro p hpm hpn
    rcases Nat.mem_primeFactors.mp hpm with ⟨hp, hpm_dvd, _⟩
    rcases Nat.mem_primeFactors.mp hpn with ⟨_, hpn_dvd, _⟩
    have hd1 : p ∣ 1 := by
      have hg := Nat.dvd_gcd hpm_dvd hpn_dvd
      rw [hmn.gcd_eq_one] at hg
      exact hg
    exact hp.ne_one (Nat.dvd_one.mp hd1)
  have hca : a.Coprime (a + b) := by
    rw [Nat.Coprime]
    have hda : Nat.gcd a (a + b) ∣ a := Nat.gcd_dvd_left a (a + b)
    have hds : Nat.gcd a (a + b) ∣ a + b := Nat.gcd_dvd_right a (a + b)
    have hdb : Nat.gcd a (a + b) ∣ b := (Nat.dvd_add_right hda).mp hds
    have hg : Nat.gcd a (a + b) ∣ Nat.gcd a b := Nat.dvd_gcd hda hdb
    rw [hcop.gcd_eq_one] at hg
    exact Nat.dvd_one.mp hg
  have hcb : b.Coprime (a + b) := by
    rw [Nat.Coprime]
    have hdb : Nat.gcd b (a + b) ∣ b := Nat.gcd_dvd_left b (a + b)
    have hds : Nat.gcd b (a + b) ∣ a + b := Nat.gcd_dvd_right b (a + b)
    have hda : Nat.gcd b (a + b) ∣ a := (Nat.dvd_add_left hdb).mp hds
    have hg : Nat.gcd b (a + b) ∣ Nat.gcd a b := Nat.dvd_gcd hda hdb
    rw [hcop.gcd_eq_one] at hg
    exact Nat.dvd_one.mp hg
  have hcab : (a * b).Coprime (a + b) := hca.mul_left hcb
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  have hb0 : b ≠ 0 := Nat.ne_of_gt hb
  have hab0 : a * b ≠ 0 := Nat.mul_ne_zero ha0 hb0
  have hsum0 : a + b ≠ 0 := by omega
  rw [rad_mul hab0 hsum0 hcab, rad_mul ha0 hb0 hcop]
