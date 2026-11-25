import Mathlib

private lemma rem_covers (r : ℕ) (hr : r < 210) (he : Even r) :
    ∃ p ∈ ({3,5,7,11,13,17,19} : Finset ℕ),
      (r + 210 - p) % 3 ≠ 0 ∧ (r + 210 - p) % 5 ≠ 0 ∧ (r + 210 - p) % 7 ≠ 0 := by
  interval_cases r <;> decide

private lemma sub_mod_transfer {n p q : ℕ} (hpn : p ≤ n) (hp : p ≤ 210) (hq : q ∣ 210) :
    (n - p) % q = (n % 210 + 210 - p) % q := by
  have hp2 : p ≤ n % 210 + 210 := by
    have := Nat.mod_lt n (by norm_num : 0 < 210)
    omega
  have hlt : n % 210 < 210 := Nat.mod_lt n (by norm_num)
  have hab : n ≡ n % 210 + 210 [MOD 210] := by
    show n % 210 = (n % 210 + 210) % 210
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt hlt]
  have hsub : (n - p) % 210 = (n % 210 + 210 - p) % 210 :=
    Nat.ModEq.sub hpn hp2 hab (Nat.ModEq.refl p)
  calc (n - p) % q = ((n - p) % 210) % q := (Nat.mod_mod_of_dvd (n - p) hq).symm
    _ = ((n % 210 + 210 - p) % 210) % q := by rw [hsub]
    _ = (n % 210 + 210 - p) % q := Nat.mod_mod_of_dvd _ hq

theorem PEqualNP.Outside.L_goldbach_finite_rough_candidate_lift : ∀ n : ℕ, 22 ≤ n → Even n → ∃ p : ℕ, Nat.Prime p ∧ p < n ∧ 2 ≤ n-p ∧ Nat.Coprime (n-p) 210 := by
  intro n hn he
  have hmod : Even (n % 210) := by
    rw [Nat.even_iff] at he ⊢
    rw [Nat.mod_mod_of_dvd n (by norm_num : (2:ℕ) ∣ 210)]
    exact he
  obtain ⟨p, hpmem, h3, h5, h7⟩ := rem_covers (n % 210) (Nat.mod_lt n (by norm_num)) hmod
  have hcase : p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hpmem
  have hpprime : Nat.Prime p := by
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hp19 : p ≤ 19 := by
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hpodd : Odd p := by
    rcases hcase with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have hpn : p ≤ n := by omega
  refine ⟨p, hpprime, by omega, by omega, ?_⟩
  have hm3 : (n - p) % 3 ≠ 0 := by
    rw [sub_mod_transfer hpn (by omega) (by norm_num : (3:ℕ) ∣ 210)]
    exact h3
  have hm5 : (n - p) % 5 ≠ 0 := by
    rw [sub_mod_transfer hpn (by omega) (by norm_num : (5:ℕ) ∣ 210)]
    exact h5
  have hm7 : (n - p) % 7 ≠ 0 := by
    rw [sub_mod_transfer hpn (by omega) (by norm_num : (7:ℕ) ∣ 210)]
    exact h7
  have hmodd : Odd (n - p) := Nat.Even.sub_odd hpn he hpodd
  have hc2 : Nat.Coprime (n - p) 2 := Nat.coprime_two_right.2 hmodd
  have hc3 : Nat.Coprime (n - p) 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).2 (fun h => hm3 (Nat.dvd_iff_mod_eq_zero.mp h))).symm
  have hc5 : Nat.Coprime (n - p) 5 :=
    ((Nat.prime_five.coprime_iff_not_dvd).2 (fun h => hm5 (Nat.dvd_iff_mod_eq_zero.mp h))).symm
  have hc7 : Nat.Coprime (n - p) 7 :=
    ((Nat.prime_seven.coprime_iff_not_dvd).2 (fun h => hm7 (Nat.dvd_iff_mod_eq_zero.mp h))).symm
  have hall : Nat.Coprime (n - p) (2 * (3 * (5 * 7))) :=
    hc2.mul_right (hc3.mul_right (hc5.mul_right hc7))
  norm_num at hall ⊢
  exact hall