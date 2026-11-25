import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_local_obstruction :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r)%q).Coprime q)).card; ∀ n q : ℕ, 0<q → (0<R n q ↔ Odd q ∨ Even n) := by
  dsimp only
  intro n q hq
  constructor
  · -- R > 0 implies Odd q or Even n, by contraposition
    intro hR
    by_contra hcon
    have hqeven : Even q := by
      rcases Nat.even_or_odd q with h | h
      · exact h
      · exact absurd (Or.inl h) hcon
    have hnode : Odd n := by
      rcases Nat.even_or_odd n with h | h
      · exact absurd (Or.inr h) hcon
      · exact h
    obtain ⟨r, hr⟩ := Finset.card_pos.mp hR
    rw [Finset.mem_filter, Finset.mem_range] at hr
    obtain ⟨hrlt, hcop1, hcop2⟩ := hr
    have hq2dvd : 2 ∣ q := by
      rw [Nat.dvd_iff_mod_eq_zero]
      exact Nat.even_iff.mp hqeven
    have hr_odd : Odd r :=
      Nat.coprime_two_right.mp (hcop1.coprime_dvd_right hq2dvd)
    have hn_odd : Odd n := hnode
    have hr2 : r % 2 = 1 := Nat.odd_iff.mp hr_odd
    have hn2 : n % 2 = 1 := Nat.odd_iff.mp hn_odd
    have hq2 : q % 2 = 0 := Nat.even_iff.mp hqeven
    have hmeven : Even ((n + q - r) % q) := by
      rw [Nat.even_iff, Nat.mod_mod_of_dvd _ hq2dvd]
      omega
    have hmodd : Odd ((n + q - r) % q) :=
      Nat.coprime_two_right.mp (hcop2.coprime_dvd_right hq2dvd)
    exact (Nat.not_even_iff_odd.mpr hmodd) hmeven
  · -- Odd q or Even n implies R > 0
    intro h
    rw [Finset.card_pos]
    by_cases hq1 : q = 1
    · subst hq1
      exact ⟨0, by simp⟩
    · have hq0 : q ≠ 0 := by omega
      -- the local residue choice at each prime: avoid 0 and n mod p
      set a : ℕ → ℕ := fun p => if p = 2 then 1 else if n % p = 1 % p then 2 else 1 with ha
      have hpne2 : ∀ p, p.Prime → p ∣ q → (p ≠ 2 ∨ Even n) := by
        intro p hpp hpd
        rcases h with hqo | hne
        · left
          intro hp2
          have hqmod : q % 2 = 1 := Nat.odd_iff.mp hqo
          have hd : 2 ∣ q := hp2 ▸ hpd
          have hz : q % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
          omega
        · exact Or.inr hne
      have hloc : ∀ p, p.Prime → p ∣ q → (a p % p ≠ 0 ∧ a p % p ≠ n % p) := by
        intro p hpp hpd
        have hne2 := hpne2 p hpp hpd
        by_cases hp_eq2 : p = 2
        · have ha2 : a p = 1 := by rw [ha]; simp [hp_eq2]
          have hne : Even n := by
            rcases hne2 with h' | h'
            · exact absurd hp_eq2 h'
            · exact h'
          have hn0 : n % 2 = 0 := Nat.even_iff.mp hne
          constructor
          · rw [ha2, hp_eq2]
            norm_num
          · rw [ha2, hp_eq2, hn0]
            norm_num
        · have hge3 : 3 ≤ p := by have := hpp.two_le; omega
          have h2p : 2 % p = 2 := Nat.mod_eq_of_lt (by omega)
          have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
          by_cases hc : n % p = 1 % p
          · have ha2 : a p = 2 := by rw [ha]; simp [hp_eq2, hc]
            rw [ha2, h2p]
            refine ⟨by norm_num, ?_⟩
            rw [hc, h1p]
            norm_num
          · have ha1 : a p = 1 := by rw [ha]; simp [hp_eq2, hc]
            rw [ha1, h1p]
            exact ⟨by norm_num, fun hh => hc (by rw [← hh, h1p])⟩
      -- Chinese remainder over the prime divisors
      have hpair : (↑q.primeFactors : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
        intro p hp p' hp' hne
        exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
          (Nat.prime_of_mem_primeFactors hp')).mpr hne
      have hspos : ∀ p ∈ q.primeFactors, (id : ℕ → ℕ) p ≠ 0 := by
        intro p hp
        exact (Nat.prime_of_mem_primeFactors hp).ne_zero
      obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset a id q.primeFactors hspos hpair
      have hrp : ∀ p ∈ q.primeFactors, k % q ≡ a p [MOD p] := by
        intro p hp
        exact (Nat.ModEq.of_dvd (Nat.dvd_of_mem_primeFactors hp) (Nat.mod_modEq k q)).trans (hk p hp)
      have hrlt : k % q < q := Nat.mod_lt _ hq
      have hrle : k % q ≤ n + q := by omega
      refine ⟨k % q, ?_⟩
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hrlt, ?_, ?_⟩
      · -- coprimality of the residue with q
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        have hpq : p ∣ q := hpdvd.trans (Nat.gcd_dvd_right (k % q) q)
        have hpr : p ∣ k % q := hpdvd.trans (Nat.gcd_dvd_left (k % q) q)
        have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpq, hq0⟩
        exact (hloc p hpp hpq).1 (Nat.dvd_iff_mod_eq_zero.mp
          (((hrp p hpmem).dvd_iff (dvd_refl p)).mp hpr))
      · -- coprimality of the reflected residue with q
        rw [Nat.coprime_iff_gcd_eq_one]
        by_contra hne
        obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
        have hpq : p ∣ q := hpdvd.trans (Nat.gcd_dvd_right ((n + q - k % q) % q) q)
        have hpm : p ∣ (n + q - k % q) % q := hpdvd.trans (Nat.gcd_dvd_left _ q)
        have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hpp, hpq, hq0⟩
        have hmain : p ∣ n + q - k % q :=
          ((Nat.mod_modEq (n + q - k % q) q).dvd_iff hpq).mp hpm
        have hzero : n + q - k % q ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hmain
        have hqzero : q ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpq
        have hsum : (n + q - k % q) + (k % q) ≡ 0 + a p [MOD p] := hzero.add (hrp p hpmem)
        rw [Nat.sub_add_cancel hrle, Nat.zero_add] at hsum
        have h2 : n + q ≡ n [MOD p] := by simpa using hqzero.add_left n
        exact (hloc p hpp hpq).2 (h2.symm.trans hsum).symm