import Mathlib

theorem PEqualNP.Outside.L_goldbach_unit_nonempty_even :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ q n, 0<q → Even n → (U q n).Nonempty := by
  intro U q n hq hn
  obtain ⟨k, rfl⟩ := hn
  -- Each prime divisor of q divides exactly one of k and r.
  let primes := q.primeFactors.filter (fun p => ¬ p ∣ k)
  let r := primes.prod id
  have factors {p : ℕ} (hp : p.Prime) (hpq : p ∣ q) : p ∣ r ↔ ¬ p ∣ k := by
    change p ∣ primes.prod id ↔ _
    rw [hp.prime.dvd_finsetProd_iff]
    constructor
    · rintro ⟨t, ht, hpt⟩
      obtain ⟨htq, htk⟩ := Finset.mem_filter.mp ht
      have htp := (Nat.prime_of_mem_primeFactors htq).dvd_iff_eq hp.ne_one |>.mp hpt
      simpa [htp] using htk
    · intro hpk
      exact ⟨p, Finset.mem_filter.mpr ⟨hp.mem_primeFactors hpq hq.ne', hpk⟩, dvd_rfl⟩
  let a := (k + r) % q
  have ha : a < q := Nat.mod_lt _ hq
  refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, ?_, ?_⟩⟩
  · apply Nat.coprime_of_dvd
    intro p hp hpa hpq
    have hsum : p ∣ k + r := (Nat.dvd_mod_iff hpq).mp hpa
    by_cases hpk : p ∣ k
    · exact (factors hp hpq).mp ((Nat.dvd_add_iff_right hpk).mpr hsum) hpk
    · exact hpk ((Nat.dvd_add_iff_left ((factors hp hpq).mpr hpk)).mpr hsum)
  · apply Nat.coprime_of_dvd
    intro p hp hpb hpq
    -- If the reflected term vanished modulo p, then k+r and k+k would agree.
    have heq : k + r ≡ k + k [MOD p] := calc
      k + r ≡ a [MOD p] := ((Nat.mod_modEq _ q).of_dvd hpq).symm
      _ ≡ (k + k + q - a) + a [MOD p] := by
        simpa only [Nat.zero_add] using hpb.zero_modEq_nat.add_right a
      _ = k + k + q := Nat.sub_add_cancel (by omega)
      _ ≡ k + k [MOD p] := (show k + k + q ≡ k + k [MOD q] from Nat.add_modEq_right).of_dvd hpq
    have same : p ∣ r ↔ p ∣ k := (Nat.ModEq.add_left_cancel' k heq).dvd_iff dvd_rfl
    by_cases hpk : p ∣ k
    · exact (factors hp hpq).mp (same.mpr hpk) hpk
    · exact hpk (same.mp ((factors hp hpq).mpr hpk))
