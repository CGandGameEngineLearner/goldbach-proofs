import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith

theorem PEqualNP.Outside.L_goldbach_unit_nonempty_even :
    let U := fun q n : ℕ => (Finset.range q).filter (fun a => Nat.Coprime a q ∧ Nat.Coprime (n+q-a) q); ∀ q n, 0<q → Even n → (U q n).Nonempty := by
  intro U q n hq hn
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset
    (fun p : ℕ => if p ∣ n + q - 1 then 2 else 1) (fun p : ℕ => p) q.primeFactors
    (by intro i hi; exact (Nat.prime_of_mem_primeFactors hi).ne_zero)
    (by
      intro i hi j hj hij
      exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hi)
        (Nat.prime_of_mem_primeFactors hj)).mpr hij)
  have hn2 : 2 ∣ n := even_iff_two_dvd.mp hn
  have key : ∀ p, p.Prime → p ∣ q →
      ¬ p ∣ (k % q) ∧ ¬ p ∣ (n + q - k % q) := by
    intro p hp hpq
    have hmem : p ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne'⟩
    have h1 := hk p hmem
    have ha : (k % q) % p = (if p ∣ n + q - 1 then 2 else 1) % p := by
      rw [Nat.mod_mod_of_dvd _ hpq]; exact h1
    have hlt : k % q < q := Nat.mod_lt _ hq
    have hp2 := hp.two_le
    have hsub : p ∣ k % q - k % q % p := Nat.dvd_sub_mod (k % q)
    by_cases hd : p ∣ n + q - 1
    · simp only [hd, if_true] at ha
      have hp3 : 3 ≤ p := by
        by_contra hcon
        have : p = 2 := by omega
        subst this
        omega
      have h2m : 2 % p = 2 := Nat.mod_eq_of_lt (by omega)
      rw [h2m] at ha
      rw [ha] at hsub
      constructor
      · intro h
        have := Nat.dvd_iff_mod_eq_zero.mp h
        omega
      · intro h
        have h2 : k % q ≥ 2 := by
          by_contra hcon
          have : k % q % p = k % q := Nat.mod_eq_of_lt (by omega)
          omega
        have h3 : p ∣ (n + q - k % q) + (k % q - 2) := Nat.dvd_add h hsub
        have e : (n + q - k % q) + (k % q - 2) = n + q - 2 := by omega
        rw [e] at h3
        have h4 := Nat.dvd_sub hd h3
        have e2 : n + q - 1 - (n + q - 2) = 1 := by omega
        rw [e2] at h4
        have := Nat.le_of_dvd one_pos h4
        omega
    · simp only [hd, if_false] at ha
      have h1m : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
      rw [h1m] at ha
      rw [ha] at hsub
      constructor
      · intro h
        have := Nat.dvd_iff_mod_eq_zero.mp h
        omega
      · intro h
        have h2 : k % q ≥ 1 := by
          by_contra hcon
          have h0 : k % q = 0 := by omega
          rw [h0] at ha
          simp at ha
        have h3 : p ∣ (n + q - k % q) + (k % q - 1) := Nat.dvd_add h hsub
        have e : (n + q - k % q) + (k % q - 1) = n + q - 1 := by omega
        rw [e] at h3
        exact hd h3
  refine ⟨k % q, ?_⟩
  simp only [U, Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.mod_lt _ hq, ?_, ?_⟩
  · exact Nat.coprime_of_dvd (fun p hp hpa hpq => (key p hp hpq).1 hpa)
  · exact Nat.coprime_of_dvd (fun p hp hpa hpq => (key p hp hpq).2 hpa)
