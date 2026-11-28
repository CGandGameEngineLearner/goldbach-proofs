import Mathlib

/-!
Premise 1/4 of a cut of L-goldbach-chen-coprime-shift-products.

If `x1 ≠ x2` and each of `x1`, `x2` has at most two prime factors counted with multiplicity,
then `x1` and `x2` share at most one prime factor.

Indeed, suppose two distinct primes `p ≠ q` divide both `x1` and `x2`.  Then `p` and `q` both
belong to `x.primeFactorsList` for `x = x1, x2` (membership in `primeFactors` is membership in
`primeFactorsList`), so as a multiset that list is `p ::ₘ q ::ₘ u`; the length bound forces
`u = 0`, and the product of the list, which is `x` itself, is `p * q`.  Hence `x1 = p * q = x2`,
contradicting `x1 ≠ x2`.  Self-contained: Mathlib only.
-/

namespace Conjectures.Cuts.Taskc2471cd7110ea42affd69679_aux

/-- Two distinct prime factors of `n` exhaust a factorization of length at most two. -/
private lemma eq_mul_of_two_mem {n p q : ℕ} (hp : p ∈ n.primeFactorsList)
    (hq : q ∈ n.primeFactorsList) (hpq : p ≠ q) (hlen : n.primeFactorsList.length ≤ 2) :
    n = p * q := by
  have hn0 : n ≠ 0 := by
    intro h0
    subst h0
    simp at hp
  set L : List ℕ := n.primeFactorsList
  have hpM : p ∈ (L : Multiset ℕ) := Multiset.mem_coe.mpr hp
  have hqM : q ∈ (L : Multiset ℕ) := Multiset.mem_coe.mpr hq
  obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hpM
  have hqt : q ∈ t := by
    rcases Multiset.mem_cons.mp (ht ▸ hqM) with h | h
    · exact absurd h.symm hpq
    · exact h
  obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem hqt
  have hM : (L : Multiset ℕ) = p ::ₘ q ::ₘ u := by rw [ht, hu]
  have hcard : (L : Multiset ℕ).card = u.card + 2 := by
    rw [hM]; simp
  have hlen' : (L : Multiset ℕ).card ≤ 2 := by
    rw [Multiset.coe_card]; exact hlen
  have hu0 : u = 0 := by
    have : u.card = 0 := by omega
    exact Multiset.card_eq_zero.mp this
  have hprod : (L : Multiset ℕ).prod = p * q := by
    rw [hM, hu0]
    simp
  have hprodL : L.prod = n := Nat.prod_primeFactorsList hn0
  calc n = L.prod := hprodL.symm
    _ = (L : Multiset ℕ).prod := (Multiset.prod_coe L).symm
    _ = p * q := hprod

end Conjectures.Cuts.Taskc2471cd7110ea42affd69679_aux

theorem Conjectures.Cuts.Taskc2471cd7110ea42affd69679 :
    ∀ (x1 x2 : ℕ), x1 ≠ x2 → x1.primeFactorsList.length ≤ (2 : ℕ) → x2.primeFactorsList.length ≤ (2 : ℕ) → (x1.primeFactors ∩ x2.primeFactors).card ≤ (1 : ℕ) := by
  intro x1 x2 hne h1 h2
  by_contra h
  have h2' : 1 < (x1.primeFactors ∩ x2.primeFactors).card := by omega
  obtain ⟨p, q, hp, hq, hpq⟩ := Finset.one_lt_card_iff.mp h2'
  have hp1 : p ∈ x1.primeFactors := (Finset.mem_inter.mp hp).1
  have hp2 : p ∈ x2.primeFactors := (Finset.mem_inter.mp hp).2
  have hq1 : q ∈ x1.primeFactors := (Finset.mem_inter.mp hq).1
  have hq2 : q ∈ x2.primeFactors := (Finset.mem_inter.mp hq).2
  have e1 : x1 = p * q := Conjectures.Cuts.Taskc2471cd7110ea42affd69679_aux.eq_mul_of_two_mem
    (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp1)
    (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hq1) hpq h1
  have e2 : x2 = p * q := Conjectures.Cuts.Taskc2471cd7110ea42affd69679_aux.eq_mul_of_two_mem
    (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hp2)
    (Nat.mem_primeFactors_iff_mem_primeFactorsList.mp hq2) hpq h2
  exact hne (e1.trans e2.symm)
