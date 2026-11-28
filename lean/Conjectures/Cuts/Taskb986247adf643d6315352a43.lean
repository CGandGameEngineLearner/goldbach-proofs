import Mathlib

/-!
Premise 2/3 of a cut of L-goldbach-chen-common-prime-two-targets.

The predicate `x1 n = Nat.Prime n ∧ (n + 2).primeFactorsList.length ≤ 2` is a Chen-type
condition: `n` prime and `n + 2` with at most two prime factors counted with multiplicity.
For the two targets `6 * x2 + 1` and `6 * x2 + 7` the shifted numbers factor as
`(6 * x2 + 1) + 2 = 3 * (2 * x2 + 1)` and `(6 * x2 + 7) + 2 = 3 * (2 * x2 + 3)`, so the
Chen conditions on the two targets are exactly the primality of `6 * x2 + 1`, `6 * x2 + 7`,
`2 * x2 + 1` and `2 * x2 + 3`.

The arithmetic core is `len_mul_three`: for `1 < m`, the number `3 * m` has at most two prime
factors (with multiplicity) iff `m` is prime.  Indeed
`(3 * m).primeFactorsList ~ 3.primeFactorsList ++ m.primeFactorsList` (`Nat.perm_primeFactorsList_mul`),
so the length is `1 + m.primeFactorsList.length`; the bound makes that list of length at most one,
and since `m > 1` it is nonempty, hence `[p]`, whose product is `m`, so `m = p` is prime.
Self-contained: Mathlib only, one auxiliary lemma.
-/

namespace Conjectures.Cuts.Taskb986247adf643d6315352a43_aux

/-- For `1 < m`, the number `3 * m` has at most two prime factors counted with multiplicity
exactly when `m` is prime. -/
lemma len_mul_three (m : ℕ) (hm : 1 < m) :
    (3 * m).primeFactorsList.length ≤ 2 ↔ Nat.Prime m := by
  have hm0 : m ≠ 0 := by omega
  have hperm : List.Perm (3 * m).primeFactorsList
      ((3 : ℕ).primeFactorsList ++ m.primeFactorsList) :=
    Nat.perm_primeFactorsList_mul (by norm_num) hm0
  have hlen : (3 * m).primeFactorsList.length = 1 + m.primeFactorsList.length := by
    rw [hperm.length_eq]
    simp [Nat.primeFactorsList_prime (by norm_num : Nat.Prime 3)]
    omega
  constructor
  · intro h
    have h1 : m.primeFactorsList.length ≤ 1 := by omega
    have hne : m.primeFactorsList ≠ [] := (Nat.primeFactorsList_ne_nil m).mpr hm
    have hL : ∃ p, m.primeFactorsList = [p] := by
      cases hL' : m.primeFactorsList with
      | nil => exact absurd hL' hne
      | cons p t =>
        have ht : t.length = 0 := by
          have : (p :: t).length ≤ 1 := by rw [← hL']; exact h1
          simp only [List.length_cons] at this
          omega
        exact ⟨p, by rw [List.eq_nil_of_length_eq_zero ht]⟩
    obtain ⟨p, hp⟩ := hL
    have hmem : p ∈ m.primeFactorsList := by rw [hp]; simp
    have hprod : m.primeFactorsList.prod = m := Nat.prod_primeFactorsList hm0
    rw [hp] at hprod
    have hpm : p = m := by simpa using hprod
    rw [← hpm]
    exact Nat.prime_of_mem_primeFactorsList hmem
  · intro hp
    rw [hlen, Nat.primeFactorsList_prime hp]
    simp

end Conjectures.Cuts.Taskb986247adf643d6315352a43_aux

theorem Conjectures.Cuts.Taskb986247adf643d6315352a43 :
    have x1 : ℕ → Prop := fun (x1 : ℕ) => Nat.Prime x1 ∧ (x1 + (2 : ℕ)).primeFactorsList.length ≤ (2 : ℕ); ∀ (x2 : ℕ), (1 : ℕ) ≤ x2 → (x1 ((6 : ℕ) * x2 + (1 : ℕ)) ∧ x1 ((6 : ℕ) * x2 + (7 : ℕ)) ↔ Nat.Prime ((6 : ℕ) * x2 + (1 : ℕ)) ∧ Nat.Prime ((6 : ℕ) * x2 + (7 : ℕ)) ∧ Nat.Prime ((2 : ℕ) * x2 + (1 : ℕ)) ∧ Nat.Prime ((2 : ℕ) * x2 + (3 : ℕ))) := by
  intro x1 x2 hx2
  dsimp only [x1]
  have e1 : (6 : ℕ) * x2 + 1 + 2 = 3 * (2 * x2 + 1) := by ring
  have e2 : (6 : ℕ) * x2 + 7 + 2 = 3 * (2 * x2 + 3) := by ring
  have h1 : 1 < 2 * x2 + 1 := by omega
  have h2 : 1 < 2 * x2 + 3 := by omega
  rw [e1, e2,
    Conjectures.Cuts.Taskb986247adf643d6315352a43_aux.len_mul_three _ h1,
    Conjectures.Cuts.Taskb986247adf643d6315352a43_aux.len_mul_three _ h2]
  tauto
