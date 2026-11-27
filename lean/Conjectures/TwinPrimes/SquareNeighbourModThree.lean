import Mathlib

namespace Conjectures.TwinPrimes.SquareNeighbourModThree_aux

/-- A prime `p ≥ 4` satisfies `3 ∣ p ^ 2 + 2`: `p ≠ 3`, so `p ≡ ±1 [3]` and `p ^ 2 ≡ 1 [3]`. -/
private lemma three_dvd_sq_add_two {p : ℕ} (hp : p.Prime) (hp4 : 4 ≤ p) : 3 ∣ p ^ 2 + 2 := by
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
    have h3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases h3 with h | h | h
    · exfalso
      have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
      have hpeq : p = 3 := (hp.dvd_iff_eq (by norm_num)).mp hdvd
      omega
    · exact Or.inl h
    · exact Or.inr h
  have hsq : (p ^ 2) % 3 = 1 := by
    rw [Nat.pow_mod]
    rcases hmod with h | h
    · simp [h]
    · simp [h]
  have h0 : (p ^ 2 + 2) % 3 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero h0

/-- `10 ≤ p ^ 2` forces `4 ≤ p`. -/
private lemma four_le_of_sq_ge_ten {p : ℕ} (h : 10 ≤ p ^ 2) : 4 ≤ p := by
  by_contra hlt
  have hp3 : p ≤ 3 := by omega
  have h9 : p ^ 2 ≤ 9 := by
    calc p ^ 2 = p * p := by ring
      _ ≤ 3 * 3 := Nat.mul_le_mul hp3 hp3
      _ = 9 := by norm_num
  omega

end Conjectures.TwinPrimes.SquareNeighbourModThree_aux

/-- PREPUB twin-primes gap `L-twin-primes-square-neighbour-mod-three`:
square contamination in a gap-two window.  If `n ≥ 10` carries von Mangoldt mass at both `n` and
`n + 2`, then `n = p ^ a` and `n + 2 = q ^ b` with `p, q` prime and `a, b ≥ 1`; if they are not
both prime, then either one of the two exponents is at least `3`, or `n` is prime and `n + 2` is a
prime square.  Indeed `a = 2` is impossible next to `b = 1` or `b = 2`: a prime square `p ^ 2` with
`p ≥ 5` is `1 [3]`, so `p ^ 2 + 2 ≡ 0 [3]`, forcing the neighbour to be `3` and `n < 10`. -/
theorem Conjectures.TwinPrimes.SquareNeighbourModThree :
    ∀ n : ℕ, 10 ≤ n → ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) ≠ 0 → (¬ n.Prime ∨ ¬ (n+2).Prime) → (∃ p a : ℕ, p.Prime ∧ 3 ≤ a ∧ (p^a=n ∨ p^a=n+2)) ∨ (n.Prime ∧ ∃ p : ℕ, p.Prime ∧ p^2=n+2) := by
  intro n hn hΛ hnot
  have hΛn : ArithmeticFunction.vonMangoldt n ≠ 0 := fun h => hΛ (by rw [h, zero_mul])
  have hΛn2 : ArithmeticFunction.vonMangoldt (n + 2) ≠ 0 := fun h => hΛ (by rw [h, mul_zero])
  obtain ⟨p, a, hp, ha, hpa⟩ :=
    (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛn)
  obtain ⟨q, b, hq, hb, hqb⟩ :=
    (isPrimePow_nat_iff (n + 2)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛn2)
  have ha3 : 3 ≤ a ∨ a ≤ 2 := by omega
  rcases ha3 with ha3 | ha3
  · exact Or.inl ⟨p, a, hp, ha3, Or.inl hpa⟩
  have hb3 : 3 ≤ b ∨ b ≤ 2 := by omega
  rcases hb3 with hb3 | hb3
  · exact Or.inl ⟨q, b, hq, hb3, Or.inr hqb⟩
  have ha' : a = 1 ∨ a = 2 := by omega
  have hb' : b = 1 ∨ b = 2 := by omega
  have hpa' := hpa
  have hqb' := hqb
  rcases ha' with ha1 | ha2
  · rcases hb' with hb1 | hb2
    · -- both exponents are 1: both `n` and `n + 2` are prime, excluded by hypothesis
      exfalso
      rw [ha1, pow_one] at hpa'
      rw [hb1, pow_one] at hqb'
      have hnp : n.Prime := by rw [← hpa']; exact hp
      have hn2p : (n + 2).Prime := by rw [← hqb']; exact hq
      rcases hnot with h | h
      · exact h hnp
      · exact h hn2p
    · -- `n = p` prime, `n + 2 = q ^ 2`: the second disjunct
      right
      rw [ha1, pow_one] at hpa'
      rw [hb2] at hqb'
      refine ⟨?_, q, hq, hqb'⟩
      rw [← hpa']; exact hp
  · rcases hb' with hb1 | hb2
    · -- `n = p ^ 2`, `n + 2 = q` prime: impossible for `n ≥ 10`
      exfalso
      rw [ha2] at hpa'
      rw [hb1, pow_one] at hqb'
      have hp4 : 4 ≤ p :=
        Conjectures.TwinPrimes.SquareNeighbourModThree_aux.four_le_of_sq_ge_ten (hpa' ▸ hn)
      have hdvd : 3 ∣ q := by
        have h3 : 3 ∣ p ^ 2 + 2 :=
          Conjectures.TwinPrimes.SquareNeighbourModThree_aux.three_dvd_sq_add_two hp hp4
        rw [hqb', ← hpa']
        exact h3
      have hq3 : q = 3 := (hq.dvd_iff_eq (by norm_num)).mp hdvd
      omega
    · -- `n = p ^ 2`, `n + 2 = q ^ 2`: impossible for `n ≥ 10`
      exfalso
      rw [ha2] at hpa'
      rw [hb2] at hqb'
      have hp4 : 4 ≤ p :=
        Conjectures.TwinPrimes.SquareNeighbourModThree_aux.four_le_of_sq_ge_ten (hpa' ▸ hn)
      have hdvd : 3 ∣ q ^ 2 := by
        have h3 : 3 ∣ p ^ 2 + 2 :=
          Conjectures.TwinPrimes.SquareNeighbourModThree_aux.three_dvd_sq_add_two hp hp4
        rw [hqb', ← hpa']
        exact h3
      have hdvdq : 3 ∣ q := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      have hq3 : q = 3 := (hq.dvd_iff_eq (by norm_num)).mp hdvdq
      have hn9 : n + 2 = 9 := by rw [← hqb', hq3]; norm_num
      omega
