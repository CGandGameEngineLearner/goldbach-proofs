import Mathlib

namespace Conjectures.JoshiAbc.LogDomination_aux

theorem multSelf (p : ℕ) (hp : p.Prime) : multiplicity p p = 1 :=
  Irreducible.multiplicity_self hp

theorem multTwoFour : multiplicity 2 4 = 2 := by
  apply multiplicity_eq_of_dvd_of_not_dvd (k := 2)
  · norm_num
  · norm_num

theorem addTwoLePowThree : ∀ k : ℕ, 1 ≤ k → k + 2 ≤ 3 ^ k := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ m ih =>
    intro hk
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; norm_num
    · have ih' := ih (by omega)
      have hstep : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
      omega

end Conjectures.JoshiAbc.LogDomination_aux

theorem Conjectures.JoshiAbc.LogDomination :
    ∀ (p n : ℕ), p.Prime → 2 ≤ n →
      let c : ℕ := if p = 2 then 4 else p; multiplicity p n < (n - 1) * multiplicity p c := by
  intro p n hp hn
  dsimp only
  by_cases hp2 : p = 2
  · subst hp2
    have hc : (if (2 : ℕ) = 2 then 4 else 2) = 4 := by simp
    rw [hc, Conjectures.JoshiAbc.LogDomination_aux.multTwoFour]
    have hdvd : 2 ^ multiplicity 2 n ∣ n := pow_multiplicity_dvd 2 n
    have hle : 2 ^ multiplicity 2 n ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hlt : multiplicity 2 n < 2 ^ multiplicity 2 n := Nat.lt_two_pow_self
    omega
  · have hc : (if p = 2 then 4 else p) = p := by simp [hp2]
    rw [hc, Conjectures.JoshiAbc.LogDomination_aux.multSelf p hp, mul_one]
    have hdvd : p ^ multiplicity p n ∣ n := pow_multiplicity_dvd p n
    have hle : p ^ multiplicity p n ≤ n := Nat.le_of_dvd (by omega) hdvd
    have hp3 : 3 ≤ p := by have h := hp.two_le; omega
    have hpow : 3 ^ multiplicity p n ≤ p ^ multiplicity p n :=
      Nat.pow_le_pow_left hp3 _
    rcases Nat.eq_zero_or_pos (multiplicity p n) with hk0 | hk0
    · omega
    · have h3 := Conjectures.JoshiAbc.LogDomination_aux.addTwoLePowThree _ hk0
      omega
