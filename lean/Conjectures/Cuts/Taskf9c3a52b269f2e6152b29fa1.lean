import Mathlib

theorem Conjectures.Cuts.Taskf9c3a52b269f2e6152b29fa1 :
∀ (x1 : ℕ),   (∃ (x2 : ℕ) (x3 : ℕ), Nat.Prime x2 ∧ Nat.Prime x3 ∧ x2 * x3 = x1 + (2 : ℕ) ∧ x2 ^ (5 : ℕ) ≤ x1 + (2 : ℕ) ∧ x1 + (2 : ℕ) ≤ x2 ^ (6 : ℕ)) ↔     have x2 : ℕ := (x1 + (2 : ℕ)).minFac;     have x3 : ℕ := (x1 + (2 : ℕ)) / x2;     Nat.Prime x3 ∧ x2 ^ (4 : ℕ) ≤ x3 ∧ x3 ≤ x2 ^ (5 : ℕ) := by
  intro n
  change (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p*q=n+2 ∧ p^5≤n+2 ∧ n+2≤p^6) ↔ _
  let d := (n+2).minFac
  let b := (n+2)/d
  have hd : d.Prime := Nat.minFac_prime (by omega)
  have hprod : d*b = n+2 := Nat.mul_div_cancel' (Nat.minFac_dvd _)
  change _ ↔ b.Prime ∧ d^4 ≤ b ∧ b ≤ d^5
  constructor
  · rintro ⟨p,q,hp,hq,hpq,hlo,hhi⟩
    have h1 : p^4 ≤ q := by
      rw [← hpq, pow_succ] at hlo
      exact Nat.le_of_mul_le_mul_right (by simpa only [Nat.mul_comm p q] using hlo) hp.pos
    have h2 : q ≤ p^5 := by
      rw [← hpq, pow_succ] at hhi
      exact Nat.le_of_mul_le_mul_right (by simpa only [Nat.mul_comm p q] using hhi) hp.pos
    have hpq' : p ≤ q := (Nat.le_self_pow (by decide : (4:ℕ) ≠ 0) p).trans h1
    have hdiv : d ∣ p*q := hpq ▸ Nat.minFac_dvd _
    have hdp : d ≤ p := Nat.minFac_le_of_dvd hp.two_le (hpq ▸ dvd_mul_right p q)
    have deq : d=p := by
      rcases hd.dvd_mul.mp hdiv with hl|hr
      · exact ((Nat.prime_dvd_prime_iff_eq hd hp).mp hl)
      · have := (Nat.prime_dvd_prime_iff_eq hd hq).mp hr
        omega
    have beq : b=q := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      simpa only [← deq] using hprod.trans hpq.symm
    simpa only [deq, beq] using And.intro hq (And.intro h1 h2)
  · rintro ⟨hb, h1, h2⟩
    refine ⟨d,b,hd,hb,hprod,?_,?_⟩
    · rw [← hprod,pow_succ,Nat.mul_comm d b]
      exact Nat.mul_le_mul_right _ h1
    · rw [← hprod,pow_succ,Nat.mul_comm d b]
      exact Nat.mul_le_mul_right _ h2
