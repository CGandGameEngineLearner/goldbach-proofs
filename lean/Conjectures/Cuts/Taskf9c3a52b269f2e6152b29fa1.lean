import Mathlib

theorem Conjectures.Cuts.Taskf9c3a52b269f2e6152b29fa1 : (∀ (x1 : ℕ),   (∃ (x2 : ℕ) (x3 : ℕ), Nat.Prime x2 ∧ Nat.Prime x3 ∧ x2 * x3 = x1 + (2 : ℕ) ∧ x2 ^ (5 : ℕ) ≤ x1 + (2 : ℕ) ∧ x1 + (2 : ℕ) ≤ x2 ^ (6 : ℕ)) ↔     have x2 : ℕ := (x1 + (2 : ℕ)).minFac;     have x3 : ℕ := (x1 + (2 : ℕ)) / x2;     Nat.Prime x3 ∧ x2 ^ (4 : ℕ) ≤ x3 ∧ x3 ≤ x2 ^ (5 : ℕ)) := by
  intro n
  let m := n + 2
  let r := m.minFac
  have hr : Nat.Prime r := Nat.minFac_prime (by dsimp [m]; omega)
  have hdiv : r ∣ m := Nat.minFac_dvd m
  change (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p * q = m ∧ p ^ 5 ≤ m ∧ m ≤ p ^ 6) ↔
    (m / r).Prime ∧ r ^ 4 ≤ m / r ∧ m / r ≤ r ^ 5
  constructor
  · rintro ⟨p, q, hp, hq, hpq, hlo, hhi⟩
    have h₄ : p ^ 4 ≤ q := Nat.le_of_mul_le_mul_right
      (show p ^ 4 * p ≤ q * p by simpa only [← pow_succ, mul_comm q p, hpq] using hlo) hp.pos
    have h₅ : q ≤ p ^ 5 := Nat.le_of_mul_le_mul_right
      (show q * p ≤ p ^ 5 * p by simpa only [← pow_succ, mul_comm q p, hpq] using hhi) hp.pos
    have hp_le : p ≤ q := (Nat.le_self_pow (by decide : 4 ≠ 0) p).trans h₄
    have hr_le : r ≤ p := Nat.minFac_le_of_dvd hp.two_le ⟨q, hpq.symm⟩
    have hr_eq : r = p := by
      rcases hr.dvd_mul.mp (show r ∣ p * q by rw [hpq]; exact hdiv) with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hr hp).mp h
      · have heq := (Nat.prime_dvd_prime_iff_eq hr hq).mp h
        omega
    have hquot : m / r = q := by rw [hr_eq, ← hpq, Nat.mul_div_cancel_left _ hp.pos]
    rw [hquot, hr_eq]
    exact ⟨hq, h₄, h₅⟩
  · rintro ⟨hq, hlo, hhi⟩
    have hprod : r * (m / r) = m := by rw [mul_comm, Nat.div_mul_cancel hdiv]
    refine ⟨r, m / r, hr, hq, hprod, ?_, ?_⟩
    · calc r ^ 5 = r * r ^ 4 := by ring
           _ ≤ r * (m / r) := Nat.mul_le_mul_left _ hlo
           _ = m := hprod
    · calc m = r * (m / r) := hprod.symm
           _ ≤ r * r ^ 5 := Nat.mul_le_mul_left _ hhi
           _ = r ^ 6 := by ring
