import Mathlib.Data.Nat.Prime.Basic

theorem PEqualNP.Outside.L_goldbach_pp_base_unique :
    ∀ p q a b : ℕ, p.Prime → q.Prime → 0<a → 0<b → p^a=q^b → p=q := by
  intro p q a b hp hq ha hb hpow
  have hpqpow : p ∣ q ^ b := by
    rw [← hpow]
    exact dvd_pow_self p (Nat.ne_of_gt ha)
  have hqppow : q ∣ p ^ a := by
    rw [hpow]
    exact dvd_pow_self q (Nat.ne_of_gt hb)
  exact Nat.dvd_antisymm (hp.dvd_of_dvd_pow hpqpow) (hq.dvd_of_dvd_pow hqppow)
