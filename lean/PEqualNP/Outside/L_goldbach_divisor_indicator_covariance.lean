import Mathlib

theorem PEqualNP.Outside.L_goldbach_divisor_indicator_covariance :
    let X := fun (p t : ℕ) => (p:ℝ)*(if p ∣ t then 1 else 0)-1; ∀ (N p q : ℕ), 0 < N → Nat.Prime p → Nat.Prime q → p ∣ N → q ∣ N → ((∑ t ∈ Finset.range N, X p t * X q t)/(N:ℝ)) = if p=q then (p:ℝ)-1 else 0 := by
  intro X N p q hN hp hq hpN hqN
  let Y := fun (d t : ℕ) => (d : ℝ) * (if d ∣ t then 1 else 0)
  have hmean (d : ℕ) (hd : d ∣ N) : (∑ t ∈ Finset.range N, Y d t) = N := by
    have shift := Finset.sum_range_succ' (fun t : ℕ => if d ∣ t then (1 : ℝ) else 0) N
    rw [Finset.sum_range_succ] at shift
    simp only [hd, dvd_zero, if_true, add_right_cancel_iff] at shift
    dsimp only [Y]
    rw [← Finset.mul_sum, shift, Finset.sum_boole, Nat.card_multiples]
    exact_mod_cast Nat.mul_div_cancel' hd
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  by_cases heq : p = q
  · subst q
    rw [if_pos rfl, div_eq_iff hNr]
    have hdiag (t : ℕ) : X p t * X p t = ((p : ℝ) - 2) * Y p t + 1 := by
      dsimp only [X, Y]
      split <;> ring
    simp_rw [hdiag]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hmean p hpN]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    ring
  · rw [if_neg heq, div_eq_iff hNr, zero_mul]
    have hc := (Nat.coprime_primes hp hq).mpr heq
    have hpqN := hc.mul_dvd_of_dvd_of_dvd hpN hqN
    have hcross (t : ℕ) : Y p t * Y q t = Y (p*q) t := by
      have hiff : p*q ∣ t ↔ p ∣ t ∧ q ∣ t :=
        ⟨fun h => ⟨dvd_trans (dvd_mul_right p q) h, dvd_trans (dvd_mul_left q p) h⟩,
          fun h => hc.mul_dvd_of_dvd_of_dvd h.1 h.2⟩
      by_cases hpt : p ∣ t <;> by_cases hqt : q ∣ t <;> simp [Y, hiff, hpt, hqt]
    have hexpand (t : ℕ) : X p t * X q t = Y (p*q) t - Y p t - Y q t + 1 := by
      change (Y p t - 1) * (Y q t - 1) = _
      rw [← hcross]
      ring
    simp_rw [hexpand]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      hmean _ hpqN, hmean p hpN, hmean q hqN]
    simp
