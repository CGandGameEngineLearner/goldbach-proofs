import Mathlib

theorem PEqualNP.Outside.L_goldbach_cert_140 :
    ∀ a:ℕ, Nat.Coprime a 140 → (∑ b ∈ (Finset.range 140).filter (fun b => Nat.Coprime b 140), Complex.exp (((2*Real.pi*(a:ℝ)*b/140:ℝ):ℂ)*Complex.I))/(48:ℂ)=(0:ℂ)/48 := by
  intro a ha
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / 140))
  have hζ : IsPrimitiveRoot ζ 140 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp_of_coprime a 140 (by decide) ha
  have half : ζ ^ 70 = -1 := by
    have h : IsPrimitiveRoot (ζ ^ 70) 2 := hζ.pow_of_dvd (by decide) (by decide)
    exact h.eq_neg_one_of_two_right
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 140 : ℝ) : ℂ) * Complex.I) = ζ ^ b := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    ring
  have unit_iff (k : ℕ) : Nat.Coprime k 140 ↔ (¬ 2 ∣ k ∧ ¬ 5 ∣ k) ∧ ¬ 7 ∣ k := by
    rw [Nat.coprime_comm, show 140 = 2 * 2 * 5 * 7 by decide]
    simp only [Nat.coprime_mul_iff_left, (by decide : Nat.Prime 2).coprime_iff_not_dvd,
      (by decide : Nat.Prime 5).coprime_iff_not_dvd, (by decide : Nat.Prime 7).coprime_iff_not_dvd, and_self]
  have shift (b : ℕ) : Nat.Coprime (70 + b) 140 ↔ Nat.Coprime b 140 := by
    rw [unit_iff, unit_iff]
    omega
  have cancel : (∑ b ∈ (Finset.range 140).filter (fun b => Nat.Coprime b 140), ζ ^ b) = 0 := by
    rw [Finset.sum_filter]
    change (∑ b ∈ Finset.range (70 + 70), if Nat.Coprime b 140 then ζ ^ b else 0) = 0
    rw [Finset.sum_range_add, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : Nat.Coprime b 140
    · rw [ite_eq_left hb, ite_eq_left ((shift b).2 hb), pow_add, half, neg_one_mul, add_neg_cancel]
    · rw [ite_eq_right hb, ite_eq_right (fun h => hb ((shift b).1 h)), add_zero]
  simp_rw [phase]
  rw [cancel]
