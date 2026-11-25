import Mathlib

private lemma sumMultiples (z : ℂ) (d m : ℕ) (hd : 0 < d) :
    (∑ b ∈ (Finset.range (d * m)).filter (fun b => d ∣ b), z ^ b) =
      ∑ j ∈ Finset.range m, (z ^ d) ^ j := by
  have indices : (Finset.range (d * m)).filter (fun b => d ∣ b) =
      (Finset.range m).image (fun j => d * j) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hlt, j, rfl⟩
      exact ⟨j, Nat.lt_of_mul_lt_mul_left hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(Nat.mul_lt_mul_left hd).2 hj, Nat.dvd_mul_right d j⟩
  rw [indices, Finset.sum_image]
  · simp only [pow_mul]
  · intro i _ j _ hij
    exact Nat.eq_of_mul_eq_mul_left hd hij

theorem PEqualNP.Outside.L_goldbach_cert_154 :
    ∀ a:ℕ, Nat.Coprime a 154 → (∑ b ∈ (Finset.range 154).filter (fun b => Nat.Coprime b 154), Complex.exp (((2*Real.pi*(a:ℝ)*b/154:ℝ):ℂ)*Complex.I))/(60:ℂ)=(-1:ℂ)/60 := by
  intro a ha
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / 154))
  have hζ : IsPrimitiveRoot ζ 154 := by
    simpa [ζ] using Complex.isPrimitiveRoot_exp_of_coprime a 154 (by decide) ha
  have phase (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 154 : ℝ) : ℂ) * Complex.I) = ζ ^ b := by
    dsimp only [ζ]
    rw [← Complex.exp_nat_mul]
    apply congrArg Complex.exp
    push_cast
    ring
  let term (d b : ℕ) : ℂ := if d ∣ b then ζ ^ b else 0
  let total (d : ℕ) : ℂ := ∑ b ∈ Finset.range 154, term d b
  have total_eq (d : ℕ) (hd : 0 < d) (hdiv : d ∣ 154) :
      total d = ∑ j ∈ Finset.range (154 / d), (ζ ^ d) ^ j := by
    dsimp only [total, term]
    rw [← Finset.sum_filter]
    simpa only [Nat.mul_div_cancel' hdiv] using sumMultiples ζ d (154 / d) hd
  have vanish (d : ℕ) (hd : 0 < d) (hdiv : d ∣ 154) (hn : 1 < 154 / d) : total d = 0 := by
    rw [total_eq d hd hdiv]
    exact (hζ.pow_of_dvd hd.ne' hdiv).geom_sum_eq_zero hn
  have lastTerm : total 154 = 1 := by
    rw [total_eq 154 (by decide) (dvd_refl _)]
    norm_num
  have inclusion (b : ℕ) : (if Nat.Coprime b 154 then ζ ^ b else 0) =
      term 1 b - term 2 b - term 7 b - term 11 b +
        term 14 b + term 22 b + term 77 b - term 154 b := by
    have unit_iff : Nat.Coprime b 154 ↔ (¬ 2 ∣ b ∧ ¬ 7 ∣ b) ∧ ¬ 11 ∣ b := by
      rw [Nat.coprime_comm, show 154 = 2 * 7 * 11 by decide]
      simp only [Nat.coprime_mul_iff_left, (by decide : Nat.Prime 2).coprime_iff_not_dvd,
        (by decide : Nat.Prime 7).coprime_iff_not_dvd, (by decide : Nat.Prime 11).coprime_iff_not_dvd]
    have h14 : 14 ∣ b ↔ 2 ∣ b ∧ 7 ∣ b := @Nat.lcm_dvd_iff 2 7 b
    have h22 : 22 ∣ b ↔ 2 ∣ b ∧ 11 ∣ b := @Nat.lcm_dvd_iff 2 11 b
    have h77 : 77 ∣ b ↔ 7 ∣ b ∧ 11 ∣ b := @Nat.lcm_dvd_iff 7 11 b
    have h154 : 154 ∣ b ↔ 14 ∣ b ∧ 11 ∣ b := @Nat.lcm_dvd_iff 14 11 b
    by_cases h₂ : 2 ∣ b <;> by_cases h₇ : 7 ∣ b <;> by_cases h₁₁ : 11 ∣ b <;>
      simp [term, unit_iff, h154, h14, h22, h77, h₂, h₇, h₁₁]
  have coefficient : (∑ b ∈ (Finset.range 154).filter (fun b => Nat.Coprime b 154), ζ ^ b) = -1 := by
    rw [Finset.sum_filter]
    simp_rw [inclusion]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    change total 1 - total 2 - total 7 - total 11 + total 14 + total 22 + total 77 - total 154 = -1
    simp (disch := decide) only [lastTerm, vanish, sub_zero, zero_add, zero_sub]
  simp_rw [phase]
  rw [coefficient]
