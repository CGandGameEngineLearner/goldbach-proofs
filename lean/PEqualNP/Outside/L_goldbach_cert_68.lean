import Mathlib

set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_goldbach_cert_68 :
    ∀ a : ℕ, Nat.Coprime a 68 →
      (∑ b ∈ (Finset.range 68).filter (fun b => Nat.Coprime b 68),
        Complex.exp (((2 * Real.pi * (a : ℝ) * b / 68 : ℝ) : ℂ) * Complex.I)) /
        (32 : ℂ) = (0 : ℂ) / 32 := by
  intro a ha
  have hodd : ¬ 2 ∣ a := by
    intro h
    exact (by decide : ¬ (2 : ℕ) ∣ 1) (ha.gcd_eq_one ▸ Nat.dvd_gcd h (by decide))
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a = 2 * k + 1 := ⟨a / 2, by omega⟩
  let t : ℂ := (2 * Real.pi * (a : ℝ) / 68 : ℝ) * Complex.I
  let z := Complex.exp t
  have h34 : z ^ 34 = -1 := by
    change Complex.exp t ^ 34 = -1
    rw [← Complex.exp_nat_mul]
    have ht : (34 : ℂ) * t =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) + (Real.pi : ℂ) * Complex.I := by
      dsimp [t]
      rw [hk]
      push_cast
      ring
    change Complex.exp ((34 : ℂ) * t) = -1
    rw [ht, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]
  have hpow (b : ℕ) :
      Complex.exp (((2 * Real.pi * (a : ℝ) * b / 68 : ℝ) : ℂ) * Complex.I) = z ^ b := by
    refine (congrArg Complex.exp ?_).trans (Complex.exp_nat_mul t b)
    dsimp [t]
    push_cast
    ring
  simp_rw [hpow]
  let flip (b : ℕ) := if b < 34 then b + 34 else b - 34
  have hpres : ∀ b : Fin 68, Nat.Coprime b.val 68 →
      flip b.val < 68 ∧ Nat.Coprime (flip b.val) 68 := by decide
  have hsum : ∑ b ∈ (Finset.range 68).filter (fun b => Nat.Coprime b 68), z ^ b = 0 := by
    apply Finset.sum_involution (fun b _ => flip b)
    · intro b hb
      by_cases hl : b < 34
      · simp [flip, hl, pow_add, h34]
      · have he : b = (b - 34) + 34 := by omega
        calc
          z ^ b + z ^ flip b = z ^ ((b - 34) + 34) + z ^ (b - 34) := by
            simpa only [flip, if_neg hl] using congrArg (fun v : ℂ => v + z ^ (b - 34)) (congrArg (fun m : ℕ => z ^ m) he)
          _ = 0 := by simp [pow_add, h34]
    · intro b _ _
      dsimp [flip]
      split <;> omega
    · intro b hb
      have hp := Finset.mem_filter.mp hb
      have h := hpres ⟨b, Finset.mem_range.mp hp.1⟩ hp.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h.1, h.2⟩
    · intro b hb
      have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
      dsimp [flip]
      split <;> split <;> omega
  rw [hsum]
