import Mathlib

theorem PEqualNP.Outside.L_goldbach_ram_period :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let ram := fun (q h : ℕ) => Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q)) (fun a => E ((h:ℝ)*(a:ℝ)/(q:ℝ))); ∀ q h, 0<q → ram q (h+q)=ram q h := by
  intro E ram q h hq
  simp only [ram]
  have hper : ∀ (x : ℝ) (m : ℤ), E (x + (m:ℝ)) = E x := by
    intro x m
    simp only [E]
    have e1 : ((2 * Real.pi * (x + (m : ℝ)) : ℝ) : ℂ) * Complex.I =
        ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I + (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      ring
    rw [e1, Complex.exp_add]
    have h1 : Complex.exp ((m : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I m
      push_cast at this ⊢
      exact this
    rw [h1, mul_one]
  apply Finset.sum_congr rfl
  intro a ha
  have hq' : (q:ℝ) ≠ 0 := by
    have : 0 < (q:ℝ) := by exact_mod_cast hq
    positivity
  have e : ((h + q : ℕ) : ℝ) * (a:ℝ) / (q:ℝ) = ((h:ℝ)*(a:ℝ)/(q:ℝ)) + ((a:ℤ):ℝ) := by
    push_cast
    field_simp
  rw [e]
  exact hper ((h:ℝ)*(a:ℝ)/(q:ℝ)) (a:ℤ)
