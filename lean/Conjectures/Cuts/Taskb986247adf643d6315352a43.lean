import Mathlib.NumberTheory.ArithmeticFunction.Misc

private theorem three_mul_length_le_two {m : ℕ} (hm : 1 < m) :
    (3*m).primeFactorsList.length ≤ 2 ↔ m.Prime := by
  change ArithmeticFunction.cardFactors (3*m) ≤ 2 ↔ m.Prime
  rw [ArithmeticFunction.cardFactors_mul (by decide) (by omega),
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_three,
    ← ArithmeticFunction.cardFactors_eq_one_iff_prime]
  have := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hm
  omega

theorem Conjectures.Cuts.Taskb986247adf643d6315352a43 :
    (have x1 : ℕ → Prop := fun (x1 : ℕ) => Nat.Prime x1 ∧ (x1 + (2 : ℕ)).primeFactorsList.length ≤ (2 : ℕ); ∀ (x2 : ℕ), (1 : ℕ) ≤ x2 → (x1 ((6 : ℕ) * x2 + (1 : ℕ)) ∧ x1 ((6 : ℕ) * x2 + (7 : ℕ)) ↔ Nat.Prime ((6 : ℕ) * x2 + (1 : ℕ)) ∧ Nat.Prime ((6 : ℕ) * x2 + (7 : ℕ)) ∧ Nat.Prime ((2 : ℕ) * x2 + (1 : ℕ)) ∧ Nat.Prime ((2 : ℕ) * x2 + (3 : ℕ)))) := by
  dsimp only
  intro k hk
  rw [show 6*k+1+2 = 3*(2*k+1) by omega,
    show 6*k+7+2 = 3*(2*k+3) by omega,
    three_mul_length_le_two (by omega : 1 < 2*k+1),
    three_mul_length_le_two (by omega : 1 < 2*k+3)]
  exact ⟨fun ⟨⟨hp,hr⟩,hq,hs⟩ => ⟨hp,hq,hr,hs⟩,
    fun ⟨hp,hq,hr,hs⟩ => ⟨⟨hp,hr⟩,hq,hs⟩⟩
