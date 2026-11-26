import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_line_fiber_param :
    ∀ (a b N r₀ s₀ : ℤ), 0 < a → 0 < b → a*r₀+b*s₀=N → let g := (Int.gcd a b : ℤ); ∀ r s : ℤ, a*r+b*s=N ↔ ∃ j : ℤ, r=r₀+(b/g)*j ∧ s=s₀-(a/g)*j := by
  intro a b N r₀ s₀ ha hb hN
  dsimp only
  intro r s
  have hga : (↑(a.gcd b) : ℤ) ∣ a := Int.gcd_dvd_left a b
  have hgb : (↑(a.gcd b) : ℤ) ∣ b := Int.gcd_dvd_right a b
  have hgnz : a.gcd b ≠ 0 := by
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    linarith [h0.1]
  have hgpos : 0 < a.gcd b := Nat.pos_of_ne_zero hgnz
  have hgne : (↑(a.gcd b) : ℤ) ≠ 0 := by exact_mod_cast hgnz
  have ha' : (a / ↑(a.gcd b)) * ↑(a.gcd b) = a := Int.ediv_mul_cancel hga
  have hb' : (b / ↑(a.gcd b)) * ↑(a.gcd b) = b := Int.ediv_mul_cancel hgb
  have hcop : IsCoprime (a / ↑(a.gcd b)) (b / ↑(a.gcd b)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact Int.gcd_div_gcd_div_gcd hgpos
  have hb'ne : (b / ↑(a.gcd b)) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hb'
    linarith [hb']
  have hab : a * (b / ↑(a.gcd b)) = b * (a / ↑(a.gcd b)) := by
    apply mul_right_cancel₀ hgne
    calc a * (b / ↑(a.gcd b)) * ↑(a.gcd b) = a * b := by rw [mul_assoc, Int.ediv_mul_cancel hgb]
      _ = b * (a / ↑(a.gcd b)) * ↑(a.gcd b) := by rw [mul_assoc, Int.ediv_mul_cancel hga]; ring
  constructor
  · intro h
    have key : (a / ↑(a.gcd b)) * (r - r₀) + (b / ↑(a.gcd b)) * (s - s₀) = 0 := by
      have e1 : a * (r - r₀) + b * (s - s₀) = 0 := by linarith
      have h2 : (↑(a.gcd b) : ℤ) * ((a / ↑(a.gcd b)) * (r - r₀) + (b / ↑(a.gcd b)) * (s - s₀)) = 0 := by
        calc (↑(a.gcd b) : ℤ) * ((a / ↑(a.gcd b)) * (r - r₀) + (b / ↑(a.gcd b)) * (s - s₀))
            = ((a / ↑(a.gcd b)) * ↑(a.gcd b)) * (r - r₀) + ((b / ↑(a.gcd b)) * ↑(a.gcd b)) * (s - s₀) := by ring
          _ = a * (r - r₀) + b * (s - s₀) := by rw [ha', hb']
          _ = 0 := e1
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hgne
      · exact h3
    have hdvd : (b / ↑(a.gcd b)) ∣ (r - r₀) := by
      have h1 : (a / ↑(a.gcd b)) * (r - r₀) = (b / ↑(a.gcd b)) * (-(s - s₀)) := by linarith [key]
      exact hcop.symm.dvd_of_dvd_mul_left ⟨-(s - s₀), h1⟩
    obtain ⟨j, hj⟩ := hdvd
    refine ⟨j, by linarith [hj], ?_⟩
    have h3 : (b / ↑(a.gcd b)) * ((a / ↑(a.gcd b)) * j + (s - s₀)) = 0 := by
      rw [hj] at key
      ring_nf at key ⊢
      linarith [key]
    have h4 : (a / ↑(a.gcd b)) * j + (s - s₀) = 0 := (mul_eq_zero.mp h3).resolve_left hb'ne
    linarith [h4]
  · rintro ⟨j, rfl, rfl⟩
    have e : a * (r₀ + b / ↑(a.gcd b) * j) + b * (s₀ - a / ↑(a.gcd b) * j) = a * r₀ + b * s₀ := by
      linear_combination j * hab
    linarith [e, hN]
