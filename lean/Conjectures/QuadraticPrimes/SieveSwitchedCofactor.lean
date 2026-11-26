import Mathlib

theorem Conjectures.QuadraticPrimes.SieveSwitchedCofactor :
    let f := fun k : ℕ => 4*k^2+1
    ∀ p r t : ℕ, 2<p → p.Prime → r<p → p ∣ f r →
      let cofactor := 4*p*t^2+8*r*t+(f r)/p
      f (p*t+r) = p*cofactor ∧
        (8*(r : ℤ))^2 - 4*(4*(p : ℤ))*((f r / p : ℕ) : ℤ) = -16 ∧
        (∀ d : ℕ, Nat.Coprime d p → (d ∣ cofactor ↔ d ∣ f (p*t+r))) := by
  dsimp only
  intro p r t hp2 hpp hr hdiv
  have hmul : p * ((4*r^2+1)/p) = 4*r^2+1 := Nat.mul_div_cancel' hdiv
  have hf1 : 4*(p*t+r)^2+1 = p*(4*p*t^2+8*r*t+(4*r^2+1)/p) := by
    calc 4*(p*t+r)^2+1 = p*(4*p*t^2+8*r*t) + (4*r^2+1) := by ring
      _ = p*(4*p*t^2+8*r*t) + p*((4*r^2+1)/p) := by rw [hmul]
      _ = p*(4*p*t^2+8*r*t+(4*r^2+1)/p) := by ring
  refine ⟨hf1, ?_, ?_⟩
  · have hq : (p:ℤ) * (((4*r^2+1)/p : ℕ) : ℤ) = 4*(r:ℤ)^2+1 := by
      have h : ((p * ((4*r^2+1)/p) : ℕ) : ℤ) = ((4*r^2+1 : ℕ) : ℤ) := by rw [hmul]
      push_cast at h ⊢
      linarith [h]
    linear_combination (-16) * hq
  · intro d hd
    rw [hf1]
    constructor
    · intro h
      exact dvd_mul_of_dvd_right h p
    · intro h
      exact hd.dvd_of_dvd_mul_left h
