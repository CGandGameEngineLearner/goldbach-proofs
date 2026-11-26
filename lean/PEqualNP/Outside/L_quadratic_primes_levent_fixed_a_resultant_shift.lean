import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_levent_fixed_a_resultant_shift :
    ∀ a n h d : ℤ, d ∣ n^2+a → d ∣ (n+h)^2+a → d ∣ h^2*(h^2+4*a) := by
  intro a n h d h₁ h₂
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  refine ⟨4*h^2*u - (2*n*h-h^2)*(v-u), ?_⟩
  calc
    h^2*(h^2+4*a) =
        4*h^2*(n^2+a) - (2*n*h-h^2)*((n+h)^2+a-(n^2+a)) := by ring
    _ = d * (4*h^2*u - (2*n*h-h^2)*(v-u)) := by rw [hu, hv]; ring
