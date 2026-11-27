import Mathlib


namespace Conjectures.TwinPrimes.JumpAbelEndpointIdentity_aux

private lemma recip_step (j : ℕ) (hj : 1 ≤ j) :
    (((j : ℕ) : ℝ))⁻¹ - (((j + 1 : ℕ) : ℝ))⁻¹ = 1 / ((j : ℝ) * ((j : ℝ) + 1)) := by
  have hj0 : ((j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  have hcast : (((j + 1 : ℕ) : ℝ)) = (j : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

private lemma main (a : ℕ → ℝ) :
    ∀ m : ℕ,
      (∑ t ∈ Finset.Ico 2 (m + 2),
          (∑ n ∈ Finset.range (t - 1), a n) / ((t : ℝ) * (t + 1)))
        = ∑ n ∈ Finset.range (m + 1),
            a n * ((n + 2 : ℝ)⁻¹ - (((m + 2 : ℕ) : ℝ))⁻¹) := by
  intro m
  induction m with
  | zero => simp
  | succ k ih =>
    have hk2 : k + 1 + 2 = k + 3 := by omega
    have hk1 : k + 1 + 1 = k + 2 := by omega
    rw [hk2, hk1]
    have hIco : Finset.Ico 2 (k + 3) = insert (k + 2) (Finset.Ico 2 (k + 2)) := by
      have h : k + 3 = (k + 2).succ := by omega
      rw [h, Nat.Ico_succ_right_eq_insert_Ico (by omega)]
    have hsub : k + 2 - 1 = k + 1 := by omega
    have hR : (∑ n ∈ Finset.range (k + 2),
          a n * ((n + 2 : ℝ)⁻¹ - (((k + 3 : ℕ) : ℝ))⁻¹))
        = (∑ n ∈ Finset.range (k + 1),
            a n * ((n + 2 : ℝ)⁻¹ - (((k + 3 : ℕ) : ℝ))⁻¹))
          + a (k + 1) * (((k + 1 : ℝ) + 2)⁻¹ - (((k + 3 : ℕ) : ℝ))⁻¹) := by
      have := Finset.sum_range_succ
        (fun n => a n * ((n + 2 : ℝ)⁻¹ - (((k + 3 : ℕ) : ℝ))⁻¹)) (k + 1)
      simpa [hk1] using this
    have hzero : a (k + 1) * (((k + 1 : ℝ) + 2)⁻¹ - (((k + 3 : ℕ) : ℝ))⁻¹) = 0 := by
      have hc : ((k + 1 : ℝ) + 2) = (((k + 3 : ℕ) : ℝ)) := by push_cast; ring
      rw [hc, sub_self, mul_zero]
    have hsplit : (∑ n ∈ Finset.range (k + 1),
          a n * ((n + 2 : ℝ)⁻¹ - (((k + 3 : ℕ) : ℝ))⁻¹))
        = (∑ n ∈ Finset.range (k + 1),
            a n * ((n + 2 : ℝ)⁻¹ - (((k + 2 : ℕ) : ℝ))⁻¹))
          + (∑ n ∈ Finset.range (k + 1), a n) *
              ((((k + 2 : ℕ) : ℝ))⁻¹ - (((k + 3 : ℕ) : ℝ))⁻¹) := by
      rw [Finset.sum_mul]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro n _
      ring
    rw [hIco, Finset.sum_insert (by simp), hsub]
    rw [hR, hzero, add_zero, hsplit, ih, recip_step (k + 2) (by omega)]
    ring

end Conjectures.TwinPrimes.JumpAbelEndpointIdentity_aux

theorem Conjectures.TwinPrimes.JumpAbelEndpointIdentity :
∀ N : ℕ, 2≤N → (∑ t ∈ Finset.Ico 2 N, (∑ n ∈ Finset.range (t-1), ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2))/((t:ℝ)*(t+1))) = ∑ n ∈ Finset.range (N-1), ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n+2) * ((n+2:ℝ)⁻¹-(N:ℝ)⁻¹) := by
  intro N hN
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, N = m + 2 := ⟨N - 2, by omega⟩
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub]
  exact Conjectures.TwinPrimes.JumpAbelEndpointIdentity_aux.main
    (fun n => ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt (n + 2)) m
