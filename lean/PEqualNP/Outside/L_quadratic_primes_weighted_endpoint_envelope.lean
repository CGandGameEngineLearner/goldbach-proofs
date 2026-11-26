import Mathlib

private theorem sum_le_card_mul {ι : Type} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) (B : ℝ) (h : ∀ i ∈ s, f i ≤ B) :
    (∑ i ∈ s, f i) ≤ (s.card : ℝ) * B := by
  calc
    (∑ i ∈ s, f i) ≤ ∑ _i ∈ s, B := Finset.sum_le_sum h
    _ = (s.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

theorem PEqualNP.Outside.L_quadratic_primes_weighted_endpoint_envelope :
    ∀ (ι : Type) [DecidableEq ι] (rows near : Finset ι) (f : ι → ℝ) (x C D α β γ : ℝ), 1 ≤ x → 0 ≤ C → 0 ≤ D → near ⊆ rows → (rows.card : ℝ) ≤ C * x ^ α → (near.card : ℝ) ≤ C * x ^ γ → (∀ i ∈ near, f i ≤ D * (Real.log x)^2) → (∀ i ∈ rows \ near, f i ≤ D * x ^ (α / 2 - β) * (Real.log x)^2) → (∑ i ∈ rows, f i) ≤ C * D * (x ^ γ + x ^ (3 * α / 2 - β)) * (Real.log x)^2 := by
  intro ι _ rows near f x C D α β γ hx hC hD hsub hrows hnear hnear_point hfar_point
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 ≤ (Real.log x) ^ 2 := sq_nonneg _
  have hnear_weight : 0 ≤ D * (Real.log x) ^ 2 := mul_nonneg hD hlog
  have hfar_weight : 0 ≤ D * x ^ (α / 2 - β) * (Real.log x) ^ 2 :=
    mul_nonneg (mul_nonneg hD (Real.rpow_pos_of_pos hxpos _).le) hlog
  have hnear_sum :
      (∑ i ∈ near, f i) ≤
        (near.card : ℝ) * (D * (Real.log x) ^ 2) :=
    sum_le_card_mul near f _ hnear_point
  have hnear_bound :
      (near.card : ℝ) * (D * (Real.log x) ^ 2) ≤
        (C * x ^ γ) * (D * (Real.log x) ^ 2) :=
    mul_le_mul_of_nonneg_right hnear hnear_weight
  have hfar_card :
      (((rows \ near).card : ℕ) : ℝ) ≤ (rows.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hfar_card_bound :
      (((rows \ near).card : ℕ) : ℝ) ≤ C * x ^ α := hfar_card.trans hrows
  have hfar_sum :
      (∑ i ∈ rows \ near, f i) ≤
        (((rows \ near).card : ℕ) : ℝ) *
          (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) :=
    sum_le_card_mul (rows \ near) f _ hfar_point
  have hfar_bound :
      (((rows \ near).card : ℕ) : ℝ) *
          (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) ≤
        (C * x ^ α) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) :=
    mul_le_mul_of_nonneg_right hfar_card_bound hfar_weight
  have hpow :
      x ^ α * x ^ (α / 2 - β) = x ^ (3 * α / 2 - β) := by
    calc
      x ^ α * x ^ (α / 2 - β) = x ^ (α + (α / 2 - β)) :=
        (Real.rpow_add hxpos _ _).symm
      _ = x ^ (3 * α / 2 - β) := by
        congr 1
        ring
  have hfar_algebra :
      (C * x ^ α) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) =
        C * D * x ^ (3 * α / 2 - β) * (Real.log x) ^ 2 := by
    calc
      (C * x ^ α) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) =
          C * D * (x ^ α * x ^ (α / 2 - β)) * (Real.log x) ^ 2 := by ring
      _ = C * D * x ^ (3 * α / 2 - β) * (Real.log x) ^ 2 := by rw [hpow]
  calc
    (∑ i ∈ rows, f i) =
        (∑ i ∈ rows \ near, f i) + ∑ i ∈ near, f i := by
          symm
          exact Finset.sum_sdiff hsub
    _ ≤ (((rows \ near).card : ℕ) : ℝ) *
          (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) +
        (near.card : ℝ) * (D * (Real.log x) ^ 2) :=
      add_le_add hfar_sum hnear_sum
    _ ≤ (C * x ^ α) * (D * x ^ (α / 2 - β) * (Real.log x) ^ 2) +
        (C * x ^ γ) * (D * (Real.log x) ^ 2) :=
      add_le_add hfar_bound hnear_bound
    _ = C * D * (x ^ γ + x ^ (3 * α / 2 - β)) * (Real.log x) ^ 2 := by
      rw [hfar_algebra]
      ring
