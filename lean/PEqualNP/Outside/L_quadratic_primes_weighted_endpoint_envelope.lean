import Mathlib

theorem PEqualNP.Outside.L_quadratic_primes_weighted_endpoint_envelope :
    ∀ (ι : Type) [DecidableEq ι] (rows near : Finset ι) (f : ι → ℝ) (x C D α β γ : ℝ),
      1 ≤ x → 0 ≤ C → 0 ≤ D → near ⊆ rows → (rows.card : ℝ) ≤ C * x ^ α →
      (near.card : ℝ) ≤ C * x ^ γ → (∀ i ∈ near, f i ≤ D * (Real.log x)^2) →
      (∀ i ∈ rows \ near, f i ≤ D * x ^ (α / 2 - β) * (Real.log x)^2) →
      (∑ i ∈ rows, f i) ≤ C * D * (x ^ γ + x ^ (3 * α / 2 - β)) * (Real.log x)^2 := by
  intro ι _ rows near f x C D α β γ hx hC hD hsub hrows hnear hf1 hf2
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hL : (0:ℝ) ≤ (Real.log x)^2 := sq_nonneg _
  have hN : ∑ i ∈ near, f i ≤ C * D * x ^ γ * (Real.log x)^2 := by
    have h1 : ∑ i ∈ near, f i ≤ ∑ _i ∈ near, D * (Real.log x)^2 :=
      Finset.sum_le_sum (fun i hi => hf1 i hi)
    have h2 : ∑ _i ∈ near, D * (Real.log x)^2 = (near.card : ℝ) * (D * (Real.log x)^2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h3 : (near.card : ℝ) * (D * (Real.log x)^2) ≤ (C * x ^ γ) * (D * (Real.log x)^2) :=
      mul_le_mul_of_nonneg_right hnear (mul_nonneg hD hL)
    have h4 : (C * x ^ γ) * (D * (Real.log x)^2) = C * D * x ^ γ * (Real.log x)^2 := by ring
    linarith
  have hR : ∑ i ∈ rows \ near, f i ≤ C * D * x ^ (3 * α / 2 - β) * (Real.log x)^2 := by
    have hnn : (0:ℝ) ≤ D * x ^ (α / 2 - β) * (Real.log x)^2 :=
      mul_nonneg (mul_nonneg hD (Real.rpow_nonneg hx0 _)) hL
    have h1 : ∑ i ∈ rows \ near, f i ≤ ∑ _i ∈ rows \ near, D * x ^ (α / 2 - β) * (Real.log x)^2 :=
      Finset.sum_le_sum (fun i hi => hf2 i hi)
    have h2 : ∑ _i ∈ rows \ near, D * x ^ (α / 2 - β) * (Real.log x)^2
        = ((rows \ near).card : ℝ) * (D * x ^ (α / 2 - β) * (Real.log x)^2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((rows \ near).card : ℝ) ≤ C * x ^ α := by
      have h : (rows \ near).card ≤ rows.card := Finset.card_le_card (Finset.sdiff_subset (s := rows) (t := near))
      have h' : ((rows \ near).card : ℝ) ≤ (rows.card : ℝ) := by exact_mod_cast h
      linarith
    have h3 : ((rows \ near).card : ℝ) * (D * x ^ (α / 2 - β) * (Real.log x)^2)
        ≤ (C * x ^ α) * (D * x ^ (α / 2 - β) * (Real.log x)^2) :=
      mul_le_mul_of_nonneg_right hcard hnn
    have h4 : (C * x ^ α) * (D * x ^ (α / 2 - β) * (Real.log x)^2)
        = C * D * x ^ (3 * α / 2 - β) * (Real.log x)^2 := by
      have hxp : x ^ α * x ^ (α / 2 - β) = x ^ (α + (α / 2 - β)) :=
        (Real.rpow_add hxpos α (α / 2 - β)).symm
      have hsum : α + (α / 2 - β) = 3 * α / 2 - β := by ring
      calc (C * x ^ α) * (D * x ^ (α / 2 - β) * (Real.log x)^2)
          = C * D * (x ^ α * x ^ (α / 2 - β)) * (Real.log x)^2 := by ring
        _ = C * D * x ^ (α + (α / 2 - β)) * (Real.log x)^2 := by rw [hxp]
        _ = C * D * x ^ (3 * α / 2 - β) * (Real.log x)^2 := by rw [hsum]
    linarith
  have hkey : ∑ i ∈ rows, f i = ∑ i ∈ rows \ near, f i + ∑ i ∈ near, f i :=
    (Finset.sum_sdiff hsub).symm
  rw [hkey]
  have hfin : C * D * x ^ (3 * α / 2 - β) * (Real.log x)^2 + C * D * x ^ γ * (Real.log x)^2
      = C * D * (x ^ γ + x ^ (3 * α / 2 - β)) * (Real.log x)^2 := by ring
  linarith
