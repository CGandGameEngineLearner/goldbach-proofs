import Mathlib

/-- Sharp transfer of a joint squared error budget to the anti-spike comparison.
The coefficient at the left endpoint occurs on both sides of the comparison. -/
theorem PEqualNP.Outside.L_goldbach_antispike_shared_coefficient_error :
    ∀ (n : ℕ) (a w : ℕ → ℝ) (δ T : ℝ), 0 ≤ δ →
    let s := Finset.Icc n (2 * n)
    ((∀ c : ℕ → ℝ, (∑ m ∈ s, (c m - a m) ^ 2) ≤ δ ^ 2 →
      (∑ m ∈ s, w m * c m) - c n ≤ T) ↔
      (∑ m ∈ s, w m * a m) - a n +
        δ * Real.sqrt (1 - 2 * w n + ∑ m ∈ s, (w m) ^ 2) ≤ T) := by
  intro n a w δ T hδ
  dsimp only
  let s := Finset.Icc n (2 * n)
  have hn : n ∈ s := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  let b := fun m => w m - (if m = n then 1 else 0)
  let E := ∑ m ∈ s, (b m) ^ 2
  have hdot (e : ℕ → ℝ) :
      (∑ m ∈ s, b m * e m) = (∑ m ∈ s, w m * e m) - e n := by
    simp [b, sub_mul, Finset.sum_sub_distrib, ite_mul, hn]
  have hE : E = 1 - 2 * w n + ∑ m ∈ s, (w m) ^ 2 := by
    have hexp (m : ℕ) : (b m) ^ 2 =
        (w m)^2 + (if m = n then (1 - 2 * w n) else 0) := by
      by_cases h : m = n
      · subst m
        simp [b]
        ring
      · simp [b, h]
    simp [E, hexp, Finset.sum_add_distrib, hn, add_comm]
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun m _ => sq_nonneg (b m)
  have hshift (c : ℕ → ℝ) : (∑ m ∈ s, w m * c m) - c n =
      ((∑ m ∈ s, w m * a m) - a n) + ∑ m ∈ s, b m * (c m - a m) := by
    rw [hdot]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    ring
  change (∀ c : ℕ → ℝ, (∑ m ∈ s, (c m - a m)^2) ≤ δ^2 →
    (∑ m ∈ s, w m * c m) - c n ≤ T) ↔ _
  change _ ↔ (∑ m ∈ s, w m * a m) - a n + δ * Real.sqrt
    (1 - 2 * w n + ∑ m ∈ s, (w m)^2) ≤ T
  rw [← hE]
  constructor
  · intro h
    by_cases hz : Real.sqrt E = 0
    · simpa [hz] using h a (by simpa using sq_nonneg δ)
    have hsq := Real.sq_sqrt hE0
    let k := δ / Real.sqrt E
    have hk : k * Real.sqrt E = δ := div_mul_cancel₀ δ hz
    have hcost : k ^ 2 * E = δ ^ 2 := by
      calc
        k ^ 2 * E = (k * Real.sqrt E) ^ 2 := by rw [mul_pow, hsq]
        _ = δ ^ 2 := by rw [hk]
    have hgain : k * E = δ * Real.sqrt E := by
      calc
        k * E = (k * Real.sqrt E) * Real.sqrt E := by rw [mul_assoc, ← sq, hsq]
        _ = δ * Real.sqrt E := by rw [hk]
    let c := fun m => a m + k * b m
    have herr (m : ℕ) : c m - a m = k * b m := by simp [c]
    have hc : (∑ m ∈ s, (c m - a m)^2) ≤ δ^2 := by
      simp_rw [herr, mul_pow]
      rw [← Finset.mul_sum]
      exact hcost.le
    have hlin : (∑ m ∈ s, b m * (c m - a m)) = δ * Real.sqrt E := by
      simp_rw [herr, show ∀ m, b m * (k * b m) = k * b m ^ 2 from fun m => by ring]
      rw [← Finset.mul_sum]
      exact hgain
    simpa only [hshift c, hlin] using h c hc
  · intro h c hc
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt s b (fun m => c m - a m)
    have hnorm : Real.sqrt (∑ m ∈ s, (c m - a m) ^ 2) ≤ δ := by
      simpa [Real.sqrt_sq hδ] using Real.sqrt_le_sqrt hc
    rw [hshift]
    apply le_trans _ h
    apply add_le_add_right
    calc
      (∑ m ∈ s, b m * (c m - a m)) ≤ Real.sqrt E *
          Real.sqrt (∑ m ∈ s, (c m - a m)^2) := hcs
      _ ≤ Real.sqrt E * δ := mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg E)
      _ = δ * Real.sqrt E := mul_comm _ _
