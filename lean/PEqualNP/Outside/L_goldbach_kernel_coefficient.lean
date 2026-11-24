import Mathlib

open scoped BigOperators Interval

theorem PEqualNP.Outside.L_goldbach_kernel_coefficient :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let K := fun (N : ℕ) (b : ℝ) => Finset.sum (Finset.range (N+1)) (fun k => E ((k:ℝ)*b)); ∀ N s : ℕ, s≤N → intervalIntegral (fun t => (K N t)^2*E (-(s:ℝ)*t)) (0:ℝ) 1 MeasureTheory.volume = ((s+1:ℕ):ℂ) := by
  intro E K N s hs
  let c (m : ℤ) : ℂ := (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  let term (i j : ℕ) (t : ℝ) := Complex.exp (c ((i : ℤ) + j - s) * (t : ℂ))
  have cont (i j : ℕ) : Continuous (term i j) := by unfold term; fun_prop
  have expand (t : ℝ) : (K N t)^2 * E (-(s : ℝ) * t) =
      ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (N+1), term i j t := by
    simp only [K, pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    simp only [E, term, c, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have orth (i j : ℕ) : (∫ t in (0:ℝ)..1, term i j t) =
      if i + j = s then (1 : ℂ) else 0 := by
    by_cases h : i + j = s
    · have hz : (i : ℤ) + j - s = 0 := by omega
      simp [term, c, hz, h]
    · have hz : (i : ℤ) + j - s ≠ 0 := by omega
      have hc : c ((i : ℤ) + j - s) ≠ 0 := by
        unfold c
        exact mul_ne_zero (Int.cast_ne_zero.mpr hz)
          (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      simp only [term, if_neg h, integral_exp_mul_complex hc]
      simp [c, Complex.exp_int_mul_two_pi_mul_I]
  have row (i : ℕ) : (∑ j ∈ Finset.range (N+1), if i+j=s then (1:ℂ) else 0) =
      if i ≤ s then 1 else 0 := by
    by_cases hi : i ≤ s
    · rw [if_pos hi, Finset.sum_eq_single (s-i)]
      · simp [Nat.add_sub_of_le hi]
      · intro j _ hj
        exact if_neg (by omega)
      · intro h
        exact False.elim (h (Finset.mem_range.mpr (by omega)))
    · simp [hi, show ∀ j : ℕ, i+j ≠ s by omega]
  simp_rw [expand]
  rw [intervalIntegral.integral_finsetSum (fun i _ =>
    (continuous_finsetSum _ (fun j _ => cont i j)).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_finsetSum (fun j _ => (cont _ j).intervalIntegrable _ _),
    orth, row]
  have sub : Finset.range (s+1) ⊆ Finset.range (N+1) := Finset.range_mono (by omega)
  rw [← Finset.sum_subset sub (by
    intro i _ hi
    exact if_neg (by simpa [Finset.mem_range, Nat.lt_succ_iff] using hi))]
  calc
    _ = ∑ _i ∈ Finset.range (s+1), (1:ℂ) := Finset.sum_congr rfl fun i hi =>
      if_pos (by have := Finset.mem_range.mp hi; omega)
    _ = _ := by simp
