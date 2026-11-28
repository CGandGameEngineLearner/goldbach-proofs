import Mathlib

/-!
# The dyadic jump bound used to transfer progression estimates from ψ to θ

Bennett, Martin, O'Bryant and Rechnitzer, "Explicit bounds for primes in arithmetic
progressions", §5.1, Lemma 5.4 and Theorem 5.5, https://arxiv.org/abs/1802.00085.
The activation of the exponent j at 2^j contributes the quantity `jump j` to
the normalized error. Definition 5.1 uses 1 + j/(2 log x) for x ≤ q^j.
The proof of Lemma 5.4 prints 1 + 1/(2j log x) at x = 2^j. Starting with
Definition 5.1 yields a finite-tail estimate with coefficient 10; the statement
below does not use the printed coefficient 6.
-/

namespace BMOR.PsiThetaTransfer

noncomputable def jump (j : ℕ) : ℝ :=
  (j * (2 * Real.log 2 + 1)) / (2 : ℝ)^j

/-- Evaluate the small-x branch of Definition 5.1 at its activation x = 2^j.
For q ≥ 3 this point lies below q^j. -/
theorem jump_from_definition {j : ℕ} (hj : 0 < j) :
    Real.log ((2:ℝ)^j) / (((2:ℝ)^j) ^ (1 - 1 / (j:ℝ))) *
      (1 + (j:ℝ) / (2 * Real.log ((2:ℝ)^j))) = jump j := by
  have hj' : (j:ℝ) ≠ 0 := by positivity
  have hp : 0 < (2:ℝ)^j := by positivity
  have hl : 0 < Real.log 2 := by positivity
  rw [Real.rpow_sub hp, Real.rpow_one, one_div, Real.pow_rpow_inv_natCast (by norm_num) hj.ne',
    Real.log_pow]
  unfold jump
  field_simp

private noncomputable def tail (j : ℕ) : ℝ :=
  2 * (j + 1) * (2 * Real.log 2 + 1) / (2 : ℝ)^j

private theorem jump_eq_drop (j : ℕ) : jump j = tail j - tail (j+1) := by
  unfold jump tail
  rw [pow_succ, Nat.cast_add, Nat.cast_one]
  ring

/-- Total cost of actual Definition 5.1 jumps in a finite block. The comparison
uses the exact telescoping tail 2(d+1)(2 log 2 + 1)/2^d. -/
theorem dyadic_jumps_lt {x : ℝ} {d : ℕ} (hx : Real.exp 2 ≤ x)
    (hd : 3 ≤ d) (hbegin : x ≤ (2 : ℝ)^d) (length : ℕ) :
    (∑ i ∈ Finset.range length, jump (d+i)) < 10 * Real.log x / x := by
  have hpartial (m : ℕ) : (∑ i ∈ Finset.range m, jump (d+i)) = tail d - tail (d+m) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Nat.add_succ, ih, jump_eq_drop]
      ring
  have htail : 0 ≤ tail (d+length) := by unfold tail; positivity
  have hd' : 3 ≤ (d : ℝ) := by exact_mod_cast hd
  have hsmall : tail d < 10 * (Real.log ((2 : ℝ)^d) / (2 : ℝ)^d) := by
    unfold tail
    rw [Real.log_pow, ← mul_div_assoc, div_lt_div_iff_of_pos_right (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd') (show 0 ≤ 6 * Real.log 2 - 2 by
      linarith [Real.log_two_gt_d9]), Real.log_two_gt_d9]
  have hdomain : Real.exp 1 ≤ x := (Real.exp_le_exp.mpr (by norm_num)).trans hx
  have hmono := Real.log_div_self_antitoneOn (show x ∈ Set.Ici (Real.exp 1) from hdomain)
    (show (2 : ℝ)^d ∈ Set.Ici (Real.exp 1) from hdomain.trans hbegin) hbegin
  dsimp only at hmono
  rw [mul_div_assoc, hpartial]
  linarith

/-- The factor multiplying Δₖ in Definition 5.1 decreases on [exp 2,∞)
for every exponent k ≥ 2. -/
theorem log_kernel_antitone (k : ℕ) (hk : 2 ≤ k) :
    AntitoneOn (fun x : ℝ => Real.log x / x ^ (1 - 1 / (k : ℝ))) (Set.Ici (Real.exp 2)) := by
  have hk' : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hi : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hk'
  apply (Real.log_div_self_rpow_antitoneOn (a := 1 - 1 / (k : ℝ)) (by linarith)).mono
  apply Set.Ici_subset_Ici.mpr
  apply Real.exp_le_exp.mpr
  rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
  linarith

/-- The concluding transfer in Theorem 5.5. The three input bounds are explicit:
the normalized ψ error, the nonnegative correction ψ−θ, and its majorant made of
the old exponents at the cutoff plus the jumps of the newly introduced exponents. -/
theorem theta_error_of_jump_envelope {ψ θ main D old X x : ℝ} {d : ℕ}
    (hX : Real.exp 2 ≤ X) (hx : X ≤ x) (hd : 3 ≤ d) (hbegin : X ≤ (2 : ℝ)^d)
    (length : ℕ) (hψ : |ψ - main| / (x / Real.log x) ≤ D)
    (hpos : θ ≤ ψ) (hcorr : (ψ - θ) / (x / Real.log x)
      ≤ old + ∑ i ∈ Finset.range length, jump (d+i)) :
    |θ - main| / (x / Real.log x) < D + old + 10 * Real.log X / X := by
  have hx1 : 1 < x :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ) < 2)).trans_le (hX.trans hx)
  have hscale : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx1)
  have htriangle : |θ - main| ≤ |ψ - main| + (ψ - θ) := by
    calc
      _ = |(ψ - main) - (ψ - θ)| := by congr 1; ring
      _ ≤ |ψ - main| + |ψ - θ| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg (sub_nonneg.mpr hpos)]
  have hnorm := div_le_div_of_nonneg_right htriangle hscale.le
  rw [add_div] at hnorm
  linarith [dyadic_jumps_lt hX hd hbegin length]

end BMOR.PsiThetaTransfer
