import Mathlib

namespace PEqualNP.Outside

private def roughComplementPrime : Bool → Bool → Bool → ℕ
  | false, false, false => 211
  | false, false, true => 181
  | false, true, false => 379
  | false, true, true => 139
  | true, false, false => 71
  | true, false, true => 41
  | true, true, false => 29
  | true, true, true => 419

private theorem roughComplementPrime_spec (three five seven : Bool) :
    let p := roughComplementPrime three five seven
    p.Prime ∧ p < 500 ∧ p % 2 = 1 ∧
      p % 3 = (if three then 2 else 1) ∧
      p % 5 = (if five then 4 else 1) ∧
      p % 7 = (if seven then 6 else 1) := by
  cases three <;> cases five <;> cases seven <;> norm_num [roughComplementPrime]

private theorem chosen_residue_avoids {n p modulus : ℕ} (modulusLarge : 2 < modulus)
    (residue : p % modulus =
      (if decide (n % modulus = 1) then modulus - 1 else 1)) :
    p % modulus ≠ n % modulus := by
  intro equalResidues
  by_cases atOne : n % modulus = 1
  · have chosen : p % modulus = modulus - 1 := by simpa [atOne] using residue
    omega
  · have chosen : p % modulus = 1 := by simpa [atOne] using residue
    exact atOne (equalResidues.symm.trans chosen)

private theorem small_prime_options {r : ℕ} (prime : r.Prime) (below : r < 11) :
    r = 2 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by
  have lower := prime.two_le
  interval_cases r <;> norm_num at prime <;> norm_num

private theorem exists_rough_complement {n : ℕ} (large : 1000 ≤ n) (evenN : Even n) :
    ∃ p : ℕ, p.Prime ∧ 2 ≤ n - p ∧ ∀ r ∈ (n - p).primeFactorsList, 11 ≤ r := by
  let side (modulus : ℕ) : Bool := decide (n % modulus = 1)
  let p := roughComplementPrime (side 3) (side 5) (side 7)
  obtain ⟨pPrime, pBelow, pOdd, residue3, residue5, residue7⟩ :=
    roughComplementPrime_spec (side 3) (side 5) (side 7)
  have pBound : p < 500 := pBelow
  have pLeN : p ≤ n := by omega
  refine ⟨p, pPrime, by omega, ?_⟩
  intro r factor
  by_contra below
  have divides : r ∣ n - p := Nat.dvd_of_mem_primeFactorsList factor
  have sameResidue : n % r = p % r := by
    calc
      n % r = (n - p + p) % r :=
        congrArg (fun m : ℕ => m % r) (Nat.sub_add_cancel pLeN).symm
      _ = p % r := by
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd divides, zero_add, Nat.mod_mod]
  rcases small_prime_options (Nat.prime_of_mem_primeFactorsList factor)
      (lt_of_not_ge below) with rfl | rfl | rfl | rfl
  · exact Nat.zero_ne_one ((Nat.even_iff.mp evenN).symm.trans (sameResidue.trans pOdd))
  · exact chosen_residue_avoids (by decide : 2 < 3) residue3 sameResidue.symm
  · exact chosen_residue_avoids (by decide : 2 < 5) residue5 sameResidue.symm
  · exact chosen_residue_avoids (by decide : 2 < 7) residue7 sameResidue.symm

private theorem factor_count_le_sixty_one {base m : ℕ} (basePositive : 0 < base)
    (mNonzero : m ≠ 0) (upper : m < base ^ 62)
    (factorLower : ∀ p ∈ m.primeFactorsList, base ≤ p) :
    m.primeFactorsList.length ≤ 61 := by
  have listBound (factors : List ℕ) :
      (∀ p ∈ factors, base ≤ p) → base ^ factors.length ≤ factors.prod := by
    induction factors with
    | nil => simp
    | cons p factors inductionHypothesis =>
      intro allFactors
      rw [List.length_cons, pow_succ', List.prod_cons]
      exact Nat.mul_le_mul (allFactors p (by simp))
        (inductionHypothesis fun q membership => allFactors q (by simp [membership]))
  have productLower : base ^ m.primeFactorsList.length ≤ m :=
    (listBound m.primeFactorsList factorLower).trans_eq (Nat.prod_primeFactorsList mNonzero)
  by_contra tooMany
  have exponentLe : 62 ≤ m.primeFactorsList.length := by omega
  exact (not_le_of_gt upper) ((Nat.pow_le_pow_right basePositive exponentLe).trans productLower)

private theorem rough_prototype_upper : Real.exp (Real.exp 5) < (11 : ℝ) ^ 62 := by
  have expOneUpper : Real.exp 1 < (27183 : ℝ) / 10000 :=
    Real.exp_one_lt_d9.trans (by norm_num)
  have expFiveUpper : Real.exp 5 < (297 : ℝ) / 2 := by
    calc
      Real.exp 5 = (Real.exp 1) ^ 5 := by
        rw [← Real.exp_nat_mul, mul_one]
        norm_num
      _ < ((27183 : ℝ) / 10000) ^ 5 :=
        pow_lt_pow_left₀ expOneUpper (Real.exp_nonneg 1) (by decide)
      _ < (297 : ℝ) / 2 := by norm_num
  have ratioLower : (6 : ℝ) / 19 < Real.log (11 / 8) := by
    convert Real.lt_log_one_add_of_pos (x := (3 : ℝ) / 8) (by norm_num) using 1 <;> norm_num
  have logEleven : Real.log 11 = 3 * Real.log 2 + Real.log (11 / 8) := by
    calc
      Real.log 11 = Real.log ((2 : ℝ) ^ 3 * (11 / 8)) := by norm_num
      _ = _ := by rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  have expFiveBelowLogPower : Real.exp 5 < 62 * Real.log 11 := by
    rw [logEleven]
    linarith [Real.log_two_gt_d9]
  calc
    Real.exp (Real.exp 5) < Real.exp (62 * Real.log 11) :=
      Real.exp_lt_exp.mpr expFiveBelowLogPower
    _ = Real.exp (Real.log ((11 : ℝ) ^ 62)) := by rw [Real.log_pow]; norm_num
    _ = (11 : ℝ) ^ 62 := Real.exp_log (by positivity)

set_option maxRecDepth 2048 in
theorem L_goldbach_finite_rough_prototype_61 :
    ∀ n : ℕ, 4 ≤ n → Even n → (n : ℝ) < Real.exp (Real.exp 5) →
      ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n - p ∧ (n - p).primeFactorsList.length ≤ 61 := by
  intro n nLower nEven nUpper
  by_cases small : n < 1000
  · have complementLower : 2 ≤ n - 2 := by omega
    have complementUpper : n - 2 < 2 ^ 62 :=
      (Nat.sub_le n 2).trans_lt (small.trans_le (by norm_num))
    exact ⟨2, Nat.prime_two, complementLower, factor_count_le_sixty_one
      (by decide : 0 < 2) (by omega) complementUpper
      (fun p membership => (Nat.prime_of_mem_primeFactorsList membership).two_le)⟩
  · obtain ⟨p, pPrime, complementLower, factorsLarge⟩ :=
      exists_rough_complement (le_of_not_gt small) nEven
    have realUpper : (n : ℝ) < (11 : ℝ) ^ 62 := lt_trans nUpper rough_prototype_upper
    have castUpper : (n : ℝ) < ((11 ^ 62 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      exact realUpper
    have naturalUpper : n < 11 ^ 62 := Nat.cast_lt.mp castUpper
    exact ⟨p, pPrime, complementLower, factor_count_le_sixty_one
      (by decide : 0 < 11) (by omega) ((Nat.sub_le n p).trans_lt naturalUpper) factorsLarge⟩

end PEqualNP.Outside
