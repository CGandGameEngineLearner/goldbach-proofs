import Mathlib
import PEqualNP.Outside.L_twin_primes_ap_short_error
noncomputable def twF : ArithmeticFunction ℝ :=
  ⟨fun d => (ArithmeticFunction.moebius d : ℝ) / d.totient, by simp⟩
lemma twF_mult : twF.IsMultiplicative := by
  constructor
  · simp [twF]
  · intro a b hab
    have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hab
    simp only [twF, ArithmeticFunction.coe_mk, hmu, Nat.totient_mul hab]
    push_cast
    ring
lemma twEuler (q : ℕ) (hq : Squarefree q) :
    (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) / d.totient) =
      ∏ r ∈ q.primeFactors, (1 - 1 / ((r:ℝ)-1)) := by
  have h := twF_mult.prodPrimeFactors_one_add_of_squarefree hq
  change (∏ p ∈ q.primeFactors, (1 + (ArithmeticFunction.moebius p : ℝ) / p.totient)) = (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) / d.totient) at h
  rw [← h]
  apply Finset.prod_congr rfl
  intro p hp
  have hp' := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.moebius_apply_prime hp', Nat.totient_prime hp']
  have hp2 : 1 ≤ p := hp'.one_le
  rw [Nat.cast_sub hp2]
  norm_num

  ring


lemma twInd (q x : ℕ) (hq : q ≠ 0) :
    (∑ d ∈ q.divisors.filter (fun d => d ∣ x), (ArithmeticFunction.moebius d : ℝ)) = if Nat.Coprime x q then 1 else 0 := by
  have hg : Nat.gcd q x ≠ 0 := by
    intro hz
    have hh := Nat.gcd_dvd_left q x
    rw [hz] at hh
    simp at hh
    exact hq hh
  have hset : q.divisors.filter (fun d => d ∣ x) = (Nat.gcd q x).divisors := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
    simp [hq, hg]
  rw [hset]
  have h := congrArg (fun f : ArithmeticFunction ℝ => f (Nat.gcd q x)) (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  change (∑ d ∈ (Nat.gcd q x).divisors, (ArithmeticFunction.moebius d : ℝ)) = _ at h
  rw [h]
  simp [Nat.Coprime, Nat.gcd_comm]

lemma twMask (W : Finset ℕ) (q : ℕ) (hq : q ≠ 0) :
    (∑ p ∈ W.filter (fun p => p.Prime ∧ Nat.Coprime (p+2) q), Real.log p) =
    ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (∑ p ∈ W.filter (fun p => p.Prime ∧ d ∣ p+2), Real.log p) := by
  let WP := W.filter Nat.Prime
  have h1 : W.filter (fun p => p.Prime ∧ Nat.Coprime (p+2) q) = WP.filter (fun p => Nat.Coprime (p+2) q) := by ext p; simp [WP, and_assoc]
  have h2 (d : ℕ) : W.filter (fun p => p.Prime ∧ d ∣ p+2) = WP.filter (fun p => d ∣ p+2) := by ext p; simp [WP, and_assoc]
  rw [h1]
  simp_rw [h2]
  calc
    (∑ p ∈ WP.filter (fun p => Nat.Coprime (p+2) q), Real.log p) = ∑ p ∈ WP, Real.log p * (if Nat.Coprime (p+2) q then 1 else 0) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp
    _ = ∑ p ∈ WP, Real.log p * ∑ d ∈ q.divisors.filter (fun d => d ∣ p+2), (ArithmeticFunction.moebius d : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [twInd q (p+2) hq]
    _ = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * (∑ p ∈ WP.filter (fun p => d ∣ p+2), Real.log p) := by
      simp only [Finset.sum_filter, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> ring


lemma twAgg (W : Finset ℕ) (X q : ℕ) (C : ℝ) (hX : 2 ≤ X) (hq : q ≠ 0) (hodd : Odd q) (hsq : Squarefree q) (hC : 0 < C)
    (hAP : ∀ d ∈ q.divisors,
      |(∑ p ∈ W.filter (fun p => p.Prime ∧ d ∣ p+2), Real.log p) - (X:ℝ)/(50*d.totient)| ≤ C*Real.sqrt X*(Real.log (2*(d:ℝ)*X))^2) :
    |(∑ p ∈ W.filter (fun p => p.Prime ∧ Nat.Coprime (p+2) q), Real.log p) - (X:ℝ)/50 * ∏ r ∈ q.primeFactors, (1 - 1 / ((r:ℝ)-1))| ≤ C*(q.divisors.card:ℝ)*Real.sqrt X*(Real.log (2*(q:ℝ)*X))^2 := by
  let T := fun d : ℕ => ∑ p ∈ W.filter (fun p => p.Prime ∧ d ∣ p+2), Real.log p
  let M := fun d : ℕ => (X:ℝ)/(50*d.totient)
  let U := C*Real.sqrt X*(Real.log (2*(q:ℝ)*X))^2
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hterm (d : ℕ) (hd : d ∈ q.divisors) : |(ArithmeticFunction.moebius d : ℝ)*(T d-M d)| ≤ U := by
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.pos_of_ne_zero hq)
    have hdle : d ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq) hdvd
    have hlog1 : 0 ≤ Real.log (2*(d:ℝ)*X) := by
      apply Real.log_nonneg
      have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hdpos
      have hX2 : (2:ℝ) ≤ X := by exact_mod_cast hX
      nlinarith
    have hlogq : Real.log (2*(d:ℝ)*X) ≤ Real.log (2*(q:ℝ)*X) := by
      apply Real.log_le_log (by positivity)
      have hd' : (d:ℝ) ≤ q := by exact_mod_cast hdle
      have hX' : (0:ℝ) ≤ X := by positivity
      nlinarith
    have hlogs : (Real.log (2*(d:ℝ)*X))^2 ≤ (Real.log (2*(q:ℝ)*X))^2 := by nlinarith
    have hh := hAP d hd
    change |T d-M d| ≤ C*Real.sqrt X*(Real.log (2*(d:ℝ)*X))^2 at hh
    have hscale : C*Real.sqrt X*(Real.log (2*(d:ℝ)*X))^2 ≤ U := by
      dsimp [U]
      exact mul_le_mul_of_nonneg_left hlogs (by positivity)
    have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    rw [abs_mul]
    calc
      |(ArithmeticFunction.moebius d : ℝ)| * |T d-M d| ≤ 1*U := mul_le_mul hmu (hh.trans hscale) (abs_nonneg _) (by norm_num)
      _ = U := one_mul _
  have hmain : (∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) * M d) = (X:ℝ)/50 * ∏ r ∈ q.primeFactors, (1 - 1 / ((r:ℝ)-1)) := by
    rw [← twEuler q hsq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp [M]
    ring
  rw [twMask W q hq, ← hmain, ← Finset.sum_sub_distrib]
  have heq : (∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℝ) * T d - (ArithmeticFunction.moebius d : ℝ) * M d)) = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)*(T d-M d) := by
    apply Finset.sum_congr rfl
    intro d hd
    ring
  change |(∑ d ∈ q.divisors, ((ArithmeticFunction.moebius d : ℝ) * T d - (ArithmeticFunction.moebius d : ℝ) * M d))| ≤ _
  rw [heq]
  calc
    |∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ)*(T d-M d)| ≤ ∑ d ∈ q.divisors, |(ArithmeticFunction.moebius d : ℝ)*(T d-M d)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ q.divisors, U := Finset.sum_le_sum hterm
    _ = C*(q.divisors.card:ℝ)*Real.sqrt X*(Real.log (2*(q:ℝ)*X))^2 := by dsimp [U]; simp; ring



theorem Conjectures.TwinPrimes.PrimeWheelProgressionBudget : (∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1/2) → (let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let S := fun (X q : ℕ) => ((w X).filter (fun p => p.Prime ∧ Nat.Coprime (p+2) q)).sum (fun p => Real.log p); let V := fun (q : ℕ) => q.primeFactors.prod (fun r => 1-1/((r:ℝ)-1)); ∃ C : ℝ, 0 < C ∧ ∀ (X q : ℕ), 2 ≤ X → q ≤ X → Odd q → Squarefree q → |S X q-(X:ℝ)/50*V q| ≤ C*(q.divisors.card:ℝ)*Real.sqrt X*(Real.log (2*(q:ℝ)*X))^2) := by
  intro hGRH
  have hAP := PEqualNP.Outside.L_twin_primes_ap_short_error hGRH
  dsimp only at hAP ⊢
  obtain ⟨C, hC, hAP⟩ := hAP
  refine ⟨C, hC, ?_⟩
  intro X q hX hqX hodd hsq
  have hq0 : q ≠ 0 := by
    intro he
    subst q
    norm_num at hodd
  let W := (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X)
  apply twAgg W X q C hX hq0 hodd hsq hC
  intro d hd
  have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
  have hdle : d ≤ X := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) hdvd) hqX
  have hdodd : Odd d := hodd.of_dvd_nat hdvd
  exact hAP X d hX hdle hdodd

