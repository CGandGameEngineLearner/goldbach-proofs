import Mathlib

private def checkBlock (test : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, start => test start
  | depth + 1, start =>
      checkBlock test depth start && checkBlock test depth (start + 2 ^ depth)

private theorem checkBlock_sound (test : ℕ → Bool) (depth start i : ℕ)
    (checked : checkBlock test depth start = true) (hlo : start ≤ i)
    (hhi : i < start + 2 ^ depth) : test i = true := by
  induction depth generalizing start with
  | zero =>
    simp only [pow_zero] at hhi
    have hi : i = start := by omega
    simpa only [checkBlock, hi] using checked
  | succ depth ih =>
    rw [checkBlock, Bool.and_eq_true] at checked
    rw [pow_succ] at hhi
    by_cases h : i < start + 2 ^ depth
    · exact ih start checked.1 hlo h
    · exact ih (start + 2 ^ depth) checked.2 (by omega) (by omega)

private def probePrimes : List ℕ := [3, 5, 7, 11, 31, 43, 61, 79, 149, 197]

private def probe (i : ℕ) : Bool :=
  probePrimes.any fun p => decide (Nat.Coprime ((2 * i + 30030 - p) % 30030) 30030)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem probe_checked : checkBlock probe 14 0 = true := by decide

private theorem roughWitness (n : ℕ) (hn : 200 ≤ n) (heven : Even n) :
    ∃ p : ℕ, p.Prime ∧ 2 ≤ n - p ∧ Nat.Coprime (n - p) 30030 := by
  let r := n % 30030
  have hr : r = 2 * (r / 2) := by
    obtain ⟨k, hk⟩ := heven
    dsimp only [r]
    omega
  have hi : r / 2 < 0 + 2 ^ 14 := by
    have hlt : r < 30030 := Nat.mod_lt _ (by decide)
    norm_num
    omega
  have hprobe := checkBlock_sound probe 14 0 (r / 2) probe_checked (Nat.zero_le _) hi
  rw [probe, List.any_eq_true] at hprobe
  obtain ⟨p, hp, hgood⟩ := hprobe
  have hprimes : ∀ q ∈ probePrimes, Nat.Prime q ∧ q ≤ 197 := by
    intro q hq
    simp only [probePrimes, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  obtain ⟨hprime, hpmax⟩ := hprimes p hp
  have hresidue : (2 * (r / 2) + 30030 - p) % 30030 = (n - p) % 30030 := by
    rw [← hr]
    dsimp only [r]
    omega
  have hc : Nat.Coprime ((n - p) % 30030) 30030 := by
    rw [← hresidue]
    exact of_decide_eq_true hgood
  refine ⟨p, hprime, by omega, ?_⟩
  change Nat.gcd (n - p) 30030 = 1
  rw [Nat.gcd_comm, Nat.gcd_rec 30030 (n - p)]
  exact hc

private theorem factorLowerBound (s : ℕ) (hs : 2 ≤ s) (hrough : Nat.Coprime s 30030) :
    17 ^ s.primeFactorsList.length ≤ s := by
  have hsmall : ∀ q : Fin 17, q.val.Prime → q.val ∣ 30030 := by decide
  have hlarge : ∀ q ∈ s.primeFactorsList, 17 ≤ q := by
    intro q hq
    by_contra! hqsmall
    have hprime := Nat.prime_of_mem_primeFactorsList hq
    have hdiv := Nat.dvd_of_mem_primeFactorsList hq
    exact hprime.ne_one (Nat.eq_one_of_dvd_coprimes hrough hdiv (hsmall ⟨q, hqsmall⟩ hprime))
  have productLowerBound (factors : List ℕ) (h : ∀ q ∈ factors, 17 ≤ q) :
      17 ^ factors.length ≤ factors.prod := by
    induction factors with
    | nil => simp
    | cons q qs ih =>
      rw [List.length_cons, pow_succ, List.prod_cons, mul_comm q]
      exact Nat.mul_le_mul (ih (fun p hp => h p (List.mem_cons_of_mem q hp))) (h q (by simp))
  exact (productLowerBound s.primeFactorsList hlarge).trans_eq (Nat.prod_primeFactorsList (by omega))

private theorem prototypeUpperBound : Real.exp (Real.exp 5) < (17 : ℝ) ^ 53 := by
  have hexp : Real.exp 5 < 149 := calc
    Real.exp 5 = Real.exp 1 ^ (5 : ℕ) := by simp [← Real.exp_nat_mul]
    _ ≤ (2719 / 1000 : ℝ) ^ (5 : ℕ) :=
      pow_le_pow_left₀ (Real.exp_pos _).le (by linarith [Real.exp_one_lt_d9]) _
    _ < 149 := by norm_num
  have hsplit : Real.log 17 = 4 * Real.log 2 + Real.log (17 / 16) := by
    calc
      Real.log 17 = Real.log ((2 : ℝ) ^ 4 * (17 / 16)) := by norm_num
      _ = _ := by rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; norm_num
  have hcorrection : (1 / 17 : ℝ) ≤ Real.log (17 / 16) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (17 / 16 : ℝ)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlog : (149 : ℝ) < 53 * Real.log 17 := by
    rw [hsplit]
    linarith [Real.log_two_gt_d9]
  calc
    Real.exp (Real.exp 5) < Real.exp ((53 : ℕ) * Real.log 17) :=
      Real.exp_lt_exp.mpr (hexp.trans hlog)
    _ = (17 : ℝ) ^ 53 := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem smallWitness : ∀ a : Fin 200, 4 ≤ a.val → Even a.val →
    ∃ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19} : Finset ℕ), p.Prime ∧ (a.val - p).Prime := by
  decide

theorem PEqualNP.Outside.L_goldbach_finite_rough_prototype_52 :
    ∀ n : ℕ, 4 ≤ n → Even n → (n:ℝ) < Real.exp (Real.exp 5) → ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 52 := by
  intro n hn heven hupper
  by_cases hsmall : n < 200
  · obtain ⟨p, _, hp, hq⟩ := smallWitness ⟨n, hsmall⟩ hn heven
    refine ⟨p, hp, hq.two_le, ?_⟩
    simp [Nat.primeFactorsList_prime hq]
  · obtain ⟨p, hp, hdiff, hrough⟩ := roughWitness n (by omega) heven
    refine ⟨p, hp, hdiff, ?_⟩
    by_contra! hlength
    have hpower : (17 : ℕ) ^ 53 ≤ n := calc
      _ ≤ 17 ^ (n - p).primeFactorsList.length := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ n - p := factorLowerBound (n - p) hdiff hrough
      _ ≤ n := Nat.sub_le _ _
    have hpower' : (17 : ℝ) ^ 53 ≤ (n : ℝ) := by exact_mod_cast hpower
    exact (not_lt_of_ge hpower') (hupper.trans prototypeUpperBound)
