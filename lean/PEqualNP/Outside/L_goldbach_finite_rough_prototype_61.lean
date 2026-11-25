import Mathlib

/-- The end-point comparison behind the constant 61: `exp 5 < 62 log 11`. -/
private theorem exp_five_lt_log_eleven : Real.exp 5 < 62 * Real.log 11 := by
  have hlog : Real.log 11 = Real.log (1 + 3/8) + 3 * Real.log 2 := by
    rw [show (1 + 3/8 : ℝ) = 11 / 8 by norm_num]
    rw [Real.log_div (by norm_num) (by norm_num), show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
    push_cast
    ring
  have hlow : (6/19 : ℝ) ≤ Real.log (1 + 3/8) := by
    have := Real.le_log_one_add_of_nonneg (x := (3/8 : ℝ)) (by norm_num)
    norm_num at this ⊢
    linarith
  have h2 := Real.log_two_gt_d9
  have hexp5 : Real.exp 5 < 148.5 := by
    have h1 : Real.exp 5 = (Real.exp 1)^5 := by
      simp
    have h2' := Real.exp_one_lt_d9
    have hp : (Real.exp 1)^5 < (2.7182818286:ℝ)^5 :=
      pow_lt_pow_left₀ h2' (by positivity) (by norm_num)
    have hnum : (2.7182818286:ℝ)^5 < 148.5 := by norm_num
    linarith
  have : (148.5:ℝ) < 62 * (6/19 + 3 * 0.6931471803) := by norm_num
  nlinarith [hlog, hlow, h2, hexp5]

/-- A list whose entries are all at least `y ≥ 2` has product at least `y` to the length. -/
private theorem pow_length_le_prod {L : List ℕ} {y : ℕ} (h : ∀ q ∈ L, y ≤ q) :
    y ^ L.length ≤ L.prod := by
  induction L with
  | nil => simp
  | cons a t ih =>
    have ha : y ≤ a := h a (by simp)
    have ht : ∀ q ∈ t, y ≤ q := fun q hq => h q (by simp [hq])
    have iht := ih ht
    calc y ^ (a :: t).length = y ^ t.length * y := by simp [pow_succ]
      _ ≤ t.prod * a := Nat.mul_le_mul iht ha
      _ = a * t.prod := Nat.mul_comm _ _

/-- The number of prime factors counted with multiplicity never exceeds the number. -/
private theorem length_primeFactorsList_le_self (s : ℕ) : s.primeFactorsList.length ≤ s := by
  by_cases h0 : s = 0
  · subst h0
    simp
  · have h2 : 2 ^ s.primeFactorsList.length ≤ s := by
      have := pow_length_le_prod (L := s.primeFactorsList) (y := 2)
        (fun q hq => (Nat.prime_of_mem_primeFactorsList hq).two_le)
      rwa [Nat.prod_primeFactorsList h0] at this
    have := s.primeFactorsList.length.lt_two_pow_self
    omega

set_option maxRecDepth 4096 in
/-- The five primes 3, 5, 7, 11, 19 cover every even residue modulo 210. -/
private theorem evenResidueCover : ∀ a : Fin 210, a.val % 2 = 0 →
    Nat.Coprime (a.val + 210 - 3) 210 ∨ Nat.Coprime (a.val + 210 - 5) 210 ∨
    Nat.Coprime (a.val + 210 - 7) 210 ∨ Nat.Coprime (a.val + 210 - 11) 210 ∨
    Nat.Coprime (a.val + 210 - 19) 210 := by
  decide

/-- The residue witness of one of those five primes lifts from `n % 210` to `n`. -/
private theorem roughWitness : ∀ n : ℕ, 22 ≤ n → Even n →
    ∃ p : ℕ, Nat.Prime p ∧ p < n ∧ 2 ≤ n - p ∧ Nat.Coprime (n - p) 210 := by
  intro n hn heven
  have hparity : n % 210 % 2 = 0 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have lift (p : ℕ) (hp : Nat.Prime p) (hp19 : p ≤ 19)
      (hc : Nat.Coprime (n % 210 + 210 - p) 210) :
      ∃ q : ℕ, Nat.Prime q ∧ q < n ∧ 2 ≤ n - q ∧ Nat.Coprime (n - q) 210 := by
    refine ⟨p, hp, by omega, by omega, ?_⟩
    have hshift : n - p + 210 = (n % 210 + 210 - p) + 210 * (n / 210) := by omega
    have hmod : (n - p) % 210 = (n % 210 + 210 - p) % 210 := by
      simpa only [Nat.add_mod_right, Nat.add_mul_mod_self_left] using
        congrArg (fun x : ℕ => x % 210) hshift
    rw [Nat.coprime_iff_gcd_eq_one] at hc ⊢
    calc
      Nat.gcd (n - p) 210 = Nat.gcd ((n - p) % 210) 210 :=
        (Nat.gcd_comm _ _).trans (Nat.gcd_rec _ _)
      _ = Nat.gcd ((n % 210 + 210 - p) % 210) 210 := by rw [hmod]
      _ = Nat.gcd (n % 210 + 210 - p) 210 :=
        (Nat.gcd_rec _ _).symm.trans (Nat.gcd_comm _ _)
      _ = 1 := hc
  rcases evenResidueCover ⟨n % 210, Nat.mod_lt _ (by decide)⟩ hparity with h | h | h | h | h
  · exact lift 3 (by decide) (by decide) h
  · exact lift 5 (by decide) (by decide) h
  · exact lift 7 (by decide) (by decide) h
  · exact lift 11 (by decide) (by decide) h
  · exact lift 19 (by decide) (by decide) h

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_goldbach_finite_rough_prototype_61 :
    ∀ n : ℕ, 4 ≤ n → Even n → (n:ℝ) < Real.exp (Real.exp 5) →
      ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 61 := by
  intro n hn4 heven hnbound
  by_cases h22 : 22 ≤ n
  · obtain ⟨p, hp, hpn, hple, hcop⟩ := roughWitness n h22 heven
    refine ⟨p, hp, hple, ?_⟩
    -- every prime factor of `n - p` avoids 2, 3, 5, 7, hence is at least 11
    have hfac : ∀ q ∈ (n - p).primeFactorsList, 11 ≤ q := by
      intro q hq
      have hqp : Nat.Prime q := Nat.prime_of_mem_primeFactorsList hq
      have hqd : q ∣ n - p := Nat.dvd_of_mem_primeFactorsList hq
      by_contra hlt
      push Not at hlt
      have hq2 : 2 ≤ q := hqp.two_le
      have hq210 : q ∣ 210 := by
        interval_cases q <;> first | exact absurd hqp (by decide) | norm_num
      have hunit : Nat.gcd (n - p) 210 = 1 := by
        rw [Nat.coprime_iff_gcd_eq_one] at hcop
        exact hcop
      have hdvd : q ∣ Nat.gcd (n - p) 210 := Nat.dvd_gcd hqd hq210
      rw [hunit] at hdvd
      have hq1 : q = 1 := Nat.dvd_one.mp hdvd
      omega
    have hlower : 11 ^ (n - p).primeFactorsList.length ≤ n - p := by
      have hne : n - p ≠ 0 := by omega
      have h := pow_length_le_prod (L := (n - p).primeFactorsList) (y := 11) hfac
      rwa [Nat.prod_primeFactorsList hne] at h
    -- the same certificate gives `n - p < 11 ^ 62`
    have hupper : ((n - p : ℕ) : ℝ) < (11:ℝ)^62 := by
      have hexp : Real.exp (Real.exp 5) < (11:ℝ)^62 := by
        have h1 : Real.exp (Real.exp 5) < Real.exp ((62:ℕ) * Real.log 11) :=
          Real.exp_lt_exp.mpr exp_five_lt_log_eleven
        have h2 : Real.exp ((62:ℕ) * Real.log 11) = (11:ℝ)^62 := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
        linarith
      have hle : ((n - p : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.sub_le n p
      linarith
    have hupperNat : n - p < 11^62 := by exact_mod_cast hupper
    have hlt : 11 ^ (n - p).primeFactorsList.length < 11 ^ 62 := lt_of_le_of_lt hlower hupperNat
    have hlt' : (n - p).primeFactorsList.length < 61 + 1 := by
      have h := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (11:ℕ))).mp hlt
      simpa using h
    exact Nat.le_of_lt_succ hlt'
  · have hlt22 : n < 22 := Nat.lt_of_not_le h22
    exact ⟨2, by norm_num, by omega,
      le_trans (length_primeFactorsList_le_self (n - 2)) (by omega)⟩