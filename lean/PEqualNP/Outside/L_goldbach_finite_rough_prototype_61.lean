import Mathlib

private lemma log11_gt : (2395:ℝ)/1000 < Real.log 11 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := (-(3/8) : ℝ)) (by norm_num) 6
  have hlog : Real.log (1 - (-(3/8) : ℝ)) = Real.log (11/8) := by norm_num
  rw [hlog] at h
  have hrhs : |(-(3/8) : ℝ)| ^ (6 + 1) / (1 - |(-(3/8) : ℝ)|) = (2187:ℝ)/1310720 := by
    norm_num
  rw [hrhs] at h
  have hsum : (∑ i ∈ Finset.range 6, (-(3/8) : ℝ) ^ (i + 1) / (i + 1)) = -(2503539:ℝ)/7864320 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum] at h
  have hle := abs_le.mp h
  have hlow : (316:ℝ)/1000 < Real.log (11/8) := by nlinarith [hle.1, hle.2]
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
    norm_num
  have hlog11 : Real.log 11 = Real.log 8 + Real.log (11/8) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h2 := Real.log_two_gt_d9
  nlinarith [hlog11, hlog8, h2, hlow]

private lemma exp_5_lt : Real.exp (5:ℝ) < 62 * Real.log 11 := by
  have h4eq : Real.exp (5:ℝ) = (Real.exp 1)^5 := by
    rw [show (5:ℝ) = (5:ℕ) * 1 by norm_num, Real.exp_nat_mul]
  have hexp5lt : Real.exp (5:ℝ) < 148.4133 := by
    rw [h4eq]
    have hp : Real.exp 1 ^ 5 ≤ (2.7182818286:ℝ)^5 :=
      pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 5
    nlinarith [hp]
  have hlog : (148.4133:ℝ) < 62 * Real.log 11 := by nlinarith [log11_gt]
  linarith

set_option maxRecDepth 4000 in
private lemma exp_exp_5_lt : Real.exp (Real.exp (5:ℝ)) < (11:ℝ)^62 := by
  have h1 : Real.exp (5:ℝ) < 62 * Real.log 11 := exp_5_lt
  have h2 : Real.exp (Real.exp (5:ℝ)) < Real.exp (62 * Real.log 11) :=
    Real.exp_lt_exp.mpr h1
  have h3 : Real.exp (62 * Real.log 11) = (11:ℝ)^62 := by
    rw [show (62 * Real.log 11) = Real.log ((11:ℝ)^62) by
      rw [Real.log_pow]
      norm_num]
    exact Real.exp_log (by positivity)
  rw [h3] at h2
  exact h2

private lemma cover210_bool :
    (List.range 210).all (fun a =>
      !(decide (Even a)) ||
      (decide (Nat.Coprime ((a + 210 - 3) % 210) 210) ||
       decide (Nat.Coprime ((a + 210 - 5) % 210) 210) ||
       decide (Nat.Coprime ((a + 210 - 7) % 210) 210) ||
       decide (Nat.Coprime ((a + 210 - 11) % 210) 210) ||
       decide (Nat.Coprime ((a + 210 - 19) % 210) 210))) = true := by
  decide

private lemma cover210 : ∀ a : ℕ, a < 210 → Even a →
    Nat.Coprime ((a + 210 - 3) % 210) 210 ∨ Nat.Coprime ((a + 210 - 5) % 210) 210 ∨
    Nat.Coprime ((a + 210 - 7) % 210) 210 ∨ Nat.Coprime ((a + 210 - 11) % 210) 210 ∨
    Nat.Coprime ((a + 210 - 19) % 210) 210 := by
  intro a ha he
  have h := List.all_eq_true.mp cover210_bool a (List.mem_range.mpr ha)
  simp only [decide_eq_true_iff.mpr he, Bool.not_true, Bool.false_or] at h
  simp only [Bool.or_eq_true, decide_eq_true_iff] at h
  tauto

private lemma one_le_prod : ∀ l : List ℕ, (∀ x ∈ l, 1 ≤ x) → 1 ≤ l.prod
  | [], _ => by simp
  | a :: t, h => by
      have ha : 1 ≤ a := h a (by simp)
      have ht : ∀ x ∈ t, 1 ≤ x := fun x hx => h x (by simp [hx])
      have h1 := one_le_prod t ht
      simp only [List.prod_cons]
      exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))

private lemma pow_length_le_prod' (b : ℕ) :
    ∀ l : List ℕ, (∀ x ∈ l, b ≤ x) → b ^ l.length ≤ l.prod
  | [], _ => by simp
  | a :: t, h => by
      have ha : b ≤ a := h a (by simp)
      have ht : ∀ x ∈ t, b ≤ x := fun x hx => h x (by simp [hx])
      have ih := pow_length_le_prod' b t ht
      simp only [List.length_cons, List.prod_cons, pow_succ]
      calc b ^ t.length * b ≤ t.prod * a := Nat.mul_le_mul ih ha
        _ = a * t.prod := Nat.mul_comm _ _

set_option maxRecDepth 4000 in
private lemma rough_construction (n p : ℕ) (hn : 210 ≤ n) (hp : 3 ≤ p) (hp19 : p ≤ 19)
    (hbound : (n:ℝ) < Real.exp (Real.exp (5:ℝ)))
    (hc : Nat.Coprime ((n % 210 + 210 - p) % 210) 210) :
    2 ≤ n - p ∧ (n - p).primeFactorsList.length ≤ 61 := by
  have hdiv := Nat.div_add_mod n 210
  have hmlt : n % 210 < 210 := Nat.mod_lt n (by norm_num)
  have hq : 1 ≤ n / 210 := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [h0] at hdiv
    omega
  have hdecomp : n - p = 210 * (n / 210 - 1) + (n % 210 + 210 - p) := by omega
  have hm2 : 2 ≤ n - p := by omega
  have hmne : n - p ≠ 0 := by omega
  have hmod : (n - p) % 210 = (n % 210 + 210 - p) % 210 := by
    rw [hdecomp, Nat.mul_add_mod_self_left]
  have hgcd : Nat.gcd (n - p) 210 = 1 := by
    rw [Nat.gcd_comm (n - p) 210, Nat.gcd_rec]
    rw [hmod]
    exact hc.gcd_eq_one
  have hge : ∀ q ∈ (n - p).primeFactorsList, 11 ≤ q := by
    intro q hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactorsList hq
    have hqdvd : q ∣ (n - p) := Nat.dvd_of_mem_primeFactorsList hq
    by_contra hlt
    push_neg at hlt
    have hq2 : 2 ≤ q := hqprime.two_le
    have hdvd210 : q ∣ 210 := by
      interval_cases q <;> (norm_num at hqprime) <;> norm_num
    have hgd : q ∣ Nat.gcd (n - p) 210 := Nat.dvd_gcd hqdvd hdvd210
    rw [hgcd] at hgd
    have hq1 : q = 1 := Nat.dvd_one.mp hgd
    omega
  have hpow := pow_length_le_prod' 11 (n - p).primeFactorsList hge
  rw [Nat.prod_primeFactorsList hmne] at hpow
  have hlt19 : n - p < 11 ^ 62 := by
    have h1 : ((n - p : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n p
    have h3 : Real.exp (Real.exp (5:ℝ)) < ((11:ℕ)^62 : ℝ) := by
      have h := exp_exp_5_lt
      push_cast
      exact h
    have h4 : ((n - p : ℕ) : ℝ) < ((11:ℕ)^62 : ℝ) :=
      lt_of_le_of_lt h1 (lt_of_lt_of_le hbound (le_of_lt h3))
    exact_mod_cast h4
  have hlen : (n - p).primeFactorsList.length ≤ 61 := by
    have hlt : 11 ^ (n - p).primeFactorsList.length < 11 ^ 62 := lt_of_le_of_lt hpow hlt19
    have h19 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 11)).mp hlt
    omega
  exact ⟨hm2, hlen⟩

set_option maxRecDepth 4000 in
theorem PEqualNP.Outside.L_goldbach_finite_rough_prototype_61 :
    ∀ n : ℕ, 4 ≤ n → Even n → (n:ℝ) < Real.exp (Real.exp (5)) →
      ∃ p : ℕ, Nat.Prime p ∧ 2 ≤ n-p ∧ (n-p).primeFactorsList.length ≤ 61 := by
  intro n hn4 hEven hbound
  by_cases h4 : n = 4
  · subst h4
    have h2le : 2 ≤ 4 - 2 := by norm_num
    refine ⟨ 2, by norm_num, h2le, ?_ ⟩
    have hm0 : 4 - 2 ≠ 0 := by norm_num
    have hlen_le : 2 ^ (4 - 2).primeFactorsList.length ≤ (4 - 2).primeFactorsList.prod := by
      apply pow_length_le_prod' 2
      intro x hx
      exact (Nat.prime_of_mem_primeFactorsList hx).two_le
    rw [Nat.prod_primeFactorsList hm0] at hlen_le
    have hlt : 2 ^ (4 - 2).primeFactorsList.length < 2 ^ 2 :=
      lt_of_le_of_lt hlen_le (by norm_num)
    have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
    omega
  · have hn5 : 5 ≤ n := by
      by_contra h
      push_neg at h
      have : n = 4 := by omega
      exact h4 this
    have hEven' := hEven
    obtain ⟨ k, hk ⟩ := hEven
    have hn6 : 6 ≤ n := by omega
    by_cases hn210 : n < 210
    · have h2le : 2 ≤ n - 3 := by omega
      refine ⟨ 3, by norm_num, h2le, ?_ ⟩
      have hm0 : n - 3 ≠ 0 := by omega
      have hlen_le : 2 ^ (n - 3).primeFactorsList.length ≤ (n - 3).primeFactorsList.prod := by
        apply pow_length_le_prod' 2
        intro x hx
        exact (Nat.prime_of_mem_primeFactorsList hx).two_le
      rw [Nat.prod_primeFactorsList hm0] at hlen_le
      have hlt256 : n - 3 < 2 ^ 8 := by omega
      have hlt : 2 ^ (n - 3).primeFactorsList.length < 2 ^ 8 := lt_of_le_of_lt hlen_le hlt256
      have h8 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hlt
      omega
    · have hn210' : 210 ≤ n := by omega
      have hmod_lt : n % 210 < 210 := Nat.mod_lt n (by norm_num)
      have ha_even : Even (n % 210) := by
        rw [Nat.even_iff] at hEven' ⊢
        rw [Nat.mod_mod_of_dvd n (by norm_num : 2 ∣ 210)]
        exact hEven'
      rcases cover210 (n % 210) hmod_lt ha_even with h3 | h5 | h7 | h11 | h19
      · obtain ⟨ h2, hlen ⟩ := rough_construction n 3 hn210' (by norm_num) (by norm_num) hbound h3
        exact ⟨ 3, by norm_num, h2, hlen ⟩
      · obtain ⟨ h2, hlen ⟩ := rough_construction n 5 hn210' (by norm_num) (by norm_num) hbound h5
        exact ⟨ 5, by norm_num, h2, hlen ⟩
      · obtain ⟨ h2, hlen ⟩ := rough_construction n 7 hn210' (by norm_num) (by norm_num) hbound h7
        exact ⟨ 7, by norm_num, h2, hlen ⟩
      · obtain ⟨ h2, hlen ⟩ := rough_construction n 11 hn210' (by norm_num) (by norm_num) hbound h11
        exact ⟨ 11, by norm_num, h2, hlen ⟩
      · obtain ⟨ h2, hlen ⟩ := rough_construction n 19 hn210' (by norm_num) (by norm_num) hbound h19
        exact ⟨ 19, by norm_num, h2, hlen ⟩
