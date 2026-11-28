import Mathlib

/-!
Refutation of L-goldbach-cut-e6ac0e824543bcd70ccf7537.

The statement claims that for every sufficiently large even integer n, the count of
two-sided cube-root-rough semiprime pairs (u, n - u) with u in [n/3, 2n/3] is at most
(189 / 500) * V(n, sqrt n).

Averaging over even n in a short window [X, (1 + delta) X] (delta = 1/10000):
- The pair count sum is at least (1 - o(1)) * (1/3) * (log 2)^2 * delta * X^2 / (log X)^2
  using Chebyshev.tendsto_theta_div_atTop (weak PNT) and discrete summation by parts.
- The sieve volume sum is at most (1 + o(1)) * (4/3) * exp(-2 * g0) * delta * X^2 / (log X)^2
  with g0 = 5755/10000, using a finite Euler product at sigma = 1 / log z together with
  elementary polynomial and 9-interval secant bounds (no integrals or zeta machinery).
Since (log 2)^2 * exp(2 * g0) / 4 > 0.3796 > 0.378 = 189/500, this yields a contradiction.
-/

namespace RefuteE6ac

open scoped BigOperators
open Finset Filter Topology

private lemma prod_le_prod_real {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hfg : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has]
    have ha0 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
    have hag : f a ≤ g a := hfg a (Finset.mem_insert_self a s)
    have hs0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have hsg : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i :=
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    exact mul_le_mul hag hsg hs0 (le_trans ha0 hag)

private lemma finset_prod_rpow_real {ι : Type*} (s : Finset ι) (f : ι → ℝ) (y : ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∏ i ∈ s, f i) ^ y = ∏ i ∈ s, (f i) ^ y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has,
      Real.mul_rpow (hf a (Finset.mem_insert_self a s))
        (Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private lemma sub_eq_mul_of_div_eq {a b c d : ℝ} (hc : c ≠ 0) (h : (a - b) / c = d) :
    a - b = c * d := by
  rw [div_eq_iff hc] at h
  linarith

/-! ### Section 1: Elementary numerical bounds for exp and log 2 -/

private lemma exp_quarter_bounds :
    (1284025 / 1000000 : ℝ) ≤ Real.exp (1 / 4 : ℝ) ∧
      Real.exp (1 / 4 : ℝ) ≤ (1284026 / 1000000 : ℝ) := by
  constructor
  · have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 / 4 by norm_num) 6
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith
  · have h := Real.exp_bound' (show (0 : ℝ) ≤ 1 / 4 by norm_num)
      (show (1 / 4 : ℝ) ≤ 1 by norm_num) (show (0 : ℕ) < 6 by decide)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num at h
    linarith

private lemma exp_neg_quarter_bounds :
    (778800 / 1000000 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) ∧
      Real.exp (-(1 / 4 : ℝ)) ≤ (778802 / 1000000 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := exp_quarter_bounds
  rw [Real.exp_neg]
  have hpos : (0 : ℝ) < Real.exp (1 / 4 : ℝ) := Real.exp_pos _
  constructor
  · rw [le_inv_comm₀ (by norm_num) hpos]
    linarith
  · rw [inv_le_comm₀ hpos (by norm_num)]
    linarith

private lemma exp_neg_pow_quarter (k : ℕ) :
    Real.exp (-((k : ℝ) / 4)) = (Real.exp (-(1 / 4 : ℝ))) ^ k := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

private lemma rpow_int_bounds {r a b : ℝ} (ha : 0 ≤ a) (hlo : a ≤ r) (hhi : r ≤ b) (k : ℕ) :
    a ^ k ≤ r ^ k ∧ r ^ k ≤ b ^ k := by
  have hr : 0 ≤ r := le_trans ha hlo
  exact ⟨pow_le_pow_left₀ ha hlo k, pow_le_pow_left₀ hr hhi k⟩

private lemma sec_nine_sum_le :
    let e := fun t : ℝ => Real.exp (-t)
    let term := fun a b : ℝ => ((b - 1) * e a - (a - 1) * e b) / (a * b)
    term 1 (5 / 4) + term (5 / 4) (3 / 2) + term (3 / 2) (7 / 4) + term (7 / 4) 2 +
      term 2 (5 / 2) + term (5 / 2) 3 + term 3 4 + term 4 6 + term 6 10 ≤
      (220925 / 1000000 : ℝ) := by
  intro e term
  set r : ℝ := Real.exp (-(1 / 4 : ℝ))
  have hr := exp_neg_quarter_bounds
  have hr0 : 0 ≤ r := le_trans (by norm_num) hr.1
  have h1 : e 1 = r ^ 4 := by dsimp [e, r]; rw [← exp_neg_pow_quarter 4]; norm_num
  have h54 : e (5 / 4) = r ^ 5 := by dsimp [e, r]; rw [← exp_neg_pow_quarter 5]; norm_num
  have h32 : e (3 / 2) = r ^ 6 := by dsimp [e, r]; rw [← exp_neg_pow_quarter 6]; norm_num
  have h74 : e (7 / 4) = r ^ 7 := by dsimp [e, r]; rw [← exp_neg_pow_quarter 7]; norm_num
  have h2 : e 2 = r ^ 8 := by dsimp [e, r]; rw [← exp_neg_pow_quarter 8]; norm_num
  have h52 : e (5 / 2) = r ^ 10 := by dsimp [e, r]; rw [← exp_neg_pow_quarter 10]; norm_num
  have h3 : e 3 = r ^ 12 := by dsimp [e, r]; rw [← exp_neg_pow_quarter 12]; norm_num
  have h4 : e 4 = r ^ 16 := by dsimp [e, r]; rw [← exp_neg_pow_quarter 16]; norm_num
  have h6 : e 6 = r ^ 24 := by dsimp [e, r]; rw [← exp_neg_pow_quarter 24]; norm_num
  have h10 : e 10 = r ^ 40 := by dsimp [e, r]; rw [← exp_neg_pow_quarter 40]; norm_num
  have hr4 : (367877 / 1000000 : ℝ) ≤ r ^ 4 ∧ r ^ 4 ≤ (367883 / 1000000 : ℝ) := by
    have h := rpow_int_bounds (by norm_num) hr.1 hr.2 4
    norm_num at h
    constructor <;> linarith [h.1, h.2]
  have hr5 : (286502 / 1000000 : ℝ) ≤ r ^ 5 ∧ r ^ 5 ≤ (286509 / 1000000 : ℝ) := by
    have hlo : (367877 / 1000000 : ℝ) * (778800 / 1000000) ≤ r ^ 4 * r :=
      mul_le_mul hr4.1 hr.1 (by norm_num) (le_trans (by norm_num) hr4.1)
    have hhi : r ^ 4 * r ≤ (367883 / 1000000 : ℝ) * (778802 / 1000000) :=
      mul_le_mul hr4.2 hr.2 hr0 (by norm_num)
    rw [show r ^ 5 = r ^ 4 * r by ring]
    constructor <;> linarith
  have hr6 : (223127 / 1000000 : ℝ) ≤ r ^ 6 ∧ r ^ 6 ≤ (223134 / 1000000 : ℝ) := by
    have hlo : (286502 / 1000000 : ℝ) * (778800 / 1000000) ≤ r ^ 5 * r :=
      mul_le_mul hr5.1 hr.1 (by norm_num) (le_trans (by norm_num) hr5.1)
    have hhi : r ^ 5 * r ≤ (286509 / 1000000 : ℝ) * (778802 / 1000000) :=
      mul_le_mul hr5.2 hr.2 hr0 (by norm_num)
    rw [show r ^ 6 = r ^ 5 * r by ring]
    constructor <;> linarith
  have hr7 : (173771 / 1000000 : ℝ) ≤ r ^ 7 ∧ r ^ 7 ≤ (173778 / 1000000 : ℝ) := by
    have hlo : (223127 / 1000000 : ℝ) * (778800 / 1000000) ≤ r ^ 6 * r :=
      mul_le_mul hr6.1 hr.1 (by norm_num) (le_trans (by norm_num) hr6.1)
    have hhi : r ^ 6 * r ≤ (223134 / 1000000 : ℝ) * (778802 / 1000000) :=
      mul_le_mul hr6.2 hr.2 hr0 (by norm_num)
    rw [show r ^ 7 = r ^ 6 * r by ring]
    constructor <;> linarith
  have hr8 : (135333 / 1000000 : ℝ) ≤ r ^ 8 ∧ r ^ 8 ≤ (135339 / 1000000 : ℝ) := by
    have hlo : (367877 / 1000000 : ℝ) * (367877 / 1000000) ≤ r ^ 4 * r ^ 4 :=
      mul_le_mul hr4.1 hr4.1 (by norm_num) (le_trans (by norm_num) hr4.1)
    have hhi : r ^ 4 * r ^ 4 ≤ (367883 / 1000000 : ℝ) * (367883 / 1000000) :=
      mul_le_mul hr4.2 hr4.2 (pow_nonneg hr0 4) (by norm_num)
    rw [show r ^ 8 = r ^ 4 * r ^ 4 by ring]
    constructor <;> linarith
  have hr10 : (82083 / 1000000 : ℝ) ≤ r ^ 10 ∧ r ^ 10 ≤ (82088 / 1000000 : ℝ) := by
    have hlo : (286502 / 1000000 : ℝ) * (286502 / 1000000) ≤ r ^ 5 * r ^ 5 :=
      mul_le_mul hr5.1 hr5.1 (by norm_num) (le_trans (by norm_num) hr5.1)
    have hhi : r ^ 5 * r ^ 5 ≤ (286509 / 1000000 : ℝ) * (286509 / 1000000) :=
      mul_le_mul hr5.2 hr5.2 (pow_nonneg hr0 5) (by norm_num)
    rw [show r ^ 10 = r ^ 5 * r ^ 5 by ring]
    constructor <;> linarith
  have hr12 : (49785 / 1000000 : ℝ) ≤ r ^ 12 ∧ r ^ 12 ≤ (49790 / 1000000 : ℝ) := by
    have hlo : (223127 / 1000000 : ℝ) * (223127 / 1000000) ≤ r ^ 6 * r ^ 6 :=
      mul_le_mul hr6.1 hr6.1 (by norm_num) (le_trans (by norm_num) hr6.1)
    have hhi : r ^ 6 * r ^ 6 ≤ (223134 / 1000000 : ℝ) * (223134 / 1000000) :=
      mul_le_mul hr6.2 hr6.2 (pow_nonneg hr0 6) (by norm_num)
    rw [show r ^ 12 = r ^ 6 * r ^ 6 by ring]
    constructor <;> linarith
  have hr16 : (18315 / 1000000 : ℝ) ≤ r ^ 16 ∧ r ^ 16 ≤ (18317 / 1000000 : ℝ) := by
    have hlo : (135333 / 1000000 : ℝ) * (135333 / 1000000) ≤ r ^ 8 * r ^ 8 :=
      mul_le_mul hr8.1 hr8.1 (by norm_num) (le_trans (by norm_num) hr8.1)
    have hhi : r ^ 8 * r ^ 8 ≤ (135339 / 1000000 : ℝ) * (135339 / 1000000) :=
      mul_le_mul hr8.2 hr8.2 (pow_nonneg hr0 8) (by norm_num)
    rw [show r ^ 16 = r ^ 8 * r ^ 8 by ring]
    constructor <;> linarith
  have hr24 : (2478 / 1000000 : ℝ) ≤ r ^ 24 ∧ r ^ 24 ≤ (2480 / 1000000 : ℝ) := by
    have hlo : (49785 / 1000000 : ℝ) * (49785 / 1000000) ≤ r ^ 12 * r ^ 12 :=
      mul_le_mul hr12.1 hr12.1 (by norm_num) (le_trans (by norm_num) hr12.1)
    have hhi : r ^ 12 * r ^ 12 ≤ (49790 / 1000000 : ℝ) * (49790 / 1000000) :=
      mul_le_mul hr12.2 hr12.2 (pow_nonneg hr0 12) (by norm_num)
    rw [show r ^ 24 = r ^ 12 * r ^ 12 by ring]
    constructor <;> linarith
  have hr40 : (0 : ℝ) ≤ r ^ 40 := pow_nonneg hr0 40
  dsimp only [term]
  rw [h1, h54, h32, h74, h2, h52, h3, h4, h6, h10]
  ring_nf
  linarith [hr4.1, hr4.2, hr5.1, hr5.2, hr6.1, hr6.2, hr7.1, hr7.2,
    hr8.1, hr8.2, hr10.1, hr10.2, hr12.1, hr12.2, hr16.1, hr16.2, hr24.1, hr24.2, hr40]

private lemma exp_neg_ten_le : Real.exp (-(10 : ℝ)) ≤ (1 / 20000 : ℝ) := by
  have h1 : Real.exp (-(10 : ℝ)) = (Real.exp (-(1 / 4 : ℝ))) ^ 40 := by
    rw [← exp_neg_pow_quarter 40]; norm_num
  rw [h1]
  have hr := exp_neg_quarter_bounds
  have hr0 : 0 ≤ Real.exp (-(1 / 4 : ℝ)) := (Real.exp_pos _).le
  have h4 : (Real.exp (-(1 / 4 : ℝ))) ^ 4 ≤ (37 / 100 : ℝ) := by
    have h := pow_le_pow_left₀ hr0 hr.2 4
    linarith
  have h10 : ((Real.exp (-(1 / 4 : ℝ))) ^ 4) ^ 10 ≤ (37 / 100 : ℝ) ^ 10 :=
    pow_le_pow_left₀ (pow_nonneg hr0 4) h4 10
  rw [← pow_mul] at h10
  norm_num at h10 ⊢
  linarith

private lemma log_two_gt : (6931 / 10000 : ℝ) < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h : Real.exp (6931 / 40000 : ℝ) ≤
      (∑ m ∈ Finset.range 6, (6931 / 40000 : ℝ) ^ m / m.factorial) +
        (6931 / 40000 : ℝ) ^ 6 * (6 + 1) / ((6 : ℕ).factorial * 6) :=
    Real.exp_bound' (by norm_num) (by norm_num) (by decide)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  have h1 : Real.exp (6931 / 40000 : ℝ) ≤ (11892 / 10000 : ℝ) := by
    norm_num at h; linarith
  have h4 : (Real.exp (6931 / 40000 : ℝ)) ^ 4 ≤ (11892 / 10000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (Real.exp_pos _).le h1 4
  have heq : (Real.exp (6931 / 40000 : ℝ)) ^ 4 = Real.exp (6931 / 10000 : ℝ) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [heq] at h4
  norm_num at h4
  linarith

private lemma exp_two_g0_gt : (31613 / 10000 : ℝ) < Real.exp (2 * (5755 / 10000 : ℝ)) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 5755 / 20000 by norm_num) 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial_succ, Nat.factorial_zero] at h
  have h1 : (133342 / 100000 : ℝ) ≤ Real.exp (5755 / 20000 : ℝ) := by
    norm_num at h; linarith
  have h4 : (133342 / 100000 : ℝ) ^ 4 ≤ (Real.exp (5755 / 20000 : ℝ)) ^ 4 :=
    pow_le_pow_left₀ (by norm_num) h1 4
  have heq : (Real.exp (5755 / 20000 : ℝ)) ^ 4 = Real.exp (2 * (5755 / 10000 : ℝ)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [heq] at h4
  norm_num at h4
  linarith

private lemma exp_neg_poly_lower {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    1 - u / 2 + u ^ 2 / 6 - u ^ 3 / 24 + u ^ 4 / 120 - u ^ 5 / 720 - u ^ 6 / 4410 ≤
      (1 - Real.exp (-u)) / u := by
  have habs : |-u| ≤ 1 := by rw [abs_neg, abs_of_pos hu0]; exact hu1
  have hb := Real.exp_bound habs (show (0 : ℕ) < 7 by decide)
  rw [abs_neg, abs_of_pos hu0] at hb
  have hup := (abs_sub_le_iff.mp hb).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hup
  have h2 : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 - u ^ 3 / 6 + u ^ 4 / 24 -
      u ^ 5 / 120 + u ^ 6 / 720 + u ^ 7 / 4410 := by
    norm_num at hup
    linarith
  rw [le_div_iff₀ hu0]
  nlinarith

/-! ### Section 2: Discrete prime sums from Chebyshev.tendsto_theta_div_atTop -/

private lemma theta_eventually_bounds {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ x : ℝ, (X₀ : ℝ) ≤ x →
      (1 - ε) * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ (1 + ε) * x := by
  have ht := Chebyshev.tendsto_theta_div_atTop
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨R, hR⟩ := ht ε hε
  obtain ⟨N, hN⟩ := exists_nat_ge (max R 4)
  refine ⟨max N 4, le_max_right _ _, fun x hx => ?_⟩
  have hxR : R ≤ x := (le_max_left R 4).trans (hN.trans ((Nat.cast_le.mpr (le_max_left N 4)).trans hx))
  have hx4 : (4 : ℝ) ≤ x := (Nat.cast_le.mpr (le_max_right N 4)).trans hx
  have hx0 : 0 < x := by linarith
  have hd := hR x hxR
  rw [Real.dist_eq, abs_lt] at hd
  constructor
  · have h1 : 1 - ε < Chebyshev.theta x / x := by linarith
    exact (lt_div_iff₀ hx0).mp h1 |>.le
  · have h2 : Chebyshev.theta x / x < 1 + ε := by linarith
    exact (div_lt_iff₀ hx0).mp h2 |>.le

private lemma theta_succ_sub (k : ℕ) :
    Chebyshev.theta ((k + 1 : ℕ) : ℝ) - Chebyshev.theta (k : ℝ) =
      if (k + 1).Prime then Real.log ((k + 1 : ℕ) : ℝ) else 0 := by
  rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
  rw [Nat.floor_natCast, Nat.floor_natCast, Nat.primesLE_succ]
  split_ifs with hp
  · rw [Finset.sum_insert (Nat.notMem_primesLE k)]
    ring
  · ring

private lemma sum_inv_Ioc_log_bounds {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    Real.log (((B + 1 : ℕ) : ℝ) / ((A + 1 : ℕ) : ℝ)) ≤
        ∑ k ∈ Finset.Ioc A B, (1 : ℝ) / (k : ℝ) ∧
      ∑ k ∈ Finset.Ioc A B, (1 : ℝ) / (k : ℝ) ≤
        Real.log ((B : ℝ) / (A : ℝ)) := by
  have step_le (k : ℕ) (hk : 1 ≤ k) :
      Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ≤ 1 / (k : ℝ) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h := Real.log_le_sub_one_of_pos (show 0 < ((k + 1 : ℕ) : ℝ) / (k : ℝ) by positivity)
    have heq : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
      push_cast; field_simp; ring
    linarith
  have step_ge (k : ℕ) (hk : 1 ≤ k) :
      1 / ((k + 1 : ℕ) : ℝ) ≤ Real.log (((k + 1 : ℕ) : ℝ) / (k : ℝ)) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h := Real.one_sub_inv_le_log_of_pos (show 0 < ((k + 1 : ℕ) : ℝ) / (k : ℝ) by positivity)
    have heq : 1 - (((k + 1 : ℕ) : ℝ) / (k : ℝ))⁻¹ = 1 / ((k + 1 : ℕ) : ℝ) := by
      push_cast; field_simp; ring
    linarith
  constructor
  · induction B, hAB using Nat.le_induction with
    | base =>
      simp only [Finset.Ioc_self, Finset.sum_empty]
      rw [div_self (by positivity), Real.log_one]
    | succ B hAB ih =>
      rw [Finset.sum_Ioc_succ_top (by omega)]
      have hB1 : 1 ≤ B + 1 := by omega
      have hst := step_le (B + 1) hB1
      have hlog : Real.log (((B + 2 : ℕ) : ℝ) / ((A + 1 : ℕ) : ℝ)) =
          Real.log (((B + 1 : ℕ) : ℝ) / ((A + 1 : ℕ) : ℝ)) +
            Real.log (((B + 2 : ℕ) : ℝ) / ((B + 1 : ℕ) : ℝ)) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1; push_cast; field_simp
      rw [show B + 1 + 1 = B + 2 by omega]
      linarith
  · induction B, hAB using Nat.le_induction with
    | base =>
      simp only [Finset.Ioc_self, Finset.sum_empty]
      have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
      rw [div_self hA0, Real.log_one]
    | succ B hAB ih =>
      rw [Finset.sum_Ioc_succ_top (by omega)]
      have hB1 : 1 ≤ B := by omega
      have hst := step_ge B hB1
      have hlog : Real.log (((B + 1 : ℕ) : ℝ) / (A : ℝ)) =
          Real.log ((B : ℝ) / (A : ℝ)) + Real.log (((B + 1 : ℕ) : ℝ) / (B : ℝ)) := by
        have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
        have hA0 : (A : ℝ) ≠ 0 := by exact_mod_cast (show A ≠ 0 by omega)
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1; field_simp
      linarith

private lemma abel_sum_Ioc (f : ℕ → ℝ) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    ∑ k ∈ Finset.Ioc A B, (f k - f (k - 1)) / (k : ℝ) =
      f B / (B : ℝ) - f A / (A : ℝ) +
        ∑ k ∈ Finset.Ico A B, f k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ico_succ_top hAB, ih]
    simp only [Nat.add_sub_cancel]
    ring

private lemma sum_log_div_prime_Ioc {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ X₀ : ℕ, 8 ≤ X₀ ∧ ∀ A B : ℕ, X₀ ≤ A → A ≤ B →
      (1 - ε) * Real.log ((B : ℝ) / (A : ℝ)) - 4 * ε - 2 / (A : ℝ) ≤
          ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ∧
        ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) ≤
          (1 + ε) * Real.log ((B : ℝ) / (A : ℝ)) + 4 * ε + 2 / (A : ℝ) := by
  obtain ⟨X₀, hX4, hθ⟩ := theta_eventually_bounds hε
  refine ⟨max X₀ 8, le_max_right _ _, fun A B hA hAB => ?_⟩
  have hAX : X₀ ≤ A := (le_max_left X₀ 8).trans hA
  have hA8 : 8 ≤ A := (le_max_right X₀ 8).trans hA
  have hA1 : 1 ≤ A := by omega
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA1
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 1 ≤ B by omega)
  have hsum_eq :
      ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) =
        ∑ k ∈ Finset.Ioc A B,
          (Chebyshev.theta (k : ℝ) - Chebyshev.theta ((k - 1 : ℕ) : ℝ)) / (k : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := by have := (Finset.mem_Ioc.mp hk).1; omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    rw [Nat.succ_eq_add_one, Nat.add_sub_cancel, theta_succ_sub]
    split_ifs <;> simp
  rw [hsum_eq, abel_sum_Ioc (fun k => Chebyshev.theta (k : ℝ)) hA1 hAB]
  have hθA := hθ (A : ℝ) (by exact_mod_cast hAX)
  have hθB := hθ (B : ℝ) (by exact_mod_cast (hAX.trans hAB))
  have hbd_lo : -(2 * ε) ≤ Chebyshev.theta (B : ℝ) / (B : ℝ) - Chebyshev.theta (A : ℝ) / (A : ℝ) := by
    have h1 : 1 - ε ≤ Chebyshev.theta (B : ℝ) / (B : ℝ) := (le_div_iff₀ hB0).mpr hθB.1
    have h2 : Chebyshev.theta (A : ℝ) / (A : ℝ) ≤ 1 + ε := (div_le_iff₀ hA0).mpr hθA.2
    linarith
  have hbd_hi : Chebyshev.theta (B : ℝ) / (B : ℝ) - Chebyshev.theta (A : ℝ) / (A : ℝ) ≤ 2 * ε := by
    have h1 : Chebyshev.theta (B : ℝ) / (B : ℝ) ≤ 1 + ε := (div_le_iff₀ hB0).mpr hθB.2
    have h2 : 1 - ε ≤ Chebyshev.theta (A : ℝ) / (A : ℝ) := (le_div_iff₀ hA0).mpr hθA.1
    linarith
  have hmain_lo :
      (1 - ε) * ∑ k ∈ Finset.Ico A B, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ≤
        ∑ k ∈ Finset.Ico A B,
          Chebyshev.theta (k : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkA : A ≤ k := (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 1 ≤ k by omega)
    have hdiff : 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) = 1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
      push_cast; field_simp; ring
    have hθk := (hθ (k : ℝ) (by exact_mod_cast (hAX.trans hkA))).1
    rw [hdiff]
    have hmul := mul_le_mul_of_nonneg_right hθk (show 0 ≤ 1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) by positivity)
    calc (1 - ε) * (1 / ((k + 1 : ℕ) : ℝ))
        = (1 - ε) * (k : ℝ) * (1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ))) := by field_simp
      _ ≤ Chebyshev.theta (k : ℝ) * (1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ))) := hmul
  have hmain_hi :
      ∑ k ∈ Finset.Ico A B,
          Chebyshev.theta (k : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) ≤
        (1 + ε) * ∑ k ∈ Finset.Ico A B, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkA : A ≤ k := (Finset.mem_Ico.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 1 ≤ k by omega)
    have hdiff : 1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ) = 1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
      push_cast; field_simp; ring
    have hθk := (hθ (k : ℝ) (by exact_mod_cast (hAX.trans hkA))).2
    rw [hdiff]
    have hmul := mul_le_mul_of_nonneg_right hθk (show 0 ≤ 1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) by positivity)
    calc Chebyshev.theta (k : ℝ) * (1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)))
        ≤ (1 + ε) * (k : ℝ) * (1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ))) := hmul
      _ = (1 + ε) * (1 / ((k + 1 : ℕ) : ℝ)) := by field_simp
  have hshift :
      ∑ k ∈ Finset.Ico A B, (1 : ℝ) / ((k + 1 : ℕ) : ℝ) =
        ∑ k ∈ Finset.Ioc A B, (1 : ℝ) / (k : ℝ) := by
    refine Finset.sum_bij (fun k _ => k + 1) ?_ ?_ ?_ ?_
    · intro k hk; rw [Finset.mem_Ico] at hk; rw [Finset.mem_Ioc]; omega
    · intro _ _ _ _ h; omega
    · intro k hk; rw [Finset.mem_Ioc] at hk; exact ⟨k - 1, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro _ _; rfl
  rw [hshift] at hmain_lo hmain_hi
  obtain ⟨hlog_lo, hlog_hi⟩ := sum_inv_Ioc_log_bounds hA1 hAB
  have hratio_gap :
      Real.log ((B : ℝ) / (A : ℝ)) - 1 / (A : ℝ) ≤
        Real.log (((B + 1 : ℕ) : ℝ) / ((A + 1 : ℕ) : ℝ)) := by
    have h1 : Real.log (((A + 1 : ℕ) : ℝ) / (A : ℝ)) ≤ 1 / (A : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show 0 < ((A + 1 : ℕ) : ℝ) / (A : ℝ) by positivity)
      have heq : ((A + 1 : ℕ) : ℝ) / (A : ℝ) - 1 = 1 / (A : ℝ) := by push_cast; field_simp; ring
      linarith
    have h2 : Real.log ((B : ℝ) / (A : ℝ)) ≤
        Real.log (((B + 1 : ℕ) : ℝ) / (A : ℝ)) := by
      apply Real.log_le_log (by positivity)
      apply div_le_div_of_nonneg_right _ hA0.le
      push_cast; linarith
    have h3 : Real.log (((B + 1 : ℕ) : ℝ) / ((A + 1 : ℕ) : ℝ)) =
        Real.log (((B + 1 : ℕ) : ℝ) / (A : ℝ)) - Real.log (((A + 1 : ℕ) : ℝ) / (A : ℝ)) := by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1; field_simp
    linarith
  constructor
  · have h1 : (1 - ε) * (Real.log ((B : ℝ) / (A : ℝ)) - 1 / (A : ℝ)) ≤
        (1 - ε) * ∑ k ∈ Finset.Ioc A B, (1 : ℝ) / (k : ℝ) :=
      mul_le_mul_of_nonneg_left (hratio_gap.trans hlog_lo) (by linarith)
    have h2 : (1 - ε) * (1 / (A : ℝ)) ≤ 2 / (A : ℝ) := by
      have hnn : 0 ≤ 1 / (A : ℝ) := by positivity
      have h1 : (1 - ε) * (1 / (A : ℝ)) ≤ 2 * (1 / (A : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hnn
      linarith [show 2 * (1 / (A : ℝ)) = 2 / (A : ℝ) by ring]
    linarith
  · have h1 : (1 + ε) * ∑ k ∈ Finset.Ioc A B, (1 : ℝ) / (k : ℝ) ≤
        (1 + ε) * Real.log ((B : ℝ) / (A : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog_hi (by linarith)
    have h2 : (0 : ℝ) ≤ 2 / (A : ℝ) := by positivity
    linarith

/-! ### Section 3: Sharp Mertens upper bound via finite Euler product -/

private lemma finite_euler_product_le (M : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-(1 + σ)) ≤
      ∏ p ∈ Nat.primesLE M, (1 - (p : ℝ) ^ (-(1 + σ)))⁻¹ := by
  have hgeom : ∀ p ∈ Nat.primesLE M,
      ∑ j ∈ Finset.range (M + 1), ((p : ℝ) ^ (-(1 + σ))) ^ j ≤
        (1 - (p : ℝ) ^ (-(1 + σ)))⁻¹ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have hr0 : 0 ≤ (p : ℝ) ^ (-(1 + σ)) := Real.rpow_nonneg (by linarith) _
    have hr1 : (p : ℝ) ^ (-(1 + σ)) < 1 := by
      rw [Real.rpow_neg (by linarith)]
      apply inv_lt_one_of_one_lt₀
      exact Real.one_lt_rpow (by linarith) (by linarith)
    rw [geom_sum_eq hr1.ne]
    have hpos : 0 < 1 - (p : ℝ) ^ (-(1 + σ)) := sub_pos.mpr hr1
    rw [← neg_div_neg_eq, neg_sub, neg_sub, inv_eq_one_div]
    apply div_le_div_of_nonneg_right _ hpos.le
    have := pow_nonneg hr0 (M + 1)
    linarith
  have hprod_le :
      ∏ p ∈ Nat.primesLE M, ∑ j ∈ Finset.range (M + 1), ((p : ℝ) ^ (-(1 + σ))) ^ j ≤
        ∏ p ∈ Nat.primesLE M, (1 - (p : ℝ) ^ (-(1 + σ)))⁻¹ := by
    apply prod_le_prod_real
    · intro p hp
      apply Finset.sum_nonneg
      intro j _
      exact pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) j
    · exact hgeom
  refine le_trans ?_ hprod_le
  rw [Finset.prod_sum]
  let φ : ℕ → ∀ p ∈ Nat.primesLE M, ℕ := fun n p _ => n.factorization p
  have hmem : ∀ n ∈ Finset.Icc 1 M, φ n ∈ (Nat.primesLE M).pi (fun _ => Finset.range (M + 1)) := by
    intro n hn
    rw [Finset.mem_pi]
    intro p hp
    rw [Finset.mem_range]
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
    have hlt : n.factorization p < n := Nat.factorization_lt p (by omega)
    dsimp [φ]
    omega
  have hval : ∀ n ∈ Finset.Icc 1 M,
      (∏ p ∈ (Nat.primesLE M).attach, ((p.1 : ℝ) ^ (-(1 + σ))) ^ (φ n p.1 p.2)) =
        (n : ℝ) ^ (-(1 + σ)) := by
    intro n hn
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
    have hfac_sub : n.primeFactors ⊆ Nat.primesLE M := by
      intro p hp
      rw [Nat.mem_primesLE]
      exact ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_primeFactors hp)).trans hnM,
        Nat.prime_of_mem_primeFactors hp⟩
    have hnat : (∏ p ∈ (Nat.primesLE M).attach, p.1 ^ (n.factorization p.1)) = n := by
      rw [Finset.prod_attach (Nat.primesLE M) (fun p => p ^ (n.factorization p))]
      rw [← Finset.prod_subset hfac_sub]
      · simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn0
      · intro p _ hpnot
        have : n.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
          exact hpnot
        rw [this, pow_zero]
    have hreal : (∏ p ∈ (Nat.primesLE M).attach, ((p.1 : ℝ) ^ (n.factorization p.1))) = (n : ℝ) := by
      exact_mod_cast hnat
    rw [← hreal, finset_prod_rpow_real _ _ _ (fun p _ => pow_nonneg (Nat.cast_nonneg _) _)]
    apply Finset.prod_congr rfl
    intro p _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1; ring
  have hinj : Set.InjOn φ (Finset.Icc 1 M : Set ℕ) := by
    intro a ha b hb hab
    have ha0 : a ≠ 0 := by have := (Finset.mem_Icc.mp ha).1; omega
    have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp hb).1; omega
    have haM : a ≤ M := (Finset.mem_Icc.mp ha).2
    have hbM : b ≤ M := (Finset.mem_Icc.mp hb).2
    have hfa : a.factorization = b.factorization := by
      ext p
      by_cases hp : p ∈ Nat.primesLE M
      · exact congrFun (congrFun hab p) hp
      · have h1 : a.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
          intro hmem
          exact hp (Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero ha0)
            (Nat.dvd_of_mem_primeFactors hmem)).trans haM, Nat.prime_of_mem_primeFactors hmem⟩)
        have h2 : b.factorization p = 0 := by
          rw [← Finsupp.notMem_support_iff, Nat.support_factorization]
          intro hmem
          exact hp (Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (Nat.pos_of_ne_zero hb0)
            (Nat.dvd_of_mem_primeFactors hmem)).trans hbM, Nat.prime_of_mem_primeFactors hmem⟩)
        rw [h1, h2]
    exact Nat.eq_of_factorization_eq ha0 hb0 (fun p => congrFun (congrArg DFunLike.coe hfa) p)
  calc ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-(1 + σ))
      = ∑ n ∈ Finset.Icc 1 M,
          ∏ p ∈ (Nat.primesLE M).attach, ((p.1 : ℝ) ^ (-(1 + σ))) ^ (φ n p.1 p.2) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (hval n hn).symm
    _ = ∑ g ∈ (Finset.Icc 1 M).image φ,
          ∏ p ∈ (Nat.primesLE M).attach, ((p.1 : ℝ) ^ (-(1 + σ))) ^ (g p.1 p.2) := by
        rw [Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
    _ ≤ ∑ g ∈ (Nat.primesLE M).pi (fun _ => Finset.range (M + 1)),
          ∏ p ∈ (Nat.primesLE M).attach, ((p.1 : ℝ) ^ (-(1 + σ))) ^ (g p.1 p.2) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro g hg
          rcases Finset.mem_image.mp hg with ⟨n, hn, rfl⟩
          exact hmem n hn
        · intro g _ _
          exact Finset.prod_nonneg (fun p _ => pow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) _)

private lemma sum_rpow_ge {M : ℕ} (hM : 1 ≤ M) {σ : ℝ} (hσ : 0 < σ) :
    (1 - ((M + 1 : ℕ) : ℝ) ^ (-σ)) / σ ≤ ∑ n ∈ Finset.Icc 1 M, (n : ℝ) ^ (-(1 + σ)) := by
  let g : ℝ → ℝ := fun t => -(t ^ (-σ)) / σ
  have hstep : ∀ n : ℕ, 1 ≤ n → g ((n + 1 : ℕ) : ℝ) - g (n : ℝ) ≤ (n : ℝ) ^ (-(1 + σ)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlt : (n : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self n
    have hderiv : ∀ t ∈ Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ),
        HasDerivAt g (t ^ (-(1 + σ))) t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hn0 ht.1
      have h1 : HasDerivAt (fun x : ℝ => x ^ (-σ)) ((-σ) * t ^ (-σ - 1)) t :=
        Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
      have h2 := h1.neg.div_const σ
      convert h2 using 1
      have hσ0 : σ ≠ 0 := hσ.ne'
      rw [show -σ - 1 = -(1 + σ) by ring]
      field_simp
    have hcont : ContinuousOn g (Set.Icc (n : ℝ) ((n + 1 : ℕ) : ℝ)) :=
      fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope g (fun t => t ^ (-(1 + σ))) hlt
      hcont (fun t ht => hderiv t (Set.Ioo_subset_Icc_self ht))
    have hdiff : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
    rw [hdiff, div_one] at hslope
    rw [← hslope]
    exact Real.rpow_le_rpow_of_nonpos hn0 hξ.1.le (by linarith)
  have htel : ∑ n ∈ Finset.Icc 1 M, (g ((n + 1 : ℕ) : ℝ) - g (n : ℝ)) =
      g ((M + 1 : ℕ) : ℝ) - g 1 := by
    induction M, hM using Nat.le_induction with
    | base => simp; norm_num
    | succ M hM ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      ring
  have hg1 : g ((M + 1 : ℕ) : ℝ) - g 1 = (1 - ((M + 1 : ℕ) : ℝ) ^ (-σ)) / σ := by
    dsimp [g]; rw [Real.one_rpow]; ring
  rw [← hg1, ← htel]
  exact Finset.sum_le_sum (fun n hn => hstep n (Finset.mem_Icc.mp hn).1)

private lemma log_one_sub_ratio_ge {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    b - a ≤ Real.log ((1 - a) / (1 - b)) := by
  have h1a : 0 < 1 - a := by linarith
  have h1b : 0 < 1 - b := by linarith
  rw [Real.log_div h1a.ne' h1b.ne']
  rcases eq_or_lt_of_le hab with rfl | hlt
  · simp
  let f : ℝ → ℝ := fun t => -Real.log (1 - t) - t
  have hderiv : ∀ t ∈ Set.Icc a b, HasDerivAt f (t / (1 - t)) t := by
    intro t ht
    have h1t : 1 - t ≠ 0 := by linarith [ht.2]
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := by
      have := (hasDerivAt_id t).const_sub (1 : ℝ)
      simpa using this
    have h2 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) ((-1) / (1 - t)) t :=
      h1.log h1t
    have h3 : HasDerivAt f (-((-1) / (1 - t)) - 1) t :=
      h2.fun_neg.fun_sub (hasDerivAt_id t)
    convert h3 using 1
    field_simp
    ring
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f (fun t => t / (1 - t)) hlt
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t (Set.Ioo_subset_Icc_self ht))
  have hpos : 0 ≤ ξ / (1 - ξ) := div_nonneg (le_trans ha.le hξ.1.le) (by linarith [hξ.2])
  have hsub : 0 ≤ f b - f a := by
    rw [hslope] at hpos
    have hba : 0 < b - a := sub_pos.mpr hlt
    rcases div_nonneg_iff.mp hpos with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · linarith
  dsimp [f] at hsub
  linarith

private lemma neg_log_one_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    -Real.log (1 - t) ≤ t / (1 - t) := by
  have hpos : 0 < 1 - t := sub_pos.mpr ht1
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by field_simp; ring
  linarith

private lemma one_sub_exp_div_anti {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    (1 - Real.exp (-v)) / v ≤ (1 - Real.exp (-u)) / u := by
  rcases eq_or_lt_of_le huv with rfl | hlt
  · exact le_rfl
  let f : ℝ → ℝ := fun t => (1 - Real.exp (-t)) / t
  have hderiv : ∀ t ∈ Set.Icc u v,
      HasDerivAt f (((1 + t) * Real.exp (-t) - 1) / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := (lt_of_lt_of_le hu ht.1).ne'
    have h1 : HasDerivAt (fun x : ℝ => 1 - Real.exp (-x)) (Real.exp (-t)) t := by
      have he : HasDerivAt (fun x : ℝ => Real.exp (-x)) (Real.exp (-t) * (-1)) t :=
        ((hasDerivAt_id t).fun_neg).exp
      exact (he.const_sub (1 : ℝ)).congr_deriv (by ring)
    exact (h1.fun_div (hasDerivAt_id t) ht0).congr_deriv (by simp only [id_eq]; field_simp; ring)
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f
    (fun t => ((1 + t) * Real.exp (-t) - 1) / t ^ 2) hlt
    (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
    (fun t ht => hderiv t (Set.Ioo_subset_Icc_self ht))
  have hξ0 : 0 < ξ := lt_trans hu hξ.1
  have hle : (1 + ξ) * Real.exp (-ξ) - 1 ≤ 0 := by
    have h1 : 1 + ξ ≤ Real.exp ξ := by linarith [Real.add_one_le_exp ξ]
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-ξ)).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h2
    linarith
  have hnonpos : ((1 + ξ) * Real.exp (-ξ) - 1) / ξ ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hle (sq_nonneg ξ)
  rw [hslope] at hnonpos
  have hvu : 0 < v - u := sub_pos.mpr hlt
  rcases div_nonpos_iff.mp hnonpos with ⟨_, hbad⟩ | ⟨hgood, _⟩
  · linarith
  · dsimp [f] at hgood; linarith

private lemma riemann_poly_S1_lower (K : ℕ) (hK : 4 ≤ K) :
    (79654 / 100000 : ℝ) - 3 / (K : ℝ) ≤
      ∑ j ∈ Finset.Ico 1 K,
        (1 / (K : ℝ)) * ((1 - Real.exp (-(((j + 1 : ℕ) : ℝ) / (K : ℝ)))) /
          (((j + 1 : ℕ) : ℝ) / (K : ℝ))) := by
  let P : ℝ → ℝ := fun u =>
    1 - u / 2 + u ^ 2 / 6 - u ^ 3 / 24 + u ^ 4 / 120 - u ^ 5 / 720 - u ^ 6 / 4410
  let Q : ℝ → ℝ := fun u =>
    u - u ^ 2 / 4 + u ^ 3 / 18 - u ^ 4 / 96 + u ^ 5 / 600 - u ^ 6 / 4320 - u ^ 7 / 30870
  have hQderiv : ∀ u : ℝ, HasDerivAt Q (P u) u := by
    intro u
    dsimp [Q, P]
    have h := ((((((hasDerivAt_id u).fun_sub
      ((hasDerivAt_pow 2 u).div_const 4)).fun_add
      ((hasDerivAt_pow 3 u).div_const 18)).fun_sub
      ((hasDerivAt_pow 4 u).div_const 96)).fun_add
      ((hasDerivAt_pow 5 u).div_const 600)).fun_sub
      ((hasDerivAt_pow 6 u).div_const 4320)).fun_sub
      ((hasDerivAt_pow 7 u).div_const 30870)
    exact h.congr_deriv (by ring)
  let P' : ℝ → ℝ := fun u =>
    -(1 / 2) + u / 3 - u ^ 2 / 8 + u ^ 3 / 30 - u ^ 4 / 144 - u ^ 5 / 735
  have hPderiv : ∀ u : ℝ, HasDerivAt P (P' u) u := by
    intro u
    dsimp [P, P']
    have h := ((((((hasDerivAt_const u (1 : ℝ)).fun_sub
      ((hasDerivAt_id u).div_const 2)).fun_add
      ((hasDerivAt_pow 2 u).div_const 6)).fun_sub
      ((hasDerivAt_pow 3 u).div_const 24)).fun_add
      ((hasDerivAt_pow 4 u).div_const 120)).fun_sub
      ((hasDerivAt_pow 5 u).div_const 720)).fun_sub
      ((hasDerivAt_pow 6 u).div_const 4410)
    exact h.congr_deriv (by ring)
  have hPanti : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 → P b ≤ P a := by
    intro a b ha hab hb
    rcases eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope P P' hlt
      (fun t _ => (hPderiv t).continuousAt.continuousWithinAt)
      (fun t _ => hPderiv t)
    have hξ0 : 0 ≤ ξ := le_trans ha hξ.1.le
    have hξ1 : ξ ≤ 1 := le_trans hξ.2.le hb
    have hP'neg : P' ξ ≤ 0 := by
      dsimp [P']
      have h2 : 0 ≤ ξ ^ 2 := sq_nonneg ξ
      have h3 : ξ ^ 3 ≤ ξ ^ 2 := by nlinarith
      have h4 : 0 ≤ ξ ^ 4 := by positivity
      have h5 : 0 ≤ ξ ^ 5 := by positivity
      linarith
    rw [hslope] at hP'neg
    have hba : 0 < b - a := sub_pos.mpr hlt
    rcases div_nonpos_iff.mp hP'neg with ⟨_, hbad⟩ | ⟨hgood, _⟩
    · linarith
    · linarith
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hstep : ∀ j ∈ Finset.Ico 1 K,
      Q (((j + 1 : ℕ) : ℝ) / (K : ℝ)) - Q ((j : ℝ) / (K : ℝ)) - 1 / (K : ℝ) ^ 2 ≤
        (1 / (K : ℝ)) * P (((j + 1 : ℕ) : ℝ) / (K : ℝ)) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hjK : j < K := (Finset.mem_Ico.mp hj).2
    set a : ℝ := (j : ℝ) / (K : ℝ)
    set b : ℝ := ((j + 1 : ℕ) : ℝ) / (K : ℝ)
    have hab : a < b := by
      apply div_lt_div_of_pos_right _ hK0
      exact_mod_cast Nat.lt_succ_self j
    have ha0 : 0 ≤ a := by positivity
    have hb1 : b ≤ 1 := by
      rw [div_le_one hK0]
      exact_mod_cast (show j + 1 ≤ K by omega)
    have hba : b - a = 1 / (K : ℝ) := by dsimp [a, b]; push_cast; field_simp; ring
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope Q P hab
      (fun t _ => (hQderiv t).continuousAt.continuousWithinAt)
      (fun t _ => hQderiv t)
    have hQeq : Q b - Q a = (1 / (K : ℝ)) * P ξ := by
      rw [← hba]; exact sub_eq_mul_of_div_eq (sub_ne_zero.mpr hab.ne') hslope.symm
    have hPa : P ξ ≤ P a := hPanti a ξ ha0 hξ.1.le (le_trans hξ.2.le hb1)
    have hdiffP : P a - P b ≤ 1 / (K : ℝ) := by
      obtain ⟨ζ, hζ, hsl⟩ := exists_hasDerivAt_eq_slope P P' hab
        (fun t _ => (hPderiv t).continuousAt.continuousWithinAt) (fun t _ => hPderiv t)
      have hζ0 : 0 ≤ ζ := le_trans ha0 hζ.1.le
      have hζ1 : ζ ≤ 1 := le_trans hζ.2.le hb1
      have hP'ge : -(1 : ℝ) ≤ P' ζ := by
        dsimp [P']
        have h2 : ζ ^ 2 ≤ 1 := pow_le_one₀ hζ0 hζ1
        have h3 : 0 ≤ ζ ^ 3 := pow_nonneg hζ0 3
        have h4 : ζ ^ 4 ≤ 1 := pow_le_one₀ hζ0 hζ1
        have h5 : ζ ^ 5 ≤ 1 := pow_le_one₀ hζ0 hζ1
        linarith
      have hPbPa : P b - P a = (1 / (K : ℝ)) * P' ζ := by
        rw [← hba]; exact sub_eq_mul_of_div_eq (sub_ne_zero.mpr hab.ne') hsl.symm
      have := mul_le_mul_of_nonneg_left hP'ge (show (0 : ℝ) ≤ 1 / (K : ℝ) by positivity)
      linarith
    have h1 : (1 / (K : ℝ)) * P ξ ≤ (1 / (K : ℝ)) * (P b + 1 / (K : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [hQeq]
    have hsq : (1 / (K : ℝ)) * (1 / (K : ℝ)) = 1 / (K : ℝ) ^ 2 := by ring
    linarith
  have htel : ∑ j ∈ Finset.Ico 1 K,
      (Q (((j + 1 : ℕ) : ℝ) / (K : ℝ)) - Q ((j : ℝ) / (K : ℝ))) =
        Q 1 - Q (1 / (K : ℝ)) := by
    have hK1 : 1 ≤ K := by omega
    have haux : ∀ m : ℕ, 1 ≤ m →
        ∑ j ∈ Finset.Ico 1 m, (Q (((j + 1 : ℕ) : ℝ) / (K : ℝ)) - Q ((j : ℝ) / (K : ℝ))) =
          Q ((m : ℝ) / (K : ℝ)) - Q (1 / (K : ℝ)) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        rw [Finset.sum_Ico_succ_top hm, ih]; ring
    rw [haux K hK1, div_self hK0.ne']
  have hsum_le :
      (Q 1 - Q (1 / (K : ℝ))) - ((K - 1 : ℕ) : ℝ) * (1 / (K : ℝ) ^ 2) ≤
        ∑ j ∈ Finset.Ico 1 K, (1 / (K : ℝ)) * P (((j + 1 : ℕ) : ℝ) / (K : ℝ)) := by
    rw [← htel]
    have hcard : ((K - 1 : ℕ) : ℝ) * (1 / (K : ℝ) ^ 2) =
        ∑ _j ∈ Finset.Ico 1 K, (1 / (K : ℝ) ^ 2) := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [hcard, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum hstep
  have hcomp :
      ∑ j ∈ Finset.Ico 1 K, (1 / (K : ℝ)) * P (((j + 1 : ℕ) : ℝ) / (K : ℝ)) ≤
        ∑ j ∈ Finset.Ico 1 K,
          (1 / (K : ℝ)) * ((1 - Real.exp (-(((j + 1 : ℕ) : ℝ) / (K : ℝ)))) /
            (((j + 1 : ℕ) : ℝ) / (K : ℝ))) := by
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply exp_neg_poly_lower
    · positivity
    · rw [div_le_one hK0]
      exact_mod_cast (show j + 1 ≤ K by have := (Finset.mem_Ico.mp hj).2; omega)
  have hQ1 : (79654 / 100000 : ℝ) ≤ Q 1 := by dsimp [Q]; norm_num
  have hQinv : Q (1 / (K : ℝ)) ≤ 2 / (K : ℝ) := by
    set t : ℝ := 1 / (K : ℝ)
    have ht0 : 0 ≤ t := by positivity
    have ht1 : t ≤ 1 := by
      dsimp [t]; rw [div_le_one hK0]; exact_mod_cast (show 1 ≤ K by omega)
    have h2 : 0 ≤ t ^ 2 := sq_nonneg t
    have h3 : t ^ 3 ≤ t := by
      have : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
      nlinarith
    have h4 : 0 ≤ t ^ 4 := pow_nonneg ht0 4
    have h5 : t ^ 5 ≤ t := by
      have : t ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
      nlinarith
    have h6 : 0 ≤ t ^ 6 := pow_nonneg ht0 6
    have h7 : 0 ≤ t ^ 7 := pow_nonneg ht0 7
    change t - t ^ 2 / 4 + t ^ 3 / 18 - t ^ 4 / 96 + t ^ 5 / 600 - t ^ 6 / 4320 - t ^ 7 / 30870 ≤ 2 / (K : ℝ)
    have h2t : 2 * t = 2 / (K : ℝ) := by dsimp [t]; ring
    linarith
  have herr : ((K - 1 : ℕ) : ℝ) * (1 / (K : ℝ) ^ 2) ≤ 1 / (K : ℝ) := by
    have hle : ((K - 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast Nat.sub_le K 1
    calc ((K - 1 : ℕ) : ℝ) * (1 / (K : ℝ) ^ 2)
        ≤ (K : ℝ) * (1 / (K : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hle (by positivity)
      _ = 1 / (K : ℝ) := by field_simp
  have h3K : 2 / (K : ℝ) + 1 / (K : ℝ) = 3 / (K : ℝ) := by ring
  linarith [hsum_le, hcomp, hQ1, hQinv, herr, h3K]

private lemma riemann_sec_S2_upper {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) (L : ℕ) (hL : 1 ≤ L) :
    let h := (b - a) / (L : ℝ)
    ∑ j ∈ Finset.range L, h * (Real.exp (-(a + (j : ℝ) * h)) / (a + (j : ℝ) * h)) ≤
      ((b - 1) * Real.exp (-a) - (a - 1) * Real.exp (-b)) / (a * b) + h := by
  intro h
  have hh0 : 0 < h := div_pos (sub_pos.mpr hab) (by exact_mod_cast hL)
  let F : ℝ → ℝ := fun u => ((a + b - u) / (a * b)) * Real.exp (-u)
  let G : ℝ → ℝ := fun u => -((a + b - 1 - u) / (a * b)) * Real.exp (-u)
  have hGderiv : ∀ u : ℝ, HasDerivAt G (F u) u := by
    intro u
    dsimp [G, F]
    have h1 : HasDerivAt (fun x : ℝ => -((a + b - 1 - x) / (a * b))) (1 / (a * b)) u :=
      ((((hasDerivAt_id u).const_sub (a + b - 1)).div_const (a * b)).fun_neg).congr_deriv (by ring)
    have h2 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-u)) u :=
      (((hasDerivAt_id u).fun_neg).exp).congr_deriv (by simp only [id_eq]; ring)
    have hab0 : a * b ≠ 0 := by nlinarith only [ha, hab]
    exact (h1.fun_mul h2).congr_deriv (by field_simp; ring)
  have hFanti : ∀ u v : ℝ, a ≤ u → u ≤ v → v ≤ b → F v ≤ F u := by
    intro u v hau huv hvb
    dsimp [F]
    have hab0 : 0 < a * b := by nlinarith
    have h1 : (a + b - v) / (a * b) ≤ (a + b - u) / (a * b) :=
      div_le_div_of_nonneg_right (by linarith) hab0.le
    have h2 : Real.exp (-v) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
    have hpos : 0 ≤ (a + b - v) / (a * b) := div_nonneg (by linarith) hab0.le
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (div_nonneg (by linarith) hab0.le)
  have hsec : ∀ u : ℝ, a ≤ u → u ≤ b → Real.exp (-u) / u ≤ F u := by
    intro u hau hub
    dsimp [F]
    have hu0 : 0 < u := by linarith
    have hab0 : 0 < a * b := by nlinarith
    have hinv : 1 / u ≤ (a + b - u) / (a * b) := by
      rw [div_le_div_iff₀ hu0 hab0]
      nlinarith
    calc Real.exp (-u) / u = (1 / u) * Real.exp (-u) := by ring
      _ ≤ ((a + b - u) / (a * b)) * Real.exp (-u) :=
        mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
  have h1 :
      ∑ j ∈ Finset.range L, h * (Real.exp (-(a + (j : ℝ) * h)) / (a + (j : ℝ) * h)) ≤
        ∑ j ∈ Finset.range L, h * F (a + (j : ℝ) * h) := by
    apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ hh0.le
    apply hsec
    · have : 0 ≤ (j : ℝ) * h := by positivity
      linarith
    · have hjL : (j : ℝ) ≤ (L : ℝ) := by exact_mod_cast (Finset.mem_range.mp hj).le
      have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
      have : (j : ℝ) * h ≤ b - a := by
        dsimp [h]; rw [mul_div_assoc', div_le_iff₀ hL0]; nlinarith
      linarith
  have hstep : ∀ j ∈ Finset.range L,
      h * F (a + ((j + 1 : ℕ) : ℝ) * h) ≤
        G (a + ((j + 1 : ℕ) : ℝ) * h) - G (a + (j : ℝ) * h) := by
    intro j hj
    set u := a + (j : ℝ) * h
    set v := a + ((j + 1 : ℕ) : ℝ) * h
    have huv : u < v := by dsimp [u, v]; push_cast; linarith
    have hvu : v - u = h := by dsimp [u, v]; push_cast; ring
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope G F huv
      (fun t _ => (hGderiv t).continuousAt.continuousWithinAt) (fun t _ => hGderiv t)
    have hGeq : G v - G u = h * F ξ := by
      rw [← hvu]; exact sub_eq_mul_of_div_eq (sub_ne_zero.mpr huv.ne') hslope.symm
    rw [hGeq]
    apply mul_le_mul_of_nonneg_left _ hh0.le
    have hau : a ≤ u := by
      dsimp [u]
      have h0 : 0 ≤ (j : ℝ) * h := by positivity
      linarith
    have hvb : v ≤ b := by
      dsimp [v, h]
      have hjL : ((j + 1 : ℕ) : ℝ) ≤ (L : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
      have hL0 : (0 : ℝ) < L := by exact_mod_cast hL
      have : ((j + 1 : ℕ) : ℝ) * ((b - a) / (L : ℝ)) ≤ b - a := by
        rw [mul_div_assoc', div_le_iff₀ hL0]; nlinarith
      linarith
    exact hFanti ξ v (le_trans hau hξ.1.le) hξ.2.le hvb
  have htel :
      ∑ j ∈ Finset.range L, (G (a + ((j + 1 : ℕ) : ℝ) * h) - G (a + (j : ℝ) * h)) =
        G b - G a := by
    have haux : ∀ m : ℕ,
        ∑ j ∈ Finset.range m, (G (a + ((j + 1 : ℕ) : ℝ) * h) - G (a + (j : ℝ) * h)) =
          G (a + (m : ℝ) * h) - G a := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [Finset.sum_range_succ, ih]; ring
    rw [haux L]
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    have heq : a + (L : ℝ) * h = b := by dsimp [h]; field_simp; ring
    rw [heq]
  have hshift :
      ∑ j ∈ Finset.range L, h * F (a + (j : ℝ) * h) =
        h * F a - h * F b + ∑ j ∈ Finset.range L, h * F (a + ((j + 1 : ℕ) : ℝ) * h) := by
    have haux : ∀ m : ℕ,
        ∑ j ∈ Finset.range m, h * F (a + (j : ℝ) * h) =
          h * F a - h * F (a + (m : ℝ) * h) +
            ∑ j ∈ Finset.range m, h * F (a + ((j + 1 : ℕ) : ℝ) * h) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
        ring
    rw [haux L]
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
    have heq : a + (L : ℝ) * h = b := by dsimp [h]; field_simp; ring
    rw [heq]
  have hGbGa : G b - G a = ((b - 1) * Real.exp (-a) - (a - 1) * Real.exp (-b)) / (a * b) := by
    dsimp [G]; ring
  have hFa : F a ≤ 1 := by
    dsimp [F]
    have hab0 : a * b ≠ 0 := by nlinarith
    have hb0 : b ≠ 0 := by linarith
    have heq : (a + b - a) / (a * b) = 1 / a := by field_simp; ring
    rw [heq]
    have h1 : 1 / a ≤ 1 := (div_le_one (by linarith)).mpr ha
    have h2 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-a)]
  have hFb : 0 ≤ F b := by
    dsimp [F]
    have hab0 : 0 < a * b := by nlinarith
    exact mul_nonneg (div_nonneg (by linarith) hab0.le) (Real.exp_pos _).le
  have hsum2 : ∑ j ∈ Finset.range L, h * F (a + ((j + 1 : ℕ) : ℝ) * h) ≤ G b - G a := by
    rw [← htel]
    exact Finset.sum_le_sum hstep
  linarith [h1, hshift, hsum2, hGbGa, mul_le_mul_of_nonneg_left hFa hh0.le,
    mul_nonneg hh0.le hFb]

set_option maxHeartbeats 600000 in
private lemma S2_interval_upper {a b : ℝ} (ha : 1 ≤ a) (hab : a < b) {ε : ℝ} (hε : 0 < ε) :
    ∃ Z₀ : ℕ, 16 ≤ Z₀ ∧ ∀ z : ℕ, Z₀ ≤ z →
      let σ := (Real.log (z : ℝ))⁻¹
      ∑ p ∈ (Finset.Ioc ⌊(z : ℝ) ^ a⌋₊ ⌊(z : ℝ) ^ b⌋₊).filter Nat.Prime,
        (p : ℝ) ^ (-(1 + σ)) ≤
        ((b - 1) * Real.exp (-a) - (a - 1) * Real.exp (-b)) / (a * b) + ε := by
  obtain ⟨L, hL⟩ := exists_nat_ge (max (4 * (b - a) / ε) 4)
  have hL1 : 1 ≤ L := by
    have : (4 : ℝ) ≤ (L : ℝ) := (le_max_right _ _).trans hL
    exact_mod_cast (by linarith : (1 : ℝ) ≤ (L : ℝ))
  have hL0 : (0 : ℝ) < L := by exact_mod_cast hL1
  set h : ℝ := (b - a) / (L : ℝ)
  have hh0 : 0 < h := div_pos (sub_pos.mpr hab) hL0
  have hh_lt : h ≤ ε / 4 := by
    have h1 : 4 * (b - a) / ε ≤ (L : ℝ) := (le_max_left _ _).trans hL
    rw [div_le_iff₀ hε] at h1
    dsimp [h]
    rw [div_le_iff₀ hL0]
    nlinarith
  set δ : ℝ := min (ε / (16 * (b - a + 1))) (1 / 4)
  have hδ0 : 0 < δ := lt_min (div_pos hε (by nlinarith)) (by norm_num)
  have hδ2 : δ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨X₀, hX8, hsum_p⟩ := sum_log_div_prime_Ioc hδ0 hδ2
  have h_log_tend : Tendsto (fun z : ℕ => Real.log (z : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_z_large : ∀ᶠ z : ℕ in atTop,
      16 ≤ z ∧
      (X₀ : ℝ) + 2 ≤ (z : ℝ) ^ a ∧
      (16 * (L : ℝ) * (4 * δ + 2) / ε) ≤ Real.log (z : ℝ) ∧
      (8 * (L : ℝ) / ε) ≤ (z : ℝ) ^ a := by
    have h1 : ∀ᶠ z : ℕ in atTop, 16 ≤ z := eventually_ge_atTop 16
    have h2 : ∀ᶠ z : ℕ in atTop, (X₀ : ℝ) + 2 ≤ (z : ℝ) ^ a := by
      have ht : Tendsto (fun z : ℕ => (z : ℝ) ^ a) atTop atTop :=
        (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
      exact ht.eventually (eventually_ge_atTop _)
    have h3 : ∀ᶠ z : ℕ in atTop, (16 * (L : ℝ) * (4 * δ + 2) / ε) ≤ Real.log (z : ℝ) :=
      h_log_tend.eventually (eventually_ge_atTop _)
    have h4 : ∀ᶠ z : ℕ in atTop, (8 * (L : ℝ) / ε) ≤ (z : ℝ) ^ a := by
      have ht : Tendsto (fun z : ℕ => (z : ℝ) ^ a) atTop atTop :=
        (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
      exact ht.eventually (eventually_ge_atTop _)
    filter_upwards [h1, h2, h3, h4] with z hz1 hz2 hz3 hz4
    exact ⟨hz1, hz2, hz3, hz4⟩
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp h_z_large
  refine ⟨max Z₀ 16, le_max_right _ _, fun z hz => ?_⟩
  obtain ⟨hz16, hzaX, hlogz_big, hza_big⟩ := hZ₀ z ((le_max_left Z₀ 16).trans hz)
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (show 1 < z by omega)
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos hz1
  set σ : ℝ := (Real.log (z : ℝ))⁻¹
  let u : ℕ → ℝ := fun j => a + (j : ℝ) * h
  let N : ℕ → ℕ := fun j => ⌊(z : ℝ) ^ (u j)⌋₊
  have hu0 : u 0 = a := by dsimp [u]; ring
  have huL : u L = b := by dsimp [u, h]; field_simp; ring
  have hN_mono : ∀ j : ℕ, j < L → N j ≤ N (j + 1) := by
    intro j _
    apply Nat.floor_mono
    apply Real.rpow_le_rpow_of_exponent_le hz1.le
    dsimp [u]; push_cast; linarith
  have hsplit :
      ∑ p ∈ (Finset.Ioc (N 0) (N L)).filter Nat.Prime, (p : ℝ) ^ (-(1 + σ)) =
        ∑ j ∈ Finset.range L,
          ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, (p : ℝ) ^ (-(1 + σ)) := by
    have haux : ∀ m : ℕ, m ≤ L →
        ∑ p ∈ (Finset.Ioc (N 0) (N m)).filter Nat.Prime, (p : ℝ) ^ (-(1 + σ)) =
          ∑ j ∈ Finset.range m,
            ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, (p : ℝ) ^ (-(1 + σ)) := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
        have hN0m : N 0 ≤ N m := by
          apply Nat.floor_mono
          apply Real.rpow_le_rpow_of_exponent_le hz1.le
          dsimp [u]
          have h0 : 0 ≤ (m : ℝ) * h := by positivity
          linarith
        have hNmm : N m ≤ N (m + 1) := hN_mono m (by omega)
        rw [Finset.sum_range_succ, ← ih (by omega)]
        rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
        exact (Finset.sum_Ioc_consecutive _ hN0m hNmm).symm
    exact haux L le_rfl
  dsimp only
  rw [show ⌊(z : ℝ) ^ a⌋₊ = N 0 by dsimp [N]; rw [hu0],
    show ⌊(z : ℝ) ^ b⌋₊ = N L by dsimp [N]; rw [huL], hsplit]
  have hblock : ∀ j ∈ Finset.range L,
      ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, (p : ℝ) ^ (-(1 + σ)) ≤
        (1 + δ) * h * (Real.exp (-(u j)) / u j) +
          (4 * δ + 2) / Real.log (z : ℝ) + 2 / ((z : ℝ) ^ a) := by
    intro j hj
    have hjL : j < L := Finset.mem_range.mp hj
    have huj_ge : a ≤ u j := by
      dsimp [u]
      have h0 : 0 ≤ (j : ℝ) * h := by positivity
      linarith
    have hNj_ge : (z : ℝ) ^ a - 1 ≤ (N j : ℝ) := by
      have h1 : (z : ℝ) ^ a ≤ (z : ℝ) ^ (u j) :=
        Real.rpow_le_rpow_of_exponent_le hz1.le huj_ge
      have h2 := Nat.sub_one_lt_floor ((z : ℝ) ^ (u j))
      linarith
    have hNjX : X₀ ≤ N j := by
      have h1 : (X₀ : ℝ) ≤ (N j : ℝ) := by linarith
      exact_mod_cast h1
    have hNjpos : 0 < (N j : ℝ) := by
      have hXpos : (0 : ℝ) < X₀ := by exact_mod_cast (show 0 < X₀ by omega)
      linarith
    have hpt : ∀ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime,
        (p : ℝ) ^ (-(1 + σ)) ≤
          (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) * (Real.log (p : ℝ) / (p : ℝ)) := by
      intro p hp
      have hp_mem := Finset.mem_filter.mp hp
      have hp_gt : (N j : ℝ) < (p : ℝ) := by exact_mod_cast (Finset.mem_Ioc.mp hp_mem.1).1
      have hp_z : (z : ℝ) ^ (u j) < (p : ℝ) := by
        exact lt_of_lt_of_le (Nat.lt_floor_add_one _) (by exact_mod_cast (Finset.mem_Ioc.mp hp_mem.1).1)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp_mem.2.pos
      have hlogp_gt : u j * Real.log (z : ℝ) < Real.log (p : ℝ) := by
        have h := Real.log_lt_log (Real.rpow_pos_of_pos (by linarith) _) hp_z
        rwa [Real.log_rpow (by linarith)] at h
      have hlogp_pos : 0 < Real.log (p : ℝ) := lt_trans (mul_pos (by linarith) hlogz) hlogp_gt
      have hps : (p : ℝ) ^ (-σ) ≤ Real.exp (-(u j)) := by
        rw [Real.rpow_def_of_pos hp0]
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_right hlogp_gt.le (show 0 ≤ σ by positivity)
        have heq : u j * Real.log (z : ℝ) * σ = u j := by dsimp [σ]; field_simp
        rw [heq] at hmul
        linarith
      have hpow_split : (p : ℝ) ^ (-(1 + σ)) = (p : ℝ) ^ (-σ) / (p : ℝ) := by
        rw [show -(1 + σ) = (-σ) + (-1) by ring, Real.rpow_add hp0, Real.rpow_neg_one, div_eq_mul_inv]
      rw [hpow_split]
      have hdiv : 1 / Real.log (p : ℝ) ≤ 1 / (u j * Real.log (z : ℝ)) :=
        one_div_le_one_div_of_le (mul_pos (by linarith) hlogz) hlogp_gt.le
      calc (p : ℝ) ^ (-σ) / (p : ℝ)
          = ((p : ℝ) ^ (-σ) / Real.log (p : ℝ)) * (Real.log (p : ℝ) / (p : ℝ)) := by field_simp
        _ ≤ (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) * (Real.log (p : ℝ) / (p : ℝ)) := by
            apply mul_le_mul_of_nonneg_right _ (div_nonneg hlogp_pos.le hp0.le)
            rw [div_eq_mul_inv, div_eq_mul_inv]
            exact mul_le_mul hps (by simpa [one_div] using hdiv)
              (inv_nonneg.mpr hlogp_pos.le) (Real.exp_pos _).le
    have hsum1 := Finset.sum_le_sum hpt
    rw [← Finset.mul_sum] at hsum1
    have hlog_sum := (hsum_p (N j) (N (j + 1)) hNjX (hN_mono j hjL)).2
    have hratio : Real.log ((N (j + 1) : ℝ) / (N j : ℝ)) ≤ h * Real.log (z : ℝ) + 2 / ((z : ℝ) ^ a) := by
      have hnum : (N (j + 1) : ℝ) ≤ (z : ℝ) ^ (u (j + 1)) := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
      have hden_pos : 0 < (z : ℝ) ^ (u j) - 1 := by
        have h1 : (z : ℝ) ^ a ≤ (z : ℝ) ^ (u j) :=
          Real.rpow_le_rpow_of_exponent_le hz1.le huj_ge
        have hX4 : (8 : ℝ) ≤ (X₀ : ℝ) := by exact_mod_cast hX8
        linarith
      have hden : (z : ℝ) ^ (u j) - 1 < (N j : ℝ) := Nat.sub_one_lt_floor _
      have hle1 : (N (j + 1) : ℝ) / (N j : ℝ) ≤ (z : ℝ) ^ (u (j + 1)) / ((z : ℝ) ^ (u j) - 1) :=
        div_le_div₀ (Real.rpow_nonneg (by linarith) _) hnum hden_pos hden.le
      have hle2 : Real.log ((N (j + 1) : ℝ) / (N j : ℝ)) ≤
          Real.log ((z : ℝ) ^ (u (j + 1)) / ((z : ℝ) ^ (u j) - 1)) :=
        Real.log_le_log (div_pos (by have hmono := hN_mono j hjL; exact_mod_cast (show 0 < N (j + 1) by omega)) hNjpos) hle1
      have hpow_div : (z : ℝ) ^ (u (j + 1)) / ((z : ℝ) ^ (u j) - 1) =
          (z : ℝ) ^ h * (1 - ((z : ℝ) ^ (u j))⁻¹)⁻¹ := by
        have hzuj : (z : ℝ) ^ (u j) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
        have hu_add : u (j + 1) = u j + h := by dsimp [u]; push_cast; ring
        rw [hu_add, Real.rpow_add (by linarith)]
        field_simp
      rw [hpow_div, Real.log_mul (Real.rpow_pos_of_pos (by linarith) _).ne'
        (inv_ne_zero (sub_ne_zero.mpr (by
          have h1 : 1 < (z : ℝ) ^ (u j) := by linarith
          exact (inv_lt_one_of_one_lt₀ h1).ne'))),
        Real.log_rpow (by linarith), Real.log_inv] at hle2
      have hinv_lt : ((z : ℝ) ^ (u j))⁻¹ ≤ 1 / 2 := by
        have h1 : (2 : ℝ) ≤ (z : ℝ) ^ (u j) := by
          have : (z : ℝ) ^ a ≤ (z : ℝ) ^ (u j) := Real.rpow_le_rpow_of_exponent_le hz1.le huj_ge
          have hX4 : (8 : ℝ) ≤ (X₀ : ℝ) := by exact_mod_cast hX8
          linarith
        exact inv_le_of_inv_le₀ (by norm_num) (by simpa using h1)
      have hneglog := neg_log_one_sub_le (inv_nonneg.mpr (Real.rpow_nonneg (by linarith) _))
        (lt_of_le_of_lt hinv_lt (by norm_num))
      have h2bound : ((z : ℝ) ^ (u j))⁻¹ / (1 - ((z : ℝ) ^ (u j))⁻¹) ≤ 2 / ((z : ℝ) ^ a) := by
        have h1 : (1 / 2 : ℝ) ≤ 1 - ((z : ℝ) ^ (u j))⁻¹ := by linarith
        have h2 : ((z : ℝ) ^ (u j))⁻¹ ≤ ((z : ℝ) ^ a)⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
            (Real.rpow_le_rpow_of_exponent_le hz1.le huj_ge)
        calc ((z : ℝ) ^ (u j))⁻¹ / (1 - ((z : ℝ) ^ (u j))⁻¹)
            ≤ ((z : ℝ) ^ (u j))⁻¹ / (1 / 2) :=
              div_le_div_of_nonneg_left (inv_nonneg.mpr (Real.rpow_nonneg (by linarith) _)) (by norm_num) h1
          _ = 2 * ((z : ℝ) ^ (u j))⁻¹ := by ring
          _ ≤ 2 * ((z : ℝ) ^ a)⁻¹ := mul_le_mul_of_nonneg_left h2 (by norm_num)
          _ = 2 / ((z : ℝ) ^ a) := by rw [div_eq_mul_inv]
      linarith
    have hcoeff_le : Real.exp (-(u j)) / (u j * Real.log (z : ℝ)) ≤ 1 / Real.log (z : ℝ) := by
      rw [← div_div]
      apply div_le_div_of_nonneg_right _ hlogz.le
      have h1 : Real.exp (-(u j)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h2 : (1 : ℝ) ≤ u j := le_trans ha huj_ge
      rw [div_le_one (by linarith)]; linarith
    have hcoeff_pos : 0 ≤ Real.exp (-(u j)) / (u j * Real.log (z : ℝ)) := by
      have : 0 < u j := by linarith
      positivity
    have hN2 : 2 / (N j : ℝ) ≤ 1 := by
      have hX8' : (8 : ℝ) ≤ (X₀ : ℝ) := by exact_mod_cast hX8
      have hNj8 : (8 : ℝ) ≤ (N j : ℝ) := by exact_mod_cast (hX8.trans hNjX)
      rw [div_le_one (by linarith)]; linarith
    have hstep1 := hsum1.trans (mul_le_mul_of_nonneg_left hlog_sum hcoeff_pos)
    have hstep2 :
        (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) *
          ((1 + δ) * Real.log ((N (j + 1) : ℝ) / (N j : ℝ)) + 4 * δ + 2 / (N j : ℝ)) ≤
        (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) *
          ((1 + δ) * (h * Real.log (z : ℝ) + 2 / ((z : ℝ) ^ a)) + (4 * δ + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hcoeff_pos
      have := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ 1 + δ by linarith)
      linarith
    have hmain_eq :
        (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) * ((1 + δ) * (h * Real.log (z : ℝ))) =
          (1 + δ) * h * (Real.exp (-(u j)) / u j) := by
      field_simp
    have hrem1 :
        (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) * ((1 + δ) * (2 / ((z : ℝ) ^ a))) ≤
          2 / ((z : ℝ) ^ a) := by
      have hlog1 : 1 ≤ Real.log (z : ℝ) := by
        have : Real.exp 1 ≤ (z : ℝ) := by
          have he : Real.exp 1 ≤ 3 := by
            have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1) le_rfl (by decide : (0 : ℕ) < 4)
            simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
            norm_num at hb; linarith
          have hz3 : (3 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show 3 ≤ z by omega)
          linarith
        calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
          _ ≤ Real.log (z : ℝ) := Real.log_le_log (Real.exp_pos 1) this
      have h3 : Real.exp (-(u j)) / (u j * Real.log (z : ℝ)) ≤ 1 / 2 := by
        have h1 : Real.exp (-(u j)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
        have he1 : Real.exp (-1) ≤ 1 / 2 := by
          have : Real.exp (-1) = (Real.exp (-(1 / 4 : ℝ))) ^ 4 := by
            rw [← exp_neg_pow_quarter 4]; norm_num
          rw [this]
          have h := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_quarter_bounds.2 4
          norm_num at h; linarith
        have hden : 1 ≤ u j * Real.log (z : ℝ) := by nlinarith only [ha, huj_ge, hlog1]
        rw [div_le_iff₀ (by linarith)]
        linarith
      have h4 : (1 + δ) * (2 / ((z : ℝ) ^ a)) ≤ 4 / ((z : ℝ) ^ a) := by
        have hpos : 0 ≤ 2 / ((z : ℝ) ^ a) := by positivity
        have heq4 : 4 / ((z : ℝ) ^ a) = 2 * (2 / ((z : ℝ) ^ a)) := by ring
        rw [heq4]
        nlinarith only [hδ2, hpos]
      calc (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) * ((1 + δ) * (2 / ((z : ℝ) ^ a)))
          ≤ (1 / 2) * (4 / ((z : ℝ) ^ a)) :=
            mul_le_mul h3 h4 (by positivity) (by norm_num)
        _ = 2 / ((z : ℝ) ^ a) := by ring
    have hrem2 :
        (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) * (4 * δ + 1) ≤
          (4 * δ + 2) / Real.log (z : ℝ) := by
      calc (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) * (4 * δ + 1)
          ≤ (1 / Real.log (z : ℝ)) * (4 * δ + 1) :=
            mul_le_mul_of_nonneg_right hcoeff_le (by linarith)
        _ ≤ (4 * δ + 2) / Real.log (z : ℝ) := by
            rw [one_div_mul_eq_div]
            exact div_le_div_of_nonneg_right (by linarith) hlogz.le
    calc ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, (p : ℝ) ^ (-(1 + σ))
        ≤ (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) *
            ((1 + δ) * (h * Real.log (z : ℝ) + 2 / ((z : ℝ) ^ a)) + (4 * δ + 1)) :=
          hstep1.trans hstep2
      _ = (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) * ((1 + δ) * (h * Real.log (z : ℝ))) +
          (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) * ((1 + δ) * (2 / ((z : ℝ) ^ a))) +
          (Real.exp (-(u j)) / (u j * Real.log (z : ℝ))) * (4 * δ + 1) := by ring
      _ ≤ (1 + δ) * h * (Real.exp (-(u j)) / u j) +
          2 / ((z : ℝ) ^ a) + (4 * δ + 2) / Real.log (z : ℝ) := by
          rw [hmain_eq]; linarith
      _ = (1 + δ) * h * (Real.exp (-(u j)) / u j) +
          (4 * δ + 2) / Real.log (z : ℝ) + 2 / ((z : ℝ) ^ a) := by ring
  have hsum_all := Finset.sum_le_sum hblock
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_all
  have hfactor :
      ∑ j ∈ Finset.range L, (1 + δ) * h * (Real.exp (-(u j)) / u j) =
        (1 + δ) * ∑ j ∈ Finset.range L, h * (Real.exp (-(a + (j : ℝ) * h)) / (a + (j : ℝ) * h)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; dsimp [u]; ring
  rw [hfactor] at hsum_all
  have hriem := riemann_sec_S2_upper ha hab L hL1
  set T : ℝ := ((b - 1) * Real.exp (-a) - (a - 1) * Real.exp (-b)) / (a * b)
  have hab0 : 0 < a * b := mul_pos (by linarith) (by linarith)
  have hT_nonneg : 0 ≤ T := by
    dsimp [T]
    apply div_nonneg _ hab0.le
    have h1 : a - 1 ≤ b - 1 := by linarith
    have h2 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    nlinarith only [ha, h1, h2, Real.exp_pos (-a), Real.exp_pos (-b)]
  have hT_ub : T ≤ 1 := by
    dsimp [T]
    rw [div_le_one hab0]
    have h1 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 0 ≤ Real.exp (-b) := (Real.exp_pos _).le
    have h3 : (b - 1) * Real.exp (-a) ≤ b - 1 := mul_le_of_le_one_right (by linarith) h1
    have h4 : 0 ≤ (a - 1) * Real.exp (-b) := mul_nonneg (by linarith) h2
    have h5 : b ≤ a * b := by nlinarith only [ha, hab]
    linarith
  have hterm1 : (1 + δ) * (T + h) ≤ T + ε / 2 := by
    have hδ_le : δ ≤ ε / (16 * (b - a + 1)) := min_le_left _ _
    have hba1 : 0 < 16 * (b - a + 1) := by linarith
    have hδ_T : δ * T ≤ ε / 8 := by
      calc δ * T ≤ (ε / (16 * (b - a + 1))) * 1 :=
            mul_le_mul hδ_le hT_ub hT_nonneg (div_nonneg hε.le hba1.le)
        _ ≤ ε / 8 := by
            rw [mul_one, div_le_div_iff₀ hba1 (by norm_num)]
            nlinarith only [hε, hab]
    have hδ_h : (1 + δ) * h ≤ (3 / 2) * (ε / 4) :=
      mul_le_mul (by linarith) hh_lt hh0.le (by norm_num)
    linarith
  have hterm2 : (L : ℝ) * ((4 * δ + 2) / Real.log (z : ℝ)) ≤ ε / 4 := by
    rw [mul_div_assoc', div_le_iff₀ hlogz]
    have h1 := (div_le_iff₀ hε).mp hlogz_big
    have h2 : 16 * ((L : ℝ) * (4 * δ + 2)) = 16 * (L : ℝ) * (4 * δ + 2) := by ring
    have h3 : Real.log (z : ℝ) * ε = 4 * (ε / 4 * Real.log (z : ℝ)) := by ring
    have hnn : 0 ≤ (L : ℝ) * (4 * δ + 2) := mul_nonneg hL0.le (by linarith)
    linarith
  have hterm3 : (L : ℝ) * (2 / ((z : ℝ) ^ a)) ≤ ε / 4 := by
    have hza_pos : 0 < (z : ℝ) ^ a := Real.rpow_pos_of_pos (by linarith) _
    rw [mul_div_assoc', div_le_iff₀ hza_pos]
    have h1 := (div_le_iff₀ hε).mp hza_big
    have h2 : (z : ℝ) ^ a * ε = ε * (z : ℝ) ^ a := by ring
    linarith
  have hriem_mul := mul_le_mul_of_nonneg_left hriem (show (0 : ℝ) ≤ 1 + δ by linarith)
  linarith

private lemma S1_lower_bound :
    ∃ Z₀ : ℕ, 16 ≤ Z₀ ∧ ∀ z : ℕ, Z₀ ≤ z →
      let σ := (Real.log (z : ℝ))⁻¹
      (79650 / 100000 : ℝ) ≤
        ∑ p ∈ Nat.primesLE z, (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) := by
  obtain ⟨K, hKeq⟩ : ∃ K : ℕ, K = 100000 := ⟨100000, rfl⟩
  have hK4 : 4 ≤ K := by omega
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  let δ : ℝ := 1 / 1000000
  have hδ0 : 0 < δ := by norm_num [δ]
  have hδ2 : δ < 1 / 2 := by norm_num [δ]
  obtain ⟨X₀, hX8, hsum_p⟩ := sum_log_div_prime_Ioc hδ0 hδ2
  have h_log_tend : Tendsto (fun z : ℕ => Real.log (z : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h_pow_tend : Tendsto (fun z : ℕ => (z : ℝ) ^ (1 / (K : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
  have h_ev : ∀ᶠ z : ℕ in atTop,
      16 ≤ z ∧
      (X₀ : ℝ) + 2 ≤ (z : ℝ) ^ (1 / (K : ℝ)) ∧
      (10 ^ 12 : ℝ) ≤ Real.log (z : ℝ) ∧
      (10 ^ 12 : ℝ) ≤ (z : ℝ) ^ (1 / (K : ℝ)) := by
    filter_upwards [eventually_ge_atTop 16,
      h_pow_tend.eventually (eventually_ge_atTop ((X₀ : ℝ) + 2)),
      h_log_tend.eventually (eventually_ge_atTop (10 ^ 12 : ℝ)),
      h_pow_tend.eventually (eventually_ge_atTop (10 ^ 12 : ℝ))] with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨Z₀, hZ₀⟩ := eventually_atTop.mp h_ev
  refine ⟨max Z₀ 16, le_max_right _ _, fun z hz => ?_⟩
  obtain ⟨hz16, hzX, hlog_big, hzpow_big⟩ := hZ₀ z ((le_max_left Z₀ 16).trans hz)
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (show 1 < z by omega)
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos hz1
  set σ : ℝ := (Real.log (z : ℝ))⁻¹
  let u : ℕ → ℝ := fun j => (j : ℝ) / (K : ℝ)
  let N : ℕ → ℕ := fun j => ⌊(z : ℝ) ^ (u j)⌋₊
  have hNK : N K = z := by
    dsimp [N, u]; rw [div_self hK0.ne', Real.rpow_one, Nat.floor_natCast]
  have hN_mono : ∀ j : ℕ, N j ≤ N (j + 1) := by
    intro j
    apply Nat.floor_mono
    apply Real.rpow_le_rpow_of_exponent_le hz1.le
    dsimp [u]
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hK0.le
  have hsub : (Finset.Ioc (N 1) (N K)).filter Nat.Prime ⊆ Nat.primesLE z := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp
    rw [Nat.mem_primesLE, ← hNK]
    exact ⟨hp.1.2, hp.2⟩
  have hdrop :
      ∑ p ∈ (Finset.Ioc (N 1) (N K)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) ≤
        ∑ p ∈ Nat.primesLE z, (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro p hp _
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le
    apply div_nonneg _ (by linarith)
    have : (p : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by dsimp [σ]; positivity |> neg_nonpos.mpr)
    linarith
  have hsplit :
      ∑ p ∈ (Finset.Ioc (N 1) (N K)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) =
        ∑ j ∈ Finset.Ico 1 K,
          ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) := by
    have haux : ∀ m : ℕ, 1 ≤ m →
        ∑ p ∈ (Finset.Ioc (N 1) (N m)).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) =
          ∑ j ∈ Finset.Ico 1 m,
            ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => simp
      | succ m hm ih =>
        have hN1m : N 1 ≤ N m := by
          apply Nat.floor_mono
          apply Real.rpow_le_rpow_of_exponent_le hz1.le
          dsimp [u]; exact div_le_div_of_nonneg_right (by exact_mod_cast hm) hK0.le
        rw [Finset.sum_Ico_succ_top hm, ← ih]
        rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
        exact (Finset.sum_Ioc_consecutive _ hN1m (hN_mono m)).symm
    exact haux K (by omega)
  have hblock : ∀ j ∈ Finset.Ico 1 K,
      (1 - δ) * (1 / (K : ℝ)) * ((1 - Real.exp (-(u (j + 1)))) / u (j + 1)) -
        (4 * δ + 2) / Real.log (z : ℝ) - 2 / ((z : ℝ) ^ (1 / (K : ℝ))) ≤
        ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) := by
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    have hjK : j < K := (Finset.mem_Ico.mp hj).2
    have hu1_le : 1 / (K : ℝ) ≤ u j := by
      dsimp [u]; exact div_le_div_of_nonneg_right (by exact_mod_cast hj1) hK0.le
    have huj1_pos : 0 < u (j + 1) := by dsimp [u]; positivity
    have hNjX : X₀ ≤ N j := by
      have h1 : (z : ℝ) ^ (1 / (K : ℝ)) ≤ (z : ℝ) ^ (u j) :=
        Real.rpow_le_rpow_of_exponent_le hz1.le hu1_le
      have h2 := Nat.sub_one_lt_floor ((z : ℝ) ^ (u j))
      have h3 : (X₀ : ℝ) ≤ (N j : ℝ) := by linarith
      exact_mod_cast h3
    have hpt : ∀ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime,
        ((1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ))) * (Real.log (p : ℝ) / (p : ℝ)) ≤
          (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) := by
      intro p hp
      have hp_mem := Finset.mem_filter.mp hp
      have hp_le : (p : ℝ) ≤ (z : ℝ) ^ (u (j + 1)) :=
        (Nat.cast_le.mpr (Finset.mem_Ioc.mp hp_mem.1).2).trans
          (Nat.floor_le (Real.rpow_nonneg (by linarith) _))
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hp_mem.2.one_lt
      have hp0 : (0 : ℝ) < p := by linarith
      have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
      have hlogp_le : σ * Real.log (p : ℝ) ≤ u (j + 1) := by
        have h := Real.log_le_log hp0 hp_le
        rw [Real.log_rpow (by linarith)] at h
        dsimp [σ]
        rw [inv_mul_le_iff₀ hlogz]
        linarith
      have hanti := one_sub_exp_div_anti (mul_pos (by dsimp [σ]; positivity) hlogp_pos) hlogp_le
      have hpeq : Real.exp (-(σ * Real.log (p : ℝ))) = (p : ℝ) ^ (-σ) := by
        rw [Real.rpow_def_of_pos hp0]; congr 1; ring
      rw [hpeq] at hanti
      have hanti2 : (1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ)) ≤
          (1 - (p : ℝ) ^ (-σ)) / Real.log (p : ℝ) := by
        have hmul := mul_le_mul_of_nonneg_right hanti (show (0 : ℝ) ≤ σ by dsimp [σ]; positivity)
        have hlhs : (1 - Real.exp (-(u (j + 1)))) / u (j + 1) * σ =
            (1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ)) := by
          dsimp [σ]; field_simp
        have hrhs : (1 - (p : ℝ) ^ (-σ)) / (σ * Real.log (p : ℝ)) * σ =
            (1 - (p : ℝ) ^ (-σ)) / Real.log (p : ℝ) := by
          have hσ0 : σ ≠ 0 := by dsimp [σ]; positivity
          field_simp
        linarith
      calc ((1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ))) * (Real.log (p : ℝ) / (p : ℝ))
          ≤ ((1 - (p : ℝ) ^ (-σ)) / Real.log (p : ℝ)) * (Real.log (p : ℝ) / (p : ℝ)) :=
            mul_le_mul_of_nonneg_right hanti2 (div_nonneg hlogp_pos.le hp0.le)
        _ = (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) := by field_simp
    have hsum1 := Finset.sum_le_sum hpt
    rw [← Finset.mul_sum] at hsum1
    have hlog_sum := (hsum_p (N j) (N (j + 1)) hNjX (hN_mono j)).1
    have hratio : (1 / (K : ℝ)) * Real.log (z : ℝ) - 2 / ((z : ℝ) ^ (1 / (K : ℝ))) ≤
        Real.log ((N (j + 1) : ℝ) / (N j : ℝ)) := by
      have hnum : (z : ℝ) ^ (u (j + 1)) - 1 < (N (j + 1) : ℝ) := Nat.sub_one_lt_floor _
      have hden : (N j : ℝ) ≤ (z : ℝ) ^ (u j) := Nat.floor_le (Real.rpow_nonneg (by linarith) _)
      have hNj_pos : 0 < (N j : ℝ) := by exact_mod_cast (show 0 < N j by omega)
      have hnum_pos : 0 < (z : ℝ) ^ (u (j + 1)) - 1 := by
        have h1 : (z : ℝ) ^ (1 / (K : ℝ)) ≤ (z : ℝ) ^ (u (j + 1)) :=
          Real.rpow_le_rpow_of_exponent_le hz1.le
            (le_trans hu1_le (by dsimp [u]; exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hK0.le))
        linarith
      have hle1 : ((z : ℝ) ^ (u (j + 1)) - 1) / ((z : ℝ) ^ (u j)) ≤ (N (j + 1) : ℝ) / (N j : ℝ) :=
        div_le_div₀ (Nat.cast_nonneg _) hnum.le hNj_pos hden
      have hle2 := Real.log_le_log (div_pos hnum_pos (Real.rpow_pos_of_pos (by linarith) _)) hle1
      have hpow_eq : ((z : ℝ) ^ (u (j + 1)) - 1) / ((z : ℝ) ^ (u j)) =
          (z : ℝ) ^ (1 / (K : ℝ)) * (1 - ((z : ℝ) ^ (u (j + 1)))⁻¹) := by
        have hu_add : u (j + 1) = u j + 1 / (K : ℝ) := by dsimp [u]; push_cast; field_simp
        rw [hu_add, Real.rpow_add (by linarith)]
        have hzuj : (z : ℝ) ^ (u j) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
        have hzK : (z : ℝ) ^ (1 / (K : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos (by linarith) _).ne'
        field_simp
      rw [hpow_eq, Real.log_mul (Real.rpow_pos_of_pos (by linarith) _).ne'
        (sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))).ne', Real.log_rpow (by linarith)] at hle2
      have hinv_le : ((z : ℝ) ^ (u (j + 1)))⁻¹ ≤ 1 / 2 := by
        have h1 : (2 : ℝ) ≤ (z : ℝ) ^ (u (j + 1)) := by
          have : (z : ℝ) ^ (1 / (K : ℝ)) ≤ (z : ℝ) ^ (u (j + 1)) :=
            Real.rpow_le_rpow_of_exponent_le hz1.le
              (le_trans hu1_le (by dsimp [u]; exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hK0.le))
          linarith
        exact inv_le_of_inv_le₀ (by norm_num) (by simpa using h1)
      have hneg := neg_log_one_sub_le (inv_nonneg.mpr (Real.rpow_nonneg (by linarith) _))
        (lt_of_le_of_lt hinv_le (by norm_num))
      have h2b : ((z : ℝ) ^ (u (j + 1)))⁻¹ / (1 - ((z : ℝ) ^ (u (j + 1)))⁻¹) ≤
          2 / ((z : ℝ) ^ (1 / (K : ℝ))) := by
        have h1 : (1 / 2 : ℝ) ≤ 1 - ((z : ℝ) ^ (u (j + 1)))⁻¹ := by linarith
        have h2 : ((z : ℝ) ^ (u (j + 1)))⁻¹ ≤ ((z : ℝ) ^ (1 / (K : ℝ)))⁻¹ :=
          inv_anti₀ (Real.rpow_pos_of_pos (by linarith) _)
            (Real.rpow_le_rpow_of_exponent_le hz1.le
              (le_trans hu1_le (by dsimp [u]; exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ j) hK0.le)))
        calc ((z : ℝ) ^ (u (j + 1)))⁻¹ / (1 - ((z : ℝ) ^ (u (j + 1)))⁻¹)
            ≤ ((z : ℝ) ^ (u (j + 1)))⁻¹ / (1 / 2) :=
              div_le_div_of_nonneg_left (inv_nonneg.mpr (Real.rpow_nonneg (by linarith) _)) (by norm_num) h1
          _ = 2 * ((z : ℝ) ^ (u (j + 1)))⁻¹ := by ring
          _ ≤ 2 * ((z : ℝ) ^ (1 / (K : ℝ)))⁻¹ := mul_le_mul_of_nonneg_left h2 (by norm_num)
          _ = 2 / ((z : ℝ) ^ (1 / (K : ℝ))) := by rw [← div_eq_mul_inv]
      linarith
    have hcoeff_pos : 0 ≤ (1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ)) := by
      apply div_nonneg _ (mul_nonneg huj1_pos.le hlogz.le)
      have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr huj1_pos.le)
      linarith
    have hcoeff_le : (1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ)) ≤
        1 / Real.log (z : ℝ) := by
      have h1 : 1 - Real.exp (-(u (j + 1))) ≤ u (j + 1) := by
        have := Real.add_one_le_exp (-(u (j + 1)))
        linarith
      rw [div_le_div_iff₀ (mul_pos huj1_pos hlogz) hlogz]
      have h2 := mul_le_mul_of_nonneg_right h1 hlogz.le
      linarith
    have hN2 : 2 / (N j : ℝ) ≤ 1 := by
      have hNj8 : (8 : ℝ) ≤ (N j : ℝ) := by exact_mod_cast (hX8.trans hNjX)
      rw [div_le_one (by linarith)]; linarith
    have hmain_eq :
        ((1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ))) *
          ((1 - δ) * ((1 / (K : ℝ)) * Real.log (z : ℝ))) =
          (1 - δ) * (1 / (K : ℝ)) * ((1 - Real.exp (-(u (j + 1)))) / u (j + 1)) := by
      field_simp
    have hlog1 : 1 ≤ Real.log (z : ℝ) := by linarith
    have hrem1 :
        ((1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ))) *
          ((1 - δ) * (2 / ((z : ℝ) ^ (1 / (K : ℝ))))) ≤ 2 / ((z : ℝ) ^ (1 / (K : ℝ))) := by
      have h1 : (1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ)) ≤ 1 := by
        exact hcoeff_le.trans ((div_le_one hlogz).mpr hlog1)
      have h2 : (1 - δ) * (2 / ((z : ℝ) ^ (1 / (K : ℝ)))) ≤ 2 / ((z : ℝ) ^ (1 / (K : ℝ))) := by
        have hnn : 0 ≤ 2 / ((z : ℝ) ^ (1 / (K : ℝ))) := by positivity
        have h1d : 1 - δ ≤ 1 := by linarith
        calc (1 - δ) * (2 / ((z : ℝ) ^ (1 / (K : ℝ)))) ≤ 1 * (2 / ((z : ℝ) ^ (1 / (K : ℝ)))) :=
              mul_le_mul_of_nonneg_right h1d hnn
          _ = 2 / ((z : ℝ) ^ (1 / (K : ℝ))) := one_mul _
      calc _ ≤ 1 * (2 / ((z : ℝ) ^ (1 / (K : ℝ)))) :=
            mul_le_mul h1 h2 (by positivity) zero_le_one
        _ = 2 / ((z : ℝ) ^ (1 / (K : ℝ))) := one_mul _
    have hrem2 :
        ((1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ))) * (4 * δ + 2 / (N j : ℝ)) ≤
          (4 * δ + 2) / Real.log (z : ℝ) := by
      calc _ ≤ (1 / Real.log (z : ℝ)) * (4 * δ + 1) :=
            mul_le_mul hcoeff_le (by linarith) (by positivity) (by positivity)
        _ ≤ (4 * δ + 2) / Real.log (z : ℝ) := by
            rw [one_div_mul_eq_div]
            exact div_le_div_of_nonneg_right (by linarith) hlogz.le
    have hcomb1 :
        (1 - δ) * ((1 / (K : ℝ)) * Real.log (z : ℝ) - 2 / ((z : ℝ) ^ (1 / (K : ℝ)))) -
          (4 * δ + 2 / (N j : ℝ)) ≤
        ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
      have := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ 1 - δ by norm_num [δ])
      linarith
    have hcomb2 := (mul_le_mul_of_nonneg_left hcomb1 hcoeff_pos).trans hsum1
    have hexpand :
        ((1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ))) *
          ((1 - δ) * ((1 / (K : ℝ)) * Real.log (z : ℝ) - 2 / ((z : ℝ) ^ (1 / (K : ℝ)))) -
            (4 * δ + 2 / (N j : ℝ))) =
        ((1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ))) *
          ((1 - δ) * ((1 / (K : ℝ)) * Real.log (z : ℝ))) -
        ((1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ))) *
          ((1 - δ) * (2 / ((z : ℝ) ^ (1 / (K : ℝ))))) -
        ((1 - Real.exp (-(u (j + 1)))) / (u (j + 1) * Real.log (z : ℝ))) *
          (4 * δ + 2 / (N j : ℝ)) := by ring
    rw [hexpand, hmain_eq] at hcomb2
    linarith
  have hsum_all := Finset.sum_le_sum hblock
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at hsum_all
  have hfac :
      ∑ j ∈ Finset.Ico 1 K,
        (1 - δ) * (1 / (K : ℝ)) * ((1 - Real.exp (-(u (j + 1)))) / u (j + 1)) =
        (1 - δ) * ∑ j ∈ Finset.Ico 1 K,
          (1 / (K : ℝ)) * ((1 - Real.exp (-(((j + 1 : ℕ) : ℝ) / (K : ℝ)))) /
            (((j + 1 : ℕ) : ℝ) / (K : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; dsimp [u]; ring
  rw [hfac] at hsum_all
  have hriem := riemann_poly_S1_lower K hK4
  have hriem_mul := mul_le_mul_of_nonneg_left hriem (show (0 : ℝ) ≤ 1 - δ by norm_num [δ])
  have hK_real : (K : ℝ) = 100000 := by exact_mod_cast hKeq
  have herr1 : ((K - 1 : ℕ) : ℝ) * ((4 * δ + 2) / Real.log (z : ℝ)) ≤ 1 / 1000000 := by
    have hK_le : ((K - 1 : ℕ) : ℝ) ≤ 100000 := by
      have : K - 1 ≤ 100000 := by omega
      exact_mod_cast this
    have hnum : (4 * δ + 2) ≤ 3 := by norm_num [δ]
    have hdiv : (4 * δ + 2) / Real.log (z : ℝ) ≤ 3 / (10 ^ 12 : ℝ) :=
      div_le_div₀ (by norm_num) hnum (by norm_num) hlog_big
    calc ((K - 1 : ℕ) : ℝ) * ((4 * δ + 2) / Real.log (z : ℝ))
        ≤ 100000 * (3 / (10 ^ 12 : ℝ)) :=
          mul_le_mul hK_le hdiv (by positivity) (by norm_num)
      _ ≤ 1 / 1000000 := by norm_num
  have herr2 : ((K - 1 : ℕ) : ℝ) * (2 / ((z : ℝ) ^ (1 / (K : ℝ)))) ≤ 1 / 1000000 := by
    have hK_le : ((K - 1 : ℕ) : ℝ) ≤ 100000 := by
      have : K - 1 ≤ 100000 := by omega
      exact_mod_cast this
    calc ((K - 1 : ℕ) : ℝ) * (2 / ((z : ℝ) ^ (1 / (K : ℝ))))
        ≤ 100000 * (2 / (10 ^ 12 : ℝ)) := by
          apply mul_le_mul hK_le _ (by positivity) (by norm_num)
          exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hzpow_big
      _ ≤ 1 / 1000000 := by norm_num
  have hnum_final : (79650 / 100000 : ℝ) ≤
      (1 - δ) * ((79654 / 100000 : ℝ) - 3 / (K : ℝ)) - 1 / 1000000 - 1 / 1000000 := by
    rw [hK_real]; norm_num [δ]
  dsimp only
  linarith [hdrop, hsplit, hsum_all, hriem_mul, herr1, herr2, hnum_final]

private lemma S2_total_upper :
    ∃ Z₀ : ℕ, 16 ≤ Z₀ ∧ ∀ z : ℕ, Z₀ ≤ z →
      let σ := (Real.log (z : ℝ))⁻¹
      ∑ p ∈ (Finset.Ioc z (z ^ 10)).filter Nat.Prime, (p : ℝ) ^ (-(1 + σ)) ≤
        (22093 / 100000 : ℝ) := by
  let ε : ℝ := 1 / 2000000
  have hε : 0 < ε := by norm_num [ε]
  obtain ⟨Z1, _, h1⟩ := S2_interval_upper (a := 1) (b := 5 / 4) (by norm_num) (by norm_num) hε
  obtain ⟨Z2, _, h2⟩ := S2_interval_upper (a := 5 / 4) (b := 3 / 2) (by norm_num) (by norm_num) hε
  obtain ⟨Z3, _, h3⟩ := S2_interval_upper (a := 3 / 2) (b := 7 / 4) (by norm_num) (by norm_num) hε
  obtain ⟨Z4, _, h4⟩ := S2_interval_upper (a := 7 / 4) (b := 2) (by norm_num) (by norm_num) hε
  obtain ⟨Z5, _, h5⟩ := S2_interval_upper (a := 2) (b := 5 / 2) (by norm_num) (by norm_num) hε
  obtain ⟨Z6, _, h6⟩ := S2_interval_upper (a := 5 / 2) (b := 3) (by norm_num) (by norm_num) hε
  obtain ⟨Z7, _, h7⟩ := S2_interval_upper (a := 3) (b := 4) (by norm_num) (by norm_num) hε
  obtain ⟨Z8, _, h8⟩ := S2_interval_upper (a := 4) (b := 6) (by norm_num) (by norm_num) hε
  obtain ⟨Z9, _, h9⟩ := S2_interval_upper (a := 6) (b := 10) (by norm_num) (by norm_num) hε
  let Z₀ := max (max (max Z1 Z2) (max Z3 Z4)) (max (max (max Z5 Z6) (max Z7 Z8)) (max Z9 16))
  refine ⟨Z₀, by omega, fun z hz => ?_⟩
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show 1 ≤ z by omega)
  let σ : ℝ := (Real.log (z : ℝ))⁻¹
  let f : ℕ → ℝ := fun p => if Nat.Prime p then (p : ℝ) ^ (-(1 + σ)) else 0
  have hf_sum : ∀ A B : ℕ,
      ∑ p ∈ (Finset.Ioc A B).filter Nat.Prime, (p : ℝ) ^ (-(1 + σ)) =
        ∑ p ∈ Finset.Ioc A B, f p := fun A B => Finset.sum_filter _ _
  have hfl (a b : ℝ) (hab : a ≤ b) : ⌊(z : ℝ) ^ a⌋₊ ≤ ⌊(z : ℝ) ^ b⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hz1 hab)
  have hfl1 : ⌊(z : ℝ) ^ (1 : ℝ)⌋₊ = z := by rw [Real.rpow_one, Nat.floor_natCast]
  have hfl10 : ⌊(z : ℝ) ^ (10 : ℝ)⌋₊ = z ^ 10 := by
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← Nat.cast_pow, Nat.floor_natCast]
  have hsplit :
      ∑ p ∈ Finset.Ioc z (z ^ 10), f p =
        ∑ p ∈ Finset.Ioc ⌊(z : ℝ) ^ (1 : ℝ)⌋₊ ⌊(z : ℝ) ^ (5 / 4 : ℝ)⌋₊, f p +
        ∑ p ∈ Finset.Ioc ⌊(z : ℝ) ^ (5 / 4 : ℝ)⌋₊ ⌊(z : ℝ) ^ (3 / 2 : ℝ)⌋₊, f p +
        ∑ p ∈ Finset.Ioc ⌊(z : ℝ) ^ (3 / 2 : ℝ)⌋₊ ⌊(z : ℝ) ^ (7 / 4 : ℝ)⌋₊, f p +
        ∑ p ∈ Finset.Ioc ⌊(z : ℝ) ^ (7 / 4 : ℝ)⌋₊ ⌊(z : ℝ) ^ (2 : ℝ)⌋₊, f p +
        ∑ p ∈ Finset.Ioc ⌊(z : ℝ) ^ (2 : ℝ)⌋₊ ⌊(z : ℝ) ^ (5 / 2 : ℝ)⌋₊, f p +
        ∑ p ∈ Finset.Ioc ⌊(z : ℝ) ^ (5 / 2 : ℝ)⌋₊ ⌊(z : ℝ) ^ (3 : ℝ)⌋₊, f p +
        ∑ p ∈ Finset.Ioc ⌊(z : ℝ) ^ (3 : ℝ)⌋₊ ⌊(z : ℝ) ^ (4 : ℝ)⌋₊, f p +
        ∑ p ∈ Finset.Ioc ⌊(z : ℝ) ^ (4 : ℝ)⌋₊ ⌊(z : ℝ) ^ (6 : ℝ)⌋₊, f p +
        ∑ p ∈ Finset.Ioc ⌊(z : ℝ) ^ (6 : ℝ)⌋₊ ⌊(z : ℝ) ^ (10 : ℝ)⌋₊, f p := by
    rw [Finset.sum_Ioc_consecutive f (hfl 1 (5 / 4) (by norm_num)) (hfl (5 / 4) (3 / 2) (by norm_num)),
      Finset.sum_Ioc_consecutive f (hfl 1 (3 / 2) (by norm_num)) (hfl (3 / 2) (7 / 4) (by norm_num)),
      Finset.sum_Ioc_consecutive f (hfl 1 (7 / 4) (by norm_num)) (hfl (7 / 4) 2 (by norm_num)),
      Finset.sum_Ioc_consecutive f (hfl 1 2 (by norm_num)) (hfl 2 (5 / 2) (by norm_num)),
      Finset.sum_Ioc_consecutive f (hfl 1 (5 / 2) (by norm_num)) (hfl (5 / 2) 3 (by norm_num)),
      Finset.sum_Ioc_consecutive f (hfl 1 3 (by norm_num)) (hfl 3 4 (by norm_num)),
      Finset.sum_Ioc_consecutive f (hfl 1 4 (by norm_num)) (hfl 4 6 (by norm_num)),
      Finset.sum_Ioc_consecutive f (hfl 1 6 (by norm_num)) (hfl 6 10 (by norm_num)),
      hfl1, hfl10]
  dsimp only
  rw [hf_sum, hsplit]
  simp only [← hf_sum]
  have hb1 := h1 z (by omega)
  have hb2 := h2 z (by omega)
  have hb3 := h3 z (by omega)
  have hb4 := h4 z (by omega)
  have hb5 := h5 z (by omega)
  have hb6 := h6 z (by omega)
  have hb7 := h7 z (by omega)
  have hb8 := h8 z (by omega)
  have hb9 := h9 z (by omega)
  have h9sum := sec_nine_sum_le
  dsimp only at h9sum hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  linarith [hb1, hb2, hb3, hb4, hb5, hb6, hb7, hb8, hb9, h9sum]

private lemma mertens_prod_upper :
    ∃ Z₀ : ℕ, 16 ≤ Z₀ ∧ ∀ z : ℕ, Z₀ ≤ z →
      (∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ))) ≤
        Real.exp (-(5755 / 10000 : ℝ)) / Real.log (z : ℝ) := by
  obtain ⟨Z1, hZ1, hS1⟩ := S1_lower_bound
  obtain ⟨Z2, hZ2, hS2⟩ := S2_total_upper
  refine ⟨max (max Z1 Z2) 1000000, by omega, fun z hz => ?_⟩
  have hz1 : (1 : ℝ) < (z : ℝ) := by exact_mod_cast (show 1 < z by omega)
  have hlogz : 0 < Real.log (z : ℝ) := Real.log_pos hz1
  set σ : ℝ := (Real.log (z : ℝ))⁻¹
  have hσ : 0 < σ := inv_pos.mpr hlogz
  set M : ℕ := z ^ 10
  have hM1 : 1 ≤ M := Nat.one_le_pow 10 z (by omega)
  have h1 := (sum_rpow_ge hM1 hσ).trans (finite_euler_product_le M hσ)
  have hM_rpow : ((M + 1 : ℕ) : ℝ) ^ (-σ) ≤ Real.exp (-(10 : ℝ)) := by
    have hle : (z : ℝ) ^ (10 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact_mod_cast (show z ^ 10 ≤ M + 1 by omega)
    have hr := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos (by linarith) _) hle (neg_nonpos.mpr hσ.le)
    calc ((M + 1 : ℕ) : ℝ) ^ (-σ)
        ≤ ((z : ℝ) ^ (10 : ℝ)) ^ (-σ) := hr
      _ = Real.exp (-(10 : ℝ)) := by
          rw [← Real.rpow_mul (by linarith), Real.rpow_def_of_pos (by linarith)]
          congr 1; dsimp [σ]; field_simp
  have h_lhs_ge : (1 - (1 / 20000 : ℝ)) * Real.log (z : ℝ) ≤
      ∏ p ∈ Nat.primesLE M, (1 - (p : ℝ) ^ (-(1 + σ)))⁻¹ := by
    have h2 : (1 - (1 / 20000 : ℝ)) / σ ≤ (1 - ((M + 1 : ℕ) : ℝ) ^ (-σ)) / σ :=
      div_le_div_of_nonneg_right (by linarith [hM_rpow, exp_neg_ten_le]) hσ.le
    rw [div_eq_mul_inv, inv_inv] at h2
    exact h2.trans h1
  have hlog_le := Real.log_le_log (by positivity) h_lhs_ge
  rw [Real.log_mul (by norm_num) hlogz.ne'] at hlog_le
  have hprod_pos : ∀ p ∈ Nat.primesLE M, (1 - (p : ℝ) ^ (-(1 + σ)))⁻¹ ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    apply inv_ne_zero
    have : (p : ℝ) ^ (-(1 + σ)) < 1 := by
      rw [Real.rpow_neg (by linarith)]
      exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by linarith) (by linarith))
    linarith
  rw [Real.log_prod hprod_pos] at hlog_le
  have hzM : Nat.primesLE z ⊆ Nat.primesLE M :=
    Nat.primesLE_mono (by
      have : z ^ 1 ≤ z ^ 10 := Nat.pow_le_pow_right (by omega) (by decide)
      simpa using this)
  have hsplit_primes :
      ∑ p ∈ Nat.primesLE M, Real.log ((1 - (p : ℝ) ^ (-(1 + σ)))⁻¹) =
        ∑ p ∈ Nat.primesLE z, Real.log ((1 - (p : ℝ) ^ (-(1 + σ)))⁻¹) +
        ∑ p ∈ (Finset.Ioc z M).filter Nat.Prime, Real.log ((1 - (p : ℝ) ^ (-(1 + σ)))⁻¹) := by
    have hsdiff : Nat.primesLE M \ Nat.primesLE z = (Finset.Ioc z M).filter Nat.Prime := by
      ext p
      simp only [Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨hpM, hp⟩, hnot⟩
        exact ⟨⟨by by_contra hle; push_neg at hle; exact hnot ⟨hle, hp⟩, hpM⟩, hp⟩
      · rintro ⟨⟨hgt, hpM⟩, hp⟩
        exact ⟨⟨hpM, hp⟩, fun h => by omega⟩
    have hs := Finset.sum_sdiff (f := fun p : ℕ => Real.log ((1 - (p : ℝ) ^ (-(1 + σ)))⁻¹)) hzM
    rw [hsdiff] at hs
    linarith
  rw [hsplit_primes] at hlog_le
  have h_prod_z_pos : ∀ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ)) ≠ 0 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  have hdiff_S1 :
      ∑ p ∈ Nat.primesLE z, (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) ≤
        ∑ p ∈ Nat.primesLE z, (-Real.log (1 - 1 / (p : ℝ))) -
          ∑ p ∈ Nat.primesLE z, Real.log ((1 - (p : ℝ) ^ (-(1 + σ)))⁻¹) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have hp0 : (0 : ℝ) < p := by linarith
    have ha : 0 < (p : ℝ) ^ (-(1 + σ)) := Real.rpow_pos_of_pos hp0 _
    have hab : (p : ℝ) ^ (-(1 + σ)) ≤ 1 / (p : ℝ) := by
      rw [show -(1 + σ) = (-1 : ℝ) + (-σ) by ring, Real.rpow_add hp0, Real.rpow_neg_one, one_div]
      have : (p : ℝ) ^ (-σ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (neg_nonpos.mpr hσ.le)
      nlinarith [inv_pos.mpr hp0]
    have hb : 1 / (p : ℝ) < 1 := (div_lt_one hp0).mpr (by linarith)
    have hlog := log_one_sub_ratio_ge ha hab hb
    rw [Real.log_inv]
    rw [Real.log_div (by linarith) (by linarith)] at hlog
    have hpow : 1 / (p : ℝ) - (p : ℝ) ^ (-(1 + σ)) = (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) := by
      rw [show -(1 + σ) = (-1 : ℝ) + (-σ) by ring, Real.rpow_add hp0, Real.rpow_neg_one]; ring
    linarith
  have hS2_bound :
      ∑ p ∈ (Finset.Ioc z M).filter Nat.Prime, Real.log ((1 - (p : ℝ) ^ (-(1 + σ)))⁻¹) ≤
        (1 + 2 / (z : ℝ)) *
          ∑ p ∈ (Finset.Ioc z M).filter Nat.Prime, (p : ℝ) ^ (-(1 + σ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hp_gt : (z : ℝ) < p := by exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hp0 : (0 : ℝ) < p := by linarith
    have ht_le : (p : ℝ) ^ (-(1 + σ)) ≤ 1 / (z : ℝ) := by
      have h1 : (p : ℝ) ^ (-(1 + σ)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [Real.rpow_neg_one, ← one_div] at h1
      exact h1.trans (one_div_le_one_div_of_le (by linarith) hp_gt.le)
    have hz_ge : (2 : ℝ) ≤ z := by exact_mod_cast (show 2 ≤ z by omega)
    have ht1 : (p : ℝ) ^ (-(1 + σ)) < 1 := lt_of_le_of_lt ht_le ((div_lt_one (by linarith)).mpr (by linarith))
    rw [Real.log_inv]
    have h1 := neg_log_one_sub_le (Real.rpow_nonneg hp0.le _) ht1
    have h2 : (1 - (p : ℝ) ^ (-(1 + σ)))⁻¹ ≤ 1 + 2 / (z : ℝ) := by
      have hpos : 0 < 1 - (p : ℝ) ^ (-(1 + σ)) := sub_pos.mpr ht1
      rw [inv_le_iff_one_le_mul₀' hpos]
      have h3 : 1 ≤ (1 - 1 / (z : ℝ)) * (1 + 2 / (z : ℝ)) := by
        have h2z : 2 / (z : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hz_ge
        have h1z : 0 ≤ 1 / (z : ℝ) := by positivity
        have hprod : 0 ≤ (1 / (z : ℝ)) * (1 - 2 / (z : ℝ)) := mul_nonneg h1z (by linarith)
        have hid : (1 - 1 / (z : ℝ)) * (1 + 2 / (z : ℝ)) - 1 = (1 / (z : ℝ)) * (1 - 2 / (z : ℝ)) := by ring
        linarith
      have h4 : (1 - 1 / (z : ℝ)) * (1 + 2 / (z : ℝ)) ≤
          (1 - (p : ℝ) ^ (-(1 + σ))) * (1 + 2 / (z : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      exact h3.trans h4
    calc -Real.log (1 - (p : ℝ) ^ (-(1 + σ)))
        ≤ (p : ℝ) ^ (-(1 + σ)) / (1 - (p : ℝ) ^ (-(1 + σ))) := h1
      _ = (1 - (p : ℝ) ^ (-(1 + σ)))⁻¹ * (p : ℝ) ^ (-(1 + σ)) := by ring
      _ ≤ (1 + 2 / (z : ℝ)) * (p : ℝ) ^ (-(1 + σ)) :=
          mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hp0.le _)
  have hS1_val := hS1 z (by omega)
  have hS2_val := hS2 z (by omega)
  dsimp only at hS1_val hS2_val
  change (79650 / 100000 : ℝ) ≤ ∑ p ∈ Nat.primesLE z, (1 - (p : ℝ) ^ (-σ)) / (p : ℝ) at hS1_val
  change ∑ p ∈ (Finset.Ioc z M).filter Nat.Prime, (p : ℝ) ^ (-(1 + σ)) ≤ (22093 / 100000 : ℝ) at hS2_val
  have hlog_tiny : -(6 / 100000 : ℝ) ≤ Real.log (1 - 1 / 20000 : ℝ) := by
    have h := neg_log_one_sub_le (by norm_num : (0 : ℝ) ≤ 1 / 20000) (by norm_num)
    linarith
  have hS2_num : (1 + 2 / (z : ℝ)) * (22093 / 100000 : ℝ) ≤ (22094 / 100000 : ℝ) := by
    have hz_big : (1000000 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show 1000000 ≤ z by omega)
    have h2z : 2 / (z : ℝ) ≤ 2 / 1000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hz_big
    linarith
  have hsum_neglog :
      Real.log (Real.log (z : ℝ)) + (5755 / 10000 : ℝ) ≤
        ∑ p ∈ Nat.primesLE z, (-Real.log (1 - 1 / (p : ℝ))) := by
    have hS2_comb := hS2_bound.trans ((mul_le_mul_of_nonneg_left hS2_val (by positivity)).trans hS2_num)
    linarith [hlog_le, hdiff_S1, hS1_val, hlog_tiny, hS2_comb]
  have hlog_prod :
      Real.log (∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ))) ≤
        -(5755 / 10000 : ℝ) - Real.log (Real.log (z : ℝ)) := by
    rw [Real.log_prod h_prod_z_pos]
    rw [Finset.sum_neg_distrib] at hsum_neglog
    linarith
  have hexp := Real.exp_le_exp.mpr hlog_prod
  have hprod_z_gt : 0 < ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
    have : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
    linarith
  rw [Real.exp_log hprod_z_gt, Real.exp_sub, Real.exp_log hlogz] at hexp
  exact hexp

/-! ### Section 4: Average upper bound on the sieve volume V(n, sqrt n) -/

private lemma period_avg_odd_primes (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ 3 ≤ p) :
    ∑ m ∈ Finset.range (∏ p ∈ S, p),
        (∏ p ∈ S.filter (fun p => p ∣ m), ((p - 1 : ℝ) / (p - 2 : ℝ))) =
      ((∏ p ∈ S, p : ℕ) : ℝ) *
        ∏ p ∈ S, ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ))) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hpS ih =>
    have hp_pr : Nat.Prime p := (hS p (Finset.mem_insert_self p S)).1
    have hp3 : 3 ≤ p := (hS p (Finset.mem_insert_self p S)).2
    have hS' : ∀ q ∈ S, Nat.Prime q ∧ 3 ≤ q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    set M : ℕ := ∏ q ∈ S, q
    have hMpos : 0 < M := Finset.prod_pos (fun q hq => (hS' q hq).1.pos)
    have hcop : Nat.Coprime M p := by
      refine Nat.Coprime.prod_left fun q hq => ?_
      have hq_pr := (hS' q hq).1
      exact (Nat.coprime_primes hq_pr hp_pr).mpr (fun heq => hpS (heq ▸ hq))
    rw [Finset.prod_insert hpS, Finset.prod_insert hpS, Nat.cast_mul]
    rw [show p * M = M * p by ring]
    have hbij :
        ∑ m ∈ Finset.range (M * p),
            (∏ q ∈ (insert p S).filter (fun q => q ∣ m), ((q - 1 : ℝ) / (q - 2 : ℝ))) =
          ∑ r ∈ Finset.range M, ∑ t ∈ Finset.range p,
            (∏ q ∈ (insert p S).filter (fun q => q ∣ (t * M + r)), ((q - 1 : ℝ) / (q - 2 : ℝ))) := by
      rw [← Finset.sum_product']
      refine Finset.sum_bij (fun m _ => (m % M, m / M)) ?_ ?_ ?_ ?_
      · intro m hm
        rw [Finset.mem_range] at hm
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
        exact ⟨Nat.mod_lt m hMpos, Nat.div_lt_of_lt_mul (by linarith)⟩
      · intro m1 _ m2 _ h
        have h1 : m1 % M = m2 % M := congrArg Prod.fst h
        have h2 : m1 / M = m2 / M := congrArg Prod.snd h
        rw [← Nat.div_add_mod m1 M, ← Nat.div_add_mod m2 M, h1, h2]
      · intro x hx
        rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hx
        refine ⟨x.2 * M + x.1, Finset.mem_range.mpr ?_, ?_⟩
        · nlinarith
        · apply Prod.ext
          · dsimp only; rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hx.1]
          · dsimp only
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ hMpos, Nat.div_eq_of_lt hx.1, zero_add]
      · intro m _
        dsimp only
        have hm : m / M * M + m % M = m := by
          have := Nat.div_add_mod m M; linarith
        rw [hm]
    rw [hbij]
    have hinner : ∀ r ∈ Finset.range M,
        ∑ t ∈ Finset.range p,
            (∏ q ∈ (insert p S).filter (fun q => q ∣ (t * M + r)), ((q - 1 : ℝ) / (q - 2 : ℝ))) =
          ((p : ℝ) * ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ)))) *
            (∏ q ∈ S.filter (fun q => q ∣ r), ((q - 1 : ℝ) / (q - 2 : ℝ))) := by
      intro r hr
      have hfactor : ∀ t : ℕ,
          (∏ q ∈ (insert p S).filter (fun q => q ∣ (t * M + r)), ((q - 1 : ℝ) / (q - 2 : ℝ))) =
            (if p ∣ (t * M + r) then ((p - 1 : ℝ) / (p - 2 : ℝ)) else 1) *
              (∏ q ∈ S.filter (fun q => q ∣ r), ((q - 1 : ℝ) / (q - 2 : ℝ))) := by
        intro t
        have hS_eq : S.filter (fun q => q ∣ (t * M + r)) = S.filter (fun q => q ∣ r) := by
          ext q
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hqS, hd⟩
            refine ⟨hqS, ?_⟩
            have hqM : q ∣ M := Finset.dvd_prod_of_mem _ hqS
            have hqtM : q ∣ t * M := dvd_mul_of_dvd_right hqM t
            exact (Nat.dvd_add_right hqtM).mp hd
          · rintro ⟨hqS, hd⟩
            refine ⟨hqS, dvd_add (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hqS) t) hd⟩
        rw [Finset.filter_insert]
        split_ifs with hdp
        · rw [Finset.prod_insert (by simp [hpS]), hS_eq]
        · rw [one_mul, hS_eq]
      simp_rw [hfactor]
      rw [← Finset.sum_mul]
      congr 1
      -- Exactly one t in range p satisfies p | t * M + r
      have hexists_uniq : ∃! t, t ∈ Finset.range p ∧ p ∣ (t * M + r) := by
        have hp_ne : p ≠ 0 := hp_pr.ne_zero
        have hmod_inj : Set.InjOn (fun t : ℕ => (t * M + r) % p) (Finset.range p : Set ℕ) := by
          intro t1 ht1 t2 ht2 heq
          have h1 : t1 < p := Finset.mem_range.mp ht1
          have h2 : t2 < p := Finset.mem_range.mp ht2
          have hcong : t1 * M ≡ t2 * M [MOD p] := by
            have hadd : t1 * M + r ≡ t2 * M + r [MOD p] := heq
            exact Nat.ModEq.add_right_cancel' r hadd
          have hcong2 : t1 ≡ t2 [MOD p] := Nat.ModEq.cancel_right_of_coprime hcop.symm hcong
          rw [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hcong2
          exact hcong2
        have hcard : ((Finset.range p).image (fun t => (t * M + r) % p)).card = p := by
          rw [Finset.card_image_of_injOn hmod_inj, Finset.card_range]
        have hsub : (Finset.range p).image (fun t => (t * M + r) % p) ⊆ Finset.range p := by
          intro x hx
          rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
          exact Finset.mem_range.mpr (Nat.mod_lt _ hp_pr.pos)
        have heq_set : (Finset.range p).image (fun t => (t * M + r) % p) = Finset.range p :=
          Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
        have h0mem : 0 ∈ (Finset.range p).image (fun t => (t * M + r) % p) := by
          rw [heq_set]; exact Finset.mem_range.mpr hp_pr.pos
        rcases Finset.mem_image.mp h0mem with ⟨t0, ht0, h0eq⟩
        refine ⟨t0, ⟨ht0, Nat.dvd_of_mod_eq_zero h0eq⟩, fun t ht => ?_⟩
        exact hmod_inj ht.1 ht0 (by dsimp only; rw [Nat.mod_eq_zero_of_dvd ht.2, h0eq])
      obtain ⟨t0, ⟨ht0, hdiv0⟩, huniq⟩ := hexists_uniq
      rw [← Finset.add_sum_erase _ _ ht0]
      rw [if_pos hdiv0]
      have hrest : ∑ t ∈ (Finset.range p).erase t0,
          (if p ∣ (t * M + r) then ((p - 1 : ℝ) / (p - 2 : ℝ)) else 1) = (p - 1 : ℝ) := by
        have hcongr : ∑ t ∈ (Finset.range p).erase t0,
            (if p ∣ (t * M + r) then ((p - 1 : ℝ) / (p - 2 : ℝ)) else 1) =
              ∑ _t ∈ (Finset.range p).erase t0, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro t ht
          have hne : t ≠ t0 := (Finset.mem_erase.mp ht).1
          have hmem : t ∈ Finset.range p := (Finset.mem_erase.mp ht).2
          rw [if_neg (fun hd => hne (huniq t ⟨hmem, hd⟩))]
        rw [hcongr, Finset.sum_const, Finset.card_erase_of_mem ht0, Finset.card_range, nsmul_eq_mul, mul_one]
        rw [Nat.cast_sub (by omega), Nat.cast_one]
      rw [hrest]
      have hp_ne : (p : ℝ) ≠ 0 := by exact_mod_cast hp_pr.ne_zero
      have hp2_ne : (p : ℝ) - 2 ≠ 0 := by
        have : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        linarith
      field_simp
      ring
    rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, ih hS']
    ring

private lemma card_primes_gt_dvd_le {n y : ℕ} (hn : 1 ≤ n) (hy : 2 ≤ y) :
    ((n.primeFactors.filter (fun p => y < p)).card) ≤ Nat.log y n := by
  have hy1 : 1 < y := by omega
  apply Nat.le_log_of_pow_le hy1
  have hprod_le : ∏ p ∈ n.primeFactors.filter (fun p => y < p), y ≤
      ∏ p ∈ n.primeFactors.filter (fun p => y < p), p := by
    apply Finset.prod_le_prod'
    intro p hp
    exact (Finset.mem_filter.mp hp).2.le
  rw [Finset.prod_const] at hprod_le
  have hprod_dvd : (∏ p ∈ n.primeFactors.filter (fun p => y < p), p) ∣ n := by
    have hsub : n.primeFactors.filter (fun p => y < p) ⊆ n.primeFactors := Finset.filter_subset _ _
    have h1 : (∏ p ∈ n.primeFactors.filter (fun p => y < p), p) ∣ ∏ p ∈ n.primeFactors, p :=
      Finset.prod_dvd_prod_of_subset _ _ _ hsub
    exact h1.trans (Nat.prod_primeFactors_dvd n)
  exact hprod_le.trans (Nat.le_of_dvd (by omega) hprod_dvd)

set_option maxHeartbeats 600000 in
private lemma V_avg_upper :
    ∃ X₀ : ℕ, 100000 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X →
      let D := X / 10000
      let E := (Finset.Icc X (X + D)).filter Even
      let I := fun n : ℕ => Finset.Icc ((n + 2) / 3) ((2 * n) / 3)
      let P := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime
      let V := fun n : ℕ => ((I n).card : ℝ) * (n.totient : ℝ) / (n : ℝ) *
          ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))
      ∑ n ∈ E, V n ≤
        (1 + 1 / 5000 : ℝ) * (4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) *
          Real.exp (-2 * (5755 / 10000 : ℝ)) * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
  obtain ⟨Z₀, hZ16, hmert⟩ := mertens_prod_upper
  have h_ev : ∀ᶠ X : ℕ in atTop,
      10 ^ 20 ≤ X ∧
      Z₀ ≤ X.sqrt ∧
      100000 ≤ Nat.log 4 X / 3 ∧
      (1 + 1 / ((Nat.log 4 X / 3 : ℕ) - 2 : ℝ)) ^ (Nat.log (Nat.log 4 X / 3) (2 * X)) ≤
        (1 + 1 / 50000 : ℝ) ∧
      (Real.log (X : ℝ)) / 2 - 1 ≤ Real.log ((X.sqrt : ℕ) : ℝ) ∧
      (1 : ℝ) / (Real.log ((X.sqrt : ℕ) : ℝ)) ^ 2 ≤
        (1 + 1 / 50000 : ℝ) * (4 / (Real.log (X : ℝ)) ^ 2) ∧
      (4 : ℝ) ^ (Nat.log 4 X / 3) * (2 : ℝ) ^ (Nat.log 4 X / 3) * (Real.log (X : ℝ)) ^ 2 ≤
        (1 / 10 ^ 10 : ℝ) * (X : ℝ) ∧
      (10 ^ 8 : ℝ) ≤ (X : ℝ) := by
    have h1 : ∀ᶠ X : ℕ in atTop, 10 ^ 20 ≤ X := eventually_ge_atTop _
    have h2 : ∀ᶠ X : ℕ in atTop, Z₀ ≤ X.sqrt := by
      filter_upwards [eventually_ge_atTop (Z₀ ^ 2)] with X hX
      exact Nat.le_sqrt.mpr (by simpa [sq] using hX)
    have h3 : ∀ᶠ X : ℕ in atTop, 100000 ≤ Nat.log 4 X / 3 := by
      filter_upwards [eventually_ge_atTop (4 ^ 300000)] with X hX
      have := Nat.le_log_of_pow_le (by decide : 1 < 4) hX
      omega
    have h4 : ∀ᶠ X : ℕ in atTop,
        (1 + 1 / ((Nat.log 4 X / 3 : ℕ) - 2 : ℝ)) ^ (Nat.log (Nat.log 4 X / 3) (2 * X)) ≤
          (1 + 1 / 50000 : ℝ) := by
      -- Since y = log_4 X / 3 >= log X / 5 - 1 and k = log_y (2X) <= log(2X) / log y,
      -- k / (y - 2) <= 10 / log y -> 0, so (1 + 1/(y-2))^k <= exp(k / (y-2)) <= 1 + 1/50000.
      have hlog_tend : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      have hy_tend : Tendsto (fun X : ℕ => ((Nat.log 4 X / 3 : ℕ) : ℝ)) atTop atTop := by
        rw [tendsto_atTop_atTop]
        intro b
        obtain ⟨M, hM⟩ := exists_nat_ge b
        refine ⟨4 ^ (3 * M), fun X hX => ?_⟩
        have h1 := Nat.le_log_of_pow_le (by decide : 1 < 4) hX
        exact hM.trans (by exact_mod_cast (show M ≤ Nat.log 4 X / 3 by omega))
      have hlogy_tend : Tendsto (fun X : ℕ => Real.log ((Nat.log 4 X / 3 : ℕ) : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp hy_tend
      filter_upwards [eventually_ge_atTop (4 ^ 300000),
        hlogy_tend.eventually (eventually_ge_atTop (2000000 : ℝ))] with X hX hlogy
      set y : ℕ := Nat.log 4 X / 3
      have hy100 : 100000 ≤ y := by
        have := Nat.le_log_of_pow_le (by decide : 1 < 4) hX; omega
      have hX_lt : X < 4 ^ (Nat.log 4 X + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 4) X
      have hX_le : (2 * X : ℝ) ≤ (4 : ℝ) ^ (3 * y + 4) := by
        have h1 : 2 * X ≤ 4 ^ (3 * y + 4) := by
          have h2 : Nat.log 4 X + 1 ≤ 3 * y + 3 := by dsimp [y]; omega
          have h3 : X ≤ 4 ^ (3 * y + 3) := hX_lt.le.trans (Nat.pow_le_pow_right (by decide) h2)
          calc 2 * X ≤ 4 * X := by omega
            _ ≤ 4 * 4 ^ (3 * y + 3) := Nat.mul_le_mul_left 4 h3
            _ = 4 ^ (3 * y + 4) := by ring
        exact_mod_cast h1
      have hk_le : ((Nat.log y (2 * X) : ℕ) : ℝ) * Real.log (y : ℝ) ≤
          ((3 * y + 4 : ℕ) : ℝ) * Real.log 4 := by
        have hpow : y ^ Nat.log y (2 * X) ≤ 2 * X :=
          Nat.pow_log_le_self y (by omega)
        have hpow_r : ((y : ℝ) ^ Nat.log y (2 * X)) ≤ (4 : ℝ) ^ (3 * y + 4) :=
          (by exact_mod_cast hpow : (y : ℝ) ^ Nat.log y (2 * X) ≤ (2 * X : ℝ)).trans hX_le
        have hlog_ineq := Real.log_le_log (pow_pos (by exact_mod_cast (show 0 < y by omega)) _) hpow_r
        rwa [Real.log_pow, Real.log_pow] at hlog_ineq
      have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
        have : (4 : ℝ) ≤ Real.exp 2 := by
          have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num) 4
          simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
          norm_num at h; linarith
        calc Real.log (4 : ℝ) ≤ Real.log (Real.exp 2) := Real.log_le_log (by norm_num) this
          _ = 2 := Real.log_exp 2
      have hfrac : ((Nat.log y (2 * X) : ℕ) : ℝ) / ((y : ℝ) - 2) ≤ 1 / 100000 := by
        have hy_r : (100000 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy100
        have hy2 : 0 < (y : ℝ) - 2 := by linarith
        have hlogy_pos : 0 < Real.log (y : ℝ) := by linarith
        rw [div_le_iff₀ hy2]
        have h1 : ((Nat.log y (2 * X) : ℕ) : ℝ) ≤ (((3 * y + 4 : ℕ) : ℝ) * 2) / Real.log (y : ℝ) := by
          rw [le_div_iff₀ hlogy_pos]
          have : ((3 * y + 4 : ℕ) : ℝ) * Real.log 4 ≤ ((3 * y + 4 : ℕ) : ℝ) * 2 :=
            mul_le_mul_of_nonneg_left hlog4 (Nat.cast_nonneg _)
          linarith
        have h2 : (((3 * y + 4 : ℕ) : ℝ) * 2) / Real.log (y : ℝ) ≤ (7 * (y : ℝ)) / 2000000 := by
          have hnum : ((3 * y + 4 : ℕ) : ℝ) * 2 ≤ 7 * (y : ℝ) := by push_cast; linarith
          exact div_le_div₀ (by linarith) hnum (by norm_num) hlogy
        linarith
      have hexp1 : (1 + 1 / ((y : ℝ) - 2)) ^ Nat.log y (2 * X) ≤
          Real.exp (((Nat.log y (2 * X) : ℕ) : ℝ) / ((y : ℝ) - 2)) := by
        have h1 : 1 + 1 / ((y : ℝ) - 2) ≤ Real.exp (1 / ((y : ℝ) - 2)) := by
          linarith [Real.add_one_le_exp (1 / ((y : ℝ) - 2))]
        have hhy2 : (0 : ℝ) ≤ 1 + 1 / ((y : ℝ) - 2) := by
          have hyr : (100000 : ℝ) ≤ y := by exact_mod_cast hy100
          have hden : (0 : ℝ) < (y : ℝ) - 2 := by linarith
          have : 0 ≤ 1 / ((y : ℝ) - 2) := div_nonneg zero_le_one hden.le
          linarith
        calc (1 + 1 / ((y : ℝ) - 2)) ^ Nat.log y (2 * X)
            ≤ (Real.exp (1 / ((y : ℝ) - 2))) ^ Nat.log y (2 * X) :=
              pow_le_pow_left₀ hhy2 h1 _
          _ = Real.exp (((Nat.log y (2 * X) : ℕ) : ℝ) * (1 / ((y : ℝ) - 2))) :=
              (Real.exp_nat_mul _ _).symm
          _ = Real.exp (((Nat.log y (2 * X) : ℕ) : ℝ) / ((y : ℝ) - 2)) := by ring_nf
      have hexp2 : Real.exp (1 / 100000 : ℝ) ≤ 1 + 1 / 50000 := by
        have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1 / 100000) (by norm_num) (by decide : (0 : ℕ) < 3)
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
        norm_num at hb; linarith
      exact hexp1.trans ((Real.exp_le_exp.mpr hfrac).trans hexp2)
    have h5 : ∀ᶠ X : ℕ in atTop,
        (Real.log (X : ℝ)) / 2 - 1 ≤ Real.log ((X.sqrt : ℕ) : ℝ) := by
      filter_upwards [eventually_ge_atTop 100] with X hX
      have hsq : Real.sqrt (X : ℝ) / 2 ≤ ((X.sqrt : ℕ) : ℝ) := by
        have hlt : Real.sqrt (X : ℝ) < (X.sqrt : ℝ) + 1 := by
          have h1 : X < (X.sqrt + 1) ^ 2 := Nat.lt_succ_sqrt' X
          have h2 : (X : ℝ) < ((X.sqrt : ℝ) + 1) ^ 2 := by exact_mod_cast h1
          have h3 := Real.sqrt_lt_sqrt (Nat.cast_nonneg X) h2
          rwa [Real.sqrt_sq (by positivity)] at h3
        have h10 : (10 : ℝ) ≤ Real.sqrt (X : ℝ) := by
          rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 10 by norm_num)]
          exact Real.sqrt_le_sqrt (by exact_mod_cast (show 10 ^ 2 ≤ X by omega))
        linarith
      have hlog := Real.log_le_log (by positivity) hsq
      rw [Real.log_div (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < X by omega))).ne' (by norm_num),
        Real.log_sqrt (Nat.cast_nonneg X)] at hlog
      have hlog2 : Real.log 2 ≤ 1 := by
        have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        calc Real.log 2 ≤ Real.log (Real.exp 1) := Real.log_le_log (by norm_num) this
          _ = 1 := Real.log_exp 1
      linarith
    have h6 : ∀ᶠ X : ℕ in atTop,
        (1 : ℝ) / (Real.log ((X.sqrt : ℕ) : ℝ)) ^ 2 ≤
          (1 + 1 / 50000 : ℝ) * (4 / (Real.log (X : ℝ)) ^ 2) := by
      have hlog_tend : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      filter_upwards [h5, hlog_tend.eventually (eventually_ge_atTop (400000 : ℝ))] with X h5X hlogX
      have hlb : (1 - 1 / 200000 : ℝ) * (Real.log (X : ℝ) / 2) ≤ Real.log ((X.sqrt : ℕ) : ℝ) := by
        linarith
      have hlb_pos : 0 < (1 - 1 / 200000 : ℝ) * (Real.log (X : ℝ) / 2) := by positivity
      have hsq := pow_le_pow_left₀ hlb_pos.le hlb 2
      have hinv := one_div_le_one_div_of_le (pow_pos hlb_pos 2) hsq
      calc (1 : ℝ) / (Real.log ((X.sqrt : ℕ) : ℝ)) ^ 2
          ≤ 1 / ((1 - 1 / 200000 : ℝ) * (Real.log (X : ℝ) / 2)) ^ 2 := hinv
        _ = (1 / (1 - 1 / 200000 : ℝ) ^ 2) * (4 / (Real.log (X : ℝ)) ^ 2) := by ring
        _ ≤ (1 + 1 / 50000 : ℝ) * (4 / (Real.log (X : ℝ)) ^ 2) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            norm_num
    have h7 : ∀ᶠ X : ℕ in atTop,
        (4 : ℝ) ^ (Nat.log 4 X / 3) * (2 : ℝ) ^ (Nat.log 4 X / 3) * (Real.log (X : ℝ)) ^ 2 ≤
          (1 / 10 ^ 10 : ℝ) * (X : ℝ) := by
      -- 4^y * 2^y = 8^y = (4^y)^(3/2) <= X^(1/2), and (log X)^2 <= X^(1/4), so product <= X^(3/4) <= 10^-10 * X.
      have ht := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)
      have hb := ht.bound (show (0 : ℝ) < 1 by norm_num)
      filter_upwards [tendsto_natCast_atTop_atTop.eventually hb, eventually_ge_atTop (10 ^ 44)] with X hlogb hX
      have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 1 ≤ X by omega)
      have hlog0 : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg hX1
      rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg X) _),
        one_mul] at hlogb
      have hlogsq : (Real.log (X : ℝ)) ^ 2 ≤ (X : ℝ) ^ (1 / 4 : ℝ) := by
        have h := pow_le_pow_left₀ hlog0 hlogb 2
        rw [← Real.rpow_natCast ((X : ℝ) ^ (1 / 8 : ℝ)), ← Real.rpow_mul (Nat.cast_nonneg X)] at h
        norm_num at h; exact h
      have h4y : ((4 : ℝ) ^ (Nat.log 4 X / 3)) ^ 3 ≤ (X : ℝ) := by
        have hnat : (4 ^ (Nat.log 4 X / 3)) ^ 3 ≤ X := by
          rw [← pow_mul]
          have hle : (Nat.log 4 X / 3) * 3 ≤ Nat.log 4 X := Nat.div_mul_le_self _ 3
          exact (Nat.pow_le_pow_right (by decide) hle).trans (Nat.pow_log_le_self 4 (by omega))
        exact_mod_cast hnat
      have h4y_rpow : (4 : ℝ) ^ (Nat.log 4 X / 3) ≤ (X : ℝ) ^ (1 / 3 : ℝ) := by
        have h := Real.rpow_le_rpow (by positivity) h4y (show (0 : ℝ) ≤ 1 / 3 by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)] at h
        norm_num at h; exact h
      have h2y_rpow : (2 : ℝ) ^ (Nat.log 4 X / 3) ≤ (X : ℝ) ^ (1 / 6 : ℝ) := by
        have hsq : ((2 : ℝ) ^ (Nat.log 4 X / 3)) ^ 2 = (4 : ℝ) ^ (Nat.log 4 X / 3) := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        have h := Real.rpow_le_rpow (by positivity) (hsq ▸ h4y_rpow) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (Nat.cast_nonneg X)] at h
        norm_num at h; exact h
      have hprod : (4 : ℝ) ^ (Nat.log 4 X / 3) * (2 : ℝ) ^ (Nat.log 4 X / 3) * (Real.log (X : ℝ)) ^ 2 ≤
          (X : ℝ) ^ (3 / 4 : ℝ) := by
        calc _ ≤ (X : ℝ) ^ (1 / 3 : ℝ) * (X : ℝ) ^ (1 / 6 : ℝ) * (X : ℝ) ^ (1 / 4 : ℝ) := by
              apply mul_le_mul (mul_le_mul h4y_rpow h2y_rpow (by positivity) (by positivity))
                hlogsq (sq_nonneg _) (by positivity)
          _ = (X : ℝ) ^ (1 / 3 + 1 / 6 + 1 / 4 : ℝ) := by
              rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
          _ = (X : ℝ) ^ (3 / 4 : ℝ) := by norm_num
      have hXquarter : (10 ^ 10 : ℝ) ≤ (X : ℝ) ^ (1 / 4 : ℝ) := by
        have h := Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast hX : ((10 ^ 44 : ℕ) : ℝ) ≤ (X : ℝ)) (show (0 : ℝ) ≤ 1 / 4 by norm_num)
        have h10 : ((10 ^ 44 : ℕ) : ℝ) ^ (1 / 4 : ℝ) = (10 ^ 11 : ℝ) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
          norm_num
        rw [h10] at h; linarith
      have hfin : (X : ℝ) ^ (3 / 4 : ℝ) ≤ (1 / 10 ^ 10 : ℝ) * (X : ℝ) := by
        have h1 : (10 ^ 10 : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) ≤ (X : ℝ) ^ (1 / 4 : ℝ) * (X : ℝ) ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_right hXquarter (Real.rpow_nonneg (Nat.cast_nonneg X) _)
        rw [← Real.rpow_add (by linarith)] at h1
        norm_num at h1
        linarith
      exact hprod.trans hfin
    filter_upwards [h1, h2, h3, h4, h5, h6, h7, eventually_ge_atTop (10 ^ 8)] with X a b c d e f g h
    exact ⟨a, b, c, d, e, f, g, by exact_mod_cast h⟩
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp h_ev
  refine ⟨max X₀ 100000, le_max_right _ _, fun X hX => ?_⟩
  obtain ⟨hX20, hZsqrt, hy100, htail_le, _, hlogsqrt_sq, hrem_small, hX8⟩ :=
    hX₀ X ((le_max_left X₀ 100000).trans hX)
  set D : ℕ := X / 10000
  set E : Finset ℕ := (Finset.Icc X (X + D)).filter Even
  let I : ℕ → Finset ℕ := fun n => Finset.Icc ((n + 2) / 3) ((2 * n) / 3)
  let P : ℕ → Finset ℕ := fun z => (Finset.Icc 2 z).filter Nat.Prime
  let V : ℕ → ℝ := fun n => ((I n).card : ℝ) * (n.totient : ℝ) / (n : ℝ) *
      ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))
  set z : ℕ := X.sqrt
  set y : ℕ := Nat.log 4 X / 3
  have hz_ge_y : y ≤ z := by
    have h4y : 4 ^ y ≤ X := (Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ 3)).trans
      (Nat.pow_log_le_self 4 (by omega))
    have hy2 : y ^ 2 ≤ 4 ^ y := by
      have h1 : ∀ k : ℕ, k ^ 2 ≤ 4 ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rcases k with _ | k
          · decide
          · have hsq : (k + 2) ^ 2 ≤ 4 * (k + 1) ^ 2 := by
              have h1 : (k + 2) ^ 2 = k ^ 2 + 4 * k + 4 := by ring
              have h2 : 4 * (k + 1) ^ 2 = 4 * k ^ 2 + 8 * k + 4 := by ring
              omega
            calc (k + 2) ^ 2 ≤ 4 * (k + 1) ^ 2 := hsq
              _ ≤ 4 * 4 ^ (k + 1) := Nat.mul_le_mul_left 4 ih
              _ = 4 ^ (k + 2) := by ring
      exact h1 y
    exact Nat.le_sqrt.mpr (by simpa [sq] using hy2.trans h4y)
  set Pz : Finset ℕ := (Nat.primesLE z).erase 2
  set Py : Finset ℕ := (Nat.primesLE y).erase 2
  have hPy_sub : Py ⊆ Pz := Finset.erase_subset_erase 2 (Nat.primesLE_mono hz_ge_y)
  have hPz_ge3 : ∀ p ∈ Pz, Nat.Prime p ∧ 3 ≤ p := by
    intro p hp
    have h1 := Finset.mem_erase.mp hp
    have hpr := (Nat.mem_primesLE.mp h1.2).2
    exact ⟨hpr, by have := hpr.two_le; omega⟩
  have hPy_ge3 : ∀ p ∈ Py, Nat.Prime p ∧ 3 ≤ p := fun p hp => hPz_ge3 p (hPy_sub hp)
  have hP_eq_primesLE : ∀ w : ℕ, P w = Nat.primesLE w := fun w => (Nat.primesLE_eq_filter_Icc_two w).symm
  -- Pointwise upper bound on V n for n in E
  have hI_bound : ∀ n ∈ E, ((I n).card : ℝ) ≤ (1 + 1 / 10000 : ℝ) * (X : ℝ) / 3 + 1 := by
    intro n hn
    have hn_le : n ≤ X + D := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have hcard : (I n).card ≤ n / 3 + 1 := by
      dsimp [I]; rw [Nat.card_Icc]; omega
    have hnr : (n : ℝ) ≤ (1 + 1 / 10000 : ℝ) * (X : ℝ) := by
      have hD : (D : ℝ) ≤ (X : ℝ) / 10000 := by
        dsimp [D]
        have hdm := Nat.div_mul_le_self X 10000
        have hdmr : ((X / 10000 : ℕ) : ℝ) * 10000 ≤ (X : ℝ) := by exact_mod_cast hdm
        linarith
      have : (n : ℝ) ≤ (X : ℝ) + (D : ℝ) := by exact_mod_cast hn_le
      linarith
    have hdiv : ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by
      have : ((n / 3 : ℕ) : ℝ) * 3 ≤ (n : ℝ) := by exact_mod_cast Nat.div_mul_le_self n 3
      linarith
    have : ((I n).card : ℝ) ≤ ((n / 3 : ℕ) : ℝ) + 1 := by exact_mod_cast hcard
    linarith
  have hV_pt : ∀ n ∈ E,
      V n ≤ ((1 + 1 / 10000 : ℝ) * (X : ℝ) / 3 + 1) * (1 / 2) *
        (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (1 + 1 / 50000 : ℝ) *
        (∏ p ∈ Py.filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ))) := by
    intro n hn
    have hn_mem := Finset.mem_filter.mp hn
    have hn_lo : X ≤ n := (Finset.mem_Icc.mp hn_mem.1).1
    have hn_hi : n ≤ X + D := (Finset.mem_Icc.mp hn_mem.1).2
    have hn_ev : Even n := hn_mem.2
    have h2n : 2 ∣ n := even_iff_two_dvd.mp hn_ev
    have hn_pos : 0 < n := by omega
    -- 1. totient n / n = prod_{p | n} (1 - 1/p) <= (1/2) * prod_{p in Pz, p | n} (1 - 1/p)
    have htot : (n.totient : ℝ) / (n : ℝ) ≤
        (1 / 2 : ℝ) * ∏ p ∈ Pz.filter (fun p => p ∣ n), (1 - 1 / (p : ℝ)) := by
      have hformula : (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
        have hq := Nat.totient_eq_mul_prod_factors n
        have hr := congrArg (fun q : ℚ => (q : ℝ)) hq
        push_cast at hr
        exact hr
      rw [hformula, mul_div_cancel_left₀ _ (by exact_mod_cast hn_pos.ne')]
      have h2mem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2n, hn_pos.ne'⟩
      have hsub_tot : insert 2 (Pz.filter (fun p => p ∣ n)) ⊆ n.primeFactors := by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact h2mem
        · have hf := Finset.mem_filter.mp hp'
          exact Nat.mem_primeFactors.mpr ⟨(hPz_ge3 p hf.1).1, hf.2, hn_pos.ne'⟩
      have hprod_le :
          ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) ≤
            ∏ p ∈ insert 2 (Pz.filter (fun p => p ∣ n)), (1 - (p : ℝ)⁻¹) := by
        rw [← Finset.prod_sdiff hsub_tot]
        have h1 : ∏ p ∈ n.primeFactors \ insert 2 (Pz.filter (fun p => p ∣ n)), (1 - (p : ℝ)⁻¹) ≤ 1 := by
          have h := prod_le_prod_real (s := n.primeFactors \ insert 2 (Pz.filter (fun p => p ∣ n)))
            (f := fun p => 1 - (p : ℝ)⁻¹) (g := fun _ => 1)
            (fun p hp => by
              have hpr := Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
              have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpr.one_lt.le)
              linarith)
            (fun p hp => by
              have : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg p)
              linarith)
          simpa using h
        have h2 : 0 ≤ ∏ p ∈ insert 2 (Pz.filter (fun p => p ∣ n)), (1 - (p : ℝ)⁻¹) := by
          apply Finset.prod_nonneg
          intro p hp
          have hpr := Nat.prime_of_mem_primeFactors (hsub_tot hp)
          have : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hpr.one_lt.le)
          linarith
        exact mul_le_of_le_one_left h2 h1
      have h2not : 2 ∉ Pz.filter (fun p => p ∣ n) := by simp [Pz]
      rw [Finset.prod_insert h2not] at hprod_le
      norm_num only [one_div] at hprod_le ⊢
      exact hprod_le
    -- 2. prod_{p in P n.sqrt, ¬ p | n} (1 - 2/p) <= prod_{p in Pz, ¬ p | n} (1 - 2/p)
    have hprod_nondiv :
        ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) ≤
          ∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) := by
      have hsub : Pz.filter (fun p => ¬ p ∣ n) ⊆ (P n.sqrt).filter (fun p => ¬ p ∣ n) := by
        intro p hp
        rw [Finset.mem_filter] at hp ⊢
        rw [hP_eq_primesLE]
        exact ⟨Nat.primesLE_mono (Nat.sqrt_le_sqrt hn_lo) (Finset.mem_erase.mp hp.1).2, hp.2⟩
      rw [← Finset.prod_sdiff hsub]
      have h1 : ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n) \ Pz.filter (fun p => ¬ p ∣ n),
          (1 - 2 / (p : ℝ)) ≤ 1 := by
        have h := prod_le_prod_real
          (s := (P n.sqrt).filter (fun p => ¬ p ∣ n) \ Pz.filter (fun p => ¬ p ∣ n))
          (f := fun p => 1 - 2 / (p : ℝ)) (g := fun _ => 1)
          (fun p hp => by
            have hp_mem := Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1
            rw [hP_eq_primesLE, Nat.mem_primesLE] at hp_mem
            have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp_mem.1.2.two_le
            have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hp2
            linarith)
          (fun p _ => by
            have : 0 ≤ 2 / (p : ℝ) := by positivity
            linarith)
        simpa using h
      have h2 : 0 ≤ ∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) := by
        apply Finset.prod_nonneg
        intro p hp
        have hp3 := (hPz_ge3 p (Finset.mem_filter.mp hp).1).2
        have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by exact_mod_cast (show 0 < p by omega))).mpr
          (by exact_mod_cast (show 2 ≤ p by omega))
        linarith
      exact mul_le_of_le_one_left h2 h1
    -- 3. Combine: prod_{p in Pz, p | n} (1 - 1/p) * prod_{p in Pz, ¬ p | n} (1 - 2/p)
    --           = (prod_{p in Pz} (1 - 2/p)) * prod_{p in Pz, p | n} ((p-1)/(p-2))
    have hcombine :
        (∏ p ∈ Pz.filter (fun p => p ∣ n), (1 - 1 / (p : ℝ))) *
          (∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))) =
          (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
            ∏ p ∈ Pz.filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ)) := by
      have hpart := Finset.prod_filter_mul_prod_filter_not Pz (fun p => p ∣ n) (fun p => 1 - 2 / (p : ℝ))
      rw [← hpart, mul_assoc, mul_comm (∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))), ← mul_assoc]
      congr 1
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPz_ge3 p (Finset.mem_filter.mp hp).1).2
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
      field_simp
    -- 4. Split Pz.filter (p | n) into Py and Pz \ Py; bound Pz \ Py by 1 + 1/50000
    have hsplit_div :
        ∏ p ∈ Pz.filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ)) =
          (∏ p ∈ Py.filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ))) *
            (∏ p ∈ (Pz \ Py).filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ))) := by
      have hsub : Py.filter (fun p => p ∣ n) ⊆ Pz.filter (fun p => p ∣ n) :=
        Finset.filter_subset_filter _ hPy_sub
      have hsdiff : Pz.filter (fun p => p ∣ n) \ Py.filter (fun p => p ∣ n) =
          (Pz \ Py).filter (fun p => p ∣ n) := by
        ext p; simp only [Finset.mem_sdiff, Finset.mem_filter]; tauto
      rw [← hsdiff, mul_comm, Finset.prod_sdiff hsub]
    have htail_prod :
        ∏ p ∈ (Pz \ Py).filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ)) ≤
          (1 + 1 / 50000 : ℝ) := by
      have hsub_n : (Pz \ Py).filter (fun p => p ∣ n) ⊆ n.primeFactors.filter (fun p => y < p) := by
        intro p hp
        have hf := Finset.mem_filter.mp hp
        have hs := Finset.mem_sdiff.mp hf.1
        have hpr := (hPz_ge3 p hs.1).1
        have hgt : y < p := by
          by_contra hle
          push_neg at hle
          apply hs.2
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hs.1).1, Nat.mem_primesLE.mpr ⟨hle, hpr⟩⟩
        exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpr, hf.2, hn_pos.ne'⟩, hgt⟩
      have hcard_le : ((Pz \ Py).filter (fun p => p ∣ n)).card ≤ Nat.log y (2 * X) := by
        have h1 := Finset.card_le_card hsub_n
        have h2 := card_primes_gt_dvd_le (by omega : 1 ≤ n) (by omega : 2 ≤ y)
        have h3 : Nat.log y n ≤ Nat.log y (2 * X) := Nat.log_mono_right (by omega)
        omega
      have heach : ∀ p ∈ (Pz \ Py).filter (fun p => p ∣ n),
          ((p - 1 : ℝ) / (p - 2 : ℝ)) ≤ 1 + 1 / ((y : ℝ) - 2) := by
        intro p hp
        have hgt : y < p := (Finset.mem_filter.mp (hsub_n hp)).2
        have hy_r : (100000 : ℝ) ≤ y := by exact_mod_cast hy100
        have hp_r : (y : ℝ) < p := by exact_mod_cast hgt
        have h1 : ((p - 1 : ℝ) / (p - 2 : ℝ)) = 1 + 1 / ((p : ℝ) - 2) := by
          have : (p : ℝ) - 2 ≠ 0 := by linarith
          field_simp; ring
        rw [h1]
        have : 1 / ((p : ℝ) - 2) ≤ 1 / ((y : ℝ) - 2) :=
          one_div_le_one_div_of_le (by linarith) (by linarith)
        linarith
      have hprod_pow :
          ∏ p ∈ (Pz \ Py).filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ)) ≤
            (1 + 1 / ((y : ℝ) - 2)) ^ ((Pz \ Py).filter (fun p => p ∣ n)).card := by
        calc _ ≤ ∏ _p ∈ (Pz \ Py).filter (fun p => p ∣ n), (1 + 1 / ((y : ℝ) - 2)) :=
              prod_le_prod_real (fun p hp => by
                have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPz_ge3 p (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1).2
                exact div_nonneg (by linarith) (by linarith)) heach
          _ = _ := Finset.prod_const _
      have hbase : 1 ≤ 1 + 1 / ((y : ℝ) - 2) := by
        have hy_r : (100000 : ℝ) ≤ y := by exact_mod_cast hy100
        have hden : (0 : ℝ) < (y : ℝ) - 2 := by linarith
        have : 0 ≤ 1 / ((y : ℝ) - 2) := div_nonneg zero_le_one hden.le
        linarith
      exact hprod_pow.trans ((pow_le_pow_right₀ hbase hcard_le).trans htail_le)
    have hV_nonneg_prod : 0 ≤ ∏ p ∈ Pz, (1 - 2 / (p : ℝ)) := by
      apply Finset.prod_nonneg
      intro p hp
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPz_ge3 p hp).2
      have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      linarith
    have hPy_nonneg : 0 ≤ ∏ p ∈ Py.filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ)) := by
      apply Finset.prod_nonneg
      intro p hp
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPy_ge3 p (Finset.mem_filter.mp hp).1).2
      exact div_nonneg (by linarith) (by linarith)
    have hV_step1 :
        (n.totient : ℝ) / (n : ℝ) *
          ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) ≤
        (1 / 2) * (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (1 + 1 / 50000 : ℝ) *
          (∏ p ∈ Py.filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ))) := by
      have hmul := mul_le_mul htot hprod_nondiv
        (Finset.prod_nonneg fun p hp => by
          have hp2 : (2 : ℝ) ≤ p := by
            have := Finset.mem_filter.mp hp; rw [hP_eq_primesLE, Nat.mem_primesLE] at this
            exact_mod_cast this.1.2.two_le
          have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hp2
          linarith)
        (mul_nonneg (by norm_num) (Finset.prod_nonneg fun p hp => by
          have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPz_ge3 p (Finset.mem_filter.mp hp).1).2
          have : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
          linarith))
      rw [mul_assoc, hcombine, hsplit_div] at hmul
      calc (n.totient : ℝ) / (n : ℝ) * ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))
          ≤ (1 / 2) * ((∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
              ((∏ p ∈ Py.filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ))) *
                (∏ p ∈ (Pz \ Py).filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ))))) := hmul
        _ ≤ (1 / 2) * ((∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
              ((∏ p ∈ Py.filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ))) *
                (1 + 1 / 50000 : ℝ))) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply mul_le_mul_of_nonneg_left _ hV_nonneg_prod
            exact mul_le_mul_of_nonneg_left htail_prod hPy_nonneg
        _ = (1 / 2) * (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (1 + 1 / 50000 : ℝ) *
              (∏ p ∈ Py.filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ))) := by ring
    dsimp [V]
    rw [mul_div_assoc]
    calc ((I n).card : ℝ) * ((n.totient : ℝ) / (n : ℝ)) *
          ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))
        = ((I n).card : ℝ) * ((n.totient : ℝ) / (n : ℝ) *
            ∏ p ∈ (P n.sqrt).filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))) := by ring
      _ ≤ ((1 + 1 / 10000 : ℝ) * (X : ℝ) / 3 + 1) *
            ((1 / 2) * (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (1 + 1 / 50000 : ℝ) *
              (∏ p ∈ Py.filter (fun p => p ∣ n), ((p - 1 : ℝ) / (p - 2 : ℝ)))) := by
          apply mul_le_mul (hI_bound n hn) hV_step1
          · apply mul_nonneg (by positivity)
            apply Finset.prod_nonneg
            intro p hp
            have hp2 : (2 : ℝ) ≤ p := by
              have := Finset.mem_filter.mp hp; rw [hP_eq_primesLE, Nat.mem_primesLE] at this
              exact_mod_cast this.1.2.two_le
            have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hp2
            linarith
          · positivity
      _ = _ := by ring
  -- Sum over E using periodicity mod W = prod_{p in Py} p
  set W : ℕ := ∏ p ∈ Py, p
  have hW_pos : 0 < W := Finset.prod_pos (fun p hp => (hPy_ge3 p hp).1.pos)
  have hW_le : (W : ℝ) ≤ (4 : ℝ) ^ y := by
    have hsub : Py ⊆ Nat.primesLE y := Finset.erase_subset 2 _
    have hdvd : W ∣ primorial y := Finset.prod_dvd_prod_of_subset _ _ _ hsub
    have hle : W ≤ 4 ^ y := (Nat.le_of_dvd (primorial_pos y) hdvd).trans (primorial_le_four_pow y)
    exact_mod_cast hle
  let f : ℕ → ℝ := fun m => ∏ p ∈ Py.filter (fun p => p ∣ m), ((p - 1 : ℝ) / (p - 2 : ℝ))
  have hf_even : ∀ m : ℕ, f (2 * m) = f m := by
    intro m
    dsimp [f]
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hd⟩
      refine ⟨hp, ?_⟩
      have hpr := (hPy_ge3 p hp).1
      have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hpr Nat.prime_two).mpr
        (by have := (hPy_ge3 p hp).2; omega)
      exact hcop.dvd_of_dvd_mul_left hd
    · rintro ⟨hp, hd⟩
      exact ⟨hp, dvd_mul_of_dvd_right hd 2⟩
  have hf_per : ∀ m : ℕ, f (m % W) = f m := by
    intro m
    dsimp [f]
    congr 1
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hd⟩
      refine ⟨hp, ?_⟩
      have hpW : p ∣ W := Finset.dvd_prod_of_mem _ hp
      exact (Nat.dvd_mod_iff hpW).mp hd
    · rintro ⟨hp, hd⟩
      exact ⟨hp, (Nat.dvd_mod_iff (Finset.dvd_prod_of_mem _ hp)).mpr hd⟩
  have hf_ub : ∀ m : ℕ, f m ≤ (2 : ℝ) ^ y := by
    intro m
    dsimp [f]
    have h1 : ∏ p ∈ Py.filter (fun p => p ∣ m), ((p - 1 : ℝ) / (p - 2 : ℝ)) ≤
        ∏ _p ∈ Py.filter (fun p => p ∣ m), (2 : ℝ) := by
      apply prod_le_prod_real
      · intro p hp
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPy_ge3 p (Finset.mem_filter.mp hp).1).2
        exact div_nonneg (by linarith) (by linarith)
      · intro p hp
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPy_ge3 p (Finset.mem_filter.mp hp).1).2
        rw [div_le_iff₀ (by linarith)]; linarith
    rw [Finset.prod_const] at h1
    have hcard : (Py.filter (fun p => p ∣ m)).card ≤ y := by
      have hsub : Py.filter (fun p => p ∣ m) ⊆ Finset.Icc 1 y := by
        intro p hp
        have hmem := (Finset.mem_erase.mp (Finset.mem_filter.mp hp).1).2
        rw [Nat.mem_primesLE] at hmem
        exact Finset.mem_Icc.mpr ⟨hmem.2.pos, hmem.1⟩
      exact (Finset.card_le_card hsub).trans (by simp)
    exact h1.trans (pow_le_pow_right₀ (by norm_num) hcard)
  -- Reindex E via n = 2 * m for m in Icc ((X + 1) / 2) ((X + D) / 2)
  set A : ℕ := (X + 1) / 2
  set B : ℕ := (X + D) / 2
  have hE_sum : ∑ n ∈ E, f n = ∑ m ∈ Finset.Icc A B, f m := by
    refine Finset.sum_bij (fun n _ => n / 2) ?_ ?_ ?_ ?_
    · intro n hn
      have hf := Finset.mem_filter.mp hn
      have hi := Finset.mem_Icc.mp hf.1
      have h2 := even_iff_two_dvd.mp hf.2
      rw [Finset.mem_Icc]; dsimp [A, B]; omega
    · intro n1 hn1 n2 hn2 heq
      have h1 := even_iff_two_dvd.mp (Finset.mem_filter.mp hn1).2
      have h2 := even_iff_two_dvd.mp (Finset.mem_filter.mp hn2).2
      omega
    · intro m hm
      rw [Finset.mem_Icc] at hm
      refine ⟨2 * m, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by dsimp [A] at hm; omega,
        by dsimp [B] at hm; omega⟩, even_two_mul m⟩, by omega⟩
    · intro n hn
      have h2 := even_iff_two_dvd.mp (Finset.mem_filter.mp hn).2
      have hne : n = 2 * (n / 2) := by omega
      conv_lhs => rw [hne]
      exact hf_even (n / 2)
  -- Bound ∑ m ∈ Icc A B, f m by q full periods + remainder
  set Llen : ℕ := B + 1 - A
  have hIcc_eq : Finset.Icc A B = (Finset.range Llen).image (fun k => A + k) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hm; exact ⟨m - A, by dsimp [Llen]; omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; dsimp [Llen] at hk; omega
  have hsum_per :
      ∑ m ∈ Finset.Icc A B, f m ≤
        (((Llen / W : ℕ) : ℝ) * (W : ℝ)) * (∏ p ∈ Py, ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ)))) +
          (W : ℝ) * (2 : ℝ) ^ y := by
    rw [hIcc_eq, Finset.sum_image (fun _ _ _ _ h => by omega)]
    set q : ℕ := Llen / W
    set rem : ℕ := Llen % W
    have hLlen : q * W + rem = Llen := by
      have := Nat.div_add_mod Llen W; dsimp [q, rem]; linarith
    have hsplit_r : ∑ k ∈ Finset.range Llen, f (A + k) =
        (∑ j ∈ Finset.range q, ∑ t ∈ Finset.range W, f (A + j * W + t)) +
        ∑ t ∈ Finset.range rem, f (A + q * W + t) := by
      rw [← hLlen, Finset.sum_range_add]
      congr 1
      · induction q with
        | zero => simp
        | succ q ih =>
          rw [Nat.succ_mul, Finset.sum_range_add, Finset.sum_range_succ, ih]
          congr 1; apply Finset.sum_congr rfl; intro t _; ring_nf
      · apply Finset.sum_congr rfl; intro t _; ring_nf
    rw [hsplit_r]
    have hperiod_one : ∀ c : ℕ, ∑ t ∈ Finset.range W, f (c + t) =
        (W : ℝ) * ∏ p ∈ Py, ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ))) := by
      intro c
      have hrot : ∑ t ∈ Finset.range W, f (c + t) = ∑ m ∈ Finset.range W, f m := by
        refine Finset.sum_bij (fun t _ => (c + t) % W) ?_ ?_ ?_ ?_
        · intro t _; exact Finset.mem_range.mpr (Nat.mod_lt _ hW_pos)
        · intro t1 ht1 t2 ht2 hmod
          have h1 := Finset.mem_range.mp ht1
          have h2 := Finset.mem_range.mp ht2
          have hcong : c + t1 ≡ c + t2 [MOD W] := hmod
          have hcong2 : t1 ≡ t2 [MOD W] := Nat.ModEq.add_left_cancel' c hcong
          rw [Nat.ModEq, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hcong2
          exact hcong2
        · intro m hm
          have hmW := Finset.mem_range.mp hm
          refine ⟨(W + m - c % W) % W, Finset.mem_range.mpr (Nat.mod_lt _ hW_pos), ?_⟩
          have hcW := Nat.mod_lt c hW_pos
          have h1 : c + (W + m - c % W) % W ≡ c % W + (W + m - c % W) [MOD W] :=
            (Nat.mod_modEq c W).symm.add (Nat.mod_modEq _ W)
          have h2 : c % W + (W + m - c % W) = W + m := by omega
          rw [h2] at h1
          have h3 : (W + m) % W = m := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt hmW]
          have hmod := h1.trans (by rw [Nat.ModEq, Nat.mod_eq_of_lt hmW]; exact h3)
          rw [Nat.ModEq, Nat.mod_eq_of_lt hmW] at hmod
          exact hmod
        · intro t _; exact (hf_per (c + t)).symm
      rw [hrot]
      exact period_avg_odd_primes Py hPy_ge3
    have hq_sum : ∑ j ∈ Finset.range q, ∑ t ∈ Finset.range W, f (A + j * W + t) =
        ((q : ℝ) * (W : ℝ)) * ∏ p ∈ Py, ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ))) := by
      simp_rw [hperiod_one]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]
    have hrem_sum : ∑ t ∈ Finset.range rem, f (A + q * W + t) ≤ (W : ℝ) * (2 : ℝ) ^ y := by
      calc ∑ t ∈ Finset.range rem, f (A + q * W + t)
          ≤ ∑ _t ∈ Finset.range rem, (2 : ℝ) ^ y := Finset.sum_le_sum (fun t _ => hf_ub _)
        _ = (rem : ℝ) * (2 : ℝ) ^ y := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ (W : ℝ) * (2 : ℝ) ^ y :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mod_lt Llen hW_pos).le) (by positivity)
    linarith
  -- Now combine (∏_{Pz} (1 - 2/p)) * (∏_{Py} ((p-1)^2 / (p*(p-2)))) <= 4 * (∏_{primesLE z} (1 - 1/p))^2
  have hprod_cancel :
      (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
          (∏ p ∈ Py, ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ)))) ≤
        4 * (∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ))) ^ 2 := by
    rw [← Finset.prod_sdiff hPy_sub]
    have h1 : (∏ p ∈ Py, (1 - 2 / (p : ℝ))) *
        (∏ p ∈ Py, ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ)))) =
        ∏ p ∈ Py, (1 - 1 / (p : ℝ)) ^ 2 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPy_ge3 p hp).2
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
      field_simp
    have h2 : ∏ p ∈ Pz \ Py, (1 - 2 / (p : ℝ)) ≤ ∏ p ∈ Pz \ Py, (1 - 1 / (p : ℝ)) ^ 2 := by
      apply prod_le_prod_real
      · intro p hp
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPz_ge3 p (Finset.mem_sdiff.mp hp).1).2
        have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
        linarith
      · intro p hp
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPz_ge3 p (Finset.mem_sdiff.mp hp).1).2
        have : 0 ≤ (1 / (p : ℝ)) ^ 2 := sq_nonneg _
        linarith [show (1 - 1 / (p : ℝ)) ^ 2 = 1 - 2 / (p : ℝ) + (1 / (p : ℝ)) ^ 2 by ring]
    have hPy_sq_nn : 0 ≤ ∏ p ∈ Py, (1 - 1 / (p : ℝ)) ^ 2 :=
      Finset.prod_nonneg (fun _ _ => sq_nonneg _)
    have h3 : (∏ p ∈ Pz \ Py, (1 - 2 / (p : ℝ))) * (∏ p ∈ Py, (1 - 2 / (p : ℝ))) *
          (∏ p ∈ Py, ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ)))) ≤
        (∏ p ∈ Pz, (1 - 1 / (p : ℝ))) ^ 2 := by
      rw [mul_assoc, h1, ← Finset.prod_pow, ← Finset.prod_sdiff hPy_sub]
      exact mul_le_mul_of_nonneg_right h2 hPy_sq_nn
    have h2mem : 2 ∈ Nat.primesLE z := Nat.mem_primesLE.mpr ⟨by omega, Nat.prime_two⟩
    have h4 : ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ)) = (1 / 2) * ∏ p ∈ Pz, (1 - 1 / (p : ℝ)) := by
      have := Finset.mul_prod_erase (Nat.primesLE z) (fun p => 1 - 1 / (p : ℝ)) h2mem
      rw [← this]; norm_num [Pz]
    rw [h4]
    linarith [show 4 * ((1 / 2) * ∏ p ∈ Pz, (1 - 1 / (p : ℝ))) ^ 2 =
      (∏ p ∈ Pz, (1 - 1 / (p : ℝ))) ^ 2 by ring]
  -- Assemble the full sum bound
  have hsum_V := Finset.sum_le_sum hV_pt
  rw [← Finset.mul_sum, hE_sum] at hsum_V
  have hPz_le1 : ∏ p ∈ Pz, (1 - 2 / (p : ℝ)) ≤ 1 := by
    have h := prod_le_prod_real (s := Pz) (f := fun p => 1 - 2 / (p : ℝ)) (g := fun _ => 1)
      (fun p hp => by
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPz_ge3 p hp).2
        have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
        linarith)
      (fun p _ => by
        have : 0 ≤ 2 / (p : ℝ) := by positivity
        linarith)
    simpa using h
  have hPz_nn : 0 ≤ ∏ p ∈ Pz, (1 - 2 / (p : ℝ)) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPz_ge3 p hp).2
    have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hLlen_le : (((Llen / W : ℕ) : ℝ) * (W : ℝ)) ≤ (X : ℝ) / 20000 + 2 := by
    have h1 : (Llen / W) * W ≤ Llen := Nat.div_mul_le_self Llen W
    have h2 : Llen ≤ X / 20000 + 2 := by dsimp [Llen, A, B, D]; omega
    have h3 : ((X / 20000 : ℕ) : ℝ) ≤ (X : ℝ) / 20000 := by
      have : ((X / 20000 : ℕ) : ℝ) * 20000 ≤ (X : ℝ) := by exact_mod_cast Nat.div_mul_le_self X 20000
      linarith
    have h4 : (((Llen / W : ℕ) : ℝ) * (W : ℝ)) ≤ (Llen : ℝ) := by exact_mod_cast h1
    have h5 : (Llen : ℝ) ≤ ((X / 20000 : ℕ) : ℝ) + 2 := by exact_mod_cast h2
    linarith
  have hMert_sq : (∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ))) ^ 2 ≤
      Real.exp (-2 * (5755 / 10000 : ℝ)) * (1 + 1 / 50000 : ℝ) * (4 / (Real.log (X : ℝ)) ^ 2) := by
    have hm := hmert z hZsqrt
    have hnn : 0 ≤ ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ)) :=
      Finset.prod_nonneg (fun p hp => by
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.two_le
        have : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
        linarith)
    have hsq := pow_le_pow_left₀ hnn hm 2
    rw [div_pow, ← Real.exp_nat_mul] at hsq
    have hexp_eq : (2 : ℕ) * (-(5755 / 10000 : ℝ)) = -2 * (5755 / 10000 : ℝ) := by push_cast; ring
    rw [hexp_eq] at hsq
    calc (∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ))) ^ 2
        ≤ Real.exp (-2 * (5755 / 10000 : ℝ)) * (1 / (Real.log (z : ℝ)) ^ 2) := by
          rw [mul_one_div]; exact hsq
      _ ≤ Real.exp (-2 * (5755 / 10000 : ℝ)) *
            ((1 + 1 / 50000 : ℝ) * (4 / (Real.log (X : ℝ)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hlogsqrt_sq (Real.exp_pos _).le
      _ = _ := by ring
  have hmain_comb :
      (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (∑ m ∈ Finset.Icc A B, f m) ≤
        ((X : ℝ) / 20000 + 2) * (4 * Real.exp (-2 * (5755 / 10000 : ℝ)) *
          (1 + 1 / 50000 : ℝ) * (4 / (Real.log (X : ℝ)) ^ 2)) +
        (W : ℝ) * (2 : ℝ) ^ y := by
    have h1 := mul_le_mul_of_nonneg_left hsum_per hPz_nn
    rw [mul_add] at h1
    have h2 : (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
          ((((Llen / W : ℕ) : ℝ) * (W : ℝ)) *
            ∏ p ∈ Py, ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ)))) ≤
        ((X : ℝ) / 20000 + 2) * (4 * Real.exp (-2 * (5755 / 10000 : ℝ)) *
          (1 + 1 / 50000 : ℝ) * (4 / (Real.log (X : ℝ)) ^ 2)) := by
      have hrearr : (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
            ((((Llen / W : ℕ) : ℝ) * (W : ℝ)) *
              ∏ p ∈ Py, ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ)))) =
          (((Llen / W : ℕ) : ℝ) * (W : ℝ)) *
            ((∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
              ∏ p ∈ Py, ((p - 1 : ℝ) ^ 2 / ((p : ℝ) * (p - 2 : ℝ)))) := by ring
      rw [hrearr]
      apply mul_le_mul hLlen_le
        (hprod_cancel.trans (by linarith [hMert_sq]))
      · apply mul_nonneg hPz_nn
        apply Finset.prod_nonneg
        intro p hp
        have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPy_ge3 p hp).2
        exact div_nonneg (sq_nonneg _) (by nlinarith only [hp3])
      · positivity
    have h3 : (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * ((W : ℝ) * (2 : ℝ) ^ y) ≤ (W : ℝ) * (2 : ℝ) ^ y := by
      calc _ ≤ 1 * ((W : ℝ) * (2 : ℝ) ^ y) := mul_le_mul_of_nonneg_right hPz_le1 (by positivity)
        _ = _ := one_mul _
    linarith
  have hW_rem : (W : ℝ) * (2 : ℝ) ^ y ≤
      (1 / 10 ^ 10 : ℝ) * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := by
    have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    rw [le_div_iff₀ (sq_pos_of_pos hlogX_pos)]
    calc (W : ℝ) * (2 : ℝ) ^ y * (Real.log (X : ℝ)) ^ 2
        ≤ (4 : ℝ) ^ y * (2 : ℝ) ^ y * (Real.log (X : ℝ)) ^ 2 := by
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hW_le (by positivity)) (sq_nonneg _)
      _ ≤ (1 / 10 ^ 10 : ℝ) * (X : ℝ) := hrem_small
  have hX_tiny : (2 : ℝ) ≤ (1 / 50000 : ℝ) * ((X : ℝ) / 20000) := by
    have hX20r : (10 ^ 20 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX20
    linarith
  have hI_tiny : (1 : ℝ) ≤ (1 / 50000 : ℝ) * ((1 + 1 / 10000 : ℝ) * (X : ℝ) / 3) := by linarith
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hexp_lb : (1 / 4 : ℝ) ≤ Real.exp (-2 * (5755 / 10000 : ℝ)) := by
    rw [show -2 * (5755 / 10000 : ℝ) = -(2 * (5755 / 10000 : ℝ)) by ring, Real.exp_neg]
    rw [le_inv_comm₀ (by norm_num) (Real.exp_pos _)]
    have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 5755 / 20000) (by norm_num) (by decide : (0 : ℕ) < 5)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
    have h1 : Real.exp (5755 / 20000 : ℝ) ≤ 14 / 10 := by norm_num at hb; linarith
    have h4 := pow_le_pow_left₀ (Real.exp_pos _).le h1 4
    rw [← Real.exp_nat_mul] at h4
    have heq : (4 : ℕ) * (5755 / 20000 : ℝ) = 2 * (5755 / 10000 : ℝ) := by norm_num
    rw [heq] at h4
    norm_num at h4; linarith
  have hW_rel : (1 / 10 ^ 10 : ℝ) * (X : ℝ) / (Real.log (X : ℝ)) ^ 2 ≤
      (1 / 50000 : ℝ) * ((X : ℝ) / 20000) * (16 * Real.exp (-2 * (5755 / 10000 : ℝ)) / (Real.log (X : ℝ)) ^ 2) := by
    have hpos : 0 < (X : ℝ) / (Real.log (X : ℝ)) ^ 2 := div_pos (by positivity) (sq_pos_of_pos hlogX_pos)
    have h1 : (1 / 10 ^ 10 : ℝ) ≤ (1 / 50000 : ℝ) * (1 / 20000) * (16 * (1 / 4)) := by norm_num
    have h2 : (1 / 50000 : ℝ) * (1 / 20000) * (16 * (1 / 4)) ≤
        (1 / 50000 : ℝ) * (1 / 20000) * (16 * Real.exp (-2 * (5755 / 10000 : ℝ))) := by linarith [hexp_lb]
    have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) hpos.le
    calc (1 / 10 ^ 10 : ℝ) * (X : ℝ) / (Real.log (X : ℝ)) ^ 2
        = (1 / 10 ^ 10 : ℝ) * ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) := by ring
      _ ≤ (1 / 50000 : ℝ) * (1 / 20000) * (16 * Real.exp (-2 * (5755 / 10000 : ℝ))) *
            ((X : ℝ) / (Real.log (X : ℝ)) ^ 2) := h3
      _ = _ := by ring
  set M_val : ℝ := Real.exp (-2 * (5755 / 10000 : ℝ)) * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2
  have hM_nn : 0 ≤ M_val := by dsimp [M_val]; positivity
  have hmid :
      (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (∑ m ∈ Finset.Icc A B, f m) ≤
        ((1 + 1 / 50000 : ℝ) ^ 2 + 1 / 50000 : ℝ) *
          ((X : ℝ) / 20000) * (16 * Real.exp (-2 * (5755 / 10000 : ℝ)) / (Real.log (X : ℝ)) ^ 2) := by
    have hpos1 : 0 ≤ 16 * Real.exp (-2 * (5755 / 10000 : ℝ)) / (Real.log (X : ℝ)) ^ 2 := by positivity
    have hstep :
        ((X : ℝ) / 20000 + 2) * (4 * Real.exp (-2 * (5755 / 10000 : ℝ)) *
          (1 + 1 / 50000 : ℝ) * (4 / (Real.log (X : ℝ)) ^ 2)) ≤
        (1 + 1 / 50000 : ℝ) ^ 2 * ((X : ℝ) / 20000) *
          (16 * Real.exp (-2 * (5755 / 10000 : ℝ)) / (Real.log (X : ℝ)) ^ 2) := by
      have h1 : (X : ℝ) / 20000 + 2 ≤ (1 + 1 / 50000 : ℝ) * ((X : ℝ) / 20000) := by linarith
      have h2 := mul_le_mul_of_nonneg_right h1 (show 0 ≤ (1 + 1 / 50000 : ℝ) *
        (16 * Real.exp (-2 * (5755 / 10000 : ℝ)) / (Real.log (X : ℝ)) ^ 2) by positivity)
      linarith [show ((X : ℝ) / 20000 + 2) * (4 * Real.exp (-2 * (5755 / 10000 : ℝ)) *
          (1 + 1 / 50000 : ℝ) * (4 / (Real.log (X : ℝ)) ^ 2)) =
        ((X : ℝ) / 20000 + 2) * ((1 + 1 / 50000 : ℝ) *
          (16 * Real.exp (-2 * (5755 / 10000 : ℝ)) / (Real.log (X : ℝ)) ^ 2)) by ring,
        show (1 + 1 / 50000 : ℝ) * ((X : ℝ) / 20000) * ((1 + 1 / 50000 : ℝ) *
          (16 * Real.exp (-2 * (5755 / 10000 : ℝ)) / (Real.log (X : ℝ)) ^ 2)) =
        (1 + 1 / 50000 : ℝ) ^ 2 * ((X : ℝ) / 20000) *
          (16 * Real.exp (-2 * (5755 / 10000 : ℝ)) / (Real.log (X : ℝ)) ^ 2) by ring]
    linarith [hmain_comb, hW_rem, hW_rel, hstep]
  have hpref :
      ((1 + 1 / 10000 : ℝ) * (X : ℝ) / 3 + 1) * (1 / 2) * (1 + 1 / 50000 : ℝ) ≤
        (1 + 1 / 50000 : ℝ) ^ 2 * ((1 + 1 / 10000 : ℝ) * (X : ℝ) / 6) := by
    have h1 : (1 + 1 / 10000 : ℝ) * (X : ℝ) / 3 + 1 ≤
        (1 + 1 / 50000 : ℝ) * ((1 + 1 / 10000 : ℝ) * (X : ℝ) / 3) := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (show (0 : ℝ) ≤ (1 / 2) * (1 + 1 / 50000 : ℝ) by norm_num)
    linarith
  have hsum_f_nn : 0 ≤ ∑ m ∈ Finset.Icc A B, f m :=
    Finset.sum_nonneg (fun m _ => Finset.prod_nonneg (fun p hp => by
      have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hPy_ge3 p (Finset.mem_filter.mp hp).1).2
      exact div_nonneg (by linarith) (by linarith)))
  have hfinal_mul :
      ((1 + 1 / 10000 : ℝ) * (X : ℝ) / 3 + 1) * (1 / 2) *
          (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (1 + 1 / 50000 : ℝ) *
          (∑ m ∈ Finset.Icc A B, f m) ≤
        ((1 + 1 / 50000 : ℝ) ^ 2 * ((1 + 1 / 50000 : ℝ) ^ 2 + 1 / 50000 : ℝ)) *
          ((4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) * M_val) := by
    have hrearr :
        ((1 + 1 / 10000 : ℝ) * (X : ℝ) / 3 + 1) * (1 / 2) *
            (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (1 + 1 / 50000 : ℝ) *
            (∑ m ∈ Finset.Icc A B, f m) =
          (((1 + 1 / 10000 : ℝ) * (X : ℝ) / 3 + 1) * (1 / 2) * (1 + 1 / 50000 : ℝ)) *
            ((∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (∑ m ∈ Finset.Icc A B, f m)) := by ring
    rw [hrearr]
    have hmul := mul_le_mul hpref hmid (mul_nonneg hPz_nn hsum_f_nn) (by positivity)
    have hrhs_eq :
        (1 + 1 / 50000 : ℝ) ^ 2 * ((1 + 1 / 10000 : ℝ) * (X : ℝ) / 6) *
          (((1 + 1 / 50000 : ℝ) ^ 2 + 1 / 50000 : ℝ) * ((X : ℝ) / 20000) *
            (16 * Real.exp (-2 * (5755 / 10000 : ℝ)) / (Real.log (X : ℝ)) ^ 2)) =
        ((1 + 1 / 50000 : ℝ) ^ 2 * ((1 + 1 / 50000 : ℝ) ^ 2 + 1 / 50000 : ℝ)) *
          ((4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) * M_val) := by
      dsimp [M_val]; ring
    linarith
  have hconst_le :
      (1 + 1 / 50000 : ℝ) ^ 2 * ((1 + 1 / 50000 : ℝ) ^ 2 + 1 / 50000 : ℝ) ≤ (1 + 1 / 5000 : ℝ) := by
    norm_num
  have hcomp := mul_le_mul_of_nonneg_right hconst_le
    (show 0 ≤ (4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) * M_val by positivity)
  have hgoal_eq :
      (1 + 1 / 5000 : ℝ) * ((4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) * M_val) =
        (1 + 1 / 5000 : ℝ) * (4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) *
          Real.exp (-2 * (5755 / 10000 : ℝ)) * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
    dsimp [M_val]; ring
  linarith [hsum_V, hfinal_mul, hcomp, hgoal_eq]

/-! ### Section 5: Lower bound on cube-root-rough semiprimes in an interval and pair sums -/

private lemma minFac_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    (p * q).minFac = p := by
  have h1 : p * q ≠ 1 := by have := hp.two_le; have := hq.two_le; nlinarith
  have hmp := Nat.minFac_prime h1
  have hdvd := Nat.minFac_dvd (p * q)
  have hle := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
  rcases hmp.dvd_mul.mp hdvd with hdp | hdq
  · exact (Nat.prime_dvd_prime_iff_eq hmp hp).mp hdp
  · have := (Nat.prime_dvd_prime_iff_eq hmp hq).mp hdq; omega

set_option maxHeartbeats 1200000 in
private lemma semiprime_Ioc_lower {c d η : ℝ} (hc : 0 < c) (hcd : c < d) (hd : d ≤ 3 / 4)
    (hη : 0 < η) (hη4 : η < 1 / 4) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      let z₁ := ⌊((X + X / 10000 : ℕ) : ℝ) ^ (1 / 3 : ℝ)⌋₊
      (1 - η) * (d - c) * Real.log 2 * (X : ℝ) / Real.log (X : ℝ) ≤
        (((Finset.Ioc ⌊c * (X : ℝ)⌋₊ ⌊d * (X : ℝ)⌋₊).filter
          (fun u => z₁ < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime)).card : ℝ) := by
  -- Choose small ρ > 0 so log(((1/2 - ρ)*(2/3 - ρ))/((1/3 + ρ)*(1/2 + ρ))) >= (1 - η/8) * log 2
  have hcont : ContinuousAt (fun ρ : ℝ =>
      Real.log (((1 / 2 - ρ) * (2 / 3 - ρ)) / ((1 / 3 + ρ) * (1 / 2 + ρ)))) 0 := by
    have hnum : ContinuousAt (fun ρ : ℝ => (1 / 2 - ρ) * (2 / 3 - ρ)) 0 :=
      (continuousAt_const.sub continuousAt_id).mul (continuousAt_const.sub continuousAt_id)
    have hden : ContinuousAt (fun ρ : ℝ => (1 / 3 + ρ) * (1 / 2 + ρ)) 0 :=
      (continuousAt_const.add continuousAt_id).mul (continuousAt_const.add continuousAt_id)
    exact (hnum.div hden (by norm_num)).log (by norm_num)
  have hval0 : Real.log (((1 / 2 - (0 : ℝ)) * (2 / 3 - 0)) / ((1 / 3 + 0) * (1 / 2 + 0))) = Real.log 2 := by
    norm_num
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnhds : ∀ᶠ ρ in 𝓝 (0 : ℝ),
      (1 - η / 8) * Real.log 2 <
        Real.log (((1 / 2 - ρ) * (2 / 3 - ρ)) / ((1 / 3 + ρ) * (1 / 2 + ρ))) := by
    have hlt : (1 - η / 8) * Real.log 2 < Real.log 2 := by nlinarith
    exact hcont.eventually (lt_mem_nhds (by dsimp only; rwa [hval0]))
  rw [Metric.eventually_nhds_iff] at hnhds
  obtain ⟨r₀, hr₀, hρ_all⟩ := hnhds
  set ρ : ℝ := min (r₀ / 2) (1 / 100)
  have hρ0 : 0 < ρ := lt_min (half_pos hr₀) (by norm_num)
  have hρ100 : ρ ≤ 1 / 100 := min_le_right _ _
  have hρ_log : (1 - η / 8) * Real.log 2 ≤
      Real.log (((1 / 2 - ρ) * (2 / 3 - ρ)) / ((1 / 3 + ρ) * (1 / 2 + ρ))) := by
    have hdist : dist ρ 0 < r₀ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hρ0]
      exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr₀)
    exact (hρ_all hdist).le
  set a₀ : ℝ := 1 / 3 + ρ
  set b₀ : ℝ := 1 / 2 - ρ
  have hab₀ : a₀ < b₀ := by dsimp [a₀, b₀]; linarith
  obtain ⟨K, hK⟩ := exists_nat_ge (max (100 * (b₀ - a₀) / η) 4)
  have hK1 : 1 ≤ K := by
    have : (4 : ℝ) ≤ K := (le_max_right _ _).trans hK
    exact_mod_cast (by linarith : (1 : ℝ) ≤ K)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  set h : ℝ := (b₀ - a₀) / (K : ℝ)
  have hh0 : 0 < h := div_pos (sub_pos.mpr hab₀) hK0
  have hh_small : (1 + 3 * h) * (1 + 2 * h) ≤ 1 / (1 - η / 8) := by
    have h1 : h ≤ η / 100 := by
      have hK_ge : 100 * (b₀ - a₀) / η ≤ (K : ℝ) := (le_max_left _ _).trans hK
      rw [div_le_iff₀ hη] at hK_ge
      dsimp [h]
      rw [div_le_iff₀ hK0]
      nlinarith
    rw [le_div_iff₀ (by linarith)]
    have h2 : 6 * h ^ 2 ≤ 6 * (η / 100) ^ 2 := by nlinarith
    nlinarith
  set δ : ℝ := min (η * (d - c) / (32 * (d + 1))) (η / 32)
  have hδ0 : 0 < δ := lt_min (div_pos (mul_pos hη (sub_pos.mpr hcd)) (by linarith)) (by linarith)
  have hδ2 : δ < 1 / 2 := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨Xθ, _, hθ⟩ := theta_eventually_bounds hδ0
  obtain ⟨Xp, hXp8, hsum_p⟩ := sum_log_div_prime_Ioc hδ0 hδ2
  -- Choose X large enough for all asymptotic inequalities
  have h_ev : ∀ᶠ X : ℕ in atTop,
      10000 ≤ X ∧
      (Xp : ℝ) + 2 ≤ (X : ℝ) ^ a₀ ∧
      (Xθ : ℝ) + 2 ≤ c * (X : ℝ) ^ (1 - b₀) ∧
      ((X + X / 10000 : ℕ) : ℝ) ^ (1 / 3 : ℝ) + 2 ≤ (X : ℝ) ^ a₀ ∧
      (X : ℝ) ^ b₀ + 2 ≤ c * (X : ℝ) ^ (1 - b₀) ∧
      (4 * δ + 2) / (h * Real.log (X : ℝ)) ≤ δ / 2 ∧
      2 / ((X : ℝ) ^ a₀ * h * Real.log (X : ℝ)) ≤ δ / 2 := by
    have hpow_a : Tendsto (fun X : ℕ => (X : ℝ) ^ a₀) atTop atTop :=
      (tendsto_rpow_atTop (by dsimp [a₀]; linarith)).comp tendsto_natCast_atTop_atTop
    have hpow_1b : Tendsto (fun X : ℕ => (X : ℝ) ^ (1 - b₀)) atTop atTop :=
      (tendsto_rpow_atTop (by dsimp [b₀]; linarith)).comp tendsto_natCast_atTop_atTop
    have hlog_t : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hratio1 : Tendsto (fun X : ℕ => (X : ℝ) ^ ρ) atTop atTop :=
      (tendsto_rpow_atTop hρ0).comp tendsto_natCast_atTop_atTop
    have hratio2 : Tendsto (fun X : ℕ => (X : ℝ) ^ (2 * ρ)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 10000,
      hpow_a.eventually (eventually_ge_atTop ((Xp : ℝ) + 2)),
      hpow_1b.eventually (eventually_ge_atTop (((Xθ : ℝ) + 2) / c)),
      hratio1.eventually (eventually_ge_atTop (4 : ℝ)),
      hratio2.eventually (eventually_ge_atTop (4 / c)),
      hlog_t.eventually (eventually_ge_atTop ((4 * δ + 2) / (h * (δ / 2)))),
      hpow_a.eventually (eventually_ge_atTop (2 / (h * (δ / 2))))]
      with X hX1 hX2 hX3 hX4 hX5 hX6 hX7
    have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hX1r : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    have hlogX_ge1 : 1 ≤ Real.log (X : ℝ) := by
      have : Real.exp 1 ≤ (X : ℝ) := by
        have hb := Real.exp_bound' (by norm_num : (0 : ℝ) ≤ 1) le_rfl (by decide : (0 : ℕ) < 4)
        simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hb
        have : (10000 : ℝ) ≤ X := by exact_mod_cast hX1
        norm_num at hb; linarith
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log (X : ℝ) := Real.log_le_log (Real.exp_pos 1) this
    refine ⟨hX1, hX2, ?_, ?_, ?_, ?_, ?_⟩
    · have := (div_le_iff₀ hc).mp hX3; linarith
    · have h2X : ((X + X / 10000 : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
        have : X + X / 10000 ≤ 2 * X := by omega
        exact_mod_cast this
      have h1 : ((X + X / 10000 : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) * (X : ℝ) ^ (1 / 3 : ℝ) := by
        have h := Real.rpow_le_rpow (Nat.cast_nonneg _) h2X (show (0 : ℝ) ≤ 1 / 3 by norm_num)
        rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg X)] at h
        have h2r : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
          calc (2 : ℝ) ^ (1 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
        nlinarith [Real.rpow_nonneg (Nat.cast_nonneg X) (1 / 3 : ℝ)]
      have h2 : (X : ℝ) ^ a₀ = (X : ℝ) ^ (1 / 3 : ℝ) * (X : ℝ) ^ ρ := by
        dsimp [a₀]; rw [Real.rpow_add hXpos]
      have h3 : (1 : ℝ) ≤ (X : ℝ) ^ (1 / 3 : ℝ) := Real.one_le_rpow hX1r (by norm_num)
      rw [h2]; nlinarith
    · have h1 : (X : ℝ) ^ (1 - b₀) = (X : ℝ) ^ b₀ * (X : ℝ) ^ (2 * ρ) := by
        rw [← Real.rpow_add hXpos]; congr 1; dsimp [b₀]; ring
      have h2 : (4 : ℝ) ≤ c * (X : ℝ) ^ (2 * ρ) := by
        have := (div_le_iff₀ hc).mp hX5; linarith
      have h3 : (1 : ℝ) ≤ (X : ℝ) ^ b₀ := Real.one_le_rpow hX1r (by dsimp [b₀]; linarith)
      rw [h1]; nlinarith
    · rw [div_le_iff₀ (mul_pos hh0 (by linarith))]
      have := (div_le_iff₀ (mul_pos hh0 (half_pos hδ0))).mp hX6
      linarith
    · rw [div_le_iff₀ (mul_pos (mul_pos (Real.rpow_pos_of_pos hXpos _) hh0) (by linarith))]
      have := (div_le_iff₀ (mul_pos hh0 (half_pos hδ0))).mp hX7
      have h1 : (2 : ℝ) ≤ (X : ℝ) ^ a₀ * h * (δ / 2) := by linarith
      have h2 : (X : ℝ) ^ a₀ * h * (δ / 2) ≤ (X : ℝ) ^ a₀ * h * Real.log (X : ℝ) * (δ / 2) := by
        have : 0 ≤ (X : ℝ) ^ a₀ * h * (δ / 2) := by positivity
        nlinarith
      linarith
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp h_ev
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨hX10000, hXpX, hXθX, hz1_lt, hbp_lt, herr1, herr2⟩ := hX₀ X hX
  set z₁ : ℕ := ⌊((X + X / 10000 : ℕ) : ℝ) ^ (1 / 3 : ℝ)⌋₊
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hX1 : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hX1
  let t : ℕ → ℝ := fun j => a₀ + (j : ℝ) * h
  let N : ℕ → ℕ := fun j => ⌊(X : ℝ) ^ (t j)⌋₊
  let P_all : Finset ℕ := (Finset.Ioc (N 0) (N K)).filter Nat.Prime
  let Q : ℕ → Finset ℕ := fun p => (Finset.Ioc ⌊c * (X : ℝ) / (p : ℝ)⌋₊ ⌊d * (X : ℝ) / (p : ℝ)⌋₊).filter Nat.Prime
  -- Inject Sigma p ∈ P_all, Q p into the target finset via (p, q) ↦ p * q
  have h_inj_card :
      ∑ p ∈ P_all, (Q p).card ≤
        ((Finset.Ioc ⌊c * (X : ℝ)⌋₊ ⌊d * (X : ℝ)⌋₊).filter
          (fun u => z₁ < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime)).card := by
    rw [← Finset.card_sigma]
    have ht0 : t 0 = a₀ := by dsimp [t]; ring
    have htK : t K = b₀ := by dsimp [t, h]; field_simp; ring
    have hp_bounds : ∀ p ∈ P_all, Nat.Prime p ∧ z₁ < p ∧ (X : ℝ) ^ a₀ < (p : ℝ) ∧ (p : ℝ) ≤ (X : ℝ) ^ b₀ := by
      intro p hp
      have hf := Finset.mem_filter.mp hp
      have hi := Finset.mem_Ioc.mp hf.1
      have hp_gt : (X : ℝ) ^ a₀ < (p : ℝ) := by
        have h1 : (X : ℝ) ^ (t 0) < (N 0 : ℝ) + 1 := Nat.lt_floor_add_one _
        rw [ht0] at h1
        have h2 : (N 0 : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast (show N 0 + 1 ≤ p by omega)
        linarith
      have hp_le : (p : ℝ) ≤ (X : ℝ) ^ b₀ := by
        have h1 : (N K : ℝ) ≤ (X : ℝ) ^ (t K) := Nat.floor_le (Real.rpow_nonneg hXpos.le _)
        rw [htK] at h1
        exact (Nat.cast_le.mpr hi.2).trans h1
      have hz1_p : z₁ < p := by
        have h1 : (z₁ : ℝ) ≤ ((X + X / 10000 : ℕ) : ℝ) ^ (1 / 3 : ℝ) :=
          Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        have h2 : (z₁ : ℝ) < (p : ℝ) := by linarith
        exact_mod_cast h2
      exact ⟨hf.2, hz1_p, hp_gt, hp_le⟩
    have hq_bounds : ∀ p ∈ P_all, ∀ q ∈ Q p,
        Nat.Prime q ∧ p ≤ q ∧ p * q ∈ Finset.Ioc ⌊c * (X : ℝ)⌋₊ ⌊d * (X : ℝ)⌋₊ := by
      intro p hp q hq
      obtain ⟨hp_pr, _, _, hp_le⟩ := hp_bounds p hp
      have hqf := Finset.mem_filter.mp hq
      have hqi := Finset.mem_Ioc.mp hqf.1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp_pr.pos
      have hq_gt : c * (X : ℝ) / (p : ℝ) < (q : ℝ) := by
        have h1 := Nat.lt_floor_add_one (c * (X : ℝ) / (p : ℝ))
        have h2 : (⌊c * (X : ℝ) / (p : ℝ)⌋₊ : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast (show _ + 1 ≤ q by omega)
        linarith
      have hq_le : (q : ℝ) ≤ d * (X : ℝ) / (p : ℝ) :=
        (Nat.cast_le.mpr hqi.2).trans (Nat.floor_le (by have hd0 : 0 < d := hc.trans hcd; positivity))
      have hpq_lt : p ≤ q := by
        have h1 : c * (X : ℝ) ^ (1 - b₀) ≤ c * (X : ℝ) / (p : ℝ) := by
          rw [le_div_iff₀ hp0]
          have heq : (X : ℝ) ^ (1 - b₀) * (X : ℝ) ^ b₀ = (X : ℝ) := by
            rw [← Real.rpow_add hXpos]; norm_num
          have := mul_le_mul_of_nonneg_left hp_le (show 0 ≤ c * (X : ℝ) ^ (1 - b₀) by positivity)
          linarith [show c * (X : ℝ) ^ (1 - b₀) * (X : ℝ) ^ b₀ = c * (X : ℝ) by
            rw [mul_assoc, heq]]
        have h2 : (p : ℝ) < (q : ℝ) := by linarith
        exact_mod_cast h2.le
      have hmem_Ioc : p * q ∈ Finset.Ioc ⌊c * (X : ℝ)⌋₊ ⌊d * (X : ℝ)⌋₊ := by
        rw [Finset.mem_Ioc]
        have hlow : c * (X : ℝ) < ((p * q : ℕ) : ℝ) := by
          rw [Nat.cast_mul]; exact (div_lt_iff₀ hp0).mp hq_gt |> fun h => by linarith
        have hhi : ((p * q : ℕ) : ℝ) ≤ d * (X : ℝ) := by
          rw [Nat.cast_mul]; exact (le_div_iff₀ hp0).mp hq_le |> fun h => by linarith
        constructor
        · have hfl : (⌊c * (X : ℝ)⌋₊ : ℝ) ≤ c * (X : ℝ) := Nat.floor_le (by positivity)
          exact_mod_cast (hfl.trans_lt hlow)
        · exact Nat.le_floor hhi
      exact ⟨hqf.2, hpq_lt, hmem_Ioc⟩
    apply Finset.card_le_card_of_injOn (fun x : Σ _ : ℕ, ℕ => x.1 * x.2)
    · rintro ⟨p, q⟩ hx
      rw [Finset.mem_coe, Finset.mem_sigma] at hx
      dsimp only at hx
      obtain ⟨hp, hq⟩ := hx
      obtain ⟨hp_pr, hz1_p, _, _⟩ := hp_bounds p hp
      obtain ⟨hq_pr, hpq, hmem⟩ := hq_bounds p hp q hq
      rw [Finset.mem_coe, Finset.mem_filter]
      dsimp only
      rw [minFac_mul_primes hp_pr hq_pr hpq, Nat.mul_div_cancel_left _ hp_pr.pos]
      exact ⟨hmem, hz1_p, hp_pr, hq_pr⟩
    · rintro ⟨p1, q1⟩ h1 ⟨p2, q2⟩ h2 heq
      rw [Finset.mem_coe, Finset.mem_sigma] at h1 h2
      dsimp only at h1 h2
      obtain ⟨hp1, hq1⟩ := h1
      obtain ⟨hp2, hq2⟩ := h2
      obtain ⟨hp1_pr, _, _, _⟩ := hp_bounds p1 hp1
      obtain ⟨hp2_pr, _, _, _⟩ := hp_bounds p2 hp2
      obtain ⟨hq1_pr, hpq1, _⟩ := hq_bounds p1 hp1 q1 hq1
      obtain ⟨hq2_pr, hpq2, _⟩ := hq_bounds p2 hp2 q2 hq2
      change p1 * q1 = p2 * q2 at heq
      have hmf := congrArg Nat.minFac heq
      rw [minFac_mul_primes hp1_pr hq1_pr hpq1, minFac_mul_primes hp2_pr hq2_pr hpq2] at hmf
      subst hmf
      exact congrArg (Sigma.mk p1) (Nat.eq_of_mul_eq_mul_left hp1_pr.pos heq)
  -- Split P_all into K subintervals
  have hN_mono : ∀ j : ℕ, N j ≤ N (j + 1) := by
    intro j
    apply Nat.floor_mono
    apply Real.rpow_le_rpow_of_exponent_le hX1.le
    dsimp [t]; push_cast; linarith
  have hsplit :
      ∑ p ∈ P_all, ((Q p).card : ℝ) =
        ∑ j ∈ Finset.range K,
          ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, ((Q p).card : ℝ) := by
    have haux : ∀ m : ℕ,
        ∑ p ∈ (Finset.Ioc (N 0) (N m)).filter Nat.Prime, ((Q p).card : ℝ) =
          ∑ j ∈ Finset.range m,
            ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, ((Q p).card : ℝ) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        have hN0m : N 0 ≤ N m := by
          apply Nat.floor_mono
          apply Real.rpow_le_rpow_of_exponent_le hX1.le
          dsimp [t]
          simp only [Nat.cast_zero, zero_mul, add_zero]
          have h0 : 0 ≤ (m : ℝ) * h := by positivity
          linarith
        rw [Finset.sum_range_succ, ← ih, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
        exact (Finset.sum_Ioc_consecutive _ hN0m (hN_mono m)).symm
    exact haux K
  -- Lower bound each block j ∈ range K
  have hblock : ∀ j ∈ Finset.range K,
      ((1 - δ) * d - (1 + δ) * c) * (1 - 2 * δ) * ((X : ℝ) / Real.log (X : ℝ)) *
          (h / (t (j + 1) * (1 - t j))) ≤
        ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, ((Q p).card : ℝ) := by
    intro j hj
    have hjK : j < K := Finset.mem_range.mp hj
    have htj_ge : a₀ ≤ t j := by
      dsimp [t]
      have h0 : 0 ≤ (j : ℝ) * h := by positivity
      linarith
    have htj1_le : t (j + 1) ≤ b₀ := by
      dsimp [t, h]
      have hj1 : ((j + 1 : ℕ) : ℝ) ≤ K := by exact_mod_cast (show j + 1 ≤ K by omega)
      have : ((j + 1 : ℕ) : ℝ) * ((b₀ - a₀) / (K : ℝ)) ≤ b₀ - a₀ := by
        rw [mul_div_assoc', div_le_iff₀ hK0]; nlinarith
      linarith
    have h1tj_pos : 0 < 1 - t j := by
      have : t j ≤ b₀ := le_trans (by dsimp [t]; push_cast; linarith) htj1_le
      dsimp [b₀] at this; linarith
    have htj1_pos : 0 < t (j + 1) := by
      have : a₀ ≤ t (j + 1) := le_trans htj_ge (by dsimp [t]; push_cast; linarith)
      dsimp [a₀] at this; linarith
    -- For each p in block j, lower bound (Q p).card
    have hQ_pt : ∀ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime,
        (((1 - δ) * d - (1 + δ) * c) / (1 - t j)) * ((X : ℝ) / Real.log (X : ℝ)) * (1 / (p : ℝ)) ≤
          ((Q p).card : ℝ) := by
      intro p hp
      have hpf := Finset.mem_filter.mp hp
      have hpi := Finset.mem_Ioc.mp hpf.1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpf.2.pos
      have hp_gt : (X : ℝ) ^ (t j) < (p : ℝ) := by
        have h1 := Nat.lt_floor_add_one ((X : ℝ) ^ (t j))
        have h2 : (N j : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast (show N j + 1 ≤ p by omega)
        linarith
      have hp_le : (p : ℝ) ≤ (X : ℝ) ^ b₀ := by
        have h1 : (p : ℝ) ≤ (X : ℝ) ^ (t (j + 1)) :=
          (Nat.cast_le.mpr hpi.2).trans (Nat.floor_le (Real.rpow_nonneg hXpos.le _))
        exact h1.trans (Real.rpow_le_rpow_of_exponent_le hX1.le htj1_le)
      have hcXp : (Xθ : ℝ) ≤ c * (X : ℝ) / (p : ℝ) := by
        have h1 : c * (X : ℝ) ^ (1 - b₀) ≤ c * (X : ℝ) / (p : ℝ) := by
          rw [le_div_iff₀ hp0]
          have heq : (X : ℝ) ^ (1 - b₀) * (X : ℝ) ^ b₀ = (X : ℝ) := by
            rw [← Real.rpow_add hXpos]; norm_num
          have := mul_le_mul_of_nonneg_left hp_le (show 0 ≤ c * (X : ℝ) ^ (1 - b₀) by positivity)
          linarith [show c * (X : ℝ) ^ (1 - b₀) * (X : ℝ) ^ b₀ = c * (X : ℝ) by rw [mul_assoc, heq]]
        linarith
      have hdXp : (Xθ : ℝ) ≤ d * (X : ℝ) / (p : ℝ) := by
        exact hcXp.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcd.le hXpos.le) hp0.le)
      have hθ_hi := (hθ (d * (X : ℝ) / (p : ℝ)) hdXp).1
      have hθ_lo := (hθ (c * (X : ℝ) / (p : ℝ)) hcXp).2
      have hdiff_theta :
          ((1 - δ) * d - (1 + δ) * c) * ((X : ℝ) / (p : ℝ)) ≤
            Chebyshev.theta (d * (X : ℝ) / (p : ℝ)) - Chebyshev.theta (c * (X : ℝ) / (p : ℝ)) := by
        linarith [show (1 - δ) * (d * (X : ℝ) / (p : ℝ)) - (1 + δ) * (c * (X : ℝ) / (p : ℝ)) =
          ((1 - δ) * d - (1 + δ) * c) * ((X : ℝ) / (p : ℝ)) by ring]
      have htheta_eq :
          Chebyshev.theta (d * (X : ℝ) / (p : ℝ)) - Chebyshev.theta (c * (X : ℝ) / (p : ℝ)) =
            ∑ q ∈ Q p, Real.log (q : ℝ) := by
        rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE]
        have hsub : Nat.primesLE ⌊c * (X : ℝ) / (p : ℝ)⌋₊ ⊆ Nat.primesLE ⌊d * (X : ℝ) / (p : ℝ)⌋₊ :=
          Nat.primesLE_mono (Nat.floor_mono (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcd.le hXpos.le) hp0.le))
        rw [← Finset.sum_sdiff_eq_sub hsub]
        congr 1
        ext q
        simp only [Q, Finset.mem_sdiff, Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨hqd, hqp⟩, hnot⟩
          exact ⟨⟨by by_contra hle; push_neg at hle; exact hnot ⟨hle, hqp⟩, hqd⟩, hqp⟩
        · rintro ⟨⟨hgt, hqd⟩, hqp⟩
          exact ⟨⟨hqd, hqp⟩, fun h => by omega⟩
      have hsum_log :
          ∑ q ∈ Q p, Real.log (q : ℝ) ≤ ((Q p).card : ℝ) * ((1 - t j) * Real.log (X : ℝ)) := by
        have hd0 : 0 < d := hc.trans hcd
        calc ∑ q ∈ Q p, Real.log (q : ℝ)
            ≤ ∑ _q ∈ Q p, ((1 - t j) * Real.log (X : ℝ)) := by
              apply Finset.sum_le_sum
              intro q hq
              have hqf := Finset.mem_filter.mp hq
              have hq_le : (q : ℝ) ≤ d * (X : ℝ) / (p : ℝ) :=
                (Nat.cast_le.mpr (Finset.mem_Ioc.mp hqf.1).2).trans (Nat.floor_le (by positivity))
              have hq_le2 : (q : ℝ) ≤ (X : ℝ) ^ (1 - t j) := by
                have h1 : d * (X : ℝ) / (p : ℝ) ≤ (X : ℝ) / (X : ℝ) ^ (t j) := by
                  apply div_le_div₀ (by positivity) (by nlinarith) (Real.rpow_pos_of_pos hXpos _) hp_gt.le
                have h2 : (X : ℝ) / (X : ℝ) ^ (t j) = (X : ℝ) ^ (1 - t j) := by
                  rw [Real.rpow_sub hXpos, Real.rpow_one]
                linarith
              have hlog := Real.log_le_log (by exact_mod_cast hqf.2.pos) hq_le2
              rwa [Real.log_rpow hXpos] at hlog
          _ = ((Q p).card : ℝ) * ((1 - t j) * Real.log (X : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      have hdiv := (div_le_iff₀ (mul_pos h1tj_pos hlogX)).mpr (hdiff_theta.trans (htheta_eq ▸ hsum_log))
      calc (((1 - δ) * d - (1 + δ) * c) / (1 - t j)) * ((X : ℝ) / Real.log (X : ℝ)) * (1 / (p : ℝ))
          = ((1 - δ) * d - (1 + δ) * c) * ((X : ℝ) / (p : ℝ)) / ((1 - t j) * Real.log (X : ℝ)) := by
            field_simp
        _ ≤ ((Q p).card : ℝ) := hdiv
    have hsum1 := Finset.sum_le_sum hQ_pt
    rw [← Finset.mul_sum] at hsum1
    -- Lower bound ∑ p in block j, 1 / p >= (1 - 2 * δ) * h / t (j + 1)
    have hinv_p :
        (1 - 2 * δ) * (h / t (j + 1)) ≤
          ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, (1 : ℝ) / (p : ℝ) := by
      have hpt2 : ∀ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime,
          (1 / (t (j + 1) * Real.log (X : ℝ))) * (Real.log (p : ℝ) / (p : ℝ)) ≤ (1 : ℝ) / (p : ℝ) := by
        intro p hp
        have hpf := Finset.mem_filter.mp hp
        have hp_le : (p : ℝ) ≤ (X : ℝ) ^ (t (j + 1)) :=
          (Nat.cast_le.mpr (Finset.mem_Ioc.mp hpf.1).2).trans (Nat.floor_le (Real.rpow_nonneg hXpos.le _))
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hpf.2.pos
        have hlogp := Real.log_le_log hp0 hp_le
        rw [Real.log_rpow hXpos] at hlogp
        have h1 : Real.log (p : ℝ) / (t (j + 1) * Real.log (X : ℝ)) ≤ 1 :=
          (div_le_one (mul_pos htj1_pos hlogX)).mpr hlogp
        calc (1 / (t (j + 1) * Real.log (X : ℝ))) * (Real.log (p : ℝ) / (p : ℝ))
            = (Real.log (p : ℝ) / (t (j + 1) * Real.log (X : ℝ))) * (1 / (p : ℝ)) := by ring
          _ ≤ 1 * (1 / (p : ℝ)) := mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = 1 / (p : ℝ) := one_mul _
      have hsum2 := Finset.sum_le_sum hpt2
      rw [← Finset.mul_sum] at hsum2
      have hNjX : Xp ≤ N j := by
        have h1 : (X : ℝ) ^ a₀ ≤ (X : ℝ) ^ (t j) := Real.rpow_le_rpow_of_exponent_le hX1.le htj_ge
        have h2 := Nat.sub_one_lt_floor ((X : ℝ) ^ (t j))
        have h3 : (Xp : ℝ) ≤ (N j : ℝ) := by linarith
        exact_mod_cast h3
      have hlog_sum := (hsum_p (N j) (N (j + 1)) hNjX (hN_mono j)).1
      have hratio : h * Real.log (X : ℝ) - 2 / ((X : ℝ) ^ a₀) ≤
          Real.log ((N (j + 1) : ℝ) / (N j : ℝ)) := by
        have hnum : (X : ℝ) ^ (t (j + 1)) - 1 < (N (j + 1) : ℝ) := Nat.sub_one_lt_floor _
        have hden : (N j : ℝ) ≤ (X : ℝ) ^ (t j) := Nat.floor_le (Real.rpow_nonneg hXpos.le _)
        have hNj_pos : 0 < (N j : ℝ) := by exact_mod_cast (show 0 < N j by omega)
        have hnum_pos : 0 < (X : ℝ) ^ (t (j + 1)) - 1 := by
          have h1 : (X : ℝ) ^ a₀ ≤ (X : ℝ) ^ (t (j + 1)) :=
            Real.rpow_le_rpow_of_exponent_le hX1.le (le_trans htj_ge (by dsimp [t]; push_cast; linarith))
          have hXp8r : (8 : ℝ) ≤ Xp := by exact_mod_cast hXp8
          linarith
        have hle1 : ((X : ℝ) ^ (t (j + 1)) - 1) / ((X : ℝ) ^ (t j)) ≤ (N (j + 1) : ℝ) / (N j : ℝ) :=
          div_le_div₀ (Nat.cast_nonneg _) hnum.le hNj_pos hden
        have hle2 := Real.log_le_log (div_pos hnum_pos (Real.rpow_pos_of_pos hXpos _)) hle1
        have hpow_eq : ((X : ℝ) ^ (t (j + 1)) - 1) / ((X : ℝ) ^ (t j)) =
            (X : ℝ) ^ h * (1 - ((X : ℝ) ^ (t (j + 1)))⁻¹) := by
          have ht_add : t (j + 1) = t j + h := by dsimp [t]; push_cast; ring
          rw [ht_add, Real.rpow_add hXpos]
          have h1 : (X : ℝ) ^ (t j) ≠ 0 := (Real.rpow_pos_of_pos hXpos _).ne'
          have h2 : (X : ℝ) ^ h ≠ 0 := (Real.rpow_pos_of_pos hXpos _).ne'
          field_simp
        have hge2 : (2 : ℝ) ≤ (X : ℝ) ^ (t (j + 1)) := by
          have h1 : (X : ℝ) ^ a₀ ≤ (X : ℝ) ^ (t (j + 1)) :=
            Real.rpow_le_rpow_of_exponent_le hX1.le (le_trans htj_ge (by dsimp [t]; push_cast; linarith))
          have hXp8r : (8 : ℝ) ≤ Xp := by exact_mod_cast hXp8
          linarith
        rw [hpow_eq, Real.log_mul (Real.rpow_pos_of_pos hXpos _).ne'
          (sub_pos.mpr (inv_lt_one_of_one_lt₀ (by linarith))).ne', Real.log_rpow hXpos] at hle2
        have hinv_le : ((X : ℝ) ^ (t (j + 1)))⁻¹ ≤ 1 / 2 :=
          inv_le_of_inv_le₀ (by norm_num) (by simpa using hge2)
        have hneg := neg_log_one_sub_le (inv_nonneg.mpr (Real.rpow_nonneg hXpos.le _))
          (lt_of_le_of_lt hinv_le (by norm_num))
        have h2b : ((X : ℝ) ^ (t (j + 1)))⁻¹ / (1 - ((X : ℝ) ^ (t (j + 1)))⁻¹) ≤ 2 / ((X : ℝ) ^ a₀) := by
          have h1 : (1 / 2 : ℝ) ≤ 1 - ((X : ℝ) ^ (t (j + 1)))⁻¹ := by linarith
          have h2 : ((X : ℝ) ^ (t (j + 1)))⁻¹ ≤ ((X : ℝ) ^ a₀)⁻¹ :=
            inv_anti₀ (Real.rpow_pos_of_pos hXpos _)
              (Real.rpow_le_rpow_of_exponent_le hX1.le (le_trans htj_ge (by dsimp [t]; push_cast; linarith)))
          calc _ ≤ ((X : ℝ) ^ (t (j + 1)))⁻¹ / (1 / 2) :=
                div_le_div_of_nonneg_left (inv_nonneg.mpr (Real.rpow_nonneg hXpos.le _)) (by norm_num) h1
            _ = 2 * ((X : ℝ) ^ (t (j + 1)))⁻¹ := by ring
            _ ≤ 2 * ((X : ℝ) ^ a₀)⁻¹ := mul_le_mul_of_nonneg_left h2 (by norm_num)
            _ = 2 / ((X : ℝ) ^ a₀) := by rw [div_eq_mul_inv]
        linarith
      have hNj2 : 2 / (N j : ℝ) ≤ 2 := by
        have h1 : (1 : ℝ) ≤ (N j : ℝ) := by exact_mod_cast (show 1 ≤ N j by omega)
        rw [div_le_iff₀ (by linarith)]; linarith
      have hcomb :
          (1 - 2 * δ) * (h * Real.log (X : ℝ)) ≤
            ∑ p ∈ (Finset.Ioc (N j) (N (j + 1))).filter Nat.Prime, Real.log (p : ℝ) / (p : ℝ) := by
        have h1 := mul_le_mul_of_nonneg_left hratio (show (0 : ℝ) ≤ 1 - δ by linarith)
        have h2 : (4 * δ + 2) ≤ (δ / 2) * (h * Real.log (X : ℝ)) :=
          (div_le_iff₀ (mul_pos hh0 hlogX)).mp herr1
        have h3 : 2 / ((X : ℝ) ^ a₀) ≤ (δ / 2) * (h * Real.log (X : ℝ)) := by
          have := (div_le_iff₀ (mul_pos (mul_pos (Real.rpow_pos_of_pos hXpos _) hh0) hlogX)).mp herr2
          rw [div_le_iff₀ (Real.rpow_pos_of_pos hXpos _)]
          linarith
        have h4 : (1 - δ) * (2 / ((X : ℝ) ^ a₀)) ≤ 2 / ((X : ℝ) ^ a₀) := by
          have hpos : 0 ≤ 2 / ((X : ℝ) ^ a₀) := by positivity
          nlinarith only [hδ0, hpos]
        linarith
      have hmul2 := (mul_le_mul_of_nonneg_left hcomb (show 0 ≤ 1 / (t (j + 1) * Real.log (X : ℝ)) by positivity)).trans hsum2
      calc (1 - 2 * δ) * (h / t (j + 1))
          = (1 / (t (j + 1) * Real.log (X : ℝ))) * ((1 - 2 * δ) * (h * Real.log (X : ℝ))) := by field_simp
        _ ≤ _ := hmul2
    have hcoeff_nn : 0 ≤ (((1 - δ) * d - (1 + δ) * c) / (1 - t j)) * ((X : ℝ) / Real.log (X : ℝ)) := by
      have hdc : 0 ≤ (1 - δ) * d - (1 + δ) * c := by
        have hδ_dc : δ ≤ η * (d - c) / (32 * (d + 1)) := min_le_left _ _
        have h1 : δ * (d + c) ≤ (d - c) / 2 := by
          have h2 : δ * (d + 1) ≤ η * (d - c) / 32 := by
            have := (le_div_iff₀ (show (0 : ℝ) < 32 * (d + 1) by linarith)).mp hδ_dc
            linarith
          have h3 : d + c ≤ 2 * (d + 1) := by linarith
          nlinarith only [hδ0, hη4, hcd, h2, h3]
        linarith
      exact mul_nonneg (div_nonneg hdc h1tj_pos.le) (div_nonneg hXpos.le hlogX.le)
    have hmul := (mul_le_mul_of_nonneg_left hinv_p hcoeff_nn).trans hsum1
    calc ((1 - δ) * d - (1 + δ) * c) * (1 - 2 * δ) * ((X : ℝ) / Real.log (X : ℝ)) *
            (h / (t (j + 1) * (1 - t j)))
        = (((1 - δ) * d - (1 + δ) * c) / (1 - t j)) * ((X : ℝ) / Real.log (X : ℝ)) *
            ((1 - 2 * δ) * (h / t (j + 1))) := by field_simp
      _ ≤ _ := hmul
  -- Sum over j ∈ range K and telescope via MVT on F(s) = log(s / (1 - s))
  have hsum_K := Finset.sum_le_sum hblock
  rw [← Finset.mul_sum] at hsum_K
  let F : ℝ → ℝ := fun s => Real.log (s / (1 - s))
  have hFderiv : ∀ s : ℝ, 0 < s → s < 1 → HasDerivAt F (1 / (s * (1 - s))) s := by
    intro s hs0 hs1
    dsimp [F]
    have hsub : HasDerivAt (fun x : ℝ => 1 - x) (-1) s :=
      ((hasDerivAt_id s).const_sub (1 : ℝ)).congr_deriv (by ring)
    have h1 : HasDerivAt (fun x : ℝ => x / (1 - x)) (1 / (1 - s) ^ 2) s :=
      ((hasDerivAt_id s).fun_div hsub (by linarith)).congr_deriv (by simp only [id_eq]; field_simp; ring)
    exact (h1.log (div_pos hs0 (by linarith)).ne').congr_deriv (by
      have hs0' : s ≠ 0 := hs0.ne'
      have h1s' : 1 - s ≠ 0 := by linarith
      field_simp)
  have hFbFa_eq : F b₀ - F a₀ = Real.log (b₀ * (2 / 3 - ρ) / (a₀ * (1 / 2 + ρ))) := by
    dsimp [F]
    have ha0_pos : 0 < a₀ := by dsimp [a₀]; linarith
    have hb0_pos : 0 < b₀ := by dsimp [b₀]; linarith
    have h1a : 1 - a₀ = 2 / 3 - ρ := by dsimp [a₀]; ring
    have h1b : 1 - b₀ = 1 / 2 + ρ := by dsimp [b₀]; ring
    have h1a_pos : 0 < 1 - a₀ := by rw [h1a]; linarith
    have h1b_pos : 0 < 1 - b₀ := by rw [h1b]; linarith
    rw [← Real.log_div (div_pos hb0_pos h1b_pos).ne' (div_pos ha0_pos h1a_pos).ne']
    congr 1
    rw [h1a, h1b]
    have ha0_ne : a₀ ≠ 0 := ha0_pos.ne'
    have h1a_ne : 2 / 3 - ρ ≠ 0 := by linarith
    have h1b_ne : 1 / 2 + ρ ≠ 0 := by linarith
    field_simp
  have hriem_log :
      (1 - η / 8) * (F b₀ - F a₀) ≤ ∑ j ∈ Finset.range K, h / (t (j + 1) * (1 - t j)) := by
    have hstep_F : ∀ j ∈ Finset.range K,
        F (t (j + 1)) - F (t j) ≤ (1 + 3 * h) * (1 + 2 * h) * (h / (t (j + 1) * (1 - t j))) := by
      intro j hj
      have hjK : j < K := Finset.mem_range.mp hj
      have hlt : t j < t (j + 1) := by dsimp [t]; push_cast; linarith
      have htj_ge : 1 / 3 ≤ t j := by
        dsimp [t, a₀]
        have h0 : 0 ≤ (j : ℝ) * h := by positivity
        linarith
      have htj1_le : t (j + 1) ≤ 1 / 2 := by
        have hj1 : ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show j + 1 ≤ K by omega)
        have hmul_le : ((j + 1 : ℕ) : ℝ) * h ≤ b₀ - a₀ := by
          calc ((j + 1 : ℕ) : ℝ) * h ≤ (K : ℝ) * h := mul_le_mul_of_nonneg_right hj1 hh0.le
            _ = b₀ - a₀ := by dsimp [h]; exact mul_div_cancel₀ _ hK0.ne'
        dsimp [t, b₀] at hmul_le ⊢
        linarith
      obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope F (fun s => 1 / (s * (1 - s))) hlt
        (fun s hs => (hFderiv s (by linarith [hs.1]) (by linarith [hs.2])).continuousAt.continuousWithinAt)
        (fun s hs => hFderiv s (by linarith [hs.1]) (by linarith [hs.2]))
      have hdiff : t (j + 1) - t j = h := by dsimp [t]; push_cast; ring
      have hFeq : F (t (j + 1)) - F (t j) = h / (ξ * (1 - ξ)) := by
        have := sub_eq_mul_of_div_eq (sub_ne_zero.mpr hlt.ne') hslope.symm
        rw [hdiff] at this; linarith [show h * (1 / (ξ * (1 - ξ))) = h / (ξ * (1 - ξ)) by ring]
      rw [hFeq]
      have h1 : t (j + 1) ≤ (1 + 3 * h) * ξ := by
        have hξ_ge : 1 / 3 ≤ ξ := le_trans htj_ge hξ.1.le
        have hle : t (j + 1) ≤ ξ + h := by linarith [hξ.1]
        nlinarith only [hξ_ge, hle, hh0]
      have h2 : 1 - t j ≤ (1 + 2 * h) * (1 - ξ) := by
        have h1ξ_ge : 1 / 2 ≤ 1 - ξ := by linarith [hξ.2]
        have hle : 1 - t j ≤ (1 - ξ) + h := by linarith [hξ.2]
        nlinarith only [h1ξ_ge, hle, hh0]
      have hmul_den : t (j + 1) * (1 - t j) ≤ (1 + 3 * h) * (1 + 2 * h) * (ξ * (1 - ξ)) := by
        have hξ_nn : 0 ≤ (1 + 3 * h) * ξ := mul_nonneg (by linarith) (by linarith [hξ.1])
        have := mul_le_mul h1 h2 (by linarith [hξ.2]) hξ_nn
        linarith
      have hpos1 : 0 < ξ * (1 - ξ) := mul_pos (by linarith [hξ.1]) (by linarith [hξ.2])
      have hpos2 : 0 < t (j + 1) * (1 - t j) := mul_pos (by linarith) (by linarith)
      rw [mul_div_assoc', div_le_div_iff₀ hpos1 hpos2]
      nlinarith only [hh0, hmul_den]
    have htel : ∑ j ∈ Finset.range K, (F (t (j + 1)) - F (t j)) = F b₀ - F a₀ := by
      have haux : ∀ m : ℕ, ∑ j ∈ Finset.range m, (F (t (j + 1)) - F (t j)) = F (t m) - F (t 0) := by
        intro m
        induction m with
        | zero => simp
        | succ m ih => rw [Finset.sum_range_succ, ih]; ring
      rw [haux K]
      have ht0 : t 0 = a₀ := by dsimp [t]; ring
      have htK : t K = b₀ := by dsimp [t, h]; field_simp; ring
      rw [ht0, htK]
    have hsum_F := Finset.sum_le_sum hstep_F
    rw [htel, ← Finset.mul_sum] at hsum_F
    have h1 := hsum_F.trans (mul_le_mul_of_nonneg_right hh_small
      (Finset.sum_nonneg (fun j hj => by
        have hjK : j < K := Finset.mem_range.mp hj
        have ht1 : 1 / 3 ≤ t (j + 1) := by
          dsimp [t, a₀]
          have h0 : 0 ≤ ((j + 1 : ℕ) : ℝ) * h := by positivity
          linarith
        have ht2 : t j ≤ 1 / 2 := by
          have hj_le : (j : ℝ) ≤ K := by exact_mod_cast hjK.le
          have hjh : (j : ℝ) * h ≤ b₀ - a₀ := by
            calc (j : ℝ) * h ≤ (K : ℝ) * h := mul_le_mul_of_nonneg_right hj_le hh0.le
              _ = b₀ - a₀ := by dsimp [h]; exact mul_div_cancel₀ _ hK0.ne'
          dsimp [t, b₀] at hjh ⊢; linarith
        exact div_nonneg hh0.le (mul_nonneg (by linarith) (by linarith)))))
    rw [div_mul_eq_mul_div, le_div_iff₀ (show (0 : ℝ) < 1 - η / 8 by linarith)] at h1
    linarith
  have hFbFa : (1 - η / 8) * Real.log 2 ≤ F b₀ - F a₀ := by
    rw [hFbFa_eq]; exact hρ_log
  have hdc_lb : (1 - η / 4) * (d - c) ≤ (1 - δ) * d - (1 + δ) * c := by
    have hδ_dc : δ ≤ η * (d - c) / (32 * (d + 1)) := min_le_left _ _
    have h1 : δ * (d + c) ≤ η * (d - c) / 4 := by
      have h2 : δ * (32 * (d + 1)) ≤ η * (d - c) := (le_div_iff₀ (by linarith)).mp hδ_dc
      have h3 : d + c ≤ 2 * (d + 1) := by linarith
      have hmul3 := mul_le_mul_of_nonneg_left h3 hδ0.le
      have h16 : 16 * (δ * (2 * (d + 1))) = δ * (32 * (d + 1)) := by ring
      have hnn : 0 ≤ δ * (2 * (d + 1)) := mul_nonneg hδ0.le (by linarith)
      linarith
    linarith
  have h12δ : 1 - η / 8 ≤ 1 - 2 * δ := by
    have : δ ≤ η / 32 := min_le_right _ _
    linarith
  have hprod_coeff :
      (1 - η) * (d - c) * Real.log 2 ≤
        ((1 - δ) * d - (1 + δ) * c) * (1 - 2 * δ) * ((1 - η / 8) * ((1 - η / 8) * Real.log 2)) := by
    have h1 : 1 - η ≤ (1 - η / 4) * (1 - η / 8) * (1 - η / 8) * (1 - η / 8) := by
      have ha : 1 - 3 * η / 8 ≤ (1 - η / 4) * (1 - η / 8) := by nlinarith only [hη]
      have hb : 1 - η / 2 ≤ (1 - 3 * η / 8) * (1 - η / 8) := by nlinarith only [hη]
      have hc : 1 - 5 * η / 8 ≤ (1 - η / 2) * (1 - η / 8) := by nlinarith only [hη]
      have h12 : 1 - η / 2 ≤ (1 - η / 4) * (1 - η / 8) * (1 - η / 8) :=
        hb.trans (mul_le_mul_of_nonneg_right ha (by linarith))
      have h13 : 1 - 5 * η / 8 ≤ (1 - η / 4) * (1 - η / 8) * (1 - η / 8) * (1 - η / 8) :=
        hc.trans (mul_le_mul_of_nonneg_right h12 (by linarith))
      linarith
    have h2 : (1 - η / 4) * (d - c) * (1 - η / 8) * ((1 - η / 8) * ((1 - η / 8) * Real.log 2)) ≤
        ((1 - δ) * d - (1 + δ) * c) * (1 - 2 * δ) * ((1 - η / 8) * ((1 - η / 8) * Real.log 2)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (by linarith) (mul_nonneg (by linarith) hlog2_pos.le))
      exact mul_le_mul hdc_lb h12δ (by linarith)
        (le_trans (mul_nonneg (by linarith) (sub_nonneg.mpr hcd.le)) hdc_lb)
    have h3 : (1 - η) * (d - c) * Real.log 2 ≤
        (1 - η / 4) * (d - c) * (1 - η / 8) * ((1 - η / 8) * ((1 - η / 8) * Real.log 2)) := by
      have hpos : 0 ≤ (d - c) * Real.log 2 := mul_nonneg (sub_nonneg.mpr hcd.le) hlog2_pos.le
      nlinarith only [h1, hpos]
    exact h3.trans h2
  have hcard_cast : ∑ p ∈ P_all, ((Q p).card : ℝ) ≤
      (((Finset.Ioc ⌊c * (X : ℝ)⌋₊ ⌊d * (X : ℝ)⌋₊).filter
        (fun u => z₁ < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime)).card : ℝ) := by
    exact_mod_cast h_inj_card
  have hstep_final :
      ((1 - δ) * d - (1 + δ) * c) * (1 - 2 * δ) * ((X : ℝ) / Real.log (X : ℝ)) *
          ((1 - η / 8) * ((1 - η / 8) * Real.log 2)) ≤
        ∑ p ∈ P_all, ((Q p).card : ℝ) := by
    rw [hsplit]
    have hnn : 0 ≤ ((1 - δ) * d - (1 + δ) * c) * (1 - 2 * δ) * ((X : ℝ) / Real.log (X : ℝ)) := by
      have : 0 ≤ (1 - δ) * d - (1 + δ) * c := le_trans (mul_nonneg (by linarith) (sub_nonneg.mpr hcd.le)) hdc_lb
      exact mul_nonneg (mul_nonneg this (by linarith)) (div_nonneg hXpos.le hlogX.le)
    have hriem2 : (1 - η / 8) * ((1 - η / 8) * Real.log 2) ≤
        ∑ j ∈ Finset.range K, h / (t (j + 1) * (1 - t j)) :=
      (mul_le_mul_of_nonneg_left hFbFa (by linarith)).trans hriem_log
    exact (mul_le_mul_of_nonneg_left hriem2 hnn).trans hsum_K
  calc (1 - η) * (d - c) * Real.log 2 * (X : ℝ) / Real.log (X : ℝ)
      = ((1 - η) * (d - c) * Real.log 2) * ((X : ℝ) / Real.log (X : ℝ)) := by ring
    _ ≤ (((1 - δ) * d - (1 + δ) * c) * (1 - 2 * δ) * ((1 - η / 8) * ((1 - η / 8) * Real.log 2))) *
          ((X : ℝ) / Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_right hprod_coeff (div_nonneg hXpos.le hlogX.le)
    _ = ((1 - δ) * d - (1 + δ) * c) * (1 - 2 * δ) * ((X : ℝ) / Real.log (X : ℝ)) *
          ((1 - η / 8) * ((1 - η / 8) * Real.log 2)) := by ring
    _ ≤ ∑ p ∈ P_all, ((Q p).card : ℝ) := hstep_final
    _ ≤ _ := hcard_cast

private lemma pair_sum_lower :
    ∃ X₀ : ℕ, 100000 ≤ X₀ ∧ ∀ X : ℕ, X₀ ≤ X →
      let D := X / 10000
      let E := (Finset.Icc X (X + D)).filter Even
      let x1 := fun n : ℕ => Finset.Icc ((n + 2) / 3) ((2 * n) / 3)
      let x3 := fun n : ℕ => (x1 n).filter (fun u =>
          ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac))
      let x5 := fun n : ℕ => (x3 n).filter (fun u => n - u ∈ x3 n)
      (1 - 1 / 5000 : ℝ) ^ 2 * ((3332 / 10000 : ℝ) * (1 / 10000 - (3332 / 10000) / (10 ^ 7 : ℝ))) *
          (Real.log 2) ^ 2 * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 ≤
        ∑ n ∈ E, ((x5 n).card : ℝ) := by
  let A : ℝ := 3334 / 10000
  let B : ℝ := 6666 / 10000
  let δ : ℝ := 1 / 10000
  obtain ⟨M, hMeq⟩ : ∃ M : ℕ, M = 10 ^ 7 := ⟨10 ^ 7, rfl⟩
  have hMr : (M : ℝ) = (10 ^ 7 : ℝ) := by exact_mod_cast hMeq
  have hM0 : (0 : ℝ) < (M : ℝ) := by rw [hMr]; positivity
  let η : ℝ := 1 / 5000
  let α : ℕ → ℝ := fun j => A + (j : ℝ) * ((B - A) / (M : ℝ))
  let β : ℕ → ℝ := fun j => A + ((j + 1 : ℕ) : ℝ) * ((B - A) / (M : ℝ))
  have hBA_pos : 0 < B - A := by norm_num [A, B]
  have hbin_u : ∀ j : ℕ, j < M →
      ∃ Xj : ℕ, ∀ X : ℕ, Xj ≤ X →
        let z₁ := ⌊((X + X / 10000 : ℕ) : ℝ) ^ (1 / 3 : ℝ)⌋₊
        (1 - η) * (β j - α j) * Real.log 2 * (X : ℝ) / Real.log (X : ℝ) ≤
          (((Finset.Ioc ⌊α j * (X : ℝ)⌋₊ ⌊β j * (X : ℝ)⌋₊).filter
            (fun u => z₁ < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime)).card : ℝ) := by
    intro j hj
    apply semiprime_Ioc_lower
    · dsimp [α, A, B]; positivity
    · dsimp [α, β]; push_cast
      have : 0 < (B - A) / (M : ℝ) := div_pos hBA_pos hM0
      linarith
    · have hj1 : ((j + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast (show j + 1 ≤ M by omega)
      have h1 : ((j + 1 : ℕ) : ℝ) * ((B - A) / (M : ℝ)) ≤ B - A := by
        rw [mul_div_assoc', div_le_iff₀ hM0]; nlinarith
      dsimp [β, A, B] at h1 ⊢; linarith
    · norm_num [η]
    · norm_num [η]
  have hbin_v : ∀ j : ℕ, j < M →
      ∃ Xj : ℕ, ∀ X : ℕ, Xj ≤ X →
        let z₁ := ⌊((X + X / 10000 : ℕ) : ℝ) ^ (1 / 3 : ℝ)⌋₊
        (1 - η) * ((1 + δ - β j) - (1 - α j)) * Real.log 2 * (X : ℝ) / Real.log (X : ℝ) ≤
          (((Finset.Ioc ⌊(1 - α j) * (X : ℝ)⌋₊ ⌊(1 + δ - β j) * (X : ℝ)⌋₊).filter
            (fun u => z₁ < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime)).card : ℝ) := by
    intro j hj
    have hjM : (j : ℝ) ≤ (M : ℝ) := by exact_mod_cast hj.le
    have hα_le : α j ≤ B := by
      have : (j : ℝ) * ((B - A) / (M : ℝ)) ≤ B - A := by
        rw [mul_div_assoc', div_le_iff₀ hM0]; nlinarith
      dsimp [α]; linarith
    apply semiprime_Ioc_lower
    · dsimp [A, B] at hα_le; linarith
    · have hsub : (1 + δ - β j) - (1 - α j) = δ - (B - A) / (M : ℝ) := by
        dsimp [α, β]; push_cast; ring
      rw [← sub_pos, hsub, hMr]; norm_num [δ, A, B]
    · dsimp [β]
      have h0 : 0 ≤ ((j + 1 : ℕ) : ℝ) * ((B - A) / (M : ℝ)) := by positivity
      have h1 : 1 + δ - A ≤ 3 / 4 := by norm_num [A, δ]
      linarith
    · norm_num [η]
    · norm_num [η]
  classical
  let Xu : ℕ → ℕ := fun j => if h : j < M then Classical.choose (hbin_u j h) else 0
  let Xv : ℕ → ℕ := fun j => if h : j < M then Classical.choose (hbin_v j h) else 0
  let X_sup : ℕ := max ((Finset.range M).sup (fun j => max (Xu j) (Xv j))) (10 ^ 10)
  refine ⟨X_sup, by omega, fun X hX => ?_⟩
  dsimp only
  set D : ℕ := X / 10000
  set E : Finset ℕ := (Finset.Icc X (X + D)).filter Even
  let x1 : ℕ → Finset ℕ := fun n => Finset.Icc ((n + 2) / 3) ((2 * n) / 3)
  let x3 : ℕ → Finset ℕ := fun n => (x1 n).filter (fun u =>
      ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac))
  let x5 : ℕ → Finset ℕ := fun n => (x3 n).filter (fun u => n - u ∈ x3 n)
  set z₁ : ℕ := ⌊((X + X / 10000 : ℕ) : ℝ) ^ (1 / 3 : ℝ)⌋₊
  let U : ℕ → Finset ℕ := fun j => (Finset.Ioc ⌊α j * (X : ℝ)⌋₊ ⌊β j * (X : ℝ)⌋₊).filter
      (fun u => z₁ < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime)
  let V_bin : ℕ → Finset ℕ := fun j => (Finset.Ioc ⌊(1 - α j) * (X : ℝ)⌋₊ ⌊(1 + δ - β j) * (X : ℝ)⌋₊).filter
      (fun v => z₁ < v.minFac ∧ v.minFac.Prime ∧ (v / v.minFac).Prime)
  have hX10 : 10 ^ 10 ≤ X := (le_max_right _ _).trans hX
  have hX_pos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hcard_inj :
      ∑ j ∈ Finset.range M, (U j).card * (V_bin j).card ≤ ∑ n ∈ E, (x5 n).card := by
    have hlhs : ∑ j ∈ Finset.range M, (U j).card * (V_bin j).card =
        ((Finset.range M).sigma (fun j => (U j) ×ˢ (V_bin j))).card := by
      rw [Finset.card_sigma]
      apply Finset.sum_congr rfl
      intro j _; rw [Finset.card_product]
    have hrhs : ∑ n ∈ E, (x5 n).card = (E.sigma x5).card := (Finset.card_sigma _ _).symm
    rw [hlhs, hrhs]
    have hz1_ge2 : 2 ≤ z₁ := by
      have h1 : (2 : ℝ) ^ (3 : ℝ) ≤ ((X + X / 10000 : ℕ) : ℝ) := by
        have h8 : ((8 : ℕ) : ℝ) ≤ ((X + X / 10000 : ℕ) : ℝ) := by exact_mod_cast (show 8 ≤ X + X / 10000 by omega)
        norm_num at h8 ⊢; linarith
      have h2 := Real.rpow_le_rpow (by norm_num) h1 (show (0 : ℝ) ≤ 1 / 3 by norm_num)
      rw [← Real.rpow_mul (by norm_num)] at h2
      norm_num at h2
      have h2' : ((2 : ℕ) : ℝ) ≤ ((X + X / 10000 : ℕ) : ℝ) ^ (1 / 3 : ℝ) := by norm_num; exact h2
      exact Nat.le_floor h2'
    apply Finset.card_le_card_of_injOn (fun x : Σ _ : ℕ, ℕ × ℕ => (⟨x.2.1 + x.2.2, x.2.1⟩ : Σ _ : ℕ, ℕ))
    · rintro ⟨j, ⟨u, v⟩⟩ hx
      rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_product] at hx
      dsimp only at hx
      obtain ⟨hj, hu, hv⟩ := hx
      have hjM : j < M := Finset.mem_range.mp hj
      have huf := Finset.mem_filter.mp hu
      have hvf := Finset.mem_filter.mp hv
      have hui := Finset.mem_Ioc.mp huf.1
      have hvi := Finset.mem_Ioc.mp hvf.1
      have hu_gt : α j * (X : ℝ) < (u : ℝ) := by
        have h1 := Nat.lt_floor_add_one (α j * (X : ℝ))
        have h2 : (⌊α j * (X : ℝ)⌋₊ : ℝ) + 1 ≤ (u : ℝ) := by exact_mod_cast (show _ + 1 ≤ u by omega)
        linarith
      have hu_le : (u : ℝ) ≤ β j * (X : ℝ) :=
        (Nat.cast_le.mpr hui.2).trans (Nat.floor_le (by dsimp [β, A, B]; positivity))
      have hv_gt : (1 - α j) * (X : ℝ) < (v : ℝ) := by
        have h1 := Nat.lt_floor_add_one ((1 - α j) * (X : ℝ))
        have h2 : (⌊(1 - α j) * (X : ℝ)⌋₊ : ℝ) + 1 ≤ (v : ℝ) := by exact_mod_cast (show _ + 1 ≤ v by omega)
        linarith
      have hv_le : (v : ℝ) ≤ (1 + δ - β j) * (X : ℝ) :=
        (Nat.cast_le.mpr hvi.2).trans (Nat.floor_le (by
          have hj1 : ((j + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast (show j + 1 ≤ M by omega)
          have : ((j + 1 : ℕ) : ℝ) * ((B - A) / (M : ℝ)) ≤ B - A := by
            rw [mul_div_assoc', div_le_iff₀ hM0]; nlinarith
          have : β j ≤ B := by dsimp [β]; linarith
          dsimp [B, δ] at this ⊢; nlinarith))
      have huv_lo : X ≤ u + v := by
        have h1 : (X : ℝ) < (u : ℝ) + (v : ℝ) := by linarith
        have h2 : (X : ℝ) < ((u + v : ℕ) : ℝ) := by push_cast; linarith
        exact_mod_cast h2.le
      have huv_hi : u + v ≤ X + D := by
        have h1 : ((u + v : ℕ) : ℝ) ≤ (1 + δ) * (X : ℝ) := by push_cast; linarith
        have h2 : (1 + δ) * (X : ℝ) < ((X + D + 1 : ℕ) : ℝ) := by
          have hD : (X : ℝ) / 10000 - 1 < (D : ℝ) := by
            dsimp [D]
            have hrem := Nat.div_add_mod X 10000
            have hlt := Nat.mod_lt X (by decide : 0 < 10000)
            have : (X : ℝ) < ((X / 10000 : ℕ) : ℝ) * 10000 + 10000 := by exact_mod_cast (by omega : X < X / 10000 * 10000 + 10000)
            linarith
          dsimp [δ]; push_cast; linarith
        have h3 : ((u + v : ℕ) : ℝ) < ((X + D + 1 : ℕ) : ℝ) := lt_of_le_of_lt h1 h2
        have h4 : u + v < X + D + 1 := by exact_mod_cast h3
        omega
      have hu_odd : Odd u := by
        by_contra hnot
        rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hnot
        have h2le : u.minFac ≤ 2 := Nat.minFac_le_of_dvd (by decide) hnot
        omega
      have hv_odd : Odd v := by
        by_contra hnot
        rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hnot
        have h2le : v.minFac ≤ 2 := Nat.minFac_le_of_dvd (by decide) hnot
        omega
      have huv_ev : Even (u + v) := hu_odd.add_odd hv_odd
      have hα_ge : A ≤ α j := by
        dsimp [α]
        have : 0 ≤ (j : ℝ) * ((B - A) / (M : ℝ)) := by positivity
        linarith
      have hβ_le : β j ≤ B := by
        have hj1 : ((j + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast (show j + 1 ≤ M by omega)
        have : ((j + 1 : ℕ) : ℝ) * ((B - A) / (M : ℝ)) ≤ B - A := by
          rw [mul_div_assoc', div_le_iff₀ hM0]; nlinarith
        dsimp [β]; linarith
      have hu_in_x1 : u ∈ x1 (u + v) := by
        rw [Finset.mem_Icc]
        have h1 : A * (X : ℝ) < (u : ℝ) := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα_ge hX_pos.le) hu_gt
        have h2 : (u : ℝ) ≤ B * (X : ℝ) := hu_le.trans (mul_le_mul_of_nonneg_right hβ_le hX_pos.le)
        have h3 : ((u + v : ℕ) : ℝ) ≤ (1 + δ) * (X : ℝ) := by push_cast; linarith
        have h4 : (X : ℝ) ≤ ((u + v : ℕ) : ℝ) := by exact_mod_cast huv_lo
        have h3u_lo : u + v + 2 ≤ 3 * u := by
          have hXr : (10 ^ 10 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX10
          have : ((u + v + 2 : ℕ) : ℝ) ≤ (3 * u : ℝ) := by
            push_cast at h3 ⊢; dsimp [A, δ] at h1 h3; linarith
          exact_mod_cast this
        have h3u_hi : 3 * u ≤ 2 * (u + v) := by
          have : ((3 * u : ℕ) : ℝ) ≤ ((2 * (u + v) : ℕ) : ℝ) := by
            push_cast at h4 ⊢; dsimp [B] at h2; linarith
          exact_mod_cast this
        omega
      have hv_in_x1 : v ∈ x1 (u + v) := by
        rw [Finset.mem_Icc]
        have h1 := Finset.mem_Icc.mp hu_in_x1
        omega
      have hz_mono : ⌊((u + v : ℕ) : ℝ) ^ (1 / 3 : ℝ)⌋₊ ≤ z₁ := by
        apply Nat.floor_mono
        apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ (by norm_num)
        exact_mod_cast huv_hi
      rw [Finset.mem_coe, Finset.mem_sigma]
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨huv_lo, huv_hi⟩, huv_ev⟩, ?_⟩
      dsimp only [x5, x3]
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter, Nat.add_sub_cancel_left]
      exact ⟨⟨hu_in_x1, lt_of_le_of_lt hz_mono huf.2.1, huf.2.2⟩,
        ⟨hv_in_x1, lt_of_le_of_lt hz_mono hvf.2.1, hvf.2.2⟩⟩
    · rintro ⟨j1, ⟨u1, v1⟩⟩ h1 ⟨j2, ⟨u2, v2⟩⟩ h2 heq
      have hu_eq : u1 = u2 := congrArg Sigma.snd heq
      have hsum_eq : u1 + v1 = u2 + v2 := congrArg Sigma.fst heq
      have hv_eq : v1 = v2 := by omega
      subst hu_eq; subst hv_eq
      rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_product] at h1 h2
      dsimp only at h1 h2
      have hi1 := Finset.mem_Ioc.mp (Finset.mem_filter.mp h1.2.1).1
      have hi2 := Finset.mem_Ioc.mp (Finset.mem_filter.mp h2.2.1).1
      have hj_eq : j1 = j2 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · have hle : β j1 ≤ α j2 := by
            dsimp [α, β]
            have : ((j1 + 1 : ℕ) : ℝ) ≤ (j2 : ℝ) := by exact_mod_cast hlt
            nlinarith [div_nonneg hBA_pos.le hM0.le]
          have hfl : ⌊β j1 * (X : ℝ)⌋₊ ≤ ⌊α j2 * (X : ℝ)⌋₊ :=
            Nat.floor_mono (mul_le_mul_of_nonneg_right hle hX_pos.le)
          omega
        · have hle : β j2 ≤ α j1 := by
            dsimp [α, β]
            have : ((j2 + 1 : ℕ) : ℝ) ≤ (j1 : ℝ) := by exact_mod_cast hgt
            nlinarith [div_nonneg hBA_pos.le hM0.le]
          have hfl : ⌊β j2 * (X : ℝ)⌋₊ ≤ ⌊α j1 * (X : ℝ)⌋₊ :=
            Nat.floor_mono (mul_le_mul_of_nonneg_right hle hX_pos.le)
          omega
      subst hj_eq
      rfl
  have hterm : ∀ j ∈ Finset.range M,
      (1 - η) ^ 2 * ((B - A) / (M : ℝ)) * (δ - (B - A) / (M : ℝ)) *
          (Real.log 2) ^ 2 * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 ≤
        ((U j).card : ℝ) * ((V_bin j).card : ℝ) := by
    intro j hj
    have hjM : j < M := Finset.mem_range.mp hj
    have hX_sup_j : max (Xu j) (Xv j) ≤ X :=
      (Finset.le_sup (f := fun i => max (Xu i) (Xv i)) hj).trans ((le_max_left _ _).trans hX)
    have hXu : Xu j ≤ X := (le_max_left _ _).trans hX_sup_j
    have hXv : Xv j ≤ X := (le_max_right _ _).trans hX_sup_j
    have hu := Classical.choose_spec (hbin_u j hjM) X (by dsimp [Xu] at hXu; rw [dite_eq_left hjM] at hXu; exact hXu)
    have hv := Classical.choose_spec (hbin_v j hjM) X (by dsimp [Xv] at hXv; rw [dite_eq_left hjM] at hXv; exact hXv)
    have hdu : β j - α j = (B - A) / (M : ℝ) := by dsimp [α, β]; push_cast; ring
    have hdv : (1 + δ - β j) - (1 - α j) = δ - (B - A) / (M : ℝ) := by dsimp [α, β]; push_cast; ring
    rw [hdu] at hu
    rw [hdv] at hv
    have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hmul := mul_le_mul hu hv
      (by
        have h1 : 0 ≤ δ - (B - A) / (M : ℝ) := by rw [hMr]; norm_num [δ, A, B]
        have h2 : 0 ≤ 1 - η := by norm_num [η]
        positivity)
      (Nat.cast_nonneg _)
    calc (1 - η) ^ 2 * ((B - A) / (M : ℝ)) * (δ - (B - A) / (M : ℝ)) *
            (Real.log 2) ^ 2 * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2
        = ((1 - η) * ((B - A) / (M : ℝ)) * Real.log 2 * (X : ℝ) / Real.log (X : ℝ)) *
          ((1 - η) * (δ - (B - A) / (M : ℝ)) * Real.log 2 * (X : ℝ) / Real.log (X : ℝ)) := by ring
      _ ≤ ((U j).card : ℝ) * ((V_bin j).card : ℝ) := hmul
  have hsum_lb := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum_lb
  have hcast : ∑ j ∈ Finset.range M, ((U j).card : ℝ) * ((V_bin j).card : ℝ) ≤
      ∑ n ∈ E, ((x5 n).card : ℝ) := by
    exact_mod_cast hcard_inj
  have hlhs_eq :
      (M : ℝ) * ((1 - η) ^ 2 * ((B - A) / (M : ℝ)) * (δ - (B - A) / (M : ℝ)) *
          (Real.log 2) ^ 2 * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) =
        (1 - 1 / 5000 : ℝ) ^ 2 * ((3332 / 10000 : ℝ) * (1 / 10000 - (3332 / 10000) / (10 ^ 7 : ℝ))) *
          (Real.log 2) ^ 2 * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
    have hBA : B - A = 3332 / 10000 := by norm_num [A, B]
    dsimp [η, δ]
    rw [hBA, hMr]
    field_simp
  exact (hlhs_eq ▸ hsum_lb).trans hcast

end RefuteE6ac

theorem Conjectures.Cuts.Refute29952a4156349f5cd5eb5835 : ¬ (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊Real.exp (Real.log (↑x6 : ℝ) / (2 : ℝ) - (2 : ℝ) * Real.log (↑x6 : ℝ) ^ (2 / 3 : ℝ))⌋₊; have x7 : ℕ → ℕ := fun (x7 : ℕ) => ⌊(↑x7 : ℝ) ^ (2 / 5 : ℝ)⌋₊; ∃ (x8 : ℕ), ∀ (x9 : ℕ), x8 ≤ x9 → Even x9 → (↑(x5 x9).card : ℝ) ≤ (189 / 500 : ℝ) * x4 x9) := by
  classical
  dsimp only
  rintro ⟨N₀, hN₀⟩
  obtain ⟨X1, _, hV⟩ := RefuteE6ac.V_avg_upper
  obtain ⟨X2, _, hP⟩ := RefuteE6ac.pair_sum_lower
  set X : ℕ := max (max X1 X2) (max N₀ 100000)
  have hX1 : X1 ≤ X := (le_max_left X1 X2).trans (le_max_left _ _)
  have hX2 : X2 ≤ X := (le_max_right X1 X2).trans (le_max_left _ _)
  have hXN : N₀ ≤ X := (le_max_left N₀ 100000).trans (le_max_right _ _)
  have hX100 : 100000 ≤ X := (le_max_right N₀ 100000).trans (le_max_right _ _)
  have hup := hV X hX1
  have hlo := hP X hX2
  dsimp only at hup hlo
  set D : ℕ := X / 10000
  set E : Finset ℕ := (Finset.Icc X (X + D)).filter Even
  have hsum_hyp :
      ∑ n ∈ E, (({x6 ∈ {x4 ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) |
        ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)} |
        n - x6 ∈ {x4 ∈ Finset.Icc ((n + 2) / 3) (2 * n / 3) |
        ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}}).card : ℝ) ≤
      (189 / 500 : ℝ) * ∑ n ∈ E, ((Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) *
        (n.totient : ℝ) / (n : ℝ) *
        ∏ x5 ∈ (Finset.filter Nat.Prime (Finset.Icc 2 n.sqrt)) with ¬x5 ∣ n, (1 - 2 / (x5 : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hnf := Finset.mem_filter.mp hn
    have hnX : X ≤ n := (Finset.mem_Icc.mp hnf.1).1
    exact hN₀ n (hXN.trans hnX) hnf.2
  have hcomb := hlo.trans (hsum_hyp.trans (mul_le_mul_of_nonneg_left hup (by norm_num)))
  have hscale_pos : 0 < (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
    have hX1r : (1 : ℝ) < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
    exact div_pos (pow_pos (by linarith) 2) (pow_pos (Real.log_pos hX1r) 2)
  have hcoeff_ineq :
      (1 - 1 / 5000 : ℝ) ^ 2 * ((3332 / 10000 : ℝ) * (1 / 10000 - (3332 / 10000) / (10 ^ 7 : ℝ))) *
          (Real.log 2) ^ 2 ≤
      (189 / 500 : ℝ) * ((1 + 1 / 5000 : ℝ) * (4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) *
          Real.exp (-2 * (5755 / 10000 : ℝ))) := by
    have h1 :
        ((1 - 1 / 5000 : ℝ) ^ 2 * ((3332 / 10000 : ℝ) * (1 / 10000 - (3332 / 10000) / (10 ^ 7 : ℝ))) *
            (Real.log 2) ^ 2) * ((X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) ≤
        ((189 / 500 : ℝ) * ((1 + 1 / 5000 : ℝ) * (4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) *
            Real.exp (-2 * (5755 / 10000 : ℝ)))) * ((X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) := by
      linarith [show (1 - 1 / 5000 : ℝ) ^ 2 * ((3332 / 10000 : ℝ) * (1 / 10000 - (3332 / 10000) / (10 ^ 7 : ℝ))) *
            (Real.log 2) ^ 2 * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 =
          ((1 - 1 / 5000 : ℝ) ^ 2 * ((3332 / 10000 : ℝ) * (1 / 10000 - (3332 / 10000) / (10 ^ 7 : ℝ))) *
            (Real.log 2) ^ 2) * ((X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) by ring,
        show (189 / 500 : ℝ) * ((1 + 1 / 5000 : ℝ) * (4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) *
            Real.exp (-2 * (5755 / 10000 : ℝ)) * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) =
          ((189 / 500 : ℝ) * ((1 + 1 / 5000 : ℝ) * (4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) *
            Real.exp (-2 * (5755 / 10000 : ℝ)))) * ((X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) by ring]
    exact le_of_mul_le_mul_right h1 hscale_pos
  have hlog2 := RefuteE6ac.log_two_gt
  have hexp2 := RefuteE6ac.exp_two_g0_gt
  have hlog2_sq : (6931 / 10000 : ℝ) ^ 2 ≤ (Real.log 2) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlog2.le 2
  have hexp_inv : Real.exp (-2 * (5755 / 10000 : ℝ)) ≤ (10000 / 31613 : ℝ) := by
    rw [show -2 * (5755 / 10000 : ℝ) = -(2 * (5755 / 10000 : ℝ)) by ring, Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num at hexp2 ⊢; linarith
  have hlhs_num :
      (1 - 1 / 5000 : ℝ) ^ 2 * ((3332 / 10000 : ℝ) * (1 / 10000 - (3332 / 10000) / (10 ^ 7 : ℝ))) *
          (6931 / 10000 : ℝ) ^ 2 ≤
        (1 - 1 / 5000 : ℝ) ^ 2 * ((3332 / 10000 : ℝ) * (1 / 10000 - (3332 / 10000) / (10 ^ 7 : ℝ))) *
          (Real.log 2) ^ 2 :=
    mul_le_mul_of_nonneg_left hlog2_sq (by norm_num)
  have hrhs_num :
      (189 / 500 : ℝ) * ((1 + 1 / 5000 : ℝ) * (4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) *
          Real.exp (-2 * (5755 / 10000 : ℝ))) ≤
        (189 / 500 : ℝ) * ((1 + 1 / 5000 : ℝ) * (4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) *
          (10000 / 31613 : ℝ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_inv (by norm_num)) (by norm_num)
  have hcontra :
      (189 / 500 : ℝ) * ((1 + 1 / 5000 : ℝ) * (4 / 3 : ℝ) * (1 / 10000 : ℝ) * (1 + 1 / 10000 : ℝ) *
          (10000 / 31613 : ℝ)) <
        (1 - 1 / 5000 : ℝ) ^ 2 * ((3332 / 10000 : ℝ) * (1 / 10000 - (3332 / 10000) / (10 ^ 7 : ℝ))) *
          (6931 / 10000 : ℝ) ^ 2 := by
    norm_num
  linarith

