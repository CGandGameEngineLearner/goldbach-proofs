import Mathlib
open scoped BigOperators
open Filter

private lemma theta_term_norm (K : Type) [NontriviallyNormedField K]
    (r z : K) (l j : ℕ) (n : ℤ) (hr : 0 < ‖r‖) (hz : ‖z‖ = 1) :
    ‖(r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1)‖ =
    ‖r‖ ^ ((l:ℤ)*(n*(n+1))+(j:ℤ)*(2*n+1)) := by
  have hdiv : 2 ∣ n*(n+1) := (Int.even_mul_succ_self n).two_dvd
  have heq : (n*(n+1)/2)*2 = n*(n+1) := Int.ediv_mul_cancel hdiv
  rw [norm_mul, norm_zpow, norm_pow, norm_zpow, norm_mul, norm_pow, hz, mul_one]
  rw [← zpow_natCast (‖r‖) (2*l), ← zpow_natCast (‖r‖) j]
  rw [← zpow_mul, ← zpow_mul]
  rw [← zpow_add₀ (ne_of_gt hr)]
  congr 1
  push_cast
  nlinarith [heq]

private lemma exponent_pos (l j n : ℤ) (hj : 0 ≤ j) (hjl : j < l) (hn : 0 ≤ n) :
    n ≤ l*(n*(n+1)) + j*(2*n+1) + j := by
  have hl : 1 ≤ l := by omega
  have h1 : 0 ≤ (l-1)*n := mul_nonneg (by omega) hn
  have h2 : 0 ≤ n*(l*n + 2*j) := mul_nonneg hn (by positivity)
  nlinarith

private lemma exponent_neg (l j n : ℤ) (hj : 0 ≤ j) (hjl : j < l) (hn : n ≤ -1) :
    -n-1 ≤ l*(n*(n+1)) + j*(2*n+1) + j := by
  let m := -n-1
  have hm : 0 ≤ m := by dsimp [m]; omega
  have hl : 1 ≤ l := by omega
  by_cases hm0 : m=0
  · dsimp [m] at hm0
    have hn1 : n = -1 := by omega
    subst n
    norm_num
  · have hm1 : 1 ≤ m := by omega
    have hm2 : 0 ≤ l*(m-1) := mul_nonneg (by omega) (by omega)
    have hcoeff : 1 ≤ l*(m+1) - 2*j := by nlinarith
    have hprod : m ≤ m*(l*(m+1)-2*j) := by nlinarith
    dsimp [m] at *
    nlinarith

private lemma theta_summable (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    (r z : K) (l j : ℕ) (hr : 0 < ‖r‖) (hr1 : ‖r‖ < 1) (hz : ‖z‖ = 1) (hjl : j < l) :
    Summable (fun n : ℤ => (r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1)) := by
  let f : ℤ → K := fun n => (r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1)
  let rho : ℝ := ‖r‖
  let A : ℝ := rho ^ (-(j:ℤ)-1)
  have hbound (n : ℤ) (N : ℕ)
      (hn : (N:ℤ) - (j:ℤ) - 1 ≤ (l:ℤ)*(n*(n+1)) + (j:ℤ)*(2*n+1)) :
      ‖f n‖ ≤ A * rho^N := by
    dsimp only [f]
    rw [theta_term_norm K r z l j n hr hz]
    change rho ^ ((l:ℤ)*(n*(n+1))+(j:ℤ)*(2*n+1)) ≤ A * rho^N
    calc
      _ ≤ rho ^ ((N:ℤ) - (j:ℤ) - 1) := zpow_le_zpow_right_of_le_one₀ hr hr1.le hn
      _ = A * rho^N := by
        dsimp [A]
        rw [← zpow_natCast rho N, ← zpow_add₀ (ne_of_gt hr)]
        congr 1
        ring
  have hg : Summable (fun n : ℕ => A*rho^n) :=
    (summable_geometric_of_lt_one (le_of_lt hr) hr1).mul_left A
  apply summable_int_iff_summable_nat_and_neg.mpr
  constructor
  · apply hg.of_norm_bounded
    intro n
    apply hbound (n:ℤ) n
    have h := exponent_pos (l:ℤ) (j:ℤ) n (by positivity) (by exact_mod_cast hjl) (by positivity)
    omega
  · apply hg.of_norm_bounded
    intro n
    apply hbound (-(n:ℤ)) n
    rcases n with _ | n
    · have h := exponent_pos (l:ℤ) (j:ℤ) 0 (by positivity) (by exact_mod_cast hjl) (by omega)
      norm_num at h ⊢
      omega
    · have hn : -(↑(n+1):ℤ) ≤ -1 := by omega
      have h := exponent_neg (l:ℤ) (j:ℤ) (-(↑(n+1):ℤ)) (by positivity) (by exact_mod_cast hjl) hn
      omega

private lemma exponent_gap (l j : ℕ) (n : ℤ) (hj : 0 < j) (hjl : j < l) (hn : n ≠ -1) :
    1-(j:ℤ) ≤ (l:ℤ)*(n*(n+1)) + (j:ℤ)*(2*n+1) := by
  have hjz : (0:ℤ) < j := by exact_mod_cast hj
  have hjlz : (j:ℤ) < l := by exact_mod_cast hjl
  by_cases hn0 : 0 ≤ n
  · have hh := exponent_pos (l:ℤ) (j:ℤ) n (by omega) hjlz hn0
    by_cases heq : n=0
    · subst n; norm_num; omega
    · have hn1 : 1 ≤ n := by omega
      omega
  · have hnneg : n ≤ -1 := by omega
    have hh := exponent_neg (l:ℤ) (j:ℤ) n (by omega) hjlz hnneg
    have hn2 : n ≤ -2 := by omega
    omega

private lemma exponent_gap_zero (l : ℕ) (n : ℤ) (hl : 0 < l) (hn0 : n ≠ 0) (hn1 : n ≠ -1) :
    1 ≤ (l:ℤ)*(n*(n+1)) := by
  have hlz : (0:ℤ) < l := by exact_mod_cast hl
  by_cases hn : 0 ≤ n
  · have h := exponent_pos (l:ℤ) 0 n (by omega) (by omega) hn
    simp only [Int.cast_ofNat, zero_mul, add_zero] at h
    omega
  · have h := exponent_neg (l:ℤ) 0 n (by omega) (by omega) (by omega)
    simp only [Int.cast_ofNat, zero_mul, add_zero] at h
    omega

private lemma ultra_norm_add_eq (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]
    (a b : K) (h : ‖b‖ < ‖a‖) : ‖a+b‖ = ‖a‖ := by
  have hup : ‖a+b‖ ≤ ‖a‖ := by
    exact (IsUltrametricDist.norm_add_le_max a b).trans (by rw [max_eq_left h.le])
  have hlow : ‖a‖ ≤ max ‖a+b‖ ‖b‖ := by
    have hh := IsUltrametricDist.norm_add_le_max (a+b) (-b)
    simpa using hh
  rcases le_max_iff.mp hlow with h1 | h2
  · exact le_antisymm hup h1
  · linarith

private lemma theta_denominator_norm (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (r z : K) (l j : ℕ) (hr : 0 < ‖r‖) (hr1 : ‖r‖ < 1)
    (hz : ‖z‖ = 1) (hj : 0 < j) (hjl : j < l) :
    ‖∑' n : ℤ, (r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1)‖ = ‖r‖ ^ (-(j:ℤ)) := by
  let f : ℤ → K := fun n => (r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1)
  change ‖∑' n : ℤ, f n‖ = ‖r‖ ^ (-(j:ℤ))
  have hs : Summable f := theta_summable K r z l j hr hr1 hz hjl
  have hfirst : ‖f (-1)‖ = ‖r‖ ^ (-(j:ℤ)) := by
    have h := theta_term_norm K r z l j (-1) hr hz
    simpa [f] using h
  have htail : ‖∑' n : ℤ, if n = -1 then 0 else f n‖ ≤ ‖r‖ ^ (1-(j:ℤ)) := by
    apply IsUltrametricDist.norm_tsum_le_of_forall_le
    intro n
    by_cases hn : n = -1
    · simp [hn, zpow_nonneg (le_of_lt hr)]
    · simp only [hn, if_false]
      rw [show f n = (r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1) by rfl]
      rw [theta_term_norm K r z l j n hr hz]
      exact zpow_le_zpow_right_of_le_one₀ hr hr1.le (exponent_gap l j n hj hjl hn)
  have hstrict : ‖r‖ ^ (1-(j:ℤ)) < ‖r‖ ^ (-(j:ℤ)) :=
    zpow_lt_zpow_right_of_lt_one₀ hr hr1 (by omega)
  have hdom : ‖∑' n : ℤ, if n = -1 then 0 else f n‖ < ‖f (-1)‖ := by rw [hfirst]; exact htail.trans_lt hstrict
  rw [hs.tsum_eq_add_tsum_ite (-1), ultra_norm_add_eq K _ _ hdom, hfirst]

private lemma theta_numerator_norm (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (r z : K) (l : ℕ) (hr : 0 < ‖r‖) (hr1 : ‖r‖ < 1)
    (hz : ‖z‖ = 1) (hzz : ‖z+z⁻¹‖=1) (hl : 0 < l) :
    ‖∑' n : ℤ, (r^(2*l))^(n*(n+1)/2) * z^(2*n+1)‖ = 1 := by
  let f : ℤ → K := fun n => (r^(2*l))^(n*(n+1)/2) * z^(2*n+1)
  let s : Finset ℤ := {0,-1}
  change ‖∑' n : ℤ, f n‖ = 1
  have hs : Summable f := by
    simpa only [pow_zero, one_mul] using theta_summable K r z l 0 hr hr1 hz hl
  have hsum : (∑ n ∈ s, f n) = z+z⁻¹ := by
    simp [s, f]
  letI : Nonempty {n : ℤ // n ∉ s} := ⟨⟨1, by simp [s]⟩⟩
  have htail : ‖∑' n : {n : ℤ // n ∉ s}, f n‖ ≤ ‖r‖ := by
    apply IsUltrametricDist.norm_tsum_le_of_forall_le
    intro n
    have hn0 : (n:ℤ) ≠ 0 := by have h := n.property; simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or] at h; exact h.1
    have hn1 : (n:ℤ) ≠ -1 := by have h := n.property; simp only [s, Finset.mem_insert, Finset.mem_singleton, not_or] at h; exact h.2
    have he := exponent_gap_zero l n hl hn0 hn1
    have ht := theta_term_norm K r z l 0 n hr hz
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero] at ht
    rw [show f n = (r^(2*l))^((n:ℤ)*((n:ℤ)+1)/2) * z^(2*(n:ℤ)+1) by rfl]
    rw [ht]
    have h := zpow_le_zpow_right_of_le_one₀ hr hr1.le he
    simpa using h
  have hdom : ‖∑' n : {n : ℤ // n ∉ s}, f n‖ < ‖z+z⁻¹‖ := by rw [hzz]; exact htail.trans_lt hr1
  have hsplit := hs.sum_add_tsum_subtype_compl s
  rw [hsum] at hsplit
  rw [← hsplit, ultra_norm_add_eq K _ _ hdom, hzz]

private theorem theta_ratio_aux (K : Type) [NontriviallyNormedField K] [CompleteSpace K]
    [IsUltrametricDist K] (r z : K) (l j : ℕ) (hr : 0 < ‖r‖) (hr1 : ‖r‖ < 1)
    (hz : ‖z‖ = 1) (hzz : ‖z+z⁻¹‖=1) (hj : 0 < j) (hjl : j < l) :
    ‖(∑' n : ℤ, (r^(2*l))^(n*(n+1)/2) * z^(2*n+1)) /
      (∑' n : ℤ, (r^(2*l))^(n*(n+1)/2) * (r^j*z)^(2*n+1))‖ = ‖r‖^j := by
  rw [norm_div, theta_numerator_norm K r z l hr hr1 hz hzz (by omega),
    theta_denominator_norm K r z l j hr hr1 hz hj hjl]
  simp [zpow_neg, zpow_natCast]


theorem Conjectures.JoshiAbc.ThetaRatioNorm :
    ∀ (K : Type) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K], let theta := fun (q u : K) => ∑' n : ℤ, q^(n*(n+1)/2) * u^(2*n+1); ∀ (r z : K) (l j : ℕ), 0 < ‖r‖ → ‖r‖ < 1 → ‖z‖=1 → ‖z+z⁻¹‖=1 → 0 < j → j < l → ‖theta (r^(2*l)) z / theta (r^(2*l)) (r^j*z)‖ = ‖r‖^j := by
  intro K _ _ _
  dsimp only
  intro r z l j hr hr1 hz hzz hj hjl
  exact theta_ratio_aux K r z l j hr hr1 hz hzz hj hjl
