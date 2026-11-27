import Mathlib

/-!
# The weight of smooth denominators

Use Rankin's inequality with exponent 1/32 and expand the divisor-count bound
for the reciprocal totient. Both factors of a smooth denominator are smooth,
so the finite convolution is bounded by the square of a smooth Euler product.
Its logarithm is at most a constant times the square root of the binary logarithm
of Q, which is absorbed by the factor Q^(-1/32).

The task and Rankin-method suggestion are from goldbach-proofs PR #2327.
The reciprocal-totient comparison also appears in the project's
L_goldbach_frontier_medcore_bv_band (Apache-2.0).
-/

open Finset

namespace GoldbachSmoothModuli

private theorem rankin_min (x : ℝ) (hx : 0 < x) : min 1 x ≤ x^(1/32 : ℝ) := by
  by_cases hx1 : x ≤ 1
  · rw [min_eq_right hx1]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by norm_num : (1/32:ℝ) ≤ 1)
  · rw [min_eq_left (le_of_not_ge hx1)]
    exact Real.one_le_rpow (le_of_not_ge hx1) (by norm_num)

private theorem reciprocal_totient (q : ℕ) (hq : 0 < q) :
    1 / (q.totient : ℝ) ≤ (q.divisors.card : ℝ) / q := by
  have hcount : q ≤ q.divisors.card * q.totient := by
    calc
      q = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
      _ ≤ ∑ _d ∈ q.divisors, q.totient := sum_le_sum fun d hd =>
        Nat.le_of_dvd (Nat.totient_pos.mpr hq) (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
      _ = _ := by simp
  apply (div_le_div_iff₀ (by exact_mod_cast Nat.totient_pos.mpr hq) (by exact_mod_cast hq)).2
  simpa using (show (q : ℝ) ≤ (q.divisors.card : ℝ) * q.totient by exact_mod_cast hcount)

/-- Expanding the divisor count sends each factor pair into the square of the smooth set. -/
theorem smooth_convolution_bound (Q Y : ℕ) (hQ : 1 ≤ Q) :
    (∑ q ∈ (Icc 1 (Q^2)).filter (fun q => ∀ p ∈ q.primeFactors, p ≤ Y),
      min (1 : ℝ) ((q : ℝ) / Q) / (q.totient : ℝ)) ≤
    (Q : ℝ)^(-(1/32:ℝ)) *
      (∑ a ∈ (Icc 1 (Q^2)).filter (fun a => ∀ p ∈ a.primeFactors, p ≤ Y),
        (a:ℝ)^((1/32:ℝ)-1))^2 := by
  classical
  let S := (Icc 1 (Q^2)).filter (fun q => ∀ p ∈ q.primeFactors, p ≤ Y)
  let w (a : ℕ) := (a:ℝ)^((1/32:ℝ)-1)
  let F (ab : ℕ × ℕ) := w ab.1 * w ab.2
  have hQR : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have w_nonneg (a : ℕ) : 0 ≤ w a := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsingle (q : ℕ) (hq : q ∈ S) :
      min (1 : ℝ) ((q : ℝ)/Q) / (q.totient : ℝ) ≤
      (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ q.divisorsAntidiagonal, F ab := by
    have hq0 : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
    have hsum : (∑ ab ∈ q.divisorsAntidiagonal, F ab) = (q.divisors.card : ℝ) * w q := by
      calc
        _ = ∑ _ab ∈ q.divisorsAntidiagonal, w q := by
          apply sum_congr rfl
          intro ab hab
          unfold F w
          rw [← Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
            ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp hab).1]
        _ = _ := by
          rw [Nat.sum_divisorsAntidiagonal (fun _ _ => w q)]
          simp
    rw [hsum]
    calc
      min (1 : ℝ) ((q : ℝ)/Q) / (q.totient : ℝ) ≤
          ((q : ℝ)/Q)^(1/32:ℝ) * (1/(q.totient : ℝ)) := by
            rw [mul_one_div]
            exact div_le_div_of_nonneg_right (rankin_min _ (div_pos hqr hQR)) (Nat.cast_nonneg _)
      _ ≤ ((q : ℝ)/Q)^(1/32:ℝ) * ((q.divisors.card : ℝ)/q) :=
        mul_le_mul_of_nonneg_left (reciprocal_totient q hq0) (Real.rpow_nonneg (div_pos hqr hQR).le _)
      _ = _ := by
        rw [Real.div_rpow hqr.le hQR.le, Real.rpow_neg hQR.le]
        simp only [w, Real.rpow_sub hqr, Real.rpow_one]
        ring
  have hdisj : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint a.divisorsAntidiagonal b.divisorsAntidiagonal := by
    intro a _ b _ hab
    apply disjoint_left.mpr
    intro ab ha hb
    exact hab ((Nat.mem_divisorsAntidiagonal.mp ha).1.symm.trans (Nat.mem_divisorsAntidiagonal.mp hb).1)
  have hsub : S.biUnion Nat.divisorsAntidiagonal ⊆ S ×ˢ S := by
    intro ab hab
    obtain ⟨q, hq, habq⟩ := mem_biUnion.mp hab
    obtain ⟨hqI,hqS⟩ := mem_filter.mp hq
    obtain ⟨hqpos,hqle⟩ := mem_Icc.mp hqI
    have hd (d : ℕ) (hdq : d ∈ q.divisors) : d ∈ S := by
      have hdiv := Nat.dvd_of_mem_divisors hdq
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hdq, ?_⟩, ?_⟩
      · exact (Nat.le_of_dvd hqpos hdiv).trans hqle
      · exact fun p hp => hqS p (Nat.primeFactors_mono hdiv (by omega) hp)
    exact mem_product.mpr ⟨hd _ (Nat.fst_mem_divisors_of_mem_antidiagonal habq),
      hd _ (Nat.snd_mem_divisors_of_mem_antidiagonal habq)⟩
  change (∑ q ∈ S, _) ≤ (Q : ℝ)^(-(1/32:ℝ)) * (∑ a ∈ S, w a)^2
  calc
    _ ≤ ∑ q ∈ S, (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ q.divisorsAntidiagonal, F ab :=
      sum_le_sum hsingle
    _ = (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ S.biUnion Nat.divisorsAntidiagonal, F ab := by
      rw [← mul_sum, sum_biUnion hdisj]
    _ ≤ (Q : ℝ)^(-(1/32:ℝ)) * ∑ ab ∈ S ×ˢ S, F ab := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      apply sum_le_sum_of_subset_of_nonneg hsub
      exact fun ab _ _ => mul_nonneg (w_nonneg ab.1) (w_nonneg ab.2)
    _ = _ := by
      congr 1
      rw [Finset.sum_product, sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]

private noncomputable def rankinWeight : ℕ →* ℝ where
  toFun m := (m : ℝ) ^ ((1 / 32 : ℝ) - 1)
  map_one' := by simp
  map_mul' a b := by rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]

theorem finite_smooth_weight_le_product (y : ℕ) (S : Finset ℕ)
    (hS : ∀ m ∈ S, m ∈ Nat.smoothNumbers (y + 1)) :
    (∑ m ∈ S, (m : ℝ) ^ ((1 / 32 : ℝ) - 1)) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ ((1 / 32 : ℝ) - 1))⁻¹ := by
  classical
  have hin : ∀ {p : ℕ}, p.Prime → ‖rankinWeight p‖ < 1 := by
    intro p hp
    change ‖(p : ℝ) ^ ((1 / 32 : ℝ) - 1)‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by norm_num)
  have hs := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := rankinWeight) hin (y + 1)).2
  change (∑ m ∈ S, rankinWeight m) ≤ _
  rw [← S.sum_subtype_of_mem (fun m => rankinWeight m) hS]
  exact sum_le_hasSum _ (fun m _ => Real.rpow_nonneg (Nat.cast_nonneg (m : ℕ)) _) hs

theorem smooth_interval_weight_le_product (y N : ℕ) :
    (∑ m ∈ (Finset.Icc 1 N).filter (fun m => ∀ p ∈ m.primeFactors, p ≤ y),
        (m : ℝ) ^ ((1 / 32 : ℝ) - 1)) ≤
      ∏ p ∈ (y + 1).primesBelow, (1 - (p : ℝ) ^ ((1 / 32 : ℝ) - 1))⁻¹ := by
  apply finite_smooth_weight_le_product
  intro m hm
  obtain ⟨hrange, hfactors⟩ := Finset.mem_filter.mp hm
  have hmpos := (Finset.mem_Icc.mp hrange).1
  apply Nat.mem_smoothNumbers'.2
  intro p hp hpm
  exact Nat.lt_succ_of_le (hfactors p (Nat.mem_primeFactors.mpr ⟨hp, hpm, by omega⟩))

private theorem factor_bound {p : ℕ} (hp : Nat.Prime p) :
    let t := (p : ℝ)^((1/32:ℝ)-1)
    0 < 1-t ∧ (1-t)⁻¹ ≤ Real.exp (4*t) := by
  let t := (p : ℝ)^((1/32:ℝ)-1)
  change 0 < 1-t ∧ _
  have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0:ℝ) < p := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hp0.le _
  have ht2 : t*t ≤ (p:ℝ)⁻¹ := by
    dsimp [t]
    rw [← Real.rpow_add hp0, ← Real.rpow_neg_one]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num
  have hinv : (p:ℝ)⁻¹ ≤ 1/2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have h34 : t ≤ 3/4 := by nlinarith
  have hpos : 0 < 1-t := by linarith
  refine ⟨hpos, le_trans ?_ (Real.add_one_le_exp (4*t))⟩
  rw [inv_eq_one_div, div_le_iff₀ hpos]
  nlinarith [mul_nonneg ht0 (show 0 ≤ 3-4*t by linarith)]

/-- Compare the logarithm of the Euler product with a weighted harmonic sum. -/
theorem eulerProduct_le (y : ℕ) (hy : 1 ≤ y) :
    (∏ p ∈ (y+1).primesBelow, (1 - (p:ℝ)^((1/32:ℝ)-1))⁻¹) ≤
      Real.exp (500 * (y:ℝ)^(1/16:ℝ)) := by
  let P := (y+1).primesBelow
  let t (p : ℕ) := (p:ℝ)^((1/32:ℝ)-1)
  have hsub : P ⊆ Icc 1 y := by
    intro p hp
    obtain ⟨hpy,hpp⟩ := Nat.mem_primesBelow.mp hp
    exact mem_Icc.mpr ⟨hpp.one_le, Nat.le_of_lt_succ hpy⟩
  have hy1 : (1:ℝ) ≤ y := by exact_mod_cast hy
  have hy0 : (0:ℝ) < y := by linarith
  have hpow : 0 ≤ (y:ℝ)^(1/32:ℝ) := Real.rpow_nonneg hy0.le _
  have hlog : 1 + Real.log (y:ℝ) ≤ 32 * (y:ℝ)^(1/32:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hy0 (1/32:ℝ))
    rw [Real.log_rpow hy0] at h
    linarith
  have hs : (∑ p ∈ P, t p) ≤ 32 * (y:ℝ)^(1/16:ℝ) := by
    calc
      _ ≤ ∑ p ∈ P, (y:ℝ)^(1/32:ℝ) * (p:ℝ)⁻¹ := by
        apply sum_le_sum
        intro p hp
        have hpy : p ≤ y := (mem_Icc.mp (hsub hp)).2
        have hp0 : (0:ℝ) < p := by exact_mod_cast (mem_Icc.mp (hsub hp)).1
        dsimp only [t]
        rw [Real.rpow_sub hp0, Real.rpow_one, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp0.le (by exact_mod_cast hpy) (by norm_num)) (inv_nonneg.mpr hp0.le)
      _ = (y:ℝ)^(1/32:ℝ) * ∑ p ∈ P, (p:ℝ)⁻¹ := (mul_sum ..).symm
      _ ≤ (y:ℝ)^(1/32:ℝ) * ∑ p ∈ Icc 1 y, (p:ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)) hpow
      _ ≤ (y:ℝ)^(1/32:ℝ) * (1+Real.log (y:ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hpow
        simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] using harmonic_le_one_add_log y
      _ ≤ (y:ℝ)^(1/32:ℝ) * (32*(y:ℝ)^(1/32:ℝ)) := mul_le_mul_of_nonneg_left hlog hpow
      _ = 32 * (y:ℝ)^(1/16:ℝ) := by
        rw [show (1/16:ℝ)=1/32+1/32 by norm_num, Real.rpow_add hy0]; ring
  calc
    _ ≤ ∏ p ∈ P, Real.exp (4*t p) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        exact inv_nonneg.mpr (factor_bound (Nat.prime_of_mem_primesBelow hp)).1.le
      · intro p hp
        exact (factor_bound (Nat.prime_of_mem_primesBelow hp)).2
    _ = Real.exp (4*∑ p ∈ P, t p) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      linarith [Real.rpow_nonneg hy0.le (1/16:ℝ)]

/-- Exponential growth of Q in its binary logarithm absorbs the square-root
growth in the exponent of the smooth Euler product. -/
theorem eventual_rankin_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N,
      let Q : ℕ := (Nat.log 2 (n + 2)) ^ 2
      let Y : ℕ := (1 + Nat.log 2 Q) ^ 8
      (Q : ℝ) ^ (-(1 / 32 : ℝ)) *
        (Real.exp (500 * (Y : ℝ) ^ (1 / 16 : ℝ))) ^ 2 ≤ ε := by
  obtain ⟨b, hb⟩ := exists_nat_ge (128 * (32000001 - Real.log ε))
  refine ⟨2 ^ (2 ^ b), fun n hn => ?_⟩
  let L := Nat.log 2 (n + 2)
  let Q : ℕ := L ^ 2
  let k := Nat.log 2 Q
  have hLb : 2 ^ b ≤ L :=
    Nat.le_log_of_pow_le (by decide) (hn.trans (by omega))
  have hL : 1 ≤ L := (Nat.one_le_two_pow (n := b)).trans hLb
  have hQ : L ≤ Q := by dsimp [Q]; nlinarith
  have hk : b ≤ k := Nat.le_log_of_pow_le (by decide) (hLb.trans hQ)
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hdyadic : (2 : ℝ) ^ k ≤ Q := by
    exact_mod_cast Nat.pow_log_le_self 2 (show Q ≠ 0 by omega)
  have hlog := Real.log_le_log (by positivity) hdyadic
  rw [Real.log_pow] at hlog
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hklog : (k : ℝ) / 2 ≤ Real.log Q := by
    calc
      (k : ℝ) / 2 = (k : ℝ) * (1 / 2) := by ring
      _ ≤ (k : ℝ) * Real.log 2 := by gcongr
      _ ≤ Real.log Q := hlog
  have hrpow : ((((1 + k)^8 : ℕ) : ℝ) ^ (1 / 16 : ℝ)) =
      Real.sqrt (1 + (k : ℝ)) := by
    push_cast
    rw [← Real.rpow_natCast_mul (by positivity), Real.sqrt_eq_rpow]
    norm_num
  change (Q : ℝ) ^ (-(1 / 32 : ℝ)) *
    (Real.exp (500 * ((((1 + k)^8 : ℕ) : ℝ) ^ (1 / 16 : ℝ)))) ^ 2 ≤ ε
  rw [hrpow, Real.rpow_def_of_pos hQpos, sq, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_log hε, Real.exp_le_exp]
  have hb' : (b : ℝ) ≤ k := by exact_mod_cast hk
  -- Completing the square absorbs the square root into the linear decay in k.
  have hs := sq_nonneg (Real.sqrt (1 + (k : ℝ)) - 64000)
  nlinarith [Real.sq_sqrt (show 0 ≤ 1 + (k : ℝ) by positivity)]

end GoldbachSmoothModuli

theorem Conjectures.Goldbach.PacketSmoothModuliWeight :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε := by
  dsimp only
  intro ε hε
  obtain ⟨N, hN⟩ := GoldbachSmoothModuli.eventual_rankin_budget ε hε
  refine ⟨N, fun n hn => ?_⟩
  let Q : ℕ := (Nat.log 2 (n + 2)) ^ 2
  let Y : ℕ := (1 + Nat.log 2 Q) ^ 8
  have hlog : 1 ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hQ : 1 ≤ Q := Nat.pow_pos hlog
  have hY : 1 ≤ Y := Nat.pow_pos (by omega : 0 < 1 + Nat.log 2 Q)
  have he := (GoldbachSmoothModuli.smooth_interval_weight_le_product Y (Q^2)).trans
    (GoldbachSmoothModuli.eulerProduct_le Y hY)
  refine (GoldbachSmoothModuli.smooth_convolution_bound Q Y hQ).trans (le_trans ?_ (hN n hn))
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg Q) _)
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ => Real.rpow_nonneg (Nat.cast_nonneg a) _)) he 2
