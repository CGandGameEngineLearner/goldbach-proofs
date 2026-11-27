import Mathlib

/-!
# Weighted short-order center count

The large-prime denominator estimate below adapts the project's Apache-2.0
`research/reference-proofs/fixed-budget-packet.lean` (PR #2327). Its declarations
are scoped to this proof. The smooth estimate reuses the Rankin proof for
`L-goldbach-packet-smooth-moduli-weight` (PR #3341); the reciprocal-totient comparison
follows `L_goldbach_frontier_medcore_bv_band` in the same project.
-/

namespace GoldbachShortOrderCount
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

private theorem smoothDenominatorWeight :
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

private theorem shortlistedNumerators (q : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((range (q+1)).filter (fun a => a.Coprime q ∧ P a)).card ≤ 2*q.totient := by
  by_cases h : q = 1
  · subst q
    simpa using ((range 2).card_filter_le (fun a => a.Coprime 1 ∧ P a))
  · have hincl : (range (q+1)).filter (fun a => a.Coprime q ∧ P a) ⊆
        (range q).filter (fun a => q.Coprime a) := by
      intro a ha
      obtain ⟨ha, hac, _⟩ := mem_filter.mp ha
      have hne : a ≠ q := by
        rintro rfl
        exact h (by simpa using hac)
      exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp ha; omega), hac.symm⟩
    exact (card_le_card hincl).trans (by rw [← Nat.totient_eq_card_coprime]; omega)

private theorem totalPopulationBound (T : Finset ℕ) (o smooth : ℕ → Prop)
    [DecidablePred o] [DecidablePred smooth] (w : ℕ → ℝ) (hw : ∀ q, 0 ≤ w q) :
    (∑ q ∈ T.filter o, w q) ≤ (∑ q ∈ T.filter smooth, w q) +
      (∑ q ∈ T.filter (fun q => o q ∧ ¬smooth q), w q) := by
  have hsub : (T.filter o).filter smooth ⊆ T.filter smooth := by
    intro q hq
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hq).1).1, (mem_filter.mp hq).2⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not (T.filter o) smooth w
  have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := w) hsub (fun i _ _ => hw i)
  simp only [filter_filter] at hsplit hle
  linarith

private theorem shortCentersFromModuli :
    (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; let smooth := fun n q : ℕ => ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q ∧ ¬smooth n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ))/(Nat.totient q:ℝ)) ≤ ε) → (let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε) := by
  classical
  let Q (n : ℕ) := (Nat.log 2 (n+2))^2
  let L (n : ℕ) := max 1 (Nat.log 2 n / 2)
  let K (n : ℕ) (t : ℝ) := (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ)
  let o (n q : ℕ) := q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty
  let smooth (n q : ℕ) := ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (Q n))^8
  let T (n : ℕ) := Finset.Icc 1 ((Q n)^2)
  let v (n q : ℕ) := min (1:ℝ) ((q:ℝ)/(Q n:ℝ))
  let w (n q : ℕ) := v n q / (q.totient:ℝ)
  intro hs hr
  dsimp only
  intro ε hε
  obtain ⟨Ns, hNs⟩ := hs (ε/4) (by linarith)
  obtain ⟨Nr, hNr⟩ := hr (ε/4) (by linarith)
  refine ⟨max Ns Nr, ?_⟩
  intro n hn
  have hs' : (∑ q ∈ (T n).filter (smooth n), w n q) ≤ ε/4 := hNs n ((le_max_left ..).trans hn)
  have hr' : (∑ q ∈ (T n).filter (fun q => o n q ∧ ¬smooth n q), w n q) ≤ ε/4 := hNr n ((le_max_right ..).trans hn)
  have hv (q : ℕ) : 0 ≤ v n q := le_min zero_le_one (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hw (q : ℕ) : 0 ≤ w n q := div_nonneg (hv q) (Nat.cast_nonneg _)
  have hpop := totalPopulationBound (T n) (o n) (smooth n) (w n) hw
  let P (q a : ℕ) := (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ))
  change (∑ q ∈ (T n).filter (o n), v n q * (((range (q+1)).filter (fun a => a.Coprime q ∧ P q a)).card:ℝ) / (q.totient:ℝ)^2) ≤ ε
  calc
    _ ≤ ∑ q ∈ (T n).filter (o n), 2 * w n q := by
      apply sum_le_sum
      intro q hq
      have hqpos : 0 < q := (mem_Icc.mp (mem_filter.mp hq).1).1
      have hφ : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hqpos
      have hc : (((range (q+1)).filter (fun a => a.Coprime q ∧ P q a)).card:ℝ) ≤ 2*(q.totient:ℝ) := by
        exact_mod_cast shortlistedNumerators q (P q)
      calc
        _ ≤ v n q * (2*(q.totient:ℝ)) / (q.totient:ℝ)^2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (hv q)) (sq_nonneg _)
        _ = _ := by dsimp only [w]; field_simp
    _ = 2 * ∑ q ∈ (T n).filter (o n), w n q := (Finset.mul_sum ..).symm
    _ ≤ ε := by linarith

namespace LargePrimes
noncomputable section

private def gridQ (n : ℕ) := (Nat.log 2 (n+2))^2

private abbrev lowOrderTest (n q : ℕ) := q % 2 = 1 ∧
  ((Finset.Icc 1 ((Nat.log 2 (gridQ n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty

private abbrev smoothTest (n q : ℕ) :=
  ∀ p ∈ q.primeFactors, p ≤ (1+Nat.log 2 (gridQ n))^8

private def denominatorWeight (n q : ℕ) := min (1:ℝ) ((q:ℝ)/(gridQ n:ℝ))/(q.totient:ℝ)

theorem periodPrimeBudget (H Y : ℕ) (hY : 0<Y) :
    (∑ j ∈ Finset.Icc 1 H, ∑ p ∈ ((2^j-1:ℕ).primeFactors.filter (fun p => Y<p)),
      1/((p:ℝ)-1)) ≤ (H:ℝ)^2/Y := by
  have one (j : ℕ) (hj : j ∈ Finset.Icc 1 H) :
      (∑ p ∈ ((2^j-1:ℕ).primeFactors.filter (fun p => Y<p)), 1/((p:ℝ)-1)) ≤ (H:ℝ)/(Y:ℝ) := by
    let M : ℕ := 2^j-1
    let primes := M.primeFactors
    let T := primes.filter (fun p => Y<p)
    have jpos := (Finset.mem_Icc.mp hj).1
    have jle := (Finset.mem_Icc.mp hj).2
    have Mpos : 0<M := by
      have two : 2 ≤ 2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) jpos
      dsimp [M]; omega
    have hc : 2^primes.card ≤ M := by
      calc
        _ = ∏ _p ∈ primes, (2:ℕ) := by simp
        _ ≤ ∏ p ∈ primes, p := Finset.prod_le_prod (fun p h => (Nat.prime_of_mem_primeFactors h).two_le)
        _ ≤ M := Nat.le_of_dvd Mpos (Nat.prod_primeFactors_dvd M)
    have card : primes.card ≤ j := by
      by_contra! hh
      have lower := Nat.pow_le_pow_right (by decide : 0<2) (show j+1 ≤ primes.card by omega)
      rw [pow_succ] at lower
      dsimp [M] at hc
      omega
    have cr : (T.card:ℝ) ≤ (H:ℝ) := by exact_mod_cast
      ((Finset.card_le_card (Finset.filter_subset _ primes)).trans card).trans jle
    change (∑ p ∈ T, _) ≤ _
    calc
      _ ≤ ∑ _p ∈ T, 1/(Y:ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hi : (Y:ℝ)+1 ≤ (p:ℝ) := by exact_mod_cast (Finset.mem_filter.mp hp).2
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      _ = (T.card:ℝ)/(Y:ℝ) := by simp [div_eq_mul_inv]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 H, (H:ℝ)/(Y:ℝ) := Finset.sum_le_sum one
    _ = _ := by simp [pow_two]; ring


private theorem fractionProduct (S : Finset ℕ) (hs : ∀ p ∈ S, 2≤p) :
    (∏ p ∈ S, (p:ℝ)/((p:ℝ)-1)) ≤ (S.card:ℝ)+1 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hmax ih =>
    have ha := hs a (Finset.mem_insert_self ..)
    have old (p : ℕ) (hp : p∈S) := hs p (Finset.mem_insert_of_mem hp)
    have ha' : 0 < (a:ℝ)-1 := by
      have h : (2:ℝ) ≤ a := by exact_mod_cast ha
      linarith
    have notMem : a ∉ S := fun h => (lt_irrefl a) (hmax a h)
    have sub : S ⊆ Finset.Ico 2 a := fun p hp => Finset.mem_Ico.mpr ⟨old p hp,hmax p hp⟩
    have count := Finset.card_le_card sub
    rw [Nat.card_Ico] at count
    have cr : (S.card:ℝ)+2 ≤ (a:ℝ) := by exact_mod_cast (show S.card+2≤a by omega)
    rw [Finset.prod_insert notMem,Finset.card_insert_of_notMem notMem,Nat.cast_add,Nat.cast_one]
    apply (mul_le_mul_of_nonneg_left (ih old) (div_nonneg (Nat.cast_nonneg _) ha'.le)).trans
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ ha').mpr
    linarith

private theorem totientLogLower (q : ℕ) (hq : 0<q) :
    (q:ℝ)/(q.totient:ℝ) ≤ (Nat.log 2 q:ℝ)+1 := by
  let S := q.primeFactors
  have hs (p : ℕ) (hp : p∈S) := (Nat.prime_of_mem_primeFactors hp).two_le
  have card : S.card ≤ Nat.log 2 q := by
    apply Nat.le_log_of_pow_le (by decide)
    calc
      _ = ∏ _p ∈ S, (2:ℕ) := by simp
      _ ≤ ∏ p ∈ S, p := Finset.prod_le_prod hs
      _ ≤ q := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
  have hf : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  have id : (q:ℝ)/(q.totient:ℝ) = ∏ p ∈ S, (p:ℝ)/((p:ℝ)-1) := by
    rw [Finset.prod_div_distrib]
    have pos : 0 < ∏ p ∈ S, ((p:ℝ)-1) := Finset.prod_pos (fun p hp => by
      have h : (2:ℝ)≤p := by exact_mod_cast hs p hp
      linarith)
    apply (div_eq_div_iff hf.ne' pos.ne').mpr
    have formula := congrArg (fun k : ℕ => (k:ℝ)) (Nat.totient_mul_prod_primeFactors q)
    simp only [Nat.cast_mul,Nat.cast_prod] at formula
    change (q:ℝ)*_ = _*(q.totient:ℝ)
    rw [mul_comm _ (q.totient:ℝ)]
    dsimp [S]
    rw [formula]
    congr 1
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (by have h := hs p hp; omega),Nat.cast_one]
  rw [id]
  exact (fractionProduct S hs).trans (by exact_mod_cast (show S.card+1≤Nat.log 2 q+1 by omega))

private theorem harmonicBlock (k : ℕ) :
    (∑ m ∈ Finset.range (2^k), 1/((m:ℝ)+1)) ≤ (k:ℝ)+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_two, Finset.sum_range_add]
    have block : (∑ j ∈ Finset.range (2^k), 1/(((2^k+j:ℕ):ℝ)+1)) ≤ 1 := by
      calc
        _ ≤ ∑ _j ∈ Finset.range (2^k), 1/((2:ℝ)^k) := by
          apply Finset.sum_le_sum
          intro j _
          apply one_div_le_one_div_of_le (by positivity)
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) j]
        _ = _ := by simp
    push_cast at block ⊢
    linarith only [ih,block]

theorem reciprocalTotientLogBound (X : ℕ) (_ : 0<X) :
    (∑ m ∈ Finset.Icc 1 X, 1/(m.totient:ℝ)) ≤ ((Nat.log 2 X:ℝ)+2)^2 := by
  let k := Nat.log 2 X
  have idx : Finset.Icc 1 X = (Finset.range X).map (addRightEmbedding 1) := by
    ext m
    simp only [Finset.mem_Icc,Finset.mem_map,Finset.mem_range,addRightEmbedding_apply]
    constructor
    · intro h; exact ⟨m-1,by omega,by omega⟩
    · rintro ⟨j,h,rfl⟩; omega
  have upper := (Nat.lt_pow_succ_log_self (by decide : 1<2) X).le
  have harm : (∑ m ∈ Finset.range X, 1/((m:ℝ)+1)) ≤ (k:ℝ)+2 := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono upper) (fun m _ _ => by positivity)).trans
    convert harmonicBlock (k+1) using 1; push_cast; ring
  rw [idx,Finset.sum_map]
  calc
    _ ≤ ∑ j ∈ Finset.range X, ((k:ℝ)+1)*(1/((j:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro j hj
      have le : j+1 ≤ X := Finset.mem_range.mp hj
      have hk : Nat.log 2 (j+1) ≤ k := Nat.log_mono_right le
      have b := totientLogLower (j+1) (by omega)
      have h : (((j+1:ℕ):ℝ)/((j+1).totient:ℝ)) ≤ (k:ℝ)+1 := b.trans (by exact_mod_cast (Nat.add_le_add_right hk 1))
      change 1/((j+1).totient:ℝ) ≤ _
      rw [mul_one_div]
      apply (le_div_iff₀ (by positivity)).mpr
      push_cast at h
      simpa only [one_div,div_eq_mul_inv,one_mul,mul_one,mul_comm] using h
    _ = ((k:ℝ)+1)*_ := (Finset.mul_sum ..).symm
    _ ≤ ((k:ℝ)+1)*((k:ℝ)+2) := mul_le_mul_of_nonneg_left harm (by positivity)
    _ ≤ _ := by dsimp [k]; nlinarith only [Nat.cast_nonneg (α := ℝ) (Nat.log 2 X)]


private theorem chargeWitnesses {α β : Type*} [DecidableEq β]
    (S : Finset β) (T : Finset α) (key : α → β) (w : β → ℝ) (v : α → ℝ)
    (pos : ∀ a∈T, 0≤v a) (charge : ∀ b∈S, ∃ a∈T, key a=b ∧ w b≤v a) :
    (∑ b ∈ S, w b) ≤ ∑ a ∈ T, v a := by
  calc
    _ ≤ ∑ b ∈ S, ∑ a ∈ T, if key a=b then v a else 0 := by
      apply Finset.sum_le_sum
      intro b hb
      obtain ⟨a,ha,e,h⟩ := charge b hb
      apply h.trans
      simpa only [e,ite_true] using Finset.single_le_sum
        (s := T) (f := fun x => if key x=b then v x else 0)
        (fun x hx => by split <;> first | exact pos x hx | exact le_rfl) ha
    _ = ∑ a ∈ T, ∑ b ∈ S, if key a=b then v a else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases h : key a ∈ S <;> simp [h,pos a ha]

private theorem largePeriodWeightFinite (n : ℕ) :
    (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => lowOrderTest n q ∧ ¬smoothTest n q),
      denominatorWeight n q) ≤
      (∑ m ∈ Finset.Icc 1 ((gridQ n)^2), 1/(m.totient:ℝ)) *
        (((1+Nat.log 2 (gridQ n):ℕ):ℝ)^4 / ((1+Nat.log 2 (gridQ n):ℕ):ℝ)^8) := by
  classical
  let u := 1+Nat.log 2 (gridQ n)
  let H := u^2
  let Y := u^8
  let X := (gridQ n)^2
  let D := Finset.Icc 1 X
  let J := Finset.Icc 1 H
  let Ps := fun j : ℕ => (2^j-1:ℕ).primeFactors.filter (fun p => Y<p)
  let T : Finset (Σ _j : ℕ, ℕ × ℕ) := J.sigma (fun j => Ps j ×ˢ D)
  let S := D.filter (fun q => lowOrderTest n q ∧ ¬smoothTest n q)
  let v := fun a : (Σ _j : ℕ, ℕ × ℕ) => (1/((a.2.1:ℝ)-1))*(1/(a.2.2.totient:ℝ))
  let M := ∑ m ∈ D, 1/(m.totient:ℝ)
  have vpos (a : Σ _j : ℕ, ℕ × ℕ) (ha : a∈T) : 0≤v a := by
    have h := (Finset.mem_product.mp (Finset.mem_sigma.mp ha).2).1
    have hp := (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp h).1).two_le
    have hp' : (2:ℝ)≤a.2.1 := by exact_mod_cast hp
    exact mul_nonneg (one_div_nonneg.mpr (by linarith)) (one_div_nonneg.mpr (Nat.cast_nonneg _))
  have witnesses (q : ℕ) (hq : q∈S) : ∃ a∈T, a.2.1*a.2.2=q ∧ denominatorWeight n q≤v a := by
    obtain ⟨hd,hshort,hnsm⟩ := Finset.mem_filter.mp hq
    change ¬∀ p ∈ q.primeFactors, p≤Y at hnsm
    push Not at hnsm
    obtain ⟨p,hp,hY⟩ := hnsm
    obtain ⟨j,hj⟩ := hshort.2
    obtain ⟨hjrange,dvd⟩ := Finset.mem_filter.mp hj
    have hj' : j ∈ J := by simpa only [J,H,u,Nat.add_comm 1] using hjrange
    have pPrime := Nat.prime_of_mem_primeFactors hp
    have dp := Nat.dvd_of_mem_primeFactors hp
    obtain ⟨m,eq⟩ := dp
    have qpos : 0<q := (Finset.mem_Icc.mp hd).1
    have mpos : 0< m := Nat.pos_of_ne_zero (fun e => (Nat.ne_of_gt qpos) (by simp [eq,e]))
    have mQ : m≤q := Nat.le_of_dvd qpos ⟨p,by simpa only [mul_comm] using eq⟩
    have hpos : 0<(2^j-1:ℕ) := by
      have two : 2≤2^j := by simpa using Nat.pow_le_pow_right (by decide : 0<2) (Finset.mem_Icc.mp hj').1
      omega
    have pm : p∈Ps j := Finset.mem_filter.mpr ⟨pPrime.mem_primeFactors ((Nat.dvd_of_mem_primeFactors hp).trans dvd) hpos.ne',hY⟩
    refine ⟨⟨j,(p,m)⟩, Finset.mem_sigma.mpr ⟨hj', Finset.mem_product.mpr ⟨pm,Finset.mem_Icc.mpr ⟨mpos,mQ.trans (Finset.mem_Icc.mp hd).2⟩⟩⟩,eq.symm, ?_⟩
    have phip : 0<(p.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr pPrime.pos
    have phim : 0<(m.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr mpos
    have phi : (p.totient:ℝ)*(m.totient:ℝ) ≤ (q.totient:ℝ) := by rw [eq]; exact_mod_cast Nat.totient_super_multiplicative p m
    have phiq : 0<(q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr qpos
    have primeId : (p.totient:ℝ)=(p:ℝ)-1 := by
      rw [Nat.totient_prime pPrime,Nat.cast_sub (by have := pPrime.two_le; omega),Nat.cast_one]
    calc
      _ ≤ 1/(q.totient:ℝ) := div_le_div_of_nonneg_right (min_le_left ..) phiq.le
      _ ≤ 1/((p.totient:ℝ)*(m.totient:ℝ)) := one_div_le_one_div_of_le (mul_pos phip phim) phi
      _ = _ := by dsimp [v]; rw [primeId]; simp only [one_div,mul_inv_rev,mul_comm]
  have eq : (∑ a ∈ T, v a) = M*(∑ j ∈ J, ∑ p ∈ Ps j, 1/((p:ℝ)-1)) := by
    dsimp only [T]
    rw [Finset.sum_sigma,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_product,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [v]
    rw [← Finset.mul_sum,mul_comm]
  have ub := periodPrimeBudget H Y (by dsimp [H,Y,u]; positivity)
  have conv : (H:ℝ)^2/(Y:ℝ) = (u:ℝ)^4/(u:ℝ)^8 := by dsimp [H,Y]; push_cast; ring
  rw [conv] at ub
  apply (chargeWitnesses S T (fun a => a.2.1*a.2.2) (denominatorWeight n) v vpos witnesses).trans
  rw [eq]
  exact mul_le_mul_of_nonneg_left ub (Finset.sum_nonneg fun _ _ => by positivity)

theorem shortPeriodLargePrimeWeight : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N,
    (∑ q ∈ (Finset.Icc 1 ((gridQ n)^2)).filter (fun q => lowOrderTest n q ∧ ¬smoothTest n q),
      denominatorWeight n q) ≤ ε := by
  intro ε hε
  obtain ⟨M,hM⟩ := exists_nat_ge (16/ε)
  refine ⟨2^(2^M), ?_⟩
  intro n hn
  let Q := gridQ n
  let u := 1+Nat.log 2 Q
  have hlog : 2^M ≤ Nat.log 2 (n+2) := Nat.le_log_of_pow_le (by decide) (by omega)
  have hQ : 2^M ≤ Q := by dsimp [Q,gridQ]; nlinarith [Nat.le_mul_self (Nat.log 2 (n+2))]
  have qpos : 0<Q := lt_of_lt_of_le (by positivity : 0<2^M) hQ
  have hu : M ≤ u := by have h := Nat.le_log_of_pow_le (by decide : 1<2) hQ; dsimp [u]; omega
  have u1 : (1:ℝ) ≤ u := by exact_mod_cast (show 1≤u by dsimp [u]; omega)
  have upos : (0:ℝ)<u := by linarith
  have cap := Nat.lt_pow_succ_log_self (by decide : 1<2) Q
  have cap' : Q < 2^u := by simpa only [u,Nat.add_comm 1] using cap
  have both : Q^2 < 2^(2*u) := by
    rw [mul_comm 2 u,pow_mul]
    exact Nat.pow_lt_pow_left cap' (by decide)
  have hL : Nat.log 2 (Q^2) < 2*u := by
    by_contra! hh
    have power := Nat.pow_le_pow_right (by decide : 0<2) hh
    have b := Nat.pow_log_le_self 2 (by positivity : Q^2≠0)
    omega
  have hR : (Nat.log 2 (Q^2):ℝ)+2 ≤ 4*(u:ℝ) := by exact_mod_cast (show Nat.log 2 (Q^2)+2≤4*u by omega)
  have hb := (reciprocalTotientLogBound (Q^2) (by positivity)).trans (pow_le_pow_left₀ (by positivity) hR 2)
  apply (largePeriodWeightFinite n).trans
  change _ * ((u:ℝ)^4/(u:ℝ)^8) ≤ ε
  apply (mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ (u:ℝ)^4/(u:ℝ)^8)).trans
  have limit : 16 ≤ ε*(u:ℝ) := by
    have h := (div_le_iff₀ hε).mp (hM.trans (by exact_mod_cast hu : (M:ℝ) ≤ u))
    linarith
  calc
    _ = 16/(u:ℝ)^2 := by field_simp; ring
    _ ≤ 16/(u:ℝ) := div_le_div_of_nonneg_left (by norm_num) upos (by nlinarith [sq_nonneg ((u:ℝ)-1)])
    _ ≤ ε := (div_le_iff₀ upos).mpr limit

end
end LargePrimes
end GoldbachShortOrderCount

open GoldbachShortOrderCount in
theorem Conjectures.Goldbach.PacketShortOrderCenterCount :
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let L := fun n : ℕ => max 1 (Nat.log 2 n / 2); let K := fun (n : ℕ) (t : ℝ) => (∑ j ∈ Finset.range (L n), Real.cos (2*Real.pi*(2:ℝ)^(j+1)*t))/(L n:ℝ); let o := fun n q : ℕ => q % 2 = 1 ∧ ((Finset.Icc 1 ((Nat.log 2 (Q n)+1)^2)).filter (fun j => q ∣ 2^j-1)).Nonempty; ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n ≥ N, (∑ q ∈ (Finset.Icc 1 ((Q n)^2)).filter (fun q => o n q), min (1:ℝ) ((q:ℝ)/(Q n:ℝ)) * (((Finset.range (q+1)).filter (fun a => Nat.Coprime a q ∧ (1:ℝ)/3 < K n ((a:ℝ)/(q:ℝ)))).card:ℝ) / (Nat.totient q:ℝ)^2) ≤ ε := by
  exact shortCentersFromModuli smoothDenominatorWeight
    LargePrimes.shortPeriodLargePrimeWeight
