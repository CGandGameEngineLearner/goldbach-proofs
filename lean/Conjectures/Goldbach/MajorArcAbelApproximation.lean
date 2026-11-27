import Mathlib

/-!
# Goldbach gap `L-goldbach-major-arc-abel-approximation`

Dirichlet model approximation on a major arc `a/q + β` via discrete Abel summation
on each reduced residue class `r (mod q)`. Primes in non-coprime residue classes divide `q`,
so their total log-weight is at most `log q` independently of `β`.
-/

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Polynomial ArithmeticFunction

namespace Conjectures.Goldbach.MajorArcAbelApproximation_aux

private theorem sumPrimitive (n : ℕ) :
    (∑ z ∈ primitiveRoots n ℂ, z) = (μ n : ℂ) := by
  classical
  let F : ArithmeticFunction ℂ := ⟨fun k => ∑ z ∈ primitiveRoots k ℂ, z, by simp⟩
  have hF : F * (ζ : ArithmeticFunction ℂ) = 1 := by
    ext k
    by_cases hk : k = 0
    · subst k
      simp
    let : NeZero k := ⟨hk⟩
    have hk' := Nat.pos_of_ne_zero hk
    let z := Complex.exp (2 * Real.pi * Complex.I / k)
    have hz : IsPrimitiveRoot z k := Complex.isPrimitiveRoot_exp k hk
    rw [coe_mul_zeta_apply]
    change (∑ i ∈ k.divisors, ∑ t ∈ primitiveRoots i ℂ, t) = _
    rw [← Finset.sum_biUnion (fun i _ j _ hij => IsPrimitiveRoot.disjoint hij),
      ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
    have hall : (∑ j ∈ Finset.range k, z ^ j) = ∑ t ∈ nthRootsFinset k (1 : ℂ), t := by
      apply Finset.sum_bij (fun j _ => z ^ j)
      · intro j _
        apply (mem_nthRootsFinset hk' _).mpr
        rw [← pow_mul, Nat.mul_comm, pow_mul, hz.pow_eq_one, one_pow]
      · intro i hi j hj eq
        exact hz.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) eq
      · intro x hx
        obtain ⟨j, hj, he⟩ := hz.eq_pow_of_pow_eq_one ((mem_nthRootsFinset hk' _).mp hx)
        exact ⟨j, Finset.mem_range.mpr hj, he⟩
      · intros
        rfl
    rw [← hall]
    by_cases h : k = 1
    · subst k
      simp
    · rw [hz.geom_sum_eq_zero (by omega)]
      simp [h]
  have hμ : F = (μ : ArithmeticFunction ℂ) := by
    calc
      F = (F * (ζ : ArithmeticFunction ℂ)) * (μ : ArithmeticFunction ℂ) := by
        rw [mul_assoc, coe_zeta_mul_coe_moebius, mul_one]
      _ = _ := by rw [hF, one_mul]
  exact congrArg (fun f : ArithmeticFunction ℂ => f n) hμ

private theorem ramanujan (q a : ℕ) (hq : 0 < q) (ha : a.Coprime q) :
    (∑ r ∈ (Finset.range q).filter (fun r => Nat.Coprime r q),
      Complex.exp (((2 * Real.pi * ((r : ℝ) * (a : ℝ) / q) : ℝ) : ℂ) * Complex.I)) =
        (μ q : ℂ) := by
  classical
  let : NeZero q := ⟨hq.ne'⟩
  let θ : ℂ := 2 * Real.pi * Complex.I * ((a : ℂ) / q)
  have hz : IsPrimitiveRoot (Complex.exp θ) q :=
    Complex.isPrimitiveRoot_exp_of_coprime a q hq.ne' ha
  rw [← sumPrimitive q]
  apply Finset.sum_bij (fun i _ => Complex.exp θ ^ i)
  · intro i hi
    exact (mem_primitiveRoots hq).mpr (hz.pow_of_coprime i (Finset.mem_filter.mp hi).2)
  · intro i hi j hj
    exact hz.pow_inj (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
      (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)
  · intro x hx
    obtain ⟨i, hi, hc, he⟩ := hz.isPrimitiveRoot_iff.mp ((mem_primitiveRoots hq).mp hx)
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi, hc⟩, he⟩
  · intro i _
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp [θ]
    push_cast
    ring

end Conjectures.Goldbach.MajorArcAbelApproximation_aux

theorem Conjectures.Goldbach.MajorArcAbelApproximation :
    let w (k : ℕ) := if Nat.Prime k then Real.log (k : ℝ) else 0; let E (x : ℝ) := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I); let S (n : ℕ) (t : ℝ) := ∑ k ∈ Finset.range (n + 1), (w k : ℂ) * E ((k : ℝ) * t); let ap (q r m : ℕ) := ∑ k ∈ (Finset.range (m + 1)).filter (fun k => k % q = r), w k; let K1 (n : ℕ) (b : ℝ) := ∑ k ∈ Finset.Icc 1 n, E ((k : ℝ) * b); ∀ (n q a : ℕ) (β e : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ e → (∀ m : ℕ, 1 ≤ m → m ≤ n → ∀ r < q, Nat.Coprime r q → |ap q r m - (m : ℝ) / (Nat.totient q : ℝ)| ≤ e) → ‖S n ((a : ℝ) / q + β) - ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β‖ ≤ Real.log (q : ℝ) + (Nat.totient q : ℝ) * e * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
  intro w E S ap K1 n q a β e hq ha he hdisc
  have hq_pos : 0 < q := by omega
  have hφ_pos : 0 < Nat.totient q := Nat.totient_pos.mpr hq_pos
  have hφ_ne : (Nat.totient q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hφ_pos.ne'
  have hφ_nonneg : (0 : ℝ) ≤ (Nat.totient q : ℝ) := Nat.cast_nonneg _
  have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  by_cases hn0 : n = 0
  · subst hn0
    have hw0 : w 0 = 0 := by simp [w]
    have hS0 : S 0 ((a : ℝ) / q + β) = 0 := by simp [S, hw0]
    have hK0 : K1 0 β = 0 := by simp [K1]
    rw [hS0, hK0, mul_zero, sub_zero, norm_zero]
    have hrhs : 0 ≤ (Nat.totient q : ℝ) * e * (1 + 2 * Real.pi * ((0 : ℕ) : ℝ) * |β|) := by
      positivity
    linarith
  have hn_pos : 1 ≤ n := Nat.pos_of_ne_zero hn0
  have hEmul : ∀ x y : ℝ, E x * E y = E (x + y) := by
    intro x y
    simp only [E, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hEnat : ∀ m : ℕ, E (m : ℝ) = 1 := by
    intro m
    simp only [E]
    rw [show (((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I) =
      (m : ℂ) * (2 * ↑Real.pi * Complex.I) by push_cast; ring]
    rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  have hEnorm : ∀ x : ℝ, ‖E x‖ = 1 := fun x => Complex.norm_exp_ofReal_mul_I _
  have hEmod : ∀ k r : ℕ, k % q = r →
      E ((k : ℝ) * ((a : ℝ) / q)) = E ((r : ℝ) * (a : ℝ) / q) := by
    intro k r hkr
    have hkdiv : k = q * (k / q) + r := by
      rw [← hkr]
      exact (Nat.div_add_mod k q).symm
    have hk_eq : (k : ℝ) * ((a : ℝ) / q) = ((k / q * a : ℕ) : ℝ) + (r : ℝ) * (a : ℝ) / q := by
      have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
      have hkR : (k : ℝ) = (q : ℝ) * ((k / q : ℕ) : ℝ) + (r : ℝ) := by
        exact_mod_cast hkdiv
      rw [hkR]
      push_cast
      field_simp [hqR]
    rw [hk_eq, ← hEmul, hEnat, one_mul]
  have hdiff_E : ‖1 - E β‖ ≤ 2 * Real.pi * |β| := by
    have hnormSq : ‖1 - E β‖ ^ 2 =
        (1 - Real.cos (2 * Real.pi * β)) ^ 2 + (-Real.sin (2 * Real.pi * β)) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [E, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
        Complex.exp_ofReal_mul_I, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add, zero_sub]
      ring
    have hcos2 : Real.cos (2 * Real.pi * β) = 1 - 2 * (Real.sin (Real.pi * β)) ^ 2 := by
      have h := Real.cos_two_mul (Real.pi * β)
      rw [show 2 * (Real.pi * β) = 2 * Real.pi * β by ring] at h
      have hcs := Real.cos_sq_add_sin_sq (Real.pi * β)
      linarith
    have hcs2 := Real.cos_sq_add_sin_sq (2 * Real.pi * β)
    have htrig : (1 - Real.cos (2 * Real.pi * β)) ^ 2 + (-Real.sin (2 * Real.pi * β)) ^ 2 =
        4 * (Real.sin (Real.pi * β)) ^ 2 := by
      nlinarith
    have hsin_le : |Real.sin (Real.pi * β)| ≤ Real.pi * |β| := by
      calc
        |Real.sin (Real.pi * β)| ≤ |Real.pi * β| := Real.abs_sin_le_abs
        _ = Real.pi * |β| := by rw [abs_mul, abs_of_pos Real.pi_pos]
    have hsq_le : ‖1 - E β‖ ^ 2 ≤ (2 * Real.pi * |β|) ^ 2 := by
      rw [hnormSq, htrig]
      have h1 : (Real.sin (Real.pi * β)) ^ 2 ≤ (Real.pi * |β|) ^ 2 := by
        rw [← sq_abs (Real.sin (Real.pi * β))]
        exact sq_le_sq' (by linarith [abs_nonneg (Real.sin (Real.pi * β))]) hsin_le
      nlinarith
    have hnonneg : 0 ≤ 2 * Real.pi * |β| := by positivity
    nlinarith [norm_nonneg (1 - E β)]
  -- Rewrite `S n` as a sum over `Icc 1 n`, then fiberwise over `r ∈ range q`.
  have hw_nonneg : ∀ k : ℕ, 0 ≤ w k := by
    intro k
    by_cases hp : Nat.Prime k
    · simp only [w, hp, ↓reduceIte]
      exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    · simp [w, hp]
  have hS_icc : S n ((a : ℝ) / q + β) =
      ∑ k ∈ Finset.Icc 1 n, (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β) := by
    have hr : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
      ext k
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    have h0_mem : (0 : ℕ) ∉ Finset.Icc 1 n := by simp
    have hw0 : w 0 = 0 := by simp [w]
    dsimp only [S]
    rw [hr, Finset.sum_insert h0_mem, hw0, Complex.ofReal_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, hEmul]
    congr 2
    ring
  have hmaps : ∀ k ∈ Finset.Icc 1 n, k % q ∈ Finset.range q := fun k _ =>
    Finset.mem_range.mpr (Nat.mod_lt k hq_pos)
  have hS_fib : S n ((a : ℝ) / q + β) =
      ∑ r ∈ Finset.range q,
        ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r),
          (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β) := by
    rw [hS_icc]
    exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  let Rcop := (Finset.range q).filter (fun r => Nat.Coprime r q)
  let Rnon := (Finset.range q).filter (fun r => ¬ Nat.Coprime r q)
  have hS_split : S n ((a : ℝ) / q + β) =
      (∑ r ∈ Rcop, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r),
        (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β)) +
      (∑ r ∈ Rnon, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r),
        (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β)) := by
    rw [hS_fib]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range q) (fun r => Nat.Coprime r q) _).symm
  -- Bound the non-coprime classes by `Real.log (q : ℝ)`.
  have hnon_bound :
      ‖∑ r ∈ Rnon, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r),
        (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β)‖ ≤ Real.log (q : ℝ) := by
    have h1 :
        ‖∑ r ∈ Rnon, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r),
          (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β)‖ ≤
        ∑ r ∈ Rnon, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r), w k := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, norm_mul, hEnorm, hEnorm, mul_one, mul_one, Complex.norm_real,
        Real.norm_of_nonneg (hw_nonneg k)]
    have h2 :
        (∑ r ∈ Rnon, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r), w k) =
        ∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ Nat.Coprime (k % q) q), w k := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (s := (Finset.Icc 1 n).filter (fun k => ¬ Nat.Coprime (k % q) q))
        (t := Rnon) (g := fun k => k % q) ?_ w]
      · refine Finset.sum_congr rfl fun r hr => Finset.sum_congr ?_ fun _ _ => rfl
        ext k
        simp only [Finset.mem_filter, Rnon, Finset.mem_range] at hr ⊢
        exact ⟨fun h => ⟨⟨h.1, h.2 ▸ hr.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
      · intro k hk
        simp only [Finset.mem_filter, Rnon, Finset.mem_range] at hk ⊢
        exact ⟨Nat.mod_lt k hq_pos, hk.2⟩
    have hsub : ((Finset.Icc 1 n).filter (fun k => ¬ Nat.Coprime (k % q) q)).filter Nat.Prime ⊆
        q.primeFactors := by
      intro p hp
      simp only [Finset.mem_filter] at hp
      have hp_prime : Nat.Prime p := hp.2
      have hnotcop : ¬ Nat.Coprime (p % q) q := hp.1.2
      have hgcd : Nat.gcd q p = Nat.gcd (p % q) q := Nat.gcd_rec q p
      have hnotcop_pq : ¬ Nat.Coprime p q := by
        intro hcp
        apply hnotcop
        rw [Nat.Coprime, ← hgcd, Nat.gcd_comm]
        exact hcp
      have hdvd : p ∣ q := by
        by_contra hd
        exact hnotcop_pq (hp_prime.coprime_iff_not_dvd.mpr hd)
      exact Nat.mem_primeFactors.mpr ⟨hp_prime, hdvd, hq_pos.ne'⟩
    have h3 :
        (∑ k ∈ (Finset.Icc 1 n).filter (fun k => ¬ Nat.Coprime (k % q) q), w k) =
        ∑ p ∈ ((Finset.Icc 1 n).filter (fun k => ¬ Nat.Coprime (k % q) q)).filter Nat.Prime,
          Real.log (p : ℝ) := by
      rw [← Finset.sum_filter_add_sum_filter_not
        ((Finset.Icc 1 n).filter (fun k => ¬ Nat.Coprime (k % q) q)) Nat.Prime w]
      have hzero :
          (∑ k ∈ ((Finset.Icc 1 n).filter (fun k => ¬ Nat.Coprime (k % q) q)).filter
            (fun k => ¬ Nat.Prime k), w k) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        have hnp : ¬ Nat.Prime k := (Finset.mem_filter.mp hk).2
        simp [w, hnp]
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp).2
      simp [w, hp_prime]
    have h4 :
        (∑ p ∈ ((Finset.Icc 1 n).filter (fun k => ¬ Nat.Coprime (k % q) q)).filter Nat.Prime,
          Real.log (p : ℝ)) ≤ ∑ p ∈ q.primeFactors, Real.log (p : ℝ) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => ?_
      exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
    have h5 : (∑ p ∈ q.primeFactors, Real.log (p : ℝ)) ≤ Real.log (q : ℝ) := by
      have hne0 : ∀ p ∈ q.primeFactors, (p : ℝ) ≠ 0 := fun p hp =>
        Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
      rw [← Real.log_prod hne0]
      have hdvd : (∏ p ∈ q.primeFactors, p) ∣ q := Nat.prod_primeFactors_dvd q
      have hpos_prod : 0 < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun p hp =>
          (Nat.prime_of_mem_primeFactors hp).ne_zero)
      have hle_prod : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast Nat.le_of_dvd hq_pos hdvd
      push_cast at hpos_prod hle_prod ⊢
      exact Real.log_le_log hpos_prod hle_prod
    exact h1.trans (by linarith [h2, h3, h4, h5])
  -- Rewrite the Dirichlet model using `ramanujan`.
  have hram : (∑ r ∈ Rcop, E ((r : ℝ) * (a : ℝ) / q)) = (ArithmeticFunction.moebius q : ℂ) :=
    Conjectures.Goldbach.MajorArcAbelApproximation_aux.ramanujan q a hq_pos ha
  have hmodel :
      ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β =
      ∑ r ∈ Rcop, E ((r : ℝ) * (a : ℝ) / q) * ((1 / (Nat.totient q : ℂ)) * K1 n β) := by
    rw [← hram, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  -- Bound each reduced residue class `r ∈ Rcop` via discrete Abel summation.
  have hcop_class : ∀ r ∈ Rcop,
      ‖(∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r),
          (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β)) -
        E ((r : ℝ) * (a : ℝ) / q) * ((1 / (Nat.totient q : ℂ)) * K1 n β)‖ ≤
      e * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
    intro r hr
    have hr_lt : r < q := (Finset.mem_filter.mp hr).1 |> Finset.mem_range.mp
    have hr_cop : Nat.Coprime r q := (Finset.mem_filter.mp hr).2
    have hfactor1 :
        (∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r),
          (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β)) =
        E ((r : ℝ) * (a : ℝ) / q) *
          ∑ k ∈ Finset.Icc 1 n, (if k % q = r then (w k : ℂ) else 0) * E ((k : ℝ) * β) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hkr
      · rw [hEmod k r hkr]
        ring
      · ring
    have hfactor2 :
        E ((r : ℝ) * (a : ℝ) / q) * ((1 / (Nat.totient q : ℂ)) * K1 n β) =
        E ((r : ℝ) * (a : ℝ) / q) *
          ∑ k ∈ Finset.Icc 1 n, (1 / (Nat.totient q : ℂ)) * E ((k : ℝ) * β) := by
      congr 1
      dsimp only [K1]
      rw [Finset.mul_sum]
    rw [hfactor1, hfactor2, ← mul_sub, norm_mul, hEnorm, one_mul, ← Finset.sum_sub_distrib]
    let u : ℕ → ℝ := fun m => ap q r m - (m : ℝ) / (Nat.totient q : ℝ)
    have hu0 : u 0 = 0 := by
      have hw0 : w 0 = 0 := by simp [w]
      simp only [u, ap, Nat.cast_zero, zero_div, sub_zero, Finset.sum_filter]
      simp [hw0]
    have hu_bound : ∀ m : ℕ, m ≤ n → |u m| ≤ e := by
      intro m hmn
      by_cases hm0 : m = 0
      · subst hm0
        rw [hu0, abs_zero]
        exact he
      · exact hdisc m (Nat.pos_of_ne_zero hm0) hmn r hr_lt hr_cop
    have hstep : ∀ k : ℕ, 1 ≤ k →
        (if k % q = r then (w k : ℂ) else 0) * E ((k : ℝ) * β) -
          (1 / (Nat.totient q : ℂ)) * E ((k : ℝ) * β) =
        ((u k - u (k - 1) : ℝ) : ℂ) * E ((k : ℝ) * β) := by
      intro k hk
      have hap_step : ap q r k - ap q r (k - 1) = if k % q = r then w k else 0 := by
        have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
        dsimp only [ap]
        rw [hk1, Finset.sum_filter, Finset.sum_filter, Finset.sum_range_succ]
        ring
      have hlin_step : (k : ℝ) / (Nat.totient q : ℝ) - ((k - 1 : ℕ) : ℝ) / (Nat.totient q : ℝ) =
          1 / (Nat.totient q : ℝ) := by
        have hφR : (Nat.totient q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hφ_pos.ne'
        have hk_cast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
          rw [Nat.cast_sub hk, Nat.cast_one]
        rw [hk_cast]
        field_simp [hφR]
        ring
      have hu_diff : u k - u (k - 1) = (if k % q = r then w k else 0) - 1 / (Nat.totient q : ℝ) := by
        dsimp only [u]
        linarith [hap_step, hlin_step]
      rw [← sub_mul, hu_diff]
      push_cast
      split_ifs <;> simp
    have hsum_eq :
        (∑ k ∈ Finset.Icc 1 n, ((if k % q = r then (w k : ℂ) else 0) * E ((k : ℝ) * β) -
          (1 / (Nat.totient q : ℂ)) * E ((k : ℝ) * β))) =
        ∑ k ∈ Finset.Icc 1 n, ((u k - u (k - 1) : ℝ) : ℂ) * E ((k : ℝ) * β) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      exact hstep k (Finset.mem_Icc.mp hk).1
    have habel : ∀ m : ℕ, 1 ≤ m →
        (∑ k ∈ Finset.Icc 1 m, ((u k - u (k - 1) : ℝ) : ℂ) * E ((k : ℝ) * β)) =
        (u m : ℂ) * E ((m : ℝ) * β) +
          ∑ k ∈ Finset.Icc 1 (m - 1), (u k : ℂ) * (E ((k : ℝ) * β) - E (((k + 1 : ℕ) : ℝ) * β)) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
          simp [hu0]
      | @succ m hm ih =>
          have hIcc1 : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
            ext k
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          have hnot1 : m + 1 ∉ Finset.Icc 1 m := by simp
          have hIcc2 : Finset.Icc 1 m = insert m (Finset.Icc 1 (m - 1)) := by
            ext k
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          have hnot2 : m ∉ Finset.Icc 1 (m - 1) := by
            simp only [Finset.mem_Icc]
            omega
          rw [hIcc1, Finset.sum_insert hnot1, ih, Nat.add_sub_cancel, hIcc2, Finset.sum_insert hnot2]
          push_cast
          ring
    rw [hsum_eq, habel n hn_pos]
    have htri :
        ‖(u n : ℂ) * E ((n : ℝ) * β) +
          ∑ k ∈ Finset.Icc 1 (n - 1), (u k : ℂ) * (E ((k : ℝ) * β) - E (((k + 1 : ℕ) : ℝ) * β))‖ ≤
        ‖(u n : ℂ) * E ((n : ℝ) * β)‖ +
          ∑ k ∈ Finset.Icc 1 (n - 1), ‖(u k : ℂ) * (E ((k : ℝ) * β) - E (((k + 1 : ℕ) : ℝ) * β))‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    have hhead : ‖(u n : ℂ) * E ((n : ℝ) * β)‖ ≤ e := by
      rw [norm_mul, hEnorm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hu_bound n le_rfl
    have htail :
        (∑ k ∈ Finset.Icc 1 (n - 1), ‖(u k : ℂ) * (E ((k : ℝ) * β) - E (((k + 1 : ℕ) : ℝ) * β))‖) ≤
          (n : ℝ) * (e * (2 * Real.pi * |β|)) := by
      have hterm : ∀ k ∈ Finset.Icc 1 (n - 1),
          ‖(u k : ℂ) * (E ((k : ℝ) * β) - E (((k + 1 : ℕ) : ℝ) * β))‖ ≤
            e * (2 * Real.pi * |β|) := by
        intro k hk
        have hkn : k ≤ n := by
          have := (Finset.mem_Icc.mp hk).2
          omega
        have hEdiff : E ((k : ℝ) * β) - E (((k + 1 : ℕ) : ℝ) * β) = E ((k : ℝ) * β) * (1 - E β) := by
          have h1 : (((k + 1 : ℕ) : ℝ) * β) = (k : ℝ) * β + β := by
            push_cast
            ring
          rw [h1, ← hEmul]
          ring
        rw [norm_mul, hEdiff, norm_mul, hEnorm, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul (hu_bound k hkn) hdiff_E (norm_nonneg _) he
      have hsum_le :
          (∑ k ∈ Finset.Icc 1 (n - 1), ‖(u k : ℂ) * (E ((k : ℝ) * β) - E (((k + 1 : ℕ) : ℝ) * β))‖) ≤
            ∑ _k ∈ Finset.Icc 1 (n - 1), e * (2 * Real.pi * |β|) :=
        Finset.sum_le_sum hterm
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsum_le
      have hcard : ((n - 1 + 1 - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (by omega : n - 1 + 1 - 1 ≤ n)
      have hnonneg : 0 ≤ e * (2 * Real.pi * |β|) := by positivity
      exact hsum_le.trans (mul_le_mul_of_nonneg_right hcard hnonneg)
    linarith [htri, hhead, htail]
  have hcop_bound :
      ‖(∑ r ∈ Rcop, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r),
          (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β)) -
        ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β‖ ≤
      (Nat.totient q : ℝ) * e * (1 + 2 * Real.pi * (n : ℝ) * |β|) := by
    rw [hmodel, ← Finset.sum_sub_distrib]
    have h1 := (norm_sum_le Rcop _).trans (Finset.sum_le_sum hcop_class)
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have hcard : Rcop.card = Nat.totient q := by
      simp [Rcop, Nat.totient_eq_card_coprime]
      congr 1
      ext r
      simp [Nat.coprime_comm]
    rw [hcard] at h1
    linarith
  have hdecomp :
      S n ((a : ℝ) / q + β) - ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β =
      ((∑ r ∈ Rcop, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r),
          (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β)) -
        ((ArithmeticFunction.moebius q : ℂ) / (Nat.totient q : ℂ)) * K1 n β) +
      (∑ r ∈ Rnon, ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k % q = r),
        (w k : ℂ) * E ((k : ℝ) * ((a : ℝ) / q)) * E ((k : ℝ) * β)) := by
    rw [hS_split]
    ring
  rw [hdecomp]
  exact (norm_add_le _ _).trans (by linarith [hcop_bound, hnon_bound])
