import Mathlib

import Conjectures.Goldbach.EstermannAlmostAllPolylog
import Conjectures.Cuts.Taskba08eb3c3998330911d98843

/-!
# The sharp reflected major-arc floor is twice the twin-prime constant

On the polylogarithmic major arcs of Goldbach PR #4198 (denominator cutoff `k = log₂(N+2)`,
arc radius `k³/(qN)`) the normalized prime-square coefficient `A(N,m)/(2N-m)` on the reflected
even band `4N/3 ≤ m ≤ 3N/2` has the asymptotic lower envelope `2C₂`, where `C₂` is the twin-prime
constant, and the envelope is attained along powers of two.

## Inputs

* `Conjectures.Cuts.Taskba08eb3c3998330911d98843` (Goldbach PR #4198, Apache-2.0): the arc
  geometry, the uniform polylogarithmic approximation error (`eventually_approx`), the square-kernel
  tail estimate `norm_twisted_tail_upper` and the equality `scaledModel = complexModel`.
* `Conjectures.Goldbach.EstermannAlmostAllPolylog` (Goldbach PR #3615 / #316, Apache-2.0): the
  Ramanujan coefficients, `negative_factors_lower`, `sum_norm_coefficient_le_sqrt`.
  The three reindexing lemmas `coefficient_prod_primes`, `coefficient_eq_zero_of_not_squarefree`
  and `reindex_denominators` are adapted from the private lemmas of PR #316.

## Proof

Write `T_k(m) = ∑_{q ≤ k} coefficient(q,m)` for the truncated singular series. Grouping the
squarefree denominators by the part supported on the primes dividing `m` (theorem `floor_eq_grouped`)
gives, for even `m`, `T_k(m) ≥ altMass(B,1,k) + altMass(B,2,k)` where `B` is the set of primes
`≤ k` not dividing `m`; along powers of two equality holds. The coprime alternating masses are
compared with the finite Euler product `fullMass(B) = ∏_{p ∈ B}(1 - 1/(p-1)²)` through
`altMass_truncation`, and the removed mass is bounded by Rankin's trick
(`removedMass_le`: at most `128·√(c/k)` for scale `c`). Every finite partial Euler product of
odd primes dominates the twin-prime constant (`twin_le_fullMass`), and the constant factors as the
partial product at level `k` times a tail product that is at least `1 - 4/(k-1)` (`tail_prod_lower`),
so the partial product is at most `C₂(1 + 16/k)` for `k ≥ 9`. This yields the uniform sharp
bounds `2C₂ - 128(1+√2)/√k ≤ T_k(m)` for even `m` (`floor_lower_sharp`) and
`T_k(2^a) ≤ 2C₂(1+16/k) + 128(1+√2)/√k` (`floor_upper_sharp`).

The square-kernel model of PR #4198 differs from `(2N-m+1)·T_k(m)` by at most `8N/√k`
(`model_bounds`). Together with the uniform approximation error this proves both halves of the
frozen statement: a uniform `(2C₂ - ε)(2N-m)` floor for all large `N`, and along `N = ⌈2^{a+1}/3⌉`,
`m = 2^a`, an upper bound `(2C₂ + ε)(2N-m)` for arbitrarily large `N`. Minor arcs are not used;
the coefficient is restricted to the major arcs by definition.
-/

section

namespace GoldbachSharpReflected

open Finset Filter MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Topology

noncomputable section

/-! ### Coefficients of squarefree denominators -/

/-- The local Ramanujan factor in terms of the verified bad factor. -/
theorem localCoefficient_eq (p n : ℕ) :
    GoldbachMajorArc.localCoefficient p n =
      if p ∣ n then 1 / ((p : ℝ) - 1) else -(GoldbachMajorArc.badFactor p) := by
  simp [GoldbachMajorArc.localCoefficient, GoldbachMajorArc.badFactor]

/-- Adapted from `coefficient_prime_product` in DFQDZZ's goldbach-proofs PR #316
(revision e4ab24712555ae8c2c926adf19d368a9fb392c35, Apache-2.0). -/
theorem coefficient_prod_primes (n : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    GoldbachMajorArc.coefficient (∏ p ∈ s, p) n =
      ((∏ p ∈ s, GoldbachMajorArc.localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [GoldbachMajorArc.coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, GoldbachMajorArc.coefficient_mul hprime.pos
      (prod_pos fun r hr => (hs' r hr).pos) hcop, GoldbachMajorArc.coefficient_prime hprime,
      ih hs', Complex.ofReal_mul]

/-- Adapted from `coefficient_not_squarefree` in PR #316 (Apache-2.0). -/
theorem coefficient_eq_zero_of_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : GoldbachMajorArc.coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact GoldbachMajorArc.coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [GoldbachMajorArc.coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h, h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

/-- Adapted from `reindex_denominators` in PR #316 (Apache-2.0): the truncated singular
series is the sum over subsets of primes of the local factors, weighted by `W`. -/
theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Icc 1 Q, (GoldbachMajorArc.coefficient q n).re * W q) =
    ∑ t ∈ ((range (Q + 1)).filter Nat.Prime).powerset,
      (∏ p ∈ t, GoldbachMajorArc.localCoefficient p n) * W (∏ p ∈ t, p) := by
  classical
  let P := (range (Q + 1)).filter Nat.Prime
  have hprime {t : Finset ℕ} (ht : t ∈ P.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => (mem_filter.mp (mem_powerset.mp ht hp)).2
  symm
  apply sum_bij_ne_zero (fun t _ _ => ∏ p ∈ t, p)
  · intro t ht hnz
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (hprime ht p hp).pos,
      le_of_not_gt fun h => hnz (by rw [hcut _ h, mul_zero])⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hprime hs)).symm.trans
      ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hprime ht)))
  · intro q hq hnz
    have hq' := mem_Icc.mp hq
    have hsq : Squarefree q := by
      by_contra hh
      exact hnz (by rw [coefficient_eq_zero_of_not_squarefree n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply mem_powerset.mpr
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr
        (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
        Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prod_primes n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub,
      fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prod_primes n t (hprime ht), Complex.ofReal_re]

/-- The unit-weight specialization: only subsets whose product is at most the cutoff. -/
theorem sum_re_floor_eq_powerset (Q n : ℕ) :
    (∑ q ∈ Icc 1 Q, (GoldbachMajorArc.coefficient q n).re) =
      ∑ t ∈ (((range (Q + 1)).filter Nat.Prime).powerset).filter
          (fun t => ∏ p ∈ t, p ≤ Q),
        ∏ p ∈ t, GoldbachMajorArc.localCoefficient p n := by
  have h := reindex_denominators Q n (fun q => if q ≤ Q then (1 : ℝ) else 0)
    (by intro q hq; simp [not_le.mpr hq])
  rw [sum_congr rfl (fun q hq => by rw [ite_eq_left (mem_Icc.mp hq).2, mul_one])] at h
  rw [h, sum_filter]
  refine sum_congr rfl fun t ht => ?_
  by_cases hc : ∏ p ∈ t, p ≤ Q <;> simp [hc]


/-! ### The coprime alternating mass -/

theorem badFactor_nonneg (p : ℕ) : 0 ≤ GoldbachMajorArc.badFactor p := by
  unfold GoldbachMajorArc.badFactor; positivity

/-- Alternating mass of the subsets of `B` whose scaled product is at most `k`. -/
def altMass (B : Finset ℕ) (c k : ℕ) : ℝ :=
  ∑ r ∈ B.powerset.filter (fun r => c * ∏ p ∈ r, p ≤ k), ∏ p ∈ r, -(GoldbachMajorArc.badFactor p)

/-- The absolute mass removed by the truncation. -/
def removedMass (B : Finset ℕ) (c k : ℕ) : ℝ :=
  ∑ r ∈ B.powerset.filter (fun r => k < c * ∏ p ∈ r, p), ∏ p ∈ r, GoldbachMajorArc.badFactor p

/-- The full alternating mass over all subsets of `B`. -/
def fullMass (B : Finset ℕ) : ℝ := ∑ r ∈ B.powerset, ∏ p ∈ r, -(GoldbachMajorArc.badFactor p)

theorem fullMass_eq_prod (B : Finset ℕ) :
    fullMass B = ∏ p ∈ B, (1 - GoldbachMajorArc.badFactor p) := by
  unfold fullMass
  rw [← Finset.prod_one_add (f := fun p => -(GoldbachMajorArc.badFactor p)) B]
  exact prod_congr rfl fun p _ => by ring

theorem altMass_eq (B : Finset ℕ) (c k : ℕ) :
    altMass B c k = ∑ r ∈ B.powerset, (∏ p ∈ r, -(GoldbachMajorArc.badFactor p)) *
        (if c * ∏ p ∈ r, p ≤ k then 1 else 0) := by
  unfold altMass
  rw [sum_filter]
  exact sum_congr rfl fun r _ => by split_ifs <;> ring

/-- The alternating signed factors away from the target retain one third of the unit mass. -/
theorem altMass_lower (B : Finset ℕ) (c k : ℕ) (hB : ∀ p ∈ B, p.Prime ∧ 2 < p) :
    (if c ≤ k then 1 / 3 else 0) ≤ altMass B c k := by
  classical
  rw [altMass_eq]
  have h := GoldbachMajorArc.negative_factors_lower hB
    (fun q => if c * q ≤ k then (1 : ℝ) else 0)
    (fun q => by split_ifs <;> norm_num)
    (fun i j _ hij => by
      by_cases h : c * j ≤ k
      · rw [ite_eq_left h, ite_eq_left ((Nat.mul_le_mul_left c hij).trans h)]
      · rw [ite_eq_right h]; split_ifs <;> norm_num)
    (d := 1) (by decide)
  simp only [one_mul, Nat.mul_one] at h
  split_ifs with hck
  · refine le_trans (le_of_eq ?_) h
    rw [ite_eq_left hck]
  · have hzero : ∀ x ∈ B.powerset, ¬ c * ∏ p ∈ x, p ≤ k := by
      intro x hx hc
      exact hck ((Nat.le_mul_of_pos_right c
        (prod_pos fun p _ => (hB p (mem_powerset.mp hx ‹_›)).1.pos)).trans hc)
    refine sum_nonneg fun x hx => ?_
    rw [ite_eq_right (hzero x hx), mul_zero]

theorem altMass_nonneg (B : Finset ℕ) (c k : ℕ) (hB : ∀ p ∈ B, p.Prime ∧ 2 < p) :
    0 ≤ altMass B c k := by
  have := altMass_lower B c k hB
  split_ifs at this <;> linarith

theorem removed_filter (B : Finset ℕ) (c k : ℕ) :
    B.powerset.filter (fun r => ¬ c * ∏ p ∈ r, p ≤ k) =
      B.powerset.filter (fun r => k < c * ∏ p ∈ r, p) :=
  filter_congr fun r _ => by simp only [not_le]

/-- Truncation moves the alternating mass by at most the absolute removed mass. -/
theorem altMass_truncation (B : Finset ℕ) (c k : ℕ) :
    fullMass B - removedMass B c k ≤ altMass B c k ∧ altMass B c k ≤ fullMass B + removedMass B c k := by
  classical
  have h : altMass B c k + ∑ r ∈ B.powerset.filter (fun r => ¬ c * ∏ p ∈ r, p ≤ k),
      ∏ p ∈ r, -(GoldbachMajorArc.badFactor p) = fullMass B :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  rw [removed_filter] at h
  have habs : |∑ r ∈ B.powerset.filter (fun r => k < c * ∏ p ∈ r, p),
      ∏ p ∈ r, -(GoldbachMajorArc.badFactor p)| ≤ removedMass B c k := by
    unfold removedMass
    refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
    rw [Finset.abs_prod]
    simp only [abs_neg, abs_of_nonneg (badFactor_nonneg _)]
    exact le_refl _
  obtain ⟨h1, h2⟩ := abs_le.mp habs
  unfold removedMass at h1 h2 ⊢
  constructor <;> linarith

/-! ### Rankin's trick -/

theorem prod_sqrt_prod (r : Finset ℕ) :
    (∏ p ∈ r, Real.sqrt (p : ℝ)) = Real.sqrt (∏ p ∈ r, p) := by
  classical
  induction r using Finset.induction_on with
  | empty => simp
  | insert p r hp ih =>
    rw [prod_insert hp, prod_insert hp, ih, Real.sqrt_mul (Nat.cast_nonneg p)]

theorem sqrt_prod_cast (r : Finset ℕ) :
    Real.sqrt (∏ p ∈ r, (p : ℝ)) = ∏ p ∈ r, Real.sqrt (p : ℝ) := (prod_sqrt_prod r).symm

theorem term_bound (n : ℕ) (hn : 3 ≤ n) :
    1 / ((n : ℝ) * Real.sqrt (n : ℝ)) ≤ 2 / Real.sqrt ((n : ℝ) - 1) - 2 / Real.sqrt (n : ℝ) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hA : Real.sqrt ((n : ℝ) - 1) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hB : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by linarith)
  have hApos : 0 < Real.sqrt ((n : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  have hBpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hle : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt (by linarith)
  have hsub : 2 / Real.sqrt ((n : ℝ) - 1) - 2 / Real.sqrt (n : ℝ) =
      2 * (Real.sqrt (n : ℝ) - Real.sqrt ((n : ℝ) - 1)) /
        (Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ)) := by
    rw [div_sub_div 2 2 hApos.ne' hBpos.ne']
    congr 1
    ring
  have hBA : Real.sqrt (n : ℝ) - Real.sqrt ((n : ℝ) - 1) =
      1 / (Real.sqrt ((n : ℝ) - 1) + Real.sqrt (n : ℝ)) := by
    rw [eq_div_iff (b := Real.sqrt ((n : ℝ) - 1) + Real.sqrt (n : ℝ)) (by linarith)]
    nlinarith [hA, hB]
  have hAB : Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) :=
    mul_le_mul_of_nonneg_right hle hBpos.le
  have hcomb : 2 * (1 / (Real.sqrt ((n : ℝ) - 1) + Real.sqrt (n : ℝ))) /
      (Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ)) =
      2 / ((Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ)) *
        (Real.sqrt ((n : ℝ) - 1) + Real.sqrt (n : ℝ))) := by
    field_simp
  rw [hsub, hBA, hcomb, div_le_div_iff₀ (by positivity) (by positivity)]
  have hstep1 : Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ) *
      (Real.sqrt ((n : ℝ) - 1) + Real.sqrt (n : ℝ)) ≤
      Real.sqrt (n : ℝ) * ((n : ℝ) - 1 + n) := by
    calc
      _ = Real.sqrt (n : ℝ) * (Real.sqrt ((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1) +
          Real.sqrt ((n : ℝ) - 1) * Real.sqrt (n : ℝ)) := by ring
      _ ≤ Real.sqrt (n : ℝ) * ((n : ℝ) - 1 + n) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (le_of_eq ((pow_two _).symm.trans hA))
            (hAB.trans_eq ((pow_two _).symm.trans hB))) hBpos.le
  nlinarith [hstep1]

theorem telescoping (g : ℝ → ℝ) (a b : ℕ) (hab : a ≤ b + 1) :
    (∑ n ∈ Icc a b, (g ((n : ℝ) - 1) - g (n : ℝ))) = g ((a : ℝ) - 1) - g (b : ℝ) := by
  by_cases hab' : a ≤ b
  · have hIcc : Icc a b = (range (b - a + 1)).image (fun i => i + a) := by
      ext n
      simp only [mem_Icc, mem_image, mem_range]
      constructor
      · rintro ⟨ha, hb⟩
        exact ⟨n - a, by omega, by omega⟩
      · rintro ⟨i, hi, rfl⟩
        omega
    have hcc : (∑ n ∈ Icc a b, (g ((n : ℝ) - 1) - g (n : ℝ))) =
        ∑ i ∈ range (b - a + 1), (g (((i + a : ℕ) : ℝ) - 1) - g (((i + 1 + a : ℕ) : ℝ) - 1)) := by
      rw [hIcc, Finset.sum_image]
      · refine sum_congr rfl fun i _ => ?_
        push_cast
        ring
      · intro i hi j hj hij
        simp only [Finset.mem_coe, mem_range] at hi hj
        have hij' : i + a = j + a := hij
        omega
    rw [hcc, Finset.sum_range_sub' (fun i => g (((i + a : ℕ) : ℝ) - 1)) (b - a + 1)]
    rw [show b - a + 1 + a = b + 1 by omega]
    push_cast
    ring
  · have ha : a = b + 1 := by omega
    subst a
    simp

theorem sum_inv_sqrt_le (k : ℕ) (hk : 3 ≤ k) :
    (∑ n ∈ Icc 3 k, 1 / ((n : ℝ) * Real.sqrt (n : ℝ))) ≤ Real.sqrt 2 := by
  calc
    _ ≤ ∑ n ∈ Icc 3 k, (2 / Real.sqrt ((n : ℝ) - 1) - 2 / Real.sqrt (n : ℝ)) :=
      sum_le_sum fun n hn => term_bound n (mem_Icc.mp hn).1
    _ = 2 / Real.sqrt ((3 : ℝ) - 1) - 2 / Real.sqrt (k : ℝ) :=
      telescoping (fun y => 2 / Real.sqrt y) 3 k (by omega)
    _ ≤ Real.sqrt 2 := by
      have h2 : Real.sqrt 2 = 2 / Real.sqrt 2 := by
        apply (eq_div_iff (b := Real.sqrt 2) (Real.sqrt_pos.2 (by norm_num)).ne').2
        have := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith
      have h0 : 0 ≤ 2 / Real.sqrt (k : ℝ) := by positivity
      rw [show (3 : ℝ) - 1 = 2 by norm_num, ← h2]
      linarith

/-- Rankin's trick bounds the removed mass by a constant over the square root of the cutoff. -/
theorem removedMass_le (B : Finset ℕ) (c k : ℕ) (hk : 3 ≤ k) (hlo : ∀ p ∈ B, 3 ≤ p)
    (hhi : ∀ p ∈ B, p ≤ k) : removedMass B c k ≤ 128 * Real.sqrt ((c : ℝ) / (k : ℝ)) := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  rcases Nat.eq_zero_or_pos c with hc0 | hc
  · subst c
    simp [removedMass]
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hnum : ∀ r : Finset ℕ, 0 ≤ ∏ p ∈ r, Real.sqrt (p : ℝ) * GoldbachMajorArc.badFactor p :=
    fun r => prod_nonneg fun p _ => mul_nonneg (Real.sqrt_nonneg _) (badFactor_nonneg p)
  have hprodpos (r : Finset ℕ) (hrB : r ⊆ B) : 0 < ∏ p ∈ r, (p : ℝ) :=
    prod_pos fun p _ => Nat.cast_pos.mpr (by have := hlo p (hrB ‹_›); omega)
  have hterm (r : Finset ℕ) (hrB : r ⊆ B) (hrlt : k < c * ∏ p ∈ r, p) :
      (∏ p ∈ r, GoldbachMajorArc.badFactor p) ≤
        (∏ p ∈ r, Real.sqrt (p : ℝ) * GoldbachMajorArc.badFactor p) / Real.sqrt ((k : ℝ) / c) := by
    have hp := hprodpos r hrB
    have hlt : (k : ℝ) / c < ∏ p ∈ r, (p : ℝ) := by
      rw [div_lt_iff₀ hcR, mul_comm, ← prod_natCast]
      exact_mod_cast hrlt
    have hs : Real.sqrt ((k : ℝ) / c) ≤ Real.sqrt (∏ p ∈ r, (p : ℝ)) :=
      Real.sqrt_le_sqrt hlt.le
    have hpos : 0 < Real.sqrt (∏ p ∈ r, (p : ℝ)) := Real.sqrt_pos.mpr hp
    have heq : (∏ p ∈ r, GoldbachMajorArc.badFactor p) * Real.sqrt (∏ p ∈ r, (p : ℝ)) =
        ∏ p ∈ r, Real.sqrt (p : ℝ) * GoldbachMajorArc.badFactor p := by
      rw [prod_mul_distrib, sqrt_prod_cast]
      ring
    rw [← heq]
    refine (le_div_iff₀ (by positivity : (0 : ℝ) < Real.sqrt ((k : ℝ) / c))).2 ?_
    exact mul_le_mul_of_nonneg_left hs
      (prod_nonneg fun p _ => badFactor_nonneg p)
  have hfactor (p : ℕ) (hp : 3 ≤ p) :
      Real.sqrt (p : ℝ) * GoldbachMajorArc.badFactor p ≤ 9 / (4 * ((p : ℝ) * Real.sqrt (p : ℝ))) := by
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hs2 : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = p := Real.mul_self_sqrt (Nat.cast_nonneg p)
    have hs2p : (p : ℝ) * (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) = (p : ℝ) * (p : ℝ) := by
      rw [hs2]
    unfold GoldbachMajorArc.badFactor
    rw [mul_one_div, div_le_div_iff₀ (pow_pos hp1 2) (by positivity)]
    nlinarith [hs2p, mul_nonneg (sub_nonneg.mpr hp3) (show (0 : ℝ) ≤ 5 * (p : ℝ) - 3 by linarith)]
  have hprod128 : ∏ p ∈ B, (1 + Real.sqrt (p : ℝ) * GoldbachMajorArc.badFactor p) ≤ 128 := by
    calc
      _ ≤ ∏ p ∈ B, (1 + 9 / (4 * ((p : ℝ) * Real.sqrt (p : ℝ)))) :=
        Finset.prod_le_prod₀
          (fun p _ => add_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _) (badFactor_nonneg p)))
          fun p hp => add_le_add (le_refl 1) (hfactor p (hlo p hp))
      _ ≤ ∏ n ∈ Icc 3 k, (1 + 9 / (4 * ((n : ℝ) * Real.sqrt (n : ℝ)))) := by
        apply prod_le_prod_of_subset_of_one_le₀
        · intro p hp
          exact mem_Icc.mpr ⟨hlo p hp, hhi p hp⟩
        · intro p _; positivity
        · intro p _ _
          have : 0 ≤ 9 / (4 * ((p : ℝ) * Real.sqrt (p : ℝ))) := by positivity
          linarith
      _ ≤ Real.exp (∑ n ∈ Icc 3 k, 9 / (4 * ((n : ℝ) * Real.sqrt (n : ℝ)))) :=
        Real.prod_one_add_le_exp_sum _ (fun n => by positivity)
      _ ≤ Real.exp 4 := by
        apply Real.exp_le_exp.mpr
        have hsum : (∑ n ∈ Icc 3 k, 9 / (4 * ((n : ℝ) * Real.sqrt (n : ℝ)))) =
            (9 / 4 : ℝ) * ∑ n ∈ Icc 3 k, 1 / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
          rw [Finset.mul_sum]
          exact sum_congr rfl fun n _ => by field_simp
        rw [hsum]
        refine (mul_le_mul_of_nonneg_left (sum_inv_sqrt_le k hk) (by norm_num)).trans ?_
        have hs2 : Real.sqrt 2 ≤ 16 / 9 := by
          rw [Real.sqrt_le_iff]
          norm_num
        nlinarith
      _ ≤ 128 := by
        have h1 := Real.exp_one_lt_d9
        calc
          Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
          _ ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ (by positivity) h1.le 4
          _ ≤ 128 := by norm_num
  unfold removedMass
  calc
    _ ≤ ∑ r ∈ B.powerset.filter (fun r => k < c * ∏ p ∈ r, p),
        (∏ p ∈ r, Real.sqrt (p : ℝ) * GoldbachMajorArc.badFactor p) / Real.sqrt ((k : ℝ) / c) := by
      refine sum_le_sum fun r hr => ?_
      simp only [mem_filter, mem_powerset] at hr
      exact hterm r hr.1 hr.2
    _ ≤ (∏ p ∈ B, (1 + Real.sqrt (p : ℝ) * GoldbachMajorArc.badFactor p)) / Real.sqrt ((k : ℝ) / c) := by
      rw [Finset.prod_one_add
        (f := fun p : ℕ => Real.sqrt (p : ℝ) * GoldbachMajorArc.badFactor p) B, Finset.sum_div]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun r _ _ => div_nonneg (hnum r) (Real.sqrt_nonneg _))
    _ ≤ 128 / Real.sqrt ((k : ℝ) / c) :=
      div_le_div_of_nonneg_right hprod128 (by positivity)
    _ = 128 * Real.sqrt ((c : ℝ) / (k : ℝ)) := by
      rw [Real.sqrt_div hkR.le (c : ℝ), Real.sqrt_div hcR.le (k : ℝ)]
      field_simp
/-! ### Grouping the truncated singular series -/

/-- Primes up to a cutoff. -/
def smallPrimes (k : ℕ) : Finset ℕ := (range (k + 1)).filter Nat.Prime

/-- Primes up to the cutoff that divide the target. -/
def dividingPrimes (m k : ℕ) : Finset ℕ := (smallPrimes k).filter (fun p => p ∣ m)

/-- Primes up to the cutoff that do not divide the target. -/
def coprimePrimes (m k : ℕ) : Finset ℕ := (smallPrimes k).filter (fun p => ¬ p ∣ m)

/-- The powerset of a disjoint union as a double sum. -/
theorem sum_powerset_union (G B : Finset ℕ) (F : Finset ℕ → ℝ) :
    Disjoint G B →
    ∑ t ∈ (G ∪ B).powerset, F t = ∑ s ∈ G.powerset, ∑ r ∈ B.powerset, F (s ∪ r) := by
  classical
  induction G using Finset.induction_on generalizing F with
  | empty => simp
  | insert p G hp ih =>
    intro hd
    have hpB : p ∉ B := (Finset.disjoint_insert_left.mp hd).1
    have hd' : Disjoint G B := (Finset.disjoint_insert_left.mp hd).2
    have hpu : p ∉ G ∪ B := by simp [hp, hpB]
    rw [insert_union]
    rw [sum_powerset_insert hpu F]
    rw [ih F hd']
    have h2 := ih (fun t => F (insert p t)) hd'
    rw [h2]
    rw [sum_powerset_insert hp (fun s => ∑ r ∈ B.powerset, F (s ∪ r))]
    refine congrArg₂ (· + ·) rfl ?_
    refine sum_congr rfl fun s _ => sum_congr rfl fun r _ => ?_
    show F (insert p (s ∪ r)) = F (insert p s ∪ r)
    rw [Finset.insert_union]

/-- The truncated singular series, grouped by the squarefree divisor supported on the target. -/
theorem floor_eq_grouped (m k : ℕ) :
    (∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q m).re) =
      ∑ s ∈ (dividingPrimes m k).powerset,
        (∏ p ∈ s, GoldbachMajorArc.localCoefficient p m) *
          altMass (coprimePrimes m k) (∏ p ∈ s, p) k := by
  classical
  rw [sum_re_floor_eq_powerset]
  let F : Finset ℕ → ℝ := fun t =>
    (∏ p ∈ t, GoldbachMajorArc.localCoefficient p m) * (if ∏ p ∈ t, p ≤ k then 1 else 0)
  have hF : (∑ t ∈ (((range (k + 1)).filter Nat.Prime).powerset).filter (fun t => ∏ p ∈ t, p ≤ k),
      ∏ p ∈ t, GoldbachMajorArc.localCoefficient p m) =
      ∑ t ∈ ((range (k + 1)).filter Nat.Prime).powerset, F t := by
    unfold F
    rw [sum_filter]
    exact sum_congr rfl fun t _ => by split_ifs <;> ring
  rw [hF]
  have hunion : ((range (k + 1)).filter Nat.Prime) = dividingPrimes m k ∪ coprimePrimes m k := by
    unfold dividingPrimes coprimePrimes
    exact (Finset.filter_union_filter_not_eq _ _).symm
  have hdis : Disjoint (dividingPrimes m k) (coprimePrimes m k) :=
    Finset.disjoint_filter_filter_not _ _ _
  rw [hunion, sum_powerset_union _ _ F hdis]
  refine sum_congr rfl fun s hs => ?_
  rw [altMass_eq, Finset.mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hdisj : Disjoint s r :=
    Finset.disjoint_of_subset_right (mem_powerset.mp hr)
      (Finset.disjoint_of_subset_left (mem_powerset.mp hs) hdis)
  have hcop : ∀ p ∈ r, GoldbachMajorArc.localCoefficient p m = -(GoldbachMajorArc.badFactor p) := by
    intro p hp
    rw [localCoefficient_eq, ite_eq_right (mem_filter.mp (mem_powerset.mp hr hp)).2]
  show (∏ p ∈ s ∪ r, GoldbachMajorArc.localCoefficient p m) *
      (if ∏ p ∈ s ∪ r, p ≤ k then 1 else 0) = _
  rw [Finset.prod_union hdisj, Finset.prod_union hdisj, Finset.prod_congr rfl hcop]
  ring

/-- Primes not dividing an even target are odd. -/
theorem coprimePrimes_odd {m k : ℕ} (he : Even m) :
    ∀ p ∈ coprimePrimes m k, p.Prime ∧ 2 < p := by
  intro p hp
  simp only [coprimePrimes, smallPrimes, mem_filter] at hp
  obtain ⟨⟨_, hprime⟩, hnd⟩ := hp
  refine ⟨hprime, ?_⟩
  by_contra hcon
  have hlt : p < 3 := by omega
  interval_cases p
  · norm_num at hprime
  · norm_num at hprime
  · exact hnd (even_iff_two_dvd.mp he)

theorem localCoefficient_two {m : ℕ} (hm : 2 ∣ m) : GoldbachMajorArc.localCoefficient 2 m = 1 := by
  rw [localCoefficient_eq, ite_eq_left hm]
  norm_num

/-- The retained coprime masses at scales one and two bound the truncated series from below. -/
theorem floor_lower (m k : ℕ) (he : Even m) (hk : 2 ≤ k) :
    altMass (coprimePrimes m k) 1 k + altMass (coprimePrimes m k) 2 k ≤
      ∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q m).re := by
  classical
  have hB : ∀ p ∈ coprimePrimes m k, p.Prime ∧ 2 < p := coprimePrimes_odd he
  have hnonneg : ∀ s ∈ (dividingPrimes m k).powerset,
      0 ≤ (∏ p ∈ s, GoldbachMajorArc.localCoefficient p m) *
        altMass (coprimePrimes m k) (∏ p ∈ s, p) k := by
    intro s hs
    refine mul_nonneg (prod_nonneg fun p hp => ?_) (altMass_nonneg _ _ _ hB)
    have hmem := mem_powerset.mp hs hp
    rw [localCoefficient_eq, ite_eq_left (mem_filter.mp hmem).2]
    exact one_div_nonneg.mpr (sub_nonneg.mpr
      (by exact_mod_cast ((mem_filter.mp (mem_filter.mp hmem).1).2).one_le))
  have hmem1 : (∅ : Finset ℕ) ∈ (dividingPrimes m k).powerset := by simp
  have hmem2 : ({2} : Finset ℕ) ∈ (dividingPrimes m k).powerset := by
    apply mem_powerset.mpr
    intro p hp
    simp only [mem_singleton] at hp
    subst hp
    simp only [dividingPrimes, smallPrimes, mem_filter]
    exact ⟨⟨mem_range.mpr (by omega), by decide⟩, even_iff_two_dvd.mp he⟩
  rw [floor_eq_grouped]
  have hrest := Finset.sum_nonneg (s := ((dividingPrimes m k).powerset.erase ∅).erase {2})
    (fun s hs => hnonneg s (((erase_subset _ _).trans (erase_subset _ _)) hs))
  rw [← Finset.sum_erase_add _ _ hmem1]
  have h2 : {2} ∈ (dividingPrimes m k).powerset.erase ∅ := by simp [hmem2]
  rw [← Finset.sum_erase_add (f := fun s => (∏ p ∈ s, GoldbachMajorArc.localCoefficient p m) *
    altMass (coprimePrimes m k) (∏ p ∈ s, p) k) _ h2]
  have htwo : (∏ p ∈ ({2} : Finset ℕ), GoldbachMajorArc.localCoefficient p m) *
      altMass (coprimePrimes m k) (∏ p ∈ ({2} : Finset ℕ), p) k =
      altMass (coprimePrimes m k) 2 k := by
    simp [localCoefficient_two (even_iff_two_dvd.mp he)]
  have hone : (∏ p ∈ (∅ : Finset ℕ), GoldbachMajorArc.localCoefficient p m) *
      altMass (coprimePrimes m k) (∏ p ∈ (∅ : Finset ℕ), p) k =
      altMass (coprimePrimes m k) 1 k := by simp
  rw [hone, htwo]
  linarith

/-- Along powers of two only the prime two divides the target. -/
theorem floor_eq_two (a k : ℕ) (ha : 0 < a) (hk : 2 ≤ k) :
    (∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q (2 ^ a)).re) =
      altMass (coprimePrimes (2 ^ a) k) 1 k + altMass (coprimePrimes (2 ^ a) k) 2 k := by
  classical
  have hG : dividingPrimes (2 ^ a) k = {2} := by
    ext p
    simp only [dividingPrimes, smallPrimes, mem_filter, mem_singleton]
    constructor
    · rintro ⟨⟨_, hprime⟩, hdvd⟩
      by_cases hne : p = 2
      · exact hne
      · exfalso
        have hc : Nat.Coprime p 2 := (Nat.coprime_primes hprime Nat.prime_two).mpr hne
        have hc' : Nat.Coprime p (2 ^ a) := Nat.Coprime.pow_right a hc
        have hd1 : p ∣ 1 := hc' ▸ Nat.dvd_gcd dvd_rfl hdvd
        exact hprime.ne_one (Nat.eq_one_of_dvd_one hd1)
    · rintro rfl
      exact ⟨⟨mem_range.mpr (by omega), by decide⟩, dvd_pow_self 2 ha.ne'⟩
  have hp2 : ({2} : Finset ℕ).powerset = {∅, {2}} := by decide
  rw [floor_eq_grouped, hG, hp2]
  have htwo : (∏ p ∈ ({2} : Finset ℕ), GoldbachMajorArc.localCoefficient p (2 ^ a)) *
      altMass (coprimePrimes (2 ^ a) k) (∏ p ∈ ({2} : Finset ℕ), p) k =
      altMass (coprimePrimes (2 ^ a) k) 2 k := by
    simp [localCoefficient_two (dvd_pow_self 2 ha.ne')]
  have hone : (∏ p ∈ (∅ : Finset ℕ), GoldbachMajorArc.localCoefficient p (2 ^ a)) *
      altMass (coprimePrimes (2 ^ a) k) (∏ p ∈ (∅ : Finset ℕ), p) k =
      altMass (coprimePrimes (2 ^ a) k) 1 k := by simp
  simp only [sum_insert (by decide : (∅ : Finset ℕ) ∉ {({2} : Finset ℕ)}), sum_singleton]
  rw [hone, htwo]
/-! ### The twin-prime constant -/

/-- Odd primes up to a cutoff. -/
def oddPrimes (k : ℕ) : Finset ℕ := (smallPrimes k).filter (fun p => 2 < p)

/-- The Euler factor of the twin-prime constant. -/
def twinFactor (p : ℕ) : ℝ :=
  if Nat.Prime p ∧ 2 < p then 1 - GoldbachMajorArc.badFactor p else 1

theorem twinFactor_eq (p : ℕ) :
    twinFactor p = (if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
  simp [twinFactor, GoldbachMajorArc.badFactor]

theorem badFactor_quarter {p : ℕ} (hp : 3 ≤ p) : GoldbachMajorArc.badFactor p ≤ 1 / 4 := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold GoldbachMajorArc.badFactor
  rw [div_le_iff₀ (pow_pos (by linarith) 2)]
  nlinarith

theorem twinFactor_le_one (p : ℕ) : twinFactor p ≤ 1 := by
  unfold twinFactor
  split_ifs <;> [linarith [badFactor_nonneg p]; exact le_refl _]

theorem twinFactor_pos (p : ℕ) : 0 < twinFactor p := by
  unfold twinFactor
  split_ifs
  · have hp : 3 ≤ p := by omega
    linarith [badFactor_quarter hp]
  · norm_num

theorem summable_badFactor :
    Summable (fun p : ℕ => if Nat.Prime p ∧ 2 < p then GoldbachMajorArc.badFactor p else 0) := by
  refine Summable.of_norm_bounded
    (g := fun p => (9 / 4 : ℝ) * (1 / (p : ℝ) ^ 2)) ?_ ?_
  · exact ((Real.summable_one_div_nat_pow (p := 2)).2 (by decide)).mul_left (9 / 4)
  · intro p
    split_ifs
    · have hp : (3 : ℝ) ≤ p := by exact_mod_cast (by omega : 3 ≤ p)
      rw [Real.norm_eq_abs, abs_of_nonneg (badFactor_nonneg p)]
      unfold GoldbachMajorArc.badFactor
      have hrhs : (9 / 4 : ℝ) * (1 / ((p : ℝ)) ^ 2) = 9 / (4 * (p : ℝ) ^ 2) := by
        field_simp
      rw [hrhs, div_le_div_iff₀ (pow_pos (by linarith) 2) (mul_pos (by norm_num) (pow_pos (by linarith) 2))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (show (0 : ℝ) ≤ 5 * p - 3 by linarith)]
    · simp

theorem summable_badFactor_norm :
    Summable (fun p : ℕ => ‖if Nat.Prime p ∧ 2 < p then GoldbachMajorArc.badFactor p else 0‖) := by
  simpa only [Real.norm_eq_abs] using summable_badFactor.abs

theorem multipliable_twinFactor : Multipliable (fun p : ℕ => twinFactor p) := by
  have hnorm := summable_badFactor_norm
  have h := multipliable_one_sub_of_summable
    (f := fun p : ℕ => if Nat.Prime p ∧ 2 < p then GoldbachMajorArc.badFactor p else 0) hnorm
  refine h.congr fun p => ?_
  unfold twinFactor
  split_ifs <;> ring

/-- A logarithmic lower bound for Euler factors. -/
theorem log_one_sub_lower {u : ℝ} (h0 : 0 ≤ u) (h : u ≤ 1 / 4) : -(4 / 3 : ℝ) * u ≤ Real.log (1 - u) := by
  have hu1 : 0 < 1 - u := by linarith
  have h2 : Real.log ((1 - u)⁻¹) ≤ (1 - u)⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (inv_pos.mpr hu1)
  have h3 : (1 - u)⁻¹ - 1 ≤ (4 / 3 : ℝ) * u := by
    rw [← one_div, sub_le_iff_le_add, div_le_iff₀ hu1]
    nlinarith [mul_nonneg h0 (show (0 : ℝ) ≤ 1 - 4 * u by linarith)]
  have hlog : Real.log (1 - u) = -Real.log ((1 - u)⁻¹) := by rw [Real.log_inv]; ring
  rw [hlog]
  linarith

theorem log_twinFactor_bound (p : ℕ) :
    -(4 / 3 : ℝ) * (if Nat.Prime p ∧ 2 < p then GoldbachMajorArc.badFactor p else 0) ≤
      Real.log (twinFactor p) := by
  unfold twinFactor
  split_ifs
  · have hp : 3 ≤ p := by omega
    exact log_one_sub_lower (badFactor_nonneg p) (badFactor_quarter hp)
  · simp

theorem log_twinFactor_nonpos (p : ℕ) : Real.log (twinFactor p) ≤ 0 := by
  have h := Real.log_le_sub_one_of_pos (twinFactor_pos p)
  linarith [twinFactor_le_one p]

theorem summable_log_twinFactor : Summable (fun p : ℕ => Real.log (twinFactor p)) := by
  refine Summable.of_norm_bounded
    (g := fun p => (4 / 3 : ℝ) * (if Nat.Prime p ∧ 2 < p then GoldbachMajorArc.badFactor p else 0)) ?_ ?_
  · exact summable_badFactor.mul_left (4 / 3)
  · intro p
    rw [Real.norm_eq_abs, abs_of_nonpos (log_twinFactor_nonpos p)]
    have hb := log_twinFactor_bound p
    linarith

/-- Every finite partial Euler product of the odd primes dominates the twin-prime constant. -/
theorem twin_le_fullMass {B : Finset ℕ} (hB : ∀ p ∈ B, Nat.Prime p ∧ 2 < p) :
    (∏' p : ℕ, twinFactor p) ≤ fullMass B := by
  have hg : Summable (fun p => if p ∈ B then Real.log (twinFactor p) else 0) :=
    summable_log_twinFactor.abs.of_norm_bounded fun p => by
      split_ifs <;> simp [Real.norm_eq_abs]
  have hle : ∀ p : ℕ, Real.log (twinFactor p) ≤ (if p ∈ B then Real.log (twinFactor p) else 0) := by
    intro p
    split_ifs
    · exact le_refl _
    · simpa using log_twinFactor_nonpos p
  have h : (∑' p, Real.log (twinFactor p)) ≤ ∑' p, (if p ∈ B then Real.log (twinFactor p) else 0) :=
    summable_log_twinFactor.tsum_le_tsum hle hg
  have hsum' : (∑' p, (if p ∈ B then Real.log (twinFactor p) else 0)) = ∑ p ∈ B, Real.log (twinFactor p) := by
    rw [tsum_eq_sum (fun b hb => ite_eq_right hb)]
    exact sum_congr rfl fun p hp => ite_eq_left hp
  rw [hsum'] at h
  have htwin : (∏' p : ℕ, twinFactor p) = Real.exp (∑' p, Real.log (twinFactor p)) :=
    (Real.rexp_tsum_eq_tprod twinFactor_pos summable_log_twinFactor).symm
  rw [fullMass_eq_prod, htwin]
  calc
    Real.exp (∑' p, Real.log (twinFactor p)) ≤ Real.exp (∑ p ∈ B, Real.log (twinFactor p)) :=
      Real.exp_le_exp.mpr h
    _ = ∏ p ∈ B, twinFactor p := by
      rw [Real.exp_sum]
      exact prod_congr rfl fun p _ => Real.exp_log (twinFactor_pos p)
    _ = _ := prod_congr rfl fun p hp => by rw [twinFactor, ite_eq_left (hB p hp)]

/-- The tail factor: the Euler factor restricted to odd primes above a cutoff. -/
def tailFactor (k : ℕ) (p : ℕ) : ℝ :=
  if Nat.Prime p ∧ 2 < p ∧ k < p then 1 - GoldbachMajorArc.badFactor p else 1

theorem tailFactor_pos (k p : ℕ) : 0 < tailFactor k p := by
  unfold tailFactor
  split_ifs
  · have hp : 3 ≤ p := by omega
    linarith [badFactor_quarter hp]
  · norm_num

theorem log_tailFactor_lower (k p : ℕ) :
    -(4 / 3 : ℝ) * (if k < p then 1 / ((p : ℝ) - 1) ^ 2 else 0) ≤ Real.log (tailFactor k p) := by
  unfold tailFactor
  by_cases hc : Nat.Prime p ∧ 2 < p ∧ k < p
  · rw [ite_eq_left hc]
    have hp : 3 ≤ p := by omega
    unfold GoldbachMajorArc.badFactor
    have hk : k < p := hc.2.2
    rw [ite_eq_left hk]
    exact log_one_sub_lower (badFactor_nonneg p) (badFactor_quarter hp)
  · rw [ite_eq_right hc]
    have : 0 ≤ (4 / 3 : ℝ) * (if k < p then 1 / ((p : ℝ) - 1) ^ 2 else 0) := by positivity
    linarith [Real.log_one]

theorem summable_tailDeficit {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun p : ℕ => if k < p then 1 / ((p : ℝ) - 1) ^ 2 else 0) := by
  refine Summable.of_norm_bounded (g := fun p => (9 / 4 : ℝ) * (1 / (p : ℝ) ^ 2)) ?_ ?_
  · exact ((Real.summable_one_div_nat_pow (p := 2)).2 (by decide)).mul_left (9 / 4)
  · intro p
    split_ifs
    · have hp : (3 : ℝ) ≤ p := by
        have h3 : 3 ≤ p := by omega
        exact_mod_cast h3
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hrhs : (9 / 4 : ℝ) * (1 / ((p : ℝ)) ^ 2) = 9 / (4 * (p : ℝ) ^ 2) := by
        field_simp
      rw [hrhs, div_le_div_iff₀ (pow_pos (by linarith) 2) (mul_pos (by norm_num) (pow_pos (by linarith) 2))]
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (show (0 : ℝ) ≤ 5 * p - 3 by linarith)]
    · simp

theorem summable_log_tailFactor {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun p => Real.log (tailFactor k p)) := by
  refine Summable.of_norm_bounded
    (g := fun p => (4 / 3 : ℝ) * (if k < p then 1 / ((p : ℝ) - 1) ^ 2 else 0)) ?_ ?_
  · exact (summable_tailDeficit hk).mul_left (4 / 3)
  · intro p
    have hnon : Real.log (tailFactor k p) ≤ 0 := by
      have h := Real.log_le_sub_one_of_pos (tailFactor_pos k p)
      have hle : tailFactor k p ≤ 1 := by
        unfold tailFactor
        split_ifs <;> [linarith [badFactor_nonneg p]; exact le_refl _]
      linarith
    rw [Real.norm_eq_abs, abs_of_nonpos hnon]
    have hb := log_tailFactor_lower k p
    linarith

/-- A telescoping bound for sums over an integer interval. -/
theorem sum_sq_inv_le (k : ℕ) (hk : 2 ≤ k) (s : Finset ℕ) :
    (∑ p ∈ s, if k < p then 1 / ((p : ℝ) - 1) ^ 2 else 0) ≤ 1 / ((k : ℝ) - 1) := by
  classical
  have hkR : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  rw [← Finset.sum_filter]
  by_cases hs : s.filter (fun p => k < p) = ∅
  · rw [hs]
    positivity
  · obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image (s.filter (fun p => k < p)) id
      (Finset.nonempty_iff_ne_empty.mpr hs)
    have hkm : k + 1 ≤ M := by
      rw [mem_filter] at hM
      omega
    have hM3 : (2 : ℝ) < M := by exact_mod_cast (show 3 ≤ M by omega)
    calc
      _ ≤ ∑ n ∈ Icc (k + 1) M, 1 / ((n : ℝ) - 1) ^ 2 := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro p hp
          rw [mem_filter] at hp
          exact mem_Icc.mpr ⟨by omega, by simpa using hmax p (mem_filter.mpr hp)⟩
        · intro p _ _; positivity
      _ ≤ ∑ n ∈ Icc (k + 1) M, (1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)) := by
        refine sum_le_sum fun n hn => ?_
        have hmem := mem_Icc.mp hn
        have hn3 : 3 ≤ n := by omega
        have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
          have hnR : (2 : ℝ) < n := by exact_mod_cast (show 3 ≤ n by omega)
          linarith
        have hn2 : (0 : ℝ) < (n : ℝ) - 2 := by
          have hnR : (2 : ℝ) < n := by exact_mod_cast (show 3 ≤ n by omega)
          linarith
        rw [div_sub_div 1 1 hn2.ne' hn1.ne',
          show (1 : ℝ) * ((n : ℝ) - 1) - ((n : ℝ) - 2) * 1 = 1 by ring,
          div_le_div_iff₀ (pow_pos hn1 2) (mul_pos hn2 hn1)]
        have hle : ((n : ℝ) - 2) * ((n : ℝ) - 1) ≤ ((n : ℝ) - 1) * ((n : ℝ) - 1) :=
          mul_le_mul_of_nonneg_right (by linarith) hn1.le
        nlinarith
      _ = 1 / (((k + 1 : ℕ) : ℝ) - 2) - 1 / ((M : ℝ) - 1) := by
        have h := telescoping (fun y => 1 / (y - 1)) (k + 1) M (by omega)
        convert h using 1 <;> push_cast <;> ring
      _ ≤ 1 / ((k : ℝ) - 1) := by
        have hM1 : (0 : ℝ) < (M : ℝ) - 1 := by linarith
        have hnon : 0 ≤ 1 / ((M : ℝ) - 1) := by positivity
        have heq : (((k + 1 : ℕ) : ℝ) - 2) = (k : ℝ) - 1 := by push_cast; ring
        rw [heq]
        linarith

/-- The logarithm of the tail product is bounded below. -/
theorem tsum_log_tail_lower {k : ℕ} (hk : 2 ≤ k) :
    -(4 / 3 : ℝ) * (1 / ((k : ℝ) - 1)) ≤ ∑' p, Real.log (tailFactor k p) := by
  have ha := (summable_log_tailFactor hk).hasSum
  have hlow : -(4 / 3 : ℝ) * (1 / ((k : ℝ) - 1)) ≤ ∑' p, Real.log (tailFactor k p) := by
    apply le_hasSum_of_le_sum ha
    intro s
    have h1 : -(4 / 3 : ℝ) * (∑ p ∈ s, (if k < p then 1 / ((p : ℝ) - 1) ^ 2 else 0)) ≤
        ∑ p ∈ s, Real.log (tailFactor k p) := by
      rw [Finset.mul_sum]
      exact sum_le_sum fun p _ => log_tailFactor_lower k p
    have h2 := sum_sq_inv_le k hk s
    have h4 : (0 : ℝ) ≤ 4 / 3 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left h2 h4]
  exact hlow

/-- The product over odd primes above a cutoff is at least `1 - 4/(k-1)`. -/
theorem tail_prod_lower {k : ℕ} (hk : 2 ≤ k) :
    1 - 4 / ((k : ℝ) - 1) ≤ ∏' p : ℕ, tailFactor k p := by
  have htprod : (∏' p : ℕ, tailFactor k p) = Real.exp (∑' p, Real.log (tailFactor k p)) :=
    (Real.rexp_tsum_eq_tprod (tailFactor_pos k) (summable_log_tailFactor hk)).symm
  rw [htprod]
  calc
    (1 : ℝ) - 4 / ((k : ℝ) - 1) ≤ Real.exp (-(4 / 3 : ℝ) * (1 / ((k : ℝ) - 1))) := by
      have h := Real.add_one_le_exp (-(4 / 3 : ℝ) * (1 / ((k : ℝ) - 1)))
      have hpos : 0 < (k : ℝ) - 1 := by
        have hk1 : (1 : ℝ) < k := by exact_mod_cast (by omega : 1 < k)
        linarith
      have hone : 0 < 1 / ((k : ℝ) - 1) := by positivity
      have hc : (4 / 3 : ℝ) * (1 / ((k : ℝ) - 1)) ≤ 4 * (1 / ((k : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hone.le
      rw [show (4 : ℝ) / ((k : ℝ) - 1) = 4 * (1 / ((k : ℝ) - 1)) by ring]
      linarith
    _ ≤ Real.exp (∑' p, Real.log (tailFactor k p)) := Real.exp_le_exp.mpr (tsum_log_tail_lower hk)

/-- The Euler factors outside a finite set are multipliable. -/
theorem multipliable_indicator (B : Finset ℕ) :
    Multipliable (fun p => if p ∈ B then twinFactor p else 1) := by
  have hnorm : Summable (fun p : ℕ =>
      ‖if Nat.Prime p ∧ 2 < p then GoldbachMajorArc.badFactor p else 0‖) := by
    simpa only [Real.norm_eq_abs] using summable_badFactor.abs
  have hsum : Summable (fun p : ℕ => ‖if p ∈ B then 1 - twinFactor p else 0‖) :=
    hnorm.of_norm_bounded fun p => by
      rw [norm_norm]
      by_cases hb : p ∈ B
      · rw [ite_eq_left hb]
        have ht : 1 - twinFactor p = if Nat.Prime p ∧ 2 < p then GoldbachMajorArc.badFactor p else 0 := by
          rw [twinFactor]
          split_ifs <;> ring
        rw [ht]
      · rw [ite_eq_right hb]
        exact norm_nonneg _
  have h := multipliable_one_sub_of_summable
    (f := fun p : ℕ => if p ∈ B then 1 - twinFactor p else 0) hsum
  refine h.congr fun p => ?_
  by_cases hb : p ∈ B
  · rw [ite_eq_left hb, ite_eq_left hb]
    unfold twinFactor at h ⊢
    split_ifs <;> ring
  · rw [ite_eq_right hb, ite_eq_right hb, sub_zero]

theorem multipliable_tailFactor {k : ℕ} : Multipliable (tailFactor k) := by
  have hsum : Summable (fun p : ℕ =>
      ‖if Nat.Prime p ∧ 2 < p ∧ k < p then GoldbachMajorArc.badFactor p else 0‖) :=
    summable_badFactor_norm.of_norm_bounded fun p => by
      rw [norm_norm]
      by_cases hc : Nat.Prime p ∧ 2 < p ∧ k < p
      · rw [ite_eq_left hc, ite_eq_left (show Nat.Prime p ∧ 2 < p from ⟨hc.1, hc.2.1⟩)]
      · rw [ite_eq_right hc]
        exact (norm_nonneg
          (if Nat.Prime p ∧ 2 < p then GoldbachMajorArc.badFactor p else 0 : ℝ)).trans_eq' (norm_zero).symm
  have h := multipliable_one_sub_of_summable
    (f := fun p : ℕ => if Nat.Prime p ∧ 2 < p ∧ k < p then GoldbachMajorArc.badFactor p else 0) hsum
  refine h.congr fun p => ?_
  unfold tailFactor
  by_cases hc : Nat.Prime p ∧ 2 < p ∧ k < p
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc, sub_zero]

theorem coprimePrimes_two_pow (a k : ℕ) (ha : 0 < a) : coprimePrimes (2 ^ a) k = oddPrimes k := by
  ext p
  simp only [coprimePrimes, oddPrimes, smallPrimes, mem_filter]
  constructor
  · rintro ⟨⟨hr, hprime⟩, hnd⟩
    refine ⟨⟨hr, hprime⟩, ?_⟩
    by_contra hc
    interval_cases p
    · norm_num at hprime
    · norm_num at hprime
    · exact hnd (dvd_pow_self 2 ha.ne')
  · rintro ⟨⟨hr, hprime⟩, hpos⟩
    refine ⟨⟨hr, hprime⟩, fun hd => ?_⟩
    have hne : p ≠ 2 := by
      rintro rfl
      norm_num at hpos
    have hc : Nat.Coprime p 2 := (Nat.coprime_primes hprime Nat.prime_two).mpr hne
    have hc' : Nat.Coprime p (2 ^ a) := Nat.Coprime.pow_right a hc
    have hd1 : p ∣ 1 := hc' ▸ Nat.dvd_gcd dvd_rfl hd
    exact hprime.ne_one (Nat.eq_one_of_dvd_one hd1)

/-- The twin-prime constant as a finite partial product times the tail product. -/
theorem twin_eq_prod_mul_tail {k : ℕ} (_hk : 2 ≤ k) :
    (∏' p : ℕ, twinFactor p) = fullMass (oddPrimes k) * (∏' p : ℕ, tailFactor k p) := by
  have hsplit : ∀ p, twinFactor p = (if p ∈ oddPrimes k then twinFactor p else 1) * tailFactor k p := by
    intro p
    by_cases hb : p ∈ oddPrimes k
    · have hk : ¬ k < p := by
        simp only [oddPrimes, smallPrimes, mem_filter] at hb
        have hr : p ∈ range (k + 1) := hb.1.1
        simp only [mem_range] at hr
        omega
      unfold tailFactor
      rw [ite_eq_left hb, ite_eq_right (fun h => hk h.2.2), mul_one]
    · have hkp : (Nat.Prime p ∧ 2 < p) → k < p := by
        rintro ⟨h1, h2⟩
        by_contra hc
        simp only [oddPrimes, smallPrimes, mem_filter] at hb
        exact hb ⟨⟨mem_range.mpr (by omega), h1⟩, h2⟩
      unfold twinFactor tailFactor
      by_cases hp : Nat.Prime p ∧ 2 < p
      · rw [ite_eq_right hb, ite_eq_left hp,
          ite_eq_left (show Nat.Prime p ∧ 2 < p ∧ k < p from ⟨hp.1, hp.2, hkp hp⟩), one_mul]
      · rw [ite_eq_right hb, ite_eq_right hp, ite_eq_right (fun h => hp ⟨h.1, h.2.1⟩), mul_one]
  rw [tprod_congr hsplit, Multipliable.tprod_mul (multipliable_indicator (oddPrimes k))
    (multipliable_tailFactor)]
  refine congrArg₂ (· * ·) ?_ rfl
  rw [tprod_eq_prod (fun b hb => ite_eq_right hb), fullMass_eq_prod]
  refine prod_congr rfl fun p hp => ?_
  have hOdd : Nat.Prime p ∧ 2 < p := by
    simp only [oddPrimes, smallPrimes, mem_filter] at hp
    exact ⟨hp.1.2, hp.2⟩
  rw [ite_eq_left hp, twinFactor, ite_eq_left hOdd]/-! ### Sharp bounds for the truncated singular series -/

theorem twin_le_one : (∏' p : ℕ, twinFactor p) ≤ 1 := by
  calc
    (∏' p : ℕ, twinFactor p) ≤ fullMass ∅ := twin_le_fullMass (by simp)
    _ = 1 := by simp [fullMass]

theorem fullMass_nonneg {B : Finset ℕ} (hB : ∀ p ∈ B, 3 ≤ p) : 0 ≤ fullMass B := by
  rw [fullMass_eq_prod]
  exact prod_nonneg fun p hp => by linarith [badFactor_quarter (hB p hp)]

theorem tail_prod_pos {k : ℕ} (hk : 2 ≤ k) : 0 < ∏' p : ℕ, tailFactor k p := by
  rw [show (∏' p : ℕ, tailFactor k p) = Real.exp (∑' p, Real.log (tailFactor k p)) from
    (Real.rexp_tsum_eq_tprod (tailFactor_pos k) (summable_log_tailFactor hk)).symm]
  exact Real.exp_pos _

theorem twin_nonneg {k : ℕ} (hk : 2 ≤ k) : 0 ≤ (∏' p : ℕ, twinFactor p) := by
  rw [twin_eq_prod_mul_tail hk]
  have hOdd : ∀ p ∈ oddPrimes k, 3 ≤ p := by
    intro p hp
    simp only [oddPrimes, smallPrimes, mem_filter] at hp
    omega
  exact mul_nonneg (fullMass_nonneg hOdd) (tail_prod_pos hk).le

theorem coprimePrimes_le {m k : ℕ} {p : ℕ} (hp : p ∈ coprimePrimes m k) : p ≤ k := by
  simp only [coprimePrimes, smallPrimes, mem_filter] at hp
  have hr : p ∈ range (k + 1) := hp.1.1
  simp only [mem_range] at hr
  omega

/-- The finite partial product at a large cutoff is at most `1 + 16/k` times the constant. -/
theorem fullMass_odd_le {k : ℕ} (hk : 9 ≤ k) :
    fullMass (oddPrimes k) ≤ (∏' p : ℕ, twinFactor p) * (1 + 16 / (k : ℝ)) := by
  have hkR : (9 : ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) < k := by linarith
  have htail : (1 : ℝ) - 4 / ((k : ℝ) - 1) ≤ ∏' p : ℕ, tailFactor k p := tail_prod_lower (by omega)
  have htpos' : (0 : ℝ) < ∏' p : ℕ, tailFactor k p := tail_prod_pos (by omega)
  have hdiv : fullMass (oddPrimes k) =
      (∏' p : ℕ, twinFactor p) / (∏' p : ℕ, tailFactor k p) := by
    rw [eq_div_iff htpos'.ne']
    exact (twin_eq_prod_mul_tail (by omega)).symm
  have e1 : (1 : ℝ) / (1 + 16 / (k : ℝ)) = (k : ℝ) / (k + 16) := by
    field_simp [ne_of_gt hk1]
  have e2 : (1 : ℝ) - 4 / ((k : ℝ) - 1) = ((k : ℝ) - 5) / ((k : ℝ) - 1) := by
    field_simp [ne_of_gt hk1]
    ring
  have hstep : (k : ℝ) / (k + 16) ≤ ((k : ℝ) - 5) / ((k : ℝ) - 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr (show (7 : ℝ) ≤ k by linarith)) (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [← e2] at hstep
  have hinv : (1 : ℝ) / (1 + 16 / (k : ℝ)) ≤ ∏' p : ℕ, tailFactor k p := by
    rw [e1]
    exact hstep.trans htail
  rw [hdiv]
  refine mul_le_mul_of_nonneg_left ?_ (twin_nonneg (k := k) (by omega))
  have hkpos : (0 : ℝ) < k := by linarith
  calc
    (∏' p : ℕ, tailFactor k p)⁻¹ = 1 / (∏' p : ℕ, tailFactor k p) := (one_div _).symm
    _ ≤ 1 / (1 / (1 + 16 / (k : ℝ))) :=
      one_div_le_one_div_of_le
        (div_pos (by norm_num)
          (show (0 : ℝ) < 1 + 16 / (k : ℝ) by
            have h16 : (0 : ℝ) < 16 / (k : ℝ) := div_pos (by norm_num) hkpos
            linarith)) hinv
    _ = 1 + 16 / (k : ℝ) := one_div_one_div _

/-- Uniform sharp lower bound for the truncated singular series of an even target. -/
theorem floor_lower_sharp (m k : ℕ) (he : Even m) (hk : 3 ≤ k) :
    2 * (∏' p : ℕ, twinFactor p) - 128 * (1 + Real.sqrt 2) / Real.sqrt ((k : ℝ)) ≤
      ∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q m).re := by
  classical
  have hB : ∀ p ∈ coprimePrimes m k, p.Prime ∧ 2 < p := coprimePrimes_odd he
  have hlo : ∀ p ∈ coprimePrimes m k, 3 ≤ p := fun p hp => by have := hB p hp; omega
  have hhi : ∀ p ∈ coprimePrimes m k, p ≤ k := fun p hp => coprimePrimes_le hp
  have h1 := altMass_truncation (coprimePrimes m k) 1 k
  have h2 := altMass_truncation (coprimePrimes m k) 2 k
  have hr1 := removedMass_le (coprimePrimes m k) 1 k hk hlo hhi
  have hr2 := removedMass_le (coprimePrimes m k) 2 k hk hlo hhi
  have hmass := twin_le_fullMass hB
  have hlow := floor_lower m k he (by omega)
  rw [Real.sqrt_div (Nat.cast_nonneg 1) ((k : ℝ))] at hr1
  rw [Real.sqrt_div (Nat.cast_nonneg 2) ((k : ℝ))] at hr2
  norm_num at hr1 hr2
  have hsplit : 128 * (1 + Real.sqrt 2) / Real.sqrt ((k : ℝ)) =
      128 * (Real.sqrt ((k : ℝ)))⁻¹ + 128 * (Real.sqrt 2 / Real.sqrt ((k : ℝ))) := by ring
  nlinarith [h1.1, h2.1, hr1, hr2, hlow, hmass]

/-- Sharp upper bound along powers of two. -/
theorem floor_upper_sharp (a k : ℕ) (ha : 0 < a) (hk : 9 ≤ k) :
    (∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q (2 ^ a)).re) ≤
      2 * (∏' p : ℕ, twinFactor p) * (1 + 16 / (k : ℝ)) +
        128 * (1 + Real.sqrt 2) / Real.sqrt ((k : ℝ)) := by
  classical
  have he : Even (2 ^ a) := even_iff_two_dvd.mpr (dvd_pow_self 2 ha.ne')
  have hB : ∀ p ∈ coprimePrimes (2 ^ a) k, p.Prime ∧ 2 < p := coprimePrimes_odd he
  have hlo : ∀ p ∈ coprimePrimes (2 ^ a) k, 3 ≤ p := fun p hp => by have := hB p hp; omega
  have hhi : ∀ p ∈ coprimePrimes (2 ^ a) k, p ≤ k := fun p hp => coprimePrimes_le hp
  have h1 := altMass_truncation (coprimePrimes (2 ^ a) k) 1 k
  have h2 := altMass_truncation (coprimePrimes (2 ^ a) k) 2 k
  have hr1 := removedMass_le (coprimePrimes (2 ^ a) k) 1 k (by omega) hlo hhi
  have hr2 := removedMass_le (coprimePrimes (2 ^ a) k) 2 k (by omega) hlo hhi
  have hprod := fullMass_odd_le hk
  rw [← coprimePrimes_two_pow a k ha] at hprod
  have hlow := floor_eq_two a k ha (by omega)
  rw [Real.sqrt_div (Nat.cast_nonneg 1) ((k : ℝ))] at hr1
  rw [Real.sqrt_div (Nat.cast_nonneg 2) ((k : ℝ))] at hr2
  norm_num at hr1 hr2
  have hsplit : 128 * (1 + Real.sqrt 2) / Real.sqrt ((k : ℝ)) =
      128 * (Real.sqrt ((k : ℝ)))⁻¹ + 128 * (Real.sqrt 2 / Real.sqrt ((k : ℝ))) := by ring
  have hprod2 := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [h1.2, h2.2, hr1, hr2, hlow, hprod2, hsplit]

/- The square kernel integral over the arc of denominator `q`, with the width of PR #4198. -/
/-- The square kernel integral over the arc of denominator `q`. -/
def arcIntegral (N k m q : ℕ) : ℂ :=
  ∫ t in -(((k : ℝ) ^ 3) / ((q : ℝ) * N))..(((k : ℝ) ^ 3) / ((q : ℝ) * N)),
    GoldbachEstermannKernel.twisted N m t

open GoldbachBa08Approx GoldbachBa08Kernel in
/-- The square-kernel model of PR #4198 differs from the count `v = 2N - m + 1` times the
truncated singular series by at most `8 N / √k`. -/
theorem model_bounds (N k m : ℕ) (hk : 0 < k) (hwidth : 2 * k ^ 3 ≤ N)
    (hNm : N ≤ m) (hm : m ≤ 2 * N) :
    (((2 * N - m : ℕ) : ℝ) + 1) * (∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q m).re) -
        8 * (N : ℝ) / Real.sqrt ((k : ℝ)) ≤ (GoldbachBa08Kernel.complexModel N k m ((k : ℝ) ^ 3)).re ∧
      (GoldbachBa08Kernel.complexModel N k m ((k : ℝ) ^ 3)).re ≤
        (((2 * N - m : ℕ) : ℝ) + 1) * (∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q m).re) +
        8 * (N : ℝ) / Real.sqrt ((k : ℝ)) := by
  classical
  have hN : (0 : ℝ) < N := by
    have hk3 : 1 ≤ k ^ 3 := Nat.one_le_pow 3 k hk
    exact_mod_cast (show 0 < N by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  set v : ℝ := ((2 * N - m : ℕ) : ℝ) + 1 with hv
  have hvc : (((2 * N - m : ℕ) : ℂ) + 1) = (v : ℂ) := by
    dsimp [v]
    push_cast
    ring
  have htail (q : ℕ) (hq : q ∈ Icc 1 k) : ‖arcIntegral N k m q - (v : ℂ)‖ ≤
      2 * ((q : ℝ) * (N : ℝ)) / (k : ℝ) ^ 3 := by
    unfold arcIntegral
    obtain ⟨hq1, hq2⟩ := mem_Icc.mp hq
    have hb : (0 : ℝ) < ((k : ℝ) ^ 3) / ((q : ℝ) * N) := by positivity
    have hbhalf : ((k : ℝ) ^ 3) / ((q : ℝ) * N) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      have hkc3 : ((k : ℝ)) ^ 3 = ((k ^ 3 : ℕ) : ℝ) := by push_cast; ring
      have hle : 2 * ((k ^ 3 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hwidth
      have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq1
      nlinarith [mul_le_mul_of_nonneg_right hq1R hN.le]
    have h := norm_twisted_tail_upper N m hb hbhalf hNm hm
    rw [hvc] at h
    exact h.trans (le_of_eq (div_div_eq_mul_div _ _ _))
  have hcv (q : ℕ) (hq : q ∈ Icc 1 k) :
      (GoldbachMajorArc.coefficient q m * (v : ℂ)).re = (GoldbachMajorArc.coefficient q m).re * v := by
    simp only [Complex.mul_re, GoldbachMajorArc.coefficient_im_zero m (mem_Icc.mp hq).1, zero_mul,
      sub_zero, Complex.ofReal_re]
  have hmain : ∀ q ∈ Icc 1 k,
      (GoldbachMajorArc.coefficient q m * arcIntegral N k m q).re =
        (GoldbachMajorArc.coefficient q m).re * v +
          (GoldbachMajorArc.coefficient q m * (arcIntegral N k m q - (v : ℂ))).re := by
    intro q hq
    conv_lhs => rw [show arcIntegral N k m q = (v : ℂ) + (arcIntegral N k m q - (v : ℂ)) from by ring]
    rw [mul_add, Complex.add_re, hcv q hq]
  have hE : |∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q m * (arcIntegral N k m q - (v : ℂ))).re| ≤
      8 * (N : ℝ) / Real.sqrt ((k : ℝ)) := by
    calc
      |∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q m * (arcIntegral N k m q - (v : ℂ))).re| ≤
          ∑ q ∈ Icc 1 k, |(GoldbachMajorArc.coefficient q m * (arcIntegral N k m q - (v : ℂ))).re| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q ∈ Icc 1 k,
          ‖GoldbachMajorArc.coefficient q m‖ * ‖arcIntegral N k m q - (v : ℂ)‖ := by
        refine sum_le_sum fun q hq => ?_
        exact (Complex.abs_re_le_norm _).trans_eq (norm_mul _ _)
      _ ≤ ∑ q ∈ Icc 1 k,
          ‖GoldbachMajorArc.coefficient q m‖ * (2 * ((q : ℝ) * (N : ℝ)) / (k : ℝ) ^ 3) :=
        sum_le_sum fun q hq => mul_le_mul_of_nonneg_left (htail q hq) (norm_nonneg _)
      _ ≤ ∑ q ∈ Icc 1 k,
          ‖GoldbachMajorArc.coefficient q m‖ * (2 * ((k : ℝ) * (N : ℝ)) / (k : ℝ) ^ 3) := by
        refine sum_le_sum fun q hq => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have hq2 : (q : ℝ) ≤ (k : ℝ) := by exact_mod_cast (mem_Icc.mp hq).2
        gcongr
      _ = (2 * ((k : ℝ) * (N : ℝ)) / (k : ℝ) ^ 3) *
          (∑ q ∈ Icc 1 k, ‖GoldbachMajorArc.coefficient q m‖) := by
        rw [← Finset.sum_mul]
        ring
      _ ≤ (2 * ((k : ℝ) * (N : ℝ)) / (k : ℝ) ^ 3) * (4 * Real.sqrt ((k : ℝ))) :=
        mul_le_mul_of_nonneg_left (GoldbachMajorArc.sum_norm_coefficient_le_sqrt k m) (by positivity)
      _ = 8 * (N : ℝ) * Real.sqrt ((k : ℝ)) / ((k : ℝ)) ^ 2 := by
        field_simp [hkR.ne']
        ring
      _ ≤ 8 * (N : ℝ) / Real.sqrt ((k : ℝ)) := by
        have hs : Real.sqrt ((k : ℝ)) ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hk1 hN.le]
  unfold GoldbachBa08Kernel.complexModel
  change _ ≤ (∑ q ∈ Icc 1 k, GoldbachMajorArc.coefficient q m * arcIntegral N k m q).re ∧
    (∑ q ∈ Icc 1 k, GoldbachMajorArc.coefficient q m * arcIntegral N k m q).re ≤ _
  rw [Complex.re_sum, sum_congr rfl hmain, Finset.sum_add_distrib, ← Finset.sum_mul]
  obtain ⟨h1, h2⟩ := abs_le.mp hE
  dsimp [v] at h1 h2 ⊢
  constructor <;> nlinarith

/-! ### The main theorem -/

/-- The key cutoff: beyond it the truncation and model losses are controlled by `ε`. -/
def sharpCutoff (ε : ℝ) : ℕ := max 9 (Nat.floor ((800 / ε) ^ 2) + 1)

theorem sqrt_ge_sharpCutoff {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : sharpCutoff ε ≤ k) :
    800 / ε ≤ Real.sqrt ((k : ℝ)) := by
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  have hK : Nat.floor ((800 / ε) ^ 2) + 1 ≤ k := le_trans (le_max_right _ _) hk
  have hfl : (800 / ε) ^ 2 < (k : ℝ) := (Nat.floor_lt (by positivity)).mp (by omega)
  exact le_of_lt hfl

theorem one_div_sqrt_le {ε : ℝ} (hε : 0 < ε) {k : ℕ} (hk : sharpCutoff ε ≤ k) :
    1 / Real.sqrt ((k : ℝ)) ≤ ε / 800 := by
  have hsk := sqrt_ge_sharpCutoff hε hk
  refine (one_div_le_one_div_of_le (by positivity) hsk).trans_eq ?_
  field_simp

theorem nine_le_sharpCutoff (ε : ℝ) : 9 ≤ sharpCutoff ε := le_max_left _ _

/-- The eventual inputs of PR #4198: arc geometry and the uniform approximation error. -/
theorem sharp_inputs (δ : ℝ) (hδ : 0 < δ) :
    ∃ T : ℕ, ∀ N : ℕ, T ≤ N →
      1 ≤ Nat.log 2 (N + 2) ∧ Nat.log 2 (N + 2) ≤ (Nat.log 2 (N + 2)) ^ 3 ∧
        2 * ((Nat.log 2 (N + 2)) ^ 3) ^ 2 < N ∧
      ∀ m : ℕ, ‖GoldbachBa08Approx.coefficient N m (Nat.log 2 (N + 2))
        ((Nat.log 2 (N + 2)) ^ 3) - GoldbachBa08Approx.scaledModel N m (Nat.log 2 (N + 2))
        ((Nat.log 2 (N + 2)) ^ 3)‖ ≤ δ * (N : ℝ) := by
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1
    (GoldbachBa08Approx.eventually_geometry.and (GoldbachBa08Approx.eventually_approx (ε := δ) hδ))
  refine ⟨T₀, fun N hN => ?_⟩
  have h := hT₀ N hN
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  dsimp only at h4
  exact ⟨h1, h2, h3, h4⟩

/-- Eventual uniform sharp lower bound on the reflected band. -/
theorem eventually_lower_sharp (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℕ, ∀ N m : ℕ, T ≤ N → 4 * N ≤ 3 * m → 2 * m ≤ 3 * N → Even m →
      (2 * (∏' p : ℕ, twinFactor p) - ε) * (2 * (N : ℝ) - (m : ℝ)) ≤
        (GoldbachBa08Approx.coefficient N m (Nat.log 2 (N + 2)) ((Nat.log 2 (N + 2)) ^ 3)).re := by
  classical
  obtain ⟨T₀, hT₀⟩ := sharp_inputs (ε / 8) (by positivity)
  refine ⟨max (2 ^ (sharpCutoff ε)) T₀, ?_⟩
  intro N m hN h4 h2 he
  have hN₀ : T₀ ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hk1, hkc, hsep, happ⟩ := hT₀ N hN₀
  have hkK : sharpCutoff ε ≤ Nat.log 2 (N + 2) :=
    Nat.le_log_of_pow_le (by decide) ((le_max_left _ _).trans (hN.trans (Nat.le_add_right N 2)))
  set k := Nat.log 2 (N + 2) with hkdef
  have hwidth : 2 * k ^ 3 ≤ N := by
    have hk3 : 1 ≤ k ^ 3 := Nat.one_le_pow 3 k (by omega)
    calc
      2 * k ^ 3 = 2 * k ^ 3 * 1 := by ring
      _ ≤ 2 * k ^ 3 * k ^ 3 := Nat.mul_le_mul_left _ hk3
      _ = 2 * (k ^ 3) ^ 2 := by rw [Nat.pow_two]; ring
      _ ≤ N := le_of_lt hsep
  have hmN : N ≤ m := by omega
  have hm2 : m ≤ 2 * N := by omega
  have hsub : ((2 * N - m : ℕ) : ℝ) = 2 * (N : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have h2' : 2 * (m : ℝ) ≤ 3 * (N : ℝ) := by exact_mod_cast h2
  have hvN : (N : ℝ) ≤ 2 * (((2 * N - m : ℕ) : ℝ) + 1) := by linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hv0 : (0 : ℝ) ≤ ((2 * N - m : ℕ) : ℝ) + 1 := by linarith
  have hw := one_div_sqrt_le hε hkK
  have hmodel := (model_bounds N k m hk1 hwidth hmN hm2).1
  have hfloor := floor_lower_sharp m k he
    ((show (3 : ℕ) ≤ 9 by omega).trans ((nine_le_sharpCutoff ε).trans hkK))
  rw [div_eq_mul_one_div] at hmodel hfloor
  have hs3 : 1 + Real.sqrt 2 ≤ (3 : ℝ) := by
    have hs2 : Real.sqrt 2 ≤ 2 := by
      rw [Real.sqrt_le_iff]
      norm_num
    linarith
  have hR : (128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ))) ≤ (12 / 25 : ℝ) * ε := by
    calc
      (128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ))) ≤ (384 : ℝ) * (1 / Real.sqrt ((k : ℝ))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ 384 * (ε / 800) := mul_le_mul_of_nonneg_left hw (by norm_num)
      _ = (12 / 25 : ℝ) * ε := by ring
  have hRv : (((2 * N - m : ℕ) : ℝ) + 1) * ((128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ)))) ≤
      (((2 * N - m : ℕ) : ℝ) + 1) * ((12 / 25 : ℝ) * ε) := mul_le_mul_of_nonneg_left hR hv0
  have h8 : 8 * (N : ℝ) * (1 / Real.sqrt ((k : ℝ))) ≤ (ε / 100) * (N : ℝ) := by
    calc
      8 * (N : ℝ) * (1 / Real.sqrt ((k : ℝ))) ≤ 8 * (N : ℝ) * (ε / 800) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      _ = (ε / 100) * (N : ℝ) := by ring
  have hA : (GoldbachBa08Kernel.complexModel N k m ((k : ℝ) ^ 3)).re - ε / 8 * (N : ℝ) ≤
      (GoldbachBa08Approx.coefficient N m k (k ^ 3)).re := by
    have heq : GoldbachBa08Approx.scaledModel N m k (k ^ 3) =
      GoldbachBa08Kernel.complexModel N k m ((k : ℝ) ^ 3) := by
      simp only [GoldbachBa08Approx.scaledModel, GoldbachBa08Kernel.complexModel,
        GoldbachBlockGeometry.width, Nat.cast_pow]
    have h := Complex.abs_re_le_norm (GoldbachBa08Approx.coefficient N m k (k ^ 3) -
      GoldbachBa08Approx.scaledModel N m k (k ^ 3))
    rw [Complex.sub_re] at h
    obtain ⟨h1, h2⟩ := abs_le.mp (h.trans (happ m))
    rw [heq] at h1
    linarith
  have hvE : (ε / 8) * (N : ℝ) ≤ (((2 * N - m : ℕ) : ℝ) + 1) * (ε / 4) := by
    have h := mul_le_mul_of_nonneg_right hvN hε.le
    nlinarith
  have hvNε : (ε / 100) * (N : ℝ) ≤ (ε / 100) * (2 * (((2 * N - m : ℕ) : ℝ) + 1)) := by
    have h := mul_le_mul_of_nonneg_right hvN (by positivity : (0 : ℝ) ≤ ε / 100)
    nlinarith
  have hvfloor : (((2 * N - m : ℕ) : ℝ) + 1) *
      (2 * (∏' p : ℕ, twinFactor p) - (128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ)))) ≤
      (((2 * N - m : ℕ) : ℝ) + 1) * (∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q m).re) :=
    mul_le_mul_of_nonneg_left hfloor hv0
  have hN6 : 6 ≤ N := by
    have h9 : (2 : ℕ) ^ 9 ≤ 2 ^ sharpCutoff ε := Nat.pow_le_pow_right (by decide) (nine_le_sharpCutoff ε)
    have := (le_max_left (2 ^ sharpCutoff ε) T₀).trans hN
    norm_num at h9
    omega
  have hv4 : (4 : ℝ) ≤ ((2 * N - m : ℕ) : ℝ) + 1 := by
    have hv' : (N : ℝ) ≤ 2 * ((2 * N - m : ℕ) : ℝ) := by
      have : N ≤ 2 * (2 * N - m) := by omega
      exact_mod_cast this
    have : 6 ≤ (N : ℝ) := by exact_mod_cast hN6
    linarith
  have hv4ε : (4 : ℝ) * ε ≤ (((2 * N - m : ℕ) : ℝ) + 1) * ε := mul_le_mul_of_nonneg_right hv4 hε.le
  have hC : (0 : ℝ) ≤ 2 * (∏' p : ℕ, twinFactor p) :=
    mul_nonneg (by norm_num) (twin_nonneg (k := k) ((show (2 : ℕ) ≤ 9 by omega).trans
      ((nine_le_sharpCutoff ε).trans hkK)))
  nlinarith [hsub, hmodel, hA, hvfloor, hRv, h8, hvNε, hvE, hv4ε, hC]

/-- Beyond the sharp cutoff the spectrum is large compared with the reciprocal of `ε`. -/
theorem epsilon_mul_le_two_pow_sharpCutoff {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : sharpCutoff ε ≤ K) :
    (1600 : ℝ) ≤ ε * ((2 ^ K : ℕ) : ℝ) ∧ 512 * ε ≤ ε * ((2 ^ K : ℕ) : ℝ) := by
  have hK9 : 9 ≤ K := (nine_le_sharpCutoff ε).trans hK
  have h512 : (512 : ℕ) ≤ 2 ^ K := by
    calc
      512 = 2 ^ 9 := by norm_num
      _ ≤ 2 ^ K := Nat.pow_le_pow_right (by decide) hK9
  have hε2 : 512 * ε ≤ ε * ((2 ^ K : ℕ) : ℝ) := by
    refine (le_of_eq ?_).trans (mul_le_mul_of_nonneg_left
      (show ((512 : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) by exact_mod_cast h512) hε.le)
    ring
  refine ⟨?_, hε2⟩
  have hpow : ((K + 1 : ℕ) : ℝ) ≤ ((2 ^ K : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := K)))
  have hKx : (800 / ε) ^ 2 < (K : ℝ) := by
    have hK' : Nat.floor ((800 / ε) ^ 2) + 1 ≤ K := le_trans (le_max_right _ _) hK
    exact (Nat.floor_lt (by positivity)).mp (by omega)
  have heq : ε * (800 / ε) ^ 2 = 640000 / ε := by
    field_simp [hε.ne']
    ring
  by_cases hε4 : ε ≤ 400
  · calc
      (1600 : ℝ) ≤ 640000 / ε := by
        rw [le_div_iff₀ hε]
        nlinarith
      _ = ε * (800 / ε) ^ 2 := heq.symm
      _ ≤ ε * ((K + 1 : ℕ) : ℝ) := by
        have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        nlinarith [mul_lt_mul_of_pos_left hKx hε]
      _ ≤ ε * ((2 ^ K : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hpow hε.le
  · calc
      (1600 : ℝ) ≤ 512 * ε := by nlinarith
      _ ≤ ε * ((2 ^ K : ℕ) : ℝ) := hε2

/-- The arithmetic skeleton of the upper bound along powers of two. -/
theorem upper_arith (A S v C R X w N ε : ℝ) (_hv : 0 ≤ v) (_hε : 0 ≤ ε) (_hC : C ≤ 1)
    (hS : S ≤ v * (2 * C) + X + R + 8 * N * w) (hA : A ≤ S + ε / 8 * N)
    (hR : R ≤ (12 / 25 : ℝ) * (ε * v)) (hX : X ≤ (32 * ε / 800) * v)
    (h8 : 8 * N * w ≤ (ε / 100) * N) (hNε : ε * N ≤ 2 * (ε * v))
    (hbig : ε + 2 * C ≤ (21 / 100 : ℝ) * (ε * v)) :
    A ≤ (2 * C + ε) * (v - 1) := by
  have hNε' : (ε / 100) * N + ε / 8 * N ≤ (1 / 50 + 1 / 4) * (ε * v) := by
    have h1 : (ε / 100) * N ≤ (ε / 100) * (2 * v) := by nlinarith
    have h2 : ε / 8 * N ≤ ε / 8 * (2 * v) := by nlinarith
    nlinarith
  have hRX : X + R ≤ (32 * ε / 800) * v + (12 / 25 : ℝ) * (ε * v) := by linarith
  nlinarith

set_option maxHeartbeats 1600000 in
/-- Along powers of two the normalized coefficient is eventually at most `2C₂ + ε`. -/
theorem eventually_upper_sharp (ε : ℝ) (hε : 0 < ε) :
    ∀ T : ℕ, ∃ N m : ℕ, T ≤ N ∧ 1 ≤ N ∧ 4 * N ≤ 3 * m ∧ 2 * m ≤ 3 * N ∧ Even m ∧
      (GoldbachBa08Approx.coefficient N m (Nat.log 2 (N + 2)) ((Nat.log 2 (N + 2)) ^ 3)).re ≤
        (2 * (∏' p : ℕ, twinFactor p) + ε) * (2 * (N : ℝ) - (m : ℝ)) := by
  classical
  obtain ⟨T₀, hT₀⟩ := sharp_inputs (ε / 8) (by positivity)
  intro T₀'
  obtain ⟨T, hTdef⟩ : ∃ T, T = max T₀' T₀ := ⟨_, rfl⟩
  have hT₀T : T₀ ≤ T := by rw [hTdef]; exact le_max_right _ _
  obtain ⟨K, hKdef⟩ : ∃ K, K = sharpCutoff ε := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a, a = K + T + 3 := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N, N = (2 ^ (a + 1) + 2) / 3 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = 2 ^ a := ⟨_, rfl⟩
  have hPa : 2 ^ (a + 1) = 2 * P := by
    rw [hPdef]
    exact Nat.pow_succ' (m := 2) (n := a)
  have hdiv : 3 * N + (2 ^ (a + 1) + 2) % 3 = 2 * P + 2 := by
    rw [hNdef, Nat.div_add_mod, Nat.pow_succ', hPdef]
  have hmod : (2 ^ (a + 1) + 2) % 3 < 3 := Nat.mod_lt _ (by decide)
  have h8a : 8 ≤ P := by
    rw [hPdef]
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) (by rw [hadef]; omega)
  have hpowpos : 1 ≤ 2 * P := by omega
  have hpowT : 2 ^ (T + 3) ≤ 2 * P := by
    rw [← hPa]
    exact Nat.pow_le_pow_right (by decide) (by rw [hadef]; omega)
  have hpowTe : 2 ^ (T + 3) = 8 * 2 ^ T := by
    rw [Nat.pow_add]
    norm_num
    ring
  have hlt : T < 2 ^ T := Nat.lt_two_pow_self (n := T)
  have hpowK : 2 ^ (K + 2) ≤ 2 * P := by
    rw [← hPa]
    exact Nat.pow_le_pow_right (by decide) (by rw [hadef]; omega)
  have hpowKe : 2 ^ (K + 2) = 4 * 2 ^ K := by
    rw [Nat.pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num]
    ring
  have hTN : T ≤ N := by
    have h1 : 8 * 2 ^ T ≤ 2 * P := by rw [← hpowTe]; exact hpowT
    omega
  have h1N : 1 ≤ N := by omega
  have h4N : 4 * N ≤ 3 * P := by omega
  have h2P : 2 * P ≤ 3 * N := by omega
  have hT₀'T : T₀' ≤ T := by rw [hTdef]; exact le_max_left _ _
  refine ⟨N, P, hT₀'T.trans hTN, h1N, h4N, h2P, ?_, ?_⟩
  · rw [hPdef]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 (by rw [hadef]; omega))
  · -- the inequality
    obtain ⟨k, hkdef⟩ : ∃ k, k = Nat.log 2 (N + 2) := ⟨_, rfl⟩
    rw [← hkdef]
    have hNK : 2 ^ K ≤ N := by
      have h1 : 4 * 2 ^ K ≤ 2 * P := by rw [← hpowKe]; exact hpowK
      omega
    have hgeom := hT₀ N (by
      have h1 : 8 * 2 ^ T ≤ 2 * P := by rw [← hpowTe]; exact hpowT
      have hT : T₀ ≤ T := by rw [hTdef]; exact le_max_right _ _
      omega)
    rw [← hkdef] at hgeom
    obtain ⟨hk1, hkc, hsep, happ⟩ := hgeom
    have hkK : K ≤ k := by
      rw [hkdef]
      exact Nat.le_log_of_pow_le (by decide) (hNK.trans (Nat.le_add_right N 2))
    have ha : 0 < a := by rw [hadef]; omega
    have hk9 : 9 ≤ k := by
      have hK9 : 9 ≤ K := by rw [hKdef]; exact nine_le_sharpCutoff ε
      exact hK9.trans hkK
    have hwidth : 2 * k ^ 3 ≤ N := by
      have hk3 : 1 ≤ k ^ 3 := Nat.one_le_pow 3 k (by omega)
      calc
        2 * k ^ 3 = 2 * k ^ 3 * 1 := by ring
        _ ≤ 2 * k ^ 3 * k ^ 3 := Nat.mul_le_mul_left _ hk3
        _ = 2 * (k ^ 3) ^ 2 := by rw [Nat.pow_two]; ring
        _ ≤ N := le_of_lt hsep
    have hsub : ((2 * N - P : ℕ) : ℝ) = 2 * (N : ℝ) - ((P : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hvN : (N : ℝ) ≤ 2 * (((2 * N - P : ℕ) : ℝ) + 1) := by
      have hv' : N ≤ 2 * (2 * N - P + 1) := by omega
      have hv'' : ((2 * N - P + 1 : ℕ) : ℝ) = ((2 * N - P : ℕ) : ℝ) + 1 := by push_cast; ring
      have h : ((N : ℕ) : ℝ) ≤ 2 * (((2 * N - P + 1 : ℕ) : ℝ)) := by exact_mod_cast hv'
      rw [hv''] at h
      exact h
    have hNpos : (0 : ℝ) < (N : ℝ) := by
      have : 0 < N := by omega
      exact_mod_cast this
    have hv0 : (0 : ℝ) ≤ ((2 * N - P : ℕ) : ℝ) + 1 := by linarith
    have hklog : ((2 ^ k : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      have h : (2 ^ k : ℕ) ≤ N + 2 := by
        rw [hkdef]
        exact Nat.pow_log_le_self (x := N + 2) 2 (by omega)
      have hR : ((2 ^ k : ℕ) : ℝ) ≤ (N : ℝ) + 2 := by exact_mod_cast h
      have hN2 : (2 : ℝ) ≤ (N : ℝ) := by
        have : 2 ≤ N := by omega
        exact_mod_cast this
      linarith
    have hKK : sharpCutoff ε ≤ K := by rw [hKdef]
    have hεK := epsilon_mul_le_two_pow_sharpCutoff hε ((hKK.trans hkK))
    obtain ⟨hεN1, hεN2⟩ := hεK
    have hεN1' : (800 : ℝ) ≤ ε * (N : ℝ) := by
      have h := hεN1.trans (mul_le_mul_of_nonneg_left hklog hε.le)
      nlinarith
    have hεN2' : (256 : ℝ) * ε ≤ ε * (N : ℝ) := by
      have h := hεN2.trans (mul_le_mul_of_nonneg_left hklog hε.le)
      nlinarith
    have hw := one_div_sqrt_le hε (hKK.trans hkK)
    have hkR : (0 : ℝ) < Real.sqrt ((k : ℝ)) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
    have hkR1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have h32 : (1 : ℝ) / (k : ℝ) ≤ 1 / Real.sqrt ((k : ℝ)) := by
      apply one_div_le_one_div_of_le hkR
      rw [Real.sqrt_le_iff]
      exact ⟨by positivity, by nlinarith [sq_nonneg ((k : ℝ) - 1)]⟩
    have hNm : N ≤ P := by omega
    have hm2 : P ≤ 2 * N := by omega
    have hmodel := (model_bounds N k P hk1 hwidth hNm hm2).2
    rw [div_eq_mul_one_div] at hmodel
    have hupper : (∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q P).re) ≤
        (2 * (∏' p : ℕ, twinFactor p)) * (1 + 16 * (1 / (k : ℝ))) +
          (128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ))) := by
      have h := floor_upper_sharp a k ha hk9
      rw [div_eq_mul_one_div] at h
      rw [hPdef]
      convert h using 1 <;> ring_nf
    have hs3 : 1 + Real.sqrt 2 ≤ (3 : ℝ) := by
      have hs2 : Real.sqrt 2 ≤ 2 := by
        rw [Real.sqrt_le_iff]
        norm_num
      linarith
    have hC0 : (0 : ℝ) ≤ 2 * (∏' p : ℕ, twinFactor p) :=
      mul_nonneg (by norm_num) (twin_nonneg (k := k) (by omega))
    have hC1 : (2 * (∏' p : ℕ, twinFactor p)) ≤ 2 := by linarith [twin_le_one]
    have hR : (128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ))) ≤ (12 / 25 : ℝ) * ε := by
      calc
        (128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ))) ≤ (384 : ℝ) * (1 / Real.sqrt ((k : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ 384 * (ε / 800) := mul_le_mul_of_nonneg_left hw (by norm_num)
        _ = (12 / 25 : ℝ) * ε := by ring
    have h16 : ((2 * (∏' p : ℕ, twinFactor p)) * (16 * (1 / (k : ℝ)))) ≤ 32 * (ε / 800) := by
      have h1 : (16 : ℝ) * (1 / (k : ℝ)) ≤ 16 * (ε / 800) :=
        (mul_le_mul_of_nonneg_left h32 (show (0 : ℝ) ≤ 16 by norm_num)).trans
          (mul_le_mul_of_nonneg_left hw (show (0 : ℝ) ≤ 16 by norm_num))
      calc
        ((2 * (∏' p : ℕ, twinFactor p)) * (16 * (1 / (k : ℝ)))) ≤
            (2 * (∏' p : ℕ, twinFactor p)) * (16 * (ε / 800)) :=
          mul_le_mul_of_nonneg_left h1 hC0
        _ ≤ 2 * (16 * (ε / 800)) := mul_le_mul_of_nonneg_right hC1 (by positivity)
        _ = 32 * (ε / 800) := by ring
    have hA : (GoldbachBa08Approx.coefficient N P k (k ^ 3)).re ≤
        (GoldbachBa08Kernel.complexModel N k P ((k : ℝ) ^ 3)).re + ε / 8 * (N : ℝ) := by
      have heq : GoldbachBa08Approx.scaledModel N P k (k ^ 3) =
        GoldbachBa08Kernel.complexModel N k P ((k : ℝ) ^ 3) := by
        simp only [GoldbachBa08Approx.scaledModel, GoldbachBa08Kernel.complexModel,
          GoldbachBlockGeometry.width, Nat.cast_pow]
      have h := Complex.abs_re_le_norm (GoldbachBa08Approx.coefficient N P k (k ^ 3) -
        GoldbachBa08Approx.scaledModel N P k (k ^ 3))
      rw [Complex.sub_re] at h
      obtain ⟨h1, h2⟩ := abs_le.mp (h.trans (happ P))
      rw [heq] at h2
      linarith
    have hvU : (((2 * N - P : ℕ) : ℝ) + 1) *
        (∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q P).re) ≤
      (((2 * N - P : ℕ) : ℝ) + 1) * (2 * (∏' p : ℕ, twinFactor p)) +
        ((((2 * N - P : ℕ) : ℝ) + 1) * ((2 * (∏' p : ℕ, twinFactor p)) * (16 * (1 / (k : ℝ)))) +
          (((2 * N - P : ℕ) : ℝ) + 1) * ((128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ))))) := by
      have h := mul_le_mul_of_nonneg_left hupper hv0
      calc
        _ ≤ _ := h
        _ = _ := by ring
    have hA : (GoldbachBa08Approx.coefficient N P k (k ^ 3)).re ≤
        (GoldbachBa08Kernel.complexModel N k P ((k : ℝ) ^ 3)).re + ε / 8 * (N : ℝ) := by
      have heq : GoldbachBa08Approx.scaledModel N P k (k ^ 3) =
        GoldbachBa08Kernel.complexModel N k P ((k : ℝ) ^ 3) := by
        simp only [GoldbachBa08Approx.scaledModel, GoldbachBa08Kernel.complexModel,
          GoldbachBlockGeometry.width, Nat.cast_pow]
      have h := Complex.abs_re_le_norm (GoldbachBa08Approx.coefficient N P k (k ^ 3) -
        GoldbachBa08Approx.scaledModel N P k (k ^ 3))
      rw [Complex.sub_re] at h
      obtain ⟨h1, h2⟩ := abs_le.mp (h.trans (happ P))
      rw [heq] at h2
      linarith
    have hvR : ((((2 * N - P : ℕ) : ℝ) + 1) * ((128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ))))) ≤
        (12 / 25 : ℝ) * (ε * (((2 * N - P : ℕ) : ℝ) + 1)) := by
      have h := mul_le_mul_of_nonneg_left hR hv0
      nlinarith
    have hv16 : ((((2 * N - P : ℕ) : ℝ) + 1) *
        ((2 * (∏' p : ℕ, twinFactor p)) * (16 * (1 / (k : ℝ))))) ≤ (32 * ε / 800) * (((2 * N - P : ℕ) : ℝ) + 1) := by
      have h := mul_le_mul_of_nonneg_left h16 hv0
      nlinarith
    have h8 : 8 * (N : ℝ) * (1 / Real.sqrt ((k : ℝ))) ≤ (ε / 100) * (N : ℝ) := by
      calc
        8 * (N : ℝ) * (1 / Real.sqrt ((k : ℝ))) ≤ 8 * (N : ℝ) * (ε / 800) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
        _ = (ε / 100) * (N : ℝ) := by ring
    have hNε : ε * (N : ℝ) ≤ 2 * (ε * (((2 * N - P : ℕ) : ℝ) + 1)) := by
      have h := mul_le_mul_of_nonneg_right hvN hε.le
      nlinarith
    have hεv : (21 / 100 : ℝ) * (ε * (((2 * N - P : ℕ) : ℝ) + 1)) ≥ (105 / 1000 : ℝ) * (ε * (N : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hvN hε.le
      nlinarith
    have hεv1 : (105 / 1000 : ℝ) * (ε * (N : ℝ)) ≥ (105 / 1000 : ℝ) * 800 :=
      mul_le_mul_of_nonneg_left hεN1' (by norm_num)
    have hεv2 : (105 / 1000 : ℝ) * (256 * ε) ≤ (105 / 1000 : ℝ) * (ε * (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hεN2' (by norm_num)
    have hbig : ε + 2 * (∏' p : ℕ, twinFactor p) ≤
        (21 / 100 : ℝ) * (ε * (((2 * N - P : ℕ) : ℝ) + 1)) := by
      have hC1 : (∏' p : ℕ, twinFactor p) ≤ 1 := twin_le_one
      linarith
    have hS : (GoldbachBa08Kernel.complexModel N k P ((k : ℝ) ^ 3)).re ≤
        (((2 * N - P : ℕ) : ℝ) + 1) * (2 * (∏' p : ℕ, twinFactor p)) +
        (((2 * N - P : ℕ) : ℝ) + 1) * ((2 * (∏' p : ℕ, twinFactor p)) * (16 * (1 / (k : ℝ)))) +
        (((2 * N - P : ℕ) : ℝ) + 1) * ((128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ)))) +
        8 * (N : ℝ) * (1 / Real.sqrt ((k : ℝ))) := by
      linarith [hmodel, hvU]
    have hfinal := upper_arith
      ((GoldbachBa08Approx.coefficient N P k (k ^ 3)).re)
      ((GoldbachBa08Kernel.complexModel N k P ((k : ℝ) ^ 3)).re)
      (((2 * N - P : ℕ) : ℝ) + 1) (∏' p : ℕ, twinFactor p)
      ((((2 * N - P : ℕ) : ℝ) + 1) * ((128 * (1 + Real.sqrt 2)) * (1 / Real.sqrt ((k : ℝ)))))
      ((((2 * N - P : ℕ) : ℝ) + 1) * ((2 * (∏' p : ℕ, twinFactor p)) * (16 * (1 / (k : ℝ)))))
      (1 / Real.sqrt ((k : ℝ))) (N : ℝ) ε hv0 hε.le twin_le_one hS hA hvR hv16 h8 hNε hbig
    rw [← hsub]
    convert hfinal using 1 <;> ring_nf
/-- The twin-prime constant in the form of the frozen statement. -/
theorem twin_prod_eq : (∏' p : ℕ, twinFactor p) =
    ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1 :=
  tprod_congr twinFactor_eq

end
end GoldbachSharpReflected

open Finset Filter MeasureTheory

theorem Conjectures.Goldbach.ReflectedMajorSharpFloor :
    (by
  classical
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
  exact ∀ ε : ℝ, 0 < ε →
    (∃ T : ℕ, ∀ N m : ℕ, T ≤ N → band N m → (2*C₂-ε)*(2*(N : ℝ)-(m : ℝ)) ≤ A N m) ∧
    (∀ T : ℕ, ∃ N m : ℕ, T ≤ N ∧ 1 ≤ N ∧ band N m ∧ A N m ≤ (2*C₂+ε)*(2*(N : ℝ)-(m : ℝ)))) := by
  classical
  dsimp only
  intro ε hε
  constructor
  · obtain ⟨T, hT⟩ := GoldbachSharpReflected.eventually_lower_sharp ε hε
    refine ⟨T, fun N m hN hE => ?_⟩
    have h := hT N m hN hE.1 hE.2.1 hE.2.2
    rw [GoldbachSharpReflected.twin_prod_eq] at h
    simpa only [GoldbachBa08Approx.coefficient, GoldbachBa08Approx.arcs,
      Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachBlockGeometry.width,
      GoldbachBa08Approx.primeSum_eq,
      Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc.phase] using h
  · intro T
    obtain ⟨N, m, hN, h1, h4, h2, hE, hle⟩ := GoldbachSharpReflected.eventually_upper_sharp ε hε T
    refine ⟨N, m, hN, h1, ⟨h4, h2, hE⟩, ?_⟩
    rw [GoldbachSharpReflected.twin_prod_eq] at hle
    simpa only [GoldbachBa08Approx.coefficient, GoldbachBa08Approx.arcs,
      Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachBlockGeometry.width,
      GoldbachBa08Approx.primeSum_eq,
      Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.GoldbachMajorArc.phase] using hle
