import Mathlib
import Conjectures.Cuts.Taskba08eb3c3998330911d98843

/-!
Sharp asymptotic constant for the reflected major arcs.

The analytic approximation and reciprocal-square kernel tail use the verified
module from https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/4198 .
The squarefree reindexing and signed-subset induction adapt the arithmetic
arguments in EstermannAlmostAllPolylog, introduced in PR 3615 (Apache-2.0).
The new uniform truncation argument uses the absolute summability of weights
indexed by finite sets of odd primes.  Positive local factors may be discarded;
the two branches at the prime 2 give the sharp lower constant.  Powers of two
provide matching upper witnesses at arbitrarily large scales.
-/


open Finset Filter
open scoped BigOperators Topology

namespace SharpArithmetic
noncomputable section

open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open GoldbachMajorArc

def atom (p : ℕ) : ℝ :=
  if p.Prime ∧ 2 < p then 1 / ((p : ℝ) - 1)^2 else 0

def C₂ : ℝ := ∏' p : ℕ, if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ)-1)^2 else 1

def mass (s : Finset ℕ) : ℝ := ∏ p ∈ s, atom p

def signed (s : Finset ℕ) : ℝ := ∏ p ∈ s, -atom p

def cutSum (s : Finset ℕ) (K d : ℕ) : ℝ :=
  ∑ t ∈ s.powerset, signed t * (if d * ∏ p ∈ t, p ≤ K then 1 else 0)

lemma atom_nonneg (p : ℕ) : 0 ≤ atom p := by
  unfold atom
  split_ifs <;> positivity

lemma atom_le_one (p : ℕ) : atom p ≤ 1 := by
  unfold atom
  split_ifs with hp
  · have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp.2
    have hsq : 1 ≤ ((p : ℝ)-1)^2 := by nlinarith
    exact (div_le_one (by positivity)).2 hsq
  · norm_num

lemma mass_nonneg (s : Finset ℕ) : 0 ≤ mass s :=
  prod_nonneg fun p _ => atom_nonneg p

lemma abs_signed (s : Finset ℕ) : |signed s| = mass s := by
  simp only [signed, mass, abs_prod, abs_neg, abs_of_nonneg (atom_nonneg _)]

/-- A uniform bound on the finite Euler products implies absolute summability
of all squarefree subset weights. -/
lemma summable_mass_of_bound (hbound : ∀ s : Finset ℕ, ∏ p ∈ s, (1 + atom p) ≤ (5/3 : ℝ)) :
    Summable mass := by
  apply summable_of_sum_le mass_nonneg
  intro T
  calc
    ∑ s ∈ T, mass s ≤ ∑ s ∈ (T.biUnion id).powerset, mass s := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro s hs
        exact mem_powerset.mpr (subset_biUnion_of_mem id hs)
      · intro s _ _; exact mass_nonneg s
    _ = ∏ p ∈ T.biUnion id, (1 + atom p) := by
      exact (prod_one_add _).symm
    _ ≤ 5/3 := hbound _

lemma summable_signed (hs : Summable mass) : Summable signed := by
  apply hs.of_norm_bounded
  intro s
  rw [Real.norm_eq_abs, abs_signed]

lemma C₂_eq_tsum (hs : Summable mass) : C₂ = ∑' s : Finset ℕ, signed s := by
  have h := tprod_one_add (summable_signed hs)
  change (∏' p : ℕ, if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ)-1)^2 else 1) = _
  change _ = ∑' s : Finset ℕ, ∏ p ∈ s, -atom p
  rw [← h]
  apply tprod_congr
  intro p
  simp only [atom]
  split_ifs <;> ring

lemma hasProd_factor (hs : Summable mass) : HasProd (fun p => 1 - atom p) C₂ := by
  rw [C₂_eq_tsum hs]
  convert hasProd_one_add_of_hasSum_prod (summable_signed hs).hasSum using 1 <;>
    simp only [sub_eq_add_neg, signed]

lemma C₂_nonneg (hs : Summable mass) : 0 ≤ C₂ := by
  apply ge_of_tendsto (hasProd_factor hs)
  exact Filter.Eventually.of_forall fun s => prod_nonneg fun p _ => sub_nonneg.mpr (atom_le_one p)

lemma C₂_le_finite (hs : Summable mass) (s : Finset ℕ) : C₂ ≤ ∏ p ∈ s, (1 - atom p) := by
  apply le_of_tendsto (hasProd_factor hs)
  filter_upwards [eventually_ge_atTop s] with t ht
  exact prod_le_prod_of_subset_of_le_one₀ ht (fun p _ => sub_nonneg.mpr (atom_le_one p))
    (fun p _ _ => sub_le_self _ (atom_nonneg p))

/-- Uniform truncation in both the finite prime set and in the target's excluded
prime set. The shared absolutely summable subset weights supply the tail. -/
lemma uniform_cut_error (hs : Summable mass) (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ s : Finset ℕ, ∀ d : ℕ, d ≤ 2 →
      |cutSum s K d - ∏ p ∈ s, (1 - atom p)| < ε := by
  obtain ⟨T, hT⟩ := summable_iff_vanishing_norm.mp hs ε hε
  refine ⟨2 * T.sup (fun t => ∏ p ∈ t, p), ?_⟩
  intro K hK s d hd
  let U := s.powerset.filter (fun t => K < d * ∏ p ∈ t, p)
  have hdis : Disjoint U T := by
    apply disjoint_left.mpr
    intro t ht hmem
    have hsup := le_sup (f := fun t : Finset ℕ => ∏ p ∈ t, p) hmem
    have hle : d * ∏ p ∈ t, p ≤ 2 * T.sup (fun t => ∏ p ∈ t, p) :=
      Nat.mul_le_mul hd hsup
    exact (not_lt_of_ge (hle.trans hK)) (mem_filter.mp ht).2
  have htail := hT U hdis
  have heq : cutSum s K d - ∏ p ∈ s, (1 - atom p) = -(∑ t ∈ U, signed t) := by
    rw [show (∏ p ∈ s, (1 - atom p)) = ∑ t ∈ s.powerset, signed t by
      simpa only [signed, sub_eq_add_neg] using (prod_one_add (f := fun p => -atom p) s)]
    rw [cutSum, ← sum_sub_distrib, ← sum_neg_distrib]
    rw [show (∑ t ∈ U, -signed t) = ∑ t ∈ s.powerset,
        if K < d * ∏ p ∈ t, p then -signed t else 0 by
      exact sum_filter _ _]
    apply sum_congr rfl
    intro t _
    by_cases h : d * ∏ p ∈ t, p ≤ K
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_ge h]
  rw [heq, abs_neg]
  apply lt_of_le_of_lt (abs_sum_le_sum_abs _ _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sum_nonneg (fun t _ => mass_nonneg t)),
    abs_signed] using htail

lemma euler_bound (s : Finset ℕ) : ∏ p ∈ s, (1 + atom p) ≤ (5/3 : ℝ) := by
  have h := product_bad_factors (s := s.filter (fun p => p.Prime ∧ 2 < p))
    (fun p hp => (mem_filter.mp hp).2)
  convert h using 1
  rw [prod_filter]
  apply prod_congr rfl
  intro p _
  simp only [atom, badFactor]
  split_ifs <;> simp

lemma mass_summable : Summable mass := summable_mass_of_bound euler_bound

lemma constant_nonneg : 0 ≤ C₂ := C₂_nonneg mass_summable

def singularReal (K m : ℕ) : ℝ := ∑ q ∈ Icc 1 K, (coefficient q m).re

def primes (K : ℕ) : Finset ℕ := (range (K+1)).filter Nat.Prime

def badPrimes (K m : ℕ) : Finset ℕ := (primes K).filter (fun p => ¬ p ∣ m)

def W (K : ℕ) (q : ℕ) : ℝ := if q ≤ K then 1 else 0

lemma W_nonneg (K q : ℕ) : 0 ≤ W K q := by unfold W; split_ifs <;> norm_num
lemma W_mono (K i j : ℕ) (_hi : 0 < i) (hij : i ≤ j) : W K j ≤ W K i := by
  unfold W
  split_ifs <;> norm_num <;> omega

theorem coefficient_not_squarefree {q : ℕ} (n : ℕ) (hq : 0 < q)
    (hs : ¬ Squarefree q) : coefficient q n = 0 := by
  induction q using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact (hs squarefree_one).elim
  | prime_pow p k hp hk =>
    cases k with
    | zero => omega
    | succ k =>
      cases k with
      | zero => exact (hs (by simpa using hp.squarefree)).elim
      | succ j => exact coefficient_higher_power hp j n
  | coprime a b ha hb hab ia ib =>
    rw [coefficient_mul (by omega) (by omega) hab]
    by_cases h : Squarefree a
    · rw [ib (by omega) (fun h' => hs ((Nat.squarefree_mul hab).mpr ⟨h,h'⟩)), mul_zero]
    · rw [ia (by omega) h, zero_mul]

theorem coefficient_prime_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    coefficient (∏ p ∈ s, p) n = ((∏ p ∈ s, localCoefficient p n : ℝ) : ℂ) := by
  induction s using Finset.induction_on with
  | empty => simp [coefficient_one]
  | @insert p s hp ih =>
    have hprime := hs p (mem_insert_self _ _)
    have hs' : ∀ r ∈ s, r.Prime := fun r hr => hs r (mem_insert_of_mem hr)
    have hcop : p.Coprime (∏ r ∈ s, r) := Nat.coprime_prod_right_iff.mpr fun r hr =>
      (Nat.coprime_primes hprime (hs' r hr)).mpr fun he => hp (he ▸ hr)
    rw [prod_insert hp, prod_insert hp, coefficient_mul hprime.pos (prod_pos fun r hr => (hs' r hr).pos) hcop,
      coefficient_prime hprime, ih hs', Complex.ofReal_mul]

theorem reindex_denominators (Q n : ℕ) (W : ℕ → ℝ) (hcut : ∀ q, Q < q → W q = 0) :
    (∑ q ∈ Icc 1 Q, (coefficient q n).re * W q) =
    ∑ t ∈ ((range (Q + 1)).filter Nat.Prime).powerset, (∏ p ∈ t, localCoefficient p n) * W (∏ p ∈ t, p) := by
  classical
  let P := (range (Q + 1)).filter Nat.Prime
  have hprime {t : Finset ℕ} (ht : t ∈ P.powerset) : ∀ p ∈ t, p.Prime :=
    fun p hp => (mem_filter.mp (mem_powerset.mp ht hp)).2
  symm
  apply sum_bij_ne_zero (fun t _ _ => ∏ p ∈ t, p)
  · intro t ht hnz
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (hprime ht p hp).pos, le_of_not_gt fun h => hnz (by rw [hcut _ h, mul_zero])⟩
  · intro s hs _ t ht _ he
    exact (Nat.primeFactors_prod (hprime hs)).symm.trans ((congrArg Nat.primeFactors he).trans (Nat.primeFactors_prod (hprime ht)))
  · intro q hq hnz
    have hq' := mem_Icc.mp hq
    have hsq : Squarefree q := by
      by_contra hh
      exact hnz (by rw [coefficient_not_squarefree n hq'.1 hh]; simp)
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    have hsub : q.primeFactors ∈ P.powerset := by
      apply mem_powerset.mpr
      intro p hp
      exact mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans hq'.2)),
        Nat.prime_of_mem_primeFactors hp⟩
    have hc := coefficient_prime_product n q.primeFactors (hprime hsub)
    rw [hprod] at hc
    exact ⟨q.primeFactors, hsub, fun hh => hnz (by rw [hprod] at hh; simpa only [hc, Complex.ofReal_re] using hh), hprod⟩
  · intro t ht _
    rw [coefficient_prime_product n t (hprime ht), Complex.ofReal_re]

theorem signed_powerset_floor (n : ℕ) (W : ℕ → ℝ) (hnonneg : ∀ k, 0 ≤ W k)
    (hmono : ∀ i j, 0 < i → i ≤ j → W j ≤ W i)
    (B G : Finset ℕ) (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n)
    (hG : ∀ p ∈ G, p.Prime ∧ p ∣ n) (d : ℕ) (hd : 0 < d) :
    W d / 3 ≤ ∑ t ∈ (G ∪ B).powerset,
      (∏ p ∈ t, localCoefficient p n) * W (d * ∏ p ∈ t, p) := by
  classical
  induction G using Finset.induction_on generalizing d with
  | empty =>
    rw [empty_union]
    apply (negative_factors_lower (fun p hp => (hB p hp).1) W hnonneg hmono hd).trans
    apply le_of_eq
    apply sum_congr rfl
    intro t ht
    congr 1
    apply prod_congr rfl
    intro p hp
    simp [localCoefficient, badFactor, (hB p (mem_powerset.mp ht hp)).2]
  | @insert p G hp ih =>
    have hp' := hG p (mem_insert_self _ _)
    have hG' : ∀ r ∈ G, r.Prime ∧ r ∣ n := fun r hr => hG _ (mem_insert_of_mem hr)
    have hpB : p ∉ B := fun h => (hB p h).2 hp'.2
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hsign : 0 ≤ localCoefficient p n := by
      have h : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
      simp [localCoefficient, hp'.2, le_of_lt h]
    rw [insert_union, sum_powerset_insert hpGB]
    have hsecond : 0 ≤ ∑ t ∈ (G ∪ B).powerset, (∏ r ∈ insert p t, localCoefficient r n) *
        W (d * ∏ r ∈ insert p t, r) := by
      calc
        0 ≤ localCoefficient p n * (∑ t ∈ (G ∪ B).powerset, (∏ r ∈ t, localCoefficient r n) *
            W (d * p * ∏ r ∈ t, r)) :=
          mul_nonneg hsign ((div_nonneg (hnonneg _) (by norm_num)).trans (ih hG' _ (Nat.mul_pos hd hp'.1.pos)))
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro t ht
          have hpt : p ∉ t := fun h => hpGB (mem_powerset.mp ht h)
          rw [prod_insert hpt, prod_insert hpt, ← mul_assoc d, mul_assoc (localCoefficient p n)]
    linarith [ih hG' d hd]

/-- Inserting positive local factors can only increase the truncated series:
each inserted branch is nonnegative by the existing signed Euler bound. -/
theorem discard_good (n K : ℕ) (B G : Finset ℕ)
    (hB : ∀ p ∈ B, (p.Prime ∧ 2 < p) ∧ ¬ p ∣ n)
    (hG : ∀ p ∈ G, p.Prime ∧ p ∣ n) (d : ℕ) (hd : 0 < d) :
    cutSum B K d ≤ ∑ t ∈ (G ∪ B).powerset,
      (∏ p ∈ t, localCoefficient p n) * W K (d * ∏ p ∈ t, p) := by
  classical
  induction G using Finset.induction_on generalizing d with
  | empty =>
    rw [empty_union]
    apply le_of_eq
    apply sum_congr rfl
    intro t ht
    congr 1
    apply prod_congr rfl
    intro p hp
    have h := hB p (mem_powerset.mp ht hp)
    simp [signed, atom, localCoefficient, h.1, h.2]
  | @insert p G hp ih =>
    have hp' := hG p (mem_insert_self _ _)
    have hG' : ∀ r ∈ G, r.Prime ∧ r ∣ n := fun r hr => hG _ (mem_insert_of_mem hr)
    have hpB : p ∉ B := fun h => (hB p h).2 hp'.2
    have hpGB : p ∉ G ∪ B := by simp [hp, hpB]
    have hsign : 0 ≤ localCoefficient p n := by
      have h : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
      simp [localCoefficient, hp'.2, le_of_lt h]
    rw [insert_union, sum_powerset_insert hpGB]
    have hfloor := signed_powerset_floor n (W K) (W_nonneg K) (W_mono K)
      B G hB hG' (d*p) (Nat.mul_pos hd hp'.1.pos)
    have hsecond : 0 ≤ ∑ t ∈ (G ∪ B).powerset, (∏ r ∈ insert p t, localCoefficient r n) *
        W K (d * ∏ r ∈ insert p t, r) := by
      calc
        0 ≤ localCoefficient p n * (∑ t ∈ (G ∪ B).powerset, (∏ r ∈ t, localCoefficient r n) *
            W K (d * p * ∏ r ∈ t, r)) :=
          mul_nonneg hsign ((div_nonneg (W_nonneg K _) (by norm_num)).trans hfloor)
        _ = _ := by
          rw [mul_sum]
          apply sum_congr rfl
          intro t ht
          have hpt : p ∉ t := fun h => hpGB (mem_powerset.mp ht h)
          rw [prod_insert hpt, prod_insert hpt, ← mul_assoc d, mul_assoc (localCoefficient p n)]
    exact (ih hG' d hd).trans (le_add_of_nonneg_right hsecond)

lemma singular_as_powerset (K m : ℕ) :
    singularReal K m = ∑ t ∈ (primes K).powerset,
      (∏ p ∈ t, localCoefficient p m) * W K (∏ p ∈ t, p) := by
  unfold primes
  rw [← reindex_denominators K m (W K) (fun q hq => by simp [W, Nat.not_le.mpr hq])]
  apply sum_congr rfl
  intro q hq
  simp [W, (mem_Icc.mp hq).2]

lemma badPrimes_spec {K m p : ℕ} (hm : Even m) (hp : p ∈ badPrimes K m) :
    (p.Prime ∧ 2 < p) ∧ ¬ p ∣ m := by
  have hn := (mem_filter.mp hp).2
  have hpr := (mem_filter.mp (mem_filter.mp hp).1).2
  have hne : p ≠ 2 := fun e => hn (e ▸ even_iff_two_dvd.mp hm)
  exact ⟨⟨hpr, lt_of_le_of_ne hpr.two_le (Ne.symm hne)⟩, hn⟩

lemma split_two {K m : ℕ} (hK : 2 ≤ K) (hm : Even m) :
    singularReal K m =
      (∑ t ∈ ((primes K).erase 2).powerset,
        (∏ p ∈ t, localCoefficient p m) * W K (∏ p ∈ t, p)) +
      (∑ t ∈ ((primes K).erase 2).powerset,
        (∏ p ∈ t, localCoefficient p m) * W K (2 * ∏ p ∈ t, p)) := by
  have htwo : 2 ∈ primes K := by simp [primes, Nat.prime_two, hK]
  conv_lhs => rw [singular_as_powerset, ← insert_erase htwo, sum_powerset_insert (notMem_erase 2 _)]
  congr 1
  apply sum_congr rfl
  intro t ht
  have hnot : 2 ∉ t := fun h => (mem_erase.mp (mem_powerset.mp ht h)).1 rfl
  rw [prod_insert hnot, prod_insert hnot]
  have hc : localCoefficient 2 m = 1 := by norm_num [localCoefficient, even_iff_two_dvd.mp hm]
  rw [hc, one_mul]

lemma lower_by_two {K m : ℕ} (hK : 2 ≤ K) (hm : Even m) :
    cutSum (badPrimes K m) K 1 + cutSum (badPrimes K m) K 2 ≤ singularReal K m := by
  let G := ((primes K).filter (fun p => p ∣ m)).erase 2
  have hGB : G ∪ badPrimes K m = (primes K).erase 2 := by
    ext p
    have htwo : 2 ∣ m := even_iff_two_dvd.mp hm
    simp only [G, badPrimes, mem_union, mem_filter, mem_erase]
    by_cases hp : p = 2
    · subst p; simp [htwo]
    · simp [hp]; tauto
  have hG : ∀ p ∈ G, p.Prime ∧ p ∣ m := by
    intro p hp
    have h := (mem_filter.mp (mem_erase.mp hp).2)
    exact ⟨(mem_filter.mp h.1).2, h.2⟩
  have ha := discard_good m K (badPrimes K m) G (fun p hp => badPrimes_spec hm hp) hG 1 (by omega)
  have hb := discard_good m K (badPrimes K m) G (fun p hp => badPrimes_spec hm hp) hG 2 (by omega)
  rw [hGB] at ha hb
  simp only [one_mul] at ha
  rw [split_two hK hm]
  exact add_le_add ha hb

theorem eventually_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ m : ℕ, Even m → 2*C₂ - ε ≤ singularReal K m := by
  obtain ⟨K₀, h₀⟩ := uniform_cut_error mass_summable (ε/2) (by positivity)
  refine ⟨max K₀ 2, ?_⟩
  intro K hK m hm
  have ha := h₀ K (le_trans (le_max_left _ _) hK) (badPrimes K m) 1 (by omega)
  have hb := h₀ K (le_trans (le_max_left _ _) hK) (badPrimes K m) 2 (by omega)
  have hc := C₂_le_finite mass_summable (badPrimes K m)
  have hd := lower_by_two (le_trans (le_max_right _ _) hK) hm
  have ha' := (abs_lt.mp ha).1
  have hb' := (abs_lt.mp hb).1
  linarith

lemma badPrimes_pow_two (K j : ℕ) (hj : 0 < j) :
    badPrimes K (2^j) = (primes K).erase 2 := by
  ext p
  simp only [badPrimes, mem_filter, mem_erase]
  by_cases hP : p ∈ primes K
  · have hp : p.Prime := (mem_filter.mp hP).2
    have heq : p ∣ 2^j ↔ p = 2 := by
      constructor
      · intro h
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)
      · rintro rfl
        exact dvd_pow_self 2 (Nat.ne_of_gt hj)
    simp [hP, heq, and_comm]
  · simp [hP]

lemma pow_two_split {K j : ℕ} (hK : 2 ≤ K) (hj : 0 < j) :
    singularReal K (2^j) = cutSum ((primes K).erase 2) K 1 +
      cutSum ((primes K).erase 2) K 2 := by
  have he : Even (2^j) := even_iff_two_dvd.mpr (dvd_pow_self 2 hj.ne')
  rw [split_two hK he]
  congr 1 <;> apply sum_congr rfl <;> intro t ht
  all_goals
    have hc : (∏ p ∈ t, localCoefficient p (2^j)) = signed t := by
      apply prod_congr rfl
      intro p hp
      have hpB : p ∈ badPrimes K (2^j) := by
        rw [badPrimes_pow_two K j hj]
        exact mem_powerset.mp ht hp
      have h := badPrimes_spec he hpB
      simp [localCoefficient, atom, h.1, h.2]
    rw [hc]
    simp [W, cutSum]

lemma finite_product_eq_range (K : ℕ) :
    (∏ p ∈ (primes K).erase 2, (1-atom p)) = ∏ p ∈ range (K+1), (1-atom p) := by
  apply prod_subset
  · intro p hp
    exact (mem_filter.mp (mem_erase.mp hp).2).1
  · intro p hp hnot
    have hz : atom p = 0 := by
      unfold atom
      apply if_neg
      intro h
      exact hnot (mem_erase.mpr ⟨by omega, mem_filter.mpr ⟨hp, h.1⟩⟩)
    rw [hz, sub_zero]

lemma finite_product_tendsto :
    Tendsto (fun K => ∏ p ∈ (primes K).erase 2, (1-atom p)) atTop (𝓝 C₂) := by
  simp_rw [finite_product_eq_range]
  exact (hasProd_factor mass_summable).tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)

theorem eventually_pow_two (ε : ℝ) (hε : 0 < ε) :
    ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ j : ℕ, 0 < j →
      |singularReal K (2^j) - 2*C₂| ≤ ε := by
  obtain ⟨K₀, h₀⟩ := uniform_cut_error mass_summable (ε/4) (by positivity)
  have hp := (Metric.tendsto_atTop.mp finite_product_tendsto) (ε/4) (by positivity)
  obtain ⟨K₁, h₁⟩ := hp
  refine ⟨max 2 (max K₀ K₁), ?_⟩
  intro K hK j hj
  have hk₂ : 2 ≤ K := (le_max_left _ _).trans hK
  have hk₀ : K₀ ≤ K := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hK
  have hk₁ : K₁ ≤ K := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hK
  have ha := h₀ K hk₀ ((primes K).erase 2) 1 (by omega)
  have hb := h₀ K hk₀ ((primes K).erase 2) 2 (by omega)
  have hc := h₁ K hk₁
  rw [Real.dist_eq] at hc
  rw [pow_two_split hk₂ hj]
  have ha' := abs_lt.mp ha
  have hb' := abs_lt.mp hb
  have hc' := abs_lt.mp hc
  rw [abs_le]
  constructor <;> linarith

end
end SharpArithmetic



open Finset Filter MeasureTheory
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux

namespace SharpAnalytic
noncomputable section

abbrev cutoff (N : ℕ) := Nat.log 2 (N + 2)
abbrev AComplex (N m : ℕ) : ℂ :=
  GoldbachBa08Approx.coefficient N m (cutoff N) ((cutoff N)^3)
abbrev A (N m : ℕ) : ℝ := (AComplex N m).re
abbrev singularSum (B m : ℕ) : ℂ :=
  ∑ q ∈ Icc 1 B, GoldbachMajorArc.coefficient q m
abbrev singularReal (B m : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 B, (GoldbachMajorArc.coefficient q m).re

/-- A uniform complex error estimate; no parity hypothesis is needed. -/
theorem model_error (N B m : ℕ) (hN : 0 < N) (hB : 1 ≤ B)
    (hwidth : 2 * B^3 ≤ N) (hNm : N ≤ m) (hm : m ≤ 2*N) :
    ‖GoldbachBa08Approx.scaledModel N m B (B^3) -
      ((((2*N-m : ℕ) : ℂ)+1) * singularSum B m)‖ ≤ 8*(N:ℝ)/(B:ℝ) := by
  let v : ℂ := ((2*N-m : ℕ) : ℂ)+1
  let C (q : ℕ) : ℂ := GoldbachMajorArc.coefficient q m
  let width (q : ℕ) : ℝ := (B:ℝ)^3 / ((q:ℝ)*N)
  let I (q : ℕ) : ℂ := ∫ t in -(width q)..width q, GoldbachEstermannKernel.twisted N m t
  let cost : ℝ := 2*(B:ℝ)*N/(B:ℝ)^3
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hb : (1:ℝ) ≤ B := by exact_mod_cast hB
  have hbp : 0 < (B:ℝ) := lt_of_lt_of_le zero_lt_one hb
  have hc : 0 ≤ cost := by dsimp [cost]; positivity
  have hwidthR : 2*(B:ℝ)^3 ≤ N := by exact_mod_cast hwidth
  have tail (q : ℕ) (hq : q ∈ Icc 1 B) : ‖I q - v‖ ≤ cost := by
    obtain ⟨hq₁, hq₂⟩ := mem_Icc.mp hq
    have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq₁
    have hqB : (q:ℝ) ≤ B := by exact_mod_cast hq₂
    have hpw : 0 < width q := div_pos (pow_pos hbp _) (mul_pos (lt_of_lt_of_le zero_lt_one hqR) hn)
    have hw : width q ≤ 1/2 := by
      apply (div_le_iff₀ (mul_pos (lt_of_lt_of_le zero_lt_one hqR) hn)).mpr
      nlinarith only [hwidthR, mul_le_mul_of_nonneg_right hqR hn.le]
    have ht := GoldbachBa08Kernel.norm_twisted_tail_upper N m hpw hw hNm hm
    change ‖I q-v‖ ≤ 2/width q at ht
    refine ht.trans ?_
    calc
      2/width q = 2*(q:ℝ)*N/(B:ℝ)^3 := by
        dsimp only [width]
        rw [div_div_eq_mul_div]
        ring
      _ ≤ cost := by dsimp only [cost]; gcongr
  have hs : Real.sqrt (B:ℝ) ≤ B := by
    apply (Real.sqrt_le_left hbp.le).mpr
    nlinarith only [mul_nonneg hbp.le (sub_nonneg.mpr hb)]
  have sum_bound : (∑ q ∈ Icc 1 B, ‖C q‖) ≤ 4*(B:ℝ) :=
    (GoldbachMajorArc.sum_norm_coefficient_le_sqrt B m).trans (by gcongr)
  have heq : GoldbachBa08Approx.scaledModel N m B (B^3) -
      v * singularSum B m = ∑ q ∈ Icc 1 B, C q * (I q-v) := by
    simp only [GoldbachBa08Approx.scaledModel, GoldbachBlockGeometry.width,
      Nat.cast_pow, singularSum, mul_sum, mul_sub, sum_sub_distrib, C, I, width]
    congr 1
    apply sum_congr rfl
    intro q hq
    ring
  change ‖GoldbachBa08Approx.scaledModel N m B (B^3) - v * singularSum B m‖ ≤ _
  rw [heq]
  calc
    ‖∑ q ∈ Icc 1 B, C q * (I q-v)‖ ≤ ∑ q ∈ Icc 1 B, ‖C q * (I q-v)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ Icc 1 B, ‖C q‖*cost := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (tail q hq) (norm_nonneg _)
    _ = (∑ q ∈ Icc 1 B, ‖C q‖)*cost := (sum_mul ..).symm
    _ ≤ (4*(B:ℝ))*cost := mul_le_mul_of_nonneg_right sum_bound hc
    _ = 8*(N:ℝ)/(B:ℝ) := by dsimp [cost]; field_simp; ring

/-- The core major-arc integral equals the full triangular coefficient times
its truncated singular series, with an arbitrarily small uniform linear error. -/
theorem eventually_complex_approx {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 4*N ≤ 3*m → 2*m ≤ 3*N →
      ‖AComplex N m - ((((2*N-m : ℕ) : ℂ)+1) * singularSum (cutoff N) m)‖ ≤ ε*N := by
  obtain ⟨K, hK⟩ := exists_nat_gt (16/ε)
  have hlog : ∀ᶠ N : ℕ in atTop, K ≤ cutoff N := by
    filter_upwards [eventually_ge_atTop (2^K : ℕ)] with N hN
    exact Nat.le_log_of_pow_le (by decide) (hN.trans (Nat.le_add_right N 2))
  filter_upwards [hlog, GoldbachBa08Approx.eventually_geometry,
    GoldbachBa08Approx.eventually_approx (half_pos hε)] with N hk hg ha
  let B := cutoff N
  obtain ⟨hB, hBcube, hsep⟩ := hg
  have hN : 0 < N := by omega
  have hcube : 1 ≤ B^3 := hB.trans hBcube
  have hwidth : 2*B^3 ≤ N := by
    have hmul := Nat.mul_le_mul_left (2*B^3) hcube
    nlinarith only [hmul, hsep]
  have hb : 0 < (B:ℝ) := by
    exact_mod_cast (show 0 < B from lt_of_lt_of_le Nat.zero_lt_one hB)
  have hKB : (K:ℝ) ≤ B := by exact_mod_cast hk
  have hlarge : 16 ≤ ε*(B:ℝ) := by
    have hh : 16 < (K:ℝ)*ε := (div_lt_iff₀ hε).mp hK
    nlinarith [mul_le_mul_of_nonneg_left hKB hε.le]
  have hsmall : 8*(N:ℝ)/(B:ℝ) ≤ (ε/2)*N := by
    apply (div_le_iff₀ hb).mpr
    have hh := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ (N:ℝ) by positivity)
    nlinarith only [hh]
  intro m hl hu
  have hmodel := model_error N B m hN hB hwidth (by omega) (by omega)
  have happrox := ha m
  change ‖AComplex N m - GoldbachBa08Approx.scaledModel N m B (B^3)‖ ≤ (ε/2)*N at happrox
  calc
    ‖AComplex N m - ((((2*N-m : ℕ) : ℂ)+1) * singularSum (cutoff N) m)‖ ≤
        ‖AComplex N m - GoldbachBa08Approx.scaledModel N m B (B^3)‖ +
        ‖GoldbachBa08Approx.scaledModel N m B (B^3) -
          ((((2*N-m : ℕ) : ℂ)+1) * singularSum B m)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (ε/2)*N + (ε/2)*N := add_le_add happrox (hmodel.trans hsmall)
    _ = ε*N := by ring

/-- Real-part version of the uniform approximation. -/
theorem eventually_real_approx {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 4*N ≤ 3*m → 2*m ≤ 3*N →
      |A N m - (((2*N-m : ℕ) : ℝ)+1) * singularReal (cutoff N) m| ≤ ε*N := by
  filter_upwards [eventually_complex_approx hε] with N hN
  intro m hl hu
  have h := (Complex.abs_re_le_norm
    (AComplex N m - ((((2*N-m : ℕ) : ℂ)+1) * singularSum (cutoff N) m))).trans (hN m hl hu)
  simpa [A, singularSum, singularReal, Complex.sub_re, Complex.mul_re,
    Complex.add_re, Complex.add_im] using h

/-- Threshold form, convenient for the final frozen theorem. -/
theorem real_approx (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ m : ℕ, 4*N ≤ 3*m → 2*m ≤ 3*N →
      |A N m - (((2*N-m : ℕ) : ℝ)+1) * singularReal (cutoff N) m| ≤ ε*N :=
  Filter.eventually_atTop.mp (eventually_real_approx hε)

end
end SharpAnalytic


namespace SharpGlue

private theorem lower_algebra {a s c δ n d : ℝ}
    (hδ : 0 < δ) (hn : 0 ≤ n) (hd : n / 2 ≤ d)
    (hc : |c| + δ ≤ δ * n) (hs : c - δ ≤ s)
    (ha : |a - (d + 1) * s| ≤ δ * n) :
    (c - 8 * δ) * d ≤ a := by
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ d + 1 by linarith)
  have hab := (abs_le.mp ha).1
  have hcn := neg_abs_le c
  nlinarith

private theorem upper_algebra {a s c δ n d : ℝ}
    (hδ : 0 < δ) (hn : 0 ≤ n) (hd : n / 2 ≤ d)
    (hc : |c| + δ ≤ δ * n) (hs : s ≤ c + δ)
    (ha : |a - (d + 1) * s| ≤ δ * n) :
    a ≤ (c + 8 * δ) * d := by
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ d + 1 by linarith)
  have hab := (abs_le.mp ha).2
  have hcn := le_abs_self c
  nlinarith

/-- A uniform approximation plus sharp arithmetic estimates yields the two halves
of the frozen major-arc statement.  The upper witnesses use m=2^(j+2), N=3*2^j. -/
theorem sharp_of_inputs (A s : ℕ → ℕ → ℝ) (c : ℝ)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N m : ℕ,
      T ≤ N → 4*N ≤ 3*m → 2*m ≤ 3*N →
      |A N m - (2*(N:ℝ)-(m:ℝ)+1) * s (Nat.log 2 (N+2)) m| ≤ ε*(N:ℝ))
    (hl : ∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ m : ℕ,
      Even m → c-ε ≤ s K m)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ j : ℕ,
      0 < j → |s K (2^j)-c| ≤ ε) :
    ∀ ε : ℝ, 0 < ε →
      (∃ T : ℕ, ∀ N m : ℕ, T ≤ N →
        (4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m) →
        (c-ε)*(2*(N:ℝ)-(m:ℝ)) ≤ A N m) ∧
      (∀ T : ℕ, ∃ N m : ℕ, T ≤ N ∧ 1 ≤ N ∧
        (4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m) ∧
        A N m ≤ (c+ε)*(2*(N:ℝ)-(m:ℝ))) := by
  intro ε hε
  let δ := ε / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ8 : 8*δ = ε := by dsimp [δ]; ring
  obtain ⟨T₁,hT₁⟩ := ha δ hδ
  obtain ⟨K₁,hK₁⟩ := hl δ hδ
  obtain ⟨K₂,hK₂⟩ := hu δ hδ
  obtain ⟨M,hM⟩ := exists_nat_gt ((|c|+δ)/δ)
  have hconstant : ∀ N : ℕ, M ≤ N → |c|+δ ≤ δ*(N:ℝ) := by
    intro N hN
    have hMN : (M:ℝ) ≤ N := by exact_mod_cast hN
    have hC := (div_lt_iff₀ hδ).mp hM
    nlinarith
  let T₀ := max (max T₁ M) (max (2^K₁) (2^K₂))
  have hlog₁ : ∀ N ≥ T₀, K₁ ≤ Nat.log 2 (N+2) := by
    intro N hN
    apply Nat.le_log_of_pow_le (by decide)
    dsimp [T₀] at hN
    omega
  have hlog₂ : ∀ N ≥ T₀, K₂ ≤ Nat.log 2 (N+2) := by
    intro N hN
    apply Nat.le_log_of_pow_le (by decide)
    dsimp [T₀] at hN
    omega
  have hT : ∀ N ≥ T₀, T₁ ≤ N ∧ M ≤ N := by
    intro N hN
    dsimp [T₀] at hN
    omega
  constructor
  · refine ⟨T₀, ?_⟩
    intro N m hN hb
    have hD : (N:ℝ)/2 ≤ 2*(N:ℝ)-(m:ℝ) := by
      have hm : 2*(m:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hb.2.1
      linarith
    have h := lower_algebra hδ (Nat.cast_nonneg N) hD
      (hconstant N (hT N hN).2) (hK₁ _ (hlog₁ N hN) m hb.2.2)
      (hT₁ N m (hT N hN).1 hb.1 hb.2.1)
    simpa only [hδ8] using h
  · intro T
    let j := Nat.clog 2 (max T T₀)
    let N := 3*2^j
    let m := 2^(j+2)
    have hpow : max T T₀ ≤ 2^j := Nat.le_pow_clog (by decide) _
    have hNm : m = 4*2^j := by dsimp [m]; rw [pow_add]; ring
    have hN : T₀ ≤ N := by dsimp [N]; omega
    have hTN : T ≤ N := by dsimp [N]; omega
    have hNpos : 1 ≤ N := by
      have hp : 0 < 2^j := by positivity
      dsimp [N]
      omega
    have hb1 : 4*N ≤ 3*m := by dsimp [N]; omega
    have hb2 : 2*m ≤ 3*N := by dsimp [N]; omega
    have heven : Even m := ⟨2*2^j, by omega⟩
    have hs : s (Nat.log 2 (N+2)) m ≤ c+δ := by
      have hx := (abs_le.mp (hK₂ _ (hlog₂ N hN) (j+2) (by omega))).2
      dsimp [m]
      linarith
    have hD : (N:ℝ)/2 ≤ 2*(N:ℝ)-(m:ℝ) := by
      have hm : 2*(m:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hb2
      linarith
    have h := upper_algebra hδ (Nat.cast_nonneg N) hD
      (hconstant N (hT N hN).2) hs (hT₁ N m (hT N hN).1 hb1 hb2)
    refine ⟨N,m,hTN,hNpos,⟨hb1,hb2,heven⟩,?_⟩
    simpa only [hδ8] using h

end SharpGlue

namespace SharpAssembly
noncomputable def twinConstant : ℝ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1

theorem assemble
    (hl : ∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ m : ℕ,
      Even m → 2*twinConstant-ε ≤ SharpAnalytic.singularReal K m)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, ∀ K ≥ K₀, ∀ j : ℕ,
      0 < j → |SharpAnalytic.singularReal K (2^j)-2*twinConstant| ≤ ε) :
    by
      classical
      let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
      let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
      let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
      let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
      let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
      let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
      exact ∀ ε : ℝ, 0 < ε →
        (∃ T : ℕ, ∀ N m : ℕ, T ≤ N → band N m → (2*C₂-ε)*(2*(N : ℝ)-(m : ℝ)) ≤ A N m) ∧
        (∀ T : ℕ, ∃ N m : ℕ, T ≤ N ∧ 1 ≤ N ∧ band N m ∧ A N m ≤ (2*C₂+ε)*(2*(N : ℝ)-(m : ℝ))) := by
  have ha : ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N m : ℕ,
      T ≤ N → 4*N ≤ 3*m → 2*m ≤ 3*N →
      |SharpAnalytic.A N m - (2*(N:ℝ)-(m:ℝ)+1) *
        SharpAnalytic.singularReal (Nat.log 2 (N+2)) m| ≤ ε*(N:ℝ) := by
    intro ε hε
    obtain ⟨T,hT⟩ := SharpAnalytic.real_approx ε hε
    refine ⟨T, ?_⟩
    intro N m hN hb1 hb2
    have hm : m ≤ 2*N := by omega
    simpa only [Nat.cast_sub hm, Nat.cast_mul, Nat.cast_ofNat] using hT N hN m hb1 hb2
  have h := SharpGlue.sharp_of_inputs SharpAnalytic.A SharpAnalytic.singularReal
    (2*twinConstant) ha hl hu
  simpa only [SharpAnalytic.A, SharpAnalytic.AComplex, SharpAnalytic.cutoff,
    GoldbachBa08Approx.coefficient, GoldbachBa08Approx.arcs,
    GoldbachBlockGeometry.width, GoldbachBa08Approx.primeSum_eq,
    GoldbachMajorArc.phase, twinConstant] using h

end SharpAssembly

theorem Conjectures.Goldbach.ReflectedMajorSharpFloor :
by
  classical
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
  exact ∀ ε : ℝ, 0 < ε →
    (∃ T : ℕ, ∀ N m : ℕ, T ≤ N → band N m → (2*C₂-ε)*(2*(N : ℝ)-(m : ℝ)) ≤ A N m) ∧
    (∀ T : ℕ, ∃ N m : ℕ, T ≤ N ∧ 1 ≤ N ∧ band N m ∧ A N m ≤ (2*C₂+ε)*(2*(N : ℝ)-(m : ℝ))) := by
  apply SharpAssembly.assemble
  · simpa only [SharpAssembly.twinConstant, SharpArithmetic.C₂,
      SharpArithmetic.singularReal, SharpAnalytic.singularReal] using
      SharpArithmetic.eventually_lower
  · simpa only [SharpAssembly.twinConstant, SharpArithmetic.C₂,
      SharpArithmetic.singularReal, SharpAnalytic.singularReal] using
      SharpArithmetic.eventually_pow_two
