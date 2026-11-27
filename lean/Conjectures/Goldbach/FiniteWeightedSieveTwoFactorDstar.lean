import Mathlib

import Conjectures.Goldbach.FiniteWeightedSieveRemoveUnit
import Conjectures.Goldbach.FiniteWeightedSieveFactorCap

open scoped BigOperators

set_option autoImplicit false

/-!
The implication from the counting margin to the weighted sum is one direction of
`finite_weighted_sieve_two_factor_iff_count_margin`. The bound on the actual
divisibility counts over the range in FR-9018 is a separate mathematical input.
-/

def W (z y s : ℕ) : ℤ :=
  let P := (Finset.Ico z y).filter Nat.Prime
  (2 : ℤ) - ((P.filter (fun q => q ∣ s)).card : ℤ)
    - ((P.filter (fun q => q ^ 2 ∣ s)).card : ℤ)

def A (n z : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun p =>
    p.Prime ∧ ¬ (p ∣ n) ∧
    ((Finset.Ico 2 z).filter (fun q => Nat.Prime q ∧ q ∣ n - p)) = ∅)

/-- The primes in the sieve after excluding remainders below two. -/
def dstarSifted (n z : ℕ) : Finset ℕ :=
  (A n z).filter (fun p => 2 ≤ n - p)

private lemma dstar_sifted_eq_filter_minFac (n z : ℕ) :
    dstarSifted n z =
      ((n - 2).primesLE.filter (fun p => ¬p ∣ n)).filter
        (fun p => z ≤ (n - p).minFac) := by
  ext p
  simp only [dstarSifted, A, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpn, hp, hcop, hsmall⟩, hr⟩
    refine ⟨⟨⟨by omega, hp⟩, hcop⟩, ?_⟩
    by_contra! hbad
    have hprime : Nat.Prime (n - p).minFac := Nat.minFac_prime (by omega)
    have hmem : (n - p).minFac ∈ (Finset.Ico 2 z).filter
        (fun q => Nat.Prime q ∧ q ∣ n - p) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hprime.two_le, hbad⟩,
        hprime, Nat.minFac_dvd _⟩
    rw [hsmall] at hmem
    simp at hmem
  · rintro ⟨⟨⟨hpn', hp⟩, hcop⟩, hmin⟩
    have hp2 := hp.two_le
    refine ⟨⟨by omega, hp, hcop, ?_⟩, by omega⟩
    ext q
    constructor
    · intro hq
      obtain ⟨hqIco, hqprime, hqdvd⟩ := Finset.mem_filter.mp hq
      have hlt := (Finset.mem_Ico.mp hqIco).2
      have hle : (n - p).minFac ≤ q := Nat.minFac_le_of_dvd hqprime.two_le hqdvd
      exact ((not_lt_of_ge (hmin.trans hle)) hlt).elim
    · simp

/-- Buchstab's identity for the cardinalities of the shifted-prime sieve. -/
lemma dstar_buchstab_card (n w z₀ : ℕ) (hw : w ≤ z₀) :
    (dstarSifted n w).card = (dstarSifted n z₀).card +
      ∑ q ∈ (Finset.Ico w z₀).filter Nat.Prime,
        ((dstarSifted n q).filter (fun p => q ∣ n - p)).card := by
  let S := dstarSifted n w
  let R := S.filter (fun p => (n - p).minFac < z₀)
  let Q := (Finset.Ico w z₀).filter Nat.Prime
  have hmap : Set.MapsTo (fun p => (n - p).minFac) (↑R : Set ℕ) (↑Q : Set ℕ) := by
    intro p hp
    obtain ⟨hpS, hpR⟩ := Finset.mem_filter.mp (show p ∈ R from hp)
    have hp2 := (Finset.mem_filter.mp hpS).2
    rw [show S = dstarSifted n w from rfl, dstar_sifted_eq_filter_minFac] at hpS
    have hmin := (Finset.mem_filter.mp hpS).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hmin, hpR⟩,
      Nat.minFac_prime (by omega)⟩
  have hremain : S.filter (fun p => ¬ (n - p).minFac < z₀) = dstarSifted n z₀ := by
    unfold S
    rw [dstar_sifted_eq_filter_minFac n w, dstar_sifted_eq_filter_minFac n z₀]
    ext p
    simp only [Finset.mem_filter, not_lt]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hw.trans h.2⟩, h.2⟩⟩
  have hsplit : R.card + (dstarSifted n z₀).card = S.card := by
    rw [← hremain]
    exact Finset.card_filter_add_card_filter_not (s := S) (fun p => (n - p).minFac < z₀)
  have hfiber (q : ℕ) (hq : q ∈ Q) :
      R.filter (fun p => (n - p).minFac = q) =
        (dstarSifted n q).filter (fun p => q ∣ n - p) := by
    obtain ⟨hqIco, hqprime⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqlo, hqhi⟩ := Finset.mem_Ico.mp hqIco
    ext p
    simp only [R, S, dstar_sifted_eq_filter_minFac, Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨hp, _⟩, _⟩, hqeq⟩
      refine ⟨⟨hp, hqeq.ge⟩, ?_⟩
      rw [← hqeq]
      exact Nat.minFac_dvd _
    · rintro ⟨⟨hp, hmin⟩, hdiv⟩
      have hEq : (n - p).minFac = q :=
        (Nat.minFac_le_of_dvd hqprime.two_le hdiv).antisymm hmin
      exact ⟨⟨⟨hp, hqlo.trans hmin⟩, hEq.trans_lt hqhi⟩, hEq⟩
  calc
    (dstarSifted n w).card = (dstarSifted n z₀).card + R.card := by
      rw [add_comm]
      exact hsplit.symm
    _ = _ := by
      rw [Finset.card_eq_sum_card_fiberwise hmap]
      congr 1
      exact Finset.sum_congr rfl (fun q hq => congrArg Finset.card (hfiber q hq))

-- BEGIN Dstar lower sieve
/-- An intermediate cutoff with fourth power at most the effective lower-sieve level. -/
def dstarIntermediateCutoff (D : ℕ) : ℕ :=
  min 2999999 (Nat.sqrt (Nat.sqrt D))

lemma dstar_intermediate_cutoff_spec (D : ℕ) (hD : 16 ≤ D) :
    2 ≤ dstarIntermediateCutoff D ∧
      dstarIntermediateCutoff D < 3000000 ∧
      (dstarIntermediateCutoff D) ^ 4 ≤ D := by
  have hroot : 2 ≤ Nat.sqrt (Nat.sqrt D) := by
    apply Nat.le_sqrt.mpr
    apply Nat.le_sqrt.mpr
    exact hD
  have hw : dstarIntermediateCutoff D ≤ Nat.sqrt (Nat.sqrt D) := min_le_right _ _
  refine ⟨le_min (by decide) hroot, (min_le_left _ _).trans_lt (by decide), ?_⟩
  calc
    (dstarIntermediateCutoff D) ^ 4 = ((dstarIntermediateCutoff D) ^ 2) ^ 2 := by
      rw [← pow_mul]
    _ ≤ (Nat.sqrt D) ^ 2 := by
      apply Nat.pow_le_pow_left _ 2
      exact (Nat.pow_le_pow_left hw 2).trans
        (by simpa only [pow_two] using Nat.sqrt_le (Nat.sqrt D))
    _ ≤ D := by simpa only [pow_two] using Nat.sqrt_le D

/-- Prime candidates before sifting, with the unit remainder already excluded. -/
def dstarSieveBase (n : ℕ) : Finset ℕ :=
  (n - 2).primesLE.filter (fun p => ¬p ∣ n)

private def dstarSievePrimes (n w : ℕ) : Finset ℕ :=
  ((Finset.Ico 2 w).filter Nat.Prime).filter (fun q => ¬q ∣ n)

private lemma dstar_mem_sievePrimes {n w q : ℕ} :
    q ∈ dstarSievePrimes n w ↔ q.Prime ∧ q < w ∧ ¬q ∣ n := by
  simp only [dstarSievePrimes, Finset.mem_filter, Finset.mem_Ico]
  exact ⟨fun ⟨⟨⟨_, hlt⟩, hp⟩, hnd⟩ => ⟨hp, hlt, hnd⟩,
    fun ⟨hp, hlt, hnd⟩ => ⟨⟨⟨hp.two_le, hlt⟩, hp⟩, hnd⟩⟩

private def dstarSieveProduct (n w : ℕ) : ℕ :=
  ∏ q ∈ dstarSievePrimes n w, q

private noncomputable def dstarInverseTotient : ArithmeticFunction ℝ where
  toFun d := (d.totient : ℝ)⁻¹
  map_zero' := by simp

/-- The shifted-prime sequence with the reciprocal totient as local density. -/
noncomputable def dstarBoundingSieve (n w : ℕ) (h30 : 30 ∣ n) : BoundingSieve where
  support := (dstarSieveBase n).image (fun p => n - p)
  prodPrimes := dstarSieveProduct n w
  prodPrimes_squarefree := by
    unfold dstarSieveProduct
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro a ha b hb hab
      exact Nat.coprime_iff_isRelPrime.mp
        ((Nat.coprime_primes (dstar_mem_sievePrimes.mp ha).1
          (dstar_mem_sievePrimes.mp hb).1).mpr hab)
    · intro q hq
      exact ((dstar_mem_sievePrimes.mp hq).1).prime.squarefree
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (dstarSieveBase n).card
  nu := dstarInverseTotient
  nu_mult := by
    refine ⟨by norm_num [dstarInverseTotient], ?_⟩
    intro a b hab
    change (((a * b).totient : ℕ) : ℝ)⁻¹ =
      (a.totient : ℝ)⁻¹ * (b.totient : ℝ)⁻¹
    rw [Nat.totient_mul hab, Nat.cast_mul, mul_inv]
  nu_pos_of_prime := by
    intro q hq _
    change 0 < (q.totient : ℝ)⁻¹
    apply inv_pos.mpr
    exact_mod_cast Nat.totient_pos.mpr hq.pos
  nu_lt_one_of_prime := by
    intro q hq hprod
    have hmem : q ∈ dstarSievePrimes n w := by
      by_contra hm
      have hcop : q.Coprime (dstarSieveProduct n w) := by
        unfold dstarSieveProduct
        apply Nat.coprime_prod_right_iff.mpr
        intro r hr
        apply (Nat.coprime_primes hq (dstar_mem_sievePrimes.mp hr).1).mpr
        intro heq
        exact hm (heq.symm ▸ hr)
      exact (hq.coprime_iff_not_dvd.mp hcop) hprod
    have hnq : ¬q ∣ n := (dstar_mem_sievePrimes.mp hmem).2.2
    have h2 : 2 ∣ n := (by decide : 2 ∣ (30 : ℕ)).trans h30
    have hne : q ≠ 2 := fun h => hnq (h.symm ▸ h2)
    have hq3 : 2 < q := lt_of_le_of_ne hq.two_le hne.symm
    have hφ : 1 < q.totient := by rw [Nat.totient_prime hq]; omega
    change (q.totient : ℝ)⁻¹ < 1
    have hφR : (1 : ℝ) < (q.totient : ℝ) := by exact_mod_cast hφ
    exact (inv_lt_one₀ (zero_lt_one.trans hφR)).mpr hφR

private lemma dstar_sifted_eq_filter_coprime (n w : ℕ) :
    dstarSifted n w = (dstarSieveBase n).filter
      (fun p => (dstarSieveProduct n w).Coprime (n - p)) := by
  ext p
  simp only [dstarSifted, A, dstarSieveBase, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨_, hp, hnd, hsmall⟩, hr⟩
    refine ⟨⟨⟨by omega, hp⟩, hnd⟩, ?_⟩
    unfold dstarSieveProduct
    refine Nat.coprime_prod_left_iff.mpr ?_
    intro q hq
    obtain ⟨hqPrime, hqw, _⟩ := dstar_mem_sievePrimes.mp hq
    refine hqPrime.coprime_iff_not_dvd.mpr ?_
    intro hdiv
    exact Finset.filter_eq_empty_iff.mp hsmall
      (Finset.mem_Ico.mpr ⟨hqPrime.two_le, hqw⟩) ⟨hqPrime, hdiv⟩
  · rintro ⟨⟨⟨hpn2, hp⟩, hnd⟩, hcop⟩
    have hp2 := hp.two_le
    have hpn : p ≤ n := by omega
    refine ⟨⟨hpn, hp, hnd, ?_⟩, by omega⟩
    apply Finset.filter_eq_empty_iff.mpr
    intro q hq ⟨hqPrime, hdiv⟩
    have hqn : ¬q ∣ n := by
      intro hqn
      have hqp : q ∣ p := by
        simpa only [Nat.sub_sub_self hpn] using Nat.dvd_sub hqn hdiv
      rcases (Nat.dvd_prime hp).mp hqp with heq | heq
      · exact hqPrime.ne_one heq
      · exact hnd (heq ▸ hqn)
    have hmem : q ∈ dstarSievePrimes n w :=
      dstar_mem_sievePrimes.mpr ⟨hqPrime, (Finset.mem_Ico.mp hq).2, hqn⟩
    exact (hqPrime.coprime_iff_not_dvd.mp (Nat.coprime_prod_left_iff.mp hcop q hmem)) hdiv

/-- At cutoff seven the sieve removes no additional prime candidates when thirty divides n. -/
lemma dstar_sifted_seven_eq_base (n : ℕ) (h30 : 30 ∣ n) :
    dstarSifted n 7 = dstarSieveBase n := by
  have hsmall : ∀ q ∈ (Finset.Ico 2 7).filter Nat.Prime, q ∣ (30 : ℕ) := by decide
  have hP : dstarSievePrimes n 7 = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro q hq hnd
    exact hnd ((hsmall q hq).trans h30)
  rw [dstar_sifted_eq_filter_coprime]
  simp [dstarSieveProduct, hP]

private lemma dstar_sieve_base_le {n p : ℕ} (hp : p ∈ dstarSieveBase n) : p ≤ n :=
  ((Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).1).trans (Nat.sub_le _ _)

private lemma dstar_sub_injOn (n : ℕ) :
    Set.InjOn (fun p => n - p) (↑(dstarSieveBase n) : Set ℕ) := by
  intro p hp q hq heq
  have hpn := dstar_sieve_base_le (show p ∈ dstarSieveBase n from hp)
  have hqn := dstar_sieve_base_le (show q ∈ dstarSieveBase n from hq)
  change n - p = n - q at heq
  omega

lemma dstar_boundingSieve_siftedSum (n w : ℕ) (h30 : 30 ∣ n) :
    (dstarBoundingSieve n w h30).siftedSum = ((dstarSifted n w).card : ℝ) := by
  rw [dstar_sifted_eq_filter_coprime]
  change (∑ m ∈ (dstarSieveBase n).image (fun p => n - p),
    if (dstarSieveProduct n w).Coprime m then (1 : ℝ) else 0) = _
  rw [Finset.sum_image (dstar_sub_injOn n), Finset.sum_boole]

lemma dstar_boundingSieve_multSum (n w d : ℕ) (h30 : 30 ∣ n) :
    (dstarBoundingSieve n w h30).multSum d =
      (((dstarSieveBase n).filter (fun p => p ≡ n [MOD d])).card : ℝ) := by
  change (∑ m ∈ (dstarSieveBase n).image (fun p => n - p),
    if d ∣ m then (1 : ℝ) else 0) = _
  rw [Finset.sum_image (dstar_sub_injOn n), Finset.sum_boole]
  have hfilter :
      (dstarSieveBase n).filter (fun p => d ∣ n - p) =
        (dstarSieveBase n).filter (fun p => p ≡ n [MOD d]) := by
    ext p
    simp only [Finset.mem_filter]
    exact and_congr_right (fun hp => (Nat.modEq_iff_dvd' (dstar_sieve_base_le hp)).symm)
  rw [hfilter]

lemma dstar_boundingSieve_rem (n w d : ℕ) (h30 : 30 ∣ n) :
    (dstarBoundingSieve n w h30).rem d =
      (((dstarSieveBase n).filter (fun p => p ≡ n [MOD d])).card : ℝ) -
        ((dstarSieveBase n).card : ℝ) / (d.totient : ℝ) := by
  unfold BoundingSieve.rem
  rw [dstar_boundingSieve_multSum]
  change _ - (d.totient : ℝ)⁻¹ * ((dstarSieveBase n).card : ℝ) =
    _ - ((dstarSieveBase n).card : ℝ) / (d.totient : ℝ)
  rw [div_eq_mul_inv, mul_comm (d.totient : ℝ)⁻¹]

private lemma dstar_mainSum_sub_errSum_le_siftedSum
    (s : BoundingSieve) (weight : ℕ → ℝ)
    (hlower : ∀ m : ℕ, m ∣ s.prodPrimes → (∑ d ∈ m.divisors, weight d) ≤ if m = 1 then 1 else 0) :
    s.totalMass * s.mainSum weight - s.errSum weight ≤ s.siftedSum := by
  have herr : -s.errSum weight ≤
      ∑ d ∈ s.prodPrimes.divisors, weight d * s.rem d := by
    rw [BoundingSieve.errSum, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum (fun d _ => by rw [← abs_mul]; exact neg_abs_le _)
  calc
    s.totalMass * s.mainSum weight - s.errSum weight
      ≤ s.totalMass * s.mainSum weight +
          ∑ d ∈ s.prodPrimes.divisors, weight d * s.rem d := by
        rw [sub_eq_add_neg]
        exact add_le_add_right herr _
    _ = ∑ d ∈ s.prodPrimes.divisors, weight d * s.multSum d := by
      symm
      rw [BoundingSieve.mainSum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      rw [BoundingSieve.multSum_eq_main_err]
      ring
    _ = ∑ m ∈ s.support, s.weights m *
          ∑ d ∈ (s.prodPrimes.gcd m).divisors, weight d := by
      symm
      calc
        _ = ∑ m ∈ s.support, ∑ d ∈ s.prodPrimes.divisors,
            if d ∣ m then s.weights m * weight d else 0 := by
          simp_rw [Finset.mul_sum, ← Finset.sum_filter]
          congr with m
          congr
          rw [← Nat.divisors_filter_dvd_of_dvd s.prodPrimes_ne_zero
            (Nat.gcd_dvd_left _ _)]
          ext d
          simp +contextual [Nat.dvd_gcd_iff]
        _ = _ := by
          rw [Finset.sum_comm]
          simp_rw [BoundingSieve.multSum, ← Finset.sum_filter, Finset.mul_sum, mul_comm]
    _ ≤ s.siftedSum := by
      rw [BoundingSieve.siftedSum_eq_sum_support_mul_ite]
      exact Finset.sum_le_sum (fun m _ =>
        mul_le_mul_of_nonneg_left (hlower _ (Nat.gcd_dvd_left _ _)) (s.weights_nonneg m))

/-- A lower bound for the actual candidate set from valid lower-sieve weights.
`hlower` certifies the pointwise minorant. `hmain` and `herr` bound its main term and error. -/
lemma dstar_sifted_card_ge_of_lower_weights (n w : ℕ) (h30 : 30 ∣ n)
    (weight : ℕ → ℝ) {M E : ℝ}
    (hlower : ∀ m : ℕ, m ∣ (dstarBoundingSieve n w h30).prodPrimes →
      (∑ d ∈ m.divisors, weight d) ≤ if m = 1 then 1 else 0)
    (hmain : M ≤ (dstarBoundingSieve n w h30).mainSum weight)
    (herr : (dstarBoundingSieve n w h30).errSum weight ≤ E) :
    ((dstarSieveBase n).card : ℝ) * M - E ≤ ((dstarSifted n w).card : ℝ) := by
  let s := dstarBoundingSieve n w h30
  have hmass : (0 : ℝ) ≤ s.totalMass := by
    change 0 ≤ ((dstarSieveBase n).card : ℝ)
    positivity
  rw [← dstar_boundingSieve_siftedSum n w h30]
  change s.totalMass * M - E ≤ s.siftedSum
  exact (sub_le_sub (mul_le_mul_of_nonneg_left hmain hmass) herr).trans
    (dstar_mainSum_sub_errSum_le_siftedSum s weight hlower)
-- END Dstar lower sieve

/-- The smallest upper cutoff compatible with `z < y` and `n ≤ z * y ^ 2`,
    for positive `n` and `z`. -/
def minSieveUpperCutoff (n z : ℕ) : ℕ :=
  max (z + 1) (Nat.sqrt ((n - 1) / z) + 1)

private theorem minSieveUpperCutoff_spec (n z : ℕ) (hn : 0 < n) (hz : 0 < z) :
    z < minSieveUpperCutoff n z ∧ n ≤ z * (minSieveUpperCutoff n z) ^ 2 := by
  have hroot : Nat.sqrt ((n - 1) / z) + 1 ≤ minSieveUpperCutoff n z :=
    le_max_right _ _
  have hfloor : (n - 1) / z < (Nat.sqrt ((n - 1) / z) + 1) ^ 2 := by
    simpa only [pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt ((n - 1) / z)
  have hdiv : (n - 1) / z < (minSieveUpperCutoff n z) ^ 2 :=
    hfloor.trans_le (Nat.pow_le_pow_left hroot 2)
  have hmul : n - 1 < z * (minSieveUpperCutoff n z) ^ 2 := by
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hz).mp hdiv
  exact ⟨(Nat.lt_succ_self z).trans_le (le_max_left _ _), by omega⟩

private theorem minSieveUpperCutoff_le (n z y : ℕ) (hn : 0 < n) (hz : 0 < z)
    (hzy : z < y) (hny : n ≤ z * y ^ 2) : minSieveUpperCutoff n z ≤ y := by
  have hmul : n - 1 < y ^ 2 * z := by
    rw [Nat.mul_comm]
    omega
  have hdiv : (n - 1) / z < y ^ 2 := (Nat.div_lt_iff_lt_mul hz).mpr hmul
  have hroot : Nat.sqrt ((n - 1) / z) < y := by
    exact Nat.sqrt_lt.mpr (by simpa only [pow_two] using hdiv)
  exact max_le (by omega) (by omega)

private theorem weight_antitone_upper (z y₀ y s : ℕ) (hy : y₀ ≤ y) :
    W z y s ≤ W z y₀ s := by
  let P₀ := (Finset.Ico z y₀).filter Nat.Prime
  let P := (Finset.Ico z y).filter Nat.Prime
  have hsubset : P₀ ⊆ P := by
    intro q hq
    obtain ⟨hqr, hqp⟩ := Finset.mem_filter.mp hq
    obtain ⟨hzq, hqy⟩ := Finset.mem_Ico.mp hqr
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hzq, hqy.trans_le hy⟩, hqp⟩
  have hcard (f : ℕ → Prop) [DecidablePred f] :
      ((P₀.filter f).card : ℤ) ≤ ((P.filter f).card : ℤ) := by
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter f hsubset)
  have hfirst := hcard (fun q => q ∣ s)
  have hsecond := hcard (fun q => q ^ 2 ∣ s)
  change (2 : ℤ) - ((P.filter (fun q => q ∣ s)).card : ℤ)
    - ((P.filter (fun q => q ^ 2 ∣ s)).card : ℤ) ≤
    (2 : ℤ) - ((P₀.filter (fun q => q ∣ s)).card : ℤ)
    - ((P₀.filter (fun q => q ^ 2 ∣ s)).card : ℤ)
  omega

theorem finite_weighted_sieve_pos_iff_count_margin (n z y : ℕ) :
    let S := (A n z).filter (fun p => 2 ≤ n - p)
    let P := (Finset.Ico z y).filter Nat.Prime
    (0 < ∑ p ∈ S, W z y (n - p)) ↔
      (∑ q ∈ P, ((S.filter (fun p => q ∣ n - p)).card : ℤ)) +
        (∑ q ∈ P, ((S.filter (fun p => q ^ 2 ∣ n - p)).card : ℤ)) <
          2 * (S.card : ℤ) := by
  intro S P
  change (0 < ∑ p ∈ S, ((2 : ℤ)
    - ((P.filter (fun q => q ∣ n - p)).card : ℤ)
    - ((P.filter (fun q => q ^ 2 ∣ n - p)).card : ℤ))) ↔ _
  have hswap (f : ℕ → ℕ) :
      (∑ p ∈ S, ((P.filter (fun q => f q ∣ n - p)).card : ℤ)) =
        ∑ q ∈ P, ((S.filter (fun p => f q ∣ n - p)).card : ℤ) := by
    simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
    exact Finset.sum_comm
  have htwo : (∑ _p ∈ S, (2 : ℤ)) = 2 * (S.card : ℤ) := by
    rw [mul_comm 2]
    simp [Finset.sum_const]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, htwo,
    hswap (fun q => q), hswap (fun q => q ^ 2)]
  omega

theorem finite_weighted_sieve_two_factor_iff_count_margin (n : ℕ) (hn : 0 < n) :
    (∃ z y : ℕ, 2 < z ∧ z < y ∧ n ≤ y ^ 3 ∧ n ≤ z * y ^ 2 ∧
      0 < ∑ p ∈ (A n z).filter (fun p => 2 ≤ n - p), W z y (n - p)) ↔
    (∃ z : ℕ, 2 < z ∧
      let y := minSieveUpperCutoff n z
      let S := (A n z).filter (fun p => 2 ≤ n - p)
      let P := (Finset.Ico z y).filter Nat.Prime
      (∑ q ∈ P, ((S.filter (fun p => q ∣ n - p)).card : ℤ)) +
        (∑ q ∈ P, ((S.filter (fun p => q ^ 2 ∣ n - p)).card : ℤ)) <
          2 * (S.card : ℤ)) := by
  constructor
  · rintro ⟨z, y, hz, hzy, _, hny, hsum⟩
    let y₀ := minSieveUpperCutoff n z
    have hy₀ : y₀ ≤ y := minSieveUpperCutoff_le n z y hn (by omega) hzy hny
    have hsum_le :
        (∑ p ∈ (A n z).filter (fun p => 2 ≤ n - p), W z y (n - p)) ≤
          ∑ p ∈ (A n z).filter (fun p => 2 ≤ n - p), W z y₀ (n - p) :=
      Finset.sum_le_sum (fun p _ => weight_antitone_upper z y₀ y (n - p) hy₀)
    exact ⟨z, hz, (finite_weighted_sieve_pos_iff_count_margin n z y₀).mp
      (hsum.trans_le hsum_le)⟩
  · rintro ⟨z, hz, hmargin⟩
    let y := minSieveUpperCutoff n z
    obtain ⟨hzy, hny⟩ := minSieveUpperCutoff_spec n z hn (by omega)
    have hcube : n ≤ y ^ 3 := by
      calc
        n ≤ z * y ^ 2 := hny
        _ ≤ y * y ^ 2 := Nat.mul_le_mul_right _ hzy.le
        _ = y ^ 3 := by ring
    exact ⟨z, y, hz, hzy, hcube, hny,
      (finite_weighted_sieve_pos_iff_count_margin n z y).mpr hmargin⟩

/-- Count the positive multiples of `q ^ 2` accessible to the sieve candidates. -/
private theorem sieve_square_count_le (n z q : ℕ) :
    let S := (A n z).filter (fun p => 2 ≤ n - p)
    (S.filter (fun p => q ^ 2 ∣ n - p)).card ≤ (n - 2) / q ^ 2 := by
  intro S
  let B := S.filter (fun p => q ^ 2 ∣ n - p)
  have hcount : B.card ≤ (Finset.Icc 1 ((n - 2) / q ^ 2)).card := by
    refine Finset.card_le_card_of_injOn (fun p => (n - p) / q ^ 2) ?_ ?_
    · intro p hp
      obtain ⟨hpS, hdiv⟩ := Finset.mem_filter.mp (show p ∈ B from hp)
      have hrem := (Finset.mem_filter.mp hpS).2
      have hpA : p ∈ A n z := (Finset.mem_filter.mp hpS).1
      have hp2 : 2 ≤ p := (Finset.mem_filter.mp hpA).2.1.two_le
      have hmul := Nat.div_mul_cancel hdiv
      have hquot : 1 ≤ (n - p) / q ^ 2 := by
        apply Nat.pos_of_ne_zero
        intro hzero
        rw [hzero, zero_mul] at hmul
        omega
      exact Finset.mem_Icc.mpr
        ⟨hquot, Nat.div_le_div_right (Nat.sub_le_sub_left hp2 n)⟩
    · intro a ha b hb hab
      have da := Nat.div_mul_cancel (Finset.mem_filter.mp (show a ∈ B from ha)).2
      have db := Nat.div_mul_cancel (Finset.mem_filter.mp (show b ∈ B from hb)).2
      have hra := (Finset.mem_filter.mp (Finset.mem_filter.mp (show a ∈ B from ha)).1).2
      have hrb := (Finset.mem_filter.mp (Finset.mem_filter.mp (show b ∈ B from hb)).1).2
      change (n - a) / q ^ 2 = (n - b) / q ^ 2 at hab
      rw [hab, db] at da
      omega
  simpa using hcount

private theorem div_square_le_div_difference (m q : ℕ) (hq : 2 ≤ q) :
    ((m / q ^ 2 : ℕ) : ℤ) ≤ ((m / (q - 1) : ℕ) : ℤ) - ((m / q : ℕ) : ℤ) := by
  let a := m / q
  let b := m / q ^ 2
  have hb : b * q ≤ a := by
    dsimp only [b, a]
    rw [pow_two, ← Nat.div_div_eq_div_mul]
    exact Nat.div_mul_le_self _ _
  have hq_pos : 0 < q - 1 := by omega
  have hq_eq : q - 1 + 1 = q := by omega
  have hab : a + b ≤ m / (q - 1) := by
    apply (Nat.le_div_iff_mul_le hq_pos).2
    have hb' : b * (q - 1) ≤ a :=
      (Nat.mul_le_mul_left b (Nat.sub_le q 1)).trans hb
    calc
      (a + b) * (q - 1) = a * (q - 1) + b * (q - 1) := Nat.add_mul _ _ _
      _ ≤ a * (q - 1) + a := Nat.add_le_add_left hb' _
      _ = a * (q - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = a * q := by rw [hq_eq]
      _ ≤ m := Nat.div_mul_le_self _ _
  have hint : (a : ℤ) + (b : ℤ) ≤ ((m / (q - 1) : ℕ) : ℤ) := by
    exact_mod_cast hab
  change (b : ℤ) ≤ ((m / (q - 1) : ℕ) : ℤ) - (a : ℤ)
  omega

private theorem dstar_sum_div_square_tail_le (m y T : ℕ) (Q : Finset ℕ)
    (hT : 2 ≤ T) (hTy : T ≤ y) (hQ : Q ⊆ Finset.Ico T y) :
    (∑ q ∈ Q, ((m / q ^ 2 : ℕ) : ℤ)) ≤
      ((m / (T - 1) : ℕ) : ℤ) - ((m / (y - 1) : ℕ) : ℤ) := by
  calc
    _ ≤ ∑ q ∈ Finset.Ico T y, ((m / q ^ 2 : ℕ) : ℤ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => Int.natCast_nonneg _)
    _ ≤ ∑ q ∈ Finset.Ico T y, (((m / (q - 1) : ℕ) : ℤ) - ((m / q : ℕ) : ℤ)) :=
      Finset.sum_le_sum (fun _ hq =>
        div_square_le_div_difference m _ (hT.trans (Finset.mem_Ico.mp hq).1))
    _ = _ := by
      simpa only [Nat.add_sub_cancel, neg_sub_neg] using
        Finset.sum_Ico_sub (fun q => -((m / (q - 1) : ℕ) : ℤ)) hTy

/-- Bound the square divisibility loss from primes `q ≥ T` in the prime interval. -/
theorem finite_weighted_sieve_square_tail_le (n z y T : ℕ) (hT : 2 ≤ T) (hTy : T ≤ y) :
    let S := (A n z).filter (fun p => 2 ≤ n - p)
    let P := (Finset.Ico z y).filter Nat.Prime
    (∑ q ∈ P.filter (fun q => T ≤ q), ((S.filter (fun p => q ^ 2 ∣ n - p)).card : ℤ)) ≤
      (((n - 2) / (T - 1) : ℕ) : ℤ) - (((n - 2) / (y - 1) : ℕ) : ℤ) := by
  intro S P
  let m := n - 2
  let D (q : ℕ) : ℤ := (S.filter (fun p => q ^ 2 ∣ n - p)).card
  have hsubset : P.filter (fun q => T ≤ q) ⊆ Finset.Ico T y := by
    intro q hq
    obtain ⟨hqP, hqT⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_Ico.mpr ⟨hqT, (Finset.mem_Ico.mp (Finset.mem_filter.mp hqP).1).2⟩
  exact (Finset.sum_le_sum (fun q _ =>
    show D q ≤ ((m / q ^ 2 : ℕ) : ℤ) from
      Int.ofNat_le.mpr (sieve_square_count_le n z q))).trans
    (dstar_sum_div_square_tail_le m y T _ hT hTy hsubset)

/-- Split the square loss at `T`. Taking `T = y` recovers the exact estimate. -/
theorem finite_weighted_sieve_count_margin_iff_square_budget (n z y : ℕ) (hy : 2 ≤ y) :
    let S := (A n z).filter (fun p => 2 ≤ n - p)
    let P := (Finset.Ico z y).filter Nat.Prime
    let D₁ := ∑ q ∈ P, ((S.filter (fun p => q ∣ n - p)).card : ℤ)
    let D₂ (q : ℕ) : ℤ := (S.filter (fun p => q ^ 2 ∣ n - p)).card
    (D₁ + (∑ q ∈ P, D₂ q) < 2 * (S.card : ℤ)) ↔
      (∃ T : ℕ, 2 ≤ T ∧ T ≤ y ∧
        D₁ + (∑ q ∈ P.filter (fun q => q < T), D₂ q) +
            (((n - 2) / (T - 1) : ℕ) : ℤ) - (((n - 2) / (y - 1) : ℕ) : ℤ) <
          2 * (S.card : ℤ)) := by
  intro S P D₁ D₂
  constructor
  · intro h
    have hfilter : P.filter (fun q => q < y) = P := by
      apply Finset.filter_true_of_mem
      intro q hq
      exact (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).2
    refine ⟨y, hy, le_rfl, ?_⟩
    simpa only [hfilter, add_sub_cancel_right] using h
  · rintro ⟨T, hT, hTy, hb⟩
    have htail :
        (∑ q ∈ P.filter (fun q => T ≤ q), D₂ q) ≤
          (((n - 2) / (T - 1) : ℕ) : ℤ) - (((n - 2) / (y - 1) : ℕ) : ℤ) :=
      finite_weighted_sieve_square_tail_le n z y T hT hTy
    have hsplit := Finset.sum_filter_add_sum_filter_not P (fun q => q < T) D₂
    simp only [not_lt] at hsplit
    omega


private theorem dstar_remainder_coprime {n z p : ℕ} (hp : p ∈ A n z) :
    n.Coprime (n - p) := by
  obtain ⟨hp_range, hp_prime, hp_not, _⟩ := Finset.mem_filter.mp hp
  have hp_le : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp_range)
  rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_eq_one_iff]
  intro d hdn hds
  have hdp := (Nat.dvd_sub_iff_right hp_le hdn).mp hds
  rcases (Nat.dvd_prime hp_prime).mp hdp with heq | heq
  · exact heq
  · exact (hp_not (heq ▸ hdn)).elim

private def dstarWheelRank (a : ℕ) : ℕ :=
  (4 * a + 14) / 15

private def dstarWheelResidues : List ℕ :=
  [1, 7, 11, 13, 17, 19, 23, 29]

private theorem dstar_wheel_residue_rank {r : ℕ} (hr : r < 30) (hc : (30 : ℕ).Coprime r) :
    1 ≤ dstarWheelRank r ∧ dstarWheelRank r ≤ 8 ∧
      dstarWheelResidues.getD (dstarWheelRank r - 1) 0 = r := by
  have table :
      ∀ a : Fin 30, (30 : ℕ).Coprime a.val →
        1 ≤ dstarWheelRank a.val ∧ dstarWheelRank a.val ≤ 8 ∧
          dstarWheelResidues.getD (dstarWheelRank a.val - 1) 0 = a.val := by
    decide +kernel
  exact table ⟨r, hr⟩ hc

private theorem dstar_wheel_rank_inj {a b : ℕ}
    (ha : (30 : ℕ).Coprime a) (hb : (30 : ℕ).Coprime b)
    (heq : dstarWheelRank a = dstarWheelRank b) : a = b := by
  have hmod (x : ℕ) (hx : (30 : ℕ).Coprime x) : (30 : ℕ).Coprime (x % 30) := by
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm 30 (x % 30), ← Nat.gcd_rec 30 x]
    exact hx.gcd_eq_one
  obtain ⟨ha_lo, ha_hi, ha_residue⟩ :=
    dstar_wheel_residue_rank (Nat.mod_lt a (by decide)) (hmod a ha)
  obtain ⟨hb_lo, hb_hi, hb_residue⟩ :=
    dstar_wheel_residue_rank (Nat.mod_lt b (by decide)) (hmod b hb)
  have hshift (x : ℕ) :
      dstarWheelRank x = 8 * (x / 30) + dstarWheelRank (x % 30) := by
    unfold dstarWheelRank
    omega
  rw [hshift a, hshift b] at heq
  have hblock : a / 30 = b / 30 := by omega
  have hrank : dstarWheelRank (a % 30) = dstarWheelRank (b % 30) := by omega
  have hresidue : a % 30 = b % 30 := by
    calc
      a % 30 = dstarWheelResidues.getD (dstarWheelRank (a % 30) - 1) 0 := ha_residue.symm
      _ = dstarWheelResidues.getD (dstarWheelRank (b % 30) - 1) 0 := by rw [hrank]
      _ = b % 30 := hb_residue
  omega

/-- Count the allowable quotients using the residue classes coprime to thirty. -/
private theorem dstar_divisor_count_wheel_le (n z d : ℕ) (h30 : 30 ∣ n) :
    let S := (A n z).filter (fun p => 2 ≤ n - p)
    (S.filter (fun p => d ∣ n - p)).card ≤ dstarWheelRank ((n - 2) / d) := by
  intro S
  let B := S.filter (fun p => d ∣ n - p)
  have hquotient (p : ℕ) (hp : p ∈ B) :
      1 ≤ (n - p) / d ∧ (n - p) / d ≤ (n - 2) / d ∧
        (30 : ℕ).Coprime ((n - p) / d) := by
    obtain ⟨hpS, hdiv⟩ := Finset.mem_filter.mp (show p ∈ B from hp)
    obtain ⟨hpA, hrem⟩ := Finset.mem_filter.mp hpS
    have hp2 : 2 ≤ p := (Finset.mem_filter.mp hpA).2.1.two_le
    have hpos : 1 ≤ (n - p) / d := by
      apply Nat.pos_of_ne_zero
      intro hzero
      have hmul := Nat.div_mul_cancel hdiv
      rw [hzero, zero_mul] at hmul
      omega
    exact ⟨hpos, Nat.div_le_div_right (Nat.sub_le_sub_left hp2 n),
      ((dstar_remainder_coprime hpA).coprime_dvd_left h30).coprime_dvd_right
        (Nat.div_dvd_of_dvd hdiv)⟩
  have hcard : B.card ≤ (Finset.Icc 1 (dstarWheelRank ((n - 2) / d))).card := by
    refine Finset.card_le_card_of_injOn (fun p => dstarWheelRank ((n - p) / d)) ?_ ?_
    · intro p hp
      obtain ⟨hp_lo, hp_hi, _⟩ := hquotient p hp
      apply Finset.mem_Icc.mpr
      change 1 ≤ dstarWheelRank ((n - p) / d) ∧
        dstarWheelRank ((n - p) / d) ≤ dstarWheelRank ((n - 2) / d)
      unfold dstarWheelRank
      constructor <;> omega
    · intro a ha b hb heq
      have hquot := dstar_wheel_rank_inj (hquotient a ha).2.2 (hquotient b hb).2.2 heq
      obtain ⟨haS, haD⟩ := Finset.mem_filter.mp (show a ∈ B from ha)
      obtain ⟨hbS, hbD⟩ := Finset.mem_filter.mp (show b ∈ B from hb)
      have ha_rem := (Finset.mem_filter.mp haS).2
      have hb_rem := (Finset.mem_filter.mp hbS).2
      have ha_mul := Nat.div_mul_cancel haD
      have hb_mul := Nat.div_mul_cancel hbD
      rw [hquot, hb_mul] at ha_mul
      omega
  simpa using hcard

private theorem dstar_sum_remove_divisors (n z : ℕ) (P : Finset ℕ) (f : ℕ → ℕ)
    (hprime : ∀ q ∈ P, q.Prime) (hdiv : ∀ q, q ∣ f q) :
    let S := (A n z).filter (fun p => 2 ≤ n - p)
    (∑ q ∈ P, ((S.filter (fun p => f q ∣ n - p)).card : ℤ)) =
      ∑ q ∈ P.filter (fun q => ¬ q ∣ n), ((S.filter (fun p => f q ∣ n - p)).card : ℤ) := by
  intro S
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro q hq hnot
  have hqn : q ∣ n := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hq, h⟩)
  have hempty : S.filter (fun p => f q ∣ n - p) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpS, hpf⟩ := Finset.mem_filter.mp hp
    have hpA := (Finset.mem_filter.mp hpS).1
    have hc := dstar_remainder_coprime hpA
    have hqone := Nat.eq_one_of_dvd_coprimes hc hqn ((hdiv q).trans hpf)
    exact (hprime q hq).ne_one hqone
  simp [hempty]

/-- Use the smaller of the unrestricted tail bound and the bound from residues modulo thirty. -/
private def dstarSquareTailBudget (n y T : ℕ) (Q : Finset ℕ) : ℤ :=
  let B := (((n - 2) / (T - 1) : ℕ) : ℤ) - (((n - 2) / (y - 1) : ℕ) : ℤ)
  min B ((4 * B + 14 * (Q.card : ℤ)) / 15)

private theorem dstar_square_tail_wheel_le (n z y T : ℕ) (Q : Finset ℕ)
    (h30 : 30 ∣ n) (hT : 2 ≤ T) (hTy : T ≤ y) (hQ : Q ⊆ Finset.Ico T y) :
    let S := (A n z).filter (fun p => 2 ≤ n - p)
    (∑ q ∈ Q, ((S.filter (fun p => q ^ 2 ∣ n - p)).card : ℤ)) ≤
      dstarSquareTailBudget n y T Q := by
  intro S
  let D (q : ℕ) : ℤ := (S.filter (fun p => q ^ 2 ∣ n - p)).card
  let F (q : ℕ) : ℤ := (↑((n - 2) / q ^ 2 : ℕ) : ℤ)
  let B : ℤ := (((n - 2) / (T - 1) : ℕ) : ℤ) - (((n - 2) / (y - 1) : ℕ) : ℤ)
  have hf : (∑ q ∈ Q, F q) ≤ B := dstar_sum_div_square_tail_le (n - 2) y T Q hT hTy hQ
  have hcount (q : ℕ) : 15 * D q ≤ 4 * F q + 14 := by
    have h : (S.filter (fun p => q ^ 2 ∣ n - p)).card ≤
        dstarWheelRank ((n - 2) / q ^ 2) :=
      dstar_divisor_count_wheel_le n z (q ^ 2) h30
    unfold dstarWheelRank at h
    have hh : 15 * (S.filter (fun p => q ^ 2 ∣ n - p)).card ≤ 4 * ((n - 2) / q ^ 2) + 14 := by
      omega
    dsimp only [D, F]
    exact_mod_cast hh
  change (∑ q ∈ Q, D q) ≤ min B ((4 * B + 14 * (Q.card : ℤ)) / 15)
  apply le_min
  · exact (Finset.sum_le_sum (fun q _ => Int.ofNat_le.mpr (sieve_square_count_le n z q))).trans hf
  · apply (Int.le_ediv_iff_mul_le (by decide : (0 : ℤ) < 15)).mpr
    have hsum : 15 * (∑ q ∈ Q, D q) ≤ 4 * (∑ q ∈ Q, F q) + 14 * (Q.card : ℤ) := by
      calc
        _ = ∑ q ∈ Q, 15 * D q := Finset.mul_sum _ _ _
        _ ≤ ∑ q ∈ Q, (4 * F q + 14) := Finset.sum_le_sum (fun q _ => hcount q)
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp [mul_comm]
    omega

/-- Split the square budget after discarding primes that divide the target. -/
theorem finite_weighted_sieve_count_margin_iff_wheel_budget (n z y : ℕ) (h30 : 30 ∣ n)
    (hy : 2 ≤ y) :
    let S := (A n z).filter (fun p => 2 ≤ n - p)
    let P := (Finset.Ico z y).filter Nat.Prime
    let Q := P.filter (fun q => ¬ q ∣ n)
    let D₁ (q : ℕ) : ℤ := (S.filter (fun p => q ∣ n - p)).card
    let D₂ (q : ℕ) : ℤ := (S.filter (fun p => q ^ 2 ∣ n - p)).card
    ((∑ q ∈ P, D₁ q) + (∑ q ∈ P, D₂ q) < 2 * (S.card : ℤ)) ↔
      (∃ T : ℕ, 2 ≤ T ∧ T ≤ y ∧
        (∑ q ∈ Q, D₁ q) + (∑ q ∈ Q.filter (fun q => q < T), D₂ q) +
            dstarSquareTailBudget n y T (Q.filter (fun q => T ≤ q)) <
          2 * (S.card : ℤ)) := by
  intro S P Q D₁ D₂
  have hprime (q : ℕ) (hq : q ∈ P) := (Finset.mem_filter.mp hq).2
  have hfirst : ∑ q ∈ P, D₁ q = ∑ q ∈ Q, D₁ q :=
    dstar_sum_remove_divisors n z P (fun q => q) hprime dvd_refl
  have hsecond : ∑ q ∈ P, D₂ q = ∑ q ∈ Q, D₂ q :=
    dstar_sum_remove_divisors n z P (fun q => q ^ 2) hprime (fun q => by rw [pow_two]; exact dvd_mul_right q q)
  have hlt (q : ℕ) (hq : q ∈ Q) : q < y :=
    (Finset.mem_Ico.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1).2
  rw [hfirst, hsecond]
  constructor
  · intro h
    have hsmall : Q.filter (fun q => q < y) = Q := Finset.filter_true_of_mem hlt
    have hempty : Q.filter (fun q => y ≤ q) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      exact (not_le_of_gt (hlt q (Finset.mem_filter.mp hq).1)) (Finset.mem_filter.mp hq).2
    refine ⟨y, hy, le_rfl, ?_⟩
    simpa [hsmall, hempty, dstarSquareTailBudget] using h
  · rintro ⟨T, hT, hTy, h⟩
    have hsubset : Q.filter (fun q => T ≤ q) ⊆ Finset.Ico T y := by
      intro q hq
      obtain ⟨hqQ, hqT⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_Ico.mpr ⟨hqT, hlt q hqQ⟩
    have htail : ∑ q ∈ Q.filter (fun q => T ≤ q), D₂ q ≤
        dstarSquareTailBudget n y T (Q.filter (fun q => T ≤ q)) :=
      dstar_square_tail_wheel_le n z y T _ h30 hT hTy hsubset
    have hsplit := Finset.sum_filter_add_sum_filter_not Q (fun q => q < T) D₂
    simp only [not_lt] at hsplit
    omega

/-- A prime pair with a large second summand gives positive weight at a composite cutoff. -/
private theorem finite_weighted_sieve_of_prime_pair {n z p q : ℕ}
    (hsum : n = p + q) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hz : 2 < z) (hzcomp : ¬ z.Prime) (hzq : z ≤ q) (hbound : n ≤ z * (z + 1) ^ 2) :
    ∃ z y : ℕ, 2 < z ∧ z < y ∧ n ≤ y^3 ∧ n ≤ z * y^2 ∧
      0 < ∑ p ∈ (A n z).filter (fun p => 2 ≤ n - p), W z y (n - p) := by
  have hrem : n - p = q := by omega
  have hpn : ¬ p ∣ n := by
    intro hd
    have hdq : p ∣ q := hrem ▸ Nat.dvd_sub hd (dvd_refl p)
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdq)
  have hrough : ((Finset.Ico 2 z).filter (fun r => Nat.Prime r ∧ r ∣ n - p)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨hrI, hrP, hrD⟩ := Finset.mem_filter.mp hr
    have hrz := (Finset.mem_Ico.mp hrI).2
    have heq : r = q := (Nat.prime_dvd_prime_iff_eq hrP hq).mp (hrem ▸ hrD)
    omega
  let S := (A n z).filter (fun p => 2 ≤ n - p)
  have hpS : p ∈ S := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hp, hpn, hrough⟩
    · simpa only [hrem] using hq.two_le
  have hP : ((Finset.Ico z (z + 1)).filter Nat.Prime) = ∅ := by
    rw [Nat.Ico_succ_singleton]
    simp [hzcomp]
  have hw (s : ℕ) : W z (z + 1) s = 2 := by
    change (2 : ℤ) - ((((Finset.Ico z (z + 1)).filter Nat.Prime).filter
      (fun r => r ∣ s)).card : ℤ) - ((((Finset.Ico z (z + 1)).filter Nat.Prime).filter
      (fun r => r ^ 2 ∣ s)).card : ℤ) = 2
    rw [hP]
    simp
  have hpos : 0 < ∑ r ∈ S, W z (z + 1) (n - r) := by
    have hcard : (0 : ℤ) < (S.card : ℤ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨p, hpS⟩
    simpa only [hw, Finset.sum_const, nsmul_eq_mul] using
      (mul_pos hcard (by norm_num : (0 : ℤ) < 2))
  have hcube : n ≤ (z + 1) ^ 3 := by
    calc
      n ≤ z * (z + 1) ^ 2 := hbound
      _ ≤ (z + 1) * (z + 1) ^ 2 := Nat.mul_le_mul_right _ (Nat.le_succ _)
      _ = (z + 1) ^ 3 := by ring
  exact ⟨z, z + 1, hz, by omega, hcube, hbound, hpos⟩

/-- Check the prime certificate by Lucas's criterion and kernel reduction of modular powers. -/
private theorem dstar_prime_of_lucas {p a : ℕ} {factors : List ℕ}
    (hp : 1 < p) (hprod : factors.prod = p - 1)
    (hprime : ∀ r ∈ factors, Nat.Prime r)
    (hfull : Nat.powMod a (p - 1) p = 1)
    (hproper : ∀ r ∈ factors, Nat.powMod a ((p - 1) / r) p ≠ 1) : Nat.Prime p := by
  have castPow (k : ℕ) : ((Nat.powMod a k p : ℕ) : ZMod p) = (a : ZMod p)^k := by
    rw [Nat.powMod_def, ZMod.natCast_mod, Nat.cast_pow]
  refine lucas_primality p (a : ZMod p) ?_ ?_
  · simpa only [castPow, Nat.cast_one] using congrArg (fun x : ℕ => (x : ZMod p)) hfull
  · intro r hr hdiv heq
    have hmem : r ∈ factors := by
      apply mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hr)
      · exact fun t ht => Nat.prime_iff.mp (hprime t ht)
      · rwa [hprod]
    have hcast : ((Nat.powMod a ((p - 1) / r) p : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      simpa only [castPow, Nat.cast_one] using heq
    have hm := (ZMod.natCast_eq_natCast_iff _ _ _).mp hcast
    have hlt : Nat.powMod a ((p - 1) / r) p < p := by
      rw [Nat.powMod_def]
      exact Nat.mod_lt _ (by omega)
    exact hproper r hmem (Nat.ModEq.eq_of_lt_of_lt hm hlt hp)

section
set_option maxRecDepth 10000

private theorem dstar_prime_55229 : Nat.Prime 55229 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 2, 13807]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide

private theorem dstar_prime_162011 : Nat.Prime 162011 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 5, 17, 953]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_5624461 : Nat.Prime 5624461 := by
  refine dstar_prime_of_lucas (a := 7)
    (factors := [2, 2, 3, 3, 5, 31247]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_15924371 : Nat.Prime 15924371 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 5, 7, 11, 20681]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_17026637 : Nat.Prime 17026637 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 2, 11, 11, 127, 277]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_42393521 : Nat.Prime 42393521 := by
  refine dstar_prime_of_lucas (a := 3)
    (factors := [2, 2, 2, 2, 5, 13, 40763]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_56535509 : Nat.Prime 56535509 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 2, 1327, 10651]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_157479667 : Nat.Prime 157479667 := by
  refine dstar_prime_of_lucas (a := 5)
    (factors := [2, 3, 23, 263, 4339]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_2731697863 : Nat.Prime 2731697863 := by
  refine dstar_prime_of_lucas (a := 3)
    (factors := [2, 3, 29, 977, 16069]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_5312954681 : Nat.Prime 5312954681 := by
  refine dstar_prime_of_lucas (a := 3)
    (factors := [2, 2, 2, 5, 11, 89, 211, 643]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_4090975104371 : Nat.Prime 4090975104371 := by
  refine dstar_prime_of_lucas (a := 10)
    (factors := [2, 5, 7, 11, 5312954681]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_5312954681 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_1692047377326563 : Nat.Prime 1692047377326563 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 521, 9437, 10399, 16547]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_117647058823529329 : Nat.Prime 117647058823529329 := by
  refine dstar_prime_of_lucas (a := 7)
    (factors := [2, 2, 2, 2, 3, 3, 61, 5393, 15329, 162011]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_162011 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_3999999999999994027 : Nat.Prime 3999999999999994027 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 3, 89, 2399, 55229, 56535509]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_55229 | exact dstar_prime_56535509 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_3999999999999994933 : Nat.Prime 3999999999999994933 := by
  refine dstar_prime_of_lucas (a := 5)
    (factors := [2, 2, 3, 197, 1692047377326563]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_1692047377326563 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_3999999999999997153 : Nat.Prime 3999999999999997153 := by
  refine dstar_prime_of_lucas (a := 7)
    (factors := [2, 2, 2, 2, 2, 3, 3, 17, 61, 5393, 15329, 162011]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_162011 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_3999999999999997187 : Nat.Prime 3999999999999997187 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 17, 117647058823529329]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
      <;> first | exact dstar_prime_117647058823529329 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> decide

private theorem dstar_prime_3999999999999997703 : Nat.Prime 3999999999999997703 := by
  refine dstar_prime_of_lucas (a := 5)
    (factors := [2, 37, 73, 181, 4090975104371]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_4090975104371 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_3999999999999998171 : Nat.Prime 3999999999999998171 := by
  refine dstar_prime_of_lucas (a := 6)
    (factors := [2, 5, 11, 23, 31, 31, 31, 337, 157479667]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_157479667 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_3999999999999998369 : Nat.Prime 3999999999999998369 := by
  refine dstar_prime_of_lucas (a := 3)
    (factors := [2, 2, 2, 2, 2, 11, 11, 37, 277, 17921, 5624461]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_5624461 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_3999999999999998803 : Nat.Prime 3999999999999998803 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 3, 229, 8147, 8429, 42393521]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_42393521 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_3999999999999998867 : Nat.Prime 3999999999999998867 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 43, 17026637, 2731697863]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_17026637 | exact dstar_prime_2731697863 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide

private theorem dstar_prime_3999999999999999883 : Nat.Prime 3999999999999999883 := by
  refine dstar_prime_of_lucas (a := 2)
    (factors := [2, 3, 19, 157, 547, 25657, 15924371]) (by decide) (by decide) ?_ (by decide) ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      <;> first | exact dstar_prime_15924371 | norm_num
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end

/-- For a boundary input `4000000000000000020 + 30 * j`, each offset `b` yields the
same large summand `4000000000000000020 - b` and a small summand `b + 30 * j`. -/
private def dstarBoundaryOffsets : List ℕ :=
  [137, 1217, 1849, 2867, 2833, 5993, 5087, 1153, 2317, 1651]

private theorem dstar_boundary_large_prime {b : ℕ} (hb : b ∈ dstarBoundaryOffsets) :
    b ≤ 6000 ∧ Nat.Prime (4000000000000000020 - b) := by
  simp only [dstarBoundaryOffsets, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, dstar_prime_3999999999999999883⟩
  · exact ⟨by decide, dstar_prime_3999999999999998803⟩
  · exact ⟨by decide, dstar_prime_3999999999999998171⟩
  · exact ⟨by decide, dstar_prime_3999999999999997153⟩
  · exact ⟨by decide, dstar_prime_3999999999999997187⟩
  · exact ⟨by decide, dstar_prime_3999999999999994027⟩
  · exact ⟨by decide, dstar_prime_3999999999999994933⟩
  · exact ⟨by decide, dstar_prime_3999999999999998867⟩
  · exact ⟨by decide, dstar_prime_3999999999999997703⟩
  · exact ⟨by decide, dstar_prime_3999999999999998369⟩

private def dstarTrialPrimes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
   59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131,
   137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]

private def dstarTrialPrimeProduct : ℕ :=
  7799922041683461553249199106329813876687996789903550945093032474868511536164700810

private theorem dstar_trial_prime_product_eq :
    dstarTrialPrimes.prod = dstarTrialPrimeProduct := by
  decide +kernel

private def dstarSmallPrimeTest (p : ℕ) : Bool :=
  if p < 200 then decide p.Prime else decide (p.Coprime dstarTrialPrimeProduct)

set_option maxRecDepth 35000 in
private theorem dstar_trial_primes_complete :
    (List.range 200).all
      (fun q => !(decide q.Prime) || decide (q ∈ dstarTrialPrimes)) = true := by
  decide +kernel

private theorem dstar_small_prime_of_check {p : ℕ} (hp : p < 40000)
    (htest : dstarSmallPrimeTest p = true) : p.Prime := by
  by_cases hsmall : p < 200
  · exact of_decide_eq_true (by simpa only [dstarSmallPrimeTest, ite_eq_left hsmall] using htest)
  have hcop : p.Coprime dstarTrialPrimeProduct :=
    of_decide_eq_true (by simpa only [dstarSmallPrimeTest, ite_eq_right hsmall] using htest)
  rw [Nat.prime_def_le_sqrt]
  refine ⟨(by decide : 2 ≤ (200 : ℕ)).trans (le_of_not_gt hsmall), ?_⟩
  intro d hd hds hdvd
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (ne_of_gt (Nat.lt_of_succ_le hd))
  have hqle := Nat.le_of_dvd (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hd) hqd
  have hsqrt : Nat.sqrt p < 200 := Nat.sqrt_lt.mpr hp
  have hqlt := (hqle.trans hds).trans_lt hsqrt
  have hqmem : q ∈ dstarTrialPrimes := by
    have hqcheck := List.all_eq_true.mp dstar_trial_primes_complete q (List.mem_range.mpr hqlt)
    have hqdec : decide q.Prime = true := decide_eq_true hq
    simpa [hqdec] using hqcheck
  have hqprod : q ∣ dstarTrialPrimeProduct := by
    rw [← dstar_trial_prime_product_eq]
    exact List.dvd_prod hqmem
  exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hcop (hqd.trans hdvd) hqprod)

private def dstarBoundaryCheck (j : ℕ) : Bool :=
  dstarBoundaryOffsets.any (fun b => dstarSmallPrimeTest (b + 30 * j))

private def dstarBoundaryGroupCheck (g : ℕ) : Bool :=
  (List.range 84).all (fun i => dstarBoundaryCheck (84 * g + i))

section
set_option maxRecDepth 35000

private theorem dstar_boundary_group_0 : dstarBoundaryGroupCheck 0 = true := by
  decide +kernel

private theorem dstar_boundary_group_1 : dstarBoundaryGroupCheck 1 = true := by
  decide +kernel

private theorem dstar_boundary_group_2 : dstarBoundaryGroupCheck 2 = true := by
  decide +kernel

private theorem dstar_boundary_group_3 : dstarBoundaryGroupCheck 3 = true := by
  decide +kernel

private theorem dstar_boundary_group_4 : dstarBoundaryGroupCheck 4 = true := by
  decide +kernel

private theorem dstar_boundary_group_5 : dstarBoundaryGroupCheck 5 = true := by
  decide +kernel

private theorem dstar_boundary_group_6 : dstarBoundaryGroupCheck 6 = true := by
  decide +kernel

private theorem dstar_boundary_group_7 : dstarBoundaryGroupCheck 7 = true := by
  decide +kernel

private theorem dstar_boundary_group_8 : dstarBoundaryGroupCheck 8 = true := by
  decide +kernel

private theorem dstar_boundary_group_9 : dstarBoundaryGroupCheck 9 = true := by
  decide +kernel

private theorem dstar_boundary_group_10 : dstarBoundaryGroupCheck 10 = true := by
  decide +kernel

private theorem dstar_boundary_group_11 : dstarBoundaryGroupCheck 11 = true := by
  decide +kernel

private theorem dstar_boundary_group_12 : dstarBoundaryGroupCheck 12 = true := by
  decide +kernel

end

private theorem dstar_boundary_group_checks (g : ℕ) (hg : g < 13) :
    dstarBoundaryGroupCheck g = true := by
  interval_cases g
  · exact dstar_boundary_group_0
  · exact dstar_boundary_group_1
  · exact dstar_boundary_group_2
  · exact dstar_boundary_group_3
  · exact dstar_boundary_group_4
  · exact dstar_boundary_group_5
  · exact dstar_boundary_group_6
  · exact dstar_boundary_group_7
  · exact dstar_boundary_group_8
  · exact dstar_boundary_group_9
  · exact dstar_boundary_group_10
  · exact dstar_boundary_group_11
  · exact dstar_boundary_group_12

private theorem dstar_boundary_small_prime (j : ℕ) (hj : j < 1092) :
    ∃ b ∈ dstarBoundaryOffsets, Nat.Prime (b + 30 * j) := by
  let group := j / 84
  let index := j % 84
  have hg : group < 13 := (Nat.div_lt_iff_lt_mul (by decide : 0 < (84 : ℕ))).2 hj
  have hi : index < 84 := Nat.mod_lt _ (by decide)
  have hgroup : (List.range 84).all (fun i => dstarBoundaryCheck (84 * group + i)) = true :=
    dstar_boundary_group_checks group hg
  have hcheck := List.all_eq_true.mp hgroup index (List.mem_range.mpr hi)
  have hj_eq : 84 * group + index = j := Nat.div_add_mod j 84
  rw [hj_eq] at hcheck
  obtain ⟨b, hb, hp⟩ := List.any_eq_true.mp hcheck
  have hb_le := (dstar_boundary_large_prime hb).1
  exact ⟨b, hb, dstar_small_prime_of_check (by omega) hp⟩

/-- The weighted-sieve statement for the multiples of thirty up to the finite boundary. -/
theorem finite_weighted_sieve_boundary_through_32768
    (n : ℕ) (hn : 4000000000000000000 < n) (h30 : 30 ∣ n) (hstop : n ≤ 4000000000000032768) :
    ∃ z y : ℕ, 2 < z ∧ z < y ∧ n ≤ y^3 ∧ n ≤ z * y^2 ∧
      0 < ∑ p ∈ (A n z).filter (fun p => 2 ≤ n - p), W z y (n - p) := by
  have hmod : n % 30 = 0 := Nat.mod_eq_zero_of_dvd h30
  let j := (n - 4000000000000000020) / 30
  have hj : j < 1092 := by dsimp only [j]; omega
  have hn_eq : n = 4000000000000000020 + 30 * j := by dsimp only [j]; omega
  obtain ⟨b, hb, hp⟩ := dstar_boundary_small_prime j hj
  obtain ⟨hb, hq⟩ := dstar_boundary_large_prime hb
  exact finite_weighted_sieve_of_prime_pair (z := 2000000)
    (by omega) hp hq (by omega) (by decide)
    (by norm_num) (by omega) (hstop.trans (by decide))

/-- Cover the first five multiples of thirty in the task's range. -/
theorem finite_weighted_sieve_first_five
    (n : ℕ) (hn : 4000000000000000000 < n) (h30 : 30 ∣ n)
    (hstop : n ≤ 4000000000000000140) :
    ∃ z y : ℕ, 2 < z ∧ z < y ∧ n ≤ y^3 ∧ n ≤ z * y^2 ∧
      0 < ∑ p ∈ (A n z).filter (fun p => 2 ≤ n - p), W z y (n - p) := by
  exact finite_weighted_sieve_boundary_through_32768 n hn h30 (hstop.trans (by decide))

private theorem dstar_exp_upper_bound :
    Real.exp (Real.exp (19 / 5)) < (27000000000000000000 : ℝ) := by
  have hsmall : Real.exp (19 / 20) < (25858 / 10000 : ℝ) := by
    refine lt_of_le_of_lt (Real.exp_bound' (x := (19 / 20 : ℝ)) (n := 10)
      (by norm_num) (by norm_num) (by decide)) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  have hinner : Real.exp (19 / 5) < (4471 / 100 : ℝ) := by
    calc
      Real.exp (19 / 5) = (Real.exp (19 / 20)) ^ 4 := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ ≤ (25858 / 10000 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le hsmall.le 4
      _ < _ := by norm_num
  have houter : Real.exp (4471 / 6400) < (20111 / 10000 : ℝ) := by
    refine lt_of_le_of_lt (Real.exp_bound' (x := (4471 / 6400 : ℝ)) (n := 10)
      (by norm_num) (by norm_num) (by decide)) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial_succ]
  calc
    _ < Real.exp (4471 / 100) := Real.exp_lt_exp.mpr hinner
    _ = (Real.exp (4471 / 6400)) ^ 64 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (20111 / 10000 : ℝ) ^ 64 := pow_le_pow_left₀ (Real.exp_pos _).le houter.le 64
    _ < (27000000000000000000 : ℝ) := by norm_num

private theorem dstar_goal_of_fixed_cutoff_nonempty (n : ℕ) (hn : 0 < n)
    (hX : (n : ℝ) < Real.exp (Real.exp (19 / 5)))
    (hS : ((A n 3000000).filter (fun p => 2 ≤ n - p)).Nonempty) :
    ∃ z : ℕ, 2 < z ∧
      let y := minSieveUpperCutoff n z
      let S := (A n z).filter (fun p => 2 ≤ n - p)
      let Q := ((Finset.Ico z y).filter Nat.Prime).filter (fun q => ¬ q ∣ n)
      ∃ T : ℕ, 2 ≤ T ∧ T ≤ y ∧
        (∑ q ∈ Q, ((S.filter (fun p => q ∣ n - p)).card : ℤ)) +
          (∑ q ∈ Q.filter (fun q => q < T), ((S.filter (fun p => q ^ 2 ∣ n - p)).card : ℤ)) +
          dstarSquareTailBudget n y T (Q.filter (fun q => T ≤ q)) <
        2 * (S.card : ℤ) := by
  have hnUpper : n < 27000000000000000000 := by
    exact_mod_cast hX.trans dstar_exp_upper_bound
  let y := minSieveUpperCutoff n 3000000
  have hy : y = 3000001 := by
    apply le_antisymm
    · exact minSieveUpperCutoff_le n 3000000 3000001 hn (by decide) (by decide)
        (hnUpper.le.trans (by decide))
    · unfold y minSieveUpperCutoff
      exact le_max_left _ _
  let S := (A n 3000000).filter (fun p => 2 ≤ n - p)
  let Q := ((Finset.Ico 3000000 y).filter Nat.Prime).filter (fun q => ¬ q ∣ n)
  have hP : (Finset.Ico 3000000 y).filter Nat.Prime = ∅ := by
    rw [hy, show (3000001 : ℕ) = 3000000 + 1 by decide, Nat.Ico_succ_singleton]
    have hcomp : ¬ Nat.Prime 3000000 := by
      intro hp
      have h2 : (2 : ℕ) ∣ 3000000 := ⟨1500000, by decide⟩
      rcases (Nat.dvd_prime hp).mp h2 with h | h <;> norm_num at h
    simp [hcomp]
  have hQ : Q = ∅ := by
    unfold Q
    rw [hP]
    simp
  have hSpos : (0 : ℤ) < (S.card : ℤ) := by
    exact_mod_cast (Finset.card_pos.mpr hS)
  have hy2 : 2 ≤ y := by rw [hy]; decide
  refine ⟨3000000, by decide, y, hy2, le_rfl, ?_⟩
  change (∑ q ∈ Q, ((S.filter (fun p => q ∣ n - p)).card : ℤ)) +
    (∑ q ∈ Q.filter (fun q => q < y), ((S.filter (fun p => q ^ 2 ∣ n - p)).card : ℤ)) +
    dstarSquareTailBudget n y y (Q.filter (fun q => y ≤ q)) <
      2 * (S.card : ℤ)
  simpa [hQ, dstarSquareTailBudget] using (mul_pos (by decide : (0 : ℤ) < 2) hSpos)

theorem finite_weighted_sieve_two_factor_dstar :
  ∀ n : ℕ, 4000000000000000000 < n → 30 ∣ n → (n:ℝ) < Real.exp (Real.exp (19/5)) →
  ∃ z y : ℕ, 2 < z ∧ z < y ∧ n ≤ y^3 ∧ n ≤ z * y^2 ∧
  0 < ∑ p ∈ Finset.filter (fun p => 2 ≤ n - p) (A n z), W z y (n - p) := by
  intro n hn h30 hX
  by_cases hfirst : n ≤ 4000000000000032768
  · exact finite_weighted_sieve_boundary_through_32768 n hn h30 hfirst
  have hnext : 4000000000000032780 ≤ n := by
    have hmod : n % 30 = 0 := Nat.mod_eq_zero_of_dvd h30
    omega
  have hn_pos : 0 < n := (by decide : 0 < (4000000000000000000 : ℕ)).trans hn
  have hS : ((A n 3000000).filter (fun p => 2 ≤ n - p)).Nonempty := by
    sorry
  obtain ⟨z, hz, hbudget⟩ := dstar_goal_of_fixed_cutoff_nonempty n hn_pos hX hS
  have hz_pos : 0 < z := (by decide : 0 < (2 : ℕ)).trans hz
  have hzy := (minSieveUpperCutoff_spec n z hn_pos hz_pos).1
  apply (finite_weighted_sieve_two_factor_iff_count_margin n hn_pos).2
  exact ⟨z, hz, (finite_weighted_sieve_count_margin_iff_wheel_budget n z
    (minSieveUpperCutoff n z) h30 (le_of_lt (hz.trans hzy))).2 hbudget⟩
