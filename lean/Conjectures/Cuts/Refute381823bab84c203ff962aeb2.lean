import Mathlib
import Conjectures.Goldbach.FareyCubeSqrtDensityRatio

/-!
Refutation of `L-goldbach-cut-c88cf0e7c2b48ab83875a8d4` (the two-sided cube-root-rough
semiprime pairing upper bound `(2/25) * V(n)` from PR #4456).

Averaging over even `n ∈ (2000m, 2020m]` (`X = 2000m`):
- Lower bound: counting pairs `(u, v)` of cube-root-rough semiprimes with `u ∈ (690m, 1310m]`
  and `v ∈ (2000m - u, 2020m - u]` across 16 prime-factor exponent bands in `[0.335, 0.495]`
  via Mathlib's `Nat.isEquivalent_primeCounting` and Mertens' second theorem from
  `Conjectures.Goldbach.FareyCubeSqrtDensityRatio` gives
  `∑_{n ∈ E} |T(n)| ≥ (63/100)^2 * 12400 * m^2 / (log X)^2 = 4921.56 * m^2 / (log X)^2`.
- Upper bound: expanding the local sieve correction on primes `2 < p ≤ ⌊(log X)/4⌋` via
  `Finset.prod_one_add`, bounding primorials with `Chebyshev.theta_le_log4_mul_x`, and
  bounding `∏_{2 < p ≤ √X} (1 - 1/p)^2 ≤ 16 / (log X)^2` via the harmonic-series Euler
  product gives `(2/25) * ∑_{n ∈ E} V(n) ≤ 4401 * m^2 / (log X)^2`, contradicting the claim.
-/

namespace RefuteTwoSidedSemiprimePairing

open Finset Filter Real
open ErdosStraus.PrimeEstimates.Mertens
open scoped BigOperators Topology Classical

/-! ### Part 1: Upper bound on the averaged terminal sieve volume -/

private theorem log_succ_le_harmonic (z : ℕ) :
    Real.log ((z : ℝ) + 1) ≤ ∑ k ∈ Finset.Icc 1 z, ((k : ℝ)⁻¹) := by
  induction z with
  | zero => simp
  | succ z ih =>
    have hnotmem : z + 1 ∉ Finset.Icc 1 z := by simp
    have hIcc : Finset.Icc 1 (z + 1) = insert (z + 1) (Finset.Icc 1 z) := by
      ext k; simp only [mem_Icc, mem_insert]; omega
    rw [hIcc, sum_insert hnotmem]
    have hz1 : (0 : ℝ) < (z : ℝ) + 1 := by positivity
    have hz2 : (0 : ℝ) < (z : ℝ) + 2 := by positivity
    have hstep : Real.log ((z : ℝ) + 2) - Real.log ((z : ℝ) + 1) ≤ (((z + 1 : ℕ) : ℝ))⁻¹ := by
      rw [← Real.log_div hz2.ne' hz1.ne']
      have hle := Real.log_le_sub_one_of_pos (div_pos hz2 hz1)
      have hEq : ((z : ℝ) + 2) / ((z : ℝ) + 1) - 1 = (((z + 1 : ℕ) : ℝ))⁻¹ := by
        push_cast; field_simp; ring
      linarith
    push_cast at hstep ⊢
    have hadd : (z : ℝ) + 1 + 1 = (z : ℝ) + 2 := by ring
    rw [hadd]
    linarith

private theorem prod_primes_dvd {s : Finset ℕ} {n : ℕ}
    (hprime : ∀ p ∈ s, p.Prime) (hdvd : ∀ p ∈ s, p ∣ n) : (∏ p ∈ s, p) ∣ n := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    have hpa : a.Prime := hprime a (mem_insert_self a t)
    have hcop : Nat.Coprime a (∏ p ∈ t, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hpa (hprime p (mem_insert_of_mem hp))).mpr (fun h => ha (h ▸ hp))
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd a (mem_insert_self a t))
      (ih (fun p hp => hprime p (mem_insert_of_mem hp)) (fun p hp => hdvd p (mem_insert_of_mem hp)))

private theorem prod_primesUpTo_factorization {z k : ℕ} (hk1 : 1 ≤ k) (hkz : k ≤ z) :
    ∏ p ∈ primesUpTo z, p ^ (k.factorization p) = k := by
  have hk0 : k ≠ 0 := by omega
  have hsub : k.primeFactors ⊆ primesUpTo z := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    exact mem_primesUpTo.mpr ⟨hp.1, (Nat.le_of_dvd (by omega) hp.2.1).trans hkz⟩
  rw [← Finset.prod_subset hsub]
  · exact (Nat.prod_primeFactors_pow_factorization hk0).symm
  · intro p _ hpnot
    have hzero : k.factorization p = 0 := by
      rw [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] at hpnot
      exact hpnot
    simp [hzero]

private theorem harmonic_le_inv_prime_prod (z : ℕ) :
    (∑ k ∈ Finset.Icc 1 z, ((k : ℝ)⁻¹)) ≤
      (∏ p ∈ primesUpTo z, (1 - 1 / (p : ℝ)))⁻¹ := by
  let P := primesUpTo z
  let t : ℕ → Finset ℕ := fun _ => Finset.range (z + 1)
  have hgeom : ∏ p ∈ P, ∑ j ∈ t p, ((p : ℝ)⁻¹) ^ j ≤
      (∏ p ∈ P, (1 - 1 / (p : ℝ)))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_le_prod₀
    · intro p _; exact Finset.sum_nonneg fun _ _ => by positivity
    · intro p hp
      have hp_prime : p.Prime := (mem_primesUpTo.mp hp).1
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
      have hr0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by linarith)
      have hr1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one_iff₀.mpr (Or.inr (by linarith)))
      have hne : (p : ℝ)⁻¹ ≠ 1 := hr1.ne
      rw [geom_sum_eq hne]
      have hden : 0 < 1 - (p : ℝ)⁻¹ := by linarith
      have hnum : 1 - ((p : ℝ)⁻¹) ^ (z + 1) ≤ 1 := by
        linarith [pow_nonneg hr0.le (z + 1)]
      have hrew : (((p : ℝ)⁻¹) ^ (z + 1) - 1) / ((p : ℝ)⁻¹ - 1) =
          (1 - ((p : ℝ)⁻¹) ^ (z + 1)) / (1 - (p : ℝ)⁻¹) := by
        rw [← neg_div_neg_eq]
        congr 1 <;> ring
      rw [hrew, one_div]
      exact (div_le_div_of_nonneg_right hnum hden.le).trans_eq (one_div _)
  rw [Finset.prod_sum] at hgeom
  refine le_trans ?_ hgeom
  let φ : ℕ → (∀ p ∈ P, ℕ) := fun k p _ => k.factorization p
  have hmem : ∀ k ∈ Finset.Icc 1 z, φ k ∈ P.pi t := by
    intro k hk
    obtain ⟨hk1, hkz⟩ := Finset.mem_Icc.mp hk
    rw [Finset.mem_pi]
    intro p hp
    dsimp [φ, t]
    rw [Finset.mem_range]
    have hp_prime : p.Prime := (mem_primesUpTo.mp hp).1
    have hpow1 : k.factorization p < 2 ^ (k.factorization p) := Nat.lt_two_pow_self
    have hpow2 : 2 ^ (k.factorization p) ≤ p ^ (k.factorization p) :=
      Nat.pow_le_pow_left hp_prime.two_le _
    have hpow3 : p ^ (k.factorization p) ≤ k := Nat.ordProj_le p (by omega)
    omega
  have hval : ∀ k ∈ Finset.Icc 1 z,
      (∏ x ∈ P.attach, ((x.1 : ℝ)⁻¹) ^ (φ k x.1 x.2)) = ((k : ℝ)⁻¹) := by
    intro k hk
    obtain ⟨hk1, hkz⟩ := Finset.mem_Icc.mp hk
    have h1 : (∏ x ∈ P.attach, ((x.1 : ℝ)⁻¹) ^ (φ k x.1 x.2)) =
        ∏ p ∈ P, ((p : ℝ)⁻¹) ^ (k.factorization p) := by
      simpa [φ] using Finset.prod_attach P (fun p => ((p : ℝ)⁻¹) ^ (k.factorization p))
    rw [h1]
    have h2 : (∏ p ∈ P, ((p : ℝ)⁻¹) ^ (k.factorization p)) =
        (∏ p ∈ P, (p : ℝ) ^ (k.factorization p))⁻¹ := by
      simp_rw [inv_pow, Finset.prod_inv_distrib]
    rw [h2]
    congr 1
    have h3 : (∏ p ∈ P, (p : ℝ) ^ (k.factorization p)) =
        ((∏ p ∈ P, p ^ (k.factorization p) : ℕ) : ℝ) := by
      push_cast; rfl
    rw [h3, prod_primesUpTo_factorization hk1 hkz]
  have hinj : Set.InjOn φ (Finset.Icc 1 z : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ heq
    obtain ⟨h1a, h1b⟩ := Finset.mem_Icc.mp hk₁
    obtain ⟨h2a, h2b⟩ := Finset.mem_Icc.mp hk₂
    have hprod1 := prod_primesUpTo_factorization h1a h1b
    have hprod2 := prod_primesUpTo_factorization h2a h2b
    rw [← hprod1, ← hprod2]
    apply Finset.prod_congr rfl
    intro p hp
    have := congrFun (congrFun heq p) hp
    dsimp [φ] at this
    rw [this]
  calc
    (∑ k ∈ Finset.Icc 1 z, ((k : ℝ)⁻¹))
        = ∑ k ∈ Finset.Icc 1 z, ∏ x ∈ P.attach, ((x.1 : ℝ)⁻¹) ^ (φ k x.1 x.2) :=
      Finset.sum_congr rfl fun k hk => (hval k hk).symm
    _ = ∑ f ∈ (Finset.Icc 1 z).image φ, ∏ x ∈ P.attach, ((x.1 : ℝ)⁻¹) ^ (f x.1 x.2) :=
      (Finset.sum_image (f := fun f : (∀ p ∈ P, ℕ) => ∏ x ∈ P.attach, ((x.1 : ℝ)⁻¹) ^ (f x.1 x.2))
        (fun a ha b hb h => hinj ha hb h)).symm
    _ ≤ ∑ f ∈ P.pi t, ∏ x ∈ P.attach, ((x.1 : ℝ)⁻¹) ^ (f x.1 x.2) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro f hf
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hf
        exact hmem k hk
      · intro f _ _; exact Finset.prod_nonneg fun _ _ => by positivity

private theorem odd_prime_prod_sq_le {X : ℕ} (hX : 4 ≤ X) :
    (∏ p ∈ (primesUpTo X.sqrt).erase 2, (1 - 1 / (p : ℝ)) ^ 2) ≤
      16 / (Real.log (X : ℝ)) ^ 2 := by
  let z := X.sqrt
  have hz2 : 2 ≤ z := by
    have : 2 * 2 ≤ X := by omega
    exact Nat.le_sqrt.mpr this
  have h2mem : 2 ∈ primesUpTo z := mem_primesUpTo.mpr ⟨Nat.prime_two, hz2⟩
  have hprod_pos : 0 < ∏ p ∈ primesUpTo z, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (mem_primesUpTo.mp hp).1.two_le
    rw [sub_pos, div_lt_one (by linarith)]
    linarith
  have hlogz : 0 < Real.log ((z : ℝ) + 1) :=
    Real.log_pos (by exact_mod_cast (show 1 < z + 1 by omega))
  have hmain : (∏ p ∈ primesUpTo z, (1 - 1 / (p : ℝ))) ≤ (Real.log ((z : ℝ) + 1))⁻¹ := by
    have h1 := (log_succ_le_harmonic z).trans (harmonic_le_inv_prime_prod z)
    exact (le_inv_comm₀ hlogz hprod_pos).mp h1
  have hsplit := Finset.mul_prod_erase (primesUpTo z) (fun p : ℕ => 1 - 1 / (p : ℝ)) h2mem
  have hodd : (∏ p ∈ (primesUpTo z).erase 2, (1 - 1 / (p : ℝ))) ≤
      2 / Real.log ((z : ℝ) + 1) := by
    have htwo : (1 : ℝ) - 1 / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
    rw [htwo] at hsplit
    have hrew : ∏ p ∈ (primesUpTo z).erase 2, (1 - 1 / (p : ℝ)) =
        2 * ∏ p ∈ primesUpTo z, (1 - 1 / (p : ℝ)) := by linarith
    rw [hrew, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hmain (by norm_num)
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  have hlogX_pos : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hsqrt_lt : (X : ℝ) < ((z : ℝ) + 1) ^ 2 := by
    have hnat : X < (z + 1) * (z + 1) := Nat.lt_succ_sqrt X
    have hreal : (X : ℝ) < ((z + 1 : ℕ) : ℝ) * ((z + 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hreal
    linarith [sq ((z : ℝ) + 1)]
  have hlog_cmp : Real.log (X : ℝ) ≤ 2 * Real.log ((z : ℝ) + 1) := by
    have h := Real.log_le_log hXpos hsqrt_lt.le
    rw [Real.log_pow] at h
    simpa using h
  have hodd2 : (∏ p ∈ (primesUpTo z).erase 2, (1 - 1 / (p : ℝ))) ≤
      4 / Real.log (X : ℝ) := by
    apply hodd.trans
    rw [div_le_div_iff₀ hlogz hlogX_pos]
    linarith
  have hnonneg : 0 ≤ ∏ p ∈ (primesUpTo z).erase 2, (1 - 1 / (p : ℝ)) :=
    Finset.prod_nonneg fun p hp => by
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (mem_primesUpTo.mp (mem_of_mem_erase hp)).1.two_le
      have : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      linarith
  calc
    (∏ p ∈ (primesUpTo z).erase 2, (1 - 1 / (p : ℝ)) ^ 2)
        = (∏ p ∈ (primesUpTo z).erase 2, (1 - 1 / (p : ℝ))) ^ 2 := by
          rw [Finset.prod_pow]
    _ ≤ (4 / Real.log (X : ℝ)) ^ 2 := pow_le_pow_left₀ hnonneg hodd2 2
    _ = 16 / (Real.log (X : ℝ)) ^ 2 := by ring

private theorem totient_div_eq_prod {n : ℕ} (hn : 0 < n) :
    (n.totient : ℝ) / (n : ℝ) = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have hq := Nat.totient_eq_mul_prod_factors n
  have hr : (n.totient : ℝ) = (n : ℝ) * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
    have hcast := congrArg (Rat.cast (K := ℝ)) hq
    push_cast at hcast
    simpa only [one_div] using hcast
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hr, mul_div_cancel_left₀ _ hn0]

private theorem odd_prime_factor_id {p : ℕ} (hp : 3 ≤ p) :
    (1 - 1 / (p : ℝ)) = (1 - 2 / (p : ℝ)) * (1 + 1 / ((p : ℝ) - 2)) := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

private theorem odd_prime_cancel_id {p : ℕ} (hp : 3 ≤ p) :
    (1 - 2 / (p : ℝ)) * (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) = (1 - 1 / (p : ℝ)) ^ 2 := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp2 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp
  ring

private theorem odd_prime_one_sub_two_le_sq {p : ℕ} (hp : 3 ≤ p) :
    1 - 2 / (p : ℝ) ≤ (1 - 1 / (p : ℝ)) ^ 2 := by
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 : (1 - 1 / (p : ℝ)) ^ 2 - (1 - 2 / (p : ℝ)) = (1 / (p : ℝ)) ^ 2 := by ring
  nlinarith [sq_nonneg (1 / (p : ℝ))]

private theorem odd_prime_ge_three {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le; omega

private theorem x4_pointwise_le {m n M : ℕ} (hm : 3 ≤ m)
    (hlo : 2000 * m < n) (hhi : n ≤ 2020 * m) (heven : Even n)
    (hM : M ≤ (2000 * m).sqrt) :
    let X := 2000 * m
    let Pz := (primesUpTo X.sqrt).erase 2
    let PM := (primesUpTo M).erase 2
    let x1 := Finset.Icc ((n + 2) / 3) ((2 * n) / 3)
    let x2 := (Finset.Icc 2 n.sqrt).filter Nat.Prime
    let x4 := ((x1.card : ℝ) * (n.totient : ℝ) / (n : ℝ)) *
      ∏ p ∈ x2.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))
    x4 ≤ ((674 * m : ℕ) : ℝ) * (1 / 2) *
      (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
      (∏ p ∈ PM.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) *
      (∏ p ∈ (Pz \ PM).filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) := by
  intro X Pz PM x1 x2 x4
  have hn0 : 0 < n := by omega
  have hcard : x1.card ≤ 674 * m := by
    dsimp [x1]
    rw [Nat.card_Icc]
    omega
  have hcardR : (x1.card : ℝ) ≤ ((674 * m : ℕ) : ℝ) := by exact_mod_cast hcard
  have h2dvd : 2 ∣ n := even_iff_two_dvd.mp heven
  have h2mem : 2 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, hn0.ne'⟩
  have htot : (n.totient : ℝ) / (n : ℝ) =
      (1 / 2 : ℝ) * ∏ p ∈ n.primeFactors.erase 2, (1 - 1 / (p : ℝ)) := by
    rw [totient_div_eq_prod hn0, ← Finset.mul_prod_erase _ _ h2mem]
    norm_num
  have hx2_eq : x2 = primesUpTo n.sqrt := by
    ext p
    simp only [x2, mem_filter, mem_Icc, mem_primesUpTo]
    exact ⟨fun ⟨⟨_, hle⟩, hp⟩ => ⟨hp, hle⟩, fun ⟨hp, hle⟩ => ⟨⟨hp.two_le, hle⟩, hp⟩⟩
  have hsub_ndvd : Pz.filter (fun p => ¬ p ∣ n) ⊆ x2.filter (fun p => ¬ p ∣ n) := by
    intro p hp
    rw [mem_filter] at hp ⊢
    rw [hx2_eq]
    have hmem := mem_primesUpTo.mp (mem_of_mem_erase hp.1)
    exact ⟨mem_primesUpTo.mpr ⟨hmem.1, hmem.2.trans (Nat.sqrt_le_sqrt (by omega))⟩, hp.2⟩
  have hsieve_le :
      (∏ p ∈ x2.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))) ≤
        ∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) := by
    rw [← Finset.prod_sdiff hsub_ndvd]
    have hnonneg : 0 ≤ ∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) := by
      apply Finset.prod_nonneg
      intro p hp
      have hp' := mem_primesUpTo.mp (mem_of_mem_erase (mem_filter.mp hp).1)
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast odd_prime_ge_three hp'.1 (ne_of_mem_erase (mem_filter.mp hp).1)
      have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      linarith
    have hrest_le : (∏ p ∈ x2.filter (fun p => ¬ p ∣ n) \ Pz.filter (fun p => ¬ p ∣ n),
        (1 - 2 / (p : ℝ))) ≤ 1 := by
      calc
        (∏ p ∈ x2.filter (fun p => ¬ p ∣ n) \ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)))
            ≤ ∏ _p ∈ x2.filter (fun p => ¬ p ∣ n) \ Pz.filter (fun p => ¬ p ∣ n), (1 : ℝ) := by
              apply Finset.prod_le_prod₀
              · intro p hp
                have hf := mem_filter.mp (Finset.mem_sdiff.mp hp).1
                rw [hx2_eq] at hf
                have hp_prime := (mem_primesUpTo.mp hf.1).1
                have hne2 : p ≠ 2 := fun h => hf.2 (h ▸ h2dvd)
                have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast odd_prime_ge_three hp_prime hne2
                have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
                linarith
              · intro p hp
                have hf := mem_filter.mp (Finset.mem_sdiff.mp hp).1
                rw [hx2_eq] at hf
                have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (mem_primesUpTo.mp hf.1).1.pos
                linarith [div_pos (by norm_num : (0 : ℝ) < 2) hp_pos]
        _ = 1 := by simp
    calc
      _ ≤ 1 * ∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hrest_le hnonneg
      _ = _ := one_mul _
  have hsub_dvd : Pz.filter (· ∣ n) ⊆ n.primeFactors.erase 2 := by
    intro p hp
    obtain ⟨hpz, hdvd⟩ := mem_filter.mp hp
    exact mem_erase.mpr ⟨ne_of_mem_erase hpz,
      Nat.mem_primeFactors.mpr ⟨(mem_primesUpTo.mp (mem_of_mem_erase hpz)).1, hdvd, hn0.ne'⟩⟩
  have htot_le :
      (∏ p ∈ n.primeFactors.erase 2, (1 - 1 / (p : ℝ))) ≤
        ∏ p ∈ Pz.filter (· ∣ n), (1 - 1 / (p : ℝ)) := by
    rw [← Finset.prod_sdiff hsub_dvd]
    have hnonneg : 0 ≤ ∏ p ∈ Pz.filter (· ∣ n), (1 - 1 / (p : ℝ)) := by
      apply Finset.prod_nonneg
      intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (mem_primesUpTo.mp (mem_of_mem_erase (mem_filter.mp hp).1)).1.two_le
      have : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
      linarith
    have hrest_le : (∏ p ∈ n.primeFactors.erase 2 \ Pz.filter (· ∣ n),
        (1 - 1 / (p : ℝ))) ≤ 1 := by
      calc
        (∏ p ∈ n.primeFactors.erase 2 \ Pz.filter (· ∣ n), (1 - 1 / (p : ℝ)))
            ≤ ∏ _p ∈ n.primeFactors.erase 2 \ Pz.filter (· ∣ n), (1 : ℝ) := by
              apply Finset.prod_le_prod₀
              · intro p hp
                have hp_prime := (Nat.mem_primeFactors.mp (mem_of_mem_erase (Finset.mem_sdiff.mp hp).1)).1
                have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp_prime.two_le
                have : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
                linarith
              · intro p hp
                have hp_prime := (Nat.mem_primeFactors.mp (mem_of_mem_erase (Finset.mem_sdiff.mp hp).1)).1
                have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
                linarith [div_pos (by norm_num : (0 : ℝ) < 1) hp_pos]
        _ = 1 := by simp
    calc
      _ ≤ 1 * ∏ p ∈ Pz.filter (· ∣ n), (1 - 1 / (p : ℝ)) :=
        mul_le_mul_of_nonneg_right hrest_le hnonneg
      _ = _ := one_mul _
  have hdvd_eq :
      (∏ p ∈ Pz.filter (· ∣ n), (1 - 1 / (p : ℝ))) =
        (∏ p ∈ Pz.filter (· ∣ n), (1 - 2 / (p : ℝ))) *
          (∏ p ∈ Pz.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpz := (mem_filter.mp hp).1
    exact odd_prime_factor_id (odd_prime_ge_three (mem_primesUpTo.mp (mem_of_mem_erase hpz)).1
      (ne_of_mem_erase hpz))
  have hcombine :
      (∏ p ∈ Pz.filter (· ∣ n), (1 - 2 / (p : ℝ))) *
        (∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))) =
        ∏ p ∈ Pz, (1 - 2 / (p : ℝ)) :=
    Finset.prod_filter_mul_prod_filter_not Pz (· ∣ n) _
  have hPM_sub : PM ⊆ Pz := by
    intro p hp
    exact mem_erase.mpr ⟨ne_of_mem_erase hp,
      mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp (mem_of_mem_erase hp)).1,
        (mem_primesUpTo.mp (mem_of_mem_erase hp)).2.trans hM⟩⟩
  have hsplit_corr :
      (∏ p ∈ Pz.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) =
        (∏ p ∈ PM.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) *
          (∏ p ∈ (Pz \ PM).filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) := by
    have hdisj : Disjoint (PM.filter (· ∣ n)) ((Pz \ PM).filter (· ∣ n)) :=
      Disjoint.mono (filter_subset _ _) (filter_subset _ _) disjoint_sdiff_self_right
    have hunion : PM.filter (· ∣ n) ∪ (Pz \ PM).filter (· ∣ n) = Pz.filter (· ∣ n) := by
      rw [← Finset.filter_union, Finset.union_sdiff_of_subset hPM_sub]
    rw [← Finset.prod_union hdisj, hunion]
  have hsieve_nonneg : 0 ≤ ∏ p ∈ x2.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) := by
    apply Finset.prod_nonneg
    intro p hp
    have hf := mem_filter.mp hp
    rw [hx2_eq] at hf
    have hp_prime := (mem_primesUpTo.mp hf.1).1
    have hne2 : p ≠ 2 := fun h => hf.2 (h ▸ h2dvd)
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast odd_prime_ge_three hp_prime hne2
    have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have htot_nonneg : 0 ≤ ∏ p ∈ n.primeFactors.erase 2, (1 - 1 / (p : ℝ)) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.mem_primeFactors.mp (mem_of_mem_erase hp)).1.two_le
    have : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hsieve_pz_nonneg : 0 ≤ ∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) :=
    hsieve_nonneg.trans hsieve_le
  have htot_pz_nonneg : 0 ≤ ∏ p ∈ Pz.filter (· ∣ n), (1 - 1 / (p : ℝ)) :=
    htot_nonneg.trans htot_le
  calc
    x4 = (x1.card : ℝ) * ((n.totient : ℝ) / (n : ℝ)) *
          ∏ p ∈ x2.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) := by
          dsimp [x4]; ring
    _ = (x1.card : ℝ) * ((1 / 2 : ℝ) * ∏ p ∈ n.primeFactors.erase 2, (1 - 1 / (p : ℝ))) *
          ∏ p ∈ x2.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) := by rw [htot]
    _ ≤ ((674 * m : ℕ) : ℝ) * ((1 / 2 : ℝ) * ∏ p ∈ Pz.filter (· ∣ n), (1 - 1 / (p : ℝ))) *
          ∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)) := by
          gcongr
    _ = ((674 * m : ℕ) : ℝ) * (1 / 2 : ℝ) *
          ((∏ p ∈ Pz.filter (· ∣ n), (1 - 2 / (p : ℝ))) *
            (∏ p ∈ Pz.filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ)))) *
          (∏ p ∈ Pz.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) := by
          rw [hdvd_eq]; ring
    _ = _ := by rw [hcombine, hsplit_corr]; ring

private theorem tail_correction_le {X n M : ℕ} (hM4 : 4 ≤ M) (hnpos : 0 < n) (hn : n ≤ 2 * X)
    (hsmall : Real.log ((2 * X : ℕ) : ℝ) / (((M : ℝ) - 1) * Real.log (M : ℝ)) ≤ 1 / 200) :
    let Pz := (primesUpTo X.sqrt).erase 2
    let PM := (primesUpTo M).erase 2
    (∏ p ∈ (Pz \ PM).filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) ≤ 101 / 100 := by
  intro Pz PM
  let T := (Pz \ PM).filter (· ∣ n)
  have hM_gt : ∀ p ∈ T, M < p := by
    intro p hp
    obtain ⟨hsd, _⟩ := mem_filter.mp hp
    obtain ⟨hpz, hnotM⟩ := Finset.mem_sdiff.mp hsd
    have hprime := (mem_primesUpTo.mp (mem_of_mem_erase hpz)).1
    have hne2 := ne_of_mem_erase hpz
    by_contra! hle
    exact hnotM (mem_erase.mpr ⟨hne2, mem_primesUpTo.mpr ⟨hprime, hle⟩⟩)
  have hdvd_prod : (∏ p ∈ T, p) ∣ n :=
    prod_primes_dvd
      (fun p hp => (mem_primesUpTo.mp (mem_of_mem_erase (Finset.mem_sdiff.mp (mem_filter.mp hp).1).1)).1)
      (fun p hp => (mem_filter.mp hp).2)
  have hprod_le : (∏ p ∈ T, p) ≤ 2 * X :=
    (Nat.le_of_dvd hnpos hdvd_prod).trans hn
  have hpow_le : M ^ T.card ≤ 2 * X := by
    calc
      M ^ T.card = ∏ _p ∈ T, M := by simp
      _ ≤ ∏ p ∈ T, p := Finset.prod_le_prod fun p hp => (hM_gt p hp).le
      _ ≤ 2 * X := hprod_le
  have hM_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hlogM_pos : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hcard_bound : (T.card : ℝ) * Real.log (M : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) := by
    have hpowR : ((M : ℝ) ^ T.card) ≤ ((2 * X : ℕ) : ℝ) := by exact_mod_cast hpow_le
    have hlog := Real.log_le_log (pow_pos hM_pos T.card) hpowR
    rwa [Real.log_pow] at hlog
  have hM1_pos : (0 : ℝ) < (M : ℝ) - 1 := by
    have : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
    linarith
  have hcard_div : (T.card : ℝ) / ((M : ℝ) - 1) ≤ 1 / 200 := by
    have h1 : (T.card : ℝ) ≤ Real.log ((2 * X : ℕ) : ℝ) / Real.log (M : ℝ) :=
      (le_div_iff₀ hlogM_pos).mpr hcard_bound
    calc
      (T.card : ℝ) / ((M : ℝ) - 1)
          ≤ (Real.log ((2 * X : ℕ) : ℝ) / Real.log (M : ℝ)) / ((M : ℝ) - 1) :=
            div_le_div_of_nonneg_right h1 hM1_pos.le
      _ = Real.log ((2 * X : ℕ) : ℝ) / (((M : ℝ) - 1) * Real.log (M : ℝ)) := by
            rw [div_div, mul_comm (Real.log (M : ℝ))]
      _ ≤ 1 / 200 := hsmall
  have hprod_exp : (∏ p ∈ T, (1 + 1 / ((p : ℝ) - 2))) ≤
      Real.exp ((T.card : ℝ) / ((M : ℝ) - 1)) := by
    calc
      (∏ p ∈ T, (1 + 1 / ((p : ℝ) - 2)))
          ≤ ∏ _p ∈ T, Real.exp (1 / ((M : ℝ) - 1)) := by
            apply Finset.prod_le_prod₀
            · intro p hp
              have hgt : (M : ℝ) < (p : ℝ) := by exact_mod_cast hM_gt p hp
              have hM4R : (4 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM4
              have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
              positivity
            · intro p hp
              have hgt : (M + 1 : ℕ) ≤ p := hM_gt p hp
              have hge : (M : ℝ) - 1 ≤ (p : ℝ) - 2 := by
                have hR : ((M + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by exact_mod_cast hgt
                push_cast at hR; linarith
              have hinv : 1 / ((p : ℝ) - 2) ≤ 1 / ((M : ℝ) - 1) :=
                one_div_le_one_div_of_le hM1_pos hge
              calc
                1 + 1 / ((p : ℝ) - 2) ≤ 1 + 1 / ((M : ℝ) - 1) := by linarith
                _ ≤ Real.exp (1 / ((M : ℝ) - 1)) := by
                  linarith [Real.add_one_le_exp (1 / ((M : ℝ) - 1))]
      _ = (Real.exp (1 / ((M : ℝ) - 1))) ^ T.card := by rw [Finset.prod_const]
      _ = Real.exp ((T.card : ℝ) * (1 / ((M : ℝ) - 1))) := by rw [← Real.exp_nat_mul]
      _ = Real.exp ((T.card : ℝ) / ((M : ℝ) - 1)) := by ring_nf
  have hexp_bound : Real.exp (1 / 200 : ℝ) ≤ 101 / 100 := by
    have h1 := Real.exp_bound (x := (1 / 200 : ℝ)) (n := 2) (by norm_num) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h1
    rw [abs_le] at h1
    norm_num at h1
    linarith [h1.2]
  exact hprod_exp.trans ((Real.exp_le_exp.mpr hcard_div).trans hexp_bound)

private theorem multiples_in_Ioc_le (m d : ℕ) (hd : 0 < d) (hodd : Odd d) :
    (((Finset.Ioc (2000 * m) (2020 * m)).filter (fun n => Even n ∧ d ∣ n)).card : ℝ) ≤
      (10 * m : ℝ) / (d : ℝ) + 1 := by
  have hcop : Nat.Coprime 2 d := Nat.prime_two.coprime_iff_not_dvd.mpr (by
    intro h; obtain ⟨k, rfl⟩ := hodd; omega)
  let S := (Finset.Ioc (2000 * m) (2020 * m)).filter (fun n => Even n ∧ d ∣ n)
  let K := Finset.Ioc (2000 * m / (2 * d)) (2020 * m / (2 * d))
  have hinj : S.card ≤ K.card := by
    apply Finset.card_le_card_of_injOn (fun n => n / (2 * d))
    · intro n hn
      obtain ⟨hI, he, hdvd⟩ := Finset.mem_filter.mp hn
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hI
      have h2d : (2 * d) ∣ n := hcop.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp he) hdvd
      obtain ⟨q, rfl⟩ := h2d
      dsimp only
      rw [Nat.mul_div_cancel_left q (by omega)]
      refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
      · exact (Nat.div_lt_iff_lt_mul (by omega)).mpr (by linarith)
      · exact Nat.le_div_iff_mul_le (by omega) |>.mpr (by linarith)
    · intro n₁ hn₁ n₂ hn₂ hq
      obtain ⟨_, he₁, hd₁⟩ := Finset.mem_filter.mp hn₁
      obtain ⟨_, he₂, hd₂⟩ := Finset.mem_filter.mp hn₂
      have h2d₁ := hcop.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp he₁) hd₁
      have h2d₂ := hcop.mul_dvd_of_dvd_of_dvd (even_iff_two_dvd.mp he₂) hd₂
      dsimp only at hq
      rw [← Nat.mul_div_cancel' h2d₁, ← Nat.mul_div_cancel' h2d₂, hq]
  have hKcard : K.card = 2020 * m / (2 * d) - 2000 * m / (2 * d) := Nat.card_Ioc _ _
  have hnat : (2 * d) * (2020 * m / (2 * d) - 2000 * m / (2 * d)) ≤ 20 * m + 2 * d := by
    have h1 := Nat.mul_div_le (2020 * m) (2 * d)
    have h2 := Nat.lt_mul_div_succ (2000 * m) (show 0 < 2 * d by omega)
    rw [Nat.mul_add, mul_one] at h2
    rw [Nat.mul_sub_left_distrib]
    omega
  have hreal : (2 * (d : ℝ)) * (K.card : ℝ) ≤ 20 * (m : ℝ) + 2 * (d : ℝ) := by
    rw [hKcard]
    have : ((2 * d * (2020 * m / (2 * d) - 2000 * m / (2 * d)) : ℕ) : ℝ) ≤
        ((20 * m + 2 * d : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at this
    linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hKbound : (K.card : ℝ) ≤ (10 * m : ℝ) / (d : ℝ) + 1 := by
    have hdiv : (K.card : ℝ) ≤ (20 * (m : ℝ) + 2 * (d : ℝ)) / (2 * (d : ℝ)) :=
      (le_div_iff₀ (by positivity)).mpr (by linarith)
    apply hdiv.trans_eq
    field_simp
    ring
  exact (show (S.card : ℝ) ≤ (K.card : ℝ) by exact_mod_cast hinj).trans hKbound

private theorem subset_prod_le_pow {M : ℕ} {s : Finset ℕ} (hs : s ⊆ (primesUpTo M).erase 2) :
    ((∏ p ∈ s, p : ℕ) : ℝ) ≤ Real.exp (Real.log 4 * (M : ℝ)) := by
  have hpos : (0 : ℝ) < ((∏ p ∈ s, p : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun p hp =>
      (mem_primesUpTo.mp (mem_of_mem_erase (hs hp))).1.pos
  rw [← Real.log_le_iff_le_exp hpos]
  have hcast : ((∏ p ∈ s, p : ℕ) : ℝ) = ∏ p ∈ s, (p : ℝ) := by push_cast; rfl
  rw [hcast, Real.log_prod (fun p hp => by
    exact_mod_cast (mem_primesUpTo.mp (mem_of_mem_erase (hs hp))).1.ne_zero)]
  have hsub : s ⊆ Nat.primesLE M := by
    intro p hp
    have hm := mem_primesUpTo.mp (mem_of_mem_erase (hs hp))
    exact Nat.mem_primesLE.mpr ⟨hm.2, hm.1⟩
  have htheta : ∑ p ∈ Nat.primesLE M, Real.log (p : ℝ) = Chebyshev.theta (M : ℝ) := by
    rw [Chebyshev.theta_eq_sum_primesLE, Nat.floor_natCast]
  calc
    (∑ p ∈ s, Real.log (p : ℝ))
        ≤ ∑ p ∈ Nat.primesLE M, Real.log (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
            Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_le)
    _ = Chebyshev.theta (M : ℝ) := htheta
    _ ≤ Real.log 4 * (M : ℝ) := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg M)

private theorem tendsto_mul_2000 : Tendsto (fun m : ℕ => ((2000 * m : ℕ) : ℝ)) atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by norm_num : (0 : ℝ) < 2000)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

private theorem sum_x4_upper :
    ∃ M₁ : ℕ, ∀ m : ℕ, M₁ ≤ m →
      let X := 2000 * m
      let E := (Finset.Ioc (2000 * m) (2020 * m)).filter Even
      let x1 := fun n : ℕ => Finset.Icc ((n + 2) / 3) ((2 * n) / 3)
      let x2 := fun z : ℕ => (Finset.Icc 2 z).filter Nat.Prime
      let x4 := fun n : ℕ => ((x1 n).card : ℝ) * (n.totient : ℝ) / (n : ℝ) *
        ∏ p ∈ (x2 n.sqrt).filter (fun p => ¬ p ∣ n), (1 - 2 / (p : ℝ))
      (2 / 25 : ℝ) * (∑ n ∈ E, x4 n) ≤
        4401 * ((m : ℝ) ^ 2) / (Real.log (X : ℝ)) ^ 2 := by
  have hlog_inf : Tendsto (fun m : ℕ => Real.log ((2000 * m : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_mul_2000
  have hloglog_inf : Tendsto (fun m : ℕ => Real.log (Real.log ((2000 * m : ℕ) : ℝ) / 8)) atTop atTop :=
    Real.tendsto_log_atTop.comp (hlog_inf.atTop_div_const (by norm_num : (0 : ℝ) < 8))
  have hrpow_small : Tendsto (fun m : ℕ =>
      ((2000 * m : ℕ) : ℝ) ^ (-(3 / 5 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < 3 / 5 by norm_num)).comp tendsto_mul_2000
  have hlog_div_sqrt : Tendsto (fun m : ℕ =>
      Real.log ((2000 * m : ℕ) : ℝ) / Real.sqrt ((2000 * m : ℕ) : ℝ)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have hr := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
      exact hr.tendsto_div_nhds_zero
    exact (h2.comp tendsto_mul_2000).congr fun m => by simp [Function.comp, Real.sqrt_eq_rpow]
  have hev : ∀ᶠ m : ℕ in atTop,
      3 ≤ m ∧
      40 ≤ Real.log ((2000 * m : ℕ) : ℝ) ∧
      4000 ≤ Real.log (Real.log ((2000 * m : ℕ) : ℝ) / 8) ∧
      ((2000 * m : ℕ) : ℝ) ^ (-(3 / 5 : ℝ)) ≤ 1 / 20000 ∧
      Real.log ((2000 * m : ℕ) : ℝ) / Real.sqrt ((2000 * m : ℕ) : ℝ) ≤ 1 := by
    filter_upwards [eventually_ge_atTop 3,
      hlog_inf.eventually (eventually_ge_atTop 40),
      hloglog_inf.eventually (eventually_ge_atTop 4000),
      hrpow_small.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1 / 20000)),
      hlog_div_sqrt.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))] with m h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp hev
  refine ⟨M₁, fun m hm => ?_⟩
  obtain ⟨hm3, hL40, hLL, hrpow, hLsqrt⟩ := hM₁ m hm
  intro X E x1 x2 x4
  have hX4 : 4 ≤ X := by dsimp [X]; omega
  have hXpos : (0 : ℝ) < (X : ℝ) := by positivity
  let L := Real.log (X : ℝ)
  have hLpos : 0 < L := by linarith
  let M := ⌊L / 4⌋₊
  have hM_ge4 : 4 ≤ M := by
    apply Nat.le_floor
    change (4 : ℝ) ≤ L / 4
    linarith
  have hM_le_L4 : (M : ℝ) ≤ L / 4 := Nat.floor_le (by positivity)
  have hM_gt_L8 : L / 8 ≤ (M : ℝ) := by
    have hlt := Nat.lt_floor_add_one (L / 4)
    change L / 4 < (M : ℝ) + 1 at hlt
    linarith
  have hM_sub1 : L / 10 ≤ (M : ℝ) - 1 := by linarith
  have hM_le_sqrt : M ≤ X.sqrt := by
    have h1 : (M : ℝ) ≤ Real.sqrt (X : ℝ) := by
      have hls : L ≤ Real.sqrt (X : ℝ) := by
        exact (div_le_one (Real.sqrt_pos.mpr hXpos)).mp hLsqrt
      linarith
    have h2 : (M : ℝ) ^ 2 ≤ (X : ℝ) := by
      calc
        (M : ℝ) ^ 2 ≤ (Real.sqrt (X : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (Nat.cast_nonneg M) h1 2
        _ = (X : ℝ) := Real.sq_sqrt hXpos.le
    have h3 : M * M ≤ X := by exact_mod_cast (by nlinarith : (M : ℝ) * (M : ℝ) ≤ (X : ℝ))
    exact Nat.le_sqrt.mpr h3
  have htail_small :
      Real.log ((2 * X : ℕ) : ℝ) / (((M : ℝ) - 1) * Real.log (M : ℝ)) ≤ 1 / 200 := by
    have hlog2X : Real.log ((2 * X : ℕ) : ℝ) ≤ 2 * L := by
      push_cast
      rw [Real.log_mul (by norm_num) hXpos.ne']
      have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have hlogM : 4000 ≤ Real.log (M : ℝ) :=
      hLL.trans (Real.log_le_log (by positivity) hM_gt_L8)
    have hM1_pos : 0 < (M : ℝ) - 1 := by linarith
    have hlogM_pos : 0 < Real.log (M : ℝ) := by linarith
    have hden_pos : 0 < ((M : ℝ) - 1) * Real.log (M : ℝ) := mul_pos hM1_pos hlogM_pos
    rw [div_le_iff₀ hden_pos]
    have hmul : 400 * L ≤ ((M : ℝ) - 1) * Real.log (M : ℝ) := by nlinarith
    linarith
  let Pz := (primesUpTo X.sqrt).erase 2
  let PM := (primesUpTo M).erase 2
  have hPM_sub : PM ⊆ Pz := by
    intro p hp
    exact mem_erase.mpr ⟨ne_of_mem_erase hp,
      mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp (mem_of_mem_erase hp)).1,
        (mem_primesUpTo.mp (mem_of_mem_erase hp)).2.trans hM_le_sqrt⟩⟩
  have hPz_nonneg : 0 ≤ ∏ p ∈ Pz, (1 - 2 / (p : ℝ)) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast odd_prime_ge_three (mem_primesUpTo.mp (mem_of_mem_erase hp)).1
        (ne_of_mem_erase hp)
    have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hpoint : ∀ n ∈ E, x4 n ≤
      ((674 * m : ℕ) : ℝ) * (1 / 2) * (101 / 100) *
      (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
      (∏ p ∈ PM.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) := by
    intro n hn
    obtain ⟨hI, heven⟩ := mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hI
    have hbase := x4_pointwise_le hm3 hlo hhi heven hM_le_sqrt
    have htail := tail_correction_le hM_ge4 (by omega : 0 < n) (by dsimp [X]; omega) htail_small
    have hPM_nonneg : 0 ≤ ∏ p ∈ PM.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2)) := by
      apply Finset.prod_nonneg
      intro p hp
      have hpz := (mem_filter.mp hp).1
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast odd_prime_ge_three (mem_primesUpTo.mp (mem_of_mem_erase hpz)).1
          (ne_of_mem_erase hpz)
      have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      positivity
    calc
      x4 n ≤ ((674 * m : ℕ) : ℝ) * (1 / 2) * (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
          (∏ p ∈ PM.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) *
          (∏ p ∈ (Pz \ PM).filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) := hbase
      _ ≤ ((674 * m : ℕ) : ℝ) * (1 / 2) * (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
          (∏ p ∈ PM.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) * (101 / 100) := by
          gcongr
      _ = _ := by ring
  have hsum1 : ∑ n ∈ E, x4 n ≤
      ((674 * m : ℕ) : ℝ) * (1 / 2) * (101 / 100) * (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
      ∑ n ∈ E, ∏ p ∈ PM.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hpoint
  have hexpand : ∀ n ∈ E,
      (∏ p ∈ PM.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) =
        ∑ s ∈ PM.powerset, if (∏ p ∈ s, p) ∣ n then ∏ p ∈ s, (1 / ((p : ℝ) - 2)) else 0 := by
    intro n _
    rw [Finset.prod_one_add]
    rw [← Finset.sum_filter]
    congr 1
    ext s
    simp only [mem_powerset, mem_filter]
    constructor
    · intro hs
      refine ⟨hs.trans (filter_subset _ _), ?_⟩
      exact prod_primes_dvd
        (fun p hp => (mem_primesUpTo.mp (mem_of_mem_erase (mem_filter.mp (hs hp)).1)).1)
        (fun p hp => (mem_filter.mp (hs hp)).2)
    · rintro ⟨hs, hdvd⟩ p hp
      exact mem_filter.mpr ⟨hs hp, (Finset.dvd_prod_of_mem _ hp).trans hdvd⟩
  have hsum_swap :
      (∑ n ∈ E, ∏ p ∈ PM.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) =
        ∑ s ∈ PM.powerset,
          (∏ p ∈ s, (1 / ((p : ℝ) - 2))) *
            ((E.filter (fun n => (∏ p ∈ s, p) ∣ n)).card : ℝ) := by
    rw [Finset.sum_congr rfl hexpand, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hd_bound : ∀ s ∈ PM.powerset,
      ((E.filter (fun n => (∏ p ∈ s, p) ∣ n)).card : ℝ) ≤
        (101 / 100 : ℝ) * (10 * m : ℝ) / ((∏ p ∈ s, p : ℕ) : ℝ) := by
    intro s hs
    have hs' : s ⊆ PM := Finset.mem_powerset.mp hs
    let d := ∏ p ∈ s, p
    have hd_pos : 0 < d := Finset.prod_pos fun p hp =>
      (mem_primesUpTo.mp (mem_of_mem_erase (hs' hp))).1.pos
    have hd_odd : Odd d := by
      have : ∀ p ∈ s, Odd p := fun p hp =>
        (mem_primesUpTo.mp (mem_of_mem_erase (hs' hp))).1.odd_of_ne_two
          (ne_of_mem_erase (hs' hp))
      exact Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one this
    have hfilt : E.filter (fun n => d ∣ n) =
        (Finset.Ioc (2000 * m) (2020 * m)).filter (fun n => Even n ∧ d ∣ n) := by
      ext n; simp [E, and_assoc]
    have hmult := multiples_in_Ioc_le m d hd_pos hd_odd
    rw [← hfilt] at hmult
    have hd_le_rpow : (d : ℝ) ≤ (X : ℝ) ^ (2 / 5 : ℝ) := by
      have h1 := subset_prod_le_pow hs'
      have hlog4 : Real.log 4 ≤ 8 / 5 := by
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith [Real.log_two_lt_d9]
      have hexp_le : Real.log 4 * (M : ℝ) ≤ (2 / 5 : ℝ) * L := by
        nlinarith [hM_le_L4, hlog4, hLpos]
      calc
        (d : ℝ) ≤ Real.exp (Real.log 4 * (M : ℝ)) := h1
        _ ≤ Real.exp ((2 / 5 : ℝ) * L) := Real.exp_le_exp.mpr hexp_le
        _ = (X : ℝ) ^ (2 / 5 : ℝ) := by
          rw [Real.rpow_def_of_pos hXpos, mul_comm]
    have h1_le : (1 : ℝ) ≤ (1 / 100 : ℝ) * ((10 * m : ℝ) / (d : ℝ)) := by
      have hdR_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd_pos
      have hX_eq : (10 * m : ℝ) = (X : ℝ) / 200 := by
        dsimp [X]; push_cast; ring
      rw [hX_eq]
      have hmul_rpow : (X : ℝ) ^ (2 / 5 : ℝ) ≤ (X : ℝ) / 20000 := by
        have hsplit : (X : ℝ) ^ (2 / 5 : ℝ) = (X : ℝ) * (X : ℝ) ^ (-(3 / 5 : ℝ)) := by
          rw [← Real.rpow_one_add' hXpos.le (by norm_num)]
          norm_num
        rw [hsplit]
        nlinarith [hrpow, hXpos]
      have hd_small : (d : ℝ) ≤ (X : ℝ) / 20000 := hd_le_rpow.trans hmul_rpow
      have hrew : (1 / 100 : ℝ) * ((X : ℝ) / 200 / (d : ℝ)) = ((X : ℝ) / 20000) / (d : ℝ) := by
        ring
      rw [hrew, le_div_iff₀ hdR_pos]
      linarith
    calc
      ((E.filter (fun n => d ∣ n)).card : ℝ) ≤ (10 * m : ℝ) / (d : ℝ) + 1 := hmult
      _ ≤ (10 * m : ℝ) / (d : ℝ) + (1 / 100 : ℝ) * ((10 * m : ℝ) / (d : ℝ)) := by linarith
      _ = (101 / 100 : ℝ) * (10 * m : ℝ) / (d : ℝ) := by ring
  have hsum_corr :
      (∑ n ∈ E, ∏ p ∈ PM.filter (· ∣ n), (1 + 1 / ((p : ℝ) - 2))) ≤
        (101 / 100 : ℝ) * (10 * m : ℝ) *
          ∏ p ∈ PM, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
    rw [hsum_swap, Finset.prod_one_add, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s hs
    have hs' : s ⊆ PM := Finset.mem_powerset.mp hs
    have hnonneg : 0 ≤ ∏ p ∈ s, (1 / ((p : ℝ) - 2)) := by
      apply Finset.prod_nonneg
      intro p hp
      have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast odd_prime_ge_three (mem_primesUpTo.mp (mem_of_mem_erase (hs' hp))).1
          (ne_of_mem_erase (hs' hp))
      have : (0 : ℝ) < (p : ℝ) - 2 := by linarith
      positivity
    calc
      (∏ p ∈ s, (1 / ((p : ℝ) - 2))) * ((E.filter (fun n => (∏ p ∈ s, p) ∣ n)).card : ℝ)
          ≤ (∏ p ∈ s, (1 / ((p : ℝ) - 2))) *
              ((101 / 100 : ℝ) * (10 * m : ℝ) / ((∏ p ∈ s, p : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hd_bound s hs) hnonneg
      _ = (101 / 100 : ℝ) * (10 * m : ℝ) *
            ((∏ p ∈ s, (1 / ((p : ℝ) - 2))) / (∏ p ∈ s, (p : ℝ))) := by
            push_cast; ring
      _ = (101 / 100 : ℝ) * (10 * m : ℝ) *
            ∏ p ∈ s, (1 / ((p : ℝ) * ((p : ℝ) - 2))) := by
            congr 1
            rw [← Finset.prod_div_distrib]
            apply Finset.prod_congr rfl
            intro p _; rw [div_div, mul_comm ((p : ℝ) - 2)]
  have hprod_cancel :
      (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (∏ p ∈ PM, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) ≤
        ∏ p ∈ Pz, (1 - 1 / (p : ℝ)) ^ 2 := by
    rw [← Finset.prod_sdiff hPM_sub]
    have hleft :
        (∏ p ∈ PM, (1 - 2 / (p : ℝ))) * (∏ p ∈ PM, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) =
          ∏ p ∈ PM, (1 - 1 / (p : ℝ)) ^ 2 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      exact odd_prime_cancel_id (odd_prime_ge_three (mem_primesUpTo.mp (mem_of_mem_erase hp)).1
        (ne_of_mem_erase hp))
    have hright :
        (∏ p ∈ Pz \ PM, (1 - 2 / (p : ℝ))) ≤ ∏ p ∈ Pz \ PM, (1 - 1 / (p : ℝ)) ^ 2 := by
      apply Finset.prod_le_prod₀
      · intro p hp
        have hpz := (Finset.mem_sdiff.mp hp).1
        have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast odd_prime_ge_three (mem_primesUpTo.mp (mem_of_mem_erase hpz)).1
            (ne_of_mem_erase hpz)
        have : 2 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
        linarith
      · intro p hp
        have hpz := (Finset.mem_sdiff.mp hp).1
        exact odd_prime_one_sub_two_le_sq
          (odd_prime_ge_three (mem_primesUpTo.mp (mem_of_mem_erase hpz)).1 (ne_of_mem_erase hpz))
    have hPM_sq_nonneg : 0 ≤ ∏ p ∈ PM, (1 - 1 / (p : ℝ)) ^ 2 :=
      Finset.prod_nonneg fun _ _ => sq_nonneg _
    calc
      (∏ p ∈ Pz \ PM, (1 - 2 / (p : ℝ))) * (∏ p ∈ PM, (1 - 2 / (p : ℝ))) *
          (∏ p ∈ PM, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))))
          = (∏ p ∈ Pz \ PM, (1 - 2 / (p : ℝ))) *
              ((∏ p ∈ PM, (1 - 2 / (p : ℝ))) * (∏ p ∈ PM, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))))) := by
            ring
      _ = (∏ p ∈ Pz \ PM, (1 - 2 / (p : ℝ))) * (∏ p ∈ PM, (1 - 1 / (p : ℝ)) ^ 2) := by
            rw [hleft]
      _ ≤ (∏ p ∈ Pz \ PM, (1 - 1 / (p : ℝ)) ^ 2) * (∏ p ∈ PM, (1 - 1 / (p : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_right hright hPM_sq_nonneg
      _ = ∏ p ∈ Pz, (1 - 1 / (p : ℝ)) ^ 2 := Finset.prod_sdiff hPM_sub
  have heuler := odd_prime_prod_sq_le hX4
  have hsum_final : ∑ n ∈ E, x4 n ≤
      ((674 * m : ℕ) : ℝ) * (1 / 2) * (101 / 100) * ((101 / 100) * (10 * m : ℝ)) *
        (16 / L ^ 2) := by
    calc
      ∑ n ∈ E, x4 n
          ≤ ((674 * m : ℕ) : ℝ) * (1 / 2) * (101 / 100) * (∏ p ∈ Pz, (1 - 2 / (p : ℝ))) *
              ((101 / 100 : ℝ) * (10 * m : ℝ) * ∏ p ∈ PM, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2)))) :=
            hsum1.trans (mul_le_mul_of_nonneg_left hsum_corr (by positivity))
      _ = ((674 * m : ℕ) : ℝ) * (1 / 2) * (101 / 100) * ((101 / 100) * (10 * m : ℝ)) *
            ((∏ p ∈ Pz, (1 - 2 / (p : ℝ))) * (∏ p ∈ PM, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 2))))) := by
            ring
      _ ≤ ((674 * m : ℕ) : ℝ) * (1 / 2) * (101 / 100) * ((101 / 100) * (10 * m : ℝ)) *
            (16 / L ^ 2) := by
            gcongr
            exact hprod_cancel.trans heuler
  have hcoeff : (2 / 25 : ℝ) * (674 * (1 / 2) * (101 / 100) * ((101 / 100) * 10) * 16) ≤ 4401 := by
    norm_num
  have hsq_nonneg : 0 ≤ (m : ℝ) ^ 2 / L ^ 2 := by positivity
  calc
    (2 / 25 : ℝ) * ∑ n ∈ E, x4 n
        ≤ (2 / 25 : ℝ) * (((674 * m : ℕ) : ℝ) * (1 / 2) * (101 / 100) *
            ((101 / 100) * (10 * m : ℝ)) * (16 / L ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum_final (by norm_num)
    _ = ((2 / 25 : ℝ) * (674 * (1 / 2) * (101 / 100) * ((101 / 100) * 10) * 16)) *
          ((m : ℝ) ^ 2 / L ^ 2) := by push_cast; ring
    _ ≤ 4401 * ((m : ℝ) ^ 2 / L ^ 2) := mul_le_mul_of_nonneg_right hcoeff hsq_nonneg
    _ = 4401 * (m : ℝ) ^ 2 / L ^ 2 := by ring

/-! ### Part 2: Lower bound on the averaged two-sided semiprime pairing count -/

private theorem minFac_mul_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hle : p ≤ q) :
    (p * q).minFac = p := by
  have hne : p * q ≠ 1 := by
    have := hp.two_le; have := hq.two_le; nlinarith
  have hm := Nat.minFac_prime hne
  have hdvd := Nat.minFac_dvd (p * q)
  have hle' := Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p q)
  rcases hm.dvd_mul.mp hdvd with h1 | h2
  · exact (Nat.prime_dvd_prime_iff_eq hm hp).mp h1
  · have := (Nat.prime_dvd_prime_iff_eq hm hq).mp h2
    omega

private theorem card_primesUpTo_eq_primeCounting (N : ℕ) :
    (primesUpTo N).card = Nat.primeCounting N := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rfl

private theorem pnt_interval_bounds :
    ∃ Y₀ : ℝ, 4 ≤ Y₀ ∧ ∀ y : ℝ, Y₀ ≤ y →
      (1 - 1 / 20000 : ℝ) * (y / Real.log y) ≤ ((primesUpTo ⌊y⌋₊).card : ℝ) ∧
      ((primesUpTo ⌊y⌋₊).card : ℝ) ≤ (1 + 1 / 20000 : ℝ) * (y / Real.log y) := by
  have heq := Nat.isEquivalent_primeCounting
  have hne : ∀ᶠ y : ℝ in atTop, y / Real.log y ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    exact div_ne_zero (by linarith) (Real.log_pos hy).ne'
  have ht := (Asymptotics.isEquivalent_iff_tendsto_one hne).mp heq
  have hmem : Set.Icc (1 - 1 / 20000 : ℝ) (1 + 1 / 20000 : ℝ) ∈ 𝓝 (1 : ℝ) :=
    Icc_mem_nhds (by norm_num) (by norm_num)
  have hev := ht.eventually hmem
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop (4 : ℝ)))
  refine ⟨max 4 Y₁, le_max_left _ _, fun y hy => ?_⟩
  have ⟨hb, hy4⟩ := hY₁ y ((le_max_right _ _).trans hy)
  have hpos : 0 < y / Real.log y := div_pos (by linarith) (Real.log_pos (by linarith))
  rw [card_primesUpTo_eq_primeCounting]
  exact ⟨(le_div_iff₀ hpos).mp hb.1, (div_le_iff₀ hpos).mp hb.2⟩

private noncomputable def bandAlpha (k : ℕ) : ℝ := (335 + 10 * (k : ℝ)) / 1000
private noncomputable def bandBeta (k : ℕ) : ℝ := (345 + 10 * (k : ℝ)) / 1000

private theorem band_sum_ge :
    (63 / 100 : ℝ) ≤ (98 / 100 : ℝ) *
      ∑ k ∈ Finset.range 16,
        ((1 - bandAlpha k / bandBeta k) - 1 / 10000) / (1 - bandAlpha k) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bandAlpha, bandBeta]
  norm_num

private theorem one_sub_inv_le_log {x : ℝ} (hx : 0 < x) :
    1 - x⁻¹ ≤ Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  linarith

private theorem semi_interval_lower :
    ∃ M₂ : ℕ, 3 ≤ M₂ ∧ ∀ m : ℕ, M₂ ≤ m →
      let X := 2000 * m
      let Z := ⌊((2020 * m : ℕ) : ℝ) ^ (1 / 3 : ℝ)⌋₊
      ∀ A B : ℕ, 690 * m ≤ A → B ≤ 1330 * m → 20 * m ≤ B - A →
        (63 / 100 : ℝ) * (((B - A : ℕ) : ℝ) / Real.log (X : ℝ)) ≤
          (((Finset.Ioc A B).filter (fun u =>
            Z < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime)).card : ℝ) := by
  obtain ⟨Y₀, hY₀4, hPNT⟩ := pnt_interval_bounds
  obtain ⟨Cm, hCm, hMert⟩ := mertensSecond
  have hX_inf : Tendsto (fun m : ℕ => ((2000 * m : ℕ) : ℝ)) atTop atTop := tendsto_mul_2000
  have hL_inf : Tendsto (fun m : ℕ => Real.log ((2000 * m : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hX_inf
  have hpow0505 : Tendsto (fun m : ℕ => ((2000 * m : ℕ) : ℝ) ^ (505 / 1000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 505 / 1000)).comp hX_inf
  have hpow001 : Tendsto (fun m : ℕ => ((2000 * m : ℕ) : ℝ) ^ (1 / 100 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).comp hX_inf
  have hpow0001 : Tendsto (fun m : ℕ => ((2000 * m : ℕ) : ℝ) ^ (1 / 600 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 600)).comp hX_inf
  have hpow0335 : Tendsto (fun m : ℕ => ((2000 * m : ℕ) : ℝ) ^ (335 / 1000 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 335 / 1000)).comp hX_inf
  have hev : ∀ᶠ m : ℕ in atTop,
      3 ≤ m ∧
      (69 / 200 : ℝ) * ((2000 * m : ℕ) : ℝ) ^ (505 / 1000 : ℝ) ≥ max Y₀ (Real.exp 20000) ∧
      ((2000 * m : ℕ) : ℝ) ^ (1 / 100 : ℝ) ≥ 4 ∧
      ((2000 * m : ℕ) : ℝ) ^ (1 / 600 : ℝ) ≥ 2 ∧
      ((2000 * m : ℕ) : ℝ) ^ (335 / 1000 : ℝ) ≥ 4 ∧
      Real.log ((2000 * m : ℕ) : ℝ) ≥ max 10 (60000 * Cm) := by
    filter_upwards [eventually_ge_atTop 3,
      (hpow0505.const_mul_atTop (by norm_num : (0 : ℝ) < 69 / 200)).eventually
        (eventually_ge_atTop (max Y₀ (Real.exp 20000))),
      hpow001.eventually (eventually_ge_atTop 4),
      hpow0001.eventually (eventually_ge_atTop 2),
      hpow0335.eventually (eventually_ge_atTop 4),
      hL_inf.eventually (eventually_ge_atTop (max 10 (60000 * Cm)))] with m h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  obtain ⟨M₂, hM₂⟩ := eventually_atTop.mp hev
  refine ⟨max 3 M₂, le_max_left _ _, fun m hm => ?_⟩
  obtain ⟨hm3, hbigA, hgap, hcube, h335, hLbig⟩ := hM₂ m ((le_max_right _ _).trans hm)
  intro X Z A B hA_lo hB_hi hBA
  have hXpos : (0 : ℝ) < (X : ℝ) := by dsimp [X]; positivity
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by dsimp [X]; exact_mod_cast (by omega : 1 ≤ 2000 * m)
  let L := Real.log (X : ℝ)
  have hL10 : 10 ≤ L := (le_max_left _ _).trans hLbig
  have hLpos : 0 < L := by linarith
  let Pk : ℕ → Finset ℕ := fun k =>
    primesUpTo ⌊(X : ℝ) ^ (bandBeta k)⌋₊ \ primesUpTo ⌊(X : ℝ) ^ (bandAlpha k)⌋₊
  let Qp : ℕ → Finset ℕ := fun p =>
    primesUpTo ⌊(B : ℝ) / (p : ℝ)⌋₊ \ primesUpTo ⌊(A : ℝ) / (p : ℝ)⌋₊
  let Semi := (Finset.Ioc A B).filter (fun u =>
    Z < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime)
  let P_all := (Finset.range 16).biUnion Pk
  have hPk_disj : Set.PairwiseDisjoint (Finset.range 16 : Set ℕ) Pk := by
    intro k₁ hk₁ k₂ hk₂ hne
    show Disjoint (Pk k₁) (Pk k₂)
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    have hm₁ := Finset.mem_sdiff.mp hp₁
    have hm₂ := Finset.mem_sdiff.mp hp₂
    have hle₁ := (mem_primesUpTo.mp hm₁.1).2
    have hle₂ := (mem_primesUpTo.mp hm₂.1).2
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hba : bandBeta k₁ ≤ bandAlpha k₂ := by
        unfold bandAlpha bandBeta
        have hk : (k₁ + 1 : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast hlt
        linarith
      have hpow : (X : ℝ) ^ (bandBeta k₁) ≤ (X : ℝ) ^ (bandAlpha k₂) :=
        Real.rpow_le_rpow_of_exponent_le hX1 hba
      exact hm₂.2 (mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hm₁.1).1,
        hle₁.trans (Nat.floor_mono hpow)⟩)
    · have hba : bandBeta k₂ ≤ bandAlpha k₁ := by
        unfold bandAlpha bandBeta
        have hk : (k₂ + 1 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast hgt
        linarith
      have hpow : (X : ℝ) ^ (bandBeta k₂) ≤ (X : ℝ) ^ (bandAlpha k₁) :=
        Real.rpow_le_rpow_of_exponent_le hX1 hba
      exact hm₁.2 (mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hm₂.1).1,
        hle₂.trans (Nat.floor_mono hpow)⟩)
  have hp_props : ∀ k ∈ Finset.range 16, ∀ p ∈ Pk k,
      p.Prime ∧ (X : ℝ) ^ (bandAlpha k) < (p : ℝ) ∧ (p : ℝ) ≤ (X : ℝ) ^ (bandBeta k) ∧
      Z < p := by
    intro k hk p hp
    obtain ⟨hhi, hlo⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp_prime, hp_le⟩ := mem_primesUpTo.mp hhi
    have hp_gt_floor : ⌊(X : ℝ) ^ (bandAlpha k)⌋₊ < p := by
      by_contra! hle
      exact hlo (mem_primesUpTo.mpr ⟨hp_prime, hle⟩)
    have hp_gt : (X : ℝ) ^ (bandAlpha k) < (p : ℝ) :=
      (Nat.floor_lt (Real.rpow_nonneg hXpos.le _)).mp hp_gt_floor
    have hp_leR : (p : ℝ) ≤ (X : ℝ) ^ (bandBeta k) :=
      (Nat.le_floor_iff (Real.rpow_nonneg hXpos.le _)).mp hp_le
    have hk_lt : k < 16 := Finset.mem_range.mp hk
    have ha_ge : (335 / 1000 : ℝ) ≤ bandAlpha k := by
      unfold bandAlpha; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hZ_lt : Z < p := by
      have h1 : ((2020 * m : ℕ) : ℝ) ^ (1 / 3 : ℝ) < (X : ℝ) ^ (335 / 1000 : ℝ) := by
        have h2020 : ((2020 * m : ℕ) : ℝ) ≤ 2 * (X : ℝ) := by
          dsimp [X]; push_cast; linarith
        have hr1 : ((2020 * m : ℕ) : ℝ) ^ (1 / 3 : ℝ) ≤ (2 * (X : ℝ)) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (by positivity) h2020 (by norm_num)
        rw [Real.mul_rpow (by norm_num) hXpos.le] at hr1
        have h2c : (2 : ℝ) ^ (1 / 3 : ℝ) < 2 := by
          have : (2 : ℝ) ^ (1 / 3 : ℝ) < (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
          simpa using this
        have hsplit : (X : ℝ) ^ (335 / 1000 : ℝ) =
            (X : ℝ) ^ (1 / 3 : ℝ) * (X : ℝ) ^ (1 / 600 : ℝ) := by
          rw [← Real.rpow_add hXpos]; norm_num
        rw [hsplit]
        have hpos3 : 0 < (X : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hXpos _
        calc
          ((2020 * m : ℕ) : ℝ) ^ (1 / 3 : ℝ)
              ≤ (2 : ℝ) ^ (1 / 3 : ℝ) * (X : ℝ) ^ (1 / 3 : ℝ) := hr1
          _ < 2 * (X : ℝ) ^ (1 / 3 : ℝ) := mul_lt_mul_of_pos_right h2c hpos3
          _ ≤ (X : ℝ) ^ (1 / 600 : ℝ) * (X : ℝ) ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_right hcube hpos3.le
          _ = _ := mul_comm _ _
      have h2 : (X : ℝ) ^ (335 / 1000 : ℝ) ≤ (X : ℝ) ^ (bandAlpha k) :=
        Real.rpow_le_rpow_of_exponent_le hX1 ha_ge
      have h3 : ((2020 * m : ℕ) : ℝ) ^ (1 / 3 : ℝ) < (p : ℝ) := h1.trans (h2.trans_lt hp_gt)
      have hZ_le : (Z : ℝ) ≤ ((2020 * m : ℕ) : ℝ) ^ (1 / 3 : ℝ) :=
        Nat.floor_le (by positivity)
      exact_mod_cast hZ_le.trans_lt h3
    exact ⟨hp_prime, hp_gt, hp_leR, hZ_lt⟩
  have hpair_mem : ∀ k ∈ Finset.range 16, ∀ p ∈ Pk k, ∀ q ∈ Qp p,
      p < q ∧ p * q ∈ Semi := by
    intro k hk p hp q hq
    obtain ⟨hp_prime, hp_gt, hp_leR, hZp⟩ := hp_props k hk p hp
    obtain ⟨hq_hi, hq_lo⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hq_prime, hq_le⟩ := mem_primesUpTo.mp hq_hi
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hq_gt_floor : ⌊(A : ℝ) / (p : ℝ)⌋₊ < q := by
      by_contra! hle
      exact hq_lo (mem_primesUpTo.mpr ⟨hq_prime, hle⟩)
    have hq_gt : (A : ℝ) / (p : ℝ) < (q : ℝ) :=
      (Nat.floor_lt (by positivity)).mp hq_gt_floor
    have hq_leR : (q : ℝ) ≤ (B : ℝ) / (p : ℝ) :=
      (Nat.le_floor_iff (by positivity)).mp hq_le
    have hk_lt : k < 16 := Finset.mem_range.mp hk
    have hb_le : bandBeta k ≤ 495 / 1000 := by
      unfold bandBeta
      have hk15 : (k : ℝ) ≤ 15 := by exact_mod_cast (show k ≤ 15 by omega)
      linarith
    have hp_le495 : (p : ℝ) ≤ (X : ℝ) ^ (495 / 1000 : ℝ) :=
      hp_leR.trans (Real.rpow_le_rpow_of_exponent_le hX1 hb_le)
    have hA_R : (69 / 200 : ℝ) * (X : ℝ) ≤ (A : ℝ) := by
      have : ((690 * m : ℕ) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA_lo
      dsimp [X] at *; push_cast at *; linarith
    have hp_lt_q : p < q := by
      have hdiv : (X : ℝ) ^ (495 / 1000 : ℝ) < (A : ℝ) / (p : ℝ) := by
        rw [lt_div_iff₀ hp_pos]
        have hmul : (X : ℝ) ^ (495 / 1000 : ℝ) * (p : ℝ) ≤
            (X : ℝ) ^ (99 / 100 : ℝ) := by
          calc
            (X : ℝ) ^ (495 / 1000 : ℝ) * (p : ℝ)
                ≤ (X : ℝ) ^ (495 / 1000 : ℝ) * (X : ℝ) ^ (495 / 1000 : ℝ) :=
                  mul_le_mul_of_nonneg_left hp_le495 (Real.rpow_nonneg hXpos.le _)
            _ = (X : ℝ) ^ (99 / 100 : ℝ) := by rw [← Real.rpow_add hXpos]; norm_num
        have hlt_A : (X : ℝ) ^ (99 / 100 : ℝ) < (69 / 200 : ℝ) * (X : ℝ) := by
          have hsplit : (X : ℝ) = (X : ℝ) ^ (99 / 100 : ℝ) * (X : ℝ) ^ (1 / 100 : ℝ) := by
            rw [← Real.rpow_add hXpos]; norm_num
          have hpos99 : 0 < (X : ℝ) ^ (99 / 100 : ℝ) := Real.rpow_pos_of_pos hXpos _
          have hgap' : (4 : ℝ) ≤ (X : ℝ) ^ (1 / 100 : ℝ) := hgap
          nlinarith [hsplit, hgap', hpos99]
        exact (hmul.trans_lt hlt_A).trans_le hA_R
      exact_mod_cast hp_le495.trans_lt (hdiv.trans hq_gt)
    have hpq_lo : A < p * q := by
      have h1 : (A : ℝ) < (p : ℝ) * (q : ℝ) := by
        have := (div_lt_iff₀ hp_pos).mp hq_gt; linarith
      exact_mod_cast h1
    have hpq_hi : p * q ≤ B := by
      have h1 : (p : ℝ) * (q : ℝ) ≤ (B : ℝ) := by
        have := (le_div_iff₀ hp_pos).mp hq_leR; linarith
      exact_mod_cast h1
    have hmin : (p * q).minFac = p := minFac_mul_primes hp_prime hq_prime hp_lt_q.le
    refine ⟨hp_lt_q, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpq_lo, hpq_hi⟩, ?_, ?_, ?_⟩⟩
    · rw [hmin]; exact hZp
    · rw [hmin]; exact hp_prime
    · rw [hmin, Nat.mul_div_cancel_left q hp_prime.pos]; exact hq_prime
  have hcard_semi :
      ∑ k ∈ Finset.range 16, ∑ p ∈ Pk k, (Qp p).card ≤ Semi.card := by
    rw [← Finset.sum_biUnion hPk_disj, ← Finset.card_sigma]
    apply Finset.card_le_card_of_injOn (fun x : Σ p : ℕ, ℕ => x.1 * x.2)
    · intro x hx
      obtain ⟨hpx, hqx⟩ := Finset.mem_sigma.mp hx
      obtain ⟨k, hk, hpk⟩ := Finset.mem_biUnion.mp hpx
      exact (hpair_mem k hk x.1 hpk x.2 hqx).2
    · intro x hx y hy heq
      obtain ⟨hpx, hqx⟩ := Finset.mem_sigma.mp hx
      obtain ⟨hpy, hqy⟩ := Finset.mem_sigma.mp hy
      obtain ⟨kx, hkx, hpkx⟩ := Finset.mem_biUnion.mp hpx
      obtain ⟨ky, hky, hpky⟩ := Finset.mem_biUnion.mp hpy
      have h1 := hpair_mem kx hkx x.1 hpkx x.2 hqx
      have h2 := hpair_mem ky hky y.1 hpky y.2 hqy
      have hpx' := (hp_props kx hkx x.1 hpkx).1
      have hpy' := (hp_props ky hky y.1 hpky).1
      have hqx' := (mem_primesUpTo.mp (Finset.mem_sdiff.mp hqx).1).1
      have hqy' := (mem_primesUpTo.mp (Finset.mem_sdiff.mp hqy).1).1
      have hmin_eq : x.1 = y.1 := by
        have h := congrArg Nat.minFac heq
        rw [minFac_mul_primes hpx' hqx' h1.1.le, minFac_mul_primes hpy' hqy' h2.1.le] at h
        exact h
      cases x with | mk p₁ q₁ =>
      cases y with | mk p₂ q₂ =>
      dsimp at hmin_eq heq
      subst hmin_eq
      have hq_eq : q₁ = q₂ := Nat.eq_of_mul_eq_mul_left hpx'.pos heq
      subst hq_eq
      rfl
  have hQp_lower : ∀ k ∈ Finset.range 16, ∀ p ∈ Pk k,
      (98 / 100 : ℝ) * (((B - A : ℕ) : ℝ) / ((1 - bandAlpha k) * L)) * (1 / (p : ℝ)) ≤
        ((Qp p).card : ℝ) := by
    intro k hk p hp
    obtain ⟨hp_prime, hp_gt, hp_leR, _⟩ := hp_props k hk p hp
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hk_lt : k < 16 := Finset.mem_range.mp hk
    have hb_le : bandBeta k ≤ 495 / 1000 := by
      unfold bandBeta
      have : (k : ℝ) ≤ 15 := by exact_mod_cast (show k ≤ 15 by omega)
      linarith
    have ha_lt1 : 0 < 1 - bandAlpha k := by
      unfold bandAlpha
      have : (k : ℝ) ≤ 15 := by exact_mod_cast (show k ≤ 15 by omega)
      linarith
    have hp_le495 : (p : ℝ) ≤ (X : ℝ) ^ (495 / 1000 : ℝ) :=
      hp_leR.trans (Real.rpow_le_rpow_of_exponent_le hX1 hb_le)
    have hA_R : (69 / 200 : ℝ) * (X : ℝ) ≤ (A : ℝ) := by
      have : ((690 * m : ℕ) : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA_lo
      dsimp [X] at *; push_cast at *; linarith
    have hAp_ge : max Y₀ (Real.exp 20000) ≤ (A : ℝ) / (p : ℝ) := by
      apply hbigA.trans
      rw [le_div_iff₀ hp_pos]
      calc
        (69 / 200 : ℝ) * (X : ℝ) ^ (505 / 1000 : ℝ) * (p : ℝ)
            ≤ (69 / 200 : ℝ) * (X : ℝ) ^ (505 / 1000 : ℝ) * (X : ℝ) ^ (495 / 1000 : ℝ) := by
              gcongr
        _ = (69 / 200 : ℝ) * ((X : ℝ) ^ (505 / 1000 : ℝ) * (X : ℝ) ^ (495 / 1000 : ℝ)) := by ring
        _ = (69 / 200 : ℝ) * (X : ℝ) := by rw [← Real.rpow_add hXpos]; norm_num
        _ ≤ (A : ℝ) := hA_R
    have hAB : (A : ℝ) ≤ (B : ℝ) := by exact_mod_cast (show A ≤ B by omega)
    have hBp_ge : Y₀ ≤ (B : ℝ) / (p : ℝ) :=
      (le_max_left _ _).trans (hAp_ge.trans (div_le_div_of_nonneg_right hAB hp_pos.le))
    have hAp_Y₀ : Y₀ ≤ (A : ℝ) / (p : ℝ) := (le_max_left _ _).trans hAp_ge
    have hAp_exp : Real.exp 20000 ≤ (A : ℝ) / (p : ℝ) := (le_max_right _ _).trans hAp_ge
    have hAp_pos : 0 < (A : ℝ) / (p : ℝ) := (Real.exp_pos 20000).trans_le hAp_exp
    have hBp_pos : 0 < (B : ℝ) / (p : ℝ) :=
      hAp_pos.trans_le (div_le_div_of_nonneg_right hAB hp_pos.le)
    have hlogAp_ge : 20000 ≤ Real.log ((A : ℝ) / (p : ℝ)) := by
      have h := Real.log_le_log (Real.exp_pos 20000) hAp_exp
      rwa [Real.log_exp] at h
    have hlogAp_pos : 0 < Real.log ((A : ℝ) / (p : ℝ)) := by linarith
    have hlogBp_pos : 0 < Real.log ((B : ℝ) / (p : ℝ)) :=
      hlogAp_pos.trans_le (Real.log_le_log hAp_pos (div_le_div_of_nonneg_right hAB hp_pos.le))
    have hB_le_2A : (B : ℝ) ≤ 2 * (A : ℝ) := by
      have h1 : B ≤ 2 * A := by omega
      exact_mod_cast h1
    have hlog_ratio : Real.log ((B : ℝ) / (p : ℝ)) ≤
        (1 + 1 / 20000 : ℝ) * Real.log ((A : ℝ) / (p : ℝ)) := by
      have h1 : (B : ℝ) / (p : ℝ) ≤ 2 * ((A : ℝ) / (p : ℝ)) := by
        rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hB_le_2A hp_pos.le
      have h2 := Real.log_le_log hBp_pos h1
      rw [Real.log_mul (by norm_num) hAp_pos.ne'] at h2
      have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have hBp_le_X : (B : ℝ) / (p : ℝ) ≤ (X : ℝ) ^ (1 - bandAlpha k) := by
      rw [div_le_iff₀ hp_pos]
      have hBX : (B : ℝ) ≤ (X : ℝ) := by
        have : B ≤ X := by dsimp [X]; omega
        exact_mod_cast this
      calc
        (B : ℝ) ≤ (X : ℝ) := hBX
        _ = (X : ℝ) ^ (1 - bandAlpha k) * (X : ℝ) ^ (bandAlpha k) := by
          rw [← Real.rpow_add hXpos]; simp
        _ ≤ (X : ℝ) ^ (1 - bandAlpha k) * (p : ℝ) :=
          mul_le_mul_of_nonneg_left hp_gt.le (Real.rpow_nonneg hXpos.le _)
    have hlogBp_le : Real.log ((B : ℝ) / (p : ℝ)) ≤ (1 - bandAlpha k) * L := by
      have h := Real.log_le_log hBp_pos hBp_le_X
      rwa [Real.log_rpow hXpos] at h
    have hsub_Qp : primesUpTo ⌊(A : ℝ) / (p : ℝ)⌋₊ ⊆ primesUpTo ⌊(B : ℝ) / (p : ℝ)⌋₊ := by
      intro r hr
      exact mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hr).1,
        (mem_primesUpTo.mp hr).2.trans (Nat.floor_mono (div_le_div_of_nonneg_right hAB hp_pos.le))⟩
    have hcard_diff : ((Qp p).card : ℝ) =
        ((primesUpTo ⌊(B : ℝ) / (p : ℝ)⌋₊).card : ℝ) -
          ((primesUpTo ⌊(A : ℝ) / (p : ℝ)⌋₊).card : ℝ) := by
      have h := Finset.card_sdiff_of_subset hsub_Qp
      have hle : (primesUpTo ⌊(A : ℝ) / (p : ℝ)⌋₊).card ≤
          (primesUpTo ⌊(B : ℝ) / (p : ℝ)⌋₊).card := Finset.card_le_card hsub_Qp
      dsimp [Qp]
      rw [h, Nat.cast_sub hle]
    have hB_pnt := (hPNT ((B : ℝ) / (p : ℝ)) hBp_ge).1
    have hA_pnt := (hPNT ((A : ℝ) / (p : ℝ)) hAp_Y₀).2
    have hA_adj : (1 + 1 / 20000 : ℝ) * (((A : ℝ) / (p : ℝ)) / Real.log ((A : ℝ) / (p : ℝ))) ≤
        (1 + 1 / 20000 : ℝ) ^ 2 * (((A : ℝ) / (p : ℝ)) / Real.log ((B : ℝ) / (p : ℝ))) := by
      have hinv : (1 : ℝ) / Real.log ((A : ℝ) / (p : ℝ)) ≤
          (1 + 1 / 20000 : ℝ) / Real.log ((B : ℝ) / (p : ℝ)) := by
        rw [div_le_div_iff₀ hlogAp_pos hlogBp_pos]
        linarith
      have hA_nonneg : 0 ≤ (1 + 1 / 20000 : ℝ) * ((A : ℝ) / (p : ℝ)) := by positivity
      calc
        (1 + 1 / 20000 : ℝ) * (((A : ℝ) / (p : ℝ)) / Real.log ((A : ℝ) / (p : ℝ)))
            = ((1 + 1 / 20000 : ℝ) * ((A : ℝ) / (p : ℝ))) * (1 / Real.log ((A : ℝ) / (p : ℝ))) := by
              ring
        _ ≤ ((1 + 1 / 20000 : ℝ) * ((A : ℝ) / (p : ℝ))) *
              ((1 + 1 / 20000 : ℝ) / Real.log ((B : ℝ) / (p : ℝ))) :=
              mul_le_mul_of_nonneg_left hinv hA_nonneg
        _ = _ := by ring
    have hnum_ge : (98 / 100 : ℝ) * ((B - A : ℕ) : ℝ) ≤
        (1 - 1 / 20000 : ℝ) * (B : ℝ) - (1 + 1 / 20000 : ℝ) ^ 2 * (A : ℝ) := by
      have hBA_cast : ((B - A : ℕ) : ℝ) = (B : ℝ) - (A : ℝ) := Nat.cast_sub (by omega)
      have hA_le_67BA : (A : ℝ) ≤ 67 * ((B - A : ℕ) : ℝ) := by
        have : A ≤ 67 * (B - A) := by omega
        exact_mod_cast this
      have hB_le_68BA : (B : ℝ) ≤ 68 * ((B - A : ℕ) : ℝ) := by
        have : B ≤ 68 * (B - A) := by omega
        exact_mod_cast this
      rw [hBA_cast] at hA_le_67BA hB_le_68BA ⊢
      linarith
    calc
      (98 / 100 : ℝ) * (((B - A : ℕ) : ℝ) / ((1 - bandAlpha k) * L)) * (1 / (p : ℝ))
          = ((98 / 100 : ℝ) * ((B - A : ℕ) : ℝ)) / ((p : ℝ) * ((1 - bandAlpha k) * L)) := by
            field_simp
      _ ≤ ((98 / 100 : ℝ) * ((B - A : ℕ) : ℝ)) / ((p : ℝ) * Real.log ((B : ℝ) / (p : ℝ))) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left hlogBp_le hp_pos.le
      _ ≤ ((1 - 1 / 20000 : ℝ) * (B : ℝ) - (1 + 1 / 20000 : ℝ) ^ 2 * (A : ℝ)) /
            ((p : ℝ) * Real.log ((B : ℝ) / (p : ℝ))) :=
            div_le_div_of_nonneg_right hnum_ge (by positivity)
      _ = (1 - 1 / 20000 : ℝ) * (((B : ℝ) / (p : ℝ)) / Real.log ((B : ℝ) / (p : ℝ))) -
            (1 + 1 / 20000 : ℝ) ^ 2 * (((A : ℝ) / (p : ℝ)) / Real.log ((B : ℝ) / (p : ℝ))) := by
            field_simp
      _ ≤ ((primesUpTo ⌊(B : ℝ) / (p : ℝ)⌋₊).card : ℝ) -
            ((primesUpTo ⌊(A : ℝ) / (p : ℝ)⌋₊).card : ℝ) := by
            linarith [hB_pnt, hA_pnt, hA_adj]
      _ = ((Qp p).card : ℝ) := hcard_diff.symm
  have hPk_recip : ∀ k ∈ Finset.range 16,
      (1 - bandAlpha k / bandBeta k) - 1 / 10000 ≤ ∑ p ∈ Pk k, (1 / (p : ℝ)) := by
    intro k hk
    have hk_lt : k < 16 := Finset.mem_range.mp hk
    have ha_pos : (335 / 1000 : ℝ) ≤ bandAlpha k := by
      unfold bandAlpha; linarith [Nat.cast_nonneg (α := ℝ) k]
    have ha_gt0 : 0 < bandAlpha k := lt_of_lt_of_le (by norm_num) ha_pos
    have hab : bandAlpha k < bandBeta k := by unfold bandAlpha bandBeta; linarith
    have hb_pos : 0 < bandBeta k := ha_gt0.trans hab
    have hXa_ge2 : 2 ≤ (X : ℝ) ^ (bandAlpha k) := by
      have h1 : (4 : ℝ) ≤ (X : ℝ) ^ (335 / 1000 : ℝ) := h335
      have h2 := Real.rpow_le_rpow_of_exponent_le hX1 ha_pos
      linarith
    have hXb_ge2 : 2 ≤ (X : ℝ) ^ (bandBeta k) :=
      hXa_ge2.trans (Real.rpow_le_rpow_of_exponent_le hX1 hab.le)
    have hsub_k : primesUpTo ⌊(X : ℝ) ^ (bandAlpha k)⌋₊ ⊆
        primesUpTo ⌊(X : ℝ) ^ (bandBeta k)⌋₊ := by
      intro p hp
      exact mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hp).1,
        (mem_primesUpTo.mp hp).2.trans
          (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hX1 hab.le))⟩
    have hsum_eq : ∑ p ∈ Pk k, (1 / (p : ℝ)) =
        primeReciprocalSum ⌊(X : ℝ) ^ (bandBeta k)⌋₊ -
          primeReciprocalSum ⌊(X : ℝ) ^ (bandAlpha k)⌋₊ := by
      have h := Finset.sum_sdiff hsub_k (f := fun p : ℕ => 1 / (p : ℝ))
      dsimp only [Pk]
      unfold primeReciprocalSum
      linarith
    rw [hsum_eq]
    have hMb := abs_le.mp (hMert ((X : ℝ) ^ (bandBeta k)) hXb_ge2)
    have hMa := abs_le.mp (hMert ((X : ℝ) ^ (bandAlpha k)) hXa_ge2)
    have hlog_b : Real.log ((X : ℝ) ^ (bandBeta k)) = bandBeta k * L := Real.log_rpow hXpos _
    have hlog_a : Real.log ((X : ℝ) ^ (bandAlpha k)) = bandAlpha k * L := Real.log_rpow hXpos _
    have hdiff_log : Real.log (Real.log ((X : ℝ) ^ (bandBeta k))) -
        Real.log (Real.log ((X : ℝ) ^ (bandAlpha k))) = Real.log (bandBeta k / bandAlpha k) := by
      rw [hlog_b, hlog_a, ← Real.log_div (by positivity) (by positivity)]
      congr 1; field_simp
    have hlog_lb : 1 - bandAlpha k / bandBeta k ≤ Real.log (bandBeta k / bandAlpha k) := by
      have := one_sub_inv_le_log (div_pos hb_pos ha_gt0)
      rwa [inv_div] at this
    have herr_a : Cm / Real.log ((X : ℝ) ^ (bandAlpha k)) ≤ 1 / 20000 := by
      rw [hlog_a, div_le_iff₀ (by positivity)]
      have hLcm : 60000 * Cm ≤ L := (le_max_right _ _).trans hLbig
      nlinarith
    have herr_b : Cm / Real.log ((X : ℝ) ^ (bandBeta k)) ≤ 1 / 20000 := by
      rw [hlog_b, div_le_iff₀ (by positivity)]
      have hLcm : 60000 * Cm ≤ L := (le_max_right _ _).trans hLbig
      nlinarith
    linarith [hMb.1, hMa.2, hdiff_log, hlog_lb, herr_a, herr_b]
  have hcast_semi :
      (∑ k ∈ Finset.range 16, ∑ p ∈ Pk k, ((Qp p).card : ℝ)) ≤ (Semi.card : ℝ) := by
    exact_mod_cast hcard_semi
  calc
    (63 / 100 : ℝ) * (((B - A : ℕ) : ℝ) / L)
        ≤ ((98 / 100 : ℝ) * ∑ k ∈ Finset.range 16,
            ((1 - bandAlpha k / bandBeta k) - 1 / 10000) / (1 - bandAlpha k)) *
            (((B - A : ℕ) : ℝ) / L) :=
          mul_le_mul_of_nonneg_right band_sum_ge (by positivity)
    _ = ∑ k ∈ Finset.range 16,
          ((98 / 100 : ℝ) * (((B - A : ℕ) : ℝ) / ((1 - bandAlpha k) * L))) *
            ((1 - bandAlpha k / bandBeta k) - 1 / 10000) := by
          rw [Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k hk
          have hk_lt : k < 16 := Finset.mem_range.mp hk
          have ha_lt1 : 0 < 1 - bandAlpha k := by
            unfold bandAlpha
            have : (k : ℝ) ≤ 15 := by exact_mod_cast (show k ≤ 15 by omega)
            linarith
          field_simp
    _ ≤ ∑ k ∈ Finset.range 16,
          ((98 / 100 : ℝ) * (((B - A : ℕ) : ℝ) / ((1 - bandAlpha k) * L))) *
            (∑ p ∈ Pk k, (1 / (p : ℝ))) := by
          apply Finset.sum_le_sum
          intro k hk
          have hk_lt : k < 16 := Finset.mem_range.mp hk
          have ha_lt1 : 0 < 1 - bandAlpha k := by
            unfold bandAlpha
            have : (k : ℝ) ≤ 15 := by exact_mod_cast (show k ≤ 15 by omega)
            linarith
          exact mul_le_mul_of_nonneg_left (hPk_recip k hk) (by positivity)
    _ = ∑ k ∈ Finset.range 16, ∑ p ∈ Pk k,
          (98 / 100 : ℝ) * (((B - A : ℕ) : ℝ) / ((1 - bandAlpha k) * L)) * (1 / (p : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k _; rw [Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range 16, ∑ p ∈ Pk k, ((Qp p).card : ℝ) := by
          apply Finset.sum_le_sum
          intro k hk
          exact Finset.sum_le_sum fun p hp => hQp_lower k hk p hp
    _ ≤ (Semi.card : ℝ) := hcast_semi

private theorem sum_x5_lower :
    ∃ M₃ : ℕ, ∀ m : ℕ, M₃ ≤ m →
      let X := 2000 * m
      let E := (Finset.Ioc (2000 * m) (2020 * m)).filter Even
      let x1 := fun n : ℕ => Finset.Icc ((n + 2) / 3) ((2 * n) / 3)
      let x3 := fun n : ℕ => (x1 n).filter (fun u =>
        ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac))
      let x5 := fun n : ℕ => (x3 n).filter (fun u => n - u ∈ x3 n)
      4900 * ((m : ℝ) ^ 2) / (Real.log (X : ℝ)) ^ 2 ≤
        ∑ n ∈ E, ((x5 n).card : ℝ) := by
  obtain ⟨M₂, hM₂3, hsemi⟩ := semi_interval_lower
  refine ⟨max 10 M₂, fun m hm => ?_⟩
  have hm10 : 10 ≤ m := (le_max_left _ _).trans hm
  have hmM₂ : M₂ ≤ m := (le_max_right _ _).trans hm
  intro X E x1 x3 x5
  let Z := ⌊((2020 * m : ℕ) : ℝ) ^ (1 / 3 : ℝ)⌋₊
  have hZ2 : 2 ≤ Z := by
    apply Nat.le_floor
    have h1 : (8 : ℝ) ≤ ((2020 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 8 ≤ 2020 * m)
    have h2 : (2 : ℝ) = (8 : ℝ) ^ (1 / 3 : ℝ) := by
      rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    change (2 : ℝ) ≤ ((2020 * m : ℕ) : ℝ) ^ (1 / 3 : ℝ)
    rw [h2]
    exact Real.rpow_le_rpow (by norm_num) h1 (by norm_num)
  let semi := fun A B : ℕ => (Finset.Ioc A B).filter (fun u =>
    Z < u.minFac ∧ u.minFac.Prime ∧ (u / u.minFac).Prime)
  let U₁ := semi (690 * m) (1310 * m)
  have hodd_semi : ∀ A B u, u ∈ semi A B → Odd u := by
    intro A B u hu
    obtain ⟨_, hZu, hp1, hp2⟩ := mem_filter.mp hu
    have hu_eq : u = u.minFac * (u / u.minFac) := (Nat.mul_div_cancel' (Nat.minFac_dvd u)).symm
    have h1_odd : Odd u.minFac := hp1.odd_of_ne_two (by omega)
    have h2_ge : u.minFac ≤ u / u.minFac := by
      have hu1 : u ≠ 1 := by
        intro h; rw [h, Nat.minFac_one] at hZu; omega
      have hdvd : (u / u.minFac) ∣ u := Nat.div_dvd_of_dvd (Nat.minFac_dvd u)
      exact Nat.minFac_le_of_dvd hp2.two_le hdvd
    have h2_odd : Odd (u / u.minFac) := hp2.odd_of_ne_two (by omega)
    rw [hu_eq]
    exact h1_odd.mul h2_odd
  have hdouble :
      (∑ u ∈ U₁, (semi (2000 * m - u) (2020 * m - u)).card) ≤ ∑ n ∈ E, (x5 n).card := by
    rw [← Finset.card_sigma, ← Finset.card_sigma]
    apply Finset.card_le_card_of_injOn (fun x : Σ u : ℕ, ℕ => (⟨x.1 + x.2, x.1⟩ : Σ n : ℕ, ℕ))
    · intro x hx
      obtain ⟨hu, hv⟩ := Finset.mem_sigma.mp hx
      obtain ⟨hu_I, huZ, hup1, hup2⟩ := mem_filter.mp hu
      obtain ⟨hv_I, hvZ, hvp1, hvp2⟩ := mem_filter.mp hv
      obtain ⟨hu_lo, hu_hi⟩ := mem_Ioc.mp hu_I
      obtain ⟨hv_lo, hv_hi⟩ := mem_Ioc.mp hv_I
      have hn_lo : 2000 * m < x.1 + x.2 := by omega
      have hn_hi : x.1 + x.2 ≤ 2020 * m := by omega
      have hn_even : Even (x.1 + x.2) := (hodd_semi _ _ _ hu).add_odd (hodd_semi _ _ _ hv)
      have hn_mem : x.1 + x.2 ∈ E := mem_filter.mpr ⟨mem_Ioc.mpr ⟨hn_lo, hn_hi⟩, hn_even⟩
      have hfloor_le : ⌊((x.1 + x.2 : ℕ) : ℝ) ^ (1 / 3 : ℝ)⌋₊ ≤ Z := by
        apply Nat.floor_mono
        exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hn_hi) (by norm_num)
      have hu_x1 : x.1 ∈ x1 (x.1 + x.2) := by
        dsimp [x1]; rw [mem_Icc]; omega
      have hv_x1 : x.2 ∈ x1 (x.1 + x.2) := by
        dsimp [x1]; rw [mem_Icc]; omega
      have hu_x3 : x.1 ∈ x3 (x.1 + x.2) :=
        mem_filter.mpr ⟨hu_x1, hfloor_le.trans_lt huZ, hup1, hup2⟩
      have hv_x3 : x.2 ∈ x3 (x.1 + x.2) :=
        mem_filter.mpr ⟨hv_x1, hfloor_le.trans_lt hvZ, hvp1, hvp2⟩
      refine Finset.mem_sigma.mpr ⟨hn_mem, mem_filter.mpr ⟨hu_x3, ?_⟩⟩
      simpa only [Nat.add_sub_cancel_left] using hv_x3
    · intro x _ y _ heq
      cases x with | mk u₁ v₁ =>
      cases y with | mk u₂ v₂ =>
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      obtain ⟨hsum, hu⟩ := heq
      subst hu
      have hv : v₁ = v₂ := by omega
      subst hv
      rfl
  have hU₁_lb : (63 / 100 : ℝ) * (((620 * m : ℕ) : ℝ) / Real.log (X : ℝ)) ≤ (U₁.card : ℝ) := by
    have h := hsemi m hmM₂ (690 * m) (1310 * m) le_rfl (by omega) (by omega)
    simpa only [show 1310 * m - 690 * m = 620 * m by omega] using h
  have hV_lb : ∀ u ∈ U₁,
      (63 / 100 : ℝ) * (((20 * m : ℕ) : ℝ) / Real.log (X : ℝ)) ≤
        ((semi (2000 * m - u) (2020 * m - u)).card : ℝ) := by
    intro u hu
    obtain ⟨hu_lo, hu_hi⟩ := mem_Ioc.mp (mem_filter.mp hu).1
    have h := hsemi m hmM₂ (2000 * m - u) (2020 * m - u) (by omega) (by omega) (by omega)
    simpa only [show 2020 * m - u - (2000 * m - u) = 20 * m by omega] using h
  have hLpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by dsimp [X]; exact_mod_cast (by omega : 1 < 2000 * m))
  have hdoubleR :
      (∑ u ∈ U₁, ((semi (2000 * m - u) (2020 * m - u)).card : ℝ)) ≤
        ∑ n ∈ E, ((x5 n).card : ℝ) := by
    exact_mod_cast hdouble
  have hsum_V :
      (U₁.card : ℝ) * ((63 / 100 : ℝ) * (((20 * m : ℕ) : ℝ) / Real.log (X : ℝ))) ≤
        ∑ u ∈ U₁, ((semi (2000 * m - u) (2020 * m - u)).card : ℝ) := by
    calc
      (U₁.card : ℝ) * ((63 / 100 : ℝ) * (((20 * m : ℕ) : ℝ) / Real.log (X : ℝ)))
          = ∑ _u ∈ U₁, ((63 / 100 : ℝ) * (((20 * m : ℕ) : ℝ) / Real.log (X : ℝ))) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ u ∈ U₁, ((semi (2000 * m - u) (2020 * m - u)).card : ℝ) :=
            Finset.sum_le_sum hV_lb
  have hcoeff : (4900 : ℝ) ≤ (63 / 100) * 620 * ((63 / 100) * 20) := by norm_num
  have hsq_nonneg : 0 ≤ (m : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by positivity
  calc
    4900 * (m : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2
        = 4900 * ((m : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) := by ring
    _ ≤ ((63 / 100 : ℝ) * 620 * ((63 / 100 : ℝ) * 20)) *
          ((m : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_right hcoeff hsq_nonneg
    _ = ((63 / 100 : ℝ) * (((620 * m : ℕ) : ℝ) / Real.log (X : ℝ))) *
          ((63 / 100 : ℝ) * (((20 * m : ℕ) : ℝ) / Real.log (X : ℝ))) := by
          push_cast; ring
    _ ≤ (U₁.card : ℝ) * ((63 / 100 : ℝ) * (((20 * m : ℕ) : ℝ) / Real.log (X : ℝ))) :=
          mul_le_mul_of_nonneg_right hU₁_lb (by positivity)
    _ ≤ ∑ u ∈ U₁, ((semi (2000 * m - u) (2020 * m - u)).card : ℝ) := hsum_V
    _ ≤ ∑ n ∈ E, ((x5 n).card : ℝ) := hdoubleR

end RefuteTwoSidedSemiprimePairing

theorem Conjectures.Cuts.Refute381823bab84c203ff962aeb2 : ¬ (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊(↑x6 : ℝ) ^ (2 / 5 : ℝ)⌋₊; ∃ (x7 : ℕ), ∀ (x8 : ℕ), x7 ≤ x8 → Even x8 → (↑(x5 x8).card : ℝ) ≤ (2 / 25 : ℝ) * x4 x8) := by
  intro h
  dsimp only at h
  obtain ⟨N₀, hN₀⟩ := h
  obtain ⟨M₁, hM₁⟩ := RefuteTwoSidedSemiprimePairing.sum_x4_upper
  obtain ⟨M₃, hM₃⟩ := RefuteTwoSidedSemiprimePairing.sum_x5_lower
  let m := max (max M₁ M₃) (max N₀ 10)
  have hm1 : M₁ ≤ m := (le_max_left _ _).trans (le_max_left _ _)
  have hm3 : M₃ ≤ m := (le_max_right _ _).trans (le_max_left _ _)
  have hmN : N₀ ≤ m := (le_max_left _ _).trans (le_max_right _ _)
  have hm10 : 10 ≤ m := (le_max_right _ _).trans (le_max_right _ _)
  have hup := hM₁ m hm1
  have hlo := hM₃ m hm3
  let E := (Finset.Ioc (2000 * m) (2020 * m)).filter Even
  have hle :
      (∑ n ∈ E, (({u ∈ (Finset.Icc ((n + 2) / 3) (2 * n / 3)).filter (fun u =>
        ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac)) |
        n - u ∈ (Finset.Icc ((n + 2) / 3) (2 * n / 3)).filter (fun u =>
        ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊ < u.minFac ∧ Nat.Prime u.minFac ∧ Nat.Prime (u / u.minFac))}).card : ℝ)) ≤
      (2 / 25 : ℝ) * ∑ n ∈ E,
        ((Finset.Icc ((n + 2) / 3) (2 * n / 3)).card : ℝ) * (n.totient : ℝ) / (n : ℝ) *
          ∏ p ∈ ((Finset.Icc 2 n.sqrt).filter Nat.Prime).filter (fun p => ¬ p ∣ n),
            ((1 : ℝ) - (2 : ℝ) / (p : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hI, heven⟩ := Finset.mem_filter.mp hn
    have hn_ge : N₀ ≤ n := by
      have := (Finset.mem_Ioc.mp hI).1
      omega
    exact hN₀ n hn_ge heven
  have hLpos : 0 < Real.log ((2000 * m : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < 2000 * m))
  have hratio_pos : 0 < (m : ℝ) ^ 2 / (Real.log ((2000 * m : ℕ) : ℝ)) ^ 2 := by positivity
  dsimp only at hup hlo
  have hcomb : 4900 * (m : ℝ) ^ 2 / (Real.log ((2000 * m : ℕ) : ℝ)) ^ 2 ≤
      4401 * (m : ℝ) ^ 2 / (Real.log ((2000 * m : ℕ) : ℝ)) ^ 2 :=
    hlo.trans (hle.trans hup)
  have hcomb' : (4900 : ℝ) * ((m : ℝ) ^ 2 / (Real.log ((2000 * m : ℕ) : ℝ)) ^ 2) ≤
      4401 * ((m : ℝ) ^ 2 / (Real.log ((2000 * m : ℕ) : ℝ)) ^ 2) := by
    simpa only [mul_div_assoc] using hcomb
  linarith
