import Mathlib
import Conjectures.Goldbach.BinaryShiftShortMixedEnergy

-- Uses the reciprocal-prime estimate and periodic counting theorem verified in #3352.
-- The attribution for their upstream sources is retained in that module.

namespace GoldbachSieve
open Finset
open scoped Classical

private def smallPrimes (p R : ℕ) : Finset ℕ :=
  (Icc 2 R).filter fun ℓ => Nat.Prime ℓ ∧ ℓ ≠ p

def sieveGood (p R n : ℕ) : Prop :=
  ¬ p ∣ n ∧ ∀ ℓ ∈ smallPrimes p R, ¬ ℓ ^ 2 ∣ n

theorem sieveGood_mod {p R : ℕ} (hp : p.Prime) (hpR : p ≤ R) (n : ℕ) :
    sieveGood p R (n % R.factorial ^ 2) ↔ sieveGood p R n := by
  have dp : p ∣ R.factorial ^ 2 := by
    rw [pow_two]
    exact (Nat.dvd_factorial hp.pos hpR).trans (dvd_mul_right _ _)
  have ds (ℓ : ℕ) (hℓ : ℓ ∈ smallPrimes p R) : ℓ ^ 2 ∣ R.factorial ^ 2 := by
    have h : ℓ ∣ R.factorial := Nat.dvd_factorial (mem_filter.mp hℓ).2.1.pos
      (mem_Icc.mp (mem_filter.mp hℓ).1).2
    rw [pow_two, pow_two]
    exact Nat.mul_dvd_mul h h
  simp only [sieveGood, Nat.dvd_mod_iff dp]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact ⟨h₁, fun ℓ hℓ hn => h₂ ℓ hℓ ((Nat.dvd_mod_iff (ds ℓ hℓ)).mpr hn)⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨h₁, fun ℓ hℓ hn => h₂ ℓ hℓ ((Nat.dvd_mod_iff (ds ℓ hℓ)).mp hn)⟩

private theorem countDiv {M d : ℕ} (hd : 0 < d) (h : d ∣ M) :
    ((range M).filter (fun n => d ∣ n)).card = M / d := by
  have cnt := Nat.count_modEq_card M hd 0
  rw [Nat.count_eq_card_filter_range, Nat.mod_eq_zero_of_dvd h] at cnt
  have e : ((range M).filter (fun n => d ∣ n)) =
      ((range M).filter (fun n => n ≡ 0 [MOD d])) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hr, hdv⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hr, Nat.modEq_zero_iff_dvd.mpr hdv⟩
    · intro hn
      obtain ⟨hr, hmod⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hr, Nat.modEq_zero_iff_dvd.mp hmod⟩
  rw [e]
  simpa only [Nat.zero_mod, lt_self_iff_false, ite_false, Nat.add_zero] using cnt

set_option maxHeartbeats 1200000 in
private theorem reciprocals (p R : ℕ) (hp : 3 ≤ p) (hR : p ≤ R) :
    (1 : ℝ)/(p:ℝ) + ∑ ℓ ∈ smallPrimes p R, ((ℓ:ℝ) ^ 2)⁻¹ ≤ 35/36 := by
  let f : ℕ → ℝ := fun ℓ => ((ℓ:ℝ)^2)⁻¹
  have htail : ∑ ℓ ∈ Ioc 3 R, f ℓ ≤ (1:ℝ)/3 := by
    have hh := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 3) (n := R) (by decide) (hp.trans hR)
    dsimp [f]
    norm_num at hh
    have hn : 0 ≤ (↑R : ℝ)⁻¹ := by positivity
    linarith only [hh,hn]
  have no2 : 2 ∉ Ioc 3 R := by simp
  have no3 : 3 ∉ Ioc 3 R := by simp
  by_cases h3 : p = 3
  · subst p
    have hsub : smallPrimes 3 R ⊆ insert 2 (Ioc 3 R) := by
      intro k hk
      have hk0 := mem_filter.mp hk
      have hk1 := mem_Icc.mp hk0.1
      by_cases he : k=2
      · simp [he]
      · exact mem_insert_of_mem (mem_Ioc.mpr ⟨by have := hk0.2.2; omega, hk1.2⟩)
    have hcomp := sum_le_sum_of_subset_of_nonneg (f := f) hsub (by intros; dsimp [f]; positivity)
    rw [sum_insert no2] at hcomp
    change 1/(3:ℝ) + ∑ ℓ ∈ smallPrimes 3 R, f ℓ ≤ 35/36
    have h2 : f 2 = 1/4 := by norm_num [f]
    rw [h2] at hcomp
    calc
      _ ≤ (1:ℝ)/3 + ((1:ℝ)/4 + ∑ ℓ ∈ Ioc 3 R, f ℓ) := add_le_add_right hcomp _
      _ ≤ (1:ℝ)/3 + ((1:ℝ)/4+(1:ℝ)/3) :=
        (add_le_add_right (add_le_add_right htail ((1:ℝ)/4)) ((1:ℝ)/3))
      _ ≤ _ := by norm_num
  · have hsub : smallPrimes p R ⊆ insert 2 (insert 3 (Ioc 3 R)) := by
      intro k hk
      have hk0 := mem_Icc.mp (mem_filter.mp hk).1
      by_cases he : k=2
      · simp [he]
      by_cases he' : k=3
      · simp [he']
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_Ioc.mpr ⟨by omega, hk0.2⟩))
    have n2 : 2 ∉ insert 3 (Ioc 3 R) := by simp [no2]
    have hcomp := sum_le_sum_of_subset_of_nonneg (f := f) hsub (by intros; dsimp [f]; positivity)
    rw [sum_insert n2, sum_insert no3] at hcomp
    have hp4 : (4:ℝ) ≤ (p:ℝ) := by exact_mod_cast (show 4 ≤ p by omega)
    have hp0 : (0:ℝ) < (p:ℝ) := by linarith only [hp4]
    have hfrac : 1/(p:ℝ) ≤ 1/4 := by
      apply (div_le_div_iff₀ hp0 (by norm_num : (0:ℝ)<4)).mpr
      linarith only [hp4]
    change 1/(p:ℝ) + ∑ ℓ ∈ smallPrimes p R, f ℓ ≤ 35/36
    have h2 : f 2 = 1/4 := by norm_num [f]
    have h3' : f 3 = 1/9 := by norm_num [f]
    rw [h2, h3'] at hcomp
    calc
      _ ≤ (1:ℝ)/4 + ((1:ℝ)/4 + (1/9 + ∑ ℓ ∈ Ioc 3 R, f ℓ)) := add_le_add hfrac hcomp
      _ ≤ (1:ℝ)/4 + ((1:ℝ)/4 + ((1:ℝ)/9 + (1:ℝ)/3)) :=
        (add_le_add_right (add_le_add_right (add_le_add_right htail ((1:ℝ)/9)) ((1:ℝ)/4)) ((1:ℝ)/4))
      _ ≤ _ := by norm_num

theorem sieveGood_density {p R : ℕ} (hp : p.Prime) (h₃ : 3 ≤ p) (hpR : p ≤ R) :
    let M := R.factorial ^ 2
    (M:ℝ) / 36 ≤ (((Finset.range M).filter fun n => sieveGood p R n).card : ℝ) := by
  classical
  let M := R.factorial ^ 2
  change (M:ℝ) / 36 ≤ (((range M).filter fun n => sieveGood p R n).card : ℝ)
  let V (d : ℕ) : Finset ℕ := (range M).filter fun x => d ∣ x
  let S := smallPrimes p R
  let B := V p ∪ S.biUnion (fun ℓ => V (ℓ^2))
  have incl : ((range M).filter (fun n => ¬ sieveGood p R n)) ⊆ B := by
    intro n hn
    have hnm := (mem_filter.mp hn).1
    have hbad := (mem_filter.mp hn).2
    by_cases hpn : p ∣ n
    · exact mem_union_left _ (mem_filter.mpr ⟨hnm,hpn⟩)
    · have hex : ∃ ℓ ∈ S, ℓ ^ 2 ∣ n := by
        by_contra! hnone
        exact hbad ⟨hpn, hnone⟩
      obtain ⟨ℓ, hℓ, hnℓ⟩ := hex
      exact mem_union_right _ (mem_biUnion.mpr ⟨ℓ,hℓ,mem_filter.mpr ⟨hnm,hnℓ⟩⟩)
  have countBad : ((range M).filter (fun n => ¬ sieveGood p R n)).card ≤
      (V p).card + ∑ ℓ ∈ S, (V (ℓ^2)).card :=
    (card_le_card incl).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left card_biUnion_le _))
  have Mnonneg : (0:ℝ) ≤ M := by positivity
  have dp : p ∣ M := by
    dsimp only [M]
    rw [pow_two]
    exact (Nat.dvd_factorial hp.pos hpR).trans (dvd_mul_right _ _)
  have castCount {d : ℕ} (hd : 0 < d) (h : d ∣ M) : ((V d).card:ℝ) = (M:ℝ)/(d:ℝ) := by
    dsimp only [V]
    rw [countDiv hd h, Nat.cast_div h (by positivity)]
  have castSum : ∑ ℓ ∈ S, ((V (ℓ^2)).card:ℝ) =
      ∑ ℓ ∈ S, ((M:ℝ) * ((ℓ:ℝ)^2)⁻¹) := by
    apply sum_congr rfl
    intro ℓ hℓ
    have hℓp := (mem_filter.mp hℓ).2.1.pos
    have hₗ := Nat.dvd_factorial hℓp (mem_Icc.mp (mem_filter.mp hℓ).1).2
    have hd : ℓ ^ 2 ∣ M := by
      dsimp only [M]
      rw [pow_two, pow_two]
      exact Nat.mul_dvd_mul hₗ hₗ
    rw [castCount (by positivity) hd]
    simp only [Nat.cast_pow, div_eq_mul_inv]
  have badreal : (((range M).filter (fun n => ¬ sieveGood p R n)).card : ℝ) ≤
      (M:ℝ)*((1:ℝ)/(p:ℝ) + ∑ ℓ ∈ S, ((ℓ:ℝ)^2)⁻¹) := by
    have hr : (((range M).filter (fun n => ¬ sieveGood p R n)).card : ℝ) ≤
        ((V p).card:ℝ) + ∑ ℓ ∈ S, ((V (ℓ^2)).card:ℝ) := by exact_mod_cast countBad
    rw [castCount hp.pos dp, castSum, ← mul_sum] at hr
    rw [mul_add, mul_one_div]
    exact hr
  have badBound : (((range M).filter (fun n => ¬ sieveGood p R n)).card : ℝ) ≤
      (M:ℝ)*(35/36 : ℝ) := badreal.trans (mul_le_mul_of_nonneg_left (reciprocals p R h₃ hpR) Mnonneg)
  have cards := @card_filter_add_card_filter_not ℕ (range M) (sieveGood p R) _ _
  rw [card_range] at cards
  have cards' : (((range M).filter fun n => sieveGood p R n).card:ℝ) +
      (((range M).filter fun n => ¬ sieveGood p R n).card:ℝ) = M := by exact_mod_cast cards
  linarith only [cards', badBound]

theorem sieveGood_count_density {p R : ℕ} (hp : p.Prime) (h₃ : 3 ≤ p) (hpR : p ≤ R) :
    let M := R.factorial ^ 2
    (M:ℝ) / 36 ≤ (Nat.count (sieveGood p R) M : ℝ) := by
  simpa only [Nat.count_eq_card_filter_range] using sieveGood_density hp h₃ hpR

theorem prime_coprime_sieve_period {q R : ℕ} (hq : q.Prime) (hRq : R < q) :
    q.Coprime (R.factorial ^ 2) :=
  ((hq.coprime_iff_not_dvd).mpr (fun h => (Nat.not_le_of_gt hRq) (hq.dvd_factorial.mp h))).pow_right 2

end GoldbachSieve


namespace GoldbachSkirtPeriodic

open Finset
open Conjectures.Goldbach.ShiftPairSieve.Foundation
open scoped Classical

private theorem ioc_succ_eq (X Y : ℕ) : Ioc X Y = Ico (X+1) (Y+1) := by
  ext n
  simp only [mem_Ioc, mem_Ico]
  omega

/-- Residue-set discrepancy on a half-open interval of integers. -/
theorem zmod_Ioc_discrepancy (M X Y : ℕ) [NeZero M]
    (P : ZMod M → Prop) [DecidablePred P] (hXY : X ≤ Y) :
    |(((Ioc X Y).filter (fun n : ℕ => P (n : ZMod M))).card : ℝ) -
      ((Y-X : ℕ) : ℝ) * (univ.filter P).card / M| ≤ (univ.filter P).card := by
  rw [ioc_succ_eq, show Y+1 = X+1+(Y-X) by omega]
  exact OAI.Problem337.zmod_predicate_Ico_discrepancy M P (X+1) (Y-X)

/-- The number of allowed classes in one period is the initial natural count. -/
private theorem mass_eq (M : ℕ) [NeZero M] (Good : ℕ → Prop) [DecidablePred Good] :
    (univ.filter (fun r : ZMod M => Good r.val)).card = Nat.count Good M := by
  rw [← OAI.Problem337.zmod_predicate_period_count M (fun r : ZMod M => Good r.val)]
  simp_rw [Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp only [mem_filter, mem_range, ZMod.val_natCast]
  by_cases hn : n < M
  · simp only [hn, Nat.mod_eq_of_lt hn, true_and]
  · simp only [hn, false_and]

/-- The discrepancy bound for a predicate specified by natural remainders. -/
theorem good_Ioc_discrepancy (M X Y : ℕ) [NeZero M]
    (Good : ℕ → Prop) [DecidablePred Good]
    (hGood : ∀ n, Good (n % M) ↔ Good n) (hXY : X ≤ Y) :
    |(((Ioc X Y).filter Good).card : ℝ) -
      ((Y-X : ℕ) : ℝ) * Nat.count Good M / M| ≤ Nat.count Good M := by
  have h := zmod_Ioc_discrepancy M X Y (fun r : ZMod M => Good r.val) hXY
  rw [mass_eq M Good] at h
  simpa only [ZMod.val_natCast, hGood] using h

/-- A coprime multiplier permutes the residues in the period. -/
private theorem mul_mass_eq (M q : ℕ) [NeZero M]
    (P : ZMod M → Prop) [DecidablePred P] (hc : q.Coprime M) :
    (univ.filter (fun r : ZMod M => P ((q : ZMod M) * r))).card =
      (univ.filter P).card := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime q M).mpr hc
  apply Finset.card_bijective (fun r : ZMod M => (q : ZMod M) * r)
  · rw [← hu]
    exact u.mulLeft_bijective
  · intro r
    simp only [mem_filter, mem_univ, true_and]

/-- Restricting to multiples of q amounts to counting the quotient variable. -/
private theorem multiples_card_eq (X Y q : ℕ) (hq : 0 < q)
    (Good : ℕ → Prop) [DecidablePred Good] :
    ((Ioc X Y).filter (fun n => Good n ∧ q ∣ n)).card =
      ((Ioc (X/q) (Y/q)).filter (fun m => Good (q*m))).card := by
  let f : ℕ ↪ ℕ := ⟨fun n => q*n, fun a b h => Nat.eq_of_mul_eq_mul_left hq h⟩
  rw [← card_map (s := (Ioc (X/q) (Y/q)).filter (fun m => Good (q*m))) f]
  congr 1
  ext n
  simp only [mem_filter, mem_Ioc, mem_map]
  constructor
  · rintro ⟨⟨hlo, hhi⟩, hgood, ⟨m, rfl⟩⟩
    refine ⟨m, ⟨⟨?_, ?_⟩, hgood⟩, rfl⟩
    · exact (Nat.div_lt_iff_lt_mul hq).mpr (by simpa [Nat.mul_comm] using hlo)
    · exact (Nat.le_div_iff_mul_le hq).mpr (by simpa [Nat.mul_comm] using hhi)
  · rintro ⟨m, ⟨⟨hlo, hhi⟩, hgood⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, hgood, ⟨m, rfl⟩⟩
    · change X < q*m
      simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hq).mp hlo
    · change q*m ≤ Y
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hq).mp hhi

/-- The quotient interval loses at most one point to integer rounding. -/
private theorem quotient_length_upper (X Y q : ℕ) (hXY : X ≤ Y) (hq : 0 < q) :
    ((Y/q-X/q : ℕ) : ℝ) ≤ ((Y-X : ℕ) : ℝ) / q + 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hx : (X : ℝ) < ((X/q : ℕ) : ℝ) * q + q := by
    have hr : ((X % q : ℕ) : ℝ) < q := by exact_mod_cast Nat.mod_lt X hq
    have h := Nat.div_add_mod X q
    have hd : (q : ℝ) * ((X/q : ℕ) : ℝ) + (X % q : ℕ) = X := by exact_mod_cast h
    linarith only [hd, hr, mul_comm (q : ℝ) ((X/q : ℕ) : ℝ)]
  have hy : ((Y/q : ℕ) : ℝ) * q ≤ Y := by
    exact_mod_cast Nat.div_mul_le_self Y q
  rw [Nat.cast_sub (Nat.div_le_div_right hXY), Nat.cast_sub hXY]
  have hx' : (X : ℝ)/q < ((X/q : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ hqR).mpr
    simpa only [add_mul, one_mul] using hx
  have hy' : ((Y/q : ℕ) : ℝ) ≤ (Y : ℝ)/q := (le_div_iff₀ hqR).mpr hy
  rw [sub_div]
  linarith only [hx', hy']

/-- Upper estimate on allowed multiples, with an error of two periods' mass. -/
theorem good_Ioc_multiples_upper (M X Y q : ℕ) [NeZero M]
    (Good : ℕ → Prop) [DecidablePred Good]
    (hGood : ∀ n, Good (n % M) ↔ Good n) (hXY : X ≤ Y)
    (hq : 0 < q) (hc : q.Coprime M) :
    (((Ioc X Y).filter (fun n => Good n ∧ q ∣ n)).card : ℝ) ≤
      ((Y-X : ℕ) : ℝ) * Nat.count Good M / ((q : ℝ)*M) + 2*Nat.count Good M := by
  let P (r : ZMod M) := Good r.val
  let Pq (r : ZMod M) := P ((q : ZMod M)*r)
  have hperiod : (univ.filter Pq).card = Nat.count Good M :=
    (mul_mass_eq M q P hc).trans (mass_eq M Good)
  have hdisc := zmod_Ioc_discrepancy M (X/q) (Y/q) Pq (Nat.div_le_div_right hXY)
  rw [hperiod] at hdisc
  have hpred : ∀ n : ℕ, Pq (n : ZMod M) ↔ Good (q*n) := by
    intro n
    dsimp only [Pq, P]
    rw [← Nat.cast_mul, ZMod.val_natCast]
    exact hGood _
  have hcount : (((Ioc (X/q) (Y/q)).filter (fun n : ℕ => Good (q*n))).card : ℝ) ≤
      ((Y/q-X/q : ℕ) : ℝ)*Nat.count Good M / M + Nat.count Good M := by
    rw [abs_le] at hdisc
    have h := hdisc.2
    simp only [hpred] at h
    linarith only [h]
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast NeZero.pos M
  have hMpos : 0 < (M : ℝ) := by positivity
  have hmass : (Nat.count Good M : ℝ)/M ≤ Nat.count Good M :=
    div_le_self (Nat.cast_nonneg _) hM
  rw [multiples_card_eq X Y q hq Good]
  apply hcount.trans
  calc
    _ ≤ (((Y-X : ℕ) : ℝ)/q+1)*Nat.count Good M/M + Nat.count Good M := by
      gcongr
      exact quotient_length_upper X Y q hXY hq
    _ ≤ _ := by
      rw [add_mul, add_div, one_mul]
      have heq : (((Y-X : ℕ) : ℝ)/q)*Nat.count Good M/M =
          ((Y-X : ℕ) : ℝ)*Nat.count Good M/((q : ℝ)*M) := by ring
      linarith only [heq, hmass]

end GoldbachSkirtPeriodic


namespace GoldbachSkirtHarmonic

open Finset Filter
open scoped BigOperators Topology
open ErdosStraus.PrimeEstimates.Mertens

def omittedPrimorial (p y : ℕ) : ℕ :=
  ∏ q ∈ (Icc 2 y).filter (fun q => q.Prime ∧ q ≠ p), q

def skirtQ (N : ℕ) : ℕ := (Nat.log 2 (N + 2)) ^ 2

noncomputable def scale (p y : ℕ) : ℝ :=
  (skirtQ (omittedPrimorial p y) : ℝ) / (p : ℝ)

private theorem omittedPrimorial_pos (p y : ℕ) : 0 < omittedPrimorial p y := by
  exact prod_pos (fun q hq => ((mem_filter.mp hq).2.1 : Nat.Prime q).pos)

private theorem log_omittedPrimorial (p y : ℕ) (hp : p.Prime) (hy : p ≤ y) :
    Real.log (omittedPrimorial p y : ℝ) =
      Chebyshev.theta (y : ℝ) - Real.log (p : ℝ) := by
  have hset : (Icc 2 y).filter (fun q : ℕ => q.Prime ∧ q ≠ p) =
      y.primesLE.erase p := by
    ext q
    simp only [mem_filter, mem_Icc, mem_erase, Nat.mem_primesLE]
    constructor
    · rintro ⟨⟨_, hqy⟩, hqp, hne⟩
      exact ⟨hne, hqy, hqp⟩
    · rintro ⟨hne, hqy, hqp⟩
      exact ⟨⟨hqp.two_le, hqy⟩, hqp, hne⟩
  rw [omittedPrimorial, hset, Nat.cast_prod, Real.log_prod]
  · rw [Chebyshev.theta_eq_sum_primesLE_log]
    have hpmem : p ∈ y.primesLE := Nat.mem_primesLE.mpr ⟨hy, hp⟩
    linarith only [Finset.sum_erase_add _ (fun q : ℕ => Real.log (q : ℝ)) hpmem]
  · intro q hq
    exact_mod_cast (Nat.prime_of_mem_primesLE (mem_erase.mp hq).2).ne_zero

theorem eventually_scale_bounds (p : ℕ) (hp : p.Prime) :
    ∀ᶠ y : ℕ in atTop, (y : ℝ) ^ 2 / (16 * (p : ℝ)) ≤ scale p y ∧
      scale p y ≤ 36 * (y : ℝ) ^ 2 := by
  have ht := Chebyshev.tendsto_theta_div_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hθ := ht.eventually (Ioo_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 2))
  have hyBig := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
    (max (6 * Real.log (p : ℝ)) (max (Real.log 3) 12))
  filter_upwards [hθ, hyBig, eventually_ge_atTop p] with y hyθ hyB hyp
  have hy12 : (12 : ℝ) ≤ y := (le_max_right (Real.log 3) 12).trans ((le_max_right _ _).trans hyB)
  have hypos : (0 : ℝ) < y := by linarith
  have hyplog : 6 * Real.log (p : ℝ) ≤ y := (le_max_left _ _).trans hyB
  have hy3log : Real.log 3 ≤ y := (le_max_left (Real.log 3) 12).trans ((le_max_right _ _).trans hyB)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  let N := omittedPrimorial p y
  let h := Nat.log 2 (N + 2)
  have hN : 0 < N := omittedPrimorial_pos p y
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN := log_omittedPrimorial p y hp hyp
  change Real.log (N : ℝ) = _ at hlogN
  have hyθ' : (1 / 2 : ℝ) < Chebyshev.theta (y : ℝ) / y ∧
      Chebyshev.theta (y : ℝ) / y < 2 := hyθ
  have hloθ := (lt_div_iff₀ hypos).mp hyθ'.1
  have hhiθ := (div_lt_iff₀ hypos).mp hyθ'.2
  have hlN : (y : ℝ) / 3 ≤ Real.log (N : ℝ) := by linarith
  have huN : Real.log (N : ℝ) ≤ 2 * (y : ℝ) := by
    have hpLog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
    linarith
  have hlogNaddUpper : Real.log ((N : ℝ) + 2) ≤ Real.log (N : ℝ) + Real.log 3 := by
    rw [← Real.log_mul (by positivity) (by norm_num : (3 : ℝ) ≠ 0)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlogNaddLower : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hpowlo : (2 : ℝ) ^ h ≤ (N : ℝ) + 2 := by
    exact_mod_cast Nat.pow_log_le_self 2 (show N + 2 ≠ 0 by omega)
  have hpowhi : (N : ℝ) + 2 < (2 : ℝ) ^ (h + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (N + 2)
  have hLogLo := Real.log_le_log (by positivity) hpowlo
  have hLogHi := Real.log_lt_log (by positivity) hpowhi
  rw [Real.log_pow] at hLogLo hLogHi
  push_cast at hLogHi
  have hlog2a : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2b : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hh0 : (0 : ℝ) ≤ h := by positivity
  have hhlo : (y : ℝ) / 4 ≤ (h : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left hlog2b (show (0 : ℝ) ≤ (h : ℝ) + 1 by positivity)
    linarith
  have hhhi : (h : ℝ) ≤ 6 * (y : ℝ) := by
    have hc := mul_le_mul_of_nonneg_left hlog2a hh0
    linarith
  have hloSq : ((y : ℝ) / 4) ^ 2 ≤ (h : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hhlo _
  have hhiSq : (h : ℝ) ^ 2 ≤ (6 * (y : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hh0 hhhi _
  change (y : ℝ)^2 / (16 * (p : ℝ)) ≤ (skirtQ N : ℝ) / (p : ℝ) ∧
    (skirtQ N : ℝ) / (p : ℝ) ≤ 36 * (y : ℝ)^2
  have hQ : (skirtQ N : ℝ) = (h : ℝ)^2 := by simp [skirtQ, h]
  rw [hQ]
  constructor
  · apply (div_le_div_iff₀ (by positivity : 0 < 16 * (p : ℝ)) hpR).2
    nlinarith [mul_le_mul_of_nonneg_right hloSq hpR.le]
  · calc
      _ ≤ (h : ℝ) ^ 2 := div_le_self (by positivity) hp1
      _ ≤ (6 * (y : ℝ)) ^ 2 := hhiSq
      _ = _ := by ring

private theorem primesUpTo_eq (y : ℕ) : primesUpTo y = y.primesLE := by
  ext q
  simp only [mem_primesUpTo, Nat.mem_primesLE, and_comm]

theorem eventually_prime_reciprocal_tail_le (X : ℕ → ℝ)
    (hX : ∀ᶠ y : ℕ in atTop, X y ≤ 72 * (y : ℝ) ^ 2) :
    ∀ᶠ y : ℕ in atTop,
      (∑ q ∈ (Nat.primesLE ⌊X y⌋₊ \ Nat.primesLE y), 1 / (q : ℝ)) ≤ 3 / 4 := by
  let z (y : ℕ) : ℝ := (y : ℝ) ^ (33 / 16 : ℝ)
  have ht0 := tendsto_natCast_atTop_atTop (R := ℝ)
  have htz : Tendsto z atTop atTop := (tendsto_rpow_atTop (by norm_num)).comp ht0
  have hpow : ∀ᶠ y : ℕ in atTop, (72 : ℝ) ≤ (y : ℝ) ^ (1 / 16 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 16)).comp ht0).eventually_ge_atTop 72
  obtain ⟨C, hC, hM⟩ := mertensSecond
  have herror_y : ∀ᶠ y : ℕ in atTop, C / Real.log (y : ℝ) < 1 / 100 := by
    have ht : Tendsto (fun n : ℕ => C / Real.log (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp ht0)
    exact ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  have herror_z : ∀ᶠ y : ℕ in atTop, C / Real.log (z y) < 1 / 100 := by
    have ht : Tendsto (fun n : ℕ => C / Real.log (z n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp htz)
    exact ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 100))
  filter_upwards [hX, hpow, herror_y, herror_z, eventually_ge_atTop 2] with y hyX hyPow hyErr hzErr hy2
  have hy2R : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  have hypos : (0 : ℝ) < y := by linarith
  have hylogpos : 0 < Real.log (y : ℝ) := Real.log_pos (by linarith)
  have hyz : (y : ℝ) ≤ z y := by
    unfold z
    conv_lhs => rw [← Real.rpow_one (y : ℝ)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hXz : X y ≤ z y := by
    apply hyX.trans
    calc
      _ ≤ (y : ℝ) ^ 2 * (y : ℝ) ^ (1 / 16 : ℝ) := by
        rw [mul_comm 72]
        exact mul_le_mul_of_nonneg_left hyPow (by positivity)
      _ = z y := by
        rw [← Real.rpow_natCast (y : ℝ) 2, ← Real.rpow_add hypos]
        norm_num [z]
  have hsub : primesUpTo y ⊆ primesUpTo ⌊z y⌋₊ := by
    rw [primesUpTo_eq, primesUpTo_eq]
    exact Nat.primesLE_mono (by simpa using Nat.floor_mono hyz)
  have hupper := (abs_le.mp (hM (z y) (hy2R.trans hyz))).2
  have hlower := (abs_le.mp (hM (y : ℝ) hy2R)).1
  rw [Nat.floor_natCast] at hlower
  have hlogz : Real.log (z y) = (33 / 16 : ℝ) * Real.log (y : ℝ) :=
    Real.log_rpow hypos _
  have hloglog : Real.log (Real.log (z y)) - Real.log (Real.log (y : ℝ)) =
      Real.log (33 / 16 : ℝ) := by
    rw [hlogz, Real.log_mul (by norm_num) hylogpos.ne', add_sub_cancel_right]
  have hconstant : Real.log (33 / 16 : ℝ) < 73 / 100 := by
    have h1 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 33 / 32)
    have hh : Real.log (33 / 16 : ℝ) = Real.log 2 + Real.log (33 / 32 : ℝ) := by
      rw [show (33 / 16 : ℝ) = 2 * (33 / 32) by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
    rw [hh]
    linarith [Real.log_two_lt_d9]
  have hdiff : (∑ q ∈ primesUpTo ⌊z y⌋₊ \ primesUpTo y, 1 / (q : ℝ)) =
      primeReciprocalSum ⌊z y⌋₊ - primeReciprocalSum y := by
    apply eq_sub_of_add_eq
    exact Finset.sum_sdiff hsub
  calc
    _ ≤ ∑ q ∈ primesUpTo ⌊z y⌋₊ \ primesUpTo y, 1 / (q : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · rw [primesUpTo_eq, primesUpTo_eq]
        exact Finset.sdiff_subset_sdiff (Nat.primesLE_mono (Nat.floor_mono hXz)) (fun _ h => h)
      · intro q _ _
        positivity
    _ ≤ 3 / 4 := by
      rw [hdiff]
      linarith only [hupper, hlower, hloglog, hconstant, hyErr, hzErr]

theorem eventually_scale_prime_reciprocal_tail_le (p : ℕ) (hp : p.Prime) :
    ∀ᶠ y : ℕ in atTop,
      (∑ q ∈ (Nat.primesLE ⌊2 * scale p y⌋₊ \ Nat.primesLE y), 1 / (q : ℝ)) ≤ 3 / 4 := by
  apply eventually_prime_reciprocal_tail_le
  filter_upwards [eventually_scale_bounds p hp] with y hy
  linarith only [hy.2]

theorem tendsto_scale (p : ℕ) (hp : p.Prime) : Tendsto (scale p) atTop atTop := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hySq : Tendsto (fun y : ℕ => (y : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlo : Tendsto (fun y : ℕ => (y : ℝ) ^ 2 / (16 * (p : ℝ))) atTop atTop :=
    hySq.atTop_div_const (by positivity)
  exact tendsto_atTop_mono' atTop ((eventually_scale_bounds p hp).mono fun _ h => h.1) hlo

theorem eventually_prime_count_error (p : ℕ) (hp : p.Prime)
    (M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∀ᶠ y : ℕ in atTop,
      M * (1 + ((Nat.primesLE ⌊2 * scale p y⌋₊).card : ℝ)) ≤ ε * scale p y := by
  have hx := tendsto_scale p hp
  have h2x : Tendsto (fun y : ℕ => 2 * scale p y) atTop atTop := hx.const_mul_atTop (by norm_num)
  have hpcount := h2x.eventually (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  have hlimit1 : Tendsto (fun y : ℕ => M / scale p y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hx
  have hlimit2 : Tendsto (fun y : ℕ => (2 * M * (Real.log 4 + 1)) / Real.log (2 * scale p y))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp h2x)
  have heps : (0 : ℝ) < ε / 2 := by positivity
  filter_upwards [hx.eventually_gt_atTop 0, hpcount, hlimit1.eventually (gt_mem_nhds heps),
    hlimit2.eventually (gt_mem_nhds heps)] with y hy hπ h₁ h₂
  let x := scale p y
  let π := ((Nat.primesLE ⌊2 * x⌋₊).card : ℝ)
  have hπ' : π ≤ (Real.log 4 + 1) * (2 * x) / Real.log (2 * x) := by
    simpa only [x, π, Nat.primesLE_card_eq_primeCounting] using hπ
  have hA : M ≤ (ε / 2) * x := (div_le_iff₀ hy).mp h₁.le
  have hB : M * π ≤ (ε / 2) * x := calc
    _ ≤ M * ((Real.log 4 + 1) * (2 * x) / Real.log (2 * x)) :=
      mul_le_mul_of_nonneg_left hπ' hM
    _ = (2 * M * (Real.log 4 + 1) / Real.log (2 * x)) * x := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h₂.le hy.le
  change M * (1 + π) ≤ ε * x
  nlinarith only [hA, hB]

def natScale (p y : ℕ) : ℕ := skirtQ (omittedPrimorial p y) / p

def natBand (p y : ℕ) : Finset ℕ := (Ioc y (2 * natScale p y)).filter Nat.Prime

theorem floor_scale (p y : ℕ) : ⌊scale p y⌋₊ = natScale p y := by
  unfold scale natScale
  exact Nat.floor_div_eq_div _ _

theorem natScale_le_scale (p y : ℕ) : (natScale p y : ℝ) ≤ scale p y := by
  rw [← floor_scale]
  exact Nat.floor_le (by unfold scale; positivity)

private theorem scale_le_two_mul_natScale (p y : ℕ) (h : (2 : ℝ) ≤ scale p y) :
    scale p y ≤ 2 * (natScale p y : ℝ) := by
  have hfloor := Nat.lt_floor_add_one (scale p y)
  rw [floor_scale] at hfloor
  have hX : (1 : ℝ) ≤ natScale p y := by linarith
  linarith

private theorem natBand_subset_realBand (p y : ℕ) :
    natBand p y ⊆ Nat.primesLE ⌊2 * scale p y⌋₊ \ Nat.primesLE y := by
  intro q hq
  have hq' : (y < q ∧ q ≤ 2 * natScale p y) ∧ q.Prime := by
    simpa only [natBand, mem_filter, mem_Ioc] using hq
  obtain ⟨⟨hy, hqup⟩, hqprime⟩ := hq'
  refine Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨?_, hqprime⟩, ?_⟩
  · have hup : (q : ℝ) ≤ 2 * (natScale p y : ℝ) := by exact_mod_cast hqup
    exact Nat.le_floor (hup.trans (by linarith only [natScale_le_scale p y]))
  · intro h
    exact (not_le_of_gt hy) (Nat.mem_primesLE.mp h).1

theorem eventually_nat_reciprocal_tail_le (p : ℕ) (hp : p.Prime) :
    ∀ᶠ y : ℕ in atTop, (∑ q ∈ natBand p y, 1 / (q : ℝ)) ≤ 3 / 4 := by
  filter_upwards [eventually_scale_prime_reciprocal_tail_le p hp] with y h
  exact (Finset.sum_le_sum_of_subset_of_nonneg (f := fun q : ℕ => (1 : ℝ) / (q : ℝ))
    (natBand_subset_realBand p y) (fun q _ _ => by positivity)).trans h

theorem eventually_nat_prime_count_error (p : ℕ) (hp : p.Prime) (E : ℝ) (hE : 0 ≤ E) :
    ∀ᶠ y : ℕ in atTop, E * (1 + ((natBand p y).card : ℝ)) ≤ (natScale p y : ℝ) / 576 := by
  filter_upwards [(tendsto_scale p hp).eventually_ge_atTop (2 : ℝ),
    eventually_prime_count_error p hp E (1 / 1152) hE (by norm_num)] with y hy h
  have hcard : ((natBand p y).card : ℝ) ≤ (Nat.primesLE ⌊2 * scale p y⌋₊).card := by
    exact_mod_cast Finset.card_le_card ((natBand_subset_realBand p y).trans Finset.sdiff_subset)
  calc
    _ ≤ E * (1 + ((Nat.primesLE ⌊2 * scale p y⌋₊).card : ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith only [hcard]) hE
    _ ≤ (1 / 1152) * scale p y := h
    _ ≤ _ := by linarith only [scale_le_two_mul_natScale p y hy]

theorem eventually_Q_le_two_mul_natScale (p : ℕ) (hp : p.Prime) :
    ∀ᶠ y : ℕ in atTop, skirtQ (omittedPrimorial p y) ≤ 2 * p * natScale p y := by
  filter_upwards [(tendsto_scale p hp).eventually_ge_atTop (2 : ℝ)] with y hy
  have h := scale_le_two_mul_natScale p y hy
  unfold scale at h
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h' := (div_le_iff₀ hpR).mp h
  rw [mul_right_comm] at h'
  exact_mod_cast h'

end GoldbachSkirtHarmonic



namespace GoldbachSkirtSurvivors

open Finset

/-- No more than the full initial-interval count of multiples of `k`. -/
private theorem band_multiples_le (X k : ℕ) :
    ((Ioc X (2*X)).filter fun d => k ∣ d).card ≤ (2*X)/k := by
  apply le_trans (Finset.card_le_card ?_) (Nat.card_multiples' (2*X) k).le
  intro d hd
  rcases Finset.mem_filter.mp hd with ⟨hband,hdiv⟩
  rcases Finset.mem_Ioc.mp hband with ⟨hl,hu⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hu), by omega, hdiv⟩

/-- The total loss from square factors with base above a fixed sieve threshold. -/
theorem square_loss (X R : ℕ) (hR : 0 < R) :
    (((Ioc R (2*X)).biUnion
      (fun r => (Ioc X (2*X)).filter fun d => r*r ∣ d)).card : ℝ) ≤ 2*(X : ℝ)/(R : ℝ) := by
  by_cases hRX : R ≤ 2*X
  · calc
      _ ≤ ∑ r ∈ Ioc R (2*X), (((Ioc X (2*X)).filter fun d => r*r ∣ d).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ r ∈ Ioc R (2*X), (2*(X : ℝ))*(((r : ℝ)^2)⁻¹) := by
        apply Finset.sum_le_sum
        intro r hr
        calc
          _ ≤ (((2*X)/(r*r) : ℕ) : ℝ) := by exact_mod_cast band_multiples_le X (r*r)
          _ ≤ 2*(X : ℝ)*(((r : ℝ)^2)⁻¹) := by
            rw [← div_eq_mul_inv, pow_two]
            simpa only [Nat.cast_mul, Nat.cast_ofNat] using
              (Nat.cast_div_le (α := ℝ) (m := 2*X) (n := r*r))
      _ = 2*(X : ℝ) * (∑ r ∈ Ioc R (2*X), (((r : ℝ)^2)⁻¹)) := by
        rw [Finset.mul_sum]
      _ ≤ _ := by
        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (sum_Ioc_inv_sq_le_sub hR.ne' hRX).trans (sub_le_self _ (by positivity))
  · have hempty : Ioc R (2*X) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr (fun _ hi =>
        hRX (((Finset.mem_Ioc.mp hi).1.le).trans (Finset.mem_Ioc.mp hi).2))
    simp [hempty]
    positivity

/-- A squarefree integer avoiding p and all primes greater than y divides the omitted-prime product. -/
theorem dvd_omitted {p y d : ℕ} (hsq : Squarefree d) (hp : ¬p ∣ d)
    (hsmooth : ∀ q : ℕ, q.Prime → q ∣ d → q ≤ y) :
    d ∣ ∏ r ∈ (Icc 2 y).filter (fun r => r.Prime ∧ r ≠ p), r := by
  rw [← Nat.prod_primeFactors_of_squarefree hsq]
  apply Finset.prod_dvd_prod_of_subset
  intro q hq
  obtain ⟨hprime, hdvd, _⟩ := Nat.mem_primeFactors.mp hq
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_Icc.mpr ⟨hprime.two_le, hsmooth q hprime hdvd⟩,
      hprime, fun heq => hp (heq ▸ hdvd)⟩

/-- Surviving elements of the band satisfy the frozen divisor and denominator conditions. -/
theorem band_mem_divisors {p y Q d : ℕ} (hp : 0 < p)
    (hd : d ∈ Ioc (Q/p) (2*(Q/p))) (hsq : Squarefree d) (hnp : ¬p ∣ d)
    (hsmooth : ∀ q : ℕ, q.Prime → q ∣ d → q ≤ y) :
    let N := ∏ r ∈ (Icc 2 y).filter (fun r => r.Prime ∧ r ≠ p), r
    d ∈ N.divisors.filter (fun e => Q < p*e ∧ p*e ≤ 2*Q) := by
  let N := ∏ r ∈ (Icc 2 y).filter (fun r => r.Prime ∧ r ≠ p), r
  have hN : 0 < N := Finset.prod_pos (fun r hr => ((Finset.mem_filter.mp hr).2.1).pos)
  change d ∈ N.divisors.filter (fun e => Q < p*e ∧ p*e ≤ 2*Q)
  obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hd
  have hl' := (Nat.div_lt_iff_lt_mul hp).mp hl
  have hu' := Nat.mul_le_mul_left p hu
  have hx : p*(Q/p) ≤ Q := by rw [mul_comm]; exact Nat.div_mul_le_self Q p
  exact Finset.mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨dvd_omitted hsq hnp hsmooth, hN.ne'⟩,
      by simpa [mul_comm] using hl',
      hu'.trans (by rw [← mul_assoc, mul_comm p 2, mul_assoc]; gcongr)⟩


/-- A periodic sieve with low harmonic tail and small counting errors leaves enough divisors. -/
theorem survivor_count {p y R X : ℕ} (hp : 0 < p) (hR : 1152 ≤ R)
    (good : ℕ → Prop) [DecidablePred good] (δ E : ℝ)
    (hδ : 1/36 ≤ δ)
    (hgoodp : ∀ d, good d → ¬p ∣ d)
    (hgoodsq : ∀ d, good d → ∀ r, r.Prime → r ≤ R → ¬r*r ∣ d)
    (hcount : δ*(X : ℝ)-E ≤ (((Ioc X (2*X)).filter good).card : ℝ))
    (hper : ∀ q ∈ (Ioc y (2*X)).filter Nat.Prime,
      (((Ioc X (2*X)).filter (fun d => good d ∧ q ∣ d)).card : ℝ) ≤
        δ*(X : ℝ)*(q : ℝ)⁻¹ + E)
    (htail : (∑ q ∈ (Ioc y (2*X)).filter Nat.Prime, (q : ℝ)⁻¹) ≤ 3/4)
    (herror : E*(1+(((Ioc y (2*X)).filter Nat.Prime).card : ℝ)) ≤ (X : ℝ)/576)
    (Q : ℕ) (hX : X = Q/p) :
    let N := ∏ r ∈ (Icc 2 y).filter (fun r => r.Prime ∧ r ≠ p), r
    (X : ℝ)/288 ≤ ((N.divisors.filter (fun d => Q < p*d ∧ p*d ≤ 2*Q)).card : ℝ) := by
  let N := ∏ r ∈ (Icc 2 y).filter (fun r => r.Prime ∧ r ≠ p), r
  let D := N.divisors.filter (fun d => Q < p*d ∧ p*d ≤ 2*Q)
  let G := (Ioc X (2*X)).filter good
  let primes := (Ioc y (2*X)).filter Nat.Prime
  let badPrime := primes.biUnion (fun q => (Ioc X (2*X)).filter fun d => good d ∧ q ∣ d)
  let badSquare := (Ioc R (2*X)).biUnion (fun r => (Ioc X (2*X)).filter fun d => r*r ∣ d)
  have hδnn : 0 ≤ δ := by linarith only [hδ]
  have hXnn : 0 ≤ (X : ℝ) := Nat.cast_nonneg X
  have hpbound : (badPrime.card : ℝ) ≤ 3/4*(δ*(X : ℝ)) + E*(primes.card : ℝ) := by
    calc
      _ ≤ ∑ q ∈ primes, (((Ioc X (2*X)).filter (fun d => good d ∧ q ∣ d)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ q ∈ primes, (δ*(X : ℝ)*(q : ℝ)⁻¹ + E) := Finset.sum_le_sum hper
      _ = δ*(X : ℝ)*(∑ q ∈ primes, (q : ℝ)⁻¹) + E*(primes.card : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
        simp [nsmul_eq_mul, mul_comm]
      _ ≤ _ := by
        apply add_le_add_left _ _
        calc
          _ ≤ δ*(X : ℝ)*(3/4) := mul_le_mul_of_nonneg_left htail (mul_nonneg hδnn hXnn)
          _ = _ := by ring
  have hsbound : (badSquare.card : ℝ) ≤ (X : ℝ)/576 := by
    have hRp : 0 < R := by omega
    have hRR : (1152 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    calc
      _ ≤ 2*(X : ℝ)/(R : ℝ) := square_loss X R hRp
      _ ≤ 2*(X : ℝ)/1152 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hRR
      _ = _ := by ring
  have hgoodSub : G \ (badPrime ∪ badSquare) ⊆ D := by
    intro d hd
    obtain ⟨hG, hbad⟩ := Finset.mem_sdiff.mp hd
    obtain ⟨hI, hdgood⟩ := Finset.mem_filter.mp hG
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hI
    have hdpos : 0 < d := by omega
    have hs : Squarefree d := by
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro r hr hsq
      by_cases hrR : r ≤ R
      · exact hgoodsq d hdgood r hr hrR hsq
      · have hrd : r ∣ d := dvd_trans (dvd_mul_right r r) hsq
        have hrX := (Nat.le_of_dvd hdpos hrd).trans hu
        exact hbad (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨r, Finset.mem_Ioc.mpr ⟨lt_of_not_ge hrR, hrX⟩, Finset.mem_filter.mpr ⟨hI,hsq⟩⟩))
    have hsmooth : ∀ q : ℕ, q.Prime → q ∣ d → q ≤ y := by
      intro q hq hqd
      by_contra hqy
      have hqX := (Nat.le_of_dvd hdpos hqd).trans hu
      have hqP : q ∈ primes :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨lt_of_not_ge hqy, hqX⟩, hq⟩
      exact hbad (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨q,hqP,Finset.mem_filter.mpr ⟨hI,hdgood,hqd⟩⟩))
    exact band_mem_divisors hp (by simpa only [← hX] using hI) hs (hgoodp d hdgood) hsmooth
  have hcomb : (G.card : ℝ) ≤ (D.card : ℝ) + (badPrime.card : ℝ) + (badSquare.card : ℝ) := by
    exact_mod_cast calc
      G.card ≤ (G \ (badPrime ∪ badSquare)).card + (badPrime ∪ badSquare).card :=
        Finset.card_le_card_sdiff_add_card
      _ ≤ D.card + (badPrime.card + badSquare.card) :=
        Nat.add_le_add (Finset.card_le_card hgoodSub) (Finset.card_union_le _ _)
      _ = _ := (Nat.add_assoc _ _ _).symm
  have hlower : (1/36 : ℝ)*(X : ℝ) ≤ δ*(X : ℝ) := mul_le_mul_of_nonneg_right hδ hXnn
  change (X : ℝ)/288 ≤ (D.card : ℝ)
  change δ*(X : ℝ)-E ≤ (G.card : ℝ) at hcount
  change E*(1+(primes.card : ℝ)) ≤ (X : ℝ)/576 at herror
  nlinarith only [hcount, hpbound, hsbound, hcomb, hlower, herror]

end GoldbachSkirtSurvivors
open Finset Filter GoldbachSieve GoldbachSkirtHarmonic

theorem Conjectures.Cuts.Task85565ada5b6d7ee4d3536a3d : (
  have x1 : ℕ → ℕ → ℕ := fun (x1 x2 : ℕ) => ∏ x3 ∈ Finset.Icc (2 : ℕ) x2 with Nat.Prime x3 ∧ x3 ≠ x1, x3; have x2 : ℕ → ℕ := fun (x2 : ℕ) => Nat.log (2 : ℕ) (x2 + (2 : ℕ)) ^ (2 : ℕ); ∀ (x3 : ℕ),   Nat.Prime x3 →     (3 : ℕ) ≤ x3 →       ∃ (x6 : ℝ),         (0 : ℝ) < x6 ∧           ∃ (x7 : ℕ),             ∀ (x8 : ℕ),               x7 ≤ x8 →                 have x10 : ℕ := x1 x3 x8;                 have x11 : Finset ℕ := {x11 ∈ x10.divisors | x2 x10 < x3 * x11 ∧ x3 * x11 ≤ (2 : ℕ) * x2 x10};                 x6 * ↑(x2 x10) ≤ ↑x11.card
) := by
  classical
  dsimp only
  intro p hp hp3
  let R := max p 1152
  let M := R.factorial ^ 2
  have hpR : p ≤ R := le_max_left _ _
  have hRbig : 1152 ≤ R := le_max_right _ _
  have hM : 0 < M := pow_pos (Nat.factorial_pos R) 2
  let : NeZero M := ⟨hM.ne'⟩
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  let good := sieveGood p R
  let mass : ℝ := Nat.count good M
  let δ := mass / (M : ℝ)
  let E := 2 * mass
  have hδ : 1/36 ≤ δ := by
    change (1/36 : ℝ) ≤ mass / (M : ℝ)
    apply (le_div_iff₀ hMR).mpr
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using sieveGood_count_density hp hp3 hpR
  have hmass : 0 ≤ mass := Nat.cast_nonneg _
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hGood (n : ℕ) : good (n % M) ↔ good n := sieveGood_mod hp hpR n
  have hgoodp (n : ℕ) (hn : good n) : ¬p ∣ n := hn.1
  have hgoodsq (n : ℕ) (hn : good n) (r : ℕ) (hr : r.Prime) (hrR : r ≤ R) : ¬r*r ∣ n := by
    intro hsq
    by_cases hrp : r = p
    · exact hn.1 (hrp ▸ (dvd_mul_right r r).trans hsq)
    · exact hn.2 r (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr.two_le, hrR⟩, hr, hrp⟩)
        (by simpa only [pow_two] using hsq)
  have hEventually : ∀ᶠ y : ℕ in atTop, R ≤ y ∧
      (∑ q ∈ natBand p y, 1 / (q : ℝ)) ≤ 3/4 ∧
      E * (1 + ((natBand p y).card : ℝ)) ≤ (natScale p y : ℝ) / 576 ∧
      skirtQ (omittedPrimorial p y) ≤ 2 * p * natScale p y := by
    filter_upwards [eventually_ge_atTop R, eventually_nat_reciprocal_tail_le p hp,
      eventually_nat_prime_count_error p hp E hE, eventually_Q_le_two_mul_natScale p hp]
      with y hy ht he hq
    exact ⟨hy, ht, he, hq⟩
  obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp hEventually
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  refine ⟨1/(576*(p : ℝ)), by positivity, Y, ?_⟩
  intro y hy
  obtain ⟨hyR, htail, herror, hQbound⟩ := hY y hy
  let N := omittedPrimorial p y
  let Q := skirtQ N
  let X := natScale p y
  let D := N.divisors.filter (fun d => Q < p*d ∧ p*d ≤ 2*Q)
  change (1/(576*(p : ℝ))) * (Q : ℝ) ≤ (D.card : ℝ)
  have hXY : X ≤ 2*X := by omega
  have hLen : 2*X-X = X := by omega
  have hcount : δ*(X : ℝ)-E ≤ (((Ioc X (2*X)).filter good).card : ℝ) := by
    have h := (abs_le.mp
      (GoldbachSkirtPeriodic.good_Ioc_discrepancy M X (2*X) good hGood hXY)).1
    rw [hLen] at h
    change -mass ≤ (((Ioc X (2*X)).filter good).card : ℝ) - (X : ℝ)*mass/(M : ℝ) at h
    have heq : (X : ℝ)*mass/(M : ℝ) = δ*(X : ℝ) := by dsimp [δ]; ring
    dsimp only [E]
    linarith only [h, heq, hmass]
  have hper : ∀ q ∈ natBand p y,
      (((Ioc X (2*X)).filter fun d => good d ∧ q ∣ d).card : ℝ) ≤
        δ*(X : ℝ)*(q : ℝ)⁻¹ + E := by
    intro q hq
    obtain ⟨hqband, hprime⟩ := Finset.mem_filter.mp hq
    have hRq := hyR.trans_lt (Finset.mem_Ioc.mp hqband).1
    have hc : q.Coprime M := prime_coprime_sieve_period hprime hRq
    have h := GoldbachSkirtPeriodic.good_Ioc_multiples_upper M X (2*X) q good hGood
      hXY hprime.pos hc
    rw [hLen] at h
    change _ ≤ (X : ℝ)*mass/((q : ℝ)*(M : ℝ)) + E at h
    convert h using 1
    dsimp [δ]
    ring
  have htail' : (∑ q ∈ natBand p y, (q : ℝ)⁻¹) ≤ 3/4 := by
    simpa only [one_div] using htail
  have hcountD : (X : ℝ)/288 ≤ (D.card : ℝ) :=
    GoldbachSkirtSurvivors.survivor_count hp.pos hRbig good δ E hδ hgoodp hgoodsq hcount hper
      htail' herror Q rfl
  have hQ : (Q : ℝ) ≤ 2 * (p : ℝ) * (X : ℝ) := by exact_mod_cast hQbound
  apply le_trans _ hcountD
  rw [one_div_mul_eq_div]
  apply (div_le_iff₀ (by positivity : 0 < 576 * (p : ℝ))).mpr
  calc
    _ ≤ 2 * (p : ℝ) * (X : ℝ) := hQ
    _ = _ := by ring
