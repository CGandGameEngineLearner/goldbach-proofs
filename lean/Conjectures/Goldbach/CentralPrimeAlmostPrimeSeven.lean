import Mathlib

/-!
# Seven-factor counting at a prime-square center

Fixed-parameter Richert weights, the arithmetic progression reduction, and the
square correction for the TH-8000 window. The terminal counting implication
below takes a lower bound on the weighted sifted sum as an explicit hypothesis.

The factor-budget argument is adapted from LonelyQuantum/goldbach-proofs,
research/diagnostics/RichertFactorBudget.lean, revision
36b0d52d9585d07feeb93da6ac3b8de09b36f018 (Apache-2.0).
The square-error section identifies a further Apache-2.0 source below.
Analytic context: Cai and Lu, Chen's theorem in short intervals,
Acta Arithmetica 91 (1999), pp. 311–323, Lemmas 1–3.
-/

section
namespace GoldbachRichert

/-- The Richert penalty, with each prime counted with multiplicity. -/
noncomputable def penalty (a : ℕ) (y : ℝ) : ℝ :=
  a.factorization.sum fun q e => (e : ℝ) * max (1 - Real.log q / Real.log y) 0

theorem factor_budget (a : ℕ) (y : ℝ) :
    (ArithmeticFunction.cardFactors a : ℝ) - Real.log a / Real.log y ≤ penalty a y := by
  rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Real.log_nat_eq_sum_factorization]
  simp only [penalty, Finsupp.sum, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro q _
  calc
    _ = (a.factorization q : ℝ) * (1 - Real.log q / Real.log y) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg _)

/-- A positive total weight certifies elements with at most r prime factors. -/
theorem weighted_count_le (A : Finset ℕ) (r : ℕ) (y b lam : ℝ) (hlam : 0 < lam)
    (hsize : ∀ a ∈ A, Real.log a / Real.log y ≤ b)
    (hbudget : b + lam ≤ (r : ℝ) + 1) :
    (∑ a ∈ A, (1 - penalty a y / lam)) ≤
      ((A.filter fun a => ArithmeticFunction.cardFactors a ≤ r).card : ℝ) := by
  calc
    _ ≤ ∑ a ∈ A, (if ArithmeticFunction.cardFactors a ≤ r then (1 : ℝ) else 0) := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases good : ArithmeticFunction.cardFactors a ≤ r
      · simp only [good, ↓reduceIte]
        have hn : 0 ≤ penalty a y := by
          unfold penalty Finsupp.sum
          apply Finset.sum_nonneg
          intro q _
          exact mul_nonneg (Nat.cast_nonneg _) (le_max_right _ _)
        linarith [div_nonneg hn hlam.le]
      · simp only [good, ↓reduceIte]
        have hc : r + 1 ≤ ArithmeticFunction.cardFactors a := Nat.lt_iff_add_one_le.mp (Nat.lt_of_not_ge good)
        have hcr : (r : ℝ) + 1 ≤ (ArithmeticFunction.cardFactors a : ℝ) := by exact_mod_cast hc
        have hp : lam ≤ penalty a y := by linarith [factor_budget a y, hsize a ha]
        linarith [(one_le_div hlam).mpr hp]
    _ = _ := by simp [Finset.sum_boole]

end GoldbachRichert
end

section
namespace GoldbachCentralSeven

open Finset

/-- The standard representative used in the progression distribution estimate. -/
def crtClass (p d b k : ℕ) : ℕ :=
  if hc : d.Coprime k then Nat.chineseRemainder hc b (2*p^2) else 0

theorem crtClass_data {p d b k : ℕ} (hd : 0 < d) (hk : 0 < k) (hc : d.Coprime k) :
    crtClass p d b k < d*k ∧
    Nat.ModEq d (crtClass p d b k) b ∧ Nat.ModEq k (crtClass p d b k) (2*p^2) := by
  simp only [crtClass, dite_eq_left hc]
  exact ⟨Nat.chineseRemainder_lt_mul hc b (2*p^2) hd.ne' hk.ne',
    (Nat.chineseRemainder hc b (2*p^2)).property⟩

private theorem coprime_of_ap_class {a b d : ℕ} (hm : Nat.ModEq d a b) (hb : b.Coprime d) :
    a.Coprime d := by
  unfold Nat.ModEq at hm
  change a.gcd d = 1
  rw [Nat.gcd_comm a d, Nat.gcd_rec, hm, ← Nat.gcd_rec, Nat.gcd_comm d b]
  exact hb

/-- Reducedness uses k<p and parity away from 2; no progression theorem is assumed. -/
theorem crtClass_reduced {p d b k : ℕ} (hp : p.Prime) (hd : 0 < d) (hk : 0 < k)
    (hkp : k < p) (hc : d.Coprime k) (hk2 : Nat.Coprime 2 k) (hb : b.Coprime d) :
    (crtClass p d b k).Coprime (d*k) := by
  obtain ⟨_, h1, h2⟩ := crtClass_data (p := p) (b := b) hd hk hc
  have hpk := Nat.coprime_of_lt_prime hk.ne' hkp hp
  exact Nat.coprime_mul_iff_right.mpr ⟨coprime_of_ap_class h1 hb,
    coprime_of_ap_class h2 (hk2.mul_left (hpk.pow_left 2))⟩

theorem crtClass_iff {p d b k t : ℕ} (hd : 0 < d) (hk : 0 < k) (hc : d.Coprime k) :
    Nat.ModEq (d*k) t (crtClass p d b k) ↔ Nat.ModEq d t b ∧ Nat.ModEq k t (2*p^2) := by
  obtain ⟨_, h1, h2⟩ := crtClass_data (p := p) (b := b) hd hk hc
  constructor
  · intro h
    obtain ⟨hd', hk'⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hc).mpr h
    exact ⟨hd'.trans h1, hk'.trans h2⟩
  · rintro ⟨h1',h2'⟩
    simpa only [crtClass, dite_eq_left hc] using Nat.chineseRemainder_modEq_unique hc h1' h2'

theorem reflected_dvd_iff {X h k : ℕ} (hh : h ≤ X) :
    k ∣ X-h ↔ Nat.ModEq k (X+h) (2*X) := by
  rw [Nat.modEq_iff_dvd' (by omega), show 2*X-(X+h)=X-h by omega]

/-- The other admissibility condition excludes the prime factors of d from the
    reflected sieve source. -/
theorem reflected_coprime_fixed {X h d b : ℕ} (hh : h ≤ X) (hb : b ≤ 2*X)
    (ht : Nat.ModEq d (X+h) b) (hadm : (2*X-b).Coprime d) : (X-h).Coprime d := by
  have heq : Nat.ModEq d ((X+h)+(X-h)) (b+(2*X-b)) := by
    rw [show X+h+(X-h)=2*X by omega, show b+(2*X-b)=2*X by omega]
  exact coprime_of_ap_class (Nat.ModEq.add_left_cancel' b ((ht.add_right (X-h)).symm.trans heq)) hadm

def sievedAPOffsets (p H d b k : ℕ) := (Icc 1 H).filter (fun h =>
  (p^2+h).Prime ∧ Nat.ModEq d (p^2+h) b ∧ k ∣ p^2-h)

def shortAPPrimes (X H q a : ℕ) := (Ioc X (X+H)).filter (fun t => t.Prime ∧ t % q = a)

/-- Exact transport from positive offsets to the strict-left, closed-right AP
    window of the short-interval distribution theorem. -/
theorem rho_count_eq_short_AP {p H d b k : ℕ} (hH : H ≤ p^2) (hd : 0 < d)
    (hk : 0 < k) (hc : d.Coprime k) :
    (sievedAPOffsets p H d b k).card =
      (shortAPPrimes (p^2) H (d*k) (crtClass p d b k)).card := by
  have hrep := (crtClass_data (p := p) (b := b) hd hk hc).1
  have hmem (h : ℕ) (hh : h ≤ p^2) :
      p^2+h ∈ shortAPPrimes (p^2) H (d*k) (crtClass p d b k) ↔
        h ∈ sievedAPOffsets p H d b k := by
    simp only [shortAPPrimes, sievedAPOffsets, mem_filter, mem_Ioc, mem_Icc]
    have hm : (p^2+h) % (d*k) = crtClass p d b k ↔
        Nat.ModEq d (p^2+h) b ∧ k ∣ p^2-h := by
      rw [reflected_dvd_iff hh, ← crtClass_iff hd hk hc]
      simp only [Nat.ModEq, Nat.mod_eq_of_lt hrep]
    rw [hm]
    have hw : p^2 < p^2+h ∧ p^2+h ≤ p^2+H ↔ 1 ≤ h ∧ h ≤ H := by omega
    rw [hw]
  refine card_bij' (fun h _ => p^2+h) (fun t _ => t-p^2) ?_ ?_ ?_ ?_
  · intro h hh
    exact (hmem h ((mem_Icc.mp (mem_filter.mp hh).1).2.trans hH)).mpr hh
  · intro t ht
    have hi := mem_Ioc.mp (mem_filter.mp ht).1
    exact (hmem (t-p^2) (by omega)).mp (by simpa only [Nat.add_sub_of_le hi.1.le] using ht)
  · intro h _; omega
  · intro t ht
    have hi := mem_Ioc.mp (mem_filter.mp ht).1
    omega

theorem normalized_main_mul {d k : ℕ} (hc : d.Coprime k) (J : ℝ) :
    J/(d*k).totient = (J/(d.totient:ℝ))/(k.totient:ℝ) := by
  rw [Nat.totient_mul hc, Nat.cast_mul, div_mul_eq_div_div]

/-- All residue classes of each modulus are charged to its single largest
    reduced-class error. The scalar J can in particular be the short li integral. -/
noncomputable def shortAPWorst (X H q : ℕ) (J : ℝ) : NNReal :=
  (range q).sup fun a => if a.Coprime q then
    (⟨|((shortAPPrimes X H q a).card : ℝ) - J/q.totient|, abs_nonneg _⟩ : NNReal)
    else 0

theorem shortAP_error_le {X H q a : ℕ} (ha : a < q) (hc : a.Coprime q) (J : ℝ) :
    |((shortAPPrimes X H q a).card : ℝ) - J/q.totient| ≤ (shortAPWorst X H q J : ℝ) := by
  let e := fun a : ℕ => if a.Coprime q then
    (⟨|((shortAPPrimes X H q a).card : ℝ) - J/q.totient|, abs_nonneg _⟩ : NNReal) else 0
  have h : e a ≤ (range q).sup e := le_sup (f := e) (mem_range.mpr ha)
  have he : (e a : ℝ) = |((shortAPPrimes X H q a).card : ℝ) - J/q.totient| := by
    unfold e
    rw [ite_eq_left hc]
  rw [← he]
  exact NNReal.coe_le_coe.mpr h

/-- Any admissible collection of sieve divisors consumes each modulus dk once.
    The sum of progression errors over moduli up to D bounds the sieve remainder. -/
theorem sum_rho_errors_le {p H d b D : ℕ} (hp : p.Prime) (hd : 0 < d) (hb : b.Coprime d)
    (hH : H ≤ p^2) (S : Finset ℕ) (J : ℝ)
    (hS : ∀ k ∈ S, 0 < k ∧ k < p ∧ d.Coprime k ∧ Nat.Coprime 2 k ∧ d*k ≤ D) :
    (∑ k ∈ S, |((sievedAPOffsets p H d b k).card : ℝ) - J/d.totient/k.totient|) ≤
      ∑ q ∈ Icc 1 D, (shortAPWorst (p^2) H q J : ℝ) := by
  calc
    _ ≤ ∑ k ∈ S, (shortAPWorst (p^2) H (d*k) J : ℝ) := by
      refine sum_le_sum fun k hk => ?_
      obtain ⟨hkpos, hkp, hc, hk2, _⟩ := hS k hk
      rw [rho_count_eq_short_AP hH hd hkpos hc, ← normalized_main_mul hc J]
      exact shortAP_error_le (crtClass_data hd hkpos hc).1
        (crtClass_reduced hp hd hkpos hkp hc hk2 hb) J
    _ = ∑ q ∈ S.image (fun k => d*k), (shortAPWorst (p^2) H q J : ℝ) := by
      rw [sum_image]
      intro a _ b _ hh
      exact Nat.eq_of_mul_eq_mul_left hd hh
    _ ≤ _ := by
      refine sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => (shortAPWorst (p^2) H q J).coe_nonneg)
      intro q hq
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hq
      obtain ⟨hkpos, _, _, _, hdk⟩ := hS k hk
      exact mem_Icc.mpr ⟨Nat.mul_pos hd hkpos, hdk⟩

/-- Sieving omits primes dividing 2d; none divide any reflected candidate
    in the given admissible fixed class. -/
theorem reflected_coprime_twice_fixed {X h d b : ℕ} (hh : h ≤ X) (hb : b ≤ 2*X)
    (ht : Nat.ModEq d (X+h) b) (hadm : (2*X-b).Coprime d)
    (hp : (X+h).Prime) (hgt : 2 < X+h) : (X-h).Coprime (2*d) := by
  refine Nat.coprime_mul_iff_right.mpr ⟨?_, reflected_coprime_fixed hh hb ht hadm⟩
  apply Nat.coprime_two_right.mpr
  have hpodd := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  exact Nat.odd_iff.mpr (by omega)

/-- The upper inequality defining the floor window implies H ≤ p². -/
theorem floor_window_le_center {p H : ℕ} (hp : 0 < p) (h : H^3 ≤ p^4) : H ≤ p^2 := by
  have hpp : p^4 ≤ (p^2)^3 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp (by norm_num)
  exact le_of_not_gt fun hgt => (Nat.pow_lt_pow_left hgt (by decide : 3 ≠ 0)).not_ge (h.trans hpp)

end GoldbachCentralSeven
end

section
namespace GoldbachCentralSeven

open Filter Finset

noncomputable def fixedSieveLevel (X : ℕ) := ⌊(X:ℝ)^(5/32:ℝ)⌋₊
noncomputable def shortDistributionLevel (X : ℕ) (B : ℝ) :=
  ⌊(X:ℝ)^(1/6:ℝ)/(Real.log (X:ℝ))^B⌋₊

/-- The slack 1/6−5/32=1/96 absorbs both the fixed modulus and every
    fixed real power of the logarithm in the short-interval level. -/
theorem eventually_fixed_modulus_level (d : ℕ) (hd : 0 < d) (B : ℝ) :
    ∀ᶠ X : ℕ in atTop, ∀ k ≤ fixedSieveLevel X,
      d*k ≤ shortDistributionLevel X B := by
  have hdpos : 0 < (d:ℝ) := by exact_mod_cast hd
  have hf := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    ((isLittleO_log_rpow_rpow_atTop B (show 0 < (1/96 : ℝ) by norm_num)).bound
      (show 0 < 1/(d:ℝ) by positivity))
  filter_upwards [hf, eventually_ge_atTop 2] with X hX htwo
  intro k hk
  have hgt : 1 < (X:ℝ) := by exact_mod_cast (by omega : 1 < X)
  have hpos : 0 < (X:ℝ) := by linarith
  have hlog := Real.log_pos hgt
  have hlogB := Real.rpow_pos_of_pos hlog B
  change ‖Real.log (X:ℝ)^B‖ ≤ (1/(d:ℝ))*‖(X:ℝ)^(1/96:ℝ)‖ at hX
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlogB,
    abs_of_pos (Real.rpow_pos_of_pos hpos _)] at hX
  have hcost : (d:ℝ)*(Real.log (X:ℝ))^B ≤ (X:ℝ)^(1/96:ℝ) := by
    calc
      _ ≤ (d:ℝ)*((1/(d:ℝ))*(X:ℝ)^(1/96:ℝ)) := by gcongr
      _ = _ := by field_simp
  have hkR : (k:ℝ) ≤ (X:ℝ)^(5/32:ℝ) := (by exact_mod_cast hk : (k:ℝ) ≤ fixedSieveLevel X).trans
    (Nat.floor_le (by positivity))
  apply (Nat.le_floor_iff (div_nonneg (Real.rpow_nonneg hpos.le _) hlogB.le)).mpr
  rw [Nat.cast_mul]
  apply (le_div_iff₀ hlogB).mpr
  calc
    _ = (k:ℝ)*((d:ℝ)*Real.log (X:ℝ)^B) := by ring
    _ ≤ (X:ℝ)^(5/32:ℝ)*(X:ℝ)^(1/96:ℝ) :=
      mul_le_mul hkR hcost (mul_nonneg hdpos.le hlogB.le) (by positivity)
    _ = _ := by rw [← Real.rpow_add hpos]; norm_num

theorem fixed_level_at_prime_squares (d : ℕ) (hd : 0 < d) (B : ℝ) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ k ≤ fixedSieveLevel (p^2),
      k < p ∧ d*k ≤ shortDistributionLevel (p^2) B := by
  have hh := (tendsto_pow_atTop (α := ℕ) (by decide : 2 ≠ 0)).eventually
    (eventually_fixed_modulus_level d hd B)
  apply eventually_atTop.mp
  filter_upwards [hh, eventually_ge_atTop 2] with p hp htwo
  intro k hk
  refine ⟨?_, hp k hk⟩
  have hgt : 1 < ((p^2:ℕ):ℝ) := by
    exact_mod_cast (by nlinarith : 1 < p^2)
  have hlt : (((p^2:ℕ):ℝ))^(5/32:ℝ) < (((p^2:ℕ):ℝ))^(1/2:ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hgt (by norm_num)
  have hright : (((p^2:ℕ):ℝ))^(1/2:ℝ) = p := by
    rw [← Real.sqrt_eq_rpow, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg p)]
  rw [hright] at hlt
  have hk' : (k:ℝ) ≤ fixedSieveLevel (p^2) := by exact_mod_cast hk
  exact_mod_cast hk'.trans_lt ((Nat.floor_le (by positivity)).trans_lt hlt)

/-- Every residue b uses the very same thresholds and distribution budget. -/
theorem eventually_reflected_remainder_at_level (d : ℕ) (hd : 0 < d) (B : ℝ) :
    ∃ p₀ : ℕ, ∀ p ≥ p₀, p.Prime → ∀ (H b : ℕ) (S : Finset ℕ) (J : ℝ),
      H^3 ≤ p^4 → b.Coprime d →
      (∀ k ∈ S, 0 < k ∧ k ≤ fixedSieveLevel (p^2) ∧ d.Coprime k ∧ Nat.Coprime 2 k) →
      (∑ k ∈ S, |((sievedAPOffsets p H d b k).card : ℝ) - J/d.totient/k.totient|) ≤
        ∑ q ∈ Icc 1 (shortDistributionLevel (p^2) B), (shortAPWorst (p^2) H q J : ℝ) := by
  obtain ⟨p₀, h₀⟩ := fixed_level_at_prime_squares d hd B
  refine ⟨p₀, ?_⟩
  intro p hp hprime H b S J hH hb hS
  apply sum_rho_errors_le hprime hd hb (floor_window_le_center hprime.pos hH)
  intro k hk
  obtain ⟨hpos, hlevel, hc, hk2⟩ := hS k hk
  obtain ⟨hlt, hdk⟩ := h₀ p hp k hlevel
  exact ⟨hpos, hlt, hc, hk2, hdk⟩

end GoldbachCentralSeven
end

section
open Finset Filter
open scoped Classical

namespace TH8000Square

noncomputable def squareHits (p H z : ℕ) : Finset ℕ :=
  (Icc 1 H).filter (fun h => ∃ q : ℕ, q.Prime ∧ z ≤ q ∧ q^2 ∣ p^2-h)

noncomputable def repeatedRough (p H z : ℕ) : Finset ℕ :=
  (Icc 1 H).filter (fun h => z ≤ (p^2-h).minFac ∧ ¬ (p^2-h).primeFactorsList.Nodup)

/- The telescoping reciprocal-square estimate is adapted from goldbach-proofs,
RoughFifthSquareError.lean, blob de3ff3af11c97483115a76fb38310b69649e3b05,
under Apache License 2.0. The residue-class count below retains the window width. -/
private lemma reciprocal_tail (z k : ℕ) (hz : 1 ≤ z) :
    (∑ i ∈ range k, (1:ℝ) / ((z+i+1:ℕ):ℝ)^2) ≤ 1/(z:ℝ) - 1/((z+k:ℕ):ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have hstep : (1:ℝ)/((z+k+1:ℕ):ℝ)^2 ≤ 1/((z+k:ℕ):ℝ) - 1/((z+k+1:ℕ):ℝ) := by
      let x : ℝ := z+k
      have hx : 0 < x := by dsimp [x]; exact_mod_cast (show 0 < z+k by omega)
      push_cast
      change 1/(x+1)^2 ≤ 1/x - 1/(x+1)
      field_simp
      nlinarith
    change _ ≤ 1/(z:ℝ) - 1/((z+k+1:ℕ):ℝ)
    linarith

private lemma fiber_count (N H D : ℕ) (hH : H ≤ N) :
    ((Icc 1 H).filter (fun h => D ∣ N-h)).card ≤ H/D+1 := by
  have hmem (h) (hh : h ∈ (Icc 1 H).filter (fun h => D ∣ N-h)) :
      h % D = N % D := by
    obtain ⟨hi,hd⟩ := mem_filter.mp hh
    exact (Nat.modEq_iff_dvd' ((mem_Icc.mp hi).2.trans hH)).mpr hd
  rw [← card_range (H/D+1)]
  apply card_le_card_of_injOn (fun h => h/D)
  · intro h hh
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right ((mem_Icc.mp (mem_filter.mp hh).1).2)))
  · intro h hh k hk he
    change h/D=k/D at he
    have hr := (hmem h hh).trans (hmem k hk).symm
    calc h = h % D + D*(h/D) := (Nat.mod_add_div ..).symm
      _ = k % D + D*(k/D) := by rw [hr,he]
      _ = k := Nat.mod_add_div .. 

/-- The possible zero reflected endpoint costs at most one, even when z>p. -/
theorem square_count_le (p H z : ℕ) (hp : 1 ≤ p) (hH : H ≤ p^2) (hz : 2 ≤ z) :
    ((squareHits p H z).card:ℝ) ≤ (H:ℝ)/((z:ℝ)-1) + p := by
  let q := fun i : ℕ => z-1+i+1
  let S := fun i : ℕ => (Icc 1 H).filter (fun h => (q i)^2 ∣ p^2-h)
  have cover : squareHits p H z ⊆ insert (p^2) ((range (p-1)).biUnion S) := by
    intro h hh
    obtain ⟨hh, r, _hr, hzr, hd⟩ := mem_filter.mp hh
    rcases eq_or_ne h (p^2) with he | he
    · exact mem_insert.mpr (Or.inl he)
    have hlt : h < p^2 := lt_of_le_of_ne ((mem_Icc.mp hh).2.trans hH) he
    have hsquare := Nat.le_of_dvd (Nat.sub_pos_of_lt hlt) hd
    have h1 := (mem_Icc.mp hh).1
    have hrp : r < p := by
      by_contra! hge
      have := Nat.pow_le_pow_left hge 2
      omega
    apply mem_insert.mpr
    right
    apply mem_biUnion.mpr
    refine ⟨r-z, mem_range.mpr (by omega), mem_filter.mpr ⟨hh, ?_⟩⟩
    simpa only [show q (r-z) = r by dsimp [q]; omega] using hd
  have hc : (squareHits p H z).card ≤ (∑ i ∈ range (p-1), (H/(q i)^2+1)) + 1 := by
    calc
      _ ≤ _ := (card_le_card cover).trans (card_insert_le ..)
      _ ≤ (∑ i ∈ range (p-1), (S i).card) + 1 := Nat.add_le_add_right card_biUnion_le _
      _ ≤ _ := Nat.add_le_add_right (sum_le_sum fun i _ => fiber_count (p^2) H ((q i)^2) hH) _
  have hcast : ((squareHits p H z).card:ℝ) ≤
      (∑ i ∈ range (p-1), (((H/(q i)^2:ℕ):ℝ)+1)) + 1 := by exact_mod_cast hc
  have hterm (i : ℕ) : ((H/(q i)^2:ℕ):ℝ) ≤ H*(1/((q i:ℕ):ℝ)^2) := by
    rw [mul_one_div, ← Nat.cast_pow]
    exact Nat.cast_div_le
  have hs : (∑ i ∈ range (p-1), 1/((q i):ℝ)^2) ≤ 1/((z:ℝ)-1) := by
    have h := reciprocal_tail (z-1) (p-1) (by omega)
    have hn : (0:ℝ) ≤ 1/((((z-1)+(p-1):ℕ):ℝ)) := by positivity
    have h' := h.trans (sub_le_self _ hn)
    simpa only [q, Nat.cast_sub (by omega : 1 ≤ z), Nat.cast_one] using h'
  have hsum := (sum_le_sum (s := range (p-1)) (fun i _ => hterm i))
  rw [← mul_sum] at hsum
  have hresult := hsum.trans (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  rw [sum_add_distrib] at hcast
  simp only [sum_const, nsmul_eq_mul, mul_one, card_range,
    Nat.cast_sub hp, Nat.cast_one] at hcast
  linarith only [hcast, hresult, mul_one_div (H:ℝ) ((z:ℝ)-1)]

theorem repeatedRough_subset (p H z : ℕ) : repeatedRough p H z ⊆ squareHits p H z := by
  intro h hh
  obtain ⟨hI,hz,hn⟩ := mem_filter.mp hh
  have hm : p^2-h ≠ 0 := by
    intro hm
    simp [hm] at hn
  have hsf : ¬Squarefree (p^2-h) := fun hs => hn ((Nat.squarefree_iff_nodup_primeFactorsList hm).mp hs)
  rw [Nat.squarefree_iff_prime_squarefree] at hsf
  push Not at hsf
  obtain ⟨q,hq,hd⟩ := hsf
  have hdiv : q ∣ p^2-h := dvd_trans (dvd_mul_right q q) hd
  exact mem_filter.mpr ⟨hI,q,hq,hz.trans (Nat.minFac_le_of_dvd hq.two_le hdiv),by simpa [sq] using hd⟩

private lemma eventually_logSquare_le {a e : ℝ} (ha : 0 < a) (he : 0 < e) :
    ∀ᶠ p : ℕ in atTop, (Real.log ((p:ℝ)^2))^2 ≤ e*(p:ℝ)^a := by
  have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) ha).bound (show 0 < e/4 by positivity)
  have hnat := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually h
  filter_upwards [hnat] with p hp
  have hp' : (Real.log (p:ℝ))^2 ≤ e/4*(p:ℝ)^a := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (p:ℝ))),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) a)] using hp
  rw [Real.log_pow, Nat.cast_ofNat]
  nlinarith only [hp']

private lemma width_bounds (p H : ℕ) (hp : 2 ≤ p)
    (hlo : H^3 ≤ p^4) (hhi : p^4 < (H+1)^3) :
    H ≤ p^2 ∧ (p:ℝ)*(p:ℝ)^(1/3:ℝ) ≤ 2*(H:ℝ) := by
  have hp1 : 1 ≤ p := by omega
  have hp4 : p^4 ≤ (p^2)^3 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp1 (by norm_num)
  have hHp : H ≤ p^2 := by
    by_contra! h
    have := Nat.pow_lt_pow_left h (by norm_num : 3 ≠ 0)
    omega
  have hH0 : 1 ≤ H := by
    by_contra! h
    have : H = 0 := by omega
    subst H
    simp at hhi
    omega
  have hHR : (1:ℝ) ≤ H := by exact_mod_cast hH0
  have h4 : (p:ℝ)^4 ≤ ((H:ℝ)+1)^3 := by exact_mod_cast hhi.le
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg p
  refine ⟨hHp, ?_⟩
  calc
    (p:ℝ)*(p:ℝ)^(1/3:ℝ) = (p:ℝ)^(1+(1/3):ℝ) := by rw [Real.rpow_add (by positivity)]; simp
    _ = ((p:ℝ)^4)^(1/3:ℝ) := by
      rw [← Real.rpow_natCast (p:ℝ) 4, ← Real.rpow_mul hp0]
      norm_num
    _ ≤ (((H:ℝ)+1)^3)^(1/3:ℝ) := Real.rpow_le_rpow (by positivity) h4 (by norm_num)
    _ = (H:ℝ)+1 := by
      rw [← Real.rpow_natCast ((H:ℝ)+1) 3, ← Real.rpow_mul (by positivity)]
      norm_num
    _ ≤ _ := by linarith

/-- The threshold is uniform over every window and cutoff with the indicated
power constraints. The normalization agrees with the frozen hit-count scale. -/
theorem square_error_negligible {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → ∀ H z : ℕ,
      H^3 ≤ p^4 → p^4 < (H+1)^3 → (p:ℝ)^η ≤ z →
      ((squareHits p H z).card:ℝ) * (Real.log ((p:ℝ)^2))^2 ≤ ε*(H:ℝ) := by
  have hηlog := eventually_logSquare_le hη (show 0 < ε/4 by positivity)
  have hthird := eventually_logSquare_le (show (0:ℝ) < 1/3 by norm_num) (show 0 < ε/4 by positivity)
  have hpow : Tendsto (fun p : ℕ => (p:ℝ)^η) atTop atTop :=
    (tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop
  apply eventually_atTop.mp
  filter_upwards [hηlog, hthird, hpow.eventually_ge_atTop 2,
    eventually_ge_atTop (2:ℕ)] with p hA hB hpow hp H z hlo hhi hz
  have hz2r : (2:ℝ) ≤ z := hpow.trans hz
  have hz2 : 2 ≤ z := by exact_mod_cast hz2r
  obtain ⟨hHp,hwidth⟩ := width_bounds p H hp hlo hhi
  have hcard := square_count_le p H z (by omega) hHp hz2
  let L := (Real.log ((p:ℝ)^2))^2
  have hper : L/((z:ℝ)-1) ≤ ε/2 := by
    apply (div_le_iff₀ (by linarith : 0 < (z:ℝ)-1)).mpr
    have hh := hA.trans (mul_le_mul_of_nonneg_left hz (show 0 ≤ ε/4 by positivity))
    have he := mul_nonneg hε.le (show 0 ≤ (z:ℝ)-2 by linarith)
    dsimp only [L]
    nlinarith only [hh, he]
  have hfirst : (H:ℝ)/((z:ℝ)-1)*L ≤ (H:ℝ)*(ε/2) := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hper (Nat.cast_nonneg _)
  have hsecond : (p:ℝ)*L ≤ (ε/4)*(2*(H:ℝ)) := by
    calc
      _ ≤ (p:ℝ)*(ε/4*(p:ℝ)^(1/3:ℝ)) := mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg _)
      _ = (ε/4)*((p:ℝ)*(p:ℝ)^(1/3:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwidth (by positivity)
  have hfinal := mul_le_mul_of_nonneg_right hcard (show 0 ≤ L from sq_nonneg _)
  change ((squareHits p H z).card:ℝ)*L ≤ _
  rw [add_mul] at hfinal
  linarith only [hfirst,hsecond,hfinal]

theorem repeatedRough_error_negligible {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ P : ℕ, ∀ p : ℕ, P ≤ p → ∀ H z : ℕ,
      H^3 ≤ p^4 → p^4 < (H+1)^3 → (p:ℝ)^η ≤ z →
      ((repeatedRough p H z).card:ℝ) * (Real.log ((p:ℝ)^2))^2 ≤ ε*(H:ℝ) := by
  obtain ⟨P,hP⟩ := square_error_negligible hη hε
  refine ⟨P, fun p hp H z hlo hhi hz => le_trans ?_ (hP p hp H z hlo hhi hz)⟩
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact_mod_cast card_le_card (repeatedRough_subset p H z)


end TH8000Square
end

section
namespace GoldbachSevenWeight

open Finset Real

/-- These exponents leave slack both in the seven-factor threshold and in
the middle range of the hybrid zero-density estimate. -/
lemma parameter_slack :
    (5/32 : ℝ) < 4/25 ∧ (5/32 : ℝ)/(25/162) = 81/80 ∧
    (5/32 : ℝ)/(5/128) = 4 ∧ (162/25 : ℝ)+3/2 < 8 := by norm_num

noncomputable def distinctPenalty (a : ℕ) (y : ℝ) : ℝ :=
  ∑ q ∈ a.primeFactors, max (1 - log q / log y) 0

lemma penalty_eq_of_squarefree {a : ℕ} (hs : Squarefree a) (y : ℝ) :
    GoldbachRichert.penalty a y = distinctPenalty a y := by
  unfold GoldbachRichert.penalty distinctPenalty Finsupp.sum
  change (∑ q ∈ a.primeFactors, _) = _
  apply sum_congr rfl
  intro q hq
  obtain ⟨hp, hd, _⟩ := Nat.mem_primeFactors.mp hq
  simp only [Nat.factorization_eq_one_of_squarefree hs hp hd, Nat.cast_one, one_mul]

noncomputable def upperCut (X : ℕ) : ℝ := (X:ℝ) ^ (25/162 : ℝ)

lemma partner_log_bound {X a : ℕ} (hX : 2 ≤ X) (ha : 0 < a) (hle : a ≤ X) :
    log (a:ℝ) / log (upperCut X) ≤ 162/25 := by
  have hx : (1:ℝ)<X := by exact_mod_cast (show 1<X by omega)
  have hpos := Real.log_pos hx
  have hle' : log (a:ℝ) ≤ log (X:ℝ) :=
    Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hle)
  rw [upperCut, Real.log_rpow (by linarith : 0 < (X:ℝ)), div_le_iff₀ (by positivity)]
  linarith

noncomputable def weight (X a : ℕ) : ℝ := 1 - distinctPenalty a (upperCut X)/(3/2)

lemma weight_le_one (X a : ℕ) : weight X a ≤ 1 := by
  have h : 0 ≤ distinctPenalty a (upperCut X) := sum_nonneg (fun _ _ => le_max_right _ _)
  unfold weight
  linarith

lemma weight_nonpos_of_many_factors {X a : ℕ} (hX : 2 ≤ X) (hs : Squarefree a)
    (haX : a ≤ X) (hmany : 7 < a.primeFactorsList.length) : weight X a ≤ 0 := by
  have ha : 0 < a := Nat.pos_of_ne_zero hs.ne_zero
  have hb := GoldbachRichert.factor_budget a (upperCut X)
  rw [penalty_eq_of_squarefree hs, ArithmeticFunction.cardFactors_apply] at hb
  have hlen : (8:ℝ) ≤ a.primeFactorsList.length := by exact_mod_cast hmany
  have hu := partner_log_bound hX ha haX
  unfold weight
  linarith

def hits (p H d b : ℕ) : Finset ℕ :=
  (Icc 1 H).filter (fun h => (p^2+h)%d=b ∧ (p^2+h).Prime ∧
    (p^2-h).primeFactorsList.Nodup ∧ (p^2-h).primeFactorsList.length ≤ 7)

/-- A lower bound on the total distinct-prime weight transfers to the exact
frozen counting function after subtracting the repeated-prime contribution. -/
theorem weight_transfer (p H d b : ℕ) (hp : 2 ≤ p) (A : Finset ℕ)
    (hA : ∀ h ∈ A, h ∈ Icc 1 H ∧ (p^2+h)%d=b ∧ (p^2+h).Prime) :
    (∑ h ∈ A, weight (p^2) (p^2-h)) -
      ((A.filter fun h => ¬Squarefree (p^2-h)).card : ℝ) ≤ (hits p H d b).card := by
  let G := A.filter (fun h => (p^2-h).primeFactorsList.Nodup ∧
    (p^2-h).primeFactorsList.length ≤ 7)
  have hsub : G ⊆ hits p H d b := by
    intro h hh
    obtain ⟨hA', hn, hcount⟩ := mem_filter.mp hh
    obtain ⟨hI,hres,hprime⟩ := hA h hA'
    exact mem_filter.mpr ⟨hI,hres,hprime,hn,hcount⟩
  have hpoint (h : ℕ) (_ : h ∈ A) : weight (p^2) (p^2-h) ≤
      (if (p^2-h).primeFactorsList.Nodup ∧ (p^2-h).primeFactorsList.length ≤ 7 then (1:ℝ) else 0)
        + (if ¬Squarefree (p^2-h) then 1 else 0) := by
    have h1 := weight_le_one (p^2) (p^2-h)
    by_cases hs : Squarefree (p^2-h)
    · simp only [hs, not_true_eq_false, ite_false, add_zero, hs.nodup_primeFactorsList, true_and]
      split_ifs with hle
      · exact h1
      · exact weight_nonpos_of_many_factors (by nlinarith) hs (Nat.sub_le ..) (by omega)
    · have hnn : 0 ≤ (if (p^2-h).primeFactorsList.Nodup ∧ (p^2-h).primeFactorsList.length ≤ 7
          then (1:ℝ) else 0) := by split <;> norm_num
      simp only [hs, not_false_eq_true, ite_true]
      linarith
  have hsum := Finset.sum_le_sum hpoint
  rw [sum_add_distrib] at hsum
  simp only [Finset.sum_boole] at hsum
  have hg : (G.card:ℝ) ≤ (hits p H d b).card := by exact_mod_cast Finset.card_le_card hsub
  dsimp [G] at hg
  linarith

end GoldbachSevenWeight
end

section
namespace GoldbachSevenWeight
open Finset

noncomputable def sieveCut (p : ℕ) := ⌈(p:ℝ) ^ (5/64:ℝ)⌉₊

noncomputable def roughOffsets (p H d b : ℕ) :=
  (Icc 1 H).filter fun h => (p^2+h)%d=b ∧ (p^2+h).Prime ∧ sieveCut p ≤ (p^2-h).minFac

lemma half_window (p H : ℕ) (hp : 4 ≤ p) (hH : H^3 ≤ p^4) : 2*H ≤ p^2 := by
  have h8 : 8 ≤ p^2 := by nlinarith
  have hlevel : (2*H)^3 ≤ (p^2)^3 := calc
    (2*H)^3 = 8*H^3 := by ring
    _ ≤ 8*p^4 := by omega
    _ ≤ p^2*p^4 := Nat.mul_le_mul_right _ h8
    _ = _ := by ring
  by_contra! hlt
  exact (not_lt_of_ge hlevel) (Nat.pow_lt_pow_left hlt (by decide))

lemma case_error (p H d b : ℕ) (hp : 4 ≤ p) (hH : H^3 ≤ p^4) :
    ((roughOffsets p H d b).filter fun h => ¬Squarefree (p^2-h)) ⊆
      TH8000Square.repeatedRough p H (sieveCut p) := by
  intro h hh
  obtain ⟨hc,hs⟩ := mem_filter.mp hh
  obtain ⟨hI,_,_,hrough⟩ := mem_filter.mp hc
  have hwindow := half_window p H hp hH
  have hH' := (mem_Icc.mp hI).2
  have hX : 4 ≤ p^2 := by nlinarith
  have hpos : p^2-h ≠ 0 := by omega
  exact mem_filter.mpr ⟨hI,hrough,fun hnodup =>
    hs ((Nat.squarefree_iff_nodup_primeFactorsList hpos).mpr hnodup)⟩

/-- A positive Richert-weighted main term on the actual offsets suffices
uniformly in all admissible residues of each fixed modulus. -/
theorem seven_of_weighted_lower
    (hweighted : ∀ d : ℕ, 0 < d → ∃ c : ℝ, 0 < c ∧ ∃ P : ℕ, ∀ p H b : ℕ,
      P ≤ p → p.Prime → b < d → b.Coprime d → (2*p^2-b).Coprime d →
      H^3 ≤ p^4 → p^4 < (H+1)^3 →
      c*(H:ℝ) ≤ (∑ h ∈ roughOffsets p H d b, weight (p^2) (p^2-h)) *
        (Real.log ((p:ℝ)^2))^2) :
    ∀ d : ℕ, 0 < d → ∃ c : ℝ, 0 < c ∧ ∃ p₀ : ℕ, ∀ p H b : ℕ,
      p₀ ≤ p → p.Prime → b < d → b.Coprime d → (2*p^2-b).Coprime d →
      H^3 ≤ p^4 → p^4 < (H+1)^3 →
      c*(H:ℝ) ≤ ((hits p H d b).card : ℝ) * (Real.log ((p:ℝ)^2))^2 := by
  intro d hd
  obtain ⟨c,hc,P,hpos⟩ := hweighted d hd
  obtain ⟨P',hbad⟩ := TH8000Square.repeatedRough_error_negligible
    (show (0:ℝ)<5/64 by norm_num) (half_pos hc)
  refine ⟨c/2,half_pos hc,max 4 (max P P'),?_⟩
  intro p H b hp hprime hb hadm hadm' hlo hhi
  have hp4 : 4 ≤ p := by omega
  have hm := hpos p H b (by omega) hprime hb hadm hadm' hlo hhi
  have he := hbad p (by omega) H (sieveCut p) hlo hhi (Nat.le_ceil _)
  have htrans := weight_transfer p H d b (by omega) (roughOffsets p H d b)
    (by
      intro h hh
      obtain ⟨hI,hres,ht,_⟩ := mem_filter.mp hh
      exact ⟨hI,hres,ht⟩)
  have hcard := Finset.card_le_card (case_error p H d b hp4 hlo)
  have hle : (((roughOffsets p H d b).filter fun h => ¬Squarefree (p^2-h)).card : ℝ) ≤
      ((TH8000Square.repeatedRough p H (sieveCut p)).card : ℝ) := by exact_mod_cast hcard
  have hs := mul_le_mul_of_nonneg_right hle (sq_nonneg (Real.log ((p:ℝ)^2)))
  have hh := mul_le_mul_of_nonneg_right htrans (sq_nonneg (Real.log ((p:ℝ)^2)))
  linarith only [hm,he,hs,hh]

end GoldbachSevenWeight
end

section
namespace GoldbachSevenWeight
open Finset Real

noncomputable def penaltyBand (X z : ℕ) : Finset ℕ :=
  (Icc z X).filter (fun q : ℕ => q.Prime ∧ (q:ℝ)<upperCut X)

theorem distinctPenalty_band {X a z : ℕ} (hX : 2 ≤ X) (ha : 1 < a)
    (haX : a ≤ X) (hz : z ≤ a.minFac) :
    distinctPenalty a (upperCut X) =
      ∑ q ∈ penaltyBand X z, if q ∣ a then 1 - log q / log (upperCut X) else 0 := by
  have hX' : (1:ℝ) < X := by exact_mod_cast (show 1<X by omega)
  have hy : 1 < upperCut X := Real.one_lt_rpow hX' (by norm_num)
  have hly := Real.log_pos hy
  have heq : a.primeFactors.filter (fun q : ℕ => (q:ℝ) < upperCut X) =
      (penaltyBand X z).filter (fun q => q ∣ a) := by
    ext q
    simp only [penaltyBand, mem_filter, mem_Icc, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp,hd,_⟩,hqy⟩
      exact ⟨⟨⟨hz.trans (Nat.minFac_le_of_dvd hp.two_le hd),
        (Nat.le_of_dvd (by omega) hd).trans haX⟩,hp,hqy⟩,hd⟩
    · rintro ⟨⟨_,hp,hq⟩,hd⟩
      exact ⟨⟨hp,hd,by omega⟩,hq⟩
  unfold distinctPenalty
  rw [← Finset.sum_filter, ← heq, Finset.sum_filter]
  apply sum_congr rfl
  intro q hq
  have hqpos : (0:ℝ)<q := by exact_mod_cast (Nat.prime_of_mem_primeFactors hq).pos
  split_ifs with h
  · apply max_eq_left
    exact sub_nonneg.mpr ((div_le_one hly).mpr (Real.log_le_log hqpos h.le))
  · apply max_eq_right
    exact sub_nonpos.mpr ((one_le_div hly).mpr (Real.log_le_log (by linarith) (le_of_not_gt h)))

def rowCount (S : Finset ℕ) (X q : ℕ) : ℕ := (S.filter fun h => q ∣ X-h).card

theorem rough_weight_eq_rows (p H d b : ℕ) (hp : 4 ≤ p) (hH : H^3 ≤ p^4) :
    let S := roughOffsets p H d b
    ∑ h ∈ S, weight (p^2) (p^2-h) =
      (S.card:ℝ) - (∑ q ∈ penaltyBand (p^2) (sieveCut p),
        (1 - log q / log (upperCut (p^2))) * (rowCount S (p^2) q:ℝ))/(3/2) := by
  classical
  intro S
  have hp2 : 4 ≤ p^2 := by nlinarith
  have hhalf := half_window p H hp hH
  unfold weight
  rw [sum_sub_distrib, ← sum_div, sum_const, nsmul_eq_mul, mul_one]
  congr 2
  calc
    _ = ∑ h ∈ S, ∑ q ∈ penaltyBand (p^2) (sieveCut p),
        if q ∣ p^2-h then 1 - log q / log (upperCut (p^2)) else 0 := by
      apply sum_congr rfl
      intro h hh
      obtain ⟨hI,_,_,hz⟩ := mem_filter.mp hh
      have := (mem_Icc.mp hI).2
      exact distinctPenalty_band (by omega) (by omega) (Nat.sub_le ..) hz
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro q _
      rw [← sum_filter, sum_const, nsmul_eq_mul, rowCount, mul_comm]

end GoldbachSevenWeight
end

section
open MeasureTheory Set
open scoped Interval

namespace GoldbachSevenParameters

/- Scalar evaluation for the Richert weight with distribution exponent 5/32.
The split is the same as in TH8000Margin. This file checks the constants only.
The underlying weight comes from CentralPrimeAlmostPrime.md by LonelyQuantum
in goldbach-proofs at 36b0d52d9585d07feeb93da6ac3b8de09b36f018. -/

noncomputable def looseLoss : ℝ :=
  (∫ t : ℝ in (1/4)..(1/2), 2*(1-(81/80)*t)/t) +
    ∫ t : ℝ in (1/2)..(80/81), (1-(81/80)*t)/(t*(1-t))

set_option maxHeartbeats 600000 in
theorem looseLoss_eval :
    looseLoss = Real.log (640/81) - 81/160 + Real.log (2/81)/80 := by
  let u : ℝ := 81/80
  have ha : ∫ t : ℝ in (1/4)..(1/2), 2*(1-u*t)/t =
      (fun t : ℝ => 2*Real.log t - (2*u)*t) (1/2) -
      (fun t : ℝ => 2*Real.log t - (2*u)*t) (1/4) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => 2*Real.log t-(2*u)*t) (f' := fun t : ℝ => 2*(1-u*t)/t)
    · intro t ht
      rw [uIcc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2)] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have hd : HasDerivAt (fun x : ℝ => 2*Real.log x-(2*u)*x) (2*t⁻¹-(2*u)*1) t :=
        ((Real.hasDerivAt_log ht0).const_mul 2).sub ((hasDerivAt_id t).const_mul (2*u))
      convert hd using 1
      field_simp [ht0]
    · have hnum : Continuous (fun t : ℝ => 2*(1-u*t)) := by fun_prop
      apply (hnum.continuousOn.div continuousOn_id ?_).intervalIntegrable
      intro t ht
      rw [uIcc_of_le (by norm_num : (1:ℝ)/4 ≤ 1/2)] at ht
      change t ≠ 0
      exact ne_of_gt (by linarith [ht.1])
  have hb : ∫ t : ℝ in (1/2)..(80/81), (1-u*t)/(t*(1-t)) =
      (fun t : ℝ => Real.log t + (u-1)*Real.log (1-t)) (80/81) -
      (fun t : ℝ => Real.log t + (u-1)*Real.log (1-t)) (1/2) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => Real.log t+(u-1)*Real.log (1-t))
      (f' := fun t : ℝ => (1-u*t)/(t*(1-t)))
    · intro t ht
      rw [uIcc_of_le (by norm_num : (1:ℝ)/2 ≤ 80/81)] at ht
      have ht0 : t ≠ 0 := by linarith [ht.1]
      have ht1 : 1-t ≠ 0 := by linarith [ht.2]
      have hd : HasDerivAt (fun x : ℝ => 1-x) (-1) t := (hasDerivAt_id t).const_sub 1
      have hder : HasDerivAt (fun x : ℝ => Real.log x+(u-1)*Real.log (1-x))
          (t⁻¹ + (u-1)*((-1)/(1-t))) t :=
        (Real.hasDerivAt_log ht0).add ((hd.log ht1).const_mul (u-1))
      convert hder using 1
      field_simp [ht0, ht1]
      ring
    · have hnum : Continuous (fun t : ℝ => 1-u*t) := by fun_prop
      have hden : Continuous (fun t : ℝ => t*(1-t)) := by fun_prop
      apply (hnum.continuousOn.div hden.continuousOn ?_).intervalIntegrable
      intro t ht
      rw [uIcc_of_le (by norm_num : (1:ℝ)/2 ≤ 80/81)] at ht
      exact mul_ne_zero (by linarith [ht.1]) (by linarith [ht.2])
  have hdiv (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : a/b=c) :
      Real.log a - Real.log b = Real.log c := by rw [← Real.log_div ha hb,hc]
  have h1 := hdiv (1/2) (1/4) 2 (by norm_num) (by norm_num) (by norm_num)
  have h2 := hdiv (80/81) (1/2) (160/81) (by norm_num) (by norm_num) (by norm_num)
  have h3 := hdiv (1/81) (1/2) (2/81) (by norm_num) (by norm_num) (by norm_num)
  have h4 : 2*Real.log 2 + Real.log (160/81) = Real.log (640/81) := by
    rw [show 2*Real.log 2 = Real.log ((2:ℝ)^2) by rw [Real.log_pow]; norm_num]
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  change (∫ t : ℝ in (1/4)..(1/2), 2*(1-u*t)/t) +
    (∫ t : ℝ in (1/2)..(80/81), (1-u*t)/(t*(1-t))) = _
  rw [ha,hb]
  dsimp only [u]
  norm_num1
  linarith only [h1,h2,h3,h4]

/-- Positive slack for the weighted lower bound and the eight-factor loss. -/
theorem margin :
    looseLoss + 1/160 < (3/2)*Real.log 3 ∧
    (3/2:ℝ) + (81/80)/(5/32) + 1/50 = 8 := by
  constructor
  · have hneg : Real.log ((2:ℝ)/81) ≤ 0 := Real.log_nonpos (by norm_num) (by norm_num)
    have hl := Real.log_lt_log (by norm_num : (0:ℝ) < 640/81)
      (by norm_num : ((640:ℝ)/81) < 2^3)
    rw [Real.log_pow] at hl
    have hsplit : Real.log ((4:ℝ)/3) = 2*Real.log 2 - Real.log 3 := by
      rw [Real.log_div (by norm_num) (by norm_num),
        show Real.log (4:ℝ) = 2*Real.log 2 by
          convert Real.log_pow (2:ℝ) 2 using 1
          norm_num]
    have hupper := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 4/3)
    rw [hsplit] at hupper
    rw [looseLoss_eval]
    norm_num1 at hl
    linarith only [hl,hneg,hupper]
  · norm_num

theorem cutoffs (x : ℝ) (hx : 0 ≤ x) :
    (x^(5/32:ℝ))^(1/4:ℝ) = x^(5/128:ℝ) ∧
    (x^(5/32:ℝ))^(1/(81/80:ℝ)) = x^(25/162:ℝ) ∧
    (81/80:ℝ)/(5/32) = 162/25 ∧ (5/32:ℝ) < 4/25 := by
  rw [← Real.rpow_mul hx, ← Real.rpow_mul hx]
  norm_num

end GoldbachSevenParameters
end

section
namespace GoldbachCentralSeven.Density

/-- The normalized exponent from the ordinary mixed density bound; r is the
    conductor exponent and t is the height exponent. -/
noncomputable def exponent (r t σ : ℝ) : ℝ :=
  -r + (3*(2*r+t)/(2-σ)-1)*(1-σ)

theorem exponent_identity (r t u : ℝ) (hu : 0 ≤ u) :
    exponent r t (1-u) * (1+u) = r*(5*u-1) + (3*t-1)*u - u^2 := by
  unfold exponent
  rw [show 2-(1-u)=1+u by ring]
  field_simp
  ring

/-- A fixed positive height slack still allows a strict saving on this middle
    range of zeros, uniformly in the entire indicated conductor range. -/
theorem medium_strip_margin {r t σ : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 5/32) (ht : t ≤ 1/3+1/1024)
    (hσlo : 1/2 ≤ σ) (hσhi : σ ≤ 7/8) :
    exponent r t σ ≤ -(1/1024) := by
  let u := 1-σ
  have hu : (1:ℝ)/8 ≤ u := by dsimp [u]; linarith
  have hu' : u ≤ (1:ℝ)/2 := by dsimp [u]; linarith
  have h0 : 0 ≤ u := by linarith
  have hid := exponent_identity r t u h0
  rw [show 1-u = σ by dsimp [u]; ring] at hid
  apply le_of_mul_le_mul_right (a := 1+u) _ (by linarith)
  rw [hid]
  have ht' : 3*t-1 ≤ 3/1024 := by linarith
  have htprod := mul_le_mul_of_nonneg_right ht' h0
  by_cases hsign : 5*u-1 ≤ 0
  · have hrprod := mul_nonpos_of_nonneg_of_nonpos hr0 hsign
    nlinarith only [hrprod, htprod, hu, hu', mul_nonneg h0 (sub_nonneg.mpr hu)]
  · have hrprod := mul_le_mul_of_nonneg_right hr (le_of_not_ge hsign)
    nlinarith only [hrprod, htprod, hu', sq_nonneg (u-25/64)]

/-- Even at height exponent exactly 1/3 the worst medium ordinate precludes
    a saving beyond the conductor threshold 4/25 for this density inequality. -/
theorem middle_witness (r : ℝ) (hr : 0 ≤ r) :
    exponent r (1/3) (1-5*r/2) * (1+5*r/2) = r*(25*r/4-1) := by
  rw [exponent_identity _ _ _ (by positivity)]
  ring

/-- The conductor cutoff used by the seven-factor sieve is already beyond
    the preceding obstruction at an ordinate strictly inside the medium strip. -/
theorem level_witness (t : ℝ) (ht : 1/3 ≤ t) :
    (1/2:ℝ) < 93/158 ∧ (93/158:ℝ) < 7/8 ∧
    (117/35234:ℝ) ≤ exponent (13/79) t (93/158) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  unfold exponent
  norm_num
  linarith

/-- Fixed positive height slack actually incurs a positive exponent at
    r=0 and σ=1−δ. This records the scope of the middle-strip estimate. -/
theorem near_one_obstruction {δ : ℝ} (hδ : 0 < δ) :
    0 < exponent 0 (1/3+δ) (1-δ) := by
  have h := exponent_identity 0 (1/3+δ) δ hδ.le
  apply pos_of_mul_pos_left (b := 1+δ) _ (by linarith)
  rw [h]
  nlinarith only [sq_pos_of_pos hδ]

/-- Away from tiny conductors, the −r term pays the near-one loss. Thus that
    loss is localized to r < 12δ² for a height exponent at most 1/3+δ. -/
theorem near_one_conductor_margin {δ t r σ : ℝ} (ht : t ≤ 1/3+δ)
    (hr : 12*δ^2 ≤ r) (hσlo : 7/8 ≤ σ) (hσhi : σ ≤ 1) :
    exponent r t σ ≤ -r/6 := by
  let u := 1-σ
  have h0 : 0 ≤ u := by dsimp [u]; linarith
  have hu : u ≤ (1:ℝ)/8 := by dsimp [u]; linarith
  have hr0 : 0 ≤ r := by nlinarith only [hr, sq_nonneg δ]
  have hid := exponent_identity r t u h0
  rw [show 1-u=σ by dsimp [u]; ring] at hid
  apply le_of_mul_le_mul_right (a := 1+u) _ (by linarith)
  rw [hid]
  have hru := mul_le_mul_of_nonneg_left hu hr0
  have huT := mul_le_mul_of_nonneg_right (by linarith : 3*t-1 ≤ 3*δ) h0
  nlinarith only [hr, hru, huT, sq_nonneg (u-3*δ/2)]

/-- At the limiting height t=1/3 and bounded conductor the ordinary density
    exponent has only a quadratic saving in the distance from 1. -/
theorem near_one_boundary {u : ℝ} (hu : 0 ≤ u) :
    exponent 0 (1/3) (1-u) = -u^2/(1+u) := by
  apply (eq_div_iff (by linarith : 1+u ≠ 0)).mpr
  rw [exponent_identity _ _ _ hu]
  ring

/-- For u=L^(-2/3) the upper scale u²L of the logarithmic exponent in the
    preceding bound tends to zero. A further log-log denominator only shrinks it. -/
theorem quadratic_loss_at_two_thirds_scale :
    Filter.Tendsto (fun L : ℝ => (L ^ (-(2/3:ℝ)))^2 * L) Filter.atTop (nhds 0) := by
  have hlim := tendsto_rpow_neg_atTop (show 0 < (1/3:ℝ) by norm_num)
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with L hL
  rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
  conv_rhs => rhs; rw [← Real.rpow_one L]
  rw [← Real.rpow_add hL]
  norm_num

end GoldbachCentralSeven.Density
end
