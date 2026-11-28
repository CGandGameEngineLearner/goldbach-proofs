import Mathlib
import Conjectures.Goldbach.ReflectedMajorSharpFloor

namespace ReflectedShortProgression

open Finset Filter MeasureTheory Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Classical Interval Topology

noncomputable section

def coefficientPrefix (k m : ℕ) : ℝ :=
  ∑ q ∈ Icc 1 k, (GoldbachMajorArc.coefficient q m).re

def normalized (N m : ℕ) : ℝ :=
  let k := Nat.log 2 (N+2)
  (GoldbachBa08Approx.coefficient N m k (k^3)).re / (2*(N:ℝ)-(m:ℝ))

/-- The library coefficient uses the same prime weights, phase, and arc mask
as the posted integral. -/
theorem coefficient_eq_frozen (N m : ℕ) :
    let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
    let S := fun t : ℝ =>
      ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
    let k := Nat.log 2 (N+2)
    let arcs := {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
    (GoldbachBa08Approx.coefficient N m k (k^3)).re =
      (intervalIntegral (arcs.indicator (fun t : ℝ => (S t)^2 * e (-(m : ℝ)*t)))
        (0 : ℝ) 1 MeasureTheory.volume).re := by
  simp only [GoldbachBa08Approx.coefficient, GoldbachBa08Approx.arcs,
    GoldbachBlockGeometry.width, GoldbachBa08Approx.primeSum_eq, GoldbachMajorArc.phase]

private theorem eventually_cutoff_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, 4*(Nat.log 2 (N+2):ℝ) ≤ ε*(N:ℝ) := by
  have ht : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto ht).bound
    (show 0 < ε/16 by positivity)
  filter_upwards [h, eventually_ge_atTop (2:ℕ)] with N hN h2
  have h2' : (2:ℝ) ≤ N := by exact_mod_cast h2
  have h1' : (1:ℝ) ≤ N := by linarith only [h2']
  change ‖Real.log (N:ℝ)‖ ≤ (ε/16)*‖(N:ℝ)‖ at hN
  rw [Real.norm_of_nonneg (Real.log_nonneg h1'),
    Real.norm_of_nonneg (Nat.cast_nonneg N)] at hN
  have hlog : (Nat.log 2 (N+2):ℝ) ≤ 4*Real.log (N:ℝ) := by
    simpa only [GoldbachMajorArc.Polylog.cutoff, pow_one] using
      GoldbachMajorArc.Polylog.cutoff_le_log 1 h2
  linarith only [hlog, hN]

/-- Normalize the uniform core approximation by the reflected interval
length. The extra endpoint term is bounded by the sum of coefficient norms. -/
theorem eventually_normalized_transfer {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ m : ℕ, 4*N ≤ 3*m → 2*m ≤ 3*N →
      |normalized N m - coefficientPrefix (Nat.log 2 (N+2)) m| ≤ ε := by
  have hδ : 0 < ε/4 := by positivity
  filter_upwards [SharpArcTransfer.transfer (ε/4) hδ, eventually_cutoff_small hδ,
    eventually_ge_atTop (2:ℕ)] with N hApprox hCut hN
  intro m hLow hHigh
  have hNm : N ≤ m := by omega
  have hmN : m ≤ 2*N := by omega
  let k := Nat.log 2 (N+2)
  let D : ℝ := 2*(N:ℝ)-(m:ℝ)
  let A := (GoldbachBa08Approx.coefficient N m k (k^3)).re
  let v : ℂ := ((2*N-m:ℕ):ℂ)+1
  let s := ∑ q ∈ Icc 1 k, GoldbachMajorArc.coefficient q m
  have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hHigh' : 2*(m:ℝ) ≤ 3*(N:ℝ) := by exact_mod_cast hHigh
  have hD : (N:ℝ)/2 ≤ D := by dsimp [D]; linarith only [hHigh']
  have hDpos : 0 < D := (half_pos hNpos).trans_le hD
  have hs : s.re = coefficientPrefix k m := by simp only [s, coefficientPrefix, Complex.re_sum]
  have he : ‖GoldbachBa08Approx.coefficient N m k (k^3)-v*s‖ ≤
      (ε/4)*(N:ℝ) := hApprox m hNm hmN
  have hv : v = ((D+1:ℝ):ℂ) := by
    dsimp [v, D]
    push_cast [hmN]
    ring
  have hAbs : |A-(D+1)*coefficientPrefix k m| ≤ (ε/4)*(N:ℝ) := by
    have hh := (Complex.abs_re_le_norm _).trans he
    rw [hv, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hs] at hh
    exact hh
  have hk : 1 ≤ k := by
    apply Nat.le_log_of_pow_le (by decide : 1 < 2)
    simpa only [pow_one] using (show (2:ℕ) ≤ N+2 by omega)
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hPrefix : |coefficientPrefix k m| ≤ (ε/4)*(N:ℝ) := by
    rw [← hs]
    calc
      _ ≤ ‖s‖ := Complex.abs_re_le_norm s
      _ ≤ ∑ q ∈ Icc 1 k, ‖GoldbachMajorArc.coefficient q m‖ := norm_sum_le _ _
      _ ≤ 4*Real.sqrt k := GoldbachMajorArc.sum_norm_coefficient_le_sqrt k m
      _ ≤ 4*(k:ℝ) := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_self_iff.mpr (Or.inr hk')) (by norm_num)
      _ ≤ _ := hCut
  have hBudget : |A-D*coefficientPrefix k m| ≤ ε*D := by
    rw [show A-D*coefficientPrefix k m = (A-(D+1)*coefficientPrefix k m)+coefficientPrefix k m by ring]
    have hAbsAdd := (abs_add_le (A-(D+1)*coefficientPrefix k m) (coefficientPrefix k m)).trans
      (add_le_add hAbs hPrefix)
    linarith only [hAbsAdd, mul_le_mul_of_nonneg_left hD hε.le]
  change |A/D-coefficientPrefix k m| ≤ ε
  rw [show A/D-coefficientPrefix k m = (A-D*coefficientPrefix k m)/D by field_simp [hDpos.ne'],
    abs_div, abs_of_pos hDpos]
  exact (div_le_iff₀ hDpos).mpr hBudget

end

end ReflectedShortProgression

namespace ReflectedShortProgression

open Finset

/-- Even integers in the interval having the prescribed residue modulo `d`. -/
def window (d a x H : ℕ) : Finset ℕ :=
  (Icc x (x + H)).filter (fun m => Even m ∧ m % d = a)

private theorem even_residue_representative {d a : ℕ} (hd : Odd d) (ha : a < d) :
    ∃ r < 2 * d, ∀ m : ℕ, Even m ∧ m % d = a ↔ m % (2 * d) = r := by
  have hd0 : 0 < d := by
    have := Nat.odd_iff.mp hd
    omega
  have hd2 := Nat.odd_iff.mp hd
  let r := if Even a then a else a + d
  have hr : r < 2 * d := by
    dsimp only [r]
    split <;> omega
  have hr_d : r % d = a := by
    dsimp only [r]
    split
    · exact Nat.mod_eq_of_lt ha
    · rw [Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  have hr_2 : r % 2 = 0 := by
    dsimp only [r]
    split
    · exact Nat.even_iff.mp ‹Even a›
    · rename_i h
      rw [Nat.even_iff] at h
      omega
  refine ⟨r, hr, fun m => ?_⟩
  have hm_d : m % (2 * d) % d = m % d :=
    Nat.mod_mod_of_dvd m (Nat.dvd_mul_left d 2)
  have hm_2 : m % (2 * d) % 2 = m % 2 :=
    Nat.mod_mod_of_dvd m (Nat.dvd_mul_right 2 d)
  rw [Nat.even_iff, ← hm_d, ← hm_2]
  let u := m % (2 * d)
  change u % 2 = 0 ∧ u % d = a ↔ u = r
  constructor
  · rintro ⟨hu2, hud⟩
    have hu : u < 2 * d := Nat.mod_lt _ (by omega)
    have hquot : u / d < 2 := (Nat.div_lt_iff_lt_mul hd0).2 hu
    have hsum := Nat.mod_add_div u d
    rw [hud] at hsum
    rcases Nat.eq_zero_or_pos (u / d) with h | hpos
    · rw [h, Nat.mul_zero, Nat.add_zero] at hsum
      have hev : Even a := Nat.even_iff.mpr (by omega)
      simpa [r, hev] using hsum.symm
    · have h : u / d = 1 := by omega
      rw [h, Nat.mul_one] at hsum
      have hodd : ¬Even a := by
        rw [Nat.even_iff]
        omega
      simpa [r, hodd] using hsum.symm
  · intro heq
    rw [heq]
    exact ⟨hr_2, hr_d⟩

/-- The shorter frozen window inherits its reflected-band constraints from the endpoints. -/
theorem frozen_filter_eq_window {d a N x H : ℕ}
    (hlo : 4 * N ≤ 3 * x) (hhi : 2 * (x + H) ≤ 3 * N) :
    ((((Icc N (2 * N)).filter (fun m =>
      4 * N ≤ 3 * m ∧ 2 * m ≤ 3 * N ∧ Even m)) ∩ Icc x (x + H)).filter
      (fun m => m % d = a)) = window d a x H := by
  ext m
  simp only [window, mem_filter, mem_inter, mem_Icc]
  constructor
  · rintro ⟨⟨⟨_, _, _, he⟩, hxm, hmx⟩, hmod⟩
    exact ⟨⟨hxm, hmx⟩, he, hmod⟩
  · rintro ⟨⟨hxm, hmx⟩, he, hmod⟩
    exact ⟨⟨⟨⟨by omega, by omega⟩, by omega, by omega, he⟩, hxm, hmx⟩, hmod⟩

/-- A nonempty even residue window is an injectively enumerated progression. -/
theorem window_progression {d a x H : ℕ} (hd : Odd d) (ha : a < d)
    (hH : 2 * d ≤ H) :
    ∃ b K : ℕ, x ≤ b ∧ b < x + 2 * d ∧ 0 < K ∧
      window d a x H = (range K).image (fun j => b + (2 * d) * j) ∧
      Function.Injective (fun j : ℕ => b + (2 * d) * j) ∧
      (window d a x H).card = K ∧ H / (2 * d) ≤ K ∧
      (H : ℝ) / (4 * (d : ℝ)) ≤ (K : ℝ) := by
  obtain ⟨r, hr, hresidue⟩ := even_residue_representative hd ha
  have hd0 : 0 < d := by
    have := Nat.odd_iff.mp hd
    omega
  let P := 2 * d
  have hp : 0 < P := by dsimp [P]; omega
  let s := x / P + if x % P ≤ r then 0 else 1
  let b := r + P * s
  have hb : x ≤ b ∧ b < x + P := by
    have hx := Nat.mod_add_div x P
    have hxrem := Nat.mod_lt x hp
    dsimp only [b, s]
    split <;> rw [Nat.mul_add] <;> simp only [Nat.mul_zero, Nat.mul_one, Nat.add_zero] <;> omega
  have hbH : b ≤ x + H := by omega
  let K := (x + H - b) / P + 1
  have hk : 0 < K := Nat.succ_pos _
  have htop : x + H < b + P * K := by
    have hrem := Nat.mod_lt (x + H - b) hp
    have hdiv := Nat.mod_add_div (x + H - b) P
    dsimp only [K]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hbmod : b % P = r := by
    dsimp only [b]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  have hwin : window d a x H = (range K).image (fun j => b + P * j) := by
    ext m
    simp only [window, mem_filter, mem_Icc, hresidue m, mem_image, mem_range]
    constructor
    · rintro ⟨⟨hxm, hmx⟩, hm⟩
      have hrepr := Nat.mod_add_div m P
      rw [hm] at hrepr
      have hmin : s ≤ m / P := by
        by_contra! hs
        have hle := Nat.mul_le_mul_left P (show m / P + 1 ≤ s by omega)
        rw [Nat.mul_add, Nat.mul_one] at hle
        dsimp only [b] at hb
        omega
      have heq : b + P * (m / P - s) = m := by
        dsimp only [b]
        rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_of_le hmin]
        exact hrepr
      refine ⟨m / P - s, ?_, heq⟩
      by_contra! hlarge
      have hle := Nat.mul_le_mul_left P hlarge
      omega
    · rintro ⟨j, hj, rfl⟩
      have hle : P * j ≤ x + H - b := by
        have h_j : j ≤ (x + H - b) / P := by
          dsimp only [K] at hj
          omega
        simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp h_j
      exact ⟨⟨by omega, by omega⟩, by rw [Nat.add_mul_mod_self_left, hbmod]⟩
  have hinj : Function.Injective (fun j : ℕ => b + P * j) := by
    intro i j h
    exact Nat.eq_of_mul_eq_mul_left hp (Nat.add_left_cancel h)
  have hKmul : H < P * K + P := by omega
  have hKdiv : H / P ≤ K := by
    have hmul : (K + 1) * P = P * K + P := by ring
    rw [← hmul] at hKmul
    have hq := (Nat.div_lt_iff_lt_mul hp).mpr hKmul
    omega
  have hP_le : P ≤ P * K := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left P (show 1 ≤ K by omega)
  have hnat : H ≤ (4 * d) * K := calc
    H ≤ P * K + P := hKmul.le
    _ ≤ 2 * (P * K) := by omega
    _ = (4 * d) * K := by dsimp only [P]; ring
  have hreal : (H : ℝ) / (4 * (d : ℝ)) ≤ (K : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    exact_mod_cast (Nat.mul_comm (4 * d) K ▸ hnat)
  refine ⟨b, K, hb.1, hb.2, hk, hwin, hinj, ?_, hKdiv, hreal⟩
  rw [hwin, card_image_of_injective _ hinj, card_range]

end ReflectedShortProgression

namespace ReflectedShortProgression

open Finset
open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux GoldbachMajorArc

noncomputable section

private def coefficientFunction (m : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => coefficient n m, by simp [coefficient, ram]⟩

private theorem coefficientFunction_multiplicative (m : ℕ) :
    (coefficientFunction m).IsMultiplicative :=
  ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
    ⟨coefficient_one m, fun hn hk hc =>
      coefficient_mul (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hk) hc m⟩

private def coefficientDivisorSum (m : ℕ) : ArithmeticFunction ℂ :=
  coefficientFunction m * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)

private theorem coefficientDivisorSum_apply (m n : ℕ) :
    coefficientDivisorSum m n = ∑ q ∈ n.divisors, coefficient q m := by
  exact ArithmeticFunction.coe_mul_zeta_apply

private theorem coefficientDivisorSum_multiplicative (m : ℕ) :
    (coefficientDivisorSum m).IsMultiplicative :=
  (coefficientFunction_multiplicative m).mul ArithmeticFunction.isMultiplicative_zeta.natCast

private theorem sum_coefficient_powers {p : ℕ} (hp : p.Prime) (m k : ℕ) :
    (∑ j ∈ range (k+2), coefficient (p^j) m) = 1 + (localCoefficient p m : ℂ) := by
  induction k with
  | zero =>
    simp [Finset.sum_range_succ, coefficient_one, coefficient_prime hp]
  | succ k ih =>
    rw [show k.succ+2 = (k+2)+1 by omega, Finset.sum_range_succ,
      coefficient_higher_power hp k m, add_zero, ih]

private theorem coefficientDivisorSum_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (m : ℕ) : coefficientDivisorSum m (p^k) = 1 + (localCoefficient p m : ℂ) := by
  rw [coefficientDivisorSum_apply, Nat.sum_divisors_prime_pow hp]
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact sum_coefficient_powers hp m j

/-- Summing the principal coefficients over all divisors gives one local
factor for each prime divisor. The higher prime powers contribute zero. -/
theorem sum_divisors_coefficient_eq_euler (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    (∑ q ∈ n.divisors, (coefficient q m).re) =
      ∏ p ∈ n.primeFactors, (1 + localCoefficient p m) := by
  have hfac : coefficientDivisorSum m n = ∏ p ∈ n.primeFactors,
      coefficientDivisorSum m (p ^ n.factorization p) := by
    rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
      (coefficientDivisorSum_multiplicative m) hn, Nat.prod_factorization_eq_prod_primeFactors]
  have hsum : coefficientDivisorSum m n =
      ((∏ p ∈ n.primeFactors, (1 + localCoefficient p m) : ℝ) : ℂ) := by
    rw [hfac, Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro p hp
    have hdata := Nat.mem_primeFactors.mp hp
    rw [coefficientDivisorSum_prime_pow hdata.1
      (hdata.1.factorization_pos_of_dvd hn hdata.2.1) m]
    simp
  simpa only [coefficientDivisorSum_apply, Complex.re_sum, Complex.ofReal_re] using
    congrArg Complex.re hsum

private theorem local_euler_ratio {p d m a : ℕ} (hp : 2 < p) (hpd : p ∣ d)
    (hmod : m % d = a) :
    1 + localCoefficient p m =
      (if p ∣ a then 1 + 1/((p:ℝ)-2) else 1)/(1+1/((p:ℝ)*((p:ℝ)-2))) := by
  have hpR : (2:ℝ) < p := by exact_mod_cast hp
  have hp₀ : (p:ℝ) ≠ 0 := by linarith
  have hp₁ : (p:ℝ)-1 ≠ 0 := by linarith
  have hp₂ : (p:ℝ)-2 ≠ 0 := by linarith
  have hp₂pos : 0 < (p:ℝ)-2 := by linarith
  have hdvd : p ∣ m ↔ p ∣ a := by
    rw [← hmod]
    exact (Nat.dvd_mod_iff hpd).symm
  apply (eq_div_iff (by positivity : (1:ℝ)+1/((p:ℝ)*((p:ℝ)-2)) ≠ 0)).2
  unfold localCoefficient
  by_cases h : p ∣ a
  · rw [ite_eq_left h, ite_eq_left (hdvd.mpr h)]
    field_simp [hp₀,hp₁,hp₂]
    ring
  · rw [ite_eq_right h, ite_eq_right (fun hm => h (hdvd.mp hm))]
    field_simp [hp₀,hp₁,hp₂]
    ring

/-- The finite Euler value selected by averaging the reflected core along
an even progression with odd modulus. -/
theorem sum_divisors_two_mul_eq_baseline {d m a : ℕ} (hd : Odd d) (hm : Even m)
    (hmod : m % d = a) :
    (∑ q ∈ (2*d).divisors, (coefficient q m).re) =
      2 * ∏ p ∈ d.primeFactors,
        ((if p ∣ a then 1 + 1/((p:ℝ)-2) else 1)/(1+1/((p:ℝ)*((p:ℝ)-2)))) := by
  have hd₀ : d ≠ 0 := by
    intro h
    subst d
    norm_num at hd
  have h₂ : 2 ∉ d.primeFactors := fun h =>
    hd.not_two_dvd_nat (Nat.mem_primeFactors.mp h).2.1
  have hlocal : localCoefficient 2 m = 1 := by
    norm_num [localCoefficient, even_iff_two_dvd.mp hm]
  rw [sum_divisors_coefficient_eq_euler m (mul_ne_zero (by decide) hd₀),
    Nat.primeFactors_mul (by decide : (2:ℕ) ≠ 0) hd₀, Nat.prime_two.primeFactors,
    Finset.singleton_union, Finset.prod_insert h₂, hlocal, one_add_one_eq_two]
  congr 1
  apply Finset.prod_congr rfl
  intro p hp
  obtain ⟨hp',hpd,_⟩ := Nat.mem_primeFactors.mp hp
  have hp₂ : p ≠ 2 := fun h => h₂ (h ▸ hp)
  exact local_euler_ratio (lt_of_le_of_ne hp'.two_le hp₂.symm) hpd hmod

end
end ReflectedShortProgression

namespace ReflectedShortProgression

open Finset Conjectures.Goldbach.EstermannAlmostAllPolylog_aux GoldbachMajorArc
open scoped ComplexConjugate

noncomputable section

private theorem phase_eq_zmod_character (q n a : ℕ) [NeZero q] :
    phase ((n : ℝ) * a / q) = ZMod.stdAddChar ((n*a : ℕ) : ZMod q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
  unfold phase
  congr 1
  push_cast
  ring

private theorem geometric_remainder {z : ℂ} {q : ℕ} (hq : 0 < q)
    (hnorm : ‖z‖ = 1) (hcycle : z^q = 1) (hne : z ≠ 1) (K : ℕ) :
    ‖∑ j ∈ range K, z^j‖ ≤ q := by
  have hsplit : (∑ j ∈ range K, z^j) = ∑ j ∈ range (K % q), z^j := by
    rw [geom_sum_eq hne, geom_sum_eq hne, pow_eq_pow_mod K hcycle]
  rw [hsplit]
  apply (norm_sum_le _ _).trans
  simpa only [norm_pow, hnorm, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
    using (show ((K % q : ℕ) : ℝ) ≤ q by exact_mod_cast (Nat.mod_lt K hq).le)

private theorem phase_progression (q a b D j : ℕ) [NeZero q] :
    phase (((b+D*j : ℕ) : ℝ) * a / q) =
      phase ((b : ℝ)*a/q) * (ZMod.stdAddChar ((D*a : ℕ) : ZMod q))^j := by
  rw [phase_eq_zmod_character, phase_eq_zmod_character, ← AddChar.map_nsmul_eq_pow,
    ← AddChar.map_add_eq_mul]
  congr 1
  push_cast
  rw [nsmul_eq_mul]
  ring

private theorem ram_progression_constant {q D : ℕ} (hq : 0 < q) (hdiv : q ∣ D)
    (b j : ℕ) : ram q (b+D*j) = ram q b := by
  letI : NeZero q := ⟨hq.ne'⟩
  have hD : (D : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff D q).2 hdiv
  apply sum_congr rfl
  intro a _
  rw [phase_progression]
  have hzero : ((D*a : ℕ) : ZMod q) = 0 := by rw [Nat.cast_mul, hD, zero_mul]
  rw [hzero, AddChar.map_zero_eq_one, one_pow, mul_one]

private theorem ram_mean_bound {q D : ℕ} (hq : 0 < q) (hnd : ¬ q ∣ D)
    (b K : ℕ) : ‖∑ j ∈ range K, ram q (b+D*j)‖ ≤ (q : ℝ)^2 := by
  letI : NeZero q := ⟨hq.ne'⟩
  let U := (range q).filter fun a => a.Coprime q
  change ‖∑ j ∈ range K, ∑ a ∈ U, phase (((b+D*j : ℕ) : ℝ)*a/q)‖ ≤ _
  rw [sum_comm]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _a ∈ U, (q : ℝ) := by
      apply sum_le_sum
      intro a ha
      let χ : AddChar (ZMod q) ℂ := ZMod.stdAddChar
      let z := χ ((D*a : ℕ) : ZMod q)
      have hnorm : ‖z‖ = 1 := by
        change ‖ZMod.stdAddChar ((D*a : ℕ) : ZMod q)‖ = 1
        rw [ZMod.stdAddChar_apply]
        exact Circle.norm_coe _
      have hzq : z^q = 1 := by
        change χ ((D*a : ℕ) : ZMod q)^q = 1
        rw [← χ.map_nsmul_eq_pow, nsmul_eq_mul]
        have hq0 : (q : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff q q).2 (dvd_refl q)
        rw [hq0, zero_mul, χ.map_zero_eq_one]
      have hzne : z ≠ 1 := by
        intro hz
        have hcast : ((D*a : ℕ) : ZMod q) = 0 :=
          ZMod.injective_stdAddChar (show χ ((D*a : ℕ) : ZMod q) = χ 0 by
            rw [χ.map_zero_eq_one]; exact hz)
        have hac : a.Coprime q := (mem_filter.mp ha).2
        exact hnd (hac.symm.dvd_of_dvd_mul_right ((ZMod.natCast_eq_zero_iff (D*a) q).1 hcast))
      simp only [phase_progression]
      rw [← mul_sum, norm_mul]
      have hbase : ‖phase ((b:ℝ)*a/q)‖ = 1 := by
        exact Complex.norm_exp_ofReal_mul_I _
      rw [hbase, one_mul]
      exact geometric_remainder hq hnorm hzq hzne K
    _ = (U.card : ℝ)*(q:ℝ) := by simp
    _ ≤ (q : ℝ)^2 := by
      rw [pow_two]
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg q)
      exact_mod_cast ((card_filter_le _ _).trans_eq (card_range q) : U.card ≤ q)

private theorem norm_ram_ratio_le_one {q : ℕ} (hq : 0 < q) :
    ‖ram q 1 / (q.totient : ℂ)‖ ≤ 1 := by
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  rw [norm_div, Complex.norm_natCast, div_le_one hφ]
  unfold ram
  apply (norm_sum_le _ _).trans
  simp only [phase, Complex.norm_exp_ofReal_mul_I, sum_const, nsmul_eq_mul, mul_one]
  rw [Nat.totient_eq_card_coprime, show
    ((range q).filter (fun a => q.Coprime a)) =
      ((range q).filter (fun a => a.Coprime q)) from filter_congr (fun _ _ => Nat.coprime_comm)]

theorem progression_row_error {q D : ℕ} (hq : 0 < q) (b K : ℕ) :
    |(∑ j ∈ range K, (coefficient q (b+D*j)).re) -
      (if q ∣ D then (K : ℝ) * (coefficient q b).re else 0)| ≤ (q : ℝ)^2 := by
  by_cases hdiv : q ∣ D
  · simp only [ite_eq_left hdiv, coefficient, ram_progression_constant hq hdiv, sum_const,
      card_range, nsmul_eq_mul, sub_self, abs_zero]
    positivity
  · rw [ite_eq_right hdiv, sub_zero, ← Complex.re_sum]
    have hsum : (∑ j ∈ range K, coefficient q (b+D*j)) =
        (ram q 1 / (q.totient : ℂ))^2 * conj (∑ j ∈ range K, ram q (b+D*j)) := by
      simp only [coefficient, map_sum, mul_sum]
    apply (Complex.abs_re_le_norm _).trans
    rw [hsum, norm_mul, norm_pow, Complex.norm_conj]
    calc
      _ ≤ (1 : ℝ)^2 * (q : ℝ)^2 := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (norm_nonneg _) (norm_ram_ratio_le_one hq) _
        · exact ram_mean_bound hq hdiv b K
        · positivity
        · positivity
      _ = _ := by ring

theorem progression_prefix_error {D k : ℕ} (hD : 0 < D) (hDk : D ≤ k) (b K : ℕ) :
    |(∑ j ∈ range K, ∑ q ∈ Icc 1 k, (coefficient q (b+D*j)).re) -
      (K : ℝ) * ∑ q ∈ D.divisors, (coefficient q b).re| ≤ (k : ℝ)^3 := by
  let Z (q : ℕ) : ℝ := if q ∣ D then (K : ℝ) * (coefficient q b).re else 0
  have hfilter : ((Icc 1 k).filter (fun q => q ∣ D)) = D.divisors := by
    ext q
    simp only [mem_filter, mem_Icc, Nat.mem_divisors]
    constructor
    · exact fun h => ⟨h.2, hD.ne'⟩
    · rintro ⟨hq, _⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hq hD, (Nat.le_of_dvd hD hq).trans hDk⟩, hq⟩
  have hz : ∑ q ∈ Icc 1 k, Z q = (K : ℝ) * ∑ q ∈ D.divisors, (coefficient q b).re := by
    rw [mul_sum, ← hfilter, sum_filter]
  rw [sum_comm, ← hz, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ q ∈ Icc 1 k, (q : ℝ)^2 := by
      apply sum_le_sum
      intro q hq
      exact progression_row_error (mem_Icc.mp hq).1 b K
    _ ≤ ∑ _q ∈ Icc 1 k, (k : ℝ)^2 := by
      apply sum_le_sum
      intro q hq
      exact pow_le_pow_left₀ (Nat.cast_nonneg q) (by exact_mod_cast (mem_Icc.mp hq).2) _
    _ = (k : ℝ)^3 := by
      simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      ring

end

end ReflectedShortProgression

namespace ReflectedShortProgression

open Finset Filter Conjectures.Goldbach.EstermannAlmostAllPolylog_aux
open scoped Classical Topology

private theorem eventually_log_cube_le {θ c : ℝ} (hθ : 0 < θ) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, (Nat.log 2 (N+2) : ℝ)^3 ≤ c * (N:ℝ)^θ := by
  have ht : Tendsto (fun N : ℕ => (N:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := ((isLittleO_log_rpow_rpow_atTop (3:ℝ) hθ).comp_tendsto ht).bound
    (show 0 < c/64 by positivity)
  filter_upwards [hl, eventually_ge_atTop (2:ℕ)] with N hN h2
  have h1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  change ‖(Real.log (N:ℝ))^(3:ℝ)‖ ≤ (c/64)*‖(N:ℝ)^θ‖ at hN
  have hpow : (Real.log (N:ℝ))^(3:ℝ) = (Real.log (N:ℝ))^(3:ℕ) :=
    Real.rpow_natCast _ 3
  rw [hpow, Real.norm_of_nonneg (pow_nonneg (Real.log_nonneg h1) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hN
  calc
    _ ≤ (4*Real.log (N:ℝ))^3 := by
      simpa only [GoldbachMajorArc.Polylog.cutoff, Nat.cast_pow] using
        GoldbachMajorArc.Polylog.cutoff_le_log 3 h2
    _ = 64*(Real.log (N:ℝ))^3 := by ring
    _ ≤ 64*((c/64)*(N:ℝ)^θ) := mul_le_mul_of_nonneg_left hN (by norm_num)
    _ = _ := by ring

private theorem average_error {N x H d a : ℕ} {ε : ℝ} (hε : 0<ε)
    (hd : Odd d) (ha : a < d)
    (hlo : 4*N ≤ 3*x) (hhi : 2*(x+H) ≤ 3*N) (hH : 2*d ≤ H)
    (hlog : 2*d ≤ Nat.log 2 (N+2))
    (hCube : (Nat.log 2 (N+2):ℝ)^3 ≤ (ε/(8*(d:ℝ)))*(H:ℝ))
    (hNorm : ∀ m : ℕ, 4*N ≤ 3*m → 2*m ≤ 3*N →
      |normalized N m - coefficientPrefix (Nat.log 2 (N+2)) m| ≤ ε/2) :
    |(∑ m ∈ window d a x H, normalized N m)/((window d a x H).card:ℝ) -
      2 * ∏ p ∈ d.primeFactors, ((if p ∣ a then 1+1/((p:ℝ)-2) else 1)/
        (1+1/((p:ℝ)*((p:ℝ)-2))))| ≤ ε := by
  let F := window d a x H
  let k := Nat.log 2 (N+2)
  let E : ℝ := 2 * ∏ p ∈ d.primeFactors, ((if p ∣ a then 1+1/((p:ℝ)-2) else 1)/
    (1+1/((p:ℝ)*((p:ℝ)-2))))
  let A : ℝ := ∑ m ∈ F, normalized N m
  let B : ℝ := ∑ m ∈ F, coefficientPrefix k m
  obtain ⟨b, K, _, _, hK, hF, hinj, hcard, _, hlen⟩ := window_progression hd ha hH
  have hKpos : (0:ℝ)<K := by exact_mod_cast hK
  have hdN : 0<d := by have := Nat.odd_iff.mp hd; omega
  have hdpos : 0<(d:ℝ) := by exact_mod_cast hdN
  have hbF : b ∈ F := by
    rw [show F = _ from hF]
    exact mem_image.mpr ⟨0, mem_range.mpr hK, by simp⟩
  have hb : Even b ∧ b % d = a := (mem_filter.mp hbF).2
  have hD : 0 < 2*d := by omega
  have hE : (∑ q ∈ (2*d).divisors, (GoldbachMajorArc.coefficient q b).re) = E :=
    sum_divisors_two_mul_eq_baseline hd hb.1 hb.2
  have hArc : |A-B| ≤ (K:ℝ)*(ε/2) := by
    dsimp only [A, B]
    rw [← sum_sub_distrib]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _m ∈ F, ε/2 := by
        apply sum_le_sum
        intro m hm
        have hmem : x ≤ m ∧ m ≤ x+H := mem_Icc.mp (mem_filter.mp hm).1
        exact hNorm m (by omega) (by omega)
      _ = _ := by simp only [sum_const, nsmul_eq_mul, show F.card = K from hcard]
  have hArith : |B-(K:ℝ)*E| ≤ (k:ℝ)^3 := by
    dsimp only [B]
    rw [show F = _ from hF, sum_image (fun _ _ _ _ h => hinj h), ← hE]
    exact progression_prefix_error hD hlog b K
  have hSize : (k:ℝ)^3 ≤ (K:ℝ)*(ε/2) := by
    calc
      _ ≤ (ε/(8*(d:ℝ)))*(H:ℝ) := hCube
      _ = ((H:ℝ)/(4*(d:ℝ)))*(ε/2) := by field_simp [hdpos.ne']; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlen (by positivity)
  have hBoth : |A-(K:ℝ)*E| ≤ (K:ℝ)*ε := by
    rw [show A-(K:ℝ)*E = (A-B)+(B-(K:ℝ)*E) by ring]
    exact (abs_add_le _ _).trans (by
      have hSum := add_le_add hArc (hArith.trans hSize)
      linarith only [hSum])
  change |A/(F.card:ℝ) - E| ≤ ε
  rw [show F.card=K from hcard,
    show A/(K:ℝ)-E = (A-(K:ℝ)*E)/(K:ℝ) by field_simp [hKpos.ne'],
    abs_div, abs_of_pos hKpos]
  exact (div_le_iff₀ hKpos).mpr (by simpa only [mul_comm] using hBoth)

theorem eventually_window_average {d a : ℕ} {θ ε : ℝ} (hd : Odd d) (ha : a < d)
    (hθ : 0<θ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x H : ℕ, 4*N ≤ 3*x → 2*(x+H) ≤ 3*N → (N:ℝ)^θ ≤ (H:ℝ) →
    |(∑ m ∈ window d a x H, normalized N m)/((window d a x H).card:ℝ) -
      2 * ∏ p ∈ d.primeFactors, ((if p ∣ a then 1+1/((p:ℝ)-2) else 1)/
        (1+1/((p:ℝ)*((p:ℝ)-2))))| ≤ ε := by
  have hdN : 0<d := by have := Nat.odd_iff.mp hd; omega
  have hdpos : 0 < (d:ℝ) := by exact_mod_cast hdN
  have hc : 0 < ε/(8*(d:ℝ)) := by positivity
  have hθlarge : ∀ᶠ N : ℕ in atTop, (2:ℝ)*(d:ℝ) ≤ (N:ℝ)^θ :=
    ((tendsto_rpow_atTop hθ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop _
  filter_upwards [eventually_log_cube_le hθ hc,
    eventually_normalized_transfer (show 0<ε/2 by positivity),
    eventually_ge_atTop (2^(2*d) : ℕ), hθlarge] with N hcN hNorm hLarge hGrow
  intro x H hLo hHi hH
  have hlog : 2*d ≤ Nat.log 2 (N+2) :=
    Nat.le_log_of_pow_le (by decide) (hLarge.trans (Nat.le_add_right N 2))
  have hHlarge : 2*d ≤ H := by exact_mod_cast hGrow.trans hH
  exact average_error hε hd ha hLo hHi hHlarge hlog
    (hcN.trans (mul_le_mul_of_nonneg_left hH hc.le)) hNorm

end ReflectedShortProgression

open Filter
open scoped Classical

theorem Conjectures.Goldbach.ReflectedShortProgressionMean : by
  classical
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
  let R := fun N m : ℕ => A N m / (2*(N:ℝ)-(m:ℝ))
  let B := fun N : ℕ => (Finset.Icc N (2*N)).filter (band N)
  let avg := fun (F : Finset ℕ) (f : ℕ → ℝ) => (∑ m ∈ F, f m)/(F.card:ℝ)
  exact ∀ d a : ℕ, Odd d → a < d → ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ N x H : ℕ, T ≤ N → 4*N ≤ 3*x → 2*(x+H) ≤ 3*N → (N:ℝ)^θ ≤ (H:ℝ) →
    let F := ((B N) ∩ Finset.Icc x (x+H)).filter (fun m => m % d = a)
    let E := 2 * ∏ p ∈ d.primeFactors, ((if p ∣ a then 1+1/((p:ℝ)-2) else 1)/(1+1/((p:ℝ)*((p:ℝ)-2))))
    |avg F (R N) - E| ≤ ε := by
  dsimp only
  intro d a hd ha θ hθ _ ε hε
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (ReflectedShortProgression.eventually_window_average hd ha hθ hε)
  refine ⟨T,?_⟩
  intro N x H hN hLo hHi hSize
  rw [ReflectedShortProgression.frozen_filter_eq_window hLo hHi]
  simpa only [ReflectedShortProgression.normalized,
    ReflectedShortProgression.coefficient_eq_frozen] using hT N hN x H hLo hHi hSize
