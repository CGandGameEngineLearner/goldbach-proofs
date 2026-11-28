import Conjectures.Goldbach.SqrtArcSecondMomentFloor

/-!
Large pointwise values outside the published rational arcs.
The reduced-residue amplitude and Farey separation estimates are from #3727.
The additional factor comes from selecting a squarefree denominator with
small totient relative to its size, uniformly in each sufficiently high block.
-/

namespace Conjectures.Goldbach.EndpointPrimePeaks

open Finset Filter
open Conjectures.Goldbach.SqrtArcSecondMomentFloor
open Conjectures.Goldbach.SqrtArcSecondMomentFloor.GoldbachSupport
open scoped BigOperators

private theorem primeProduct (s : Finset Nat.Primes) :
    let m := ∏ p ∈ s, (p : ℕ)
    Squarefree m ∧ (1 + ∑ p ∈ s, (1 / (p : ℝ))) * (m.totient : ℝ) ≤ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    let m := ∏ t ∈ s, (t : ℕ)
    have hc : (p : ℕ).Coprime m := by
      apply Nat.coprime_prod_right_iff.mpr
      intro t ht
      apply (Nat.coprime_primes p.property t.property).mpr
      intro heq
      exact hp (Subtype.ext heq ▸ ht)
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hsum : 0 ≤ ∑ t ∈ s, (1 / (t : ℝ)) := by positivity
    have hstep : (1 + (1 / (p : ℝ) + ∑ t ∈ s, 1 / (t : ℝ))) * ((p : ℝ) - 1)
        ≤ (p : ℝ) * (1 + ∑ t ∈ s, 1 / (t : ℝ)) := by
      have hdiv : 1 / (p : ℝ) * (p : ℝ) = 1 := by field_simp
      have hrec : 0 ≤ 1 / (p : ℝ) := by positivity
      nlinarith only [hdiv, hsum, hrec]
    simp only [Finset.prod_insert hp, Finset.sum_insert hp]
    change Squarefree ((p : ℕ) * m) ∧ _
    refine ⟨Nat.squarefree_mul_iff.mpr ⟨hc, p.property.squarefree, ih.1⟩, ?_⟩
    change (1 + (1 / (p : ℝ) + ∑ t ∈ s, 1 / (t : ℝ))) *
      (((p : ℕ) * m).totient : ℝ) ≤ (((p : ℕ) * m : ℕ) : ℝ)
    rw [Nat.totient_mul hc, Nat.totient_prime p.property, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_sub p.property.one_le, Nat.cast_one, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hstep (Nat.cast_nonneg m.totient)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih.2 hp0.le)

private theorem thinTotient (B : ℝ) : ∃ m : ℕ, Squarefree m ∧ B * (m.totient : ℝ) < m := by
  classical
  have hex : ∃ s : Finset Nat.Primes, B < ∑ p ∈ s, (1 / (p : ℝ)) := by
    by_contra! h
    exact Nat.Primes.not_summable_one_div (summable_of_sum_le (fun p => by positivity) h)
  obtain ⟨s, hs⟩ := hex
  let m := ∏ p ∈ s, (p : ℕ)
  obtain ⟨hsq,hbound⟩ := primeProduct s
  have hm : 0 < m := Finset.prod_pos fun p _ => p.property.pos
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  exact ⟨m, hsq, (mul_lt_mul_of_pos_right (by linarith only [hs] :
    B < 1 + ∑ p ∈ s, (1 / (p : ℝ))) hφ).trans_le hbound⟩

private theorem denominators (C : ℝ) (hC : 0 < C) :
    ∃ D₀ : ℕ, ∀ D ≥ D₀, ∃ q : ℕ, D < q ∧ q ≤ 2*D ∧ Squarefree q ∧
      8 * C * (q.totient : ℝ) < D := by
  obtain ⟨m, hsq, hthin⟩ := thinTotient (16*C)
  have hm : 0 < m := Nat.pos_of_ne_zero hsq.ne_zero
  refine ⟨m*m, ?_⟩
  intro D hD
  have hdiv : m ≤ D / m := (Nat.le_div_iff_mul_le hm).2 hD
  obtain ⟨r, hr, hrgt, hrle⟩ := Nat.exists_prime_lt_and_le_two_mul (D/m)
    ((hm.trans_le hdiv).ne')
  have hcop : m.Coprime r := (hr.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hm (hdiv.trans_lt hrgt))).symm
  have hlow : D < m*r := by
    simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hm).1 hrgt
  have hhigh : m*r ≤ 2*D := by
    calc
      m*r ≤ m*(2*(D/m)) := Nat.mul_le_mul_left m hrle
      _ = 2*((D/m)*m) := by ring
      _ ≤ 2*D := Nat.mul_le_mul_left _ (Nat.div_mul_le_self ..)
  refine ⟨m*r, hlow, hhigh, Nat.squarefree_mul_iff.mpr ⟨hcop, hsq, hr.squarefree⟩, ?_⟩
  rw [Nat.totient_mul hcop, Nat.cast_mul]
  have hφr : (r.totient : ℝ) ≤ r := by exact_mod_cast Nat.totient_le r
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hg : (m : ℝ) * r ≤ 2 * D := by exact_mod_cast hhigh
  have hφm : 0 ≤ (m.totient : ℝ) := Nat.cast_nonneg _
  have hl := mul_le_mul_of_nonneg_left hφr (show 0 ≤ 16*C*(m.totient : ℝ) by positivity)
  have hu := mul_lt_mul_of_pos_right hthin hr0
  linarith only [show 16*C*((m.totient : ℝ)*r.totient) < (m : ℝ)*r by
    simpa only [mul_assoc] using hl.trans_lt hu, hg]

private theorem largeResidue (n q D : ℕ) (C h : ℝ) (hn : 0 < n)
    (hφ : 8*C*(q.totient : ℝ) < D)
    (hamplitude : (n : ℝ)/8 ≤ ‖∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
      GoldbachL2Arithmetic.primeSum n ((a : ℝ)/q+h)‖) :
    ∃ a : ℕ, a < q ∧ a.Coprime q ∧
      C*(n : ℝ) < (D : ℝ)*‖GoldbachL2Arithmetic.primeSum n ((a : ℝ)/q+h)‖ := by
  classical
  let s := (Finset.range q).filter (fun a => Nat.Coprime a q)
  let z := fun a : ℕ => GoldbachL2Arithmetic.primeSum n ((a : ℝ)/q+h)
  have hcard : s.card = q.totient := by
    simp only [s, Nat.totient_eq_card_coprime, Nat.coprime_comm (m := q)]
  by_contra! hbad
  have upper : ∑ a ∈ s, (D : ℝ)*‖z a‖ ≤ ∑ _a ∈ s, C*(n : ℝ) := by
    apply Finset.sum_le_sum
    intro a ha
    obtain ⟨ha1, ha2⟩ : a < q ∧ a.Coprime q := by simpa [s] using ha
    exact hbad a ha1 ha2
  rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hcard] at upper
  have lower := mul_le_mul_of_nonneg_left (hamplitude.trans (norm_sum_le s z))
    (Nat.cast_nonneg D : 0 ≤ (D : ℝ))
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  nlinarith only [lower.trans upper, mul_lt_mul_of_pos_right hφ hn']

theorem peaks :
    ∀ C : ℝ, 0 < C → ∃ N D₀ : ℕ, ∀ n ≥ N, ∀ D ≥ D₀, ∀ H : ℕ,
      16*(D : ℝ) ≤ Real.sqrt n → (H : ℝ) ≤ Real.sqrt n →
      ∃ q : ℕ, D < q ∧ q ≤ 2*D ∧ Squarefree q ∧
      ∀ h ∈ Set.Icc (0 : ℝ) (1/(6*(n : ℝ))), ∃ a : ℕ,
        a < q ∧ a.Coprime q ∧ (a : ℝ)/q+h ∈ Set.Icc (0 : ℝ) 1 ∧
        (a : ℝ)/q+h ∉ GoldbachSupport.publishedWideArcs D H n ∧
        C*(n : ℝ) < (D : ℝ)*‖GoldbachL2Arithmetic.primeSum n ((a : ℝ)/q+h)‖ := by
  intro C hC
  obtain ⟨D₀, hD₀⟩ := denominators C hC
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 primeAmplitudeBounds
  refine ⟨N, D₀, ?_⟩
  intro n hn D hD H hcut hH
  obtain ⟨hn2, hθ, hlog⟩ := hN n hn
  have hn0 : 0 < n := by omega
  obtain ⟨q, hdq, hqD, hsq, hφ⟩ := hD₀ D hD
  have hD' := Nat.cast_nonneg D (α := ℝ)
  have hqR : (q : ℝ) ≤ 2*(D : ℝ) := by exact_mod_cast hqD
  have hfit : q ≤ ⌊Real.sqrt n / 4⌋₊ := Nat.le_floor (by linarith only [hqR, hcut, hD'])
  obtain ⟨hend, hmask, _⟩ := denominatorWindowLimits n D H hn2
    (by linarith only [hcut, hD']) hH
  refine ⟨q, hdq, hqD, hsq, ?_⟩
  intro h hh
  obtain ⟨a, haq, hcop, hpeak⟩ := largeResidue n q D C h hn0 hφ
    (GoldbachL2Arithmetic.reduced_amplitude n q hn0 hsq hθ (hlog q hfit) h hh.1 hh.2)
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hdq
  have ha1 : (a : ℝ)+1 ≤ q := by exact_mod_cast haq
  have hhq : h ≤ 1/(q : ℝ) := hh.2.trans (one_div_le_one_div_of_le hqpos (hend q hfit))
  have htop : (a : ℝ)/q+h ≤ 1 := calc
    _ ≤ (a : ℝ)/q+1/q := by linarith only [hhq]
    _ = ((a : ℝ)+1)/q := by ring
    _ ≤ 1 := (div_le_one hqpos).2 ha1
  refine ⟨a, haq, hcop, ⟨add_nonneg (by positivity) hh.1, htop⟩, ?_, hpeak⟩
  exact GoldbachSupport.outsideWideArcs a q D H n h hcop hdq hn0 hh.1 hh.2 (hmask q hfit)

end Conjectures.Goldbach.EndpointPrimePeaks

open Conjectures.Goldbach.EndpointPrimePeaks
open Conjectures.Goldbach.SqrtArcSecondMomentFloor

/-- No fixed multiple of n/D bounds the prime sum on the exterior, even on these short rational windows. -/
theorem Conjectures.Goldbach.EndpointPrimePeaks :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I)
    let S := fun (n : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (n+1), (w k : ℂ)*E ((k : ℝ)*t)
    let arcs := fun (n D H : ℕ) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t-(a : ℝ)/q| ≤ (H : ℝ)/((q : ℝ)*n)}
    ∀ C : ℝ, 0 < C → ∃ N D₀ : ℕ, ∀ n ≥ N, ∀ D ≥ D₀, ∀ H : ℕ,
      16*(D : ℝ) ≤ Real.sqrt n → (H : ℝ) ≤ Real.sqrt n →
      ∃ q : ℕ, D < q ∧ q ≤ 2*D ∧ Squarefree q ∧
      ∀ h ∈ Set.Icc (0 : ℝ) (1/(6*(n : ℝ))), ∃ a : ℕ,
        a < q ∧ a.Coprime q ∧ (a : ℝ)/q+h ∈ Set.Icc (0 : ℝ) 1 ∧
        (a : ℝ)/q+h ∉ arcs n D H ∧ C*(n : ℝ) < (D : ℝ)*‖S n ((a : ℝ)/q+h)‖ := by
  simpa only [GoldbachL2Arithmetic.primeSum_eq_catalogue, GoldbachL2Arithmetic.E,
    GoldbachSupport.publishedWideArcs] using peaks
