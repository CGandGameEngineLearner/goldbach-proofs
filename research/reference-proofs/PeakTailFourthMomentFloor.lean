import Conjectures.Goldbach.SqrtArcSecondMomentFloor

/-!
The fourth-moment mass above any fixed multiple of the natural scale n/D.
The mask, rational-window integration, and reduced-residue amplitude come
from Goldbach #3727. The reciprocal-square budget below follows its elementary
squarefree count. Here the sieve is restricted to an arithmetic progression.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Interval Topology
open Conjectures.Goldbach.SqrtArcSecondMomentFloor
open Conjectures.Goldbach.SqrtArcSecondMomentFloor.GoldbachSupport

namespace Conjectures.Goldbach.PeakTailFourthMomentFloor

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

private theorem reciprocalSquareBudget (X : ℕ) :
    ∑ d ∈ Ioc 1 X, ((d : ℝ) ^ 2)⁻¹ ≤ 3/4 := by
  by_cases h : 2 ≤ X
  · have ht := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := 2) (n := X) (by decide) h
    rw [← sum_Ioc_consecutive _ (by decide : 1 ≤ 2) h]
    simp only [show Ioc 1 2 = {2} by decide, sum_singleton, Nat.cast_ofNat]
    have hX : 0 ≤ ((X : ℝ)⁻¹) := by positivity
    norm_num at ht ⊢
    linarith
  · have hX : X ≤ 1 := by omega
    norm_num [Ioc_eq_empty_of_le hX]

/-- Solutions of d² ∣ mk+1 have distinct quotients k/d² on a finite range. -/
private theorem oneProgression (m d X : ℕ) :
    ((Ioc 0 X).filter (fun k => d^2 ∣ m*k+1)).card ≤ X/(d^2)+1 := by
  classical
  let s := (Ioc 0 X).filter (fun k => d^2 ∣ m*k+1)
  have mapping : Set.MapsTo (fun k : ℕ => k/(d^2)) s (Finset.range (X/d^2+1)) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le
      (Nat.div_le_div_right (Finset.mem_Ioc.mp (Finset.mem_filter.mp hk).1).2))
  have hinj : Set.InjOn (fun k : ℕ => k/(d^2)) s := by
    intro i hi j hj heq
    have hi' := (mem_filter.mp hi).2
    have hj' := (mem_filter.mp hj).2
    have hc : m.Coprime (d^2) := Nat.Coprime.of_dvd_right hi'
      ((Nat.coprime_mul_left_add_right m 1 i).2 (Nat.coprime_one_right _))
    have hcong : m*i+1 ≡ m*j+1 [MOD d^2] :=
      (Nat.modEq_zero_iff_dvd.2 hi').trans (Nat.modEq_zero_iff_dvd.2 hj').symm
    have hmod : i % d^2 = j % d^2 := Nat.ModEq.cancel_left_of_coprime hc.symm
      (Nat.ModEq.add_right_cancel' 1 hcong)
    calc
      i = d^2*(i/d^2)+i%d^2 := (Nat.div_add_mod i _).symm
      _ = d^2*(j/d^2)+j%d^2 := by rw [show i/d^2 = j/d^2 from heq, hmod]
      _ = j := Nat.div_add_mod j _
  exact (Finset.card_le_card_of_injOn _ mapping hinj).trans_eq (Finset.card_range _)

private theorem countProgression (m X : ℕ) :
    (X : ℝ)/4 - Nat.sqrt (m*X+1) ≤
      (((Ioc 0 X).filter (fun k => Squarefree (m*k+1))).card : ℝ) := by
  classical
  let U := Nat.sqrt (m*X+1)
  let B := (Ioc 0 X).filter (fun k => ¬Squarefree (m*k+1))
  let A := fun d : ℕ => (Ioc 0 X).filter (fun k => d^2 ∣ m*k+1)
  have sub : B ⊆ (Ioc 1 U).biUnion A := by
    intro k hk
    obtain ⟨hkI,hbad⟩ := mem_filter.mp hk
    rw [Nat.squarefree_iff_prime_squarefree] at hbad
    push Not at hbad
    obtain ⟨p,hp,hdvd⟩ := hbad
    have hd : p^2 ∣ m*k+1 := by simpa [pow_two] using hdvd
    have hbound : p^2 ≤ m*X+1 := (Nat.le_of_dvd (by omega) hd).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left m (mem_Ioc.mp hkI).2) 1)
    exact mem_biUnion.mpr ⟨p, mem_Ioc.mpr ⟨hp.one_lt, Nat.le_sqrt'.2 hbound⟩,
      mem_filter.mpr ⟨hkI,hd⟩⟩
  have hbN : B.card ≤ ∑ d ∈ Ioc 1 U, (X/d^2+1) := (card_le_card sub).trans
    (card_biUnion_le.trans (sum_le_sum fun d _ => oneProgression m d X))
  have hb : (B.card : ℝ) ≤ (X : ℝ)*(3/4) + U := calc
    _ ≤ ((∑ d ∈ Ioc 1 U, (X/d^2+1) : ℕ) : ℝ) := by exact_mod_cast hbN
    _ ≤ ∑ d ∈ Ioc 1 U, ((X : ℝ)*((d : ℝ)^2)⁻¹+1) := by
      rw [Nat.cast_sum]
      apply sum_le_sum
      intro d _
      push_cast
      have h := @Nat.cast_div_le ℝ _ _ _ X (d^2)
      rw [Nat.cast_pow, div_eq_mul_inv] at h
      linarith
    _ = (X : ℝ)*(∑ d ∈ Ioc 1 U, ((d : ℝ)^2)⁻¹) + ((Ioc 1 U).card : ℝ) := by
      rw [sum_add_distrib, ← mul_sum]
      simp
    _ ≤ _ := by
      apply add_le_add (mul_le_mul_of_nonneg_left (reciprocalSquareBudget U) (Nat.cast_nonneg _))
      exact_mod_cast (show (Ioc 1 U).card ≤ U by simp)
  have total := Finset.card_filter_add_card_filter_not
    (s := Ioc 0 X) (p := fun k => Squarefree (m*k+1))
  have total' : (((Ioc 0 X).filter (fun k => Squarefree (m*k+1))).card : ℝ) + B.card = X := by
    exact_mod_cast (show ((Ioc 0 X).filter (fun k => Squarefree (m*k+1))).card + B.card = X by
      simpa [B] using total)
  change (X : ℝ)/4 - (U : ℝ) ≤ _
  linarith only [total', hb]

private theorem blockProgression (m T : ℕ) (hT : 16*m+1 ≤ T) :
    T ≤ ((Ioc T (16*T)).filter (fun k => Squarefree (m*k+1))).card := by
  classical
  have h := countProgression m (16*T)
  have hr : Nat.sqrt (m*(16*T)+1) ≤ T := by
    by_contra! hbad
    have haux := Nat.le_sqrt.mp (show T+1 ≤ Nat.sqrt (m*(16*T)+1) by omega)
    have hzero : 0 < T := by omega
    nlinarith only [haux, Nat.mul_le_mul_right T hT, hzero]
  let f := fun k => Squarefree (m*k+1)
  have part : ((Ioc 0 T).filter f).card + ((Ioc T (16*T)).filter f).card =
      ((Ioc 0 (16*T)).filter f).card := by
    rw [← Ioc_union_Ioc_eq_Ioc (Nat.zero_le T) (show T ≤ 16*T by omega), filter_union,
      card_union_of_disjoint]
    exact (Ioc_disjoint_Ioc_of_le (by rfl : T ≤ T)).mono (filter_subset ..) (filter_subset ..)
  have hleft : ((Ioc 0 T).filter f).card ≤ T := by
    simpa using card_le_card (filter_subset f (Ioc 0 T))
  have hblock : 3*T ≤ ((Ioc 0 (16*T)).filter f).card := by
    change ((16*T : ℕ) : ℝ)/4 - _ ≤ (((Ioc 0 (16*T)).filter f).card : ℝ) at h
    push_cast at h
    have hreal : (Nat.sqrt (m*(16*T)+1) : ℝ) ≤ T := by exact_mod_cast hr
    exact_mod_cast (show (3:ℝ)*T ≤ (((Ioc 0 (16*T)).filter f).card : ℝ) by linarith only [h, hreal])
  change T ≤ ((Ioc T (16*T)).filter f).card
  omega

/-- A positive reciprocal mass of denominators has small enough totient that
the amplitudes below the specified threshold cannot account for its residue sum. -/
private theorem richBlock (A : ℝ) (hA : 0 < A) :
    ∃ D₀ : ℕ, ∃ σ : ℝ, 0 < σ ∧ ∀ D ≥ D₀, 0 < D ∧ ∃ s : Finset ℕ,
      (∀ q ∈ s, D < q ∧ q ≤ 40*D ∧ Squarefree q ∧ 16*A*(q.totient : ℝ) ≤ D) ∧
      σ ≤ ∑ q ∈ s, 1/(q : ℝ) := by
  classical
  obtain ⟨m,hsq,hthin⟩ := thinTotient (640*A)
  have hm : 0 < m := Nat.pos_of_ne_zero hsq.ne_zero
  have hm₂ : 0 < m*m := Nat.mul_pos hm hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨(16*m+1)*(m*m),1/(40*(m : ℝ)^2),by positivity,?_⟩
  intro D hD
  let T := D/(m*m)+1
  have hT : 16*m+1 ≤ T := Nat.le_succ_of_le ((Nat.le_div_iff_mul_le hm₂).2 hD)
  have hDlarge : m*m ≤ D := (Nat.le_mul_of_pos_left (m*m) (by omega : 0<16*m+1)).trans hD
  have hDpos := hm₂.trans_le hDlarge
  have hlow : D < (m*m)*T := by
    simpa [T, Nat.mul_comm] using
      (Nat.div_lt_iff_lt_mul hm₂).1 (Nat.lt_succ_self (D/(m*m)))
  have hhigh : (m*m)*T ≤ 2*D := by
    dsimp [T]
    rw [Nat.mul_succ]
    have hprod : (m*m)*(D/(m*m)) ≤ D := by
      rw [Nat.mul_comm]
      exact Nat.div_mul_le_self ..
    omega
  let U := (Ioc T (16*T)).filter (fun k => Squarefree (m*k+1))
  let f := fun k : ℕ => m*(m*k+1)
  let s := U.image f
  have inj : Function.Injective f := by
    intro a b h
    change m*(m*a+1) = m*(m*b+1) at h
    exact Nat.eq_of_mul_eq_mul_left hm (Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left hm h))
  have hnum : T ≤ s.card := by
    simpa [s, Finset.card_image_of_injective _ inj, U] using blockProgression m T hT
  have hmem {k : ℕ} (hk : k ∈ U) : D < f k ∧ f k ≤ 40*D ∧
      Squarefree (f k) ∧ 16*A*((f k).totient : ℝ) ≤ D := by
    obtain ⟨hkI,hrsq⟩ := mem_filter.mp hk
    obtain ⟨hlt,hltop⟩ := mem_Ioc.mp hkI
    have hd : D < f k := by
      dsimp [f]
      nlinarith only [hlow, Nat.mul_le_mul_left (m*m) hlt.le, hm]
    have hmD : m ≤ D := (Nat.le_mul_self m).trans hDlarge
    have hup : f k ≤ 40*D := by
      dsimp [f]
      nlinarith only [Nat.mul_le_mul_left (m*m) hltop,hhigh,hmD, Nat.zero_le D]
    have hcop : m.Coprime (m*k+1) := (Nat.coprime_mul_left_add_right m 1 k).2
      (Nat.coprime_one_right _)
    refine ⟨hd,hup,Nat.squarefree_mul_iff.mpr ⟨hcop,hsq,hrsq⟩,?_⟩
    let r := m*k+1
    have hr : (0 : ℝ) < r := by exact_mod_cast Nat.succ_pos (m*k)
    have hh : (m : ℝ)*r ≤ 40*(D : ℝ) := by exact_mod_cast hup
    have hφr : (r.totient : ℝ) ≤ r := by exact_mod_cast Nat.totient_le r
    have hu := (mul_le_mul_of_nonneg_left hφr (show 0 ≤ 640*A*(m.totient : ℝ) by positivity)).trans_lt
      (mul_lt_mul_of_pos_right hthin hr)
    change 16*A*((m*r).totient : ℝ) ≤ D
    rw [Nat.totient_mul hcop, Nat.cast_mul]
    linarith only [show 640*A*((m.totient : ℝ)*r.totient) < (m : ℝ)*r by
      simpa only [mul_assoc] using hu, hh]
  have hall : ∀ q ∈ s, D < q ∧ q ≤ 40*D ∧ Squarefree q ∧ 16*A*(q.totient : ℝ) ≤ D := by
    intro q hq
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hq
    exact hmem hk
  refine ⟨hDpos,s,hall,?_⟩
  have hDR : 0 < (D : ℝ) := by exact_mod_cast hDpos
  have hTmass : (D : ℝ) ≤ (m : ℝ)^2*T := by
    exact_mod_cast (show D ≤ m^2*T by simpa [pow_two] using hlow.le)
  calc
    1/(40*(m : ℝ)^2) ≤ (T : ℝ)*(1/(40*D)) := by
      field_simp
      nlinarith only [hTmass]
    _ ≤ (s.card : ℝ)*(1/(40*D)) := by gcongr
    _ = ∑ _q ∈ s, (1/(40*(D : ℝ))) := by simp
    _ ≤ ∑ q ∈ s, 1/(q : ℝ) := by
      apply sum_le_sum
      intro q hq
      apply one_div_le_one_div_of_le (by exact_mod_cast (hDpos.trans (hall q hq).1))
      exact_mod_cast (hall q hq).2.1

/-- Discarding all amplitudes up to A*n/D costs at most n/16 in the reduced-residue sum. -/
private theorem excessAmplitude {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    {A n D : ℝ} (hn : 0 < n) (hD : 0 < D) (hsmall : 16*A*(s.card : ℝ) ≤ D)
    (hsize : (s.card : ℝ) ≤ 40*D) (hamp : n/8 ≤ ‖∑ a ∈ s, z a‖) :
    n/8 ≤ ‖∑ a ∈ s, (((1280*D/n)*(max 0 (‖z a‖-A*n/D))^2 : ℝ) : ℂ)‖ := by
  let b := A*n/D
  let v := fun a => max 0 (‖z a‖-b)
  have hbudget : (s.card : ℝ)*b ≤ n/16 := by
    dsimp [b]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hD).2
    nlinarith only [mul_le_mul_of_nonneg_right hsmall hn.le]
  have near : ∑ a ∈ s, ‖z a‖ ≤ ∑ a ∈ s, (v a+b) := by
    apply sum_le_sum
    intro a _
    exact (sub_le_iff_le_add).1 (le_max_right 0 (‖z a‖-b))
  rw [sum_add_distrib, sum_const, nsmul_eq_mul] at near
  have hres : n/16 ≤ ∑ a ∈ s, v a := by
    linarith only [hamp.trans (norm_sum_le s z), near, hbudget]
  have henergy := (pow_le_pow_left₀ (by positivity : 0 ≤ n/16) hres 2).trans
    (sq_sum_le_card_mul_sum_sq (s := s) (f := v))
  have hnneg : 0 ≤ ∑ a ∈ s, v a ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  change n/8 ≤ ‖∑ a ∈ s, (((1280*D/n)*v a^2 : ℝ) : ℂ)‖
  rw [← Complex.ofReal_sum, ← mul_sum, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) hnneg), div_mul_eq_mul_div]
  apply (le_div_iff₀ hn).2
  nlinarith only [henergy.trans (mul_le_mul_of_nonneg_right hsize hnneg)]

private theorem integrateExcess (mask : Set ℝ) (V : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b) :
    (∫ t in (0 : ℝ)..1, mask.indicator (fun u => ‖((b*(V u)^2 : ℝ) : ℂ)‖^2) t)
      = b^2 * ∫ t in (0 : ℝ)..1, mask.indicator (fun u => (V u)^4) t := by
  classical
  have h (t : ℝ) : mask.indicator (fun u => ‖((b*(V u)^2 : ℝ) : ℂ)‖^2) t =
      b^2 * mask.indicator (fun u => (V u)^4) t := by
    by_cases ht : t ∈ mask
    · simp only [Set.indicator_of_mem ht, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hb (sq_nonneg _))]
      ring
    · simp [Set.indicator_of_notMem ht]
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul]

theorem tailFloor (A : ℝ) (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∃ N D₀ : ℕ, ∀ n ≥ N, ∀ D ≥ D₀, ∀ H : ℕ,
      160*(D : ℝ) ≤ Real.sqrt n → (H : ℝ) ≤ Real.sqrt n →
      c*(n : ℝ)^3 ≤ (D : ℝ)^2 *
        ∫ t in (0 : ℝ)..1, (publishedWideArcs D H n)ᶜ.indicator
          (fun u => (max 0 (‖GoldbachL2Arithmetic.primeSum n u‖-A*n/D))^4) t := by
  classical
  obtain ⟨D₀,σ,hσ,hblocks⟩ := richBlock A hA
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.1 primeAmplitudeBounds
  refine ⟨σ/(384*1280^2),by positivity,N,D₀,?_⟩
  intro n hn D hD H hcut hH
  obtain ⟨hn2,hθ,hlog⟩ := hN n hn
  obtain ⟨hD0,s,hall,hmass⟩ := hblocks D hD
  have hn0 : 0<n := by omega
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  have hDR : (0:ℝ) < D := by exact_mod_cast hD0
  have hfit {q : ℕ} (hq : q ∈ s) : q ≤ ⌊Real.sqrt n/4⌋₊ := by
    apply Nat.le_floor
    have hr : (q : ℝ) ≤ 40*D := by exact_mod_cast (hall q hq).2.1
    linarith only [hr,hcut]
  obtain ⟨hend,hmask,hpair⟩ := denominatorWindowLimits n D H hn2
    (by linarith only [hcut,hDR]) hH
  let V := fun u => max 0 (‖GoldbachL2Arithmetic.primeSum n u‖-A*n/D)
  let b : ℝ := 1280*D/n
  let T := fun t => ((b*(V t)^2 : ℝ) : ℂ)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : Continuous (GoldbachL2Arithmetic.primeSum n) := by
    unfold GoldbachL2Arithmetic.primeSum GoldbachL2Arithmetic.primeTerm GoldbachL2Arithmetic.E
    fun_prop
  have hT : Continuous T := by dsimp [T,V]; fun_prop
  have hw := assembleWindows s D H n T hT hn0
    (fun q hq => (hall q hq).1)
    (fun q hq => hend q (hfit hq))
    (fun q hq => hmask q (hfit hq))
    (fun q hq r hr => hpair q r (hfit hq) (hfit hr))
    (by
      intro q hq h hh
      let R := (Finset.range q).filter (fun a => Nat.Coprime a q)
      have hcard : R.card = q.totient := by
        simp only [R,Nat.totient_eq_card_coprime,Nat.coprime_comm (m := q)]
      have hsz : (R.card : ℝ) ≤ 40*D := by
        exact_mod_cast ((Finset.card_filter_le ..).trans_eq (Finset.card_range q)).trans (hall q hq).2.1
      apply excessAmplitude R (fun a => GoldbachL2Arithmetic.primeSum n ((a : ℝ)/q+h)) hnR hDR
      · simpa only [hcard] using (hall q hq).2.2.2
      · exact hsz
      · exact GoldbachL2Arithmetic.reduced_amplitude n q hn0 (hall q hq).2.2.1 hθ
          (hlog q (hfit hq)) h hh.1 hh.2)
  let I := ∫ t in (0 : ℝ)..1, (publishedWideArcs D H n)ᶜ.indicator (fun u => (V u)^4) t
  have hscaled : (σ/384)*(n : ℝ) ≤ b^2 * I := by
    have he := (scaleDenominatorMass s n σ 1 (by simpa using hmass)).trans hw
    change _ ≤ ∫ t in (0 : ℝ)..1, (publishedWideArcs D H n)ᶜ.indicator
      (fun u => ‖((b*(V u)^2 : ℝ):ℂ)‖^2) t at he
    rw [integrateExcess _ V b hb] at he
    simpa only [mul_one] using he
  have hscale : b^2*(n : ℝ)^2 = 1280^2*(D : ℝ)^2 := by
    dsimp [b]
    field_simp
  have hscaled' := mul_le_mul_of_nonneg_right hscaled (sq_nonneg (n : ℝ))
  change (σ/(384*1280^2))*(n : ℝ)^3 ≤ (D : ℝ)^2*I
  have hr : (b^2*I)*(n : ℝ)^2 = 1280^2*((D : ℝ)^2*I) := by
    calc
      _ = (b^2*(n : ℝ)^2)*I := by ring
      _ = _ := by rw [hscale]; ring
  rw [hr] at hscaled'
  linarith only [hscaled']

end Conjectures.Goldbach.PeakTailFourthMomentFloor

open Conjectures.Goldbach.PeakTailFourthMomentFloor in
/-- A fixed positive proportion on the fourth-moment scale persists above
any prescribed multiple of n/D. The constant may depend on that multiple. -/
theorem Conjectures.Goldbach.PeakTailFourthMomentFloor :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k : ℝ) else 0
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I)
    let S := fun (n : ℕ) (t : ℝ) => ∑ k ∈ Finset.range (n+1), (w k : ℂ)*E ((k : ℝ)*t)
    let arcs := fun (n D H : ℕ) => {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ D ∧ a ≤ q ∧
      Nat.Coprime a q ∧ |t-(a : ℝ)/q| ≤ (H : ℝ)/((q : ℝ)*n)}
    ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∃ N D₀ : ℕ, ∀ n ≥ N, ∀ D ≥ D₀, ∀ H : ℕ,
      160*(D : ℝ) ≤ Real.sqrt n → (H : ℝ) ≤ Real.sqrt n →
      c*(n : ℝ)^3 ≤ (D : ℝ)^2 * intervalIntegral
        (fun t => (arcs n D H)ᶜ.indicator (fun u => (max 0 (‖S n u‖-A*n/D))^4) t)
        (0 : ℝ) 1 MeasureTheory.volume := by
  simpa only [GoldbachL2Arithmetic.primeSum_eq_catalogue, GoldbachL2Arithmetic.E,
    publishedWideArcs] using tailFloor
