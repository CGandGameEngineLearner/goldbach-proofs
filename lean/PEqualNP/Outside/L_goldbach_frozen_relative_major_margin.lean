import Mathlib

/-!
# Relative major-arc margin interface for the frozen minor-arc decomposition (B10)

This file formalizes `L-goldbach-frozen-relative-major-margin` for the `minor-truncation`
route feeding `L-goldbach-arc-budget-transfer` and `L-goldbach-binary-pointwise-positivity`.

Given any major-arc lower-bound witness `c > 0` on `arcs n` (`c * n ≤ (major n).re`) and a
relative high-high minor-arc lower bound `-(c * n / 2) ≤ (I n (high n) (high n)).re`,
combining the full-circle representation identity with unconditional Parseval bounds on
`I n (low n) (low n)` and `I n (low n) (high n)` yields `c * n / 4 ≤ ∑_{p ≤ n} w p * w (n - p)`
for all sufficiently large even `n`.
-/

namespace FrozenRelativeMajorMargin

open Finset Filter MeasureTheory Real Complex Topology

noncomputable section

def w (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * t))

def Q (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def arcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}

def f (n : ℕ) (t : ℝ) : ℂ := (S n w t) ^ 2 * E (-(n : ℝ) * t)

def major (n : ℕ) : ℂ :=
  intervalIntegral (fun t => (arcs n).indicator (f n) t) (0 : ℝ) 1 MeasureTheory.volume

def low (n k : ℕ) : ℝ := if k ^ 3 ≤ n then w k else 0

def high (n k : ℕ) : ℝ := w k - low n k

def I (n : ℕ) (a b : ℕ → ℝ) : ℂ :=
  intervalIntegral
    (fun t => (arcs n)ᶜ.indicator (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t)
    (0 : ℝ) 1 MeasureTheory.volume

private lemma norm_E (x : ℝ) : ‖E x‖ = 1 := by
  unfold E
  exact Complex.norm_exp_ofReal_mul_I (2 * Real.pi * x)

private lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma E_neg (x : ℝ) : E (-x) = star (E x) := by
  unfold E
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  simp [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]

private lemma S_add (n : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    S n (fun k => a k + b k) t = S n a t + S n b t := by
  unfold S
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

private lemma S_low_add_high (n : ℕ) (t : ℝ) :
    S n w t = S n (low n) t + S n (high n) t := by
  have hw : w = fun k => low n k + high n k := by
    ext k
    unfold high
    ring
  conv_lhs => rw [hw]
  exact S_add n (low n) (high n) t

private lemma measurableSet_arcs (n : ℕ) : MeasurableSet (arcs n) := by
  unfold arcs
  simp only [Set.ofPred_exists]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  by_cases h : 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q
  · have heq : {t : ℝ | 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))} =
        {t : ℝ | |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))} := by
      ext t
      exact ⟨fun ht => ht.2.2.2.2, fun ht => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, ht⟩⟩
    rw [heq]
    exact measurableSet_le (f := fun t : ℝ => |t - (a : ℝ) / (q : ℝ)|)
      (g := fun _ => (Q n : ℝ) / ((q : ℝ) * (n : ℝ))) (by fun_prop) measurable_const
  · have heq : {t : ℝ | 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))} = ∅ := by
      ext t
      exact ⟨fun ht => False.elim (h ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩), fun ht => False.elim ht⟩
    rw [heq]
    exact MeasurableSet.empty

private lemma integrable_arcs_f (n : ℕ) :
    IntervalIntegrable (fun t => (arcs n).indicator (f n) t) MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hcont : Continuous (f n) := by
    unfold f S E
    fun_prop
  exact (hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    (measurableSet_arcs n)

private lemma integrable_I (n : ℕ) (a b : ℕ → ℝ) :
    IntervalIntegrable
      (fun t => (arcs n)ᶜ.indicator (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t)
      MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hcont : Continuous (fun u : ℝ => S n a u * S n b u * E (-(n : ℝ) * u)) := by
    unfold S E
    fun_prop
  exact (hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    (measurableSet_arcs n).compl

private lemma norm_I_le (n : ℕ) (a b : ℕ → ℝ) :
    ‖I n a b‖ ≤ ∫ t in (0 : ℝ)..1, ‖S n a t‖ * ‖S n b t‖ := by
  unfold I
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun t _ => ?_
  · exact (integrable_I n a b).norm
  · have hcont : Continuous (fun t : ℝ => ‖S n a t‖ * ‖S n b t‖) := by
      unfold S E
      fun_prop
    exact hcont.intervalIntegrable 0 1
  · by_cases ht : t ∈ (arcs n)ᶜ
    · rw [Set.indicator_of_mem ht, norm_mul, norm_mul, norm_E, mul_one]
    · rw [Set.indicator_of_notMem ht, norm_zero]
      positivity

private lemma integral_E_int (m : ℤ) :
    ∫ t in (0 : ℝ)..1, E ((m : ℝ) * t) = if m = 0 then (1 : ℂ) else 0 := by
  split_ifs with hm
  · subst hm
    simp [E]
  · set c : ℂ := ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I
    have hc : c ≠ 0 := by
      intro h0
      simp only [c, mul_eq_zero, Complex.I_ne_zero, or_false, Complex.ofReal_eq_zero,
        Int.cast_eq_zero, OfNat.ofNat_ne_zero, false_or] at h0
      rcases h0 with hpi | hm0
      · exact Real.pi_ne_zero hpi
      · exact hm hm0
    have heq : (fun t : ℝ => E ((m : ℝ) * t)) = fun t : ℝ => Complex.exp (c * (t : ℂ)) := by
      funext t
      unfold E
      congr 1
      dsimp [c]
      push_cast
      ring
    rw [heq, integral_exp_mul_complex hc]
    have h1 : Complex.exp c = 1 := by
      dsimp [c]
      have : ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I = (m : ℤ) * (2 * Real.pi * Complex.I) := by
        push_cast
        ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, h1, sub_self, zero_div]

private lemma integral_normSq_S (n : ℕ) (u : ℕ → ℝ) :
    ∫ t in (0 : ℝ)..1, ‖S n u t‖ ^ 2 = ∑ k ∈ Finset.range (n + 1), (u k) ^ 2 := by
  have hint_c : ∫ t in (0 : ℝ)..1, ((‖S n u t‖ ^ 2 : ℝ) : ℂ) =
      ((∑ k ∈ Finset.range (n + 1), (u k) ^ 2 : ℝ) : ℂ) := by
    have hterm : ∀ t : ℝ, ((‖S n u t‖ ^ 2 : ℝ) : ℂ) =
        ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
          ((u j * u k : ℝ) : ℂ) * E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) := by
      intro t
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, ← Complex.star_def]
      unfold S
      rw [Finset.sum_mul, star_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [star_mul, Complex.star_def, Complex.conj_ofReal, ← Complex.star_def, ← E_neg]
      have hE : E ((j : ℝ) * t) * E (-((k : ℝ) * t)) =
          E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) := by
        rw [← E_add]
        congr 1
        push_cast
        ring
      calc
        (u j : ℂ) * E ((j : ℝ) * t) * (E (-((k : ℝ) * t)) * (u k : ℂ))
            = ((u j * u k : ℝ) : ℂ) * (E ((j : ℝ) * t) * E (-((k : ℝ) * t))) := by
              push_cast
              ring
        _ = ((u j * u k : ℝ) : ℂ) * E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t) := by rw [hE]
    simp_rw [hterm]
    have hcont : ∀ j k : ℕ, IntervalIntegrable
        (fun t : ℝ => ((u j * u k : ℝ) : ℂ) * E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t))
        MeasureTheory.volume 0 1 := by
      intro j k
      have hc : Continuous (fun t : ℝ => ((u j * u k : ℝ) : ℂ) * E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t)) := by
        unfold E
        fun_prop
      exact hc.intervalIntegrable 0 1
    rw [intervalIntegral.integral_finsetSum
      (f := fun j t => ∑ k ∈ Finset.range (n + 1),
        ((u j * u k : ℝ) : ℂ) * E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t))
      fun j _ => Continuous.intervalIntegrable (by unfold E; fun_prop) 0 1]
    have hsum : ∀ j ∈ Finset.range (n + 1),
        (∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.range (n + 1),
          ((u j * u k : ℝ) : ℂ) * E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t)) =
          ((u j ^ 2 : ℝ) : ℂ) := by
      intro j hj
      rw [intervalIntegral.integral_finsetSum
        (f := fun k t => ((u j * u k : ℝ) : ℂ) * E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t))
        fun k _ => hcont j k]
      have hdiag : ∀ k ∈ Finset.range (n + 1),
          (∫ t in (0 : ℝ)..1, ((u j * u k : ℝ) : ℂ) * E ((((j : ℤ) - (k : ℤ) : ℤ) : ℝ) * t)) =
            if k = j then ((u j ^ 2 : ℝ) : ℂ) else 0 := by
        intro k _
        rw [intervalIntegral.integral_const_mul, integral_E_int]
        by_cases hkj : k = j
        · subst hkj
          simp [sq]
        · have hne : (j : ℤ) - (k : ℤ) ≠ 0 := by omega
          simp [hkj, hne]
      rw [Finset.sum_congr rfl hdiag, Finset.sum_ite_eq']
      simp [hj]
    rw [Finset.sum_congr rfl hsum]
    push_cast
    rfl
  rw [intervalIntegral.integral_ofReal] at hint_c
  exact Complex.ofReal_injective hint_c

private lemma integral_mul_S_le (n : ℕ) (u v : ℕ → ℝ) :
    ∫ t in (0 : ℝ)..1, ‖S n u t‖ * ‖S n v t‖ ≤
      Real.sqrt (∑ k ∈ Finset.range (n + 1), (u k) ^ 2) *
        Real.sqrt (∑ k ∈ Finset.range (n + 1), (v k) ^ 2) := by
  let U2 : ℝ := ∑ k ∈ Finset.range (n + 1), (u k) ^ 2
  let V2 : ℝ := ∑ k ∈ Finset.range (n + 1), (v k) ^ 2
  have hU2 : 0 ≤ U2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hV2 : 0 ≤ V2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hU0 : U2 = 0
  · have hzero : ∀ k ∈ Finset.range (n + 1), u k = 0 := by
      intro k hk
      have hsq : (u k) ^ 2 ≤ U2 := Finset.single_le_sum (fun i _ => sq_nonneg (u i)) hk
      exact sq_eq_zero_iff.mp (le_antisymm (hsq.trans hU0.le) (sq_nonneg _))
    have hS0 : ∀ t : ℝ, S n u t = 0 := fun t => Finset.sum_eq_zero fun k hk => by simp [hzero k hk]
    simp [U2, hU0, hS0]
  · by_cases hV0 : V2 = 0
    · have hzero : ∀ k ∈ Finset.range (n + 1), v k = 0 := by
        intro k hk
        have hsq : (v k) ^ 2 ≤ V2 := Finset.single_le_sum (fun i _ => sq_nonneg (v i)) hk
        exact sq_eq_zero_iff.mp (le_antisymm (hsq.trans hV0.le) (sq_nonneg _))
      have hS0 : ∀ t : ℝ, S n v t = 0 := fun t => Finset.sum_eq_zero fun k hk => by simp [hzero k hk]
      simp [V2, hV0, hS0]
    · have hUp : 0 < U2 := lt_of_le_of_ne hU2 (Ne.symm hU0)
      have hVp : 0 < V2 := lt_of_le_of_ne hV2 (Ne.symm hV0)
      let a : ℝ := Real.sqrt (Real.sqrt V2 / Real.sqrt U2)
      have ha : 0 < a := by positivity
      have hpt : ∀ t : ℝ,
          2 * (‖S n u t‖ * ‖S n v t‖) ≤ a ^ 2 * ‖S n u t‖ ^ 2 + (a⁻¹) ^ 2 * ‖S n v t‖ ^ 2 := by
        intro t
        have hsq := two_mul_le_add_sq (a * ‖S n u t‖) (a⁻¹ * ‖S n v t‖)
        have hl : 2 * (a * ‖S n u t‖) * (a⁻¹ * ‖S n v t‖) = 2 * (‖S n u t‖ * ‖S n v t‖) := by
          field_simp [ha.ne']
        have hr : (a * ‖S n u t‖) ^ 2 + (a⁻¹ * ‖S n v t‖) ^ 2 =
            a ^ 2 * ‖S n u t‖ ^ 2 + (a⁻¹) ^ 2 * ‖S n v t‖ ^ 2 := by ring
        linarith
      have hc1 : IntervalIntegrable (fun t : ℝ => 2 * (‖S n u t‖ * ‖S n v t‖))
          MeasureTheory.volume 0 1 :=
        Continuous.intervalIntegrable (by unfold S E; fun_prop) 0 1
      have hcu : IntervalIntegrable (fun t : ℝ => ‖S n u t‖ ^ 2) MeasureTheory.volume 0 1 :=
        Continuous.intervalIntegrable (by unfold S E; fun_prop) 0 1
      have hcv : IntervalIntegrable (fun t : ℝ => ‖S n v t‖ ^ 2) MeasureTheory.volume 0 1 :=
        Continuous.intervalIntegrable (by unfold S E; fun_prop) 0 1
      have hint := intervalIntegral.integral_mono_on zero_le_one hc1
        ((hcu.const_mul (a ^ 2)).add (hcv.const_mul ((a⁻¹) ^ 2))) fun t _ => hpt t
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (hcu.const_mul _) (hcv.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_normSq_S, integral_normSq_S] at hint
      have hasq : a ^ 2 = Real.sqrt V2 / Real.sqrt U2 := Real.sq_sqrt (by positivity)
      have hainv : (a⁻¹) ^ 2 = Real.sqrt U2 / Real.sqrt V2 := by
        rw [inv_pow, hasq, inv_div]
      change 2 * ∫ t in (0 : ℝ)..1, ‖S n u t‖ * ‖S n v t‖ ≤ a ^ 2 * U2 + (a⁻¹) ^ 2 * V2 at hint
      rw [hasq, hainv] at hint
      have hcalc : (Real.sqrt V2 / Real.sqrt U2) * U2 + (Real.sqrt U2 / Real.sqrt V2) * V2 =
          2 * (Real.sqrt U2 * Real.sqrt V2) := by
        have hsU : Real.sqrt U2 * Real.sqrt U2 = U2 := Real.mul_self_sqrt hU2
        have hsV : Real.sqrt V2 * Real.sqrt V2 = V2 := Real.mul_self_sqrt hV2
        have hsU0 : Real.sqrt U2 ≠ 0 := (Real.sqrt_pos.mpr hUp).ne'
        have hsV0 : Real.sqrt V2 ≠ 0 := (Real.sqrt_pos.mpr hVp).ne'
        field_simp [hsU0, hsV0]
        nlinarith [hsU, hsV]
      linarith

private lemma integral_f_eq_sum (n : ℕ) :
    ∫ t in (0 : ℝ)..1, f n t =
      ((∑ p ∈ Finset.range (n + 1), w p * w (n - p) : ℝ) : ℂ) := by
  have hterm : ∀ t : ℝ, f n t =
      ∑ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        ((w j * w k : ℝ) : ℂ) * E ((((j : ℤ) + (k : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) := by
    intro t
    unfold f S
    rw [sq, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hE : E ((j : ℝ) * t) * E ((k : ℝ) * t) * E (-(n : ℝ) * t) =
        E ((((j : ℤ) + (k : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) := by
      rw [← E_add, ← E_add]
      congr 1
      push_cast
      ring
    calc
      (w j : ℂ) * E ((j : ℝ) * t) * ((w k : ℂ) * E ((k : ℝ) * t)) * E (-(n : ℝ) * t)
          = ((w j * w k : ℝ) : ℂ) * (E ((j : ℝ) * t) * E ((k : ℝ) * t) * E (-(n : ℝ) * t)) := by
            push_cast
            ring
      _ = ((w j * w k : ℝ) : ℂ) * E ((((j : ℤ) + (k : ℤ) - (n : ℤ) : ℤ) : ℝ) * t) := by rw [hE]
  simp_rw [hterm]
  have hcont : ∀ j k : ℕ, IntervalIntegrable
      (fun t : ℝ => ((w j * w k : ℝ) : ℂ) * E ((((j : ℤ) + (k : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))
      MeasureTheory.volume 0 1 := fun j k =>
    Continuous.intervalIntegrable (by unfold E; fun_prop) 0 1
  rw [intervalIntegral.integral_finsetSum
    (f := fun j t => ∑ k ∈ Finset.range (n + 1),
      ((w j * w k : ℝ) : ℂ) * E ((((j : ℤ) + (k : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))
    fun j _ => Continuous.intervalIntegrable (by unfold E; fun_prop) 0 1]
  have hsum : ∀ j ∈ Finset.range (n + 1),
      (∫ t in (0 : ℝ)..1, ∑ k ∈ Finset.range (n + 1),
        ((w j * w k : ℝ) : ℂ) * E ((((j : ℤ) + (k : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)) =
        ((w j * w (n - j) : ℝ) : ℂ) := by
    intro j hj
    have hjle : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [intervalIntegral.integral_finsetSum
      (f := fun k t => ((w j * w k : ℝ) : ℂ) * E ((((j : ℤ) + (k : ℤ) - (n : ℤ) : ℤ) : ℝ) * t))
      fun k _ => hcont j k]
    have hdiag : ∀ k ∈ Finset.range (n + 1),
        (∫ t in (0 : ℝ)..1, ((w j * w k : ℝ) : ℂ) * E ((((j : ℤ) + (k : ℤ) - (n : ℤ) : ℤ) : ℝ) * t)) =
          if k = n - j then ((w j * w (n - j) : ℝ) : ℂ) else 0 := by
      intro k _
      rw [intervalIntegral.integral_const_mul, integral_E_int]
      by_cases hkn : k = n - j
      · subst hkn
        have heq : (j : ℤ) + ((n - j : ℕ) : ℤ) - (n : ℤ) = 0 := by omega
        simp [heq]
      · have hne : (j : ℤ) + (k : ℤ) - (n : ℤ) ≠ 0 := by omega
        simp [hkn, hne]
    rw [Finset.sum_congr rfl hdiag, Finset.sum_ite_eq']
    have hmem : n - j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    simp [hmem]
  rw [Finset.sum_congr rfl hsum]
  push_cast
  rfl

private lemma major_add_minor (n : ℕ) :
    major n + I n w w = ((∑ p ∈ Finset.range (n + 1), w p * w (n - p) : ℝ) : ℂ) := by
  rw [← integral_f_eq_sum n]
  unfold major I
  rw [← intervalIntegral.integral_add (integrable_arcs_f n) (integrable_I n w w)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases ht : t ∈ arcs n
  · simp [ht, f]
  · simp [ht, f, sq]

private lemma I_ww_split (n : ℕ) :
    I n w w = I n (low n) (low n) + 2 * I n (low n) (high n) + I n (high n) (high n) := by
  unfold I
  have h12 : IntervalIntegrable
      (fun t => (arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (low n) u * E (-(n : ℝ) * u)) t +
        2 * (arcs n)ᶜ.indicator (fun u => S n (low n) u * S n (high n) u * E (-(n : ℝ) * u)) t)
      MeasureTheory.volume 0 1 :=
    (integrable_I n (low n) (low n)).add ((integrable_I n (low n) (high n)).const_mul 2)
  rw [← intervalIntegral.integral_const_mul (2 : ℂ),
    ← intervalIntegral.integral_add (integrable_I n (low n) (low n))
      ((integrable_I n (low n) (high n)).const_mul 2),
    ← intervalIntegral.integral_add h12 (integrable_I n (high n) (high n))]
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases ht : t ∈ (arcs n)ᶜ
  · simp only [Set.indicator_of_mem ht, S_low_add_high]
    ring
  · simp [ht]

private lemma w_nonneg (k : ℕ) : 0 ≤ w k := by
  unfold w
  split_ifs with hp
  · exact Real.log_nonneg (by exact_mod_cast hp.one_le)
  · exact le_rfl

private lemma w_le_log (n k : ℕ) (hk : k ≤ n) (hn : 1 ≤ n) :
    w k ≤ Real.log (n : ℝ) := by
  unfold w
  split_ifs with hp
  · exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hk)
  · exact Real.log_nonneg (by exact_mod_cast hn)

private lemma low_nonneg (n k : ℕ) : 0 ≤ low n k := by
  unfold low
  split_ifs
  · exact w_nonneg k
  · exact le_rfl

private lemma low_le_log (n k : ℕ) (hk : k ≤ n) (hn : 1 ≤ n) :
    low n k ≤ Real.log (n : ℝ) := by
  unfold low
  split_ifs
  · exact w_le_log n k hk hn
  · exact Real.log_nonneg (by exact_mod_cast hn)

private lemma high_nonneg (n k : ℕ) : 0 ≤ high n k := by
  unfold high low
  split_ifs
  · simp
  · simpa using w_nonneg k

private lemma high_le_log (n k : ℕ) (hk : k ≤ n) (hn : 1 ≤ n) :
    high n k ≤ Real.log (n : ℝ) := by
  unfold high low
  split_ifs
  · simp only [sub_self]
    exact Real.log_nonneg (by exact_mod_cast hn)
  · simpa using w_le_log n k hk hn

private lemma sum_low_sq_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (low n k) ^ 2 ≤
      2 * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  let M : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊
  let T := (Finset.range (n + 1)).filter (fun k => k ^ 3 ≤ n)
  have hsub : ∑ k ∈ Finset.range (n + 1), (low n k) ^ 2 = ∑ k ∈ T, (low n k) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1)) (fun k => k ^ 3 ≤ n)]
    have h0 : ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ k ^ 3 ≤ n), (low n k) ^ 2 = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [low, (Finset.mem_filter.mp hk).2]
    rw [h0, add_zero]
  rw [hsub]
  have hT_sub : T ⊆ Finset.range (M + 1) := by
    intro k hk
    have hle : k ^ 3 ≤ n := (Finset.mem_filter.mp hk).2
    have hlt : (n : ℝ) ^ (1 / 3 : ℝ) < (M : ℝ) + 1 := Nat.lt_floor_add_one _
    have hpow : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ 3 < ((M : ℝ) + 1) ^ 3 :=
      pow_lt_pow_left₀ hlt (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by decide)
    have hrpow : ((n : ℝ) ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    rw [hrpow] at hpow
    have hk3 : ((k : ℝ) ^ 3) < ((M : ℝ) + 1) ^ 3 :=
      lt_of_le_of_lt (by exact_mod_cast hle) hpow
    have hklt : (k : ℝ) < (M : ℝ) + 1 := by
      by_contra! hge
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (M : ℝ) + 1) hge 3
      linarith
    exact Finset.mem_range.mpr (by exact_mod_cast hklt)
  have hcard : (T.card : ℝ) ≤ (M : ℝ) + 1 := by
    exact_mod_cast (Finset.card_le_card hT_sub).trans (by simp)
  have hpt : ∀ k ∈ T, (low n k) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    exact pow_le_pow_left₀ (low_nonneg n k) (low_le_log n k hk_le hn) 2
  have hsum_le : ∑ k ∈ T, (low n k) ^ 2 ≤ (T.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpt
  have hM : (M : ℝ) + 1 ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) := by
    have hfl : (M : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Nat.floor_le (by positivity)
    have h1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
    linarith
  calc
    ∑ k ∈ T, (low n k) ^ 2 ≤ (T.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := hsum_le
    _ ≤ ((M : ℝ) + 1) * (Real.log (n : ℝ)) ^ 2 := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (2 * (n : ℝ) ^ (1 / 3 : ℝ)) * (Real.log (n : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hM (by positivity)
    _ = 2 * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by ring

private lemma sum_high_sq_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (high n k) ^ 2 ≤
      2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  have hpt : ∀ k ∈ Finset.range (n + 1), (high n k) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact pow_le_pow_left₀ (high_nonneg n k) (high_le_log n k hk_le hn) 2
  have h1 : ∑ k ∈ Finset.range (n + 1), (high n k) ^ 2 ≤
      ((n + 1 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpt
  have hn1 : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_right hn1 (by positivity))

private lemma norm_I_low_low_le (n : ℕ) (hn : 1 ≤ n) :
    ‖I n (low n) (low n)‖ ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  refine (norm_I_le n _ _).trans ((integral_mul_S_le n _ _).trans ?_)
  rw [← sq]
  exact (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).le.trans (sum_low_sq_le n hn)

private lemma norm_I_low_high_le (n : ℕ) (hn : 1 ≤ n) :
    ‖I n (low n) (high n)‖ ≤ 2 * (n : ℝ) ^ (2 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  have hlow := sum_low_sq_le n hn
  have hhigh := sum_high_sq_le n hn
  have hprod : (∑ k ∈ Finset.range (n + 1), (low n k) ^ 2) *
      (∑ k ∈ Finset.range (n + 1), (high n k) ^ 2) ≤
      (2 * (n : ℝ) ^ (2 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2) ^ 2 := by
    have hrpow : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) = ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 := by
      have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [← Real.rpow_natCast ((n : ℝ) ^ (2 / 3 : ℝ)) 2, ← Real.rpow_mul hpos.le]
      conv_lhs =>
        rhs
        rw [← Real.rpow_one (n : ℝ)]
      rw [← Real.rpow_add hpos]
      norm_num
    calc
      (∑ k ∈ Finset.range (n + 1), (low n k) ^ 2) *
          (∑ k ∈ Finset.range (n + 1), (high n k) ^ 2)
          ≤ (2 * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2) *
              (2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2) :=
            mul_le_mul hlow hhigh (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = 4 * ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ)) * (Real.log (n : ℝ)) ^ 4 := by ring
      _ = 4 * ((n : ℝ) ^ (2 / 3 : ℝ)) ^ 2 * (Real.log (n : ℝ)) ^ 4 := by rw [hrpow]
      _ = (2 * (n : ℝ) ^ (2 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2) ^ 2 := by ring
  refine (norm_I_le n _ _).trans ((integral_mul_S_le n _ _).trans ?_)
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact (Real.sqrt_le_sqrt hprod).trans_eq (Real.sqrt_sq (by positivity))

theorem main :
    ∀ c : ℝ, 0 < c →
      (∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → Even n → c * (n : ℝ) ≤ (major n).re) →
      (∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → Even n → -(c * (n : ℝ) / 2) ≤ (I n (high n) (high n)).re) →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
        c * (n : ℝ) / 4 ≤ Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) := by
  intro c hc ⟨N₁, hN₁⟩ ⟨N₂, hN₂⟩
  have hlim : Tendsto (fun n : ℕ => (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ (1 / 3 : ℝ)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (2 : ℕ) (show (0 : ℝ) < 1 / 3 by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast, Function.comp_def] using h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N₀, hN₀⟩ := (hlim.eventually_lt_const (show (0 : ℝ) < c / 24 by positivity)).exists_forall_of_atTop
  refine ⟨max (max N₁ N₂) (max N₀ 2), fun n hn heven => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2 : N₂ ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn0 : N₀ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hn_ge2 : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hmaj := hN₁ n hn1 heven
  have hhi := hN₂ n hn2 heven
  have hdiv := hN₀ n hn0
  have hlog : (Real.log (n : ℝ)) ^ 2 < (c / 24) * (n : ℝ) ^ (1 / 3 : ℝ) :=
    (div_lt_iff₀ (Real.rpow_pos_of_pos hpos (1 / 3 : ℝ))).mp hdiv
  have hll_err : ‖I n (low n) (low n)‖ ≤ (c / 12) * (n : ℝ) := by
    have h1 := norm_I_low_low_le n (by omega)
    have hr : (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) ≤ (n : ℝ) := by
      rw [← Real.rpow_add hpos]
      conv_rhs => rw [← Real.rpow_one (n : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n)) (by norm_num)
    calc
      ‖I n (low n) (low n)‖
          ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2 := h1
      _ ≤ 2 * (n : ℝ) ^ (1 / 3 : ℝ) * ((c / 24) * (n : ℝ) ^ (1 / 3 : ℝ)) := by gcongr
      _ = (c / 12) * ((n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
      _ ≤ (c / 12) * (n : ℝ) := by gcongr
  have hlh_err : ‖I n (low n) (high n)‖ ≤ (c / 12) * (n : ℝ) := by
    have h1 := norm_I_low_high_le n (by omega)
    have hr : (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ) = (n : ℝ) := by
      rw [← Real.rpow_add hpos]
      norm_num
    calc
      ‖I n (low n) (high n)‖
          ≤ 2 * (n : ℝ) ^ (2 / 3 : ℝ) * (Real.log (n : ℝ)) ^ 2 := h1
      _ ≤ 2 * (n : ℝ) ^ (2 / 3 : ℝ) * ((c / 24) * (n : ℝ) ^ (1 / 3 : ℝ)) := by gcongr
      _ = (c / 12) * ((n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (1 / 3 : ℝ)) := by ring
      _ = (c / 12) * (n : ℝ) := by rw [hr]
  have hre_ll : -((c / 12) * (n : ℝ)) ≤ (I n (low n) (low n)).re := by
    have hre := (Complex.abs_re_le_norm (I n (low n) (low n))).trans hll_err
    linarith [(abs_le.mp hre).1]
  have hre_lh : -((c / 12) * (n : ℝ)) ≤ (I n (low n) (high n)).re := by
    have hre := (Complex.abs_re_le_norm (I n (low n) (high n))).trans hlh_err
    linarith [(abs_le.mp hre).1]
  have htot : (major n).re + (I n (low n) (low n)).re + 2 * (I n (low n) (high n)).re +
      (I n (high n) (high n)).re = ∑ p ∈ Finset.range (n + 1), w p * w (n - p) := by
    have hid := congrArg Complex.re (major_add_minor n)
    rw [I_ww_split n] at hid
    simpa [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.re_ofNat, Complex.im_ofNat, add_assoc] using hid
  linarith

end

end FrozenRelativeMajorMargin

theorem PEqualNP.Outside.L_goldbach_frozen_relative_major_margin :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
    let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t);
    let major := fun n : ℕ => intervalIntegral (fun t => (arcs n).indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume;
    let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
    let high := fun (n k : ℕ) => w k-low n k;
    let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
    ∀ c : ℝ, 0 < c → (∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → Even n → c * (n : ℝ) ≤ (major n).re) → (∃ N₂ : ℕ, ∀ n : ℕ, N₂ ≤ n → Even n → -(c * (n : ℝ) / 2) ≤ (I n (high n) (high n)).re) → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → c * (n : ℝ) / 4 ≤ Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) := by
  exact FrozenRelativeMajorMargin.main
