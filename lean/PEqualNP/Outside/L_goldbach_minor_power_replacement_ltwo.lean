import Mathlib

/-!
# Minor-arc replacement of prime weights by von Mangoldt weights on the high segment (B04)

This file formalizes `L-goldbach-minor-power-replacement-ltwo` for the `minor-truncation`
route feeding `L-goldbach-bulk-signed-floor` and `L-goldbach-arc-minor-saving`.

On `(arcs n)ᶜ ⊆ [0, 1]`, replacing `high n k = (if k^3 ≤ n then 0 else w k)` by
`highLambda n k = (if k^3 ≤ n then 0 else Λ k)` incurs an error bounded via bilinearity,
Cauchy–Schwarz / AM–GM, Parseval on `[0, 1]`, and the proper prime-power count `O(√n log n)`.
-/

namespace MinorPowerReplacement

open Finset MeasureTheory Real Complex

noncomputable section

def w (k : ℕ) : ℝ := if Nat.Prime k then Real.log (k : ℝ) else 0

def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * t))

def Q (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def arcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}

def low (n k : ℕ) : ℝ := if k ^ 3 ≤ n then w k else 0

def high (n k : ℕ) : ℝ := w k - low n k

def highLambda (n k : ℕ) : ℝ :=
  if k ^ 3 ≤ n then 0 else ArithmeticFunction.vonMangoldt k

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

private lemma S_sub (n : ℕ) (a b : ℕ → ℝ) (t : ℝ) :
    S n (fun k => a k - b k) t = S n a t - S n b t := by
  unfold S
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

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

private lemma integrable_integrand (n : ℕ) (a b : ℕ → ℝ) :
    IntervalIntegrable
      (fun t => (arcs n)ᶜ.indicator (fun u => S n a u * S n b u * E (-(n : ℝ) * u)) t)
      MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hcont : Continuous (fun u : ℝ => S n a u * S n b u * E (-(n : ℝ) * u)) := by
    unfold S E
    fun_prop
  exact (hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    (measurableSet_arcs n).compl

private lemma I_sub_self (n : ℕ) (a b : ℕ → ℝ) :
    I n a a - I n b b = I n (fun k => a k - b k) a + I n b (fun k => a k - b k) := by
  unfold I
  rw [← intervalIntegral.integral_sub (integrable_integrand n a a) (integrable_integrand n b b),
    ← intervalIntegral.integral_add (integrable_integrand n (fun k => a k - b k) a)
      (integrable_integrand n b (fun k => a k - b k))]
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases ht : t ∈ (arcs n)ᶜ
  · simp only [Set.indicator_of_mem ht, S_sub]
    ring
  · simp only [Set.indicator_of_notMem ht, sub_zero, add_zero]

private lemma norm_I_le (n : ℕ) (a b : ℕ → ℝ) :
    ‖I n a b‖ ≤ ∫ t in (0 : ℝ)..1, ‖S n a t‖ * ‖S n b t‖ := by
  unfold I
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun t _ => ?_
  · exact (integrable_integrand n a b).norm
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
      have : (u k) ^ 2 = 0 := le_antisymm (hsq.trans hU0.le) (sq_nonneg _)
      exact sq_eq_zero_iff.mp this
    have hS0 : ∀ t : ℝ, S n u t = 0 := by
      intro t
      unfold S
      exact Finset.sum_eq_zero fun k hk => by simp [hzero k hk]
    simp [U2, hU0, hS0]
  · by_cases hV0 : V2 = 0
    · have hzero : ∀ k ∈ Finset.range (n + 1), v k = 0 := by
        intro k hk
        have hsq : (v k) ^ 2 ≤ V2 := Finset.single_le_sum (fun i _ => sq_nonneg (v i)) hk
        have : (v k) ^ 2 = 0 := le_antisymm (hsq.trans hV0.le) (sq_nonneg _)
        exact sq_eq_zero_iff.mp this
      have hS0 : ∀ t : ℝ, S n v t = 0 := by
        intro t
        unfold S
        exact Finset.sum_eq_zero fun k hk => by simp [hzero k hk]
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
          MeasureTheory.volume 0 1 := by
        have hc : Continuous (fun t : ℝ => 2 * (‖S n u t‖ * ‖S n v t‖)) := by
          unfold S E
          fun_prop
        exact hc.intervalIntegrable 0 1
      have hcu : IntervalIntegrable (fun t : ℝ => ‖S n u t‖ ^ 2) MeasureTheory.volume 0 1 := by
        have hc : Continuous (fun t : ℝ => ‖S n u t‖ ^ 2) := by
          unfold S E
          fun_prop
        exact hc.intervalIntegrable 0 1
      have hcv : IntervalIntegrable (fun t : ℝ => ‖S n v t‖ ^ 2) MeasureTheory.volume 0 1 := by
        have hc : Continuous (fun t : ℝ => ‖S n v t‖ ^ 2) := by
          unfold S E
          fun_prop
        exact hc.intervalIntegrable 0 1
      have hint := intervalIntegral.integral_mono_on zero_le_one hc1
        ((hcu.const_mul (a ^ 2)).add (hcv.const_mul ((a⁻¹) ^ 2))) fun t _ => hpt t
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (hcu.const_mul _) (hcv.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        integral_normSq_S, integral_normSq_S] at hint
      have hasq : a ^ 2 = Real.sqrt V2 / Real.sqrt U2 :=
        Real.sq_sqrt (by positivity)
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

private lemma high_nonneg (n k : ℕ) : 0 ≤ high n k := by
  unfold high low w
  by_cases hle : k ^ 3 ≤ n <;> by_cases hp : Nat.Prime k <;> simp [hle, hp]
  exact Real.log_nonneg (by exact_mod_cast hp.one_le)

private lemma high_le_log (n k : ℕ) (hk : k ≤ n) (hn : 1 ≤ n) :
    high n k ≤ Real.log (n : ℝ) := by
  unfold high low w
  by_cases hle : k ^ 3 ≤ n
  · by_cases hp : Nat.Prime k <;> simp only [hle, hp, ↓reduceIte, sub_self] <;>
      exact Real.log_nonneg (by exact_mod_cast hn)
  · by_cases hp : Nat.Prime k
    · simp only [hle, hp, ↓reduceIte, sub_zero]
      exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hk)
    · simp only [hle, hp, ↓reduceIte, sub_zero]
      exact Real.log_nonneg (by exact_mod_cast hn)

private lemma highLambda_nonneg (n k : ℕ) : 0 ≤ highLambda n k := by
  unfold highLambda
  split_ifs
  · exact le_rfl
  · exact ArithmeticFunction.vonMangoldt_nonneg

private lemma highLambda_le_log (n k : ℕ) (hk : k ≤ n) (hn : 1 ≤ n) :
    highLambda n k ≤ Real.log (n : ℝ) := by
  unfold highLambda
  split_ifs with h1
  · exact Real.log_nonneg (by exact_mod_cast hn)
  · by_cases hk0 : k = 0
    · simp [hk0]
      exact Real.log_nonneg (by exact_mod_cast hn)
    · exact (ArithmeticFunction.vonMangoldt_le_log).trans
        (Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hk0) (by exact_mod_cast hk))

private lemma diff_eq_zero_of_not_proper_pow (n k : ℕ)
    (h : ¬ (IsPrimePow k ∧ ¬ Nat.Prime k)) :
    highLambda n k - high n k = 0 := by
  unfold highLambda high low w
  by_cases hle : k ^ 3 ≤ n
  · simp [hle]
  · simp only [hle, ite_false, sub_zero]
    by_cases hp : Nat.Prime k
    · simp [hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
    · have hnp : ¬ IsPrimePow k := fun hpp => h ⟨hpp, hp⟩
      have hv : ArithmeticFunction.vonMangoldt k = 0 :=
        ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnp
      simp [hp, hv]

private lemma proper_prime_pow_card (n : ℕ) (_hn : 2 ≤ n) :
    ((Finset.range (n + 1)).filter (fun k => IsPrimePow k ∧ ¬ Nat.Prime k)).card ≤
      Nat.sqrt n * Nat.log 2 n := by
  let box := (Finset.Icc 2 (Nat.sqrt n)) ×ˢ (Finset.Icc 2 (Nat.log 2 n))
  have hsub : ((Finset.range (n + 1)).filter (fun k => IsPrimePow k ∧ ¬ Nat.Prime k)) ⊆
      box.image (fun z => z.1 ^ z.2) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk_le, hpp, hnp⟩ := hk
    rw [isPrimePow_nat_iff] at hpp
    obtain ⟨p, j, hp, hj_pos, rfl⟩ := hpp
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_trichotomy j 1 with hj0 | rfl | hj1
      · omega
      · simp at hnp; exact False.elim (hnp hp)
      · exact hj1
    have hp2 : 2 ≤ p := hp.two_le
    have hkn : p ^ j ≤ n := Nat.lt_succ_iff.mp hk_le
    have hp_sqrt : p ≤ Nat.sqrt n := by
      rw [Nat.le_sqrt]
      calc p * p = p ^ 2 := (sq p).symm
        _ ≤ p ^ j := Nat.pow_le_pow_right hp.pos hj2
        _ ≤ n := hkn
    have hj_log : j ≤ Nat.log 2 n := by
      refine Nat.le_log_of_pow_le (by decide) ?_
      calc 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left hp2 j
        _ ≤ n := hkn
    exact Finset.mem_image.mpr ⟨(p, j), Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hp2, hp_sqrt⟩, Finset.mem_Icc.mpr ⟨hj2, hj_log⟩⟩, rfl⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  dsimp only [box]
  rw [Finset.card_product]
  have h1 : (Finset.Icc 2 (Nat.sqrt n)).card ≤ Nat.sqrt n := by
    rw [Nat.card_Icc]; omega
  have h2 : (Finset.Icc 2 (Nat.log 2 n)).card ≤ Nat.log 2 n := by
    rw [Nat.card_Icc]; omega
  exact Nat.mul_le_mul h1 h2

private lemma sum_diff_sq_le (n : ℕ) (hn : 3 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (highLambda n k - high n k) ^ 2 ≤
      2 * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 4 := by
  let T := (Finset.range (n + 1)).filter (fun k => IsPrimePow k ∧ ¬ Nat.Prime k)
  have hsub : ∑ k ∈ Finset.range (n + 1), (highLambda n k - high n k) ^ 2 =
      ∑ k ∈ T, (highLambda n k - high n k) ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
      (fun k => IsPrimePow k ∧ ¬ Nat.Prime k)]
    have h0 : ∑ k ∈ (Finset.range (n + 1)).filter (fun k => ¬ (IsPrimePow k ∧ ¬ Nat.Prime k)),
        (highLambda n k - high n k) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [diff_eq_zero_of_not_proper_pow n k (Finset.mem_filter.mp hk).2, sq, mul_zero]
    rw [h0, add_zero]
  rw [hsub]
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by
    have : Real.exp 1 ≤ (n : ℝ) := by
      have := Real.exp_one_lt_d9
      have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (n : ℝ) := Real.log_le_log (Real.exp_pos 1) this
  have hpt : ∀ k ∈ T, (highLambda n k - high n k) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    have h1 := highLambda_nonneg n k
    have h2 := highLambda_le_log n k hk_le (by omega)
    have h3 := high_nonneg n k
    have h4 := high_le_log n k hk_le (by omega)
    have habs : |highLambda n k - high n k| ≤ Real.log (n : ℝ) :=
      abs_sub_le_of_nonneg_of_le h1 h2 h3 h4
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hsum_le : ∑ k ∈ T, (highLambda n k - high n k) ^ 2 ≤
      (T.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpt
  have hcard : (T.card : ℝ) ≤ (Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ) := by
    exact_mod_cast proper_prime_pow_card n (by omega)
  have hsqrt : (Nat.sqrt n : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    exact_mod_cast (by simpa [sq] using Nat.sqrt_le n)
  have hnatlog : (Nat.log 2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hb : (Nat.log 2 n : ℝ) ≤ Real.logb 2 (n : ℝ) := by
      have := Real.natLog_le_logb n 2
      simpa using this
    rw [Real.logb] at hb
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hmul : (Nat.log 2 n : ℝ) * Real.log 2 ≤ Real.log (n : ℝ) :=
      (le_div_iff₀ (by linarith : 0 < Real.log 2)).mp hb
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 n)]
  have hpow34 : (Real.log (n : ℝ)) ^ 3 ≤ (Real.log (n : ℝ)) ^ 4 := by
    have hp3 : 0 ≤ (Real.log (n : ℝ)) ^ 3 := by positivity
    calc (Real.log (n : ℝ)) ^ 3 = (Real.log (n : ℝ)) ^ 3 * 1 := (mul_one _).symm
      _ ≤ (Real.log (n : ℝ)) ^ 3 * Real.log (n : ℝ) := mul_le_mul_of_nonneg_left hlog1 hp3
      _ = (Real.log (n : ℝ)) ^ 4 := by ring
  calc
    ∑ k ∈ T, (highLambda n k - high n k) ^ 2
        ≤ (T.card : ℝ) * (Real.log (n : ℝ)) ^ 2 := hsum_le
    _ ≤ ((Nat.sqrt n : ℝ) * (Nat.log 2 n : ℝ)) * (Real.log (n : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (Real.sqrt (n : ℝ) * (2 * Real.log (n : ℝ))) * (Real.log (n : ℝ)) ^ 2 := by gcongr
    _ = 2 * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 3 := by ring
    _ ≤ 2 * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 4 := by gcongr

private lemma sum_high_sq_le (n : ℕ) (hn : 3 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (high n k) ^ 2 ≤ 2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  have hpt : ∀ k ∈ Finset.range (n + 1), (high n k) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact pow_le_pow_left₀ (high_nonneg n k) (high_le_log n k hk_le (by omega)) 2
  have h1 : ∑ k ∈ Finset.range (n + 1), (high n k) ^ 2 ≤
      ((n + 1 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpt
  have hn1 : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_right hn1 (by positivity))

private lemma sum_highLambda_sq_le (n : ℕ) (hn : 3 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (highLambda n k) ^ 2 ≤ 2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
  have hpt : ∀ k ∈ Finset.range (n + 1), (highLambda n k) ^ 2 ≤ (Real.log (n : ℝ)) ^ 2 := by
    intro k hk
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact pow_le_pow_left₀ (highLambda_nonneg n k) (highLambda_le_log n k hk_le (by omega)) 2
  have h1 : ∑ k ∈ Finset.range (n + 1), (highLambda n k) ^ 2 ≤
      ((n + 1 : ℕ) : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hpt
  have hn1 : ((n + 1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) := by
    push_cast
    have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_right hn1 (by positivity))

theorem main :
    ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ n : ℕ, N ≤ n →
      ‖I n (highLambda n) (highLambda n) - I n (high n) (high n)‖ ≤
        C * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 3 := by
  refine ⟨8, 3, by norm_num, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hdiff_sqrt : Real.sqrt (∑ k ∈ Finset.range (n + 1), (highLambda n k - high n k) ^ 2) ≤
      2 * Real.sqrt (Real.sqrt (n : ℝ)) * (Real.log (n : ℝ)) ^ 2 := by
    have hsq := sum_diff_sq_le n hn
    have h4 : 2 * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 4 ≤
        (2 * Real.sqrt (Real.sqrt (n : ℝ)) * (Real.log (n : ℝ)) ^ 2) ^ 2 := by
      have hs : (Real.sqrt (Real.sqrt (n : ℝ))) ^ 2 = Real.sqrt (n : ℝ) :=
        Real.sq_sqrt (Real.sqrt_nonneg _)
      calc 2 * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 4
          ≤ 4 * Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 4 := by
            have : 0 ≤ Real.sqrt (n : ℝ) * (Real.log (n : ℝ)) ^ 4 := by positivity
            linarith
        _ = (2 * Real.sqrt (Real.sqrt (n : ℝ)) * (Real.log (n : ℝ)) ^ 2) ^ 2 := by
            rw [mul_pow, mul_pow, hs]
            ring
    exact (Real.sqrt_le_sqrt (hsq.trans h4)).trans_eq (Real.sqrt_sq (by positivity))
  have hh_sqrt : Real.sqrt (∑ k ∈ Finset.range (n + 1), (high n k) ^ 2) ≤
      2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    have hsq := sum_high_sq_le n hn
    have h4 : 2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤
        (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ^ 2 := by
      have hs : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
      calc 2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2
          ≤ 4 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
            have : 0 ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by positivity
            linarith
        _ = (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ^ 2 := by
            rw [mul_pow, mul_pow, hs]
            ring
    exact (Real.sqrt_le_sqrt (hsq.trans h4)).trans_eq (Real.sqrt_sq (by positivity))
  have hhL_sqrt : Real.sqrt (∑ k ∈ Finset.range (n + 1), (highLambda n k) ^ 2) ≤
      2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ) := by
    have hsq := sum_highLambda_sq_le n hn
    have h4 : 2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤
        (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ^ 2 := by
      have hs : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hn0
      calc 2 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2
          ≤ 4 * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
            have : 0 ≤ (n : ℝ) * (Real.log (n : ℝ)) ^ 2 := by positivity
            linarith
        _ = (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) ^ 2 := by
            rw [mul_pow, mul_pow, hs]
            ring
    exact (Real.sqrt_le_sqrt (hsq.trans h4)).trans_eq (Real.sqrt_sq (by positivity))
  have hrpow : Real.sqrt (Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ) = (n : ℝ) ^ (3 / 4 : ℝ) := by
    have hpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hn0, ← Real.rpow_add hpos]
    norm_num
  have hterm1 : ‖I n (fun k => highLambda n k - high n k) (highLambda n)‖ ≤
      4 * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 3 := by
    refine (norm_I_le n _ _).trans ((integral_mul_S_le n _ _).trans ?_)
    calc Real.sqrt (∑ k ∈ Finset.range (n + 1), (highLambda n k - high n k) ^ 2) *
          Real.sqrt (∑ k ∈ Finset.range (n + 1), (highLambda n k) ^ 2)
        ≤ (2 * Real.sqrt (Real.sqrt (n : ℝ)) * (Real.log (n : ℝ)) ^ 2) *
            (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) := by gcongr
      _ = 4 * (Real.sqrt (Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ)) * (Real.log (n : ℝ)) ^ 3 := by ring
      _ = 4 * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 3 := by rw [hrpow]
  have hterm2 : ‖I n (high n) (fun k => highLambda n k - high n k)‖ ≤
      4 * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 3 := by
    refine (norm_I_le n _ _).trans ((integral_mul_S_le n _ _).trans ?_)
    calc Real.sqrt (∑ k ∈ Finset.range (n + 1), (high n k) ^ 2) *
          Real.sqrt (∑ k ∈ Finset.range (n + 1), (highLambda n k - high n k) ^ 2)
        ≤ (2 * Real.sqrt (n : ℝ) * Real.log (n : ℝ)) *
            (2 * Real.sqrt (Real.sqrt (n : ℝ)) * (Real.log (n : ℝ)) ^ 2) := by gcongr
      _ = 4 * (Real.sqrt (Real.sqrt (n : ℝ)) * Real.sqrt (n : ℝ)) * (Real.log (n : ℝ)) ^ 3 := by ring
      _ = 4 * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 3 := by rw [hrpow]
  rw [I_sub_self]
  calc ‖I n (fun k => highLambda n k - high n k) (highLambda n) +
        I n (high n) (fun k => highLambda n k - high n k)‖
      ≤ ‖I n (fun k => highLambda n k - high n k) (highLambda n)‖ +
          ‖I n (high n) (fun k => highLambda n k - high n k)‖ := norm_add_le _ _
    _ ≤ 4 * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 3 +
          4 * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 3 := add_le_add hterm1 hterm2
    _ = 8 * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 3 := by ring

end

end MinorPowerReplacement

theorem PEqualNP.Outside.L_goldbach_minor_power_replacement_ltwo :
    let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0;
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
    let low := fun (n k : ℕ) => if k^3≤n then w k else 0;
    let high := fun (n k : ℕ) => w k-low n k;
    let highLambda := fun (n k : ℕ) => if k^3≤n then 0 else ArithmeticFunction.vonMangoldt k;
    let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
    ∃ (C : ℝ) (N : ℕ), 0 < C ∧ ∀ n : ℕ, N ≤ n → ‖I n (highLambda n) (highLambda n) - I n (high n) (high n)‖ ≤ C * (n : ℝ) ^ (3 / 4 : ℝ) * (Real.log (n : ℝ)) ^ 3 := by
  exact MinorPowerReplacement.main
