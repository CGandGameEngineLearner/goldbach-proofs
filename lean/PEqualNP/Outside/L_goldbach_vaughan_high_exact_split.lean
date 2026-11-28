import Mathlib

/-!
# Vaughan identity on the high minor-arc segment (B05)

This file formalizes `L-goldbach-vaughan-high-exact-split` for the `minor-truncation`
route feeding `L-goldbach-bulk-signed-floor`.

With `U n = ⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊`, any `m` in the high segment `n < m ^ 3`
satisfies `U n < m`, so the truncated von Mangoldt term `Λ_{≤ U}(m)` vanishes and
Vaughan's convolution identity decomposes `highLambda n m` into `u n m + v n m`,
splitting `I n (highLambda n) (highLambda n)` into `I n (u n) (u n) + 2 * I n (u n) (v n) + I n (v n) (v n)`.
-/

namespace VaughanHighExactSplit

open Finset MeasureTheory Real Complex ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

def S (n : ℕ) (f : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (f k : ℂ) * E ((k : ℝ) * t))

def Q (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

def arcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (Q n : ℝ) / ((q : ℝ) * (n : ℝ))}

def I (n : ℕ) (a b : ℕ → ℝ) : ℂ :=
  intervalIntegral
    (fun t => (arcs n)ᶜ.indicator (fun x => S n a x * S n b x * E (-(n : ℝ) * x)) t)
    (0 : ℝ) 1 MeasureTheory.volume

def muR (d : ℕ) : ℝ := ((ArithmeticFunction.moebius d : ℤ) : ℝ)

def U (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊

def u (n m : ℕ) : ℝ :=
  if m ^ 3 ≤ n then 0
  else
    (∑ d ∈ (Nat.divisors m).filter (fun d => d ≤ U n), muR d * Real.log ((m / d : ℕ) : ℝ)) -
    (∑ d ∈ (Nat.divisors m).filter (fun d => d ≤ U n),
      muR d * ∑ l ∈ (Nat.divisors (m / d)).filter (fun l => l ≤ U n),
        ArithmeticFunction.vonMangoldt l)

def v (n m : ℕ) : ℝ :=
  if m ^ 3 ≤ n then 0
  else
    ∑ a ∈ (Nat.divisors m).filter (fun a => U n < m / a),
      (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), muR d) *
        ArithmeticFunction.vonMangoldt (m / a)

def highLambda (n k : ℕ) : ℝ :=
  if k ^ 3 ≤ n then 0 else ArithmeticFunction.vonMangoldt k

private def truncLe (f : ArithmeticFunction ℝ) (N : ℕ) : ArithmeticFunction ℝ where
  toFun k := if k ≤ N then f k else 0
  map_zero' := by simp

private def truncGt (f : ArithmeticFunction ℝ) (N : ℕ) : ArithmeticFunction ℝ where
  toFun k := if N < k then f k else 0
  map_zero' := by simp

private lemma truncLe_apply (f : ArithmeticFunction ℝ) (N k : ℕ) :
    truncLe f N k = if k ≤ N then f k else 0 := rfl

private lemma truncGt_apply (f : ArithmeticFunction ℝ) (N k : ℕ) :
    truncGt f N k = if N < k then f k else 0 := rfl

private lemma truncLe_add_truncGt (f : ArithmeticFunction ℝ) (N : ℕ) :
    truncLe f N + truncGt f N = f := by
  ext k
  rw [add_apply, truncLe_apply, truncGt_apply]
  by_cases h : k ≤ N
  · simp [h, show ¬ N < k by omega]
  · simp [h, show N < k by omega]

private lemma vaughan_conv (N : ℕ) :
    ArithmeticFunction.vonMangoldt =
      truncLe ArithmeticFunction.vonMangoldt N +
        truncLe (μ : ArithmeticFunction ℝ) N * ArithmeticFunction.log -
        truncLe (μ : ArithmeticFunction ℝ) N *
          (truncLe ArithmeticFunction.vonMangoldt N * (ζ : ArithmeticFunction ℝ)) +
        (truncGt (μ : ArithmeticFunction ℝ) N * (ζ : ArithmeticFunction ℝ)) *
          truncGt ArithmeticFunction.vonMangoldt N := by
  have hmu : truncGt (μ : ArithmeticFunction ℝ) N =
      (μ : ArithmeticFunction ℝ) - truncLe (μ : ArithmeticFunction ℝ) N :=
    eq_sub_of_add_eq' (truncLe_add_truncGt (μ : ArithmeticFunction ℝ) N)
  have hlam : truncGt ArithmeticFunction.vonMangoldt N =
      ArithmeticFunction.vonMangoldt - truncLe ArithmeticFunction.vonMangoldt N :=
    eq_sub_of_add_eq' (truncLe_add_truncGt ArithmeticFunction.vonMangoldt N)
  have hmz : (μ : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ) = 1 :=
    ArithmeticFunction.coe_moebius_mul_coe_zeta
  have hzl : (ζ : ArithmeticFunction ℝ) * ArithmeticFunction.vonMangoldt = ArithmeticFunction.log :=
    ArithmeticFunction.zeta_mul_vonMangoldt
  rw [hmu, hlam, sub_mul, hmz, sub_mul, one_mul, mul_assoc (truncLe (μ : ArithmeticFunction ℝ) N),
    mul_sub, hzl, mul_comm (ζ : ArithmeticFunction ℝ) (truncLe ArithmeticFunction.vonMangoldt N)]
  ring

private lemma truncLe_mu_mul_log_apply (N m : ℕ) :
    (truncLe (μ : ArithmeticFunction ℝ) N * ArithmeticFunction.log) m =
      ∑ d ∈ (Nat.divisors m).filter (fun d => d ≤ N),
        muR d * Real.log ((m / d : ℕ) : ℝ) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d k => truncLe (μ : ArithmeticFunction ℝ) N d *
      ArithmeticFunction.log k),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [truncLe_apply, ArithmeticFunction.log_apply]
  by_cases hd : d ≤ N
  · simp [hd, muR]
  · simp [hd]

private lemma truncLe_lam_mul_zeta_apply (N k : ℕ) :
    (truncLe ArithmeticFunction.vonMangoldt N * (ζ : ArithmeticFunction ℝ)) k =
      ∑ l ∈ (Nat.divisors k).filter (fun l => l ≤ N), ArithmeticFunction.vonMangoldt l := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun l r =>
      truncLe ArithmeticFunction.vonMangoldt N l * (ζ : ArithmeticFunction ℝ) r),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [truncLe_apply]
  have hkd : k / l ≠ 0 := by
    obtain ⟨hlm, hk0⟩ := Nat.mem_divisors.mp hl
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hlm)
      (Nat.pos_of_mem_divisors hl)).ne'
  by_cases hlN : l ≤ N
  · simp [hlN, hkd]
  · simp [hlN]

private lemma truncLe_mu_mul_lam_zeta_apply (N m : ℕ) :
    (truncLe (μ : ArithmeticFunction ℝ) N *
      (truncLe ArithmeticFunction.vonMangoldt N * (ζ : ArithmeticFunction ℝ))) m =
      ∑ d ∈ (Nat.divisors m).filter (fun d => d ≤ N),
        muR d * ∑ l ∈ (Nat.divisors (m / d)).filter (fun l => l ≤ N),
          ArithmeticFunction.vonMangoldt l := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d k => truncLe (μ : ArithmeticFunction ℝ) N d *
      (truncLe ArithmeticFunction.vonMangoldt N * (ζ : ArithmeticFunction ℝ)) k),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [truncLe_apply, truncLe_lam_mul_zeta_apply]
  by_cases hd : d ≤ N
  · simp [hd, muR]
  · simp [hd]

private lemma truncGt_mu_mul_zeta_apply (N a : ℕ) :
    (truncGt (μ : ArithmeticFunction ℝ) N * (ζ : ArithmeticFunction ℝ)) a =
      ∑ d ∈ (Nat.divisors a).filter (fun d => N < d), muR d := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d r => truncGt (μ : ArithmeticFunction ℝ) N d *
      (ζ : ArithmeticFunction ℝ) r),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [truncGt_apply]
  have had : a / d ≠ 0 := by
    obtain ⟨hda, ha0⟩ := Nat.mem_divisors.mp hd
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hda)
      (Nat.pos_of_mem_divisors hd)).ne'
  by_cases hdN : N < d
  · simp [hdN, had, muR]
  · simp [hdN]

private lemma truncGt_typeII_apply (N m : ℕ) :
    ((truncGt (μ : ArithmeticFunction ℝ) N * (ζ : ArithmeticFunction ℝ)) *
      truncGt ArithmeticFunction.vonMangoldt N) m =
      ∑ a ∈ (Nat.divisors m).filter (fun a => N < m / a),
        (∑ d ∈ (Nat.divisors a).filter (fun d => N < d), muR d) *
          ArithmeticFunction.vonMangoldt (m / a) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b =>
      (truncGt (μ : ArithmeticFunction ℝ) N * (ζ : ArithmeticFunction ℝ)) a *
        truncGt ArithmeticFunction.vonMangoldt N b),
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [truncGt_mu_mul_zeta_apply, truncGt_apply]
  by_cases hma : N < m / a
  · simp [hma]
  · simp [hma]

private lemma U_lt_of_cube_gt (n m : ℕ) (hm : ¬ m ^ 3 ≤ n) : U n < m := by
  by_cases hn0 : n = 0
  · subst hn0
    have hU0 : U 0 = 0 := by simp [U]
    rw [hU0]
    by_contra! hm0
    have : m = 0 := by omega
    subst this
    exact hm (by decide)
  · have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have hU_le : (U n : ℝ) ≤ (n : ℝ) ^ (1 / 6 : ℝ) := Nat.floor_le (by positivity)
    have hU3 : (U n : ℝ) ^ 3 ≤ ((n : ℝ) ^ (1 / 6 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hU_le 3
    have hrpow : ((n : ℝ) ^ (1 / 6 : ℝ)) ^ (3 : ℕ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      norm_num
    have hhalf : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (n : ℝ) := by
      conv_rhs => rw [← Real.rpow_one (n : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by norm_num)
    have hUn : (U n) ^ 3 ≤ n := by
      exact_mod_cast hU3.trans (hrpow.le.trans hhalf)
    by_contra! hmU
    have hm3 : m ^ 3 ≤ (U n) ^ 3 := Nat.pow_le_pow_left hmU 3
    exact hm (hm3.trans hUn)

private lemma highLambda_eq_u_add_v (n m : ℕ) :
    highLambda n m = u n m + v n m := by
  unfold highLambda u v
  by_cases hm : m ^ 3 ≤ n
  · simp [hm]
  · simp only [hm, ↓reduceIte]
    have hUm : U n < m := U_lt_of_cube_gt n m hm
    have hvan : truncLe ArithmeticFunction.vonMangoldt (U n) m = 0 := by
      simp [truncLe_apply, show ¬ m ≤ U n by omega]
    have hid := congrArg (fun f : ArithmeticFunction ℝ => f m) (vaughan_conv (U n))
    simp only [add_apply, sub_apply, hvan, zero_add] at hid
    rw [truncLe_mu_mul_log_apply, truncLe_mu_mul_lam_zeta_apply, truncGt_typeII_apply] at hid
    exact hid

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

private lemma integrable_I (n : ℕ) (a b : ℕ → ℝ) :
    IntervalIntegrable
      (fun t => (arcs n)ᶜ.indicator (fun x => S n a x * S n b x * E (-(n : ℝ) * x)) t)
      MeasureTheory.volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hcont : Continuous (fun x : ℝ => S n a x * S n b x * E (-(n : ℝ) * x)) := by
    unfold S E
    fun_prop
  exact (hcont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).indicator
    (measurableSet_arcs n).compl

private lemma S_highLambda_eq (n : ℕ) (t : ℝ) :
    S n (highLambda n) t = S n (u n) t + S n (v n) t := by
  unfold S
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [highLambda_eq_u_add_v]
  push_cast
  ring

private lemma I_highLambda_split (n : ℕ) :
    I n (highLambda n) (highLambda n) =
      I n (u n) (u n) + 2 * I n (u n) (v n) + I n (v n) (v n) := by
  unfold I
  have h12 : IntervalIntegrable
      (fun t => (arcs n)ᶜ.indicator (fun x => S n (u n) x * S n (u n) x * E (-(n : ℝ) * x)) t +
        2 * (arcs n)ᶜ.indicator (fun x => S n (u n) x * S n (v n) x * E (-(n : ℝ) * x)) t)
      MeasureTheory.volume 0 1 :=
    (integrable_I n (u n) (u n)).add ((integrable_I n (u n) (v n)).const_mul 2)
  rw [← intervalIntegral.integral_const_mul (2 : ℂ),
    ← intervalIntegral.integral_add (integrable_I n (u n) (u n))
      ((integrable_I n (u n) (v n)).const_mul 2),
    ← intervalIntegral.integral_add h12 (integrable_I n (v n) (v n))]
  refine intervalIntegral.integral_congr fun t _ => ?_
  by_cases ht : t ∈ (arcs n)ᶜ
  · simp only [Set.indicator_of_mem ht, S_highLambda_eq]
    ring
  · simp [ht]

theorem main :
    (∀ n m : ℕ, highLambda n m = u n m + v n m) ∧
      (∀ n : ℕ, I n (highLambda n) (highLambda n) =
        I n (u n) (u n) + 2 * I n (u n) (v n) + I n (v n) (v n)) :=
  ⟨highLambda_eq_u_add_v, I_highLambda_split⟩

end

end VaughanHighExactSplit

theorem PEqualNP.Outside.L_goldbach_vaughan_high_exact_split :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I);
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t));
    let Q := fun n : ℕ => (Nat.log 2 (n+2))^2;
    let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))};
    let I := fun (n:ℕ) (a b:ℕ→ℝ) => intervalIntegral (fun t => (arcs n)ᶜ.indicator (fun u => S n a u*S n b u*E (-(n:ℝ)*u)) t) (0:ℝ) 1 MeasureTheory.volume;
    let Λ := ArithmeticFunction.vonMangoldt;
    let μ := fun d : ℕ => ((ArithmeticFunction.moebius d : ℤ) : ℝ);
    let U := fun n : ℕ => ⌊(n : ℝ) ^ (1 / 6 : ℝ)⌋₊;
    let u := fun (n m : ℕ) => if m ^ 3 ≤ n then 0 else (∑ d ∈ (Nat.divisors m).filter (fun d => d ≤ U n), μ d * Real.log ((m / d : ℕ) : ℝ)) - (∑ d ∈ (Nat.divisors m).filter (fun d => d ≤ U n), μ d * ∑ l ∈ (Nat.divisors (m / d)).filter (fun l => l ≤ U n), Λ l);
    let v := fun (n m : ℕ) => if m ^ 3 ≤ n then 0 else ∑ a ∈ (Nat.divisors m).filter (fun a => U n < m / a), (∑ d ∈ (Nat.divisors a).filter (fun d => U n < d), μ d) * Λ (m / a);
    let highLambda := fun (n k : ℕ) => if k ^ 3 ≤ n then 0 else Λ k;
    (∀ n m : ℕ, highLambda n m = u n m + v n m) ∧ (∀ n : ℕ, I n (highLambda n) (highLambda n) = I n (u n) (u n) + 2 * I n (u n) (v n) + I n (v n) (v n)) := by
  exact VaughanHighExactSplit.main
