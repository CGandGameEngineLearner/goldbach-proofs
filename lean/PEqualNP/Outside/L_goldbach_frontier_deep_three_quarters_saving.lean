/-
Gap L-goldbach-frontier-deep-three-quarters-saving.

Attempted statement (verbatim from research/gaps.json):

  let w := fun k : Nat => if Nat.Prime k then Real.log (k : Real) else 0;
  let E := fun x : Real => Complex.exp (((2 * Real.pi * x : Real) : Complex) * Complex.I);
  let S := fun (n : Nat) (u : Nat -> Real) (t : Real) =>
    Finset.sum (Finset.range (n + 1)) (fun k => (u k : Complex) * E ((k : Real) * t));
  let Q := fun n : Nat => (Nat.log 2 (n + 2)) ^ 2;
  let Q1 := fun n : Nat => Nat.floor ((n : Real) ^ (1 / 3 : Real));
  let H := fun n : Nat => 256 * Q1 n * Q n;
  let wideArcs := fun n : Nat => {t : Real |
    exists q a : Nat, 1 <= q /\ q <= Q1 n /\ a <= q /\ Nat.Coprime a q /\
      abs (t - (a : Real) / (q : Real)) <= (H n : Real) / ((q : Real) * (n : Real))};
  forall eta : Real, 0 < eta -> exists N : Nat, forall n : Nat, N <= n ->
    forall t : Real, t in Set.Icc 0 1 -> t not in wideArcs n ->
      norm (S n w t) <= (n : Real) ^ (3 / 4 + eta)

VERDICT: this statement is *not* proved here.  It is a deep minor-arc estimate for the
exponential sum over primes (Vinogradov / Vaughan territory); the gap catalogue itself lists
it as an open target.  The material below is what is actually established.

Established in this file:

* `norm_S_w_le_theta`, `norm_S_w_le_log4` : the trivial bound, exponent 1, for all n, t;
* `S_w_zero`, `norm_S_w_zero` : at `t = 0` the sum is exactly `theta n` (so exponent 1 is
  attained); `zero_mem_wideArcs` : `t = 0` is inside the wide arcs, and
  `claim_fails_without_arcs` : removing the arc hypothesis makes the claim false at `t = 0`;
* `mem_wideArcs_of_two_mul_H_ge`, `claim_on_vacuous_range` : if `n <= 2 * H n` then the two
  arcs of denominator one already cover `[0,1]`, so the gap statement is vacuous there
  (covers `n <= 2 * 10^8`);
* `mem_wideArcs_of_dirichlet`, `wideArcs_cover_of_dirichlet`, `claim_on_dirichlet_range` :
  using Dirichlet's approximation theorem (`Real.exists_nat_abs_mul_sub_round_le`) plus
  reduction to lowest terms, `[0,1]` is covered by the wide arcs as soon as
  `n <= H n * (Q1 n + 1)`, which covers all `n <= 7 * 10^17`.  Beyond that range the
  hypothesis of the gap statement is non-empty, so no choice of `N` disposes of the range
  `n >= 10^18` by vacuity: that is where the actual content of the statement lives.
* `norm_S_one_le` : for the constant weight `1` (the circle model) the complement of the
  wide arcs satisfies `norm (S n 1 t) <= n / (2 * H n)`, i.e. about `n^(2/3) / log^2 n`;
* `norm_S_one_le_rpow` : consequently the constant-weight analogue of the gap statement is
  TRUE with exponent `3/4 + eta` for every `eta > 0` (already for `n >= 8`).

The step from the constant weight `1` to the prime weight `w` is the whole difficulty; see
the accompanying report for the analysis and for the numerical calibration.
-/
import Mathlib

namespace PEqualNP.Outside
namespace GoldbachFrontier34

open Finset

/-- The prime-supported logarithmic weight. -/
noncomputable def w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0

/-- The additive character `x |-> exp (2 pi i x)`. -/
noncomputable def E : ℝ → ℂ := fun x => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The exponential sum over `k <= n` with weight `u`. -/
noncomputable def S (n : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℂ :=
  Finset.sum (Finset.range (n + 1)) (fun k => (u k : ℂ) * E ((k : ℝ) * t))

/-- `(log_2 (n+2))^2`. -/
noncomputable def Q (n : ℕ) : ℕ := (Nat.log 2 (n + 2)) ^ 2

/-- `floor (n^(1/3))`. -/
noncomputable def Q1 (n : ℕ) : ℕ := ⌊(n : ℝ) ^ (1 / 3 : ℝ)⌋₊

/-- The arc height `256 * Q1 n * Q n`. -/
noncomputable def H (n : ℕ) : ℕ := 256 * Q1 n * Q n

/-- The wide arcs around the rationals `a/q` with `q <= Q1 n`. -/
noncomputable def wideArcs (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q1 n ∧ a ≤ q ∧ Nat.Coprime a q ∧
    |t - (a : ℝ) / (q : ℝ)| ≤ (H n : ℝ) / ((q : ℝ) * (n : ℝ))}

theorem norm_E (x : ℝ) : ‖E x‖ = 1 := by
  rw [E, Complex.norm_exp_ofReal_mul_I]

theorem w_nonneg (k : ℕ) : 0 ≤ w k := by
  unfold w
  split_ifs with h
  · exact Real.log_natCast_nonneg k
  · exact le_refl 0

theorem sum_w_range (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), w k) = Chebyshev.theta (n : ℝ) := by
  rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range]
  unfold w
  rw [← Finset.sum_filter]

/-- Trivial bound: the exponential sum is bounded by the total mass `theta n`. -/
theorem norm_S_w_le_theta (n : ℕ) (t : ℝ) :
    ‖S n w t‖ ≤ Chebyshev.theta (n : ℝ) := by
  have hterm : ∀ k ∈ Finset.range (n + 1), ‖(w k : ℂ) * E ((k : ℝ) * t)‖ = w k := by
    intro k _
    rw [norm_mul, norm_E, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (w_nonneg k)]
  calc ‖S n w t‖ ≤ ∑ k ∈ Finset.range (n + 1), ‖(w k : ℂ) * E ((k : ℝ) * t)‖ :=
        norm_sum_le _ _
    _ = ∑ k ∈ Finset.range (n + 1), w k := Finset.sum_congr rfl hterm
    _ = Chebyshev.theta (n : ℝ) := sum_w_range n

/-- Trivial bound with exponent `1` in explicit form. -/
theorem norm_S_w_le_log4 (n : ℕ) (t : ℝ) :
    ‖S n w t‖ ≤ Real.log 4 * n := by
  refine (norm_S_w_le_theta n t).trans ?_
  exact Chebyshev.theta_le_log4_mul_x (x := (n : ℝ)) (by positivity)

/-- At `t = 0` the sum is exactly `theta n`; it is real and positive. -/
theorem S_w_zero (n : ℕ) : S n w 0 = ((Chebyshev.theta (n : ℝ) : ℝ) : ℂ) := by
  unfold S
  have hE : ∀ k : ℕ, E ((k : ℝ) * 0) = 1 := by
    intro k
    rw [mul_zero, E, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  simp only [hE, mul_one]
  rw [← Complex.ofReal_sum]
  rw [sum_w_range]

theorem norm_S_w_zero (n : ℕ) : ‖S n w 0‖ = Chebyshev.theta (n : ℝ) := by
  rw [S_w_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Chebyshev.theta_nonneg n)]

/-- The character is multiplicative: `E (a + b) = E a * E b`. -/
theorem E_add (a b : ℝ) : E (a + b) = E a * E b := by
  unfold E
  have hcast : ((2 * Real.pi * (a + b) : ℝ) : ℂ) =
      ((2 * Real.pi * a : ℝ) : ℂ) + ((2 * Real.pi * b : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast, add_mul, Complex.exp_add]

theorem E_pow (k : ℕ) (t : ℝ) : E ((k : ℝ) * t) = E t ^ k := by
  induction k with
  | zero => simp [E]
  | succ m ih =>
      rw [Nat.cast_succ, add_mul, one_mul, E_add, ih, pow_succ]

/-- The constant-weight sum is the geometric sum in `E t`. -/
theorem S_one_eq_geom (n : ℕ) (t : ℝ) :
    S n (fun _ => (1 : ℝ)) t = ∑ k ∈ Finset.range (n + 1), E t ^ k := by
  unfold S
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [E_pow]
  norm_num

/-- Elementary lower bound for `|sin (pi t)|` in terms of the distance to the nearest
integer, for `t` in `[0,1]`. -/
theorem abs_sin_pi_ge_min (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    4 * min t (1 - t) ≤ 2 * |Real.sin (Real.pi * t)| := by
  have aux : ∀ s : ℝ, 0 ≤ s → s ≤ 1 / 2 → 4 * s ≤ 2 * |Real.sin (Real.pi * s)| := by
    intro s hs0 hs
    have hb : |Real.pi * s| ≤ Real.pi / 2 := by
      rw [abs_of_nonneg (by positivity)]
      nlinarith [Real.pi_pos]
    have h1 := Real.mul_abs_le_abs_sin hb
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi * s)] at h1
    have h3 : 2 / Real.pi * (Real.pi * s) = 2 * s := by
      field_simp
    have h4 : 2 * s ≤ |Real.sin (Real.pi * s)| := h3 ▸ h1
    linarith
  rcases le_total t (1 / 2) with h | h
  · rw [min_eq_left (by linarith)]
    exact aux t ht0 h
  · rw [min_eq_right (by linarith)]
    have hsin : Real.sin (Real.pi * t) = Real.sin (Real.pi * (1 - t)) := by
      have : Real.pi * t = Real.pi - Real.pi * (1 - t) := by ring
      rw [this, Real.sin_pi_sub]
    rw [hsin]
    exact aux (1 - t) (by linarith) (by linarith)

/-- The wide-arc height is positive as soon as `n >= 1`. -/
theorem H_pos {n : ℕ} (hn : 1 ≤ n) : 0 < H n := by
  have hQ1 : 0 < Q1 n := by
    unfold Q1
    rw [Nat.floor_pos]
    exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hQ : 0 < Q n := by
    unfold Q
    have : 0 < Nat.log 2 (n + 2) := by
      apply Nat.log_pos
      · norm_num
      · omega
    positivity
  unfold H
  positivity

/-- Every `t` in `[0,1]` lies in the wide arcs as soon as `n <= 2 * H n`. -/
theorem mem_wideArcs_of_two_mul_H_ge (n : ℕ) (hn : 1 ≤ n) (hH : n ≤ 2 * H n)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : t ∈ wideArcs n := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hHpos : (0 : ℝ) < (H n : ℝ) := by exact_mod_cast H_pos hn
  have hQ1 : 1 ≤ Q1 n := by
    unfold Q1
    rw [Nat.one_le_floor_iff]
    exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have hδ : (1 : ℝ) / 2 ≤ (H n : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hnpos]
    have : (n : ℝ) ≤ 2 * (H n : ℝ) := by exact_mod_cast hH
    linarith
  obtain ⟨ht0, ht1⟩ := ht
  rcases le_total t (1 / 2) with h | h
  · refine ⟨1, 0, le_rfl, hQ1, by norm_num, by simp, ?_⟩
    have h0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
    have h1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
    have hval : |t - ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)| = t := by
      rw [h0, h1, zero_div, sub_zero, abs_of_nonneg ht0]
    rw [hval]
    calc t ≤ 1 / 2 := h
      _ ≤ (H n : ℝ) / (n : ℝ) := hδ
      _ = (H n : ℝ) / (((1 : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by norm_num
  · refine ⟨1, 1, le_rfl, hQ1, by norm_num, by simp, ?_⟩
    have h1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
    have hval : |t - ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)| = 1 - t := by
      rw [h1, div_one, abs_of_nonpos (by linarith)]
      ring
    rw [hval]
    calc 1 - t ≤ 1 / 2 := by linarith
      _ ≤ (H n : ℝ) / (n : ℝ) := hδ
      _ = (H n : ℝ) / (((1 : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by norm_num

/-- On the range `n <= 2 * H n` the hypothesis of the gap statement is empty, so the
conclusion holds trivially. -/
theorem claim_on_vacuous_range (η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hH : n ≤ 2 * H n) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ wideArcs n → ‖S n w t‖ ≤ (n : ℝ) ^ (3 / 4 + η) :=
  fun t ht hnot => absurd (mem_wideArcs_of_two_mul_H_ge (t := t) n hn hH ht) hnot

/-- The wide arcs of denominator `1` already exclude a neighbourhood of `0` and of `1`. -/
theorem not_mem_arcs_radius {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hnot : t ∉ wideArcs n) :
    (H n : ℝ) / (n : ℝ) < t ∧ (H n : ℝ) / (n : ℝ) < 1 - t := by
  have hQ1 : 1 ≤ Q1 n := by
    unfold Q1
    rw [Nat.one_le_floor_iff]
    exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  have h0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
  have h1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
  have hnot0 : ¬ (|t - ((0 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)| ≤
      (H n : ℝ) / (((1 : ℕ) : ℝ) * ((n : ℕ) : ℝ))) := fun hc =>
    hnot ⟨1, 0, le_rfl, hQ1, by norm_num, by simp, hc⟩
  have hnot1 : ¬ (|t - ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)| ≤
      (H n : ℝ) / (((1 : ℕ) : ℝ) * ((n : ℕ) : ℝ))) := fun hc =>
    hnot ⟨1, 1, le_rfl, hQ1, by norm_num, by simp, hc⟩
  have hlt0 : (H n : ℝ) / (n : ℝ) < |t| := by
    have h := lt_of_not_ge hnot0
    simpa [h0, h1, zero_div, sub_zero, one_mul] using h
  have hlt1 : (H n : ℝ) / (n : ℝ) < |t - 1| := by
    have h := lt_of_not_ge hnot1
    simpa [h1, div_one, one_mul] using h
  constructor
  · rwa [abs_of_nonneg ht.1] at hlt0
  · have hneg : t - 1 ≤ 0 := by linarith [ht.2]
    rw [abs_of_nonpos hneg] at hlt1
    linarith

/-- Model computation: on the complement of the wide arcs the constant weight `1` gives a sum
of size at most `n / (2 * H n)`, i.e. about `n^(2/3) / log^2 n`. -/
theorem norm_S_one_le {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hnot : t ∉ wideArcs n) :
    ‖S n (fun _ => (1 : ℝ)) t‖ ≤ (n : ℝ) / (2 * (H n : ℝ)) := by
  obtain ⟨htδ, h1tδ⟩ := not_mem_arcs_radius hn ht hnot
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hHpos : (0 : ℝ) < (H n : ℝ) := by exact_mod_cast H_pos hn
  have hδpos : (0 : ℝ) < (H n : ℝ) / (n : ℝ) := div_pos hHpos hnpos
  have hm_gt : (H n : ℝ) / (n : ℝ) < min t (1 - t) := lt_min htδ h1tδ
  have hgeom : (E t - 1) * (∑ k ∈ Finset.range (n + 1), E t ^ k) = E t ^ (n + 1) - 1 :=
    mul_geom_sum _ _
  have hnorm : ‖E t - 1‖ * ‖∑ k ∈ Finset.range (n + 1), E t ^ k‖ ≤ 2 := by
    rw [← norm_mul, hgeom]
    calc ‖E t ^ (n + 1) - 1‖ ≤ ‖E t ^ (n + 1)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_E]; norm_num
  have hchord : ‖E t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
    have hEt : E t = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
      unfold E
      rw [mul_comm]
    rw [hEt, Complex.norm_exp_I_mul_ofReal_sub_one]
    have harg : 2 * Real.pi * t / 2 = Real.pi * t := by ring
    rw [harg]
    norm_num
  have hlow : 4 * min t (1 - t) ≤ ‖E t - 1‖ := by
    rw [hchord]
    exact abs_sin_pi_ge_min t ht.1 ht.2
  have hmain : ‖∑ k ∈ Finset.range (n + 1), E t ^ k‖ ≤ 1 / (2 * min t (1 - t)) := by
    have hSm : (0 : ℝ) ≤ ‖∑ k ∈ Finset.range (n + 1), E t ^ k‖ := norm_nonneg _
    have h1 : ‖∑ k ∈ Finset.range (n + 1), E t ^ k‖ * (4 * min t (1 - t)) ≤
        ‖∑ k ∈ Finset.range (n + 1), E t ^ k‖ * ‖E t - 1‖ :=
      mul_le_mul_of_nonneg_left hlow hSm
    have h2 : ‖∑ k ∈ Finset.range (n + 1), E t ^ k‖ * ‖E t - 1‖ ≤ 2 := by
      rw [mul_comm]
      exact hnorm
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 2 * min t (1 - t))]
    linarith
  have hfin : 1 / (2 * min t (1 - t)) ≤ (n : ℝ) / (2 * (H n : ℝ)) := by
    have hδm : (H n : ℝ) / (n : ℝ) ≤ min t (1 - t) := le_of_lt hm_gt
    have hpos' : (0 : ℝ) < 2 * ((H n : ℝ) / (n : ℝ)) := by linarith
    have hle : 1 / (2 * min t (1 - t)) ≤ 1 / (2 * ((H n : ℝ) / (n : ℝ))) := by
      apply one_div_le_one_div_of_le hpos'
      linarith
    have heq : 1 / (2 * ((H n : ℝ) / (n : ℝ))) = (n : ℝ) / (2 * (H n : ℝ)) := by
      field_simp
    rwa [heq] at hle
  calc ‖S n (fun _ => (1 : ℝ)) t‖ = ‖∑ k ∈ Finset.range (n + 1), E t ^ k‖ := by
        rw [S_one_eq_geom]
    _ ≤ 1 / (2 * min t (1 - t)) := hmain
    _ ≤ (n : ℝ) / (2 * (H n : ℝ)) := hfin

/-- `n^(1/3) / 2 <= Q1 n` for `n >= 8`. -/
theorem Q1_ge {n : ℕ} (hn : 8 ≤ n) : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ (Q1 n : ℝ) := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) ^ (1 / 3 : ℝ) := by
    have h8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hpow : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, ← Real.rpow_natCast (2 : ℝ) 3,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    calc (2 : ℝ) = (8 : ℝ) ^ (1 / 3 : ℝ) := hpow.symm
      _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) h8 (by norm_num)
  have hfloor : (n : ℝ) ^ (1 / 3 : ℝ) < (Q1 n : ℝ) + 1 := by
    have h := Nat.lt_floor_add_one ((n : ℝ) ^ (1 / 3 : ℝ))
    exact_mod_cast h
  linarith

/-- `Q n` is at least one. -/
theorem Q_ge_one {n : ℕ} (hn : 1 ≤ n) : 1 ≤ Q n := by
  unfold Q
  have hlog : 1 ≤ Nat.log 2 (n + 2) := by
    apply Nat.le_log_of_pow_le (by norm_num)
    omega
  calc 1 = 1 ^ 2 := by norm_num
    _ ≤ (Nat.log 2 (n + 2)) ^ 2 := by gcongr

/-- For every `eta > 0`, the constant-weight version of the gap statement holds with
exponent `3/4 + eta` outside the wide arcs.  This is the circle model for the claim; the
prime weight `w` is *not* covered by this argument. -/
theorem norm_S_one_le_rpow (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ wideArcs n →
      ‖S n (fun _ => (1 : ℝ)) t‖ ≤ (n : ℝ) ^ (3 / 4 + η) := by
  refine ⟨8, fun n hn t ht hnot => ?_⟩
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hHpos : (0 : ℝ) < (H n : ℝ) := by exact_mod_cast H_pos hn1
  have hH : (0 : ℝ) < 2 * (H n : ℝ) := by linarith
  have hp : (0 : ℝ) < (n : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hnpos _
  refine (norm_S_one_le hn1 ht hnot).trans ?_
  rw [div_le_iff₀ hH]
  have hQ1 : (n : ℝ) ^ (1 / 3 : ℝ) / 2 ≤ (Q1 n : ℝ) := Q1_ge hn
  have hQ : (1 : ℝ) ≤ (Q n : ℝ) := by exact_mod_cast Q_ge_one hn1
  have hHge : 256 * (n : ℝ) ^ (1 / 3 : ℝ) ≤ 2 * (H n : ℝ) := by
    have hprod : (n : ℝ) ^ (1 / 3 : ℝ) / 2 * 1 ≤ (Q1 n : ℝ) * (Q n : ℝ) :=
      mul_le_mul hQ1 hQ (by norm_num) (by positivity)
    unfold H
    push_cast
    nlinarith
  have hexp : (1 : ℝ) / 4 - η ≤ 1 / 3 := by linarith
  have hbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hp1 : (n : ℝ) ^ ((1 : ℝ) / 4 - η) ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hmul : (n : ℝ) ^ ((1 : ℝ) / 4 - η) * (n : ℝ) ^ (3 / 4 + η) = (n : ℝ) := by
    rw [← Real.rpow_add hnpos]
    norm_num
  have hnn : (0 : ℝ) ≤ (n : ℝ) ^ (3 / 4 + η) := Real.rpow_nonneg (le_of_lt hnpos) _
  calc (n : ℝ) = (n : ℝ) ^ ((1 : ℝ) / 4 - η) * (n : ℝ) ^ (3 / 4 + η) := hmul.symm
    _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (3 / 4 + η) :=
        mul_le_mul_of_nonneg_right hp1 hnn
    _ ≤ (2 * (H n : ℝ)) * (n : ℝ) ^ (3 / 4 + η) :=
        mul_le_mul_of_nonneg_right (by linarith) hnn
    _ = (n : ℝ) ^ (3 / 4 + η) * (2 * (H n : ℝ)) := by ring

/-- `t = 0` always lies in the wide arcs (the arc of denominator one around zero). -/
theorem zero_mem_wideArcs {n : ℕ} (hn : 1 ≤ n) : (0 : ℝ) ∈ wideArcs n := by
  have hQ1 : 1 ≤ Q1 n := by
    unfold Q1
    rw [Nat.one_le_floor_iff]
    exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  refine ⟨1, 0, le_rfl, hQ1, by norm_num, by simp, ?_⟩
  have h0 : ((0 : ℕ) : ℝ) = 0 := by norm_num
  have h1 : ((1 : ℕ) : ℝ) = 1 := by norm_num
  rw [h0, h1, zero_div, sub_zero, abs_zero]
  positivity

/-- The exponent-one bound is attained at `t = 0`, which is *inside* the wide arcs.  Hence
the hypothesis `t not in wideArcs n` is indispensable: without it the claimed bound fails at
`t = 0` as soon as `theta n > n^(3/4+eta)`. -/
theorem claim_fails_without_arcs {n : ℕ} {η : ℝ}
    (h : (n : ℝ) ^ (3 / 4 + η) < Chebyshev.theta (n : ℝ)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, (n : ℝ) ^ (3 / 4 + η) < ‖S n w t‖ := by
  refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
  rwa [norm_S_w_zero]

/-- Dirichlet's approximation theorem plus reduction to lowest terms: whenever
`n <= H n * (Q1 n + 1)`, every `t` in `[0,1]` lies in the wide arcs.  This is the sharp covering
criterion (the true threshold is `n ≲ H n * Q1 n` up to a constant). -/
theorem mem_wideArcs_of_dirichlet {n : ℕ} (hn : 1 ≤ n) (hH : n ≤ H n * (Q1 n + 1)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : t ∈ wideArcs n := by
  have hQ1 : 0 < Q1 n := by
    unfold Q1
    rw [Nat.floor_pos]
    exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
  obtain ⟨k, hk0, hkQ, hk⟩ := Real.exists_nat_abs_mul_sub_round_le t hQ1
  have hk0R : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  set j : ℤ := round ((k : ℝ) * t) with hj
  have h1 : |(k : ℝ) * t - (j : ℝ)| ≤ 1 / 2 := by
    rw [hj]
    exact abs_sub_round _
  have hkt0 : 0 ≤ (k : ℝ) * t := mul_nonneg (le_of_lt hk0R) ht.1
  have hkt1 : (k : ℝ) * t ≤ (k : ℝ) := by
    have h := mul_le_mul_of_nonneg_left ht.2 (le_of_lt hk0R)
    simpa using h
  have hj0 : (0 : ℤ) ≤ j := by
    have hlt : (-1 : ℤ) < j := by
      have hlt' : (-1 : ℝ) < (j : ℝ) := by
        have := abs_le.mp h1
        linarith [this.1]
      exact_mod_cast hlt'
    omega
  have hjk : j ≤ (k : ℤ) := by
    have hlt : j < (k : ℤ) + 1 := by
      have hlt' : (j : ℝ) < (k : ℝ) + 1 := by
        have := abs_le.mp h1
        linarith [this.2]
      exact_mod_cast hlt'
    omega
  set a : ℕ := j.toNat with ha
  have haj : (a : ℤ) = j := Int.toNat_of_nonneg hj0
  have hak : a ≤ k := by
    have h : (a : ℤ) ≤ (k : ℤ) := by rw [haj]; exact hjk
    exact_mod_cast h
  have hg0 : 0 < Nat.gcd a k := Nat.gcd_pos_of_pos_right a hk0
  have hga : Nat.gcd a k ∣ a := Nat.gcd_dvd_left a k
  have hgk : Nat.gcd a k ∣ k := Nat.gcd_dvd_right a k
  have hq1 : 1 ≤ k / Nat.gcd a k :=
    Nat.div_pos (Nat.le_of_dvd hk0 hgk) hg0
  have hqQ : k / Nat.gcd a k ≤ Q1 n := (Nat.div_le_self k _).trans hkQ
  have haq : a / Nat.gcd a k ≤ k / Nat.gcd a k := Nat.div_le_div_right hak
  have hcop : Nat.Coprime (a / Nat.gcd a k) (k / Nat.gcd a k) :=
    Nat.coprime_div_gcd_div_gcd hg0
  have hka : ((a / Nat.gcd a k : ℕ) : ℝ) * ((Nat.gcd a k : ℕ) : ℝ) = (a : ℝ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hga]
  have hkk : ((k / Nat.gcd a k : ℕ) : ℝ) * ((Nat.gcd a k : ℕ) : ℝ) = (k : ℝ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hgk]
  have hqg : ((Nat.gcd a k : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((Nat.gcd a k : ℕ) : ℝ) := by exact_mod_cast hg0
    exact ne_of_gt this
  have hkgne : ((k / Nat.gcd a k : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((k / Nat.gcd a k : ℕ) : ℝ) := by exact_mod_cast hq1
    exact ne_of_gt this
  have hfrac : ((a / Nat.gcd a k : ℕ) : ℝ) / ((k / Nat.gcd a k : ℕ) : ℝ) = (a : ℝ) / (k : ℝ) := by
    rw [div_eq_div_iff hkgne (ne_of_gt hk0R)]
    have hcross : ((a / Nat.gcd a k : ℕ) : ℝ) * (k : ℝ) =
        (a : ℝ) * ((k / Nat.gcd a k : ℕ) : ℝ) := by
      rw [← hkk, ← hka]
      ring
    exact hcross
  have hdiff : t - (a : ℝ) / (k : ℝ) = ((k : ℝ) * t - (a : ℝ)) / (k : ℝ) := by
    field_simp
  have hstep : |t - (a : ℝ) / (k : ℝ)| ≤ (1 / ((Q1 n : ℝ) + 1)) / (k : ℝ) := by
    rw [hdiff, abs_div, abs_of_pos hk0R]
    have hnum : |(k : ℝ) * t - (a : ℝ)| ≤ 1 / ((Q1 n : ℝ) + 1) := by
      have hcast : (a : ℝ) = (j : ℝ) := by exact_mod_cast haj
      rw [hcast]
      exact hk
    exact div_le_div_of_nonneg_right hnum (le_of_lt hk0R)
  have hHle : 1 / ((Q1 n : ℝ) + 1) ≤ (H n : ℝ) / (n : ℝ) := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcast : (n : ℝ) ≤ (H n : ℝ) * ((Q1 n : ℝ) + 1) := by
      have h : ((n : ℕ) : ℝ) ≤ ((H n * (Q1 n + 1) : ℕ) : ℝ) := by exact_mod_cast hH
      calc (n : ℝ) ≤ ((H n * (Q1 n + 1) : ℕ) : ℝ) := h
        _ = (H n : ℝ) * ((Q1 n : ℝ) + 1) := by push_cast; ring
    rw [div_le_div_iff₀ (by positivity) hnpos]
    simpa using hcast
  have hstep2 : (H n : ℝ) / (n : ℝ) / (k : ℝ) ≤
      (H n : ℝ) / (((k / Nat.gcd a k : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by
    have hnn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hHpos : (0 : ℝ) ≤ ((H n : ℕ) : ℝ) := Nat.cast_nonneg (H n)
    have hle : ((k / Nat.gcd a k : ℕ) : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast Nat.div_le_self k (Nat.gcd a k)
    have hpos : (0 : ℝ) < ((k / Nat.gcd a k : ℕ) : ℝ) := by exact_mod_cast hq1
    rw [div_div]
    refine div_le_div_of_nonneg_left hHpos (by positivity) ?_
    nlinarith
  have hmem : |t - ((a / Nat.gcd a k : ℕ) : ℝ) / ((k / Nat.gcd a k : ℕ) : ℝ)| ≤
      (H n : ℝ) / (((k / Nat.gcd a k : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := by
    calc |t - ((a / Nat.gcd a k : ℕ) : ℝ) / ((k / Nat.gcd a k : ℕ) : ℝ)|
        = |t - (a : ℝ) / (k : ℝ)| := by rw [hfrac]
      _ ≤ (1 / ((Q1 n : ℝ) + 1)) / (k : ℝ) := hstep
      _ ≤ (H n : ℝ) / (n : ℝ) / (k : ℝ) := div_le_div_of_nonneg_right hHle (le_of_lt hk0R)
      _ ≤ (H n : ℝ) / (((k / Nat.gcd a k : ℕ) : ℝ) * ((n : ℕ) : ℝ)) := hstep2
  exact ⟨k / Nat.gcd a k, a / Nat.gcd a k, hq1, hqQ, haq, hcop, hmem⟩

/-- Consequently the wide arcs cover `[0,1]` for all `n <= H n * (Q1 n + 1)`. -/
theorem wideArcs_cover_of_dirichlet {n : ℕ} (hn : 1 ≤ n) (hH : n ≤ H n * (Q1 n + 1)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∈ wideArcs n :=
  fun _ ht => mem_wideArcs_of_dirichlet hn hH ht

/-- The gap statement holds (vacuously) for every `n <= H n * (Q1 n + 1)`; this covers all
`n <= 7 * 10^17`; beyond it the hypothesis is non-empty. -/
theorem claim_on_dirichlet_range (η : ℝ) (n : ℕ) (hn : 1 ≤ n) (hH : n ≤ H n * (Q1 n + 1)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, t ∉ wideArcs n → ‖S n w t‖ ≤ (n : ℝ) ^ (3 / 4 + η) :=
  fun _ ht hnot => absurd (mem_wideArcs_of_dirichlet hn hH ht) hnot

end GoldbachFrontier34







end PEqualNP.Outside
