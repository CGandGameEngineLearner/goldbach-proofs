import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_medcore_model_floor

open Real Complex intervalIntegral

/-!
# Unconditional signed floor in the near-rational part of the widened remainder

Task `L-goldbach-wide-remainder-inner-floor` (route `wide-arc-signed-remainder`).

## Region identification

With `Q = ⌊log₂(n+2)⌋²`, `Q₁ = ⌊n^{1/3}⌋`, `H = 256·Q₁·Q`:

* `arcs`      : reduced arcs, `q ≤ Q`, radius `Q/(qn)` (the original major arcs);
* `wideArcs`  : `q ≤ Q₁`, radius `H/(qn)`;
* `lowWideArcs`: `q ≤ Q`, radius `H/(qn)`;
* `lowPart = lowWideArcs \ arcs` : the *low-modulus skirt* — proved separately
  (LogTruSoul, PR #2992, via character mean-square + short-interval estimates);
* `remainder = (wideArcs \ arcs) \ lowPart` : the *medium-modulus* part, `Q < q ≤ Q₁`;
* `inner` : the same arcs at the shorter radius `Q·n^{1/6}/(qn)`.

So `remainder ∩ inner` is the medium-modulus band split into

* a **core** of radius `Q/(qn)` — covered by the verified
  `L_goldbach_frontier_medcore_model_floor` (the whitelist import below), and
* an **inner skirt** annulus `Q/(qn) < |u| ≤ Q·n^{1/6}/(qn)`.

## Where the remaining difficulty sits

The skirt *model term* is harmless: with `ΔJ(q) ≤ min(n, C·Q·n^{7/6}/q)` and
`1/φ(q)² ≤ d(q)²/q²`, `d(q) ≤ 2√q`, the summed model contribution is
`O(n/√Q + n^{11/12}/√Q) = o(n)`.

The genuine obstruction is the **f–model match** on the medium band. Per-character
pointwise bounds blow up when a real character mod `q` (with `q ∣ n`) carries a
Siegel zero near `1`. Two known ways past it:

1. a **fixed positive-width zero-free strip** for Dirichlet `L`-functions
   (the route discussed in #3806 — porting the 7/8 nonvanishing theorem);
2. a **character mean-square (L²) bound** over the medium band, which dilutes a
   single exceptional character to `O(1)` — the technique that already worked for
   the polylog skirt, pushed from `q ≤ (log n)²` up to `q ≤ n^{1/3}`.

This file currently states the frozen goal; the reduction above is recorded so the
remaining gap is pinned to the skirt model-match alone.
-/

set_option maxHeartbeats 4000000

/-! ### Verified foundations: circle-method orthogonality on [0,1]

These match the frozen statement's `w` and `E` exactly. They are the starting
point of any circle-method proof: the total integral of `f n` over [0,1] is the
weighted Goldbach count `R n = Σ_{k+l=n} w k w l ≥ 0`.
-/

/-- Task's weight: `log` on primes, `0` otherwise (matches the frozen `w`). -/
noncomputable def GW (k : ℕ) : ℝ := if Nat.Prime k then Real.log k else 0

/-- Task's exponential `E x = exp(2πi x)` (matches the frozen `E`). -/
noncomputable def GE (x : ℝ) : ℂ := Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

lemma GE_add (x y : ℝ) : GE x * GE y = GE (x + y) := by
  simp only [GE]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- ∫₀¹ exp(2πi m t) dt = δ_{m,0} for integer `m`. -/
lemma integral_exp_freq (m : ℤ) :
    (∫ t in (0:ℝ)..1, Complex.exp ((2 * Real.pi * Complex.I) * (m:ℂ) * t))
      = if m = 0 then 1 else 0 := by
  by_cases h : m = 0
  · subst h; simp
  · have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [mul_eq_zero, Real.pi_ne_zero]
    have hc : (2 * Real.pi * Complex.I) * (m:ℂ) ≠ 0 := mul_ne_zero h2pi (by exact_mod_cast h)
    rw [integral_exp_mul_complex hc, if_neg h]
    have h1 : Complex.exp ((2 * Real.pi * Complex.I) * (m:ℂ) * ((1:ℝ):ℂ)) = 1 := by
      have hm := Complex.exp_int_mul_two_pi_mul_I m
      simpa [mul_comm] using hm
    have h0 : Complex.exp ((2 * Real.pi * Complex.I) * (m:ℂ) * ((0:ℝ):ℂ)) = 1 := by simp
    rw [h1, h0]; simp

/-- Bridge: `GE` at an integer multiple of `t` is the standard integer-frequency exponential. -/
lemma GE_int_mul (m : ℤ) (t : ℝ) :
    GE ((m:ℝ) * t) = Complex.exp ((2 * Real.pi * Complex.I) * (m:ℂ) * t) := by
  have h : ((2 * Real.pi * ((m:ℝ) * t) : ℝ) : ℂ) * Complex.I
      = (2 * Real.pi * Complex.I) * (m:ℂ) * t := by
    push_cast
    ring
  simp only [GE, h]

/-- Orthogonality with `GE`: ∫₀¹ GE(m·u) du = δ_{m,0}. -/
lemma integral_GE_freq (m : ℤ) :
    (∫ u in (0:ℝ)..1, GE ((m:ℝ) * u)) = if m = 0 then 1 else 0 := by
  have h : ∀ u : ℝ, GE ((m:ℝ) * u) = Complex.exp ((2 * Real.pi * Complex.I) * (m:ℂ) * u) :=
    fun u => GE_int_mul m u
  simp only [h]
  exact integral_exp_freq m

/-! ### Orthogonality, the circle-method identity, and Goldbach detection -/

lemma nat_cast_sub_eq_zero (a b c : ℕ) :
    (((a:ℤ) + (b:ℤ) - (c:ℤ) : ℤ) = 0) ↔ (a + b = c) := by
  constructor
  · intro h0
    have h1 : ((a:ℤ) + (b:ℤ):ℤ) = (c:ℤ) := by linarith
    have h2 : ((a + b : ℕ):ℤ) = (c:ℤ) := by simpa [Nat.cast_add] using h1
    exact Nat.cast_injective h2
  · intro hc
    have h2 : ((a + b : ℕ):ℤ) = (c:ℤ) := by rw [hc]
    linarith

/-- Orthogonality for a natural frequency combination: the integral picks out `a + b = c`. -/
lemma integral_GE_freq_nat (a b c : ℕ) :
    (∫ u in (0:ℝ)..1, GE (((a:ℝ) + (b:ℝ) - (c:ℝ)) * u))
      = if a + b = c then 1 else 0 := by
  have hrefl : ∀ u : ℝ, GE (((a:ℝ) + (b:ℝ) - (c:ℝ)) * u)
      = Complex.exp ((2 * Real.pi * Complex.I) * (((a:ℤ) + (b:ℤ) - (c:ℤ) : ℤ) : ℂ) * u) := by
    intro u
    rw [show (((a:ℝ) + (b:ℝ) - (c:ℝ)) = (((a:ℤ) + (b:ℤ) - (c:ℤ) : ℤ) : ℝ)) from by
      push_cast; ring]
    exact GE_int_mul ((a:ℤ) + (b:ℤ) - (c:ℤ)) u
  simp only [hrefl]
  rw [integral_exp_freq ((a:ℤ) + (b:ℤ) - (c:ℤ))]
  simp only [nat_cast_sub_eq_zero]

/-- Pointwise: the integrand `S²·E(−nt)` expands into the double sum of
`w k₁ w k₂ · E((k₁+k₂−n)t)` over the square `range(n+1)²`. -/
lemma pointwise_expand (n : ℕ) (t : ℝ) :
    (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2
      * GE (-(n:ℝ)*t)
      = ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
          ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t) := by
  have hSq : (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2
           = Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t))
           * Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)) := by
    rw [pow_two]
  rw [hSq, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hE : GE ((i:ℝ)*t) * GE ((j:ℝ)*t) * GE (-(n:ℝ)*t)
          = GE (((i:ℝ) + (j:ℝ) - (n:ℝ)) * t) := by
    rw [GE_add, GE_add]
    congr 1
    push_cast
    ring
  have hring : (↑(GW i) * GE ((i:ℝ)*t)) * (↑(GW j) * GE ((j:ℝ)*t)) * GE (-(n:ℝ)*t)
             = (↑(GW i * GW j) : ℂ) * (GE ((i:ℝ)*t) * GE ((j:ℝ)*t) * GE (-(n:ℝ)*t)) := by
    push_cast
    ring
  rw [hring, hE]

/-! ### The circle-method identity: total integral = weighted Goldbach count -/

lemma continuous_GE : Continuous GE := by
  show Continuous (fun x : ℝ => Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I))
  have h1 : Continuous (fun x : ℝ => (2 * Real.pi * x : ℝ)) := continuous_const.mul continuous_id
  have h2 : Continuous (fun x : ℝ => ((2 * Real.pi * x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h1
  have h3 : Continuous (fun x : ℝ => ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) :=
    h2.mul continuous_const
  exact Complex.continuous_exp.comp h3

lemma GW_nonneg (k : ℕ) : 0 ≤ GW k := by
  by_cases h : Nat.Prime k
  · simp only [GW, if_pos h]
    exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · simp [GW, h]

lemma continuous_const_mul_GE (c : ℂ) (r : ℝ) :
    Continuous (fun t => c * GE (r * t)) :=
  continuous_const.mul (continuous_GE.comp (continuous_const.mul continuous_id))

lemma intervalIntegrable_const_mul_GE (c : ℂ) (r : ℝ) :
    IntervalIntegrable (fun t => c * GE (r * t)) MeasureTheory.volume 0 1 :=
  Continuous.intervalIntegrable (continuous_const_mul_GE c r) 0 1

/-- **Circle-method identity.** The total integral over `[0,1]` of the Goldbach integrand
`f n t = (Σ_{k≤n} w k E(k t))² E(-n t)` is exactly the weighted representation count
`Σ_{k≤n} w k · w (n-k)`. This is the seed of the whole route: the analytic object on the
left is a nonnegative count on the right, positive precisely when `n` is a Goldbach number.
(Here `w = GW`, `E = GE`; both are definitionally the frozen statement's `w` and `E`.) -/
lemma integral_f_eq_R (n : ℕ) :
    (∫ t in (0:ℝ)..1,
        (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2
          * GE (-(n:ℝ)*t))
      = ∑ k ∈ Finset.range (n+1), ((GW k * GW (n - k) : ℝ) : ℂ) := by
  have hexpand : ∀ t : ℝ,
      (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2 * GE (-(n:ℝ)*t)
      = ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
          ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t) :=
    fun t => pointwise_expand n t
  have hsumint : ∀ k1 : ℕ, IntervalIntegrable (fun t => ∑ k2 ∈ Finset.range (n+1),
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t))
      MeasureTheory.volume 0 1 :=
    fun k1 => Continuous.intervalIntegrable
      (continuous_finsetSum (Finset.range (n+1))
        (fun k2 _ => continuous_const_mul_GE _ _)) 0 1
  have houter : (∫ t in (0:ℝ)..1, ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t))
      = ∑ k1 ∈ Finset.range (n+1), ∫ t in (0:ℝ)..1, ∑ k2 ∈ Finset.range (n+1),
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t) :=
    intervalIntegral.integral_finsetSum (fun k1 _ => hsumint k1)
  have hinnerint : ∀ k1 : ℕ, (∫ t in (0:ℝ)..1, ∑ k2 ∈ Finset.range (n+1),
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t))
      = ∑ k2 ∈ Finset.range (n+1), ∫ t in (0:ℝ)..1,
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t) :=
    fun k1 => intervalIntegral.integral_finsetSum (fun k2 _ => intervalIntegrable_const_mul_GE _ _)
  have hterm : ∀ k1 k2 : ℕ, (∫ t in (0:ℝ)..1,
        ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t))
      = ((GW k1 * GW k2 : ℝ) : ℂ) * (if k1 + k2 = n then (1:ℂ) else 0) := by
    intro k1 k2
    rw [intervalIntegral.integral_const_mul, integral_GE_freq_nat]
  have hcollapse : ∀ k1 ∈ Finset.range (n+1),
      (∑ k2 ∈ Finset.range (n+1), (if k1 + k2 = n then ((GW k1 * GW k2 : ℝ) : ℂ) else (0:ℂ)))
        = ((GW k1 * GW (n - k1) : ℝ) : ℂ) := by
    intro k1 hk1
    have hk1le : k1 ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk1)
    rw [Finset.sum_eq_single (n - k1)]
    · rw [if_pos (show k1 + (n - k1) = n by omega)]
    · intro k2 _ hk2
      rw [if_neg (show ¬(k1 + k2 = n) by omega)]
    · intro hk
      rw [Finset.mem_range] at hk
      omega
  simp only [hexpand]
  rw [houter, Finset.sum_congr rfl (fun k1 _ => hinnerint k1),
    Finset.sum_congr rfl (fun k1 _ => Finset.sum_congr rfl (fun k2 _ => hterm k1 k2))]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl (fun k1 hk1 => hcollapse k1 hk1)]

/-- The weighted representation count is nonnegative. -/
lemma R_ge_zero (n : ℕ) : 0 ≤ ∑ k ∈ Finset.range (n+1), (GW k * GW (n - k) : ℝ) :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (GW_nonneg k) (GW_nonneg (n - k)))

/-- **Goldbach detected analytically.** The weighted count is positive iff `n` has a
representation as a sum of two primes (with both summands in `[0, n]`). -/
lemma R_pos_iff (n : ℕ) :
    (0 < ∑ k ∈ Finset.range (n+1), (GW k * GW (n - k) : ℝ))
      ↔ ∃ k ∈ Finset.range (n+1), Nat.Prime k ∧ Nat.Prime (n - k) := by
  constructor
  · intro hpos
    by_contra hnone
    have hterm0 : ∀ k ∈ Finset.range (n+1), (GW k * GW (n - k) : ℝ) = 0 := by
      intro k hk
      by_cases hp : Nat.Prime k
      · by_cases hq : Nat.Prime (n - k)
        · exact absurd ⟨k, hk, hp, hq⟩ hnone
        · simp only [GW, if_neg hq, mul_zero]
      · simp only [GW, if_neg hp, zero_mul]
    rw [Finset.sum_eq_zero hterm0] at hpos
    linarith
  · rintro ⟨k0, hk0, hp, hq⟩
    have hpos_term : 0 < (GW k0 * GW (n - k0) : ℝ) :=
      mul_pos (by simp only [GW, if_pos hp]; exact Real.log_pos (by exact_mod_cast hp.one_lt))
        (by simp only [GW, if_pos hq]; exact Real.log_pos (by exact_mod_cast hq.one_lt))
    exact lt_of_lt_of_le hpos_term
      (Finset.single_le_sum (fun k _ => mul_nonneg (GW_nonneg k) (GW_nonneg (n - k))) hk0)

/-- The real part of the total integral over `[0,1]` is the weighted Goldbach count —
this is exactly `J n Set.univ` for the frozen statement's `J` (via `Set.indicator_univ`). -/
lemma re_total_integral_eq_R (n : ℕ) :
    (intervalIntegral
        (fun t => (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2
          * GE (-(n:ℝ)*t)) (0:ℝ) 1 MeasureTheory.volume).re
      = ∑ k ∈ Finset.range (n+1), (GW k * GW (n - k) : ℝ) := by
  rw [integral_f_eq_R, Complex.re_sum]
  simp


/-! ### The master reduction: J additivity and the route partition -/

/-- The Goldbach integrand of the frozen statement, built from `GW`/`GE`. -/
noncomputable def fG (n : ℕ) (t : ℝ) : ℂ :=
  (Finset.sum (Finset.range (n+1)) (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2
    * GE (-(n:ℝ)*t)

/-- The frozen `J` functional: real part of the interval integral of the
set-indicator of `A` against the Goldbach integrand. -/
noncomputable def JG (n : ℕ) (A : Set ℝ) : ℝ :=
  (intervalIntegral (fun t => A.indicator (fG n) t) (0:ℝ) 1 MeasureTheory.volume).re

lemma continuous_summand_GE (n : ℕ) (k : ℕ) :
    Continuous (fun t : ℝ => (GW k : ℂ) * GE ((k:ℝ)*t)) :=
  continuous_const_mul_GE _ _

lemma continuous_fG (n : ℕ) : Continuous (fG n) := by
  have hS : Continuous (fun t : ℝ => Finset.sum (Finset.range (n+1))
      (fun k => (GW k : ℂ) * GE ((k:ℝ)*t))) :=
    continuous_finsetSum (Finset.range (n+1)) (fun k _ => continuous_summand_GE n k)
  have h1 : Continuous (fun t : ℝ => (Finset.sum (Finset.range (n+1))
      (fun k => (GW k : ℂ) * GE ((k:ℝ)*t)))^2) := hS.pow 2
  have h2 : Continuous (fun t : ℝ => GE (-(n:ℝ)*t)) :=
    continuous_GE.comp (continuous_const.mul continuous_id)
  exact h1.mul h2

lemma intervalIntegrable_fG (n : ℕ) :
    IntervalIntegrable (fG n) MeasureTheory.volume 0 1 :=
  Continuous.intervalIntegrable (continuous_fG n) 0 1

lemma intervalIntegrable_indicator_fG (n : ℕ) {A : Set ℝ} (hA : MeasurableSet A) :
    IntervalIntegrable (fun t => A.indicator (fG n) t) MeasureTheory.volume 0 1 := by
  have hb : (0:ℝ) ≤ 1 := by norm_num
  have hIntOn : MeasureTheory.IntegrableOn (fG n) (Set.Icc (0:ℝ) 1) MeasureTheory.volume :=
    (continuous_fG n).continuousOn.integrableOn_Icc
  have h' : MeasureTheory.IntegrableOn (A.indicator (fG n)) (Set.Icc (0:ℝ) 1)
      MeasureTheory.volume :=
    (show MeasureTheory.Integrable (fG n)
        (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) from hIntOn).indicator hA
  have h : MeasureTheory.IntegrableOn (A.indicator (fG n)) (Set.uIcc (0:ℝ) 1)
      MeasureTheory.volume := by
    rwa [← Set.uIcc_of_le hb] at h'
  exact h.intervalIntegrable

/-- `JG` is finitely additive over disjoint measurable sets. -/
lemma JG_add (n : ℕ) {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hd : Disjoint A B) : JG n (A ∪ B) = JG n A + JG n B := by
  have hIA := intervalIntegrable_indicator_fG n hA
  have hIB := intervalIntegrable_indicator_fG n hB
  unfold JG
  have hstep : (∫ t in (0:ℝ)..1, (A ∪ B).indicator (fG n) t)
      = (∫ t in (0:ℝ)..1, A.indicator (fG n) t + B.indicator (fG n) t) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact congrFun (Set.indicator_union_of_disjoint hd (fG n)) t
  rw [hstep, intervalIntegral.integral_add hIA hIB, Complex.add_re]

/-! ### Measurability of the arc sets -/

/-- Any "arc family" set — a finite union over coprime `a/q` with `q ≤ Q` of intervals
of a prescribed radius `B q` — is measurable. This covers `arcs`, `wideArcs`,
`lowWideArcs` and `inner` of the frozen statement. -/
lemma measurableSet_arc_family (Q : ℕ) (B : ℕ → ℝ) :
    MeasurableSet {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q
      ∧ |t - (a:ℝ)/(q:ℝ)| ≤ B q} := by
  have hsets : {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q ∧ a ≤ q ∧ Nat.Coprime a q
      ∧ |t - (a:ℝ)/(q:ℝ)| ≤ B q}
      = ⋃ q ∈ Finset.range (Q+1), ⋃ a ∈ Finset.range (Q+1),
        {t : ℝ | 1 ≤ q ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ B q} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨q, a, h1, h2, h3, h4, h5⟩
      exact ⟨q, Finset.mem_range.mpr (Nat.lt_succ_of_le h2), a,
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_trans h3 h2)),
        h1, h3, h4, h5⟩
    · rintro ⟨q, hq, a, ha, h1, h3, h4, h5⟩
      exact ⟨q, a, h1, Nat.le_of_lt_succ (Finset.mem_range.mp hq), h3, h4, h5⟩
  rw [hsets]
  refine Finset.measurableSet_biUnion (Finset.range (Q+1)) (fun q _ =>
    Finset.measurableSet_biUnion (Finset.range (Q+1)) (fun a _ => ?_))
  by_cases h : a ≤ q ∧ Nat.Coprime a q
  · have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · subst hq0
        have ha0 : a = 0 := Nat.le_zero.mp h.1
        subst ha0
        exact absurd h.2 (by simp)
      · exact hq0
    have heq : {t : ℝ | 1 ≤ q ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ B q}
        = Set.Icc ((a:ℝ)/(q:ℝ) - B q) ((a:ℝ)/(q:ℝ) + B q) := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
      constructor
      · intro hh
        rcases hh with ⟨h1, h2, h3, h4, h5⟩
        constructor <;> linarith
      · intro hh
        rcases hh with ⟨h1, h2⟩
        exact ⟨hq1, h.1, h.2, by linarith, by linarith⟩
    rw [heq]
    exact isClosed_Icc.measurableSet
  · have heq : {t : ℝ | 1 ≤ q ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t - (a:ℝ)/(q:ℝ)| ≤ B q} = ∅ := by
      ext t
      constructor
      · intro hmem
        exact h ⟨hmem.2.1, hmem.2.2.1⟩
      · intro hfalse
        exact False.elim hfalse
    rw [heq]
    exact MeasurableSet.empty

/-! ### The frozen regions and the route partition -/

noncomputable def Qf (n : ℕ) : ℕ := (Nat.log 2 (n+2))^2
noncomputable def Q1f (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊
noncomputable def Hf (n : ℕ) : ℕ := 256 * Q1f n * Qf n

noncomputable def arcsRegion (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qf n ∧ a ≤ q ∧ Nat.Coprime a q
    ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (Qf n:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def wideArcsRegion (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q1f n ∧ a ≤ q ∧ Nat.Coprime a q
    ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (Hf n:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def lowWideArcsRegion (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Qf n ∧ a ≤ q ∧ Nat.Coprime a q
    ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (Hf n:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def innerRegion (n : ℕ) : Set ℝ :=
  {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ Q1f n ∧ a ≤ q ∧ Nat.Coprime a q
    ∧ |t - (a:ℝ)/(q:ℝ)| ≤ (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ))}

noncomputable def lowPartRegion (n : ℕ) : Set ℝ := lowWideArcsRegion n \ arcsRegion n

noncomputable def remainderRegion (n : ℕ) : Set ℝ :=
  (wideArcsRegion n \ arcsRegion n) \ lowPartRegion n

lemma measurableSet_arcsRegion (n : ℕ) : MeasurableSet (arcsRegion n) :=
  measurableSet_arc_family (Qf n) (fun q => (Qf n:ℝ)/((q:ℝ)*(n:ℝ)))

lemma measurableSet_wideArcsRegion (n : ℕ) : MeasurableSet (wideArcsRegion n) :=
  measurableSet_arc_family (Q1f n) (fun q => (Hf n:ℝ)/((q:ℝ)*(n:ℝ)))

lemma measurableSet_lowWideArcsRegion (n : ℕ) : MeasurableSet (lowWideArcsRegion n) :=
  measurableSet_arc_family (Qf n) (fun q => (Hf n:ℝ)/((q:ℝ)*(n:ℝ)))

lemma measurableSet_innerRegion (n : ℕ) : MeasurableSet (innerRegion n) :=
  measurableSet_arc_family (Q1f n) (fun q => (Qf n:ℝ)*(n:ℝ)^(1/6:ℝ)/((q:ℝ)*(n:ℝ)))

lemma measurableSet_lowPartRegion (n : ℕ) : MeasurableSet (lowPartRegion n) :=
  (measurableSet_lowWideArcsRegion n).diff (measurableSet_arcsRegion n)

lemma measurableSet_remainderRegion (n : ℕ) : MeasurableSet (remainderRegion n) :=
  ((measurableSet_wideArcsRegion n).diff (measurableSet_arcsRegion n)).diff
    (measurableSet_lowPartRegion n)

/-- **The route partition.** The weighted Goldbach count `JG n univ` splits exactly into
the five route pieces: major arcs, low-modulus skirt, the target band
(`remainder ∩ inner`), the outer skirt (`remainder \ inner`) and the deep minor arcs.
Hence the target band equals the count minus the other four — the master checklist of
the `wide-arc-signed-remainder` route. The containments `arcs ⊆ wideArcs`,
`lowWideArcs ⊆ wideArcs`, `inner ⊆ wideArcs` hold asymptotically (`Q ≤ Q₁`, `Q ≤ H`,
`Q·n^{1/6} ≤ H`). -/
lemma JG_partition (n : ℕ)
    (hsub1 : arcsRegion n ⊆ wideArcsRegion n)
    (hsub2 : lowWideArcsRegion n ⊆ wideArcsRegion n)
    (hsub3 : innerRegion n ⊆ wideArcsRegion n) :
    JG n (remainderRegion n ∩ innerRegion n)
      = JG n Set.univ - JG n (arcsRegion n) - JG n (lowPartRegion n)
        - JG n (remainderRegion n \ innerRegion n)
        - JG n (Set.univ \ wideArcsRegion n) := by
  have hUW : MeasurableSet (Set.univ \ wideArcsRegion n) :=
    MeasurableSet.univ.diff (measurableSet_wideArcsRegion n)
  have hWAdiff : MeasurableSet (wideArcsRegion n \ arcsRegion n) :=
    (measurableSet_wideArcsRegion n).diff (measurableSet_arcsRegion n)
  have h1 : JG n Set.univ = JG n (wideArcsRegion n) + JG n (Set.univ \ wideArcsRegion n) := by
    have hdisj : Disjoint (wideArcsRegion n) (Set.univ \ wideArcsRegion n) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext t
      simp
    have hthis := JG_add n (measurableSet_wideArcsRegion n) hUW hdisj
    rw [← Set.compl_eq_univ_diff, Set.union_compl_self, Set.compl_eq_univ_diff] at hthis
    exact hthis
  have h2 : JG n (wideArcsRegion n)
      = JG n (arcsRegion n) + JG n (wideArcsRegion n \ arcsRegion n) := by
    have hdisj : Disjoint (arcsRegion n) (wideArcsRegion n \ arcsRegion n) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext t
      simp
    have hthis := JG_add n (measurableSet_arcsRegion n) hWAdiff hdisj
    rw [Set.union_diff_self, Set.union_eq_self_of_subset_left hsub1] at hthis
    exact hthis
  have h3 : JG n (wideArcsRegion n \ arcsRegion n)
      = JG n (lowPartRegion n) + JG n (remainderRegion n) := by
    have hseteq : wideArcsRegion n \ arcsRegion n
        = lowPartRegion n ∪ remainderRegion n := by
      ext t
      simp only [lowPartRegion, remainderRegion, Set.mem_diff, Set.mem_union]
      by_cases h1t : t ∈ arcsRegion n
      · simp [h1t]
      · by_cases h2t : t ∈ lowWideArcsRegion n
        · simp [h1t, h2t, hsub2 h2t]
        · simp [h1t, h2t]
    have hdisj : Disjoint (lowPartRegion n) (remainderRegion n) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext t
      simp [lowPartRegion, remainderRegion]
    rw [hseteq]
    exact JG_add n (measurableSet_lowPartRegion n) (measurableSet_remainderRegion n) hdisj
  have h4 : JG n (remainderRegion n)
      = JG n (remainderRegion n ∩ innerRegion n)
        + JG n (remainderRegion n \ innerRegion n) := by
    have hseteq : remainderRegion n
        = remainderRegion n ∩ innerRegion n ∪ (remainderRegion n \ innerRegion n) := by
      ext t
      simp only [remainderRegion, Set.mem_inter_iff, Set.mem_diff, Set.mem_union]
      tauto
    have hdisj : Disjoint (remainderRegion n ∩ innerRegion n)
        (remainderRegion n \ innerRegion n) := by
      rw [Set.disjoint_iff_inter_eq_empty]
      ext t
      simp [remainderRegion]
    nth_rewrite 1 [hseteq]
    exact JG_add n
      ((measurableSet_remainderRegion n).inter (measurableSet_innerRegion n))
      ((measurableSet_remainderRegion n).diff (measurableSet_innerRegion n)) hdisj
  rw [h4] at h3
  rw [h3] at h2
  rw [h2] at h1
  linarith

/-- **Route checklist.** The frozen floor for the target band follows from the four
route bounds: the major arcs capture the weighted count up to `εn/2`, and each of
the low skirt, the outer skirt and the deep minor arcs contributes at most `εn/6`.
Every route sub-task supplies exactly one of these hypotheses. -/
theorem JG_target_floor (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hsub1 : arcsRegion n ⊆ wideArcsRegion n)
    (hsub2 : lowWideArcsRegion n ⊆ wideArcsRegion n)
    (hsub3 : innerRegion n ⊆ wideArcsRegion n)
    (harcs : JG n (arcsRegion n) ≤ JG n Set.univ + ε / 2 * n)
    (hlow : JG n (lowPartRegion n) ≤ ε / 6 * n)
    (houter : JG n (remainderRegion n \ innerRegion n) ≤ ε / 6 * n)
    (hdeep : JG n (Set.univ \ wideArcsRegion n) ≤ ε / 6 * n) :
    -(ε * n) ≤ JG n (remainderRegion n ∩ innerRegion n) := by
  have hpart := JG_partition n hsub1 hsub2 hsub3
  linarith

/-!
### Off-diagonal reduction

The band integral splits into the nonnegative diagonal term `R(n) · K(0)` — where
`K(0) = Re ∫_B 1 ≥ 0` — plus an explicit off-diagonal signed series with real weights
`GW k1 * GW k2` and oscillatory factors `Re ∫_B E((k1+k2−n)t)`. The floor `−εn ≤ JG n B`
therefore reduces to a lower bound on that discrete series.
-/
section OffDiag
open scoped Classical

lemma GE_zero : GE 0 = 1 := by
  show Complex.exp ((2 * Real.pi * 0 : ℝ) * Complex.I) = 1
  have h0 : ((2 * Real.pi * 0 : ℝ) : ℂ) = 0 := by norm_num
  rw [h0, zero_mul, Complex.exp_zero]

/-- Integrability of the indicator of a measurable set against a continuous function. -/
lemma intervalIntegrable_indicator_continuous {g : ℝ → ℂ} (hg : Continuous g)
    {B : Set ℝ} (hB : MeasurableSet B) :
    IntervalIntegrable (fun t => B.indicator g t) MeasureTheory.volume (0:ℝ) 1 := by
  have hb : (0:ℝ) ≤ 1 := by norm_num
  have hIntOn : MeasureTheory.IntegrableOn g (Set.Icc (0:ℝ) 1) MeasureTheory.volume :=
    hg.continuousOn.integrableOn_Icc
  have h' : MeasureTheory.IntegrableOn (B.indicator g) (Set.Icc (0:ℝ) 1)
      MeasureTheory.volume :=
    (show MeasureTheory.Integrable g
        (MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1)) from hIntOn).indicator hB
  have h : MeasureTheory.IntegrableOn (B.indicator g) (Set.uIcc (0:ℝ) 1)
      MeasureTheory.volume := by
    rwa [← Set.uIcc_of_le hb] at h'
  exact h.intervalIntegrable

/-- Pointwise-form finite-sum integrability. -/
lemma intervalIntegrable_sum_pointwise {ι : Type*} {F : ι → ℝ → ℂ} (s : Finset ι)
    (hF : ∀ i ∈ s, IntervalIntegrable (F i) MeasureTheory.volume (0:ℝ) 1) :
    IntervalIntegrable (fun t => ∑ i ∈ s, F i t) MeasureTheory.volume (0:ℝ) 1 := by
  exact (IntervalIntegrable.sum s hF).congr (fun t _ => by rw [Finset.sum_apply])

/-- Finite-sum interchange for interval integrals. -/
lemma intervalIntegral_sum {ι : Type*} (F : ι → ℝ → ℂ) (s : Finset ι)
    (hF : ∀ i ∈ s, IntervalIntegrable (F i) MeasureTheory.volume (0:ℝ) 1) :
    (∫ t in (0:ℝ)..1, ∑ i ∈ s, F i t)
      = ∑ i ∈ s, (∫ t in (0:ℝ)..1, F i t) := by
  classical
  revert hF
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert i s hi ih =>
    intro hF
    have hFi : IntervalIntegrable (F i) MeasureTheory.volume (0:ℝ) 1 :=
      hF i (Finset.mem_insert_self i s)
    have hs : ∀ j ∈ s, IntervalIntegrable (F j) MeasureTheory.volume (0:ℝ) 1 :=
      fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hsum : IntervalIntegrable (fun t => ∑ j ∈ s, F j t) MeasureTheory.volume (0:ℝ) 1 :=
      intervalIntegrable_sum_pointwise s hs
    have hcongr : Set.EqOn (fun t => ∑ j ∈ insert i s, F j t)
        (fun t => F i t + ∑ j ∈ s, F j t) (Set.uIcc (0:ℝ) 1) := fun t _ => by
      show ∑ j ∈ insert i s, F j t = F i t + ∑ j ∈ s, F j t
      rw [Finset.sum_insert hi]
    calc (∫ t in (0:ℝ)..1, ∑ j ∈ insert i s, F j t)
        = ∫ t in (0:ℝ)..1, (F i t + ∑ j ∈ s, F j t) :=
          intervalIntegral.integral_congr hcongr
      _ = (∫ t in (0:ℝ)..1, F i t) + (∫ t in (0:ℝ)..1, ∑ j ∈ s, F j t) :=
          intervalIntegral.integral_add hFi hsum
      _ = ∑ j ∈ insert i s, (∫ t in (0:ℝ)..1, F j t) := by
          rw [Finset.sum_insert hi, ← ih hs]

/-- Pulling a complex scalar out of a band integral. -/
theorem integral_indicator_smul (c : ℂ) (g : ℝ → ℂ) (r : ℝ) (hcg : Continuous g)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (intervalIntegral (fun t => B.indicator (fun t => c * g (r * t)) t) (0:ℝ) 1
        MeasureTheory.volume)
      = c * (intervalIntegral (fun t => B.indicator (fun t => g (r * t)) t) (0:ℝ) 1
        MeasureTheory.volume) := by
  rw [intervalIntegral.integral_congr
    (f := fun t => B.indicator (fun t => c * g (r * t)) t)
    (g := fun t => c * B.indicator (fun t => g (r * t)) t)
    (by intro t _; by_cases ht : t ∈ B <;> simp [ht])]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact MeasureTheory.integral_const_mul c _

/-- The diagonal term `K(0) = Re ∫_B 1` is nonnegative. -/
theorem K_zero_nonneg {B : Set ℝ} (hB : MeasurableSet B) :
    0 ≤ (intervalIntegral (fun t => B.indicator (fun _ => GE 0) t) (0:ℝ) 1
      MeasureTheory.volume).re := by
  have hcongr : Set.EqOn (fun t => B.indicator (fun _ => GE 0) t)
      (fun t => ((B.indicator (fun _ => (1:ℝ)) t : ℝ) : ℂ)) (Set.uIcc (0:ℝ) 1) := by
    intro t _
    by_cases ht : t ∈ B
    · simp [ht, GE_zero]
    · simp [ht]
  rw [intervalIntegral.integral_congr
    (f := fun t => B.indicator (fun _ => GE 0) t)
    (g := fun t => ((B.indicator (fun _ => (1:ℝ)) t : ℝ) : ℂ)) hcongr,
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_complex_ofReal, Complex.ofReal_re]
  exact MeasureTheory.integral_nonneg (fun t => by by_cases ht : t ∈ B <;> simp [ht])

/-- On a diagonal pair the oscillatory factor is `K(0)`. -/
theorem K_diag (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) {k1 k2 : ℕ} (hn : k1 + k2 = n) :
    (intervalIntegral
      (fun t => B.indicator (fun t => GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t) (0:ℝ) 1
        MeasureTheory.volume)
      = intervalIntegral (fun t => B.indicator (fun _ => GE 0) t) (0:ℝ) 1
        MeasureTheory.volume := by
  have h0 : ((k1:ℝ) + (k2:ℝ) - (n:ℝ)) = 0 := by
    have hcast : ((k1:ℝ) + (k2:ℝ)) = (n:ℝ) := by rw [← Nat.cast_add, hn]
    rw [hcast, sub_self]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [h0, zero_mul]

/-- **Off-diagonal expansion.** The band integral expands into the double sum with the
real weights `GW k1 * GW k2` outside the real part of each oscillatory band integral. -/
theorem JG_offdiag_expand (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    JG n B = ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
        (GW k1 * GW k2 : ℝ) * (intervalIntegral
          (fun t => B.indicator (fun t => GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
            (0:ℝ) 1 MeasureTheory.volume).re := by
  have hmain : (intervalIntegral (fun t => B.indicator (fG n) t) (0:ℝ) 1 MeasureTheory.volume)
      = ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
          ((GW k1 * GW k2 : ℝ) : ℂ) * (intervalIntegral
            (fun t => B.indicator (fun t => GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
              (0:ℝ) 1 MeasureTheory.volume) := by
    have hint : Set.EqOn (B.indicator (fG n))
        (fun t => ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
          B.indicator (fun t => ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
        (Set.uIcc (0:ℝ) 1) := by
      intro t _
      show B.indicator (fG n) t = ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
        B.indicator (fun t => ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t
      by_cases ht : t ∈ B
      · rw [Set.indicator_apply (B) (fG n) t, if_pos ht]
        simp only [fG]
        rw [pointwise_expand n t]
        refine Finset.sum_congr rfl fun k1 _ => Finset.sum_congr rfl fun k2 _ => ?_
        rw [Set.indicator_apply, if_pos ht]
      · rw [Set.indicator_apply (B) (fG n) t, if_neg ht]
        refine Eq.symm (Finset.sum_eq_zero fun k1 _ => Finset.sum_eq_zero fun k2 _ => ?_)
        rw [Set.indicator_apply, if_neg ht]
    rw [intervalIntegral.integral_congr hint]
    rw [intervalIntegral_sum
      (fun k1 t => ∑ k2 ∈ Finset.range (n+1),
        B.indicator (fun t => ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
      (Finset.range (n+1))
      (fun k1 _ => intervalIntegrable_sum_pointwise (Finset.range (n+1))
        (fun k2 _ => intervalIntegrable_indicator_continuous
          (continuous_const_mul_GE _ _) hB))]
    refine Finset.sum_congr rfl fun k1 _ => ?_
    rw [intervalIntegral_sum
      (fun k2 t => B.indicator
        (fun t => ((GW k1 * GW k2 : ℝ) : ℂ) * GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
      (Finset.range (n+1))
      (fun k2 _ => intervalIntegrable_indicator_continuous
        (continuous_const_mul_GE _ _) hB)]
    refine Finset.sum_congr rfl fun k2 _ => ?_
    exact integral_indicator_smul ((GW k1 * GW k2 : ℝ) : ℂ) GE ((k1:ℝ) + (k2:ℝ) - (n:ℝ))
      continuous_GE hB
  unfold JG
  rw [hmain, Complex.re_sum]
  refine Finset.sum_congr rfl fun k1 _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k2 _ => ?_
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- **Floor from the off-diagonal bound.** The diagonal contribution is nonnegative
(`R(n) · K(0) ≥ 0`), so the floor `−εn ≤ JG n B` holds as soon as the off-diagonal
signed series (diagonal pairs zeroed out) is bounded below by `−εn`. -/
theorem floor_of_offdiag (n : ℕ) {B : Set ℝ} (hB : MeasurableSet B) {ε : ℝ} (hε : 0 < ε)
    (hoff : -ε * n ≤ ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
        (if k1 + k2 = n then 0 else (GW k1 * GW k2 : ℝ)) *
          (intervalIntegral
            (fun t => B.indicator (fun t => GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
              (0:ℝ) 1 MeasureTheory.volume).re) :
    -ε * n ≤ JG n B := by
  have hge : ∑ k1 ∈ Finset.range (n+1), ∑ k2 ∈ Finset.range (n+1),
      (if k1 + k2 = n then 0 else (GW k1 * GW k2 : ℝ)) *
        (intervalIntegral
          (fun t => B.indicator (fun t => GE (((k1:ℝ) + (k2:ℝ) - (n:ℝ)) * t)) t)
            (0:ℝ) 1 MeasureTheory.volume).re
      ≤ JG n B := by
    rw [JG_offdiag_expand n hB]
    refine Finset.sum_le_sum fun k1 _ => Finset.sum_le_sum fun k2 _ => ?_
    by_cases h : k1 + k2 = n
    · rw [if_pos h, K_diag n hB h, zero_mul]
      exact mul_nonneg (mul_nonneg (GW_nonneg k1) (GW_nonneg k2)) (K_zero_nonneg hB)
    · rw [if_neg h]
  linarith

end OffDiag

/-!
### Route 2: character mean-square dilution

The engine for the "character mean-square (L²) → pointwise transfer" route over the
medium-modulus band: summing `‖∑_χ c_χ χ(a)‖²` over all residue classes `a mod q`
dilutes a single exceptional character by a factor `φ(q)` (Dirichlet character
orthogonality). Together with the signed-pair coefficient bound
`‖τ(χ⁻¹)τ(ψ⁻¹)G_q(χψ,−n)/φ(q)²‖ ≤ √(dχ dψ)/φ(q)` this isolates the remaining
large-sieve / zero-free-strip input as an explicit hypothesis.
-/
section Route2
open scoped ComplexConjugate
open scoped Classical
open Finset MulChar

/-- `(‖z‖ : ℂ)² = z * conj z` unfolds to the real norm square via `re`. -/
theorem norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  have h1 : ‖z‖ ^ 2 = (z.re * z.re + z.im * z.im : ℝ) := RCLike.norm_sq_eq_def_ax z
  rw [h1, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- A Dirichlet character value at `a` conjugates to the inverse character at `a`. -/
theorem conj_char_apply_eq_inv {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    conj (χ a) = χ⁻¹ a := by
  rw [MulChar.inv_apply_eq_inv']
  by_cases ha : IsUnit a
  · have h1 : ‖χ a‖ = 1 := by
      rw [← ha.unit_spec]
      exact χ.unit_norm_eq_one ha.unit
    have hnz : χ a ≠ 0 := by
      intro hc
      rw [hc] at h1
      simp at h1
    have hz : (χ a) * conj (χ a) = (χ a) * (χ a)⁻¹ := by
      rw [RCLike.mul_conj, h1]
      norm_num
      rw [mul_inv_cancel₀ hnz]
    exact mul_left_cancel₀ hnz hz
  · rw [MulCharClass.map_nonunit χ ha, inv_zero, map_zero (starRingEnd ℂ)]

/-- `re (z * k) = re z * k` for a natural scalar. -/
theorem re_mul_natCast' (z : ℂ) (k : ℕ) : (z * (k : ℂ)).re = z.re * k := by
  rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]

/-- **Character mean-square dilution.** For coefficients `c : DirichletCharacter ℂ q → ℂ`,
`∑_a ‖∑_χ c_χ χ(a)‖² = φ(q) · ∑_χ ‖c_χ‖²`. A single exceptional character carries a
`1/φ(q)` fraction of the total arc mass — the dilution mechanism of the L² route. -/
theorem char_L2_dilution (q : ℕ) [NeZero q] (c : DirichletCharacter ℂ q → ℂ) :
    ∑ a : ZMod q, ‖∑ χ : DirichletCharacter ℂ q, c χ * χ a‖ ^ 2
      = (q.totient : ℝ) * ∑ χ : DirichletCharacter ℂ q, ‖c χ‖ ^ 2 := by
  have hexp : ∀ a : ZMod q, (∑ χ : DirichletCharacter ℂ q, c χ * χ a)
      * conj (∑ ψ : DirichletCharacter ℂ q, c ψ * ψ a)
      = ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
          c χ * conj (c ψ) * ((χ * ψ⁻¹) a) := by
    intro a
    rw [map_sum (starRingEnd ℂ), Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun ψ _ => ?_
    rw [map_mul (starRingEnd ℂ), conj_char_apply_eq_inv, MulChar.mul_apply]
    ring
  have hinner : ∀ χ ψ : DirichletCharacter ℂ q,
      ∑ a : ZMod q, (χ * ψ⁻¹) a = if χ = ψ then ((q.totient : ℂ)) else 0 := by
    intro χ ψ
    by_cases h : χ = ψ
    · subst h
      rw [if_pos rfl, mul_inv_cancel, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
    · rw [if_neg h, MulChar.sum_eq_zero_of_ne_one]
      intro h1
      exact h (mul_inv_eq_one.mp h1)
  have hswap : ∑ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q,
      c χ * conj (c ψ) * ((χ * ψ⁻¹) a)
      = ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q, ∑ a : ZMod q,
          c χ * conj (c ψ) * ((χ * ψ⁻¹) a) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun χ _ => Finset.sum_comm
  have hif : ∀ χ ψ : DirichletCharacter ℂ q,
      c χ * conj (c ψ) * (if χ = ψ then ((q.totient : ℂ)) else 0)
        = if χ = ψ then c χ * conj (c ψ) * ((q.totient : ℂ)) else 0 := by
    intro χ ψ
    by_cases h : χ = ψ <;> simp [h]
  -- main computation
  rw [Finset.sum_congr rfl fun a _ => norm_sq_eq_re_mul_conj (∑ χ : DirichletCharacter ℂ q, c χ * χ a)]
  rw [← Complex.re_sum]
  have hbig : ∑ a : ZMod q, (∑ χ : DirichletCharacter ℂ q, c χ * χ a)
      * conj (∑ ψ : DirichletCharacter ℂ q, c ψ * ψ a)
      = ∑ χ : DirichletCharacter ℂ q, ∑ ψ : DirichletCharacter ℂ q, ∑ a : ZMod q,
          c χ * conj (c ψ) * ((χ * ψ⁻¹) a) := by
    rw [Finset.sum_congr rfl fun a _ => hexp a]
    exact hswap
  rw [hbig]
  rw [Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun ψ _ => by
    rw [← Finset.mul_sum, hinner χ ψ, hif χ ψ]]
  rw [Finset.sum_congr rfl fun χ _ => Finset.sum_ite_eq Finset.univ χ
    (fun ψ => c χ * conj (c ψ) * ((q.totient : ℂ)))]
  simp only [Finset.mem_univ, if_true]
  rw [Complex.re_sum]
  rw [Finset.sum_congr rfl fun χ _ => re_mul_natCast' (c χ * conj (c χ)) q.totient]
  rw [Finset.sum_congr rfl fun χ _ => by rw [(norm_sq_eq_re_mul_conj (c χ)).symm]]
  rw [← Finset.sum_mul, mul_comm]

end Route2

theorem WideRemainderInnerFloor : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor (fun n => remainder n ∩ inner n) := by
  sorry
