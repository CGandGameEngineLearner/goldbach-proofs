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


theorem WideRemainderInnerFloor : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor (fun n => remainder n ∩ inner n) := by
  sorry
