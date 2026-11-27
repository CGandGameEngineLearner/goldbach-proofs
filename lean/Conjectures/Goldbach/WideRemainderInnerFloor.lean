import Mathlib
import PEqualNP.Outside.L_goldbach_frontier_medcore_model_floor

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

theorem WideRemainderInnerFloor : let w := fun k : ℕ => if Nat.Prime k then Real.log (k:ℝ) else 0; let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let S := fun (n : ℕ) (u : ℕ → ℝ) (t : ℝ) => Finset.sum (Finset.range (n+1)) (fun k => (u k:ℂ)*E ((k:ℝ)*t)); let Q := fun n : ℕ => (Nat.log 2 (n+2))^2; let arcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n:ℝ)/((q:ℝ)*(n:ℝ))}; let f := fun (n : ℕ) (t : ℝ) => (S n w t)^2*E (-(n:ℝ)*t); let Q₁ := fun n : ℕ => ⌊(n:ℝ)^(1/3:ℝ)⌋₊; let H := fun n : ℕ => 256 * Q₁ n * Q n; let wideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowWideArcs := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (H n:ℝ)/((q:ℝ)*(n:ℝ))}; let lowPart := fun n : ℕ => lowWideArcs n \ arcs n; let remainder := fun n : ℕ => (wideArcs n \ arcs n) \ lowPart n; let inner := fun n : ℕ => {t : ℝ | ∃ q a : ℕ, 1≤q ∧ q≤Q₁ n ∧ a≤q ∧ Nat.Coprime a q ∧ |t-(a:ℝ)/(q:ℝ)| ≤ (Q n : ℝ) * (n : ℝ)^(1/6 : ℝ) / ((q:ℝ)*(n:ℝ))}; let J := fun (n : ℕ) (A : Set ℝ) => (intervalIntegral (fun t => A.indicator (f n) t) (0:ℝ) 1 MeasureTheory.volume).re; let floor := fun (A : ℕ → Set ℝ) => ∀ e : ℝ, 0 < e → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → -(e * (n:ℝ)) ≤ J n (A n); floor (fun n => remainder n ∩ inner n) := by
  sorry
