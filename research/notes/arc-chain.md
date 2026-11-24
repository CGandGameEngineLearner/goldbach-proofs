# The last four entries are not four independent problems

`research/gaps.json` lists 196 gaps. 111 carry an `ACCEPTED` verdict; four do not.

| gap | role | what it actually is |
|---|---|---|
| `L-goldbach-binary-pointwise-positivity` | `endpoint` | equivalent to binary Goldbach |
| `L-goldbach-dyadic-correlation-floor` | — | strictly stronger than binary Goldbach |
| `L-goldbach-arc-major-floor` | `target` | one number: a lower bound for the major arcs |
| `L-goldbach-arc-minor-saving` | `target` | one number: a lower bound for the minor arcs |

The catalogue presents these as four parallel jobs. They are not parallel. Two of
them are hypotheses, one is a sink, and one is a consequence. What is missing
between them is not a fifth lemma but a chain, and that chain has exactly two
missing links. One of the two is proved in this note.

## The chain

    arc-major-floor ─┐
                     ├─ arc-split ─ arc-coefficient ─ transfer ─→ ∃N, ∀n≥N, conv n > 0
    arc-minor-saving ┘

Write `w k = log k` on primes and `0` elsewhere, `S n w t = Σ_{k≤n} w k · e(k t)`,
`f n t = (S n w t)² · e(−n t)`, and let `arcs n` be the major arcs of the two
targets. Then `major n` and `minor n` are the integrals of `f n` against the
indicator of `arcs n` and of its complement.

* **`arc-split`** — `major n + minor n = ∫₀¹ f n`. Two facts: `arcs n` is
  measurable (a countable union of closed intervals), and the two indicators add
  to `1`. Routine measure theory, no arithmetic.
* **`arc-coefficient`** — `∫₀¹ f n = Σ_{p+q=n} w p · w q`, as a complex number.
  Proved here. This is the only place where the two arc numbers are related to
  the object the endpoint talks about.
* **`transfer`** — if `A ≥ c·n`, `B ≥ −e·n`, `0 < e < c` and `A + B = conv n`,
  then `conv n ≥ (c−e)·n > 0`. Three lines, no analysis.

## Link 2, proved: `arc-coefficient`

    ∫₀¹ (Σ_{k≤n} w k · e(k t))² · e(−n t) dt  =  Σ_{p+q=n} w p · w q

Expand the square into a double sum. Each term is `w p · w q · e((p+q−n) t)`, and
a single Fourier mode integrates to `1` at frequency zero and to `0` at every other
integer frequency, because `exp(2πim) = 1`. Only the terms with `p + q = n`
survive, and since `p, q ≤ n` the inner sum collapses to `q = n − p`.

This is the linear counterpart of `L-goldbach-fourth-energy`, which is already
accepted and gives `∫₀¹ ‖S‖⁴ = Σ_s conv_s²`. The energy version bounds the
convolution in `L²`; the coefficient version *is* the convolution. The catalogue
has the first and not the second, and the second is what the endpoints need.

The statement is registered as `L-goldbach-arc-coefficient` and the proof is in the
appendix. It was elaborated against the pinned toolchain (`lean/lean-toolchain`,
Mathlib as pinned in `lake-manifest.json`) with no errors and no warnings, and
`#print axioms` reports `propext, Classical.choice, Quot.sound` only.

## Link 1, not proved: `arc-split`

`arcs n = {t | ∃ q a, 1 ≤ q ∧ q ≤ Q n ∧ a ≤ q ∧ Coprime a q ∧ |t − a/q| ≤ Q n/(q n)}`
is a countable union of closed intervals, hence measurable, and
`1_{arcs n} + 1_{(arcs n)ᶜ} = 1`. The obligation is `intervalIntegral` additivity
for a measurable set, which is why this is registered as its own gap rather than
folded into the coefficient identity: it is the only measure-theoretic step in the
chain, and keeping it separate keeps the coefficient identity free of measure
theory.

## What each of the four reduces to

**`arc-major-floor` decomposes into three separable jobs, and only the third is
open.**

1. *Archimedean.* With `S` restricted to the arc around `0`, the integral is
   `∫_{−Q/n}^{Q/n} (sin(π(n+1)b)/sin(πb))² db = n + 1 − (truncation loss)` with
   the loss one-sided and at most `n/(2Q)`. No primes, no zeros: it is a statement
   about `Σ_{k≤n} e(kb)` alone. Provable today.
2. *Singular product.* `Π_{p ≤ Q n} (p/(p−1) if p | n else 1 − 1/(p−1)²) ≥ 1` for
   even `n`. Already available from the accepted `series-uniform-floor`; the
   infimum over even `n` is `2·C₂ ≈ 1.3209`.
3. *Uniform error.* `ψ(x; q, a) = x/φ(q) + O(x·exp(−c√log x))` uniformly for
   `q ≤ Q n = log²(n+2)`. This is the Siegel–Walfisz range, i.e. the prime number
   theorem in arithmetic progressions, or GRH. **This, and only this, is the open
   part of the major arc.**

So the major arc does not need anything about the minor arcs, and vice versa. The
two targets really are independent -- which is exactly why proving both of them
still does not give the endpoint without the two links above.

**`arc-minor-saving` does not decompose.** It is one pointwise cancellation bound
on a set of measure `1 − o(1)`. The accepted `L-goldbach-minor-gap-scale`
(`Σ_{p≤n} log²p ≥ 2n`) is the reason: the trivial bound on the minor arcs is an
order of magnitude larger than `n`, so no argument that only uses *sizes* can
reach `o(n)`. That rules out, in one stroke, every route through `fourth-energy`,
`continuous-parseval` and the `integrals` track: those bound `L²` and `L⁴` norms,
which is precisely the information that is insufficient. Sign cancellation has to
enter. The only two weakenings that exist are averaging over `n` (the `exceptions`
track, 14/14 accepted, and it stops at "almost everywhere") and assuming GRH (the
`grh` track, 13/13 accepted). Both are already exhausted; there is no third.

**`dyadic-correlation-floor` is a consequence, not a task.** It asks for
`c·n ≤ conv n` on a dyadic range, which is stronger than positivity. Once
`arc-coefficient` and the transfer exist, the chain gives `(c−e)·n ≤ conv n`, so
this entry is implied by the chain and adding it as a separate target double-counts
the same work.

**`binary-pointwise-positivity` is a sink.** It is equivalent to binary Goldbach:
`conv n > 0` iff `n` has a Goldbach decomposition, because the weights vanish
off the primes and are positive on them. Nothing should be *refined* toward it; it
is what the chain lands on.

## The residual that no entry covers

The chain concludes `∃N, ∀n ≥ N`. The endpoint asks for every even `n ≥ 4`. The
difference is a finite range `4 ≤ n < N`, and `N` is not effective: it is the
maximum of the thresholds in the two targets, and neither target provides a value.
`arc-cutoff-scale` has the same shape -- it asserts `2Q² < n` holds *eventually*,
not from an explicit point.

So even with both targets and both links, the catalogue would prove "all
sufficiently large even numbers". Closing `4 ≤ n < N` needs either an explicit
threshold plus a finite verification, or a separate argument for bounded `n`.
There is no entry for that obligation today. This is the fifth gap, and it is
invisible in the current layout: 115 entries can be accepted and the endpoint still
not follow, because the threshold is where the last step dies.

## Why the answer is not more entries

The verification cone is capped. `outside-guard.mjs` sets `MAX_OUTSIDE = 16`: the
transitive closure of outside modules that a proof may depend on is at most
sixteen files, and the guard refuses the rest. A proof that cites a thousand
lemmas cannot be verified by the authority at all -- not because it is wrong, but
because the checker will not build it.

The cone this problem needs is three deep: two targets, two links, one transfer.
Sixteen is more than enough. A thousand is not "more resolution"; it is
unverifiable by construction. The unit of progress here is a **link**, not a leaf.

## Status

| item | state |
|---|---|
| `arc-coefficient` | **proved** (appendix); registered by this PR |
| `arc-split` | open, routine; registered by this PR |
| `transfer` | three lines of `linarith`; not registered, too small to deserve a slot |
| `arc-major-floor` | open; reduces to PNT in AP (Siegel–Walfisz / GRH) |
| `arc-minor-saving` | open; no known decomposition |
| threshold `4 ≤ n < N` | no entry exists |

The immediate sequence is: merge this, claim `L-goldbach-arc-coefficient`, submit the
appendix as `lean/PEqualNP/Outside/L_goldbach_arc_coefficient.lean`. That is one
new verified link, which is worth more than another hundred leaves.

## Appendix: the proof of `L-goldbach-arc-coefficient`

```lean
import Mathlib

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace ArcCoeff

noncomputable def E (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  rw [E, E, E, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma E_zero : E 0 = 1 := by
  simp [E]

lemma integral_E_int (m : ℤ) : (∫ t in (0:ℝ)..1, E ((m:ℝ) * t)) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [E_zero]
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    have hreal : (2 * Real.pi * (m:ℝ) : ℝ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hm'
    have hC : (((2 * Real.pi * (m:ℝ) : ℝ)) : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hreal) Complex.I_ne_zero
    have hpt : ∀ t : ℝ,
        E ((m:ℝ) * t) = Complex.exp (((((2 * Real.pi * (m:ℝ) : ℝ)) : ℂ) * Complex.I) * (t:ℂ)) := by
      intro t
      rw [E]
      congr 1
      push_cast
      ring
    simp only [hpt]
    rw [integral_exp_mul_complex hC]
    have hexp : Complex.exp (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I) = 1 := by
      rw [show (2 * (Real.pi : ℂ) * (m : ℂ) * Complex.I)
            = (((2 * Real.pi * (m:ℝ) : ℝ)) : ℂ) * Complex.I by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I]
      have h1 : Real.cos (2 * Real.pi * (m:ℝ)) = 1 := by
        have := Real.cos_int_mul_two_pi m
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have h2 : Real.sin (2 * Real.pi * (m:ℝ)) = 0 := by
        have := Real.sin_int_mul_two_pi_sub (0:ℝ) m
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
      simp [h1, h2]
    simp [hexp, hm]

lemma row (n p : ℕ) (hp : p ≤ n) (c : ℕ → ℂ) :
    (∑ q ∈ Finset.range (n+1), (if ((p:ℤ) + (q:ℤ) - (n:ℤ) = 0) then c q else 0)) = c (n - p) := by
  rw [Finset.sum_eq_single (n - p)]
  · have hzero : (p:ℤ) + ((n - p : ℕ) : ℤ) - (n:ℤ) = 0 := by omega
    simp [hzero]
  · intro q hq hne
    have hcond : ¬ ((p:ℤ) + (q:ℤ) - (n:ℤ) = 0) := by
      intro h
      exact hne (by omega)
    simp [hcond]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le n p))) hmem

lemma coefficient (n : ℕ) (w : ℕ → ℝ) :
    (∫ t in (0:ℝ)..1,
        (∑ k ∈ Finset.range (n+1), (w k : ℂ) * E ((k:ℝ) * t))^2 * E (-(n:ℝ) * t))
      = ((∑ p ∈ Finset.range (n+1), w p * w (n - p) : ℝ) : ℂ) := by
  have hsq : ∀ t : ℝ,
      (∑ k ∈ Finset.range (n+1), (w k : ℂ) * E ((k:ℝ) * t))^2 * E (-(n:ℝ) * t)
        = ∑ p ∈ Finset.range (n+1), ∑ q ∈ Finset.range (n+1),
            ((w p : ℂ) * (w q : ℂ)) * E ((((p:ℤ) + (q:ℤ) - (n:ℤ) : ℤ) : ℝ) * t) := by
    intro t
    rw [sq, Finset.sum_mul_sum]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    have hphase : E ((p:ℝ) * t) * E ((q:ℝ) * t) * E (-(n:ℝ) * t)
        = E ((((p:ℤ) + (q:ℤ) - (n:ℤ) : ℤ) : ℝ) * t) := by
      rw [← E_add, ← E_add]
      congr 1
      push_cast
      ring
    calc ((w p : ℂ) * E ((p:ℝ) * t)) * ((w q : ℂ) * E ((q:ℝ) * t)) * E (-(n:ℝ) * t)
        = ((w p : ℂ) * (w q : ℂ))
            * (E ((p:ℝ) * t) * E ((q:ℝ) * t) * E (-(n:ℝ) * t)) := by ring
      _ = ((w p : ℂ) * (w q : ℂ)) * E ((((p:ℤ) + (q:ℤ) - (n:ℤ) : ℤ) : ℝ) * t) := by rw [hphase]
  simp only [hsq]
  rw [Complex.ofReal_sum]
  have hInt : ∀ p ∈ Finset.range (n+1), IntervalIntegrable
      (fun t : ℝ => ∑ q ∈ Finset.range (n+1),
        ((w p : ℂ) * (w q : ℂ)) * E ((((p:ℤ) + (q:ℤ) - (n:ℤ) : ℤ) : ℝ) * t)) volume 0 1 := by
    intro p _
    refine Continuous.intervalIntegrable ?_ 0 1
    simp only [E]
    fun_prop
  rw [intervalIntegral.integral_finsetSum hInt]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
  have hInt2 : ∀ q ∈ Finset.range (n+1), IntervalIntegrable
      (fun t : ℝ => ((w p : ℂ) * (w q : ℂ)) * E ((((p:ℤ) + (q:ℤ) - (n:ℤ) : ℤ) : ℝ) * t)) volume 0 1 := by
    intro q _
    refine Continuous.intervalIntegrable ?_ 0 1
    simp only [E]
    fun_prop
  rw [intervalIntegral.integral_finsetSum hInt2]
  have hval : ∀ q : ℕ,
      (∫ t in (0:ℝ)..1,
          ((w p : ℂ) * (w q : ℂ)) * E ((((p:ℤ) + (q:ℤ) - (n:ℤ) : ℤ) : ℝ) * t))
        = if ((p:ℤ) + (q:ℤ) - (n:ℤ) = 0) then ((w p * w q : ℝ) : ℂ) else 0 := by
    intro q
    rw [intervalIntegral.integral_const_mul, integral_E_int]
    by_cases h : ((p:ℤ) + (q:ℤ) - (n:ℤ)) = 0
    · simp [h]
    · simp [h]
  simp only [hval]
  exact row n p hp' (fun q => ((w p * w q : ℝ) : ℂ))

end ArcCoeff

theorem L_goldbach_arc_coefficient :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I)
    let S := fun (n : ℕ) (w : ℕ → ℝ) (t : ℝ) =>
      Finset.sum (Finset.range (n+1)) (fun k => (w k:ℂ)*E ((k:ℝ)*t))
    ∀ (n : ℕ) (w : ℕ → ℝ),
      intervalIntegral (fun t => (S n w t)^2*E (-(n:ℝ)*t)) (0:ℝ) 1 MeasureTheory.volume
        = ((Finset.sum (Finset.range (n+1)) (fun p => w p * w (n-p)) : ℝ) : ℂ) := by
  dsimp only
  intro n w
  exact ArcCoeff.coefficient n w
```
