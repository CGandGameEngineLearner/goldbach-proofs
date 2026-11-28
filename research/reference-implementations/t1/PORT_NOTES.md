# PORT_NOTES — porting `kimihiro64/bombieri-vinogradov` to our Lean 4.36 / Mathlib

**Result: `BombieriVinogradov.SiegelWalfisz.siegel_walfisz` compiles in our environment,
axioms `[propext, Classical.choice, Quot.sound]`, and the whole 730-module import
closure builds. The glue file `dg/P33_sw_implies_hchi.lean` derives the per-character
Siegel–Walfisz input `DgBmorP33.per_character_siegelWalfisz` and hence
`DgTargetT1.T1` (`DgBmorP33.T1_discharged`), both also with axioms
`[propext, Classical.choice, Quot.sound]`.**

---

## 1. How the build works

Module roots (`LEAN_PATH`, in order):

1. `goldbach-work/lean/.lake/build/lib/lean` (+ every `.lake/packages/*/.lake/build/lib/lean`)
2. `vendor/pnt-work/src`
3. `vendor/pnt-work/lib`  (the `Architect` stub)
4. `vendor/bv/src`
5. `vendor/bv/extra`      (files fetched from other repos: PNT+ tactic, Robin1984)
6. `dg`, `dg/oleans`      (only needed for `P33`)

Scripts (all under `vendor/bv/`):

* **`mkbuild.ps1`** — walks the import graph from
  `BombieriVinogradov.Assembly.SiegelWalfisz.Main`, resolves each module to a file in
  the roots above (Mathlib modules are assumed to have oleans), writes a topological
  build order to `build_order.txt` and the closure list to `closure_full.txt`.
* **`build_par.ps1`** — builds `build_order.txt` with N parallel `lean.exe` processes
  (`-Jobs 9`), skipping files whose `.olean` already exists and only spawning a file
  once all of its *local* imports have oleans. Per-file output goes to
  `errlog/<module>.txt`. `-SkipFile` temporarily excludes modules.
* **`build_one.ps1`** — rebuild individual files (`-Files a.lean,b.lean` or
  `-ListFile list.txt`); used while fixing a batch of errors.
* **`addsetapply.ps1`** — inserts one line after the import block of the listed files
  (see error class (1) below).

Compile flags (the original hand recipe):

```
lean.exe -DautoImplicit=false -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3
         -DmaxHeartbeats=4000000 -DmaxRecDepth=10000 -o <file>.olean <file>.lean
```

Closure size: **730 local modules** = 643 `BombieriVinogradov.*`
+ 81 `PrimeNumberTheoremAnd.*` + 4 `Robin1984.*`
+ 1 `PrimeNumberTheoremAnd.Tactic.AdditiveCombination` + 1 `Architect`;
plus 247 Mathlib modules.

Final state (2026-11-28 09:2x):

```
$ build_par.ps1 -Jobs 9
done=730 failed=0 blocked=0 total=730
```

Verification transcript (final state):

```
$ lean.exe probe_p33.lean          # dg/probe_p33.lean
'DgBmorP33.per_character_siegelWalfisz' depends on axioms: [propext, Classical.choice, Quot.sound]
'DgBmorP33.T1_discharged' depends on axioms: [propext, Classical.choice, Quot.sound]
'BombieriVinogradov.SiegelWalfisz.siegel_walfisz' depends on axioms: [propext, Classical.choice, Quot.sound]

$ lean.exe probe_sw.lean           # dg/probe_sw.lean
'BombieriVinogradov.SiegelWalfisz.siegel_walfisz' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Staleness check: for all 730 closure modules the `.olean` is newer than its `.lean`
source (0 stale), so the state is consistent.

Note: the driver marks success by "olean produced ∧ no `: error` in the output",
*not* by the process exit code (PowerShell's `Start-Process -PassThru` does not
reliably populate `ExitCode` for redirected non-`-Wait` processes).
It also tends to need 2–3 consecutive invocations to unblock the last few levels
(state updates happen after the spawn scan); just re-run it.

---

## 2. API drift we had to fix (error classes)

Our Mathlib is newer than bv's pinned one, and in two respects it is **structurally
different**, which drives most of the work.

### (0) `Set` is a structure, not a function  ← biggest class
`Mathlib/Data/Set/Defs.lean` in our snapshot:

```lean
structure Set (α : Type u) where
  ofPred ::
  protected Mem : α → Prop
```

So `(someSet) x` (applying a set as a predicate — used all over bv/PNT+) no longer
elaborates: *"Function expected at `Icc 0 delta` … this term has type `Set ℝ`"*.

**Fix** (mechanical, one line per affected file, inserted by `addsetapply.ps1`
right after the import block):

```lean
instance (A : Type*) : CoeFun (Set A) (fun _ => A -> Prop) := { coe := Set.Mem }
```

With this instance both directions work (`(s) x` and `h : x ∈ s` are interchangeable,
because `CoeFun.coe s x` unfolds to `s.Mem x`, i.e. `x ∈ s`).
(Note `:= Set.Mem` does **not** elaborate — the instance needs the structure literal
`{ coe := Set.Mem }`.)

Files that needed it: `Helpers/Nat/BadPrimePowerCover`,
`Helpers/ComplexAnalysis/RectangleInverseSquare`,
`Helpers/RealAnalysis/{LogOverOnePlusAbsIntegral,LogOverOnePlusAbsContinuity,OneDivAbsIntegral,PositiveIntervalSplit}`,
`Proof/SiegelWalfisz/ExplicitFormula/{Exceptional/RealDifferenceQuotient,Contour/ZeroAvoidance,Contour/LFunctionNonvanishing,Residue/Poles/BoundaryDisjoint,Residue/CandidateValues,Residue/CandidateValueSum,PerronError/Optimize/HorizontalStrip,Perron/CircleValue,Perron/RightArcGeometry,Cutoff/DifferenceIndices,Cutoff/ValuePartition,Cutoff/ExceptionalValuePartition,Horizontal/TwoSidedZeroHeightSelection}`,
`Assembly/SiegelWalfisz/ExplicitFormula/HorizontalIntegrandTermContinuity`,
`ZeroFree/CompletedZeroValue`.

Related: `Union (Finset α)` is *not* an instance in this Mathlib (only the `∪`
notation is available), so `Union.union a b` fails to synthesize.
**Fix:** write `(· ∪ ·) a b` (or `a ∪ b`). Files: `Residue/CandidateValues`,
`Residue/CandidateValueSum`, `Cutoff/ValuePartition`, `Cutoff/ExceptionalValuePartition`,
`Horizontal/TwoSidedZeroHeightSelection`, `Helpers/RealAnalysis/PositiveIntervalSplit`.

### (1) `logDeriv_mul` / `logDeriv_prod` are about *pointwise* products
They are stated for `f * g` (Pi multiplication); bv/PNT+ often apply them to
`logDeriv (fun z => f z * g z)`, which no longer keyed-matches — and trying to
unify `(∏ i ∈ s, f i)` with `fun z => ∏ i ∈ s, f i z` is a **non-pattern
unification that loops** (it produced the three "20M heartbeats" timeouts, see (8)).
**Fix:** use `logDeriv_fun_mul` / `logDeriv_fun_prod` (same argument order:
`x`, nonzero hypotheses, differentiability hypotheses).
Files: `PrimeNumberTheoremAnd/IEANTN/HadamardLogDerivative`,
`ZeroFree/{CompletedProductLogDerivative,LevelCorrectionEulerProduct,PrincipalLevelCorrectionLogDerivativeBound}`.

### (2) `DifferentiableAt.ofReal_cpow_const` gained an explicit exponent argument
It is now `variable (c)` ⇒ `c : ℂ` is an *explicit* first argument and the `c ≠ 0`
hypothesis is gone: `differentiableAt_id.ofReal_cpow_const (-s) (h : t ≠ 0)`.
File: `Helpers/DirichletCharacter/CpowDerivative`.

### (3) `Continuous.isOpen_preimage` + `.mem_nhds` no longer unifies a set-comprehension goal
`(Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds h` leaves the set
metavariable unsolved (the expected type `{z | 0 < z.re} ∈ 𝓝 s` is now a `Set`
structure literal, so higher-order unification gets stuck).
**Fix:** state the open set directly, matching the constant in the goal:
`(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h` for `0 < re`, and
`(isOpen_lt (continuous_const : Continuous fun _ : Complex => (1 : ℝ)) Complex.continuous_re).mem_nhds h`
for `1 < re`.
Files: `ZeroFree/{CompletedProductLogDerivative,CompletedLFunctionOrder,CompletedConjugation,LFunctionConjugation,PrincipalHighStripLogDerivativeBound}`,
`Helpers/DirichletCharacter/AbelIntegralLFunction`, `SiegelProduct/Cauchy/LFunctionBlockEquality`,
`extra/Robin1984/NicolasLandau/XiLogDerivative`.

### (4) `norm_num at h` now normalises *through* addition
`h : 1 + 2 ≤ K + 2` was rewritten to `1 ≤ K`, so the following `exact h` failed.
**Fix:** `simpa using h` (or `omega`). File: `Helpers/RealAnalysis/LogQuadraticAbsorption`.

### (5) `positivity` on `|t| + 1 ≠ 0` after `Continuous.div` / `Continuous.log`
The side-condition goal is the *unfolded* Cauchy-reals `abs` term
(`{ cauchy := Quotient.map₂ (fun x1 x2 => x1 ⊔ x2) ⋯ } + 1 ≠ 0`), which
`positivity` and `linarith` cannot see through.
**Fix:** `change (abs t + 1 : Real) ≠ 0; positivity`.
Files: `Helpers/RealAnalysis/{LogOverOnePlusAbsContinuity,OneDivAbsIntegral}`.

### (6) `congr 1` now closes goals it used to leave
`congr 1; · simpa using hPow` → *"No goals to be solved"*.
**Fix:** `first | simpa using hPow | congr 1`. File: `ZeroFree/GammaFactorConjugation`.

### (7) `noncomputable` needed for `def`s mentioning a metric instance
`def siegelCauchyCircle : Set ℂ := sphere 2 (3/2)` (and `ball`) now need
`noncomputable def`. Files: `SiegelProduct/Cauchy/{Geometry,AnalyticDomain}`.

### (8) Heartbeat timeouts (three files, all one-liners)
`ZeroFree/LevelCorrectionEulerProduct`, `ZeroFree/PrincipalLevelCorrectionLogDerivativeBound`,
`ExplicitFormula/PerronSeries/Interchange` hit the 4M-heartbeat limit — and even
20M heartbeats / 13 minutes did not finish them. The cause is class (1): the
`logDeriv_prod` lambda-vs-Pi-product unification, plus (for `Interchange`) the
implicit-continuous-map argument of
`intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm`.
**Fix:** `logDeriv_fun_prod`, and for `Interchange` supply the arguments explicitly:

```lean
  exact intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (f := fun n : Nat => perronSeriesContinuousMap chi hx n hc)
    (a := -T) (b := T)
    (summable_norm_restrict_perronSeriesContinuousMap chi hx hc)
```

All three then compile in seconds. (Do **not** just raise `maxHeartbeats`.)

### (9) `HasDerivAt.comp` / `Polynomial.differentiableAt` shapes
`((Complex.hasDerivAt_exp e).comp z (P.hasDerivAt z)).differentiableAt` no longer
elaborates (`Polynomial.differentiableAt` is a value, not a function of the point).
**Fix:** `by fun_prop`. File: `ZeroFree/CompletedLogDerivativeZeroSum`.

### (10) `mul_le_mul_of_nonneg_left` + `simpa` on `1/x` vs `x / y`
In `ExplicitFormula/Centered/UnitPerronTermBound` the goal is
`Λ n * (1 / n^c * min …) ≤ Λ n / n^c`; `simpa using hInner` produced a term whose
`LE ℝ` instance / unfolded Cauchy `inv` did not match the goal's.
**Fix:** do the algebra explicitly:

```lean
      calc ArithmeticFunction.vonMangoldt n * (1 / (n : Real) ^ c * min 1 (…))
          <= ArithmeticFunction.vonMangoldt n * (1 / (n : Real) ^ c) :=
            mul_le_mul_of_nonneg_left hInner
              (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        _ = ArithmeticFunction.vonMangoldt n / (n : Real) ^ c := by ring
```

### (11) Module-root shadowing for `PrimeNumberTheoremAnd.*`
Lean resolves `PrimeNumberTheoremAnd.Tactic.AdditiveCombination` to
`vendor/pnt-work/src/...` **because that root already contains the parent directory
`PrimeNumberTheoremAnd/Tactic/`**, and then reports the missing olean *there*.
So a module that lives under an existing PNT+ directory must be placed in
`vendor/pnt-work/src` (not in `extra`). Files moved there for this reason:

* `PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean`
* `PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannXiDivisorZeros.lean`
  (fetched from `kimihiro64/Robin1984`, path
  `lean-eval/riemann_hypothesis_iff_lagarias_elementary_criterion/Submission/...`;
  the `Submission.` import prefix had to be stripped)

### (12) Fetched files
`gh api ... > file` in PowerShell 5.1 writes **UTF-16LE**; every file under
`vendor/bv/extra/Robin1984` had to be re-encoded to UTF-8.

---

## 3. `additive_combination` (PNT+ tactic) — local reimplementation

`vendor/pnt-work/src/PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean`
(identical copy kept at `vendor/bv/extra/PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean`)
imports only `Mathlib.Tactic.Abel` + `Mathlib.Algebra.Group.Basic`.

Upstream imported `Mathlib.Tactic.LinearCombinationPrime`, which does not exist in our
Mathlib. We restated the handful of one-line lemmas it needs (`pf_add_c`, `c_add_pf`,
`add_pf`, `pf_sub_c`, `c_sub_pf`, `sub_pf`, `neg_pf`, `pf_smul_c`, `c_smul_pf`,
`smul_pf`) and proved the central reduction `eq_of_add` over `[AddGroup α]`
(`IsRightCancelAdd` is *not* derivable for e.g. `ℚ` with the imports this file has, so
`eq_of_add` is stated over `AddGroup`). Nothing in the bv closure actually *calls*
`additive_combination`; two files only `import` it
(`Proof/SiegelWalfisz/ExplicitFormula/Perron/{LeftRectangle,RightRectangle}`).
The file ends with five working `example`s (doc-test). No `sorry`.

---

## 4. `dg/P33_sw_implies_hchi.lean` (the glue)

```lean
theorem DgBmorP33.characterChebyshevSum_eq_psiChi :
    BombieriVinogradov.SiegelWalfisz.characterChebyshevSum n χ = DgBmorM8a.psiChi χ n

theorem DgBmorP33.psiChiR_bound :   -- rate halved, constant unchanged, X = exp 10
    ‖DgBmorM8a.psiChiR χ x‖ ≤ C * x * Real.exp (-((a / 2) * Real.sqrt (Real.log x)))

theorem DgBmorP33.per_character_siegelWalfisz :
    ∃ C c X : ℝ, 0 < C ∧ 0 < c ∧ 0 < X ∧
      ∀ (m : ℕ) [NeZero m], 3 ≤ m → m ≤ 105 →
        ∀ χ : DirichletCharacter ℂ m, χ ≠ 1 → ∀ x : ℝ, X ≤ x →
          ‖DgBmorM8a.psiChiR χ x‖ ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x)))

theorem DgBmorP33.T1_discharged : DgTargetT1.T1 :=
  DgBmorP17.T1_of_per_character per_character_siegelWalfisz
```

Idea: bv's theorem is at *natural* endpoints (`Σ_{n≤x}`, `x : ℕ`), ours
(`psiChiR`) at real endpoints with `⌊x⌋₊`. `psiChiR χ x = psiChi χ ⌊x⌋₊` is
definitional; for `x ≥ e^{10}` one has `n = ⌊x⌋₊ ≥ x/2`, hence
`log n ≥ log x / 4` and `√(log x)/2 ≤ √(log n)`, so the exponential factor is
bounded by `exp(-(a/2)·√log x)` — **rate halved, constant unchanged**.
`N ≤ 105 ≤ 5^5 ≤ (log n)^5` gives bv's modulus hypothesis with `A = 5`, and
`X = exp 10`.

`#print axioms` for all three of `siegel_walfisz`, `per_character_siegelWalfisz`,
`T1_discharged`: `[propext, Classical.choice, Quot.sound]`.

---

## 5. Remaining gaps / things a human should know

1. All 730 closure modules compile, but the build is **not** reproducible from
   scratch by one command: the driver needs 2–3 invocations because a file is only
   spawned once its deps' oleans exist and the loop can stop one level early
   (see §1). A simple fix would be to re-scan after updating states.
2. `-Jobs 9` is a pragmatic choice (16 cores, ~18 GB RAM); some bv files are heavy.
3. The three "slow" files of class (8) are fixed semantically, not by raising limits —
   the `maxHeartbeats 20000000` lines we added experimentally were removed again.
4. `vendor/pnt-work/src` was modified in exactly two places (the two modules of
   class (11)); everything else is in `vendor/bv/`.
5. `vendor/bv/extra` now also contains a `Robin1984/` tree (3 files) fetched with
   `gh api`, plus the `PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean` copy.
6. Not attempted: making `BombieriVinogradov.lean` (their full root module) compile;
   only the `SiegelWalfisz` closure was in scope.
