/-
Copyright (c) 2022 Abby J. Goldberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abby J. Goldberg, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Group.Basic

/-!
# additive_combination Tactic

In this file, the `additive_combination` tactic is created. This tactic, which
works over `AddGroup`s, attempts to simplify the target by creating an additive
combination of a list of equalities and subtracting it from the target.

This is a local (port) copy of `PrimeNumberTheoremAnd/Tactic/AdditiveCombination.lean`
from the PNT+ project.  Upstream it is derived from `Mathlib.Tactic.LinearCombination`
and reused the lemma names of the (long removed) `LinearCombination.Lemmas` file; here
the handful of one-line lemmas it needs are stated locally, so that the file depends on
nothing but `Mathlib.Tactic.Abel`.

## Implementation Notes

This tactic works by creating a weighted sum of the given equations with the
given coefficients.  Then, it subtracts the right side of the weighted sum
from the left side so that the right side equals 0, and it does the same with
the target.  Afterwards, it sets the goal to be the equality between the
left-hand side of the new goal and the left-hand side of the new weighted sum.
Lastly, calls a normalization tactic on this target.

## References

* <https://leanprover.zulipchat.com/#narrow/stream/239415-metaprogramming-.2F.20tactics/topic/Linear.20algebra.20tactic/near/213928196>

-/

namespace Mathlib.Tactic.LinearCombinationPrime
open Lean Elab Meta Term

variable {α β : Type*}

theorem pf_add_c [Add α] {a b : α} (p : a = b) (c : α) : a + c = b + c := p ▸ rfl

theorem c_add_pf [Add α] {b c : α} (p : b = c) (a : α) : a + b = a + c := p ▸ rfl

theorem add_pf [Add α] {a₁ b₁ a₂ b₂ : α} (p₁ : a₁ = b₁) (p₂ : a₂ = b₂) :
    a₁ + a₂ = b₁ + b₂ := p₁ ▸ p₂ ▸ rfl

theorem pf_sub_c [Sub α] {a b : α} (p : a = b) (c : α) : a - c = b - c := p ▸ rfl

theorem c_sub_pf [Sub α] {b c : α} (p : b = c) (a : α) : a - b = a - c := p ▸ rfl

theorem sub_pf [Sub α] {a₁ b₁ a₂ b₂ : α} (p₁ : a₁ = b₁) (p₂ : a₂ = b₂) :
    a₁ - a₂ = b₁ - b₂ := p₁ ▸ p₂ ▸ rfl

theorem neg_pf [Neg α] {a b : α} (p : a = b) : -a = -b := p ▸ rfl

theorem pf_smul_c [SMul α β] {a b : α} (p : a = b) (c : β) : a • c = b • c := p ▸ rfl

theorem c_smul_pf [SMul α β] {b c : β} (p : b = c) (a : α) : a • b = a • c := p ▸ rfl

theorem smul_pf [SMul α β] {a₁ b₁ : α} (p₁ : (a₁ : α) = b₁) {a₂ b₂ : β} (p₂ : a₂ = b₂) :
    a₁ • a₂ = b₁ • b₂ := p₁ ▸ p₂ ▸ rfl

/-- The central reduction lemma: a proof `p` of `a = b` reduces a goal `a' = b'` to
`a' + b = b' + a`. -/
theorem eq_of_add [AddGroup α] {a a' b b' : α} (p : a = b)
    (H : a' + b = b' + a) : a' = b' := by
  calc a' = a' + b - b := by rw [add_sub_cancel_right]
    _ = b' + a - b := by rw [H]
    _ = b' := by rw [p, add_sub_cancel_right]

/-- Result of `expandAdditiveCombo`, either a proof of an equality or a value. -/
inductive Expanded
  /-- A proof of `a = b`. -/
  | proof (pf : Syntax.Term)
  /-- A value, equivalently a proof of `c = c`. -/
  | const (c : Syntax.Term)

/--
Performs macro expansion of an additive combination expression,
using `+`/`-`/`•` on equations and values.
* `.proof p` means that `p` is a syntax corresponding to a proof of an equation.
  For example, if `h : a = b` then `expandAdditiveCombo (2 • h)` returns
  `.proof (c_smul_pf 2 h)` which is a proof of `2 • a = 2 • b`.
* `.const c` means that the input expression is not an equation but a value.
-/
partial def expandAdditiveCombo (ty : Expr) (stx : Syntax.Term) : TermElabM Expanded := withRef stx do
  match stx with
  | `(($e)) => expandAdditiveCombo ty e
  | `($e₁ + $e₂) => do
    match ← expandAdditiveCombo ty e₁, ← expandAdditiveCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ + $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_add_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_add_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(add_pf $p₁ $p₂)
  | `($e₁ - $e₂) => do
    match ← expandAdditiveCombo ty e₁, ← expandAdditiveCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ - $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_sub_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_sub_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(sub_pf $p₁ $p₂)
  | `(-$e) => do
    match ← expandAdditiveCombo ty e with
    | .const c => .const <$> `(-$c)
    | .proof p => .proof <$> ``(neg_pf $p)
  | `(← $e:term) => do
    match ← expandAdditiveCombo ty e with
    | .const c => return .const c
    | .proof p => .proof <$> ``(Eq.symm $p)
  | `($e₁ • $e₂) => do
    match ← expandAdditiveCombo ty e₁, ← expandAdditiveCombo ty e₂ with
    | .const c₁, .const c₂ => .const <$> ``($c₁ • $c₂)
    | .proof p₁, .const c₂ => .proof <$> ``(pf_smul_c $p₁ $c₂)
    | .const c₁, .proof p₂ => .proof <$> ``(c_smul_pf $p₂ $c₁)
    | .proof p₁, .proof p₂ => .proof <$> ``(smul_pf $p₁ $p₂)
  | e =>
    -- We have the expected type from the goal, so we can fully synthesize this leaf node.
    withSynthesize do
      -- It is OK to use `ty` as the expected type even if `e` is a proof.
      -- The expected type is just a hint.
      let c ← withSynthesizeLight <| Term.elabTerm e ty
      if (← whnfR (← inferType c)).isAppOfArity ``Eq 3 then
        .proof <$> c.toSyntax
      else
        .const <$> c.toSyntax

/-- Implementation of `additive_combination`. -/
def elabAdditiveCombination (tk : Syntax)
    (norm? : Option Syntax.Tactic) (input : Option Syntax.Term) : Tactic.TacticM Unit :=
  Tactic.withMainContext do
  let ty ← Tactic.getMainTarget
  unless ty.isAppOfArity ``Eq 3 do
    throwError "'additive_combination' only proves equalities"
  let elTy := ty.getArg! 0
  let p ← match input with
  | none => `(Eq.refl 0)
  | some e =>
    match ← expandAdditiveCombo elTy e with
    | .const c => `(Eq.refl $c)
    | .proof p => pure p
  let norm := norm?.getD
    (Unhygienic.run <| withRef tk `(tactic| ((try simp only [smul_add, smul_sub]); abel)))
  Term.withoutErrToSorry <| Tactic.evalTactic <| ← withFreshMacroScope <|
    `(tactic| (refine eq_of_add $p ?a; case' a => $norm:tactic))

/--
`additive_combination` attempts to simplify the target by creating an additive combination
of a list of equalities and subtracting it from the target.
The tactic will create an additive combination by adding the equalities together from
left to right, so the order of the input hypotheses does matter.

Note: The left and right sides of all the equalities should have the same
type, and the coefficients should also have this type.  There must be
instances of `Add`, `Sub`, `Neg` and `SMul` for this type as appropriate.

* The input `e` in `additive_combination e` is an additive combination of proofs of equalities,
  given as a sum/difference of coefficients (scalar-)multiplied with expressions.
  The coefficients may be arbitrary expressions.
  The expressions can be arbitrary proof terms proving equalities.
  Most commonly they are hypothesis names `h1, h2, ...`.
* `additive_combination (norm := tac) e` runs the "normalization tactic" `tac`
  on the subgoal(s) after constructing the additive combination.
  * The default normalization tactic is `abel`, which closes the goal or fails.
  * To avoid normalization entirely, use `skip` as the normalization tactic.

Example Usage:
```
example (a b : ℤ) (h1 : a = 1) (h2 : b = 2) : a + b = 3 := by
  additive_combination h1 + h2

example (x y : ℤ) (h1 : x - y = 2) (h2 : y = 3) : x = 5 := by
  additive_combination h1 + h2
```
-/
/- The `(norm := $tac)` syntax says to use `tac` as a normalization postprocessor for
`additive_combination`.  The default normalizer is `abel`. -/
syntax additiveNormStx := atomic(" (" &"norm" " := ") withoutPosition(tactic) ")"

syntax (name := AdditiveCombination) "additive_combination"
  (additiveNormStx)? (ppSpace colGt term)? : tactic
elab_rules : tactic
  | `(tactic| additive_combination%$tk $[(norm := $tac)]? $(e)?) =>
    elabAdditiveCombination tk tac e

end Mathlib.Tactic.LinearCombinationPrime

example (a b : ℤ) (h1 : a = 1) (h2 : b = 2) : a + b = 3 := by
  additive_combination h1 + h2

example (a : ℤ) (h1 : a = 1) : -a = -1 := by
  additive_combination -h1

example (V : Type) [AddCommGroup V] (x y : V) (h1 : x + y = 0) : x = -y := by
  additive_combination h1

example (a b : ℤ) (h1 : a - b = 2) (h2 : b = 3) : a = 5 := by
  additive_combination h1 + h2

example (a b : ℤ) (h1 : a = b) : a + 1 = 1 + b := by
  additive_combination (norm := abel) h1
