open Lean Elab Command

/-- Inspect parsed syntax, so explicit parentheses and binder boundaries are preserved. -/
private partial def checkIffScope (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | `($lhs ↔ $_rhs) =>
    match lhs with
    | `($_premise → $_result) =>
      throwErrorAt lhs "Parenthesize the intended scope: H → (A ↔ B) or (H → A) ↔ B"
    | _ => pure ()
  | _ => pure ()
  for child in stx.getArgs do
    checkIffScope child

elab "#check_statement_scope " t:term : command => checkIffScope t

#check_statement_scope (True → (True ↔ False))
#check_statement_scope ((True → True) ↔ False)

/-- error: Parenthesize the intended scope: H → (A ↔ B) or (H → A) ↔ B -/
#guard_msgs in
#check_statement_scope (True → True ↔ False)

example : ¬ (∀ n d e : ℕ, 0 < d → 0 < e →
    (∃ p : ℕ, p % d = n % d ∧ p % e = 1 % e) ↔ n % (Nat.gcd d e) = 1 % (Nat.gcd d e)) := by
  intro h
  simpa using h 2 0 3
