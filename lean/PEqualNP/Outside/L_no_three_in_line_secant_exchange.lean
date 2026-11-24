import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_secant_exchange :
    let d := fun (a b c : ℤ × ℤ) => (b.1-a.1)*(c.2-a.2)-(b.2-a.2)*(c.1-a.1); let ok := fun (S : Finset (ℤ × ℤ)) => ∀ a∈S, ∀ b∈S, ∀ c∈S, a≠b → b≠c → a≠c → d a b c≠0; ∀ (S : Finset (ℤ × ℤ)) (r x y : ℤ × ℤ), let T := S.erase r; ok S → x≠y → (∀ a∈T,∀ b∈T,a≠b → d a b x≠0 ∧ d a b y≠0) → (∀ a∈T,d x y a≠0) → ok (insert x (insert y T)) := by
  sorry
