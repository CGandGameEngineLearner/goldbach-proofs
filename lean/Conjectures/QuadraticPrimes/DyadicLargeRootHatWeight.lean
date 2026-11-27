import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Basic

theorem Conjectures.QuadraticPrimes.DyadicLargeRootHatWeight :
    ∀ Y n : ℕ, ((Finset.Ico Y (2*Y)).filter fun x => x<n ∧ n≤2*x).card = min (2*Y) n - max Y ((n+1)/2) := by
  intro Y n
  have h : (Finset.Ico Y (2*Y)).filter fun x => x<n ∧ n≤2*x = Finset.Ico (max Y ((n+1)/2)) (min (2*Y) n) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_filter]
    omega
  rw [h, Nat.card_Ico]
