import Mathlib
import Conjectures.JoshiAbc.RadicalSupport

theorem Conjectures.Cuts.Taskb523666e3e3b1ec353be8a50 :
    ∀ (x1 x2 : ℕ), (0 : ℕ) < x1 → (0 : ℕ) < x2 → x1.Coprime x2 → (x1 * x2 * (x1 + x2)).primeFactors.prod id = x1.primeFactors.prod id * x2.primeFactors.prod id * (x1 + x2).primeFactors.prod id := by
  intro x1 x2 hx1 hx2 hcop
  exact Conjectures.JoshiAbc.RadicalSupport x1 x2 hx1 hx2 hcop
