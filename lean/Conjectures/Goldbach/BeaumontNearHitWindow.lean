import Mathlib

namespace Conjectures.Goldbach.BeaumontNearHitWindow_aux

/-- With a safety margin, a near resonance at index `k` can only occur at `k = 1`:
`k ≤ 0` contradicts `r < p + q`, and `k ≥ 2` contradicts `p + q + r < 2 * n`. -/
private theorem resonance_index_eq_one
    {n p q r : ℕ} {k : ℤ} (hn : 0 < n) (hr : r < p + q)
    (hsum : p + q + r < 2 * n)
    (hres : |(p:ℤ) + (q:ℤ) - k * (n:ℤ)| ≤ (r:ℤ)) :
    k = 1 := by
  have hnn : (0:ℤ) ≤ (n:ℤ) := by omega
  have hr' : ((r:ℤ)) < (p:ℤ) + (q:ℤ) := by omega
  have hsum' : (p:ℤ) + (q:ℤ) + (r:ℤ) < 2 * (n:ℤ) := by omega
  have hupp : (p:ℤ) + (q:ℤ) - k * (n:ℤ) ≤ (r:ℤ) := (abs_le.mp hres).2
  have hlow : -((r:ℤ)) ≤ (p:ℤ) + (q:ℤ) - k * (n:ℤ) := (abs_le.mp hres).1
  have hk1 : 1 ≤ k := by
    by_cases hk0 : k ≤ 0
    · have hkn : k * (n:ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hk0 hnn
      linarith
    · omega
  have hk2 : k ≤ 1 := by
    by_cases hkbig : 2 ≤ k
    · have hkn : 2 * (n:ℤ) ≤ k * (n:ℤ) := by
        have hpos : (0:ℤ) ≤ (k - 2) * (n:ℤ) := mul_nonneg (by omega) hnn
        linarith
      linarith
    · omega
  omega

end Conjectures.Goldbach.BeaumontNearHitWindow_aux

theorem Conjectures.Goldbach.BeaumontNearHitWindow : ∀ (n p q r : ℕ) (k : ℤ), 0 < n → 2*r < n → r < p+q → p+q+r < 2*n → |(p:ℤ)+(q:ℤ)-k*(n:ℤ)| ≤ (r:ℤ) → |(p:ℤ)+(q:ℤ)-(n:ℤ)| ≤ (r:ℤ) := by
  intro n p q r k hn _h2r hr hsum hres
  have hk : k = 1 :=
    Conjectures.Goldbach.BeaumontNearHitWindow_aux.resonance_index_eq_one hn hr hsum hres
  subst hk
  simpa using hres
