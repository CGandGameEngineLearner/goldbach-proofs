import Mathlib

/-- The strong Goldbach conjecture as a proposition. -/
def StrongGoldbach : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n →
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- Positive prime-only log mass detects precisely the existence of a prime pair. -/
theorem strongGoldbach_iff_primeMass : StrongGoldbach ↔
    ∀ n : ℕ, 4 ≤ n → Even n →
      let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
      0 < Finset.sum (Finset.range (n + 1)) (fun p => w p * w (n - p)) := by
  let w : ℕ → ℝ := fun k => if Nat.Prime k then Real.log (k : ℝ) else 0
  have pos {k : ℕ} (hk : Nat.Prime k) : 0 < w k := by
    simp only [w, if_pos hk]
    exact Real.log_pos (by exact_mod_cast hk.one_lt)
  have nn (k : ℕ) : 0 ≤ w k := by
    by_cases h : Nat.Prime k
    · exact (pos h).le
    · simp [w, h]
  constructor
  · intro h n hn he
    obtain ⟨p, q, hp, hq, hpq⟩ := h n hn he
    change 0 < ∑ i ∈ Finset.range (n+1), w i * w (n-i)
    have hm : p ∈ Finset.range (n+1) := Finset.mem_range.mpr (by omega)
    have hd : n-p = q := by omega
    have hpos : 0 < w (n-p) := by simpa only [hd] using pos hq
    exact lt_of_lt_of_le (mul_pos (pos hp) hpos)
      (Finset.single_le_sum (f := fun i => w i * w (n-i))
        (fun i _ => mul_nonneg (nn i) (nn (n-i))) hm)
  · intro h n hn he
    have hs := h n hn he
    change 0 < ∑ i ∈ Finset.range (n+1), w i * w (n-i) at hs
    by_contra noPair
    have hz : (∑ i ∈ Finset.range (n+1), w i * w (n-i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      by_cases hp : Nat.Prime i
      · have hq : ¬ Nat.Prime (n-i) := fun hq => noPair ⟨i,n-i,hp,hq,by omega⟩
        simp [w,hq]
      · simp [w,hp]
    linarith
