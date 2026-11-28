import Mathlib

theorem Conjectures.Cuts.Taskc7fea2c4c3799c095daf5d5a : (by
  classical
  exact ∀ (U : Finset ℕ) (a b : ℕ → ℕ),
    (∑ n ∈ U, a n*b n)^2 ≤ (U.filter (fun n => 0<a n ∧ 0<b n)).card * ∑ n ∈ U, (a n*b n)^2) := by
  classical
  intro U a b
  let V := U.filter (fun n => 0<a n ∧ 0<b n)
  have hm (k : ℕ) (hk : k ≠ 0) : (∑ n ∈ V, (a n*b n)^k) = ∑ n ∈ U, (a n*b n)^k := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hn hv
    have hn' : ¬(0<a n ∧ 0<b n) := fun h => hv (Finset.mem_filter.mpr ⟨hn,h⟩)
    have hz : a n=0 ∨ b n=0 := by omega
    rcases hz with ha|hb
    · simp [ha,hk]
    · simp [hb,hk]
  have cs := sq_sum_le_card_mul_sum_sq (s:=V) (f:=fun n => a n*b n)
  have first := hm 1 (by decide)
  simp only [pow_one] at first
  rw [first,hm 2 (by decide)] at cs
  exact cs
