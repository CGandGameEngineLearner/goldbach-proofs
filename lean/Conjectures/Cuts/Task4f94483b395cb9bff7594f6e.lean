import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

theorem Conjectures.Cuts.Task4f94483b395cb9bff7594f6e : (∀ (x1 x2 : ℕ) (x3 : Finset ℕ) (x4 : ℕ → Bool), x3 ⊆ Finset.range (42 : ℕ) → {x6 ∈ Finset.Icc x1 x2 | x6 % (42 : ℕ) ∈ x3 ∧ x4 x6 = Bool.true}.card = ∑ x6 ∈ x3, {x7 ∈ Finset.range (x2 / (42 : ℕ) + (1 : ℕ)) | x1 ≤ (42 : ℕ) * x7 + x6 ∧ (42 : ℕ) * x7 + x6 ≤ x2 ∧ x4 ((42 : ℕ) * x7 + x6) = Bool.true}.card) := by
  intro X Y R P hR
  let S := (Finset.Icc X Y).filter (fun n => P n = true)
  have hbase :
      ((Finset.Icc X Y).filter (fun n => n % 42 ∈ R ∧ P n = true)) =
        S.filter (fun n => n % 42 ∈ R) := by
    simp only [S, Finset.filter_filter, and_comm]
  rw [hbase, ← Finset.sum_card_fiberwise_eq_card_filter S R (fun n => n % 42)]
  apply Finset.sum_congr rfl
  intro r hr
  have hr42 : r < 42 := Finset.mem_range.mp (hR hr)
  refine Finset.card_bij (fun n _ => n / 42) ?_ ?_ ?_
  · intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn with ⟨⟨⟨hX, hY⟩, hP⟩, hm⟩
    have he : 42 * (n / 42) + r = n := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by simpa only [he] using And.intro hX (And.intro hY hP)⟩
  · intro n hn m hm he
    simp only [Finset.mem_filter] at hn hm
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨42 * k + r, ?_, by omega⟩
    have hm : (42 * k + r) % 42 = r := by omega
    simp only [S, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨hk.2.1, hk.2.2.1⟩, hk.2.2.2⟩, hm⟩
