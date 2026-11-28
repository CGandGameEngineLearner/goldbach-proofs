import Mathlib

open Finset Filter Topology

namespace AperyEnclosure

private noncomputable def term (n : ℕ) : ℝ := 1 / ((n + 1 : ℕ) : ℝ)^3
private noncomputable def correction (c : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ) * (n + 1) + c)

private theorem steps (n : ℕ) (hn : 23 ≤ n) :
    correction 1 n - correction 1 (n + 1) ≤ term n ∧
    term n ≤ correction (99/100) n - correction (99/100) (n + 1) := by
  have h : (23 : ℝ) ≤ n := by exact_mod_cast hn
  unfold correction term
  push_cast
  constructor <;> field_simp <;> nlinarith [sq_nonneg ((n : ℝ) - 1)]

private theorem vanishes (c : ℝ) (hc : 0 < c) :
    Tendsto (correction c) atTop (𝓝 0) := by
  apply tendsto_const_nhds.div_atTop
  apply tendsto_atTop.2
  intro b
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop b] with n hn
  nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]

private theorem enclosure :
    1.20205690 ≤ ∑' n, term n ∧ (∑' n, term n) ≤ 1.20205692 := by
  let partialSum (n : ℕ) := ∑ j ∈ range n, term j
  have hsum : Summable term :=
    (summable_nat_add_iff (f := fun j : ℕ => 1 / (j : ℝ)^3) 1).2
      (Real.summable_one_div_nat_pow.mpr (by norm_num))
  have hpartial : Tendsto partialSum atTop (𝓝 (∑' j, term j)) := hsum.hasSum.tendsto_sum_nat
  have bounds (n : ℕ) (hn : 23 ≤ n) :
      1.20205690 ≤ partialSum n + correction 1 n ∧
      partialSum n + correction (99/100) n ≤ 1.20205692 := by
    induction n, hn using Nat.le_induction with
    | base => norm_num [partialSum, Finset.sum_range_succ, correction, term]
    | succ n hn ih =>
      have h := steps n hn
      have hp : partialSum (n+1) = partialSum n + term n := Finset.sum_range_succ _ _
      rw [hp]
      constructor <;> linarith [h.1, h.2, ih.1, ih.2]
  have limit (c : ℝ) (hc : 0 < c) :
      Tendsto (fun n => partialSum n + correction c n) atTop (𝓝 (∑' j, term j)) := by
    simpa only [add_zero] using hpartial.add (vanishes c hc)
  constructor
  · apply ge_of_tendsto (limit 1 (by norm_num))
    filter_upwards [eventually_ge_atTop 23] with n hn using (bounds n hn).1
  · apply le_of_tendsto (limit (99/100) (by norm_num))
    filter_upwards [eventually_ge_atTop 23] with n hn using (bounds n hn).2

end AperyEnclosure

theorem Conjectures.Cuts.Task866d1277a2f1dde02f2029e1 : (have x1 : ℝ := ∑' (x1 : ℕ), (1 : ℝ) / ↑(x1 + (1 : ℕ)) ^ (3 : ℕ); 0.18403413 ≤ Real.log x1 ∧ Real.log x1 ≤ 0.18403422) := by
  intro z
  have hz : 1.20205690 ≤ z ∧ z ≤ 1.20205692 := AperyEnclosure.enclosure
  constructor
  · apply le_trans _ (Real.log_le_log (by norm_num) hz.1)
    have h := Real.abs_log_sub_add_sum_range_le (x := -0.20205690) (by norm_num) 13
    rw [abs_le] at h
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith [h.1]
  · apply le_trans (Real.log_le_log (by linarith [hz.1]) hz.2) _
    have h := Real.abs_log_sub_add_sum_range_le (x := -0.20205692) (by norm_num) 13
    rw [abs_le] at h
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith [h.2]
