import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Finset
open scoped Topology

namespace MertensZeta

private noncomputable def term (n : ℕ) : ℝ := 1 / ((n+1 : ℕ) : ℝ)^3
private noncomputable def total : ℝ := ∑' n, term n
private noncomputable def upto (N : ℕ) : ℝ := ∑ n ∈ range N, term n
private noncomputable def upper (N : ℕ) : ℝ := upto N + ((1 : ℝ)/N)^2

private lemma summable_terms : Summable term :=
  (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3))

private lemma bracket (N : ℕ) (hN : 0 < N) :
    upto N ≤ total ∧ total ≤ upper N := by
  have U : Tendsto upper atTop (𝓝 total) := by
    change Tendsto (fun n : ℕ => upto n + ((1 : ℝ)/n)^2) _ _
    simpa only [upto, total, zero_pow (by decide : 2 ≠ 0), add_zero] using
      summable_terms.hasSum.tendsto_sum_nat.add ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2)
  have step (k : ℕ) (hk : 0 < k) : upper (k+1) ≤ upper k := by
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    simp only [upper, upto, sum_range_succ, term, Nat.cast_add_one]
    field_simp
    nlinarith
  refine ⟨summable_terms.sum_le_tsum _ (fun n _ => by dsimp [term]; positivity), ?_⟩
  apply le_of_tendsto U
  filter_upwards [eventually_ge_atTop N] with k hk
  induction k, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ j hj ih => exact (step j (hN.trans_le hj)).trans ih

private def truncSum : ℕ → ℕ
  | 0 => 0
  | n+1 => truncSum n + 10^14 / (n+1)^3

private lemma rounded (n : ℕ) :
    (truncSum n : ℝ) ≤ (10^14 : ℝ) * upto n ∧
    (10^14 : ℝ) * upto n ≤ (truncSum n : ℝ) + n := by
  induction n with
  | zero => simp [truncSum, upto]
  | succ n ih =>
    let q : ℕ := 10^14 / (n+1)^3
    have hn : 0 < ((n : ℝ) + 1)^3 := by positivity
    have hleft : (q : ℝ) ≤ (10^14 : ℝ) / (n+1)^3 := by
      rw [le_div_iff₀ hn]
      exact_mod_cast Nat.div_mul_le_self (10^14) ((n+1)^3)
    have hright : (10^14 : ℝ) / (n+1)^3 ≤ (q : ℝ) + 1 := by
      rw [div_le_iff₀ hn, mul_comm]
      exact_mod_cast (Nat.lt_mul_div_succ (10^14) (pow_pos (Nat.succ_pos n) 3)).le
    change (↑(truncSum n + q) : ℝ) ≤ _ ∧ _ ≤ (↑(truncSum n + q) : ℝ) + _
    have he : upto (n+1) = upto n + 1 / ((n:ℝ)+1)^3 := by
      simp [upto, term, sum_range_succ]
    simp only [he, Nat.cast_add, Nat.cast_one, mul_add, mul_one_div]
    constructor <;> linarith only [ih.1,ih.2,hleft,hright]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem truncated : truncSum 8192 = 120205689566938 := by decide +kernel

private lemma zeta_bracket : (1.20205689 : ℝ) ≤ total ∧ total ≤ (1.20205692 : ℝ) := by
  obtain ⟨hA,hB⟩ := bracket 8192 (by decide)
  obtain ⟨hF,hG⟩ := rounded 8192
  rw [truncated] at hF hG
  norm_num only [upper, Nat.cast_ofNat] at hB hF hG
  constructor <;> linarith only [hA,hB,hF,hG]

theorem log_bounds : (0.18403413 : ℝ) ≤ Real.log total ∧ Real.log total ≤ 0.18403422 := by
  obtain ⟨hL,hU⟩ := zeta_bracket
  have hz : 0 < total := lt_of_lt_of_le (by norm_num) hL
  constructor
  · apply le_trans _ (Real.log_le_log (by norm_num : (0:ℝ) < 1.20205689) hL)
    have h := Real.sum_range_le_log_div (x := 20205689 / 220205689) (by norm_num) (by norm_num) 5
    norm_num [sum_range_succ] at h ⊢
    linarith
  · apply le_trans (Real.log_le_log hz hU)
    have h := Real.log_div_le_sum_range_add (x := 20205692 / 220205692) (by norm_num) (by norm_num) 5
    norm_num [sum_range_succ] at h ⊢
    linarith

end MertensZeta

theorem Conjectures.Cuts.Task866d1277a2f1dde02f2029e1 : (have x1 : ℝ := ∑' (x1 : ℕ), (1 : ℝ) / ↑(x1 + (1 : ℕ)) ^ (3 : ℕ); 0.18403413 ≤ Real.log x1 ∧ Real.log x1 ≤ 0.18403422) := by
  exact MertensZeta.log_bounds
