import Mathlib

namespace ZetaThreeCertificate

-- Each term is rounded down to an integer multiple of 1 / scale.
private def scaledPrefix (scale : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => scaledPrefix scale n + scale / (n + 1)^3

private theorem scaledBounds (scale n : ℕ) :
    (scaledPrefix scale n : ℝ) ≤ scale * (∑ j ∈ Finset.range n, 1 / ((j + 1 : ℕ) : ℝ)^3) ∧
    scale * (∑ j ∈ Finset.range n, 1 / ((j + 1 : ℕ) : ℝ)^3) ≤ (scaledPrefix scale n : ℝ) + n := by
  induction n with
  | zero => simp [scaledPrefix]
  | succ n ih =>
    let k := (n + 1)^3
    have hk : 0 < k := by dsimp [k]; positivity
    have hl : ((scale / k : ℕ) : ℝ) ≤ (scale : ℝ) / k := Nat.cast_div_le
    have hu : (scale : ℝ) / k ≤ ((scale / k : ℕ) : ℝ) + 1 := by
      apply (div_le_iff₀ (Nat.cast_pos.mpr hk : (0 : ℝ) < k)).mpr
      exact_mod_cast (by simpa only [Nat.mul_comm k] using (Nat.lt_mul_div_succ scale hk).le :
        scale ≤ (scale / k + 1) * k)
    rw [Finset.sum_range_succ, mul_add, scaledPrefix]
    simp only [Nat.cast_add, Nat.cast_succ, mul_one_div] at *
    dsimp only [k] at hl hu
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hl hu
    constructor <;> linarith [ih.1, ih.2]

theorem prefix_bounds :
    (1.20205499953 : ℝ) ≤ (∑ n ∈ Finset.range 512, 1 / ((n + 1 : ℕ) : ℝ)^3) ∧
    (∑ n ∈ Finset.range 512, 1 / ((n + 1 : ℕ) : ℝ)^3) ≤ (1.20205499954 : ℝ) := by
  have hsum : scaledPrefix 1000000000000000 512 = 1202054999532377 := by
    decide +kernel
  obtain ⟨hl, hu⟩ := scaledBounds 1000000000000000 512
  rw [hsum] at hl hu
  norm_num only [Nat.cast_ofNat] at hl hu
  constructor <;> linarith

private theorem between_cubes (x : ℝ) (hx : 0 < x) :
    1 / (x + 1)^3 ≤ 1 / (2*x^2) - 1 / (2*(x+1)^2) ∧
    1 / (2*x^2) - 1 / (2*(x+1)^2) ≤ 1 / x^3 := by
  constructor <;> field_simp <;> nlinarith [sq_nonneg x]

private noncomputable def halfSquare (n : ℕ) : ℝ := (1/2 : ℝ) * (1 / (n : ℝ)^2)

private theorem shifted_square_summable (k : ℕ) :
    Summable (fun n : ℕ => halfSquare (n + k)) := by
  apply (summable_nat_add_iff k).mpr
  exact (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left (1/2)

private theorem difference_hasSum (k : ℕ) :
    HasSum (fun n : ℕ => halfSquare (n+k) - halfSquare ((n+1)+k)) (halfSquare k) := by
  have h := shifted_square_summable k
  have h' := (summable_nat_add_iff 1).mpr h
  have ht := h.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, zero_add] at ht
  have hd := h.hasSum.sub h'.hasSum
  convert hd using 1
  linarith

theorem tail_bounds :
    let partialSum := ∑ n ∈ Finset.range 512, (1 : ℝ) / ((n + 1 : ℕ) : ℝ)^3
    let total := ∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ)^3
    partialSum + 1/(2*513^2) ≤ total ∧ total ≤ partialSum + 1/(2*512^2) := by
  let f := fun n : ℕ => (1 : ℝ) / ((n+1 : ℕ) : ℝ)^3
  have hf : Summable f :=
    (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 3))
  have ht := ((summable_nat_add_iff 512).mpr hf).hasSum
  have hl : halfSquare 513 ≤ ∑' n : ℕ, f (n+512) := by
    apply hasSum_le _ (difference_hasSum 513) ht
    intro n
    have h := (between_cubes ((n : ℝ) + 513) (by positivity)).2
    unfold halfSquare f
    push_cast
    simp only [one_div, mul_inv_rev] at h ⊢
    convert h using 1 <;> ring
  have hu : (∑' n : ℕ, f (n+512)) ≤ halfSquare 512 := by
    apply hasSum_le _ ht (difference_hasSum 512)
    intro n
    have h := (between_cubes ((n : ℝ) + 512) (by positivity)).1
    unfold halfSquare f
    push_cast
    simp only [one_div, mul_inv_rev] at h ⊢
    convert h using 1
    ring
  change (∑ n ∈ Finset.range 512, f n) + _ ≤ (∑' n, f n) ∧
    (∑' n, f n) ≤ (∑ n ∈ Finset.range 512, f n) + _
  rw [← hf.sum_add_tsum_nat_add 512]
  refine ⟨add_le_add (le_refl _) ?_, add_le_add (le_refl _) ?_⟩
  · convert hl using 1
    norm_num [halfSquare]
  · convert hu using 1
    norm_num [halfSquare]

theorem log_bounds (x : ℝ) (hl : 1.20205689 ≤ x) (hu : x ≤ 1.20205691) :
    0.18403413 ≤ Real.log x ∧ Real.log x ≤ 0.18403422 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hl
  constructor
  · apply (Real.le_log_iff_exp_le hx).2
    refine (Real.exp_bound' (x := 0.18403413) (by norm_num) (by norm_num)
      (n := 7) (by decide)).trans (le_trans ?_ hl)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  · apply (Real.log_le_iff_le_exp hx).2
    refine hu.trans (le_trans ?_ (Real.sum_le_exp_of_nonneg
      (x := 0.18403422) (by norm_num) 7))
    norm_num [Finset.sum_range_succ, Nat.factorial]

end ZetaThreeCertificate

theorem Conjectures.Cuts.Task866d1277a2f1dde02f2029e1 : (have x1 : ℝ := ∑' (x1 : ℕ), (1 : ℝ) / ↑(x1 + (1 : ℕ)) ^ (3 : ℕ); 0.18403413 ≤ Real.log x1 ∧ Real.log x1 ≤ 0.18403422) := by
  intro z
  obtain ⟨hpl, hpu⟩ := ZetaThreeCertificate.prefix_bounds
  obtain ⟨htl, htu⟩ := ZetaThreeCertificate.tail_bounds
  apply ZetaThreeCertificate.log_bounds
  · dsimp only [z]
    linarith
  · dsimp only [z]
    linarith
