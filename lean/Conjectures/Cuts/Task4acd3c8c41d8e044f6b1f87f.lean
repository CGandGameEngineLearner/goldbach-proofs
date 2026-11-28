import Mathlib
import Conjectures.Goldbach.EstermannAlmostAllPolylog

theorem Conjectures.Cuts.Task4acd3c8c41d8e044f6b1f87f : (∀ (x1 : ℕ), ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → ↑{x5 ∈ Finset.Ioc (x3 / (2 : ℕ)) x3 | (6 : ℕ) ∣ x5 ∧ {x6 ∈ Finset.range (x5 + (1 : ℕ)) | Nat.Prime x6 ∧ Nat.Prime (x5 - x6)}.card = (0 : ℕ)}.card * Real.log ↑x3 ^ x1 ≤ ↑x3 / (2 : ℝ)) := by
  intro A
  obtain ⟨hE, -⟩ := Conjectures.Goldbach.EstermannAlmostAllPolylog
  obtain ⟨X₁, hX₁⟩ := hE ((A : ℝ) + 1) (by positivity)
  refine ⟨max X₁ 8, fun X hX => ?_⟩
  have hE' := hX₁ X (le_trans (le_max_left _ _) hX)
  have hX8 : 8 ≤ X := le_trans (le_max_right _ _) hX
  have hsub : (Finset.Ioc (X / 2) X).filter (fun n => (6 : ℕ) ∣ n ∧
      {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card = (0 : ℕ)) ⊆
      (Finset.range (X + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card = 0) := by
    intro n hn
    obtain ⟨hnI, hn6, hn0⟩ := Finset.mem_filter.mp hn
    rw [Finset.mem_Ioc] at hnI
    rw [Finset.mem_filter]
    refine ⟨?_, ?_, even_iff_two_dvd.mpr ((dvd_mul_right 2 3).trans hn6), hn0⟩
    · rw [Finset.mem_range]
      omega
    · omega
  have hcard := Finset.card_le_card hsub
  have hreal : ({x5 ∈ Finset.Ioc (X / (2 : ℕ)) X | (6 : ℕ) ∣ x5 ∧
        {x6 ∈ Finset.range (x5 + (1 : ℕ)) | Nat.Prime x6 ∧ Nat.Prime (x5 - x6)}.card = (0 : ℕ)}.card : ℝ) ≤
      (((Finset.range (X + 1)).filter (fun n => 4 ≤ n ∧ Even n ∧
        {p ∈ Finset.range (n + 1) | Nat.Prime p ∧ Nat.Prime (n - p)}.card = 0)).card : ℝ) := by
    exact_mod_cast hcard
  have hexp : Real.exp 2 ≤ 8 := by
    have h1 := Real.exp_one_lt_d9.le
    have hpos : 0 ≤ Real.exp (1 : ℝ) := (Real.exp_pos 1).le
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith
  have hXr : (8 : ℝ) ≤ X := by exact_mod_cast hX8
  have hlog2 : 2 ≤ Real.log (X : ℝ) := by
    calc 2 = Real.log (Real.exp 2) := (Real.log_exp 2).symm
      _ ≤ Real.log 8 := Real.log_le_log (Real.exp_pos 2) hexp
      _ ≤ Real.log X := Real.log_le_log (by norm_num) hXr
  have hl : 0 < Real.log (X : ℝ) := by linarith
  have hfinal : ({x5 ∈ Finset.Ioc (X / (2 : ℕ)) X | (6 : ℕ) ∣ x5 ∧
        {x6 ∈ Finset.range (x5 + (1 : ℕ)) | Nat.Prime x6 ∧ Nat.Prime (x5 - x6)}.card = (0 : ℕ)}.card : ℝ) *
        (Real.log (X : ℝ))^A ≤
      (X : ℝ) * (Real.log (X : ℝ))^(-((A : ℝ) + 1)) * (Real.log (X : ℝ))^A :=
    (mul_le_mul_of_nonneg_right hreal (pow_nonneg hl.le A)).trans
      (mul_le_mul_of_nonneg_right hE' (pow_nonneg hl.le A))
  rw [mul_assoc] at hfinal
  have hkey : (Real.log (X : ℝ))^(-((A : ℝ) + 1)) * (Real.log (X : ℝ))^A = 1 / Real.log (X : ℝ) := by
    rw [show (Real.log (X : ℝ))^A = (Real.log (X : ℝ))^((A : ℝ)) by simp,
      ← Real.rpow_add hl, show (-((A : ℝ) + 1)) + (A : ℝ) = -1 by ring, Real.rpow_neg_one]
    ring
  rw [hkey] at hfinal
  have hdiv : (X : ℝ) * (1 / Real.log (X : ℝ)) = (X : ℝ) / Real.log (X : ℝ) := by
    field_simp
  rw [hdiv] at hfinal
  refine hfinal.trans ?_
  rw [div_le_div_iff₀ hl (by norm_num)]
  nlinarith [hl, (Nat.cast_nonneg X : (0 : ℝ) ≤ (X : ℝ))]
