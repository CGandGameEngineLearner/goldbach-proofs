import Conjectures.Goldbach.EstermannAlmostAllPolylog

open Conjectures.Goldbach.EstermannAlmostAllPolylog_aux.Cover

theorem Conjectures.Cuts.Task4acd3c8c41d8e044f6b1f87f : (∀ (x1 : ℕ), ∃ (x2 : ℕ), ∀ (x3 : ℕ), x2 ≤ x3 → ↑{x5 ∈ Finset.Ioc (x3 / (2 : ℕ)) x3 | (6 : ℕ) ∣ x5 ∧ {x6 ∈ Finset.range (x5 + (1 : ℕ)) | Nat.Prime x6 ∧ Nat.Prime (x5 - x6)}.card = (0 : ℕ)}.card * Real.log ↑x3 ^ x1 ≤ ↑x3 / (2 : ℝ)) := by
  classical
  intro A
  obtain ⟨N, hN⟩ := exc_polylog ((A + 1 : ℕ) : ℝ) (by positivity)
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2)
  refine ⟨max 8 (max N M), ?_⟩
  intro X hX
  have h8 : 8 ≤ X := (le_max_left _ _).trans hX
  have hNM : max N M ≤ X := (le_max_right _ _).trans hX
  have hlog : 2 ≤ Real.log (X : ℝ) := hM X ((le_max_right _ _).trans hNM)
  have hpos : 0 < Real.log (X : ℝ) := by linarith
  let S := (Finset.Ioc (X / 2) X).filter (fun n => 6 ∣ n ∧ (myreps n).card = 0)
  change (S.card : ℝ) * Real.log (X : ℝ) ^ A ≤ (X : ℝ) / 2
  have hsub : S ⊆ exc X := by
    intro n hn
    obtain ⟨hI, hd, hz⟩ := Finset.mem_filter.mp hn
    obtain ⟨hl, hu⟩ := Finset.mem_Ioc.mp hI
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega,
      (even_iff_two_dvd.mpr (dvd_trans (by decide : 2 ∣ 6) hd)), hz⟩
  have hc : (S.card : ℝ) ≤ ((exc X).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  have h := hc.trans (hN X ((le_max_left _ _).trans hNM))
  rw [Real.rpow_neg hpos.le, Real.rpow_natCast, ← div_eq_mul_inv] at h
  have hprod := (le_div_iff₀ (pow_pos hpos (A + 1))).mp h
  rw [pow_succ, ← mul_assoc] at hprod
  have hnon : 0 ≤ (S.card : ℝ) * Real.log (X : ℝ) ^ A := by positivity
  nlinarith [mul_nonneg hnon (sub_nonneg.mpr hlog)]
