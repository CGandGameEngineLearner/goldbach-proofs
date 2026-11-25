import Mathlib

namespace PEqualNP.Outside

abbrev goodRough (n : ℕ) : Prop := ∃ p ∈ ({3,5,7,11,31,43,61,79,149,197} : Finset ℕ), ∀ q ∈ ({2,3,5,7,11,13} : Finset ℕ), ((n+30030-p)%30030) % q ≠ 0

lemma roughCoprime (n p : ℕ) (hpS : p ∈ ({3,5,7,11,31,43,61,79,149,197} : Finset ℕ)) (hmod : ∀ q ∈ ({2,3,5,7,11,13} : Finset ℕ), ((n+30030-p)%30030) % q ≠ 0) : Nat.Coprime ((n+30030-p)%30030) 30030 := by
  have hdvd : ∀ q ∈ ({2,3,5,7,11,13} : Finset ℕ), ¬ q ∣ ((n+30030-p)%30030) := by
    intro q hq hd
    exact hmod q hq (Nat.dvd_iff_mod_eq_zero.mp hd)
  have hc : ∀ q ∈ ({2,3,5,7,11,13} : Finset ℕ), Nat.Prime q → Nat.Coprime ((n+30030-p)%30030) q := by
    intro q hq hpq
    exact ((hpq.coprime_iff_not_dvd).mpr (hdvd q hq)).symm
  have hmul : Nat.Coprime ((n+30030-p)%30030) (2 * (3 * (5 * (7 * (11 * 13))))) := by
    exact (hc 2 (by simp) (by norm_num)).mul_right ((hc 3 (by simp) (by norm_num)).mul_right ((hc 5 (by simp) (by norm_num)).mul_right ((hc 7 (by simp) (by norm_num)).mul_right ((hc 11 (by simp) (by norm_num)).mul_right (hc 13 (by simp) (by norm_num))))))
  rwa [show (30030:ℕ) = 2 * (3 * (5 * (7 * (11 * 13)))) by norm_num] at hmul
lemma roughPart0 : ∀ a' < 1024, Even (1024 * 0 + a') → goodRough (1024 * 0 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 0 + (64 * 0 + i)) → goodRough (1024 * 0 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 0 + t)) → goodRough (1024 * 0 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 0 + (64 * 1 + i)) → goodRough (1024 * 0 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 1 + t)) → goodRough (1024 * 0 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 0 + (64 * 2 + i)) → goodRough (1024 * 0 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 2 + t)) → goodRough (1024 * 0 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 0 + (64 * 3 + i)) → goodRough (1024 * 0 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 3 + t)) → goodRough (1024 * 0 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 0 + (64 * 4 + i)) → goodRough (1024 * 0 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 4 + t)) → goodRough (1024 * 0 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 0 + (64 * 5 + i)) → goodRough (1024 * 0 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 5 + t)) → goodRough (1024 * 0 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 0 + (64 * 6 + i)) → goodRough (1024 * 0 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 6 + t)) → goodRough (1024 * 0 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 0 + (64 * 7 + i)) → goodRough (1024 * 0 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 7 + t)) → goodRough (1024 * 0 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 0 + (64 * 8 + i)) → goodRough (1024 * 0 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 8 + t)) → goodRough (1024 * 0 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 0 + (64 * 9 + i)) → goodRough (1024 * 0 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 9 + t)) → goodRough (1024 * 0 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 0 + (64 * 10 + i)) → goodRough (1024 * 0 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 10 + t)) → goodRough (1024 * 0 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 0 + (64 * 11 + i)) → goodRough (1024 * 0 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 11 + t)) → goodRough (1024 * 0 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 0 + (64 * 12 + i)) → goodRough (1024 * 0 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 12 + t)) → goodRough (1024 * 0 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 0 + (64 * 13 + i)) → goodRough (1024 * 0 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 13 + t)) → goodRough (1024 * 0 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 0 + (64 * 14 + i)) → goodRough (1024 * 0 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 14 + t)) → goodRough (1024 * 0 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 0 + (64 * 15 + i)) → goodRough (1024 * 0 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 0 + (64 * 15 + t)) → goodRough (1024 * 0 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart1 : ∀ a' < 1024, Even (1024 * 1 + a') → goodRough (1024 * 1 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 1 + (64 * 0 + i)) → goodRough (1024 * 1 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 0 + t)) → goodRough (1024 * 1 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 1 + (64 * 1 + i)) → goodRough (1024 * 1 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 1 + t)) → goodRough (1024 * 1 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 1 + (64 * 2 + i)) → goodRough (1024 * 1 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 2 + t)) → goodRough (1024 * 1 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 1 + (64 * 3 + i)) → goodRough (1024 * 1 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 3 + t)) → goodRough (1024 * 1 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 1 + (64 * 4 + i)) → goodRough (1024 * 1 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 4 + t)) → goodRough (1024 * 1 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 1 + (64 * 5 + i)) → goodRough (1024 * 1 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 5 + t)) → goodRough (1024 * 1 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 1 + (64 * 6 + i)) → goodRough (1024 * 1 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 6 + t)) → goodRough (1024 * 1 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 1 + (64 * 7 + i)) → goodRough (1024 * 1 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 7 + t)) → goodRough (1024 * 1 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 1 + (64 * 8 + i)) → goodRough (1024 * 1 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 8 + t)) → goodRough (1024 * 1 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 1 + (64 * 9 + i)) → goodRough (1024 * 1 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 9 + t)) → goodRough (1024 * 1 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 1 + (64 * 10 + i)) → goodRough (1024 * 1 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 10 + t)) → goodRough (1024 * 1 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 1 + (64 * 11 + i)) → goodRough (1024 * 1 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 11 + t)) → goodRough (1024 * 1 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 1 + (64 * 12 + i)) → goodRough (1024 * 1 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 12 + t)) → goodRough (1024 * 1 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 1 + (64 * 13 + i)) → goodRough (1024 * 1 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 13 + t)) → goodRough (1024 * 1 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 1 + (64 * 14 + i)) → goodRough (1024 * 1 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 14 + t)) → goodRough (1024 * 1 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 1 + (64 * 15 + i)) → goodRough (1024 * 1 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 1 + (64 * 15 + t)) → goodRough (1024 * 1 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart2 : ∀ a' < 1024, Even (1024 * 2 + a') → goodRough (1024 * 2 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 2 + (64 * 0 + i)) → goodRough (1024 * 2 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 0 + t)) → goodRough (1024 * 2 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 2 + (64 * 1 + i)) → goodRough (1024 * 2 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 1 + t)) → goodRough (1024 * 2 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 2 + (64 * 2 + i)) → goodRough (1024 * 2 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 2 + t)) → goodRough (1024 * 2 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 2 + (64 * 3 + i)) → goodRough (1024 * 2 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 3 + t)) → goodRough (1024 * 2 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 2 + (64 * 4 + i)) → goodRough (1024 * 2 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 4 + t)) → goodRough (1024 * 2 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 2 + (64 * 5 + i)) → goodRough (1024 * 2 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 5 + t)) → goodRough (1024 * 2 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 2 + (64 * 6 + i)) → goodRough (1024 * 2 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 6 + t)) → goodRough (1024 * 2 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 2 + (64 * 7 + i)) → goodRough (1024 * 2 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 7 + t)) → goodRough (1024 * 2 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 2 + (64 * 8 + i)) → goodRough (1024 * 2 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 8 + t)) → goodRough (1024 * 2 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 2 + (64 * 9 + i)) → goodRough (1024 * 2 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 9 + t)) → goodRough (1024 * 2 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 2 + (64 * 10 + i)) → goodRough (1024 * 2 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 10 + t)) → goodRough (1024 * 2 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 2 + (64 * 11 + i)) → goodRough (1024 * 2 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 11 + t)) → goodRough (1024 * 2 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 2 + (64 * 12 + i)) → goodRough (1024 * 2 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 12 + t)) → goodRough (1024 * 2 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 2 + (64 * 13 + i)) → goodRough (1024 * 2 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 13 + t)) → goodRough (1024 * 2 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 2 + (64 * 14 + i)) → goodRough (1024 * 2 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 14 + t)) → goodRough (1024 * 2 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 2 + (64 * 15 + i)) → goodRough (1024 * 2 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 2 + (64 * 15 + t)) → goodRough (1024 * 2 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart3 : ∀ a' < 1024, Even (1024 * 3 + a') → goodRough (1024 * 3 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 3 + (64 * 0 + i)) → goodRough (1024 * 3 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 0 + t)) → goodRough (1024 * 3 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 3 + (64 * 1 + i)) → goodRough (1024 * 3 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 1 + t)) → goodRough (1024 * 3 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 3 + (64 * 2 + i)) → goodRough (1024 * 3 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 2 + t)) → goodRough (1024 * 3 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 3 + (64 * 3 + i)) → goodRough (1024 * 3 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 3 + t)) → goodRough (1024 * 3 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 3 + (64 * 4 + i)) → goodRough (1024 * 3 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 4 + t)) → goodRough (1024 * 3 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 3 + (64 * 5 + i)) → goodRough (1024 * 3 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 5 + t)) → goodRough (1024 * 3 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 3 + (64 * 6 + i)) → goodRough (1024 * 3 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 6 + t)) → goodRough (1024 * 3 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 3 + (64 * 7 + i)) → goodRough (1024 * 3 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 7 + t)) → goodRough (1024 * 3 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 3 + (64 * 8 + i)) → goodRough (1024 * 3 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 8 + t)) → goodRough (1024 * 3 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 3 + (64 * 9 + i)) → goodRough (1024 * 3 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 9 + t)) → goodRough (1024 * 3 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 3 + (64 * 10 + i)) → goodRough (1024 * 3 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 10 + t)) → goodRough (1024 * 3 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 3 + (64 * 11 + i)) → goodRough (1024 * 3 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 11 + t)) → goodRough (1024 * 3 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 3 + (64 * 12 + i)) → goodRough (1024 * 3 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 12 + t)) → goodRough (1024 * 3 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 3 + (64 * 13 + i)) → goodRough (1024 * 3 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 13 + t)) → goodRough (1024 * 3 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 3 + (64 * 14 + i)) → goodRough (1024 * 3 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 14 + t)) → goodRough (1024 * 3 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 3 + (64 * 15 + i)) → goodRough (1024 * 3 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 3 + (64 * 15 + t)) → goodRough (1024 * 3 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart4 : ∀ a' < 1024, Even (1024 * 4 + a') → goodRough (1024 * 4 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 4 + (64 * 0 + i)) → goodRough (1024 * 4 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 0 + t)) → goodRough (1024 * 4 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 4 + (64 * 1 + i)) → goodRough (1024 * 4 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 1 + t)) → goodRough (1024 * 4 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 4 + (64 * 2 + i)) → goodRough (1024 * 4 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 2 + t)) → goodRough (1024 * 4 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 4 + (64 * 3 + i)) → goodRough (1024 * 4 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 3 + t)) → goodRough (1024 * 4 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 4 + (64 * 4 + i)) → goodRough (1024 * 4 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 4 + t)) → goodRough (1024 * 4 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 4 + (64 * 5 + i)) → goodRough (1024 * 4 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 5 + t)) → goodRough (1024 * 4 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 4 + (64 * 6 + i)) → goodRough (1024 * 4 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 6 + t)) → goodRough (1024 * 4 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 4 + (64 * 7 + i)) → goodRough (1024 * 4 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 7 + t)) → goodRough (1024 * 4 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 4 + (64 * 8 + i)) → goodRough (1024 * 4 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 8 + t)) → goodRough (1024 * 4 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 4 + (64 * 9 + i)) → goodRough (1024 * 4 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 9 + t)) → goodRough (1024 * 4 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 4 + (64 * 10 + i)) → goodRough (1024 * 4 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 10 + t)) → goodRough (1024 * 4 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 4 + (64 * 11 + i)) → goodRough (1024 * 4 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 11 + t)) → goodRough (1024 * 4 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 4 + (64 * 12 + i)) → goodRough (1024 * 4 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 12 + t)) → goodRough (1024 * 4 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 4 + (64 * 13 + i)) → goodRough (1024 * 4 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 13 + t)) → goodRough (1024 * 4 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 4 + (64 * 14 + i)) → goodRough (1024 * 4 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 14 + t)) → goodRough (1024 * 4 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 4 + (64 * 15 + i)) → goodRough (1024 * 4 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 4 + (64 * 15 + t)) → goodRough (1024 * 4 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart5 : ∀ a' < 1024, Even (1024 * 5 + a') → goodRough (1024 * 5 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 5 + (64 * 0 + i)) → goodRough (1024 * 5 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 0 + t)) → goodRough (1024 * 5 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 5 + (64 * 1 + i)) → goodRough (1024 * 5 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 1 + t)) → goodRough (1024 * 5 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 5 + (64 * 2 + i)) → goodRough (1024 * 5 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 2 + t)) → goodRough (1024 * 5 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 5 + (64 * 3 + i)) → goodRough (1024 * 5 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 3 + t)) → goodRough (1024 * 5 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 5 + (64 * 4 + i)) → goodRough (1024 * 5 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 4 + t)) → goodRough (1024 * 5 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 5 + (64 * 5 + i)) → goodRough (1024 * 5 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 5 + t)) → goodRough (1024 * 5 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 5 + (64 * 6 + i)) → goodRough (1024 * 5 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 6 + t)) → goodRough (1024 * 5 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 5 + (64 * 7 + i)) → goodRough (1024 * 5 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 7 + t)) → goodRough (1024 * 5 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 5 + (64 * 8 + i)) → goodRough (1024 * 5 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 8 + t)) → goodRough (1024 * 5 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 5 + (64 * 9 + i)) → goodRough (1024 * 5 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 9 + t)) → goodRough (1024 * 5 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 5 + (64 * 10 + i)) → goodRough (1024 * 5 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 10 + t)) → goodRough (1024 * 5 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 5 + (64 * 11 + i)) → goodRough (1024 * 5 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 11 + t)) → goodRough (1024 * 5 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 5 + (64 * 12 + i)) → goodRough (1024 * 5 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 12 + t)) → goodRough (1024 * 5 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 5 + (64 * 13 + i)) → goodRough (1024 * 5 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 13 + t)) → goodRough (1024 * 5 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 5 + (64 * 14 + i)) → goodRough (1024 * 5 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 14 + t)) → goodRough (1024 * 5 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 5 + (64 * 15 + i)) → goodRough (1024 * 5 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 5 + (64 * 15 + t)) → goodRough (1024 * 5 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart6 : ∀ a' < 1024, Even (1024 * 6 + a') → goodRough (1024 * 6 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 6 + (64 * 0 + i)) → goodRough (1024 * 6 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 0 + t)) → goodRough (1024 * 6 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 6 + (64 * 1 + i)) → goodRough (1024 * 6 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 1 + t)) → goodRough (1024 * 6 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 6 + (64 * 2 + i)) → goodRough (1024 * 6 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 2 + t)) → goodRough (1024 * 6 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 6 + (64 * 3 + i)) → goodRough (1024 * 6 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 3 + t)) → goodRough (1024 * 6 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 6 + (64 * 4 + i)) → goodRough (1024 * 6 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 4 + t)) → goodRough (1024 * 6 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 6 + (64 * 5 + i)) → goodRough (1024 * 6 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 5 + t)) → goodRough (1024 * 6 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 6 + (64 * 6 + i)) → goodRough (1024 * 6 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 6 + t)) → goodRough (1024 * 6 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 6 + (64 * 7 + i)) → goodRough (1024 * 6 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 7 + t)) → goodRough (1024 * 6 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 6 + (64 * 8 + i)) → goodRough (1024 * 6 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 8 + t)) → goodRough (1024 * 6 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 6 + (64 * 9 + i)) → goodRough (1024 * 6 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 9 + t)) → goodRough (1024 * 6 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 6 + (64 * 10 + i)) → goodRough (1024 * 6 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 10 + t)) → goodRough (1024 * 6 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 6 + (64 * 11 + i)) → goodRough (1024 * 6 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 11 + t)) → goodRough (1024 * 6 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 6 + (64 * 12 + i)) → goodRough (1024 * 6 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 12 + t)) → goodRough (1024 * 6 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 6 + (64 * 13 + i)) → goodRough (1024 * 6 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 13 + t)) → goodRough (1024 * 6 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 6 + (64 * 14 + i)) → goodRough (1024 * 6 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 14 + t)) → goodRough (1024 * 6 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 6 + (64 * 15 + i)) → goodRough (1024 * 6 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 6 + (64 * 15 + t)) → goodRough (1024 * 6 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart7 : ∀ a' < 1024, Even (1024 * 7 + a') → goodRough (1024 * 7 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 7 + (64 * 0 + i)) → goodRough (1024 * 7 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 0 + t)) → goodRough (1024 * 7 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 7 + (64 * 1 + i)) → goodRough (1024 * 7 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 1 + t)) → goodRough (1024 * 7 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 7 + (64 * 2 + i)) → goodRough (1024 * 7 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 2 + t)) → goodRough (1024 * 7 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 7 + (64 * 3 + i)) → goodRough (1024 * 7 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 3 + t)) → goodRough (1024 * 7 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 7 + (64 * 4 + i)) → goodRough (1024 * 7 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 4 + t)) → goodRough (1024 * 7 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 7 + (64 * 5 + i)) → goodRough (1024 * 7 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 5 + t)) → goodRough (1024 * 7 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 7 + (64 * 6 + i)) → goodRough (1024 * 7 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 6 + t)) → goodRough (1024 * 7 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 7 + (64 * 7 + i)) → goodRough (1024 * 7 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 7 + t)) → goodRough (1024 * 7 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 7 + (64 * 8 + i)) → goodRough (1024 * 7 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 8 + t)) → goodRough (1024 * 7 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 7 + (64 * 9 + i)) → goodRough (1024 * 7 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 9 + t)) → goodRough (1024 * 7 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 7 + (64 * 10 + i)) → goodRough (1024 * 7 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 10 + t)) → goodRough (1024 * 7 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 7 + (64 * 11 + i)) → goodRough (1024 * 7 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 11 + t)) → goodRough (1024 * 7 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 7 + (64 * 12 + i)) → goodRough (1024 * 7 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 12 + t)) → goodRough (1024 * 7 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 7 + (64 * 13 + i)) → goodRough (1024 * 7 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 13 + t)) → goodRough (1024 * 7 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 7 + (64 * 14 + i)) → goodRough (1024 * 7 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 14 + t)) → goodRough (1024 * 7 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 7 + (64 * 15 + i)) → goodRough (1024 * 7 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 7 + (64 * 15 + t)) → goodRough (1024 * 7 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart8 : ∀ a' < 1024, Even (1024 * 8 + a') → goodRough (1024 * 8 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 8 + (64 * 0 + i)) → goodRough (1024 * 8 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 0 + t)) → goodRough (1024 * 8 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 8 + (64 * 1 + i)) → goodRough (1024 * 8 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 1 + t)) → goodRough (1024 * 8 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 8 + (64 * 2 + i)) → goodRough (1024 * 8 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 2 + t)) → goodRough (1024 * 8 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 8 + (64 * 3 + i)) → goodRough (1024 * 8 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 3 + t)) → goodRough (1024 * 8 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 8 + (64 * 4 + i)) → goodRough (1024 * 8 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 4 + t)) → goodRough (1024 * 8 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 8 + (64 * 5 + i)) → goodRough (1024 * 8 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 5 + t)) → goodRough (1024 * 8 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 8 + (64 * 6 + i)) → goodRough (1024 * 8 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 6 + t)) → goodRough (1024 * 8 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 8 + (64 * 7 + i)) → goodRough (1024 * 8 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 7 + t)) → goodRough (1024 * 8 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 8 + (64 * 8 + i)) → goodRough (1024 * 8 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 8 + t)) → goodRough (1024 * 8 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 8 + (64 * 9 + i)) → goodRough (1024 * 8 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 9 + t)) → goodRough (1024 * 8 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 8 + (64 * 10 + i)) → goodRough (1024 * 8 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 10 + t)) → goodRough (1024 * 8 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 8 + (64 * 11 + i)) → goodRough (1024 * 8 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 11 + t)) → goodRough (1024 * 8 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 8 + (64 * 12 + i)) → goodRough (1024 * 8 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 12 + t)) → goodRough (1024 * 8 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 8 + (64 * 13 + i)) → goodRough (1024 * 8 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 13 + t)) → goodRough (1024 * 8 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 8 + (64 * 14 + i)) → goodRough (1024 * 8 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 14 + t)) → goodRough (1024 * 8 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 8 + (64 * 15 + i)) → goodRough (1024 * 8 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 8 + (64 * 15 + t)) → goodRough (1024 * 8 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart9 : ∀ a' < 1024, Even (1024 * 9 + a') → goodRough (1024 * 9 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 9 + (64 * 0 + i)) → goodRough (1024 * 9 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 0 + t)) → goodRough (1024 * 9 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 9 + (64 * 1 + i)) → goodRough (1024 * 9 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 1 + t)) → goodRough (1024 * 9 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 9 + (64 * 2 + i)) → goodRough (1024 * 9 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 2 + t)) → goodRough (1024 * 9 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 9 + (64 * 3 + i)) → goodRough (1024 * 9 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 3 + t)) → goodRough (1024 * 9 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 9 + (64 * 4 + i)) → goodRough (1024 * 9 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 4 + t)) → goodRough (1024 * 9 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 9 + (64 * 5 + i)) → goodRough (1024 * 9 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 5 + t)) → goodRough (1024 * 9 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 9 + (64 * 6 + i)) → goodRough (1024 * 9 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 6 + t)) → goodRough (1024 * 9 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 9 + (64 * 7 + i)) → goodRough (1024 * 9 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 7 + t)) → goodRough (1024 * 9 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 9 + (64 * 8 + i)) → goodRough (1024 * 9 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 8 + t)) → goodRough (1024 * 9 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 9 + (64 * 9 + i)) → goodRough (1024 * 9 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 9 + t)) → goodRough (1024 * 9 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 9 + (64 * 10 + i)) → goodRough (1024 * 9 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 10 + t)) → goodRough (1024 * 9 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 9 + (64 * 11 + i)) → goodRough (1024 * 9 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 11 + t)) → goodRough (1024 * 9 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 9 + (64 * 12 + i)) → goodRough (1024 * 9 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 12 + t)) → goodRough (1024 * 9 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 9 + (64 * 13 + i)) → goodRough (1024 * 9 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 13 + t)) → goodRough (1024 * 9 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 9 + (64 * 14 + i)) → goodRough (1024 * 9 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 14 + t)) → goodRough (1024 * 9 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 9 + (64 * 15 + i)) → goodRough (1024 * 9 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 9 + (64 * 15 + t)) → goodRough (1024 * 9 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart10 : ∀ a' < 1024, Even (1024 * 10 + a') → goodRough (1024 * 10 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 10 + (64 * 0 + i)) → goodRough (1024 * 10 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 0 + t)) → goodRough (1024 * 10 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 10 + (64 * 1 + i)) → goodRough (1024 * 10 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 1 + t)) → goodRough (1024 * 10 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 10 + (64 * 2 + i)) → goodRough (1024 * 10 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 2 + t)) → goodRough (1024 * 10 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 10 + (64 * 3 + i)) → goodRough (1024 * 10 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 3 + t)) → goodRough (1024 * 10 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 10 + (64 * 4 + i)) → goodRough (1024 * 10 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 4 + t)) → goodRough (1024 * 10 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 10 + (64 * 5 + i)) → goodRough (1024 * 10 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 5 + t)) → goodRough (1024 * 10 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 10 + (64 * 6 + i)) → goodRough (1024 * 10 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 6 + t)) → goodRough (1024 * 10 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 10 + (64 * 7 + i)) → goodRough (1024 * 10 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 7 + t)) → goodRough (1024 * 10 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 10 + (64 * 8 + i)) → goodRough (1024 * 10 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 8 + t)) → goodRough (1024 * 10 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 10 + (64 * 9 + i)) → goodRough (1024 * 10 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 9 + t)) → goodRough (1024 * 10 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 10 + (64 * 10 + i)) → goodRough (1024 * 10 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 10 + t)) → goodRough (1024 * 10 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 10 + (64 * 11 + i)) → goodRough (1024 * 10 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 11 + t)) → goodRough (1024 * 10 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 10 + (64 * 12 + i)) → goodRough (1024 * 10 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 12 + t)) → goodRough (1024 * 10 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 10 + (64 * 13 + i)) → goodRough (1024 * 10 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 13 + t)) → goodRough (1024 * 10 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 10 + (64 * 14 + i)) → goodRough (1024 * 10 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 14 + t)) → goodRough (1024 * 10 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 10 + (64 * 15 + i)) → goodRough (1024 * 10 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 10 + (64 * 15 + t)) → goodRough (1024 * 10 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart11 : ∀ a' < 1024, Even (1024 * 11 + a') → goodRough (1024 * 11 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 11 + (64 * 0 + i)) → goodRough (1024 * 11 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 0 + t)) → goodRough (1024 * 11 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 11 + (64 * 1 + i)) → goodRough (1024 * 11 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 1 + t)) → goodRough (1024 * 11 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 11 + (64 * 2 + i)) → goodRough (1024 * 11 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 2 + t)) → goodRough (1024 * 11 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 11 + (64 * 3 + i)) → goodRough (1024 * 11 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 3 + t)) → goodRough (1024 * 11 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 11 + (64 * 4 + i)) → goodRough (1024 * 11 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 4 + t)) → goodRough (1024 * 11 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 11 + (64 * 5 + i)) → goodRough (1024 * 11 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 5 + t)) → goodRough (1024 * 11 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 11 + (64 * 6 + i)) → goodRough (1024 * 11 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 6 + t)) → goodRough (1024 * 11 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 11 + (64 * 7 + i)) → goodRough (1024 * 11 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 7 + t)) → goodRough (1024 * 11 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 11 + (64 * 8 + i)) → goodRough (1024 * 11 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 8 + t)) → goodRough (1024 * 11 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 11 + (64 * 9 + i)) → goodRough (1024 * 11 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 9 + t)) → goodRough (1024 * 11 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 11 + (64 * 10 + i)) → goodRough (1024 * 11 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 10 + t)) → goodRough (1024 * 11 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 11 + (64 * 11 + i)) → goodRough (1024 * 11 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 11 + t)) → goodRough (1024 * 11 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 11 + (64 * 12 + i)) → goodRough (1024 * 11 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 12 + t)) → goodRough (1024 * 11 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 11 + (64 * 13 + i)) → goodRough (1024 * 11 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 13 + t)) → goodRough (1024 * 11 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 11 + (64 * 14 + i)) → goodRough (1024 * 11 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 14 + t)) → goodRough (1024 * 11 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 11 + (64 * 15 + i)) → goodRough (1024 * 11 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 11 + (64 * 15 + t)) → goodRough (1024 * 11 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart12 : ∀ a' < 1024, Even (1024 * 12 + a') → goodRough (1024 * 12 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 12 + (64 * 0 + i)) → goodRough (1024 * 12 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 0 + t)) → goodRough (1024 * 12 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 12 + (64 * 1 + i)) → goodRough (1024 * 12 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 1 + t)) → goodRough (1024 * 12 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 12 + (64 * 2 + i)) → goodRough (1024 * 12 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 2 + t)) → goodRough (1024 * 12 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 12 + (64 * 3 + i)) → goodRough (1024 * 12 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 3 + t)) → goodRough (1024 * 12 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 12 + (64 * 4 + i)) → goodRough (1024 * 12 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 4 + t)) → goodRough (1024 * 12 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 12 + (64 * 5 + i)) → goodRough (1024 * 12 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 5 + t)) → goodRough (1024 * 12 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 12 + (64 * 6 + i)) → goodRough (1024 * 12 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 6 + t)) → goodRough (1024 * 12 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 12 + (64 * 7 + i)) → goodRough (1024 * 12 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 7 + t)) → goodRough (1024 * 12 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 12 + (64 * 8 + i)) → goodRough (1024 * 12 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 8 + t)) → goodRough (1024 * 12 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 12 + (64 * 9 + i)) → goodRough (1024 * 12 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 9 + t)) → goodRough (1024 * 12 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 12 + (64 * 10 + i)) → goodRough (1024 * 12 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 10 + t)) → goodRough (1024 * 12 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 12 + (64 * 11 + i)) → goodRough (1024 * 12 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 11 + t)) → goodRough (1024 * 12 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 12 + (64 * 12 + i)) → goodRough (1024 * 12 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 12 + t)) → goodRough (1024 * 12 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 12 + (64 * 13 + i)) → goodRough (1024 * 12 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 13 + t)) → goodRough (1024 * 12 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 12 + (64 * 14 + i)) → goodRough (1024 * 12 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 14 + t)) → goodRough (1024 * 12 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 12 + (64 * 15 + i)) → goodRough (1024 * 12 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 12 + (64 * 15 + t)) → goodRough (1024 * 12 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart13 : ∀ a' < 1024, Even (1024 * 13 + a') → goodRough (1024 * 13 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 13 + (64 * 0 + i)) → goodRough (1024 * 13 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 0 + t)) → goodRough (1024 * 13 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 13 + (64 * 1 + i)) → goodRough (1024 * 13 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 1 + t)) → goodRough (1024 * 13 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 13 + (64 * 2 + i)) → goodRough (1024 * 13 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 2 + t)) → goodRough (1024 * 13 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 13 + (64 * 3 + i)) → goodRough (1024 * 13 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 3 + t)) → goodRough (1024 * 13 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 13 + (64 * 4 + i)) → goodRough (1024 * 13 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 4 + t)) → goodRough (1024 * 13 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 13 + (64 * 5 + i)) → goodRough (1024 * 13 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 5 + t)) → goodRough (1024 * 13 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 13 + (64 * 6 + i)) → goodRough (1024 * 13 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 6 + t)) → goodRough (1024 * 13 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 13 + (64 * 7 + i)) → goodRough (1024 * 13 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 7 + t)) → goodRough (1024 * 13 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 13 + (64 * 8 + i)) → goodRough (1024 * 13 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 8 + t)) → goodRough (1024 * 13 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 13 + (64 * 9 + i)) → goodRough (1024 * 13 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 9 + t)) → goodRough (1024 * 13 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 13 + (64 * 10 + i)) → goodRough (1024 * 13 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 10 + t)) → goodRough (1024 * 13 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 13 + (64 * 11 + i)) → goodRough (1024 * 13 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 11 + t)) → goodRough (1024 * 13 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 13 + (64 * 12 + i)) → goodRough (1024 * 13 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 12 + t)) → goodRough (1024 * 13 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 13 + (64 * 13 + i)) → goodRough (1024 * 13 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 13 + t)) → goodRough (1024 * 13 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 13 + (64 * 14 + i)) → goodRough (1024 * 13 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 14 + t)) → goodRough (1024 * 13 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 13 + (64 * 15 + i)) → goodRough (1024 * 13 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 13 + (64 * 15 + t)) → goodRough (1024 * 13 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart14 : ∀ a' < 1024, Even (1024 * 14 + a') → goodRough (1024 * 14 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 14 + (64 * 0 + i)) → goodRough (1024 * 14 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 0 + t)) → goodRough (1024 * 14 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 14 + (64 * 1 + i)) → goodRough (1024 * 14 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 1 + t)) → goodRough (1024 * 14 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 14 + (64 * 2 + i)) → goodRough (1024 * 14 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 2 + t)) → goodRough (1024 * 14 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 14 + (64 * 3 + i)) → goodRough (1024 * 14 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 3 + t)) → goodRough (1024 * 14 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 14 + (64 * 4 + i)) → goodRough (1024 * 14 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 4 + t)) → goodRough (1024 * 14 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 14 + (64 * 5 + i)) → goodRough (1024 * 14 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 5 + t)) → goodRough (1024 * 14 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 14 + (64 * 6 + i)) → goodRough (1024 * 14 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 6 + t)) → goodRough (1024 * 14 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 14 + (64 * 7 + i)) → goodRough (1024 * 14 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 7 + t)) → goodRough (1024 * 14 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 14 + (64 * 8 + i)) → goodRough (1024 * 14 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 8 + t)) → goodRough (1024 * 14 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 14 + (64 * 9 + i)) → goodRough (1024 * 14 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 9 + t)) → goodRough (1024 * 14 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 14 + (64 * 10 + i)) → goodRough (1024 * 14 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 10 + t)) → goodRough (1024 * 14 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 14 + (64 * 11 + i)) → goodRough (1024 * 14 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 11 + t)) → goodRough (1024 * 14 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 14 + (64 * 12 + i)) → goodRough (1024 * 14 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 12 + t)) → goodRough (1024 * 14 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 14 + (64 * 13 + i)) → goodRough (1024 * 14 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 13 + t)) → goodRough (1024 * 14 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 14 + (64 * 14 + i)) → goodRough (1024 * 14 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 14 + t)) → goodRough (1024 * 14 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 14 + (64 * 15 + i)) → goodRough (1024 * 14 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 14 + (64 * 15 + t)) → goodRough (1024 * 14 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart15 : ∀ a' < 1024, Even (1024 * 15 + a') → goodRough (1024 * 15 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 15 + (64 * 0 + i)) → goodRough (1024 * 15 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 0 + t)) → goodRough (1024 * 15 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 15 + (64 * 1 + i)) → goodRough (1024 * 15 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 1 + t)) → goodRough (1024 * 15 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 15 + (64 * 2 + i)) → goodRough (1024 * 15 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 2 + t)) → goodRough (1024 * 15 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 15 + (64 * 3 + i)) → goodRough (1024 * 15 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 3 + t)) → goodRough (1024 * 15 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 15 + (64 * 4 + i)) → goodRough (1024 * 15 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 4 + t)) → goodRough (1024 * 15 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 15 + (64 * 5 + i)) → goodRough (1024 * 15 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 5 + t)) → goodRough (1024 * 15 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 15 + (64 * 6 + i)) → goodRough (1024 * 15 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 6 + t)) → goodRough (1024 * 15 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 15 + (64 * 7 + i)) → goodRough (1024 * 15 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 7 + t)) → goodRough (1024 * 15 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 15 + (64 * 8 + i)) → goodRough (1024 * 15 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 8 + t)) → goodRough (1024 * 15 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 15 + (64 * 9 + i)) → goodRough (1024 * 15 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 9 + t)) → goodRough (1024 * 15 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 15 + (64 * 10 + i)) → goodRough (1024 * 15 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 10 + t)) → goodRough (1024 * 15 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 15 + (64 * 11 + i)) → goodRough (1024 * 15 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 11 + t)) → goodRough (1024 * 15 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 15 + (64 * 12 + i)) → goodRough (1024 * 15 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 12 + t)) → goodRough (1024 * 15 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 15 + (64 * 13 + i)) → goodRough (1024 * 15 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 13 + t)) → goodRough (1024 * 15 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 15 + (64 * 14 + i)) → goodRough (1024 * 15 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 14 + t)) → goodRough (1024 * 15 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 15 + (64 * 15 + i)) → goodRough (1024 * 15 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 15 + (64 * 15 + t)) → goodRough (1024 * 15 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart16 : ∀ a' < 1024, Even (1024 * 16 + a') → goodRough (1024 * 16 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 16 + (64 * 0 + i)) → goodRough (1024 * 16 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 0 + t)) → goodRough (1024 * 16 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 16 + (64 * 1 + i)) → goodRough (1024 * 16 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 1 + t)) → goodRough (1024 * 16 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 16 + (64 * 2 + i)) → goodRough (1024 * 16 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 2 + t)) → goodRough (1024 * 16 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 16 + (64 * 3 + i)) → goodRough (1024 * 16 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 3 + t)) → goodRough (1024 * 16 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 16 + (64 * 4 + i)) → goodRough (1024 * 16 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 4 + t)) → goodRough (1024 * 16 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 16 + (64 * 5 + i)) → goodRough (1024 * 16 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 5 + t)) → goodRough (1024 * 16 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 16 + (64 * 6 + i)) → goodRough (1024 * 16 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 6 + t)) → goodRough (1024 * 16 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 16 + (64 * 7 + i)) → goodRough (1024 * 16 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 7 + t)) → goodRough (1024 * 16 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 16 + (64 * 8 + i)) → goodRough (1024 * 16 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 8 + t)) → goodRough (1024 * 16 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 16 + (64 * 9 + i)) → goodRough (1024 * 16 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 9 + t)) → goodRough (1024 * 16 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 16 + (64 * 10 + i)) → goodRough (1024 * 16 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 10 + t)) → goodRough (1024 * 16 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 16 + (64 * 11 + i)) → goodRough (1024 * 16 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 11 + t)) → goodRough (1024 * 16 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 16 + (64 * 12 + i)) → goodRough (1024 * 16 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 12 + t)) → goodRough (1024 * 16 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 16 + (64 * 13 + i)) → goodRough (1024 * 16 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 13 + t)) → goodRough (1024 * 16 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 16 + (64 * 14 + i)) → goodRough (1024 * 16 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 14 + t)) → goodRough (1024 * 16 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 16 + (64 * 15 + i)) → goodRough (1024 * 16 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 16 + (64 * 15 + t)) → goodRough (1024 * 16 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart17 : ∀ a' < 1024, Even (1024 * 17 + a') → goodRough (1024 * 17 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 17 + (64 * 0 + i)) → goodRough (1024 * 17 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 0 + t)) → goodRough (1024 * 17 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 17 + (64 * 1 + i)) → goodRough (1024 * 17 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 1 + t)) → goodRough (1024 * 17 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 17 + (64 * 2 + i)) → goodRough (1024 * 17 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 2 + t)) → goodRough (1024 * 17 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 17 + (64 * 3 + i)) → goodRough (1024 * 17 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 3 + t)) → goodRough (1024 * 17 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 17 + (64 * 4 + i)) → goodRough (1024 * 17 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 4 + t)) → goodRough (1024 * 17 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 17 + (64 * 5 + i)) → goodRough (1024 * 17 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 5 + t)) → goodRough (1024 * 17 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 17 + (64 * 6 + i)) → goodRough (1024 * 17 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 6 + t)) → goodRough (1024 * 17 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 17 + (64 * 7 + i)) → goodRough (1024 * 17 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 7 + t)) → goodRough (1024 * 17 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 17 + (64 * 8 + i)) → goodRough (1024 * 17 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 8 + t)) → goodRough (1024 * 17 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 17 + (64 * 9 + i)) → goodRough (1024 * 17 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 9 + t)) → goodRough (1024 * 17 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 17 + (64 * 10 + i)) → goodRough (1024 * 17 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 10 + t)) → goodRough (1024 * 17 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 17 + (64 * 11 + i)) → goodRough (1024 * 17 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 11 + t)) → goodRough (1024 * 17 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 17 + (64 * 12 + i)) → goodRough (1024 * 17 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 12 + t)) → goodRough (1024 * 17 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 17 + (64 * 13 + i)) → goodRough (1024 * 17 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 13 + t)) → goodRough (1024 * 17 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 17 + (64 * 14 + i)) → goodRough (1024 * 17 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 14 + t)) → goodRough (1024 * 17 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 17 + (64 * 15 + i)) → goodRough (1024 * 17 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 17 + (64 * 15 + t)) → goodRough (1024 * 17 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart18 : ∀ a' < 1024, Even (1024 * 18 + a') → goodRough (1024 * 18 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 18 + (64 * 0 + i)) → goodRough (1024 * 18 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 0 + t)) → goodRough (1024 * 18 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 18 + (64 * 1 + i)) → goodRough (1024 * 18 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 1 + t)) → goodRough (1024 * 18 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 18 + (64 * 2 + i)) → goodRough (1024 * 18 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 2 + t)) → goodRough (1024 * 18 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 18 + (64 * 3 + i)) → goodRough (1024 * 18 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 3 + t)) → goodRough (1024 * 18 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 18 + (64 * 4 + i)) → goodRough (1024 * 18 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 4 + t)) → goodRough (1024 * 18 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 18 + (64 * 5 + i)) → goodRough (1024 * 18 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 5 + t)) → goodRough (1024 * 18 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 18 + (64 * 6 + i)) → goodRough (1024 * 18 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 6 + t)) → goodRough (1024 * 18 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 18 + (64 * 7 + i)) → goodRough (1024 * 18 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 7 + t)) → goodRough (1024 * 18 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 18 + (64 * 8 + i)) → goodRough (1024 * 18 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 8 + t)) → goodRough (1024 * 18 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 18 + (64 * 9 + i)) → goodRough (1024 * 18 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 9 + t)) → goodRough (1024 * 18 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 18 + (64 * 10 + i)) → goodRough (1024 * 18 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 10 + t)) → goodRough (1024 * 18 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 18 + (64 * 11 + i)) → goodRough (1024 * 18 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 11 + t)) → goodRough (1024 * 18 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 18 + (64 * 12 + i)) → goodRough (1024 * 18 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 12 + t)) → goodRough (1024 * 18 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 18 + (64 * 13 + i)) → goodRough (1024 * 18 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 13 + t)) → goodRough (1024 * 18 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 18 + (64 * 14 + i)) → goodRough (1024 * 18 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 14 + t)) → goodRough (1024 * 18 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 18 + (64 * 15 + i)) → goodRough (1024 * 18 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 18 + (64 * 15 + t)) → goodRough (1024 * 18 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart19 : ∀ a' < 1024, Even (1024 * 19 + a') → goodRough (1024 * 19 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 19 + (64 * 0 + i)) → goodRough (1024 * 19 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 0 + t)) → goodRough (1024 * 19 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 19 + (64 * 1 + i)) → goodRough (1024 * 19 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 1 + t)) → goodRough (1024 * 19 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 19 + (64 * 2 + i)) → goodRough (1024 * 19 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 2 + t)) → goodRough (1024 * 19 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 19 + (64 * 3 + i)) → goodRough (1024 * 19 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 3 + t)) → goodRough (1024 * 19 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 19 + (64 * 4 + i)) → goodRough (1024 * 19 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 4 + t)) → goodRough (1024 * 19 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 19 + (64 * 5 + i)) → goodRough (1024 * 19 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 5 + t)) → goodRough (1024 * 19 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 19 + (64 * 6 + i)) → goodRough (1024 * 19 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 6 + t)) → goodRough (1024 * 19 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 19 + (64 * 7 + i)) → goodRough (1024 * 19 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 7 + t)) → goodRough (1024 * 19 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 19 + (64 * 8 + i)) → goodRough (1024 * 19 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 8 + t)) → goodRough (1024 * 19 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 19 + (64 * 9 + i)) → goodRough (1024 * 19 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 9 + t)) → goodRough (1024 * 19 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 19 + (64 * 10 + i)) → goodRough (1024 * 19 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 10 + t)) → goodRough (1024 * 19 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 19 + (64 * 11 + i)) → goodRough (1024 * 19 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 11 + t)) → goodRough (1024 * 19 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 19 + (64 * 12 + i)) → goodRough (1024 * 19 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 12 + t)) → goodRough (1024 * 19 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 19 + (64 * 13 + i)) → goodRough (1024 * 19 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 13 + t)) → goodRough (1024 * 19 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 19 + (64 * 14 + i)) → goodRough (1024 * 19 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 14 + t)) → goodRough (1024 * 19 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 19 + (64 * 15 + i)) → goodRough (1024 * 19 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 19 + (64 * 15 + t)) → goodRough (1024 * 19 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart20 : ∀ a' < 1024, Even (1024 * 20 + a') → goodRough (1024 * 20 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 20 + (64 * 0 + i)) → goodRough (1024 * 20 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 0 + t)) → goodRough (1024 * 20 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 20 + (64 * 1 + i)) → goodRough (1024 * 20 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 1 + t)) → goodRough (1024 * 20 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 20 + (64 * 2 + i)) → goodRough (1024 * 20 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 2 + t)) → goodRough (1024 * 20 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 20 + (64 * 3 + i)) → goodRough (1024 * 20 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 3 + t)) → goodRough (1024 * 20 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 20 + (64 * 4 + i)) → goodRough (1024 * 20 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 4 + t)) → goodRough (1024 * 20 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 20 + (64 * 5 + i)) → goodRough (1024 * 20 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 5 + t)) → goodRough (1024 * 20 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 20 + (64 * 6 + i)) → goodRough (1024 * 20 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 6 + t)) → goodRough (1024 * 20 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 20 + (64 * 7 + i)) → goodRough (1024 * 20 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 7 + t)) → goodRough (1024 * 20 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 20 + (64 * 8 + i)) → goodRough (1024 * 20 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 8 + t)) → goodRough (1024 * 20 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 20 + (64 * 9 + i)) → goodRough (1024 * 20 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 9 + t)) → goodRough (1024 * 20 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 20 + (64 * 10 + i)) → goodRough (1024 * 20 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 10 + t)) → goodRough (1024 * 20 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 20 + (64 * 11 + i)) → goodRough (1024 * 20 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 11 + t)) → goodRough (1024 * 20 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 20 + (64 * 12 + i)) → goodRough (1024 * 20 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 12 + t)) → goodRough (1024 * 20 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 20 + (64 * 13 + i)) → goodRough (1024 * 20 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 13 + t)) → goodRough (1024 * 20 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 20 + (64 * 14 + i)) → goodRough (1024 * 20 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 14 + t)) → goodRough (1024 * 20 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 20 + (64 * 15 + i)) → goodRough (1024 * 20 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 20 + (64 * 15 + t)) → goodRough (1024 * 20 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart21 : ∀ a' < 1024, Even (1024 * 21 + a') → goodRough (1024 * 21 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 21 + (64 * 0 + i)) → goodRough (1024 * 21 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 0 + t)) → goodRough (1024 * 21 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 21 + (64 * 1 + i)) → goodRough (1024 * 21 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 1 + t)) → goodRough (1024 * 21 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 21 + (64 * 2 + i)) → goodRough (1024 * 21 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 2 + t)) → goodRough (1024 * 21 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 21 + (64 * 3 + i)) → goodRough (1024 * 21 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 3 + t)) → goodRough (1024 * 21 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 21 + (64 * 4 + i)) → goodRough (1024 * 21 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 4 + t)) → goodRough (1024 * 21 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 21 + (64 * 5 + i)) → goodRough (1024 * 21 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 5 + t)) → goodRough (1024 * 21 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 21 + (64 * 6 + i)) → goodRough (1024 * 21 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 6 + t)) → goodRough (1024 * 21 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 21 + (64 * 7 + i)) → goodRough (1024 * 21 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 7 + t)) → goodRough (1024 * 21 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 21 + (64 * 8 + i)) → goodRough (1024 * 21 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 8 + t)) → goodRough (1024 * 21 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 21 + (64 * 9 + i)) → goodRough (1024 * 21 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 9 + t)) → goodRough (1024 * 21 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 21 + (64 * 10 + i)) → goodRough (1024 * 21 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 10 + t)) → goodRough (1024 * 21 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 21 + (64 * 11 + i)) → goodRough (1024 * 21 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 11 + t)) → goodRough (1024 * 21 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 21 + (64 * 12 + i)) → goodRough (1024 * 21 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 12 + t)) → goodRough (1024 * 21 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 21 + (64 * 13 + i)) → goodRough (1024 * 21 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 13 + t)) → goodRough (1024 * 21 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 21 + (64 * 14 + i)) → goodRough (1024 * 21 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 14 + t)) → goodRough (1024 * 21 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 21 + (64 * 15 + i)) → goodRough (1024 * 21 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 21 + (64 * 15 + t)) → goodRough (1024 * 21 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart22 : ∀ a' < 1024, Even (1024 * 22 + a') → goodRough (1024 * 22 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 22 + (64 * 0 + i)) → goodRough (1024 * 22 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 0 + t)) → goodRough (1024 * 22 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 22 + (64 * 1 + i)) → goodRough (1024 * 22 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 1 + t)) → goodRough (1024 * 22 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 22 + (64 * 2 + i)) → goodRough (1024 * 22 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 2 + t)) → goodRough (1024 * 22 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 22 + (64 * 3 + i)) → goodRough (1024 * 22 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 3 + t)) → goodRough (1024 * 22 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 22 + (64 * 4 + i)) → goodRough (1024 * 22 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 4 + t)) → goodRough (1024 * 22 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 22 + (64 * 5 + i)) → goodRough (1024 * 22 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 5 + t)) → goodRough (1024 * 22 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 22 + (64 * 6 + i)) → goodRough (1024 * 22 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 6 + t)) → goodRough (1024 * 22 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 22 + (64 * 7 + i)) → goodRough (1024 * 22 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 7 + t)) → goodRough (1024 * 22 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 22 + (64 * 8 + i)) → goodRough (1024 * 22 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 8 + t)) → goodRough (1024 * 22 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 22 + (64 * 9 + i)) → goodRough (1024 * 22 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 9 + t)) → goodRough (1024 * 22 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 22 + (64 * 10 + i)) → goodRough (1024 * 22 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 10 + t)) → goodRough (1024 * 22 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 22 + (64 * 11 + i)) → goodRough (1024 * 22 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 11 + t)) → goodRough (1024 * 22 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 22 + (64 * 12 + i)) → goodRough (1024 * 22 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 12 + t)) → goodRough (1024 * 22 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 22 + (64 * 13 + i)) → goodRough (1024 * 22 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 13 + t)) → goodRough (1024 * 22 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 22 + (64 * 14 + i)) → goodRough (1024 * 22 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 14 + t)) → goodRough (1024 * 22 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 22 + (64 * 15 + i)) → goodRough (1024 * 22 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 22 + (64 * 15 + t)) → goodRough (1024 * 22 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart23 : ∀ a' < 1024, Even (1024 * 23 + a') → goodRough (1024 * 23 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 23 + (64 * 0 + i)) → goodRough (1024 * 23 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 0 + t)) → goodRough (1024 * 23 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 23 + (64 * 1 + i)) → goodRough (1024 * 23 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 1 + t)) → goodRough (1024 * 23 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 23 + (64 * 2 + i)) → goodRough (1024 * 23 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 2 + t)) → goodRough (1024 * 23 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 23 + (64 * 3 + i)) → goodRough (1024 * 23 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 3 + t)) → goodRough (1024 * 23 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 23 + (64 * 4 + i)) → goodRough (1024 * 23 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 4 + t)) → goodRough (1024 * 23 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 23 + (64 * 5 + i)) → goodRough (1024 * 23 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 5 + t)) → goodRough (1024 * 23 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 23 + (64 * 6 + i)) → goodRough (1024 * 23 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 6 + t)) → goodRough (1024 * 23 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 23 + (64 * 7 + i)) → goodRough (1024 * 23 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 7 + t)) → goodRough (1024 * 23 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 23 + (64 * 8 + i)) → goodRough (1024 * 23 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 8 + t)) → goodRough (1024 * 23 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 23 + (64 * 9 + i)) → goodRough (1024 * 23 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 9 + t)) → goodRough (1024 * 23 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 23 + (64 * 10 + i)) → goodRough (1024 * 23 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 10 + t)) → goodRough (1024 * 23 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 23 + (64 * 11 + i)) → goodRough (1024 * 23 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 11 + t)) → goodRough (1024 * 23 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 23 + (64 * 12 + i)) → goodRough (1024 * 23 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 12 + t)) → goodRough (1024 * 23 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 23 + (64 * 13 + i)) → goodRough (1024 * 23 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 13 + t)) → goodRough (1024 * 23 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 23 + (64 * 14 + i)) → goodRough (1024 * 23 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 14 + t)) → goodRough (1024 * 23 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 23 + (64 * 15 + i)) → goodRough (1024 * 23 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 23 + (64 * 15 + t)) → goodRough (1024 * 23 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart24 : ∀ a' < 1024, Even (1024 * 24 + a') → goodRough (1024 * 24 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 24 + (64 * 0 + i)) → goodRough (1024 * 24 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 0 + t)) → goodRough (1024 * 24 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 24 + (64 * 1 + i)) → goodRough (1024 * 24 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 1 + t)) → goodRough (1024 * 24 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 24 + (64 * 2 + i)) → goodRough (1024 * 24 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 2 + t)) → goodRough (1024 * 24 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 24 + (64 * 3 + i)) → goodRough (1024 * 24 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 3 + t)) → goodRough (1024 * 24 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 24 + (64 * 4 + i)) → goodRough (1024 * 24 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 4 + t)) → goodRough (1024 * 24 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 24 + (64 * 5 + i)) → goodRough (1024 * 24 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 5 + t)) → goodRough (1024 * 24 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 24 + (64 * 6 + i)) → goodRough (1024 * 24 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 6 + t)) → goodRough (1024 * 24 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 24 + (64 * 7 + i)) → goodRough (1024 * 24 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 7 + t)) → goodRough (1024 * 24 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 24 + (64 * 8 + i)) → goodRough (1024 * 24 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 8 + t)) → goodRough (1024 * 24 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 24 + (64 * 9 + i)) → goodRough (1024 * 24 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 9 + t)) → goodRough (1024 * 24 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 24 + (64 * 10 + i)) → goodRough (1024 * 24 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 10 + t)) → goodRough (1024 * 24 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 24 + (64 * 11 + i)) → goodRough (1024 * 24 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 11 + t)) → goodRough (1024 * 24 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 24 + (64 * 12 + i)) → goodRough (1024 * 24 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 12 + t)) → goodRough (1024 * 24 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 24 + (64 * 13 + i)) → goodRough (1024 * 24 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 13 + t)) → goodRough (1024 * 24 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 24 + (64 * 14 + i)) → goodRough (1024 * 24 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 14 + t)) → goodRough (1024 * 24 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 24 + (64 * 15 + i)) → goodRough (1024 * 24 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 24 + (64 * 15 + t)) → goodRough (1024 * 24 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart25 : ∀ a' < 1024, Even (1024 * 25 + a') → goodRough (1024 * 25 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 25 + (64 * 0 + i)) → goodRough (1024 * 25 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 0 + t)) → goodRough (1024 * 25 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 25 + (64 * 1 + i)) → goodRough (1024 * 25 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 1 + t)) → goodRough (1024 * 25 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 25 + (64 * 2 + i)) → goodRough (1024 * 25 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 2 + t)) → goodRough (1024 * 25 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 25 + (64 * 3 + i)) → goodRough (1024 * 25 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 3 + t)) → goodRough (1024 * 25 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 25 + (64 * 4 + i)) → goodRough (1024 * 25 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 4 + t)) → goodRough (1024 * 25 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 25 + (64 * 5 + i)) → goodRough (1024 * 25 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 5 + t)) → goodRough (1024 * 25 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 25 + (64 * 6 + i)) → goodRough (1024 * 25 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 6 + t)) → goodRough (1024 * 25 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 25 + (64 * 7 + i)) → goodRough (1024 * 25 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 7 + t)) → goodRough (1024 * 25 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 25 + (64 * 8 + i)) → goodRough (1024 * 25 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 8 + t)) → goodRough (1024 * 25 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 25 + (64 * 9 + i)) → goodRough (1024 * 25 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 9 + t)) → goodRough (1024 * 25 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 25 + (64 * 10 + i)) → goodRough (1024 * 25 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 10 + t)) → goodRough (1024 * 25 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 25 + (64 * 11 + i)) → goodRough (1024 * 25 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 11 + t)) → goodRough (1024 * 25 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 25 + (64 * 12 + i)) → goodRough (1024 * 25 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 12 + t)) → goodRough (1024 * 25 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 25 + (64 * 13 + i)) → goodRough (1024 * 25 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 13 + t)) → goodRough (1024 * 25 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 25 + (64 * 14 + i)) → goodRough (1024 * 25 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 14 + t)) → goodRough (1024 * 25 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 25 + (64 * 15 + i)) → goodRough (1024 * 25 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 25 + (64 * 15 + t)) → goodRough (1024 * 25 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart26 : ∀ a' < 1024, Even (1024 * 26 + a') → goodRough (1024 * 26 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 26 + (64 * 0 + i)) → goodRough (1024 * 26 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 0 + t)) → goodRough (1024 * 26 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 26 + (64 * 1 + i)) → goodRough (1024 * 26 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 1 + t)) → goodRough (1024 * 26 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 26 + (64 * 2 + i)) → goodRough (1024 * 26 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 2 + t)) → goodRough (1024 * 26 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 26 + (64 * 3 + i)) → goodRough (1024 * 26 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 3 + t)) → goodRough (1024 * 26 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 26 + (64 * 4 + i)) → goodRough (1024 * 26 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 4 + t)) → goodRough (1024 * 26 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 26 + (64 * 5 + i)) → goodRough (1024 * 26 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 5 + t)) → goodRough (1024 * 26 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 26 + (64 * 6 + i)) → goodRough (1024 * 26 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 6 + t)) → goodRough (1024 * 26 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 26 + (64 * 7 + i)) → goodRough (1024 * 26 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 7 + t)) → goodRough (1024 * 26 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 26 + (64 * 8 + i)) → goodRough (1024 * 26 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 8 + t)) → goodRough (1024 * 26 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 26 + (64 * 9 + i)) → goodRough (1024 * 26 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 9 + t)) → goodRough (1024 * 26 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 26 + (64 * 10 + i)) → goodRough (1024 * 26 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 10 + t)) → goodRough (1024 * 26 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 26 + (64 * 11 + i)) → goodRough (1024 * 26 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 11 + t)) → goodRough (1024 * 26 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 26 + (64 * 12 + i)) → goodRough (1024 * 26 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 12 + t)) → goodRough (1024 * 26 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 26 + (64 * 13 + i)) → goodRough (1024 * 26 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 13 + t)) → goodRough (1024 * 26 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 26 + (64 * 14 + i)) → goodRough (1024 * 26 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 14 + t)) → goodRough (1024 * 26 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 26 + (64 * 15 + i)) → goodRough (1024 * 26 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 26 + (64 * 15 + t)) → goodRough (1024 * 26 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart27 : ∀ a' < 1024, Even (1024 * 27 + a') → goodRough (1024 * 27 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 27 + (64 * 0 + i)) → goodRough (1024 * 27 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 0 + t)) → goodRough (1024 * 27 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 27 + (64 * 1 + i)) → goodRough (1024 * 27 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 1 + t)) → goodRough (1024 * 27 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 27 + (64 * 2 + i)) → goodRough (1024 * 27 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 2 + t)) → goodRough (1024 * 27 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 27 + (64 * 3 + i)) → goodRough (1024 * 27 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 3 + t)) → goodRough (1024 * 27 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 27 + (64 * 4 + i)) → goodRough (1024 * 27 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 4 + t)) → goodRough (1024 * 27 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 27 + (64 * 5 + i)) → goodRough (1024 * 27 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 5 + t)) → goodRough (1024 * 27 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 27 + (64 * 6 + i)) → goodRough (1024 * 27 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 6 + t)) → goodRough (1024 * 27 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 27 + (64 * 7 + i)) → goodRough (1024 * 27 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 7 + t)) → goodRough (1024 * 27 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 27 + (64 * 8 + i)) → goodRough (1024 * 27 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 8 + t)) → goodRough (1024 * 27 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 27 + (64 * 9 + i)) → goodRough (1024 * 27 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 9 + t)) → goodRough (1024 * 27 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 27 + (64 * 10 + i)) → goodRough (1024 * 27 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 10 + t)) → goodRough (1024 * 27 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 27 + (64 * 11 + i)) → goodRough (1024 * 27 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 11 + t)) → goodRough (1024 * 27 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 27 + (64 * 12 + i)) → goodRough (1024 * 27 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 12 + t)) → goodRough (1024 * 27 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 27 + (64 * 13 + i)) → goodRough (1024 * 27 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 13 + t)) → goodRough (1024 * 27 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 27 + (64 * 14 + i)) → goodRough (1024 * 27 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 14 + t)) → goodRough (1024 * 27 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 27 + (64 * 15 + i)) → goodRough (1024 * 27 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 27 + (64 * 15 + t)) → goodRough (1024 * 27 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart28 : ∀ a' < 1024, Even (1024 * 28 + a') → goodRough (1024 * 28 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 28 + (64 * 0 + i)) → goodRough (1024 * 28 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 0 + t)) → goodRough (1024 * 28 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 28 + (64 * 1 + i)) → goodRough (1024 * 28 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 1 + t)) → goodRough (1024 * 28 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 28 + (64 * 2 + i)) → goodRough (1024 * 28 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 2 + t)) → goodRough (1024 * 28 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 28 + (64 * 3 + i)) → goodRough (1024 * 28 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 3 + t)) → goodRough (1024 * 28 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 28 + (64 * 4 + i)) → goodRough (1024 * 28 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 4 + t)) → goodRough (1024 * 28 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 64, Even (1024 * 28 + (64 * 5 + i)) → goodRough (1024 * 28 + (64 * 5 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 5 + t)) → goodRough (1024 * 28 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c6 : ∀ i < 64, Even (1024 * 28 + (64 * 6 + i)) → goodRough (1024 * 28 + (64 * 6 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 6 + t)) → goodRough (1024 * 28 + (64 * 6 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c7 : ∀ i < 64, Even (1024 * 28 + (64 * 7 + i)) → goodRough (1024 * 28 + (64 * 7 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 7 + t)) → goodRough (1024 * 28 + (64 * 7 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c8 : ∀ i < 64, Even (1024 * 28 + (64 * 8 + i)) → goodRough (1024 * 28 + (64 * 8 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 8 + t)) → goodRough (1024 * 28 + (64 * 8 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c9 : ∀ i < 64, Even (1024 * 28 + (64 * 9 + i)) → goodRough (1024 * 28 + (64 * 9 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 9 + t)) → goodRough (1024 * 28 + (64 * 9 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c10 : ∀ i < 64, Even (1024 * 28 + (64 * 10 + i)) → goodRough (1024 * 28 + (64 * 10 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 10 + t)) → goodRough (1024 * 28 + (64 * 10 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c11 : ∀ i < 64, Even (1024 * 28 + (64 * 11 + i)) → goodRough (1024 * 28 + (64 * 11 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 11 + t)) → goodRough (1024 * 28 + (64 * 11 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c12 : ∀ i < 64, Even (1024 * 28 + (64 * 12 + i)) → goodRough (1024 * 28 + (64 * 12 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 12 + t)) → goodRough (1024 * 28 + (64 * 12 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c13 : ∀ i < 64, Even (1024 * 28 + (64 * 13 + i)) → goodRough (1024 * 28 + (64 * 13 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 13 + t)) → goodRough (1024 * 28 + (64 * 13 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c14 : ∀ i < 64, Even (1024 * 28 + (64 * 14 + i)) → goodRough (1024 * 28 + (64 * 14 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 14 + t)) → goodRough (1024 * 28 + (64 * 14 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c15 : ∀ i < 64, Even (1024 * 28 + (64 * 15 + i)) → goodRough (1024 * 28 + (64 * 15 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 28 + (64 * 15 + t)) → goodRough (1024 * 28 + (64 * 15 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 16 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    exact c5 i hi he'
  · rw [haeq] at he' ⊢
    exact c6 i hi he'
  · rw [haeq] at he' ⊢
    exact c7 i hi he'
  · rw [haeq] at he' ⊢
    exact c8 i hi he'
  · rw [haeq] at he' ⊢
    exact c9 i hi he'
  · rw [haeq] at he' ⊢
    exact c10 i hi he'
  · rw [haeq] at he' ⊢
    exact c11 i hi he'
  · rw [haeq] at he' ⊢
    exact c12 i hi he'
  · rw [haeq] at he' ⊢
    exact c13 i hi he'
  · rw [haeq] at he' ⊢
    exact c14 i hi he'
  · rw [haeq] at he' ⊢
    exact c15 i hi he'
lemma roughPart29 : ∀ a' < 334, Even (1024 * 29 + a') → goodRough (1024 * 29 + a') := by
  have c0 : ∀ i < 64, Even (1024 * 29 + (64 * 0 + i)) → goodRough (1024 * 29 + (64 * 0 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 29 + (64 * 0 + t)) → goodRough (1024 * 29 + (64 * 0 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c1 : ∀ i < 64, Even (1024 * 29 + (64 * 1 + i)) → goodRough (1024 * 29 + (64 * 1 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 29 + (64 * 1 + t)) → goodRough (1024 * 29 + (64 * 1 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c2 : ∀ i < 64, Even (1024 * 29 + (64 * 2 + i)) → goodRough (1024 * 29 + (64 * 2 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 29 + (64 * 2 + t)) → goodRough (1024 * 29 + (64 * 2 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c3 : ∀ i < 64, Even (1024 * 29 + (64 * 3 + i)) → goodRough (1024 * 29 + (64 * 3 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 29 + (64 * 3 + t)) → goodRough (1024 * 29 + (64 * 3 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c4 : ∀ i < 64, Even (1024 * 29 + (64 * 4 + i)) → goodRough (1024 * 29 + (64 * 4 + i)) := by
    have h : (List.range 64).all (fun t => decide (Even (1024 * 29 + (64 * 4 + t)) → goodRough (1024 * 29 + (64 * 4 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  have c5 : ∀ i < 14, Even (1024 * 29 + (64 * 5 + i)) → goodRough (1024 * 29 + (64 * 5 + i)) := by
    have h : (List.range 14).all (fun t => decide (Even (1024 * 29 + (64 * 5 + t)) → goodRough (1024 * 29 + (64 * 5 + t)))) = true := by decide
    rw [List.all_eq_true] at h
    intro i hi
    exact of_decide_eq_true (h i (List.mem_range.mpr hi))
  intro a' ha' he'
  set q := a' / 64 with hq
  set i := a' % 64 with hi_def
  have hqG : q < 6 := by omega
  have hi : i < 64 := by omega
  have haeq : a' = 64 * q + i := by omega
  interval_cases q
  · rw [haeq] at he' ⊢
    exact c0 i hi he'
  · rw [haeq] at he' ⊢
    exact c1 i hi he'
  · rw [haeq] at he' ⊢
    exact c2 i hi he'
  · rw [haeq] at he' ⊢
    exact c3 i hi he'
  · rw [haeq] at he' ⊢
    exact c4 i hi he'
  · rw [haeq] at he' ⊢
    have hik : i < 14 := by omega
    exact c5 i hik he'
end PEqualNP.Outside

theorem PEqualNP.Outside.L_goldbach_finite_residue_rough_30030 :
    ∀ a : ℕ, a < 30030 → Even a → ∃ p ∈ ({3,5,7,11,31,43,61,79,149,197} : Finset ℕ), Nat.Coprime ((a+30030-p)%30030) 30030 := by
  intro a ha he
  set q := a / 1024 with hq
  have hqlt : q < 30 := by omega
  have haeq : a = 1024 * q + a % 1024 := by omega
  interval_cases q
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart0 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart1 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart2 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart3 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart4 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart5 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart6 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart7 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart8 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart9 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart10 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart11 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart12 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart13 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart14 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart15 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart16 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart17 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart18 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart19 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart20 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart21 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart22 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart23 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart24 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart25 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart26 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart27 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart28 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
  · rw [haeq] at he ⊢
    obtain ⟨p, hpS, hmod⟩ := PEqualNP.Outside.roughPart29 (a % 1024) (by omega) he
    exact ⟨p, hpS, PEqualNP.Outside.roughCoprime _ p hpS hmod⟩
