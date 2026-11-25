import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_finite_singular_product_lower :
    ∀ (S : Finset ℕ), (∀ p ∈ S, Nat.Prime p ∧ 2 < p) → ({3,5,7} : Finset ℕ) ⊆ S → (75/128:ℝ) ≤ ∏ p ∈ S, (1-(1:ℝ)/((p:ℝ)-1)^2) := by
  intro S hS hsub
  let g : ℕ → ℝ := fun p => 1 - (1 : ℝ) / ((p : ℝ) - 1) ^ 2
  change (75 / 128 : ℝ) ≤ ∏ p ∈ S, g p
  have h357 : ∏ p ∈ ({3, 5, 7} : Finset ℕ), g p = 175 / 256 := by
    simp [g]
    norm_num
  set S' : Finset ℕ := S \ ({3, 5, 7} : Finset ℕ)
  have hge11 : ∀ p ∈ S', 11 ≤ p := by
    intro p hp
    rw [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
    have ⟨hprime, hgt2⟩ := hS p hp.1
    by_contra hlt
    push_neg at hlt
    interval_cases p <;> norm_num at hprime hp
  have hg_bounds : ∀ k : ℕ, 11 ≤ k → 0 ≤ g k ∧ g k ≤ 1 := by
    intro k hk
    have hk1 : (10 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (11 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      linarith
    have hsq : (100 : ℝ) ≤ ((k : ℝ) - 1) ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < ((k : ℝ) - 1) ^ 2 := by linarith
    constructor
    · dsimp only [g]
      have hdiv : (1 : ℝ) / ((k : ℝ) - 1) ^ 2 ≤ 1 := by
        rw [div_le_one hpos]
        linarith
      linarith
    · dsimp only [g]
      have hdiv : (0 : ℝ) ≤ (1 : ℝ) / ((k : ℝ) - 1) ^ 2 := by positivity
      linarith
  have htel : ∀ m : ℕ, ∏ k ∈ Finset.Ico 11 (11 + m), g k =
      (9 / 10 : ℝ) * (((m + 10 : ℕ) : ℝ) / ((m + 9 : ℕ) : ℝ)) := by
    intro m
    induction m with
    | zero =>
      simp
      norm_num
    | succ m ih =>
      rw [show 11 + (m + 1) = (11 + m) + 1 by omega]
      rw [Finset.prod_Ico_succ_top (by omega : 11 ≤ 11 + m), ih]
      dsimp only [g]
      push_cast
      have h1 : ((m : ℝ) + 9) ≠ 0 := by positivity
      have h2 : ((m : ℝ) + 10) ≠ 0 := by positivity
      have h3 : (11 + (m : ℝ) - 1) ≠ 0 := by linarith [Nat.cast_nonneg (α := ℝ) m]
      have h4 : ((m : ℝ) + 1 + 9) ≠ 0 := by positivity
      field_simp
      ring
  set m : ℕ := S'.sup id + 1
  have hsub' : S' ⊆ Finset.Ico 11 (11 + m) := by
    intro p hp
    rw [Finset.mem_Ico]
    refine ⟨hge11 p hp, ?_⟩
    have hle : p ≤ S'.sup id := Finset.le_sup (f := id) hp
    omega
  have hsplit := Finset.prod_sdiff hsub'
  have hrest_le : ∏ x ∈ Finset.Ico 11 (11 + m) \ S', g x ≤ 1 := by
    apply Finset.prod_le_one
    · intro x hx
      exact (hg_bounds x (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hx).1).1).1
    · intro x hx
      exact (hg_bounds x (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hx).1).1).2
  have hS'_nonneg : 0 ≤ ∏ x ∈ S', g x := by
    apply Finset.prod_nonneg
    intro x hx
    exact (hg_bounds x (hge11 x hx)).1
  have hico_le : ∏ x ∈ Finset.Ico 11 (11 + m), g x ≤ ∏ x ∈ S', g x := by
    rw [← hsplit]
    nlinarith
  have hratio : (1 : ℝ) ≤ ((m + 10 : ℕ) : ℝ) / ((m + 9 : ℕ) : ℝ) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((m + 9 : ℕ) : ℝ))]
    push_cast
    linarith
  have hico_ge : (9 / 10 : ℝ) ≤ ∏ x ∈ Finset.Ico 11 (11 + m), g x := by
    rw [htel m]
    nlinarith
  have hmain := Finset.prod_sdiff hsub
  rw [← hmain, h357]
  linarith
