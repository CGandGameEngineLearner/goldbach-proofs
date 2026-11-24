import Mathlib

private lemma euler_prod_ge_half (m : ℕ) :
    (1/2:ℝ) < Finset.prod (Finset.range m) (fun j => 1-1/((j:ℝ)+2)^2) := by
  have htel : ∀ m : ℕ, Finset.prod (Finset.range m) (fun j => 1-1/((j:ℝ)+2)^2) = ((m:ℝ)+2)/(2*((m:ℝ)+1)) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      have h1 : ((m:ℝ)+1) ≠ 0 := by positivity
      have h2 : ((m:ℝ)+2) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  rw [htel m]
  have hpos : (0:ℝ) < 2*((m:ℝ)+1) := by
    have h : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
    linarith
  rw [lt_div_iff₀ hpos]
  push_cast
  nlinarith

private lemma euler_factor_pos (j : ℕ) : 0 < 1-1/(((j:ℝ)+2))^2 := by
  have h2 : (1:ℝ) < ((j:ℝ)+2)^2 := by
    have h : (2:ℝ) ≤ (j:ℝ)+2 := by
      have hj : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      linarith
    nlinarith
  have hpos : (0:ℝ) < ((j:ℝ)+2)^2 := by positivity
  rw [sub_pos, div_lt_one hpos]
  linarith

private lemma euler_factor_le_one (j : ℕ) : 1-1/(((j:ℝ)+2))^2 ≤ 1 := by
  have hpos : (0:ℝ) < ((j:ℝ)+2)^2 := by positivity
  have hnn : 0 ≤ 1/(((j:ℝ)+2)^2) := by positivity
  linarith

theorem PEqualNP.Outside.L_goldbach_euler_subproduct :
    ∀ (m : ℕ) (A : Finset ℕ), A ⊆ Finset.range m → (1/2:ℝ) ≤ Finset.prod A (fun j => 1-1/((j:ℝ)+2)^2) := by
  intro m A hA
  have hfull : (1/2:ℝ) < Finset.prod (Finset.range m) (fun j => 1-1/((j:ℝ)+2)^2) := euler_prod_ge_half m
  have hsplit : Finset.prod (Finset.range m) (fun j => 1-1/((j:ℝ)+2)^2)
      = Finset.prod ((Finset.range m) \ A) (fun j => 1-1/((j:ℝ)+2)^2)
        * Finset.prod A (fun j => 1-1/((j:ℝ)+2)^2) :=
    (Finset.prod_sdiff hA).symm
  have hrest_le : Finset.prod ((Finset.range m) \ A) (fun j => 1-1/((j:ℝ)+2)^2) ≤ 1 := by
    refine Finset.prod_le_one₀ ?_ ?_
    · intro j _
      exact (euler_factor_pos j).le
    · intro j _
      exact euler_factor_le_one j
  have hA_nonneg : 0 ≤ Finset.prod A (fun j => 1-1/((j:ℝ)+2)^2) := by
    refine Finset.prod_nonneg ?_
    intro j _
    exact (euler_factor_pos j).le
  have hchain : Finset.prod (Finset.range m) (fun j => 1-1/((j:ℝ)+2)^2)
      ≤ Finset.prod A (fun j => 1-1/((j:ℝ)+2)^2) := by
    rw [hsplit]
    calc Finset.prod ((Finset.range m) \ A) (fun j => 1-1/((j:ℝ)+2)^2)
          * Finset.prod A (fun j => 1-1/((j:ℝ)+2)^2)
        ≤ 1 * Finset.prod A (fun j => 1-1/((j:ℝ)+2)^2) :=
          mul_le_mul_of_nonneg_right hrest_le hA_nonneg
      _ = Finset.prod A (fun j => 1-1/((j:ℝ)+2)^2) := by rw [one_mul]
  linarith [hfull, hchain]
