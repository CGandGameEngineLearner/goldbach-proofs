import Mathlib

private lemma inv_sq_aux (a : ℕ) (ha : 2 ≤ a) :
    ∀ b : ℕ, a - 1 ≤ b →
      Finset.sum (Finset.Icc a b) (fun k => 1/(k:ℝ)^2) ≤ 1/((a:ℝ)-1) - 1/(b:ℝ) := by
  intro b hb
  refine Nat.le_induction ?base ?step b hb
  · -- b = a-1
    have hIcc : Finset.Icc a (a-1) = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hIcc]
    simp only [Finset.sum_empty]
    have hcast : (((a-1:ℕ)):ℝ) = (a:ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ a)]
      norm_num
    rw [hcast, sub_self]
  · -- b → b+1
    intro n hn ih
    rw [Finset.sum_Icc_succ_top (by omega : a ≤ n+1)]
    have hbpos : (0:ℝ) < (n:ℝ) := by
      have h1 : 1 ≤ n := by omega
      exact_mod_cast h1
    have hstep : 1/(((n:ℝ)+1))^2 ≤ 1/(n:ℝ) - 1/((n:ℝ)+1) := by
      have hb2 : (0:ℝ) < (n:ℝ)+1 := by positivity
      field_simp
      nlinarith
    push_cast
    nlinarith [hstep, ih]

theorem PEqualNP.Outside.L_goldbach_inverse_square_tail :
    ∀ a b : ℕ, 2≤a → Finset.sum (Finset.Icc a b) (fun k => 1/(k:ℝ)^2) ≤ 1/((a:ℝ)-1) := by
  intro a b ha
  have haR : (2:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
  have hpos : (0:ℝ) < (a:ℝ)-1 := by linarith
  rcases lt_or_ge b (a-1) with hlt | hge
  · have hIcc : Finset.Icc a b = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [hIcc]
    simp only [Finset.sum_empty]
    positivity
  · have haux := inv_sq_aux a ha b hge
    have hbpos : (0:ℝ) < (b:ℝ) := by
      have h1 : 1 ≤ b := by omega
      exact_mod_cast h1
    have hnn : 0 ≤ 1/(b:ℝ) := by positivity
    linarith [haux]
