import Mathlib

theorem PEqualNP.Outside.L_goldbach_exception_ltwo_split :
    ∀ (I : Finset ℕ) (e h : ℕ → ℝ), Finset.sum I (fun n => (e n+h n)^2) ≤ 2*(Finset.sum I (fun n => (e n)^2)+Finset.sum I (fun n => (h n)^2)) := by
  intro I e h
  have hpt : ∀ n : ℕ, (e n + h n)^2 ≤ 2*((e n)^2 + (h n)^2) := by
    intro n
    nlinarith [sq_nonneg (e n - h n)]
  calc
    Finset.sum I (fun n => (e n+h n)^2) ≤ Finset.sum I (fun n => 2*((e n)^2+(h n)^2)) := Finset.sum_le_sum (fun n _ => hpt n)
    _ = 2*(Finset.sum I (fun n => (e n)^2)+Finset.sum I (fun n => (h n)^2)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
