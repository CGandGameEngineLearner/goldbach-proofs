import Mathlib

namespace Conjectures.JoshiAbc.MeanLinear_aux

theorem sum_Icc_one_cast_real (m : ℕ) :
    ((Finset.Icc 1 m).sum (fun j => (j : ℝ))) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hstep : ((Finset.Icc 1 (m + 1)).sum (fun j => (j : ℝ)))
          = ((Finset.Icc 1 m).sum (fun j => (j : ℝ))) + ((m + 1 : ℕ) : ℝ) :=
        Finset.sum_Icc_succ_top (by omega) (fun j => (j : ℝ))
      rw [hstep, ih]
      push_cast
      ring

end Conjectures.JoshiAbc.MeanLinear_aux

theorem Conjectures.JoshiAbc.MeanLinear :
    ∀ m : ℕ, 0 < m → ((Finset.Icc 1 m).sum (fun j => (j:ℝ)))/(m:ℝ) = ((2*(m:ℝ)+1)+1)/4 := by
  intro m hm
  rw [Conjectures.JoshiAbc.MeanLinear_aux.sum_Icc_one_cast_real]
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hm)
  field_simp
  ring
