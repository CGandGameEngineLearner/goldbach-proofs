import Mathlib

set_option maxHeartbeats 4000000

open Set

private lemma mono_step {f : ℝ → ℝ} {x : ℝ} (hx : 0 ≤ x)
    (hcont : ContinuousOn f (Set.Icc 0 x))
    (hdiff : DifferentiableOn ℝ f (Set.Ioo 0 x))
    (h0 : f 0 = 0)
    (hderiv : ∀ t ∈ Set.Ioo 0 x, 0 ≤ deriv f t) : 0 ≤ f x := by
  have hmono : MonotoneOn f (Set.Icc 0 x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hcont ?_ ?_
    · simpa [interior_Icc] using hdiff
    · intro t ht
      rw [interior_Icc] at ht
      exact hderiv t ht
  have h1 : f 0 ≤ f x := hmono (Set.left_mem_Icc.mpr hx) (Set.right_mem_Icc.mpr hx) hx
  rwa [h0] at h1

private noncomputable abbrev P3 : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24
private noncomputable abbrev P4 : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720
private noncomputable abbrev P5 : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320
private noncomputable abbrev P6 : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320
  - t ^ 10 / 3628800
private noncomputable abbrev P7 : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320
  - t ^ 10 / 3628800 + t ^ 12 / 479001600
private noncomputable abbrev P8 : ℝ → ℝ := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320
  - t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200

private noncomputable abbrev Q2 : ℝ → ℝ := fun t => t - t ^ 3 / 6
private noncomputable abbrev Q3 : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120
private noncomputable abbrev Q4 : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040
private noncomputable abbrev Q5 : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880
private noncomputable abbrev Q6 : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880
  - t ^ 11 / 39916800
private noncomputable abbrev Q7 : ℝ → ℝ := fun t => t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880
  - t ^ 11 / 39916800 + t ^ 13 / 6227020800

private lemma dP3 (t : ℝ) : deriv P3 t = -t + t ^ 3 / 6 := by
  rw [show P3 = ((fun t : ℝ => 1 - t ^ 2 / 2) + fun t : ℝ => t ^ 4 / 24) from rfl]
  rw [deriv_add (by fun_prop) (by fun_prop)]
  rw [show deriv (fun t : ℝ => 1 - t ^ 2 / 2) t = -t from by simp]
  rw [show deriv (fun t : ℝ => t ^ 4 / 24) t = t ^ 3 / 6 from by simp <;> ring]

private lemma dQ2 (t : ℝ) : deriv Q2 t = 1 - t ^ 2 / 2 := by
  rw [show Q2 = ((fun t : ℝ => t) - fun t : ℝ => t ^ 3 / 6) from rfl]
  rw [deriv_sub (by fun_prop) (by fun_prop)]
  rw [show deriv (fun t : ℝ => t) t = 1 from by simp]
  rw [show deriv (fun t : ℝ => t ^ 3 / 6) t = t ^ 2 / 2 from by simp <;> ring]

private lemma dP4 (t : ℝ) : deriv P4 t = -(Q3 t) := by
  rw [show P4 = (P3 - fun t : ℝ => t ^ 6 / 720) from rfl]
  rw [deriv_sub (by fun_prop) (by fun_prop), dP3 t]
  rw [show deriv (fun t : ℝ => t ^ 6 / 720) t = t ^ 5 / 120 from by simp <;> ring]
  simp only [Q3]
  all_goals ring

private lemma dQ3 (t : ℝ) : deriv Q3 t = P3 t := by
  rw [show Q3 = (Q2 + fun t : ℝ => t ^ 5 / 120) from rfl]
  rw [deriv_add (by fun_prop) (by fun_prop), dQ2 t]
  rw [show deriv (fun t : ℝ => t ^ 5 / 120) t = t ^ 4 / 24 from by simp <;> ring]

private lemma dP5 (t : ℝ) : deriv P5 t = -(Q4 t) := by
  rw [show P5 = (P4 + fun t : ℝ => t ^ 8 / 40320) from rfl]
  rw [deriv_add (by fun_prop) (by fun_prop), dP4 t]
  rw [show deriv (fun t : ℝ => t ^ 8 / 40320) t = t ^ 7 / 5040 from by simp <;> ring]
  simp only [Q4, Q3]
  all_goals ring

private lemma dQ4 (t : ℝ) : deriv Q4 t = P4 t := by
  rw [show Q4 = (Q3 - fun t : ℝ => t ^ 7 / 5040) from rfl]
  rw [deriv_sub (by fun_prop) (by fun_prop), dQ3 t]
  rw [show deriv (fun t : ℝ => t ^ 7 / 5040) t = t ^ 6 / 720 from by simp <;> ring]

private lemma dP6 (t : ℝ) : deriv P6 t = -(Q5 t) := by
  rw [show P6 = (P5 - fun t : ℝ => t ^ 10 / 3628800) from rfl]
  rw [deriv_sub (by fun_prop) (by fun_prop), dP5 t]
  rw [show deriv (fun t : ℝ => t ^ 10 / 3628800) t = t ^ 9 / 362880 from by simp <;> ring]
  simp only [Q5, Q4, Q3]
  all_goals ring

private lemma dQ5 (t : ℝ) : deriv Q5 t = P5 t := by
  rw [show Q5 = (Q4 + fun t : ℝ => t ^ 9 / 362880) from rfl]
  rw [deriv_add (by fun_prop) (by fun_prop), dQ4 t]
  rw [show deriv (fun t : ℝ => t ^ 9 / 362880) t = t ^ 8 / 40320 from by simp <;> ring]

private lemma dP7 (t : ℝ) : deriv P7 t = -(Q6 t) := by
  rw [show P7 = (P6 + fun t : ℝ => t ^ 12 / 479001600) from rfl]
  rw [deriv_add (by fun_prop) (by fun_prop), dP6 t]
  rw [show deriv (fun t : ℝ => t ^ 12 / 479001600) t = t ^ 11 / 39916800 from by simp <;> ring]
  simp only [Q6, Q5, Q4, Q3]
  all_goals ring

private lemma dQ6 (t : ℝ) : deriv Q6 t = P6 t := by
  rw [show Q6 = (Q5 - fun t : ℝ => t ^ 11 / 39916800) from rfl]
  rw [deriv_sub (by fun_prop) (by fun_prop), dQ5 t]
  rw [show deriv (fun t : ℝ => t ^ 11 / 39916800) t = t ^ 10 / 3628800 from by simp <;> ring]

private lemma dP8 (t : ℝ) : deriv P8 t = -(Q7 t) := by
  rw [show P8 = (P7 - fun t : ℝ => t ^ 14 / 87178291200) from rfl]
  rw [deriv_sub (by fun_prop) (by fun_prop), dP7 t]
  rw [show deriv (fun t : ℝ => t ^ 14 / 87178291200) t = t ^ 13 / 6227020800 from by simp <;> ring]
  simp only [Q7, Q6, Q5, Q4, Q3]
  all_goals ring

private lemma dQ7 (t : ℝ) : deriv Q7 t = P7 t := by
  rw [show Q7 = (Q6 + fun t : ℝ => t ^ 13 / 6227020800) from rfl]
  rw [deriv_add (by fun_prop) (by fun_prop), dQ6 t]
  rw [show deriv (fun t : ℝ => t ^ 13 / 6227020800) t = t ^ 12 / 479001600 from by simp <;> ring]

private lemma cos_le_P3 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ P3 x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => P3 t - Real.cos t) t = Real.sin t - Q2 t := by
    intro t
    rw [show (fun t : ℝ => P3 t - Real.cos t) = (P3 - Real.cos) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dP3 t]
    rw [show deriv Real.cos t = -Real.sin t from Real.deriv_cos]
    ring
  have hmain : 0 ≤ (fun t : ℝ => P3 t - Real.cos t) x := by
    refine mono_step (f := fun t : ℝ => P3 t - Real.cos t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [P3]
    · intro t ht
      rw [hd t]
      have h := Real.sin_ge_sub_cube (le_of_lt ht.1)
      have hq : Q2 t = t - t ^ 3 / 6 := rfl
      linarith
  simpa using hmain

private lemma sin_le_Q3 (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ Q3 x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => Q3 t - Real.sin t) t = P3 t - Real.cos t := by
    intro t
    rw [show (fun t : ℝ => Q3 t - Real.sin t) = (Q3 - Real.sin) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dQ3 t]
    rw [show deriv Real.sin t = Real.cos t from by rw [Real.deriv_sin]]
  have hmain : 0 ≤ (fun t : ℝ => Q3 t - Real.sin t) x := by
    refine mono_step (f := fun t : ℝ => Q3 t - Real.sin t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [Q3]
    · intro t ht
      rw [hd t]
      exact sub_nonneg.mpr (cos_le_P3 t (le_of_lt ht.1))
  simpa using hmain

private lemma cos_ge_P4 (x : ℝ) (hx : 0 ≤ x) : P4 x ≤ Real.cos x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => Real.cos t - P4 t) t = Q3 t - Real.sin t := by
    intro t
    rw [show (fun t : ℝ => Real.cos t - P4 t) = (Real.cos - P4) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dP4 t]
    rw [show deriv Real.cos t = -Real.sin t from Real.deriv_cos]
    ring
  have hmain : 0 ≤ (fun t : ℝ => Real.cos t - P4 t) x := by
    refine mono_step (f := fun t : ℝ => Real.cos t - P4 t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [P4]
    · intro t ht
      rw [hd t]
      exact sub_nonneg.mpr (sin_le_Q3 t (le_of_lt ht.1))
  simpa using hmain

private lemma sin_ge_Q4 (x : ℝ) (hx : 0 ≤ x) : Q4 x ≤ Real.sin x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => Real.sin t - Q4 t) t = Real.cos t - P4 t := by
    intro t
    rw [show (fun t : ℝ => Real.sin t - Q4 t) = (Real.sin - Q4) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dQ4 t]
    rw [show deriv Real.sin t = Real.cos t from by rw [Real.deriv_sin]]
  have hmain : 0 ≤ (fun t : ℝ => Real.sin t - Q4 t) x := by
    refine mono_step (f := fun t : ℝ => Real.sin t - Q4 t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [Q4]
    · intro t ht
      rw [hd t]
      exact sub_nonneg.mpr (cos_ge_P4 t (le_of_lt ht.1))
  simpa using hmain

private lemma cos_le_P5 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ P5 x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => P5 t - Real.cos t) t = Real.sin t - Q4 t := by
    intro t
    rw [show (fun t : ℝ => P5 t - Real.cos t) = (P5 - Real.cos) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dP5 t]
    rw [show deriv Real.cos t = -Real.sin t from Real.deriv_cos]
    ring
  have hmain : 0 ≤ (fun t : ℝ => P5 t - Real.cos t) x := by
    refine mono_step (f := fun t : ℝ => P5 t - Real.cos t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [P5]
    · intro t ht
      rw [hd t]
      exact sub_nonneg.mpr (sin_ge_Q4 t (le_of_lt ht.1))
  simpa using hmain

private lemma sin_le_Q5 (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ Q5 x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => Q5 t - Real.sin t) t = P5 t - Real.cos t := by
    intro t
    rw [show (fun t : ℝ => Q5 t - Real.sin t) = (Q5 - Real.sin) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dQ5 t]
    rw [show deriv Real.sin t = Real.cos t from by rw [Real.deriv_sin]]
  have hmain : 0 ≤ (fun t : ℝ => Q5 t - Real.sin t) x := by
    refine mono_step (f := fun t : ℝ => Q5 t - Real.sin t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [Q5]
    · intro t ht
      rw [hd t]
      exact sub_nonneg.mpr (cos_le_P5 t (le_of_lt ht.1))
  simpa using hmain

private lemma cos_ge_P6 (x : ℝ) (hx : 0 ≤ x) : P6 x ≤ Real.cos x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => Real.cos t - P6 t) t = Q5 t - Real.sin t := by
    intro t
    rw [show (fun t : ℝ => Real.cos t - P6 t) = (Real.cos - P6) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dP6 t]
    rw [show deriv Real.cos t = -Real.sin t from Real.deriv_cos]
    ring
  have hmain : 0 ≤ (fun t : ℝ => Real.cos t - P6 t) x := by
    refine mono_step (f := fun t : ℝ => Real.cos t - P6 t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [P6]
    · intro t ht
      rw [hd t]
      exact sub_nonneg.mpr (sin_le_Q5 t (le_of_lt ht.1))
  simpa using hmain

private lemma sin_ge_Q6 (x : ℝ) (hx : 0 ≤ x) : Q6 x ≤ Real.sin x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => Real.sin t - Q6 t) t = Real.cos t - P6 t := by
    intro t
    rw [show (fun t : ℝ => Real.sin t - Q6 t) = (Real.sin - Q6) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dQ6 t]
    rw [show deriv Real.sin t = Real.cos t from by rw [Real.deriv_sin]]
  have hmain : 0 ≤ (fun t : ℝ => Real.sin t - Q6 t) x := by
    refine mono_step (f := fun t : ℝ => Real.sin t - Q6 t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [Q6]
    · intro t ht
      rw [hd t]
      exact sub_nonneg.mpr (cos_ge_P6 t (le_of_lt ht.1))
  simpa using hmain

private lemma cos_le_P7 (x : ℝ) (hx : 0 ≤ x) : Real.cos x ≤ P7 x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => P7 t - Real.cos t) t = Real.sin t - Q6 t := by
    intro t
    rw [show (fun t : ℝ => P7 t - Real.cos t) = (P7 - Real.cos) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dP7 t]
    rw [show deriv Real.cos t = -Real.sin t from Real.deriv_cos]
    ring
  have hmain : 0 ≤ (fun t : ℝ => P7 t - Real.cos t) x := by
    refine mono_step (f := fun t : ℝ => P7 t - Real.cos t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [P7]
    · intro t ht
      rw [hd t]
      exact sub_nonneg.mpr (sin_ge_Q6 t (le_of_lt ht.1))
  simpa using hmain

private lemma sin_le_Q7 (x : ℝ) (hx : 0 ≤ x) : Real.sin x ≤ Q7 x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => Q7 t - Real.sin t) t = P7 t - Real.cos t := by
    intro t
    rw [show (fun t : ℝ => Q7 t - Real.sin t) = (Q7 - Real.sin) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dQ7 t]
    rw [show deriv Real.sin t = Real.cos t from by rw [Real.deriv_sin]]
  have hmain : 0 ≤ (fun t : ℝ => Q7 t - Real.sin t) x := by
    refine mono_step (f := fun t : ℝ => Q7 t - Real.sin t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [Q7]
    · intro t ht
      rw [hd t]
      exact sub_nonneg.mpr (cos_le_P7 t (le_of_lt ht.1))
  simpa using hmain

theorem cos_ge_taylor14 (x : ℝ) (hx : 0 ≤ x) : P8 x ≤ Real.cos x := by
  have hd : ∀ t : ℝ, deriv (fun t : ℝ => Real.cos t - P8 t) t = Q7 t - Real.sin t := by
    intro t
    rw [show (fun t : ℝ => Real.cos t - P8 t) = (Real.cos - P8) from rfl]
    rw [deriv_sub (by fun_prop) (by fun_prop), dP8 t]
    rw [show deriv Real.cos t = -Real.sin t from Real.deriv_cos]
    ring
  have hmain : 0 ≤ (fun t : ℝ => Real.cos t - P8 t) x := by
    refine mono_step (f := fun t : ℝ => Real.cos t - P8 t) hx (by fun_prop) (by fun_prop) ?_ ?_
    · simp [P8]
    · intro t ht
      rw [hd t]
      exact sub_nonneg.mpr (sin_le_Q7 t (le_of_lt ht.1))
  simpa using hmain
private def Lw (w : ℕ) : ℕ :=
  ((Finset.range 15).filter (fun i => w.testBit i ≠ w.testBit (i + 1))).card
private def Wt (w : ℕ) : ℕ := 17 ^ (Lw w) * 183 ^ (15 - Lw w)
private def Dw (w : ℕ) : ℕ := min w (65536 - w)
private def MM (k : ℕ) : ℕ :=
  ∑ a ∈ Finset.range 256, ∑ b ∈ Finset.range 256, Wt (256 * a + b) * (Dw (256 * a + b)) ^ (2 * k)


private noncomputable def coef (k : ℕ) : ℝ := (-1 : ℝ) ^ k / (Nat.factorial (2 * k) : ℝ)
private noncomputable def y : ℝ := 2 * Real.pi / 65536

private lemma P8_eq_sum (x : ℝ) :
    P8 x = ∑ k ∈ Finset.range 8, coef k * x ^ (2 * k) := by
  simp [P8, coef, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring
private lemma mm0 : MM 0 = 65536000000000000000000000000000000 := by native_decide
private lemma mm1 : MM 1 = 6816321645532327741492287912169474497708032 := by native_decide
private lemma mm2 : MM 2 = 5577513720022978514822244508628905347402978157395968 := by native_decide
private lemma mm3 : MM 3 = 5469873556530933126422172753179938808934193750556206256095232 := by native_decide
private lemma mm4 : MM 4 = 5616174026770673965654196784886675418318303963445712203637094264864768 := by native_decide
private lemma mm5 : MM 5 = 5854845365403969522235084787634683688780462192001413201756130724339691586322432 := by native_decide
private lemma mm6 : MM 6 = 6144411029942511749160273957705038724268824073611313403658766613474190330471286537453568 := by native_decide
private lemma mm7 : MM 7 = 6472721346408609947965370229680190376572919820400885042283754558484355619916232065839304783429632 := by native_decide

private lemma expand_gen {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    (∑ w ∈ s, (Wt (f w) : ℝ) * (∑ k ∈ Finset.range 8, coef k * (y * (Dw (f w) : ℝ)) ^ (2 * k)))
      = ∑ k ∈ Finset.range 8, coef k * y ^ (2 * k) *
          (∑ w ∈ s, (Wt (f w) : ℝ) * (Dw (f w) : ℝ) ^ (2 * k)) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => Finset.sum_congr rfl (fun w hw => ?_))
  rw [mul_pow]
  ring
private lemma cos_symm (w : ℕ) (hw : w < 65536) :
    Real.cos (2 * Real.pi * (w : ℝ) / 65536)
      = Real.cos (2 * Real.pi * ((Dw w : ℕ) : ℝ) / 65536) := by
  have hwle : w ≤ 65536 := le_of_lt hw
  by_cases hle : w ≤ 32768
  · have hDw : Dw w = w := by rw [Dw, Nat.min_eq_left]; omega
    rw [hDw]
  · have hgt : 32768 < w := by omega
    have hDw : Dw w = 65536 - w := by rw [Dw, Nat.min_eq_right]; omega
    rw [hDw]
    have hcast : ((65536 - w : ℕ) : ℝ) = 65536 - (w : ℝ) := by
      rw [Nat.cast_sub hwle]; norm_num
    rw [hcast]
    have harg : 2 * Real.pi * (65536 - (w : ℝ)) / 65536
        = 2 * Real.pi - 2 * Real.pi * (w : ℝ) / 65536 := by ring
    rw [harg, Real.cos_two_pi_sub]
private noncomputable def Ps (d : ℝ) : ℝ := ∑ k ∈ Finset.range 8, coef k * (y * d) ^ (2 * k)

private lemma Ps_eq (d : ℝ) : Ps d = P8 (y * d) := by
  rw [P8_eq_sum]
  rfl

private lemma pointwise {w : ℕ} (hw : w < 65536) (c : ℝ) (hc : 0 ≤ c) :
    c * Ps (Dw w : ℝ) ≤ c * Real.cos (2 * Real.pi * (w : ℝ) / 65536) := by
  have hy0 : 0 ≤ y := by unfold y; positivity
  have hd0 : 0 ≤ y * (Dw w : ℝ) := mul_nonneg hy0 (Nat.cast_nonneg _)
  have harg : 2 * Real.pi * ((Dw w : ℕ) : ℝ) / 65536 = y * (Dw w : ℝ) := by
    unfold y; ring
  have h1 : Ps (Dw w : ℝ) ≤ Real.cos (2 * Real.pi * (w : ℝ) / 65536) := by
    rw [Ps_eq, cos_symm w hw, harg]
    exact cos_ge_taylor14 _ hd0
  exact mul_le_mul_of_nonneg_left h1 hc

private lemma sum_le :
    (∑ a ∈ Finset.range 256, ∑ b ∈ Finset.range 256, ((Wt (256 * a + b) : ℕ) : ℝ) * Ps ((Dw (256 * a + b) : ℕ) : ℝ))
      ≤ ∑ a ∈ Finset.range 256, ∑ b ∈ Finset.range 256,
        ((Wt (256 * a + b) : ℕ) : ℝ) * Real.cos (2 * Real.pi * ((256 * a + b : ℕ) : ℝ) / 65536) := by
  refine Finset.sum_le_sum (fun a ha => Finset.sum_le_sum (fun b hb => ?_))
  have ha' : a < 256 := Finset.mem_range.mp ha
  have hb' : b < 256 := Finset.mem_range.mp hb
  have hw : 256 * a + b < 65536 := by omega
  exact pointwise hw ((Wt (256 * a + b) : ℕ) : ℝ) (Nat.cast_nonneg _)
private lemma mm_cast (k : ℕ) :
    (MM k : ℝ) = ∑ a ∈ Finset.range 256, ∑ b ∈ Finset.range 256,
      ((Wt (256 * a + b) : ℕ) : ℝ) * (Dw (256 * a + b) : ℝ) ^ (2 * k) := by
  rw [MM]
  push_cast
  rfl
private lemma main_expand :
    (∑ a ∈ Finset.range 256, ∑ b ∈ Finset.range 256, ((Wt (256 * a + b) : ℕ) : ℝ) * Ps ((Dw (256 * a + b) : ℕ) : ℝ))
      = ∑ k ∈ Finset.range 8, coef k * y ^ (2 * k) * (MM k : ℝ) := by
  simp only [Ps]
  simp only [Finset.mul_sum]
  have hsw1 : (∑ a ∈ Finset.range 256, ∑ b ∈ Finset.range 256, ∑ k ∈ Finset.range 8,
        ((Wt (256 * a + b) : ℕ) : ℝ) * (coef k * (y * (Dw (256 * a + b) : ℝ)) ^ (2 * k)))
      = ∑ a ∈ Finset.range 256, ∑ k ∈ Finset.range 8, ∑ b ∈ Finset.range 256,
        ((Wt (256 * a + b) : ℕ) : ℝ) * (coef k * (y * (Dw (256 * a + b) : ℝ)) ^ (2 * k)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Finset.sum_comm
  rw [hsw1]
  have hsw2 : (∑ a ∈ Finset.range 256, ∑ k ∈ Finset.range 8, ∑ b ∈ Finset.range 256,
        ((Wt (256 * a + b) : ℕ) : ℝ) * (coef k * (y * (Dw (256 * a + b) : ℝ)) ^ (2 * k)))
      = ∑ k ∈ Finset.range 8, ∑ a ∈ Finset.range 256, ∑ b ∈ Finset.range 256,
        ((Wt (256 * a + b) : ℕ) : ℝ) * (coef k * (y * (Dw (256 * a + b) : ℝ)) ^ (2 * k)) := by
    exact Finset.sum_comm
  rw [hsw2]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [mm_cast k]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  rw [mul_pow]
  ring

private def qL : ℚ := 2 * (314159265358979323846 / 10 ^ 20) / 65536
private def qH : ℚ := 2 * (314159265358979323847 / 10 ^ 20) / 65536
private noncomputable def yL : ℝ := ((qL : ℚ) : ℝ)
private noncomputable def yH : ℝ := ((qH : ℚ) : ℝ)
private def coefQ (k : ℕ) : ℚ := (-1 : ℚ) ^ k / (Nat.factorial (2 * k) : ℚ)

private lemma coef_eq_Q (k : ℕ) : coef k = ((coefQ k : ℚ) : ℝ) := by
  rw [coef, coefQ]; push_cast; ring

private lemma y_bounds : yL ≤ y ∧ y ≤ yH := by
  have hL : (314159265358979323846 : ℝ) / 10 ^ 20 < Real.pi := by
    have h := Real.pi_gt_d20
    have h' : (3.14159265358979323846 : ℝ) = 314159265358979323846 / 10 ^ 20 := by norm_num
    linarith
  have hH : Real.pi < (314159265358979323847 : ℝ) / 10 ^ 20 := by
    have h := Real.pi_lt_d20
    have h' : (3.14159265358979323847 : ℝ) = 314159265358979323847 / 10 ^ 20 := by norm_num
    linarith
  constructor
  · unfold yL y qL; push_cast; linarith
  · unfold yH y qH; push_cast; linarith

private lemma term_even (k : ℕ) (hk : (0 : ℝ) ≤ coef k)
    (hp : yL ^ (2 * k) ≤ y ^ (2 * k)) :
    (coef k * yL ^ (2 * k)) * (MM k : ℝ) ≤ (coef k * y ^ (2 * k)) * (MM k : ℝ) :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hk) (Nat.cast_nonneg _)

private lemma term_odd (k : ℕ) (hk : coef k ≤ 0)
    (hp : y ^ (2 * k) ≤ yH ^ (2 * k)) :
    (coef k * yH ^ (2 * k)) * (MM k : ℝ) ≤ (coef k * y ^ (2 * k)) * (MM k : ℝ) :=
  mul_le_mul_of_nonneg_right (mul_le_mul_of_nonpos_left hp hk) (Nat.cast_nonneg _)

private lemma sum8 {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    (∑ k ∈ Finset.range 8, f k) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]

private lemma final_num :
    (1863 / 2500 : ℚ) * (2 * (200 : ℚ) ^ 15) <
      ((65536000000000000000000000000000000 : ℚ)
        + coefQ 1 * qH ^ 2 * 6816321645532327741492287912169474497708032
        + coefQ 2 * qL ^ 4 * 5577513720022978514822244508628905347402978157395968
        + coefQ 3 * qH ^ 6 * 5469873556530933126422172753179938808934193750556206256095232
        + coefQ 4 * qL ^ 8 * 5616174026770673965654196784886675418318303963445712203637094264864768
        + coefQ 5 * qH ^ 10 * 5854845365403969522235084787634683688780462192001413201756130724339691586322432
        + coefQ 6 * qL ^ 12 * 6144411029942511749160273957705038724268824073611313403658766613474190330471286537453568
        + coefQ 7 * qH ^ 14 * 6472721346408609947965370229680190376572919820400885042283754558484355619916232065839304783429632) := by
  native_decide

private lemma final_bound :
    (1863 / 2500 : ℝ) * (2 * (200 : ℝ) ^ 15)
      < ∑ k ∈ Finset.range 8, coef k * y ^ (2 * k) * (MM k : ℝ) := by
  obtain ⟨hyL, hyH⟩ := y_bounds
  have hyLpos : (0 : ℝ) ≤ yL := by unfold yL qL; push_cast; norm_num
  have hyp : (0 : ℝ) ≤ y := by unfold y; positivity
  have hc0 : (0 : ℝ) ≤ coef 0 := by norm_num [coef]
  have hc1 : coef 1 ≤ 0 := by norm_num [coef]
  have hc2 : (0 : ℝ) ≤ coef 2 := by norm_num [coef]
  have hc3 : coef 3 ≤ 0 := by norm_num [coef]
  have hc4 : (0 : ℝ) ≤ coef 4 := by norm_num [coef]
  have hc5 : coef 5 ≤ 0 := by norm_num [coef]
  have hc6 : (0 : ℝ) ≤ coef 6 := by norm_num [coef]
  have hc7 : coef 7 ≤ 0 := by norm_num [coef]
  have hp1 : y ^ (2 * 1) ≤ yH ^ (2 * 1) := pow_le_pow_left₀ hyp hyH (2 * 1)
  have hp3 : y ^ (2 * 3) ≤ yH ^ (2 * 3) := pow_le_pow_left₀ hyp hyH (2 * 3)
  have hp5 : y ^ (2 * 5) ≤ yH ^ (2 * 5) := pow_le_pow_left₀ hyp hyH (2 * 5)
  have hp7 : y ^ (2 * 7) ≤ yH ^ (2 * 7) := pow_le_pow_left₀ hyp hyH (2 * 7)
  have hp2 : yL ^ (2 * 2) ≤ y ^ (2 * 2) := pow_le_pow_left₀ hyLpos hyL (2 * 2)
  have hp4 : yL ^ (2 * 4) ≤ y ^ (2 * 4) := pow_le_pow_left₀ hyLpos hyL (2 * 4)
  have hp6 : yL ^ (2 * 6) ≤ y ^ (2 * 6) := pow_le_pow_left₀ hyLpos hyL (2 * 6)
  have h0 : (coef 0 * yL ^ (2 * 0)) * (MM 0 : ℝ) ≤ (coef 0 * y ^ (2 * 0)) * (MM 0 : ℝ) :=
    term_even 0 hc0 le_rfl
  have h1 := term_odd 1 hc1 hp1
  have h2 := term_even 2 hc2 hp2
  have h3 := term_odd 3 hc3 hp3
  have h4 := term_even 4 hc4 hp4
  have h5 := term_odd 5 hc5 hp5
  have h6 := term_even 6 hc6 hp6
  have h7 := term_odd 7 hc7 hp7
  have hq : (∑ k ∈ Finset.range 8,
        (if k % 2 = 0 then coefQ k * qL ^ (2 * k) else coefQ k * qH ^ (2 * k)) * ((MM k : ℕ) : ℚ))
      = ((65536000000000000000000000000000000 : ℚ)
        + coefQ 1 * qH ^ 2 * 6816321645532327741492287912169474497708032
        + coefQ 2 * qL ^ 4 * 5577513720022978514822244508628905347402978157395968
        + coefQ 3 * qH ^ 6 * 5469873556530933126422172753179938808934193750556206256095232
        + coefQ 4 * qL ^ 8 * 5616174026770673965654196784886675418318303963445712203637094264864768
        + coefQ 5 * qH ^ 10 * 5854845365403969522235084787634683688780462192001413201756130724339691586322432
        + coefQ 6 * qL ^ 12 * 6144411029942511749160273957705038724268824073611313403658766613474190330471286537453568
        + coefQ 7 * qH ^ 14 * 6472721346408609947965370229680190376572919820400885042283754558484355619916232065839304783429632) := by
    rw [sum8,
      if_pos (by norm_num : (0 % 2 = 0)), if_neg (by norm_num : ¬ (1 % 2 = 0)),
      if_pos (by norm_num : (2 % 2 = 0)), if_neg (by norm_num : ¬ (3 % 2 = 0)),
      if_pos (by norm_num : (4 % 2 = 0)), if_neg (by norm_num : ¬ (5 % 2 = 0)),
      if_pos (by norm_num : (6 % 2 = 0)), if_neg (by norm_num : ¬ (7 % 2 = 0))]
    rw [show ((MM 0 : ℕ) : ℚ) = (65536000000000000000000000000000000 : ℚ) from by rw [mm0]; norm_num,
        show ((MM 1 : ℕ) : ℚ) = (6816321645532327741492287912169474497708032 : ℚ) from by rw [mm1]; norm_num,
        show ((MM 2 : ℕ) : ℚ) = (5577513720022978514822244508628905347402978157395968 : ℚ) from by rw [mm2]; norm_num,
        show ((MM 3 : ℕ) : ℚ) = (5469873556530933126422172753179938808934193750556206256095232 : ℚ) from by rw [mm3]; norm_num,
        show ((MM 4 : ℕ) : ℚ) = (5616174026770673965654196784886675418318303963445712203637094264864768 : ℚ) from by rw [mm4]; norm_num,
        show ((MM 5 : ℕ) : ℚ) = (5854845365403969522235084787634683688780462192001413201756130724339691586322432 : ℚ) from by rw [mm5]; norm_num,
        show ((MM 6 : ℕ) : ℚ) = (6144411029942511749160273957705038724268824073611313403658766613474190330471286537453568 : ℚ) from by rw [mm6]; norm_num,
        show ((MM 7 : ℕ) : ℚ) = (6472721346408609947965370229680190376572919820400885042283754558484355619916232065839304783429632 : ℚ) from by rw [mm7]; norm_num]
    simp only [coefQ]
    ring
  have heq : (∑ k ∈ Finset.range 8,
        (if k % 2 = 0 then coef k * yL ^ (2 * k) else coef k * yH ^ (2 * k)) * (MM k : ℝ))
      = ((65536000000000000000000000000000000 : ℚ)
        + coefQ 1 * qH ^ 2 * 6816321645532327741492287912169474497708032
        + coefQ 2 * qL ^ 4 * 5577513720022978514822244508628905347402978157395968
        + coefQ 3 * qH ^ 6 * 5469873556530933126422172753179938808934193750556206256095232
        + coefQ 4 * qL ^ 8 * 5616174026770673965654196784886675418318303963445712203637094264864768
        + coefQ 5 * qH ^ 10 * 5854845365403969522235084787634683688780462192001413201756130724339691586322432
        + coefQ 6 * qL ^ 12 * 6144411029942511749160273957705038724268824073611313403658766613474190330471286537453568
        + coefQ 7 * qH ^ 14 * 6472721346408609947965370229680190376572919820400885042283754558484355619916232065839304783429632 : ℝ) := by
    have hcast : ((∑ k ∈ Finset.range 8,
        (if k % 2 = 0 then coefQ k * qL ^ (2 * k) else coefQ k * qH ^ (2 * k)) * ((MM k : ℕ) : ℚ) : ℚ) : ℝ)
        = ∑ k ∈ Finset.range 8,
          (if k % 2 = 0 then coef k * yL ^ (2 * k) else coef k * yH ^ (2 * k)) * (MM k : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl (fun k hk => ?_)
      rw [coef_eq_Q k]
      unfold yL yH
      push_cast
      simp only [coefQ]
      ring
    rw [← hcast, hq]
  have hsum : (∑ k ∈ Finset.range 8,
        (if k % 2 = 0 then coef k * yL ^ (2 * k) else coef k * yH ^ (2 * k)) * (MM k : ℝ))
      ≤ ∑ k ∈ Finset.range 8, coef k * y ^ (2 * k) * (MM k : ℝ) := by
    conv_lhs => rw [sum8]
    conv_rhs => rw [sum8]
    rw [if_pos (by norm_num : (0 % 2 = 0)), if_neg (by norm_num : ¬ (1 % 2 = 0)),
      if_pos (by norm_num : (2 % 2 = 0)), if_neg (by norm_num : ¬ (3 % 2 = 0)),
      if_pos (by norm_num : (4 % 2 = 0)), if_neg (by norm_num : ¬ (5 % 2 = 0)),
      if_pos (by norm_num : (6 % 2 = 0)), if_neg (by norm_num : ¬ (7 % 2 = 0))]
    linarith [h0, h1, h2, h3, h4, h5, h6, h7]
  refine lt_of_lt_of_le ?_ hsum
  rw [heq]
  have hL2 : (1863 / 2500 : ℝ) * (2 * (200 : ℝ) ^ 15) = ((1863 / 2500 : ℚ) * (2 * (200 : ℚ) ^ 15) : ℚ) := by norm_num
  rw [hL2]
  exact_mod_cast final_num
theorem Conjectures.Cuts.Taskd785031c90b0c9b18dfbd2d3 : (∀ (x1 : ℕ),   x1 = (256 : ℕ) →     have x3 : ℕ → ℕ := fun (x3 : ℕ) => {x4 ∈ Finset.range (15 : ℕ) | x3.testBit x4 ≠ x3.testBit (x4 + (1 : ℕ))}.card;     have x4 : ℕ → ℝ := fun (x4 : ℕ) => ↑((17 : ℕ) ^ x3 x4 * (183 : ℕ) ^ ((15 : ℕ) - x3 x4)) * Real.cos ((2 : ℝ) * Real.pi * ↑x4 / (65536 : ℝ));     have x5 : ℝ := (∑ x5 ∈ Finset.range x1, ∑ x6 ∈ Finset.range x1, x4 (x1 * x5 + x6)) / ((2 : ℝ) * (200 : ℝ) ^ (15 : ℕ));     (1863 / 2500 : ℝ) < x5) := by
  intro x1 hx1
  subst hx1
  dsimp only
  rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (200 : ℝ) ^ 15)]
  calc (1863 / 2500 : ℝ) * (2 * (200 : ℝ) ^ 15)
      < ∑ k ∈ Finset.range 8, coef k * y ^ (2 * k) * (MM k : ℝ) := final_bound
    _ = ∑ a ∈ Finset.range 256, ∑ b ∈ Finset.range 256,
          (Wt (256 * a + b) : ℝ) * Ps (Dw (256 * a + b) : ℝ) := main_expand.symm
    _ ≤ ∑ a ∈ Finset.range 256, ∑ b ∈ Finset.range 256,
          (Wt (256 * a + b) : ℝ) * Real.cos (2 * Real.pi * ((256 * a + b : ℕ) : ℝ) / 65536) := sum_le
