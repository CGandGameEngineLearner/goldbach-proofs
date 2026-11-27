import Mathlib

namespace Conjectures.QuadraticPrimes

private def gaussianI : GaussianInt := ⟨0, 1⟩

private theorem gaussian_norm_formula (z : GaussianInt) :
    z.norm = z.re^2 + z.im^2 := by
  rw [Zsqrtd.norm_def]
  ring

/-- The elementary Bézout identity also proves the neighbouring coprimality lemma. -/
private theorem gaussian_conjugates_coprime (n : ℕ) (hn : Even n) :
    IsCoprime ((n : GaussianInt) + gaussianI) ((n : GaussianInt) - gaussianI) := by
  obtain ⟨k, rfl⟩ := hn
  have hi : gaussianI * gaussianI = (-1 : GaussianInt) := by decide +kernel
  rw [Nat.cast_add]
  refine ⟨(k : GaussianInt) - gaussianI, -(k : GaussianInt), ?_⟩
  calc
    _ = -(gaussianI * gaussianI) := by ring
    _ = 1 := by rw [hi, neg_neg]

private theorem gaussian_unit_fourth {z : GaussianInt} (hz : IsUnit z) : z^4 = 1 := by
  have hAbs := Zsqrtd.norm_eq_one_iff.mpr hz
  have hNorm : z.norm = 1 := by
    have h : (z.norm.natAbs : ℤ) = 1 := by exact_mod_cast hAbs
    rwa [GaussianInt.abs_natCast_norm z] at h
  have hSquares : z.re^2 + z.im^2 = 1 := (gaussian_norm_formula z).symm.trans hNorm
  have hAxis : z.re = 0 ∨ z.im = 0 := by
    by_contra! h
    have hr := sq_pos_of_ne_zero h.1
    have hi := sq_pos_of_ne_zero h.2
    omega
  have hProd : z * star z = 1 := by
    rw [← Zsqrtd.norm_eq_mul_conj, hNorm, Int.cast_one]
  have hPower : z^4 = (z^2)^2 := by rw [← pow_mul]
  rw [hPower]
  rcases hAxis with hReal | hImag
  · have hStar : star z = -z := by
      apply Zsqrtd.ext <;> simp [hReal]
    rw [hStar, mul_neg] at hProd
    have hSquare : z^2 = -1 := by
      rw [pow_two]
      exact neg_eq_iff_eq_neg.mp hProd
    rw [hSquare]
    norm_num
  · have hStar : star z = z := by
      apply Zsqrtd.ext <;> simp [hImag]
    rw [hStar] at hProd
    rw [pow_two z, hProd]
    norm_num

private theorem gaussian_odd_root_of_unit (u : GaussianIntˣ) {j : ℕ} (hj : Odd j) :
    (((u : GaussianInt)^j)^j) = (u : GaussianInt) := by
  have hFourth := gaussian_unit_fourth u.isUnit
  obtain ⟨k, hk⟩ := hj
  have hSquare : j * j = 4 * (k * (k + 1)) + 1 := by
    rw [hk]
    ring
  calc
    _ = (u : GaussianInt)^(j * j) := (pow_mul _ _ _).symm
    _ = ((u : GaussianInt)^4)^(k * (k + 1)) * (u : GaussianInt) := by
      rw [hSquare, pow_add, pow_mul, pow_one]
    _ = _ := by rw [hFourth, one_pow, one_mul]

private theorem gaussian_exact_odd_power {n y j : ℕ} (hn : Even n) (hj : Odd j)
    (hEq : n^2 + 1 = y^j) :
    ∃ z : GaussianInt, z^j = (n : GaussianInt) + gaussianI := by
  let _ : GCDMonoid GaussianInt := EuclideanDomain.gcdMonoid GaussianInt
  have hISq : gaussianI^2 = (-1 : GaussianInt) := by decide +kernel
  have hProd : ((n : GaussianInt) + gaussianI) * ((n : GaussianInt) - gaussianI) =
      (y : GaussianInt)^j := by
    calc
      _ = (n : GaussianInt)^2 - gaussianI^2 := by ring
      _ = _ := by
        rw [hISq, sub_neg_eq_add]
        simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_one] using
          congrArg (fun k : ℕ => (k : GaussianInt)) hEq
  have hGcd : IsUnit (gcd ((n : GaussianInt) + gaussianI) ((n : GaussianInt) - gaussianI)) := by
    apply isUnit_of_dvd_one
    obtain ⟨u, v, huv⟩ := gaussian_conjugates_coprime n hn
    rw [← huv]
    exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
      (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _)
  obtain ⟨w, u, hu⟩ := exists_associated_pow_of_mul_eq_pow hGcd hProd
  refine ⟨w * (u : GaussianInt)^j, ?_⟩
  rw [mul_pow, gaussian_odd_root_of_unit u hj]
  exact hu

private theorem gaussian_im_dvd_im_pow (z : GaussianInt) (j : ℕ) : z.im ∣ (z^j).im := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_of_dvd_right (dvd_refl _) _) (dvd_mul_of_dvd_left ih _)

/-- Coprimality gives a Gaussian power up to a unit. Since its exponent is
odd, that unit can be absorbed before reading the imaginary coordinate. -/
theorem OddPowerImaginaryUnit :
    ∀ n y j : ℕ, 0 < n → Even n → 3 ≤ j → Odd j → n^2+1 = y^j → ∃ a : ℤ, a ≠ 0 ∧ Even a ∧ Int.natAbs (((⟨a,1⟩ : GaussianInt)^j).im) = 1 := by
  intro n y j hnPos hn hj3 hj hEq
  obtain ⟨z, hz⟩ := gaussian_exact_odd_power hn hj hEq
  have hIm : ((n : GaussianInt) + gaussianI).im = 1 := by
    change (0 : ℤ) + 1 = 1
    norm_num
  have hDvd := gaussian_im_dvd_im_pow z j
  rw [hz, hIm] at hDvd
  have hSign : z.im = 1 ∨ z.im = -1 := Int.isUnit_iff.mp (isUnit_of_dvd_one hDvd)
  have hImSq : z.im^2 = 1 := by
    rcases hSign with h | h <;> norm_num [h]
  have hNorm : z.norm^j = (n : ℤ)^2 + 1 := by
    calc
      _ = (z^j).norm := (map_pow (Zsqrtd.normMonoidHom (d := (-1 : ℤ))) z j).symm
      _ = _ := by
        rw [hz, gaussian_norm_formula]
        change ((n : ℤ) + 0)^2 + ((0 : ℤ) + 1)^2 = _
        norm_num
  have hRealNe : z.re ≠ 0 := by
    intro h
    have hUnitNorm : z.norm = 1 := by rw [gaussian_norm_formula, h, hImSq]; norm_num
    have hnIntPos : (0 : ℤ) < (n : ℤ) := by exact_mod_cast hnPos
    rw [hUnitNorm, one_pow] at hNorm
    nlinarith only [hNorm, sq_pos_of_ne_zero hnIntPos.ne']
  have hRealEven : Even z.re := by
    by_contra hEven
    have hOdd : Odd z.re := Int.not_even_iff_odd.mp hEven
    have hNormEven : Even z.norm := by
      rw [gaussian_norm_formula, hImSq]
      exact (hOdd.pow (n := 2)).add_odd odd_one
    have hPowerEven : Even (z.norm^j) := hNormEven.pow_of_ne_zero (by omega)
    have hNEven : Even (n : ℤ) := (Int.even_natCast n).mpr hn
    have hNormOdd : Odd ((n : ℤ)^2 + 1) :=
      (hNEven.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)).add_odd odd_one
    rw [hNorm] at hPowerEven
    exact (Int.not_even_iff_odd.mpr hNormOdd) hPowerEven
  refine ⟨z.re, hRealNe, hRealEven, ?_⟩
  rcases hSign with hPos | hNeg
  · have hZ : (⟨z.re, 1⟩ : GaussianInt) = z := by
      apply Zsqrtd.ext
      · rfl
      · exact hPos.symm
    rw [hZ, hz, hIm]
    decide
  · have hZ : (⟨z.re, 1⟩ : GaussianInt) = star z := by
      apply Zsqrtd.ext
      · rfl
      · simp [hNeg]
    rw [hZ, ← star_pow, hz, Zsqrtd.im_star, hIm]
    decide

end Conjectures.QuadraticPrimes
