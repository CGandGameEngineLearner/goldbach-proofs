import Mathlib

namespace Conjectures.QuadraticPrimes

private theorem gaussianImaginaryDvdPow (w : GaussianInt) (k : ℕ) :
    w.im ∣ (w ^ k).im := by
  induction k with
  | zero => simp [Zsqrtd.im_one]
  | succ k ih =>
    rw [pow_succ, Zsqrtd.im_mul]
    exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left ih _)

private theorem gaussianUnitFourth (u : GaussianInt) (hu : IsUnit u) : u ^ 4 = 1 := by
  rcases u with ⟨r,s⟩
  have hn := (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) _).2 hu
  change r * r - (-1) * s * s = 1 at hn
  have hr : r = -1 ∨ r = 0 ∨ r = 1 := by
    by_contra h
    push_neg at h
    have ht : 2 ≤ r ∨ r ≤ -2 := by omega
    rcases ht with h' | h' <;> nlinarith [sq_nonneg s, sq_nonneg (r - 2), sq_nonneg (r + 2)]
  have hs : s = -1 ∨ s = 0 ∨ s = 1 := by
    by_contra h
    push_neg at h
    have ht : 2 ≤ s ∨ s ≤ -2 := by omega
    rcases ht with h' | h' <;> nlinarith [sq_nonneg r, sq_nonneg (s - 2), sq_nonneg (s + 2)]
  rcases hr with hr | hr | hr <;> rcases hs with hs | hs | hs <;>
    subst r <;> subst s <;> first | decide | norm_num at hn

private theorem gaussianCoprimeEven (n : ℕ) (hn : Even n) :
    IsCoprime (⟨(n : ℤ), 1⟩ : GaussianInt) ⟨(n : ℤ), -1⟩ := by
  obtain ⟨t, ht⟩ := hn
  have hn' : (n : ℤ) = (t : ℤ) + t := by exact_mod_cast ht
  refine ⟨⟨(t : ℤ), -1⟩, ⟨-(t : ℤ), 0⟩, ?_⟩
  apply Zsqrtd.ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul, hn'] <;> ring

private theorem gaussianNormPow (w : GaussianInt) (k : ℕ) :
    (w ^ k).norm = w.norm ^ k := by
  induction k with
  | zero => simp
  | succ k ih => simp [pow_succ, Zsqrtd.norm_mul, ih]

theorem OddPowerImaginaryUnit :
    ∀ n y j : ℕ, 0 < n → Even n → 3 ≤ j → Odd j → n^2+1 = y^j → ∃ a : ℤ, a ≠ 0 ∧ Even a ∧ Int.natAbs (((⟨a,1⟩ : GaussianInt)^j).im) = 1 := by
  intro n y j hn he hj ho hy
  let z : GaussianInt := ⟨(n : ℤ), 1⟩
  let z' : GaussianInt := ⟨(n : ℤ), -1⟩
  have hcast : (n : ℤ)^2 + 1 = (y : ℤ)^j := by exact_mod_cast hy
  have hp : z * z' = ((y : ℤ) : GaussianInt) ^ j := by
    rw [← Int.cast_pow, ← hcast]
    apply Zsqrtd.ext <;> simp [z, z', Zsqrtd.re_mul, Zsqrtd.im_mul, pow_two] <;> ring
  obtain ⟨v, u, hu⟩ := exists_associated_pow_of_mul_eq_pow' (gaussianCoprimeEven n he) hp
  have hu4 : (u : GaussianInt) ^ 4 = 1 := gaussianUnitFourth _ u.isUnit
  obtain ⟨m, hm⟩ := ho
  have hmod : (j*j) % 4 = 1 := by
    have hm' : j = 2*m+1 := hm
    rw [hm']
    have h : (2*m+1)*(2*m+1) = 4*(m*m+m)+1 := by ring
    rw [h]
    omega
  have hroot : ((u : GaussianInt) ^ j) ^ j = u := by
    rw [← pow_mul, pow_eq_pow_mod _ hu4, hmod, pow_one]
  let w : GaussianInt := v * (u : GaussianInt) ^ j
  have hw : w ^ j = z := by simpa [w, mul_pow, hroot] using hu
  obtain ⟨a,b⟩ := w
  have hw' : (⟨a,b⟩ : GaussianInt) ^ j = z := hw
  have him : (((⟨a,b⟩ : GaussianInt) ^ j).im) = 1 := congrArg Zsqrtd.im hw'
  have hb : b ∣ (1 : ℤ) := by
    rw [← him]
    exact gaussianImaginaryDvdPow ⟨a,b⟩ j
  have hb' : b = 1 ∨ b = -1 := Int.isUnit_iff.mp (isUnit_iff_dvd_one.mpr hb)
  have hvnorm : (a*a + b*b)^j = (n : ℤ)*(n : ℤ)+1 := by
    have hv := congrArg Zsqrtd.norm hw'
    rw [gaussianNormPow] at hv
    convert hv using 1 <;> simp [z, Zsqrtd.norm] <;> ring
  have hb2 : b*b = 1 := by rcases hb' with h | h <;> simp [h]
  rw [hb2] at hvnorm
  have ha : a ≠ 0 := by
    intro h
    simp [h] at hvnorm
    have hn' : (0 : ℤ) < n := by exact_mod_cast hn
    nlinarith
  have hae : Even a := by
    by_contra h
    have ham : a % 2 = 1 := by
      have hne : a % 2 ≠ 0 := fun h0 => h (even_iff_two_dvd.mpr (Int.dvd_of_emod_eq_zero h0))
      omega
    have hnm : (n : ℤ) % 2 = 0 := by
      obtain ⟨k, hk⟩ := he
      have hk' : (n : ℤ) = (k : ℤ) + k := by exact_mod_cast hk
      omega
    have hl : (a*a+1) % 2 = 0 := by rw [Int.add_emod, Int.mul_emod a a, ham]; decide
    have hr : ((n : ℤ)*(n : ℤ)+1) % 2 = 1 := by rw [Int.add_emod, Int.mul_emod (n : ℤ) (n : ℤ), hnm]; decide
    have hd : (2 : ℤ) ∣ a*a+1 := Int.dvd_of_emod_eq_zero hl
    have hp' : (2 : ℤ) ∣ (a*a+1)^j := dvd_pow hd (by omega)
    rw [hvnorm] at hp'
    have := Int.emod_eq_zero_of_dvd hp'
    omega
  refine ⟨a, ha, hae, ?_⟩
  rcases hb' with hb' | hb'
  · rw [hb'] at him
    simp [him]
  · have hstar := congrArg star hw'
    rw [star_pow] at hstar
    have hc : star (⟨a,b⟩ : GaussianInt) = ⟨a,1⟩ := by
      rw [Zsqrtd.star_mk, hb']
      rfl
    rw [hc] at hstar
    have h := congrArg Zsqrtd.im hstar
    change (((⟨a,1⟩ : GaussianInt)^j).im) = -1 at h
    rw [h]
    decide

end Conjectures.QuadraticPrimes
