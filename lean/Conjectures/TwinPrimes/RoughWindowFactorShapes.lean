import Mathlib

namespace Conjectures.TwinPrimes.RoughWindowFactorShapes_aux

theorem z_ge_32 {X : ℕ} (hX : 4096 ≤ X) : 32 ≤ Nat.sqrt X / 2 := by
  have h64 : (64 : ℕ) * 64 ≤ X := by omega
  have hs : (64 : ℕ) ≤ Nat.sqrt X := Nat.le_sqrt.mpr h64
  omega

theorem cube_gt {X : ℕ} (hX : 4096 ≤ X) : 2 * X + 2 < (Nat.sqrt X / 2) ^ 3 := by
  have h64 : (64 : ℕ) * 64 ≤ X := by omega
  have hs : (64 : ℕ) ≤ Nat.sqrt X := Nat.le_sqrt.mpr h64
  have hz : (32 : ℕ) ≤ Nat.sqrt X / 2 := by omega
  have hlt : X < (Nat.sqrt X + 1) * (Nat.sqrt X + 1) := Nat.lt_succ_sqrt X
  have hstep : Nat.sqrt X + 1 ≤ 2 * (Nat.sqrt X / 2) + 2 := by omega
  have hsq : (Nat.sqrt X + 1) * (Nat.sqrt X + 1)
      ≤ (2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2) := by
    have h1 : (Nat.sqrt X + 1) * (Nat.sqrt X + 1)
        ≤ (2 * (Nat.sqrt X / 2) + 2) * (Nat.sqrt X + 1) :=
      mul_le_mul_of_nonneg_right hstep (Nat.zero_le _)
    have h2 : (2 * (Nat.sqrt X / 2) + 2) * (Nat.sqrt X + 1)
        ≤ (2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2) :=
      mul_le_mul_of_nonneg_left hstep (Nat.zero_le _)
    exact le_trans h1 h2
  have hXle : X + 1 ≤ (2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2) := by omega
  have hA : 2 * (Nat.sqrt X / 2) + 2 < 4 * (Nat.sqrt X / 2) := by omega
  have hB : (2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2)
      < (4 * (Nat.sqrt X / 2)) * (4 * (Nat.sqrt X / 2)) := by
    have h1 : (2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2)
        < (4 * (Nat.sqrt X / 2)) * (2 * (Nat.sqrt X / 2) + 2) :=
      mul_lt_mul_of_pos_right hA (by omega)
    have h2 : (4 * (Nat.sqrt X / 2)) * (2 * (Nat.sqrt X / 2) + 2)
        < (4 * (Nat.sqrt X / 2)) * (4 * (Nat.sqrt X / 2)) :=
      mul_lt_mul_of_pos_left hA (by omega)
    exact lt_trans h1 h2
  have hC : 2 * X + 2
      ≤ 2 * ((2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2)) := by omega
  have hD : 2 * ((2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2))
      < 2 * ((4 * (Nat.sqrt X / 2)) * (4 * (Nat.sqrt X / 2))) :=
    mul_lt_mul_of_pos_left hB (by norm_num)
  have hE : (32 : ℕ) * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2))
      ≤ (Nat.sqrt X / 2) * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) :=
    mul_le_mul_of_nonneg_right hz (Nat.zero_le _)
  calc 2 * X + 2
      ≤ 2 * ((2 * (Nat.sqrt X / 2) + 2) * (2 * (Nat.sqrt X / 2) + 2)) := hC
    _ < 2 * ((4 * (Nat.sqrt X / 2)) * (4 * (Nat.sqrt X / 2))) := hD
    _ = 32 * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) := by ring
    _ ≤ (Nat.sqrt X / 2) * ((Nat.sqrt X / 2) * (Nat.sqrt X / 2)) := hE
    _ = (Nat.sqrt X / 2) ^ 3 := by ring

theorem factor_shapes {n z : ℕ} (hz : 32 ≤ z) (hmin : z ≤ Nat.minFac n)
    (hbound : n < z ^ 3) :
    n.Prime ∨ ∃ r s : ℕ, r.Prime ∧ s.Prime ∧ z ≤ r ∧ r ≤ s ∧ r * s = n := by
  have hz2 : 2 ≤ z := by omega
  have hn0 : n ≠ 0 := by
    intro h0
    rw [h0, Nat.minFac_zero] at hmin
    omega
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hn1 : n ≠ 1 := by
    intro h1
    rw [h1, Nat.minFac_one] at hmin
    omega
  have hmprime : (Nat.minFac n).Prime := Nat.minFac_prime hn1
  have hmdvd : Nat.minFac n ∣ n := Nat.minFac_dvd n
  have hm2 : 2 ≤ Nat.minFac n := hmprime.two_le
  have hn2 : 2 ≤ n := by
    have hle := Nat.le_of_dvd hnpos hmdvd
    omega
  by_cases hmn : Nat.minFac n = n
  · exact Or.inl (Nat.prime_def_minFac.mpr ⟨hn2, hmn⟩)
  have hnnotprime : ¬ n.Prime := fun hp => hmn (Nat.prime_def_minFac.mp hp).2
  refine Or.inr ⟨Nat.minFac n, n / Nat.minFac n, hmprime, ?_, hmin, ?_, ?_⟩
  · have hq2 : 2 ≤ n / Nat.minFac n := by
      have h := Nat.minFac_le_div hnpos hnnotprime
      omega
    by_contra hqnp
    have hq1ne : n / Nat.minFac n ≠ 1 := by omega
    have hqprime : ((n / Nat.minFac n).minFac).Prime := Nat.minFac_prime hq1ne
    have hqdvd : (n / Nat.minFac n).minFac ∣ n / Nat.minFac n := Nat.minFac_dvd _
    have hqdvd2 : (n / Nat.minFac n).minFac ∣ n :=
      dvd_trans hqdvd (Nat.div_dvd_of_dvd hmdvd)
    have hmq : Nat.minFac n ≤ (n / Nat.minFac n).minFac :=
      Nat.minFac_le_of_dvd hqprime.two_le hqdvd2
    have hqq : (n / Nat.minFac n).minFac ≤ (n / Nat.minFac n) / (n / Nat.minFac n).minFac :=
      Nat.minFac_le_div (by omega) hqnp
    have hsplit : (n / Nat.minFac n).minFac * ((n / Nat.minFac n) / (n / Nat.minFac n).minFac)
        = n / Nat.minFac n := Nat.mul_div_cancel' hqdvd
    have hprod : Nat.minFac n * ((n / Nat.minFac n).minFac
        * ((n / Nat.minFac n) / (n / Nat.minFac n).minFac)) = n := by
      rw [hsplit, Nat.mul_div_cancel' hmdvd]
    have hzq1 : z ≤ (n / Nat.minFac n).minFac := le_trans hmin hmq
    have hzq2 : z ≤ (n / Nat.minFac n) / (n / Nat.minFac n).minFac := le_trans hzq1 hqq
    have hcube : z * (z * z) ≤ Nat.minFac n * ((n / Nat.minFac n).minFac
        * ((n / Nat.minFac n) / (n / Nat.minFac n).minFac)) :=
      mul_le_mul hmin (mul_le_mul hzq1 hzq2 (Nat.zero_le _) (Nat.zero_le _))
        (Nat.zero_le _) (Nat.zero_le _)
    have hkey : z ^ 3 ≤ n := by
      rw [show z ^ 3 = z * (z * z) by ring]
      exact hcube.trans hprod.le
    exact absurd hkey (not_le.mpr hbound)
  · exact Nat.minFac_le_div hnpos hnnotprime
  · exact Nat.mul_div_cancel' hmdvd

end Conjectures.TwinPrimes.RoughWindowFactorShapes_aux

open Conjectures.TwinPrimes.RoughWindowFactorShapes_aux

theorem Conjectures.TwinPrimes.RoughWindowFactorShapes :
    let w := fun (X : ℕ) => (Finset.range (2*X+1)).filter (fun n => X < n ∧ 50*n < 51*X); let z := fun (X : ℕ) => Nat.sqrt X / 2; ∀ (X p : ℕ), 4096 ≤ X → p ∈ w X → z X ≤ (p+2).minFac → (p+2).Prime ∨ (∃ r s : ℕ, r.Prime ∧ s.Prime ∧ z X ≤ r ∧ r ≤ s ∧ r ≤ Nat.sqrt (2*X+2) ∧ p+2=r*s) := by
  dsimp only
  intro X p hX hp hz
  have hmem : p ∈ Finset.range (2 * X + 1) := (Finset.mem_filter.mp hp).1
  have hplt : p < 2 * X + 1 := Finset.mem_range.mp hmem
  have hcube := cube_gt hX
  have hz32 := z_ge_32 hX
  have hbound : p + 2 < (Nat.sqrt X / 2) ^ 3 := by omega
  rcases factor_shapes hz32 hz hbound with hprime | ⟨r, s, hr, hs, hzr, hrs, hmul⟩
  · exact Or.inl hprime
  refine Or.inr ⟨r, s, hr, hs, hzr, hrs, ?_, ?_⟩
  · apply Nat.le_sqrt.mpr
    have h1 : r * r ≤ r * s := mul_le_mul_of_nonneg_left hrs (Nat.zero_le r)
    omega
  · exact hmul.symm
