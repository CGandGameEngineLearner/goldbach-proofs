import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Nat.Cast.Defs

namespace PEqualNP.Outside

set_option maxHeartbeats 2000000

theorem L_goldbach_divisor_indicator_covariance :
    let X := fun (p t : ℕ) => (p:ℝ)*(if p ∣ t then 1 else 0)-1
    ∀ (N p q : ℕ), 0 < N → Nat.Prime p → Nat.Prime q → p ∣ N → q ∣ N →
      ((∑ t ∈ Finset.range N, X p t * X q t)/(N:ℝ)) = if p=q then (p:ℝ)-1 else 0 := by
  intro X N p q hN hp hq hpd hqd
  dsimp only [X]
  have hcount : ∀ (d A : ℕ), 0 < d → N = d * A →
      ((Finset.range N).filter (fun t => d ∣ t)).card = A := by
    intro d A hd hNA
    subst hNA
    have hinj : Function.Injective (fun k => d * k) := by
      intro x y hxy
      exact mul_left_cancel₀ hd.ne' hxy
    have himg : (Finset.range A).image (fun k => d * k)
        = (Finset.range (d * A)).filter (fun t => d ∣ t) := by
      ext t
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨k, hk, rfl⟩
        exact ⟨Nat.mul_lt_mul_of_pos_left hk hd, ⟨k, rfl⟩⟩
      · rintro ⟨ht, ⟨k, rfl⟩⟩
        exact ⟨k, lt_of_mul_lt_mul_left ht (Nat.zero_le d), rfl⟩
    rw [← himg]
    rw [Finset.card_image_of_injective (s := Finset.range A) (f := fun k => d * k) hinj]
    rw [Finset.card_range]
  obtain ⟨A, hA⟩ := hpd
  obtain ⟨B, hB⟩ := hqd
  have hTp : (∑ t ∈ Finset.range N, (if p ∣ t then (1:ℝ) else 0)) = (A:ℝ) := by
    rw [Finset.sum_boole (p := fun t => p ∣ t) (s := Finset.range N)]
    rw [hcount p A hp.pos hA]
  have hTq : (∑ t ∈ Finset.range N, (if q ∣ t then (1:ℝ) else 0)) = (B:ℝ) := by
    rw [Finset.sum_boole (p := fun t => q ∣ t) (s := Finset.range N)]
    rw [hcount q B hq.pos hB]
  have expand : ∀ (S : Finset ℕ) (a b : ℝ) (f g : ℕ → ℝ),
      (∑ t ∈ S, (a * f t - 1) * (b * g t - 1))
        = a * b * (∑ t ∈ S, f t * g t) - a * (∑ t ∈ S, f t)
          - b * (∑ t ∈ S, g t) + (S.card : ℝ) := by
    intro S a b f g
    have hterm : ∀ t ∈ S,
        (a * f t - 1) * (b * g t - 1) = a * b * (f t * g t) - a * f t - b * g t + 1 := by
      intro t ht
      ring
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [(Finset.mul_sum S (fun t => f t * g t) (a * b)).symm]
    rw [(Finset.mul_sum S f a).symm]
    rw [(Finset.mul_sum S g b).symm]
    simp
  have hNnz : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  by_cases hpq : p = q
  · subst hpq
    have hsq : ∀ t, (if p ∣ t then (1:ℝ) else 0) * (if p ∣ t then (1:ℝ) else 0)
        = (if p ∣ t then (1:ℝ) else 0) := by
      intro t
      by_cases h : p ∣ t
      · rw [if_pos h, mul_one]
      · rw [if_neg h, mul_zero]
    have hff : (∑ t ∈ Finset.range N,
        (if p ∣ t then (1:ℝ) else 0) * (if p ∣ t then (1:ℝ) else 0)) = (A:ℝ) := by
      rw [Finset.sum_congr rfl (fun t ht => hsq t)]
      rw [hTp]
    have hX : (∑ t ∈ Finset.range N,
        ((p:ℝ)*(if p ∣ t then (1:ℝ) else 0)-1) * ((p:ℝ)*(if p ∣ t then (1:ℝ) else 0)-1))
        = (p:ℝ)*(p:ℝ)*(A:ℝ) - (p:ℝ)*(A:ℝ) - (p:ℝ)*(A:ℝ) + (N:ℝ) := by
      rw [expand (Finset.range N) (p:ℝ) (p:ℝ)
        (fun t => if p ∣ t then (1:ℝ) else 0) (fun t => if p ∣ t then (1:ℝ) else 0)]
      rw [hff, hTp, Finset.card_range]
    have hNA : (N:ℝ) = (p:ℝ)*(A:ℝ) := by
      rw [hA, Nat.cast_mul]
    have hval : (p:ℝ)*(p:ℝ)*(A:ℝ) - (p:ℝ)*(A:ℝ) - (p:ℝ)*(A:ℝ) + (N:ℝ)
        = ((p:ℝ)*(A:ℝ)) * ((p:ℝ)-1) := by
      rw [hNA]
      ring
    rw [hX, hval, hNA, if_pos rfl]
    have hpA : (p:ℝ)*(A:ℝ) ≠ 0 := by
      rw [← hNA]
      exact hNnz
    rw [div_eq_iff hpA]
    ring
  · have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
    have hpqdvd : p * q ∣ N := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop ⟨A, hA⟩ ⟨B, hB⟩
    obtain ⟨C, hC⟩ := hpqdvd
    have hppq : p ∣ p * q := ⟨q, rfl⟩
    have hqpq : q ∣ p * q := ⟨p, by rw [Nat.mul_comm]⟩
    have hiff : ∀ t, (if p ∣ t then (1:ℝ) else 0) * (if q ∣ t then (1:ℝ) else 0)
        = (if p * q ∣ t then (1:ℝ) else 0) := by
      intro t
      by_cases hp' : p ∣ t
      · by_cases hq' : q ∣ t
        · rw [if_pos hp', if_pos hq', if_pos (hcop.mul_dvd_of_dvd_of_dvd hp' hq'), mul_one]
        · rw [if_pos hp', if_neg hq', if_neg (fun h : p * q ∣ t => hq' (dvd_trans hqpq h)), mul_zero]
      · by_cases hq' : q ∣ t
        · rw [if_neg hp', if_pos hq', if_neg (fun h : p * q ∣ t => hp' (dvd_trans hppq h)), zero_mul]
        · rw [if_neg hp', if_neg hq', if_neg (fun h : p * q ∣ t => hp' (dvd_trans hppq h)), zero_mul]
    have hTpq : (∑ t ∈ Finset.range N,
        (if p ∣ t then (1:ℝ) else 0) * (if q ∣ t then (1:ℝ) else 0)) = (C:ℝ) := by
      rw [Finset.sum_congr rfl (fun t ht => hiff t)]
      rw [Finset.sum_boole (p := fun t => p * q ∣ t) (s := Finset.range N)]
      rw [hcount (p * q) C (Nat.mul_pos hp.pos hq.pos) hC]
    have hX : (∑ t ∈ Finset.range N,
        ((p:ℝ)*(if p ∣ t then (1:ℝ) else 0)-1) * ((q:ℝ)*(if q ∣ t then (1:ℝ) else 0)-1))
        = (p:ℝ)*(q:ℝ)*(C:ℝ) - (p:ℝ)*(A:ℝ) - (q:ℝ)*(B:ℝ) + (N:ℝ) := by
      rw [expand (Finset.range N) (p:ℝ) (q:ℝ)
        (fun t => if p ∣ t then (1:ℝ) else 0) (fun t => if q ∣ t then (1:ℝ) else 0)]
      rw [hTpq, hTp, hTq, Finset.card_range]
    have hNA : (N:ℝ) = (p:ℝ)*(A:ℝ) := by rw [hA, Nat.cast_mul]
    have hNB : (N:ℝ) = (q:ℝ)*(B:ℝ) := by rw [hB, Nat.cast_mul]
    have hNC : (N:ℝ) = (p:ℝ)*(q:ℝ)*(C:ℝ) := by
      rw [hC, Nat.cast_mul, Nat.cast_mul]
    have hzero : (p:ℝ)*(q:ℝ)*(C:ℝ) - (p:ℝ)*(A:ℝ) - (q:ℝ)*(B:ℝ) + (N:ℝ) = 0 := by
      rw [← hNC, ← hNA, ← hNB]
      ring
    rw [hX, hzero, if_neg hpq, zero_div]

end PEqualNP.Outside
