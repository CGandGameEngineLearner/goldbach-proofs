import Mathlib

open scoped BigOperators

theorem PEqualNP.Outside.L_goldbach_character_orthogonal :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); let c := fun (M j k : ℕ) => E ((j:ℝ)*(k:ℝ)/(M:ℝ)); ∀ M k, 0<M → Finset.sum (Finset.range M) (fun j => c M j k) = if M ∣ k then (M:ℂ) else 0 := by
  intro E c M k hM
  simp only [E, c]
  have hMne : M ≠ 0 := by omega
  set z : ℂ := 2 * ((Real.pi:ℝ):ℂ) * Complex.I / (M:ℂ) with hz
  have hprim : IsPrimitiveRoot (Complex.exp z) M := Complex.isPrimitiveRoot_exp M hMne
  have hstep : ∀ j : ℕ,
      Complex.exp (((2 * Real.pi * ((j:ℝ)*(k:ℝ)/(M:ℝ)) : ℝ):ℂ) * Complex.I)
        = (Complex.exp z)^(j*k) := by
    intro j
    have harg : (((2 * Real.pi * ((j:ℝ)*(k:ℝ)/(M:ℝ)) : ℝ):ℂ) * Complex.I) = (j*k:ℕ) * z := by
      rw [hz]; push_cast; field_simp
    rw [harg, Complex.exp_nat_mul]
  rw [Finset.sum_congr rfl (fun j _ => hstep j)]
  by_cases hdvd : M ∣ k
  · have h1 : (Complex.exp z)^k = 1 := by
      obtain ⟨t, rfl⟩ := hdvd
      rw [pow_mul, hprim.pow_eq_one, one_pow]
    have h1' : ∀ j : ℕ, (Complex.exp z)^(j*k) = (1:ℂ) := by
      intro j
      rw [Nat.mul_comm, pow_mul, h1, one_pow]
    rw [Finset.sum_congr rfl (fun j _ => h1' j)]
    simp [if_pos hdvd]
  · have hkne : (Complex.exp z)^k ≠ 1 := by
      intro h
      exact hdvd ((hprim.pow_eq_one_iff_dvd k).mp h)
    have hpow : (Complex.exp z)^(M*k) = 1 := by
      rw [pow_mul, hprim.pow_eq_one, one_pow]
    have hstep2 : ∀ j : ℕ, (Complex.exp z)^(j*k) = ((Complex.exp z)^k)^j := by
      intro j
      rw [show ((Complex.exp z)^k)^j = (Complex.exp z)^(k*j) by rw [pow_mul], Nat.mul_comm]
    rw [Finset.sum_congr rfl (fun j _ => hstep2 j)]
    rw [geom_sum_eq hkne M]
    have hpowM : ((Complex.exp z)^k)^M = 1 := by
      rw [← pow_mul, Nat.mul_comm k M]
      exact hpow
    rw [hpowM]
    simp [if_neg hdvd]
