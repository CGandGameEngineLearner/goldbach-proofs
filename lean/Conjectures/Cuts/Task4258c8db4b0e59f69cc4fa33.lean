import Mathlib

open scoped BigOperators
open MeasureTheory

private noncomputable def eightE (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑k * ↑t)

private theorem eightPow (f : ℕ → ℤ) (s : Finset ℕ) (t : ℝ) :
    (∑ a ∈ s, eightE (f a) t)^4 =
      ∑ u ∈ Fintype.piFinset (fun _ : Fin 4 => s), eightE (∑ i, f (u i)) t := by
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro u _
  unfold eightE
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]


private theorem eightOrth (k : ℤ) : (∫ t : ℝ in 0..1, eightE k t) = if k = 0 then 1 else 0 := by
  by_cases hk : k=0
  · subst k;simp [eightE]
  let c : ℂ := (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I)
  have eq (t:ℝ):eightE k t=Complex.exp (c*(t:ℂ)):=by unfold eightE c;congr 1;ring
  have nz:c≠0:=mul_ne_zero (by exact_mod_cast hk)
    (mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  simp_rw [eq]
  rw [integral_exp_mul_complex nz]
  simp [hk,c,Complex.exp_int_mul_two_pi_mul_I]

private theorem eightPair (k l : ℤ) (t : ℝ) : eightE k t * star (eightE l t) = eightE (k-l) t := by
  open scoped ComplexConjugate in
  have cj (x:ℂ):star (Complex.exp x)=Complex.exp (conj x):=by exact (Complex.exp_conj x).symm
  unfold eightE
  rw [cj,←Complex.exp_add]
  congr 1
  simp only [map_mul,map_ofNat,map_intCast,Complex.conj_ofReal,Complex.conj_I,Int.cast_sub]
  ring
private theorem eightNorm (z : ℂ) :
    ((‖z‖ ^ 8 : ℝ) : ℂ) = z ^ 4 * star (z ^ 4) := by
  calc
    _ = ((‖z ^ 4‖ ^ 2 : ℝ) : ℂ) := by rw [norm_pow, ← pow_mul]
    _ = _ := by rw [Complex.sq_norm, ← Complex.mul_conj]; rfl


theorem Conjectures.Cuts.Task4258c8db4b0e59f69cc4fa33 : (∀ (x1 : ℕ → ℤ) (x2 : Finset ℕ),   have x3 : ℝ → ℂ := fun (x3 : ℝ) => ∑ x4 ∈ x2, Complex.exp ((2 : ℂ) * ↑Real.pi * Complex.I * ↑(x1 x4) * ↑x3);   have x4 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x4 : Fin (4 : ℕ)) => x2;   have x5 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x5 : Fin (4 : ℕ) → ℕ) => ∑ x6 : Fin (4 : ℕ), x1 (x5 x6);   ∫ (x6 : ℝ) in (0 : ℝ)..(1 : ℝ), ‖x3 x6‖ ^ (8 : ℕ) = ↑{x6 ∈ x4.product x4 | x5 x6.1 = x5 x6.2}.card) := by

  classical
  intro f s
  let u : Finset (Fin 4 → ℕ) := Fintype.piFinset fun _ : Fin 4 => s
  let F : (Fin 4 → ℕ) → ℤ := fun x => ∑ i, f (x i)
  let v := u.product u
  let h : ℝ → ℂ := fun t => ∑ i ∈ s, eightE (f i) t
  change (∫ t : ℝ in 0..1, ‖h t‖ ^ 8) = ((v.filter fun p => F p.1 = F p.2).card : ℝ)
  have expand (t : ℝ) : ((‖h t‖ ^ 8 : ℝ) : ℂ) =
      ∑ p ∈ v, eightE (F p.1 - F p.2) t := by
    have h4 : h t ^ 4 = ∑ x ∈ u, eightE (F x) t := eightPow f s t
    dsimp only [v]
    rw [eightNorm, h4, star_sum]
    refine Eq.trans ?_ (Finset.sum_product u u (fun p => eightE (F p.1 - F p.2) t)).symm
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, eightPair]
  apply Complex.ofReal_inj.mp
  rw [← intervalIntegral.integral_ofReal]
  push_cast
  calc
    _ = ∫ t : ℝ in 0..1, ∑ p ∈ v, eightE (F p.1 - F p.2) t := by
      apply intervalIntegral.integral_congr
      intro t _
      simpa only [Complex.ofReal_pow] using expand t
    _ = ∑ p ∈ v, ∫ t : ℝ in 0..1, eightE (F p.1 - F p.2) t := by
      apply intervalIntegral.integral_finsetSum
      intro p _
      apply Continuous.intervalIntegrable
      unfold eightE
      fun_prop
    _ = _ := by simp only [eightOrth, sub_eq_zero]; apply Finset.sum_boole
