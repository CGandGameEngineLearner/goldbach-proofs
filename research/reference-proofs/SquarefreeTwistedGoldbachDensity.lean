import Mathlib

/-! Finite character-twisted Goldbach densities at squarefree levels.
The sum is over all residues, with the two Dirichlet characters extended
by zero on nonunits. No primitivity or reality hypothesis is needed.
The comparison is with the untwisted density at the same level and target. -/

namespace Conjectures.Goldbach.SquarefreeTwistedGoldbachDensity

open Finset
open scoped BigOperators Classical

noncomputable def localSum {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    (m : ZMod p) : ℂ := ∑ a : ZMod p, χ a * ψ (m-a)

private theorem norm_jacobi {p : ℕ} [hp : Fact p.Prime] {χ ψ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ*ψ ≠ 1) :
    ‖jacobiSum χ ψ‖ = Real.sqrt p := by
  have hc : star (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
    simp only [jacobiSum, star_sum, star_mul', MulChar.star_apply']
  have hchar : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ringChar.eq ℂ 0]
    exact hp.out.ne_zero.symm
  have h := congrArg (fun z : ℂ => ‖z‖) (jacobiSum_mul_jacobiSum_inv hchar hχ hψ hχψ)
  simp only [← hc, norm_mul, norm_star, ZMod.card, Complex.norm_natCast] at h
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p:ℝ), norm_nonneg (jacobiSum χ ψ)]

private theorem localSum_nonzero {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    {m : ZMod p} (hm : m ≠ 0) : localSum χ ψ m = (χ m*ψ m)*jacobiSum χ ψ := by
  have h := Equiv.sum_comp (Equiv.mulLeft₀ m hm) (fun a : ZMod p => χ a * ψ (m-a))
  calc
    _ = ∑ a : ZMod p, χ (m*a) * ψ (m-m*a) := h.symm
    _ = ∑ a : ZMod p, (χ m*ψ m)*(χ a*ψ (1-a)) := by
      apply sum_congr rfl
      intro a _
      rw [← mul_one_sub, map_mul, map_mul]
      ring
    _ = _ := (mul_sum ..).symm

private theorem localSum_zero {p : ℕ} [hp : Fact p.Prime] (χ ψ : DirichletCharacter ℂ p) :
    localSum χ ψ 0 = ψ (-1)*(if χ*ψ = 1 then ((p-1 : ℕ) : ℂ) else 0) := by
  classical
  have h : localSum χ ψ 0 = ψ (-1)*∑ a : ZMod p, (χ*ψ) a := by
    unfold localSum
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    rw [zero_sub, ← neg_one_mul a, map_mul, MulChar.mul_apply]
    ring
  rw [h]
  by_cases hprod : χ*ψ = 1
  · simp only [hprod, ite_true, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient,
      Nat.totient_prime hp.out]
  · rw [ite_eq_right hprod, MulChar.sum_eq_zero_of_ne_one hprod]

/-- Complete table, including the primes 2 and 3 and imprimitive local factors. -/
theorem local_norm {p : ℕ} [hp : Fact p.Prime] (χ ψ : DirichletCharacter ℂ p) (m : ZMod p) :
    ‖localSum χ ψ m‖ =
      if m=0 then (if χ*ψ=1 then (p:ℝ)-1 else 0)
      else if χ=1 ∧ ψ=1 then (p:ℝ)-2
      else if χ=1 ∨ ψ=1 ∨ χ*ψ=1 then 1 else Real.sqrt p := by
  classical
  by_cases hm : m=0
  · subst m
    rw [ite_eq_left rfl,localSum_zero,norm_mul,ψ.norm_neg_one,one_mul]
    by_cases h : χ*ψ=1
    · rw [ite_eq_left h,ite_eq_left h,Complex.norm_natCast,Nat.cast_sub hp.out.one_le,Nat.cast_one]
    · simp [h]
  have hu := isUnit_iff_ne_zero.mpr hm
  have v (θ : DirichletCharacter ℂ p) : ‖θ m‖=1 := θ.unit_norm_eq_one hu.unit
  rw [ite_eq_right hm,localSum_nonzero χ ψ hm,norm_mul,norm_mul,
    v χ,v ψ,one_mul,one_mul]
  by_cases hχ : χ=1
  · subst χ
    by_cases hψ : ψ=1
    · subst ψ
      have hpos : (0:ℝ) ≤ p-2 := sub_nonneg.mpr (by exact_mod_cast hp.out.two_le)
      simp only [and_self,ite_true,jacobiSum_one_one,ZMod.card]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_of_nonneg hpos]
    · simp [hψ,jacobiSum_one_nontrivial hψ]
  by_cases hψ : ψ=1
  · subst ψ
    rw [jacobiSum_comm,jacobiSum_one_nontrivial hχ]
    simp [hχ]
  by_cases hprod : χ*ψ=1
  · have hinv : ψ=χ⁻¹ := eq_inv_of_mul_eq_one_right hprod
    simp only [hχ,hψ,hprod,false_and,ite_false,false_or,ite_true]
    rw [hinv,jacobiSum_nontrivial_inv hχ,norm_neg,χ.norm_neg_one]
  · simp [hχ,hψ,hprod,norm_jacobi hχ hψ hprod]

private theorem local_le_principal {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    (m : ZMod p) : ‖localSum χ ψ m‖ ≤ ‖localSum (1 : DirichletCharacter ℂ p) 1 m‖ := by
  classical
  let U := univ.filter (fun a : ZMod p => IsUnit a ∧ IsUnit (m-a))
  have restrict (α β : DirichletCharacter ℂ p) :
      (∑ a ∈ U, α a * β (m-a)) = localSum α β m := by
    apply sum_subset (filter_subset _ _)
    intro a _ ha
    by_cases hu : IsUnit a
    · have hv : ¬IsUnit (m-a) := fun hv => ha (mem_filter.mpr ⟨mem_univ _,hu,hv⟩)
      simp [β.map_nonunit hv]
    · simp [α.map_nonunit hu]
  have triv : localSum (1 : DirichletCharacter ℂ p) 1 m = (U.card:ℂ) := by
    rw [← restrict]
    calc
      _ = ∑ _a ∈ U, (1:ℂ) := by
        apply sum_congr rfl
        intro a ha
        obtain ⟨_, hu, hv⟩ := mem_filter.mp ha
        rw [MulChar.one_apply hu,MulChar.one_apply hv,one_mul]
      _ = _ := by simp
  rw [triv,Complex.norm_natCast,← restrict]
  calc
    _ ≤ ∑ a ∈ U, ‖χ a * ψ (m-a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ U, (1:ℝ) := by
      apply sum_le_sum
      intro a _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (χ.norm_le_one _) (norm_nonneg _)).trans
        (by simpa only [one_mul] using ψ.norm_le_one (m-a))
    _ = _ := by simp

section Squarefree
variable {k : ℕ} (p : Fin k → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (cop : Pairwise (fun i j => (p i).Coprime (p j)))
    (χ ψ : (i : Fin k) → DirichletCharacter ℂ (p i))

/-- The complete sum over one actual residue ring, with both characters
assembled from their components by the Chinese remainder isomorphism. -/
noncomputable def twisted (m : ZMod (∏ i, p i)) : ℂ :=
  let e := ZMod.prodEquivPi p cop
  ∑ a : ZMod (∏ i, p i), (∏ i, χ i (e a i)) * (∏ i, ψ i (e (m-a) i))

theorem factorization (m : ZMod (∏ i, p i)) :
    twisted p cop χ ψ m = ∏ i, localSum (χ i) (ψ i) (ZMod.prodEquivPi p cop m i) := by
  classical
  let e := ZMod.prodEquivPi p cop
  let f (i : Fin k) (a : ZMod (p i)) := χ i a * ψ i (e m i-a)
  have hstep (a : ZMod (∏ i, p i)) :
      (∏ i, χ i (e a i)) * (∏ i, ψ i (e (m-a) i)) = ∏ i, f i (e a i) := by
    rw [← prod_mul_distrib,map_sub]
    rfl
  calc
    _ = ∑ a : ZMod (∏ i, p i), ∏ i, f i (e a i) := sum_congr rfl (fun a _ => hstep a)
    _ = ∑ a : (i : Fin k) → ZMod (p i), ∏ i, f i (a i) :=
      Equiv.sum_comp e.toEquiv (fun a => ∏ i, f i (a i))
    _ = _ := (Fintype.prod_sum f).symm

/-- A nonprincipal component at a prime away from the target costs a factor
of at least two for p ≥ 11. At every other prime the cost is at most one.
The saving therefore multiplies across the *distinct* offending primes. -/
theorem suppression (m : ZMod (∏ i, p i)) :
    let e := ZMod.prodEquivPi p cop
    let B := univ.filter (fun i => 11 ≤ p i ∧ e m i ≠ 0 ∧ (χ i ≠ 1 ∨ ψ i ≠ 1))
    (2:ℝ)^B.card * ‖twisted p cop χ ψ m‖ ≤
      ‖twisted p cop (fun _ => 1) (fun _ => 1) m‖ := by
  classical
  intro e B
  let w (i : Fin k) : ℝ := if i ∈ B then 2 else 1
  have hweight : (∏ i, w i) = (2:ℝ)^B.card := by
    simp [w, Finset.prod_ite_mem]
  rw [← hweight, factorization, factorization, norm_prod, norm_prod, ← prod_mul_distrib]
  apply prod_le_prod₀
  · intro i _
    exact mul_nonneg (by dsimp [w]; split <;> norm_num) (norm_nonneg _)
  · intro i _
    by_cases hi : i ∈ B
    · have ⟨hp,hm,hχψ⟩ := (mem_filter.mp hi).2
      change (ZMod.prodEquivPi p cop) m i ≠ 0 at hm
      have hn : ¬(χ i=1 ∧ ψ i=1) := by tauto
      have hpR : (11:ℝ) ≤ p i := by exact_mod_cast hp
      have hs := Real.sq_sqrt (Nat.cast_nonneg (p i))
      have hroot : 3 ≤ Real.sqrt (p i) := by nlinarith [Real.sqrt_nonneg (p i)]
      have hsmall : 2*Real.sqrt (p i) ≤ p i-2 := by nlinarith [sq_nonneg (Real.sqrt (p i)-3)]
      rw [show w i = 2 by simp [w,hi],local_norm,local_norm]
      simp only [hm,ite_false,hn,ite_true,and_self]
      split <;> linarith
    · rw [show w i = 1 by simp [w,hi],one_mul]
      exact local_le_principal _ _ _

/-- A prime dividing the target kills the entire sum when the two local
characters do not cancel one another on its units. -/
theorem vanishing (m : ZMod (∏ i, p i)) (i : Fin k)
    (hm : ZMod.prodEquivPi p cop m i = 0) (h : χ i * ψ i ≠ 1) :
    twisted p cop χ ψ m = 0 := by
  rw [factorization]
  apply prod_eq_zero (mem_univ i)
  apply norm_eq_zero.mp
  rw [local_norm,ite_eq_left hm,ite_eq_right h]

private theorem dft_convolution {N : ℕ} [NeZero N] (f g : ZMod N → ℂ) :
    ZMod.dft (fun m => ∑ a, f a * g (m-a)) =
      fun t => ZMod.dft f t * ZMod.dft g t := by
  classical
  funext t
  simp only [ZMod.dft_apply,smul_eq_mul]
  calc
    _ = ∑ a, ∑ m : ZMod N, ZMod.stdAddChar (-(m*t)) * (f a*g (m-a)) := by
      simp only [mul_sum]
      rw [sum_comm]
    _ = ∑ a, ∑ b : ZMod N, (ZMod.stdAddChar (-(a*t))*f a) *
        (ZMod.stdAddChar (-(b*t))*g b) := by
      apply sum_congr rfl
      intro a _
      let F (m : ZMod N) := ZMod.stdAddChar (-(m*t)) * (f a*g (m-a))
      calc
        _ = ∑ b : ZMod N, F (a+b) := (Equiv.sum_comp (Equiv.addLeft a) F).symm
        _ = _ := by
          apply sum_congr rfl
          intro b _
          simp only [F,add_sub_cancel_left,add_mul,neg_add_rev,AddChar.map_add_eq_mul]
          ring
    _ = _ := by simp only [sum_mul,mul_sum]; rw [sum_comm]

omit [∀ i, Fact (p i).Prime] in
/-- Normalized inverse Fourier synthesis of the product of the two complete
character sums gives the same finite local density. -/
theorem synthesis (m : ZMod (∏ i, p i)) :
    let e := ZMod.prodEquivPi p cop
    let f := fun a => ∏ i, χ i (e a i)
    let g := fun a => ∏ i, ψ i (e a i)
    ZMod.dft (fun t => ZMod.dft f t * ZMod.dft g t) (-m) =
      ((∏ i, p i : ℕ) : ℂ) * twisted p cop χ ψ m := by
  intro e f g
  rw [← dft_convolution f g,ZMod.dft_dft]
  simp only [neg_neg,smul_eq_mul]
  rfl

end Squarefree
end Conjectures.Goldbach.SquarefreeTwistedGoldbachDensity

open Conjectures.Goldbach.SquarefreeTwistedGoldbachDensity in
/-- Exact prime factors and Fourier synthesis, with cancellation and a quantitative
comparison against the principal characters on their product modulus. -/
theorem Conjectures.Goldbach.SquarefreeTwistedGoldbachDensity :
by
  classical
  exact
    (∀ (p : ℕ) [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p) (m : ZMod p),
      ‖∑ a : ZMod p, χ a * ψ (m-a)‖ =
        if m=0 then (if χ*ψ=1 then (p:ℝ)-1 else 0)
        else if χ=1 ∧ ψ=1 then (p:ℝ)-2
        else if χ=1 ∨ ψ=1 ∨ χ*ψ=1 then 1 else Real.sqrt p) ∧
    (∀ (k : ℕ) (p : Fin k → ℕ) [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
      (cop : Pairwise (fun i j => (p i).Coprime (p j)))
      (χ ψ : (i : Fin k) → DirichletCharacter ℂ (p i)) (m : ZMod (∏ i, p i)),
      let e := ZMod.prodEquivPi p cop
      let f := fun a => ∏ i, χ i (e a i)
      let g := fun a => ∏ i, ψ i (e a i)
      let u := fun a => ∏ i, (1 : DirichletCharacter ℂ (p i)) (e a i)
      let S := ∑ a : ZMod (∏ i, p i), f a * g (m-a)
      let B := Finset.univ.filter (fun i => 11 ≤ p i ∧ e m i ≠ 0 ∧ (χ i ≠ 1 ∨ ψ i ≠ 1))
      (S = ∏ i, ∑ a : ZMod (p i), χ i a * ψ i (e m i-a)) ∧
      ((∃ i, e m i=0 ∧ χ i*ψ i≠1) → S=0) ∧
      ((2:ℝ)^B.card * ‖S‖ ≤ ‖∑ a : ZMod (∏ i, p i), u a * u (m-a)‖) ∧
      (ZMod.dft (fun t => ZMod.dft f t * ZMod.dft g t) (-m) = ((∏ i, p i : ℕ):ℂ)*S)) := by
  constructor
  · intro p _ χ ψ m
    exact local_norm χ ψ m
  · intro k p _ _ cop χ ψ m e f g u S B
    refine ⟨factorization p cop χ ψ m, ?_, suppression p cop χ ψ m, synthesis p cop χ ψ m⟩
    rintro ⟨i, hm, h⟩
    exact vanishing p cop χ ψ m i hm h
