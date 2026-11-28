import Conjectures.Goldbach.TwistedGoldbachExceptionalGap
import Conjectures.Goldbach.ExceptionalZeroBetaBound
import Conjectures.Goldbach.ExceptionalConductorClasses

/-! The pole and one exceptional zero in the generalized Goldbach
explicit formula. Estimate their actual singular series, beta factors
and powers together. Only multiples of r/(r,36) can lose the resulting
lower bound once the conductor is large. This estimates the displayed
terms of the formula; the analytic remainder stays explicit.
See Pintz I, (11.41)–(11.42), https://arxiv.org/abs/1804.05561. -/

namespace Conjectures.Goldbach.SingleExceptionalZeroMajorFloor

open Finset Real DirichletCharacter TwistedGoldbachLocalProduct TwistedGoldbachConductorSuppression
open TwistedGoldbachMixedPrincipal
open scoped BigOperators Classical

private theorem prime_fourth {p : ℕ} (hp : p.Prime) :
    (primeRatio p)^4 ≤ (p:ℝ)*((if p=2 then 8 else 1)*(if p=3 then 2 else 1)) := by
  by_cases p2 : p=2
  · subst p; norm_num [primeRatio]
  by_cases p3 : p=3
  · subst p; norm_num [primeRatio]
  have p5 : 5 ≤ p := by by_contra! sm; interval_cases p <;> norm_num at *
  have pr : (5:ℝ) ≤ p := by exact_mod_cast p5
  have nonneg : 0 ≤ primeRatio p := div_nonneg (Nat.cast_nonneg p) (by linarith)
  have bound : primeRatio p ≤ 5/4 := (div_le_iff₀ (show 0 < (p:ℝ)-1 by linarith)).mpr (by linarith)
  simp only [p2,p3,ite_false,mul_one]
  exact (pow_le_pow_left₀ nonneg bound 4).trans (by linarith)

/-- A concrete totient bound without any asymptotic threshold. -/
theorem totient_fourth (r : ℕ) (hr : 0 < r) : (totRatio r)^4 ≤ 16*r := by
  classical
  let D (p : ℕ) : ℝ := (if p=2 then 8 else 1)*(if p=3 then 2 else 1)
  have sup : ∏ p ∈ r.primeFactors, D p ≤ 16 := by
    simp only [D,prod_mul_distrib,prod_ite_eq']
    split_ifs <;> norm_num
  have rad : (∏ p ∈ r.primeFactors, (p:ℝ)) ≤ r := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hr (Nat.prod_primeFactors_dvd r)
  rw [totient_euler r hr,← prod_pow]
  calc
    _ ≤ ∏ p ∈ r.primeFactors, (p:ℝ)*D p := prod_le_prod₀
      (fun p h => by
        have hpr : 1 < (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors h).one_lt
        exact pow_nonneg (div_nonneg (Nat.cast_nonneg p) (by linarith)) _)
      (fun _ h => prime_fourth (Nat.prime_of_mem_primeFactors h))
    _ = (∏ p ∈ r.primeFactors, (p:ℝ))*(∏ p ∈ r.primeFactors, D p) := prod_mul_distrib
    _ ≤ (r:ℝ)*16 := mul_le_mul rad sup (prod_nonneg fun p _ => by dsimp [D]; split_ifs <;> norm_num) (Nat.cast_nonneg _)
    _ = _ := mul_comm ..

theorem mixed_decay {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    ‖series χ (1 : DirichletCharacter ℂ 1) m‖*sqrt r ≤
      8*‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  have rpos : 0 < (r:ℝ) := by exact_mod_cast NeZero.pos r
  have phi : 0 < (r.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos r)
  have H := sqrt_le_sqrt (totient_fourth r (NeZero.pos r))
  rw [show (totRatio r)^4=((totRatio r)^2)^2 by ring,sqrt_sq (sq_nonneg _),
    sqrt_mul (by norm_num : (0:ℝ) ≤ 16),show sqrt (16:ℝ)=4 by norm_num] at H
  have raw : (2*(r:ℝ)/(r.totient:ℝ)^2)*sqrt r ≤ 8 := by
    calc
      (2*(r:ℝ)/(r.totient:ℝ)^2)*sqrt r = ((totRatio r)^2)*(2*sqrt r)/r := by
        unfold totRatio
        field_simp
      _ ≤ (4*sqrt r)*(2*sqrt r)/r := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right H (by positivity)) rpos.le
      _ = 8 := by
        rw [show (4*sqrt r)*(2*sqrt r)=8*(sqrt r*sqrt r) by ring,mul_self_sqrt rpos.le]
        field_simp
  have mixed := mul_le_mul_of_nonneg_right (mixed_bound χ hχ m hm he) (sqrt_nonneg (r:ℝ))
  change _ ≤ 8*O
  calc
    _ ≤ ((2*(r:ℝ)/(r.totient:ℝ)^2)*O)*sqrt r := mixed
    _ = ((2*(r:ℝ)/(r.totient:ℝ)^2)*sqrt r)*O := by ring
    _ ≤ 8*O := mul_le_mul_of_nonneg_right raw (norm_nonneg _)

noncomputable def kernel (m : ℕ) (z w : ℂ) : ℂ :=
  (Complex.Gamma z*Complex.Gamma w/Complex.Gamma (z+w))*(m:ℂ)^(z+w-1)

theorem kernel_bound {m : ℕ} (hm : 0 < m) {z w : ℂ}
    (hz : 1-1/128 ≤ z.re) (hz' : z.re ≤ 1) (hw : 1-1/128 ≤ w.re) (hw' : w.re ≤ 1) :
    ‖kernel m z w‖ ≤ (17/16:ℝ)*m := by
  have B := ExceptionalZeroBetaBound.gamma_ratio (δ := 1/128) (by norm_num) (by norm_num) hz hw
  have bound : ‖Complex.Gamma z*Complex.Gamma w/Complex.Gamma (z+w)‖ ≤ (17/16:ℝ) :=
    B.trans (by linarith [Real.pi_lt_four])
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have power : ‖(m:ℂ)^(z+w-1)‖ ≤ (m:ℝ) := by
    change ‖((m:ℝ):ℂ)^(z+w-1)‖ ≤ _
    rw [Complex.norm_cpow_eq_rpow_re_of_pos mp,Complex.sub_re,Complex.add_re,Complex.one_re]
    simpa using Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm : (1:ℝ) ≤ m) (by linarith : z.re+w.re-1 ≤ 1)
  rw [kernel,norm_mul]
  exact mul_le_mul bound power (norm_nonneg _) (by norm_num)

noncomputable def mainTerms {r : ℕ} (χ : DirichletCharacter ℂ r) (z : ℂ) (m : ℕ) : ℂ :=
  let oneχ : DirichletCharacter ℂ 1 := 1
  (m:ℂ)*series oneχ oneχ m - 2*(series χ oneχ m*kernel m z 1) + series χ χ m*kernel m z z

/-- The pole and a single near-one zero leave a positive fraction of
the ordinary term off the exceptional congruence class. The error can
be any complex number. -/
theorem main_floor {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (z : ℂ) (hz : 1-1/128 ≤ z.re) (hz' : z.re ≤ 1)
    (m : ℕ) (hm : 0 < m) (he : Even m) (off : ¬ r ∣ 36*m)
    (smallMixed : 262144 ≤ r ∨ ¬Squarefree r ∨ ¬m.Coprime r) (err : ℂ) :
    ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖*(m:ℝ)/6 - ‖err‖ ≤
      (mainTerms χ z m+err).re := by
  let P : DirichletCharacter ℂ 1 := 1
  let S := series P P m
  let O := ‖S‖
  let M := series χ P m*kernel m z 1
  let D := series χ χ m*kernel m z z
  have Op : 0 ≤ O := norm_nonneg _
  have mp : 0 ≤ (m:ℝ) := Nat.cast_nonneg _
  have Oeq : S.re=O := le_antisymm (Complex.re_le_norm S)
    (TwistedGoldbachSingularSeries.infinite_domination (α := P) (β := P)
      isPrimitive_one_level_one isPrimitive_one_level_one m hm)
  have msmall : ‖series χ P m‖ ≤ O/64 := by
    rcases smallMixed with big | vanish
    · have sr : 512 ≤ sqrt (r:ℝ) := le_sqrt_of_sq_le (by exact_mod_cast big)
      have a := (mul_le_mul_of_nonneg_left sr (norm_nonneg (series χ P m))).trans (mixed_decay χ hχ m hm he)
      change ‖series χ P m‖*512 ≤ 8*O at a
      linarith
    · rw [mixed_zero χ hχ m hm he vanish,norm_zero]
      positivity
  have diag : ‖series χ χ m‖ ≤ 3/4*O := by
    have H := TwistedGoldbachExceptionalGap.same_level_gap hχ hχ m hm he off
    change 4*‖series χ χ m‖ ≤ 3*O at H
    linarith
  have mlim : ‖M‖ ≤ (O/64)*((17/16:ℝ)*m) := by
    dsimp only [M]
    rw [norm_mul]
    exact mul_le_mul msmall (kernel_bound hm hz hz' (by norm_num) (by norm_num)) (norm_nonneg _) (by positivity)
  have dlim : ‖D‖ ≤ (3/4*O)*((17/16:ℝ)*m) := by
    dsimp only [D]
    rw [norm_mul]
    exact mul_le_mul diag (kernel_bound hm hz hz' hz hz') (norm_nonneg _) (by positivity)
  have Mre := (Complex.re_le_norm M).trans mlim
  have Dre := (abs_le.mp (Complex.abs_re_le_norm D)).1
  have E := (abs_le.mp (Complex.abs_re_le_norm err)).1
  change O*(m:ℝ)/6-‖err‖ ≤ ((m:ℂ)*S-2*M+D+err).re
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
    show (2:ℂ).re=2 by rfl,show (2:ℂ).im=0 by rfl,zero_mul,sub_zero,Oeq]
  nlinarith only [Mre,Dre,dlim,E,mul_nonneg Op mp]

/-- Positive even targets that violate the one-eighth floor are counted
by a single progression after cancelling the common divisor with 36. -/
theorem exceptional_count {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (z : ℂ) (hz : 1-1/128 ≤ z.re) (hz' : z.re ≤ 1) (big : 262144 ≤ r)
    (N : ℕ) (err : ℕ → ℂ) (herr : ∀ m ∈ Ioc 0 N, Even m → ‖err m‖ ≤ (m:ℝ)/24) :
    ((Ioc 0 N).filter (fun m : ℕ => _root_.Even m ∧ (mainTerms χ z m+err m).re < (m:ℝ)/8)).card ≤
      N/(r/(r.gcd 36)) := by
  classical
  rw [← ExceptionalConductorClasses.multiples r 36 N (NeZero.pos r)]
  apply card_le_card
  intro m hmem
  obtain ⟨hi,he,low⟩ := mem_filter.mp hmem
  refine mem_filter.mpr ⟨hi,?_⟩
  by_contra gap
  have hm := (mem_Ioc.mp hi).1
  have bound := main_floor χ hχ z hz hz' m hm he gap (.inl big) (err m)
  let P : DirichletCharacter ℂ 1 := 1
  have O : 1 ≤ ‖series P P m‖ := (ordinary_at_least_one m hm he).trans (Complex.re_le_norm _)
  have lower := mul_le_mul_of_nonneg_right O (Nat.cast_nonneg (α := ℝ) m)
  change ‖series P P m‖*(m:ℝ)/6-‖err m‖ ≤ _ at bound
  linarith only [low,bound,lower,herr m hi he]

end Conjectures.Goldbach.SingleExceptionalZeroMajorFloor

open Conjectures.Goldbach.SingleExceptionalZeroMajorFloor in
theorem Conjectures.Goldbach.SingleExceptionalZeroMajorFloor :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let P : DirichletCharacter ℂ 1 := 1
  let K := fun (m : ℕ) (z w : ℂ) =>
    (Complex.Gamma z*Complex.Gamma w/Complex.Gamma (z+w))*(m:ℂ)^(z+w-1)
  let F := fun {r : ℕ} (χ : DirichletCharacter ℂ r) (z : ℂ) (m : ℕ) =>
    (m:ℂ)*S P P m - 2*(S χ P m*K m z 1) + S χ χ m*K m z z
  exact
    (∀ r : ℕ, 0 < r → ((r:ℝ)/r.totient)^4 ≤ 16*r) ∧
    (∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      ∀ m : ℕ, 0 < m → Even m → ‖S χ P m‖*Real.sqrt r ≤ 8*‖S P P m‖) ∧
    (∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      ∀ z : ℂ, 1-1/128 ≤ z.re → z.re ≤ 1 →
      (∀ m : ℕ, 0 < m → Even m → ¬r ∣ 36*m → (262144 ≤ r ∨ ¬Squarefree r ∨ ¬m.Coprime r) →
        ∀ err : ℂ, ‖S P P m‖*(m:ℝ)/6-‖err‖ ≤ (F χ z m+err).re) ∧
      (262144 ≤ r → ∀ (N : ℕ) (err : ℕ → ℂ), (∀ m ∈ Finset.Ioc 0 N, Even m → ‖err m‖ ≤ (m:ℝ)/24) →
        ((Finset.Ioc 0 N).filter (fun m : ℕ => Even m ∧ (F χ z m+err m).re < (m:ℝ)/8)).card ≤
          N/(r/(r.gcd 36)))) := by
  refine ⟨totient_fourth, fun _ _ => mixed_decay, ?_⟩
  intro r _ χ hχ z hz hz'
  exact ⟨main_floor χ hχ z hz hz', exceptional_count χ hχ z hz hz'⟩
