import Conjectures.Goldbach.TwistedGoldbachLocalProduct

/-! The primitive/principal pair contributing to the exceptional-zero
formula has an elementary exact numerator, including its phase. -/

namespace Conjectures.Goldbach.TwistedGoldbachMixedPrincipal

open Finset DirichletCharacter TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open scoped BigOperators Classical
open B13BilateralVaughanReductionProof

private theorem principal_gauss (r : ℕ) [NeZero r] :
    gaussSum (1 : DirichletCharacter ℂ r) ZMod.stdAddChar = (ArithmeticFunction.moebius r : ℂ) := by
  by_cases one : r=1
  · subst r
    have trivial : (ZMod.stdAddChar : AddChar (ZMod 1) ℂ) = 1 := by
      ext x
      rw [show x=0 from Subsingleton.elim _ _]
      simp
    rw [trivial,gaussSum_one_one,Nat.card_eq_fintype_card,ZMod.card_units_eq_totient]
    norm_num
  have lower : 1 < r := by have := NeZero.pos r; omega
  have h := DyadicMixedB4Ramanujan.ramanujan_moebius lower 1
  rw [DyadicMixedB4Ramanujan.ramanujan_natural_gauss lower] at h
  simp only [Nat.cast_one,AddChar.mulShift_one] at h
  rw [h,sum_eq_single_of_mem r (Nat.mem_divisors_self _ (NeZero.ne r))]
  · simp [DyadicMixedB4MoebiusGauss.moebiusComplex,Nat.div_self (NeZero.pos r)]
  · intro d hd hne
    have h : ¬r/d ∣ 1 := by
      intro hone
      have he := Nat.eq_one_of_dvd_one hone
      apply hne
      simpa only [he,one_mul] using Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1
    simp [h]

/-- The binary convolution of a primitive character with the principal
character equals the original character multiplied by the Möbius function of
its conductor. This identity holds on every residue, including nonunits. -/
theorem mixed_jacobi {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ZMod r) : J χ 1 m = (ArithmeticFunction.moebius r:ℂ)*χ m := by
  have conv : ZMod.dft (J χ 1) = fun t => ZMod.dft χ t * ZMod.dft (1 : DirichletCharacter ℂ r) t := by
    funext t
    rw [fourierTransform_eq_gaussSum_mulShift,fourierTransform_eq_gaussSum_mulShift,gaussSum_mul,
      ZMod.dft_apply]
    apply sum_congr rfl
    intro y _
    rw [← sum_mul,smul_eq_mul,AddChar.mulShift_apply]
    simp only [J,mul_neg,mul_comm]
  have eqn : J χ 1 = fun y => (ArithmeticFunction.moebius r:ℂ)*χ y := by
    apply ZMod.dft.injective
    rw [conv,ZMod.dft_const_mul]
    funext t
    by_cases hu : IsUnit (-t)
    · have shift := gaussSum_mulShift_eq (1 : DirichletCharacter ℂ r) ZMod.stdAddChar hu.unit
      simp only [hu.unit_spec,inv_one,MulChar.one_apply hu,one_mul,principal_gauss] at shift
      rw [fourierTransform_eq_gaussSum_mulShift (1 : DirichletCharacter ℂ r),shift,mul_comm]
    · rw [hχ.fourierTransform_eq_inv_mul_gaussSum,(χ⁻¹).map_nonunit hu,zero_mul,zero_mul,mul_zero]
  exact congrFun eqn m

/-- The full mixed series, with no unsummed denominator terms. -/
theorem mixed_exact {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) :
    series χ (1 : DirichletCharacter ℂ 1) m * J (1 : DirichletCharacter ℂ r) 1 (m:ZMod r) =
      series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
        ((ArithmeticFunction.moebius r:ℂ)*χ (m:ZMod r)) := by
  have h := conductor_identity (β := (1 : DirichletCharacter ℂ 1)) hχ isPrimitive_one_level_one
    (dvd_refl r) (one_dvd r) m hm
  simpa only [series,changeLevel_self,map_one,mixed_jacobi χ hχ] using h

noncomputable def localWeight (m p : ℕ) : ℝ :=
  if p ∣ m then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2

noncomputable def ordinaryWeight (q m : ℕ) [NeZero q] : ℝ :=
  (q:ℝ) * ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ / (q.totient:ℝ)^2

private theorem weight_prime_power {p : ℕ} [hp : Fact p.Prime] (a m : ℕ) (ha : 0 < a) :
    ordinaryWeight (p^a) m = localWeight m p := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  have fpos : (0:ℝ) < ((p^j:ℕ):ℝ) := by exact_mod_cast pow_pos hp.out.pos j
  have ppos : (0:ℝ) < (p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast hp.out.one_lt)
  have form (q : ℕ) [NeZero q] (hq : q=p*p^j) : ordinaryWeight q m = localWeight m p := by
    subst q
    have tot : (p*p^j).totient = p^j*(p-1) := by rw [← pow_succ',Nat.totient_prime_pow_succ hp.out]
    unfold ordinaryWeight
    rw [tot,ordinary_prime_power,Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hp.out.one_le,Nat.cast_one]
    unfold localWeight
    split_ifs <;> field_simp [fpos.ne',ppos.ne']
  exact form _ (pow_succ' p j)

/-- The finite ordinary count has exactly the usual Euler factor at every
prime dividing the modulus, independent of its exponent. -/
theorem ordinary_product (q m : ℕ) [NeZero q] :
    ordinaryWeight q m = ∏ p ∈ q.primeFactors, localWeight m p := by
  let F (p : q.primeFactors) := (p:ℕ)^(q.factorization p)
  have pp (p : q.primeFactors) : (p:ℕ).Prime := Nat.prime_of_mem_primeFactors p.property
  let _ : ∀ p : q.primeFactors, Fact (p:ℕ).Prime := fun p => ⟨pp p⟩
  let _ : ∀ p : q.primeFactors, NeZero (F p) := fun p => ⟨pow_ne_zero _ (pp p).ne_zero⟩
  have expo (p : q.primeFactors) : 0 < q.factorization (p:ℕ) :=
    (pp p).factorization_pos_of_dvd (NeZero.ne q) (Nat.dvd_of_mem_primeFactors p.property)
  let e : ZMod q ≃+* ∀ p : q.primeFactors, ZMod (F p) := ZMod.equivPi q (NeZero.ne q)
  have hJ := local_factors e (1 : DirichletCharacter ℂ q) 1 m
  simp only [component_one] at hJ
  have hr : (q:ℝ) = ∏ p : q.primeFactors, (F p:ℝ) := by
    exact_mod_cast Nat.prod_primeFactors_coe_pow_factorization (NeZero.ne q)
  have hφ : q.totient = ∏ p : q.primeFactors, (F p).totient := by
    rw [Nat.totient_eq_prod_factorization (NeZero.ne q),Nat.prod_factorization_eq_prod_primeFactors]
    simp only [F,Nat.totient_prime_pow (pp _) (expo _)]
    exact (Finset.prod_coe_sort q.primeFactors (fun p : ℕ => p^(q.factorization p-1)*(p-1))).symm
  have hφr : (q.totient:ℝ) = ∏ p : q.primeFactors, ((F p).totient:ℝ) := by exact_mod_cast hφ
  unfold ordinaryWeight
  rw [hr,hφr,hJ,norm_prod,← prod_mul_distrib,← prod_pow,← prod_div_distrib]
  rw [← Finset.prod_coe_sort q.primeFactors (localWeight m)]
  apply prod_congr rfl
  intro p _
  exact weight_prime_power _ m (expo p)

private theorem local_minimum {p : ℕ} (hp : 2 ≤ p) (m : ℕ) :
    1-1/((p:ℝ)-1)^2 ≤ localWeight m p := by
  have hpos : (0:ℝ) < (p:ℝ)-1 := sub_pos.mpr (by exact_mod_cast (by omega : 1 < p))
  unfold localWeight
  split_ifs
  · apply (sub_le_self (1:ℝ) (by positivity)).trans
    exact (le_div_iff₀ hpos).mpr (by linarith)
  · apply le_of_eq
    field_simp [hpos.ne']
    ring

private theorem truncated_lower (S : Finset ℕ) (hp : ∀ p ∈ S, p.Prime) (m : ℕ) (he : Even m) :
    ∀ P : ℕ, 2 ≤ P →
      (if 2 ∈ S then (2:ℝ) else 1) * P / (2*((P:ℝ)-1)) ≤
        ∏ p ∈ range (P+1), (if p ∈ S then localWeight m p else 1) := by
  let a : ℝ := if 2 ∈ S then 2 else 1
  have ha : 0 < a := by dsimp [a]; split <;> norm_num
  intro P hP
  induction P,hP using Nat.le_induction with
  | base =>
    have h0 : 0 ∉ S := fun h => Nat.not_prime_zero (hp 0 h)
    have h1 : 1 ∉ S := fun h => Nat.not_prime_one (hp 1 h)
    have h2 : 2 ∣ m := even_iff_two_dvd.mp he
    rw [show range (2+1) = {0,1,2} by decide]
    by_cases ht : 2 ∈ S <;> norm_num [h0,h1,ht,localWeight,h2]
  | succ k hk ih =>
    have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
    let b : ℝ := 1-1/(k:ℝ)^2
    have hb : 0 ≤ b := by
      apply sub_nonneg.mpr
      apply (div_le_one (by positivity : 0 < (k:ℝ)^2)).mpr
      nlinarith [sq_nonneg ((k:ℝ)-2)]
    have hf : b ≤ (if k+1 ∈ S then localWeight m (k+1) else 1) := by
      split_ifs
      · simpa [b] using local_minimum (p := k+1) (by omega) m
      · exact sub_le_self _ (by positivity)
    change a*(k:ℝ)/(2*((k:ℝ)-1)) ≤ _ at ih
    have left : 0 ≤ a*(k:ℝ)/(2*((k:ℝ)-1)) :=
      div_nonneg (mul_nonneg ha.le (Nat.cast_nonneg k)) (by linarith)
    rw [prod_range_succ]
    refine le_trans ?_ (mul_le_mul ih hf hb (left.trans ih))
    change a*((k+1:ℕ):ℝ)/(2*(((k+1:ℕ):ℝ)-1)) ≤ (a*(k:ℝ)/(2*((k:ℝ)-1))) * b
    apply le_of_eq
    push_cast
    dsimp [b]
    field_simp [show (k:ℝ)-1 ≠ 0 by linarith,show (k:ℝ) ≠ 0 by linarith]
    ring

theorem uniform_weight (q m : ℕ) [NeZero q] (he : Even m) :
    (if 2 ∣ q then (1:ℝ) else 1/2) ≤ ordinaryWeight q m := by
  let P := max 2 q
  have hP : 2 ≤ P := le_max_left ..
  have hr : (2:ℝ) ≤ P := by exact_mod_cast hP
  have cover : q.primeFactors ⊆ range (P+1) := fun p hp =>
    mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_of_mem_primeFactors hp).trans (le_max_right ..)))
  have h := truncated_lower q.primeFactors (fun _ hp => Nat.prime_of_mem_primeFactors hp) m he P hP
  simp only [prod_ite_mem,inter_eq_right.mpr cover] at h
  rw [ordinary_product]
  apply le_trans _ h
  have two : 2 ∈ q.primeFactors ↔ 2 ∣ q :=
    ⟨Nat.dvd_of_mem_primeFactors,fun h => Nat.mem_primeFactors.mpr ⟨Nat.prime_two,h,NeZero.ne q⟩⟩
  by_cases ht : 2 ∣ q <;> simp only [two,ht,ite_true,ite_false,one_mul]
  all_goals apply (le_div_iff₀ (by linarith : (0:ℝ) < 2*((P:ℝ)-1))).mpr; linarith

/-- The ordinary infinite series at a positive even target has real part
at least one. -/
theorem ordinary_at_least_one (m : ℕ) (hm : 0 < m) (he : Even m) :
    1 ≤ (series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m).re := by
  let O : DirichletCharacter ℂ 1 := 1
  have lim := (TwistedGoldbachSingularSeries.partial_limit O O m hm 2 (by decide)).norm
  have lower : 1 ≤ ‖series O O m‖ := by
    apply ge_of_tendsto' lim
    intro n
    let q := 2*n.factorial
    let _ : NeZero q := ⟨mul_ne_zero (by decide) n.factorial_ne_zero⟩
    have hf := uniform_weight q m he
    rw [ite_eq_left (dvd_mul_right 2 n.factorial)] at hf
    have amb := TwistedGoldbachSingularSeries.ambient_sum (α := O) (β := O)
      isPrimitive_one_level_one isPrimitive_one_level_one (one_dvd q) (one_dvd q) m
    simp only [O,map_one] at amb
    change 1 ≤ ‖∑ d ∈ q.divisors, TwistedGoldbachSingularSeries.coefficient O O m d‖
    rw [← amb]
    simpa only [TwistedGoldbachSingularSeries.normalized,norm_div,norm_mul,norm_pow,
      Complex.norm_natCast,ordinaryWeight,J] using hf
  exact lower.trans (TwistedGoldbachSingularSeries.infinite_domination (α := O) (β := O)
    isPrimitive_one_level_one isPrimitive_one_level_one m hm)

/-- A mixed contribution vanishes at a nonsquarefree conductor or a nonunit
target. -/
theorem mixed_zero {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (bad : ¬Squarefree r ∨ ¬m.Coprime r) :
    series χ (1 : DirichletCharacter ℂ 1) m = 0 := by
  have h := mixed_exact χ hχ m hm
  apply (mul_eq_zero.mp (show series χ (1 : DirichletCharacter ℂ 1) m *
      J (1 : DirichletCharacter ℂ r) 1 (m:ZMod r) = 0 from ?_)).resolve_right (principal_ne_zero r m he)
  rw [h]
  rcases bad with hs | hc
  · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
  · simp [χ.map_nonunit (fun hu => hc ((ZMod.isUnit_iff_coprime m r).mp hu))]

/-- Explicit constant in the uniform mixed-pair bound used in (11.10) of
Pintz I and (8.1) of Bhowmik--Grimmelt. -/
theorem mixed_bound {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    ‖series χ (1 : DirichletCharacter ℂ 1) m‖ ≤
      (2*(r:ℝ)/(r.totient:ℝ)^2) * ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (mixed_exact χ hχ m hm)
  simp only [norm_mul] at h
  have small : ‖(ArithmeticFunction.moebius r:ℂ)‖ * ‖χ (m:ZMod r)‖ ≤ 1 :=
    (mul_le_mul (DyadicMixedB4MoebiusGauss.norm_moebiusComplex_le_one r)
      (χ.norm_le_one _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hφ : (0:ℝ) < (r.totient:ℝ)^2 := sq_pos_of_pos (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos r))
  have base : 1/2 ≤ ordinaryWeight r m := by
    apply le_trans _ (uniform_weight r m he)
    split <;> norm_num
  have total := (le_div_iff₀ hφ).mp base
  let O : ℝ := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let T : ℝ := ‖series χ (1 : DirichletCharacter ℂ 1) m‖
  let D : ℝ := ‖J (1 : DirichletCharacter ℂ r) 1 (m:ZMod r)‖
  have a : T*D ≤ O := h.le.trans ((mul_le_mul_of_nonneg_left small (norm_nonneg _)).trans_eq (mul_one _))
  have b : (r.totient:ℝ)^2 ≤ 2*(r:ℝ)*D := by change 1/2*(r.totient:ℝ)^2 ≤ (r:ℝ)*D at total; linarith
  change T ≤ (2*(r:ℝ)/(r.totient:ℝ)^2)*O
  rw [div_mul_eq_mul_div,le_div_iff₀ hφ]
  calc
    T*(r.totient:ℝ)^2 ≤ T*(2*(r:ℝ)*D) := mul_le_mul_of_nonneg_left b (norm_nonneg _)
    _ = 2*(r:ℝ)*(T*D) := by ring
    _ ≤ 2*(r:ℝ)*O := mul_le_mul_of_nonneg_left a (by positivity)

end Conjectures.Goldbach.TwistedGoldbachMixedPrincipal

set_option maxHeartbeats 1200000 in
open Conjectures.Goldbach.TwistedGoldbachMixedPrincipal in
theorem Conjectures.Goldbach.TwistedGoldbachMixedPrincipal :
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' d : ℕ, if hd : d ≠ 0 then
      let _ : NeZero d := ⟨hd⟩
      if h : r ∣ d ∧ s ∣ d then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod d))) / (d.totient : ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  exact
    (∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      ∀ m : ZMod r, (∑ x : ZMod r, χ x * (1 : DirichletCharacter ℂ r) (m-x)) =
        (ArithmeticFunction.moebius r:ℂ) * χ m) ∧
    (∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      ∀ m : ℕ, 0 < m →
      S χ (1 : DirichletCharacter ℂ 1) m *
        (∑ x : ZMod r, (1 : DirichletCharacter ℂ r) x * (1 : DirichletCharacter ℂ r) ((m:ZMod r)-x)) =
        O m * ((ArithmeticFunction.moebius r:ℂ)*χ (m:ZMod r))) ∧
    (∀ (q : ℕ) [NeZero q] (m : ℕ),
      let W := (q:ℝ)*‖∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) ((m:ZMod q)-x)‖/(q.totient:ℝ)^2
      W = (∏ p ∈ q.primeFactors, if p ∣ m then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2) ∧
      (Even m → (if 2 ∣ q then (1:ℝ) else 1/2) ≤ W)) ∧
    (∀ m : ℕ, 0 < m → Even m → 1 ≤ (O m).re) ∧
    (∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      ∀ m : ℕ, 0 < m → Even m → (¬Squarefree r ∨ ¬m.Coprime r) → S χ (1 : DirichletCharacter ℂ 1) m = 0) ∧
    (∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive →
      ∀ m : ℕ, 0 < m → Even m →
      ‖S χ (1 : DirichletCharacter ℂ 1) m‖ ≤ (2*(r:ℝ)/(r.totient:ℝ)^2)*‖O m‖) := by
  exact ⟨fun _ _ χ hχ m => mixed_jacobi χ hχ m,fun _ _ χ hχ m hm => mixed_exact χ hχ m hm,
    fun q _ m => ⟨ordinary_product q m,uniform_weight q m⟩,ordinary_at_least_one,
    fun _ _ χ hχ m hm he h => mixed_zero χ hχ m hm he h,
    fun _ _ χ hχ m hm he => mixed_bound χ hχ m hm he⟩
