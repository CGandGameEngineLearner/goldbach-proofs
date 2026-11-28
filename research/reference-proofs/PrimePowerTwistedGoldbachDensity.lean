import Conjectures.Goldbach.B13BilateralVaughanReduction

/-! Complete twisted binary densities on arbitrary residue rings. For a pair of
primitive characters their convolution has exactly the norm of the Fourier
transform of the inverse product character. This also covers imprimitive
products, where the conductor can be much smaller than either input level. -/

namespace Conjectures.Goldbach.PrimePowerTwistedGoldbachDensity

open Finset DirichletCharacter
open scoped BigOperators Classical

noncomputable def density {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    ℂ := ∑ a : ZMod q, χ a * ψ (m-a)

private theorem transform {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) :
    ZMod.dft (density χ ψ) = fun t => ZMod.dft χ t * ZMod.dft ψ t := by
  funext t
  rw [fourierTransform_eq_gaussSum_mulShift,fourierTransform_eq_gaussSum_mulShift,gaussSum_mul,
    ZMod.dft_apply]
  apply sum_congr rfl
  intro m _
  rw [← sum_mul,smul_eq_mul,AddChar.mulShift_apply]
  simp only [density,mul_neg,mul_comm]

theorem phase_relation {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (m : ZMod q) :
    (q:ℂ)*density χ ψ m =
      (gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar) *
      ZMod.dft (fun t => (χ*ψ)⁻¹ t) m := by
  let G := gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar
  have ht : ZMod.dft (density χ ψ) = fun t => G*(χ*ψ)⁻¹ (-t) := by
    rw [transform]
    funext t
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum,hψ.fourierTransform_eq_inv_mul_gaussSum]
    simp only [G,mul_inv,MulChar.mul_apply]
    ring
  have hi := congrFun (ZMod.dft_dft (density χ ψ)) (-m)
  rw [ht,ZMod.dft_const_mul G] at hi
  change G * ZMod.dft (fun t => (χ*ψ)⁻¹ (-t)) (-m) = (q:ℂ) • density χ ψ (- -m) at hi
  rw [ZMod.dft_comp_neg (fun t => (χ*ψ)⁻¹ t)] at hi
  simpa only [neg_neg,smul_eq_mul] using hi.symm

theorem primitive_norm {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (m : ZMod q) :
    ‖density χ ψ m‖ = ‖ZMod.dft (fun t => (χ*ψ)⁻¹ t) m‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (phase_relation hχ hψ m)
  simp only [norm_mul,Complex.norm_natCast,norm_gaussSum_stdAddChar hχ,
    norm_gaussSum_stdAddChar hψ,Real.mul_self_sqrt (Nat.cast_nonneg q)] at h
  exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne q : (q:ℝ)≠0) h

theorem primitive_product {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (hprod : (χ*ψ).IsPrimitive) (m : ZMod q) :
    ‖density χ ψ m‖ = if IsUnit m then Real.sqrt q else 0 := by
  rw [primitive_norm hχ hψ]
  change ‖ZMod.dft (⇑((χ*ψ)⁻¹)) m‖ = _
  rw [hprod.inv.fourierTransform_eq_inv_mul_gaussSum,norm_mul,norm_gaussSum_stdAddChar hprod.inv,
    inv_inv]
  by_cases hm : IsUnit m
  · have h : ‖(χ*ψ) (-m)‖ = 1 := (χ*ψ).unit_norm_eq_one hm.neg.unit
    rw [ite_eq_left hm,h,one_mul]
  · rw [ite_eq_right hm,MulChar.map_nonunit _ (by simpa using hm : ¬ IsUnit (-m)),norm_zero,zero_mul]

open B13BilateralVaughanReductionProof

private theorem lifted_character {d f : ℕ} [NeZero d] [NeZero f]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d) (a : ℕ) :
    changeLevel (dvd_mul_right d f) θ (a : ZMod (d*f)) = θ (a : ZMod d) := by
  rw [DyadicMixedB4MoebiusGauss.changeLevel_nat_indicator]
  by_cases h : a.Coprime d
  · rw [ite_eq_left (Nat.coprime_mul_iff_right.mpr ⟨h,support a h⟩),one_mul]
  · have hz : θ (a : ZMod d)=0 := θ.map_nonunit (fun hu => h ((ZMod.isUnit_iff_coprime a d).mp hu))
    simp only [hz,mul_zero]

/-- Exact Fourier support of a lifted character whenever the larger modulus
has the same prime support. Lifting introduces a divisibility condition on the
frequency and multiplies the surviving lower-level Gauss sum by the fiber size. -/
theorem lifted_gauss {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d) (k : ℕ) :
    gaussSum (changeLevel (dvd_mul_right d f) θ) (ZMod.stdAddChar.mulShift (k : ZMod (d*f))) =
      if f ∣ k then (f:ℂ)*gaussSum θ (ZMod.stdAddChar.mulShift ((k/f : ℕ) : ZMod d)) else 0 := by
  rw [DyadicMixedB4GaussLift.gaussSum_as_fraction_sum]
  simp only [lifted_character support,Nat.cast_mul]
  exact DyadicMixedB4GaussLift.lift_gaussSum θ k

private theorem neg_frequency {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (k : ℕ) :
    ‖density χ ψ (-(k : ZMod q))‖ =
      ‖gaussSum (χ*ψ)⁻¹ (ZMod.stdAddChar.mulShift (k : ZMod q))‖ := by
  rw [primitive_norm hχ hψ]
  simp only [fourierTransform_eq_gaussSum_mulShift,neg_neg]

private theorem primitive_gauss {d : ℕ} [NeZero d] {θ : DirichletCharacter ℂ d}
    (hθ : θ.IsPrimitive) (a : ℕ) :
    ‖gaussSum θ (ZMod.stdAddChar.mulShift (a : ZMod d))‖ =
      if a.Coprime d then Real.sqrt d else 0 := by
  rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hθ,norm_mul,norm_gaussSum_stdAddChar hθ]
  by_cases ha : a.Coprime d
  · rw [ite_eq_left ha]
    have v : ‖θ⁻¹ (a : ZMod d)‖=1 := θ⁻¹.unit_norm_eq_one (ZMod.unitOfCoprime a ha)
    rw [v,one_mul]
  · rw [ite_eq_right ha,MulChar.map_nonunit _ (fun hu => ha ((ZMod.isUnit_iff_coprime a d).mp hu)),
      norm_zero,zero_mul]

/-- Thin-shell support for a primitive pair whose product is induced from a
primitive character of positive level with the same prime factors. -/
theorem conductor_shell {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f)
    {χ ψ : DirichletCharacter ℂ (d*f)} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    {θ : DirichletCharacter ℂ d} (hθ : θ.IsPrimitive)
    (lift : (χ*ψ)⁻¹ = changeLevel (dvd_mul_right d f) θ) (k : ℕ) :
    ‖density χ ψ (-(k : ZMod (d*f)))‖ =
      if f ∣ k ∧ (k/f).Coprime d then (f:ℝ)*Real.sqrt d else 0 := by
  rw [neg_frequency hχ hψ,lift,lifted_gauss support]
  by_cases h : f ∣ k
  · rw [ite_eq_left h,norm_mul,Complex.norm_natCast,primitive_gauss hθ]
    by_cases hc : (k/f).Coprime d <;> simp [h,hc]
  · simp [h]

/-- Primitive and properly lifted characters have disjoint Fourier supports if
no new prime divides the larger level. Their convolution vanishes at every
target, even the zero target. -/
theorem mixed_vanishes {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (hf : 1 < f) (support : ∀ a : ℕ, a.Coprime d → a.Coprime f)
    {χ : DirichletCharacter ℂ (d*f)} (hχ : χ.IsPrimitive) (ψ : DirichletCharacter ℂ d)
    (m : ZMod (d*f)) : density χ (changeLevel (dvd_mul_right d f) ψ) m = 0 := by
  have ht : ZMod.dft (density χ (changeLevel (dvd_mul_right d f) ψ)) = 0 := by
    rw [transform]
    funext t
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum,fourierTransform_eq_gaussSum_mulShift]
    by_cases hu : IsUnit (-t)
    · let a := (-t).val
      have ha : (a : ZMod (d*f)) = -t := ZMod.natCast_zmod_val _
      have hc : a.Coprime (d*f) := (ZMod.isUnit_iff_coprime a (d*f)).mp (ha.symm ▸ hu)
      have hn : ¬ f ∣ a := fun hd => hf.ne' (Nat.eq_one_of_dvd_coprimes hc hd (dvd_mul_left f d))
      rw [← ha,lifted_gauss support,ite_eq_right hn,mul_zero]
      rfl
    · rw [MulChar.map_nonunit _ hu,zero_mul,zero_mul]
      rfl
  have h := ZMod.dft.injective (ht.trans ZMod.dft.map_zero.symm)
  exact congrFun h m

private theorem prime_gauss_one {p : ℕ} [hp : Fact p.Prime] (a : ℕ) :
    gaussSum (1 : DirichletCharacter ℂ p) (ZMod.stdAddChar.mulShift (a : ZMod p)) =
      if p ∣ a then ((p-1 : ℕ):ℂ) else -1 := by
  by_cases h : p ∣ a
  · rw [ite_eq_left h,(ZMod.natCast_eq_zero_iff a p).mpr h,AddChar.mulShift_zero,gaussSum_one_one,
      Nat.card_eq_fintype_card,ZMod.card_units_eq_totient,Nat.totient_prime hp.out]
  · rw [ite_eq_right h]
    exact gaussSum_one_left (ZMod.isPrimitive_stdAddChar p (fun z => h ((ZMod.natCast_eq_zero_iff a p).mp z)))

/-- The remaining (principal product) case gives the exact prime-power
Ramanujan magnitude, including at multiples of the whole modulus. -/
theorem principal_product_power {p : ℕ} [hp : Fact p.Prime] (j : ℕ)
    {χ ψ : DirichletCharacter ℂ (p*p^j)} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    (invpair : χ*ψ=1) (k : ℕ) :
    ‖density χ ψ (-(k : ZMod (p*p^j)))‖ =
      if p^j ∣ k then ((p^j:ℕ):ℝ) * (if p ∣ k/p^j then (p:ℝ)-1 else 1) else 0 := by
  rw [neg_frequency hχ hψ,invpair,inv_one]
  have lift : (1 : DirichletCharacter ℂ (p*p^j)) =
      changeLevel (dvd_mul_right p (p^j)) (1 : DirichletCharacter ℂ p) := (map_one _).symm
  rw [lift,lifted_gauss (fun a (h : a.Coprime p) => h.pow_right j)]
  by_cases h : p^j ∣ k
  · rw [ite_eq_left h,ite_eq_left h,norm_mul,Complex.norm_natCast,prime_gauss_one]
    by_cases hq : p ∣ k/p^j
    · rw [ite_eq_left hq,ite_eq_left hq,Complex.norm_natCast,Nat.cast_sub hp.out.one_le,Nat.cast_one]
    · simp [hq]
  · simp [h]

/-- Reflection of the target changes only the phase, for arbitrary characters. -/
theorem reflected {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    ‖density χ ψ (-m)‖ = ‖density χ ψ m‖ := by
  have h : density χ ψ (-m) = (χ (-1)*ψ (-1))*density χ ψ m := by
    let F (a : ZMod q) := χ a * ψ (-m-a)
    calc
      _ = ∑ a : ZMod q, F (-a) := (Equiv.sum_comp (Equiv.neg _) F).symm
      _ = ∑ a : ZMod q, (χ (-1)*ψ (-1))*(χ a*ψ (m-a)) := by
        apply sum_congr rfl
        intro a _
        change χ (-a) * ψ (-m - -a) = _
        rw [show -m - -a = (-1)*(m-a) by ring,← neg_one_mul a,map_mul,map_mul]
        ring
      _ = _ := (mul_sum ..).symm
  rw [h,norm_mul,norm_mul,χ.norm_neg_one,ψ.norm_neg_one,one_mul,one_mul]

private theorem shell_at_level {d q : ℕ} [NeZero d] [NeZero q] (hd : d ∣ q)
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime (q/d))
    {χ ψ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive)
    {θ : DirichletCharacter ℂ d} (hθ : θ.IsPrimitive) (lift : (χ*ψ)⁻¹=changeLevel hd θ) (k : ℕ) :
    ‖density χ ψ (k : ZMod q)‖ =
      if q/d ∣ k ∧ (k/(q/d)).Coprime d then ((q/d:ℕ):ℝ)*Real.sqrt d else 0 := by
  obtain ⟨f,rfl⟩ := hd
  have hf : NeZero f := ⟨fun h => NeZero.ne (d*f) (by simp [h])⟩
  have hr : d*f/d=f := Nat.mul_div_cancel_left f (NeZero.pos d)
  rw [hr,← reflected]
  exact conductor_shell (by simpa only [hr] using support) hχ hψ hθ lift k

private theorem conductor_coprime {p d : ℕ} [hp : Fact p.Prime] (j : ℕ)
    (hd : d ∣ p*p^j) (hne : d≠1) {a : ℕ} (ha : a.Coprime d) : a.Coprime ((p*p^j)/d) := by
  have he : p*p^j=p^(j+1) := by ring
  rw [he] at hd ⊢
  obtain ⟨b,_,hb⟩ := (Nat.dvd_prime_pow hp.out).mp hd
  have hbpos : 0<b := by by_contra! hh; simp [hb, show b=0 by omega] at hne
  have hpa : a.Coprime p := (Nat.coprime_pow_right_iff hbpos _ _).mp (hb ▸ ha)
  exact (hpa.pow_right (j+1)).of_dvd_right (Nat.div_dvd_of_dvd hd)

/-- Complete prime-power norm when both characters are primitive.
The exceptional shell is determined by the conductor of their inverse product. -/
theorem prime_power_table {p : ℕ} [hp : Fact p.Prime] (j : ℕ)
    (χ ψ : DirichletCharacter ℂ (p*p^j)) (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (k : ℕ) :
    let d := ((χ*ψ)⁻¹).conductor
    let f := (p*p^j)/d
    ‖density χ ψ (k : ZMod (p*p^j))‖ = if χ*ψ=1 then
      (if p^j ∣ k then ((p^j:ℕ):ℝ)*(if p ∣ k/p^j then (p:ℝ)-1 else 1) else 0)
      else if f ∣ k ∧ (k/f).Coprime d then (f:ℝ)*Real.sqrt d else 0 := by
  intro d f
  by_cases h : χ*ψ=1
  · rw [ite_eq_left h,← reflected]
    exact principal_product_power j hχ hψ h k
  rw [ite_eq_right h]
  let θ := (χ*ψ)⁻¹
  let _ : NeZero d := ⟨fun hzero => NeZero.ne (p*p^j) (conductor_eq_zero_iff_level_eq_zero.mp hzero)⟩
  have hd : d ∣ p*p^j := θ.conductor_dvd_level
  have hd1 : d≠1 := by
    intro h1
    have hθ : θ=1 := (eq_one_iff_conductor_eq_one (χ := θ)).mpr h1
    exact h (inv_eq_one.mp hθ)
  exact shell_at_level hd (fun _ ha => conductor_coprime j hd hd1 ha) hχ hψ
    θ.primitiveCharacter_isPrimitive θ.changeLevel_primitiveCharacter.symm k

private theorem lift_residue {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d)
    (z : ZMod (d*f)) : changeLevel (dvd_mul_right d f) θ z =
      θ (ZMod.castHom (dvd_mul_right d f) (ZMod d) z) := by
  have h := lifted_character support θ z.val
  simpa only [← map_natCast (ZMod.castHom (dvd_mul_right d f) (ZMod d)), ZMod.natCast_zmod_val] using h

/-- When both characters descend, the density at the higher level is exactly
the fiber size times the lower-level density, with the target reduced as well. -/
theorem both_lifted {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (χ ψ : DirichletCharacter ℂ d)
    (m : ZMod (d*f)) :
    density (changeLevel (dvd_mul_right d f) χ) (changeLevel (dvd_mul_right d f) ψ) m =
      (f:ℂ)*density χ ψ (ZMod.castHom (dvd_mul_right d f) (ZMod d) m) := by
  let π := ZMod.castHom (dvd_mul_right d f) (ZMod d)
  unfold density
  rw [← DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod]
  simp only [lift_residue support,map_natCast,map_sub]
  rw [DyadicMixedB4GaussLift.sum_range_blocks]
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,zero_add,sum_const,card_range,
    nsmul_eq_mul]
  exact congrArg (fun z : ℂ => (f:ℂ)*z) (DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod
    (fun a : ZMod d => χ a * ψ (π m - a)))

end Conjectures.Goldbach.PrimePowerTwistedGoldbachDensity

open Conjectures.Goldbach.PrimePowerTwistedGoldbachDensity in
theorem Conjectures.Goldbach.PrimePowerTwistedGoldbachDensity :
by
  classical
  exact
    (∀ (q : ℕ) [NeZero q] (χ ψ : DirichletCharacter ℂ q),
      χ.IsPrimitive → ψ.IsPrimitive → ∀ m : ZMod q,
      (q:ℂ)*(∑ a : ZMod q, χ a * ψ (m-a)) =
        (gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar) *
          ZMod.dft (fun t => (χ*ψ)⁻¹ t) m) ∧
    (∀ (p : ℕ) [Fact p.Prime] (j : ℕ) (χ ψ : DirichletCharacter ℂ (p*p^j)),
      χ.IsPrimitive → ψ.IsPrimitive → ∀ k : ℕ,
      let d := ((χ*ψ)⁻¹).conductor
      let f := (p*p^j)/d
      ‖∑ a : ZMod (p*p^j), χ a * ψ ((k : ZMod (p*p^j))-a)‖ =
        if χ*ψ=1 then
          (if p^j ∣ k then ((p^j:ℕ):ℝ)*(if p ∣ k/p^j then (p:ℝ)-1 else 1) else 0)
        else if f ∣ k ∧ (k/f).Coprime d then (f:ℝ)*Real.sqrt d else 0) ∧
    (∀ (d f : ℕ) [NeZero d] [NeZero f] [NeZero (d*f)], 1 < f →
      (∀ a : ℕ, a.Coprime d → a.Coprime f) →
      ∀ (χ : DirichletCharacter ℂ (d*f)), χ.IsPrimitive → ∀ (ψ : DirichletCharacter ℂ d)
        (m : ZMod (d*f)),
        (∑ a : ZMod (d*f), χ a * (DirichletCharacter.changeLevel (dvd_mul_right d f) ψ) (m-a)) = 0) ∧
    (∀ (d f : ℕ) [NeZero d] [NeZero f] [NeZero (d*f)],
      (∀ a : ℕ, a.Coprime d → a.Coprime f) →
      ∀ (χ ψ : DirichletCharacter ℂ d) (m : ZMod (d*f)),
        (∑ a : ZMod (d*f), (DirichletCharacter.changeLevel (dvd_mul_right d f) χ) a *
          (DirichletCharacter.changeLevel (dvd_mul_right d f) ψ) (m-a)) =
        (f:ℂ)*(∑ a : ZMod d, χ a * ψ ((ZMod.castHom (dvd_mul_right d f) (ZMod d)) m-a))) := by
  exact ⟨fun _ _ _ _ hχ hψ m => phase_relation hχ hψ m,
    fun _ _ j χ ψ => prime_power_table j χ ψ,
    fun _ _ _ _ _ hf hs _ hχ ψ m => mixed_vanishes hf hs hχ ψ m,
    fun _ _ _ _ _ hs χ ψ m => both_lifted hs χ ψ m⟩
