import Conjectures.Goldbach.B13BilateralVaughanReduction
import Conjectures.Goldbach.DeepThreeQuartersExceptionalZeroCriterion

/-! The generalized Goldbach singular series for two primitive Dirichlet
characters. Grouping finite Fourier frequencies by reduced denominator gives
the totient-normalized residue density. A uniform bound for the three Gauss
sums gives absolute convergence at every positive target. Taking finite
levels divisible by every fixed denominator proves the first inequality in
Pintz, “A new explicit formula in the additive theory of primes with
applications I”, §7, (7.7), https://arxiv.org/abs/1804.05561.

The Gauss sums here use the positive additive phase, so the target frequency
in the third Gauss sum is negative. -/

namespace Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Finset DirichletCharacter
open scoped BigOperators Classical
open B13BilateralVaughanReductionProof

private theorem group_average {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (π : G →* H) (onto : Function.Surjective π) (F : H → ℂ) :
    (Fintype.card H : ℂ) * ∑ x : G, F (π x) = (Fintype.card G : ℂ) * ∑ y : H, F y := by
  have left (y : H) : (∑ x : G, F (y*π x)) = ∑ x : G, F (π x) := by
    obtain ⟨z,rfl⟩ := onto y
    simp_rw [← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft z) (fun x => F (π x))
  have right (x : G) : (∑ y : H, F (y*π x)) = ∑ y : H, F y :=
    Equiv.sum_comp (Equiv.mulRight (π x)) F
  calc
    _ = ∑ _y : H, ∑ x : G, F (π x) := by simp
    _ = ∑ y : H, ∑ x : G, F (y*π x) := sum_congr rfl (fun y _ => (left y).symm)
    _ = ∑ x : G, ∑ y : H, F (y*π x) := sum_comm
    _ = ∑ _x : G, ∑ y : H, F y := sum_congr rfl (fun x _ => right x)
    _ = _ := by simp

/-- Pushing a lifted character through the reduction of residues preserves
the totient-normalized weighted sum against every function on the divisor. -/
theorem induced_average {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (θ : DirichletCharacter ℂ d) (F : ZMod d → ℂ) :
    (d.totient:ℂ)*(∑ x : ZMod q, changeLevel h θ x * F (ZMod.castHom h (ZMod d) x)) =
      (q.totient:ℂ)*(∑ y : ZMod d, θ y * F y) := by
  let _ : Fintype (ZMod q)ˣ := BombieriVinogradov.LargeSieve.characterReductionUnitFintype q
  let _ : Fintype (ZMod d)ˣ := BombieriVinogradov.LargeSieve.characterReductionUnitFintype d
  rw [← BombieriVinogradov.LargeSieve.sum_units_eq_sum_residues,
    ← BombieriVinogradov.LargeSieve.sum_units_eq_sum_residues θ]
  simp only [changeLevel_eq_cast_of_dvd, ZMod.castHom_apply]
  simpa only [ZMod.card_units_eq_totient, ZMod.unitsMap_val] using
    group_average (ZMod.unitsMap h) (ZMod.unitsMap_surjective h)
      (fun u : (ZMod d)ˣ => θ (u : ZMod d) * F u)

/-- When a character does not factor through the divisor, its whole
pushforward measure vanishes, even before choosing a Fourier phase. -/
theorem absent_average {q d : ℕ} [NeZero q] (h : d ∣ q) (χ : DirichletCharacter ℂ q)
    (hn : ¬χ.FactorsThrough d) (F : ZMod d → ℂ) :
    (∑ x : ZMod q, χ x * F (ZMod.castHom h (ZMod d) x)) = 0 := by
  classical
  have hk := mt (factorsThrough_iff_ker_unitsMap h).mpr hn
  obtain ⟨u,hu,hχ⟩ := Set.not_subset.mp hk
  have hmem : ZMod.unitsMap h u = 1 := hu
  have hne : χ (u : ZMod q) ≠ 1 := by
    intro he
    apply hχ
    apply Units.ext
    exact he
  have hu' : ZMod.castHom h (ZMod d) (u : ZMod q) = 1 := congrArg Units.val hmem
  apply eq_zero_of_mul_eq_self_left hne
  let G (x : ZMod q) := χ x * F (ZMod.castHom h (ZMod d) x)
  calc
    _ = ∑ x : ZMod q, G (u*x) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x _
      simp only [G,map_mul,hu',one_mul,mul_assoc]
    _ = _ := u.mulLeft_bijective.sum_comp G

private theorem phase_descent {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (k : ℕ) (x : ZMod q) :
    ZMod.stdAddChar (((q/d*k : ℕ) : ZMod q)*x) =
      ZMod.stdAddChar ((k : ZMod d)*ZMod.castHom h (ZMod d) x) := by
  obtain ⟨f,rfl⟩ := h
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod (d*f)) = x := ⟨x.val,ZMod.natCast_zmod_val x⟩
  rw [Nat.mul_div_cancel_left f (NeZero.pos d), map_natCast, ← Nat.cast_mul, ← Nat.cast_mul,
    DyadicMixedB4GaussLift.stdAddChar_nat_fraction, DyadicMixedB4GaussLift.stdAddChar_nat_fraction]
  congr 1
  have hf : f ≠ 0 := fun e => NeZero.ne (d*f) (by simp [e])
  push_cast
  field_simp [NeZero.ne d,hf]

noncomputable def amplitude {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (k : ℕ) : ℂ :=
  gaussSum χ (ZMod.stdAddChar.mulShift (k : ZMod q)) / (q.totient:ℂ)

theorem amplitude_at_divisor {q d : ℕ} [NeZero q] [NeZero d] (h : d ∣ q)
    (χ : DirichletCharacter ℂ q) (k : ℕ) :
    amplitude χ (q/d*k) = if H : χ.FactorsThrough d then amplitude H.χ₀ k else 0 := by
  classical
  unfold amplitude gaussSum
  simp only [AddChar.mulShift_apply,phase_descent h]
  split_ifs with H
  · apply (div_eq_div_iff (Nat.cast_ne_zero.mpr (NeZero.ne q.totient))
        (Nat.cast_ne_zero.mpr (NeZero.ne d.totient))).mpr
    calc
      _ = (d.totient:ℂ)*(∑ x : ZMod q, changeLevel h H.χ₀ x *
        ZMod.stdAddChar ((k : ZMod d)*ZMod.castHom h (ZMod d) x)) := by
          conv_lhs => rw [H.eq_changeLevel]
          ring
      _ = _ := (induced_average h H.χ₀ (fun y => ZMod.stdAddChar ((k : ZMod d)*y))).trans (mul_comm ..)
  · rw [absent_average h χ H (fun y => ZMod.stdAddChar ((k : ZMod d)*y)),zero_div]

/-- Sort the frequencies at level q by their reduced denominator.
The zero frequency is the unique reduced numerator at denominator one. -/
theorem reduced_denominators (q : ℕ) [NeZero q] (F : ℕ → ℂ) :
    ∑ k ∈ range q, F k =
      ∑ d ∈ q.divisors, ∑ a ∈ (range d).filter (fun a => d.Coprime a), F (q/d*a) := by
  classical
  let T (g : ℕ) := ∑ k ∈ (range q).filter (fun k => q.gcd k=g), F k
  have part : ∑ k ∈ range q, F k = ∑ g ∈ q.divisors, T g :=
    (sum_fiberwise_of_maps_to (fun k (_ : k ∈ range q) =>
      Nat.mem_divisors.mpr ⟨q.gcd_dvd_left k,NeZero.ne q⟩) F).symm
  rw [part, ← Nat.sum_div_divisors q T]
  apply sum_congr rfl
  intro d hd
  obtain ⟨g,hg⟩ := Nat.dvd_of_mem_divisors hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hgpos : 0 < g := by
    by_contra! hg0
    exact NeZero.ne q (by simp [hg,show g=0 by omega])
  have hquot : q/d=g := by rw [hg,Nat.mul_div_cancel_left g hdpos]
  rw [hquot]
  unfold T
  symm
  apply sum_bij (fun a _ => g*a)
  · intro a ha
    obtain ⟨ha,hc⟩ := mem_filter.mp ha
    have hq : q=g*d := hg.trans (mul_comm d g)
    exact mem_filter.mpr ⟨mem_range.mpr (hq ▸ Nat.mul_lt_mul_of_pos_left (mem_range.mp ha) hgpos),
      by rw [hq,Nat.gcd_mul_left,hc.gcd_eq_one,mul_one]⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hgpos hab
  · intro k hk
    obtain ⟨hk,hc⟩ := mem_filter.mp hk
    obtain ⟨a,rfl⟩ : g ∣ k := hc ▸ q.gcd_dvd_right k
    have hq : q=g*d := hg.trans (mul_comm d g)
    rw [hq,Nat.gcd_mul_left] at hc
    have ha : a<d := (Nat.mul_lt_mul_left hgpos).mp (hq ▸ mem_range.mp hk)
    exact ⟨a,mem_filter.mpr ⟨mem_range.mpr ha, (mul_eq_left₀ hgpos.ne').mp hc⟩,rfl⟩
  · intro _ _
    rfl

noncomputable def normalized {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) : ℂ :=
  ((q:ℂ)*∑ x : ZMod q, χ x * ψ ((m : ZMod q)-x)) / (q.totient:ℂ)^2

/-- The contribution of the reduced fractions of denominator d. It is zero
unless both characters descend. Its phases and Gauss sums are all at d. -/
noncomputable def denominatorTerm {q : ℕ} (χ ψ : DirichletCharacter ℂ q) (m d : ℕ) : ℂ := by
  classical
  exact if hd : d ≠ 0 then
    let _ : NeZero d := ⟨hd⟩
    if H : χ.FactorsThrough d then
      if K : ψ.FactorsThrough d then
        ∑ a ∈ (range d).filter (fun a => d.Coprime a),
          ZMod.stdAddChar ((a : ZMod d)*(-(m : ZMod d))) * amplitude H.χ₀ a * amplitude K.χ₀ a
      else 0
    else 0
  else 0

private theorem synthesis {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    (∑ t : ZMod q, ZMod.stdAddChar (t*(-m)) * (gaussSum χ (ZMod.stdAddChar.mulShift t) *
      gaussSum ψ (ZMod.stdAddChar.mulShift t))) = (q:ℂ) * ∑ x : ZMod q, χ x * ψ (m-x) := by
  let J (s : ZMod q) := ∑ x : ZMod q, χ x * ψ (s-x)
  have h (t : ZMod q) : ZMod.dft J (-t) =
      gaussSum χ (ZMod.stdAddChar.mulShift t) * gaussSum ψ (ZMod.stdAddChar.mulShift t) := by
    rw [gaussSum_mul,ZMod.dft_apply]
    apply sum_congr rfl
    intro s _
    rw [← sum_mul]
    simp only [J,smul_eq_mul,mul_neg,neg_neg,AddChar.mulShift_apply,mul_comm]
  calc
    _ = ZMod.dft (fun t => ZMod.dft J (-t)) m := by
      rw [ZMod.dft_apply]
      apply sum_congr rfl
      intro t _
      rw [h,smul_eq_mul,mul_neg]
    _ = _ := by rw [ZMod.dft_comp_neg,ZMod.dft_dft]; simp only [J,neg_neg,smul_eq_mul]

theorem finite_expansion {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) :
    normalized χ ψ m = ∑ d ∈ q.divisors, denominatorTerm χ ψ m d := by
  let F (k : ℕ) := ZMod.stdAddChar ((k : ZMod q)*(-(m : ZMod q))) * amplitude χ k * amplitude ψ k
  have H : normalized χ ψ m = ∑ k ∈ range q, F k := by
    unfold normalized
    rw [← synthesis, ← DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod, sum_div]
    apply sum_congr rfl
    intro k _
    dsimp only [F,amplitude]
    ring
  rw [H,reduced_denominators q F]
  apply sum_congr rfl
  intro d hd
  have hd0 := (Nat.pos_of_mem_divisors hd).ne'
  let _ : NeZero d := ⟨hd0⟩
  have divides := Nat.dvd_of_mem_divisors hd
  unfold denominatorTerm
  simp only [dite_eq_left hd0]
  by_cases Hχ : χ.FactorsThrough d <;> by_cases Hψ : ψ.FactorsThrough d <;>
    simp only [F,amplitude_at_divisor divides,phase_descent divides,map_neg,map_natCast,Hχ,Hψ,
      dite_true,dite_false,mul_zero,zero_mul,sum_const_zero]

theorem conductor_support {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m d : ℕ)
    (h : ¬Nat.lcm χ.conductor ψ.conductor ∣ d) : denominatorTerm χ ψ m d = 0 := by
  unfold denominatorTerm
  split_ifs with hd hχ hψ
  · exact False.elim (h (Nat.lcm_dvd (conductor_dvd_of_mem_conductorSet χ hχ)
      (conductor_dvd_of_mem_conductorSet ψ hψ)))
  all_goals rfl

private theorem principal_count {q : ℕ} [NeZero q] (m : ZMod q) :
    (∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) (m-x)) =
      (((univ : Finset (ZMod q)).filter (fun x => IsUnit x ∧ IsUnit (m-x))).card:ℂ) := by
  calc
    _ = ∑ x : ZMod q, if IsUnit x ∧ IsUnit (m-x) then (1:ℂ) else 0 := by
      apply sum_congr rfl
      intro x _
      by_cases hu : IsUnit x <;> by_cases hv : IsUnit (m-x) <;>
        simp [hu,hv,MulChar.one_apply,MulChar.map_nonunit]
    _ = _ := by simp

/-- Absolute values of the finite twisted residue counts are bounded by the
ordinary count on the same modulus, including composite moduli. -/
theorem chars_le_units {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q)
    (m : ZMod q) : ‖∑ x : ZMod q, χ x * ψ (m-x)‖ ≤
      ‖∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) (m-x)‖ := by
  rw [principal_count,Complex.norm_natCast]
  calc
    _ ≤ ∑ x : ZMod q, ‖χ x * ψ (m-x)‖ := norm_sum_le _ _
    _ ≤ ∑ x : ZMod q, if IsUnit x ∧ IsUnit (m-x) then (1:ℝ) else 0 := by
      apply sum_le_sum
      intro x _
      by_cases hu : IsUnit x
      · by_cases hv : IsUnit (m-x)
        · rw [ite_eq_left ⟨hu,hv⟩,norm_mul]
          simpa only [one_mul] using mul_le_mul (χ.norm_le_one x) (ψ.norm_le_one (m-x))
            (norm_nonneg _) zero_le_one
        · simp [hv,ψ.map_nonunit hv]
      · simp [hu,χ.map_nonunit hu]
    _ = _ := by simp

/-- Every complete divisor sum is dominated by the ordinary singular-series
sum at the same level and target, without any primitivity assumption. -/
theorem domination {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ℕ) :
    ‖∑ d ∈ q.divisors, denominatorTerm χ ψ m d‖ ≤
      ‖∑ d ∈ q.divisors, denominatorTerm (1 : DirichletCharacter ℂ q) 1 m d‖ := by
  rw [← finite_expansion,← finite_expansion]
  simp only [normalized,norm_div,norm_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (chars_le_units χ ψ _) (norm_nonneg _))
    (norm_nonneg _)

/-- The numerator sum at a reduced denominator is a product of three Gauss
sums. The first two use frequency one, the third uses the actual target. -/
noncomputable def gaussCoefficient {d : ℕ} [NeZero d] (χ ψ : DirichletCharacter ℂ d) (m : ℕ) : ℂ :=
  (gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar *
    gaussSum (χ*ψ)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod d)))) / (d.totient:ℂ)^2

theorem reduced_numerators {d : ℕ} [NeZero d] (χ ψ : DirichletCharacter ℂ d) (m : ℕ) :
    (∑ a ∈ (range d).filter (fun a => d.Coprime a), ZMod.stdAddChar ((a : ZMod d)*(-(m : ZMod d))) *
      amplitude χ a * amplitude ψ a) = gaussCoefficient χ ψ m := by
  let A := gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar / (d.totient:ℂ)^2
  let F (z : ZMod d) := (χ*ψ)⁻¹ z * ZMod.stdAddChar ((-(m : ZMod d))*z)
  have shift (θ : DirichletCharacter ℂ d) (a : ℕ) (hc : a.Coprime d) :
      gaussSum θ (ZMod.stdAddChar.mulShift (a : ZMod d)) =
        θ⁻¹ (a : ZMod d) * gaussSum θ ZMod.stdAddChar :=
    gaussSum_mulShift_eq θ ZMod.stdAddChar (ZMod.unitOfCoprime a hc)
  rw [sum_filter]
  calc
    _ = ∑ a ∈ range d, A * F (a : ZMod d) := by
      apply sum_congr rfl
      intro a _
      by_cases hc : d.Coprime a
      · simp only [ite_eq_left hc,A,F,amplitude,shift _ _ hc.symm,mul_inv,MulChar.mul_apply]
        rw [mul_comm (a : ZMod d) (-(m : ZMod d))]
        ring
      · have hnu : ¬IsUnit (a : ZMod d) := fun hu => hc ((ZMod.isUnit_iff_coprime a d).mp hu).symm
        simp only [ite_eq_right hc,F,MulChar.map_nonunit _ hnu,zero_mul,mul_zero]
    _ = A * ∑ z : ZMod d, F z := by
      rw [← mul_sum,DyadicMixedB4DualCharacter.sum_natCast_range_eq_zmod F]
    _ = _ := by unfold A F gaussCoefficient gaussSum; simp only [AddChar.mulShift_apply]; ring

/-- Denominator coefficient for two primitive source characters. It is
defined independently of the finite ambient modulus used in the expansion. -/
noncomputable def coefficient {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m d : ℕ) : ℂ := by
  classical
  exact if hd : d ≠ 0 then
    let _ : NeZero d := ⟨hd⟩
    if h : r ∣ d ∧ s ∣ d then gaussCoefficient (changeLevel h.1 α) (changeLevel h.2 β) m else 0
  else 0

private theorem factors_iff_source {r q d : ℕ} [NeZero q] {α : DirichletCharacter ℂ r}
    (hα : α.IsPrimitive) (hr : r ∣ q) (hd : d ∣ q) :
    (changeLevel hr α).FactorsThrough d ↔ r ∣ d := by
  constructor
  · intro H
    simpa only [conductor_changeLevel,show α.conductor=r from hα] using
      conductor_dvd_of_mem_conductorSet (changeLevel hr α) H
  · intro h
    exact ⟨hd,changeLevel h α,changeLevel_trans α h hd⟩

private theorem descended_character {r q d : ℕ} [NeZero q] (α : DirichletCharacter ℂ r)
    (hr : r ∣ q) (hd : d ∣ q) (h : r ∣ d) (H : (changeLevel hr α).FactorsThrough d) :
    H.χ₀ = changeLevel h α :=
  changeLevel_injective hd (H.eq_changeLevel.symm.trans (changeLevel_trans α h hd))

theorem stable_denominator {r s q : ℕ} [NeZero q] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ q) (hs : s ∣ q) (m d : ℕ) (hd : d ∣ q) :
    denominatorTerm (changeLevel hr α) (changeLevel hs β) m d = coefficient α β m d := by
  have hd0 : d ≠ 0 := fun e => NeZero.ne q (Nat.eq_zero_of_zero_dvd (e ▸ hd))
  let _ : NeZero d := ⟨hd0⟩
  simp only [denominatorTerm,coefficient,dite_eq_left hd0]
  by_cases H : r ∣ d
  · have H' := (factors_iff_source hα hr hd).mpr H
    by_cases K : s ∣ d
    · have K' := (factors_iff_source hβ hs hd).mpr K
      simp only [dite_eq_left H',dite_eq_left K',dite_eq_left (And.intro H K),reduced_numerators,
        descended_character α hr hd H H',descended_character β hs hd K K']
    · have K' := mt (factors_iff_source hβ hs hd).mp K
      simp only [dite_eq_left H',dite_eq_right K',dite_eq_right (not_and_of_not_right _ K)]
  · have H' := mt (factors_iff_source hα hr hd).mp H
    simp only [dite_eq_right H',dite_eq_right (not_and_of_not_left _ H)]

private theorem estimate_at_multiple {r s d : ℕ} [NeZero r] [NeZero s] [NeZero d]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (hr : r ∣ d) (hs : s ∣ d)
    (m : ℕ) (hm : 0 < m) :
    let R := Real.sqrt ((r*s:ℕ):ℝ)
    let M := ∑ f ∈ m.divisors, (f:ℝ)
    ‖gaussCoefficient (changeLevel hr α) (changeLevel hs β) m‖ ≤ R*R*(R*M)/(d.totient:ℝ)^2 := by
  intro R M
  let A := changeLevel hr α
  let B := changeLevel hs β
  let Z := (A*B)⁻¹
  have hrpos := Nat.mul_pos (NeZero.pos r) (NeZero.pos s)
  have cA : A.conductor ∣ r*s := by
    dsimp only [A]
    rw [conductor_changeLevel]
    exact α.conductor_dvd_level.trans (dvd_mul_right r s)
  have cB : B.conductor ∣ r*s := by
    dsimp only [B]
    rw [conductor_changeLevel]
    exact β.conductor_dvd_level.trans (dvd_mul_left s r)
  have cZ : Z.conductor ∣ r*s := by
    rw [show Z.conductor=(A*B).conductor from conductor_inv _]
    exact (conductor_mul_dvd_lcm_conductor A B).trans (Nat.lcm_dvd cA cB)
  have root {t : ℕ} (h : t ∣ r*s) : Real.sqrt t ≤ R :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_of_dvd hrpos h)
  have hA := (DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard A).trans (root cA)
  have hB := (DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_standard B).trans (root cB)
  have mass : (∑ f ∈ m.divisors.filter (fun f => Z.conductor*f ∣ d), (f:ℝ)) ≤ M :=
    sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun i _ _ => Nat.cast_nonneg i)
  have hsft := DyadicMixedB4CharacterFactorBound.norm_dirichlet_gauss_induced (dvd_refl d) Z m hm
  rw [changeLevel_self] at hsft
  have hZ := (DyadicMixedB4CharacterFactorBound.norm_gauss_neg_shift_le Z (m : ZMod d)).trans
    (hsft.trans (mul_le_mul (root cZ) mass (by positivity) (Real.sqrt_nonneg _)))
  change ‖(gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
    gaussSum Z (ZMod.stdAddChar.mulShift (-(m : ZMod d))))/(d.totient:ℂ)^2‖ ≤ _
  rw [norm_div,norm_pow,Complex.norm_natCast,norm_mul,norm_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul
    (mul_le_mul hA hB (norm_nonneg _) (Real.sqrt_nonneg _)) hZ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (sq_nonneg _)

private theorem totient_weight {d : ℕ} (hd : 0 < d) :
    1/(d.totient:ℝ)^2 ≤ 576 * (d:ℝ)^(-(3/2):ℝ) := by
  have h := DeepThreeQuarters.totient_ratio_le_rpow (show (0:ℝ)<1/4 by norm_num) d hd
  norm_num at h
  have dp : (0:ℝ)<d := by exact_mod_cast hd
  have hp : (0:ℝ)<d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have invbound : 1/(d.totient:ℝ) ≤ 24*(d:ℝ)^(-(3/4):ℝ) := by
    calc
      _ = ((d:ℝ)/d.totient)/d := by field_simp
      _ ≤ (24*(d:ℝ)^(1/4:ℝ))/d := div_le_div_of_nonneg_right h dp.le
      _ = _ := by
        rw [show (-(3/4):ℝ)=1/4-1 by norm_num,Real.rpow_sub dp,Real.rpow_one]
        ring
  have square := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/d.totient) invbound 2
  rw [div_pow,one_pow,mul_pow,← Real.rpow_mul_natCast dp.le] at square
  norm_num at square ⊢
  exact square

/-- Absolute convergence holds at every positive target. The divisor sum of
m controls the third Gauss sum uniformly as the reduced denominator varies. -/
theorem summable_coefficients {r s : ℕ} [NeZero r] [NeZero s]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m) :
    Summable (fun d : ℕ => ‖coefficient α β m d‖) := by
  let R := Real.sqrt ((r*s:ℕ):ℝ)
  let M := ∑ f ∈ m.divisors, (f:ℝ)
  let C := R*R*(R*M)
  have hC : 0≤C := by dsimp [C,M,R]; positivity
  have summable : Summable (fun d : ℕ => (d:ℝ)^(-(3/2):ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (summable.mul_left (C*576))
  intro d
  by_cases hd : d=0
  · simp [coefficient,hd,Real.zero_rpow (by norm_num : (-(3/2):ℝ) ≠ 0)]
  have bound0 : 0 ≤ C*576*(d:ℝ)^(-(3/2):ℝ) := by positivity
  let _ : NeZero d := ⟨hd⟩
  by_cases h : r ∣ d ∧ s ∣ d
  · simp only [coefficient,dite_eq_left hd,dite_eq_left h]
    calc
      _ ≤ C/(d.totient:ℝ)^2 := estimate_at_multiple α β h.1 h.2 m hm
      _ = C*(1/(d.totient:ℝ)^2) := by ring
      _ ≤ C*(576*(d:ℝ)^(-(3/2):ℝ)) := mul_le_mul_of_nonneg_left (totient_weight (Nat.pos_of_ne_zero hd)) hC
      _ = _ := by ring
  · simpa only [coefficient,dite_eq_left hd,dite_eq_right h,norm_zero] using bound0

theorem ambient_sum {r s q : ℕ} [NeZero q] {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ q) (hs : s ∣ q) (m : ℕ) :
    normalized (changeLevel hr α) (changeLevel hs β) m =
      ∑ d ∈ q.divisors, coefficient α β m d :=
  (finite_expansion _ _ m).trans (sum_congr rfl (fun d hd =>
    stable_denominator hα hβ hr hs m d (Nat.dvd_of_mem_divisors hd)))

open Filter Topology

private theorem cofinal_divisors (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => insert 0 (L*n.factorial).divisors) atTop atTop := by
  apply tendsto_atTop.2
  intro S
  filter_upwards [eventually_ge_atTop (S.sup id)] with n hn
  intro d hd
  by_cases h : d=0
  · simp [h]
  apply mem_insert_of_mem
  have hdn : d≤n := (S.le_sup (f := id) hd).trans hn
  exact Nat.mem_divisors.mpr ⟨(Nat.dvd_factorial (Nat.pos_of_ne_zero h) hdn).trans
    (dvd_mul_left n.factorial L),mul_ne_zero hL n.factorial_ne_zero⟩

/-- Complete divisor sums at L times n! exhaust the absolutely convergent
series, starting from any positive base level L. -/
theorem partial_limit {r s : ℕ} [NeZero r] [NeZero s]
    (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m)
    (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => ∑ d ∈ (L*n.factorial).divisors, coefficient α β m d)
      atTop (𝓝 (∑' d : ℕ, coefficient α β m d)) := by
  have h := (summable_coefficients α β m hm).of_norm.hasSum
  have hl := h.comp (cofinal_divisors L hL)
  apply hl.congr'
  filter_upwards with n
  simp [coefficient]

private theorem principal_real (q : ℕ) [NeZero q] (m : ℕ) :
    ‖normalized (1 : DirichletCharacter ℂ q) 1 m‖ = (normalized (1 : DirichletCharacter ℂ q) 1 m).re := by
  let N := ((univ : Finset (ZMod q)).filter (fun x => IsUnit x ∧ IsUnit ((m:ZMod q)-x))).card
  let v : ℝ := q*N/(q.totient:ℝ)^2
  have hv : 0≤v := by dsimp [v]; positivity
  have e : normalized (1 : DirichletCharacter ℂ q) 1 m = (v:ℂ) := by
    unfold normalized v
    rw [principal_count]
    push_cast
    rfl
  rw [e,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hv,Complex.ofReal_re]

/-- The absolute value of the full twisted singular series is at most the
ordinary singular series at each positive target. Both series converge
absolutely, with no zero-free hypothesis. -/
theorem infinite_domination {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) :
    ‖∑' d : ℕ, coefficient α β m d‖ ≤
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d).re := by
  let L := r*s
  have hL : L ≠ 0 := mul_ne_zero (NeZero.ne r) (NeZero.ne s)
  let oneχ : DirichletCharacter ℂ 1 := 1
  have main := partial_limit oneχ oneχ m hm L hL
  apply le_of_tendsto_of_tendsto' (partial_limit α β m hm L hL).norm (Complex.continuous_re.tendsto _ |>.comp main)
  intro n
  let q := L*n.factorial
  let _ : NeZero q := ⟨mul_ne_zero hL n.factorial_ne_zero⟩
  have hr : r ∣ q := (dvd_mul_right r s).trans (dvd_mul_right L n.factorial)
  have hs : s ∣ q := (dvd_mul_left s r).trans (dvd_mul_right L n.factorial)
  have ordinary := ambient_sum (α := oneχ) (β := oneχ) isPrimitive_one_level_one
    isPrimitive_one_level_one (one_dvd q) (one_dvd q) m
  simp only [oneχ,map_one] at ordinary
  change ‖∑ d ∈ q.divisors, coefficient α β m d‖ ≤
    (∑ d ∈ q.divisors, coefficient oneχ oneχ m d).re
  rw [← ambient_sum hα hβ hr hs m,← ordinary,← principal_real]
  simpa only [← finite_expansion] using domination (changeLevel hr α) (changeLevel hs β) m

end Conjectures.Goldbach.TwistedGoldbachSingularSeries

open Conjectures.Goldbach.TwistedGoldbachSingularSeries in
theorem Conjectures.Goldbach.TwistedGoldbachSingularSeries :
by
  classical
  let b := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m d : ℕ) =>
    if hd : d ≠ 0 then
      let _ : NeZero d := ⟨hd⟩
      if h : r ∣ d ∧ s ∣ d then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod d))) / (d.totient : ℂ)^2
      else 0
    else 0
  exact
    (∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      ∀ m : ℕ, 0 < m → Summable (fun d : ℕ => ‖b α β m d‖)) ∧
    (∀ (r s q : ℕ) [NeZero q] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ (hr : r ∣ q) (hs : s ∣ q) (m : ℕ),
      ((q:ℂ) * ∑ x : ZMod q, DirichletCharacter.changeLevel hr α x *
        DirichletCharacter.changeLevel hs β ((m : ZMod q)-x)) / (q.totient:ℂ)^2 =
        ∑ d ∈ q.divisors, b α β m d) ∧
    (∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m →
      ‖∑' d : ℕ, b α β m d‖ ≤
        (∑' d : ℕ, b (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d).re) := by
  exact ⟨fun _ _ _ _ α β m hm => summable_coefficients α β m hm,
    fun _ _ _ _ _ _ hα hβ hr hs m => ambient_sum hα hβ hr hs m,
    fun _ _ _ _ _ _ hα hβ m hm => infinite_domination hα hβ m hm⟩
