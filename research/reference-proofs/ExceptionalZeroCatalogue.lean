import Conjectures.Goldbach.SingleExceptionalZeroMajorFloor

/-! Actual Dirichlet zeros in the finite conductor and height windows
used by Pintz. Remove the pole for a principal character. The compact
windows then have finite zero sets with finite analytic multiplicities,
and the whole finite family has a uniform zero-free strip. -/

namespace Conjectures.Goldbach.ExceptionalZeroCatalogue

open Complex Set Filter DirichletCharacter
open scoped Topology Classical

noncomputable def regular {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) : ℂ → ℂ :=
  if χ=1 then LFunctionTrivChar₁ r else LFunction χ

def genuine {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ) : Prop :=
  (χ ≠ 1 ∨ z ≠ 1) ∧ LFunction χ z=0

theorem differentiable_regular {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) :
    Differentiable ℂ (regular χ) := by
  by_cases h : χ=1
  · rw [regular,ite_eq_left h]
    exact differentiable_LFunctionTrivChar₁ r
  · rw [regular,ite_eq_right h]
    exact differentiable_LFunction h

theorem regular_zero {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ) :
    regular χ z=0 ↔ genuine χ z := by
  classical
  by_cases h : χ=1
  · subst χ
    rw [regular,ite_eq_left rfl]
    by_cases atone : z=1
    · subst z
      exact iff_of_false (LFunctionTrivChar₁_apply_one_ne_zero r) (by simp [genuine])
    · rw [LFunctionTrivChar₁,Function.update_of_ne atone]
      simp [genuine,atone,sub_ne_zero.mpr atone,LFunctionTrivChar]
  · simp [regular,h,genuine]

theorem regular_ne {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ)
    (h : 1 ≤ z.re) : regular χ z ≠ 0 := by
  intro H
  obtain ⟨ok,zero⟩ := (regular_zero χ z).mp H
  exact LFunction_ne_zero_of_one_le_re χ ok h zero

/-- Zeros on any compact set are finite, with their true analytic orders. -/
theorem zeros_finite {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) {K : Set ℂ} (hK : IsCompact K) :
    {z : ℂ | z ∈ K ∧ genuine χ z}.Finite := by
  have H : AnalyticOnNhd ℂ (regular χ) univ := fun z _ => (differentiable_regular χ).analyticAt z
  have no := H.preimage_zero_mem_codiscrete (regular_ne χ 1 (by simp))
  have nearK : (regular χ) ⁻¹' ({0} : Set ℂ)ᶜ ∈ codiscreteWithin K :=
    (Filter.codiscreteWithin_mono (subset_univ K)) no
  have f := hK.finite_sdiff_of_mem_codiscreteWithin nearK
  apply f.subset
  intro z hz
  exact ⟨hz.1,by simp [(regular_zero χ z).mpr hz.2]⟩

theorem order_positive {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) {z : ℂ} (h : genuine χ z) :
    0 < analyticOrderNatAt (regular χ) z ∧
      analyticOrderAt (regular χ) z=(analyticOrderNatAt (regular χ) z : ℕ∞) := by
  have A (w : ℂ) := (differentiable_regular χ).analyticAt w
  have fne : regular χ ≠ 0 := fun eqn => regular_ne χ 1 (by simp) (congrFun eqn 1)
  have finite := mt (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero z A).mp fne
  have val := Nat.cast_analyticOrderNatAt finite
  refine ⟨?_,val.symm⟩
  by_contra! hz
  have top : analyticOrderAt (regular χ) z=0 := by rw [← val,show analyticOrderNatAt (regular χ) z=0 by omega]; rfl
  exact ((A z).analyticOrderAt_eq_zero.mp top) ((regular_zero χ z).mpr h)

/-- Every actual zero is repeated exactly its analytic multiplicity. -/
theorem zero_multiset {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) {K : Set ℂ}
    (hK : IsCompact K) : ∃ Z : Multiset ℂ,
      (∀ z : ℂ, z ∈ Z ↔ z ∈ K ∧ genuine χ z) ∧
      ∀ z ∈ Z, (Z.count z : ℕ∞)=analyticOrderAt (regular χ) z := by
  classical
  let A := (zeros_finite χ hK).toFinset
  let Z := ∑ z ∈ A, Multiset.replicate (analyticOrderNatAt (regular χ) z) z
  have mult (z : ℂ) : Z.count z = if z ∈ A then analyticOrderNatAt (regular χ) z else 0 := by
    simp only [Z,Multiset.count_sum',Multiset.count_replicate,Finset.sum_ite_eq']
  have mem (z : ℂ) : z ∈ Z ↔ z ∈ K ∧ genuine χ z := by
    rw [← Multiset.count_pos,mult]
    by_cases hz : z ∈ A
    · have H : z ∈ K ∧ genuine χ z := (zeros_finite χ hK).mem_toFinset.mp hz
      exact iff_of_true (by simpa [hz] using (order_positive χ H.2).1) H
    · have H : ¬(z ∈ K ∧ genuine χ z) := fun h => hz ((zeros_finite χ hK).mem_toFinset.mpr h)
      simp [hz,H]
  refine ⟨Z,mem,?_⟩
  intro z hz
  have H := (mem z).mp hz
  rw [mult,ite_eq_left ((zeros_finite χ hK).mem_toFinset.mpr H)]
  exact (order_positive χ H.2).2.symm

/-- One open neighborhood works simultaneously for every character at
every positive modulus up to R, including the regularized principals. -/
theorem bounded_strip (R : ℕ) (T : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℕ) [NeZero r], r ≤ R → ∀ (χ : DirichletCharacter ℂ r) (z : ℂ),
      |z.im| ≤ T → 1-δ ≤ z.re → ¬genuine χ z := by
  classical
  let U : Set ℂ := ⋂ (k : Fin R) (χ : DirichletCharacter ℂ (k.val+1)), (regular χ) ⁻¹' ({0} : Set ℂ)ᶜ
  have hu : IsOpen U := isOpen_iInter_of_finite (fun k => isOpen_iInter_of_finite (fun χ =>
    isClosed_singleton.isOpen_compl.preimage (differentiable_regular χ).continuous))
  let v (t : ℝ) := (1:ℂ)+(t:ℂ)*I
  let line := v '' Icc (-T) T
  have comp : IsCompact line := isCompact_Icc.image (by dsimp [v]; fun_prop)
  have sub : line ⊆ U := by
    rintro z ⟨t,_,rfl⟩
    refine mem_iInter.mpr fun k => mem_iInter.mpr fun χ => ?_
    exact regular_ne χ _ (by simp [v])
  obtain ⟨δ,hd,inside⟩ := comp.exists_cthickening_subset_open hu sub
  refine ⟨δ,hd,?_⟩
  intro r _ hr χ z ht hz
  by_cases right : 1 ≤ z.re
  · exact mt (regular_zero χ z).mpr (regular_ne χ z right)
  have imag : v z.im ∈ line := ⟨z.im,abs_le.mp ht,rfl⟩
  have E : z-v z.im=((z.re-1:ℝ):ℂ) := by apply Complex.ext <;> simp [v]
  have dist : dist z (v z.im) ≤ δ := by
    rw [dist_eq_norm,E,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    linarith
  have u := inside (Metric.mem_cthickening_of_dist_le z (v z.im) δ line imag dist)
  cases r with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    let i : Fin R := ⟨n,by omega⟩
    have H : regular χ z ≠ 0 := mem_iInter.mp (mem_iInter.mp u i) χ
    exact mt (regular_zero χ z).mpr H

/-- At fixed height, any genuine zero in the shrinking strip of the
explicit formula must have conductor larger than each fixed bound. -/
theorem conductors_escape (R : ℕ) (H T : ℝ) :
    ∀ᶠ X : ℕ in atTop, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ),
      |z.im| ≤ T → 1-H/Real.log X ≤ z.re → genuine χ z → R < r := by
  obtain ⟨δ,hδ,strip⟩ := bounded_strip R T
  have grows := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have narrow := ((tendsto_const_nhds (x := H)).div_atTop grows).eventually (gt_mem_nhds hδ)
  filter_upwards [narrow] with X hx
  intro r _ χ z ht hz zero
  by_contra! small
  change H/Real.log X < δ at hx
  exact strip r small χ z ht (by linarith) zero

/-- Apply the one-zero count to actual zeros, uniformly in all primitive
conductors. Only the stated analytic error remains an input. -/
theorem single_zero_count (H T : ℝ) :
    ∀ᶠ X : ℕ in atTop, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → ∀ z : ℂ, |z.im| ≤ T → 1-H/Real.log X ≤ z.re → genuine χ z →
      ∀ (N : ℕ) (err : ℕ → ℂ),
        (∀ m ∈ Finset.Ioc 0 N, Even m → ‖err m‖ ≤ (m:ℝ)/24) →
        ((Finset.Ioc 0 N).filter (fun m : ℕ => Even m ∧
          (SingleExceptionalZeroMajorFloor.mainTerms χ z m+err m).re < (m:ℝ)/8)).card ≤
          N/(r/(r.gcd 36)) := by
  have grows := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have thin := ((tendsto_const_nhds (x := H)).div_atTop grows).eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/128))
  filter_upwards [conductors_escape 262143 H T,thin] with X away hx
  intro r _ χ hχ z ht hz zero
  have big := away r χ z ht hz zero
  have upper : z.re < 1 := by
    by_contra! h
    exact regular_ne χ z h ((regular_zero χ z).mpr zero)
  change H/Real.log X < 1/128 at hx
  exact SingleExceptionalZeroMajorFloor.exceptional_count χ hχ z (by linarith) upper.le (by omega)

end Conjectures.Goldbach.ExceptionalZeroCatalogue

open Conjectures.Goldbach.ExceptionalZeroCatalogue in
theorem Conjectures.Goldbach.ExceptionalZeroCatalogue :
by
  classical
  let Z := fun {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (z : ℂ) =>
    (χ ≠ 1 ∨ z ≠ 1) ∧ DirichletCharacter.LFunction χ z=0
  let f := fun {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) =>
    if χ=1 then DirichletCharacter.LFunctionTrivChar₁ r else DirichletCharacter.LFunction χ
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
    (∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (K₀ : Set ℂ), IsCompact K₀ →
      ∃ M : Multiset ℂ, (∀ z : ℂ, z ∈ M ↔ z ∈ K₀ ∧ Z χ z) ∧
        ∀ z ∈ M, (M.count z : ℕ∞)=analyticOrderAt (f χ) z) ∧
    (∀ (R : ℕ) (T : ℝ), ∃ δ : ℝ, 0 < δ ∧ ∀ (r : ℕ) [NeZero r], r ≤ R →
      ∀ (χ : DirichletCharacter ℂ r) (z : ℂ), |z.im| ≤ T → 1-δ ≤ z.re → ¬Z χ z) ∧
    (∀ (R : ℕ) (H T : ℝ), ∀ᶠ X : ℕ in Filter.atTop, ∀ (r : ℕ) [NeZero r]
      (χ : DirichletCharacter ℂ r) (z : ℂ), |z.im| ≤ T → 1-H/Real.log X ≤ z.re → Z χ z → R < r) ∧
    (∀ H T : ℝ, ∀ᶠ X : ℕ in Filter.atTop, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r),
      χ.IsPrimitive → ∀ z : ℂ, |z.im| ≤ T → 1-H/Real.log X ≤ z.re → Z χ z →
      ∀ (N : ℕ) (err : ℕ → ℂ), (∀ m ∈ Finset.Ioc 0 N, Even m → ‖err m‖ ≤ (m:ℝ)/24) →
        ((Finset.Ioc 0 N).filter (fun m : ℕ => Even m ∧ (F χ z m+err m).re < (m:ℝ)/8)).card ≤
          N/(r/(r.gcd 36))) := by
  exact ⟨fun _ _ χ _ hK => zero_multiset χ hK,bounded_strip,conductors_escape,single_zero_count⟩
