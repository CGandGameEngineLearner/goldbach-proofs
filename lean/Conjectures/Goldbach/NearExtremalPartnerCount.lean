import Mathlib
import Conjectures.Goldbach.NearExtremalReducedConductor

open DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorValue
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachConductorComponents
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SharpTwistedGoldbachGap
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.SquarefreeTwistedGoldbachDensity
open scoped BigOperators Classical

namespace Conjectures.Goldbach.NearExtremalPartnerCountProof

noncomputable def partnerProduct {r s : ℕ} (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s) : DirichletCharacter ℂ (Nat.lcm r s) :=
  changeLevel (Nat.dvd_lcm_left r s) α * changeLevel (Nat.dvd_lcm_right r s) β

private theorem card_le_of_product_conductors {r N : ℕ} [NeZero r]
    (α : DirichletCharacter ℂ r)
    (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s))
    (hprim : ∀ b ∈ F, b.2.IsPrimitive)
    (hdiv : ∀ b ∈ F, (partnerProduct α b.2).conductor ∣ N) :
    F.card ≤ Fintype.card (DirichletCharacter ℂ N) := by
  classical
  let code : {b // b ∈ F} → DirichletCharacter ℂ N := fun b =>
    changeLevel (hdiv b.1 b.2) (partnerProduct α b.1.2).primitiveCharacter
  have code_injective : Function.Injective code := by
    intro b c hbc
    let βb := b.1.2
    let βc := c.1.2
    let γb := partnerProduct α βb
    let γc := partnerProduct α βc
    let ηb := γb.primitiveCharacter
    let ηc := γc.primitiveCharacter
    have hβb : βb.IsPrimitive := hprim b.1 b.2
    have hβc : βc.IsPrimitive := hprim c.1 c.2
    have hηbPrim : ηb.IsPrimitive := γb.primitiveCharacter_isPrimitive
    have hηcPrim : ηc.IsPrimitive := γc.primitiveCharacter_isPrimitive
    have hηb : ηb.conductor = γb.conductor := hηbPrim
    have hηc : ηc.conductor = γc.conductor := hηcPrim
    have hcond : γb.conductor = γc.conductor := by
      have h := congrArg DirichletCharacter.conductor hbc
      simpa only [code, conductor_changeLevel, hηb, hηc] using h
    have hη : ηb = ηc := by
      apply changeLevel_injective (hdiv b.1 b.2)
      simpa only [code, hcond] using hbc
    let Lb := Nat.lcm r b.1.1
    let Lc := Nat.lcm r c.1.1
    let P := Nat.lcm Lb Lc
    have hLbP : Lb ∣ P := Nat.dvd_lcm_left Lb Lc
    have hLcP : Lc ∣ P := Nat.dvd_lcm_right Lb Lc
    have hrP : r ∣ P := (Nat.dvd_lcm_left r b.1.1).trans hLbP
    have hsP : b.1.1 ∣ P := (Nat.dvd_lcm_right r b.1.1).trans hLbP
    have htP : c.1.1 ∣ P := (Nat.dvd_lcm_right r c.1.1).trans hLcP
    have hdP : γb.conductor ∣ P := γb.conductor_dvd_level.trans hLbP
    have hLiftB : changeLevel hdP ηb = changeLevel hLbP γb := by
      calc
        _ = changeLevel (γb.conductor_dvd_level.trans hLbP) ηb := by
          congr 1
        _ = changeLevel hLbP (changeLevel γb.conductor_dvd_level ηb) := by
          rw [← changeLevel_trans]
        _ = _ := by rw [changeLevel_primitiveCharacter]
    have hLiftC : changeLevel hdP ηc = changeLevel hLcP γc := by
      have hdP' : γc.conductor ∣ P := γc.conductor_dvd_level.trans hLcP
      have hLiftC' : changeLevel hdP' ηc = changeLevel hLcP γc := by
        calc
          _ = changeLevel (γc.conductor_dvd_level.trans hLcP) ηc := by
            congr 1
          _ = changeLevel hLcP (changeLevel γc.conductor_dvd_level ηc) := by
            rw [← changeLevel_trans]
          _ = _ := by rw [changeLevel_primitiveCharacter]
      simpa only [hcond] using hLiftC'
    have hγP : changeLevel hLbP γb = changeLevel hLcP γc := by
      rw [← hLiftB, ← hLiftC, hη]
    have hproductP :
        changeLevel hrP α * changeLevel hsP βb =
          changeLevel hrP α * changeLevel htP βc := by
      simpa only [partnerProduct, map_mul, ← changeLevel_trans] using hγP
    have hβP : changeLevel hsP βb = changeLevel htP βc := by
      have h := congrArg (fun χ : DirichletCharacter ℂ P => (changeLevel hrP α)⁻¹ * χ)
        hproductP
      group at h
      exact h
    have hsEq : b.1.1 = c.1.1 := by
      have h := congrArg DirichletCharacter.conductor hβP
      simpa only [conductor_changeLevel, show βb.conductor = b.1.1 from hβb,
        show βc.conductor = c.1.1 from hβc] using h
    have hβEq : βb = βc := by
      apply changeLevel_injective hsP
      simpa only [hsEq] using hβP
    apply Subtype.ext
    apply Sigma.ext hsEq
    exact hβEq
  have hcard := Fintype.card_le_of_injective code code_injective
  simpa only [Fintype.card_coe] using hcard

private def prodBoolRingEquiv (R S : Type*) [Semiring R] [Semiring S] :
    (R × S) ≃+* (∀ b : Bool, if b then R else S) where
  toFun x b := by
    cases b
    · exact x.2
    · exact x.1
  invFun f := (f true, f false)
  left_inv x := by cases x; rfl
  right_inv f := by
    funext b
    cases b <;> rfl
  map_mul' x y := by
    funext b
    cases b <;> rfl
  map_add' x y := by
    funext b
    cases b <;> rfl
  map_zero' := by
    funext b
    cases b <;> rfl
  map_one' := by
    funext b
    cases b <;> rfl

private theorem card_dirichletCharacter (n : ℕ) :
    Fintype.card (DirichletCharacter ℂ n) = n.totient := by
  rw [← Nat.card_eq_fintype_card]
  exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ n

private theorem local_five_conditions {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ι → ℕ} [∀ i, NeZero (q i)] {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀ i, ZMod (q i))
    {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (he : Even m)
    (hnot5 : ¬5 ∣ m) (i : ι) (hi : q i = 5)
    (hhigh : ‖TwistedGoldbachLocalProduct.series
        (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ <
      Real.sqrt 2 * ‖TwistedGoldbachLocalProduct.series α β m‖) :
    let A := component e (changeLevel hr α) i
    let B := component e (changeLevel hs β) i
    (A = 1 → B = 1) ∧ (A ≠ 1 → B ≠ 1 ∧ A * B ≠ 1) := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  let A := component e (changeLevel hr α) i
  let B := component e (changeLevel hs β) i
  have hm0 : (m : ZMod 5) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m 5).mp hnot5
  have hOrd : ‖J (1 : DirichletCharacter ℂ 5) 1 (m : ZMod 5)‖ = 3 := by
    change ‖SquarefreeTwistedGoldbachDensity.localSum
      (1 : DirichletCharacter ℂ 5) 1 (m : ZMod 5)‖ = 3
    rw [SquarefreeTwistedGoldbachDensity.local_norm]
    simp [hm0]
  have hsingle :
      ‖TwistedGoldbachLocalProduct.series α β m‖ * 3 ≤
        ‖TwistedGoldbachLocalProduct.series
          (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
          ‖J A B (m : ZMod 5)‖ := by
    have h := single_factor e hα hβ hr hs m hm he i
    simpa [hi, A, B, hOrd] using h
  have hSpos : 0 < ‖TwistedGoldbachLocalProduct.series α β m‖ := by
    apply norm_pos_iff.mpr
    intro hz
    rw [hz, norm_zero, mul_zero] at hhigh
    exact (not_lt_of_ge (norm_nonneg _)) hhigh
  have hsmall : ‖J A B (m : ZMod 5)‖ = 1 → False := by
    intro hJ
    have hbound : 3 * ‖TwistedGoldbachLocalProduct.series α β m‖ ≤
        ‖TwistedGoldbachLocalProduct.series
          (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
      rw [hJ, norm_one] at hsingle
      nlinarith [hsingle]
    have hsqrt : Real.sqrt 2 < 3 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hgap : 0 < (3 - Real.sqrt 2) *
        ‖TwistedGoldbachLocalProduct.series α β m‖ :=
      mul_pos (by linarith) hSpos
    nlinarith [hbound, hhigh, hgap]
  have hAone (hA : A = 1) (hB : B ≠ 1) : ‖J A B (m : ZMod 5)‖ = 1 := by
    change ‖SquarefreeTwistedGoldbachDensity.localSum A B (m : ZMod 5)‖ = 1
    rw [SquarefreeTwistedGoldbachDensity.local_norm]
    simp [hm0, hA, hB]
  have hBone (hA : A ≠ 1) (hB : B = 1) : ‖J A B (m : ZMod 5)‖ = 1 := by
    change ‖SquarefreeTwistedGoldbachDensity.localSum A B (m : ZMod 5)‖ = 1
    rw [SquarefreeTwistedGoldbachDensity.local_norm]
    simp [hm0, hA, hB]
  have hProdone (hA : A ≠ 1) (hAB : A * B = 1) :
      ‖J A B (m : ZMod 5)‖ = 1 := by
    change ‖SquarefreeTwistedGoldbachDensity.localSum A B (m : ZMod 5)‖ = 1
    rw [SquarefreeTwistedGoldbachDensity.local_norm]
    simp [hm0, hA, hAB]
  constructor
  · intro hA hB
    exact False.elim (hsmall (hAone hA hB))
  · intro hA
    constructor
    · intro hB
      exact False.elim (hsmall (hBone hA hB))
    · intro hAB
      exact False.elim (hsmall (hProdone hA hAB))

private theorem product_conductor_div180 {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m)
    (he : Even m)
    (hhigh : ‖TwistedGoldbachLocalProduct.series
        (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ <
      Real.sqrt 2 * ‖TwistedGoldbachLocalProduct.series α β m‖) :
    (partnerProduct α β).conductor ∣ 180 := by
  classical
  by_cases hX : SharpTwistedGoldbachGap.exceptional α β m
  · have h36 : (partnerProduct α β).conductor ∣ 36 := by
      simpa only [SharpTwistedGoldbachGap.exceptional, partnerProduct] using
        hX.2.2.2.2
    exact h36.trans (by norm_num : 36 ∣ 180)
  · have hs : TwistedGoldbachLocalProduct.series α β m ≠ 0 := by
      intro hz
      rw [hz, norm_zero, mul_zero] at hhigh
      exact (not_lt_of_ge (norm_nonneg _)) hhigh
    let L := Nat.lcm r s
    let j := L / m.gcd L
    have hsupport :=
      (TwistedGoldbachConductorValue.full_support hα hβ m hm he).mp hs
    have hdj : (partnerProduct α β).conductor ∣ j := by
      simpa only [j, L, partnerProduct, inversePair, conductor_inv] using
        hsupport.2.2.1
    have hloc := Conjectures.Goldbach.NearExtremalReducedConductor
      r s α β hα hβ m hm he hX hhigh
    exact hdj.trans hloc.2.1

private theorem char5_ext_of_apply_two {χ ψ : DirichletCharacter ℂ 5}
    (hχ : χ (2 : ZMod 5) = ψ (2 : ZMod 5)) : χ = ψ := by
  have h3 : (3 : ZMod 5) = (2 : ZMod 5)^3 := by norm_num
  have h4 : (4 : ZMod 5) = (2 : ZMod 5)^2 := by norm_num
  apply MulChar.ext
  intro x
  fin_cases x <;> simp_all [map_pow, h3, h4]

private theorem char5_eq_one_of_apply_two {χ : DirichletCharacter ℂ 5}
    (hχ : χ (2 : ZMod 5) = 1) : χ = 1 := by
  exact char5_ext_of_apply_two (by simpa using hχ)

private theorem complex_fourth_root {z : ℂ} (hz : z ^ 4 = 1) :
    z = 1 ∨ z = -1 ∨ z = Complex.I ∨ z = -Complex.I := by
  have hf : ((z - 1) * (z + 1)) * ((z - Complex.I) * (z + Complex.I)) = 0 := by
    calc
      _ = z ^ 4 - 1 := by rw [Complex.I_sq]; ring
      _ = 0 := sub_eq_zero.mpr hz
  rcases mul_eq_zero.mp hf with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left h))
  · rcases mul_eq_zero.mp h with h | h
    · exact Or.inr (Or.inr (Or.inl (sub_eq_zero.mp h)))
    · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h)))

private theorem fourth_root_shift {a z : ℂ} (ha : a ^ 4 = 1) (ha1 : a ≠ 1)
    (hz : z ^ 4 = 1) (hz1 : z ≠ 1) (hza : z ≠ a) :
    z * (if a ^ 2 = 1 then Complex.I else -1) = 1 ∨
      z * (if a ^ 2 = 1 then Complex.I else -1) = a := by
  rcases complex_fourth_root ha with h | h | h | h
  · exact False.elim (ha1 h)
  · subst a
    have hsq : (-1 : ℂ)^2 = 1 := by norm_num
    simp only [hsq, if_pos]
    rcases complex_fourth_root hz with h | h | h | h
    · exact False.elim (hz1 h)
    · exact False.elim (hza h)
    · exact Or.inr (by norm_num)
    · exact Or.inl (by norm_num)
  · subst a
    have hsq : Complex.I^2 ≠ 1 := by norm_num
    simp only [hsq, if_false]
    rcases complex_fourth_root hz with h | h | h | h
    · exact False.elim (hz1 h)
    · exact Or.inl (by norm_num)
    · exact False.elim (hza h)
    · exact Or.inr (by norm_num)
  · subst a
    have hsq : (-Complex.I)^2 ≠ 1 := by norm_num
    simp only [hsq, if_false]
    rcases complex_fourth_root hz with h | h | h | h
    · exact False.elim (hz1 h)
    · exact Or.inl (by norm_num)
    · exact Or.inr (by norm_num)
    · exact False.elim (hza h)

private theorem good_eval_card_le_24 {a : ℂ} (ha : a ^ 4 = 1) (ha1 : a ≠ 1) :
    (Finset.univ.filter (fun χ : DirichletCharacter ℂ 180 =>
      χ (37 : ZMod 180) ≠ 1 ∧ χ (37 : ZMod 180) ≠ a)).card ≤ 24 := by
  classical
  let q5 : DirichletCharacter ℂ 5 := quartic
  let q180 : DirichletCharacter ℂ 180 :=
    changeLevel (by norm_num : 5 ∣ 180) q5
  let ζ : DirichletCharacter ℂ 180 := if a ^ 2 = 1 then q180 else q180 ^ 2
  have hq5 : q5 (2 : ZMod 5) = Complex.I := rfl
  have hcast : (ZMod.castHom (by norm_num : 5 ∣ 180) (37 : ZMod 180)) =
      (2 : ZMod 5) := by norm_num
  have hq180 : q180 (37 : ZMod 180) = Complex.I := by
    change q5 (ZMod.castHom (by norm_num : 5 ∣ 180) (37 : ZMod 180)) = Complex.I
    rw [hcast, hq5]
  have hζ : ζ (37 : ZMod 180) = if a ^ 2 = 1 then Complex.I else -1 := by
    simp [ζ, hq180]
    split_ifs <;> norm_num
  let G : Finset (DirichletCharacter ℂ 180) := Finset.univ.filter (fun χ =>
    χ (37 : ZMod 180) ≠ 1 ∧ χ (37 : ZMod 180) ≠ a)
  let B : Finset (DirichletCharacter ℂ 180) := Finset.univ.filter (fun χ =>
    χ (37 : ZMod 180) = 1 ∨ χ (37 : ZMod 180) = a)
  have hmap : ∀ χ ∈ G, χ * ζ ∈ B := by
    intro χ hχ
    rcases Finset.mem_filter.mp hχ with ⟨_, hχ⟩
    have hroot : (χ (37 : ZMod 180)) ^ 4 = 1 := by
      calc
        _ = χ ((37 : ZMod 180)^4) := by rw [map_pow]
        _ = χ 1 := by norm_num
        _ = 1 := map_one _
    have hshift := fourth_root_shift ha ha1 hroot hχ.1 hχ.2
    have heval : (χ * ζ) (37 : ZMod 180) = χ (37 : ZMod 180) *
        (if a ^ 2 = 1 then Complex.I else -1) := by
      simp [map_mul, hζ]
    rcases hshift with h | h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (by rw [heval]; exact h)⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (by rw [heval]; exact h)⟩
  have hcardGB : G.card ≤ B.card := by
    apply Finset.card_le_card_of_injOn (fun χ => χ * ζ)
    · exact hmap
    · intro χ hχ ψ hψ heq
      exact mul_right_cancel heq
  have hdisj : Disjoint G B := by
    apply Finset.disjoint_left.mpr
    intro χ hχ hb
    rcases Finset.mem_filter.mp hχ with ⟨_, hgood⟩
    rcases (Finset.mem_filter.mp hb).2 with hone | ha'
    · exact hgood.1 hone
    · exact hgood.2 ha'
  have hunion : G ∪ B = Finset.univ := by
    ext χ
    simp only [G, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hone : χ (37 : ZMod 180) = 1 <;>
      by_cases htwo : χ (37 : ZMod 180) = a <;> simp [hone, htwo]
  have hsum : G.card + B.card = Fintype.card (DirichletCharacter ℂ 180) := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    simp
  have hcard : Fintype.card (DirichletCharacter ℂ 180) = 48 := by
    rw [card_dirichletCharacter]
    norm_num
  omega

end Conjectures.Goldbach.NearExtremalPartnerCountProof

open Conjectures.Goldbach.NearExtremalPartnerCountProof

theorem Conjectures.Goldbach.NearExtremalPartnerCount:
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
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  exact ∀ (r : ℕ) [NeZero r] (α : DirichletCharacter ℂ r), α.IsPrimitive →
    ∀ m : ℕ, 0 < m → Even m →
    ∀ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
    (∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive ∧ ‖O m‖ < Real.sqrt 2 * ‖S α b.2 m‖) →
    F.card ≤ 24 := by
  classical
  intro r _ α hα m hm he F hF
  have hprim (b : Σ s : ℕ, DirichletCharacter ℂ s) (hb : b ∈ F) :
      b.2.IsPrimitive := (hF b hb).2.1
  have hhigh (b : Σ s : ℕ, DirichletCharacter ℂ s) (hb : b ∈ F) :=
    (hF b hb).2.2
  have hdiv180 (b : Σ s : ℕ, DirichletCharacter ℂ s) (hb : b ∈ F) :
      (partnerProduct α b.2).conductor ∣ 180 := by
    letI : NeZero b.1 := ⟨(hF b hb).1⟩
    exact product_conductor_div180 hα (hprim b hb) m hm he (hhigh b hb)
  by_cases hm5 : 5 ∣ m
  · have hXall : ∀ b ∈ F, SharpTwistedGoldbachGap.exceptional α b.2 m := by
      intro b hb
      letI : NeZero b.1 := ⟨(hF b hb).1⟩
      by_contra hX
      have hloc := Conjectures.Goldbach.NearExtremalReducedConductor
        r b.1 α b.2 hα (hprim b hb) m hm he hX (hhigh b hb)
      exact hloc.2.2 hm5
    have hdiv36 : ∀ b ∈ F, (partnerProduct α b.2).conductor ∣ 36 := by
      intro b hb
      simpa only [SharpTwistedGoldbachGap.exceptional, partnerProduct] using
        (hXall b hb).2.2.2.2
    have hcard := card_le_of_product_conductors α F hprim hdiv36
    have hcard36 : Fintype.card (DirichletCharacter ℂ 36) = 12 := by
      rw [card_dirichletCharacter]
      norm_num
    omega
  · let k : ℕ := 36 * m
    let M : ℕ := 5 * k
    have hM_eq : M = 180 * m := by dsimp [M, k]; ring
    have h36M : 36 * m ∣ M := by
      refine ⟨5, ?_⟩
      dsimp [M, k]
      ring
    have hcop : Nat.Coprime 5 k := by
      have hnot : ¬5 ∣ k := by
        intro hk
        have hsplit := (show Nat.Prime 5 by decide).dvd_mul.mp
          (by simpa [k] using hk)
        rcases hsplit with h36 | hmdiv
        · norm_num at h36
        · exact hm5 hmdiv
      exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr hnot
    by_cases hFempty : F = ∅
    · simp [hFempty]
    · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
      obtain ⟨b0, hb0⟩ := hFne
      have lcm_div_M (s : ℕ)
          (hJ : (Nat.lcm r s) / m.gcd (Nat.lcm r s) ∣ 180) :
          Nat.lcm r s ∣ M := by
        let L := Nat.lcm r s
        let g := m.gcd L
        let j := L / g
        have hg : g ∣ m := Nat.gcd_dvd_left m L
        have hgL : g ∣ L := Nat.gcd_dvd_right m L
        have hLg : j * g = L := by
          dsimp [j, g]
          exact Nat.div_mul_cancel hgL
        have hprod : j * g ∣ 180 * m := Nat.mul_dvd_mul hJ hg
        have hLdiv : L ∣ 180 * m := by simpa [hLg] using hprod
        have hM : M = 180 * m := hM_eq
        simpa [L, hM] using hLdiv
      have hrM : r ∣ M := by
        letI : NeZero b0.1 := ⟨(hF b0 hb0).1⟩
        by_cases hx : SharpTwistedGoldbachGap.exceptional α b0.2 m
        · have hg : m.gcd r ∣ m := Nat.gcd_dvd_left m r
          have hmul : (r / m.gcd r) * m.gcd r ∣ 36 * m :=
            Nat.mul_dvd_mul hx.1 hg
          have hcancel : (r / m.gcd r) * m.gcd r = r :=
            Nat.div_mul_cancel (Nat.gcd_dvd_right m r)
          have hr36 : r ∣ 36 * m := by simpa [hcancel] using hmul
          exact hr36.trans h36M
        · have hloc := Conjectures.Goldbach.NearExtremalReducedConductor
            r b0.1 α b0.2 hα (hprim b0 hb0) m hm he hx (hhigh b0 hb0)
          exact (Nat.dvd_lcm_left r b0.1).trans (lcm_div_M b0.1 hloc.2.1)
      have h180M : 180 ∣ M := by
        rw [hM_eq]
        exact Nat.dvd_mul_right 180 m
      have h36k : 36 ∣ k := by dsimp [k]; exact Nat.dvd_mul_right 36 m
      have hkM : k ∣ M := by dsimp [M]; exact Nat.dvd_mul_left k 5
      have h36M' : 36 ∣ M := Nat.dvd_trans h36k hkM
      have h5M : 5 ∣ M := by dsimp [M]; exact Nat.dvd_mul_right 5 k
      letI : NeZero M := ⟨by dsimp [M, k]; positivity⟩
      let q : Bool → ℕ := fun i => if i then 5 else k
      letI : ∀ i : Bool, NeZero (q i) := by
        intro i
        cases i with
        | false => exact ⟨by dsimp [q, k]; positivity⟩
        | true => exact ⟨by simp [q]⟩
      let eCRT : ZMod (5 * k) ≃+* ZMod 5 × ZMod k := ZMod.chineseRemainder hcop
      let ePi := prodBoolRingEquiv (ZMod 5) (ZMod k)
      let e : ZMod M ≃+* (∀ i : Bool, ZMod (q i)) := by
        dsimp [M, q]
        exact eCRT.trans ePi
      have hqdiv : ∀ i : Bool, q i ∣ M := by
        intro i
        cases i with
        | false => change k ∣ 5 * k; exact ⟨5, by ring⟩
        | true => change 5 ∣ 5 * k; exact ⟨k, by ring⟩
      have hqcop : Pairwise (fun i j : Bool => Nat.Coprime (q i) (q j)) := by
        intro i j hij
        cases i <;> cases j
        · exact False.elim (hij rfl)
        · simpa [q] using hcop.symm
        · simpa [q] using hcop
        · exact False.elim (hij rfl)
      let e180 : ZMod 180 ≃+* ZMod 5 × ZMod 36 :=
        ZMod.chineseRemainder (by norm_num : Nat.Coprime 5 36)
      let xM : ZMod M := eCRT.symm (2, 1)
      have hcrt : eCRT xM = (2, 1) := eCRT.apply_symm_apply (2, 1)
      have h5z : ZMod.castHom h5M xM = (2 : ZMod 5) := by
        simpa [eCRT, ZMod.chineseRemainder, xM] using congrArg Prod.fst hcrt
      have hkz : ZMod.castHom hkM xM = (1 : ZMod k) := by
        simpa [eCRT, ZMod.chineseRemainder, xM] using congrArg Prod.snd hcrt
      have h36z : ZMod.castHom h36M' xM = (1 : ZMod 36) := by
        have hcomp := ZMod.castHom_comp h36k hkM
        have hproof : h36k.trans hkM = h36M' := Subsingleton.elim _ _
        rw [hproof] at hcomp
        simpa [Function.comp_apply, hkz] using (congrFun hcomp xM).symm
      have hfirst :
          ZMod.castHom (by norm_num : 5 ∣ 180) (ZMod.castHom h180M xM) =
            (2 : ZMod 5) := by
        have hcomp := ZMod.castHom_comp (by norm_num : 5 ∣ 180) h180M
        have hproof : (show 5 ∣ 180 from by norm_num).trans h180M = h5M :=
          Subsingleton.elim _ _
        rw [hproof] at hcomp
        simpa [Function.comp_apply, h5z] using congrFun hcomp xM
      have hsecond :
          ZMod.castHom (by norm_num : 36 ∣ 180) (ZMod.castHom h180M xM) =
            (1 : ZMod 36) := by
        have hcomp := ZMod.castHom_comp (by norm_num : 36 ∣ 180) h180M
        have hproof : (show 36 ∣ 180 from by norm_num).trans h180M = h36M' :=
          Subsingleton.elim _ _
        rw [hproof] at hcomp
        simpa [Function.comp_apply, h36z] using congrFun hcomp xM
      have hcoords : e180 (ZMod.castHom h180M xM) = (2, 1) := by
        apply Prod.ext
        · simpa [e180, ZMod.chineseRemainder] using hfirst
        · simpa [e180, ZMod.chineseRemainder] using hsecond
      have h37coords : e180 (37 : ZMod 180) = (2, 1) := by
        apply Prod.ext <;> norm_num [e180, ZMod.chineseRemainder]
      have hcast180 : ZMod.castHom h180M xM = (37 : ZMod 180) :=
        e180.injective (hcoords.trans h37coords.symm)
      let alphaM : DirichletCharacter ℂ M := changeLevel hrM α
      let A : DirichletCharacter ℂ 5 := component e alphaM true
      have hAcond : A.conductor = Nat.gcd 5 r := by
        have h := component_conductor e hqdiv hqcop alphaM true
        simpa [A, alphaM, q, conductor_changeLevel,
          show α.conductor = r from hα] using h
      by_cases hA : A = 1
      · have hdiv36 : ∀ b ∈ F, (partnerProduct α b.2).conductor ∣ 36 := by
          intro b hb
          letI : NeZero b.1 := ⟨(hF b hb).1⟩
          by_cases hx : SharpTwistedGoldbachGap.exceptional α b.2 m
          · simpa only [SharpTwistedGoldbachGap.exceptional, partnerProduct] using
              hx.2.2.2.2
          · have hLM := lcm_div_M_of_nonexception b hb hx
            have hrMb : r ∣ M := (Nat.dvd_lcm_left r b.1).trans hLM
            have hsMb : b.1 ∣ M := (Nat.dvd_lcm_right r b.1).trans hLM
            let betaM : DirichletCharacter ℂ M := changeLevel hsMb b.2
            let B : DirichletCharacter ℂ 5 := component e betaM true
            have hlocal := local_five_conditions e hα (hprim b hb) hrMb hsMb m hm he
              hm5 true rfl (hhigh b hb)
            have hB : B = 1 := by
              have h := hlocal.1
              simpa [A, B, alphaM, betaM] using h hA
            let gammaM : DirichletCharacter ℂ M :=
              changeLevel hLM (partnerProduct α b.2)
            have hgammaM : gammaM = alphaM * betaM := by
              simp [gammaM, alphaM, betaM, partnerProduct, changeLevel_trans]
            have hcomp : component e gammaM true = A * B := by
              rw [hgammaM]
              exact component_mul e alphaM betaM true
            have hcompOne : component e gammaM true = 1 := by
              rw [hcomp, hA, hB]
              simp
            have hcompCond : (component e gammaM true).conductor =
                Nat.gcd 5 (partnerProduct α b.2).conductor := by
              calc
                _ = Nat.gcd (q true) gammaM.conductor :=
                  component_conductor e hqdiv hqcop gammaM true
                _ = Nat.gcd 5 (partnerProduct α b.2).conductor := by
                  simp [q, gammaM, conductor_changeLevel]
            have hgcd : Nat.gcd 5 (partnerProduct α b.2).conductor = 1 := by
              have h := congrArg DirichletCharacter.conductor hcompOne
              simpa [hcompCond] using h
            have hcopc : Nat.Coprime 5 (partnerProduct α b.2).conductor := by
              rw [Nat.coprime_iff_gcd_eq_one]
              exact hgcd
            have hdiv180b := hdiv180 b hb
            have hdiv536 : (partnerProduct α b.2).conductor ∣ 5 * 36 := by
              simpa only [show (180 : ℕ) = 5 * 36 by norm_num] using hdiv180b
            exact hcopc.symm.dvd_of_dvd_mul_left hdiv536
        have hcard := card_le_of_product_conductors α F hprim hdiv36
        have hcard36 : Fintype.card (DirichletCharacter ℂ 36) = 12 := by
          rw [card_dirichletCharacter]
          norm_num
        omega
      · have h5r : 5 ∣ r := by
          by_contra hnot
          have hcopr : Nat.Coprime 5 r :=
            (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr hnot
          have hgcd : Nat.gcd 5 r = 1 := by
            rw [Nat.coprime_iff_gcd_eq_one] at hcopr
            exact hcopr
          have hcond : A.conductor = 1 := by simpa [hAcond, hgcd]
          exact hA ((eq_one_iff_conductor_eq_one (χ := A)).mpr hcond)
        have hXall : ∀ b ∈ F, ¬SharpTwistedGoldbachGap.exceptional α b.2 m := by
          intro b hb hx
          letI : NeZero b.1 := ⟨(hF b hb).1⟩
          have hgnot : ¬5 ∣ m.gcd r := by
            intro hg
            exact hm5 (hg.trans (Nat.gcd_dvd_left m r))
          have hmul : 5 ∣ (r / m.gcd r) * m.gcd r := by
            simpa [Nat.div_mul_cancel (Nat.gcd_dvd_right m r)] using h5r
          rcases (show Nat.Prime 5 by decide).dvd_mul.mp hmul with hq | hg
          · exact (by norm_num : ¬5 ∣ 36) (Nat.dvd_trans hq hx.1)
          · exact hgnot hg
        let code : {b // b ∈ F} → DirichletCharacter ℂ 180 := fun b =>
          changeLevel (hdiv180 b.1 b.2)
            (partnerProduct α b.1.2).primitiveCharacter
        have hcodeInj : Function.Injective code :=
          partnerCodeInjective α F hprim hdiv180
        have hgood (b : Σ s : ℕ, DirichletCharacter ℂ s) (hb : b ∈ F) :
            code ⟨b, hb⟩ (37 : ZMod 180) ≠ 1 ∧
              code ⟨b, hb⟩ (37 : ZMod 180) ≠ A (2 : ZMod 5) := by
          letI : NeZero b.1 := ⟨(hF b hb).1⟩
          have hX := hXall b hb
          have hLM := lcm_div_M_of_nonexception b hb hX
          have hrMb : r ∣ M := (Nat.dvd_lcm_left r b.1).trans hLM
          have hsMb : b.1 ∣ M := (Nat.dvd_lcm_right r b.1).trans hLM
          let betaM : DirichletCharacter ℂ M := changeLevel hsMb b.2
          let B : DirichletCharacter ℂ 5 := component e betaM true
          have hlocal := local_five_conditions e hα (hprim b hb) hrMb hsMb m hm he
            hm5 true rfl (hhigh b hb)
          have hBne : B ≠ 1 := by simpa [A, B, alphaM, betaM] using (hlocal.2 hA).1
          have hABne : A * B ≠ 1 := by simpa [A, B, alphaM, betaM] using (hlocal.2 hA).2
          let gammaL := partnerProduct α b.2
          let eta := gammaL.primitiveCharacter
          let gammaM : DirichletCharacter ℂ M := changeLevel hLM gammaL
          have hgammaM : gammaM = alphaM * betaM := by
            simp [gammaM, alphaM, betaM, partnerProduct, changeLevel_trans]
          have hcodeM :
              changeLevel h180M (code ⟨b, hb⟩) = alphaM * betaM := by
            calc
              _ = changeLevel ((hdiv180 b hb).trans h180M) eta := by
                rw [changeLevel_trans]
              _ = changeLevel (gammaL.conductor_dvd_level.trans hLM) eta := by
                congr 1
              _ = changeLevel hLM gammaL := by
                rw [← changeLevel_trans, changeLevel_primitiveCharacter]
              _ = _ := hgammaM
          have hcodeEval : code ⟨b, hb⟩ (37 : ZMod 180) =
              (A * B) (2 : ZMod 5) := by
            have hEval := congrArg (fun χ : DirichletCharacter ℂ M => χ xM) hcodeM
            have hAeval : A (2 : ZMod 5) = alphaM xM := by rfl
            have hBeval : B (2 : ZMod 5) = betaM xM := by rfl
            calc
              _ = code ⟨b, hb⟩ (ZMod.castHom h180M xM) := by rw [hcast180]
              _ = (changeLevel h180M (code ⟨b, hb⟩)) xM := by rfl
              _ = (alphaM * betaM) xM := hEval
              _ = (A * B) (2 : ZMod 5) := by
                rw [map_mul, hAeval, hBeval]
          have hnot1 : code ⟨b, hb⟩ (37 : ZMod 180) ≠ 1 := by
            intro h
            have hval : (A * B) (2 : ZMod 5) = 1 := by
              simpa [hcodeEval] using h
            exact hABne (char5_eq_one_of_apply_two hval)
          have hnotA : code ⟨b, hb⟩ (37 : ZMod 180) ≠ A (2 : ZMod 5) := by
            intro h
            have hval : (A * B) (2 : ZMod 5) = A (2 : ZMod 5) := by
              simpa [hcodeEval] using h
            have hchars : A * B = A := char5_ext_of_apply_two hval
            have hB : B = 1 := mul_left_cancel (by simpa using hchars)
            exact hBne hB
          exact ⟨hnot1, hnotA⟩
        let G : Finset (DirichletCharacter ℂ 180) := Finset.univ.filter
          (fun χ => χ (37 : ZMod 180) ≠ 1 ∧ χ (37 : ZMod 180) ≠ A (2 : ZMod 5))
        have hcodeMem (b : {b // b ∈ F}) : code b ∈ G := by
          simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hgood b.1 b.2
        let codeGood : {b // b ∈ F} → {χ : DirichletCharacter ℂ 180 // χ ∈ G} :=
          fun b => ⟨code b, hcodeMem b⟩
        have hcodeGoodInj : Function.Injective codeGood := by
          intro b c h
          apply Subtype.ext
          exact hcodeInj (congrArg Subtype.val h)
        have hcardF : F.card ≤ G.card := by
          have h := Fintype.card_le_of_injective codeGood hcodeGoodInj
          simpa only [Fintype.card_coe] using h
        have hA4 : (A (2 : ZMod 5)) ^ 4 = 1 := by
          calc
            _ = A ((2 : ZMod 5)^4) := by rw [map_pow]
            _ = A 1 := by norm_num
            _ = 1 := map_one _
        have hA1 : A (2 : ZMod 5) ≠ 1 := by
          intro h
          exact hA (char5_eq_one_of_apply_two h)
        have hG24 := good_eval_card_le_24 hA4 hA1
        exact hcardF.trans hG24
