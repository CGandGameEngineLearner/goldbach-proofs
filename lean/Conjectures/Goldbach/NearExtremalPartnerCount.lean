import Mathlib
import Conjectures.Goldbach.NearExtremalReducedConductor

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open Finset DirichletCharacter Real TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open TwistedGoldbachConductorValue TwistedGoldbachConductorComponents
open scoped BigOperators Classical

namespace PartnerCount

open Finset DirichletCharacter Real TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open TwistedGoldbachConductorValue TwistedGoldbachConductorComponents TwistedGoldbachExceptionalGap

theorem inverse_conductor_dvd_180 {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m)
    (above : ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ <
      Real.sqrt 2 * ‖series α β m‖) : (inversePair α β).conductor ∣ 180 := by
  classical
  by_cases ex : SharpTwistedGoldbachGap.exceptional α β m
  · have dc := ex.2.2.2.2
    exact (show (inversePair α β).conductor ∣ 36 by simpa only [inversePair,conductor_inv] using dc).trans (by decide)
  · have reduced := Conjectures.Goldbach.NearExtremalReducedConductor r s α β hα hβ m hm he ex above
    have nz : series α β m ≠ 0 := by
      intro zero
      rw [zero,norm_zero,mul_zero] at above
      exact (norm_nonneg _).not_gt above
    have support := (full_support hα hβ m hm he).mp nz
    exact support.2.2.1.trans reduced.2.1

theorem common_conductor_dvd_180 {r s T : ℕ} [NeZero r] [NeZero s] [NeZero T]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m)
    (above : ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ <
      Real.sqrt 2 * ‖series α β m‖) (hr : r ∣ T) (hs : s ∣ T) :
    ((changeLevel hr α) * (changeLevel hs β)).conductor ∣ 180 := by
  let L := Nat.lcm r s
  have ht : L ∣ T := Nat.lcm_dvd hr hs
  have moved : changeLevel ht (changeLevel (Nat.dvd_lcm_left r s) α *
      changeLevel (Nat.dvd_lcm_right r s) β) = changeLevel hr α * changeLevel hs β := by
    rw [map_mul,←changeLevel_trans,←changeLevel_trans]
  rw [←moved, conductor_changeLevel]
  simpa only [inversePair, conductor_inv] using inverse_conductor_dvd_180 hα hβ m hm he above

theorem primitive_pair_inj {T : ℕ} [NeZero T]
    {x y : Σ s : ℕ, DirichletCharacter ℂ s}
    (hx : x.2.IsPrimitive) (hy : y.2.IsPrimitive)
    (xt : x.1 ∣ T) (yt : y.1 ∣ T) (eq : changeLevel xt x.2 = changeLevel yt y.2) : x = y := by
  obtain ⟨s,β⟩ := x
  obtain ⟨t,γ⟩ := y
  have sc : s=t := by
    have v := congrArg DirichletCharacter.conductor eq
    rw [conductor_changeLevel,conductor_changeLevel] at v
    exact hx.symm.trans (v.trans hy)
  subst t
  congr 1
  exact changeLevel_injective xt eq

end PartnerCount

namespace PartnerCount

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachLocalProduct TwistedGoldbachConductorComponents DirichletCharacter Finset

theorem bounded_fiber {T : ℕ} [NeZero T] (hT : 180 ∣ T) (i : T.primeFactors)
    (hi : (i : ℕ) = 2) (A : DirichletCharacter ℂ T)
    (S : Finset (DirichletCharacter ℂ T)) (small : ∀ B ∈ S, (A * B).conductor ∣ 180)
    (same : ∀ B ∈ S, ∀ D ∈ S, component (ZMod.equivPi T (NeZero.ne T)) B i =
      component (ZMod.equivPi T (NeZero.ne T)) D i) : S.card ≤ 24 := by
  classical
  let e := ZMod.equivPi T (NeZero.ne T)
  letI : NeZero ((i:ℕ) ^ T.factorization i) := ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors i.property).ne_zero⟩
  by_cases hS : S.Nonempty
  · obtain ⟨D, hD⟩ := hS
    let g (B : S) := B.val * D⁻¹
    have cap (B : S) : (g B).conductor ∣ 45 := by
      have eg : g B = (A * B.val) * (A * D)⁻¹ := by
        dsimp only [g]
        rw [mul_inv_rev, mul_comm A B.val, mul_comm D⁻¹ A⁻¹]
        group
      have sm : (g B).conductor ∣ 180 := by
        rw [eg]
        apply (conductor_mul_dvd_lcm_conductor _ _).trans
        rw [conductor_inv]
        exact Nat.lcm_dvd (small _ B.property) (small _ hD)
      have comp : component e (g B) i = 1 := calc
        component e (g B) i =
            (component e (g B) i * component e D i) * (component e D i)⁻¹ := by group
        _ = component e B.val i * (component e D i)⁻¹ := by
          rw [← component_mul, show g B * D = B.val by dsimp [g]; group]
        _ = 1 := by
          have eqD : component e B.val i = component e D i := same _ B.property _ hD
          rw [eqD, mul_inv_cancel]
      have powone : 2 ^ (g B).conductor.factorization 2 = 1 := by
        have hp : (i:ℕ) ^ (g B).conductor.factorization i = 1 := by
          apply (prime_component_conductor (g B) i).symm.trans
          change (component e (g B) i).conductor = 1
          rw [comp, conductor_one]
        simpa only [hi] using hp
      have odd : ¬ 2 ∣ (g B).conductor := by
        intro dv
        have nz := ne_zero_of_dvd_ne_zero (by decide : (180:ℕ) ≠ 0) sm
        have powdv : (2:ℕ)^1 ∣ (g B).conductor := by simpa using dv
        have pos := (Nat.prime_two.pow_dvd_iff_le_factorization nz).mp powdv
        have high := Nat.pow_le_pow_right (by decide : 0 < 2) pos
        rw [powone] at high
        norm_num at high
      have c2 : (g B).conductor.Coprime 2 :=
        (Nat.prime_two.coprime_iff_not_dvd.mpr odd).symm
      have c4 : (g B).conductor.Coprime 4 := c2.pow_right 2
      exact c4.dvd_of_dvd_mul_left (show (g B).conductor ∣ 4 * 45 from sm)
    let encode (B : S) : DirichletCharacter ℂ 45 := changeLevel (cap B) (g B).primitiveCharacter
    have qt : 45 ∣ T := (by decide : 45 ∣ 180).trans hT
    have restore (B : S) : changeLevel qt (encode B) = g B := by
      dsimp only [encode]
      rw [← changeLevel_trans, changeLevel_primitiveCharacter]
    have inj : Function.Injective encode := by
      intro B C h
      have eq : g B = g C := (restore B).symm.trans ((congrArg (changeLevel qt) h).trans (restore C))
      exact Subtype.ext (mul_right_cancel eq)
    have cnt := Nat.card_le_card_of_injective encode inj
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 45] at cnt
    simpa [Nat.card_eq_fintype_card, show (45:ℕ).totient = 24 by decide] using cnt
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

end PartnerCount

namespace PartnerCount

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio DirichletCharacter Finset
open B13BilateralVaughanReductionProof.BombieriVinogradov.LargeSieve
open scoped BigOperators Classical

theorem jacobi_transform {q : ℕ} [NeZero q] (A B : DirichletCharacter ℂ q) (m : ZMod q) :
    J A B m = unitCharacterSum (fun u : (ZMod q)ˣ => A (m-u)) B := by
  classical
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  let e : ZMod q ≃ ZMod q :=
    ⟨fun x=>m-x, fun x=>m-x, fun x=>sub_sub_cancel m x, fun x=>sub_sub_cancel m x⟩
  have sw := Equiv.sum_comp e (fun x : ZMod q=>B x*A (m-x))
  change (∑x : ZMod q,B (m-x)*A (m-(m-x)))=_ at sw
  simp only [sub_sub_cancel] at sw
  calc
    J A B m = ∑ x : ZMod q, B (m-x)*A x := by
      unfold J;apply sum_congr rfl;intro x _;ring
    _ = ∑ x : ZMod q, B x*A (m-x) := sw
    _ = ∑ u : (ZMod q)ˣ, B (u:ZMod q)*A (m-u) := (sum_units_eq_sum_residues B _).symm
    _ = _ := by unfold unitCharacterSum;apply sum_congr rfl;intro x _;ring

theorem principal_norm_two {k : ℕ} (hk : 0<k) (m : ℕ) (he : Even m) :
    ‖J (1 : DirichletCharacter ℂ (2^k)) 1 (m:ZMod (2^k))‖ = ((2^k:ℕ).totient:ℝ) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have two : 2∣m := even_iff_two_dvd.mp he
  let Target : ℕ → Prop := fun q=>∀ [NeZero q],
    ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖=(q.totient:ℝ)
  have eq : (2:ℕ)^j.succ = 2*2^j := pow_succ' .. 
  have old : Target (2*2^j) := by
    intro inst
    have val := ordinary_prime_power (p:=2) j m
    have tot : (2*2^j:ℕ).totient=2^j := by rw [←eq,Nat.totient_prime_pow_succ Nat.prime_two];simp
    rw [tot]
    simpa only [two,ite_true,Nat.cast_ofNat,show (2:ℝ)-1=1 by norm_num,mul_one] using val
  have result : Target (2^j.succ) := by rw [eq];exact old
  exact @result inferInstance

end PartnerCount

namespace PartnerCount

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio DirichletCharacter Real Finset
open B13BilateralVaughanReductionProof.BombieriVinogradov.LargeSieve

theorem unique_local {k : ℕ} (hk : 0 < k) (A B C : DirichletCharacter ℂ (2^k))
    (m : ℕ) (he : Even m)
    (hb : ‖J (1 : DirichletCharacter ℂ (2^k)) 1 (m:ZMod (2^k))‖ < sqrt 2 * ‖J A B (m:ZMod (2^k))‖)
    (hc : ‖J (1 : DirichletCharacter ℂ (2^k)) 1 (m:ZMod (2^k))‖ < sqrt 2 * ‖J A C (m:ZMod (2^k))‖) : B=C := by
  classical
  by_contra different
  let q := 2^k
  let a (u : (ZMod q)ˣ) : ℂ := A ((m:ZMod q)-(u:ZMod q))
  let val (χ : DirichletCharacter ℂ q) := ‖unitCharacterSum a χ‖
  have pair : val B^2 + val C^2 ≤ (q.totient:ℝ)^2 := by
    calc
      _ = ∑ χ ∈ ({B,C} : Finset (DirichletCharacter ℂ q)), (val χ)^2 := by simp [different]
      _ ≤ ∑ χ : DirichletCharacter ℂ q, (val χ)^2 :=
        Finset.sum_le_univ_sum_of_nonneg (fun χ => sq_nonneg _)
      _ = (q.totient:ℝ)*∑ u : (ZMod q)ˣ, ‖a u‖^2 := by
        convert characterParseval_normSq a using 1 <;> congr 2 <;> ext u <;> simp
      _ ≤ (q.totient:ℝ)*∑ _u : (ZMod q)ˣ, (1:ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Finset.sum_le_sum
        intro u _
        simpa using pow_le_pow_left₀ (norm_nonneg (a u)) (A.norm_le_one _) 2
      _ = _ := by simp [ZMod.card_units_eq_totient,pow_two]
  rw [principal_norm_two hk m he,jacobi_transform] at hb hc
  change (q.totient:ℝ) < sqrt 2 * val B at hb
  change (q.totient:ℝ) < sqrt 2 * val C at hc
  have sq (χ : DirichletCharacter ℂ q) (lt : (q.totient:ℝ) < sqrt 2 * val χ) :
      (q.totient:ℝ)^2 < 2 * (val χ)^2 := by
    have lt2 := (sq_lt_sq₀ (Nat.cast_nonneg _) (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mpr lt
    rwa [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)] at lt2
  linarith only [sq B hb,sq C hc,pair]

end PartnerCount

namespace PartnerCount

private theorem high_component {r s T : ℕ} [NeZero r] [NeZero s] [NeZero T]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (rt : r∣T) (st : s∣T)
    (m : ℕ) (hm : 0 < m) (he : Even m) (i : T.primeFactors)
    (hi : ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ < sqrt 2 * ‖series α β m‖) :
    let e := ZMod.equivPi T (NeZero.ne T)
    let q := (i:ℕ)^T.factorization i
    letI : NeZero q := ⟨(Nat.ordProj_pos T i).ne'⟩
    ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ <
      sqrt 2 * ‖J (component e (changeLevel rt α) i) (component e (changeLevel st β) i) (m:ZMod q)‖ := by
  intro e q
  letI (k : T.primeFactors) : NeZero ((k:ℕ)^T.factorization k) := ⟨(Nat.ordProj_pos T k).ne'⟩
  letI : NeZero q := ⟨(Nat.ordProj_pos T i).ne'⟩
  have cmp := single_factor e hα hβ rt st m hm he i
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let W := ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖
  let V := ‖J (component e (changeLevel rt α) i) (component e (changeLevel st β) i) (m:ZMod q)‖
  have wp : 0 < W := norm_pos_iff.mpr (principal_ne_zero q m he)
  change ‖series α β m‖ * W ≤ O*V at cmp
  change O < sqrt 2 * ‖series α β m‖ at hi
  change W < sqrt 2 * V
  by_contra! bad
  have strict := mul_lt_mul_of_pos_right hi wp
  have a := mul_le_mul_of_nonneg_left cmp (sqrt_nonneg 2)
  have b := mul_le_mul_of_nonneg_left bad (show 0≤O from norm_nonneg _)
  linarith only [strict,a,b]

end PartnerCount

namespace PartnerCount

theorem total {r : ℕ} [NeZero r] (α : DirichletCharacter ℂ r) (ha : α.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (F : Finset (Σ s : ℕ, DirichletCharacter ℂ s))
    (good : ∀ b ∈ F, b.1 ≠ 0 ∧ b.2.IsPrimitive ∧
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
        < sqrt 2 * ‖series α b.2 m‖) : F.card ≤ 24 := by
  classical
  let P := ∏ b ∈ F,b.1
  have pp : 0<P := Finset.prod_pos (fun b hb => Nat.pos_of_ne_zero (good b hb).1)
  let T := (180*r)*P
  have tp : 0<T := Nat.mul_pos (Nat.mul_pos (by decide) (NeZero.pos r)) pp
  letI : NeZero T := ⟨tp.ne'⟩
  have big : 180∣T := (dvd_mul_right 180 r).trans (dvd_mul_right _ P)
  have rt : r∣T := (dvd_mul_left r 180).trans (dvd_mul_right _ P)
  have st (b : ↥F) : b.val.1∣T := (Finset.dvd_prod_of_mem (fun b : Σ s : ℕ, DirichletCharacter ℂ s => b.1) b.property).trans (dvd_mul_left P _)
  let f (b : ↥F) := changeLevel (st b) b.val.2
  have inj : Function.Injective f := by
    intro b c eq
    exact Subtype.ext (primitive_pair_inj (good b.val b.property).2.1 (good c.val c.property).2.1 (st b) (st c) eq)
  let S := Finset.univ.image f
  have card : S.card=F.card := by simp [S,Finset.card_image_of_injective _ inj]
  have two : 2∣T := (by decide : 2∣180).trans big
  let i : T.primeFactors := ⟨2,Nat.mem_primeFactors.mpr ⟨Nat.prime_two,two,tp.ne'⟩⟩
  have kpos : 0<T.factorization 2 := (Nat.prime_two.dvd_iff_one_le_factorization tp.ne').mp two
  rw [← card]
  apply bounded_fiber big i rfl (changeLevel rt α) S
  · intro B hb
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hb
    letI : NeZero b.val.1 := ⟨(good b.val b.property).1⟩
    exact common_conductor_dvd_180 ha (good b.val b.property).2.1 m hm he (good b.val b.property).2.2 rt (st b)
  · intro B hb D hd
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hd
    have local_high (z : ↥F) := by
      letI : NeZero z.val.1 := ⟨(good z.val z.property).1⟩
      exact high_component ha (good z.val z.property).2.1 rt (st z) m hm he i (good z.val z.property).2.2
    exact unique_local kpos _ _ _ m he (local_high b) (local_high c)

end PartnerCount

theorem Conjectures.Goldbach.NearExtremalPartnerCount :
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
  exact fun r _ α ha m hm he F H => PartnerCount.total α ha m hm he F H
