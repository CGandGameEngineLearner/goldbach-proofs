import Conjectures.Goldbach.TwistedGoldbachConductorValue

/-! Recover the conductor of every actual CRT component directly from
the original global conductor. This lets a bound obtained from one
prime-power factor control the full singular series independently of all
complementary factors. -/

namespace Conjectures.Goldbach.TwistedGoldbachConductorComponents

open Finset DirichletCharacter TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open scoped BigOperators Classical

theorem conductor_mul_coprime {L : ℕ} [NeZero L] (A B : DirichletCharacter ℂ L)
    (h : A.conductor.Coprime B.conductor) : (A*B).conductor=A.conductor*B.conductor := by
  let Z := A*B
  have Aeq : Z*B⁻¹=A := by change A*B*B⁻¹=A; group
  have Beq : Z*A⁻¹=B := by change A*B*A⁻¹=B; rw [mul_comm A B]; group
  have dA := conductor_mul_dvd_lcm_conductor Z B⁻¹
  have dB := conductor_mul_dvd_lcm_conductor Z A⁻¹
  rw [Aeq,conductor_inv] at dA
  rw [Beq,conductor_inv] at dB
  have one := h.dvd_of_dvd_mul_right (dA.trans (Nat.lcm_dvd_mul ..))
  have two := h.symm.dvd_of_dvd_mul_right (dB.trans (Nat.lcm_dvd_mul ..))
  exact Nat.dvd_antisymm ((conductor_mul_dvd_lcm_conductor A B).trans (Nat.lcm_dvd_mul ..))
    (h.mul_dvd_of_dvd_of_dvd one two)

private theorem conductor_prod {ι : Type*} [DecidableEq ι] {L : ℕ} [NeZero L]
    (f : ι → DirichletCharacter ℂ L) (S : Finset ι)
    (hc : ∀ i ∈ S, ∀ k ∈ S, i ≠ k → (f i).conductor.Coprime (f k).conductor) :
    (∏ i ∈ S, f i).conductor=∏ i ∈ S, (f i).conductor := by
  induction S using Finset.induction_on with
  | empty => simp [conductor_one]
  | @insert i S hi ih =>
    have hc' : ∀ j ∈ S, ∀ k ∈ S, j ≠ k → (f j).conductor.Coprime (f k).conductor :=
      fun j hj k hk => hc j (mem_insert_of_mem hj) k (mem_insert_of_mem hk)
    have hp : (f i).conductor.Coprime ((∏ j ∈ S, f j).conductor) := by
      rw [ih hc']
      exact Nat.Coprime.prod_right (fun k hk => hc i (mem_insert_self ..) k (mem_insert_of_mem hk) (fun e => hi (e ▸ hk)))
    rw [prod_insert hi,prod_insert hi,conductor_mul_coprime _ _ hp,ih hc']

section Coordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ} [∀ i, NeZero (q i)]
  {L : ℕ} [NeZero L] (e : ZMod L ≃+* ∀ i, ZMod (q i))

omit [Fintype ι] [∀ i, NeZero (q i)] [NeZero L] in
theorem component_mul (A B : DirichletCharacter ℂ L) (i : ι) :
    component e (A*B) i = component e A i * component e B i := by
  apply MulChar.ext
  intro _
  rfl

omit [∀ i, NeZero (q i)] in
theorem recovered (hd : ∀ i, q i ∣ L) (A : DirichletCharacter ℂ L) :
    A = ∏ i, changeLevel (hd i) (component e A i) := by
  apply MulChar.ext
  intro u
  rw [reassemble e A u]
  let ev : DirichletCharacter ℂ L →* ℂ :=
    { toFun := fun χ => χ u, map_one' := MulChar.one_apply_coe u, map_mul' := fun _ _ => rfl }
  change _ = ev (∏ i, changeLevel (hd i) (component e A i))
  rw [map_prod]
  apply prod_congr rfl
  intro i _
  change _ = changeLevel (hd i) (component e A i) u
  rw [changeLevel_eq_cast_of_dvd]
  congr 1
  suffices eqCast : ∀ x : ZMod L, e x i = ZMod.cast x from eqCast u
  intro x
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod L)=x := ⟨x.val,ZMod.natCast_zmod_val x⟩
  rw [map_natCast,ZMod.cast_natCast (hd i)]
  rfl

omit [∀ i, NeZero (q i)] in
theorem global_conductor (hd : ∀ i, q i ∣ L) (hc : Pairwise (fun i k => (q i).Coprime (q k)))
    (A : DirichletCharacter ℂ L) :
    A.conductor = ∏ i, (component e A i).conductor := by
  let f (i : ι) := changeLevel (hd i) (component e A i)
  have val (i : ι) : (f i).conductor = (component e A i).conductor := conductor_changeLevel ..
  have cop : ∀ i ∈ univ, ∀ k ∈ univ, i ≠ k → (f i).conductor.Coprime (f k).conductor := by
    intro i _ k _ h
    rw [val,val]
    exact (hc h).of_dvd ((component e A i).conductor_dvd_level) ((component e A k).conductor_dvd_level)
  calc
    _ = (∏ i, f i).conductor := congrArg conductor (recovered e hd A)
    _ = ∏ i, (f i).conductor := conductor_prod f _ cop
    _ = _ := prod_congr rfl (fun i _ => val i)

omit [∀ i, NeZero (q i)] in
theorem component_conductor (hd : ∀ i, q i ∣ L) (hc : Pairwise (fun i k => (q i).Coprime (q k)))
    (A : DirichletCharacter ℂ L) (i : ι) :
    (component e A i).conductor=(q i).gcd A.conductor := by
  let f (k : ι) := (component e A k).conductor
  have cop : (q i).Coprime (∏ k ∈ (univ.erase i), f k) := Nat.Coprime.prod_right
    (fun k hk => (hc (mem_erase.mp hk).1.symm).of_dvd_right ((component e A k).conductor_dvd_level))
  rw [global_conductor e hd hc A]
  change f i = (q i).gcd (∏ k, f k)
  rw [← prod_erase_mul _ _ (mem_univ i),cop.symm.gcd_mul_left_cancel_right,
    Nat.gcd_eq_right ((component e A i).conductor_dvd_level)]

/-- Each individual CRT factor bounds the norm of the global correction.
This form retains the unnormalized local counts and also covers zero
local sums. -/
theorem single_factor {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ L) (hs : s ∣ L)
    (m : ℕ) (hm : 0 < m) (he : Even m) (i : ι) :
    ‖series α β m‖ * ‖J (1 : DirichletCharacter ℂ (q i)) 1 (m:ZMod (q i))‖ ≤
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
      ‖J (component e (changeLevel hr α) i) (component e (changeLevel hs β) i) (m:ZMod (q i))‖ := by
  let U (k : ι) := J (1 : DirichletCharacter ℂ (q k)) 1 (m:ZMod (q k))
  let V (k : ι) := J (component e (changeLevel hr α) k) (component e (changeLevel hs β) k) (m:ZMod (q k))
  let W (k : ι) := ‖V k/U k‖
  have hU (k : ι) : 0 < ‖U k‖ := norm_pos_iff.mpr (principal_ne_zero (q k) m he)
  have small (k : ι) : W k ≤ 1 := by
    dsimp [W]
    rw [norm_div,div_le_one (hU k)]
    exact TwistedGoldbachSingularSeries.chars_le_units _ _ _
  have all : (∏ k, W k) ≤ W i := by
    rw [← prod_erase_mul _ _ (mem_univ i)]
    exact mul_le_of_le_one_left (norm_nonneg _) (prod_le_one₀ (fun k _ => norm_nonneg _) (fun k _ => small k))
  have H := congrArg (fun z : ℂ => ‖z‖) (full_product e hα hβ hr hs m hm he)
  rw [norm_mul,norm_prod] at H
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  change ‖series α β m‖=O*(∏ k, W k) at H
  have bound : ‖series α β m‖ ≤ O*W i := H.le.trans (mul_le_mul_of_nonneg_left all (norm_nonneg _))
  dsimp only [W] at bound
  rw [norm_div,← mul_div_assoc] at bound
  exact (le_div_iff₀ (hU i)).mp bound

end Coordinates

theorem prime_part_gcd {L d p : ℕ} (hp : p.Prime) (hL : L ≠ 0) (hd : d ∣ L) :
    (p^L.factorization p).gcd d = p^d.factorization p := by
  have dn : d ≠ 0 := ne_zero_of_dvd_ne_zero hL hd
  apply Nat.dvd_antisymm
  · obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_left (p^L.factorization p) d)
    rw [hk]
    exact (hp.pow_dvd_iff_dvd_ordProj dn).mp (hk ▸ Nat.gcd_dvd_right (p^L.factorization p) d)
  · exact Nat.dvd_gcd (Nat.ordProj_dvd_ordProj_of_dvd hL hd p) (Nat.ordProj_dvd d p)

/-- At the prime-power CRT coordinate, the conductor keeps exactly the
valuation of the global conductor. -/
theorem prime_component_conductor {L : ℕ} [NeZero L] (A : DirichletCharacter ℂ L)
    (i : L.primeFactors) :
    (component (ZMod.equivPi L (NeZero.ne L)) A i).conductor=(i:ℕ)^A.conductor.factorization i := by
  rw [component_conductor _ (fun k : L.primeFactors => Nat.ordProj_dvd L k)
    L.pairwise_coprime_pow_primeFactors_factorization A i]
  exact prime_part_gcd (Nat.prime_of_mem_primeFactors i.property) (NeZero.ne L) A.conductor_dvd_level

end Conjectures.Goldbach.TwistedGoldbachConductorComponents

open Conjectures.Goldbach.TwistedGoldbachConductorComponents in
theorem Conjectures.Goldbach.TwistedGoldbachConductorComponents :
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
  exact
    (∀ (L : ℕ) [NeZero L] (A B : DirichletCharacter ℂ L),
      A.conductor.Coprime B.conductor → (A*B).conductor=A.conductor*B.conductor) ∧
    (∀ (L : ℕ) [NeZero L] (A : DirichletCharacter ℂ L) (i : L.primeFactors),
      let q := (i:ℕ)^L.factorization i
      ∃ χ : DirichletCharacter ℂ q,
        (∀ x : ZMod q, χ x = A ((ZMod.equivPi L (NeZero.ne L)).symm (Pi.mulSingle i x))) ∧
        χ.conductor=(i:ℕ)^A.conductor.factorization i) ∧
    (∀ (r s L : ℕ) [NeZero r] [NeZero s] [NeZero L]
      (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ (hr : r ∣ L) (hs : s ∣ L) (m : ℕ), 0 < m → Even m →
      ∀ i : L.primeFactors,
      let q := (i:ℕ)^L.factorization i
      let _ : NeZero q := ⟨(Nat.ordProj_pos L i).ne'⟩
      let lift := fun x : ZMod q => (ZMod.equivPi L (NeZero.ne L)).symm (Pi.mulSingle i x)
      let A := DirichletCharacter.changeLevel hr α
      let B := DirichletCharacter.changeLevel hs β
      ‖S α β m‖ * ‖∑ x : ZMod q, (1 : DirichletCharacter ℂ q) x * (1 : DirichletCharacter ℂ q) ((m:ZMod q)-x)‖ ≤
        ‖S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ *
          ‖∑ x : ZMod q, A (lift x) * B (lift ((m:ZMod q)-x))‖) := by
  classical
  refine ⟨fun _ _ => conductor_mul_coprime,?_,?_⟩
  · intro L _ A i q
    exact ⟨Conjectures.Goldbach.TwistedGoldbachLocalProduct.component (ZMod.equivPi L (NeZero.ne L)) A i,
      fun _ => rfl,prime_component_conductor A i⟩
  · intro r s L _ _ _ α β hα hβ hr hs m hm he i
    let (k : L.primeFactors) : NeZero ((k:ℕ)^L.factorization k) := ⟨(Nat.ordProj_pos L k).ne'⟩
    exact single_factor (ZMod.equivPi L (NeZero.ne L)) hα hβ hr hs m hm he i
