import Conjectures.Goldbach.TwistedGoldbachSingularSeries

/-! Reduction of an admissible binary residue pair through any divisor has
uniform fibers. This lets one recover the ratio of the full twisted and
ordinary singular series from a single modulus containing both conductors. -/

namespace Conjectures.Goldbach.TwistedGoldbachConductorRatio

open Finset DirichletCharacter
open scoped BigOperators Classical

def admissible {n : ℕ} (m x : ZMod n) : Prop := IsUnit x ∧ IsUnit (m-x)

noncomputable def fiber {q L : ℕ} [NeZero q] (h : L ∣ q) (m : ZMod q) (u : ZMod L) :
    Finset (ZMod q) := univ.filter (fun x => admissible m x ∧ ZMod.castHom h (ZMod L) x=u)

private theorem unit_criterion {q : ℕ} [NeZero q] (x : ZMod q) :
    IsUnit x ↔ ∀ (p : ℕ), p.Prime → ∀ h : p ∣ q, ZMod.castHom h (ZMod p) x ≠ 0 := by
  constructor
  · intro hx p hp h
    let _ : Fact p.Prime := ⟨hp⟩
    exact (hx.map (ZMod.castHom h (ZMod p))).ne_zero
  · obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod q)=x := ⟨x.val,ZMod.natCast_zmod_val x⟩
    intro H
    apply (ZMod.isUnit_iff_coprime n q).mpr
    apply Nat.coprime_of_dvd
    intro p hp hn hq
    exact H p hp hq (by rw [map_natCast,ZMod.natCast_eq_zero_iff]; exact hn)

private theorem reduce_twice {p q L : ℕ} [NeZero q] (h : L ∣ q) (g : p ∣ L) (x : ZMod q) :
    ZMod.castHom g (ZMod p) (ZMod.castHom h (ZMod L) x) = ZMod.castHom (g.trans h) (ZMod p) x := by
  obtain ⟨n,rfl⟩ : ∃ n : ℕ, (n : ZMod q)=x := ⟨x.val,ZMod.natCast_zmod_val x⟩
  simp only [map_natCast]

private theorem preserving_shift {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (b : ZMod L) :
    ∃ c : ZMod q, ZMod.castHom h (ZMod L) c=b ∧
      ∀ p : ℕ, p.Prime → ∀ hp : p ∣ q, ¬p ∣ L → ZMod.castHom hp (ZMod p) c=0 := by
  let S := q.primeFactors.filter (fun p => ¬p ∣ L)
  let D := ∏ p ∈ S, p
  have hc : D.Coprime L := Nat.coprime_prod_left_iff.mpr (fun p hp =>
    (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).coprime_iff_not_dvd.mpr (mem_filter.mp hp).2)
  let u := ZMod.unitOfCoprime D hc
  let n := ((↑u⁻¹ : ZMod L)*b).val
  refine ⟨((D*n:ℕ):ZMod q),?_,?_⟩
  · rw [map_natCast,Nat.cast_mul,show (n : ZMod L) = (↑u⁻¹ : ZMod L)*b from ZMod.natCast_zmod_val _]
    change (↑u : ZMod L)*(↑u⁻¹*b)=b
    simp
  · intro p hp hq hL
    have hpS : p ∈ S := mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp,hq,NeZero.ne q⟩,hL⟩
    rw [map_natCast,ZMod.natCast_eq_zero_iff]
    exact (dvd_prod_of_mem (fun z : ℕ => z) hpS).trans (dvd_mul_right D n)

private theorem patch_unit {q L : ℕ} [NeZero q] (h : L ∣ q) (x c : ZMod q) (hx : IsUnit x)
    (hl : IsUnit (ZMod.castHom h (ZMod L) (x+c)))
    (away : ∀ p : ℕ, p.Prime → ∀ hp : p ∣ q, ¬p ∣ L → ZMod.castHom hp (ZMod p) c=0) :
    IsUnit (x+c) := by
  apply (unit_criterion _).mpr
  intro p hprime hp
  by_cases hL : p ∣ L
  · let _ : Fact p.Prime := ⟨hprime⟩
    rw [← reduce_twice h hL]
    exact (hl.map (ZMod.castHom hL (ZMod p))).ne_zero
  · rw [map_add,away p hprime hp hL,add_zero]
    exact (unit_criterion x).mp hx p hprime hp

private theorem fiber_card_le {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q)
    (m : ZMod q) (u v : ZMod L) (hv : admissible (ZMod.castHom h (ZMod L) m) v) :
    (fiber h m u).card ≤ (fiber h m v).card := by
  let π := ZMod.castHom h (ZMod L)
  obtain ⟨c,hc,away⟩ := preserving_shift h (v-u)
  apply card_le_card_of_injOn (fun x : ZMod q => x+c)
  · intro x hx
    obtain ⟨⟨hxunit,hother⟩,hπ⟩ := (mem_filter.mp hx).2
    have image : π (x+c)=v := by rw [map_add,hπ,hc]; abel
    refine mem_filter.mpr ⟨mem_univ _,⟨⟨?_,?_⟩,image⟩⟩
    · apply patch_unit h x c hxunit _ away
      exact image ▸ hv.1
    · rw [show m-(x+c)=(m-x)+(-c) by ring]
      apply patch_unit h (m-x) (-c) hother
      · change IsUnit (π ((m-x)+(-c)))
        rw [show (m-x)+(-c)=m-(x+c) by ring,map_sub,image]
        exact hv.2
      · intro p hprime hp hL
        rw [map_neg,away p hprime hp hL,neg_zero]
  · intro x _ y _ e
    exact add_right_cancel e

/-- Every lower admissible pair has the same number of admissible lifts,
including when q has prime factors absent from L. -/
theorem uniform_fibers {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (m : ZMod q) :
    ∃ K : ℕ, ∀ u : ZMod L, (fiber h m u).card =
      if admissible (ZMod.castHom h (ZMod L) m) u then K else 0 := by
  let π := ZMod.castHom h (ZMod L)
  have empty (u : ZMod L) (hu : ¬admissible (π m) u) : fiber h m u=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨⟨h₁,h₂⟩,e⟩ := (mem_filter.mp hx).2
    apply hu
    rw [← e]
    exact ⟨h₁.map π,by simpa only [map_sub] using h₂.map π⟩
  by_cases H : ∃ u : ZMod L, admissible (π m) u
  · obtain ⟨u,hu⟩ := H
    refine ⟨(fiber h m u).card,fun v => ?_⟩
    by_cases hv : admissible (π m) v
    · rw [ite_eq_left hv]
      exact le_antisymm (fiber_card_le h m v u hu) (fiber_card_le h m u v hv)
    · rw [ite_eq_right hv,empty v hv,card_empty]
  · refine ⟨0,fun u => ?_⟩
    have hu : ¬admissible (π m) u := fun h => H ⟨u,h⟩
    rw [ite_eq_right hu,empty u hu,card_empty]

private theorem reduce_admissible {q L : ℕ} (h : L ∣ q) {m x : ZMod q} (hx : admissible m x) :
    admissible (ZMod.castHom h (ZMod L) m) (ZMod.castHom h (ZMod L) x) :=
  ⟨hx.1.map _,by simpa only [map_sub] using hx.2.map (ZMod.castHom h (ZMod L))⟩

theorem fiber_weight {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (m : ZMod q) :
    ∃ K : ℕ, ∀ F : ZMod L → ℂ,
      (∑ x ∈ univ.filter (admissible m), F (ZMod.castHom h (ZMod L) x)) =
        (K:ℂ)*∑ y ∈ univ.filter (admissible (ZMod.castHom h (ZMod L) m)), F y := by
  let π := ZMod.castHom h (ZMod L)
  let H := univ.filter (admissible m)
  let T := univ.filter (admissible (π m))
  obtain ⟨K,hK⟩ := uniform_fibers h m
  refine ⟨K, fun F => ?_⟩
  have maps : ∀ x ∈ H, π x ∈ T := fun x hx =>
    mem_filter.mpr ⟨mem_univ _,reduce_admissible h (mem_filter.mp hx).2⟩
  have group (u : ZMod L) : H.filter (fun x => π x=u) = fiber h m u := by
    ext x
    simp only [H,π,fiber,mem_filter,mem_univ,true_and]
  change (∑ x ∈ H, F (π x)) = (K:ℂ)*∑ u ∈ T, F u
  rw [← sum_fiberwise_of_maps_to' maps F,mul_sum]
  apply sum_congr rfl
  intro u hu
  have hu' : admissible (ZMod.castHom h (ZMod L) m) u := (mem_filter.mp hu).2
  rw [group,sum_const,nsmul_eq_mul,hK u,ite_eq_left hu']

noncomputable def J {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) : ℂ :=
  ∑ x : ZMod q, χ x * ψ (m-x)

private theorem restricted_eq {q : ℕ} [NeZero q] (χ ψ : DirichletCharacter ℂ q) (m : ZMod q) :
    (∑ x ∈ univ.filter (admissible m), χ x * ψ (m-x)) = J χ ψ m := by
  apply sum_subset (filter_subset ..)
  intro x _ hx
  by_cases hu : IsUnit x
  · have hv : ¬IsUnit (m-x) := fun hv => hx (mem_filter.mpr ⟨mem_univ _,hu,hv⟩)
    simp [ψ.map_nonunit hv]
  · simp [χ.map_nonunit hu]

/-- The same lift multiplicity works for all pairs of characters at L. -/
theorem jacobi_lift {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q) (m : ZMod q) :
    ∃ K : ℕ, ∀ χ ψ : DirichletCharacter ℂ L,
      J (changeLevel h χ) (changeLevel h ψ) m = (K:ℂ)*J χ ψ (ZMod.castHom h (ZMod L) m) := by
  let π := ZMod.castHom h (ZMod L)
  obtain ⟨K,hK⟩ := fiber_weight h m
  refine ⟨K,fun χ ψ => ?_⟩
  have reduce (θ : DirichletCharacter ℂ L) (x : ZMod q) (hx : IsUnit x) :
      changeLevel h θ x = θ (π x) := by
    simpa only [π,IsUnit.unit_spec,ZMod.castHom_apply] using changeLevel_eq_cast_of_dvd θ h hx.unit
  rw [← restricted_eq,← restricted_eq χ ψ]
  calc
    _ = ∑ x ∈ univ.filter (admissible m), χ (π x)*ψ (π m-π x) := by
      apply sum_congr rfl
      intro x hx
      have h' := (mem_filter.mp hx).2
      rw [reduce χ x h'.1,reduce ψ (m-x) h'.2,map_sub]
    _ = _ := hK (fun x => χ x*ψ (π m-x))

open TwistedGoldbachSingularSeries

private theorem finite_cross {q L : ℕ} [NeZero q] [NeZero L] (h : L ∣ q)
    (χ ψ : DirichletCharacter ℂ L) (m : ℕ) :
    normalized (changeLevel h χ) (changeLevel h ψ) m * J (1 : DirichletCharacter ℂ L) 1 (m : ZMod L) =
      normalized (1 : DirichletCharacter ℂ q) 1 m * J χ ψ (m : ZMod L) := by
  obtain ⟨K,hK⟩ := jacobi_lift h (m : ZMod q)
  have weighted := hK χ ψ
  have ordinary := hK 1 1
  simp only [map_natCast,map_one] at weighted ordinary
  change ((q:ℂ)*J (changeLevel h χ) (changeLevel h ψ) (m : ZMod q)/(q.totient:ℂ)^2)*_ =
    ((q:ℂ)*J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q)/(q.totient:ℂ)^2)*_
  rw [weighted,ordinary]
  ring

open Filter Topology

/-- The ratio of the two singular series is determined at any single common
multiple of the conductors. The identity also holds at targets for which the
principal residue count vanishes. -/
theorem conductor_identity {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) :
    (∑' d : ℕ, coefficient α β m d) * J (1 : DirichletCharacter ℂ L) 1 (m : ZMod L) =
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
        J (changeLevel hr α) (changeLevel hs β) (m : ZMod L) := by
  let oneχ : DirichletCharacter ℂ 1 := 1
  have left := (partial_limit α β m hm L (NeZero.ne L)).mul_const (J (1 : DirichletCharacter ℂ L) 1 (m : ZMod L))
  have right := (partial_limit oneχ oneχ m hm L (NeZero.ne L)).mul_const
    (J (changeLevel hr α) (changeLevel hs β) (m : ZMod L))
  apply tendsto_nhds_unique_of_eventuallyEq left right
  filter_upwards with n
  let q := L*n.factorial
  let _ : NeZero q := ⟨mul_ne_zero (NeZero.ne L) n.factorial_ne_zero⟩
  have h : L ∣ q := dvd_mul_right L n.factorial
  have ordinary := ambient_sum (α := oneχ) (β := oneχ) isPrimitive_one_level_one
    isPrimitive_one_level_one (one_dvd q) (one_dvd q) m
  simp only [oneχ,map_one] at ordinary
  change ((∑ d ∈ q.divisors, coefficient α β m d)*_) =
    ((∑ d ∈ q.divisors, coefficient oneχ oneχ m d)*_)
  rw [← ambient_sum hα hβ (hr.trans h) (hs.trans h) m, ← ordinary,
    changeLevel_trans α hr h, changeLevel_trans β hs h]
  exact finite_cross h (changeLevel hr α) (changeLevel hs β) m

/-- The principal-character convolution counts admissible residues. -/
theorem principal_card {L : ℕ} [NeZero L] (m : ZMod L) :
    J (1 : DirichletCharacter ℂ L) 1 m = ((univ.filter (admissible m)).card:ℂ) := by
  rw [← restricted_eq]
  calc
    _ = ∑ _x ∈ univ.filter (admissible m), (1:ℂ) := by
      apply sum_congr rfl
      intro x hx
      have H := (mem_filter.mp hx).2
      rw [MulChar.one_apply H.1,MulChar.one_apply H.2,one_mul]
    _ = _ := by simp

/-- An explicit admissible residue for every even target and every positive
modulus. At a prime where the target is one the polynomial selects minus one,
and otherwise it selects one. -/
theorem admissible_even (L : ℕ) [NeZero L] (m : ℕ) (he : Even m) :
    ∃ x : ZMod L, admissible (m : ZMod L) x := by
  let x : ZMod L := 2*((m:ZMod L)-1)^L.factorial-1
  have both (p : ℕ) (hp : p.Prime) (h : p ∣ L) :
      ZMod.castHom h (ZMod p) x ≠ 0 ∧ ZMod.castHom h (ZMod p) ((m:ZMod L)-x) ≠ 0 := by
    let _ : Fact p.Prime := ⟨hp⟩
    have red : ZMod.castHom h (ZMod p) x = 2*((m:ZMod p)-1)^L.factorial-1 := by
      simp only [x,map_sub,map_mul,map_ofNat,map_pow,map_natCast,map_one]
    have red' : ZMod.castHom h (ZMod p) ((m:ZMod L)-x) =
        (m:ZMod p) - (2*((m:ZMod p)-1)^L.factorial-1) := by
      rw [map_sub,map_natCast,red]
    rw [red,red']
    by_cases h1 : (m:ZMod p)=1
    · have p2 : p≠2 := by
        rintro rfl
        have hz : (m : ZMod 2)=0 := (ZMod.natCast_eq_zero_iff m 2).mpr (even_iff_two_dvd.mp he)
        exact one_ne_zero (h1.symm.trans hz)
      have nz : (2 : ZMod p) ≠ 0 := fun hz =>
        p2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp hz))
      simp only [h1,sub_self,zero_pow L.factorial_ne_zero,mul_zero,zero_sub,sub_neg_eq_add]
      exact ⟨neg_ne_zero.mpr one_ne_zero,by simpa only [one_add_one_eq_two] using nz⟩
    · have hpL : p≤L := Nat.le_of_dvd (NeZero.pos L) h
      obtain ⟨t,ht⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hp.one_lt) ((Nat.sub_le p 1).trans hpL)
      have u : ((m:ZMod p)-1)^L.factorial = 1 := by
        rw [ht,pow_mul,ZMod.pow_card_sub_one_eq_one (sub_ne_zero.mpr h1),one_pow]
      rw [u,mul_one,show (2:ZMod p)-1=1 by ring]
      exact ⟨one_ne_zero,sub_ne_zero.mpr h1⟩
  exact ⟨x,(unit_criterion x).mpr (fun p hp h => (both p hp h).1),
    (unit_criterion _).mpr (fun p hp h => (both p hp h).2)⟩

/-- At even targets the ordinary count in the denominator is positive, so the
finite conductor-level correction can be used as a literal complex ratio. -/
theorem exact_ratio {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (hr : r ∣ L) (hs : s ∣ L) (m : ℕ)
    (hm : 0 < m) (he : Even m) :
    (∑' d : ℕ, coefficient α β m d) =
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
        (J (changeLevel hr α) (changeLevel hs β) (m : ZMod L) /
          ((univ.filter (admissible (m : ZMod L))).card:ℂ)) := by
  obtain ⟨x,hx⟩ := admissible_even L m he
  have positive := card_pos.mpr (show (univ.filter (admissible (m : ZMod L))).Nonempty from
    ⟨x,mem_filter.mpr ⟨mem_univ _,hx⟩⟩)
  rw [← mul_div_assoc,eq_div_iff (Nat.cast_ne_zero.mpr positive.ne')]
  rw [← principal_card]
  exact conductor_identity hα hβ hr hs m hm

/-- At zero, orthogonality selects the inverse pair of characters. -/
theorem zero_jacobi {L : ℕ} [NeZero L] (A B : DirichletCharacter ℂ L) :
    J A B 0 = if A*B=1 then B (-1)*(L.totient:ℂ) else 0 := by
  have eqn (x : ZMod L) : A x * B (0-x) = B (-1)*(A*B) x := by
    rw [zero_sub,← neg_one_mul x,map_mul,MulChar.mul_apply]
    ring
  simp only [J,eqn,← mul_sum]
  by_cases h : A*B=1
  · rw [ite_eq_left h,h,MulChar.sum_one_eq_card_units,ZMod.card_units_eq_totient]
  · rw [ite_eq_right h,MulChar.sum_eq_zero_of_ne_one h,mul_zero]

/-- On a multiple of both conductors, all off-diagonal character pairs
vanish. The surviving inverse pair retains its parity at minus one. -/
theorem at_conductor_multiple {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (m : ℕ) (hm : 0 < m) (divides : L ∣ m) :
    (∑' d : ℕ, coefficient α β m d) = if changeLevel hr α * changeLevel hs β = 1 then
      (∑' d : ℕ, coefficient (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
      changeLevel hs β (-1) else 0 := by
  have ident := conductor_identity hα hβ hr hs m hm
  have hz := (ZMod.natCast_eq_zero_iff m L).mpr divides
  have principal : J (1 : DirichletCharacter ℂ L) 1 0 = (L.totient:ℂ) := by
    rw [zero_jacobi]
    simp [MulChar.one_apply (isUnit_neg_one : IsUnit (-1 : ZMod L))]
  rw [hz,principal,zero_jacobi] at ident
  apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne L.totient) : (L.totient:ℂ) ≠ 0)
  split_ifs at ident ⊢ with h
  · simpa only [mul_assoc] using ident
  · simpa only [zero_mul,mul_zero] using ident

theorem unequal_conductors_vanish {r s L : ℕ} [NeZero r] [NeZero s] [NeZero L]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ L) (hs : s ∣ L) (hne : r≠s) (m : ℕ) (hm : 0 < m) (divides : L ∣ m) :
    (∑' d : ℕ, coefficient α β m d) = 0 := by
  rw [at_conductor_multiple hα hβ hr hs m hm divides]
  apply ite_eq_right
  intro hab
  have hinv : changeLevel hs β = (changeLevel hr α)⁻¹ := eq_inv_of_mul_eq_one_right hab
  have e := congrArg DirichletCharacter.conductor hinv
  simp only [conductor_inv,conductor_changeLevel,show α.conductor=r from hα,
    show β.conductor=s from hβ] at e
  exact hne e.symm

end Conjectures.Goldbach.TwistedGoldbachConductorRatio

set_option maxHeartbeats 1200000 in
open Conjectures.Goldbach.TwistedGoldbachConductorRatio in
theorem Conjectures.Goldbach.TwistedGoldbachConductorRatio :
by
  classical
  let c := fun (r s : ℕ) (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m d : ℕ) =>
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
    (∀ (q L : ℕ) [NeZero q] [NeZero L] (h : L ∣ q) (m : ZMod q),
      let π := ZMod.castHom h (ZMod L)
      ∃ K : ℕ, ∀ u : ZMod L,
      ((Finset.univ : Finset (ZMod q)).filter
        (fun x => (IsUnit x ∧ IsUnit (m-x)) ∧ π x = u)).card =
        if IsUnit u ∧ IsUnit (π m-u) then K else 0) ∧
    (∀ (r s L : ℕ) [NeZero r] [NeZero s] [NeZero L] (α : DirichletCharacter ℂ r)
      (β : DirichletCharacter ℂ s), α.IsPrimitive → β.IsPrimitive →
      ∀ (hr : r ∣ L) (hs : s ∣ L) (m : ℕ), 0 < m →
        (∑' d : ℕ, c r s α β m d) *
            (∑ x : ZMod L, (1 : DirichletCharacter ℂ L) x * (1 : DirichletCharacter ℂ L) ((m : ZMod L)-x)) =
        (∑' d : ℕ, c 1 1 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
            (∑ x : ZMod L, DirichletCharacter.changeLevel hr α x * DirichletCharacter.changeLevel hs β ((m : ZMod L)-x))) ∧
    (∀ (L : ℕ) [NeZero L] (m : ℕ), Even m → ∃ x : ZMod L, IsUnit x ∧ IsUnit ((m : ZMod L)-x)) ∧
    (∀ (r s L : ℕ) [NeZero r] [NeZero s] [NeZero L] (α : DirichletCharacter ℂ r)
      (β : DirichletCharacter ℂ s), α.IsPrimitive → β.IsPrimitive →
      ∀ (hr : r ∣ L) (hs : s ∣ L) (m : ℕ), 0 < m → Even m →
        (∑' d : ℕ, c r s α β m d) =
        (∑' d : ℕ, c 1 1 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
          ((∑ x : ZMod L, DirichletCharacter.changeLevel hr α x * DirichletCharacter.changeLevel hs β ((m : ZMod L)-x)) /
            (((Finset.univ : Finset (ZMod L)).filter (fun x => IsUnit x ∧ IsUnit ((m : ZMod L)-x))).card : ℂ))) ∧
    (∀ (r s L : ℕ) [NeZero r] [NeZero s] [NeZero L] (α : DirichletCharacter ℂ r)
      (β : DirichletCharacter ℂ s), α.IsPrimitive → β.IsPrimitive →
      ∀ (hr : r ∣ L) (hs : s ∣ L) (m : ℕ), 0 < m → L ∣ m →
      (∑' d : ℕ, c r s α β m d) = if DirichletCharacter.changeLevel hr α * DirichletCharacter.changeLevel hs β = 1 then
        (∑' d : ℕ, c 1 1 (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m d) *
          DirichletCharacter.changeLevel hs β (-1) else 0) ∧
    (∀ (r s L : ℕ) [NeZero r] [NeZero s] [NeZero L] (α : DirichletCharacter ℂ r)
      (β : DirichletCharacter ℂ s), α.IsPrimitive → β.IsPrimitive → r ∣ L → s ∣ L → r ≠ s →
      ∀ m : ℕ, 0 < m → L ∣ m → (∑' d : ℕ, c r s α β m d) = 0) := by
  classical
  refine ⟨?_,fun _ _ _ _ _ _ _ _ hα hβ hr hs m hm => conductor_identity hα hβ hr hs m hm,
    fun L _ m he => admissible_even L m he,?_,
    fun _ _ _ _ _ _ _ _ hα hβ hr hs m hm h => at_conductor_multiple hα hβ hr hs m hm h,
    fun _ _ _ _ _ _ _ _ hα hβ hr hs hn m hm h => unequal_conductors_vanish hα hβ hr hs hn m hm h⟩
  · intro q L _ _ h m π
    obtain ⟨K,hK⟩ := uniform_fibers h m
    refine ⟨K,fun u => ?_⟩
    have eqn : ((Finset.univ : Finset (ZMod q)).filter
      (fun x => (IsUnit x ∧ IsUnit (m-x)) ∧ π x=u)) = fiber h m u := by
      apply Finset.ext
      intro x
      constructor <;> intro hx <;>
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
    rw [eqn,hK u]
    split_ifs <;> simp_all [admissible,π]
  · intro r s L _ _ _ α β hα hβ hr hs m hm he
    have eqn : ((Finset.univ : Finset (ZMod L)).filter (fun x => IsUnit x ∧ IsUnit ((m:ZMod L)-x))) =
        Finset.univ.filter (admissible (m : ZMod L)) := by
      ext x
      simp only [admissible,Finset.mem_filter]
    rw [eqn]
    exact exact_ratio hα hβ hr hs m hm he
