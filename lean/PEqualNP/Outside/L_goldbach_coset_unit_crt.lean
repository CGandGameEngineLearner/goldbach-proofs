import Mathlib

/-- Decidable form of the residue condition, evaluated through `ZMod.val`. -/
private abbrev good (n q : ℕ) (x : ZMod q) : Prop :=
  (x.val).Coprime q ∧ ((n + q - x.val) % q).Coprime q

/-- The residue condition in `ℕ` is the unit condition in `ZMod q`. -/
private lemma good_iff (n q r : ℕ) (hr : r < q) :
    (r.Coprime q ∧ ((n + q - r) % q).Coprime q) ↔
      IsUnit (r : ZMod q) ∧ IsUnit ((n : ZMod q) - (r : ZMod q)) := by
  have hcast : (((n + q - r) % q : ℕ) : ZMod q) = (n : ZMod q) - (r : ZMod q) := by
    rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(ZMod.isUnit_iff_coprime r q).2 h1, by
      rw [← hcast]
      exact (ZMod.isUnit_iff_coprime _ q).2 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(ZMod.isUnit_iff_coprime r q).1 h1, (ZMod.isUnit_iff_coprime _ q).1 (by
      rw [hcast]
      simpa using h2)⟩

/-- The same condition read on `ZMod q` itself. -/
private lemma good_units (n q : ℕ) [NeZero q] (x : ZMod q) :
    good n q x ↔ IsUnit x ∧ IsUnit ((n : ZMod q) - x) := by
  have h := good_iff n q x.val (ZMod.val_lt x)
  rwa [ZMod.natCast_zmod_val] at h

/-- The count `R n q` equals the number of residues satisfying `good`. -/
private lemma card_bridge (n q : ℕ) [NeZero q] :
    ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n + q - r) % q).Coprime q)).card
      = (Finset.univ.filter (fun x : ZMod q => good n q x)).card := by
  refine Finset.card_bij (fun r _ => (r : ZMod q)) ?_ ?_ ?_
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_range] at hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hval : ((r : ZMod q)).val = r := ZMod.val_cast_of_lt hr.1
    show ((r : ZMod q)).val.Coprime q ∧ ((n + q - ((r : ZMod q)).val) % q).Coprime q
    rw [hval]
    exact hr.2
  · intro r1 h1 r2 h2 he
    simp only [Finset.mem_filter, Finset.mem_range] at h1 h2
    have := congrArg ZMod.val he
    rwa [ZMod.val_cast_of_lt h1.1, ZMod.val_cast_of_lt h2.1] at this
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    refine ⟨x.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt x, ?_⟩
      exact hx
    · exact ZMod.natCast_zmod_val x

/-- A pair is a unit of a product ring exactly when both components are units. -/
private lemma isUnit_prod_iff {R S : Type*} [Ring R] [Ring S] (p : R × S) :
    IsUnit p ↔ IsUnit p.1 ∧ IsUnit p.2 := by
  constructor
  · intro h
    exact ⟨h.map (RingHom.fst R S), h.map (RingHom.snd R S)⟩
  · rintro ⟨u1, u2⟩
    obtain ⟨a1, ha1⟩ := u1
    obtain ⟨a2, ha2⟩ := u2
    refine ⟨⟨(↑a1, ↑a2), (↑a1⁻¹, ↑a2⁻¹), ?_, ?_⟩, ?_⟩
    · ext <;> simp
    · ext <;> simp
    · ext <;> assumption

/-- The count is multiplicative in the modulus. -/
private lemma card_mul (n a b : ℕ) [NeZero a] [NeZero b] [NeZero (a * b)] (h : a.Coprime b) :
    (Finset.univ.filter (fun x : ZMod (a * b) => good n (a * b) x)).card
      = (Finset.univ.filter (fun x : ZMod a => good n a x)).card
        * (Finset.univ.filter (fun x : ZMod b => good n b x)).card := by
  classical
  have hA : (Finset.univ.filter (fun x : ZMod (a * b) => good n (a * b) x))
      = Finset.univ.filter (fun x : ZMod (a * b) => IsUnit x ∧ IsUnit ((n : ZMod (a * b)) - x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact good_units n (a * b) x
  have hB : (Finset.univ.filter (fun x : ZMod a => good n a x))
      = Finset.univ.filter (fun x : ZMod a => IsUnit x ∧ IsUnit ((n : ZMod a) - x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact good_units n a x
  have hC : (Finset.univ.filter (fun x : ZMod b => good n b x))
      = Finset.univ.filter (fun x : ZMod b => IsUnit x ∧ IsUnit ((n : ZMod b) - x)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact good_units n b x
  rw [hA, hB, hC]
  let e : ZMod (a * b) ≃+* ZMod a × ZMod b := ZMod.chineseRemainder h
  have e_n : e (n : ZMod (a * b)) = ((n : ZMod a), (n : ZMod b)) := by
    ext <;> simp [e, ZMod.chineseRemainder]
  have hmap : ∀ y : ZMod (a * b), IsUnit y ↔ IsUnit (e y) := by
    intro y
    constructor
    · intro hy; exact hy.map e.toRingHom
    · intro hy; simpa using hy.map e.symm.toRingHom
  have key : ∀ x : ZMod (a * b), (IsUnit x ∧ IsUnit ((n : ZMod (a * b)) - x)) ↔
      ((IsUnit (e x).1 ∧ IsUnit ((n : ZMod a) - (e x).1)) ∧
        (IsUnit (e x).2 ∧ IsUnit ((n : ZMod b) - (e x).2))) := by
    intro x
    have hsub : e ((n : ZMod (a * b)) - x) = e (n : ZMod (a * b)) - e x := map_sub e _ _
    have hprod : e (n : ZMod (a * b)) - e x
        = ((n : ZMod a) - (e x).1, (n : ZMod b) - (e x).2) := by
      rw [e_n]
      ext <;> simp
    have hmain : IsUnit ((n : ZMod (a * b)) - x) ↔
        IsUnit ((n : ZMod a) - (e x).1) ∧ IsUnit ((n : ZMod b) - (e x).2) := by
      rw [hmap, hsub, hprod]
      exact isUnit_prod_iff _
    rw [hmap, hmain, isUnit_prod_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
    · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
      exact ⟨⟨h1, h2⟩, h3, h4⟩
  rw [← Finset.card_product]
  refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hx ⊢
    exact (key x).1 hx
  · intro x1 _ x2 _ h
    exact e.injective h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hp
    refine ⟨e.symm p, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine (key (e.symm p)).2 ?_
      rw [e.apply_symm_apply]
      exact hp
    · exact e.apply_symm_apply p

theorem PEqualNP.Outside.L_goldbach_coset_unit_crt :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r)%q).Coprime q)).card; ∀ n a b : ℕ, 0<a → 0<b → a.Coprime b → R n (a*b)=R n a*R n b := by
  dsimp only
  intro n a b ha hb hcop
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  have hb0 : b ≠ 0 := Nat.ne_of_gt hb
  haveI : NeZero a := ⟨ha0⟩
  haveI : NeZero b := ⟨hb0⟩
  show ((Finset.range (a * b)).filter (fun r => r.Coprime (a * b) ∧ ((n + a * b - r) % (a * b)).Coprime (a * b))).card
      = ((Finset.range a).filter (fun r => r.Coprime a ∧ ((n + a - r) % a).Coprime a)).card
        * ((Finset.range b).filter (fun r => r.Coprime b ∧ ((n + b - r) % b).Coprime b)).card
  rw [card_bridge, card_bridge, card_bridge, card_mul n a b hcop]
