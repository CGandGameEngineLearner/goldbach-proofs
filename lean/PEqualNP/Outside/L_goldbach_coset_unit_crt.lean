import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_unit_crt :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r)%q).Coprime q)).card; ∀ n a b : ℕ, 0<a → 0<b → a.Coprime b → R n (a*b)=R n a*R n b := by
  classical
  dsimp only
  intro n a b ha hb hab
  haveI : NeZero a := ⟨by omega⟩
  haveI : NeZero b := ⟨by omega⟩
  haveI : NeZero (a*b) := ⟨(Nat.mul_pos ha hb).ne'⟩
  set P : ℕ → ℕ → Prop := fun q r => r.Coprime q ∧ ((n+q-r)%q).Coprime q with hP
  let Q : (q : ℕ) → ZMod q → Prop := fun q x => IsUnit x ∧ IsUnit ((n : ZMod q) - x)
  have hcast : ∀ q : ℕ, 0 < q → ∀ r : ℕ, r < q →
      ((((n+q-r) % q : ℕ)) : ZMod q) = (n : ZMod q) - (r : ZMod q) := by
    intro q hq r hr
    rw [ZMod.natCast_mod, Nat.cast_sub (by omega : r ≤ n + q), Nat.cast_add, ZMod.natCast_self]
    ring
  have hunit : ∀ q : ℕ, 0 < q → ∀ r : ℕ, r < q →
      ((r.Coprime q ∧ ((n+q-r)%q).Coprime q) ↔ Q q (r : ZMod q)) := by
    intro q hq r hr
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · rwa [ZMod.isUnit_iff_coprime]
      · rw [← hcast q hq r hr, ZMod.isUnit_iff_coprime]
        exact h2
    · rintro ⟨h1, h2⟩
      constructor
      · rwa [ZMod.isUnit_iff_coprime] at h1
      · rw [← ZMod.isUnit_iff_coprime, hcast q hq r hr]
        exact h2
  have hbridge : ∀ (q : ℕ) [NeZero q],
      ((Finset.range q).filter (P q)).card = (Finset.univ.filter (Q q)).card := by
    intro q hq0
    have hq : 0 < q := Nat.pos_of_ne_zero hq0.out
    refine Finset.card_bij (fun r _ => ((r : ℕ) : ZMod q)) ?_ ?_ ?_
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hunit q hq r hr.1).1 ⟨hr.2.1, hr.2.2⟩
    · intro r1 hr1 r2 hr2 heq
      simp only [Finset.mem_filter, Finset.mem_range] at hr1 hr2
      have hval : r1 % q = r2 % q := by
        have := congrArg ZMod.val heq
        simpa [ZMod.val_natCast] using this
      rwa [Nat.mod_eq_of_lt hr1.1, Nat.mod_eq_of_lt hr2.1] at hval
    · intro x hx
      have hx' : Q q x := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hx
      refine ⟨ZMod.val x, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt x, ?_⟩
      have hx'' : Q q ((ZMod.val x : ℕ) : ZMod q) := by
        rw [ZMod.natCast_zmod_val]
        exact hx'
      exact (hunit q hq (ZMod.val x) (ZMod.val_lt x)).2 hx''
  have pairUnit : ∀ {x : ZMod a} {y : ZMod b}, IsUnit x → IsUnit y → IsUnit (x, y) := by
    rintro x y ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨Units.mkOfMulEqOne (x, y) (↑u⁻¹, ↑v⁻¹) (by simp [hu, hv]), rfl⟩
  have hmain : (Finset.univ.filter (Q (a*b))).card
      = (Finset.univ.filter (fun y : ZMod a × ZMod b => Q a y.1 ∧ Q b y.2)).card := by
    set e := ZMod.chineseRemainder hab with he
    refine Finset.card_bij (fun x _ => e x) ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨h1, h2⟩ := hx
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · show IsUnit (((RingHom.fst (ZMod a) (ZMod b)).comp e.toRingHom) x)
        exact h1.map _
      · have := h2.map ((RingHom.fst (ZMod a) (ZMod b)).comp e.toRingHom)
        simpa [map_sub] using this
      · show IsUnit (((RingHom.snd (ZMod a) (ZMod b)).comp e.toRingHom) x)
        exact h1.map _
      · have := h2.map ((RingHom.snd (ZMod a) (ZMod b)).comp e.toRingHom)
        simpa [map_sub] using this
    · intro x1 _ x2 _ heq
      exact e.injective heq
    · intro y hy
      have hy' : Q a y.1 ∧ Q b y.2 := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hy
      refine ⟨e.symm y, ?_, by simp⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact (pairUnit hy'.1.1 hy'.2.1).map e.symm.toRingHom
      · have hnu : IsUnit (e (n - e.symm y)) := by
          have hp : e (n - e.symm y) = ((n : ZMod a) - y.1, (n : ZMod b) - y.2) := by
            ext <;> simp
          rw [hp]
          exact pairUnit hy'.1.2 hy'.2.2
        have := hnu.map e.symm.toRingHom
        simpa using this
  have hsplit : (Finset.univ.filter (fun y : ZMod a × ZMod b => Q a y.1 ∧ Q b y.2)).card
      = (Finset.univ.filter (Q a)).card * (Finset.univ.filter (Q b)).card := by
    rw [← Finset.card_product]
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
  rw [hbridge (a*b), hbridge a, hbridge b, hmain, hsplit]