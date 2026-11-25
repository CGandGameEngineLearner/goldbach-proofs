import Mathlib

theorem PEqualNP.Outside.L_goldbach_coset_unit_crt :
    let R := fun n q : ℕ => ((Finset.range q).filter (fun r => r.Coprime q ∧ ((n+q-r) % q).Coprime q)).card;
    ∀ n a b : ℕ, 0<a → 0<b → a.Coprime b → R n (a*b)=R n a*R n b := by
  show ∀ n a b : ℕ, 0<a → 0<b → a.Coprime b →
    ((Finset.range (a*b)).filter (fun r => r.Coprime (a*b) ∧ ((n+a*b-r) % (a*b)).Coprime (a*b))).card
      = ((Finset.range a).filter (fun r => r.Coprime a ∧ ((n+a-r) % a).Coprime a)).card
      * ((Finset.range b).filter (fun r => r.Coprime b ∧ ((n+b-r) % b).Coprime b)).card
  intro n a b ha hb hab
  have hra : ∀ r : ℕ, r % a < a := fun r => Nat.mod_lt r ha
  have hrb : ∀ r : ℕ, r % b < b := fun r => Nat.mod_lt r hb
  -- the two CRT residue transfers for the reflected partner
  have hrefa : ∀ r : ℕ, r < a*b → ((n+a*b-r) % (a*b)) % a = (n+a-r%a) % a := by
    intro r hr
    have h1 : (n+a*b-r) % (a*b) ≡ n+a*b-r [MOD a] :=
      (Nat.mod_modEq (n+a*b-r) (a*b)).of_dvd (Nat.dvd_mul_right a b)
    have hle2 : a ≤ a*b := Nat.le_mul_of_pos_right a hb
    have hle : n+a ≤ n+a*b := by omega
    have hsub : (n+a*b) - (n+a) = a*b - a := by omega
    have habm : n+a*b ≡ n+a [MOD a] :=
      ((Nat.modEq_iff_dvd' hle).mpr (by
        rw [hsub]; exact Nat.dvd_sub (Nat.dvd_mul_right a b) (Nat.dvd_refl a))).symm
    have h2 : n+a*b-r ≡ n+a-r%a [MOD a] :=
      Nat.ModEq.sub (by omega) (by have := hra r; omega) habm (Nat.mod_modEq r a).symm
    exact h1.trans h2
  have hrefb : ∀ r : ℕ, r < a*b → ((n+a*b-r) % (a*b)) % b = (n+b-r%b) % b := by
    intro r hr
    have h1 : (n+a*b-r) % (a*b) ≡ n+a*b-r [MOD b] :=
      (Nat.mod_modEq (n+a*b-r) (a*b)).of_dvd (Nat.dvd_mul_left b a)
    have hle2 : b ≤ a*b := Nat.le_mul_of_pos_left b ha
    have hle : n+b ≤ n+a*b := by omega
    have hsub : (n+a*b) - (n+b) = a*b - b := by omega
    have habm : n+a*b ≡ n+b [MOD b] :=
      ((Nat.modEq_iff_dvd' hle).mpr (by
        rw [hsub]; exact Nat.dvd_sub (Nat.dvd_mul_left b a) (Nat.dvd_refl b))).symm
    have h2 : n+a*b-r ≡ n+b-r%b [MOD b] :=
      Nat.ModEq.sub (by omega) (by have := hrb r; omega) habm (Nat.mod_modEq r b).symm
    exact h1.trans h2
  -- condition transport under the CRT map
  have key : ∀ r : ℕ, r < a*b →
      ((r.Coprime (a*b) ∧ ((n+a*b-r) % (a*b)).Coprime (a*b) ↔
      ((r % a).Coprime a ∧ ((n+a-r%a) % a).Coprime a) ∧
      ((r % b).Coprime b ∧ ((n+b-r%b) % b).Coprime b))) := by
    intro r hr
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      rw [Nat.coprime_mul_iff_right] at h1 h2
      refine ⟨⟨(ZMod.coprime_mod_iff_coprime r a).mpr h1.1, ?_⟩, ⟨(ZMod.coprime_mod_iff_coprime r b).mpr h1.2, ?_⟩⟩
      · rw [← hrefa r hr]
        exact (ZMod.coprime_mod_iff_coprime _ a).mpr h2.1
      · rw [← hrefb r hr]
        exact (ZMod.coprime_mod_iff_coprime _ b).mpr h2.2
    · intro h
      obtain ⟨⟨e1, e3⟩, ⟨e2, e4⟩⟩ := h
      refine ⟨Nat.coprime_mul_iff_right.mpr ⟨(ZMod.coprime_mod_iff_coprime r a).mp e1,
        (ZMod.coprime_mod_iff_coprime r b).mp e2⟩, ?_⟩
      rw [Nat.coprime_mul_iff_right]
      refine ⟨(ZMod.coprime_mod_iff_coprime _ a).mp (by rw [hrefa r hr]; exact e3),
        (ZMod.coprime_mod_iff_coprime _ b).mp (by rw [hrefb r hr]; exact e4)⟩
  -- the CRT map is a bijection between the filtered sets and the product
  have hinj : Set.InjOn (fun r : ℕ => (r % a, r % b))
      ↑((Finset.range (a*b)).filter (fun r => r.Coprime (a*b) ∧ ((n+a*b-r) % (a*b)).Coprime (a*b))) := by
    intro r hr r' hr' hEq
    simp only [Finset.mem_filter, Finset.mem_coe, Finset.mem_range] at hr hr'
    have h1 : r % a = r' % a := congrArg Prod.fst hEq
    have h2 : r % b = r' % b := congrArg Prod.snd hEq
    have m1 : r ≡ r' [MOD a] := h1
    have m2 : r ≡ r' [MOD b] := h2
    have hiff := Nat.modEq_and_modEq_iff_modEq_mul (a := r) (b := r') hab
    have hm : r ≡ r' [MOD a*b] := hiff.mp ⟨m1, m2⟩
    exact Nat.ModEq.eq_of_lt_of_lt hm hr.1 hr'.1
  have himg : (((Finset.range (a*b)).filter (fun r => r.Coprime (a*b) ∧ ((n+a*b-r) % (a*b)).Coprime (a*b))).image
        (fun r => (r % a, r % b)))
      = ((Finset.range a).filter (fun r => r.Coprime a ∧ ((n+a-r) % a).Coprime a)) ×ˢ
        ((Finset.range b).filter (fun r => r.Coprime b ∧ ((n+b-r) % b).Coprime b)) := by
    ext p
    obtain ⟨x, y⟩ := p
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, Finset.mem_product]
    constructor
    · rintro ⟨r, ⟨hr1, hr2⟩, hxy⟩
      obtain ⟨hx, hy⟩ := Prod.mk.inj hxy
      obtain ⟨k1, k2⟩ := (key r hr1).mp hr2
      have hmA : r % a < a := hra r
      have hmB : r % b < b := hrb r
      exact ⟨⟨by omega, by rw [← hx]; exact k1⟩, ⟨by omega, by rw [← hy]; exact k2⟩⟩
    · intro hxy
      obtain ⟨hxA, hyB⟩ := hxy
      obtain ⟨hx1, hx2⟩ := hxA
      obtain ⟨hy1, hy2⟩ := hyB
      have hcrt : (Nat.chineseRemainder hab x y : ℕ) < a*b :=
        Nat.chineseRemainder_lt_mul hab x y (ne_of_gt ha) (ne_of_gt hb)
      have hpx : (Nat.chineseRemainder hab x y : ℕ) % a = x := by
        have h : (Nat.chineseRemainder hab x y : ℕ) % a = x % a :=
          (Nat.chineseRemainder hab x y).prop.1
        rwa [Nat.mod_eq_of_lt hx1] at h
      have hpy : (Nat.chineseRemainder hab x y : ℕ) % b = y := by
        have h : (Nat.chineseRemainder hab x y : ℕ) % b = y % b :=
          (Nat.chineseRemainder hab x y).prop.2
        rwa [Nat.mod_eq_of_lt hy1] at h
      refine ⟨Nat.chineseRemainder hab x y, ⟨hcrt, ?_⟩, ?_⟩
      · exact (key _ hcrt).mpr ⟨by rw [hpx]; exact hx2, by rw [hpy]; exact hy2⟩
      · rw [hpx, hpy]
  have hcard : ((Finset.range (a*b)).filter (fun r => r.Coprime (a*b) ∧ ((n+a*b-r) % (a*b)).Coprime (a*b))).card
      = (((Finset.range a).filter (fun r => r.Coprime a ∧ ((n+a-r) % a).Coprime a)) ×ˢ
        ((Finset.range b).filter (fun r => r.Coprime b ∧ ((n+b-r) % b).Coprime b))).card := by
    rw [← himg, Finset.card_image_of_injOn hinj]
  rw [hcard, Finset.card_product]
