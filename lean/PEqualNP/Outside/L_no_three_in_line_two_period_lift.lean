import Mathlib

private def hh (p : ℕ) : ℕ := (p - 1) / 2

private def invmod (p x : ℕ) : ℕ := ((x : ZMod p)⁻¹).val

private def xb (p x : ℕ) : ℤ := if x ≤ hh p then (x : ℤ) else (x : ℤ) - p

private def dropI (p x : ℕ) : ℕ := if x ≤ hh p then 0 else 1

private def dropJ (p y : ℕ) : ℕ := if hh p < y then 0 else 1

private def gX (p x i : ℕ) : ℕ :=
  if x ≤ hh p then x + hh p + i * p else x - hh p - 1 + i * p

private def gY (p y j : ℕ) : ℕ := y + j * p

private lemma p_eq (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) : p = 2 * hh p + 1 := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hodd
  have h1 : p - 1 = 2 * k := by omega
  have h2 : hh p = k := by
    rw [hh, h1, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  omega

private lemma hh_pos (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) : 0 < hh p := by
  have h := p_eq p hp hp2
  omega

private lemma natCast_ne_zero (p x : ℕ) (hp2 : 2 < p) (hx1 : 1 ≤ x) (hx2 : x ≤ p - 1) :
    (x : ZMod p) ≠ 0 := by
  intro h0
  rw [ZMod.natCast_eq_zero_iff] at h0
  rcases Nat.eq_zero_or_pos x with h | h
  · omega
  · have hle := Nat.le_of_dvd h h0
    omega

private lemma invmod_ne_zero (p x : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hx1 : 1 ≤ x) (hx2 : x ≤ p - 1) : invmod p x ≠ 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨by omega⟩
  have hxne := natCast_ne_zero p x hp2 hx1 hx2
  have h : ((invmod p x : ℕ) : ZMod p) = (x : ZMod p)⁻¹ := by
    unfold invmod
    exact ZMod.natCast_zmod_val _
  have hne : ((invmod p x : ℕ) : ZMod p) ≠ 0 := by
    rw [h]
    exact inv_ne_zero hxne
  intro h0
  apply hne
  rw [h0]
  simp

private lemma invmod_lt (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (x : ℕ) : invmod p x < p := by
  haveI : NeZero p := ⟨by omega⟩
  unfold invmod
  exact ZMod.val_lt _

private lemma invmod_bounds (p x : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hx1 : 1 ≤ x) (hx2 : x ≤ p - 1) : 1 ≤ invmod p x ∧ invmod p x ≤ p - 1 := by
  have hlt := invmod_lt p hp hp2 x
  have hne := invmod_ne_zero p x hp hp2 hx1 hx2
  omega

private lemma invmod_mul (p x : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hx1 : 1 ≤ x) (hx2 : x ≤ p - 1) :
    (x : ZMod p) * ((invmod p x : ℕ) : ZMod p) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨by omega⟩
  have hxne := natCast_ne_zero p x hp2 hx1 hx2
  have h : ((invmod p x : ℕ) : ZMod p) = (x : ZMod p)⁻¹ := by
    unfold invmod
    exact ZMod.natCast_zmod_val _
  rw [h]
  exact mul_inv_cancel₀ hxne

private lemma p_cast (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) : (p : ℤ) = 2 * (hh p : ℤ) + 1 := by
  have h := p_eq p hp hp2
  exact_mod_cast h

private lemma xb_bounds (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (x : ℕ)
    (hx1 : 1 ≤ x) (hx2 : x ≤ p - 1) :
    -((hh p : ℤ)) ≤ xb p x ∧ xb p x ≤ (hh p : ℤ) := by
  unfold xb
  split_ifs with h
  · have h2 : (x : ℤ) ≤ (hh p : ℤ) := by exact_mod_cast h
    constructor <;> omega
  · have hpe := p_cast p hp hp2
    constructor <;> omega

private lemma gX_eq (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (x i : ℕ) (hi : i ≤ 1) :
    (gX p x i : ℤ) = xb p x + (i : ℤ) * (p : ℤ) + (hh p : ℤ) := by
  unfold gX xb
  split_ifs with hx
  · push_cast
    ring
  · have hx' : hh p + 1 ≤ x := by omega
    have hsub : x - hh p - 1 = x - (hh p + 1) := by omega
    rw [hsub, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hx']
    push_cast
    have hpe := p_cast p hp hp2
    rw [hpe]
    ring

private lemma gX_lt (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (x i : ℕ)
    (hx1 : 1 ≤ x) (hx2 : x ≤ p - 1) (hi : i ≤ 1) : gX p x i < 2 * p := by
  unfold gX
  have hpe := p_eq p hp hp2
  have hi2 : i < 2 := by omega
  interval_cases i <;> split_ifs <;> omega

private lemma gY_lt (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (y j : ℕ)
    (hy2 : y ≤ p - 1) (hj : j ≤ 1) : gY p y j < 2 * p := by
  unfold gY
  have hpe := p_eq p hp hp2
  have hj2 : j < 2 := by omega
  interval_cases j <;> omega

private lemma gX_inj (p x x' i i' : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hx1 : 1 ≤ x) (hx2 : x ≤ p - 1) (hx1' : 1 ≤ x') (hx2' : x' ≤ p - 1)
    (hi : i ≤ 1) (hi' : i' ≤ 1) (heq : gX p x i = gX p x' i') : x = x' ∧ i = i' := by
  have e1 := gX_eq p hp hp2 x i hi
  have e2 := gX_eq p hp hp2 x' i' hi'
  have hcast : (gX p x i : ℤ) = (gX p x' i') := by exact_mod_cast heq
  have hrel : xb p x + (i : ℤ) * (p : ℤ) = xb p x' + (i' : ℤ) * (p : ℤ) := by omega
  have hi2 : i < 2 := by omega
  have hi2' : i' < 2 := by omega
  by_cases hx : x ≤ hh p <;> by_cases hx' : x' ≤ hh p
  · have hb1 : xb p x = (x : ℤ) := by simp [xb, hx]
    have hb2 : xb p x' = (x' : ℤ) := by simp [xb, hx']
    rw [hb1, hb2] at hrel
    interval_cases i <;> interval_cases i' <;> simp at hrel <;> omega
  · have hb1 : xb p x = (x : ℤ) := by simp [xb, hx]
    have hb2 : xb p x' = (x' : ℤ) - (p : ℤ) := by simp [xb, hx']
    rw [hb1, hb2] at hrel
    have hpe := p_cast p hp hp2
    interval_cases i <;> interval_cases i' <;> simp at hrel <;> omega
  · have hb1 : xb p x = (x : ℤ) - (p : ℤ) := by simp [xb, hx]
    have hb2 : xb p x' = (x' : ℤ) := by simp [xb, hx']
    rw [hb1, hb2] at hrel
    have hpe := p_cast p hp hp2
    interval_cases i <;> interval_cases i' <;> simp at hrel <;> omega
  · have hb1 : xb p x = (x : ℤ) - (p : ℤ) := by simp [xb, hx]
    have hb2 : xb p x' = (x' : ℤ) - (p : ℤ) := by simp [xb, hx']
    rw [hb1, hb2] at hrel
    have hpe := p_cast p hp hp2
    interval_cases i <;> interval_cases i' <;> simp at hrel <;> omega

private def cornerSet (p x : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range 2) ×ˢ (Finset.range 2)).erase (dropI p x, dropJ p (invmod p x))

private def Params (p : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (Finset.Icc 1 (p - 1)).biUnion (fun x => (cornerSet p x).image (fun c => (x, c.1, c.2)))

private def Sset (p : ℕ) : Finset (ℕ × ℕ) :=
  (Params p).image (fun t => (gX p t.1 t.2.1, gY p (invmod p t.1) t.2.2))

private lemma mem_cornerSet {p x a b : ℕ} :
    (a, b) ∈ cornerSet p x ↔
      (a, b) ≠ (dropI p x, dropJ p (invmod p x)) ∧ a < 2 ∧ b < 2 := by
  unfold cornerSet
  rw [Finset.mem_erase, Finset.mem_product, Finset.mem_range, Finset.mem_range]

private lemma cornerSet_subset (p x : ℕ) : cornerSet p x ⊆ (Finset.range 2) ×ˢ (Finset.range 2) := by
  intro a ha
  rw [mem_cornerSet] at ha
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
  exact ⟨ha.2.1, ha.2.2⟩

private lemma cornerSet_card (p x : ℕ) :
    (cornerSet p x).card = 3 := by
  have h4 : (((Finset.range 2) ×ˢ (Finset.range 2)) : Finset (ℕ × ℕ)).card = 4 := by
    rw [Finset.card_product, Finset.card_range]
  have hmem : (dropI p x, dropJ p (invmod p x)) ∈ ((Finset.range 2) ×ˢ (Finset.range 2)) := by
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have h1 : dropI p x < 2 := by unfold dropI; split_ifs <;> omega
    have h2 : dropJ p (invmod p x) < 2 := by unfold dropJ; split_ifs <;> omega
    exact ⟨h1, h2⟩
  unfold cornerSet
  rw [Finset.card_erase_of_mem hmem, h4]

private lemma Params_card (p : ℕ) : (Params p).card = 3 * (p - 1) := by
  unfold Params
  rw [Finset.card_biUnion]
  · have himg : ∀ x ∈ Finset.Icc 1 (p - 1),
        ((cornerSet p x).image (fun c => (x, c.1, c.2))).card = 3 := by
      intro x _
      rw [Finset.card_image_of_injOn]
      · exact cornerSet_card p x
      · intro a _ b _ hab
        simp only [Prod.mk.injEq] at hab
        exact Prod.ext hab.2.1 hab.2.2
    calc ∑ x ∈ Finset.Icc 1 (p - 1), ((cornerSet p x).image (fun c => (x, c.1, c.2))).card
        = ∑ x ∈ Finset.Icc 1 (p - 1), 3 := Finset.sum_congr rfl himg
      _ = (Finset.Icc 1 (p - 1)).card * 3 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          exact Nat.cast_id _
      _ = 3 * (p - 1) := by
          rw [Nat.card_Icc]
          omega
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨c1, _, h1⟩ := ha
    obtain ⟨c2, _, h2⟩ := hb
    apply hxy
    have h3 : (x, c1.1, c1.2) = (y, c2.1, c2.2) := by rw [h1, h2]
    exact (Prod.ext_iff.mp h3).1

private lemma mem_Params {p : ℕ} {t : ℕ × ℕ × ℕ} :
    t ∈ Params p ↔ t.1 ∈ Finset.Icc 1 (p - 1) ∧ (t.2.1, t.2.2) ∈ cornerSet p t.1 := by
  constructor
  · intro ht
    unfold Params at ht
    rw [Finset.mem_biUnion] at ht
    obtain ⟨x, hx, ht2⟩ := ht
    rw [Finset.mem_image] at ht2
    obtain ⟨c, hc, hct⟩ := ht2
    rw [← hct]
    exact ⟨hx, hc⟩
  · intro ⟨hx, hc⟩
    unfold Params
    rw [Finset.mem_biUnion]
    exact ⟨t.1, hx, Finset.mem_image.mpr ⟨(t.2.1, t.2.2), hc, rfl⟩⟩

private lemma Params_allowed {p : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ Params p) :
    t.2.1 ≠ dropI p t.1 ∨ t.2.2 ≠ dropJ p (invmod p t.1) := by
  have h := (mem_Params.mp ht).2
  rw [mem_cornerSet] at h
  have hpair : ¬(t.2.1 = dropI p t.1 ∧ t.2.2 = dropJ p (invmod p t.1)) := by
    intro hc
    exact h.1 (Prod.ext hc.1 hc.2)
  exact not_and_or.mp hpair

private lemma Params_x_bounds {p : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ Params p) :
    1 ≤ t.1 ∧ t.1 ≤ p - 1 := by
  have h := (mem_Params.mp ht).1
  rw [Finset.mem_Icc] at h
  exact h

private lemma Params_ij_lt {p : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ Params p) :
    t.2.1 < 2 ∧ t.2.2 < 2 := by
  have h := (mem_Params.mp ht).2
  rw [mem_cornerSet] at h
  exact ⟨h.2.1, h.2.2⟩

private lemma xb_cast (p x : ℕ) : ((xb p x : ℤ) : ZMod p) = (x : ZMod p) := by
  unfold xb
  split_ifs with h
  · push_cast
    ring
  · push_cast
    rw [ZMod.natCast_self]
    ring

private lemma zmod_nat_eq_of_eq {p a b : ℕ} (hp : 0 < p) (h : (a : ZMod p) = (b : ZMod p))
    (ha : a < p) (hb : b < p) : a = b := by
  have h1 : a % p = b % p := by
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, ZMod.val_natCast] at this
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  exact h1

private lemma xb_inj (p u x : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (hu : u < p) (hx : x < p) (h : xb p u = xb p x) : u = x := by
  have hp0 : 0 < p := by omega
  have hcast : ((xb p u : ℤ) : ZMod p) = ((xb p x : ℤ) : ZMod p) := by rw [h]
  rw [xb_cast, xb_cast] at hcast
  exact zmod_nat_eq_of_eq hp0 hcast hu hx

private def det3 (a b c : ℕ × ℕ) : ℤ :=
  ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) - ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))

private lemma det3_cyclic (a b c : ℕ × ℕ) : det3 a b c = det3 b c a := by
  unfold det3
  ring

private lemma det3_swap (a b c : ℕ × ℕ) : det3 a c b = - det3 a b c := by
  unfold det3
  ring

private lemma field_identity (p : ℕ) (hp : p.Prime)
    (x1 x2 x3 y1 y2 y3 : ZMod p)
    (e1 : x1 * y1 = 1) (e2 : x2 * y2 = 1) (e3 : x3 * y3 = 1)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hdet : (x2 - x1) * (y3 - y1) = (y2 - y1) * (x3 - x1)) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1x : x1 ≠ 0 := by rintro rfl; simpa using e1
  have h2x : x2 ≠ 0 := by rintro rfl; simpa using e2
  have h3x : x3 ≠ 0 := by rintro rfl; simpa using e3
  have hy1 : y1 = x1⁻¹ := eq_inv_of_mul_eq_one_right e1
  have hy2 : y2 = x2⁻¹ := eq_inv_of_mul_eq_one_right e2
  have hy3 : y3 = x3⁻¹ := eq_inv_of_mul_eq_one_right e3
  rw [hy1, hy2, hy3] at hdet
  have hkey : (x2 - x1) * (x3⁻¹ - x1⁻¹) * (x1 * x2 * x3)
      - (x2⁻¹ - x1⁻¹) * (x3 - x1) * (x1 * x2 * x3) = (x1 - x2) * (x3 - x1) * (x2 - x3) := by
    field_simp
    ring
  have hzero : (x1 - x2) * (x3 - x1) * (x2 - x3) = 0 := by
    rw [← hkey, hdet]
    ring
  have hne1 : x1 - x2 ≠ 0 := sub_ne_zero.mpr h12
  have hne2 : x3 - x1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h13)
  have hne3 : x2 - x3 ≠ 0 := sub_ne_zero.mpr h23
  exact (mul_ne_zero (mul_ne_zero hne1 hne2) hne3) hzero

private lemma refl_diff (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (x y u v : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ p - 1) (hu1 : 1 ≤ u) (hu2 : u ≤ p - 1)
    (hy1 : 1 ≤ y) (hy2 : y ≤ p - 1) (hv1 : 1 ≤ v) (hv2 : v ≤ p - 1)
    (e1 : (x : ZMod p) * (y : ZMod p) = 1) (e2 : (u : ZMod p) * (v : ZMod p) = 1)
    (hne : u ≠ x)
    (h : (y : ZMod p) - (x : ZMod p) = (v : ZMod p) - (u : ZMod p)) :
    u = p - y ∧ v = p - x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx0 : (x : ZMod p) ≠ 0 := natCast_ne_zero p x hp2 hx1 hx2
  have hu0 : (u : ZMod p) ≠ 0 := natCast_ne_zero p u hp2 hu1 hu2
  have hY : ((y : ZMod p)) = (x : ZMod p)⁻¹ := eq_inv_of_mul_eq_one_right e1
  have hV : ((v : ZMod p)) = (u : ZMod p)⁻¹ := eq_inv_of_mul_eq_one_right e2
  have hne' : (u : ZMod p) ≠ (x : ZMod p) := by
    intro hh
    exact hne (zmod_nat_eq_of_eq (by omega : 0 < p) hh (by omega) (by omega))
  rw [hY, hV] at h
  have hfac : ((u : ZMod p) - (x : ZMod p)) * (1 + (x : ZMod p) * (u : ZMod p)) = 0 := by
    field_simp at h
    linear_combination h
  have hxu : (x : ZMod p) * (u : ZMod p) = -1 := by
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hne'
    · linear_combination h1
  have hu_neg : (u : ZMod p) = -((y : ZMod p)) := by
    have hthis : (u : ZMod p) = -((x : ZMod p)⁻¹) := by
      have h2 := congrArg (fun t => (x : ZMod p)⁻¹ * t) hxu
      simpa [← mul_assoc, inv_mul_cancel₀ hx0] using h2
    rw [hY]
    exact hthis
  have hv_neg : (v : ZMod p) = -((x : ZMod p)) := by
    rw [hV, hu_neg, ← neg_inv, hY, inv_inv]
  constructor
  · have hnat : (u : ZMod p) = ((p - y : ℕ) : ZMod p) := by
      rw [hu_neg, Nat.cast_sub (by omega : y ≤ p)]
      rw [ZMod.natCast_self]
      ring
    exact zmod_nat_eq_of_eq (by omega : 0 < p) hnat (by omega) (by omega)
  · have hnat : (v : ZMod p) = ((p - x : ℕ) : ZMod p) := by
      rw [hv_neg, Nat.cast_sub (by omega : x ≤ p)]
      rw [ZMod.natCast_self]
      ring
    exact zmod_nat_eq_of_eq (by omega : 0 < p) hnat (by omega) (by omega)

private lemma refl_sum (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (x y u v : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ p - 1) (hu1 : 1 ≤ u) (hu2 : u ≤ p - 1)
    (hy1 : 1 ≤ y) (hy2 : y ≤ p - 1) (hv1 : 1 ≤ v) (hv2 : v ≤ p - 1)
    (e1 : (x : ZMod p) * (y : ZMod p) = 1) (e2 : (u : ZMod p) * (v : ZMod p) = 1)
    (hne : u ≠ x)
    (h : (y : ZMod p) + (x : ZMod p) = (v : ZMod p) + (u : ZMod p)) :
    u = y ∧ v = x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hx0 : (x : ZMod p) ≠ 0 := natCast_ne_zero p x hp2 hx1 hx2
  have hu0 : (u : ZMod p) ≠ 0 := natCast_ne_zero p u hp2 hu1 hu2
  have hY : ((y : ZMod p)) = (x : ZMod p)⁻¹ := eq_inv_of_mul_eq_one_right e1
  have hV : ((v : ZMod p)) = (u : ZMod p)⁻¹ := eq_inv_of_mul_eq_one_right e2
  have hne' : (u : ZMod p) ≠ (x : ZMod p) := by
    intro hh
    exact hne (zmod_nat_eq_of_eq (by omega : 0 < p) hh (by omega) (by omega))
  rw [hY, hV] at h
  have hfac : ((u : ZMod p) - (x : ZMod p)) * (1 - (x : ZMod p) * (u : ZMod p)) = 0 := by
    field_simp at h
    linear_combination h
  have hxu : (x : ZMod p) * (u : ZMod p) = 1 := by
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hne'
    · linear_combination -h1
  have hu_eq : (u : ZMod p) = (y : ZMod p) := by
    rw [eq_inv_of_mul_eq_one_right hxu, ← hY]
  have hv_eq : (v : ZMod p) = (x : ZMod p) := by
    rw [hV, hu_eq, hY, inv_inv]
  constructor
  · exact zmod_nat_eq_of_eq (by omega : 0 < p) hu_eq (by omega) (by omega)
  · exact zmod_nat_eq_of_eq (by omega : 0 < p) hv_eq (by omega) (by omega)

private lemma moddet (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (x1 i1 j1 x2 i2 j2 x3 i3 j3 : ℕ)
    (h1 : (x1, i1, j1) ∈ Params p) (h2 : (x2, i2, j2) ∈ Params p) (h3 : (x3, i3, j3) ∈ Params p)
    (hcol : det3 (gX p x1 i1, gY p (invmod p x1) j1)
                 (gX p x2 i2, gY p (invmod p x2) j2)
                 (gX p x3 i3, gY p (invmod p x3) j3) = 0) :
    ((x2 : ZMod p) - (x1 : ZMod p)) * ((invmod p x3 : ZMod p) - (invmod p x1 : ZMod p))
      = ((invmod p x2 : ZMod p) - (invmod p x1 : ZMod p)) * ((x3 : ZMod p) - (x1 : ZMod p)) := by
  have b1 := Params_x_bounds h1
  have b2 := Params_x_bounds h2
  have b3 := Params_x_bounds h3
  have qi1 : i1 < 2 := by simpa using (Params_ij_lt h1).1
  have qj1 : j1 < 2 := by simpa using (Params_ij_lt h1).2
  have qi2 : i2 < 2 := by simpa using (Params_ij_lt h2).1
  have qj2 : j2 < 2 := by simpa using (Params_ij_lt h2).2
  have qi3 : i3 < 2 := by simpa using (Params_ij_lt h3).1
  have qj3 : j3 < 2 := by simpa using (Params_ij_lt h3).2
  have e1 : (gX p x1 i1 : ℤ) = xb p x1 + (i1 : ℤ) * (p : ℤ) + (hh p : ℤ) := gX_eq p hp hp2 x1 i1 (by omega)
  have e2 : (gX p x2 i2 : ℤ) = xb p x2 + (i2 : ℤ) * (p : ℤ) + (hh p : ℤ) := gX_eq p hp hp2 x2 i2 (by omega)
  have e3 : (gX p x3 i3 : ℤ) = xb p x3 + (i3 : ℤ) * (p : ℤ) + (hh p : ℤ) := gX_eq p hp hp2 x3 i3 (by omega)
  have f1 : (gY p (invmod p x1) j1 : ℤ) = (invmod p x1 : ℤ) + (j1 : ℤ) * (p : ℤ) := by unfold gY; push_cast; ring
  have f2 : (gY p (invmod p x2) j2 : ℤ) = (invmod p x2 : ℤ) + (j2 : ℤ) * (p : ℤ) := by unfold gY; push_cast; ring
  have f3 : (gY p (invmod p x3) j3 : ℤ) = (invmod p x3 : ℤ) + (j3 : ℤ) * (p : ℤ) := by unfold gY; push_cast; ring
  have hZ := congrArg (fun z : ℤ => (z : ZMod p)) hcol
  unfold det3 at hZ
  rw [e1, e2, e3, f1, f2, f3] at hZ
  push_cast at hZ
  simp only [ZMod.natCast_self, mul_zero, add_zero] at hZ
  rw [xb_cast, xb_cast, xb_cast] at hZ
  linear_combination hZ

private lemma xb_of_le (p x : ℕ) (h : x ≤ hh p) : xb p x = (x : ℤ) := by simp [xb, h]

private lemma xb_of_gt (p x : ℕ) (h : hh p < x) : xb p x = (x : ℤ) - (p : ℤ) := by
  simp [xb, show ¬ x ≤ hh p by omega]

private lemma dropI_of_le (p x : ℕ) (h : x ≤ hh p) : dropI p x = 0 := by simp [dropI, h]

private lemma dropI_of_gt (p x : ℕ) (h : hh p < x) : dropI p x = 1 := by
  simp [dropI, show ¬ x ≤ hh p by omega]

private lemma dropJ_of_lt (p y : ℕ) (h : hh p < y) : dropJ p y = 0 := by simp [dropJ, h]

private lemma dropJ_of_ge (p y : ℕ) (h : y ≤ hh p) : dropJ p y = 1 := by
  simp [dropJ, show ¬ hh p < y by omega]

private lemma corners_det_ne (i1 j1 i2 j2 i3 j3 : Fin 2)
    (h12 : (i1, j1) ≠ (i2, j2)) (h13 : (i1, j1) ≠ (i3, j3)) (h23 : (i2, j2) ≠ (i3, j3)) :
    (((i2 : ℤ) - (i1 : ℤ)) * ((j3 : ℤ) - (j1 : ℤ)) - ((j2 : ℤ) - (j1 : ℤ)) * ((i3 : ℤ) - (i1 : ℤ))) ≠ 0 := by
  revert i1 j1 i2 j2 i3 j3 h12 h13 h23
  decide

private lemma same_class_not_col (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (x i1 j1 i2 j2 i3 j3 : ℕ)
    (h1 : (x, i1, j1) ∈ Params p) (h2 : (x, i2, j2) ∈ Params p) (h3 : (x, i3, j3) ∈ Params p)
    (h12 : (i1, j1) ≠ (i2, j2)) (h13 : (i1, j1) ≠ (i3, j3)) (h23 : (i2, j2) ≠ (i3, j3))
    (hcol : det3 (gX p x i1, gY p (invmod p x) j1) (gX p x i2, gY p (invmod p x) j2)
      (gX p x i3, gY p (invmod p x) j3) = 0) : False := by
  have qi1 : i1 < 2 := by simpa using (Params_ij_lt h1).1
  have qj1 : j1 < 2 := by simpa using (Params_ij_lt h1).2
  have qi2 : i2 < 2 := by simpa using (Params_ij_lt h2).1
  have qj2 : j2 < 2 := by simpa using (Params_ij_lt h2).2
  have qi3 : i3 < 2 := by simpa using (Params_ij_lt h3).1
  have qj3 : j3 < 2 := by simpa using (Params_ij_lt h3).2
  have e1 : (gX p x i1 : ℤ) = xb p x + (i1 : ℤ) * (p : ℤ) + (hh p : ℤ) := gX_eq p hp hp2 x i1 (by omega)
  have e2 : (gX p x i2 : ℤ) = xb p x + (i2 : ℤ) * (p : ℤ) + (hh p : ℤ) := gX_eq p hp hp2 x i2 (by omega)
  have e3 : (gX p x i3 : ℤ) = xb p x + (i3 : ℤ) * (p : ℤ) + (hh p : ℤ) := gX_eq p hp hp2 x i3 (by omega)
  have f1 : (gY p (invmod p x) j1 : ℤ) = (invmod p x : ℤ) + (j1 : ℤ) * (p : ℤ) := by unfold gY; push_cast; ring
  have f2 : (gY p (invmod p x) j2 : ℤ) = (invmod p x : ℤ) + (j2 : ℤ) * (p : ℤ) := by unfold gY; push_cast; ring
  have f3 : (gY p (invmod p x) j3 : ℤ) = (invmod p x : ℤ) + (j3 : ℤ) * (p : ℤ) := by unfold gY; push_cast; ring
  have hfac : (p : ℤ) * (p : ℤ) * (((i2 : ℤ) - (i1 : ℤ)) * ((j3 : ℤ) - (j1 : ℤ))
      - ((j2 : ℤ) - (j1 : ℤ)) * ((i3 : ℤ) - (i1 : ℤ))) = 0 := by
    unfold det3 at hcol
    rw [e1, e2, e3, f1, f2, f3] at hcol
    linear_combination hcol
  have hpz : (p : ℤ) ≠ 0 := by omega
  have hAD : ((i2 : ℤ) - (i1 : ℤ)) * ((j3 : ℤ) - (j1 : ℤ))
      = ((j2 : ℤ) - (j1 : ℤ)) * ((i3 : ℤ) - (i1 : ℤ)) := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd h (mul_ne_zero hpz hpz)
    · linear_combination h
  have n12 : i1 ≠ i2 ∨ j1 ≠ j2 := by
    by_contra h
    push_neg at h
    exact h12 (Prod.ext h.1 h.2)
  have n13 : i1 ≠ i3 ∨ j1 ≠ j3 := by
    by_contra h
    push_neg at h
    exact h13 (Prod.ext h.1 h.2)
  have n23 : i2 ≠ i3 ∨ j2 ≠ j3 := by
    by_contra h
    push_neg at h
    exact h23 (Prod.ext h.1 h.2)
  rcases n12 with h12i | h12j <;> rcases n13 with h13i | h13j <;> rcases n23 with h23i | h23j <;>
    interval_cases i1 <;> interval_cases j1 <;> interval_cases i2 <;> interval_cases j2 <;>
    interval_cases i3 <;> interval_cases j3 <;> omega

private lemma corner_ne_of_ne (p x i1 j1 i2 j2 : ℕ)
    (h : (gX p x i1, gY p (invmod p x) j1) ≠ (gX p x i2, gY p (invmod p x) j2)) :
    (i1, j1) ≠ (i2, j2) := by
  intro hc
  apply h
  simp only [Prod.mk.injEq] at hc
  rw [hc.1, hc.2]


private lemma idx_of_sub_one (a b : ℕ) (ha : a < 2) (hb : b < 2) (h : ((b : ℤ) - (a : ℤ)) = 1) :
    a = 0 ∧ b = 1 := by omega

private lemma idx_of_sub_neg_one (a b : ℕ) (ha : a < 2) (hb : b < 2) (h : ((b : ℤ) - (a : ℤ)) = -1) :
    a = 1 ∧ b = 0 := by omega

set_option maxHeartbeats 4000000 in
private lemma two_same (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (x i1 j1 i2 j2 u i3 j3 : ℕ)
    (h1 : (x, i1, j1) ∈ Params p) (h2 : (x, i2, j2) ∈ Params p) (h3 : (u, i3, j3) ∈ Params p)
    (hxu : u ≠ x)
    (hdist : (gX p x i1, gY p (invmod p x) j1) ≠ (gX p x i2, gY p (invmod p x) j2))
    (hcol : det3 (gX p x i1, gY p (invmod p x) j1) (gX p x i2, gY p (invmod p x) j2)
      (gX p u i3, gY p (invmod p u) j3) = 0) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpe : p = 2 * hh p + 1 := p_eq p hp hp2
  obtain ⟨hxl, hxh⟩ := Params_x_bounds h1
  obtain ⟨hul, huh⟩ := Params_x_bounds h3
  obtain ⟨hyl, hyh⟩ := invmod_bounds p x hp hp2 hxl hxh
  obtain ⟨hvl, hvh⟩ := invmod_bounds p u hp hp2 hul huh
  have qi1 : i1 < 2 := by simpa using (Params_ij_lt h1).1
  have qj1 : j1 < 2 := by simpa using (Params_ij_lt h1).2
  have qi2 : i2 < 2 := by simpa using (Params_ij_lt h2).1
  have qj2 : j2 < 2 := by simpa using (Params_ij_lt h2).2
  have qi3 : i3 < 2 := by simpa using (Params_ij_lt h3).1
  have qj3 : j3 < 2 := by simpa using (Params_ij_lt h3).2
  have hyx : (x : ZMod p) * (invmod p x : ZMod p) = 1 := invmod_mul p x hp hp2 hxl hxh
  have hyu : (u : ZMod p) * (invmod p u : ZMod p) = 1 := invmod_mul p u hp hp2 hul huh
  have hcorn : (i1, j1) ≠ (i2, j2) := corner_ne_of_ne p x i1 j1 i2 j2 hdist
  have e1 : (gX p x i1 : ℤ) = xb p x + (i1 : ℤ) * (p : ℤ) + (hh p : ℤ) := gX_eq p hp hp2 x i1 (by omega)
  have e2 : (gX p x i2 : ℤ) = xb p x + (i2 : ℤ) * (p : ℤ) + (hh p : ℤ) := gX_eq p hp hp2 x i2 (by omega)
  have e3 : (gX p u i3 : ℤ) = xb p u + (i3 : ℤ) * (p : ℤ) + (hh p : ℤ) := gX_eq p hp hp2 u i3 (by omega)
  have f1 : (gY p (invmod p x) j1 : ℤ) = (invmod p x : ℤ) + (j1 : ℤ) * (p : ℤ) := by unfold gY; push_cast; ring
  have f2 : (gY p (invmod p x) j2 : ℤ) = (invmod p x : ℤ) + (j2 : ℤ) * (p : ℤ) := by unfold gY; push_cast; ring
  have f3 : (gY p (invmod p u) j3 : ℤ) = (invmod p u : ℤ) + (j3 : ℤ) * (p : ℤ) := by unfold gY; push_cast; ring
  have hpz : (p : ℤ) ≠ 0 := by omega
  have hexp : ((gX p x i2 : ℤ) - (gX p x i1 : ℤ)) * ((gY p (invmod p u) j3 : ℤ) - (gY p (invmod p x) j1 : ℤ))
      = ((gY p (invmod p x) j2 : ℤ) - (gY p (invmod p x) j1 : ℤ)) * ((gX p u i3 : ℤ) - (gX p x i1 : ℤ)) := by
    unfold det3 at hcol
    linarith [hcol]
  have hmain : ((i2 : ℤ) - (i1 : ℤ)) * ((invmod p u : ℤ) - (invmod p x : ℤ))
      - ((j2 : ℤ) - (j1 : ℤ)) * (xb p u - xb p x)
      = (p : ℤ) * (((j2 : ℤ) - (j1 : ℤ)) * ((i3 : ℤ) - (i1 : ℤ))
          - ((i2 : ℤ) - (i1 : ℤ)) * ((j3 : ℤ) - (j1 : ℤ))) := by
    have hfac : (p : ℤ) * (((i2 : ℤ) - (i1 : ℤ)) * ((invmod p u : ℤ) - (invmod p x : ℤ)
        + ((j3 : ℤ) - (j1 : ℤ)) * (p : ℤ))
        - ((j2 : ℤ) - (j1 : ℤ)) * (xb p u - xb p x + ((i3 : ℤ) - (i1 : ℤ)) * (p : ℤ))) = 0 := by
      rw [e1, e2, e3, f1, f2, f3] at hexp
      linear_combination hexp
    have hE := (mul_eq_zero.mp hfac).resolve_left hpz
    linear_combination hE
  by_cases hii : i1 = i2
  · have hA0 : ((i2 : ℤ) - (i1 : ℤ)) = 0 := by rw [hii]; ring
    rw [hA0] at hmain
    have hjj : j1 ≠ j2 := by
      intro h
      exact hcorn (by rw [hii, h])
    have hBne : ((j2 : ℤ) - (j1 : ℤ)) ≠ 0 := by
      intro h
      apply hjj
      omega
    have hxrel : xb p u - xb p x = -((p : ℤ) * ((i3 : ℤ) - (i1 : ℤ))) := by
      have h3 : ((j2 : ℤ) - (j1 : ℤ)) * (xb p u - xb p x)
          = ((j2 : ℤ) - (j1 : ℤ)) * (-((p : ℤ) * ((i3 : ℤ) - (i1 : ℤ)))) := by
        linear_combination -hmain
      exact mul_left_cancel₀ hBne h3
    have hbu := xb_bounds p hp hp2 u hul huh
    have hbx := xb_bounds p hp hp2 x hxl hxh
    have hpe := p_cast p hp hp2
    have hxb_eq : xb p u = xb p x := by
      interval_cases i1 <;> interval_cases i3 <;> omega
    exact hxu (xb_inj p u x hp hp2 (by omega) (by omega) hxb_eq)
  · by_cases hjj : j1 = j2
    · have hB0 : ((j2 : ℤ) - (j1 : ℤ)) = 0 := by rw [hjj]; ring
      rw [hB0] at hmain
      have hAne : ((i2 : ℤ) - (i1 : ℤ)) ≠ 0 := by
        intro h
        apply hii
        omega
      have hyrel : (invmod p u : ℤ) - (invmod p x : ℤ) = -((p : ℤ) * ((j3 : ℤ) - (j1 : ℤ))) := by
        have h3 : ((i2 : ℤ) - (i1 : ℤ)) * ((invmod p u : ℤ) - (invmod p x : ℤ))
            = ((i2 : ℤ) - (i1 : ℤ)) * (-((p : ℤ) * ((j3 : ℤ) - (j1 : ℤ)))) := by
          linear_combination hmain
        exact mul_left_cancel₀ hAne h3
      have hy_eq : invmod p u = invmod p x := by
        interval_cases j1 <;> interval_cases j3 <;> omega
      have hux : (u : ZMod p) = (x : ZMod p) := by
        have hsub : ((u : ZMod p) - (x : ZMod p)) * ((invmod p x : ℕ) : ZMod p) = 0 := by
          have h5 : (u : ZMod p) * ((invmod p x : ℕ) : ZMod p) = 1 := by
            rw [← hy_eq]; exact hyu
          calc ((u : ZMod p) - (x : ZMod p)) * ((invmod p x : ℕ) : ZMod p)
              = (u : ZMod p) * ((invmod p x : ℕ) : ZMod p) - (x : ZMod p) * ((invmod p x : ℕ) : ZMod p) := by ring
            _ = 1 - 1 := by rw [h5, hyx]
            _ = 0 := by ring
        have hyne : ((invmod p x : ℕ) : ZMod p) ≠ 0 := natCast_ne_zero p (invmod p x) hp2 hyl hyh
        rcases mul_eq_zero.mp hsub with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hyne
      exact hxu (zmod_nat_eq_of_eq (by omega : 0 < p) hux (by omega) (by omega))
    · have hA1 : ((i2 : ℤ) - (i1 : ℤ)) = 1 ∨ ((i2 : ℤ) - (i1 : ℤ)) = -1 := by omega
      have hB1 : ((j2 : ℤ) - (j1 : ℤ)) = 1 ∨ ((j2 : ℤ) - (j1 : ℤ)) = -1 := by omega
      have hslope : ((i2 : ℤ) - (i1 : ℤ)) = ((j2 : ℤ) - (j1 : ℤ)) ∨
          ((i2 : ℤ) - (i1 : ℤ)) = -((j2 : ℤ) - (j1 : ℤ)) := by
        rcases hA1 with h | h <;> rcases hB1 with h' | h' <;> omega
      rcases hslope with hsig | hsig
      · have hmain2 : ((invmod p u : ℤ) - (invmod p x : ℤ)) - (xb p u - xb p x)
            = (p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) - ((j3 : ℤ) - (j1 : ℤ))) := by
          rcases hA1 with hA | hA
          · have hB : ((j2 : ℤ) - (j1 : ℤ)) = 1 := by linarith [hsig, hA]
            rw [hA, hB] at hmain
            linear_combination hmain
          · have hB : ((j2 : ℤ) - (j1 : ℤ)) = -1 := by linarith [hsig, hA]
            rw [hA, hB] at hmain
            linear_combination -hmain
        have hrel : ((invmod p x : ZMod p) - (x : ZMod p)) = ((invmod p u : ZMod p) - (u : ZMod p)) := by
          have hZ := congrArg (fun z : ℤ => (z : ZMod p)) hmain
          push_cast at hZ
          simp only [ZMod.natCast_self, mul_zero, sub_zero, zero_sub] at hZ
          rw [xb_cast, xb_cast] at hZ
          rcases hA1 with hA | hA
          · have hA' : ((i2 : ZMod p) - (i1 : ZMod p)) = 1 := by
              have h := congrArg (fun w : ℤ => (w : ZMod p)) hA
              push_cast at h
              simpa using h
            have hB' : ((j2 : ZMod p) - (j1 : ZMod p)) = 1 := by
              have hBℤ : ((j2 : ℤ) - (j1 : ℤ)) = 1 := by linarith [hsig, hA]
              have h := congrArg (fun w : ℤ => (w : ZMod p)) hBℤ
              push_cast at h
              simpa using h
            rw [hA', hB'] at hZ
            linear_combination -hZ
          · have hA' : ((i2 : ZMod p) - (i1 : ZMod p)) = -1 := by
              have h := congrArg (fun w : ℤ => (w : ZMod p)) hA
              push_cast at h
              simpa using h
            have hB' : ((j2 : ZMod p) - (j1 : ZMod p)) = -1 := by
              have hBℤ : ((j2 : ℤ) - (j1 : ℤ)) = -1 := by linarith [hsig, hA]
              have h := congrArg (fun w : ℤ => (w : ZMod p)) hBℤ
              push_cast at h
              simpa using h
            rw [hA', hB'] at hZ
            linear_combination hZ
        obtain ⟨hu, hv⟩ := refl_diff p hp hp2 x (invmod p x) u (invmod p u)
          hxl hxh hul huh hyl hyh hvl hvh hyx hyu hxu hrel
        have hcase : (i1 = 0 ∧ j1 = 0 ∧ i2 = 1 ∧ j2 = 1) ∨ (i1 = 1 ∧ j1 = 1 ∧ i2 = 0 ∧ j2 = 0) := by
          rcases hA1 with hA | hA
          · have hB : ((j2 : ℤ) - (j1 : ℤ)) = 1 := by linarith [hsig, hA]
            omega
          · have hB : ((j2 : ℤ) - (j1 : ℤ)) = -1 := by linarith [hsig, hA]
            omega
        rcases hcase with ⟨hi1, hj1, hi2, hj2⟩ | ⟨hi1, hj1, hi2, hj2⟩
        · by_cases hxA : x ≤ hh p
          · by_cases hyA : hh p < invmod p x
            · have hdI : dropI p x = 0 := dropI_of_le p x hxA
              have hdJ : dropJ p (invmod p x) = 0 := dropJ_of_lt p (invmod p x) hyA
              rcases Params_allowed h1 with hc | hc
              · rw [hi1] at hc; rw [hdI] at hc; exact hc rfl
              · rw [hj1] at hc; rw [hdJ] at hc; exact hc rfl
            · have hxbx : xb p x = (x : ℤ) := xb_of_le p x hxA
              have hxbu : xb p u = -((invmod p x : ℕ) : ℤ) := by
                rw [hu, xb_of_gt p (p - invmod p x) (by omega)]
                rw [Nat.cast_sub (by omega : invmod p x ≤ p)]
                ring
              have hE : ((invmod p u : ℤ) - (invmod p x : ℤ)) - (xb p u - xb p x) = (p : ℤ) := by
                rw [hv, hxbx, hxbu]
                rw [Nat.cast_sub (by omega : x ≤ p)]
                ring
              have hCD : ((i3 : ℤ) - (i1 : ℤ)) - ((j3 : ℤ) - (j1 : ℤ)) = 1 := by
                have h2 : (p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) - ((j3 : ℤ) - (j1 : ℤ))) = (p : ℤ) * 1 := by
                  linarith [hmain2, hE]
                exact mul_left_cancel₀ hpz h2
              have hi3 : i3 = 1 := by omega
              have hj3 : j3 = 0 := by omega
              have hdI : dropI p u = 1 := by
                rw [hu]
                exact dropI_of_gt p (p - invmod p x) (by omega)
              have hdJ : dropJ p (invmod p u) = 0 := by
                rw [hv]
                exact dropJ_of_lt p (p - x) (by omega)
              rcases Params_allowed h3 with hc | hc
              · rw [hi3] at hc; exact hc hdI.symm
              · rw [hj3] at hc; exact hc hdJ.symm
          · by_cases hyA : hh p < invmod p x
            · have hxbx : xb p x = (x : ℤ) - (p : ℤ) := xb_of_gt p x (by omega)
              have hxbu : xb p u = (p : ℤ) - ((invmod p x : ℕ) : ℤ) := by
                rw [hu, xb_of_le p (p - invmod p x) (by omega)]
                rw [Nat.cast_sub (by omega : invmod p x ≤ p)]
              have hE : ((invmod p u : ℤ) - (invmod p x : ℤ)) - (xb p u - xb p x) = -((p : ℤ)) := by
                rw [hv, hxbx, hxbu]
                rw [Nat.cast_sub (by omega : x ≤ p)]
                ring
              have hCD : ((i3 : ℤ) - (i1 : ℤ)) - ((j3 : ℤ) - (j1 : ℤ)) = -1 := by
                have h2 : (p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) - ((j3 : ℤ) - (j1 : ℤ))) = (p : ℤ) * (-1) := by
                  linarith [hmain2, hE]
                exact mul_left_cancel₀ hpz h2
              have hi3 : i3 = 0 := by omega
              have hj3 : j3 = 1 := by omega
              have hdI : dropI p u = 0 := by
                rw [hu]
                exact dropI_of_le p (p - invmod p x) (by omega)
              have hdJ : dropJ p (invmod p u) = 1 := by
                rw [hv]
                exact dropJ_of_ge p (p - x) (by omega)
              rcases Params_allowed h3 with hc | hc
              · rw [hi3] at hc; exact hc hdI.symm
              · rw [hj3] at hc; exact hc hdJ.symm
            · have hdI : dropI p x = 1 := dropI_of_gt p x (by omega)
              have hdJ : dropJ p (invmod p x) = 1 := dropJ_of_ge p _ (by omega)
              rcases Params_allowed h2 with hc | hc
              · rw [hi2] at hc; rw [hdI] at hc; exact hc rfl
              · rw [hj2] at hc; rw [hdJ] at hc; exact hc rfl
        · by_cases hxA : x ≤ hh p
          · by_cases hyA : hh p < invmod p x
            · have hdI : dropI p x = 0 := dropI_of_le p x hxA
              have hdJ : dropJ p (invmod p x) = 0 := dropJ_of_lt p (invmod p x) hyA
              rcases Params_allowed h2 with hc | hc
              · rw [hi2] at hc; rw [hdI] at hc; exact hc rfl
              · rw [hj2] at hc; rw [hdJ] at hc; exact hc rfl
            · have hxbx : xb p x = (x : ℤ) := xb_of_le p x hxA
              have hxbu : xb p u = -((invmod p x : ℕ) : ℤ) := by
                rw [hu, xb_of_gt p (p - invmod p x) (by omega)]
                rw [Nat.cast_sub (by omega : invmod p x ≤ p)]
                ring
              have hE : ((invmod p u : ℤ) - (invmod p x : ℤ)) - (xb p u - xb p x) = (p : ℤ) := by
                rw [hv, hxbx, hxbu]
                rw [Nat.cast_sub (by omega : x ≤ p)]
                ring
              have hCD : ((i3 : ℤ) - (i1 : ℤ)) - ((j3 : ℤ) - (j1 : ℤ)) = 1 := by
                have h2 : (p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) - ((j3 : ℤ) - (j1 : ℤ))) = (p : ℤ) * 1 := by
                  linarith [hmain2, hE]
                exact mul_left_cancel₀ hpz h2
              have hi3 : i3 = 1 := by omega
              have hj3 : j3 = 0 := by omega
              have hdI : dropI p u = 1 := by
                rw [hu]
                exact dropI_of_gt p (p - invmod p x) (by omega)
              have hdJ : dropJ p (invmod p u) = 0 := by
                rw [hv]
                exact dropJ_of_lt p (p - x) (by omega)
              rcases Params_allowed h3 with hc | hc
              · rw [hi3] at hc; exact hc hdI.symm
              · rw [hj3] at hc; exact hc hdJ.symm
          · by_cases hyA : hh p < invmod p x
            · have hxbx : xb p x = (x : ℤ) - (p : ℤ) := xb_of_gt p x (by omega)
              have hxbu : xb p u = (p : ℤ) - ((invmod p x : ℕ) : ℤ) := by
                rw [hu, xb_of_le p (p - invmod p x) (by omega)]
                rw [Nat.cast_sub (by omega : invmod p x ≤ p)]
              have hE : ((invmod p u : ℤ) - (invmod p x : ℤ)) - (xb p u - xb p x) = -((p : ℤ)) := by
                rw [hv, hxbx, hxbu]
                rw [Nat.cast_sub (by omega : x ≤ p)]
                ring
              have hCD : ((i3 : ℤ) - (i1 : ℤ)) - ((j3 : ℤ) - (j1 : ℤ)) = -1 := by
                have h2 : (p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) - ((j3 : ℤ) - (j1 : ℤ))) = (p : ℤ) * (-1) := by
                  linarith [hmain2, hE]
                exact mul_left_cancel₀ hpz h2
              have hi3 : i3 = 0 := by omega
              have hj3 : j3 = 1 := by omega
              have hdI : dropI p u = 0 := by
                rw [hu]
                exact dropI_of_le p (p - invmod p x) (by omega)
              have hdJ : dropJ p (invmod p u) = 1 := by
                rw [hv]
                exact dropJ_of_ge p (p - x) (by omega)
              rcases Params_allowed h3 with hc | hc
              · rw [hi3] at hc; exact hc hdI.symm
              · rw [hj3] at hc; exact hc hdJ.symm
            · have hdI : dropI p x = 1 := dropI_of_gt p x (by omega)
              have hdJ : dropJ p (invmod p x) = 1 := dropJ_of_ge p _ (by omega)
              rcases Params_allowed h1 with hc | hc
              · rw [hi1] at hc; rw [hdI] at hc; exact hc rfl
              · rw [hj1] at hc; rw [hdJ] at hc; exact hc rfl
      · have hmain3 : ((invmod p u : ℤ) - (invmod p x : ℤ)) + (xb p u - xb p x)
            = -((p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) + ((j3 : ℤ) - (j1 : ℤ)))) := by
          rcases hA1 with hA | hA
          · have hB : ((j2 : ℤ) - (j1 : ℤ)) = -1 := by linarith [hsig, hA]
            rw [hA, hB] at hmain
            linear_combination hmain
          · have hB : ((j2 : ℤ) - (j1 : ℤ)) = 1 := by linarith [hsig, hA]
            rw [hA, hB] at hmain
            linear_combination -hmain
        have hrel : ((invmod p x : ZMod p) + (x : ZMod p)) = ((invmod p u : ZMod p) + (u : ZMod p)) := by
          have hZ := congrArg (fun z : ℤ => (z : ZMod p)) hmain
          push_cast at hZ
          simp only [ZMod.natCast_self, mul_zero, sub_zero, zero_sub] at hZ
          rw [xb_cast, xb_cast] at hZ
          rcases hA1 with hA | hA
          · have hA' : ((i2 : ZMod p) - (i1 : ZMod p)) = 1 := by
              have h := congrArg (fun w : ℤ => (w : ZMod p)) hA
              push_cast at h
              simpa using h
            have hB' : ((j2 : ZMod p) - (j1 : ZMod p)) = -1 := by
              have hBℤ : ((j2 : ℤ) - (j1 : ℤ)) = -1 := by linarith [hsig, hA]
              have h := congrArg (fun w : ℤ => (w : ZMod p)) hBℤ
              push_cast at h
              simpa using h
            rw [hA', hB'] at hZ
            linear_combination -hZ
          · have hA' : ((i2 : ZMod p) - (i1 : ZMod p)) = -1 := by
              have h := congrArg (fun w : ℤ => (w : ZMod p)) hA
              push_cast at h
              simpa using h
            have hB' : ((j2 : ZMod p) - (j1 : ZMod p)) = 1 := by
              have hBℤ : ((j2 : ℤ) - (j1 : ℤ)) = 1 := by linarith [hsig, hA]
              have h := congrArg (fun w : ℤ => (w : ZMod p)) hBℤ
              push_cast at h
              simpa using h
            rw [hA', hB'] at hZ
            linear_combination hZ
        obtain ⟨hu, hv⟩ := refl_sum p hp hp2 x (invmod p x) u (invmod p u)
          hxl hxh hul huh hyl hyh hvl hvh hyx hyu hxu hrel
        have hcase : (i1 = 0 ∧ j1 = 1 ∧ i2 = 1 ∧ j2 = 0) ∨ (i1 = 1 ∧ j1 = 0 ∧ i2 = 0 ∧ j2 = 1) := by
          rcases hA1 with hA | hA
          · have hB : ((j2 : ℤ) - (j1 : ℤ)) = -1 := by linarith [hsig, hA]
            obtain ⟨e1, e2⟩ := idx_of_sub_one i1 i2 qi1 qi2 hA
            obtain ⟨e3, e4⟩ := idx_of_sub_neg_one j1 j2 qj1 qj2 hB
            left
            exact ⟨e1, e3, e2, e4⟩
          · have hB : ((j2 : ℤ) - (j1 : ℤ)) = 1 := by linarith [hsig, hA]
            obtain ⟨e1, e2⟩ := idx_of_sub_neg_one i1 i2 qi1 qi2 hA
            obtain ⟨e3, e4⟩ := idx_of_sub_one j1 j2 qj1 qj2 hB
            right
            exact ⟨e1, e3, e2, e4⟩
        rcases hcase with ⟨hi1, hj1, hi2, hj2⟩ | ⟨hi1, hj1, hi2, hj2⟩
        · by_cases hxA : x ≤ hh p
          · by_cases hyA : hh p < invmod p x
            · have hxbx : xb p x = (x : ℤ) := xb_of_le p x hxA
              have hxbu : xb p u = ((invmod p x : ℕ) : ℤ) - (p : ℤ) := by
                rw [hu, xb_of_gt p (invmod p x) hyA]
              have hE : ((invmod p u : ℤ) - (invmod p x : ℤ)) + (xb p u - xb p x) = -((p : ℤ)) := by
                rw [hv, hxbx, hxbu]
                ring
              have hCD : ((i3 : ℤ) - (i1 : ℤ)) + ((j3 : ℤ) - (j1 : ℤ)) = 1 := by
                have h2 : -((p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) + ((j3 : ℤ) - (j1 : ℤ)))) = -((p : ℤ) * 1) := by
                  linarith [hmain3, hE]
                have h3 : (p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) + ((j3 : ℤ) - (j1 : ℤ))) = (p : ℤ) * 1 := by linarith
                exact mul_left_cancel₀ hpz h3
              have hi3 : i3 = 1 := by omega
              have hj3 : j3 = 1 := by omega
              have hdI : dropI p u = 1 := by
                rw [hu]
                exact dropI_of_gt p (invmod p x) hyA
              have hdJ : dropJ p (invmod p u) = 1 := by
                rw [hv]
                exact dropJ_of_ge p x (by omega)
              rcases Params_allowed h3 with hc | hc
              · rw [hi3] at hc; exact hc hdI.symm
              · rw [hj3] at hc; exact hc hdJ.symm
            · have hdI : dropI p x = 0 := dropI_of_le p x hxA
              have hdJ : dropJ p (invmod p x) = 1 := dropJ_of_ge p _ (by omega)
              rcases Params_allowed h1 with hc | hc
              · rw [hi1] at hc; rw [hdI] at hc; exact hc rfl
              · rw [hj1] at hc; rw [hdJ] at hc; exact hc rfl
          · by_cases hyA : hh p < invmod p x
            · have hdI : dropI p x = 1 := dropI_of_gt p x (by omega)
              have hdJ : dropJ p (invmod p x) = 0 := dropJ_of_lt p _ hyA
              rcases Params_allowed h2 with hc | hc
              · rw [hi2] at hc; rw [hdI] at hc; exact hc rfl
              · rw [hj2] at hc; rw [hdJ] at hc; exact hc rfl
            · have hxbx : xb p x = (x : ℤ) - (p : ℤ) := xb_of_gt p x (by omega)
              have hxbu : xb p u = ((invmod p x : ℕ) : ℤ) := by
                rw [hu]
                exact xb_of_le p (invmod p x) (by omega)
              have hE : ((invmod p u : ℤ) - (invmod p x : ℤ)) + (xb p u - xb p x) = (p : ℤ) := by
                rw [hv, hxbx, hxbu]
                ring
              have hCD : ((i3 : ℤ) - (i1 : ℤ)) + ((j3 : ℤ) - (j1 : ℤ)) = -1 := by
                have h3 : (p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) + ((j3 : ℤ) - (j1 : ℤ))) = (p : ℤ) * (-1) := by
                  linarith [hmain3, hE]
                exact mul_left_cancel₀ hpz h3
              have hi3 : i3 = 0 := by omega
              have hj3 : j3 = 0 := by omega
              have hdI : dropI p u = 0 := by
                rw [hu]
                exact dropI_of_le p (invmod p x) (by omega)
              have hdJ : dropJ p (invmod p u) = 0 := by
                rw [hv]
                exact dropJ_of_lt p x (by omega)
              rcases Params_allowed h3 with hc | hc
              · rw [hi3] at hc; exact hc hdI.symm
              · rw [hj3] at hc; exact hc hdJ.symm
        · by_cases hxA : x ≤ hh p
          · by_cases hyA : hh p < invmod p x
            · have hxbx : xb p x = (x : ℤ) := xb_of_le p x hxA
              have hxbu : xb p u = ((invmod p x : ℕ) : ℤ) - (p : ℤ) := by
                rw [hu, xb_of_gt p (invmod p x) hyA]
              have hE : ((invmod p u : ℤ) - (invmod p x : ℤ)) + (xb p u - xb p x) = -((p : ℤ)) := by
                rw [hv, hxbx, hxbu]
                ring
              have hCD : ((i3 : ℤ) - (i1 : ℤ)) + ((j3 : ℤ) - (j1 : ℤ)) = 1 := by
                have h3 : (p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) + ((j3 : ℤ) - (j1 : ℤ))) = (p : ℤ) * 1 := by
                  linarith [hmain3, hE]
                exact mul_left_cancel₀ hpz h3
              have hi3 : i3 = 1 := by omega
              have hj3 : j3 = 1 := by omega
              have hdI : dropI p u = 1 := by
                rw [hu]
                exact dropI_of_gt p (invmod p x) hyA
              have hdJ : dropJ p (invmod p u) = 1 := by
                rw [hv]
                exact dropJ_of_ge p x (by omega)
              rcases Params_allowed h3 with hc | hc
              · rw [hi3] at hc; exact hc hdI.symm
              · rw [hj3] at hc; exact hc hdJ.symm
            · have hdI : dropI p x = 0 := dropI_of_le p x hxA
              have hdJ : dropJ p (invmod p x) = 1 := dropJ_of_ge p _ (by omega)
              rcases Params_allowed h2 with hc | hc
              · rw [hi2] at hc; rw [hdI] at hc; exact hc rfl
              · rw [hj2] at hc; rw [hdJ] at hc; exact hc rfl
          · by_cases hyA : hh p < invmod p x
            · have hdI : dropI p x = 1 := dropI_of_gt p x (by omega)
              have hdJ : dropJ p (invmod p x) = 0 := dropJ_of_lt p _ hyA
              rcases Params_allowed h1 with hc | hc
              · rw [hi1] at hc; rw [hdI] at hc; exact hc rfl
              · rw [hj1] at hc; rw [hdJ] at hc; exact hc rfl
            · have hxbx : xb p x = (x : ℤ) - (p : ℤ) := xb_of_gt p x (by omega)
              have hxbu : xb p u = ((invmod p x : ℕ) : ℤ) := by
                rw [hu]
                exact xb_of_le p (invmod p x) (by omega)
              have hE : ((invmod p u : ℤ) - (invmod p x : ℤ)) + (xb p u - xb p x) = (p : ℤ) := by
                rw [hv, hxbx, hxbu]
                ring
              have hCD : ((i3 : ℤ) - (i1 : ℤ)) + ((j3 : ℤ) - (j1 : ℤ)) = -1 := by
                have h3 : (p : ℤ) * (((i3 : ℤ) - (i1 : ℤ)) + ((j3 : ℤ) - (j1 : ℤ))) = (p : ℤ) * (-1) := by
                  linarith [hmain3, hE]
                exact mul_left_cancel₀ hpz h3
              have hi3 : i3 = 0 := by omega
              have hj3 : j3 = 0 := by omega
              have hdI : dropI p u = 0 := by
                rw [hu]
                exact dropI_of_le p (invmod p x) (by omega)
              have hdJ : dropJ p (invmod p u) = 0 := by
                rw [hv]
                exact dropJ_of_lt p x (by omega)
              rcases Params_allowed h3 with hc | hc
              · rw [hi3] at hc; exact hc hdI.symm
              · rw [hj3] at hc; exact hc hdJ.symm

set_option maxHeartbeats 4000000 in
private lemma no_three (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
    (x1 i1 j1 x2 i2 j2 x3 i3 j3 : ℕ)
    (h1 : (x1, i1, j1) ∈ Params p) (h2 : (x2, i2, j2) ∈ Params p) (h3 : (x3, i3, j3) ∈ Params p)
    (hdist12 : (gX p x1 i1, gY p (invmod p x1) j1) ≠ (gX p x2 i2, gY p (invmod p x2) j2))
    (hdist13 : (gX p x1 i1, gY p (invmod p x1) j1) ≠ (gX p x3 i3, gY p (invmod p x3) j3))
    (hdist23 : (gX p x2 i2, gY p (invmod p x2) j2) ≠ (gX p x3 i3, gY p (invmod p x3) j3))
    (hcol : det3 (gX p x1 i1, gY p (invmod p x1) j1) (gX p x2 i2, gY p (invmod p x2) j2)
      (gX p x3 i3, gY p (invmod p x3) j3) = 0) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsome : x1 = x2 ∨ x1 = x3 ∨ x2 = x3 := by
    by_contra hc
    push_neg at hc
    obtain ⟨hc12, hc13, hc23⟩ := hc
    have b1 := Params_x_bounds h1
    have b2 := Params_x_bounds h2
    have b3 := Params_x_bounds h3
    have y1 := invmod_bounds p x1 hp hp2 b1.1 b1.2
    have y2 := invmod_bounds p x2 hp hp2 b2.1 b2.2
    have y3 := invmod_bounds p x3 hp hp2 b3.1 b3.2
    have em1 : (x1 : ZMod p) * (invmod p x1 : ZMod p) = 1 := invmod_mul p x1 hp hp2 b1.1 b1.2
    have em2 : (x2 : ZMod p) * (invmod p x2 : ZMod p) = 1 := invmod_mul p x2 hp hp2 b2.1 b2.2
    have em3 : (x3 : ZMod p) * (invmod p x3 : ZMod p) = 1 := invmod_mul p x3 hp hp2 b3.1 b3.2
    have hmod := moddet p hp hp2 x1 i1 j1 x2 i2 j2 x3 i3 j3 h1 h2 h3 hcol
    refine field_identity p hp (x1 : ZMod p) (x2 : ZMod p) (x3 : ZMod p)
      (invmod p x1 : ZMod p) (invmod p x2 : ZMod p) (invmod p x3 : ZMod p) em1 em2 em3 ?_ ?_ ?_ hmod
    · intro hh
      exact hc12 (zmod_nat_eq_of_eq (by omega : 0 < p) hh (by omega) (by omega))
    · intro hh
      exact hc13 (zmod_nat_eq_of_eq (by omega : 0 < p) hh (by omega) (by omega))
    · intro hh
      exact hc23 (zmod_nat_eq_of_eq (by omega : 0 < p) hh (by omega) (by omega))
  rcases hsome with h | h | h
  · rw [h] at h1 hdist12 hdist13 hcol
    by_cases hx : x3 = x2
    · rw [hx] at h3 hdist13 hdist23 hcol
      exact same_class_not_col p hp hp2 x2 i1 j1 i2 j2 i3 j3 h1 h2 h3
        (corner_ne_of_ne p x2 i1 j1 i2 j2 hdist12)
        (corner_ne_of_ne p x2 i1 j1 i3 j3 hdist13)
        (corner_ne_of_ne p x2 i2 j2 i3 j3 hdist23) hcol
    · exact two_same p hp hp2 x2 i1 j1 i2 j2 x3 i3 j3 h1 h2 h3 hx hdist12 hcol
  · rw [h] at h1 hdist12 hdist13 hcol
    have hcol' : det3 (gX p x3 i1, gY p (invmod p x3) j1) (gX p x3 i3, gY p (invmod p x3) j3)
        (gX p x2 i2, gY p (invmod p x2) j2) = 0 := by
      have hs := det3_swap (gX p x3 i1, gY p (invmod p x3) j1) (gX p x2 i2, gY p (invmod p x2) j2)
        (gX p x3 i3, gY p (invmod p x3) j3)
      rw [hs, hcol]
      ring
    by_cases hx : x2 = x3
    · rw [hx] at h2 hdist12 hdist23 hcol'
      exact same_class_not_col p hp hp2 x3 i1 j1 i3 j3 i2 j2 h1 h3 h2
        (corner_ne_of_ne p x3 i1 j1 i3 j3 hdist13)
        (corner_ne_of_ne p x3 i1 j1 i2 j2 hdist12)
        (corner_ne_of_ne p x3 i3 j3 i2 j2 hdist23.symm) hcol'
    · exact two_same p hp hp2 x3 i1 j1 i3 j3 x2 i2 j2 h1 h3 h2 hx hdist13 hcol'
  · rw [h] at h2 hdist12 hdist23 hcol
    by_cases hx : x1 = x3
    · rw [hx] at h1 hdist12 hdist13 hcol
      exact same_class_not_col p hp hp2 x3 i1 j1 i2 j2 i3 j3 h1 h2 h3
        (corner_ne_of_ne p x3 i1 j1 i2 j2 hdist12)
        (corner_ne_of_ne p x3 i1 j1 i3 j3 hdist13)
        (corner_ne_of_ne p x3 i2 j2 i3 j3 hdist23) hcol
    · have hcol'' : det3 (gX p x3 i2, gY p (invmod p x3) j2) (gX p x3 i3, gY p (invmod p x3) j3)
          (gX p x1 i1, gY p (invmod p x1) j1) = 0 := by
        have hcyc := det3_cyclic (gX p x1 i1, gY p (invmod p x1) j1) (gX p x3 i2, gY p (invmod p x3) j2)
          (gX p x3 i3, gY p (invmod p x3) j3)
        rw [hcol] at hcyc
        exact hcyc.symm
      exact two_same p hp hp2 x3 i2 j2 i3 j3 x1 i1 j1 h2 h3 h1 hx hdist23 hcol''

set_option maxHeartbeats 1000000 in
private lemma Sset_card (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) : (Sset p).card = 3 * (p - 1) := by
  unfold Sset
  rw [Finset.card_image_of_injOn, Params_card p]
  intro t ht u hu heq
  have ht1 := Params_x_bounds ht
  have hu1 := Params_x_bounds hu
  have hti := Params_ij_lt ht
  have hui := Params_ij_lt hu
  obtain ⟨heq1, heq2⟩ := Prod.ext_iff.mp heq
  have hx : t.1 = u.1 ∧ t.2.1 = u.2.1 :=
    gX_inj p t.1 u.1 t.2.1 u.2.1 hp hp2 ht1.1 ht1.2 hu1.1 hu1.2 (by omega) (by omega) heq1
  have hjeq : t.2.2 = u.2.2 := by
    have h2 : gY p (invmod p t.1) t.2.2 = gY p (invmod p u.1) u.2.2 := heq2
    rw [hx.1] at h2
    unfold gY at h2
    have ht2 : t.2.2 < 2 := by simpa using hti.2
    have hu2 : u.2.2 < 2 := by simpa using hui.2
    interval_cases t.2.2 <;> interval_cases u.2.2 <;> omega
  exact Prod.ext hx.1 (Prod.ext hx.2 hjeq)

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_no_three_in_line_two_period_lift :
    let valid := fun (n : ℕ) (S : Finset (ℕ × ℕ)) => (∀ z ∈ S, z.1 < n ∧ z.2 < n) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠ ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))); ∀ p : ℕ, Nat.Prime p → 2 < p → ∃ S : Finset (ℕ × ℕ), valid (2*p) S ∧ 3*(p-1) ≤ S.card := by
  intro valid p hp hp2
  refine ⟨Sset p, ?_, ?_⟩
  · constructor
    · intro z hz
      obtain ⟨t, ht, htz⟩ := Finset.mem_image.mp hz
      rw [← htz]
      obtain ⟨hxl, hxh⟩ := Params_x_bounds ht
      obtain ⟨hyl, hyh⟩ := invmod_bounds p t.1 hp hp2 hxl hxh
      have hi : t.2.1 < 2 := by simpa using (Params_ij_lt ht).1
      have hj : t.2.2 < 2 := by simpa using (Params_ij_lt ht).2
      exact ⟨gX_lt p hp hp2 t.1 t.2.1 hxl hxh (by omega),
        gY_lt p hp hp2 (invmod p t.1) t.2.2 hyh (by omega)⟩
    · intro a ha b hb c hc hab hac hbc hcontra
      obtain ⟨t1, ht1, htz1⟩ := Finset.mem_image.mp ha
      obtain ⟨t2, ht2, htz2⟩ := Finset.mem_image.mp hb
      obtain ⟨t3, ht3, htz3⟩ := Finset.mem_image.mp hc
      rcases t1 with ⟨x1, i1, j1⟩
      rcases t2 with ⟨x2, i2, j2⟩
      rcases t3 with ⟨x3, i3, j3⟩
      have hP1 : (gX p (x1, i1, j1).1 (x1, i1, j1).2.1, gY p (invmod p (x1, i1, j1).1) (x1, i1, j1).2.2)
          = (gX p x1 i1, gY p (invmod p x1) j1) := rfl
      have hP2 : (gX p (x2, i2, j2).1 (x2, i2, j2).2.1, gY p (invmod p (x2, i2, j2).1) (x2, i2, j2).2.2)
          = (gX p x2 i2, gY p (invmod p x2) j2) := rfl
      have hP3 : (gX p (x3, i3, j3).1 (x3, i3, j3).2.1, gY p (invmod p (x3, i3, j3).1) (x3, i3, j3).2.2)
          = (gX p x3 i3, gY p (invmod p x3) j3) := rfl
      rw [hP1] at htz1
      rw [hP2] at htz2
      rw [hP3] at htz3
      have hd12 : (gX p x1 i1, gY p (invmod p x1) j1) ≠ (gX p x2 i2, gY p (invmod p x2) j2) := by
        intro hh
        apply hab
        rw [← htz1, ← htz2]
        exact hh
      have hd13 : (gX p x1 i1, gY p (invmod p x1) j1) ≠ (gX p x3 i3, gY p (invmod p x3) j3) := by
        intro hh
        apply hac
        rw [← htz1, ← htz3]
        exact hh
      have hd23 : (gX p x2 i2, gY p (invmod p x2) j2) ≠ (gX p x3 i3, gY p (invmod p x3) j3) := by
        intro hh
        apply hbc
        rw [← htz2, ← htz3]
        exact hh
      have hdet : det3 (gX p x1 i1, gY p (invmod p x1) j1) (gX p x2 i2, gY p (invmod p x2) j2)
          (gX p x3 i3, gY p (invmod p x3) j3) = 0 := by
        rw [← htz1, ← htz2, ← htz3] at hcontra
        unfold det3
        linarith [hcontra]
      exact no_three p hp hp2 x1 i1 j1 x2 i2 j2 x3 i3 j3 ht1 ht2 ht3 hd12 hd13 hd23 hdet
  · rw [Sset_card p hp hp2]
