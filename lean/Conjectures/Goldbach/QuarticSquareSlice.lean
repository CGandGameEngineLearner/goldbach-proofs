import Mathlib
import Conjectures.Goldbach.CubicFixedLinearDefect

/-!
For triples with fixed sums of squares and fourth powers, the coordinates
u = 2a − b − c and v = b − c of the squared entries have fixed norm
u² + 3v². Together with a + b + c these coordinates determine the triple.

Primitive norm representations yield roots of r² + 3 modulo the norm.
A determinant bound accounts for the two possible signs at a fixed root,
and splitting off the gcd handles nonprimitive representations. The final
growth estimate uses the divisor bound formalized in PR #4396.
-/

namespace QuarticSlice

open Finset

private theorem factor_of_root {m a r : ℕ} (hm : 0 < m) (ha : a < m)
    (hra : m ∣ a^2 + 3) (hrr : m ∣ r^2 + 3) :
    let d := m.gcd (r+m-a)
    d ∣ m ∧ r ≡ a [MOD d] ∧ m/d ∣ r+a ∧ d.gcd (m/d) ≤ 6 := by
  let x := r+m-a
  let d := m.gcd x
  let e := m/d
  let g := d.gcd e
  change d ∣ m ∧ r ≡ a [MOD d] ∧ e ∣ r+a ∧ g ≤ 6
  have hd : d ∣ m := Nat.gcd_dvd_left _ _
  have hx : d ∣ x := Nat.gcd_dvd_right _ _
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ hm
  have hxZ : (x:ℤ) = (r:ℤ) + m - a := by
    dsimp [x]; rw [Nat.cast_sub (by omega : a ≤ r+m), Nat.cast_add]
  have hz : r ≡ a [MOD d] := by
    apply Nat.modEq_iff_dvd.mpr
    have h₁ : (d:ℤ) ∣ (m:ℤ) := by exact_mod_cast hd
    have h₂ : (d:ℤ) ∣ (x:ℤ) := by exact_mod_cast hx
    convert dvd_sub h₁ h₂ using 1
    rw [hxZ]
    ring
  have hraZ : (m:ℤ) ∣ (a:ℤ)^2+3 := by exact_mod_cast hra
  have hrrZ : (m:ℤ) ∣ (r:ℤ)^2+3 := by exact_mod_cast hrr
  have hp : m ∣ x*(r+a) := by
    have hs : (m:ℤ) ∣ (x:ℤ)*((r:ℤ)+a) := by
      convert dvd_add (dvd_sub hrrZ hraZ) (dvd_mul_right (m:ℤ) ((r:ℤ)+a)) using 1
      rw [hxZ]; ring
    exact_mod_cast hs
  have hmd : d*e = m := Nat.mul_div_cancel' hd
  have hxd : d*(x/d) = x := Nat.mul_div_cancel' hx
  have hey : e ∣ r+a := by
    have hc : e.Coprime (x/d) := Nat.coprime_div_gcd_div_gcd hd0
    apply hc.dvd_of_dvd_mul_left
    apply (Nat.mul_dvd_mul_iff_left hd0).mp
    rw [hmd, ← Nat.mul_assoc, hxd]
    exact hp
  refine ⟨hd, hz, hey, ?_⟩
  have hgd : g ∣ d := Nat.gcd_dvd_left _ _
  have hge : g ∣ e := Nat.gcd_dvd_right _ _
  have hgm := hgd.trans hd
  have hgdiff := (hz.of_dvd hgd).dvd
  have hgsum : (g:ℤ) ∣ (r:ℤ)+a := by exact_mod_cast (hge.trans hey)
  have hg2a : g ∣ 2*a := by
    have h : (g:ℤ) ∣ 2*(a:ℤ) := by
      convert dvd_add hgdiff hgsum using 1
      ring
    exact_mod_cast h
  have hgcd : g ∣ 2*m.gcd a := by
    rw [← Nat.gcd_mul_left]
    exact Nat.dvd_gcd (hgm.trans (dvd_mul_left _ _)) hg2a
  have ha3 : m.gcd a ∣ 3 := by
    apply (Nat.dvd_add_iff_right (show m.gcd a ∣ a^2 by
      rw [pow_two]; exact (Nat.gcd_dvd_right _ _).trans (dvd_mul_right _ _))).mpr
    exact (Nat.gcd_dvd_left _ _).trans hra
  exact (Nat.le_of_dvd (by positivity : 0 < 6) (hgcd.trans (by
    simpa using Nat.mul_dvd_mul_left 2 ha3)))

theorem roots_bound_nat (m : ℕ) (hm : 0 < m) :
    ((range m).filter (fun r => m ∣ r^2+3)).card ≤ 6*m.divisors.card := by
  classical
  let R := (range m).filter fun r => m ∣ r^2+3
  change R.card ≤ _
  rcases R.eq_empty_or_nonempty with he | ⟨a,ha⟩
  · simp [he]
  have info {r} (hr : r ∈ R) : r < m ∧ m ∣ r^2+3 :=
    ⟨mem_range.mp (mem_filter.mp hr).1, (mem_filter.mp hr).2⟩
  let d (r : ℕ) := m.gcd (r+m-a)
  let L (s : ℕ) := s.lcm (m/s)
  let code (r : ℕ) := (d r, r / L (d r))
  have facts {r} (hr : r ∈ R) :
      d r ∣ m ∧ r ≡ a [MOD d r] ∧ m/d r ∣ r+a ∧ (d r).gcd (m/d r) ≤ 6 :=
    factor_of_root hm (info ha).1 (info ha).2 (info hr).2
  have toCode : Set.MapsTo code R ((m.divisors ×ˢ range 6 : Finset (ℕ × ℕ)) : Set _) := by
    intro r hr
    obtain ⟨hd, _, _, hg⟩ := facts hr
    have hd0 : 0 < d r := Nat.gcd_pos_of_pos_left _ hm
    have he0 : 0 < m / d r := Nat.div_pos (Nat.le_of_dvd hm hd) hd0
    have hL : 0 < L (d r) := Nat.lcm_pos hd0 he0
    change (d r, r/L (d r)) ∈ (m.divisors ×ˢ range 6 : Finset (ℕ × ℕ))
    refine mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hd, hm.ne'⟩, mem_range.mpr ?_⟩
    apply (Nat.div_lt_iff_lt_mul hL).mpr
    have hN : (d r).gcd (m/d r)*L (d r) = m :=
      (Nat.gcd_mul_lcm _ _).trans (Nat.mul_div_cancel' hd)
    exact (info hr).1.trans_le (hN ▸ Nat.mul_le_mul_right (L (d r)) hg)
  have injective : Set.InjOn code R := by
    intro r hr s hs he
    have hd : d r = d s := congrArg Prod.fst he
    have hq : r / L (d r) = s / L (d r) := by
      simpa only [code, hd] using congrArg Prod.snd he
    obtain ⟨_, hr₁, hr₂, _⟩ := facts hr
    obtain ⟨_, hs₁, hs₂, _⟩ := facts hs
    rw [← hd] at hs₁ hs₂
    have hc₁ := hr₁.trans hs₁.symm
    have hc₂ : r ≡ s [MOD m/d r] := Nat.ModEq.add_right_cancel' a
      ((Nat.modEq_zero_iff_dvd.mpr hr₂).trans (Nat.modEq_zero_iff_dvd.mpr hs₂).symm)
    have hrem : r % L (d r) = s % L (d r) := Nat.mod_lcm hc₁ hc₂
    have h₁ := Nat.div_add_mod r (L (d r))
    have h₂ := Nat.div_add_mod s (L (d r))
    rw [hq, hrem] at h₁
    exact h₁.symm.trans h₂
  simpa [card_product, Nat.mul_comm] using card_le_card_of_injOn code toCode injective

theorem roots_bound (m : ℕ) (hm : 0 < m) :
    ((range m).filter (fun (r : ℕ) => (m:ℤ) ∣ (r:ℤ)^2+3)).card ≤ 6*m.divisors.card := by
  have h (r : ℕ) : (m:ℤ) ∣ (r:ℤ)^2+3 ↔ m ∣ r^2+3 := by exact_mod_cast Iff.rfl
  simpa only [h] using roots_bound_nat m hm

end QuarticSlice

namespace QuarticSlice
open Finset
open scoped Classical

private def slope (m : ℕ) (z : ℤ × ℤ) : ZMod m :=
  (z.1 : ZMod m) * (z.2 : ZMod m)⁻¹

private theorem slope_props {m : ℕ} [NeZero m] (z : ℤ × ℤ)
    (hz : z.1^2+3*z.2^2 = (m:ℤ)) (hc : Nat.Coprime z.1.natAbs z.2.natAbs) :
    slope m z * z.2 = z.1 ∧ m ∣ (slope m z).val^2 + 3 := by
  obtain ⟨x,y⟩ := z
  change x^2+3*y^2 = (m:ℤ) at hz
  change x.natAbs.Coprime y.natAbs at hc
  have he : x.natAbs^2 + 3*y.natAbs^2 = m := by
    exact_mod_cast (show ((x.natAbs : ℕ):ℤ)^2+3*((y.natAbs:ℕ):ℤ)^2 = m from
      by simpa only [Int.natCast_natAbs,sq_abs] using hz)
  have hy : y.natAbs.Coprime m := by
    rw [← he, show 3*y.natAbs^2 = (3*y.natAbs)*y.natAbs by ring,
      Nat.coprime_add_mul_right_right]
    exact hc.symm.pow_right 2
  have hu : IsUnit (y : ZMod m) := by
    have hh := (ZMod.isUnit_iff_coprime y.natAbs m).mpr hy
    cases y with
    | ofNat n => simpa using hh
    | negSucc n => simpa [Int.cast_negSucc] using hh.neg
  have hx : (x : ZMod m)^2+3*(y:ZMod m)^2 = 0 := by
    have hh := congrArg (fun w : ℤ => (w : ZMod m)) hz
    simpa using hh
  constructor
  · change (x:ZMod m) * (y:ZMod m)⁻¹ * y = x
    rw [mul_assoc, ZMod.inv_mul_of_unit _ hu, mul_one]
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    change ((x:ZMod m)*(y:ZMod m)⁻¹)^2 + 3 = 0
    calc
      _ = ((x:ZMod m)*(y:ZMod m)⁻¹)^2 + 3*((y:ZMod m)*(y:ZMod m)⁻¹)^2 := by
        rw [ZMod.mul_inv_of_unit _ hu]; ring
      _ = ((x:ZMod m)^2+3*(y:ZMod m)^2)*((y:ZMod m)⁻¹)^2 := by ring
      _ = 0 := by rw [hx,zero_mul]

private theorem same_line {m : ℕ} (hm : 0 < m) {x y u v : ℤ}
    (hx : x^2+3*y^2=(m:ℤ)) (hu : u^2+3*v^2=(m:ℤ))
    (hd : (m:ℤ) ∣ x*v-u*y) :
    (x=u ∧ y=v) ∨ (x= -u ∧ y= -v) := by
  let d := x*v-u*y
  let j := x*u+3*y*v
  have hgm : 3*d^2 + j^2 = (m:ℤ)^2 := by
    calc
      _ = (x^2+3*y^2)*(u^2+3*v^2) := by dsimp [d,j]; ring
      _ = _ := by rw [hx,hu,pow_two]
  have hp : 0 < (m:ℤ) := by exact_mod_cast hm
  have hds : d^2 < (m:ℤ)^2 := by nlinarith [sq_nonneg j,sq_pos_of_pos hp]
  have hda : |d| < (m:ℤ) := by simpa only [abs_of_pos hp] using (sq_lt_sq.mp hds)
  have hd0 : d = 0 := Int.eq_zero_of_abs_lt_dvd hd hda
  rw [hd0] at hgm
  have hjs : j^2=(m:ℤ)^2 := by simpa using hgm
  change (x*u+3*y*v)^2=(m:ℤ)^2 at hjs
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hjs with hj|hj
  · left
    have he : (x-u)^2+3*(y-v)^2=0 := by linarith only [hx,hu,hj]
    have eqx : (x-u)^2=0 := by nlinarith only [he,sq_nonneg (y-v),sq_nonneg (x-u)]
    have eqy : (y-v)^2=0 := by nlinarith only [he,sq_nonneg (y-v),sq_nonneg (x-u)]
    exact ⟨sub_eq_zero.mp ((pow_eq_zero_iff (by decide)).mp eqx),
       sub_eq_zero.mp ((pow_eq_zero_iff (by decide)).mp eqy)⟩
  · right
    have he : (x+u)^2+3*(y+v)^2=0 := by linarith only [hx,hu,hj]
    have eqx : (x+u)^2=0 := by nlinarith only [he,sq_nonneg (y+v),sq_nonneg (x+u)]
    have eqy : (y+v)^2=0 := by nlinarith only [he,sq_nonneg (y+v),sq_nonneg (x+u)]
    have ex : x+u=0 := (pow_eq_zero_iff (by decide)).mp eqx
    have ey : y+v=0 := (pow_eq_zero_iff (by decide)).mp eqy
    omega

private theorem primitive_fibers (m : ℕ) (hm : 0 < m) (Y : Finset (ℤ×ℤ))
    (hy : ∀ z∈Y, z.1^2+3*z.2^2=(m:ℤ) ∧ Nat.Coprime z.1.natAbs z.2.natAbs) :
    Y.card ≤ 2 * ((range m).filter (fun r => m ∣ r^2+3)).card := by
  let _ : NeZero m := ⟨hm.ne'⟩
  let tag (z : ℤ×ℤ) : Bool := decide (0 < z.1 ∨ (z.1=0 ∧ 0 ≤ z.2))
  let f (z : ℤ×ℤ) := (tag z, (slope m z).val)
  let R := (range m).filter fun r => m ∣ r^2+3
  have maps : Set.MapsTo f Y ((univ : Finset Bool) ×ˢ R : Finset (Bool × ℕ)) := by
    intro z hz
    exact mem_product.mpr ⟨mem_univ _,mem_filter.mpr
      ⟨mem_range.mpr (ZMod.val_lt _), (slope_props z (hy z hz).1 (hy z hz).2).2⟩⟩
  have inj : Set.InjOn f Y := by
    intro z hz w hw he
    have htag : tag z = tag w := congrArg Prod.fst he
    have hs : slope m z = slope m w :=
      ZMod.val_injective _ (congrArg Prod.snd he)
    have hz' := (slope_props z (hy z hz).1 (hy z hz).2).1
    have hw' := (slope_props w (hy w hw).1 (hy w hw).2).1
    have hdet : (m:ℤ) ∣ z.1*w.2-w.1*z.2 := by
      apply (CharP.intCast_eq_zero_iff (ZMod m) m _).mp
      push_cast
      rw [← hz',← hw',hs]
      ring
    rcases same_line hm (hy z hz).1 (hy w hw).1 hdet with ⟨ha,hb⟩|⟨ha,hb⟩
    · exact Prod.ext ha hb
    · simp only [tag,decide_eq_decide] at htag
      apply Prod.ext <;> omega
  simpa [R,card_product] using card_le_card_of_injOn f maps inj

theorem primitive_bound (m : ℕ) (hm : 0 < m) (Y : Finset (ℤ×ℤ))
    (hy : ∀ z∈Y, z.1^2+3*z.2^2=(m:ℤ) ∧ Nat.Coprime z.1.natAbs z.2.natAbs) :
    Y.card ≤ 12 * m.divisors.card := by
  have hr := roots_bound_nat m hm
  have h := primitive_fibers m hm Y hy
  omega

end QuarticSlice

namespace QuarticSlice
open Finset

private def reducePair (d : ℕ) (z : ℤ × ℤ) : ℤ × ℤ := (z.1 / d, z.2 / d)

private theorem restore_pair (d : ℕ) (z : ℤ × ℤ) (hg : z.1.gcd z.2 = d) :
    (reducePair d z).1 * d = z.1 ∧ (reducePair d z).2 * d = z.2 := by
  subst d
  exact ⟨Int.ediv_mul_cancel (Int.gcd_dvd_left ..), Int.ediv_mul_cancel (Int.gcd_dvd_right ..)⟩

/-- Dividing by the gcd gives a primitive representation of exactly n / d². -/
private theorem reduce_pair_spec (n : ℕ) (hn : 0<n) (d : ℕ) (z : ℤ × ℤ)
    (hz : z.1^2+3*z.2^2=(n:ℤ)) (hg : z.1.gcd z.2 = d) :
    d^2 ∣ n ∧ 0 < n / d^2 ∧
    (reducePair d z).1^2 + 3*(reducePair d z).2^2 = ((n / d^2 : ℕ) : ℤ) ∧
    Nat.Coprime (reducePair d z).1.natAbs (reducePair d z).2.natAbs := by
  let t := (reducePair d z).1^2 + 3*(reducePair d z).2^2
  have t0 : 0 ≤ t := by dsimp [t]; positivity
  have tcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg t0
  obtain ⟨hx,hy⟩ := restore_pair d z hg
  have he : (d:ℤ)^2 * (t.toNat:ℤ) = n := by
    rw [tcast, ←hz, ←hx, ←hy]
    dsimp only [t, reducePair]
    ring
  have hnat : d^2 * t.toNat = n := by exact_mod_cast he
  have hd : 0 < d := by
    by_contra! h
    have hd0 : d=0 := by omega
    rw [hd0] at hnat
    simp at hnat
    omega
  have ht : 0 < t.toNat := by
    by_contra! h
    have ht0 : t.toNat = 0 := by omega
    rw [ht0, mul_zero] at hnat
    omega
  have div_eq : n/d^2 = t.toNat := by
    rw [←hnat, Nat.mul_div_cancel_left _ (pow_pos hd _)]
  refine ⟨⟨t.toNat,hnat.symm⟩, div_eq.symm ▸ ht, ?_, ?_⟩
  · rw [div_eq,tcast]
  · subst d
    exact Int.gcd_ediv_gcd_ediv_gcd hd

/-- A fixed gcd contributes at most the primitive bound at n/d². Both d and
n/d² divide n, so each fiber and the number of fibers have divisor bounds. -/
theorem norm_bound_of_primitive (C : ℕ)
    (primitive_bound : ∀ (m : ℕ), 0 < m → ∀ Y : Finset (ℤ × ℤ),
      (∀ z∈Y, z.1^2+3*z.2^2=(m:ℤ) ∧ Nat.Coprime z.1.natAbs z.2.natAbs) →
        Y.card ≤ C*m.divisors.card)
    (n : ℕ) (hn : 0<n) (Y : Finset (ℤ×ℤ)) (hy : ∀ z∈Y, z.1^2+3*z.2^2=(n:ℤ)) :
    Y.card ≤ C * n.divisors.card^2 := by
  classical
  let g (z : ℤ×ℤ) := z.1.gcd z.2
  let fiber (d : ℕ) := Y.filter (fun z => g z = d)
  have maps : Set.MapsTo g (↑Y) (↑n.divisors) := by
    intro z hz
    have h := (reduce_pair_spec n hn (g z) z (hy z hz) rfl).1
    exact Nat.mem_divisors.mpr ⟨(dvd_pow_self (g z) (by decide : 2 ≠ 0)).trans h, hn.ne'⟩
  have fbound (d : ℕ) : (fiber d).card ≤ C*n.divisors.card := by
    rcases (fiber d).eq_empty_or_nonempty with he | ⟨z,hz⟩
    · simp [he]
    obtain ⟨hzY,hzg⟩ := mem_filter.mp hz
    obtain ⟨hdvd,hpos,_⟩ := reduce_pair_spec n hn d z (hy z hzY) hzg
    let F := (fiber d).image (reducePair d)
    have inj : Set.InjOn (reducePair d) (↑(fiber d)) := by
      intro a ha b hb heq
      obtain ⟨a₁,a₂⟩ := restore_pair d a (mem_filter.mp ha).2
      obtain ⟨b₁,b₂⟩ := restore_pair d b (mem_filter.mp hb).2
      apply Prod.ext
      · rw [←a₁, ←b₁, heq]
      · rw [←a₂, ←b₂, heq]
    have hp := primitive_bound (n / d^2) hpos F (by
      intro w hw
      obtain ⟨b,hb,rfl⟩ := mem_image.mp hw
      obtain ⟨hbY,hbG⟩ := mem_filter.mp hb
      exact (reduce_pair_spec n hn d b (hy b hbY) hbG).2.2)
    rw [show F.card = (fiber d).card from card_image_of_injOn inj] at hp
    exact hp.trans (Nat.mul_le_mul_left _ (card_le_card
      (Nat.divisors_subset_of_dvd hn.ne' (Nat.div_dvd_of_dvd hdvd))))
  calc
    _ = ∑ d ∈ n.divisors, (fiber d).card := card_eq_sum_card_fiberwise maps
    _ ≤ ∑ _d ∈ n.divisors, C*n.divisors.card := sum_le_sum (fun d _ => fbound d)
    _ = _ := by simp [pow_two, Nat.mul_left_comm]

theorem norm_bound (n : ℕ) (hn : 0 < n) (Y : Finset (ℤ × ℤ))
    (hy : ∀ z ∈ Y, z.1^2 + 3*z.2^2 = (n:ℤ)) :
    Y.card ≤ 12 * n.divisors.card^2 :=
  norm_bound_of_primitive 12 primitive_bound n hn Y hy

end QuarticSlice

namespace QuarticSlice
open Finset

private abbrev Triple (A : Finset ℕ) := Fin 3 → ↥A

private def moment {A : Finset ℕ} (k : ℕ) (y : Triple A) : ℤ :=
  ∑ i, ((y i : ℕ) : ℤ)^k

private def coordinates {A : Finset ℕ} (y : Triple A) : ℤ × ℤ :=
  let t (i : Fin 3) := ((y i : ℕ) : ℤ)^2
  (2*t 0 - t 1 - t 2, t 1 - t 2)

private theorem coord_norm {A : Finset ℕ} (y : Triple A) :
    (coordinates y).1^2 + 3*(coordinates y).2^2 =
    6*moment 4 y - 2*(moment 2 y)^2 := by
  simp only [coordinates, moment, Fin.sum_univ_three]
  ring

private theorem coord_inj {A : Finset ℕ} (Y : Finset (Triple A)) (s : ℤ)
    (hs : ∀ y ∈ Y, moment 2 y = s) : Set.InjOn (@coordinates A) (Y : Set (Triple A)) := by
  intro y hy z hz he
  have hu := congrArg Prod.fst he
  have hv := congrArg Prod.snd he
  have hsum := (hs y hy).trans (hs z hz).symm
  dsimp only [coordinates] at hu hv
  simp only [moment, Fin.sum_univ_three] at hsum
  funext i
  apply Subtype.ext
  apply (Nat.pow_left_inj (by decide : (2:ℕ) ≠ 0)).mp
  have h : ((y i : ℕ) : ℤ)^2 = ((z i : ℕ) : ℤ)^2 := by
    have e0 : ((y 0 : ℕ) : ℤ)^2 = ((z 0 : ℕ) : ℤ)^2 := by linarith only [hu,hv,hsum]
    have e1 : ((y 1 : ℕ) : ℤ)^2 = ((z 1 : ℕ) : ℤ)^2 := by linarith only [hu,hv,hsum]
    have e2 : ((y 2 : ℕ) : ℤ)^2 = ((z 2 : ℕ) : ℤ)^2 := by linarith only [hu,hv,hsum]
    fin_cases i <;> assumption
  exact_mod_cast h

private theorem moment_four_bound {A : Finset ℕ} (M : ℕ) (hA : A ⊆ Icc 1 M)
    (y : Triple A) : moment 4 y ≤ 3*(M:ℤ)^4 := by
  calc moment 4 y ≤ ∑ _i : Fin 3, (M:ℤ)^4 := by
         apply sum_le_sum
         intro i _
         exact_mod_cast Nat.pow_le_pow_left (mem_Icc.mp (hA (y i).property)).2 4
       _ = _ := by simp

private theorem divisor_growth (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M n : ℕ, 2 ≤ M → n ≤ 18*M^4 →
      12*(n.divisors.card:ℝ)^2 ≤ C*(M:ℝ)^ε := by
  obtain ⟨C,hC,H⟩ := CubicDivisor.uniform 18 (ε/2) (by linarith)
  refine ⟨3*C+1, by linarith, ?_⟩
  intro M n hM hn
  have hp : M^4 ≤ (M^2)^3 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by decide)
  have h := H (M^2) (by nlinarith) (n : ℤ) (by simpa using hn.trans (Nat.mul_le_mul_left 18 hp))
  have hr : ((M:ℝ)^2)^(ε/2) = (M:ℝ)^ε := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg M)]
    congr 1
    push_cast
    ring
  push_cast at h
  simp only [Int.natAbs_natCast] at h
  rw [hr] at h
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg M) ε]

private theorem assemble
    (norm_count : ∀ (n : ℕ), 0 < n → ∀ (Y : Finset (ℤ × ℤ)),
      (∀ z ∈ Y, z.1^2 + 3*z.2^2 = (n:ℤ)) → Y.card ≤ 12 * n.divisors.card^2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0<C ∧ ∀ M : ℕ, 2≤M → ∀ A : Finset ℕ, A ⊆ Icc 1 M → ∀ h : ℤ,
      (((univ : Finset (Triple A × Triple A)).filter
        (fun z => moment 4 z.1 = moment 4 z.2 ∧ moment 2 z.1 - moment 2 z.2 = h)).card : ℝ)
      ≤ C*(M:ℝ)^ε*(A.card:ℝ)^3 := by
  classical
  obtain ⟨C,hC,H⟩ := divisor_growth ε hε
  refine ⟨C, by linarith, ?_⟩
  intro M hM A hA h
  let R (x y : Triple A) := moment 4 x = moment 4 y ∧ moment 2 x - moment 2 y = h
  have hpow : 1 ≤ (M:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ M)) hε.le
  have fiber (x : Triple A) : (((univ : Finset (Triple A)).filter (R x)).card : ℝ) ≤ C*(M:ℝ)^ε := by
    let Y := (univ : Finset (Triple A)).filter (R x)
    change (Y.card : ℝ) ≤ _
    by_cases hne : Y.Nonempty
    · obtain ⟨r,hr⟩ := hne
      have rr : R x r := (mem_filter.mp hr).2
      have sums (y) (hy : y ∈ Y) : moment 2 y = moment 2 r := by
        have hy' := (show R x y from (mem_filter.mp hy).2).2
        have hr' := rr.2
        omega
      let Z := Y.image coordinates
      have hc : Z.card = Y.card := card_image_of_injOn (coord_inj Y _ sums)
      let d := 6*moment 4 r - 2*(moment 2 r)^2
      have hd0 : 0 ≤ d := by
        dsimp only [d]
        rw [← coord_norm]
        positivity
      have hz (z) (hz : z ∈ Z) : z.1^2 + 3*z.2^2 = (d.toNat:ℤ) := by
        obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
        obtain ⟨e,-⟩ := (show R x y from (mem_filter.mp hy).2)
        rw [Int.toNat_of_nonneg hd0, coord_norm, sums y hy, ← e, rr.1]
      rw [← hc]
      by_cases hd : d.toNat = 0
      · have sub : Z ⊆ {(0,0)} := by
          intro z hmem
          have e := hz z hmem
          rw [hd, Nat.cast_zero] at e
          have h1 : z.1^2 = 0 := by nlinarith [sq_nonneg z.1, sq_nonneg z.2]
          have h2 : z.2^2 = 0 := by nlinarith [sq_nonneg z.1, sq_nonneg z.2]
          exact mem_singleton.mpr (Prod.ext (sq_eq_zero_iff.mp h1) (sq_eq_zero_iff.mp h2))
        have h1 : Z.card ≤ 1 := (card_le_card sub).trans_eq (card_singleton _)
        exact (show (Z.card:ℝ) ≤ 1 by exact_mod_cast h1).trans (one_le_mul_of_one_le_of_one_le hC hpow)
      · have hm : d.toNat ≤ 18*M^4 := by
          have hi : d ≤ 18*(M:ℤ)^4 := by
            dsimp only [d]
            linarith [moment_four_bound M hA r, sq_nonneg (moment 2 r)]
          exact_mod_cast (show ((d.toNat:ℕ):ℤ) ≤ 18*(M:ℤ)^4 by rwa [Int.toNat_of_nonneg hd0])
        exact (show (Z.card:ℝ) ≤ 12*(d.toNat.divisors.card:ℝ)^2 by
          exact_mod_cast norm_count d.toNat (Nat.pos_of_ne_zero hd) Z hz).trans (H M d.toNat hM hm)
    · rw [not_nonempty_iff_eq_empty.mp hne]
      simp only [card_empty, Nat.cast_zero]
      exact (by linarith : 0 ≤ C).trans (le_mul_of_one_le_right (by linarith) hpow)
  have hcount := CubicDefect.total_bound R (C*(M:ℝ)^ε) fiber
  simpa only [R, Triple, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow] using hcount

end QuarticSlice

theorem Conjectures.Goldbach.QuarticSquareSlice : (
by
  classical
  exact ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ M : ℕ, 2≤M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M → ∀ h : ℤ, let w := fun (k : ℕ) (x : Fin 3 → (↥A)) => ∑ i, ((x i : ℕ):ℤ)^k; let triples := (Finset.univ : Finset ((Fin 3 → (↥A)) × (Fin 3 → (↥A)))); ((triples.filter (fun z => w 4 z.1=w 4 z.2 ∧ w 2 z.1-w 2 z.2=h)).card:ℝ) ≤ C*(M:ℝ)^ε*(A.card:ℝ)^3
) := by
  classical
  exact QuarticSlice.assemble QuarticSlice.norm_bound
