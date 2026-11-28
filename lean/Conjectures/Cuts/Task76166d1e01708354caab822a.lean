import Mathlib
import Conjectures.Goldbach.MajorArcAbelApproximation

namespace GoldbachUniformResidueBridge

open Finset

theorem coprime_iff_isUnit (d a q j : ℕ) (ha : a.Coprime d) :
    (d*j+a).Coprime (d*q) ↔ IsUnit ((d : ZMod q)*(j : ZMod q)+(a : ZMod q)) := by
  have hd : (d*j+a).Coprime d := by
    rw [add_comm (d*j) a, Nat.coprime_add_mul_left_left]
    exact ha
  rw [Nat.coprime_mul_iff_right, and_iff_right hd,
    ← ZMod.isUnit_iff_coprime (d*j+a) q, Nat.cast_add, Nat.cast_mul]

theorem phase_eq_character (q b j : ℕ) [NeZero q] :
    Complex.exp ((-2 : ℂ)*(Real.pi : ℂ)*Complex.I*
      (((b : ℝ)*(j : ℝ)/(q : ℝ)) : ℂ)) =
        ZMod.stdAddChar (-((b : ZMod q)*(j : ZMod q))) := by
  have hcast : -((b : ZMod q)*(j : ZMod q)) = ((-((b*j : ℕ) : ℤ) : ℤ) : ZMod q) := by
    rw [Int.cast_neg, Int.cast_natCast, Nat.cast_mul]
  rw [hcast, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

private theorem sum_range_to_zmod (q : ℕ) [NeZero q] (G : ZMod q → ℂ) :
    (∑ j ∈ range q, G (j : ZMod q)) = ∑ x : ZMod q, G x := by
  refine sum_bij' (fun j _ => (j : ZMod q)) (fun x _ => x.val) ?_ ?_ ?_ ?_ ?_
  · intro j _
    exact mem_univ _
  · intro x _
    exact mem_range.mpr (ZMod.val_lt x)
  · intro j hj
    exact ZMod.val_natCast_of_lt (mem_range.mp hj)
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro j _
    rfl

theorem raw_eq_character (d a q b : ℕ) [NeZero q] (ha : a.Coprime d) :
    (∑ j ∈ (range q).filter (fun j => (d*j+a).Coprime (d*q)),
      Complex.exp ((-2 : ℂ)*(Real.pi : ℂ)*Complex.I*
        (((b : ℝ)*(j : ℝ)/(q : ℝ)) : ℂ))) =
      ∑ x : ZMod q, if IsUnit ((d : ZMod q)*x+(a : ZMod q)) then
        ZMod.stdAddChar (-((b : ZMod q)*x)) else 0 := by
  classical
  let G (x : ZMod q) : ℂ := if IsUnit ((d : ZMod q)*x+(a : ZMod q)) then
    ZMod.stdAddChar (-((b : ZMod q)*x)) else 0
  rw [sum_filter]
  change _ = ∑ x : ZMod q, G x
  calc
    _ = ∑ j ∈ range q, G (j : ZMod q) := by
      apply sum_congr rfl
      intro j _
      simp only [G, coprime_iff_isUnit d a q j ha, phase_eq_character]
    _ = _ := sum_range_to_zmod q G

end GoldbachUniformResidueBridge

namespace GoldbachUniformNoncoprime

/-- A shift in the kernel of multiplication by `d` cancels the sum. -/
theorem sum_eq_zero (d a q b : ℕ) [NeZero q] (hb : b.Coprime q) (hd : ¬ d.Coprime q) :
    (∑ x : ZMod q, if IsUnit ((d : ZMod q) * x + (a : ZMod q))
      then ZMod.stdAddChar (-((b : ZMod q) * x)) else 0) = 0 := by
  classical
  let g := Nat.gcd d q
  let u : ZMod q := ((q / g : ℕ) : ZMod q)
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hgd : g ∣ d := Nat.gcd_dvd_left _ _
  have hgq : g ∣ q := Nat.gcd_dvd_right _ _
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right d hqpos
  have hgn : g ≠ 1 := hd
  have hgOne : 1 < g := by omega
  have hup : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hqpos hgq) hgpos
  have hul : q / g < q := Nat.div_lt_self hqpos hgOne
  have hu : u ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt hup hul ((ZMod.natCast_eq_zero_iff (q / g) q).mp hz)
  have hdu : (d : ZMod q) * u = 0 := by
    change (d : ZMod q) * ((q / g : ℕ) : ZMod q) = 0
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    refine ⟨d / g, ?_⟩
    calc
      d * (q / g) = (d / g * g) * (q / g) := by rw [Nat.div_mul_cancel hgd]
      _ = (q / g * g) * (d / g) := by ac_rfl
      _ = q * (d / g) := by rw [Nat.div_mul_cancel hgq]
  have hbunit : IsUnit (b : ZMod q) := by
    rw [← ZMod.coe_unitOfCoprime b hb]
    exact (ZMod.unitOfCoprime b hb).isUnit
  have hbu : (b : ZMod q) * u ≠ 0 :=
    fun h => hu (hbunit.mul_right_eq_zero.mp h)
  let σ := ZMod.stdAddChar (-((b : ZMod q) * u))
  have hσ : σ ≠ 1 := by
    intro h
    apply hbu
    apply neg_eq_zero.mp
    apply ZMod.injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using h
  let f (x : ZMod q) : ℂ :=
    if IsUnit ((d : ZMod q) * x + (a : ZMod q))
    then ZMod.stdAddChar (-((b : ZMod q) * x)) else 0
  have hEntry (x : ZMod q) : f (x + u) = σ * f x := by
    dsimp only [f, σ]
    simp only [mul_add, hdu, add_zero, neg_add, AddChar.map_add_eq_mul]
    split_ifs <;> ring
  have hSum : (∑ x : ZMod q, f x) = σ * ∑ x : ZMod q, f x := by
    calc
      (∑ x : ZMod q, f x) = ∑ x : ZMod q, f (x + u) :=
        (Fintype.sum_equiv (Equiv.addRight u) (fun x => f (x + u)) f (fun _ => rfl)).symm
      _ = ∑ x : ZMod q, σ * f x := Finset.sum_congr rfl fun x _ => hEntry x
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hProd : (1 - σ) * (∑ x : ZMod q, f x) = 0 := by
    rw [sub_mul, one_mul, ← hSum, sub_self]
  exact (mul_eq_zero.mp hProd).resolve_left (sub_ne_zero.mpr hσ.symm)

end GoldbachUniformNoncoprime

namespace GoldbachUniformCoprime

open Finset

/-- The complete unit sum of the standard character is the Ramanujan sum at one. -/
private theorem unit_sum (q : ℕ) [NeZero q] :
    (∑ x : ZMod q, if IsUnit x then ZMod.stdAddChar x else 0) =
      (ArithmeticFunction.moebius q : ℂ) := by
  classical
  rw [← class_split_aux_ramanujan q 1 (NeZero.pos q) (by simp), sum_filter]
  refine sum_nbij' ZMod.val (fun n : ℕ => (n : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro x _
    exact mem_range.mpr x.val_lt
  · intro n _
    exact mem_univ _
  · intro x _
    exact ZMod.natCast_zmod_val x
  · intro n hn
    exact ZMod.val_natCast_of_lt (mem_range.mp hn)
  · intro x _
    have hiff : IsUnit x ↔ x.val.Coprime q := by
      simpa only [ZMod.natCast_zmod_val] using ZMod.isUnit_iff_coprime x.val q
    by_cases hx : IsUnit x
    · simp only [ite_eq_left hx, ite_eq_left (hiff.mp hx)]
      rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
      unfold abelE
      push_cast
      congr 1
      ring
    · simp only [ite_eq_right hx, ite_eq_right (fun hc => hx (hiff.mpr hc))]

/-- An affine permutation sends the complete coefficient to a unit sum,
up to a character value of norm one. -/
theorem norm_le_one (d a q b : ℕ) [NeZero q] (hb : b.Coprime q) (hd : d.Coprime q) :
    ‖∑ x : ZMod q, if IsUnit ((d : ZMod q) * x + (a : ZMod q)) then
      ZMod.stdAddChar (-((b : ZMod q) * x)) else 0‖ ≤ 1 := by
  classical
  let u : (ZMod q)ˣ := -(ZMod.unitOfCoprime b hb)
  let v := ZMod.unitOfCoprime d hd
  let w := u * v⁻¹
  let c := (w : ZMod q) * (a : ZMod q)
  let E : ZMod q ≃ ZMod q := u.mulLeft.trans (Equiv.addRight c)
  have hu : (u : ZMod q) = -(b : ZMod q) := by simp [u, ZMod.coe_unitOfCoprime]
  have hv : (v : ZMod q) = (d : ZMod q) := ZMod.coe_unitOfCoprime d hd
  have hw : (w : ZMod q) * (d : ZMod q) = (u : ZMod q) := by
    rw [← hv]
    change ((u * v⁻¹ : (ZMod q)ˣ) : ZMod q) * (v : ZMod q) = (u : ZMod q)
    rw [Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
  have hE (x : ZMod q) : E x = (u : ZMod q) * x + c := rfl
  have hunit (x : ZMod q) : IsUnit (E x) ↔ IsUnit ((d : ZMod q) * x + (a : ZMod q)) := by
    rw [hE, ← hw]
    change IsUnit (((w : ZMod q) * (d : ZMod q)) * x + (w : ZMod q) * (a : ZMod q)) ↔ _
    rw [mul_assoc, ← mul_add, Units.isUnit_units_mul]
  have hχ (x : ZMod q) :
      ZMod.stdAddChar (-((b : ZMod q) * x)) = ZMod.stdAddChar (-c) * ZMod.stdAddChar (E x) := by
    rw [← AddChar.map_add_eq_mul, hE, hu]
    congr 1
    ring
  have hsum :
      (∑ x : ZMod q, if IsUnit ((d : ZMod q) * x + (a : ZMod q)) then
        ZMod.stdAddChar (-((b : ZMod q) * x)) else 0) =
      ZMod.stdAddChar (-c) * (∑ x : ZMod q, if IsUnit x then ZMod.stdAddChar x else 0) := by
    rw [← E.sum_comp (fun x => if IsUnit x then ZMod.stdAddChar x else 0), mul_sum]
    apply sum_congr rfl
    intro x _
    by_cases hx : IsUnit ((d : ZMod q) * x + (a : ZMod q))
    · simpa only [ite_eq_left hx, ite_eq_left ((hunit x).mpr hx)] using hχ x
    · simp only [ite_eq_right hx, ite_eq_right (fun hEx => hx ((hunit x).mp hEx)), mul_zero]
  have hphase : ‖ZMod.stdAddChar (-c)‖ = 1 := by
    rw [ZMod.stdAddChar_apply, Circle.norm_coe]
  rw [hsum, norm_mul, hphase, one_mul, unit_sum]
  rcases ArithmeticFunction.moebius_eq_or q with h | h | h <;> simp [h]

end GoldbachUniformCoprime

theorem Conjectures.Cuts.Task76166d1e01708354caab822a :
      ∀ d : ℕ, 2 ≤ d → ∀ a : ℕ, a < d → a.Coprime d →
        ∀ q : ℕ, 0 < q → ∀ b : ℕ, b ≤ q → b.Coprime q →
          let e := fun u : ℝ => Complex.exp ((-2:ℂ)*(Real.pi:ℂ)*Complex.I*(u:ℂ))
          ‖∑ j ∈ (Finset.range q).filter (fun j => (d*j+a).Coprime (d*q)),
            e ((b:ℝ)*(j:ℝ)/(q:ℝ))‖ ≤ if d.Coprime q then (1:ℝ) else 0 := by
  intro d hd a ha haCo q hq b hb hbCo
  let nz : NeZero q := ⟨hq.ne'⟩
  dsimp only
  have hBridge := GoldbachUniformResidueBridge.raw_eq_character d a q b haCo
  push_cast at hBridge ⊢
  rw [hBridge]
  by_cases hcop : d.Coprime q
  · rw [ite_eq_left hcop]
    exact GoldbachUniformCoprime.norm_le_one d a q b hbCo hcop
  · rw [ite_eq_right hcop,
      GoldbachUniformNoncoprime.sum_eq_zero d a q b hbCo hcop, norm_zero]
