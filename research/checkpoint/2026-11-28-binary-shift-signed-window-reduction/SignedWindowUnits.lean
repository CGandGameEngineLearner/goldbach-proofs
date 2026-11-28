import SignedFieldWindows

open Finset Filter
namespace Goldbach.MiddleCanonicalModel
open ShiftWideArc
noncomputable section
open scoped Classical

/-- At a level above one both endpoints are excluded by coprimality.
The remaining closed-window numerators are exactly the canonical representatives
of the residue units. This also reindexes any auxiliary weighted row. -/
theorem sum_numerators_eq_units {q : ℕ} [NeZero q] (hq : 1 < q)
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    (∑ a ∈ GB6Geometry.numerators q, f a) = ∑ u : (ZMod q)ˣ, f (u:ZMod q).val := by
  symm
  refine sum_bij (fun (u : (ZMod q)ˣ) _ => (u:ZMod q).val) ?_ ?_ ?_ ?_
  · intro u _
    exact mem_filter.mpr ⟨mem_range.mpr ((ZMod.val_lt _).trans (Nat.lt_succ_self q)),
      ZMod.val_coe_unit_coprime u⟩
  · intro u _ v _ he
    apply Units.ext
    rw [← ZMod.natCast_zmod_val (u:ZMod q),← ZMod.natCast_zmod_val (v:ZMod q),he]
  · intro a ha
    obtain ⟨ha,hc⟩ := mem_filter.mp ha
    have hle : a ≤ q := Nat.le_of_lt_succ (mem_range.mp ha)
    have hlt : a < q := by
      apply lt_of_le_of_ne hle
      rintro rfl
      simp [Nat.Coprime] at hc
      omega
    have hu := (ZMod.isUnit_iff_coprime a q).mpr hc
    exact ⟨hu.unit,mem_univ _, by rw [hu.unit_spec,ZMod.val_natCast_of_lt hlt]⟩
  · intro u _
    rfl

theorem one_lt_of_mem_bandDenominators {Y q : ℕ} (hq : q ∈ bandDenominators Y) : 1 < q := by
  have hh := (mem_Icc.mp hq).1
  have hlog : 1 ≤ Nat.log 2 (Y+2) := Nat.le_log_of_pow_le (by decide) (by simp)
  have hp : 1 ≤ (Nat.log 2 (Y+2))^2 := one_le_pow₀ hlog
  omega

/-- A signed Fourier row, indexed by units even when written as a total
function of the denominator. The empty zero-denominator convention is harmless. -/
def unitWindowRow (Y q m : ℕ) : ℂ :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ, phase (-(m:ℝ)*(((u:ZMod q).val:ℝ)/q)) *
      centeredMode Y q (u:ZMod q).val m

/-- The signed field coefficient is exactly a sum of unit-indexed rows, with
the same frequency, translation phase and centered interval as its window expansion. -/
theorem eventual_fieldCoefficient_by_units : ∀ᶠ Y : ℕ in atTop, ∀ m : ℕ,
    fieldCoefficient Y m = ∑ q ∈ bandDenominators Y, unitWindowRow Y q m := by
  filter_upwards [eventual_fieldCoefficient_by_window] with Y hY
  intro m
  rw [hY m]
  refine sum_congr rfl fun q hq => ?_
  have hq' := one_lt_of_mem_bandDenominators hq
  have hne : q ≠ 0 := by omega
  letI : NeZero q := ⟨hne⟩
  rw [unitWindowRow,dif_neg hne]
  exact sum_numerators_eq_units hq' _

end
end Goldbach.MiddleCanonicalModel

#print axioms Goldbach.MiddleCanonicalModel.eventual_fieldCoefficient_by_window
#print axioms Goldbach.MiddleCanonicalModel.sum_numerators_eq_units
#print axioms Goldbach.MiddleCanonicalModel.eventual_fieldCoefficient_by_units
