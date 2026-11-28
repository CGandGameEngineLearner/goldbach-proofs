import Mathlib

open scoped BigOperators ComplexConjugate
open Finset DirichletCharacter

namespace RamifiedJacobiMoment
noncomputable section

def jac {q : ℕ} [NeZero q] (m : ZMod q) (a b : DirichletCharacter ℂ q) :=
  ∑ x : ZMod q, a x * b (m-x)

theorem jac_units {q : ℕ} [NeZero q] (m : ZMod q) (a b : DirichletCharacter ℂ q) :
    jac m a b = ∑ u : (ZMod q)ˣ, a (m-(u:ZMod q))*b u := by
  classical
  let f := fun x : ZMod q => a (m-x)*b x
  have re : jac m a b = ∑ x, f x := by
    rw [← (Equiv.subLeft m).sum_comp f]
    apply sum_congr rfl
    intro x _
    simp [f, Equiv.subLeft_apply]
  have sub : ∑ x ∈ univ.filter IsUnit, f x = ∑ x, f x := by
    apply sum_subset (filter_subset ..)
    intro x _ hx
    have hu : ¬IsUnit x := fun h => hx (mem_filter.mpr ⟨mem_univ x,h⟩)
    simp [f,b.map_nonunit hu]
  have sets : (univ : Finset (ZMod q)).filter IsUnit =
      (univ : Finset (ZMod q)ˣ).map ⟨(↑), Units.val_injective⟩ := by
    ext x
    simp [IsUnit]
  rw [re, ← sub, sets, sum_map]
  rfl

theorem kernel {q : ℕ} [NeZero q] (u v : (ZMod q)ˣ) :
    ∑ b : DirichletCharacter ℂ q, b u * conj (b v) =
       if u=v then (q.totient:ℂ) else 0 := by
  have cc (b : DirichletCharacter ℂ q) : conj (b v) = b (v:ZMod q)⁻¹ := by
    rw [← Complex.inv_eq_conj (b.unit_norm_eq_one v), ZMod.inv_coe_unit, map_units_inv]
  calc
    _ = ∑ b : DirichletCharacter ℂ q, b (v:ZMod q)⁻¹ * b u := by
      apply sum_congr rfl
      intro b _
      rw [cc, mul_comm]
    _ = _ := by
      rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ v.isUnit (u:ZMod q)]
      by_cases h : u = v
      · simp [h]
      · have h' : (v:ZMod q) ≠ (u:ZMod q) := fun e => h (Units.ext e.symm)
        simp [h,h']

theorem parseval {q : ℕ} [NeZero q] (w : (ZMod q)ˣ → ℂ) :
    (∑ b : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, w u*b u‖^2) =
        (q.totient:ℝ) * ∑ u, ‖w u‖^2 := by
  classical
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, map_mul]
  calc
    _ = ∑ b : DirichletCharacter ℂ q, ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
      (w u * conj (w v))*(b u * conj (b v)) := by
        apply sum_congr rfl
        intro b _
        rw [sum_mul]
        apply sum_congr rfl
        intro u _
        rw [mul_sum]
        exact sum_congr rfl (fun _ _ => by ring)
    _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, (w u * conj (w v))*
      (if u=v then (q.totient:ℂ) else 0) := by
        rw [sum_comm]
        apply sum_congr rfl
        intro u _
        rw [sum_comm]
        apply sum_congr rfl
        intro v _
        rw [← Finset.mul_sum,kernel]
    _ = _ := by simp [Finset.mul_sum, mul_comm]

theorem bound {q : ℕ} [NeZero q] (m : ZMod q) (hm : IsNilpotent m)
    (a : DirichletCharacter ℂ q) (F : Finset (DirichletCharacter ℂ q)) :
    ∑ b ∈ F, ‖jac m a b / jac m 1 1‖^3 ≤ 1 := by
  classical
  have good (u : (ZMod q)ˣ) : IsUnit (m-(u:ZMod q)) := by
    rw [sub_eq_add_neg]
    exact hm.isUnit_add_right_of_commute u.isUnit.neg (Commute.all ..)
  have ordinary : jac m 1 1 = (q.totient:ℂ) := by
    rw [jac_units]
    simp only [MulChar.one_apply (good _), MulChar.one_apply_coe, one_mul]
    simp [ZMod.card_units_eq_totient]
  let w := fun u : (ZMod q)ˣ => a (m-(u:ZMod q))
  have unit (u : (ZMod q)ˣ) : ‖w u‖=1 := by
    simpa [w] using a.unit_norm_eq_one (good u).unit
  have cap (b : DirichletCharacter ℂ q) : ‖jac m a b‖ ≤ q.totient := by
    rw [jac_units]
    calc
      _ ≤ ∑ u : (ZMod q)ˣ, ‖w u * b u‖ := norm_sum_le ..
      _ = _ := by simp [unit,ZMod.card_units_eq_totient]
  have allsq : (∑ b : DirichletCharacter ℂ q, ‖jac m a b‖^2) = (q.totient:ℝ)^2 := by
    simp_rw [jac_units]
    simpa only [unit, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one,
      ZMod.card_units_eq_totient, sq] using parseval w
  have pos : 0 < (q.totient:ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  simp_rw [ordinary,norm_div,Complex.norm_natCast,div_pow]
  rw [← sum_div, div_le_one (pow_pos pos 3)]
  calc
    _ ≤ ∑ b ∈ F, (q.totient:ℝ)*‖jac m a b‖^2 := by
      apply sum_le_sum
      intro b _
      calc
        _ = ‖jac m a b‖ * ‖jac m a b‖^2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (cap b) (sq_nonneg _)
    _ ≤ ∑ b : DirichletCharacter ℂ q, (q.totient:ℝ)*‖jac m a b‖^2 :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => by positivity)
    _ = _ := by rw [← Finset.mul_sum, allsq]; ring

end
end RamifiedJacobiMoment

theorem Conjectures.Cuts.Task20f2602ec4088c9db5dcb4ab : (∀ (x1 x2 x3 : ℕ) [x4 : NeZero (x1 ^ x2)],   Nat.Prime x1 →     (0 : ℕ) < x2 →       Even x3 →         x1 ∣ x3 →           ∀ (x9 : DirichletCharacter ℂ (x1 ^ x2)) (x10 : Finset (DirichletCharacter ℂ (x1 ^ x2))),             have x11 : DirichletCharacter ℂ (x1 ^ x2) → DirichletCharacter ℂ (x1 ^ x2) → ℂ := fun (x11 x12 : DirichletCharacter ℂ (x1 ^ x2)) => ∑ x13 : ZMod (x1 ^ x2), x11 x13 * x12 (↑x3 - x13);             ∑ x12 ∈ x10, ‖x11 x9 x12 / x11 (1 : DirichletCharacter ℂ (x1 ^ x2)) (1 : DirichletCharacter ℂ (x1 ^ x2))‖ ^ (3 : ℕ) ≤ (1 : ℝ)) := by
  intro p e m _ _ _ _ hd a F J
  apply RamifiedJacobiMoment.bound
  obtain ⟨c,rfl⟩ := hd
  refine ⟨e, ?_⟩
  rw [Nat.cast_mul, mul_pow, ← Nat.cast_pow]
  simp
