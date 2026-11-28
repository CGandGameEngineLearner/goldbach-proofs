import Mathlib

open scoped BigOperators ComplexConjugate
open Finset DirichletCharacter

namespace CubicLocal

private theorem conj_char {q : ℕ} (χ : DirichletCharacter ℂ q) (u : (ZMod q)ˣ) :
    conj (χ (u : ZMod q)) = χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) := by
  have h := Complex.mul_conj' (χ (u : ZMod q))
  rw [χ.unit_norm_eq_one u] at h
  norm_num at h
  calc
    _ = χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) *
        (χ (u : ZMod q) * conj (χ (u : ZMod q))) := by
      rw [← mul_assoc, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        map_one, one_mul]
    _ = _ := by rw [h, mul_one]

theorem parseval_row {q : ℕ} [NeZero q] (f : (ZMod q)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)‖ ^ 2) =
      (q.totient : ℝ) * ∑ u, ‖f u‖ ^ 2 := by
  classical
  have orth (u v : (ZMod q)ˣ) :
      (∑ χ : DirichletCharacter ℂ q, χ (u : ZMod q) * conj (χ (v : ZMod q))) =
        if u = v then (q.totient : ℂ) else 0 := by
    simp_rw [conj_char, ← ZMod.inv_coe_unit]
    simpa only [Units.val_inj, eq_comm, mul_comm] using
      (DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) v.isUnit (u : ZMod q))
  rw [← Complex.ofReal_inj]
  push_cast
  simp_rw [← Complex.mul_conj']
  -- A complex equality proof also avoids converting intermediate sums in ℝ.
  have ex (χ : DirichletCharacter ℂ q) :
      (∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)) *
        conj (∑ u : (ZMod q)ˣ, f u * χ (u : ZMod q)) =
      ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
        (f u * conj (f v)) * (χ (u : ZMod q) * conj (χ (v : ZMod q))) := by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_mul]
    ring
  simp_rw [ex]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orth, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  ring

theorem sum_units_supported {q : ℕ} [NeZero q] (F : ZMod q → ℂ)
    (hF : ∀ x, ¬ IsUnit x → F x = 0) :
    (∑ x : ZMod q, F x) = ∑ u : (ZMod q)ˣ, F (u : ZMod q) := by
  classical
  let v : (ZMod q)ˣ ↪ ZMod q := ⟨Units.val, Units.val_injective⟩
  have hmap : (Finset.univ : Finset (ZMod q)ˣ).map v = Finset.univ.filter IsUnit := by
    ext x
    simp [v, IsUnit]
  change _ = ∑ u : (ZMod q)ˣ, F (v u)
  rw [← Finset.sum_map]
  rw [hmap, Finset.sum_filter]
  exact Finset.sum_congr rfl fun x _ => by
    by_cases hx : IsUnit x
    · simp [hx]
    · simpa [hx] using hF x hx

theorem isUnit_reflect_of_dvd {p e m : ℕ} [NeZero (p^e)]
    (hp : p.Prime) (he : 0 < e) (hm : p ∣ m) (x : ZMod (p^e)) :
    IsUnit ((m : ZMod (p^e)) - x) ↔ IsUnit x := by
  have hpe : p ∣ p^e := dvd_pow_self p he.ne'
  let c : ZMod (p^e) →+* ZMod p := ZMod.castHom hpe _
  have test (u : ZMod (p^e)) : IsUnit u ↔ c u ≠ 0 := by
    conv_lhs => rw [← ZMod.natCast_zmod_val u]
    conv_rhs => rw [← ZMod.natCast_zmod_val u]
    rw [map_natCast]
    exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp he).trans
      (not_congr (ZMod.natCast_eq_zero_iff u.val p)).symm
  rw [test, test, map_sub, map_natCast, (ZMod.natCast_eq_zero_iff m p).mpr hm, zero_sub, neg_ne_zero]

theorem local_divides (p e m : ℕ) [NeZero (p ^ e)] (hp : p.Prime) (he : 0 < e)
    (_hmEven : Even m) (hm : p ∣ m)
    (a : DirichletCharacter ℂ (p^e)) (T : Finset (DirichletCharacter ℂ (p^e))) :
    let Jm := fun (A B : DirichletCharacter ℂ (p ^ e)) =>
      ∑ x : ZMod (p ^ e), A x * B ((m : ZMod (p ^ e)) - x)
    (∑ b ∈ T, ‖Jm a b / Jm 1 1‖ ^ 3) ≤ 1 := by
  classical
  let Jm := fun (A B : DirichletCharacter ℂ (p ^ e)) =>
    ∑ x : ZMod (p ^ e), A x * B ((m : ZMod (p ^ e)) - x)
  let f (a : DirichletCharacter ℂ (p^e)) (u : (ZMod (p^e))ˣ) :=
    a ((m : ZMod (p^e)) - (u : ZMod (p^e)))
  have norm_f (a : DirichletCharacter ℂ (p^e)) (u : (ZMod (p^e))ˣ) : ‖f a u‖ = 1 := by
    exact a.unit_norm_eq_one ((isUnit_reflect_of_dvd hp he hm _).mpr u.isUnit).unit
  have jj (a b : DirichletCharacter ℂ (p^e)) :
      Jm a b = ∑ u : (ZMod (p^e))ˣ, f a u * b (u : ZMod (p^e)) := by
    let k : ZMod (p^e) ≃ ZMod (p^e) :=
      ⟨fun x => (m : ZMod (p ^ e)) - x, fun x => (m : ZMod (p ^ e)) - x,
        fun x => sub_sub_cancel _ _, fun x => sub_sub_cancel _ _⟩
    unfold Jm
    rw [← Equiv.sum_comp k]
    change (∑ x : ZMod (p^e), a ((m : ZMod (p^e)) - x) *
      b ((m : ZMod (p^e)) - ((m : ZMod (p^e)) - x))) = _
    simp only [sub_sub_cancel]
    exact sum_units_supported (fun x => a ((m : ZMod (p^e)) - x) * b x) (fun x hx => by rw [b.map_nonunit hx, mul_zero])
  have den : Jm 1 1 = ((p^e).totient : ℂ) := by
    rw [jj]
    have one_on (u : (ZMod (p^e))ˣ) : f 1 u = 1 :=
      MulChar.one_apply ((isUnit_reflect_of_dvd hp he hm _).mpr u.isUnit)
    simp only [one_on, MulChar.one_apply_coe, mul_one, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [Finset.card_univ, ZMod.card_units_eq_totient]
  have hnormDen : ‖Jm 1 1‖ = ((p^e).totient : ℝ) := by
    rw [den, Complex.norm_natCast]
  have hpos : 0 < ((p^e).totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos (p^e))
  have point (b : DirichletCharacter ℂ (p^e)) : ‖Jm a b / Jm 1 1‖ ≤ 1 := by
    rw [norm_div, hnormDen, div_le_one hpos, jj]
    refine (norm_sum_le Finset.univ (fun u : (ZMod (p^e))ˣ => f a u * b (↑u))).trans ?_
    calc
      _ = ∑ _u : (ZMod (p^e))ˣ, (1 : ℝ) := Finset.sum_congr rfl (fun u _ => by
        rw [norm_mul, norm_f, b.unit_norm_eq_one u, one_mul])
      _ = ((p^e).totient : ℝ) := by simp [ZMod.card_units_eq_totient]
      _ ≤ _ := le_rfl
  have energy : (∑ b : DirichletCharacter ℂ (p^e), ‖Jm a b‖ ^ 2) = ((p^e).totient : ℝ) ^ 2 := by
    simp_rw [jj]
    rw [parseval_row, pow_two]
    congr 1
    simp [norm_f, ZMod.card_units_eq_totient]
  have normalized_energy :
      (∑ b : DirichletCharacter ℂ (p^e), ‖Jm a b / Jm 1 1‖ ^ 2) = 1 := by
    simp_rw [norm_div, div_pow, hnormDen]
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, energy, mul_inv_cancel₀ (pow_ne_zero _ hpos.ne')]
  change (∑ b ∈ T, ‖Jm a b / Jm 1 1‖ ^ 3) ≤ 1
  calc
    _ ≤ ∑ b ∈ T, ‖Jm a b / Jm 1 1‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro b _
      rw [pow_succ]
      exact mul_le_of_le_one_right (by positivity) (point b)
    _ ≤ ∑ b : DirichletCharacter ℂ (p^e), ‖Jm a b / Jm 1 1‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun b _ _ => pow_nonneg (norm_nonneg _) _)
    _ = _ := normalized_energy

end CubicLocal

theorem Conjectures.Cuts.Task20f2602ec4088c9db5dcb4ab : (∀ (x1 x2 x3 : ℕ) [x4 : NeZero (x1 ^ x2)],   Nat.Prime x1 →     (0 : ℕ) < x2 →       Even x3 →         x1 ∣ x3 →           ∀ (x9 : DirichletCharacter ℂ (x1 ^ x2)) (x10 : Finset (DirichletCharacter ℂ (x1 ^ x2))),             have x11 : DirichletCharacter ℂ (x1 ^ x2) → DirichletCharacter ℂ (x1 ^ x2) → ℂ := fun (x11 x12 : DirichletCharacter ℂ (x1 ^ x2)) => ∑ x13 : ZMod (x1 ^ x2), x11 x13 * x12 (↑x3 - x13);             ∑ x12 ∈ x10, ‖x11 x9 x12 / x11 (1 : DirichletCharacter ℂ (x1 ^ x2)) (1 : DirichletCharacter ℂ (x1 ^ x2))‖ ^ (3 : ℕ) ≤ (1 : ℝ)) :=
  CubicLocal.local_divides
