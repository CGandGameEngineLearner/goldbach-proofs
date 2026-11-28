import Mathlib

/- Standalone proof of the nondividing local cubic moment.
   The finite-field norm table is adapted from the accepted SharpSingularSeriesRatios
   proof, and the primitive norm identity follows the DFT approach used there.
   All external formal dependencies in this file are Mathlib. -/

/- OrdinaryPP -/
open scoped BigOperators
open Finset DirichletCharacter

namespace CubicLocal

private theorem finEquiv_cast (n : ℕ) [NeZero n] (i : Fin n) :
    ZMod.finEquiv n i = (i.val : ZMod n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    apply Fin.ext
    change i.val = i.val % (n+1)
    exact (Nat.mod_eq_of_lt i.isLt).symm

theorem reduce_sum {A : Type*} [AddCommMonoid A] {d p : ℕ} [NeZero d] [NeZero p]
    [NeZero (d*p)] (f : ZMod p → A) :
    (∑ x : ZMod (d*p), f (ZMod.castHom (dvd_mul_left p d) _ x)) =
      d • ∑ z : ZMod p, f z := by
  classical
  let E : Fin d × Fin p ≃ ZMod (d*p) :=
    finProdFinEquiv.trans (ZMod.finEquiv (d*p)).toEquiv
  let c : ZMod (d*p) →+* ZMod p := ZMod.castHom (dvd_mul_left p d) _
  have he (v : Fin d × Fin p) : c (E v) = ZMod.finEquiv p v.2 := by
    change c (ZMod.finEquiv (d*p) (finProdFinEquiv v)) = ZMod.finEquiv p v.2
    rw [finEquiv_cast, finEquiv_cast, map_natCast]
    change ((v.2.val + p * v.1.val : ℕ) : ZMod p) = (v.2.val : ZMod p)
    simp
  calc
    _ = ∑ v : Fin d × Fin p, f (c (E v)) := (Equiv.sum_comp E _).symm
    _ = ∑ v : Fin d × Fin p, f (ZMod.finEquiv p v.2) := Finset.sum_congr rfl fun v _ => congrArg f (he v)
    _ = d • ∑ i : Fin p, f (ZMod.finEquiv p i) := by
      rw [Fintype.sum_prod_type]
      simp
    _ = _ := congrArg (d • ·) (Equiv.sum_comp (ZMod.finEquiv p).toEquiv f)

private theorem unit_iff_c {p j : ℕ} (hp : p.Prime)
    [NeZero p] [NeZero (p^j*p)] (x : ZMod (p^j*p)) :
    IsUnit x ↔ ZMod.castHom (dvd_mul_left p (p^j)) (ZMod p) x ≠ 0 := by
  let c : ZMod (p^j*p) →+* ZMod p := ZMod.castHom (dvd_mul_left p (p^j)) _
  change IsUnit x ↔ c x ≠ 0
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  conv_rhs => rw [← ZMod.natCast_zmod_val x]
  rw [map_natCast, ZMod.isUnit_iff_coprime]
  have C (n : ℕ) : n.Coprime (p^j*p) ↔ ¬p ∣ n := by
    rw [← pow_succ, Nat.coprime_pow_right_iff (Nat.succ_pos _), Nat.coprime_comm, hp.coprime_iff_not_dvd]
  exact (C x.val).trans (not_congr (ZMod.natCast_eq_zero_iff x.val p)).symm

private theorem count_complement_two {r : Type*} [Fintype r] [DecidableEq r]
    (a b : r) (hab : a ≠ b) :
    (∑ x : r, if x ≠ a ∧ x ≠ b then (1:ℂ) else 0) =
      (Fintype.card r : ℂ) - 2 := by
  have hs : (Finset.univ : Finset r).filter (fun x => x ≠ a ∧ x ≠ b) =
      (Finset.univ.erase a).erase b := by
    ext x
    simp [and_comm]
  have hb : b ∈ (Finset.univ : Finset r).erase a := by simp [Ne.symm hab]
  have ha : a ∈ (Finset.univ : Finset r) := Finset.mem_univ _
  have one : 1 ≤ ((Finset.univ : Finset r).erase a).card :=
    Finset.card_pos.mpr ⟨b, hb⟩
  have two : 1 ≤ (Finset.univ : Finset r).card :=
    Finset.card_pos.mpr ⟨a, ha⟩
  rw [← Finset.sum_filter, hs, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_erase_of_mem hb, Nat.cast_sub one, Finset.card_erase_of_mem ha,
    Nat.cast_sub two, Finset.card_univ]
  push_cast
  ring


theorem ordinary_norm_pp {p j m : ℕ} (hp : p.Prime) [NeZero (p^j*p)] (hm : ¬p ∣ m) :
    ‖∑ x : ZMod (p^j*p), (1 : DirichletCharacter ℂ (p^j*p)) x *
      (1 : DirichletCharacter ℂ (p^j*p)) ((m : ZMod (p^j*p))-x)‖ =
      (p:ℝ)^j * ((p:ℝ)-2) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p^j) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let c : ZMod (p^j*p) →+* ZMod p := ZMod.castHom (dvd_mul_left p (p^j)) _
  have H (x : ZMod (p^j*p)) : IsUnit x ↔ c x ≠ 0 := unit_iff_c hp x
  have H' (x : ZMod (p^j*p)) : IsUnit ((m : ZMod (p^j*p))-x) ↔ c x ≠ (m : ZMod p) := by
    rw [H, map_sub, map_natCast]
    simp [sub_eq_zero, ne_comm]
  let f (v : ZMod p) : ℂ := if v ≠ 0 ∧ v ≠ (m : ZMod p) then 1 else 0
  have term (x : ZMod (p^j*p)) :
      (1 : DirichletCharacter ℂ (p^j*p)) x *
        (1 : DirichletCharacter ℂ (p^j*p)) ((m : ZMod (p^j*p))-x) = f (c x) := by
    by_cases xunit : IsUnit x <;> by_cases yunit : IsUnit ((m : ZMod (p^j*p))-x)
    all_goals simp [f, xunit, yunit, MulChar.one_apply, MulChar.map_nonunit, ← H, ← H']
  simp only [term]
  change ‖∑ x : ZMod (p^j*p), f (c x)‖ = _
  rw [show (∑ x : ZMod (p^j*p), f (c x)) = (p^j) • ∑ z : ZMod p, f z from reduce_sum f]
  have nz : (m : ZMod p) ≠ 0 := (not_congr (ZMod.natCast_eq_zero_iff m p)).mpr hm
  have cnt : (∑ z : ZMod p, f z) = (p : ℂ) - 2 := by
    dsimp only [f]
    simpa [ZMod.card] using count_complement_two (0 : ZMod p) (m : ZMod p) nz.symm
  rw [cnt, nsmul_eq_mul, norm_mul, Complex.norm_natCast, Nat.cast_pow]
  congr 1
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hpR)]



end CubicLocal

/- RowParseval -/
open scoped BigOperators ComplexConjugate
open Finset DirichletCharacter

namespace CubicMass

theorem char_parseval {q : ℕ} [NeZero q]
    (g : ZMod q → ℂ) (hg : ∀ v, ¬IsUnit v → g v = 0) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ v : ZMod q, g v * χ v‖^2) =
      (q.totient : ℝ) * ∑ v : ZMod q, ‖g v‖^2 := by
  classical
  let A (χ : DirichletCharacter ℂ q) := ∑ v : ZMod q, g v * χ v
  have orth (u v : ZMod q) (hv : IsUnit v) :
      (∑ χ : DirichletCharacter ℂ q, χ u * conj (χ v)) =
        if u = v then (q.totient:ℂ) else 0 := by
    have hvv : v * (Ring.inverse v) = 1 := Ring.mul_inverse_cancel _ hv
    have E : u * (Ring.inverse v) = 1 ↔ u = v := by
      constructor
      · intro he
        calc
          u = u * ((Ring.inverse v) * v) := by rw [mul_comm ((Ring.inverse v)) v, hvv, mul_one]
          _ = v := by rw [← mul_assoc, he, one_mul]
      · intro he
        rw [he, hvv]
    simp_rw [← Complex.star_def, MulChar.star_apply', MulChar.inv_apply, ← map_mul]
    rw [sum_characters_eq]
    simp only [E]
  have expand (χ : DirichletCharacter ℂ q) :
      A χ * conj (A χ) =
        ∑ u : ZMod q, ∑ v : ZMod q, g u * conj (g v) * (χ u * conj (χ v)) := by
    simp only [A, map_sum, map_mul]
    rw [sum_mul]
    refine sum_congr rfl (fun u _ => ?_)
    rw [mul_sum]
    refine sum_congr rfl (fun v _ => ?_)
    ring
  apply Complex.ofReal_injective
  push_cast
  calc
    (∑ χ : DirichletCharacter ℂ q, (‖A χ‖:ℂ)^2)
      = ∑ χ, A χ * conj (A χ) := by simp [Complex.mul_conj']
    _ = ∑ u : ZMod q, ∑ v : ZMod q, g u * conj (g v) *
        ∑ χ : DirichletCharacter ℂ q, χ u * conj (χ v) := by
      simp only [expand, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl (fun u _ => sum_comm)
    _ = ∑ u : ZMod q, (q.totient:ℂ) * (g u * conj (g u)) := by
      refine sum_congr rfl (fun u _ => ?_)
      calc
        _ = ∑ v : ZMod q, if u = v then g u * conj (g u) * (q.totient:ℂ) else 0 := by
          refine sum_congr rfl (fun v _ => ?_)
          by_cases hv : IsUnit v
          · rw [orth u v hv]
            split_ifs with h
            · subst v; rfl
            · rw [mul_zero]
          · by_cases h : u = v
            · subst v; simp [hg _ hv]
            · simp [h, hg _ hv]
        _ = _ := by simp [mul_comm]
    _ = (q.totient:ℂ) * ∑ v : ZMod q, (‖g v‖:ℂ)^2 := by
      simp [mul_sum, Complex.mul_conj']

end CubicMass

open scoped BigOperators
open Finset DirichletCharacter

namespace CubicMass

noncomputable def jacobi {q : ℕ} [NeZero q] (a b : DirichletCharacter ℂ q) (m : ZMod q) : ℂ :=
  ∑ v : ZMod q, a v * b (m-v)

theorem jacobi_row_parseval {q : ℕ} [NeZero q] (a : DirichletCharacter ℂ q) (m : ZMod q) :
    (∑ b : DirichletCharacter ℂ q, ‖jacobi a b m‖^2) =
      (q.totient : ℝ) * ‖jacobi 1 1 m‖ := by
  classical
  let g (v : ZMod q) : ℂ := if IsUnit v then a (m-v) else 0
  let h (v : ZMod q) : ℝ := if IsUnit v ∧ IsUnit (m-v) then 1 else 0
  have G (v : ZMod q) (hv : ¬IsUnit v) : g v = 0 := ite_eq_right hv
  have eqJ (b : DirichletCharacter ℂ q) :
      (∑ v : ZMod q, g v * b v) = jacobi a b m := by
    have E (v : ZMod q) : g v * b v = a (m-v) * b v := by
      by_cases hv : IsUnit v
      · simp [g, hv]
      · simp [g, hv, MulChar.map_nonunit b hv]
    simp only [E, jacobi]
    simpa only [Equiv.subLeft_apply, sub_sub_cancel] using
      Equiv.sum_comp (Equiv.subLeft m) (fun v : ZMod q => a v * b (m-v))
  have ht (v : ZMod q) : ‖g v‖^2 = h v := by
    by_cases hv : IsUnit v
    · by_cases hw : IsUnit (m-v)
      · have H : ‖a (m-v)‖ = 1 := by simpa only [hw.unit_spec] using a.unit_norm_eq_one hw.unit
        simp [g, h, hv, hw, H]
      · simp [g, h, hv, hw, MulChar.map_nonunit a hw]
    · simp [g, h, hv]
  have Lt (v : ZMod q) :
      (1 : DirichletCharacter ℂ q) v * (1 : DirichletCharacter ℂ q) (m-v) = (h v : ℂ) := by
    by_cases hv : IsUnit v <;> by_cases hw : IsUnit (m-v) <;>
      simp [h, hv, hw, MulChar.one_apply, MulChar.map_nonunit]
  have eqO : ‖jacobi (1 : DirichletCharacter ℂ q) 1 m‖ = ∑ v, h v := by
    rw [jacobi]
    simp only [Lt, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (Finset.sum_nonneg (fun _ _ => by dsimp [h]; split_ifs <;> norm_num))
  simpa only [eqJ, ht, ← eqO] using char_parseval g G

theorem jacobi_normalized_row_parseval {q : ℕ} [NeZero q] (a : DirichletCharacter ℂ q)
    (m : ZMod q) (ho : 0 < ‖jacobi (1 : DirichletCharacter ℂ q) 1 m‖) :
    (∑ b : DirichletCharacter ℂ q, ‖jacobi a b m / jacobi 1 1 m‖^2) =
      (q.totient : ℝ) / ‖jacobi (1 : DirichletCharacter ℂ q) 1 m‖ := by
  simp only [norm_div, div_pow, ← Finset.sum_div, jacobi_row_parseval]
  field_simp

end CubicMass

/- LocalHigh -/
open scoped BigOperators Classical
open Finset DirichletCharacter

namespace CubicMass.High

noncomputable def J {q : ℕ} [NeZero q] (A B : DirichletCharacter ℂ q) (m : ZMod q) : ℂ :=
  ∑ x : ZMod q, A x * B (m - x)

theorem J_comm {q : ℕ} [NeZero q] (A B : DirichletCharacter ℂ q) (m : ZMod q) :
    J A B m = J B A m := by
  let f := fun x : ZMod q => A x * B (m-x)
  unfold J
  calc
    _ = ∑ x : ZMod q, f (m - x) := (Equiv.sum_comp (Equiv.subLeft m) f).symm
    _ = _ := by
      apply sum_congr rfl
      intro x _
      simp [f, mul_comm]

noncomputable def cap (p : ℕ) : ℝ := 1 + (((p : ℝ) - 2)^2)⁻¹

/-- Signature of the verified PrimePowerTwistedGoldbachDensity.mixed_vanishes. -/
def Mixed : Prop :=
  ∀ {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (hf : 1 < f) (support : ∀ a : ℕ, a.Coprime d → a.Coprime f)
    {χ : DirichletCharacter ℂ (d*f)}, χ.IsPrimitive →
    ∀ (ψ : DirichletCharacter ℂ d) (m : ZMod (d*f)),
      J χ (changeLevel (dvd_mul_right d f) ψ) m = 0

/-- Signature of the verified PrimePowerTwistedGoldbachDensity.both_lifted. -/
def Both : Prop :=
  ∀ {d f : ℕ} [NeZero d] [NeZero f] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f)
    (χ ψ : DirichletCharacter ℂ d) (m : ZMod (d*f)),
      J (changeLevel (dvd_mul_right d f) χ) (changeLevel (dvd_mul_right d f) ψ) m =
      (f:ℂ) * J χ ψ (ZMod.castHom (dvd_mul_right d f) (ZMod d) m)

/-- Normalized character row bound when both characters are primitive. -/
def Primitive : Prop :=
  ∀ (p e m : ℕ) [NeZero (p ^ e)], p.Prime → 2 ≤ e → Even m → ¬p ∣ m →
    ∀ (A : DirichletCharacter ℂ (p ^ e)) (T : Finset (DirichletCharacter ℂ (p ^ e))),
      A.IsPrimitive → (∀ B ∈ T, B.IsPrimitive) →
       (∑ B ∈ T, ‖J A B (m : ZMod (p ^ e)) / J 1 1 (m : ZMod (p ^ e))‖^3) ≤ cap p

def PrimeLevel : Prop :=
  ∀ (p m : ℕ) [NeZero (p ^ 1)], p.Prime → Even m → ¬p ∣ m →
    ∀ (A : DirichletCharacter ℂ (p ^ 1)) (T : Finset (DirichletCharacter ℂ (p ^ 1))),
      (∑ B ∈ T, ‖J A B (m : ZMod (p ^ 1)) / J 1 1 (m : ZMod (p ^ 1))‖^3) ≤ cap p

theorem not_primitive_lifts {p k : ℕ} (hp : p.Prime) [NeZero (p^k * p)] :
    ∀ A : DirichletCharacter ℂ (p^k * p), ¬A.IsPrimitive →
      ∃ A₀ : DirichletCharacter ℂ (p^k), changeLevel (dvd_mul_right (p^k) p) A₀ = A := by
  intro A hA
  have hd : A.conductor ∣ p^(k+1) := by
    rw [pow_succ]
    exact A.conductor_dvd_level
  obtain ⟨j, hj, hc⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hj' : j ≤ k := by
    by_contra! h
    have hj_eq : j = k+1 := by omega
    apply hA
    simpa only [DirichletCharacter.IsPrimitive, pow_succ, hj_eq] using hc
  have hCd : A.conductor ∣ p^k := hc ▸ Nat.pow_dvd_pow p hj'
  refine ⟨changeLevel hCd A.primitiveCharacter, ?_⟩
  rw [← changeLevel_trans, changeLevel_primitiveCharacter]

private theorem cancel_factor (p : ℕ) (hp : p.Prime) (x y : ℂ) :
    ((p:ℂ)*x) / ((p:ℂ)*y) = x/y :=
  mul_div_mul_left _ _ (by exact_mod_cast hp.ne_zero)

set_option maxHeartbeats 1000000 in
theorem high_step (mix : Mixed) (both : Both) (prim : Primitive)
    {p k m : ℕ} (hp : p.Prime) (hk : 0 < k) (he : Even m) (hmp : ¬p ∣ m)
    [NeZero (p^k)] [NeZero (p^k * p)]
    (ih : ∀ (A : DirichletCharacter ℂ (p ^ k)) (T : Finset (DirichletCharacter ℂ (p ^ k))),
      (∑ B ∈ T, ‖J A B (m : ZMod (p ^ k)) / J 1 1 (m : ZMod (p ^ k))‖^3) ≤ cap p)
    (A : DirichletCharacter ℂ (p^k*p)) (T : Finset (DirichletCharacter ℂ (p^k*p))) :
    (∑ B ∈ T, ‖J A B (m : ZMod (p^k*p)) / J 1 1 (m : ZMod (p^k*p))‖^3) ≤ cap p := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  let l := dvd_mul_right (p^k) p
  have support (a : ℕ) (ha : a.Coprime (p^k)) : a.Coprime p :=
    (Nat.coprime_pow_right_iff hk _ _).mp ha
  let w (B : DirichletCharacter ℂ (p^k*p)) :=
    ‖J A B (m : ZMod (p^k*p)) / J 1 1 (m : ZMod (p^k*p))‖^3
  change (∑ B ∈ T, w B) ≤ _
  by_cases hA : A.IsPrimitive
  · have vanish (B : DirichletCharacter ℂ (p^k*p)) (hB : ¬B.IsPrimitive) : w B = 0 := by
      obtain ⟨B₀, rfl⟩ := not_primitive_lifts hp B hB
      simp only [w, mix hp.one_lt support hA B₀, zero_div, norm_zero]
      norm_num
    have hfilter : (∑ B ∈ T.filter (fun B => B.IsPrimitive), w B) = ∑ B ∈ T, w B :=
      sum_filter_of_ne (fun B _ hB => by
        by_contra hn
        exact hB (vanish B hn))
    rw [← hfilter]
    refine prim p (k+1) m hp (by omega) he hmp A
      (T.filter fun B => B.IsPrimitive) hA ?_
    intro B hB
    exact (mem_filter.mp hB).2
  · obtain ⟨A₀, hAv⟩ := not_primitive_lifts hp A hA
    have vanish (B : DirichletCharacter ℂ (p^k*p)) (hB : ¬¬ B.IsPrimitive) : w B = 0 := by
      obtain hB := not_not.mp hB
      dsimp only [w]
      rw [← hAv, J_comm, mix hp.one_lt support hB A₀, zero_div, norm_zero]
      norm_num
    have hfilter : (∑ B ∈ T.filter (fun B => ¬B.IsPrimitive), w B) = ∑ B ∈ T, w B :=
      sum_filter_of_ne (fun B _ hB => by
        intro hprim
        exact hB (vanish B (not_not.mpr hprim)))
    rw [← hfilter]
    let U := univ.filter (fun B : DirichletCharacter ℂ (p^k) => changeLevel l B ∈ T)
    have mapU : T.filter (fun B => ¬B.IsPrimitive) = U.map ⟨changeLevel l, changeLevel_injective l⟩ := by
      ext B
      simp only [mem_filter, mem_map, Function.Embedding.coeFn_mk, U, mem_univ, true_and]
      constructor
      · rintro ⟨hb, hn⟩
        obtain ⟨B₀, hBl⟩ := not_primitive_lifts hp B hn
        exact ⟨B₀, hBl ▸ hb, hBl⟩
      · rintro ⟨B₀, hT, rfl⟩
        refine ⟨hT, fun hc => ?_⟩
        have eq : B₀.conductor = p^k*p := (conductor_changeLevel B₀ l).symm.trans hc
        have hle : B₀.conductor ≤ p^k := Nat.le_of_dvd (pow_pos hp.pos _) B₀.conductor_dvd_level
        exact (not_le_of_gt (by have := pow_pos hp.pos k; nlinarith [Nat.mul_le_mul_left (p^k) hp.two_le] :
          p^k < p^k * p)) (eq ▸ hle)
    rw [mapU, sum_map]
    have ordinary :
        J (1 : DirichletCharacter ℂ (p^k*p)) 1 (m : ZMod (p^k*p)) =
          (p:ℂ) * J (1 : DirichletCharacter ℂ (p^k)) 1 (m : ZMod (p^k)) := by
      simpa only [map_one, map_natCast] using
        (both support 1 1 (m : ZMod (p^k*p)))
    calc
      _ = ∑ B ∈ U, ‖J A₀ B (m : ZMod (p^k)) / J 1 1 (m : ZMod (p^k))‖^3 := by
        apply sum_congr rfl
        intro B _
        dsimp only [w, Function.Embedding.coeFn_mk]
        rw [← hAv, both support, ordinary, map_natCast, cancel_factor p hp]
      _ ≤ _ := ih A₀ U

set_option maxHeartbeats 1000000 in
theorem unit_of_prime_and_primitive (mix : Mixed) (both : Both) (prim : Primitive)
    (base : PrimeLevel)
    (p e m : ℕ) [NeZero (p^e)] (hp : p.Prime) (he : 0 < e) (hev : Even m) (hmp : ¬p ∣ m)
    (A : DirichletCharacter ℂ (p^e)) (T : Finset (DirichletCharacter ℂ (p^e))) :
    (∑ B ∈ T, ‖J A B (m : ZMod (p^e)) / J 1 1 (m : ZMod (p^e))‖^3) ≤ cap p := by
  have go (k : ℕ) :
      0 < k → ∀ [NeZero (p^k)] (A' : DirichletCharacter ℂ (p^k))
        (T' : Finset (DirichletCharacter ℂ (p^k))),
        (∑ B ∈ T', ‖J A' B (m : ZMod (p^k)) / J 1 1 (m : ZMod (p^k))‖^3) ≤ cap p := by
    induction k with
    | zero => omega
    | succ k IH =>
      intro hk' I A' T'
      by_cases h : k = 0
      · subst k
        exact base p m hp hev hmp A' T'
      · have hk : 0 < k := by omega
        letI : NeZero (p^k) := ⟨pow_ne_zero _ hp.ne_zero⟩
        letI : NeZero (p^k * p) := ⟨Nat.mul_ne_zero (pow_ne_zero _ hp.ne_zero) hp.ne_zero⟩
        exact high_step mix both prim hp hk hev hmp (IH hk) A' T'
  exact go e he A T

/-- Exact normalized square-row identity after Parseval and the ordinary count. -/
def SquareRow : Prop :=
  ∀ (p e m : ℕ) [NeZero (p^e)], p.Prime → 0 < e → Even m → ¬p ∣ m →
    ∀ A : DirichletCharacter ℂ (p^e),
      (∑ B : DirichletCharacter ℂ (p^e),
        ‖J A B (m:ZMod (p^e)) / J 1 1 (m:ZMod (p^e))‖^2) =
        ((p:ℝ)-1) / ((p:ℝ)-2)

private theorem prime_of_unit_even {p m : ℕ} (hp : p.Prime) (he : Even m) (hm : ¬p ∣ m) :
    3 ≤ p := by
  have hn : p ≠ 2 := fun h => hm (h.symm ▸ he.two_dvd)
  have := hp.two_le
  omega

set_option maxHeartbeats 1000000 in
theorem primitive_from_square (hSq : SquareRow)
    (hPoint : ∀ (p e m : ℕ) [NeZero (p^e)], p.Prime → 2 ≤ e → Even m → ¬p ∣ m →
      ∀ A B : DirichletCharacter ℂ (p^e), A.IsPrimitive → B.IsPrimitive →
      ‖J A B (m:ZMod (p^e)) / J 1 1 (m:ZMod (p^e))‖ ≤ 1 / ((p:ℝ)-2)) :
    Primitive := by
  intro p e m hzero hp he hme hmp A T hA hT
  have h3 : 3 ≤ p := prime_of_unit_even hp hme hmp
  have h3r : (3:ℝ) ≤ p := by exact_mod_cast h3
  have H : 0 < (p:ℝ)-2 := by linarith
  let w (B : DirichletCharacter ℂ (p^e)) := ‖J A B (m:ZMod (p^e))/J 1 1 (m:ZMod (p^e))‖
  change (∑ B ∈ T, w B ^ 3) ≤ _
  have sumSq := hSq p e m hp (by omega) hme hmp A
  change (∑ B : DirichletCharacter ℂ (p^e), w B ^ 2) = _ at sumSq
  have hs : (∑ B ∈ T, w B ^ 2) ≤ ∑ B : DirichletCharacter ℂ (p^e), w B ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (subset_univ T) fun i _ _ => sq_nonneg _
  calc
    _ ≤ ∑ B ∈ T, w B ^ 2 * (1 / ((p:ℝ)-2)) := by
      apply sum_le_sum
      intro B hB
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left (hPoint p e m hp he hme hmp A B hA (hT B hB))
        (sq_nonneg _)
    _ ≤ ((p:ℝ)-1) / ((p:ℝ)-2) * (1 / ((p:ℝ)-2)) := by
      rw [← sum_mul, ← sumSq]
      exact mul_le_mul_of_nonneg_right hs (by positivity)
    _ ≤ cap p := by
      unfold cap
      field_simp
      nlinarith [mul_nonneg (show 0 ≤ (p:ℝ)-3 by linarith) (show 0 ≤ (p:ℝ)-2 by linarith)]


end CubicMass.High

/- PrimitiveFourier -/
open scoped BigOperators Classical
open Finset DirichletCharacter

namespace CubicLocal

private theorem char_lift_all {d f : ℕ} [NeZero d] [NeZero (d*f)]
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d)
    (x : ZMod (d*f)) :
    changeLevel (dvd_mul_right d f) θ x = θ (ZMod.castHom (dvd_mul_right d f) (ZMod d) x) := by
  let c : ZMod (d*f) →+* ZMod d := ZMod.castHom (dvd_mul_right d f) _
  change _ = θ (c x)
  by_cases hx : IsUnit x
  · exact changeLevel_eq_cast_of_dvd θ (dvd_mul_right d f) hx.unit
  · rw [(changeLevel (dvd_mul_right d f) θ).map_nonunit hx, θ.map_nonunit]
    intro hc
    have castval := ZMod.natCast_zmod_val x
    have castval' : (x.val : ZMod d) = c x := by
      calc
        _ = c (x.val : ZMod (d*f)) := (map_natCast c x.val).symm
        _ = c x := congrArg c castval
    have hd := (ZMod.isUnit_iff_coprime x.val d).mp (castval'.symm ▸ hc)
    have hdf : x.val.Coprime (d*f) := hd.mul_right (support _ hd)
    exact hx (castval ▸ (ZMod.isUnit_iff_coprime x.val (d*f)).mpr hdf)

private theorem sum_cast_mul {A : Type*} [AddCommMonoid A] {d f : ℕ}
    [NeZero d] [NeZero f] [NeZero (d*f)] (g : ZMod d → A) :
    (∑ x : ZMod (d*f), g (ZMod.castHom (dvd_mul_right d f) _ x)) =
      f • ∑ z : ZMod d, g z := by
  have hgen : ∀ (q : ℕ) [NeZero q] (h : d ∣ q), q = f*d →
      (∑ x : ZMod q, g (ZMod.castHom h _ x)) = f • ∑ z : ZMod d, g z := by
    intro q _ hd h
    subst q
    exact reduce_sum g
  exact hgen _ _ (mul_comm ..)

theorem high_both : CubicMass.High.Both := by
  intro d f _ _ _ support a b m
  change (∑ x : ZMod (d*f), changeLevel (dvd_mul_right d f) a x *
      changeLevel (dvd_mul_right d f) b (m-x)) = _
  simp_rw [char_lift_all support, map_sub]
  unfold CubicMass.High.J
  rw [sum_cast_mul (fun y => a y * b (ZMod.castHom (dvd_mul_right d f) (ZMod d) m - y)),
    nsmul_eq_mul]

theorem lifted_std_zero {d f : ℕ} [NeZero d] [NeZero (d*f)] (hf : 1 < f)
    (support : ∀ a : ℕ, a.Coprime d → a.Coprime f) (θ : DirichletCharacter ℂ d) :
    gaussSum (changeLevel (dvd_mul_right d f) θ) ZMod.stdAddChar = 0 := by
  let c : ZMod (d*f) →+* ZMod d := ZMod.castHom (dvd_mul_right d f) _
  let z : ZMod (d*f) := (d:ℕ)
  have hz : z ≠ 0 := by
    rw [show z = (d : ZMod (d*f)) from rfl]
    intro H
    have h := (ZMod.natCast_eq_zero_iff d (d*f)).mp H
    have hlt := Nat.mul_lt_mul_of_pos_left hf (NeZero.pos d)
    have hle := Nat.le_of_dvd (NeZero.pos d) h
    apply hlt.not_ge
    simpa using hle
  have hz1 : ZMod.stdAddChar z ≠ 1 := by
    intro hh
    apply hz
    apply ZMod.injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using hh
  have hc : c z = 0 := by
    change c (d : ZMod (d*f)) = 0
    rw [map_natCast, ZMod.natCast_self]
  let g (x : ZMod (d*f)) : ℂ := θ (c x) * ZMod.stdAddChar x
  have hshift (x : ZMod (d*f)) : g (x + z) = ZMod.stdAddChar z * g x := by
    simp only [g, map_add, hc, add_zero, AddChar.map_add_eq_mul]
    ring
  have hsum : (∑ x : ZMod (d*f), g x) = ZMod.stdAddChar z * ∑ x : ZMod (d*f), g x := by
    calc
      _ = ∑ x : ZMod (d*f), g (x + z) := (Equiv.sum_comp (Equiv.addRight z) g).symm
      _ = _ := by simp_rw [hshift, Finset.mul_sum]
  simp only [gaussSum, char_lift_all support]
  change (∑ x : ZMod (d*f), g x) = 0
  exact eq_zero_of_mul_eq_self_left hz1 hsum.symm

private theorem fourier_jacobi {q : ℕ} [NeZero q] (a b : DirichletCharacter ℂ q) :
    ZMod.dft (CubicMass.High.J a b) = fun t => ZMod.dft a t * ZMod.dft b t := by
  funext t
  rw [fourierTransform_eq_gaussSum_mulShift,fourierTransform_eq_gaussSum_mulShift,gaussSum_mul,
    ZMod.dft_apply]
  apply sum_congr rfl
  intro m _
  rw [← sum_mul,smul_eq_mul,AddChar.mulShift_apply]
  simp only [CubicMass.High.J,mul_neg,mul_comm]

theorem high_mixed : CubicMass.High.Mixed := by
  intro d f _ _ _ hf support a hA b m
  have hz := lifted_std_zero hf support b
  have hzero : ZMod.dft (CubicMass.High.J a (changeLevel (dvd_mul_right d f) b)) = 0 := by
    rw [fourier_jacobi]
    funext t
    change ZMod.dft a t * ZMod.dft (changeLevel (dvd_mul_right d f) b) t = 0
    rw [hA.fourierTransform_eq_inv_mul_gaussSum, fourierTransform_eq_gaussSum_mulShift]
    by_cases H : IsUnit (-t)
    · rw [show -t = (H.unit : ZMod (d*f)) from rfl, gaussSum_mulShift_eq, hz, mul_zero, mul_zero]
    · rw [a⁻¹ |>.map_nonunit H, zero_mul, zero_mul]
  exact congrFun (ZMod.dft.injective (hzero.trans ZMod.dft.map_zero.symm)) m

private theorem phase_relation {q : ℕ} [NeZero q] {χ ψ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hψ : ψ.IsPrimitive) (m : ZMod q) :
    (q:ℂ)*CubicMass.High.J χ ψ m =
      (gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar) *
      ZMod.dft (fun t => (χ*ψ)⁻¹ t) m := by
  let G := gaussSum χ ZMod.stdAddChar * gaussSum ψ ZMod.stdAddChar
  have ht : ZMod.dft (CubicMass.High.J χ ψ) = fun t => G*(χ*ψ)⁻¹ (-t) := by
    rw [fourier_jacobi]
    funext t
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum,hψ.fourierTransform_eq_inv_mul_gaussSum]
    simp only [G,mul_inv,MulChar.mul_apply]
    ring
  have hi := congrFun (ZMod.dft_dft (CubicMass.High.J χ ψ)) (-m)
  rw [ht,ZMod.dft_const_mul G] at hi
  change G * ZMod.dft (fun t => (χ*ψ)⁻¹ (-t)) (-m) = (q:ℂ) • CubicMass.High.J χ ψ (- -m) at hi
  rw [ZMod.dft_comp_neg (fun t => (χ*ψ)⁻¹ t)] at hi
  simpa only [neg_neg,smul_eq_mul] using hi.symm

theorem gauss_primitive_norm {q : ℕ} [NeZero q] {a : DirichletCharacter ℂ q}
    (ha : a.IsPrimitive) : ‖gaussSum a ZMod.stdAddChar‖ = Real.sqrt q := by
  let tau := gaussSum a ZMod.stdAddChar
  let tauInv := gaussSum a⁻¹ ZMod.stdAddChar
  have hf : ZMod.dft (fun x : ZMod q => a x) = fun t => tau * a⁻¹ (-t) := by
    funext t
    simpa [tau, mul_comm] using ha.fourierTransform_eq_inv_mul_gaussSum t
  have ht : tau * tauInv = (q : ℂ) * a (-1) := by
    have H := congrFun (ZMod.dft_dft (fun x : ZMod q => a x)) (1 : ZMod q)
    rw [hf, ZMod.dft_const_mul tau, ZMod.dft_comp_neg] at H
    change tau * ZMod.dft (fun t => a⁻¹ t) (-(1 : ZMod q)) = (q : ℂ) * a (-(1 : ZMod q)) at H
    change tau * ZMod.dft (⇑(a⁻¹)) (-(1 : ZMod q)) = _ at H
    rw [ha.inv.fourierTransform_eq_inv_mul_gaussSum, inv_inv, neg_neg, map_one, one_mul] at H
    exact H
  have H := congrArg (fun z : ℂ => ‖z‖) ht
  have hInv : ‖tauInv‖ = ‖tau‖ := by
    simp [tauInv, tau, gaussSum_inv_eq_conj]
  rw [norm_mul, norm_mul, hInv, Complex.norm_natCast, a.norm_neg_one, mul_one, ← pow_two] at H
  change ‖tau‖ = Real.sqrt (q:ℝ)
  rw [← H, Real.sqrt_sq (norm_nonneg _)]

theorem primitive_norm {q : ℕ} [NeZero q] {a b : DirichletCharacter ℂ q}
    (ha : a.IsPrimitive) (hb : b.IsPrimitive) (m : ZMod q) :
    ‖CubicMass.High.J a b m‖ = ‖ZMod.dft (fun t => (a*b)⁻¹ t) m‖ := by
  have h := congrArg (fun z : ℂ => ‖z‖) (phase_relation ha hb m)
  simp only [norm_mul,Complex.norm_natCast,gauss_primitive_norm ha,
    gauss_primitive_norm hb,Real.mul_self_sqrt (Nat.cast_nonneg q)] at h
  exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne q : (q:ℝ)≠0) h


theorem gauss_std_bound_pp {p n : ℕ} (hp : p.Prime) (hn : 0 < n)
    [NeZero (p^n*p)] (a : DirichletCharacter ℂ (p^n*p)) :
    ‖gaussSum a ZMod.stdAddChar‖ ≤ Real.sqrt (p^n*p : ℕ) := by
  by_cases hA : a.IsPrimitive
  · rw [gauss_primitive_norm hA]
  · obtain ⟨A, rfl⟩ := CubicMass.High.not_primitive_lifts hp a hA
    let _ : NeZero (p^n) := ⟨pow_ne_zero n hp.ne_zero⟩
    have support (k : ℕ) (hk : k.Coprime (p^n)) : k.Coprime p :=
      (Nat.coprime_pow_right_iff hn k p).mp hk
    rw [lifted_std_zero hp.one_lt support, norm_zero]
    exact Real.sqrt_nonneg _

theorem primitive_point_bound_normalized
    (p e m : ℕ) [NeZero (p^e)] (hp : p.Prime) (he : 2 ≤ e) (hem : Even m) (hm : ¬p ∣ m)
    (A B : DirichletCharacter ℂ (p^e)) (hA : A.IsPrimitive) (hB : B.IsPrimitive) :
    ‖CubicMass.High.J A B (m:ZMod (p^e)) / CubicMass.High.J 1 1 (m:ZMod (p^e))‖
      ≤ 1/((p:ℝ)-2) := by
  cases e with
  | zero => omega
  | succ n =>
    have hn : 0 < n := by omega
    have h3 : 3 ≤ p := by
      have hne : p ≠ 2 := fun h => hm (h.symm ▸ hem.two_dvd)
      have := hp.two_le
      omega
    have h3R : (3 : ℝ) ≤ p := by exact_mod_cast h3
    have hpc : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hm).symm
    have hum : IsUnit (m : ZMod (p^(n+1))) :=
      (ZMod.isUnit_iff_coprime m _).mpr (hpc.pow_right _)
    have H : ‖gaussSum (A*B)⁻¹ ZMod.stdAddChar‖ ≤ Real.sqrt (p^(n+1) : ℕ) := by
      have G (q : ℕ) [NeZero q] (eq : q = p^n*p) (a : DirichletCharacter ℂ q) :
          ‖gaussSum a ZMod.stdAddChar‖ ≤ Real.sqrt q := by
        subst q
        exact gauss_std_bound_pp hp hn a
      exact G _ (pow_succ p n) _
    have num : ‖CubicMass.High.J A B (m:ZMod (p^(n+1)))‖ ≤ Real.sqrt (p^(n+1) : ℕ) := by
      rw [primitive_norm hA hB]
      change ‖ZMod.dft (⇑((A*B)⁻¹)) (m : ZMod (p^(n+1)))‖ ≤ _
      rw [fourierTransform_eq_gaussSum_mulShift]
      have hneg : IsUnit (-(m : ZMod (p^(n+1)))) := hum.neg
      rw [show -(m : ZMod (p^(n+1))) = (hneg.unit : ZMod (p^(n+1))) from rfl,
        gaussSum_mulShift_eq, norm_mul, ((A*B)⁻¹)⁻¹.unit_norm_eq_one hneg.unit, one_mul]
      exact H
    have den : ‖CubicMass.High.J (1 : DirichletCharacter ℂ (p^(n+1))) 1 (m:ZMod (p^(n+1)))‖ =
        (p:ℝ)^n *((p:ℝ)-2) := by
      have G (q : ℕ) [NeZero q] (eq : q = p^n*p) :
          ‖CubicMass.High.J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ =
            (p:ℝ)^n*((p:ℝ)-2) := by
        subst q
        exact ordinary_norm_pp hp hm
      exact G _ (pow_succ p n)
    have hpR : (0:ℝ) < p := by positivity
    have hnR : (0:ℝ) < (p:ℝ)^n := pow_pos hpR _
    have hpN : (p:ℝ) ≤ (p:ℝ)^n := by
      exact_mod_cast Nat.le_of_dvd (pow_pos hp.pos _) (dvd_pow_self _ hn.ne')
    have hS : Real.sqrt (p^(n+1):ℕ) ≤ (p:ℝ)^n := by
      apply (Real.sqrt_le_iff).2 ⟨hnR.le, ?_⟩
      rw [Nat.cast_pow, pow_succ, pow_two]
      exact mul_le_mul_of_nonneg_left hpN hnR.le
    rw [norm_div, den, ← div_div]
    exact div_le_div_of_nonneg_right ((div_le_one hnR).2 (num.trans hS)) (by linarith)

end CubicLocal

/- SquareRow -/
open scoped BigOperators
open DirichletCharacter

namespace CubicLocal

theorem square_row (p e m : ℕ) [NeZero (p^e)] (hp : p.Prime) (he : 0 < e)
    (hem : Even m) (hm : ¬p ∣ m) (A : DirichletCharacter ℂ (p^e)) :
    (∑ B : DirichletCharacter ℂ (p^e),
      ‖CubicMass.jacobi A B (m:ZMod (p^e)) / CubicMass.jacobi 1 1 (m:ZMod (p^e))‖^2) =
      ((p:ℝ)-1) / ((p:ℝ)-2) := by
  cases e with
  | zero => omega
  | succ j =>
    have h3 : 3 ≤ p := by
      have hnot : p ≠ 2 := fun h => hm (h.symm ▸ hem.two_dvd)
      have := hp.two_le
      omega
    have pR : (3:ℝ) ≤ p := by exact_mod_cast h3
    have p_pos : (0:ℝ) < p := by positivity
    have p_sub_pos : 0 < (p:ℝ)-2 := by linarith
    have oq : ∀ (q : ℕ) [NeZero q], q = p^j*p →
        ‖CubicMass.jacobi (1 : DirichletCharacter ℂ q) 1
          (m : ZMod q)‖ = (p:ℝ)^j * ((p:ℝ)-2) := by
      intro q _ E
      subst q
      exact ordinary_norm_pp hp hm
    have o := oq (p^(j+1)) (pow_succ p j)
    rw [CubicMass.jacobi_normalized_row_parseval A _ (by rw [o]; positivity), o,
      Nat.totient_prime_pow_succ hp]
    push_cast [Nat.cast_sub hp.one_lt.le]
    field_simp

end CubicLocal

/- LocalPrime -/
open scoped BigOperators Classical
open Finset DirichletCharacter
-- Exact prime norm table, adapted from the accepted SharpSingularSeriesRatios proof.
namespace CubicMass.StandalonePrimeTable

open Finset
open scoped BigOperators Classical

noncomputable def localSum {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    (m : ZMod p) : ℂ := ∑ a : ZMod p, χ a * ψ (m-a)

private theorem norm_jacobi {p : ℕ} [hp : Fact p.Prime] {χ ψ : DirichletCharacter ℂ p}
    (hχ : χ ≠ 1) (hψ : ψ ≠ 1) (hχψ : χ*ψ ≠ 1) :
    ‖jacobiSum χ ψ‖ = Real.sqrt p := by
  have hc : star (jacobiSum χ ψ) = jacobiSum χ⁻¹ ψ⁻¹ := by
    simp only [jacobiSum, star_sum, star_mul', MulChar.star_apply']
  have hchar : ringChar ℂ ≠ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ringChar.eq ℂ 0]
    exact hp.out.ne_zero.symm
  have h := congrArg (fun z : ℂ => ‖z‖) (jacobiSum_mul_jacobiSum_inv hchar hχ hψ hχψ)
  simp only [← hc, norm_mul, norm_star, ZMod.card, Complex.norm_natCast] at h
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg p), Real.sqrt_nonneg (p:ℝ), norm_nonneg (jacobiSum χ ψ)]

private theorem localSum_nonzero {p : ℕ} [Fact p.Prime] (χ ψ : DirichletCharacter ℂ p)
    {m : ZMod p} (hm : m ≠ 0) : localSum χ ψ m = (χ m*ψ m)*jacobiSum χ ψ := by
  have h := Equiv.sum_comp (Equiv.mulLeft₀ m hm) (fun a : ZMod p => χ a * ψ (m-a))
  calc
    _ = ∑ a : ZMod p, χ (m*a) * ψ (m-m*a) := h.symm
    _ = ∑ a : ZMod p, (χ m*ψ m)*(χ a*ψ (1-a)) := by
      apply sum_congr rfl
      intro a _
      rw [← mul_one_sub, map_mul, map_mul]
      ring
    _ = _ := (mul_sum ..).symm

private theorem localSum_zero {p : ℕ} [hp : Fact p.Prime] (χ ψ : DirichletCharacter ℂ p) :
    localSum χ ψ 0 = ψ (-1)*(if χ*ψ = 1 then ((p-1 : ℕ) : ℂ) else 0) := by
  classical
  have h : localSum χ ψ 0 = ψ (-1)*∑ a : ZMod p, (χ*ψ) a := by
    unfold localSum
    rw [mul_sum]
    apply sum_congr rfl
    intro a _
    rw [zero_sub, ← neg_one_mul a, map_mul, MulChar.mul_apply]
    ring
  rw [h]
  by_cases hprod : χ*ψ = 1
  · simp only [hprod, ite_true, MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient,
      Nat.totient_prime hp.out]
  · rw [ite_eq_right hprod, MulChar.sum_eq_zero_of_ne_one hprod]

/-- Complete table, including the primes 2 and 3 and imprimitive local factors. -/
theorem local_norm {p : ℕ} [hp : Fact p.Prime] (χ ψ : DirichletCharacter ℂ p) (m : ZMod p) :
    ‖localSum χ ψ m‖ =
      if m=0 then (if χ*ψ=1 then (p:ℝ)-1 else 0)
      else if χ=1 ∧ ψ=1 then (p:ℝ)-2
      else if χ=1 ∨ ψ=1 ∨ χ*ψ=1 then 1 else Real.sqrt p := by
  classical
  by_cases hm : m=0
  · subst m
    rw [ite_eq_left rfl,localSum_zero,norm_mul,ψ.norm_neg_one,one_mul]
    by_cases h : χ*ψ=1
    · rw [ite_eq_left h,ite_eq_left h,Complex.norm_natCast,Nat.cast_sub hp.out.one_le,Nat.cast_one]
    · simp [h]
  have hu := isUnit_iff_ne_zero.mpr hm
  have v (θ : DirichletCharacter ℂ p) : ‖θ m‖=1 := θ.unit_norm_eq_one hu.unit
  rw [ite_eq_right hm,localSum_nonzero χ ψ hm,norm_mul,norm_mul,
    v χ,v ψ,one_mul,one_mul]
  by_cases hχ : χ=1
  · subst χ
    by_cases hψ : ψ=1
    · subst ψ
      have hpos : (0:ℝ) ≤ p-2 := sub_nonneg.mpr (by exact_mod_cast hp.out.two_le)
      simp only [and_self,ite_true,jacobiSum_one_one,ZMod.card]
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_ofNat 2, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_of_nonneg hpos]
    · simp [hψ,jacobiSum_one_nontrivial hψ]
  by_cases hψ : ψ=1
  · subst ψ
    rw [jacobiSum_comm,jacobiSum_one_nontrivial hχ]
    simp [hχ]
  by_cases hprod : χ*ψ=1
  · have hinv : ψ=χ⁻¹ := eq_inv_of_mul_eq_one_right hprod
    simp only [hχ,hψ,hprod,false_and,ite_false,false_or,ite_true]
    rw [hinv,jacobiSum_nontrivial_inv hχ,norm_neg,χ.norm_neg_one]
  · simp [hχ,hψ,hprod,norm_jacobi hχ hψ hprod]
end CubicMass.StandalonePrimeTable

namespace CubicMass

private theorem sq_mul_ge_sqrt_mul {x : ℝ} (hx : 5 ≤ x) :
    Real.sqrt x * (x - 1) ≤ (x - 2)^2 := by
  have hx0 : 0 ≤ x := by linarith
  have H : Real.sqrt x ≤ (x + 4) / 4 := by
    nlinarith [sq_nonneg (Real.sqrt x - 2), Real.sq_sqrt hx0]
  have mul := mul_le_mul_of_nonneg_right H (show 0 ≤ x - 1 by linarith)
  have h := mul_nonneg (show 0 ≤ 3*x-4 by linarith) (show 0 ≤ x-5 by linarith)
  nlinarith

private theorem sum_row_ite {α : Type*} [Fintype α] (U : Finset α) (u v : ℝ) :
    ∑ b : α, (if b ∈ U then u else v) =
      (U.card : ℝ) * u + ((Fintype.card α - U.card : ℕ) : ℝ) * v := by
  classical
  rw [Finset.sum_ite (fun _ => u) (fun _ => v), Finset.filter_not]
  have f : (univ : Finset α).filter (· ∈ U) = U := by ext x; simp
  rw [f]
  simp [Finset.card_sdiff, nsmul_eq_mul]

/-- Prime-level bound, using the exact local Jacobi norm table. -/
theorem local_prime_moment {p : ℕ} [hp : Fact p.Prime] (m : ZMod p) (_hm : m ≠ 0)
    (hp2 : p ≠ 2)
    (norm_table : ∀ a b : DirichletCharacter ℂ p,
      ‖∑ x : ZMod p, a x * b (m-x)‖ =
        if a=1 ∧ b=1 then (p:ℝ)-2 else if a=1 ∨ b=1 ∨ a*b=1 then 1 else Real.sqrt p)
    (a : DirichletCharacter ℂ p) (T : Finset (DirichletCharacter ℂ p)) :
    (∑ b ∈ T, ‖(∑ x : ZMod p, a x * b (m-x)) /
        (∑ x : ZMod p, (1 : DirichletCharacter ℂ p) x * (1 : DirichletCharacter ℂ p) (m-x))‖^3)
      ≤ 1 + (((p:ℝ)-2)^2)⁻¹ := by
  classical
  let f (b : DirichletCharacter ℂ p) : ℝ :=
    if a=1 ∧ b=1 then (p:ℝ)-2 else if a=1 ∨ b=1 ∨ a*b=1 then 1 else Real.sqrt p
  let d : ℝ := (p:ℝ)-2
  have p3 : 3 ≤ p := by have := hp.out.two_le; omega
  have p3r : (3:ℝ) ≤ p := by exact_mod_cast p3
  have hd : 0 < d := by dsimp [d]; linarith
  have hne : d ≠ 0 := hd.ne'
  have hcard : Fintype.card (DirichletCharacter ℂ p) = p-1 := by
    rw [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ p,
      Nat.totient_prime hp.out]
  simp_rw [norm_div, norm_table]
  simp only [true_and, ite_true]
  change (∑ b ∈ T, (f b / d)^3) ≤ _
  have hf (b : DirichletCharacter ℂ p) : 0 ≤ f b := by
    simpa only [f, ← norm_table a b] using (norm_nonneg (∑ x : ZMod p, a x * b (m-x)))
  have red : ∀ U : Finset (DirichletCharacter ℂ p),
      (∑ b ∈ U, (f b / d)^3) = (∑ b ∈ U, f b^3) / d^3 := by
    intro U
    simp_rw [div_pow, div_eq_mul_inv, Finset.sum_mul]
  rw [red]
  refine (div_le_div_of_nonneg_right
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun b _ _ => pow_nonneg (hf b) _)) (pow_nonneg hd.le _)).trans ?_
  have psub : ((p-1 : ℕ) : ℝ) = (p:ℝ)-1 := Nat.cast_sub hp.out.one_le
  by_cases ha : a=1
  · have H (b : DirichletCharacter ℂ p) : f b^3 =
        if b ∈ ({1} : Finset (DirichletCharacter ℂ p)) then d^3 else (1:ℝ) := by
      by_cases hb : b = 1 <;> simp [f,d,ha,hb]
    simp_rw [H]
    rw [sum_row_ite, Finset.card_singleton, hcard]
    have pc : ((p - 1 - 1 : ℕ) : ℝ) = d := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega : 2 ≤ p)]
      rfl
    rw [pc]
    push_cast
    change (1*d^3 + d*1)/d^3 ≤ 1 + (d^2)⁻¹
    apply le_of_eq
    field_simp
  · have invne : a⁻¹ ≠ 1 := fun h => ha (inv_eq_one.mp h)
    let U : Finset (DirichletCharacter ℂ p) := {1,a⁻¹}
    have cardU : U.card = 2 := Finset.card_pair invne.symm
    have H (b : DirichletCharacter ℂ p) : f b^2 = if b ∈ U then 1 else (p:ℝ) := by
      have eqv : a*b=1 ↔ b=a⁻¹ :=
        ⟨eq_inv_of_mul_eq_one_right, fun h => h ▸ mul_inv_cancel _⟩
      by_cases hb : b = 1 ∨ b = a⁻¹
      · simp [f, U, ha, eqv, hb]
      · simp [f, U, ha, eqv, hb, Real.sq_sqrt (Nat.cast_nonneg p)]
    have sum_sq : (∑ b, f b^2) = ((p:ℝ)-1)*d := by
      simp_rw [H]
      rw [sum_row_ite, cardU,hcard]
      have pc : ((p-1-2 : ℕ) : ℝ) = (p:ℝ)-3 := by
        rw [Nat.sub_sub, Nat.cast_sub (by omega : 3 ≤ p)]
        rfl
      rw [pc]
      push_cast
      dsimp [d]
      ring
    by_cases h3 : p=3
    · have allU : U=univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        rw [Finset.card_univ, hcard, cardU]
        omega
      have F1 (b : DirichletCharacter ℂ p) : f b = 1 := by
        have B : b ∈ U := by simp [allU]
        have eqv : a*b=1 ↔ b=a⁻¹ :=
          ⟨eq_inv_of_mul_eq_one_right, fun h => h ▸ mul_inv_cancel _⟩
        have eps : b = 1 ∨ b = a⁻¹ := by simpa [U] using B
        simp [f,ha,eqv,eps]
      simp_rw [F1, one_pow]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hcard]
      norm_num [d,h3]
    · have p5 : 5 ≤ p := by have := hp.out.eq_two_or_odd; omega
      have p5r : (5:ℝ) ≤ p := by exact_mod_cast p5
      have fp (b : DirichletCharacter ℂ p) : f b ≤ Real.sqrt p := by
        have hs : 1 ≤ Real.sqrt p := Real.one_le_sqrt.mpr (by linarith)
        simp only [f,ha,false_and,false_or,ite_false]
        split_ifs <;> first | assumption | exact le_rfl
      have sumcub : (∑ b, f b^3) ≤ d^3 := by
        calc
          _ ≤ ∑ b, Real.sqrt p * f b^2 := Finset.sum_le_sum (by
            intro b _
            have hmul := mul_le_mul_of_nonneg_right (fp b) (sq_nonneg (f b))
            nlinarith)
          _ = Real.sqrt p * ((p:ℝ)-1)*d := by rw [← Finset.mul_sum,sum_sq]; ring
          _ ≤ _ := by
            have := mul_le_mul_of_nonneg_right (sq_mul_ge_sqrt_mul p5r) hd.le
            change Real.sqrt p * ((p:ℝ)-1) * d ≤ d^2 * d at this
            simpa [pow_succ] using this
      exact ((div_le_one (pow_pos hd _)).mpr sumcub).trans (le_add_of_nonneg_right (inv_nonneg.mpr (sq_nonneg d)))


open CubicMass.StandalonePrimeTable in
/-- Standalone prime-level bound for an even natural target not divisible by `p`. -/
theorem local_prime_moment_nat (p m : ℕ) [NeZero p] (hp : p.Prime) (hm : Even m) (hpm : ¬ p ∣ m)
    (a : DirichletCharacter ℂ p) (T : Finset (DirichletCharacter ℂ p)) :
    let Jm := fun (A B : DirichletCharacter ℂ p) =>
      ∑ x : ZMod p, A x * B ((m : ZMod p) - x)
    (∑ b ∈ T, ‖Jm a b / Jm 1 1‖^3) ≤ 1 + (((p:ℝ)-2)^2)⁻¹ := by
  letI : Fact p.Prime := ⟨hp⟩
  have h₂ : p ≠ 2 := fun h => hpm (h.symm ▸ Even.two_dvd hm)
  have nz : (m : ZMod p) ≠ 0 := by
    intro zero
    exact hpm ((ZMod.natCast_eq_zero_iff m p).mp zero)
  apply local_prime_moment (m : ZMod p) nz h₂ _ a T
  intro a b
  simpa only [localSum, nz, ite_false] using local_norm a b (m : ZMod p)

/-- The exact exponent-one branch of the nondividing prime-power child. -/
theorem local_prime_moment_pow_one (p m : ℕ) [NeZero (p^1)] (hp : p.Prime)
    (hm : Even m) (hpm : ¬ p ∣ m)
    (a : DirichletCharacter ℂ (p^1)) (T : Finset (DirichletCharacter ℂ (p^1))) :
    let Jm := fun (A B : DirichletCharacter ℂ (p^1)) =>
      ∑ x : ZMod (p^1), A x * B ((m : ZMod (p^1)) - x)
    (∑ b ∈ T, ‖Jm a b / Jm 1 1‖^3) ≤ 1 + (((p:ℝ)-2)^2)⁻¹ := by
  have H (q : ℕ) (hq : q = p) [NeZero q] (a : DirichletCharacter ℂ q)
      (T : Finset (DirichletCharacter ℂ q)) :
      let Jm := fun (A B : DirichletCharacter ℂ q) =>
        ∑ x : ZMod q, A x * B ((m : ZMod q) - x)
      (∑ b ∈ T, ‖Jm a b / Jm 1 1‖^3) ≤ 1 + (((p:ℝ)-2)^2)⁻¹ := by
    subst q
    exact local_prime_moment_nat p m hp hm hpm a T
  exact H (p^1) (pow_one p) a T

end CubicMass

/- LocalUnitStandalone -/
open scoped BigOperators
open DirichletCharacter

namespace CubicLocal

theorem local_nondvd (p e m : ℕ) [NeZero (p ^ e)] (hp : p.Prime) (he : 0 < e)
    (hmEven : Even m) (hm : ¬p ∣ m)
    (a : DirichletCharacter ℂ (p^e)) (T : Finset (DirichletCharacter ℂ (p^e))) :
    let Jm := fun (A B : DirichletCharacter ℂ (p ^ e)) =>
      ∑ x : ZMod (p ^ e), A x * B ((m : ZMod (p ^ e)) - x)
    (∑ b ∈ T, ‖Jm a b / Jm 1 1‖ ^ 3) ≤ 1 + (((p:ℝ)-2)^2)⁻¹ :=
  CubicMass.High.unit_of_prime_and_primitive high_mixed high_both
    (CubicMass.High.primitive_from_square square_row primitive_point_bound_normalized)
    CubicMass.local_prime_moment_pow_one p e m hp he hmEven hm a T

end CubicLocal


theorem Conjectures.Cuts.Task089bb9ca51f195a2dfa3d2ec : (∀ (x1 x2 x3 : ℕ) [x4 : NeZero (x1 ^ x2)],   Nat.Prime x1 →     (0 : ℕ) < x2 →       Even x3 →         ¬x1 ∣ x3 →           ∀ (x9 : DirichletCharacter ℂ (x1 ^ x2)) (x10 : Finset (DirichletCharacter ℂ (x1 ^ x2))),             have x11 : DirichletCharacter ℂ (x1 ^ x2) → DirichletCharacter ℂ (x1 ^ x2) → ℂ := fun (x11 x12 : DirichletCharacter ℂ (x1 ^ x2)) => ∑ x13 : ZMod (x1 ^ x2), x11 x13 * x12 (↑x3 - x13);             ∑ x12 ∈ x10, ‖x11 x9 x12 / x11 (1 : DirichletCharacter ℂ (x1 ^ x2)) (1 : DirichletCharacter ℂ (x1 ^ x2))‖ ^ (3 : ℕ) ≤ (1 : ℝ) + ((↑x1 - (2 : ℝ)) ^ (2 : ℕ))⁻¹) :=
  CubicLocal.local_nondvd
