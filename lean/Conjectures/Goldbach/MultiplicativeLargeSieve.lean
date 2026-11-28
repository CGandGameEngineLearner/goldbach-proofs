import Mathlib
import Conjectures.Goldbach.AnalyticLargeSieve

/-!
Montgomery--Vaughan multiplicative large sieve.

Credit: the Dirichlet-character orthogonality, Gauss-sum inversion and character Parseval
machinery below is adapted from the accepted module
`Conjectures.Goldbach.B13BilateralVaughanReduction` (namespace `BombieriVinogradov.LargeSieve`);
the additive (Farey) large sieve with the sharp constant `π N + Q²` is used through the accepted
module `Conjectures.Goldbach.AnalyticLargeSieve`.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace Conjectures.Goldbach.MultiplicativeLargeSieve_aux

open Conjectures.Goldbach.AnalyticLargeSieve_aux

noncomputable section

noncomputable local instance unitFintype (n : ℕ) : Fintype (ZMod n)ˣ := Fintype.ofFinite _

/-- The finite set of primitive complex Dirichlet characters of level `n`. -/
def primChars (n : ℕ) : Finset (DirichletCharacter ℂ n) := by
  classical
  exact Finset.univ.filter DirichletCharacter.IsPrimitive

/-- The interval character sum `S(χ) = ∑_{M ≤ k < M+N} c k χ(k)`. -/
def charSum (c : ℕ → ℂ) (M N n : ℕ) (χ : DirichletCharacter ℂ n) : ℂ :=
  ∑ k ∈ Ico M (M + N), c k * χ (k : ZMod n)

/-- The additive interval sum at the reduced residue `u` modulo `n`. -/
def addSum (c : ℕ → ℂ) (M N n : ℕ) [NeZero n] (u : (ZMod n)ˣ) : ℂ :=
  ∑ k ∈ Ico M (M + N), c k * ZMod.stdAddChar ((k : ZMod n) * (u : ZMod n))

/-- A character transform of a function on the unit group of `ZMod n`. -/
def unitCharSum {n : ℕ} (b : (ZMod n)ˣ → ℂ) (χ : DirichletCharacter ℂ n) : ℂ :=
  ∑ x : (ZMod n)ˣ, b x * χ (x : ZMod n)

/-- A nonnegative sum over primitive characters is bounded by the sum over all characters. -/
theorem primSum_le_all (n : ℕ) (f : DirichletCharacter ℂ n → ℝ) (hf : ∀ χ, 0 ≤ f χ) :
    ∑ χ ∈ primChars n, f χ ≤ ∑ χ : DirichletCharacter ℂ n, f χ := by
  classical
  exact Finset.sum_le_univ_sum_of_nonneg (s := primChars n) hf

/-- On units, complex conjugation of a character value is evaluation at the inverse. -/
theorem star_char_unit {n : ℕ} (χ : DirichletCharacter ℂ n) (x : (ZMod n)ˣ) :
    star (χ (x : ZMod n)) = χ ((x : ZMod n)⁻¹) := by
  rw [MulChar.star_apply']
  rw [MulChar.inv_apply_eq_inv']
  simp

/-- Orthogonality of all complex Dirichlet characters on the unit group. -/
theorem charOrthUnits {n : ℕ} [NeZero n] (x y : (ZMod n)ˣ) :
    (∑ χ : DirichletCharacter ℂ n, star (χ (x : ZMod n)) * χ (y : ZMod n)) =
      if x = y then (n.totient : ℂ) else 0 := by
  simp_rw [star_char_unit]
  simpa only [Units.val_inj] using
    (DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) x.isUnit (y : ZMod n))

/-- Finite Parseval identity for the Dirichlet-character transform on `(ZMod n)^*`. -/
theorem charParseval {n : ℕ} [NeZero n] (b : (ZMod n)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ n, star (unitCharSum b χ) * unitCharSum b χ) =
      (n.totient : ℂ) * ∑ x : (ZMod n)ˣ, star (b x) * b x := by
  classical
  unfold unitCharSum
  simp_rw [star_sum, star_mul, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, y]
    rw [Finset.sum_comm]
  have rearrange (χ : DirichletCharacter ℂ n) (x y : (ZMod n)ˣ) :
      star (χ (x : ZMod n)) * star (b x) * (b y * χ (y : ZMod n)) =
        (star (b x) * b y) * (star (χ (x : ZMod n)) * χ (y : ZMod n)) := by
    ring
  simp_rw [rearrange]
  simp_rw [← Finset.mul_sum]
  simp_rw [charOrthUnits]
  simp [mul_ite]
  rw [← Finset.sum_mul]
  ring

/-- Real norm-squared form of character Parseval. -/
theorem charParseval_normSq {n : ℕ} [NeZero n] (b : (ZMod n)ˣ → ℂ) :
    (∑ χ : DirichletCharacter ℂ n, ‖unitCharSum b χ‖ ^ 2) =
      (n.totient : ℝ) * ∑ x : (ZMod n)ˣ, ‖b x‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp_rw [← Complex.normSq_eq_norm_sq]
  push_cast
  simpa only [Complex.normSq_eq_conj_mul_self, RCLike.star_def] using (charParseval b)

/-- Discarding imprimitive characters gives the fixed-modulus primitive-character bound. -/
theorem primCharParseval_le {n : ℕ} [NeZero n] (b : (ZMod n)ˣ → ℂ) :
    ∑ χ ∈ primChars n, ‖unitCharSum b χ‖ ^ 2 ≤ (n.totient : ℝ) * ∑ x : (ZMod n)ˣ, ‖b x‖ ^ 2 := by
  calc
    _ ≤ ∑ χ : DirichletCharacter ℂ n, ‖unitCharSum b χ‖ ^ 2 :=
      primSum_le_all n _ (fun χ => sq_nonneg ‖unitCharSum b χ‖)
    _ = _ := charParseval_normSq b

/-- The Gauss sum of a primitive character has squared norm `n`. -/
theorem norm_gaussSum_sq {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (n : ℝ) := by
  rw [DirichletCharacter.norm_gaussSum_stdAddChar hχ, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- A Dirichlet-character-weighted sum over units equals the sum over all residues. -/
theorem sum_units_eq_sum_residues {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n)
    (f : ZMod n → ℂ) :
    ∑ u : (ZMod n)ˣ, χ (u : ZMod n) * f u = ∑ x : ZMod n, χ x * f x := by
  classical
  let s : Finset (ZMod n) := Finset.univ.filter IsUnit
  have hunits : (∑ u : (ZMod n)ˣ, χ (u : ZMod n) * f u) = ∑ x ∈ s, χ x * f x := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (ZMod n)ˣ)) (t := s)
      (fun u _ => (u : ZMod n))
    · intro u _
      simp [s, u.isUnit]
    · intro u _ v _ huv
      exact Units.ext huv
    · intro x hx
      have hxunit : IsUnit x := by simpa [s] using hx
      exact ⟨hxunit.unit, Finset.mem_univ _, hxunit.unit_spec⟩
    · intro u _
      rfl
  rw [hunits]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x _ hxnot
  have hxnonunit : ¬IsUnit x := by simpa [s] using hxnot
  rw [MulChar.map_nonunit χ hxnonunit, zero_mul]

/-- Primitive Gauss-sum inversion on one residue. -/
theorem shift_eq_char_mul_gauss {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}
    (hχ : χ.IsPrimitive) (k : ℕ) :
    ∑ u : (ZMod n)ˣ, χ⁻¹ (u : ZMod n) * ZMod.stdAddChar ((k : ZMod n) * (u : ZMod n)) =
      χ (k : ZMod n) * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hχInv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  calc
    _ = ∑ x : ZMod n, χ⁻¹ x * ZMod.stdAddChar ((k : ZMod n) * x) :=
      sum_units_eq_sum_residues χ⁻¹ _
    _ = gaussSum χ⁻¹ (ZMod.stdAddChar.mulShift (k : ZMod n)) := by
      simp only [gaussSum, AddChar.mulShift_apply]
    _ = _ := by
      simpa using (gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχInv (k : ZMod n))

/-- Primitive Gauss-sum inversion for the interval character sum. -/
theorem gauss_mul_charSum {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}
    (hχ : χ.IsPrimitive) (c : ℕ → ℂ) (M N : ℕ) :
    gaussSum χ⁻¹ ZMod.stdAddChar * charSum c M N n χ =
      unitCharSum (addSum c M N n) χ⁻¹ := by
  classical
  unfold charSum addSum unitCharSum
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    gaussSum χ⁻¹ ZMod.stdAddChar * (c k * χ (k : ZMod n)) =
        c k * (χ (k : ZMod n) * gaussSum χ⁻¹ ZMod.stdAddChar) := by ring
    _ = c k * ∑ u : (ZMod n)ˣ,
        χ⁻¹ (u : ZMod n) * ZMod.stdAddChar ((k : ZMod n) * (u : ZMod n)) := by
      rw [shift_eq_char_mul_gauss hχ k]
    _ = ∑ u : (ZMod n)ˣ,
        c k * (χ⁻¹ (u : ZMod n) * ZMod.stdAddChar ((k : ZMod n) * (u : ZMod n))) := by
      rw [Finset.mul_sum]
    _ = ∑ u : (ZMod n)ˣ,
        c k * ZMod.stdAddChar ((k : ZMod n) * (u : ZMod n)) * χ⁻¹ (u : ZMod n) := by
      apply Finset.sum_congr rfl
      intro u _
      ring

/-- Squared-norm form of primitive Gauss-sum inversion. -/
theorem n_mul_norm_charSum_sq {n : ℕ} [NeZero n] {χ : DirichletCharacter ℂ n}
    (hχ : χ.IsPrimitive) (c : ℕ → ℂ) (M N : ℕ) :
    (n : ℝ) * ‖charSum c M N n χ‖ ^ 2 =
      ‖unitCharSum (addSum c M N n) χ⁻¹‖ ^ 2 := by
  have hχInv : χ⁻¹.IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hχ
  calc
    (n : ℝ) * ‖charSum c M N n χ‖ ^ 2 =
        ‖gaussSum χ⁻¹ ZMod.stdAddChar‖ ^ 2 * ‖charSum c M N n χ‖ ^ 2 := by
      rw [norm_gaussSum_sq hχInv]
    _ = ‖gaussSum χ⁻¹ ZMod.stdAddChar * charSum c M N n χ‖ ^ 2 := by
      rw [norm_mul]
      ring
    _ = _ := by
      rw [gauss_mul_charSum hχ c M N]

/-- Inversion permutes the finite set of primitive characters. -/
theorem sum_prim_inv (n : ℕ) (f : DirichletCharacter ℂ n → ℝ) :
    ∑ χ ∈ primChars n, f χ⁻¹ = ∑ χ ∈ primChars n, f χ := by
  classical
  apply Finset.sum_bij (s := primChars n) (t := primChars n) (fun χ _ => χ⁻¹)
  · intro χ hχ
    have hprimitive : χ.IsPrimitive := by simpa [primChars] using hχ
    have hinv : χ⁻¹.IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
      exact hprimitive
    simpa [primChars] using hinv
  · intro χ _ ψ _ heq
    simpa only [inv_inv] using congrArg Inv.inv heq
  · intro ψ hψ
    refine ⟨ψ⁻¹, ?_, ?_⟩
    · have hprimitive : ψ.IsPrimitive := by simpa [primChars] using hψ
      have hinv : ψ⁻¹.IsPrimitive := by
        rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
        exact hprimitive
      simpa [primChars] using hinv
    · simp
  · intro χ _
    rfl

/-- At a fixed positive modulus, the weight `n / φ(n)` cancels exactly against the Gauss norm
and character Parseval constants. -/
theorem weighted_le_addSum {n : ℕ} [NeZero n] (c : ℕ → ℂ) (M N : ℕ) :
    ((n : ℝ) / (n.totient : ℝ)) * ∑ χ ∈ primChars n, ‖charSum c M N n χ‖ ^ 2 ≤
      ∑ u : (ZMod n)ˣ, ‖addSum c M N n u‖ ^ 2 := by
  classical
  let b : (ZMod n)ˣ → ℂ := addSum c M N n
  let S : ℝ := ∑ χ ∈ primChars n, ‖charSum c M N n χ‖ ^ 2
  let E : ℝ := ∑ u : (ZMod n)ˣ, ‖b u‖ ^ 2
  have hscaled : (n : ℝ) * S =
      ∑ χ ∈ primChars n, ‖unitCharSum b χ⁻¹‖ ^ 2 := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro χ hχ
    have hprimitive : χ.IsPrimitive := by simpa [primChars] using hχ
    exact n_mul_norm_charSum_sq hprimitive c M N
  have hinv :
      (∑ χ ∈ primChars n, ‖unitCharSum b χ⁻¹‖ ^ 2) =
        ∑ χ ∈ primChars n, ‖unitCharSum b χ‖ ^ 2 :=
    sum_prim_inv n (fun χ => ‖unitCharSum b χ‖ ^ 2)
  have hparseval :
      ∑ χ ∈ primChars n, ‖unitCharSum b χ‖ ^ 2 ≤ (n.totient : ℝ) * E := by
    simpa [E] using primCharParseval_le b
  have hcore : (n : ℝ) * S ≤ (n.totient : ℝ) * E := by
    rw [hscaled, hinv]
    exact hparseval
  have hphi : 0 < (n.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos n)
  change ((n : ℝ) / (n.totient : ℝ)) * S ≤ E
  calc
    ((n : ℝ) / (n.totient : ℝ)) * S = ((n : ℝ) * S) / (n.totient : ℝ) := by ring
    _ ≤ ((n.totient : ℝ) * E) / (n.totient : ℝ) :=
      (div_le_div_iff_of_pos_right hphi).2 hcore
    _ = E := by field_simp


/-- The standard additive character at a residue `k * a` is the real exponential phase at
the rational point `a / n`. -/
theorem stdAddChar_mul_eq_Ex (n a k : ℕ) [NeZero n] :
    ZMod.stdAddChar ((k : ZMod n) * (a : ZMod n)) = Ex ((k : ℝ) * ((a : ℝ) / (n : ℝ))) := by
  rw [show (k : ZMod n) * (a : ZMod n) = (((k * a : ℕ) : ℤ) : ZMod n) by push_cast; ring]
  rw [ZMod.stdAddChar_coe]
  unfold Ex
  congr 1
  push_cast
  field_simp

/-- The additive interval sum at a unit is the exponential sum at the reduced residue. -/
theorem addSum_eq_Ex (c : ℕ → ℂ) (M N n : ℕ) [NeZero n] (u : (ZMod n)ˣ) :
    addSum c M N n u =
      ∑ k ∈ Ico M (M + N), c k * Ex ((k : ℝ) * (((u.val.val : ℕ) : ℝ) / (n : ℝ))) := by
  unfold addSum
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hu : (k : ZMod n) * (u : ZMod n) = (k : ZMod n) * ((u.val.val : ℕ) : ZMod n) := by
    rw [ZMod.natCast_zmod_val]
  rw [hu, stdAddChar_mul_eq_Ex]

/-- Units of `ZMod n` are in bijection with the reduced residues `a < n`. -/
theorem sum_units_val (n : ℕ) [NeZero n] (f : ℕ → ℝ) :
    ∑ u : (ZMod n)ˣ, f u.val.val =
      ∑ a ∈ (range n).filter (fun a => Nat.Coprime a n), f a := by
  classical
  refine Finset.sum_bij (fun (u : (ZMod n)ˣ) _ => u.val.val) ?_ ?_ ?_ ?_
  · intro u _
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    rw [← ZMod.isUnit_iff_coprime]
    simpa only [ZMod.natCast_zmod_val] using u.isUnit
  · intro u _ v _ h
    exact Units.ext (ZMod.val_injective n h)
  · intro a ha
    obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
    have hunit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).mpr ha2
    refine ⟨hunit.unit, Finset.mem_univ _, ?_⟩
    have hval : ZMod.val (hunit.unit : ZMod n) = ZMod.val (a : ZMod n) := by
      rw [hunit.unit_spec]
    rw [hval, ZMod.val_natCast_of_lt (Finset.mem_range.mp ha1)]
  · intro u _
    rfl

/-- The fixed-modulus bound in the form used for the final summation. -/
theorem per_modulus (c : ℕ → ℂ) (M N n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) / (n.totient : ℝ)) * ∑ χ ∈ primChars n, ‖charSum c M N n χ‖ ^ 2 ≤
      ∑ a ∈ (range n).filter (fun a => Nat.Coprime a n),
        ‖∑ k ∈ Ico M (M + N), c k * Ex ((k : ℝ) * ((a : ℝ) / n))‖ ^ 2 := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  refine (weighted_le_addSum c M N).trans ?_
  rw [← sum_units_val n
    (fun a => ‖∑ k ∈ Ico M (M + N), c k * Ex ((k : ℝ) * ((a : ℝ) / n))‖ ^ 2)]
  refine Finset.sum_le_sum (fun u _ => ?_)
  rw [addSum_eq_Ex]

/-- Reindex `range Q` shifted by one as `Icc 1 Q`. -/
theorem sum_range_add_one (Q : ℕ) (G : ℕ → ℝ) :
    ∑ q ∈ range Q, G (q + 1) = ∑ n ∈ Icc 1 Q, G n := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]

end

end Conjectures.Goldbach.MultiplicativeLargeSieve_aux

open Conjectures.Goldbach.MultiplicativeLargeSieve_aux
open Conjectures.Goldbach.AnalyticLargeSieve_aux

theorem Conjectures.Goldbach.MultiplicativeLargeSieve :
    letI := Classical.propDecidable; ∀ (M N Q : ℕ) (c : ℕ → ℂ), (∑ q ∈ Finset.range Q, ((q + 1 : ℝ) / (Nat.totient (q + 1) : ℝ)) * ∑ χ : DirichletCharacter ℂ (q + 1), if χ.IsPrimitive then ‖∑ k ∈ Finset.Ico M (M + N), c k * χ (k : ZMod (q + 1))‖ ^ 2 else 0) ≤ (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 := by
  intro M N Q c
  classical
  calc
    (∑ q ∈ Finset.range Q, (((q : ℝ) + 1) / (Nat.totient (q + 1) : ℝ)) *
        ∑ χ : DirichletCharacter ℂ (q + 1),
          if χ.IsPrimitive then
            ‖∑ k ∈ Finset.Ico M (M + N), c k * χ (k : ZMod (q + 1))‖ ^ 2 else 0)
      ≤ ∑ q ∈ Finset.range Q,
          ∑ a ∈ (Finset.range (q + 1)).filter (fun a => Nat.Coprime a (q + 1)),
            ‖∑ k ∈ Finset.Ico M (M + N),
              c k * Ex ((k : ℝ) * ((a : ℝ) / ((q + 1 : ℕ) : ℝ)))‖ ^ 2 := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        have hprim :
            (∑ χ : DirichletCharacter ℂ (q + 1),
              if χ.IsPrimitive then
                ‖∑ k ∈ Finset.Ico M (M + N), c k * χ (k : ZMod (q + 1))‖ ^ 2 else 0) =
              ∑ χ ∈ primChars (q + 1), ‖charSum c M N (q + 1) χ‖ ^ 2 := by
          rw [primChars, Finset.sum_filter]
          rfl
        rw [hprim]
        have hq := per_modulus c M N (q + 1) (Nat.succ_le_succ (Nat.zero_le q))
        have hcast : (((q + 1 : ℕ) : ℝ) / (Nat.totient (q + 1) : ℝ)) =
            ((q : ℝ) + 1) / (Nat.totient (q + 1) : ℝ) := by push_cast; ring
        rw [hcast] at hq
        exact hq
    _ = ∑ n ∈ Finset.Icc 1 Q,
          ∑ a ∈ (Finset.range n).filter (fun a => Nat.Coprime a n),
            ‖∑ k ∈ Finset.Ico M (M + N), c k * Ex ((k : ℝ) * ((a : ℝ) / n))‖ ^ 2 := by
        induction Q with
        | zero => simp
        | succ Q ih =>
            rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega), ih]
    _ ≤ (Real.pi * (N : ℝ) + (Q : ℝ) ^ 2) *
          ∑ k ∈ Finset.Ico M (M + N), ‖c k‖ ^ 2 :=
        Conjectures.Goldbach.AnalyticLargeSieve_aux.large_sieve M N Q c
