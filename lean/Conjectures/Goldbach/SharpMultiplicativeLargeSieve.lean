import Mathlib
import Conjectures.Goldbach.SelbergSharpLargeSieve

/-!
Optimal Montgomery--Vaughan multiplicative large sieve.

Credit: the Dirichlet-character orthogonality, Gauss-sum inversion and character Parseval
machinery is adapted from the fleet proof of the sibling lemma
`L-goldbach-multiplicative-large-sieve` (which itself adapted
`Conjectures.Goldbach.B13BilateralVaughanReduction`, namespace `BombieriVinogradov.LargeSieve`).
The sharp additive large sieve on circle-separated points with constant `(M + 1/δ)` is taken from
the accepted module `Conjectures.Goldbach.SelbergSharpLargeSieve`
(`separated_additive_sieve`), used at separation `δ = Q⁻²`.
-/

open Finset
open scoped BigOperators ComplexConjugate

namespace Conjectures.Goldbach.SharpMultiplicativeLargeSieve_aux

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

/-- The real exponential phase `e(x)`. -/
noncomputable def ph (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

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
theorem stdAddChar_mul_eq_ph (n a k : ℕ) [NeZero n] :
    ZMod.stdAddChar ((k : ZMod n) * (a : ZMod n)) = ph ((k : ℝ) * ((a : ℝ) / (n : ℝ))) := by
  rw [show (k : ZMod n) * (a : ZMod n) = (((k * a : ℕ) : ℤ) : ZMod n) by push_cast; ring]
  rw [ZMod.stdAddChar_coe]
  unfold ph
  congr 1
  push_cast
  field_simp

/-- The additive interval sum at a unit is the exponential sum at the reduced residue. -/
theorem addSum_eq_ph (c : ℕ → ℂ) (M N n : ℕ) [NeZero n] (u : (ZMod n)ˣ) :
    addSum c M N n u =
      ∑ k ∈ Ico M (M + N), c k * ph ((k : ℝ) * (((u.val.val : ℕ) : ℝ) / (n : ℝ))) := by
  unfold addSum
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hu : (k : ZMod n) * (u : ZMod n) = (k : ZMod n) * ((u.val.val : ℕ) : ZMod n) := by
    rw [ZMod.natCast_zmod_val]
  rw [hu, stdAddChar_mul_eq_ph]

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
        ‖∑ k ∈ Ico M (M + N), c k * ph ((k : ℝ) * ((a : ℝ) / n))‖ ^ 2 := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  refine (weighted_le_addSum c M N).trans ?_
  rw [← sum_units_val n
    (fun a => ‖∑ k ∈ Ico M (M + N), c k * ph ((k : ℝ) * ((a : ℝ) / n))‖ ^ 2)]
  refine Finset.sum_le_sum (fun u _ => ?_)
  rw [addSum_eq_ph]

/-! ### The Farey point set and its separation -/

/-- The Farey pairs: moduli `1 ≤ q ≤ Q` with reduced numerators `a < q`. -/
def fareySet (Q : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 Q).sigma (fun q => (Finset.range q).filter (fun a => Nat.Coprime a q))

/-- The rational point attached to a Farey pair. -/
def fareyPoint (s : Σ _ : ℕ, ℕ) : ℝ := ((s.2 : ℕ) : ℝ) / ((s.1 : ℕ) : ℝ)

/-- The integer numerator of a Farey difference is never zero. -/
theorem int_farey_ne_zero {q q' a a' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q') (ha : a < q) (ha' : a' < q')
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime a' q')
    (hne : ¬(q = q' ∧ a = a')) (m : ℤ) :
    (a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - m * (q : ℤ) * (q' : ℤ) ≠ 0 := by
  intro h
  have hq0 : (q : ℤ) ≠ 0 := by omega
  have h1 : (q : ℤ) ∣ (a : ℤ) * (q' : ℤ) := by
    refine ⟨(a' : ℤ) + m * (q' : ℤ), ?_⟩
    linarith
  have h2 : (q' : ℤ) ∣ (a' : ℤ) * (q : ℤ) := by
    refine ⟨(a : ℤ) - m * (q : ℤ), ?_⟩
    linarith
  have h1' : q ∣ a * q' := by
    have hh : (q : ℤ) ∣ ((a * q' : ℕ) : ℤ) := by push_cast; exact h1
    exact_mod_cast hh
  have h2' : q' ∣ a' * q := by
    have hh : (q' : ℤ) ∣ ((a' * q : ℕ) : ℤ) := by push_cast; exact h2
    exact_mod_cast hh
  have hqdiv : q ∣ q' := hcop.symm.dvd_of_dvd_mul_left h1'
  have hq'div : q' ∣ q := hcop'.symm.dvd_of_dvd_mul_left h2'
  have hqq : q = q' := Nat.dvd_antisymm hqdiv hq'div
  subst hqq
  have hfac : ((a : ℤ) - (a' : ℤ) - m * (q : ℤ)) * (q : ℤ) = 0 := by linear_combination h
  have hlin : (a : ℤ) - (a' : ℤ) = m * (q : ℤ) := by
    rcases mul_eq_zero.mp hfac with hzero | hzero
    · linarith
    · exact absurd hzero hq0
  have hlt : (a : ℤ) - (a' : ℤ) < (q : ℤ) := by omega
  have hgt : -(q : ℤ) < (a : ℤ) - (a' : ℤ) := by omega
  have hm0 : m = 0 := by
    by_contra hm
    rcases lt_or_gt_of_ne hm with hneg | hpos
    · have : m * (q : ℤ) ≤ -(q : ℤ) := by nlinarith
      linarith
    · have : (q : ℤ) ≤ m * (q : ℤ) := by nlinarith
      linarith
  subst hm0
  have haa : a = a' := by omega
  exact hne ⟨rfl, haa⟩

/-- Two distinct Farey points are at least `1 / (q q')` apart modulo one. -/
theorem farey_sep {q q' a a' : ℕ} (m : ℤ)
    (hq : 1 ≤ q) (hq' : 1 ≤ q') (ha : a < q) (ha' : a' < q')
    (hcop : Nat.Coprime a q) (hcop' : Nat.Coprime a' q')
    (hne : ¬(q = q' ∧ a = a')) :
    1 / ((q : ℝ) * (q' : ℝ)) ≤
      |(a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ) - (m : ℝ)| := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq'pos : (0 : ℝ) < q' := by exact_mod_cast (by omega : 0 < q')
  have hN := int_farey_ne_zero hq hq' ha ha' hcop hcop' hne m
  have hNabs : (1 : ℝ) ≤
      |(a : ℝ) * (q' : ℝ) - (a' : ℝ) * (q : ℝ) - (m : ℝ) * (q : ℝ) * (q' : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |(a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - m * (q : ℤ) * (q' : ℤ)| :=
      Int.one_le_abs hN
    have h2 : (1 : ℝ) ≤
        ((|(a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - m * (q : ℤ) * (q' : ℤ)| : ℤ) : ℝ) := by
      exact_mod_cast h1
    have h4 : (((a : ℤ) * (q' : ℤ) - (a' : ℤ) * (q : ℤ) - m * (q : ℤ) * (q' : ℤ) : ℤ) : ℝ) =
        (a : ℝ) * (q' : ℝ) - (a' : ℝ) * (q : ℝ) - (m : ℝ) * (q : ℝ) * (q' : ℝ) := by
      push_cast
      ring
    rw [Int.cast_abs, h4] at h2
    exact h2
  have hident : (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ) - (m : ℝ) =
      ((a : ℝ) * (q' : ℝ) - (a' : ℝ) * (q : ℝ) - (m : ℝ) * (q : ℝ) * (q' : ℝ)) /
        ((q : ℝ) * (q' : ℝ)) := by
    field_simp
  have hden : (0 : ℝ) < (q : ℝ) * (q' : ℝ) := mul_pos hqpos hq'pos
  rw [hident, abs_div, abs_of_pos hden]
  exact (div_le_div_iff_of_pos_right hden).mpr hNabs

theorem farey_circleSeparated (Q : ℕ) (hQ : 1 ≤ Q) :
    Conjectures.Goldbach.SelbergSharpLargeSieve_aux.GoldbachBDHSharp.OAI.Ostmann.CircleSeparated
      (fun s : ↥(fareySet Q) => fareyPoint s.1) (1 / (Q : ℝ) ^ 2) := by
  classical
  intro s t hst m
  rcases s with ⟨⟨q, a⟩, hs⟩
  rcases t with ⟨⟨q', a'⟩, ht⟩
  have hne : ¬(q = q' ∧ a = a') := by
    rintro ⟨rfl, rfl⟩
    exact hst rfl
  have hs' := Finset.mem_sigma.mp hs
  have ht' := Finset.mem_sigma.mp ht
  have hq := Finset.mem_Icc.mp hs'.1
  have hq' := Finset.mem_Icc.mp ht'.1
  have ha := Finset.mem_filter.mp hs'.2
  have ha' := Finset.mem_filter.mp ht'.2
  have haq : a < q := Finset.mem_range.mp ha.1
  have haq' : a' < q' := Finset.mem_range.mp ha'.1
  have hsep := farey_sep m hq.1 hq'.1 haq haq' ha.2 ha'.2 hne
  have hQQ : (q : ℝ) * (q' : ℝ) ≤ (Q : ℝ) ^ 2 := by
    have h1 : (q : ℝ) ≤ Q := by exact_mod_cast hq.2
    have h2 : (q' : ℝ) ≤ Q := by exact_mod_cast hq'.2
    have h3 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  have hpos : (0 : ℝ) < (q : ℝ) * (q' : ℝ) := by
    have : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have : (0 : ℝ) < q' := by exact_mod_cast (by omega : 0 < q')
    positivity
  have hkey : 1 / (Q : ℝ) ^ 2 ≤ 1 / ((q : ℝ) * (q' : ℝ)) :=
    one_div_le_one_div_of_le hpos hQQ
  have hval : fareyPoint (⟨q, a⟩ : Σ _ : ℕ, ℕ) - fareyPoint (⟨q', a'⟩ : Σ _ : ℕ, ℕ) - (m : ℝ) =
      (a : ℝ) / (q : ℝ) - (a' : ℝ) / (q' : ℝ) - (m : ℝ) := rfl
  rw [hval]
  exact hkey.trans hsep

/-! ### The final assembly -/

theorem ph_eq_sieve (x : ℝ) :
    ph x = Conjectures.Goldbach.SelbergSharpLargeSieve_aux.GoldbachBDHSharp.OAI.Ostmann.sieveHalfPhase
      (2 * x) := by
  unfold ph Conjectures.Goldbach.SelbergSharpLargeSieve_aux.GoldbachBDHSharp.OAI.Ostmann.sieveHalfPhase
  congr 1
  push_cast
  ring

theorem sum_Ico_eq_sum_fin {α : Type*} [AddCommMonoid α] (f : ℕ → α) (M L : ℕ) :
    (∑ k ∈ Ico M (M + L), f k) = ∑ n : Fin L, f (M + n.val) := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, ← Fin.sum_univ_eq_sum_range]

theorem main_bound (M L Q : ℕ) (a : ℕ → ℂ) :
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (Nat.totient q : ℝ)) *
      ∑ χ ∈ primChars q, ‖charSum a M L q χ‖ ^ 2) ≤
      ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ico M (M + L), ‖a n‖ ^ 2 := by
  classical
  by_cases hQ : Q = 0
  · subst hQ
    have hempty : (Finset.Icc (1 : ℕ) 0) = ∅ := by ext q; simp
    rw [hempty, Finset.sum_empty]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    exact mul_nonneg (Nat.cast_nonneg L) (Finset.sum_nonneg (fun n _ => sq_nonneg _))
  · have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr hQ
    have hstep1 : (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (Nat.totient q : ℝ)) *
        ∑ χ ∈ primChars q, ‖charSum a M L q χ‖ ^ 2) ≤
        ∑ q ∈ Finset.Icc 1 Q, ∑ a' ∈ (range q).filter (fun a' => Nat.Coprime a' q),
          ‖∑ k ∈ Ico M (M + L), a k * ph ((k : ℝ) * ((a' : ℝ) / q))‖ ^ 2 := by
      refine Finset.sum_le_sum (fun q hq => ?_)
      exact per_modulus a M L q (Finset.mem_Icc.mp hq).1
    have hcoe : (∑ s : ↥(fareySet Q),
          ‖∑ k ∈ Ico M (M + L), a k * ph ((k : ℝ) * fareyPoint s.1)‖ ^ 2) =
        ∑ x ∈ fareySet Q, ‖∑ k ∈ Ico M (M + L), a k * ph ((k : ℝ) * fareyPoint x)‖ ^ 2 :=
      Finset.sum_coe_sort (fareySet Q)
        (fun x => ‖∑ k ∈ Ico M (M + L), a k * ph ((k : ℝ) * fareyPoint x)‖ ^ 2)
    have hstep2 : (∑ q ∈ Finset.Icc 1 Q, ∑ a' ∈ (range q).filter (fun a' => Nat.Coprime a' q),
          ‖∑ k ∈ Ico M (M + L), a k * ph ((k : ℝ) * ((a' : ℝ) / q))‖ ^ 2) =
        ∑ s : ↥(fareySet Q),
          ‖∑ k ∈ Ico M (M + L), a k * ph ((k : ℝ) * fareyPoint s.1)‖ ^ 2 := by
      rw [hcoe]
      unfold fareySet
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      rfl
    let c : Fin L → ℂ := fun n => a (M + n.val)
    have hinner : ∀ s : ↥(fareySet Q),
        (∑ k ∈ Ico M (M + L), a k * ph ((k : ℝ) * fareyPoint s.1)) =
          ∑ n : Fin L, c n *
            Conjectures.Goldbach.SelbergSharpLargeSieve_aux.GoldbachBDHSharp.OAI.Ostmann.sieveHalfPhase
              (2 * ((M : ℝ) + (n.val : ℝ)) * fareyPoint s.1) := by
      intro s
      rw [sum_Ico_eq_sum_fin]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      have hcast : ((M + n.val : ℕ) : ℝ) = (M : ℝ) + (n.val : ℝ) := by push_cast; ring
      have harg : (2 : ℝ) * (((M : ℝ) + (n.val : ℝ)) * fareyPoint s.1) =
          2 * ((M : ℝ) + (n.val : ℝ)) * fareyPoint s.1 := by ring
      rw [hcast, ph_eq_sieve, harg]
    have hstep3 : (∑ s : ↥(fareySet Q),
          ‖∑ k ∈ Ico M (M + L), a k * ph ((k : ℝ) * fareyPoint s.1)‖ ^ 2) =
        ∑ s : ↥(fareySet Q),
          ‖∑ n : Fin L, c n *
            Conjectures.Goldbach.SelbergSharpLargeSieve_aux.GoldbachBDHSharp.OAI.Ostmann.sieveHalfPhase
              (2 * ((M : ℝ) + (n.val : ℝ)) * fareyPoint s.1)‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun s _ => ?_)
      rw [hinner s]
    have hδ : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
    have hsieve :=
      Conjectures.Goldbach.SelbergSharpLargeSieve_aux.GoldbachBDHSharp.OAI.Ostmann.separated_additive_sieve
        (fun s : ↥(fareySet Q) => fareyPoint s.1) (1 / (Q : ℝ) ^ 2) hδ
        (farey_circleSeparated Q hQ1) L (M : ℝ) c
    have hnorm : (∑ n : Fin L, ‖c n‖ ^ 2) = ∑ k ∈ Ico M (M + L), ‖a k‖ ^ 2 := by
      rw [← sum_Ico_eq_sum_fin (fun k => ‖a k‖ ^ 2) M L]
    have hδinv : 1 / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by
      field_simp
    calc
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (Nat.totient q : ℝ)) *
          ∑ χ ∈ primChars q, ‖charSum a M L q χ‖ ^ 2)
        ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ a' ∈ (range q).filter (fun a' => Nat.Coprime a' q),
            ‖∑ k ∈ Ico M (M + L), a k * ph ((k : ℝ) * ((a' : ℝ) / q))‖ ^ 2 := hstep1
      _ = ∑ s : ↥(fareySet Q),
            ‖∑ k ∈ Ico M (M + L), a k * ph ((k : ℝ) * fareyPoint s.1)‖ ^ 2 := hstep2
      _ = ∑ s : ↥(fareySet Q),
            ‖∑ n : Fin L, c n *
              Conjectures.Goldbach.SelbergSharpLargeSieve_aux.GoldbachBDHSharp.OAI.Ostmann.sieveHalfPhase
                (2 * ((M : ℝ) + (n.val : ℝ)) * fareyPoint s.1)‖ ^ 2 := hstep3
      _ ≤ ((L : ℝ) + 1 / (1 / (Q : ℝ) ^ 2)) * ∑ n : Fin L, ‖c n‖ ^ 2 := hsieve
      _ = ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ k ∈ Ico M (M + L), ‖a k‖ ^ 2 := by
          rw [hnorm, hδinv]

end

end Conjectures.Goldbach.SharpMultiplicativeLargeSieve_aux

open Conjectures.Goldbach.SharpMultiplicativeLargeSieve_aux

theorem Conjectures.Goldbach.SharpMultiplicativeLargeSieve :
    letI := Classical.propDecidable; ∀ (M L Q : ℕ) (a : ℕ → ℂ), ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (Nat.totient q : ℝ)) * ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive), ‖∑ n ∈ Finset.Ico M (M + L), a n * χ (n : ZMod q)‖ ^ 2 ≤ ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ico M (M + L), ‖a n‖ ^ 2 := by
  intro M L Q a
  classical
  have hset : ∀ q : ℕ,
      (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive) = primChars q := by
    intro q
    ext χ
    simp [primChars]
  calc
    (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (Nat.totient q : ℝ)) *
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (·.IsPrimitive),
          ‖∑ n ∈ Finset.Ico M (M + L), a n * χ (n : ZMod q)‖ ^ 2)
      = ∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (Nat.totient q : ℝ)) *
          ∑ χ ∈ primChars q, ‖charSum a M L q χ‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [hset q]
        rfl
    _ ≤ ((L : ℝ) + (Q : ℝ) ^ 2) * ∑ n ∈ Finset.Ico M (M + L), ‖a n‖ ^ 2 :=
        Conjectures.Goldbach.SharpMultiplicativeLargeSieve_aux.main_bound M L Q a
