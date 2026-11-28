import Mathlib
import Conjectures.Goldbach.FareyHyperbolaRectangles

-- The divisor estimate used below was verified in #2977.
-- This is the pair-collision child of #4353.


namespace GoldbachPolynomialDifference

open Finset Polynomial
open scoped BigOperators

noncomputable def differencePolynomial (P : Polynomial ℤ) (h u : ℤ) : Polynomial ℤ :=
  P.taylor h - P - Polynomial.C u

theorem differencePolynomial_ne_zero (P : Polynomial ℤ) (h u : ℤ)
    (hdegree : 2 ≤ P.natDegree) (hh : h ≠ 0) :
    differencePolynomial P h u ≠ 0 := by
  let k := P.natDegree - 1
  let H := P.hasseDeriv k
  have hk0 : k ≠ 0 := by dsimp [k]; omega
  have h1k : 1 + k = P.natDegree := by dsimp [k]; omega
  have hHdeg : H.natDegree ≤ 1 := by
    apply (Polynomial.natDegree_hasseDeriv_le P k).trans
    dsimp [k]
    omega
  have hH_eval : H.eval h = H.coeff 1 * h + H.coeff 0 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hHdeg]
    simp
  have hP0 : P ≠ 0 := by
    intro he
    simp [he] at hdegree
  have hH1 : H.coeff 1 ≠ 0 := by
    change (P.hasseDeriv k).coeff 1 ≠ 0
    rw [Polynomial.hasseDeriv_coeff, h1k, Polynomial.coeff_natDegree]
    apply mul_ne_zero
    · exact_mod_cast (Nat.choose_pos (show k ≤ P.natDegree by dsimp [k]; omega)).ne'
    · exact Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hH0 : H.coeff 0 = P.coeff k := by
    change (P.hasseDeriv k).coeff 0 = P.coeff k
    rw [Polynomial.hasseDeriv_coeff]
    simp
  have hC : ((Polynomial.C u : Polynomial ℤ).coeff k) = 0 := by
    exact Polynomial.coeff_C_of_ne_zero hk0
  have hq : (differencePolynomial P h u).coeff k = H.coeff 1 * h := by
    simp only [differencePolynomial, Polynomial.coeff_sub, Polynomial.taylor_coeff, hC]
    change H.eval h - P.coeff k - 0 = H.coeff 1 * h
    rw [hH_eval, hH0]
    ring
  intro he
  rw [he, Polynomial.coeff_zero] at hq
  exact (mul_ne_zero hH1 hh) hq.symm

theorem differencePolynomial_natDegree_le (P : Polynomial ℤ) (h u : ℤ) :
    (differencePolynomial P h u).natDegree ≤ P.natDegree := by
  unfold differencePolynomial
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  · simp

theorem differencePolynomial_eval (P : Polynomial ℤ) (h u x : ℤ) :
    (differencePolynomial P h u).eval x = P.eval (x+h) - P.eval x - u := by
  simp [differencePolynomial, Polynomial.taylor_apply, Polynomial.eval_comp]

def differencePairs (P : Polynomial ℤ) (A : Finset ℤ) (u : ℤ) : Finset (ℤ × ℤ) :=
  (A.product A).filter fun v => P.eval v.2 - P.eval v.1 = u

private def signedDivisors (u : ℤ) : Finset ℤ :=
  (u.natAbs.divisors.image fun d : ℕ => (d : ℤ)) ∪
    (u.natAbs.divisors.image fun d : ℕ => -(d : ℤ))

private theorem signedDivisors_card (u : ℤ) :
    (signedDivisors u).card ≤ 2 * u.natAbs.divisors.card := by
  unfold signedDivisors
  rw [two_mul]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

private theorem signedDivisors_mem {u h : ℤ} (hu : u ≠ 0) (hd : h ∣ u) :
    h ∈ signedDivisors u := by
  have habs : u.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hu
  have hh : h.natAbs ∈ u.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hd, habs⟩
  unfold signedDivisors
  by_cases hn : 0 ≤ h
  · exact mem_union_left _ (mem_image.mpr ⟨h.natAbs, hh, Int.natAbs_of_nonneg hn⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨h.natAbs, hh,
      (Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)).symm⟩)

private theorem signedDivisors_ne_zero {u h : ℤ} (hh : h ∈ signedDivisors u) : h ≠ 0 := by
  have hpos {n : ℕ} (hn : n ∈ u.natAbs.divisors) : 0 < n := Nat.pos_of_mem_divisors hn
  unfold signedDivisors at hh
  rcases mem_union.mp hh with hh | hh
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
    exact Int.ofNat_ne_zero.mpr (hpos hn).ne'
  · obtain ⟨n, hn, rfl⟩ := mem_image.mp hh
    exact neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (hpos hn).ne')

theorem differencePairs_card_le (P : Polynomial ℤ) (A : Finset ℤ) (u : ℤ)
    (hdegree : 2 ≤ P.natDegree) (hu : u ≠ 0) :
    (differencePairs P A u).card ≤ 2 * P.natDegree * u.natAbs.divisors.card := by
  classical
  let B := signedDivisors u
  let R (h : ℤ) := (differencePolynomial P h u).roots.toFinset
  let f (x : ℤ × ℤ) : Σ _ : ℤ, ℤ := ⟨x.2-x.1, x.1⟩
  have hmaps (x : ℤ × ℤ) (hx : x ∈ differencePairs P A u) : f x ∈ B.sigma R := by
    rcases x with ⟨b,d⟩
    have hd := (mem_filter.mp hx).2
    change P.eval d - P.eval b = u at hd
    have hdvd : d-b ∣ u := hd ▸ Polynomial.sub_dvd_eval_sub d b P
    have hmem : d-b ∈ B := signedDivisors_mem hu hdvd
    have hne := differencePolynomial_ne_zero P (d-b) u hdegree (signedDivisors_ne_zero hmem)
    apply Finset.mem_sigma.mpr
    refine ⟨hmem, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr ?_)⟩
    change (differencePolynomial P (d-b) u).eval b = 0
    rw [differencePolynomial_eval, show b+(d-b)=d by omega, hd, sub_self]
  have hf : Set.InjOn f (↑(differencePairs P A u) : Set (ℤ × ℤ)) := by
    intro x _ y _ h
    have h1 := congrArg (fun z : Σ _ : ℤ, ℤ => z.2) h
    have h2 := congrArg (fun z : Σ _ : ℤ, ℤ => z.1) h
    change x.1 = y.1 at h1
    change x.2-x.1 = y.2-y.1 at h2
    exact Prod.ext h1 (by omega)
  calc
    _ ≤ (B.sigma R).card := Finset.card_le_card_of_injOn f hmaps hf
    _ = ∑ h ∈ B, (R h).card := Finset.card_sigma _ _
    _ ≤ ∑ _h ∈ B, P.natDegree := by
      apply Finset.sum_le_sum
      intro h _
      exact (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans (differencePolynomial_natDegree_le P h u))
    _ = B.card * P.natDegree := by simp
    _ ≤ (2*u.natAbs.divisors.card) * P.natDegree :=
      Nat.mul_le_mul_right _ (signedDivisors_card u)
    _ = _ := by ring

theorem evalFiber_card_le (P : Polynomial ℤ) (A : Finset ℤ) (v : ℤ)
    (hdegree : 0 < P.natDegree) :
    (A.filter fun x => P.eval x = v).card ≤ P.natDegree := by
  let Q := P - Polynomial.C v
  have hn : Q ≠ 0 := by
    intro h
    have he : P = Polynomial.C v := sub_eq_zero.mp h
    rw [he, Polynomial.natDegree_C] at hdegree
    exact (lt_irrefl _ hdegree)
  have hQdeg : Q.natDegree ≤ P.natDegree := (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hsub : (A.filter fun x => P.eval x = v) ⊆ Q.roots.toFinset := by
    intro x hx
    have hxv := (Finset.mem_filter.mp hx).2
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hn).mpr
    change (P - Polynomial.C v).eval x = 0
    simp [hxv]
  exact (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans hQdeg))

theorem differencePairs_zero_le (P : Polynomial ℤ) (A : Finset ℤ)
    (hdegree : 0 < P.natDegree) :
    (differencePairs P A 0).card ≤ A.card * P.natDegree := by
  let T (b : ℤ) := A.filter fun d => P.eval d = P.eval b
  let f (x : ℤ × ℤ) : Σ _ : ℤ, ℤ := ⟨x.1,x.2⟩
  have hm (x : ℤ × ℤ) (hx : x ∈ differencePairs P A 0) : f x ∈ A.sigma T := by
    have h := Finset.mem_filter.mp hx
    obtain ⟨hb, hd⟩ := Finset.mem_product.mp h.1
    exact Finset.mem_sigma.mpr ⟨hb, Finset.mem_filter.mpr ⟨hd, sub_eq_zero.mp h.2⟩⟩
  have hi : Function.Injective f := by
    intro x y h
    exact Prod.ext (congrArg (fun z : Σ _ : ℤ, ℤ => z.1) h)
      (congrArg (fun z : Σ _ : ℤ, ℤ => z.2) h)
  calc
    _ ≤ (A.sigma T).card := Finset.card_le_card_of_injOn f hm hi.injOn
    _ = ∑ b ∈ A, (T b).card := Finset.card_sigma _ _
    _ ≤ ∑ _b ∈ A, P.natDegree :=
      Finset.sum_le_sum fun b _ => evalFiber_card_le P A (P.eval b) hdegree
    _ = _ := by simp

end GoldbachPolynomialDifference



namespace GoldbachPolynomialMagnitude

open Finset

noncomputable def coefficientBound (P : Polynomial ℤ) : ℝ :=
  2 * (1 + ∑ i ∈ range (P.natDegree+1), |(P.coeff i : ℝ)|)

theorem coefficientBound_pos (P : Polynomial ℤ) : 0 < coefficientBound P := by
  unfold coefficientBound
  positivity

private theorem eval_magnitude (P : Polynomial ℤ) (M a : ℕ) (hM : 1 ≤ M) (ha : a ≤ M) :
    |(((P.eval (a : ℤ) : ℤ) : ℝ))| ≤
      (∑ i ∈ range (P.natDegree+1), |(P.coeff i : ℝ)|) * (M : ℝ)^P.natDegree := by
  have hMR : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have haR : (a : ℝ) ≤ M := by exact_mod_cast ha
  rw [Polynomial.eval_eq_sum_range]
  push_cast
  calc
    |∑ i ∈ range (P.natDegree+1), (P.coeff i : ℝ) * (a : ℝ)^i|
      ≤ ∑ i ∈ range (P.natDegree+1), |(P.coeff i : ℝ) * (a : ℝ)^i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (P.natDegree+1), |(P.coeff i : ℝ)| * (M : ℝ)^P.natDegree := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (a : ℝ)^i)]
      exact mul_le_mul_of_nonneg_left
        ((pow_le_pow_left₀ (Nat.cast_nonneg a) haR i).trans
          (pow_le_pow_right₀ hMR (by simpa using mem_range.mp hi))) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]

theorem natAbs_eval_sub_le (P : Polynomial ℤ) (M a c : ℕ)
    (hM : 1 ≤ M) (ha : a ≤ M) (hc : c ≤ M) :
    ((P.eval (a : ℤ) - P.eval (c : ℤ)).natAbs : ℝ) ≤
      coefficientBound P * (M : ℝ)^P.natDegree := by
  let S : ℝ := ∑ i ∈ range (P.natDegree+1), |(P.coeff i : ℝ)|
  have haMag : |(((P.eval (a : ℤ) : ℤ) : ℝ))| ≤ S * (M : ℝ)^P.natDegree := eval_magnitude P M a hM ha
  have hcMag : |(((P.eval (c : ℤ) : ℤ) : ℝ))| ≤ S * (M : ℝ)^P.natDegree := eval_magnitude P M c hM hc
  rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub]
  calc
    _ ≤ |(((P.eval (a : ℤ) : ℤ) : ℝ))| + |(((P.eval (c : ℤ) : ℤ) : ℝ))| := abs_sub _ _
    _ ≤ S * (M : ℝ)^P.natDegree + S * (M : ℝ)^P.natDegree := add_le_add haMag hcMag
    _ ≤ _ := by
      change _ ≤ 2*(1+S) * (M : ℝ)^P.natDegree
      nlinarith only [show 0 ≤ (M : ℝ)^P.natDegree by positivity]

theorem rpow_natAbs_eval_sub_le (P : Polynomial ℤ) (hP : 0 < P.natDegree)
    (ε : ℝ) (hε : 0 < ε) (M a c : ℕ) (hM : 1 ≤ M) (ha : a ≤ M) (hc : c ≤ M) :
    ((P.eval (a : ℤ) - P.eval (c : ℤ)).natAbs : ℝ)^(ε/(P.natDegree : ℝ)) ≤
      (coefficientBound P)^(ε/(P.natDegree : ℝ)) * (M : ℝ)^ε := by
  have hD : 0 < (P.natDegree : ℝ) := by exact_mod_cast hP
  let δ : ℝ := ε / (P.natDegree : ℝ)
  have hδ : 0 ≤ δ := div_nonneg hε.le hD.le
  change _ ^ δ ≤ (coefficientBound P)^δ * (M : ℝ)^ε
  calc
    _ ≤ (coefficientBound P * (M : ℝ)^P.natDegree)^δ :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (natAbs_eval_sub_le P M a c hM ha hc) hδ
    _ = _ := by
      rw [Real.mul_rpow (coefficientBound_pos P).le (by positivity)]
      congr 1
      rw [← Real.rpow_natCast_mul (by positivity)]
      congr 1
      dsimp [δ]
      field_simp

end GoldbachPolynomialMagnitude


namespace GoldbachPolynomialDivisors

/-- Drop the logarithmic factor from the verified divisor completion loss. -/
theorem divisor_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ δ := by
  obtain ⟨C, hC, h⟩ :=
    MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry.divisors_completion_loss hδ
  refine ⟨C, hC, fun m hm => ?_⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hfactor : (1 : ℝ) ≤ 3 + 2 * Real.log (m : ℝ) := by
    linarith only [Real.log_nonneg hm']
  exact (le_mul_of_one_le_right (by positivity) hfactor).trans (h m hm)

end GoldbachPolynomialDivisors


namespace GoldbachPolyCollision

open Finset Polynomial

/-- View the finite natural support inside the integer polynomial domain. -/
def liftSupport (A : Finset ℕ) : Finset ℤ :=
  A.map ⟨Int.ofNat, fun _ _ h => Int.ofNat.inj h⟩

theorem mem_liftSupport {A : Finset ℕ} {z : ℤ} :
    z ∈ liftSupport A ↔ ∃ a ∈ A, (a : ℤ) = z :=
  mem_map

theorem liftSupport_card (A : Finset ℕ) : (liftSupport A).card = A.card :=
  card_map _

/-- The polynomial value at the second index minus the value at the first. -/
def evalDifference (P : Polynomial ℤ) (z : ℤ × ℤ) : ℤ :=
  P.eval z.2 - P.eval z.1

/-- Move the two right-side terms across the equality to count differences. -/
theorem collision_card_eq_difference_pairs (P : Polynomial ℤ) (A : Finset ℕ) :
    let wt := fun x : Fin 2 → ↥A => ∑ i, P.eval ((x i : ℕ) : ℤ)
    ((univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
      (fun z => wt z.1 = wt z.2)).card =
      (((liftSupport A ×ˢ liftSupport A) ×ˢ (liftSupport A ×ˢ liftSupport A)).filter
        (fun z => evalDifference P z.1 = evalDifference P z.2)).card := by
  classical
  dsimp only
  let reorder (z : (Fin 2 → ↥A) × (Fin 2 → ↥A)) : (ℤ × ℤ) × (ℤ × ℤ) :=
    ((((z.2 0 : ℕ) : ℤ), ((z.1 0 : ℕ) : ℤ)), (((z.1 1 : ℕ) : ℤ), ((z.2 1 : ℕ) : ℤ)))
  have hmem (a : ↥A) : ((a : ℕ) : ℤ) ∈ liftSupport A :=
    mem_liftSupport.mpr ⟨a, a.property, rfl⟩
  apply Finset.card_bij (fun z _ => reorder z)
  · intro z hz
    refine mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_product.mpr ⟨mem_product.mpr ⟨hmem _, hmem _⟩,
        mem_product.mpr ⟨hmem _, hmem _⟩⟩
    · have h := (mem_filter.mp hz).2
      rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
      dsimp only [reorder, evalDifference]
      linarith only [h]
  · intro x _ y _ h
    apply Prod.ext
    · funext i
      apply Subtype.ext
      fin_cases i
      · exact Int.ofNat.inj (congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.1.2) h)
      · exact Int.ofNat.inj (congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.2.1) h)
    · funext i
      apply Subtype.ext
      fin_cases i
      · exact Int.ofNat.inj (congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.1.1) h)
      · exact Int.ofNat.inj (congrArg (fun z : (ℤ × ℤ) × (ℤ × ℤ) => z.2.2) h)
  · intro z hz
    obtain ⟨hz, h⟩ := mem_filter.mp hz
    obtain ⟨h1,h2⟩ := mem_product.mp hz
    obtain ⟨h11,h12⟩ := mem_product.mp h1
    obtain ⟨h21,h22⟩ := mem_product.mp h2
    rcases z with ⟨⟨z11,z12⟩,⟨z21,z22⟩⟩
    obtain ⟨c,hc,rfl⟩ := mem_liftSupport.mp h11
    obtain ⟨a,ha,rfl⟩ := mem_liftSupport.mp h12
    obtain ⟨b,hb,rfl⟩ := mem_liftSupport.mp h21
    obtain ⟨d,hd,rfl⟩ := mem_liftSupport.mp h22
    let lhs : Fin 2 → ↥A := ![⟨a,ha⟩, ⟨b,hb⟩]
    let rhs : Fin 2 → ↥A := ![⟨c,hc⟩, ⟨d,hd⟩]
    refine ⟨(lhs,rhs), mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
    simp only [Fin.sum_univ_two, lhs, rhs, Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp only [evalDifference] at h
    linarith only [h]

/-- Count ordered equal-value pairs by fixing their first member. -/
theorem card_equal_fibers_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (g : α → β) :
    ((S ×ˢ S).filter (fun p => g p.1 = g p.2)).card =
      ∑ x ∈ S, (S.filter (fun y => g y = g x)).card := by
  let R := (S ×ˢ S).filter (fun p => g p.1 = g p.2)
  have hR : R.filter (fun p => p.1 ∈ S) = R :=
    filter_eq_self.mpr (fun _ hp => (mem_product.mp (mem_filter.mp hp).1).1)
  change R.card = _
  rw [← hR, ← sum_card_fiberwise_eq_card_filter R S Prod.fst]
  apply sum_congr rfl
  intro x hx
  let e : α ↪ α × α := ⟨fun y => (x,y), fun _ _ h => congrArg Prod.snd h⟩
  rw [← card_map (s := S.filter (fun y => g y = g x)) e]
  congr 1
  ext p
  rcases p with ⟨a,b⟩
  simp only [R, mem_filter, mem_product, mem_map]
  constructor
  · rintro ⟨⟨⟨_,hb⟩,h⟩,rfl⟩
    exact ⟨b,⟨hb,h.symm⟩,rfl⟩
  · rintro ⟨y,⟨hy,h⟩,he⟩
    change (x,y) = (a,b) at he
    cases he
    exact ⟨⟨⟨hx,hy⟩,h.symm⟩,rfl⟩

/-- The frozen collision count as a sum of ordered difference-fiber sizes. -/
theorem collision_card_eq_difference_sum (P : Polynomial ℤ) (A : Finset ℕ) :
    let wt := fun x : Fin 2 → ↥A => ∑ i, P.eval ((x i : ℕ) : ℤ)
    let B := liftSupport A
    ((univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
      (fun z => wt z.1 = wt z.2)).card =
        ∑ z ∈ B ×ˢ B, ((B ×ˢ B).filter (fun w => evalDifference P w = evalDifference P z)).card := by
  exact (collision_card_eq_difference_pairs P A).trans
    (card_equal_fibers_sum (liftSupport A ×ˢ liftSupport A) (evalDifference P))

end GoldbachPolyCollision

namespace GoldbachPolyCollisionAggregation

open Finset GoldbachPolynomialDifference

/-- A bound on every nonzero fibre and a separate bound on the zero fibre. -/
theorem aggregate (P : Polynomial ℤ) (A : Finset ℤ) (hP : 0 < P.natDegree)
    (B : ℝ) (hB : 0 ≤ B)
    (hnonzero : ∀ x ∈ A ×ˢ A, P.eval x.2 - P.eval x.1 ≠ 0 →
      ((differencePairs P A (P.eval x.2 - P.eval x.1)).card : ℝ) ≤ B) :
    (∑ x ∈ A ×ˢ A, ((differencePairs P A (P.eval x.2 - P.eval x.1)).card : ℝ)) ≤
      ((P.natDegree : ℝ)^2 + B) * (A.card : ℝ)^2 := by
  let S := A ×ˢ A
  let f (x : ℤ × ℤ) := P.eval x.2 - P.eval x.1
  let g (x : ℤ × ℤ) := ((differencePairs P A (f x)).card : ℝ)
  let Z := S.filter (fun x => f x = 0)
  let U := S.filter (fun x => f x ≠ 0)
  have hZ : Z = differencePairs P A 0 := rfl
  have hC : (Z.card : ℝ) ≤ (P.natDegree : ℝ) * (A.card : ℝ) := by
    rw [hZ, ← Nat.cast_mul]
    exact_mod_cast (show _ ≤ P.natDegree * A.card by
      simpa only [mul_comm] using differencePairs_zero_le P A hP)
  have hzero : (∑ x ∈ Z, g x) = (Z.card : ℝ)^2 := by
    calc
      _ = ∑ _x ∈ Z, (Z.card : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp only [g]
        rw [(Finset.mem_filter.mp hx).2, hZ]
      _ = _ := by simp [nsmul_eq_mul, pow_two]
  have hU : (U.card : ℝ) ≤ (A.card : ℝ)^2 := by
    rw [pow_two, ← Nat.cast_mul, ← Finset.card_product]
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ S)
  have hup : (∑ x ∈ U, g x) ≤ (U.card : ℝ) * B := calc
    _ ≤ ∑ _x ∈ U, B := Finset.sum_le_sum (fun x hx =>
      hnonzero x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2)
    _ = _ := by simp [nsmul_eq_mul]
  change (∑ x ∈ S, g x) ≤ _
  calc
    _ = (∑ x ∈ Z, g x) + (∑ x ∈ U, g x) :=
      (Finset.sum_filter_add_sum_filter_not S (fun x => f x = 0) g).symm
    _ ≤ (Z.card : ℝ)^2 + (U.card : ℝ) * B := add_le_add hzero.le hup
    _ ≤ ((P.natDegree : ℝ) * (A.card : ℝ))^2 + (A.card : ℝ)^2 * B :=
      (add_le_add (pow_le_pow_left₀ (Nat.cast_nonneg _) hC 2) (mul_le_mul_of_nonneg_right hU hB))
    _ = _ := by ring

end GoldbachPolyCollisionAggregation

open Finset GoldbachPolynomialDifference GoldbachPolynomialMagnitude GoldbachPolyCollision

theorem Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b : (∀ (x1 : Polynomial ℤ),   (2 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : (Fin (2 : ℕ) → ↥x8) → ℤ := fun (x10 : Fin (2 : ℕ) → ↥x8) => ∑ x11 : Fin (2 : ℕ), Polynomial.eval (↑↑(x10 x11)) x1;                   have x11 : Finset ((Fin (2 : ℕ) → ↥x8) × (Fin (2 : ℕ) → ↥x8)) := Finset.univ;                   ↑{x12 ∈ x11 | x10 x12.1 = x10 x12.2}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ (2 : ℕ)) := by
  intro P hdegree ε hε
  have hP : 0 < P.natDegree := by omega
  let D : ℝ := P.natDegree
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast hP
  let δ : ℝ := ε / D
  have hδ : 0 < δ := div_pos hε hD
  obtain ⟨C, hC, hdiv⟩ := GoldbachPolynomialDivisors.divisor_bound hδ
  let T := 2*D*C*(coefficientBound P)^δ
  have hK : 0 < coefficientBound P := coefficientBound_pos P
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨D^2+T, by positivity, ?_⟩
  intro M hM A hA
  have hM1 : 1 ≤ M := by omega
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hpow : 1 ≤ (M : ℝ)^ε := Real.one_le_rpow hMR hε.le
  let B := liftSupport A
  have hBcard : (B.card : ℝ) = A.card := by
    exact_mod_cast liftSupport_card A
  have hcount := collision_card_eq_difference_sum P A
  dsimp only at hcount ⊢
  rw [hcount]
  push_cast
  have H (z : ℤ × ℤ) (hz : z ∈ B ×ˢ B) (hu : P.eval z.2 - P.eval z.1 ≠ 0) :
      ((differencePairs P B (P.eval z.2 - P.eval z.1)).card : ℝ) ≤ T*(M : ℝ)^ε := by
    obtain ⟨z1,z2⟩ := z
    obtain ⟨hz1,hz2⟩ := Finset.mem_product.mp hz
    obtain ⟨c,hc,rfl⟩ := mem_liftSupport.mp hz1
    obtain ⟨a,ha,rfl⟩ := mem_liftSupport.mp hz2
    let u := P.eval (a : ℤ) - P.eval (c : ℤ)
    change u ≠ 0 at hu
    change ((differencePairs P B u).card : ℝ) ≤ T*(M : ℝ)^ε
    have hm : 0 < u.natAbs := Int.natAbs_pos.mpr hu
    have huMag : (u.natAbs : ℝ)^δ ≤ (coefficientBound P)^δ * (M : ℝ)^ε :=
      rpow_natAbs_eval_sub_le P hP ε hε M a c hM1
        (mem_Icc.mp (hA ha)).2 (mem_Icc.mp (hA hc)).2
    calc
      _ ≤ 2*D*(u.natAbs.divisors.card : ℝ) := by
        dsimp only [D]
        exact_mod_cast differencePairs_card_le P B u hdegree hu
      _ ≤ 2*D*(C*(u.natAbs : ℝ)^δ) := by gcongr; exact hdiv _ hm
      _ ≤ 2*D*(C*((coefficientBound P)^δ*(M : ℝ)^ε)) := by gcongr
      _ = _ := by dsimp [T]; ring
  have hagg := GoldbachPolyCollisionAggregation.aggregate P B hP
    (T*(M : ℝ)^ε) (by positivity) H
  change (∑ z ∈ B ×ˢ B, ((differencePairs P B (P.eval z.2 - P.eval z.1)).card : ℝ)) ≤ _
  have hscaled : D^2 ≤ D^2*(M : ℝ)^ε := le_mul_of_one_le_right (sq_nonneg D) hpow
  calc
    _ ≤ (D^2 + T*(M : ℝ)^ε) * (B.card : ℝ)^2 := hagg
    _ ≤ (D^2*(M : ℝ)^ε + T*(M : ℝ)^ε) * (B.card : ℝ)^2 :=
      mul_le_mul_of_nonneg_right (add_le_add_left hscaled _) (sq_nonneg _)
    _ = _ := by rw [hBcard]; ring
