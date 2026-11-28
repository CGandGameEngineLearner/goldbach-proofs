import Mathlib
import Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b

namespace EqualSumCollision

open Finset Polynomial GoldbachPolynomialDifference

-- The leading-coefficient calculation and signed-divisor bounds are adapted
-- from the Apache-2.0 proof Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b.
private theorem degree_diff (P : Polynomial ℤ) (h : ℤ)
    (hdegree : 3 ≤ P.natDegree) (hh : h ≠ 0) :
    2 ≤ (differencePolynomial P h 0).natDegree := by
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
  have hC : ((Polynomial.C 0 : Polynomial ℤ).coeff k) = 0 := by
    exact Polynomial.coeff_C_of_ne_zero hk0
  have hq : (differencePolynomial P h 0).coeff k = H.coeff 1 * h := by
    simp only [differencePolynomial, Polynomial.coeff_sub, Polynomial.taylor_coeff, hC]
    change H.eval h - P.coeff k - 0 = H.coeff 1 * h
    rw [hH_eval, hH0]
    ring
  exact (by dsimp [k]; omega : 2 ≤ k) |>.trans (Polynomial.le_natDegree_of_ne_zero (hq ▸ mul_ne_zero hH1 hh))

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

/-- A nonzero polynomial discrepancy and equality of the two ordinary
sums restrict a quadruple to a pair of divisor choices and a root fiber. -/
theorem nonzero_fiber (P : Polynomial ℤ) (A : Finset ℕ) (D : ℤ)
    (hP : 3 ≤ P.natDegree) (hD : D ≠ 0) :
    let W (x : Fin 2 → ↥A) := ∑ i, P.eval ((x i : ℕ) : ℤ)
    ((Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
      (fun z => (z.1 0 : ℕ) + z.1 1 = (z.2 0 : ℕ) + z.2 1 ∧
        W z.1 - W z.2 = D)).card ≤
      4 * P.natDegree * D.natAbs.divisors.card ^ 2 := by
  classical
  intro W
  let X := Fin 2 → ↥A
  let S := (Finset.univ : Finset (X × X)).filter
    (fun z => (z.1 0 : ℕ) + z.1 1 = (z.2 0 : ℕ) + z.2 1 ∧ W z.1 - W z.2 = D)
  let I := A.image (fun n : ℕ => (n : ℤ))
  let B := signedDivisors D
  let F := fun h : ℤ => differencePairs (differencePolynomial P h 0) I D
  let enc := fun z : X × X => (⟨((z.1 0 : ℕ) : ℤ) - ((z.2 0 : ℕ) : ℤ),
    (((z.1 1 : ℕ) : ℤ), ((z.2 0 : ℕ) : ℤ))⟩ : Σ _ : ℤ, ℤ × ℤ)
  have maps (z : X × X) (hz : z ∈ S) : enc z ∈ B.sigma F := by
    obtain ⟨hlin, hwt⟩ := (Finset.mem_filter.mp hz).2
    let a : ℤ := z.1 0
    let b : ℤ := z.1 1
    let c : ℤ := z.2 0
    let d : ℤ := z.2 1
    have he : a+b=c+d := by
      dsimp only [a, b, c, d]
      exact_mod_cast hlin
    simp only [W, Fin.sum_univ_two] at hwt
    change P.eval a + P.eval b - (P.eval c + P.eval d) = D at hwt
    have hdvd : a-c ∣ D := by
      rw [← hwt, show P.eval a + P.eval b - (P.eval c + P.eval d) =
          (P.eval a - P.eval c) - (P.eval d - P.eval b) by ring]
      apply dvd_sub (Polynomial.sub_dvd_eval_sub a c P)
      rw [show a-c=d-b by omega]
      exact Polynomial.sub_dvd_eval_sub d b P
    refine Finset.mem_sigma.mpr ⟨signedDivisors_mem hD hdvd, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_image.mpr ⟨_, (z.1 1).property, rfl⟩,
         Finset.mem_image.mpr ⟨_, (z.2 0).property, rfl⟩⟩
    · change (differencePolynomial P (a-c) 0).eval c -
          (differencePolynomial P (a-c) 0).eval b = D
      rw [differencePolynomial_eval, differencePolynomial_eval, show c+(a-c)=a by omega,
        show b+(a-c)=d by omega]
      omega
  have inj : Set.InjOn enc (↑S : Set (X × X)) := by
    intro x hx y hy hxy
    have hb := congrArg (fun q : Σ _ : ℤ, ℤ × ℤ => q.2.1) hxy
    have hc := congrArg (fun q : Σ _ : ℤ, ℤ × ℤ => q.2.2) hxy
    have hh := congrArg (fun q : Σ _ : ℤ, ℤ × ℤ => q.1) hxy
    dsimp [enc] at hb hc hh
    have hx' := (Finset.mem_filter.mp hx).2.1
    have hy' := (Finset.mem_filter.mp hy).2.1
    apply Prod.ext <;> funext i <;> apply Subtype.ext <;> fin_cases i <;> dsimp <;> omega
  calc
    S.card ≤ (B.sigma F).card := Finset.card_le_card_of_injOn enc maps inj
    _ = ∑ h ∈ B, (F h).card := Finset.card_sigma _ _
    _ ≤ ∑ _h ∈ B, 2 * P.natDegree * D.natAbs.divisors.card := by
      apply Finset.sum_le_sum
      intro h hh
      have hdeg := degree_diff P h hP (signedDivisors_ne_zero hh)
      apply (differencePairs_card_le _ _ D hdeg hD).trans
      gcongr
      exact differencePolynomial_natDegree_le _ _ _
    _ = B.card * (2 * P.natDegree * D.natAbs.divisors.card) := by simp
    _ ≤ (2 * D.natAbs.divisors.card) * (2 * P.natDegree * D.natAbs.divisors.card) :=
      Nat.mul_le_mul_right _ (signedDivisors_card D)
    _ = 4 * P.natDegree * D.natAbs.divisors.card ^ 2 := by ring

end EqualSumCollision

namespace EqualSumCollision

open Polynomial GoldbachPolynomialMagnitude GoldbachPolynomialDivisors

theorem divisor_growth (P : Polynomial ℤ) (hP : 3 ≤ P.natDegree) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ), 2 ≤ M → ∀ (a b c d : ℕ),
      a ≤ M → b ≤ M → c ≤ M → d ≤ M → ∀ (D : ℤ), D ≠ 0 →
      D = P.eval (a : ℤ) + P.eval (b : ℤ) - (P.eval (c : ℤ) + P.eval (d : ℤ)) →
      4 * (P.natDegree : ℝ) * (D.natAbs.divisors.card : ℝ) ^ 2 ≤ C * (M : ℝ)^ε := by
  have hdR : (0 : ℝ) < P.natDegree := by exact_mod_cast (by omega : 0 < P.natDegree)
  let δ := (ε / 2) / (P.natDegree : ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK, hτ⟩ := divisor_bound hδ
  have hB := coefficientBound_pos P
  let F := K * (2 * coefficientBound P) ^ δ
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨4 * P.natDegree * F^2, by positivity, ?_⟩
  intro M hM a b c d ha hb hc hd D hD hEq
  have h1 : 1 ≤ M := by omega
  have hmag : (D.natAbs : ℝ) ≤ (2 * coefficientBound P) * (M : ℝ)^P.natDegree := by
    have he : D = (P.eval (a : ℤ) - P.eval (c : ℤ)) + (P.eval (b : ℤ) - P.eval (d : ℤ)) := by
      rw [hEq]; ring
    rw [he]
    calc
      _ ≤ ((P.eval (a : ℤ) - P.eval (c : ℤ)).natAbs : ℝ) +
          ((P.eval (b : ℤ) - P.eval (d : ℤ)).natAbs : ℝ) := by exact_mod_cast Int.natAbs_add_le _ _
      _ ≤ coefficientBound P * (M : ℝ)^P.natDegree + coefficientBound P * (M : ℝ)^P.natDegree :=
        add_le_add (natAbs_eval_sub_le P M a c h1 ha hc) (natAbs_eval_sub_le P M b d h1 hb hd)
      _ = _ := by ring
  have hpow : ((M : ℝ)^P.natDegree)^δ = (M : ℝ)^(ε/2) := by
    rw [← Real.rpow_natCast_mul (Nat.cast_nonneg M)]
    congr 1
    dsimp [δ]
    field_simp
  have hτ' : (D.natAbs.divisors.card : ℝ) ≤ F * (M : ℝ)^(ε/2) := by
    apply (hτ _ (Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr hD))).trans
    calc
      _ ≤ K * ((2 * coefficientBound P) * (M : ℝ)^P.natDegree)^δ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hmag hδ.le) hK.le
      _ = _ := by rw [Real.mul_rpow (by positivity) (by positivity), hpow]; dsimp [F]; ring
  have hsq : ((M : ℝ)^(ε/2)) ^ 2 = (M : ℝ)^ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg M)]
    congr 1
    norm_num
  calc
    _ ≤ 4 * (P.natDegree : ℝ) * (F * (M : ℝ)^(ε/2))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hτ' 2) (by positivity)
    _ = _ := by rw [mul_pow, hsq]; ring

end EqualSumCollision

namespace EqualSumCollision

def pairWeight (P : Polynomial ℤ) {A : Finset ℕ} (x : Fin 2 → ↥A) : ℤ :=
  ∑ i, P.eval ((x i : ℕ) : ℤ)

/-- Fix a pair of positions on each side. Zero complementary discrepancy
costs two ordinary pair energies; each other complementary pair costs U. -/
theorem fixed_quad_le (P : Polynomial ℤ) (A : Finset ℕ) (hP : 3 ≤ P.natDegree)
    (E U : ℝ)
    (hE : (((Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))).filter
      (fun z => pairWeight P z.1 = pairWeight P z.2)).card : ℝ) ≤ E)
    (hU : 0 ≤ U)
    (hbound : ∀ y z : Fin 2 → ↥A, let D := pairWeight P z - pairWeight P y
      D ≠ 0 → ((4 * P.natDegree * D.natAbs.divisors.card ^ 2 : ℕ) : ℝ) ≤ U) :
    let T := Fintype.piFinset fun _ : Fin 4 => A
    let W := fun x : Fin 4 → ℕ => ∑ i, P.eval ((x i : ℕ) : ℤ)
    (((T.product T).filter (fun z => W z.1 = W z.2 ∧
      z.1 0 + z.1 1 = z.2 0 + z.2 1)).card : ℝ) ≤ E^2 + (A.card : ℝ)^4 * U := by
  classical
  intro T W
  let S := (T.product T).filter (fun z => W z.1 = W z.2 ∧ z.1 0 + z.1 1 = z.2 0 + z.2 1)
  let B := (Fin 2 → ↥A) × (Fin 2 → ↥A)
  have mems (z : ↥S) : (∀ i, z.val.1 i ∈ A) ∧ (∀ i, z.val.2 i ∈ A) := by
    obtain ⟨hl, hr⟩ := Finset.mem_product.mp (Finset.mem_filter.mp z.prop).1
    exact ⟨Fintype.mem_piFinset.mp hl, Fintype.mem_piFinset.mp hr⟩
  let head (z : ↥S) : B :=
    (fun i => ⟨z.val.1 i.castSucc.castSucc, (mems z).1 _⟩,
     fun i => ⟨z.val.2 i.castSucc.castSucc, (mems z).2 _⟩)
  let tail (z : ↥S) : B :=
    (fun i => ⟨z.val.1 i.succ.succ, (mems z).1 _⟩,
     fun i => ⟨z.val.2 i.succ.succ, (mems z).2 _⟩)
  have join {x y : ↥S} (h : head x = head y) (t : tail x = tail y) : x = y := by
    have hL (i : Fin 2) := congrArg (fun q : B => (q.1 i : ℕ)) h
    have hR (i : Fin 2) := congrArg (fun q : B => (q.2 i : ℕ)) h
    have tL (i : Fin 2) := congrArg (fun q : B => (q.1 i : ℕ)) t
    have tR (i : Fin 2) := congrArg (fun q : B => (q.2 i : ℕ)) t
    apply Subtype.ext
    apply Prod.ext
    · funext i; fin_cases i
      · exact hL 0
      · exact hL 1
      · exact tL 0
      · exact tL 1
    · funext i; fin_cases i
      · exact hR 0
      · exact hR 1
      · exact tR 0
      · exact tR 1
  let d (b : B) := pairWeight P b.2 - pairWeight P b.1
  have eqn (x : ↥S) : pairWeight P (head x).1 - pairWeight P (head x).2 = d (tail x) := by
    have h := (Finset.mem_filter.mp x.prop).2.1
    simp only [W, Fin.sum_univ_four] at h
    simp only [d, pairWeight, head, tail, Fin.sum_univ_two]
    change (P.eval (x.val.1 0 : ℤ) + P.eval (x.val.1 1 : ℤ)) -
        (P.eval (x.val.2 0 : ℤ) + P.eval (x.val.2 1 : ℤ)) =
        (P.eval (x.val.2 2 : ℤ) + P.eval (x.val.2 3 : ℤ)) -
        (P.eval (x.val.1 2 : ℤ) + P.eval (x.val.1 3 : ℤ))
    omega
  let G := (Finset.univ : Finset B).filter (fun b => pairWeight P b.1 = pairWeight P b.2)
  let Z := (Finset.univ : Finset ↥S).filter (fun x => d (tail x) = 0)
  let N := (Finset.univ : Finset ↥S).filter (fun x => ¬d (tail x) = 0)
  have zeroCount : Z.card ≤ G.card ^ 2 := by
    let f (x : ↥S) := (head x, tail x)
    have maps {x : ↥S} (hx : x ∈ Z) : f x ∈ G.product G := by
      have h := (Finset.mem_filter.mp hx).2
      refine Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      · exact sub_eq_zero.mp ((eqn x).trans h)
      · exact (sub_eq_zero.mp h).symm
    have := Finset.card_le_card_of_injOn f (fun _ hx => maps hx)
      (fun _ _ _ _ h => join (congrArg Prod.fst h) (congrArg Prod.snd h))
    calc
      Z.card ≤ (G.product G).card := this
      _ = _ := (Finset.card_product G G).trans (pow_two G.card).symm
  have nonzeroCount : N.card ≤ ⌊U⌋₊ * A.card ^ 4 := by
    have fiber (t : B) (_ : t ∈ Finset.univ) :
        (N.filter (fun x => tail x = t)).card ≤ ⌊U⌋₊ := by
      let F := N.filter (fun x => tail x = t)
      by_cases hF : F.Nonempty
      · obtain ⟨x,hx⟩ := hF
        have htail := (Finset.mem_filter.mp hx).2
        have hN := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
        have hn : d t ≠ 0 := by rwa [← htail]
        let V := (Finset.univ : Finset B).filter (fun b =>
          (b.1 0 : ℕ) + b.1 1 = (b.2 0 : ℕ) + b.2 1 ∧
          pairWeight P b.1 - pairWeight P b.2 = d t)
        have maps {y : ↥S} (hy : y ∈ F) : head y ∈ V := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩
          · exact (Finset.mem_filter.mp y.prop).2.2
          · exact (eqn y).trans (congrArg d (Finset.mem_filter.mp hy).2)
        have inj : Set.InjOn head (↑F : Set ↥S) := by
          intro y hy z hz heq
          exact join heq ((Finset.mem_filter.mp hy).2.trans (Finset.mem_filter.mp hz).2.symm)
        exact (Finset.card_le_card_of_injOn head (fun _ hy => maps hy) inj).trans
          ((nonzero_fiber P A (d t) hP hn).trans (Nat.le_floor (hbound t.1 t.2 hn)))
      · change F.card ≤ _
        rw [Finset.not_nonempty_iff_eq_empty.mp hF]
        exact Nat.zero_le _
    have hn := Finset.card_le_mul_card_image_of_maps_to
      (s := N) (f := tail) (t := Finset.univ) (fun _ _ => Finset.mem_univ _) ⌊U⌋₊ fiber
    have hcard : (Finset.univ : Finset B).card = A.card^4 := by
      simp [B, pow_succ]; ring
    rwa [hcard] at hn
  have partition : Z.card + N.card = S.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ↥S)) (fun x => d (tail x) = 0))
  have zreal : (Z.card : ℝ) ≤ E^2 := by
    calc
      _ ≤ (G.card : ℝ)^2 := by exact_mod_cast zeroCount
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hE 2
  have nreal : (N.card : ℝ) ≤ (A.card : ℝ)^4 * U := by
    calc
      _ ≤ (⌊U⌋₊ : ℝ) * (A.card : ℝ)^4 := by exact_mod_cast nonzeroCount
      _ = (A.card : ℝ)^4 * (⌊U⌋₊ : ℝ) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le hU) (by positivity)
  change (S.card : ℝ) ≤ _
  rw [← partition, Nat.cast_add]
  exact add_le_add zreal nreal

end EqualSumCollision

namespace EqualSumCollision

private theorem move_pair (i j : Fin 4) (h : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  let τ := Equiv.swap 0 i
  have hτ : τ 0 = i := Equiv.swap_apply_left _ _
  have h0 : (0 : Fin 4) ≠ τ.symm j := by
    intro he
    exact h (hτ.symm.trans ((congrArg τ he).trans (τ.apply_symm_apply j)))
  refine ⟨(Equiv.swap 1 (τ.symm j)).trans τ, ?_, ?_⟩
  · change τ (Equiv.swap 1 (τ.symm j) 0) = i
    rw [Equiv.swap_apply_of_ne_of_ne (by decide : (0 : Fin 4) ≠ 1) h0, hτ]
  · change τ (Equiv.swap 1 (τ.symm j) 1) = j
    rw [Equiv.swap_apply_left, τ.apply_symm_apply]

theorem any_le (A : Finset ℕ) (v : ℕ → ℤ) :
    let T := Fintype.piFinset fun _ : Fin 4 => A
    let w := fun x : Fin 4 → ℕ => ∑ i, v (x i)
    let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
      ∀ ij : Fin 4 × Fin 4, z.1 ij.1 ≠ z.2 ij.2)
    (S.filter (fun z => ∃ ij kl : Fin 4 × Fin 4, ij.1 ≠ ij.2 ∧ kl.1 ≠ kl.2 ∧
      z.1 ij.1 + z.1 ij.2 = z.2 kl.1 + z.2 kl.2)).card ≤
      576 * ((T.product T).filter (fun z => w z.1 = w z.2 ∧
        z.1 0 + z.1 1 = z.2 0 + z.2 1)).card := by
  classical
  intro T w S
  let D := (T.product T).filter (fun z => w z.1 = w z.2 ∧
    z.1 0 + z.1 1 = z.2 0 + z.2 1)
  let perms := (Finset.univ : Finset (Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)))
  let blocks (p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)) :=
    D.image (fun z => (z.1 ∘ p.1.symm, z.2 ∘ p.2.symm))
  apply le_trans (b := (perms.biUnion blocks).card)
  · apply Finset.card_le_card
    intro z hz
    obtain ⟨hzS, ij, kl, hi, hk, hmatch⟩ := Finset.mem_filter.mp hz
    obtain ⟨hzT, hw, _⟩ := Finset.mem_filter.mp hzS
    obtain ⟨hxT, hyT⟩ := Finset.mem_product.mp hzT
    obtain ⟨σ,hσ₀,hσ₁⟩ := move_pair _ _ hi
    obtain ⟨τ,hτ₀,hτ₁⟩ := move_pair _ _ hk
    apply Finset.mem_biUnion.mpr
    refine ⟨(σ,τ), Finset.mem_univ _, Finset.mem_image.mpr ⟨(z.1 ∘ σ, z.2 ∘ τ), ?_, ?_⟩⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_⟩
      · exact Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hxT (σ i)
      · exact Fintype.mem_piFinset.mpr fun i => Fintype.mem_piFinset.mp hyT (τ i)
      · exact (Equiv.sum_comp σ (fun i => v (z.1 i))).trans (hw.trans (Equiv.sum_comp τ (fun i => v (z.2 i))).symm)
      · simpa only [Function.comp_apply, hσ₀, hσ₁, hτ₀, hτ₁] using hmatch
    · apply Prod.ext <;> funext i <;> simp
  · have h := Finset.card_biUnion_le_card_mul perms blocks D.card (fun _ _ => Finset.card_image_le)
    have hcard : perms.card = 576 := by
      norm_num [perms, Fintype.card_prod, Fintype.card_perm, Nat.factorial]
    rw [hcard] at h
    exact h

end EqualSumCollision

theorem Conjectures.Cuts.Taskf45436bd558b4113eea18aa8 : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   (↑{x13 ∈ x12 | ∃ (x14 : Fin (4 : ℕ) × Fin (4 : ℕ)) (x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 ∧ x15.1 ≠ x15.2 ∧ x13.1 x14.1 + x13.1 x14.2 = x13.2 x15.1 + x13.2 x15.2}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ)) := by
  classical
  intro P hP ε hε
  obtain ⟨C, hC, hpair⟩ := Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b P
    (by omega) (ε / 2) (by positivity)
  obtain ⟨K, hK, hgrowth⟩ := EqualSumCollision.divisor_growth P hP ε hε
  refine ⟨576 * (C^2 + K), by positivity, ?_⟩
  intro M hM A hA
  let E := C * (M : ℝ)^(ε / 2) * (A.card : ℝ)^2
  let U := K * (M : ℝ)^ε
  have hf := EqualSumCollision.fixed_quad_le P A hP E U (hpair M hM A hA)
    (by dsimp [U]; positivity) (by
      intro y z D hD
      have memle (p : ↥A) : p.val ≤ M := (Finset.mem_Icc.mp (hA p.property)).2
      have gd := hgrowth M hM (z 0) (z 1) (y 0) (y 1)
        (memle _) (memle _) (memle _) (memle _) D hD (by
         simp only [D, EqualSumCollision.pairWeight, Fin.sum_univ_two])
      exact_mod_cast gd)
  have hcount := EqualSumCollision.any_le A (fun a => P.eval (a : ℤ))
  have hsq : ((M : ℝ)^(ε/2))^2 = (M : ℝ)^ε := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg M)]
    congr 1
    norm_num
  have alg : 576 * (E^2 + (A.card : ℝ)^4 * U) =
      576 * (C^2 + K) * (M : ℝ)^ε * (A.card : ℝ)^4 := by
    dsimp [E, U]
    rw [mul_pow, mul_pow, hsq]
    ring
  apply le_trans _ alg.le
  have hc := Nat.cast_le (α := ℝ) |>.mpr hcount
  push_cast at hc
  exact hc.trans (mul_le_mul_of_nonneg_left hf (by norm_num))
