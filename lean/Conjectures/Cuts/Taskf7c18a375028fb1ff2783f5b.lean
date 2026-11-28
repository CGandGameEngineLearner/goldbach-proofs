import Mathlib

open Finset Polynomial

namespace PairCollision

-- Divisor estimate adapted from FixedModulusZeroClassSquare in this repository
-- and its cited source, Eric Naslund's GradedNear/BurgessReduction.lean.
/-- One prime-power factor of the divisor bound: `a + 1 ≤ M_p (p^ε)^a`, where `M_p = 1` for
`p ≥ K ≥ 2^{1/ε}` and `M_p = max 1 (1/(2^ε - 1))` for `p < K`. -/
private lemma divisor_factor_le {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : (2 : ℝ) ^ (1 / ε) ≤ K)
    {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (a : ℝ) + 1 ≤
      (if p < K then max 1 (1 / ((2 : ℝ) ^ ε - 1)) else 1) * ((p : ℝ) ^ ε) ^ a := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  split_ifs with hpK
  · set b : ℝ := (2 : ℝ) ^ ε with hb
    have hb1 : 1 < b := Real.one_lt_rpow (by norm_num) hε
    have hbp : b ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hp2 hε.le
    set M := max 1 (1 / (b - 1)) with hM
    have hM1 : 1 ≤ M := le_max_left _ _
    have hb' : 0 < b - 1 := by linarith
    have hMb : 1 ≤ M * (b - 1) := by
      have h1 : 1 / (b - 1) ≤ M := le_max_right _ _
      calc (1 : ℝ) = 1 / (b - 1) * (b - 1) := by field_simp
        _ ≤ M * (b - 1) := by gcongr
    have hbern : 1 + (a : ℝ) * (b - 1) ≤ b ^ a := by
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ b - 1 by linarith) a
      simpa using h
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    calc (a : ℝ) + 1 ≤ M * (1 + a * (b - 1)) := by
          nlinarith [mul_nonneg ha (sub_nonneg.mpr hMb)]
      _ ≤ M * b ^ a := by gcongr
      _ ≤ M * ((p : ℝ) ^ ε) ^ a := by gcongr
  · have hpK' : K ≤ p := not_lt.mp hpK
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ ε := by
            apply Real.rpow_le_rpow (by positivity) _ hε.le
            exact hK.trans (by exact_mod_cast hpK')
    calc (a : ℝ) + 1 ≤ 2 ^ a := by
          have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) a
          norm_num at h
          linarith
      _ ≤ ((p : ℝ) ^ ε) ^ a := by gcongr
      _ = 1 * ((p : ℝ) ^ ε) ^ a := (one_mul _).symm

/-- The divisor bound `τ(n) ≪_ε n^ε`. -/
private theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  set K : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  have hK : (2 : ℝ) ^ (1 / ε) ≤ K := Nat.le_ceil _
  set M : ℝ := max 1 (1 / ((2 : ℝ) ^ ε - 1)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  refine ⟨M ^ K, by positivity, fun n hn => ?_⟩
  set g : ℕ → ℝ := fun p => if p < K then M else 1 with hg
  have hτ : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn]
    push_cast
    rfl
  have hn' : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ (n.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Real.rpow_pow_comm (by positivity)]
  have hgK : ∏ p ∈ n.primeFactors, g p ≤ M ^ K := by
    have h1 : ∏ p ∈ n.primeFactors, g p = M ^ (n.primeFactors.filter (· < K)).card := by
      simp only [hg]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    rw [h1]
    apply pow_le_pow_right₀ hM1
    calc (n.primeFactors.filter (· < K)).card ≤ (Finset.range K).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter] at hp
          simpa using hp.2
      _ = K := Finset.card_range K
  calc (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := hτ
    _ ≤ ∏ p ∈ n.primeFactors, (g p * ((p : ℝ) ^ ε) ^ (n.factorization p)) := by
        apply Finset.prod_le_prod₀ (fun p _ => by positivity)
        intro p hp
        exact divisor_factor_le hε hK (Nat.prime_of_mem_primeFactors hp) _
    _ = (∏ p ∈ n.primeFactors, g p) * (n : ℝ) ^ ε := by rw [Finset.prod_mul_distrib, hn']
    _ ≤ M ^ K * (n : ℝ) ^ ε := by gcongr


private lemma shift_ne (P : Polynomial ℤ) (hp : 2 ≤ P.natDegree) {h : ℤ}
    (hh : h ≠ 0) (k : ℤ) : taylor h P - P - C k ≠ 0 := by
  intro he
  have step (x : ℤ) : P.eval (x+h) = P.eval x + k := by
    have z := congrArg (fun Q : Polynomial ℤ => Q.eval x) he
    simpa only [eval_sub,taylor_eval,eval_C,eval_zero,eval_add,sub_sub,sub_eq_zero] using z
  have seq (n : ℕ) : P.eval (h*n) = k*n + P.eval 0 := by
    induction n with
    | zero => simp
    | succ n ih => push_cast; rw [mul_add,mul_one,step,ih]; ring
  have identity : P.comp (C h * X) = C k * X + C (P.eval 0) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ))).mono
    rintro _ ⟨n,rfl⟩
    simpa only [Set.mem_ofPred_eq,eval_comp,eval_mul,eval_C,eval_X,eval_add] using seq n
  have deg := congrArg Polynomial.natDegree identity
  rw [natDegree_comp,natDegree_C_mul hh,natDegree_X,Nat.mul_one] at deg
  have bound : (C k * X + C (P.eval 0)).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_C_mul_le k (X : Polynomial ℤ)).trans_eq natDegree_X
    · simp
  omega

private def delta (P : Polynomial ℤ) {A : Finset ℕ} (x : A × A) :=
  P.eval (x.1.val:ℤ) - P.eval (x.2.val:ℤ)

private def reps (P : Polynomial ℤ) (A : Finset ℕ) (k : ℤ) :
    Finset (A × A) := univ.filter (fun x => delta P x = k)

private lemma zero_fiber (P : Polynomial ℤ) (hp : 2 ≤ P.natDegree) (A : Finset ℕ) :
    (reps P A 0).card ≤ P.natDegree*A.card := by
  classical
  apply (card_le_mul_card_image_of_maps_to (f := Prod.snd) (t := (univ : Finset A))
    (fun _ _ => mem_univ _) P.natDegree ?_).trans_eq (by simp)
  intro y _
  let Q := P - C (P.eval (y.val:ℤ))
  calc
    _ ≤ Q.roots.toFinset.card := by
      apply card_le_card_of_injOn (fun z : A × A => (z.1.val : ℤ))
      · intro z hz
        obtain ⟨hr,hy⟩ := mem_filter.mp hz
        have e := (mem_filter.mp hr).2
        change P.eval _ - P.eval _ = 0 at e
        apply Multiset.mem_toFinset.mpr
        apply (mem_roots_sub_C (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega : 0 < P.natDegree))).mpr
        simpa [← hy] using sub_eq_zero.mp e
      · intro z hz w hw he
        exact Prod.ext (Subtype.ext (Int.ofNat_inj.mp he))
          ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm)
    _ ≤ _ := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Polynomial.card_roots' _
    _ = _ := natDegree_sub_C

private lemma nonzero_fiber (P : Polynomial ℤ) (hp : 2 ≤ P.natDegree) (A : Finset ℕ)
    {k : ℤ} (hk : k ≠ 0) : (reps P A k).card ≤ P.natDegree*(2*k.natAbs.divisors.card) := by
  classical
  let S := k.natAbs.divisors
  let U := S.image (fun n : ℕ => (n:ℤ)) ∪ S.image (fun n : ℕ => -(n:ℤ))
  let offset (z : A × A) : ℤ := (z.1.val:ℤ) - z.2.val
  have maps (z) (hz : z ∈ reps P A k) : offset z ∈ U := by
    have e := (mem_filter.mp hz).2
    have dv : offset z ∣ k := e ▸ Polynomial.sub_dvd_eval_sub _ _ P
    have mem : (offset z).natAbs ∈ S := Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr dv, by simpa using hk⟩
    by_cases h : 0 ≤ offset z
    · exact mem_union_left _ (mem_image.mpr ⟨_,mem,by simp [abs_of_nonneg h]⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨_,mem,by simp [abs_of_neg (lt_of_not_ge h)]⟩)
  have bound (h : ℤ) (_hh : h ∈ U) : ((reps P A k).filter (fun z => offset z = h)).card ≤ P.natDegree := by
    by_cases hz : h = 0
    · subst h
      have empty : ((reps P A k).filter (fun z => offset z = 0)) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hm
        obtain ⟨he,hd⟩ := mem_filter.mp hm
        have eq : (z.1.val:ℤ) = z.2.val := sub_eq_zero.mp hd
        have e := (mem_filter.mp he).2
        simp [delta,eq,hk.symm] at e
      simp [empty]
    let Q := taylor h P - P - C k
    calc
      _ ≤ Q.roots.toFinset.card := by
        apply card_le_card_of_injOn (fun z : A × A => (z.2.val:ℤ))
        · intro z hz'
          obtain ⟨he,ho⟩ := mem_filter.mp hz'
          have e := (mem_filter.mp he).2
          have t : (z.2.val:ℤ)+h = z.1.val := by dsimp [offset] at ho; omega
          apply Multiset.mem_toFinset.mpr
          apply (Polynomial.mem_roots (shift_ne P hp hz k)).mpr
          simpa only [delta,Polynomial.IsRoot.def,eval_sub,taylor_eval,eval_C,t,sub_eq_zero] using e
        · intro z hz' w hw eq
          have e := (mem_filter.mp hz').2
          have f := (mem_filter.mp hw).2
          change (z.2.val:ℤ) = w.2.val at eq
          dsimp [offset] at e f
          exact Prod.ext (Subtype.ext (by omega)) (Subtype.ext (by omega))
      _ ≤ _ := Multiset.toFinset_card_le _
      _ ≤ Q.natDegree := Polynomial.card_roots' _
      _ ≤ _ := by
        dsimp [Q]
        rw [natDegree_sub_C]
        exact (natDegree_sub_le ..).trans (by simp [natDegree_taylor])
  have cardU : U.card ≤ 2*S.card := by
    have u := card_union_le (S.image (fun n : ℕ => (n:ℤ))) (S.image (fun n : ℕ => -(n:ℤ)))
    have a := card_image_le (s := S) (f := fun n : ℕ => (n:ℤ))
    have b := card_image_le (s := S) (f := fun n : ℕ => -(n:ℤ))
    dsimp [U]; omega
  exact (card_le_mul_card_image_of_maps_to maps _ bound).trans (Nat.mul_le_mul_left _ cardU)

private def weight (P : Polynomial ℤ) : ℕ :=
  1 + ∑ i ∈ range (P.natDegree+1), (P.coeff i).natAbs

private lemma magnitude (P : Polynomial ℤ) {M x : ℕ} (hM : 1 ≤ M) (hx : x ≤ M) :
    |P.eval (x:ℤ)| ≤ (weight P : ℤ) * (M:ℤ)^P.natDegree := by
  rw [eval_eq_sum_range]
  calc
    _ ≤ ∑ i ∈ range (P.natDegree+1), |P.coeff i * (x:ℤ)^i| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ i ∈ range (P.natDegree+1), ((P.coeff i).natAbs : ℤ)*(M:ℤ)^P.natDegree := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul,abs_of_nonneg (pow_nonneg (Int.natCast_nonneg _) i),Int.natCast_natAbs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ (Int.natCast_nonneg _) (by exact_mod_cast hx) i).trans
        (pow_le_pow_right₀ (by exact_mod_cast hM) (by have := mem_range.mp hi; omega))
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp [weight]; push_cast; omega

private lemma aggregate (P : Polynomial ℤ) (hp : 2 ≤ P.natDegree) (A : Finset ℕ)
    {L : ℝ} (hL : 0 ≤ L)
    (hnz : ∀ x : A × A, delta P x ≠ 0 → ((reps P A (delta P x)).card : ℝ) ≤ L) :
    ((univ.filter (fun z : (Fin 2 → A) × (Fin 2 → A) =>
       (∑ i, P.eval (((z.1 i).val):ℤ)) = ∑ i, P.eval (((z.2 i).val):ℤ)))).card ≤
        (L+(P.natDegree:ℝ)^2) * (A.card:ℝ)^2 := by
  classical
  let S := univ.filter (fun z : (Fin 2 → A) × (Fin 2 → A) =>
    (∑ i, P.eval ((z.1 i).val:ℤ)) = ∑ i, P.eval ((z.2 i).val:ℤ))
  let key (z : (Fin 2 → A) × (Fin 2 → A)) : A × A := (z.1 0,z.2 0)
  have fiber (x : A × A) : (S.filter (fun z => key z = x)).card ≤ (reps P A (delta P x)).card := by
    apply card_le_card_of_injOn (fun z : (Fin 2 → A) × (Fin 2 → A) => (z.2 1,z.1 1))
    · intro z hz
      obtain ⟨hs,hx⟩ := mem_filter.mp hz
      have e := (mem_filter.mp hs).2
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      rw [← hx]
      dsimp [key,delta]
      simp only [Fin.sum_univ_two] at e
      omega
    · intro z hz w hw eq
      have h := (mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm
      have h0 := congrArg Prod.fst h
      have h1 := congrArg Prod.snd h
      have e0 := congrArg Prod.fst eq
      have e1 := congrArg Prod.snd eq
      apply Prod.ext <;> funext i <;> fin_cases i <;> assumption
  have dec (x : A × A) : ((reps P A (delta P x)).card:ℝ) ≤ L +
      (if delta P x = 0 then (P.natDegree:ℝ)*A.card else 0) := by
    by_cases h : delta P x = 0
    · simp only [h, ↓reduceIte]
      have e : ((reps P A 0).card:ℝ) ≤ (P.natDegree:ℝ)*A.card := by exact_mod_cast zero_fiber P hp A
      linarith
    · simpa [h] using hnz x h
  have decomp := card_eq_sum_card_fiberwise (f := key) (s := S) (t := (univ : Finset (A × A))) (by simp)
  change (S.card:ℝ) ≤ _
  rw [decomp,Nat.cast_sum]
  calc
    _ ≤ ∑ x : A × A, (L+ (if delta P x = 0 then (P.natDegree:ℝ)*A.card else 0)) := by
      apply sum_le_sum
      intro x _
      exact (show (_:ℝ) ≤ _ by exact_mod_cast fiber x).trans (dec x)
    _ = (A.card:ℝ)^2*L + ((reps P A 0).card:ℝ)*((P.natDegree:ℝ)*A.card) := by
      rw [sum_add_distrib,← sum_filter]
      simp [reps,pow_two,nsmul_eq_mul]
    _ ≤ _ := by
      have hb : ((reps P A 0).card:ℝ) ≤ (P.natDegree:ℝ)*A.card := by exact_mod_cast zero_fiber P hp A
      calc
        _ ≤ (A.card:ℝ)^2*L + ((P.natDegree:ℝ)*A.card)*((P.natDegree:ℝ)*A.card) := by gcongr
        _ = _ := by ring

end PairCollision

open PairCollision in
theorem Conjectures.Cuts.Taskf7c18a375028fb1ff2783f5b :
∀ (x1 : Polynomial ℤ),   (2 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : (Fin (2 : ℕ) → ↥x8) → ℤ := fun (x10 : Fin (2 : ℕ) → ↥x8) => ∑ x11 : Fin (2 : ℕ), Polynomial.eval (↑↑(x10 x11)) x1;                   have x11 : Finset ((Fin (2 : ℕ) → ↥x8) × (Fin (2 : ℕ) → ↥x8)) := Finset.univ;                   ↑{x12 ∈ x11 | x10 x12.1 = x10 x12.2}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ (2 : ℕ) := by
  classical
  intro P hp ε hε
  let D : ℝ := P.natDegree
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (by omega : 0 < P.natDegree)
  let r := ε / D
  have hr : 0 < r := div_pos hε hD
  obtain ⟨B,hB,hdiv⟩ := card_divisors_le_rpow hr
  let K : ℝ := 2*(weight P : ℝ)
  have hK : 0 < K := by dsimp [K,weight]; positivity
  let V : ℝ := D*2*B*K^r
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨V+D^2,by positivity,?_⟩
  intro M hM A hA
  dsimp only
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hPow : (1:ℝ) ≤ (M:ℝ)^ε := Real.one_le_rpow hM1 hε.le
  have bound (x : A × A) (hne : delta P x ≠ 0) : ((reps P A (delta P x)).card:ℝ) ≤ V*(M:ℝ)^ε := by
    let k := delta P x
    have hmag : (k.natAbs:ℝ) ≤ K*(M:ℝ)^P.natDegree := by
      have ht (z : A) := magnitude P (show 1 ≤ M by omega) (mem_Icc.mp (hA z.property)).2
      have ab := (abs_sub_le (P.eval (x.1.val:ℤ)) 0 (P.eval (x.2.val:ℤ)))
      simp only [sub_zero,zero_sub,abs_neg] at ab
      have hi : (k.natAbs:ℤ) ≤ (2*(weight P:ℤ))*(M:ℤ)^P.natDegree := by
        rw [Int.natCast_natAbs]
        change |P.eval _ - P.eval _| ≤ _
        linarith only [ab,ht x.1,ht x.2]
      dsimp [K]; exact_mod_cast hi
    have hpow : ((M:ℝ)^P.natDegree)^r = (M:ℝ)^ε := by
      rw [← Real.rpow_natCast_mul (by positivity)]
      congr 1
      change D*(ε/D) = ε
      field_simp
    have hd := hdiv k.natAbs (by simpa [k] using hne)
    have hb : ((reps P A k).card:ℝ) ≤ (P.natDegree:ℝ)*(2*(k.natAbs.divisors.card:ℝ)) := by
      exact_mod_cast nonzero_fiber P hp A hne
    calc
      _ ≤ _ := hb
      _ ≤ (P.natDegree:ℝ)*(2*(B*((K*(M:ℝ)^P.natDegree)^r))) := by
        gcongr
        exact hd.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hmag hr.le) hB.le)
      _ = _ := by rw [Real.mul_rpow hK.le (by positivity),hpow]; dsimp [V,D]; ring
  apply (aggregate P hp A (L := V*(M:ℝ)^ε) (by positivity) bound).trans
  change (V*(M:ℝ)^ε+D^2)*_ ≤ _
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  nlinarith only [mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hPow)]
