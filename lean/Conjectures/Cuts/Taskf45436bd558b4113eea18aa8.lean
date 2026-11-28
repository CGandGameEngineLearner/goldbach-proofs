import Mathlib

namespace GoldbachChild1Base

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

open Finset Filter Topology
open scoped BigOperators

private theorem divisorPower (K : ℕ) (hK : 0<K) :
    ∃ C : ℝ,1≤C ∧ ∀ n : ℕ, 0<n → (n.divisors.card:ℝ)^K ≤ C*n := by
  have hl := (isLittleO_pow_const_const_pow_of_one_lt (R:=ℝ) K (by norm_num : (1:ℝ)<2)).bound (by norm_num : (0:ℝ)<1)
  obtain ⟨E,hE⟩ := eventually_atTop.mp hl
  let c : ℝ := (2:ℝ)^K*((E:ℝ)+1)^K
  have hc : 1≤c := by
    dsimp [c]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E]))
  have small (e : ℕ) : ((e:ℝ)+1)^K ≤ c*(2:ℝ)^e := by
    by_cases he : e<E
    · have hle : ((e:ℝ)+1)^K ≤ ((E:ℝ)+1)^K := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show e+1≤E+1 by omega)) _
      have h2 : (1:ℝ)≤2^K := one_le_pow₀ (by norm_num)
      have h3 : (1:ℝ)≤2^e := one_le_pow₀ (by norm_num)
      exact hle.trans ((le_mul_of_one_le_left (by positivity) h2).trans (le_mul_of_one_le_right (by positivity) h3))
    · have hs := hE (e+1) (by omega)
      simp only [Function.comp_apply,Real.norm_eq_abs,Nat.cast_add,Nat.cast_one,abs_of_nonneg (pow_nonneg (by positivity : 0≤(e:ℝ)+1) K),abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) (e+1)),one_mul,pow_succ] at hs
      rw [abs_of_nonneg (by positivity)] at hs
      have hK1 : (2:ℝ)≤2^K := by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hK)
      have hE1 : (1:ℝ)≤((E:ℝ)+1)^K := one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) E])
      have hc2 : (2:ℝ)≤c := hK1.trans (le_mul_of_one_le_right (by positivity) hE1)
      exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_right hc2 (by positivity : 0≤(2:ℝ)^e)])
  let P : ℕ := 2^K
  refine ⟨c^P,one_le_pow₀ hc,?_⟩
  intro n hn
  have hprod : (∏ p ∈ n.primeFactors,(p:ℝ)^(n.factorization p))=n := by
    exact_mod_cast (by simpa [Finsupp.prod,Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hn.ne' :
      (∏ p ∈ n.primeFactors,p^(n.factorization p))=n)
  have hlocal (p : ℕ) (hp : p∈n.primeFactors) :
      ((n.factorization p:ℝ)+1)^K ≤ (if p<P then c else 1)*(p:ℝ)^(n.factorization p) := by
    have h2 : (2:ℝ)≤p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    split_ifs with h
    · exact (small _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) h2 _) (by linarith))
    · rw [one_mul]
      have he : ∀ e : ℕ,(e:ℝ)+1 ≤ (2:ℝ)^e := by
        intro e; induction e with
        | zero => norm_num
        | succ e ih => push_cast; rw [pow_succ]; linarith [show (0:ℝ)≤e by positivity]
      calc
        _ ≤ ((2:ℝ)^n.factorization p)^K := pow_le_pow_left₀ (by positivity) (he _) _
        _ = ((2:ℝ)^K)^n.factorization p := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
        _ ≤ _ := pow_le_pow_left₀ (by positivity) (by exact_mod_cast (show 2^K≤p by omega)) _
  have hcount : ((n.primeFactors.filter (·<P)).card)≤P := by
    have : n.primeFactors.filter (·<P)⊆range P := fun _ h => mem_range.mpr (mem_filter.mp h).2
    simpa using card_le_card this
  have hfactor : (∏ p ∈ n.primeFactors, if p<P then c else 1)≤c^P := by
    rw [←prod_filter,prod_const]; exact pow_le_pow_right₀ hc hcount
  rw [Nat.card_divisors hn.ne',Nat.cast_prod,←prod_pow]
  simp only [Nat.cast_add,Nat.cast_one]
  calc
    _ ≤ ∏ p ∈ n.primeFactors, (if p<P then c else 1)*(p:ℝ)^(n.factorization p) :=
      prod_le_prod₀ (fun _ _ => by positivity) hlocal
    _ ≤ _ := by rw [prod_mul_distrib,hprod]; exact mul_le_mul_of_nonneg_right hfactor (by positivity)

theorem divisor_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → (m.divisors.card : ℝ) ≤ C * (m : ℝ) ^ δ := by
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / δ)
  have hKpos : 0 < K := by
    by_contra! h0
    have hK0 : K = 0 := by omega
    rw [hK0, Nat.cast_zero] at hK
    have : 0 < 1 / δ := one_div_pos.mpr hδ
    linarith
  have hK_le : (1 : ℝ) / (K : ℝ) ≤ δ := by
    have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    have h1 : 1 < δ * (K : ℝ) := (div_lt_iff₀ hδ).mp hK
    exact (div_le_iff₀ hKR).mpr (by linarith)
  obtain ⟨C, hC1, hpow⟩ := divisorPower K hKpos
  let p : ℝ := 1 / (K : ℝ)
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hC0 : 0 ≤ C := hCpos.le
  refine ⟨C ^ p, Real.rpow_pos_of_pos hCpos p, fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hKpos.ne'
  have h1 := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg m.divisors.card) K)
    (hpow m hm) hp0
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m.divisors.card),
    Real.mul_rpow hC0 (Nat.cast_nonneg m)] at h1
  have hKp : (K : ℝ) * p = 1 := by dsimp [p]; field_simp [hKR]
  rw [hKp, Real.rpow_one] at h1
  have hm_exp : (m : ℝ) ^ p ≤ (m : ℝ) ^ δ :=
    Real.rpow_le_rpow_of_exponent_le hm1 hK_le
  exact h1.trans (mul_le_mul_of_nonneg_left hm_exp (Real.rpow_nonneg hC0 p))

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

theorem pair_collision_two_bound : (∀ (x1 : Polynomial ℤ),   (2 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : (Fin (2 : ℕ) → ↥x8) → ℤ := fun (x10 : Fin (2 : ℕ) → ↥x8) => ∑ x11 : Fin (2 : ℕ), Polynomial.eval (↑↑(x10 x11)) x1;                   have x11 : Finset ((Fin (2 : ℕ) → ↥x8) × (Fin (2 : ℕ) → ↥x8)) := Finset.univ;                   ↑{x12 ∈ x11 | x10 x12.1 = x10 x12.2}.card ≤ x5 * ↑x6 ^ x3 * ↑x8.card ^ (2 : ℕ)) := by
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

end GoldbachChild1Base

namespace GoldbachChild1PairSum

open Finset Polynomial GoldbachChild1Base GoldbachChild1Base.GoldbachPolynomialDifference
  GoldbachChild1Base.GoldbachPolynomialMagnitude GoldbachChild1Base.GoldbachPolynomialDivisors
  GoldbachChild1Base.GoldbachPolyCollision
open scoped BigOperators

/-- Second-order difference polynomial for `P(x) + P(x - h₁ - h₂) - P(x - h₁) - P(x - h₂) - ℓ`. -/
noncomputable def secondDiffPoly (P : Polynomial ℤ) (h₁ h₂ ℓ : ℤ) : Polynomial ℤ :=
  P + P.taylor (-h₁ - h₂) - P.taylor (-h₁) - P.taylor (-h₂) - Polynomial.C ℓ

theorem secondDiffPoly_eval (P : Polynomial ℤ) (h₁ h₂ ℓ x : ℤ) :
    (secondDiffPoly P h₁ h₂ ℓ).eval x =
      P.eval x + P.eval (x - h₁ - h₂) - P.eval (x - h₁) - P.eval (x - h₂) - ℓ := by
  simp only [secondDiffPoly, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.taylor_apply]
  have e1 : (-h₁ - h₂) + x = x - h₁ - h₂ := by ring
  have e2 : (-h₁) + x = x - h₁ := by ring
  have e3 : (-h₂) + x = x - h₂ := by ring
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    e1, e2, e3]

theorem secondDiffPoly_natDegree_le (P : Polynomial ℤ) (h₁ h₂ ℓ : ℤ) :
    (secondDiffPoly P h₁ h₂ ℓ).natDegree ≤ P.natDegree := by
  unfold secondDiffPoly
  have h1 : (P + P.taylor (-h₁ - h₂)).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_add_le _ _).trans (max_le le_rfl (by simp))
  have h2 : (P + P.taylor (-h₁ - h₂) - P.taylor (-h₁)).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le h1 (by simp))
  have h3 : (P + P.taylor (-h₁ - h₂) - P.taylor (-h₁) - P.taylor (-h₂)).natDegree ≤ P.natDegree :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le h2 (by simp))
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le h3 (by simp))

theorem secondDiffPoly_ne_zero (P : Polynomial ℤ) (h₁ h₂ ℓ : ℤ)
    (hdeg : 3 ≤ P.natDegree) (hh₁ : h₁ ≠ 0) (hh₂ : h₂ ≠ 0) :
    secondDiffPoly P h₁ h₂ ℓ ≠ 0 := by
  let k : ℕ := P.natDegree - 2
  let H : Polynomial ℤ := P.hasseDeriv k
  have hk0 : k ≠ 0 := by dsimp [k]; omega
  have h2k : 2 + k = P.natDegree := by dsimp [k]; omega
  have hHdeg : H.natDegree ≤ 2 := by
    apply (Polynomial.natDegree_hasseDeriv_le P k).trans
    dsimp [k]
    omega
  have hH_eval (z : ℤ) : H.eval z = H.coeff 2 * z ^ 2 + H.coeff 1 * z + H.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range]
    have hrange : H.natDegree + 1 ≤ 3 := by omega
    have hsum : ∑ i ∈ range (H.natDegree + 1), H.coeff i * z ^ i =
        ∑ i ∈ range 3, H.coeff i * z ^ i := by
      symm
      apply Finset.sum_subset (Finset.range_mono hrange)
      intro i hi hnot
      have hgt : H.natDegree < i := by
        rw [Finset.mem_range] at hi hnot
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, zero_mul]
    rw [hsum, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    ring
  have hP0 : P ≠ 0 := by
    intro he
    simp [he] at hdeg
  have hH2 : H.coeff 2 ≠ 0 := by
    change (P.hasseDeriv k).coeff 2 ≠ 0
    rw [Polynomial.hasseDeriv_coeff, h2k, Polynomial.coeff_natDegree]
    apply mul_ne_zero
    · exact_mod_cast (Nat.choose_pos (show k ≤ P.natDegree by dsimp [k]; omega)).ne'
    · exact Polynomial.leadingCoeff_ne_zero.mpr hP0
  have hH0 : H.coeff 0 = P.coeff k := by
    change (P.hasseDeriv k).coeff 0 = P.coeff k
    rw [Polynomial.hasseDeriv_coeff]
    simp
  have hC : ((Polynomial.C ℓ : Polynomial ℤ).coeff k) = 0 :=
    Polynomial.coeff_C_of_ne_zero hk0
  have hcoeff : (secondDiffPoly P h₁ h₂ ℓ).coeff k = 2 * H.coeff 2 * h₁ * h₂ := by
    simp only [secondDiffPoly, Polynomial.coeff_sub, Polynomial.coeff_add,
      Polynomial.taylor_coeff, hC]
    change P.coeff k + H.eval (-h₁ - h₂) - H.eval (-h₁) - H.eval (-h₂) - 0 =
      2 * H.coeff 2 * h₁ * h₂
    rw [hH_eval (-h₁ - h₂), hH_eval (-h₁), hH_eval (-h₂), hH0]
    ring
  intro he
  rw [he, Polynomial.coeff_zero] at hcoeff
  have hnz : 2 * H.coeff 2 * h₁ * h₂ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hH2) hh₁) hh₂
  exact hnz hcoeff.symm

private def signedDivs (u : ℤ) : Finset ℤ :=
  (u.natAbs.divisors.image fun d : ℕ => (d : ℤ)) ∪
    (u.natAbs.divisors.image fun d : ℕ => -(d : ℤ))

private theorem signedDivs_card (u : ℤ) :
    (signedDivs u).card ≤ 2 * u.natAbs.divisors.card := by
  unfold signedDivs
  rw [two_mul]
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

private theorem signedDivs_mem {u h : ℤ} (hu : u ≠ 0) (hd : h ∣ u) :
    h ∈ signedDivs u := by
  have habs : u.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hu
  have hh : h.natAbs ∈ u.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hd, habs⟩
  unfold signedDivs
  by_cases hn : 0 ≤ h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨h.natAbs, hh, Int.natAbs_of_nonneg hn⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨h.natAbs, hh,
      (Int.eq_neg_natAbs_of_nonpos (le_of_not_ge hn)).symm⟩)

private theorem signedDivs_ne_zero {u h : ℤ} (hh : h ∈ signedDivs u) : h ≠ 0 := by
  have hpos {n : ℕ} (hn : n ∈ u.natAbs.divisors) : 0 < n := Nat.pos_of_mem_divisors hn
  unfold signedDivs at hh
  rcases Finset.mem_union.mp hh with hh | hh
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hh
    exact Int.ofNat_ne_zero.mpr (hpos hn).ne'
  · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hh
    exact neg_ne_zero.mpr (Int.ofNat_ne_zero.mpr (hpos hn).ne')

/-- Second-order difference `Δ(j, m, a, b) = (m+a+b)^j + m^j - (m+a)^j - (m+b)^j`. -/
def binomDiff (j : ℕ) (m a b : ℤ) : ℤ :=
  (m + a + b) ^ j + m ^ j - (m + a) ^ j - (m + b) ^ j

theorem binomDiff_zero (m a b : ℤ) : binomDiff 0 m a b = 0 := by
  simp [binomDiff]

theorem binomDiff_one (m a b : ℤ) : binomDiff 1 m a b = 0 := by
  simp [binomDiff]
  ring

theorem binomDiff_two (m a b : ℤ) : binomDiff 2 m a b = 2 * a * b := by
  simp [binomDiff]
  ring

theorem binomDiff_succ_sub_mul (j : ℕ) (m a b : ℤ) :
    binomDiff (j + 1) m a b - m * binomDiff j m a b =
      a * ((m + a + b) ^ j - (m + a) ^ j) + b * ((m + a + b) ^ j - (m + b) ^ j) := by
  simp only [binomDiff, pow_succ']
  ring

theorem binomDiff_nonneg (j : ℕ) {m a b : ℤ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ binomDiff j m a b := by
  induction j with
  | zero => simp [binomDiff_zero]
  | succ j ih =>
    have h1 : (m + a) ^ j ≤ (m + a + b) ^ j :=
      pow_le_pow_left₀ (add_nonneg hm ha) (by linarith) j
    have h2 : (m + b) ^ j ≤ (m + a + b) ^ j :=
      pow_le_pow_left₀ (add_nonneg hm hb) (by linarith) j
    have hrhs : 0 ≤ a * ((m + a + b) ^ j - (m + a) ^ j) + b * ((m + a + b) ^ j - (m + b) ^ j) :=
      exact add_nonneg (mul_nonneg ha (sub_nonneg.mpr h1)) (mul_nonneg hb (sub_nonneg.mpr h2))
    have hstep := binomDiff_succ_sub_mul j m a b
    nlinarith only [ih, hm, hrhs, hstep]

theorem mul_binomDiff_le_succ (j : ℕ) {m a b : ℤ} (hm : 0 ≤ m) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    m * binomDiff j m a b ≤ binomDiff (j + 1) m a b := by
  have h1 : (m + a) ^ j ≤ (m + a + b) ^ j :=
    pow_le_pow_left₀ (add_nonneg hm ha) (by linarith) j
  have h2 : (m + b) ^ j ≤ (m + a + b) ^ j :=
    pow_le_pow_left₀ (add_nonneg hm hb) (by linarith) j
  have hrhs : 0 ≤ a * ((m + a + b) ^ j - (m + a) ^ j) + b * ((m + a + b) ^ j - (m + b) ^ j) :=
    exact add_nonneg (mul_nonneg ha (sub_nonneg.mpr h1)) (mul_nonneg hb (sub_nonneg.mpr h2))
  linarith only [binomDiff_succ_sub_mul j m a b, hrhs]

theorem mul_binomDiff_le_of_lt {j d : ℕ} (hjd : j < d) {m a b : ℤ}
    (hm : 1 ≤ m) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    m * binomDiff j m a b ≤ binomDiff d m a b := by
  have hm0 : 0 ≤ m := by omega
  induction d with
  | zero => omega
  | succ d ih =>
    rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hjd) with rfl | hlt
    · exact mul_binomDiff_le_succ j hm0 ha hb
    · have h1 := ih hlt
      have h2 := mul_binomDiff_le_succ d hm0 ha hb
      have hnn := binomDiff_nonneg d hm0 ha hb
      nlinarith only [h1, h2, hm, hnn]

theorem binomDiff_pos {j : ℕ} (hj : 2 ≤ j) {m a b : ℤ}
    (hm : 1 ≤ m) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    0 < binomDiff j m a b := by
  have h2 : 0 < binomDiff 2 m a b := by
    rw [binomDiff_two]
    positivity
  rcases Nat.eq_or_lt_of_le hj with rfl | hlt
  · exact h2
  · have hle := mul_binomDiff_le_of_lt hlt hm (by omega) (by omega)
    nlinarith only [h2, hle, hm]

theorem eval_secondDiff_eq_sum (P : Polynomial ℤ) (m a b : ℤ) :
    P.eval (m + a + b) + P.eval m - P.eval (m + a) - P.eval (m + b) =
      ∑ j ∈ Ico 2 (P.natDegree + 1), P.coeff j * binomDiff j m a b := by
  simp only [Polynomial.eval_eq_sum_range, binomDiff]
  have hsplit : ∑ j ∈ range (P.natDegree + 1), P.coeff j *
      ((m + a + b) ^ j + m ^ j - (m + a) ^ j - (m + b) ^ j) =
      (∑ j ∈ range (P.natDegree + 1), P.coeff j * (m + a + b) ^ j) +
      (∑ j ∈ range (P.natDegree + 1), P.coeff j * m ^ j) -
      (∑ j ∈ range (P.natDegree + 1), P.coeff j * (m + a) ^ j) -
      (∑ j ∈ range (P.natDegree + 1), P.coeff j * (m + b) ^ j) := by
    simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← hsplit]
  by_cases hd : P.natDegree < 2
  · have hico : Ico 2 (P.natDegree + 1) = ∅ := Ico_eq_empty_of_le (by omega)
    rw [hico, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_range] at hj
    have hj2 : j = 0 ∨ j = 1 := by omega
    rcases hj2 with rfl | rfl <;> simp <;> ring
  · have h2le : 2 ≤ P.natDegree + 1 := by omega
    have hunion : range (P.natDegree + 1) = range 2 ∪ Ico 2 (P.natDegree + 1) := by
      ext j
      simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
      omega
    have hdisj : Disjoint (range 2) (Ico 2 (P.natDegree + 1)) := by
      rw [Finset.disjoint_left]
      intro j hj1 hj2
      simp only [Finset.mem_range, Finset.mem_Ico] at hj1 hj2
      omega
    rw [hunion, Finset.sum_union hdisj]
    have hlow : ∑ j ∈ range 2, P.coeff j *
        ((m + a + b) ^ j + m ^ j - (m + a) ^ j - (m + b) ^ j) = 0 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp
      ring
    rw [hlow, zero_add]

def zeroFiberThreshold (P : Polynomial ℤ) : ℤ :=
  1 + ∑ j ∈ Ico 2 P.natDegree, |P.coeff j|

theorem zeroFiberThreshold_pos (P : Polynomial ℤ) : 1 ≤ zeroFiberThreshold P := by
  unfold zeroFiberThreshold
  have hnn : 0 ≤ ∑ j ∈ Ico 2 P.natDegree, |P.coeff j| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith only [hnn]

theorem eval_secondDiff_ne_zero_of_large (P : Polynomial ℤ) (hdeg : 3 ≤ P.natDegree)
    {m a b : ℤ} (hm : zeroFiberThreshold P ≤ m) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    P.eval (m + a + b) + P.eval m - P.eval (m + a) - P.eval (m + b) ≠ 0 := by
  rw [eval_secondDiff_eq_sum]
  have h2le : 2 ≤ P.natDegree := by omega
  have hico_ins : Ico 2 (P.natDegree + 1) = insert P.natDegree (Ico 2 P.natDegree) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_Ico]
    omega
  have hnotmem : P.natDegree ∉ Ico 2 P.natDegree := by
    simp [Finset.mem_Ico]
  rw [hico_ins, Finset.sum_insert hnotmem, add_comm]
  have hm1 : 1 ≤ m := (zeroFiberThreshold_pos P).trans hm
  have hpos : 0 < binomDiff P.natDegree m a b := binomDiff_pos hdeg hm1 ha hb
  have hP0 : P ≠ 0 := by
    intro h
    simp [h] at hdeg
  have hlead : 1 ≤ |P.coeff P.natDegree| := by
    have hnz : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
    omega
  have hlow_abs : |∑ j ∈ Ico 2 P.natDegree, P.coeff j * binomDiff j m a b| ≤
      ∑ j ∈ Ico 2 P.natDegree, |P.coeff j| * binomDiff j m a b := by
    calc
      _ ≤ ∑ j ∈ Ico 2 P.natDegree, |P.coeff j * binomDiff j m a b| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j ∈ Ico 2 P.natDegree, |P.coeff j| * binomDiff j m a b := by
          apply Finset.sum_congr rfl
          intro j _
          rw [abs_mul, abs_of_nonneg (binomDiff_nonneg j (by omega) (by omega) (by omega))]
  have hmul_low : m * (∑ j ∈ Ico 2 P.natDegree, |P.coeff j| * binomDiff j m a b) ≤
      (∑ j ∈ Ico 2 P.natDegree, |P.coeff j|) * binomDiff P.natDegree m a b := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hjlt : j < P.natDegree := (Finset.mem_Ico.mp hj).2
    have hstep := mul_binomDiff_le_of_lt hjlt hm1 (by omega) (by omega)
    have hca : 0 ≤ |P.coeff j| := abs_nonneg _
    nlinarith only [hstep, hca]
  have hstrict : (∑ j ∈ Ico 2 P.natDegree, |P.coeff j|) * binomDiff P.natDegree m a b <
      m * (|P.coeff P.natDegree| * binomDiff P.natDegree m a b) := by
    have h1 : (∑ j ∈ Ico 2 P.natDegree, |P.coeff j|) < m := by
      unfold zeroFiberThreshold at hm
      omega
    have h2 : (∑ j ∈ Ico 2 P.natDegree, |P.coeff j|) * binomDiff P.natDegree m a b <
        m * binomDiff P.natDegree m a b :=
      mul_lt_mul_of_pos_right h1 hpos
    have h3 : m * binomDiff P.natDegree m a b ≤
        m * (|P.coeff P.natDegree| * binomDiff P.natDegree m a b) := by
      nlinarith only [hm1, hlead, hpos]
    exact lt_of_lt_of_le h2 h3
  have hlt : |∑ j ∈ Ico 2 P.natDegree, P.coeff j * binomDiff j m a b| <
      |P.coeff P.natDegree * binomDiff P.natDegree m a b| := by
    rw [abs_mul, abs_of_pos hpos]
    have hcomb : m * |∑ j ∈ Ico 2 P.natDegree, P.coeff j * binomDiff j m a b| <
        m * (|P.coeff P.natDegree| * binomDiff P.natDegree m a b) :=
      lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hlow_abs (by omega)).trans hmul_low) hstrict
    exact (mul_lt_mul_left (by omega : 0 < m)).mp hcomb
  intro heq
  have hneg : ∑ j ∈ Ico 2 P.natDegree, P.coeff j * binomDiff j m a b =
      -(P.coeff P.natDegree * binomDiff P.natDegree m a b) := by
    linarith only [heq]
  rw [hneg, abs_neg] at hlt
  exact lt_irrefl _ hlt

private theorem not_large_of_min_first {P : Polynomial ℤ} (hdeg : 3 ≤ P.natDegree)
    {x₁ x₂ y₁ y₂ : ℤ} (hsum : x₁ + x₂ = y₁ + y₂)
    (hdisj : x₁ ≠ y₁ ∧ x₁ ≠ y₂ ∧ x₂ ≠ y₁ ∧ x₂ ≠ y₂)
    (heval : P.eval x₁ + P.eval x₂ = P.eval y₁ + P.eval y₂)
    (hmin₁ : x₁ ≤ y₁) (hmin₂ : x₁ ≤ y₂) :
    x₁ < zeroFiberThreshold P := by
  by_contra! hge
  let a : ℤ := y₁ - x₁
  let b : ℤ := y₂ - x₁
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hb : 1 ≤ b := by dsimp [b]; omega
  have hx₂ : x₂ = x₁ + a + b := by dsimp [a, b]; omega
  have hy₁ : y₁ = x₁ + a := by dsimp [a]; omega
  have hy₂ : y₂ = x₁ + b := by dsimp [b]; omega
  have hne := eval_secondDiff_ne_zero_of_large P hdeg hge ha hb
  rw [← hx₂, ← hy₁, ← hy₂] at hne
  exact hne (by linarith only [heval])

theorem matchedPair_min_lt_threshold {P : Polynomial ℤ} (hdeg : 3 ≤ P.natDegree)
    {x₁ x₂ y₁ y₂ : ℤ} (hsum : x₁ + x₂ = y₁ + y₂)
    (hdisj : x₁ ≠ y₁ ∧ x₁ ≠ y₂ ∧ x₂ ≠ y₁ ∧ x₂ ≠ y₂)
    (heval : P.eval x₁ + P.eval x₂ = P.eval y₁ + P.eval y₂) :
    x₁ < zeroFiberThreshold P ∨ x₂ < zeroFiberThreshold P ∨
      y₁ < zeroFiberThreshold P ∨ y₂ < zeroFiberThreshold P := by
  rcases le_total x₁ x₂ with h12 | h21
  · rcases le_total y₁ y₂ with hy12 | hy21
    · rcases le_total x₁ y₁ with hxy | hyx
      · exact Or.inl (not_large_of_min_first hdeg hsum hdisj heval hxy (hxy.trans hy12))
      · exact Or.inr (Or.inr (Or.inl (not_large_of_min_first hdeg hsum.symm
          ⟨hdisj.1.symm, hdisj.2.2.1.symm, hdisj.2.1.symm, hdisj.2.2.2.symm⟩
          heval.symm hyx (hyx.trans h12))))
    · rcases le_total x₁ y₂ with hxy | hyx
      · exact Or.inl (not_large_of_min_first hdeg (by omega)
          ⟨hdisj.2.1, hdisj.1, hdisj.2.2.2, hdisj.2.2.1⟩
          (by linarith only [heval]) hxy (hxy.trans hy21))
      · exact Or.inr (Or.inr (Or.inr (not_large_of_min_first hdeg (by omega)
          ⟨hdisj.2.1.symm, hdisj.2.2.2.symm, hdisj.1.symm, hdisj.2.2.1.symm⟩
          (by linarith only [heval]) hyx (hyx.trans h12))))
  · rcases le_total y₁ y₂ with hy12 | hy21
    · rcases le_total x₂ y₁ with hxy | hyx
      · exact Or.inr (Or.inl (not_large_of_min_first hdeg (by omega)
          ⟨hdisj.2.2.1, hdisj.2.2.2, hdisj.1, hdisj.2.1⟩
          (by linarith only [heval]) hxy (hxy.trans hy12)))
      · exact Or.inr (Or.inr (Or.inl (not_large_of_min_first hdeg (by omega)
          ⟨hdisj.1.symm, hdisj.2.2.1.symm, hdisj.2.1.symm, hdisj.2.2.2.symm⟩
          (by linarith only [heval]) hyx (hyx.trans h21))))
    · rcases le_total x₂ y₂ with hxy | hyx
      · exact Or.inr (Or.inl (not_large_of_min_first hdeg (by omega)
          ⟨hdisj.2.2.2, hdisj.2.2.1, hdisj.2.1, hdisj.1⟩
          (by linarith only [heval]) hxy (hxy.trans hy21)))
      · exact Or.inr (Or.inr (Or.inr (not_large_of_min_first hdeg (by omega)
          ⟨hdisj.2.1.symm, hdisj.2.2.2.symm, hdisj.1.symm, hdisj.2.2.1.symm⟩
          (by linarith only [heval]) hyx (hyx.trans h21))))

def matchedLocalPairs (P : Polynomial ℤ) (B : Finset ℤ) (ℓ : ℤ) :
    Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  ((B ×ˢ B) ×ˢ (B ×ˢ B)).filter fun q =>
    q.1.1 + q.1.2 = q.2.1 + q.2.2 ∧
      q.1.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2 ∧ q.1.2 ≠ q.2.1 ∧ q.1.2 ≠ q.2.2 ∧
      P.eval q.1.1 + P.eval q.1.2 - P.eval q.2.1 - P.eval q.2.2 = ℓ

theorem matchedLocalPairs_nonzero_card_le (P : Polynomial ℤ) (B : Finset ℤ) (ℓ : ℤ)
    (hdeg : 3 ≤ P.natDegree) (hℓ : ℓ ≠ 0) :
    (matchedLocalPairs P B ℓ).card ≤ 4 * P.natDegree * (ℓ.natAbs.divisors.card) ^ 2 := by
  classical
  let D := signedDivs ℓ
  let R (p : ℤ × ℤ) := (secondDiffPoly P p.1 p.2 ℓ).roots.toFinset
  let f (q : (ℤ × ℤ) × (ℤ × ℤ)) : Σ _ : ℤ × ℤ, ℤ :=
    ⟨(q.1.1 - q.2.1, q.1.1 - q.2.2), q.1.1⟩
  have hmaps (q : (ℤ × ℤ) × (ℤ × ℤ)) (hq : q ∈ matchedLocalPairs P B ℓ) :
      f q ∈ (D ×ˢ D).sigma R := by
    rcases q with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
    obtain ⟨_, hsum, h11, h12, h21, h22, heval⟩ := Finset.mem_filter.mp hq
    let h₁ := x₁ - y₁
    let h₂ := x₁ - y₂
    have hh₁ : h₁ ≠ 0 := sub_ne_zero.mpr h11
    have hh₂ : h₂ ≠ 0 := sub_ne_zero.mpr h12
    have hdiff₁ : y₂ - x₂ = h₁ := by dsimp [h₁]; omega
    have hdiff₂ : y₁ - x₂ = h₂ := by dsimp [h₂]; omega
    have hdvd₁ : h₁ ∣ ℓ := by
      have hd1 : h₁ ∣ P.eval x₁ - P.eval y₁ := Polynomial.sub_dvd_eval_sub x₁ y₁ P
      have hd2 : h₁ ∣ P.eval y₂ - P.eval x₂ := hdiff₁ ▸ Polynomial.sub_dvd_eval_sub y₂ x₂ P
      have hsub : ℓ = (P.eval x₁ - P.eval y₁) - (P.eval y₂ - P.eval x₂) := by
        linarith only [heval]
      rw [hsub]
      exact dvd_sub hd1 hd2
    have hdvd₂ : h₂ ∣ ℓ := by
      have hd1 : h₂ ∣ P.eval x₁ - P.eval y₂ := Polynomial.sub_dvd_eval_sub x₁ y₂ P
      have hd2 : h₂ ∣ P.eval y₁ - P.eval x₂ := hdiff₂ ▸ Polynomial.sub_dvd_eval_sub y₁ x₂ P
      have hsub : ℓ = (P.eval x₁ - P.eval y₂) - (P.eval y₁ - P.eval x₂) := by
        linarith only [heval]
      rw [hsub]
      exact dvd_sub hd1 hd2
    have hm₁ : h₁ ∈ D := signedDivs_mem hℓ hdvd₁
    have hm₂ : h₂ ∈ D := signedDivs_mem hℓ hdvd₂
    have hne := secondDiffPoly_ne_zero P h₁ h₂ ℓ hdeg hh₁ hh₂
    apply Finset.mem_sigma.mpr
    refine ⟨Finset.mem_product.mpr ⟨hm₁, hm₂⟩,
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr ?_)⟩
    change (secondDiffPoly P h₁ h₂ ℓ).eval x₁ = 0
    rw [secondDiffPoly_eval]
    have e1 : x₁ - h₁ - h₂ = x₂ := by dsimp [h₁, h₂]; omega
    have e2 : x₁ - h₁ = y₁ := by dsimp [h₁]; omega
    have e3 : x₁ - h₂ = y₂ := by dsimp [h₂]; omega
    rw [e1, e2, e3]
    linarith only [heval]
  have hinj : Set.InjOn f (↑(matchedLocalPairs P B ℓ) : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
    intro q₁ hq₁ q₂ hq₂ heq
    rcases q₁ with ⟨⟨x₁, x₂⟩, ⟨y₁, y₂⟩⟩
    rcases q₂ with ⟨⟨x₁', x₂'⟩, ⟨y₁', y₂'⟩⟩
    have hs₁ := (Finset.mem_filter.mp hq₁).2.1
    have hs₂ := (Finset.mem_filter.mp hq₂).2.1
    have hx : x₁ = x₁' := congrArg (fun z : Σ _ : ℤ × ℤ, ℤ => z.2) heq
    have hd1 : x₁ - y₁ = x₁' - y₁' := congrArg (fun z : Σ _ : ℤ × ℤ, ℤ => z.1.1) heq
    have hd2 : x₁ - y₂ = x₁' - y₂' := congrArg (fun z : Σ _ : ℤ × ℤ, ℤ => z.1.2) heq
    have hy1 : y₁ = y₁' := by omega
    have hy2 : y₂ = y₂' := by omega
    have hx2 : x₂ = x₂' := by omega
    simp only [hx, hy1, hy2, hx2]
  calc
    (matchedLocalPairs P B ℓ).card
      ≤ ((D ×ˢ D).sigma R).card := Finset.card_le_card_of_injOn f hmaps hinj
    _ = ∑ p ∈ D ×ˢ D, (R p).card := Finset.card_sigma _ _
    _ ≤ ∑ _p ∈ D ×ˢ D, P.natDegree := by
      apply Finset.sum_le_sum
      intro p _
      exact (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans (secondDiffPoly_natDegree_le P p.1 p.2 ℓ))
    _ = D.card ^ 2 * P.natDegree := by simp [Finset.card_product, pow_two]
    _ ≤ (2 * ℓ.natAbs.divisors.card) ^ 2 * P.natDegree := by
      gcongr
      exact signedDivs_card ℓ
    _ = 4 * P.natDegree * (ℓ.natAbs.divisors.card) ^ 2 := by ring

theorem matchedLocalPairs_zero_card_le (P : Polynomial ℤ) (B : Finset ℤ)
    (hdeg : 3 ≤ P.natDegree) (hpos : ∀ z ∈ B, 1 ≤ z) :
    (matchedLocalPairs P B 0).card ≤
      4 * (zeroFiberThreshold P).natAbs * P.natDegree * B.card := by
  classical
  let K : ℕ := (zeroFiberThreshold P).natAbs
  have hKpos : 1 ≤ K := by
    dsimp [K]
    have h1 := zeroFiberThreshold_pos P
    omega
  let T := ((Finset.univ : Finset (Fin 4)).product (Finset.Ico 1 K)).product B
  let R (t : (Fin 4 × ℕ) × ℤ) : Finset ℤ :=
    (differencePolynomial P ((t.1.2 : ℤ) - t.2) (P.eval t.2 - P.eval (t.1.2 : ℤ))).roots.toFinset
  let tag (q : (ℤ × ℤ) × (ℤ × ℤ)) : Σ _ : (Fin 4 × ℕ) × ℤ, ℤ :=
    if q.1.1 < zeroFiberThreshold P then ⟨((0, q.1.1.natAbs), q.2.1), q.1.2⟩
    else if q.1.2 < zeroFiberThreshold P then ⟨((1, q.1.2.natAbs), q.2.1), q.1.1⟩
    else if q.2.1 < zeroFiberThreshold P then ⟨((2, q.2.1.natAbs), q.1.1), q.2.2⟩
    else ⟨((3, q.2.2.natAbs), q.1.1), q.2.1⟩
  have eval_diff_eq {a b c d : ℤ} (hsum : a + c = b + d)
      (heval : P.eval a + P.eval c = P.eval b + P.eval d) :
      (differencePolynomial P (a - b) (P.eval b - P.eval a)).eval c = 0 := by
    rw [differencePolynomial_eval, show c + (a - b) = d by omega]
    linarith only [heval]
  have mem_R {a b c d : ℤ} (ha1 : 1 ≤ a) (hab : a ≠ b) (hsum : a + c = b + d)
      (heval : P.eval a + P.eval c = P.eval b + P.eval d) (idx : Fin 4) :
      c ∈ R ((idx, a.natAbs), b) := by
    have ha_eq : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg (by omega)
    have hne := differencePolynomial_ne_zero P (a - b) (P.eval b - P.eval a)
      (by omega) (sub_ne_zero.mpr hab)
    dsimp only [R]
    rw [ha_eq]
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hne).mpr (eval_diff_eq hsum heval))
  have hmaps : Set.MapsTo tag (↑(matchedLocalPairs P B 0) : Set ((ℤ × ℤ) × (ℤ × ℤ)))
      (↑(T.sigma R) : Set (Σ _ : (Fin 4 × ℕ) × ℤ, ℤ)) := by
    intro q hq
    obtain ⟨hprod, hsum, h11, h12, h21, h22, heval⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hprod
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hp1
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hp2
    have heval0 : P.eval q.1.1 + P.eval q.1.2 = P.eval q.2.1 + P.eval q.2.2 := by
      linarith only [heval]
    have hlt := matchedPair_min_lt_threshold hdeg hsum ⟨h11, h12, h21, h22⟩ heval0
    have hK_eq : (K : ℤ) = zeroFiberThreshold P := by
      dsimp [K]
      exact Int.natAbs_of_nonneg (by linarith [zeroFiberThreshold_pos P])
    have mem_ico {z : ℤ} (hzB : z ∈ B) (hzlt : z < zeroFiberThreshold P) :
        z.natAbs ∈ Finset.Ico 1 K := by
      have hz1 : 1 ≤ z := hpos z hzB
      rw [Finset.mem_Ico]
      omega
    dsimp only [tag]
    split_ifs with c1 c2 c3
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_ico hx1 c1⟩, hy1⟩,
        mem_R (hpos _ hx1) h11 hsum heval0 0⟩
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_ico hx2 c2⟩, hy1⟩,
        mem_R (hpos _ hx2) h21 (by omega) (by linarith only [heval0]) 1⟩
    · exact Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_ico hy1 c3⟩, hx1⟩,
        mem_R (hpos _ hy1) h11.symm hsum.symm heval0.symm 2⟩
    · have hy2lt : q.2.2 < zeroFiberThreshold P := by tauto
      exact Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, mem_ico hy2 hy2lt⟩, hx1⟩,
        mem_R (hpos _ hy2) h12.symm (by omega) (by linarith only [heval0]) 3⟩
  have hinj : Set.InjOn tag (↑(matchedLocalPairs P B 0) : Set ((ℤ × ℤ) × (ℤ × ℤ))) := by
    intro q₁ hq₁ q₂ hq₂ heq
    obtain ⟨hp₁, hsum₁, _⟩ := Finset.mem_filter.mp hq₁
    obtain ⟨hp₂, hsum₂, _⟩ := Finset.mem_filter.mp hq₂
    obtain ⟨hx1₁, hx2₁⟩ := Finset.mem_product.mp (Finset.mem_product.mp hp₁).1
    obtain ⟨hy1₁, hy2₁⟩ := Finset.mem_product.mp (Finset.mem_product.mp hp₁).2
    obtain ⟨hx1₂, hx2₂⟩ := Finset.mem_product.mp (Finset.mem_product.mp hp₂).1
    obtain ⟨hy1₂, hy2₂⟩ := Finset.mem_product.mp (Finset.mem_product.mp hp₂).2
    have hidx : (tag q₁).1.1.1 = (tag q₂).1.1.1 := congrArg (fun z => z.1.1.1) heq
    have hval : (tag q₁).1.1.2 = (tag q₂).1.1.2 := congrArg (fun z => z.1.1.2) heq
    have hother : (tag q₁).1.2 = (tag q₂).1.2 := congrArg (fun z => z.1.2) heq
    have hfst : (tag q₁).2 = (tag q₂).2 := congrArg (fun z => z.2) heq
    dsimp only [tag] at hidx hval hother hfst
    split_ifs at hidx hval hother hfst with c1 c2 c3 d1 d2 d3 <;>
      first
      | (exfalso; revert hidx; decide)
      | (have eA : q₁.1.1 = q₂.1.1 := by have := hpos _ hx1₁; have := hpos _ hx1₂; omega
         have eB : q₁.2.1 = q₂.2.1 := hother
         have eC : q₁.1.2 = q₂.1.2 := hfst
         have eD : q₁.2.2 = q₂.2.2 := by omega
         exact Prod.ext (Prod.ext eA eC) (Prod.ext eB eD))
      | (have eA : q₁.1.2 = q₂.1.2 := by have := hpos _ hx2₁; have := hpos _ hx2₂; omega
         have eB : q₁.2.1 = q₂.2.1 := hother
         have eC : q₁.1.1 = q₂.1.1 := hfst
         have eD : q₁.2.2 = q₂.2.2 := by omega
         exact Prod.ext (Prod.ext eC eA) (Prod.ext eB eD))
      | (have eA : q₁.2.1 = q₂.2.1 := by have := hpos _ hy1₁; have := hpos _ hy1₂; omega
         have eB : q₁.1.1 = q₂.1.1 := hother
         have eC : q₁.2.2 = q₂.2.2 := hfst
         have eD : q₁.1.2 = q₂.1.2 := by omega
         exact Prod.ext (Prod.ext eB eD) (Prod.ext eA eC))
      | (have eA : q₁.2.2 = q₂.2.2 := by have := hpos _ hy2₁; have := hpos _ hy2₂; omega
         have eB : q₁.1.1 = q₂.1.1 := hother
         have eC : q₁.2.1 = q₂.2.1 := hfst
         have eD : q₁.1.2 = q₂.1.2 := by omega
         exact Prod.ext (Prod.ext eB eD) (Prod.ext eC eA))
  calc
    (matchedLocalPairs P B 0).card ≤ (T.sigma R).card :=
      Finset.card_le_card_of_injOn tag hmaps hinj
    _ = ∑ t ∈ T, (R t).card := Finset.card_sigma _ _
    _ ≤ ∑ _t ∈ T, P.natDegree := by
      apply Finset.sum_le_sum
      intro t _
      exact (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans (differencePolynomial_natDegree_le P _ _))
    _ = T.card * P.natDegree := by simp [nsmul_eq_mul]
    _ = 4 * (K - 1) * P.natDegree * B.card := by
      simp only [T, Finset.card_product, Finset.card_univ, Fintype.card_fin, Nat.card_Ico]
      ring
    _ ≤ 4 * K * P.natDegree * B.card := by
      have hK1 : K - 1 ≤ K := Nat.sub_le K 1
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hK1))

private theorem two_complement_pair (i₁ i₂ : Fin 4) (hi : i₁ ≠ i₂) :
    ∃ i₃ i₄ : Fin 4, i₃ ≠ i₄ ∧
      (∀ k : Fin 4, k = i₁ ∨ k = i₂ ∨ k = i₃ ∨ k = i₄) := by
  fin_cases i₁ <;> fin_cases i₂ <;> first
    | exact absurd rfl hi
    | exact ⟨0, 1, by decide, fun k => by fin_cases k <;> decide⟩
    | exact ⟨0, 2, by decide, fun k => by fin_cases k <;> decide⟩
    | exact ⟨0, 3, by decide, fun k => by fin_cases k <;> decide⟩
    | exact ⟨1, 2, by decide, fun k => by fin_cases k <;> decide⟩
    | exact ⟨1, 3, by decide, fun k => by fin_cases k <;> decide⟩
    | exact ⟨2, 3, by decide, fun k => by fin_cases k <;> decide⟩

private theorem pair_eq_zero_card_le (P : Polynomial ℤ) (A : Finset ℕ) :
    (((liftSupport A ×ˢ liftSupport A) ×ˢ (liftSupport A ×ˢ liftSupport A)).filter fun q =>
      P.eval q.1.1 + P.eval q.1.2 = P.eval q.2.1 + P.eval q.2.2).card =
      ({z ∈ (Finset.univ : Finset ((Fin 2 → ↥A) × (Fin 2 → ↥A))) |
        (∑ i : Fin 2, P.eval ((z.1 i : ℕ) : ℤ)) =
          ∑ i : Fin 2, P.eval ((z.2 i : ℕ) : ℤ)}).card := by
  classical
  let B := liftSupport A
  let mapFn (z : (Fin 2 → ↥A) × (Fin 2 → ↥A)) : (ℤ × ℤ) × (ℤ × ℤ) :=
    ((((z.1 0 : ℕ) : ℤ), ((z.1 1 : ℕ) : ℤ)), (((z.2 0 : ℕ) : ℤ), ((z.2 1 : ℕ) : ℤ)))
  have hmem (a : ↥A) : ((a : ℕ) : ℤ) ∈ B := mem_liftSupport.mpr ⟨a, a.property, rfl⟩
  symm
  apply Finset.card_bij (fun z _ => mapFn z)
  · intro z hz
    have hsum := (Finset.mem_filter.mp hz).2
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at hsum
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hmem _, hmem _⟩, Finset.mem_product.mpr ⟨hmem _, hmem _⟩⟩, hsum⟩
  · intro z₁ _ z₂ _ heq
    apply Prod.ext
    · funext i
      apply Subtype.ext
      fin_cases i
      · exact Int.ofNat.inj (congrArg (fun u => u.1.1) heq)
      · exact Int.ofNat.inj (congrArg (fun u => u.1.2) heq)
    · funext i
      apply Subtype.ext
      fin_cases i
      · exact Int.ofNat.inj (congrArg (fun u => u.2.1) heq)
      · exact Int.ofNat.inj (congrArg (fun u => u.2.2) heq)
  · intro q hq
    obtain ⟨hp, hsum⟩ := Finset.mem_filter.mp hq
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨a, ha, hae⟩ := mem_liftSupport.mp (Finset.mem_product.mp hp1).1
    obtain ⟨b, hb, hbe⟩ := mem_liftSupport.mp (Finset.mem_product.mp hp1).2
    obtain ⟨c, hc, hce⟩ := mem_liftSupport.mp (Finset.mem_product.mp hp2).1
    obtain ⟨d, hd, hde⟩ := mem_liftSupport.mp (Finset.mem_product.mp hp2).2
    let lhs : Fin 2 → ↥A := ![⟨a, ha⟩, ⟨b, hb⟩]
    let rhs : Fin 2 → ↥A := ![⟨c, hc⟩, ⟨d, hd⟩]
    refine ⟨(lhs, rhs), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simp only [Fin.sum_univ_two, lhs, rhs, Matrix.cons_val_zero, Matrix.cons_val_one,
        hae, hbe, hce, hde, hsum]
    · simp only [mapFn, lhs, rhs, Matrix.cons_val_zero, Matrix.cons_val_one,
        hae, hbe, hce, hde]

theorem local_pairSum_convolution_bound (P : Polynomial ℤ) (hdeg : 3 ≤ P.natDegree)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ M : ℕ, 2 ≤ M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M →
      let B := liftSupport A
      let Q := (B ×ˢ B) ×ˢ (B ×ˢ B)
      (((Q.product Q).filter fun p =>
        p.1.1.1 + p.1.1.2 = p.1.2.1 + p.1.2.2 ∧
        p.1.1.1 ≠ p.1.2.1 ∧ p.1.1.1 ≠ p.1.2.2 ∧
        p.1.1.2 ≠ p.1.2.1 ∧ p.1.1.2 ≠ p.1.2.2 ∧
        P.eval p.1.1.1 + P.eval p.1.1.2 + P.eval p.2.1.1 + P.eval p.2.1.2 =
          P.eval p.1.2.1 + P.eval p.1.2.2 + P.eval p.2.2.1 + P.eval p.2.2.2).card : ℝ) ≤
        C₀ * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
  classical
  have hP0 : 0 < P.natDegree := by omega
  let D : ℝ := P.natDegree
  have hD : 0 < D := by dsimp [D]; exact_mod_cast hP0
  let δ : ℝ := ε / (2 * D)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨Cdiv, hCdiv, hdiv⟩ := divisor_bound hδ
  obtain ⟨C2, hC2, b2⟩ := GoldbachChild1Base.pair_collision_two_bound P (by omega) ε hε
  let K : ℝ := (zeroFiberThreshold P).natAbs
  have hKpos : 0 < K := by
    dsimp [K]
    have h1 := zeroFiberThreshold_pos P
    exact_mod_cast (show 0 < (zeroFiberThreshold P).natAbs by omega)
  let Tconst : ℝ := 4 * D * Cdiv ^ 2 * (2 * coefficientBound P) ^ (2 * δ)
  have hTpos : 0 < Tconst := by
    have hcb := coefficientBound_pos P
    dsimp [Tconst]
    positivity
  refine ⟨4 * K * D * C2 + Tconst, by positivity, ?_⟩
  intro M hM A hA
  have hM1 : 1 ≤ M := by omega
  let B := liftSupport A
  let Q := (B ×ˢ B) ×ˢ (B ×ˢ B)
  let diff2 (q : (ℤ × ℤ) × (ℤ × ℤ)) : ℤ :=
    P.eval q.2.1 + P.eval q.2.2 - P.eval q.1.1 - P.eval q.1.2
  let S := (Q.product Q).filter fun p =>
    p.1.1.1 + p.1.1.2 = p.1.2.1 + p.1.2.2 ∧
    p.1.1.1 ≠ p.1.2.1 ∧ p.1.1.1 ≠ p.1.2.2 ∧
    p.1.1.2 ≠ p.1.2.1 ∧ p.1.1.2 ≠ p.1.2.2 ∧
    P.eval p.1.1.1 + P.eval p.1.1.2 + P.eval p.2.1.1 + P.eval p.2.1.2 =
      P.eval p.1.2.1 + P.eval p.1.2.2 + P.eval p.2.2.1 + P.eval p.2.2.2
  let S0 := S.filter fun p => diff2 p.2 = 0
  let S1 := S.filter fun p => diff2 p.2 ≠ 0
  have hsplit : (S.card : ℝ) = (S0.card : ℝ) + (S1.card : ℝ) := by
    have hnat : S.card = S0.card + S1.card := by
      dsimp only [S0, S1]
      simp only [Finset.card_eq_sum_ones]
      exact (Finset.sum_filter_add_sum_filter_not S (fun p => diff2 p.2 = 0) (fun _ => 1)).symm
    exact_mod_cast hnat
  have hBpos : ∀ z ∈ B, 1 ≤ z := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := mem_liftSupport.mp hz
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (hA ha)).1
    exact_mod_cast ha1
  have hBcard : (B.card : ℝ) = A.card := by exact_mod_cast liftSupport_card A
  -- Zero frequency part: S0 ⊆ (matchedLocalPairs P B 0).product (Q.filter (diff2 = 0))
  have hS0 : (S0.card : ℝ) ≤ (4 * K * D * C2) * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
    let Q0 := Q.filter fun q => P.eval q.1.1 + P.eval q.1.2 = P.eval q.2.1 + P.eval q.2.2
    have hsub0 : S0 ⊆ (matchedLocalPairs P B 0).product Q0 := by
      intro p hp
      obtain ⟨hpS, hdz⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpQ, hsum, h11, h12, h21, h22, heq⟩ := Finset.mem_filter.mp hpS
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpQ
      have hd2 : P.eval p.2.1.1 + P.eval p.2.1.2 = P.eval p.2.2.1 + P.eval p.2.2.2 := by
        dsimp [diff2] at hdz
        linarith only [hdz]
      have hd1 : P.eval p.1.1.1 + P.eval p.1.1.2 - P.eval p.1.2.1 - P.eval p.1.2.2 = 0 := by
        linarith only [heq, hd2]
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hp1, hsum, h11, h12, h21, h22, hd1⟩,
        Finset.mem_filter.mpr ⟨hp2, hd2⟩⟩
    have hQ0 : (Q0.card : ℝ) ≤ C2 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2 := by
      dsimp only [Q0, Q, B]
      rw [pair_eq_zero_card_le P A]
      exact b2 M hM A hA
    have hM0 : ((matchedLocalPairs P B 0).card : ℝ) ≤ 4 * K * D * (A.card : ℝ) := by
      rw [← hBcard]
      dsimp only [K, D]
      exact_mod_cast matchedLocalPairs_zero_card_le P B hdeg hBpos
    have hpow3 : (A.card : ℝ) ^ 3 ≤ (A.card : ℝ) ^ 4 := by
      by_cases h0 : A.card = 0
      · simp [h0]
      · have hone : (1 : ℝ) ≤ A.card := by exact_mod_cast (show 1 ≤ A.card by omega)
        exact pow_le_pow_right₀ hone (by decide)
    calc
      (S0.card : ℝ) ≤ ((matchedLocalPairs P B 0).card : ℝ) * (Q0.card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub0).trans (Finset.card_product _ _).le
      _ ≤ (4 * K * D * (A.card : ℝ)) * (C2 * (M : ℝ) ^ ε * (A.card : ℝ) ^ 2) := by
        gcongr
      _ = (4 * K * D * C2) * (M : ℝ) ^ ε * (A.card : ℝ) ^ 3 := by ring
      _ ≤ (4 * K * D * C2) * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by gcongr
  -- Nonzero frequency part: S1 maps into (Q.filter (diff2 ≠ 0)).sigma (fun q2 => matchedLocalPairs P B (diff2 q2))
  have hS1 : (S1.card : ℝ) ≤ Tconst * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by
    let Q1 := Q.filter fun q => diff2 q ≠ 0
    let F1 := Q1.sigma fun q2 => matchedLocalPairs P B (diff2 q2)
    have hcard1 : S1.card ≤ F1.card := by
      let map1 (p : ((ℤ × ℤ) × (ℤ × ℤ)) × ((ℤ × ℤ) × (ℤ × ℤ))) :
          Σ _ : (ℤ × ℤ) × (ℤ × ℤ), (ℤ × ℤ) × (ℤ × ℤ) := ⟨p.2, p.1⟩
      apply Finset.card_le_card_of_injOn map1
      · intro p hp
        obtain ⟨hpS, hdz⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpQ, hsum, h11, h12, h21, h22, heq⟩ := Finset.mem_filter.mp hpS
        obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpQ
        have hdiff : P.eval p.1.1.1 + P.eval p.1.1.2 - P.eval p.1.2.1 - P.eval p.1.2.2 =
            diff2 p.2 := by
          dsimp [diff2]
          linarith only [heq]
        exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨hp2, hdz⟩,
          Finset.mem_filter.mpr ⟨hp1, hsum, h11, h12, h21, h22, hdiff⟩⟩
      · intro p₁ _ p₂ _ h
        exact Prod.ext (congrArg (fun z : Σ _ : (ℤ × ℤ) × (ℤ × ℤ), (ℤ × ℤ) × (ℤ × ℤ) => z.2) h)
          (congrArg (fun z : Σ _ : (ℤ × ℤ) × (ℤ × ℤ), (ℤ × ℤ) × (ℤ × ℤ) => z.1) h)
    have hfiber_le : ∀ q2 ∈ Q1,
        ((matchedLocalPairs P B (diff2 q2)).card : ℝ) ≤ Tconst * (M : ℝ) ^ ε := by
      intro q2 hq2
      obtain ⟨hqQ, hnz⟩ := Finset.mem_filter.mp hq2
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hqQ
      obtain ⟨c, hc, hce⟩ := mem_liftSupport.mp (Finset.mem_product.mp hp1).1
      obtain ⟨d, hd, hde⟩ := mem_liftSupport.mp (Finset.mem_product.mp hp1).2
      obtain ⟨a, ha, hae⟩ := mem_liftSupport.mp (Finset.mem_product.mp hp2).1
      obtain ⟨b, hb, hbe⟩ := mem_liftSupport.mp (Finset.mem_product.mp hp2).2
      have hℓ_eq : diff2 q2 = (P.eval (a : ℤ) - P.eval (c : ℤ)) +
          (P.eval (b : ℤ) - P.eval (d : ℤ)) := by
        dsimp [diff2]
        rw [← hae, ← hbe, ← hce, ← hde]
        ring
      have hmag1 := natAbs_eval_sub_le P M a c hM1 (Finset.mem_Icc.mp (hA ha)).2
        (Finset.mem_Icc.mp (hA hc)).2
      have hmag2 := natAbs_eval_sub_le P M b d hM1 (Finset.mem_Icc.mp (hA hb)).2
        (Finset.mem_Icc.mp (hA hd)).2
      have hℓ_mag : ((diff2 q2).natAbs : ℝ) ≤
          2 * coefficientBound P * (M : ℝ) ^ P.natDegree := by
        rw [hℓ_eq, Nat.cast_natAbs, Int.cast_abs, Int.cast_add]
        have h1 : |(((P.eval (a : ℤ) - P.eval (c : ℤ) : ℤ) : ℝ))| ≤
            coefficientBound P * (M : ℝ) ^ P.natDegree := by
          simpa [Nat.cast_natAbs, Int.cast_abs] using hmag1
        have h2 : |(((P.eval (b : ℤ) - P.eval (d : ℤ) : ℤ) : ℝ))| ≤
            coefficientBound P * (M : ℝ) ^ P.natDegree := by
          simpa [Nat.cast_natAbs, Int.cast_abs] using hmag2
        calc
          |(((P.eval (a : ℤ) - P.eval (c : ℤ) : ℤ) : ℝ)) +
            (((P.eval (b : ℤ) - P.eval (d : ℤ) : ℤ) : ℝ))|
            ≤ |(((P.eval (a : ℤ) - P.eval (c : ℤ) : ℤ) : ℝ))| +
              |(((P.eval (b : ℤ) - P.eval (d : ℤ) : ℤ) : ℝ))| := abs_add_le _ _
          _ ≤ 2 * coefficientBound P * (M : ℝ) ^ P.natDegree := by linarith only [h1, h2]
      have hℓ_rpow : ((diff2 q2).natAbs : ℝ) ^ (2 * δ) ≤
          (2 * coefficientBound P) ^ (2 * δ) * (M : ℝ) ^ ε := by
        calc
          ((diff2 q2).natAbs : ℝ) ^ (2 * δ)
            ≤ (2 * coefficientBound P * (M : ℝ) ^ P.natDegree) ^ (2 * δ) :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hℓ_mag (by positivity)
          _ = (2 * coefficientBound P) ^ (2 * δ) * ((M : ℝ) ^ P.natDegree) ^ (2 * δ) := by
              rw [Real.mul_rpow (by have := coefficientBound_pos P; positivity) (by positivity)]
          _ = (2 * coefficientBound P) ^ (2 * δ) * (M : ℝ) ^ ε := by
              congr 1
              rw [← Real.rpow_natCast_mul (by positivity)]
              congr 1
              dsimp [δ, D]
              field_simp
      have hm_pos : 0 < (diff2 q2).natAbs := Int.natAbs_pos.mpr hnz
      have hdiv_le : (((diff2 q2).natAbs.divisors.card : ℝ)) ^ 2 ≤
          Cdiv ^ 2 * ((diff2 q2).natAbs : ℝ) ^ (2 * δ) := by
        have h1 := hdiv _ hm_pos
        calc
          (((diff2 q2).natAbs.divisors.card : ℝ)) ^ 2
            ≤ (Cdiv * ((diff2 q2).natAbs : ℝ) ^ δ) ^ 2 :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
          _ = Cdiv ^ 2 * (((diff2 q2).natAbs : ℝ) ^ δ) ^ 2 := by ring
          _ = Cdiv ^ 2 * ((diff2 q2).natAbs : ℝ) ^ (2 * δ) := by
              congr 1
              rw [← Real.rpow_natCast_mul (Nat.cast_nonneg _)]
              congr 1
              ring
      calc
        ((matchedLocalPairs P B (diff2 q2)).card : ℝ)
          ≤ 4 * D * (((diff2 q2).natAbs.divisors.card : ℝ)) ^ 2 := by
            dsimp only [D]
            exact_mod_cast matchedLocalPairs_nonzero_card_le P B (diff2 q2) hdeg hnz
        _ ≤ 4 * D * (Cdiv ^ 2 * ((diff2 q2).natAbs : ℝ) ^ (2 * δ)) := by gcongr
        _ ≤ 4 * D * (Cdiv ^ 2 * ((2 * coefficientBound P) ^ (2 * δ) * (M : ℝ) ^ ε)) := by gcongr
        _ = Tconst * (M : ℝ) ^ ε := by dsimp [Tconst]; ring
    have hQ1_card : (Q1.card : ℝ) ≤ (A.card : ℝ) ^ 4 := by
      have h1 : Q1.card ≤ Q.card := Finset.card_le_card (Finset.filter_subset _ Q)
      have h2 : Q.card = B.card ^ 4 := by
        simp only [Q, Finset.card_product]
        ring
      have h3 : (Q1.card : ℝ) ≤ (B.card : ℝ) ^ 4 := by
        exact_mod_cast h1.trans_eq h2
      simpa [hBcard] using h3
    calc
      (S1.card : ℝ) ≤ (F1.card : ℝ) := by exact_mod_cast hcard1
      _ = ∑ q2 ∈ Q1, ((matchedLocalPairs P B (diff2 q2)).card : ℝ) := by
          dsimp only [F1]
          rw [Finset.card_sigma]
          push_cast
          rfl
      _ ≤ ∑ _q2 ∈ Q1, Tconst * (M : ℝ) ^ ε := Finset.sum_le_sum hfiber_le
      _ = (Q1.card : ℝ) * (Tconst * (M : ℝ) ^ ε) := by simp [nsmul_eq_mul]
      _ ≤ (A.card : ℝ) ^ 4 * (Tconst * (M : ℝ) ^ ε) := by
          exact mul_le_mul_of_nonneg_right hQ1_card (by positivity)
      _ = Tconst * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by ring
  rw [hsplit]
  calc
    (S0.card : ℝ) + (S1.card : ℝ)
      ≤ (4 * K * D * C2) * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 +
          Tconst * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := add_le_add hS0 hS1
    _ = (4 * K * D * C2 + Tconst) * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by ring

theorem prove_child1_pair_sum : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   (↑{x13 ∈ x12 | ∃ (x14 : Fin (4 : ℕ) × Fin (4 : ℕ)) (x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 ∧ x15.1 ≠ x15.2 ∧ x13.1 x14.1 + x13.1 x14.2 = x13.2 x15.1 + x13.2 x15.2}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ)) := by
  classical
  intro P hdeg ε hε
  obtain ⟨C₀, hC₀, hlocal⟩ := local_pairSum_convolution_bound P hdeg ε hε
  refine ⟨256 * C₀, by positivity, ?_⟩
  intro M hM A hA
  let T := Fintype.piFinset (fun _ : Fin 4 => A)
  let w := fun u : Fin 4 → ℕ => ∑ j : Fin 4, P.eval (u j : ℤ)
  let S := (T.product T).filter (fun z => w z.1 = w z.2 ∧
    (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
    (∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧ z.1 i₁ + z.1 i₂ = z.2 j₁ + z.2 j₂))
  let B := liftSupport A
  let Q := (B ×ˢ B) ×ˢ (B ×ˢ B)
  let L := (Q.product Q).filter fun p =>
    p.1.1.1 + p.1.1.2 = p.1.2.1 + p.1.2.2 ∧
    p.1.1.1 ≠ p.1.2.1 ∧ p.1.1.1 ≠ p.1.2.2 ∧
    p.1.1.2 ≠ p.1.2.1 ∧ p.1.1.2 ≠ p.1.2.2 ∧
    P.eval p.1.1.1 + P.eval p.1.1.2 + P.eval p.2.1.1 + P.eval p.2.1.2 =
      P.eval p.1.2.1 + P.eval p.1.2.2 + P.eval p.2.2.1 + P.eval p.2.2.2
  let Pos := (Finset.univ : Finset ((Fin 4 × Fin 4) × (Fin 4 × Fin 4))).filter
    fun c => c.1.1 ≠ c.1.2 ∧ c.2.1 ≠ c.2.2
  let slice (c : (Fin 4 × Fin 4) × (Fin 4 × Fin 4)) :=
    S.filter fun z => z.1 c.1.1 + z.1 c.1.2 = z.2 c.2.1 + z.2 c.2.2
  have hcover : S ⊆ Pos.biUnion slice := by
    intro z hz
    obtain ⟨_, _, _, i₁, i₂, j₁, j₂, hi, hj, hsum⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_biUnion.mpr ⟨((i₁, i₂), (j₁, j₂)),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hj⟩,
      Finset.mem_filter.mpr ⟨hz, hsum⟩⟩
  have hslice_le : ∀ c ∈ Pos, (slice c).card ≤ L.card := by
    intro c hc
    rcases c with ⟨⟨i₁, i₂⟩, ⟨j₁, j₂⟩⟩
    obtain ⟨_, hi, hj⟩ := Finset.mem_filter.mp hc
    obtain ⟨i₃, i₄, hi34, hcovI⟩ := two_complement_pair i₁ i₂ hi
    obtain ⟨j₃, j₄, hj34, hcovJ⟩ := two_complement_pair j₁ j₂ hj
    have hsum4_eq (u : Fin 4 → ℕ) (a₁ a₂ a₃ a₄ : Fin 4)
        (hcov : ∀ k : Fin 4, k = a₁ ∨ k = a₂ ∨ k = a₃ ∨ k = a₄) :
        a₁ ≠ a₂ → a₃ ≠ a₄ →
        (a₁ ≠ a₃ ∧ a₁ ≠ a₄ ∧ a₂ ≠ a₃ ∧ a₂ ≠ a₄) →
        w u = P.eval (u a₁ : ℤ) + P.eval (u a₂ : ℤ) + P.eval (u a₃ : ℤ) + P.eval (u a₄ : ℤ) := by
      intro h12 h34 ⟨h13, h14, h23, h24⟩
      have huniv : ({a₁, a₂, a₃, a₄} : Finset (Fin 4)) = Finset.univ := by
        ext k
        simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_univ, iff_true]
        exact hcov k
      dsimp only [w]
      rw [← huniv, Finset.sum_insert, Finset.sum_insert, Finset.sum_insert, Finset.sum_singleton]
      · ring
      · simp [h34]
      · simp [h23, h24]
      · simp [h12, h13, h14]
    have hdisjI : i₁ ≠ i₃ ∧ i₁ ≠ i₄ ∧ i₂ ≠ i₃ ∧ i₂ ≠ i₄ := by
      have hcard : ({i₁, i₂, i₃, i₄} : Finset (Fin 4)).card = 4 := by
        have huniv : ({i₁, i₂, i₃, i₄} : Finset (Fin 4)) = Finset.univ := by
          ext k; simp [hcovI k]
        rw [huniv, Finset.card_univ, Fintype.card_fin]
      by_contra hbad
      have hle : ({i₁, i₂, i₃, i₄} : Finset (Fin 4)).card ≤ 3 := by
        rcases not_and_or.mp hbad with rfl | hbad
        · have : ({i₁, i₂, i₁, i₄} : Finset (Fin 4)) = {i₁, i₂, i₄} := by ext k; simp; tauto
          rw [this]
          exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
        · rcases not_and_or.mp hbad with rfl | hbad
          · have : ({i₁, i₂, i₃, i₁} : Finset (Fin 4)) = {i₁, i₂, i₃} := by ext k; simp; tauto
            rw [this]
            exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
          · rcases not_and_or.mp hbad with rfl | rfl
            · have : ({i₁, i₂, i₂, i₄} : Finset (Fin 4)) = {i₁, i₂, i₄} := by ext k; simp; tauto
              rw [this]
              exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
            · have : ({i₁, i₂, i₃, i₂} : Finset (Fin 4)) = {i₁, i₂, i₃} := by ext k; simp; tauto
              rw [this]
              exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
      omega
    have hdisjJ : j₁ ≠ j₃ ∧ j₁ ≠ j₄ ∧ j₂ ≠ j₃ ∧ j₂ ≠ j₄ := by
      have hcard : ({j₁, j₂, j₃, j₄} : Finset (Fin 4)).card = 4 := by
        have huniv : ({j₁, j₂, j₃, j₄} : Finset (Fin 4)) = Finset.univ := by
          ext k; simp [hcovJ k]
        rw [huniv, Finset.card_univ, Fintype.card_fin]
      by_contra hbad
      have hle : ({j₁, j₂, j₃, j₄} : Finset (Fin 4)).card ≤ 3 := by
        rcases not_and_or.mp hbad with rfl | hbad
        · have : ({j₁, j₂, j₁, j₄} : Finset (Fin 4)) = {j₁, j₂, j₄} := by ext k; simp; tauto
          rw [this]
          exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
        · rcases not_and_or.mp hbad with rfl | hbad
          · have : ({j₁, j₂, j₃, j₁} : Finset (Fin 4)) = {j₁, j₂, j₃} := by ext k; simp; tauto
            rw [this]
            exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
          · rcases not_and_or.mp hbad with rfl | rfl
            · have : ({j₁, j₂, j₂, j₄} : Finset (Fin 4)) = {j₁, j₂, j₄} := by ext k; simp; tauto
              rw [this]
              exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
            · have : ({j₁, j₂, j₃, j₂} : Finset (Fin 4)) = {j₁, j₂, j₃} := by ext k; simp; tauto
              rw [this]
              exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))
      omega
    let embed (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) :
        ((ℤ × ℤ) × (ℤ × ℤ)) × ((ℤ × ℤ) × (ℤ × ℤ)) :=
      ((((z.1 i₁ : ℤ), (z.1 i₂ : ℤ)), ((z.2 j₁ : ℤ), (z.2 j₂ : ℤ))),
       (((z.1 i₃ : ℤ), (z.1 i₄ : ℤ)), ((z.2 j₃ : ℤ), (z.2 j₄ : ℤ))))
    apply Finset.card_le_card_of_injOn embed
    · intro z hz
      obtain ⟨hzS, hzsum⟩ := Finset.mem_filter.mp hz
      obtain ⟨hprod, hweq, hdisj, _⟩ := Finset.mem_filter.mp hzS
      obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hprod
      have hz1A := Fintype.mem_piFinset.mp hz1
      have hz2A := Fintype.mem_piFinset.mp hz2
      have hmemB (x : ℕ) (hx : x ∈ A) : (x : ℤ) ∈ B := mem_liftSupport.mpr ⟨x, hx, rfl⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hmemB _ (hz1A i₁), hmemB _ (hz1A i₂)⟩,
         Finset.mem_product.mpr ⟨hmemB _ (hz2A j₁), hmemB _ (hz2A j₂)⟩⟩,
        Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hmemB _ (hz1A i₃), hmemB _ (hz1A i₄)⟩,
         Finset.mem_product.mpr ⟨hmemB _ (hz2A j₃), hmemB _ (hz2A j₄)⟩⟩⟩, ?_⟩
      have hw1 := hsum4_eq z.1 i₁ i₂ i₃ i₄ hcovI hi hi34 hdisjI
      have hw2 := hsum4_eq z.2 j₁ j₂ j₃ j₄ hcovJ hj hj34 hdisjJ
      refine ⟨by exact_mod_cast hzsum,
        by exact_mod_cast hdisj i₁ j₁, by exact_mod_cast hdisj i₁ j₂,
        by exact_mod_cast hdisj i₂ j₁, by exact_mod_cast hdisj i₂ j₂, ?_⟩
      linarith only [hweq, hw1, hw2]
    · intro z₁ _ z₂ _ heq
      apply Prod.ext
      · funext k
        rcases hcovI k with rfl | rfl | rfl | rfl
        · exact Int.ofNat.inj (congrArg (fun p => p.1.1.1) heq)
        · exact Int.ofNat.inj (congrArg (fun p => p.1.1.2) heq)
        · exact Int.ofNat.inj (congrArg (fun p => p.2.1.1) heq)
        · exact Int.ofNat.inj (congrArg (fun p => p.2.1.2) heq)
      · funext k
        rcases hcovJ k with rfl | rfl | rfl | rfl
        · exact Int.ofNat.inj (congrArg (fun p => p.1.2.1) heq)
        · exact Int.ofNat.inj (congrArg (fun p => p.1.2.2) heq)
        · exact Int.ofNat.inj (congrArg (fun p => p.2.2.1) heq)
        · exact Int.ofNat.inj (congrArg (fun p => p.2.2.2) heq)
  have hPos_card : Pos.card ≤ 256 := by
    have h1 := Finset.card_le_card (Finset.filter_subset _ _)
    simpa [Fintype.card_prod, Fintype.card_fin] using h1
  have hS_nat : S.card ≤ 256 * L.card := by
    calc
      S.card ≤ (Pos.biUnion slice).card := Finset.card_le_card hcover
      _ ≤ ∑ c ∈ Pos, (slice c).card := Finset.card_biUnion_le
      _ ≤ ∑ _c ∈ Pos, L.card := Finset.sum_le_sum hslice_le
      _ = Pos.card * L.card := by simp [nsmul_eq_mul]
      _ ≤ 256 * L.card := Nat.mul_le_mul_right L.card hPos_card
  have hS_real : (S.card : ℝ) ≤ 256 * (L.card : ℝ) := by exact_mod_cast hS_nat
  have hL_real : (L.card : ℝ) ≤ C₀ * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := hlocal M hM A hA
  have hgoal_le_S :
      ∀ G : Finset ((Fin 4 → ℕ) × (Fin 4 → ℕ)),
        (∀ z ∈ G, z ∈ T.product T ∧ w z.1 = w z.2 ∧
          (∀ i j : Fin 4, z.1 i ≠ z.2 j) ∧
          (∃ i₁ i₂ j₁ j₂ : Fin 4, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
            z.1 i₁ + z.1 i₂ = z.2 j₁ + z.2 j₂)) →
        (G.card : ℝ) ≤ (S.card : ℝ) := by
    intro G hG
    apply Nat.cast_le.mpr
    apply Finset.card_le_card_of_injOn id
    · intro z hz
      obtain ⟨hzT, hweq, hdisj, i₁, i₂, j₁, j₂, hi, hj, hsum⟩ := hG z hz
      exact Finset.mem_filter.mpr ⟨hzT, hweq, hdisj, i₁, i₂, j₁, j₂, hi, hj, hsum⟩
    · intro _ _ _ _ h
      exact h
  refine le_trans (hgoal_le_S _ ?_) ?_
  · intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hz12, p₁, p₂, hp₁, hp₂, hsum⟩ := hz
    rw [Finset.mem_filter] at hz12
    obtain ⟨hzT, hweq, hdisj⟩ := hz12
    exact ⟨hzT, hweq, fun i j => hdisj (i, j), p₁.1, p₁.2, p₂.1, p₂.2, hp₁, hp₂, hsum⟩
  · calc
      (S.card : ℝ) ≤ 256 * (L.card : ℝ) := hS_real
      _ ≤ 256 * (C₀ * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4) := by gcongr
      _ = 256 * C₀ * (M : ℝ) ^ ε * (A.card : ℝ) ^ 4 := by ring

end GoldbachChild1PairSum

theorem Conjectures.Cuts.Taskf45436bd558b4113eea18aa8 : (∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   (↑{x13 ∈ x12 | ∃ (x14 : Fin (4 : ℕ) × Fin (4 : ℕ)) (x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 ∧ x15.1 ≠ x15.2 ∧ x13.1 x14.1 + x13.1 x14.2 = x13.2 x15.1 + x13.2 x15.2}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ)) :=
  GoldbachChild1PairSum.prove_child1_pair_sum
