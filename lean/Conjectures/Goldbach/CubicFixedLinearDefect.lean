import Mathlib

/-!
In each fiber the right triple has prescribed linear sum and cubic weight.
The depressed cubic identity fixes the product of its three shifted pair
sums. Two signed divisors recover the triple when this product is nonzero.
When it vanishes, one pair has sum bounded in terms of the quadratic
coefficient. Both counts are uniform in the prescribed linear defect.
-/

namespace CubicDefect

def factor (a b : ℤ) (y : Fin 3 → ℕ) (i : Fin 3) : ℤ :=
  3 * a * ((∑ j, (y j : ℤ)) - y i) + 2 * b

theorem leading_ne_zero (P : Polynomial ℤ) (hP : P.natDegree = 3) : P.coeff 3 ≠ 0 := by
  rw [← hP, ← Polynomial.leadingCoeff]
  exact Polynomial.leadingCoeff_ne_zero.mpr (by rintro rfl; simp at hP)

private theorem cubic_eval (P : Polynomial ℤ) (hP : P.natDegree = 3) (x : ℤ) :
    P.eval x = P.coeff 3 * x^3 + P.coeff 2 * x^2 + P.coeff 1 * x + P.coeff 0 := by
  rw [Polynomial.eval_eq_sum_range' (n := 4) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
  ring

private theorem product_identity (P : Polynomial ℤ) (hP : P.natDegree = 3) (y : Fin 3 → ℕ) :
    let a := P.coeff 3
    let b := P.coeff 2
    let L := ∑ i, (y i : ℤ)
    let W := ∑ i, P.eval (y i : ℤ)
    3 * (∏ i, factor a b y i) =
      (3*a*L+3*b)^3 -
        (27*a^2*W + (9*a*b^2 - 27*a^2*P.coeff 1)*L + 3*b^3 - 81*a^2*P.coeff 0) := by
  dsimp only
  simp only [factor, Fin.prod_univ_three, Fin.sum_univ_three, cubic_eval P hP]
  ring

theorem factors_equal (P : Polynomial ℤ) (hP : P.natDegree = 3) (y z : Fin 3 → ℕ)
    (hL : (∑ i, (y i : ℤ)) = ∑ i, (z i : ℤ))
    (hW : (∑ i, P.eval (y i : ℤ)) = ∑ i, P.eval (z i : ℤ)) :
    (∏ i, factor (P.coeff 3) (P.coeff 2) y i) =
      ∏ i, factor (P.coeff 3) (P.coeff 2) z i := by
  have hy := product_identity P hP y
  dsimp only at hy
  rw [hL,hW] at hy
  linarith only [hy, product_identity P hP z]

theorem product_growth (a b : ℤ) (y : Fin 3 → ℕ) (M : ℕ) (hM : 2 ≤ M)
    (hy : ∀ i, y i ≤ M) :
    (∏ i, factor a b y i).natAbs ≤ (9*a.natAbs + 2*b.natAbs)^3 * M^3 := by
  have hl : (∑ j, (y j : ℤ)) ≤ 3*(M:ℤ) := by
    have h (j : Fin 3) : (y j : ℤ) ≤ M := by exact_mod_cast hy j
    rw [Fin.sum_univ_three]
    linarith [h 0, h 1, h 2]
  have single (i : Fin 3) : (factor a b y i).natAbs ≤ (9*a.natAbs + 2*b.natAbs)*M := by
    have hn : 0 ≤ (∑ j, (y j : ℤ)) - y i := sub_nonneg.mpr
      (Finset.single_le_sum (f := fun j => (y j : ℤ)) (fun _ _ => by positivity) (Finset.mem_univ i))
    have hpart : ((∑ j, (y j : ℤ)) - y i).natAbs ≤ 3*M := by
      exact_mod_cast (show ((((∑ j, (y j : ℤ)) - y i).natAbs : ℕ) : ℤ) ≤ 3*(M:ℤ) by
        rw [Int.natCast_natAbs, abs_of_nonneg hn]
        linarith [show (0:ℤ) ≤ y i by positivity])
    unfold factor
    calc
      _ ≤ _ := Int.natAbs_add_le _ _
      _ ≤ 3*a.natAbs*(3*M) + 2*b.natAbs*M := by
        simp only [Int.natAbs_mul]
        change 3*a.natAbs*_+2*b.natAbs ≤ _
        exact Nat.add_le_add (Nat.mul_le_mul_left _ hpart)
          (Nat.le_mul_of_pos_right _ (by omega))
      _ = _ := by ring
  rw [Int.natAbs_prod, ← mul_pow]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod (s := Finset.univ) (fun i _ => single i)

end CubicDefect

namespace CubicDivisor
open Finset Filter Asymptotics
open scoped BigOperators Topology

/-- Divisor growth estimate from the verified B13 far-inner arithmetic cuts,
adapted there from goldbach-proofs PR #2468, revision
3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/
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
      simp only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one, abs_of_nonneg (pow_nonneg (by positivity : 0 ≤ (e : ℝ) + 1) K), one_mul, pow_succ] at hs
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

theorem divisor_envelope (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
    (m.divisors.card : ℝ) ≤ C * (n : ℝ) ^ (1 / (k : ℝ) : ℝ) := by
  obtain ⟨C, CLower, estimate⟩ := divisorPower k hk
  let p : ℝ := 1 / (k : ℝ)
  have CNonnegative : 0 ≤ C := zero_le_one.trans CLower
  refine ⟨C ^ p, Real.one_le_rpow CLower (by unfold p; positivity), fun n m upper => ?_⟩
  by_cases mPositive : 0 < m
  · have mReal : (m : ℝ) ≤ n := by exact_mod_cast upper
    have standard := (estimate m mPositive).trans (mul_le_mul_of_nonneg_left mReal CNonnegative)
    have powered := Real.rpow_le_rpow (pow_nonneg (Nat.cast_nonneg m.divisors.card) k) standard
      (show 0 ≤ p by dsimp [p]; positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg m.divisors.card),
      Real.mul_rpow CNonnegative (Nat.cast_nonneg n)] at powered
    have kReal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have kp : (k : ℝ) * p = 1 := by unfold p; field_simp
    rw [kp, Real.rpow_one] at powered
    exact powered
  · have mZero : m = 0 := by omega
    subst m
    simp only [Nat.divisors_zero, Finset.card_empty, Nat.cast_zero]
    positivity


/-- The squared count of signed divisor choices for a cubic-size integer
is subpolynomial in the ambient interval length. -/
theorem uniform (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 2 ≤ M → ∀ D : ℤ,
      D.natAbs ≤ K*M^3 →
        (2*(D.natAbs.divisors.card:ℝ))^2 ≤ C*(M:ℝ)^ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (6/ε)
  have hk0 : 0 < (k:ℝ) := (by positivity : 0 < 6/ε).trans hk
  have hkpos : 0 < k := by exact_mod_cast hk0
  have hexp : 6*(1/(k:ℝ)) ≤ ε := by
    have h := (div_lt_iff₀ hε).mp hk
    rw [mul_one_div, div_le_iff₀ hk0]
    linarith
  let δ : ℝ := 1/(k:ℝ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,H⟩ := divisor_envelope k hkpos
  have hCp : 0 < C := by linarith
  refine ⟨(2*C*((K:ℝ)+1)^δ)^2, by positivity, ?_⟩
  intro M hM D hD
  have hMK : D.natAbs ≤ (K+1)*M^3 :=
    hD.trans (Nat.mul_le_mul_right _ (Nat.le_succ K))
  have h := H ((K+1)*M^3) D.natAbs hMK
  change (D.natAbs.divisors.card:ℝ) ≤ C*(((K+1)*M^3 : ℕ):ℝ)^δ at h
  push_cast at h
  rw [Real.mul_rpow (by positivity) (by positivity), ←Real.rpow_natCast,
    ← Real.rpow_mul (Nat.cast_nonneg M)] at h
  have hbase : (1:ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  calc
    (2*(D.natAbs.divisors.card:ℝ))^2 ≤
        (2*(C*(((K:ℝ)+1)^δ * (M:ℝ)^((3:ℝ)*δ))))^2 := by
          gcongr
          norm_num at h
          exact h
    _ = (2*C*((K:ℝ)+1)^δ)^2 * (M:ℝ)^(6*δ) := by
      have H2 : ((M:ℝ)^((3:ℝ)*δ))^(2:ℕ) = (M:ℝ)^(6*δ) := by
        rw [←Real.rpow_natCast, ←Real.rpow_mul (Nat.cast_nonneg M)]
        norm_num
        ring_nf
      linear_combination (2*C*((K:ℝ)+1)^δ)^2*H2
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase hexp) (sq_nonneg _)
end CubicDivisor

namespace CubicDefect
open Finset

/-- In the zero-product case one pair is bounded in terms of the quadratic
coefficient, and its ordered entries determine the remaining entry. -/
theorem zero_fiber_bound (a b S : ℤ) (ha : a ≠ 0) (A : Finset ℕ) :
    ((univ : Finset (Fin 3 → ↥A)).filter (fun y =>
      (∑ i, ((y i : ℕ) : ℤ)) = S ∧
        ∃ i, 3*a*(S - ((y i : ℕ) : ℤ)) + 2*b = 0)).card ≤
      3*(2*b.natAbs+1)^2 := by
  classical
  let L := 2*b.natAbs
  let F (i : Fin 3) := (univ : Finset (Fin 3 → ↥A)).filter fun y =>
    (∑ j, ((y j : ℕ):ℤ)) = S ∧ 3*a*(S - ((y i : ℕ):ℤ)) + 2*b = 0
  have pair_bound (u v : ℕ) (h : 3*a*((u:ℤ)+v) + 2*b = 0) : u ≤ L ∧ v ≤ L := by
    have he := congrArg Int.natAbs (show (3*a)*((u:ℤ)+v) = -(2*b) by linarith)
    rw [← Nat.cast_add, Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_neg, Int.natAbs_mul] at he
    have hn : 0 < (3*a).natAbs := Int.natAbs_pos.mpr (mul_ne_zero (by decide) ha)
    have le := Nat.le_mul_of_pos_left (u+v) hn
    have eq' : (3*a).natAbs*(u+v) = 2*b.natAbs := by
      simpa only [Int.natAbs_mul, show (2:ℤ).natAbs = 2 by decide] using he
    dsimp [L]
    omega
  have triple (i : Fin 3) (y : Fin 3 → ↥A) :
      ((y i : ℕ):ℤ) + ((y (i+1) : ℕ):ℤ) + ((y (i+2) : ℕ):ℤ) = ∑ j, ((y j : ℕ):ℤ) := by
    fin_cases i <;> norm_num [Fin.sum_univ_three] <;> ring
  have bound (i : Fin 3) : (F i).card ≤ (L+1)^2 := by
    let f (y : Fin 3 → ↥A) : ℕ × ℕ := (y (i+1), y (i+2))
    let R := range (L+1)
    have maps : Set.MapsTo f (F i) (↑(R ×ˢ R : Finset (ℕ × ℕ))) := by
      intro y hy
      obtain ⟨hs,hz⟩ := (mem_filter.mp hy).2
      have hsum := (triple i y).trans hs
      have hp := pair_bound (y (i+1)) (y (i+2)) (by
        rw [show (((y (i+1) : ℕ):ℤ)+((y (i+2) : ℕ):ℤ)) = S-((y i : ℕ):ℤ) by linarith]
        exact hz)
      exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hp.1),
        mem_range.mpr (Nat.lt_succ_of_le hp.2)⟩
    have inj : Set.InjOn f (F i) := by
      intro y hy z hz he
      have h₁ : (y (i+1) : ℕ) = (z (i+1) : ℕ) := congrArg Prod.fst he
      have h₂ : (y (i+2) : ℕ) = (z (i+2) : ℕ) := congrArg Prod.snd he
      have sy := (triple i y).trans (mem_filter.mp hy).2.1
      have sz := (triple i z).trans (mem_filter.mp hz).2.1
      have hi : (y i : ℕ) = (z i : ℕ) := by omega
      have cover : ∀ i j : Fin 3, j=i ∨ j=i+1 ∨ j=i+2 := by decide
      funext j
      apply Subtype.ext
      rcases cover i j with rfl | rfl | rfl
      · exact hi
      · exact h₁
      · exact h₂
    simpa [R, card_product, pow_two] using card_le_card_of_injOn f maps inj
  have cover : ((univ : Finset (Fin 3 → ↥A)).filter (fun y =>
      (∑ i, ((y i : ℕ) : ℤ)) = S ∧ ∃ i, 3*a*(S-((y i : ℕ):ℤ))+2*b = 0)) ⊆ univ.biUnion F := by
    intro y hy
    obtain ⟨hs,i,hi⟩ := (mem_filter.mp hy).2
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem_univ _,hs,hi⟩⟩
  calc
    _ ≤ _ := card_le_card cover
    _ ≤ ∑ i : Fin 3, (F i).card := card_biUnion_le
    _ ≤ ∑ _i : Fin 3, (L+1)^2 := sum_le_sum (fun i _ => bound i)
    _ = _ := by simp [L]

end CubicDefect

namespace CubicDefect
open Finset

private def signedDivisors (n : ℕ) : Finset ℤ :=
  (n.divisors.image (fun k : ℕ => (k : ℤ))) ∪ (n.divisors.image (fun k : ℕ => -(k : ℤ)))

private theorem signed_mem {k d : ℤ} (h : k ∣ d) (hd : d ≠ 0) :
    k ∈ signedDivisors d.natAbs := by
  obtain ⟨l, hl⟩ := h
  have hdiv : k.natAbs ∣ d.natAbs := ⟨l.natAbs, by rw [hl, Int.natAbs_mul]⟩
  have hh := Nat.mem_divisors.mpr ⟨hdiv, Int.natAbs_ne_zero.mpr hd⟩
  by_cases hk : 0 ≤ k
  · exact mem_union_left _ (mem_image.mpr ⟨_, hh, by rw [Int.natCast_natAbs, abs_of_nonneg hk]⟩)
  · exact mem_union_right _ (mem_image.mpr ⟨_, hh, by rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hk), neg_neg]⟩)

private theorem signed_card (n : ℕ) : (signedDivisors n).card ≤ 2 * n.divisors.card := by
  exact (card_union_le _ _).trans ((add_le_add card_image_le card_image_le).trans_eq (two_mul _).symm)

theorem nonzero_fiber (a b S d : ℤ) (ha : a ≠ 0) (hd : d ≠ 0)
    (A : Finset ℕ) (Y : Finset (Fin 3 → ↥A))
    (hs : ∀ y ∈ Y, (∑ i, ((y i : ℕ) : ℤ)) = S)
    (hp : ∀ y ∈ Y, (∏ i, (3*a*(S-((y i : ℕ):ℤ)) + 2*b)) = d) :
    Y.card ≤ (2*d.natAbs.divisors.card)^2 := by
  classical
  let F (y : Fin 3 → ↥A) (i : Fin 3) : ℤ := 3*a*(S-((y i : ℕ):ℤ)) + 2*b
  let V := signedDivisors d.natAbs
  let f (y : Fin 3 → ↥A) := (F y 0, F y 1)
  have memV (y) (hy : y ∈ Y) (i : Fin 3) : F y i ∈ V := by
    apply signed_mem _ hd
    rw [← hp y hy]
    exact Finset.dvd_prod_of_mem (F y) (mem_univ i)
  have hm : Set.MapsTo f Y ((V ×ˢ V : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := fun y hy =>
    mem_product.mpr ⟨memV y hy 0, memV y hy 1⟩
  have hinj : Set.InjOn f Y := by
    intro y hy z hz hh
    have recover (i : Fin 3) (e : F y i = F z i) : y i = z i := by
      dsimp only [F] at e
      have hprod : 3*a ≠ 0 := mul_ne_zero (by decide) ha
      have ee := mul_left_cancel₀ hprod (add_right_cancel e)
      apply Subtype.ext
      exact_mod_cast (sub_right_inj.mp ee)
    have h0 := recover 0 (congrArg Prod.fst hh)
    have h1 := recover 1 (congrArg Prod.snd hh)
    have sl := (hs y hy).trans (hs z hz).symm
    simp only [Fin.sum_univ_three, h0, h1] at sl
    have h2 : y 2 = z 2 := by
      apply Subtype.ext
      exact_mod_cast (show ((y 2 : ℕ):ℤ) = ((z 2 : ℕ):ℤ) by omega)
    funext i
    fin_cases i <;> assumption
  calc
    Y.card ≤ (V ×ˢ V).card := card_le_card_of_injOn f hm hinj
    _ = V.card^2 := by rw [card_product, sq]
    _ ≤ _ := Nat.pow_le_pow_left (signed_card _) _
end CubicDefect

namespace CubicDefect

open Finset

theorem total_bound {α : Type*} [Fintype α] [DecidableEq α]
    (R : α → α → Prop) [DecidableRel R] (B : ℝ)
    (hb : ∀ x, (((Finset.univ : Finset α).filter (R x)).card : ℝ) ≤ B) :
    (((Finset.univ : Finset (α × α)).filter (fun z => R z.1 z.2)).card : ℝ) ≤
      B * (Fintype.card α : ℝ) := by
  have count :
      ((univ : Finset (α × α)).filter (fun z => R z.1 z.2)).card =
        ∑ x : α, ((univ : Finset α).filter (R x)).card := by
    simp only [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  rw [count, Nat.cast_sum]
  calc
    _ ≤ ∑ _x : α, B := sum_le_sum fun x _ => hb x
    _ = _ := by simp [mul_comm]

end CubicDefect

theorem Conjectures.Goldbach.CubicFixedLinearDefect : (
by
  classical
  exact ∀ P : Polynomial ℤ, P.natDegree=3 → ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ M : ℕ, 2≤M → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M → ∀ h : ℤ, let wt := fun (x : Fin 3 → (↥A)) => ∑ i, P.eval ((x i : ℕ):ℤ); let lin := fun (x : Fin 3 → (↥A)) => ∑ i, ((x i : ℕ):ℤ); let triples := (Finset.univ : Finset ((Fin 3 → (↥A)) × (Fin 3 → (↥A)))); ((triples.filter (fun z => wt z.1=wt z.2 ∧ lin z.1-lin z.2=h)).card:ℝ) ≤ C*(M:ℝ)^ε*(A.card:ℝ)^3
) := by
  classical
  intro P hP ε hε
  let a := P.coeff 3
  let b := P.coeff 2
  let K := (9*a.natAbs + 2*b.natAbs)^3
  let Z : ℕ := 3*(2*b.natAbs + 1)^2
  obtain ⟨C, hC, hτ⟩ := CubicDivisor.uniform K ε hε
  have ha : a ≠ 0 := CubicDefect.leading_ne_zero P hP
  refine ⟨C + Z, by positivity, ?_⟩
  intro M hM A hA h
  dsimp only
  let val (x : Fin 3 → ↥A) (i : Fin 3) : ℕ := x i
  let L (x : Fin 3 → ↥A) := ∑ i, ((val x i : ℕ) : ℤ)
  let W (x : Fin 3 → ↥A) := ∑ i, P.eval ((val x i : ℕ) : ℤ)
  let R (x y : Fin 3 → ↥A) := W x = W y ∧ L x - L y = h
  have hpow : 1 ≤ (M : ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ M)) hε.le
  have fiber (x : Fin 3 → ↥A) :
      (((Finset.univ : Finset (Fin 3 → ↥A)).filter (R x)).card : ℝ) ≤ (C + Z) * (M:ℝ)^ε := by
    let Y := (Finset.univ : Finset (Fin 3 → ↥A)).filter (R x)
    change (Y.card : ℝ) ≤ _
    by_cases hn : Y.Nonempty
    · obtain ⟨r, hr⟩ := hn
      let S := L r
      let d := ∏ i, CubicDefect.factor a b (val r) i
      have ref : W x = W r ∧ L x - L r = h := (Finset.mem_filter.mp hr).2
      have sl (y) (hy : y ∈ Y) : L y = S := by
        have hy' : W x = W y ∧ L x - L y = h := (Finset.mem_filter.mp hy).2
        dsimp only [S]
        omega
      have pr (y) (hy : y ∈ Y) : (∏ i, (3*a*(S - ((y i : ℕ):ℤ)) + 2*b)) = d := by
        have hy' : W x = W y ∧ L x - L y = h := (Finset.mem_filter.mp hy).2
        have ep := CubicDefect.factors_equal P hP (val y) (val r) (sl y hy) (hy'.1.symm.trans ref.1)
        change (∏ i, (3*a*(L y - ((y i : ℕ):ℤ)) + 2*b)) = d at ep
        rwa [sl y hy] at ep
      by_cases hd : d = 0
      · have incl : Y ⊆ (Finset.univ : Finset (Fin 3 → ↥A)).filter (fun y =>
              (∑ i, ((y i : ℕ) : ℤ)) = S ∧ ∃ i, 3*a*(S - ((y i : ℕ):ℤ)) + 2*b = 0) := by
          intro y hy
          obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp ((pr y hy).trans hd)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,sl y hy,i,hi⟩
        have hz : Y.card ≤ Z := (Finset.card_le_card incl).trans (CubicDefect.zero_fiber_bound a b S ha A)
        calc
          (Y.card : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hz
          _ ≤ C + Z := by linarith
          _ ≤ (C + Z) * (M:ℝ)^ε := le_mul_of_one_le_right (by positivity) hpow
      · have hnz := CubicDefect.nonzero_fiber a b S d ha hd A Y sl pr
        have hg : d.natAbs ≤ K*M^3 := CubicDefect.product_growth a b (val r) M hM
          (fun i => (Finset.mem_Icc.mp (hA (r i).property)).2)
        calc
          (Y.card:ℝ) ≤ (2*(d.natAbs.divisors.card:ℝ))^2 := by exact_mod_cast hnz
          _ ≤ C*(M:ℝ)^ε := hτ M hM d hg
          _ ≤ _ := by gcongr; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have all := CubicDefect.total_bound R ((C + Z)*(M:ℝ)^ε) fiber
  simpa only [R, W, L, val, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow] using all
