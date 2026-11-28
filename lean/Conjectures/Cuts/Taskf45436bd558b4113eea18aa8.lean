import Mathlib
open Finset Function
namespace EqualPair
def D (f : ℕ → ℤ) (n : ℕ) := f (n+1)-f n
def eventuallyPos (f : ℕ → ℤ) := ∃ T : ℕ, ∀ n ≥ T, 0 < f n

private theorem grows {f : ℕ → ℤ} {t : ℕ} (h : ∀ n ≥ t, 0 < D f n) (k : ℕ) :
    f t + (k:ℤ) ≤ f (t+k) := by
  induction k with
  | zero => simp
  | succ k ih => have hh := h (t+k) (by omega); dsimp [D] at hh; rw [←Nat.add_assoc]; push_cast; omega

private theorem down {f : ℕ → ℤ} (h : eventuallyPos (D f)) : eventuallyPos f := by
  obtain ⟨t,ht⟩ := h
  refine ⟨t+(f t).natAbs+1, fun n hn => ?_⟩
  have hg := grows ht (n-t)
  have hh : -f t ≤ ((-f t).natAbs:ℤ) := Int.le_natAbs
  rw [Int.natAbs_neg] at hh
  rw [Nat.add_sub_of_le (by omega : t ≤ n)] at hg
  omega

def iter (P : Polynomial ℤ) (k n : ℕ) : ℤ := ((fwdDiff (1:ℤ))^[k] P.eval) (n:ℤ)

private theorem iter_succ (P : Polynomial ℤ) (k : ℕ) : iter P (k+1) = D (iter P k) := by
  funext n; simp [iter,D,Function.iterate_succ_apply',fwdDiff]

theorem iter_pos (P : Polynomial ℤ) (h : 0 < P.leadingCoeff)
    (k : ℕ) (hk : k ≤ P.natDegree) : eventuallyPos (iter P k) := by
  have hi : ∀ j k, k+j=P.natDegree → eventuallyPos (iter P k) := by
    intro j
    induction j with
    | zero =>
      intro k hk
      simp only [Nat.add_zero] at hk; subst k
      refine ⟨0,fun n hn => ?_⟩
      unfold iter; rw [P.fwdDiff_iter_degree_eq_factorial]
      change 0 < P.leadingCoeff * (P.natDegree.factorial : ℤ)
      positivity
    | succ j ih =>
      intro k hk
      apply down
      rw [←iter_succ]
      exact ih (k+1) (by omega)
  exact hi (P.natDegree-k) k (by omega)

private theorem record {f : ℕ → ℤ} (h : eventuallyPos (D f)) :
    ∃ T : ℕ, ∀ n ≥ T, ∀ i < n, f i < f n := by
  obtain ⟨t,ht⟩ := h
  let S : ℤ := ∑ i ∈ range t, |f i|
  have hS (i : ℕ) (hi : i<t) : f i ≤ S :=
    (le_abs_self _).trans (single_le_sum (f:=fun j => |f j|) (fun j _ => abs_nonneg _) (mem_range.mpr hi))
  refine ⟨t+(S-f t).natAbs+1, fun n hn i hi => ?_⟩
  by_cases hit : i<t
  · have hg := grows ht (n-t)
    rw [Nat.add_sub_of_le (by omega : t ≤ n)] at hg
    have hh : S-f t ≤ ((S-f t).natAbs:ℤ) := Int.le_natAbs
    have he := hS i hit
    omega
  · have hg := grows (t:=i) (fun j hj => ht j (by omega)) (n-i)
    rw [Nat.add_sub_of_le hi.le] at hg
    omega

def box (f : ℕ → ℤ) (x u v : ℕ) := f (x+u+v)-f (x+u)-f (x+v)+f x

private theorem box_succ (f : ℕ → ℤ) (x u v : ℕ) :
    box f x (u+1) v = box f x u v + (D f (x+u+v) - D f (x+u)) := by
  simp only [box,D]; rw [show x+(u+1)+v=x+u+v+1 by omega,show x+(u+1)=x+u+1 by omega]; ring

theorem box_pos_of_record {f : ℕ → ℤ} {T : ℕ} (h : ∀ n ≥ T, ∀ i<n, D f i < D f n)
    (x u v : ℕ) (hu : 0<u) (hv : 0<v) (hx : T≤x+v) : 0 < box f x u v := by
  have aux (k : ℕ) : (k:ℤ) ≤ box f x k v := by
    induction k with
    | zero => simp [box]
    | succ k ih => rw [box_succ]; have hh := h (x+k+v) (by omega) (x+k) (by omega); push_cast; omega
  have := aux u; omega

private theorem delta_box (f : ℕ → ℤ) (x u v : ℕ) :
    box f (x+1) u v - box f x u v = box (D f) x u v := by
  simp only [box,D]; rw [show x+1+u+v=x+u+v+1 by omega,show x+1+u=x+u+1 by omega, show x+1+v=x+v+1 by omega]; ring

theorem eventual_boxes (P : Polynomial ℤ) (hP : 3 ≤ P.natDegree) (hL : 0 < P.leadingCoeff) :
    ∃ T : ℕ, ∀ x u v : ℕ, 0 < u → 0 < v →
      (T ≤ x+v → 0 < box (iter P 0) x u v) ∧
      (T ≤ x+v → box (iter P 0) x u v < box (iter P 0) (x+1) u v) := by
  have h₂ := iter_pos P hL 2 (by omega)
  have h₃ := iter_pos P hL 3 hP
  rw [show iter P 2 = D (D (iter P 0)) by rw [←iter_succ,←iter_succ]] at h₂
  rw [show iter P 3 = D (D (D (iter P 0))) by rw [←iter_succ,←iter_succ,←iter_succ]] at h₃
  obtain ⟨a,ha⟩ := record h₂
  obtain ⟨b,hb⟩ := record h₃
  refine ⟨max a b,fun x u v hu hv => ⟨fun hx => box_pos_of_record ha x u v hu hv (by omega),fun hx => ?_⟩⟩
  have hh := box_pos_of_record hb x u v hu hv (by omega : b ≤ x+v)
  rw [←delta_box] at hh; omega

private theorem box_comm (f : ℕ → ℤ) (x u v : ℕ) : box f x u v = box f x v u := by
  simp only [box]; rw [show x+u+v=x+v+u by omega]; ring

theorem divides (P : Polynomial ℤ) (x u v : ℕ) : u ∣ (box (iter P 0) x u v).natAbs := by
  have h (t : ℕ) : (u:ℤ) ∣ P.eval ((t:ℤ)+(u:ℤ)) - P.eval (↑t) := by
    simpa using Polynomial.sub_dvd_eval_sub ((t:ℤ)+u) (t:ℤ) P
  have z := dvd_sub (h (x+v)) (h x)
  have he : box (iter P 0) x u v =
      (P.eval (((x+v:ℕ):ℤ)+(u:ℤ))-P.eval ↑(x+v:ℕ)) - (P.eval ((x:ℤ)+(u:ℤ))-P.eval ↑x) := by
    simp only [box,iter,Function.iterate_zero, id_eq,Nat.cast_add]
    rw [show (x:ℤ)+u+v=x+v+u by ring]; ring
  rw [he]; exact_mod_cast (Int.natAbs_dvd_natAbs.mpr z)

abbrev Triple := ℕ × ℕ × ℕ

private theorem positive_card (P : Polynomial ℤ) (hd : 3 ≤ P.natDegree) (hL : 0 < P.leadingCoeff) :
    ∃ C : ℕ, ∀ (k : ℤ) (s : Finset Triple),
    (∀ z ∈ s, 0<z.2.1 ∧ 0<z.2.2 ∧ box (iter P 0) z.1 z.2.1 z.2.2 = k) →
    s.card ≤ C*(1+k.natAbs.divisors.card^2) := by
  obtain ⟨T,hT⟩ := eventual_boxes P hd hL
  refine ⟨(T+1)^3,fun k s hs => ?_⟩
  by_cases hk : k=0
  · subst k
    have hsub : s ⊆ (range T) ×ˢ ((range T) ×ˢ (range T)) := by
      intro z hz
      obtain ⟨hu,hv,hb⟩ := hs z hz
      have hn : z.1+z.2.2<T := by by_contra! hh; have := (hT _ _ _ hu hv).1 hh; omega
      have hm : z.1+z.2.1<T := by
        by_contra! hh; have hh' := (hT _ _ _ hv hu).1 hh; rw [←box_comm] at hh'; omega
      simp only [mem_product,mem_range]; omega
    have hc := card_le_card hsub
    simp only [card_product,card_range] at hc
    simp; nlinarith
  · let enc (z : Triple) : Triple := (min z.1 T,z.2)
    have hin : Set.MapsTo enc (↑s) (↑((range (T+1)) ×ˢ (k.natAbs.divisors ×ˢ k.natAbs.divisors)) : Set Triple) := by
      intro z hz
      have hb := (hs z hz).2.2
      have h₁ := divides P z.1 z.2.1 z.2.2
      have h₂ := divides P z.1 z.2.2 z.2.1
      rw [box_comm] at h₂; rw [hb] at h₁ h₂
      exact mem_product.mpr ⟨mem_range.mpr (by change min z.1 T < T+1; omega), mem_product.mpr
        ⟨Nat.mem_divisors.mpr ⟨h₁,by simpa using hk⟩,Nat.mem_divisors.mpr ⟨h₂,by simpa using hk⟩⟩⟩
    have hij : (s : Set Triple).InjOn enc := by
      rintro ⟨x,u,v⟩ hx ⟨y,u',v'⟩ hy he
      change (min x T,u,v) = (min y T,u',v') at he
      obtain ⟨hm,he⟩ := Prod.mk.inj he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
      obtain ⟨hu,hv,hx'⟩ := hs _ hx
      obtain ⟨_,_,hy'⟩ := hs _ hy
      dsimp only at hx' hy' hu hv
      have hmono : StrictMono (fun n : ℕ => box (iter P 0) (T+n) u v) := by
        apply strictMono_nat_of_lt_succ
        intro n; simpa [Nat.add_assoc] using (hT (T+n) u v hu hv).2 (by omega)
      by_cases h : x<T
      · have : x=y := by omega
        simp [this]
      · have h1 : T+(x-T)=x := by omega
        have h2 : T+(y-T)=y := by omega
        have h3 : box (iter P 0) (T+(x-T)) u v = box (iter P 0) (T+(y-T)) u v := by
          rw [h1,h2,hx',hy']
        have heq := hmono.injective h3
        have : x=y := by omega
        simp [this]
    have hc := card_le_card_of_injOn enc hin hij
    simp only [card_product,card_range] at hc
    calc
      _ ≤ (T+1)*k.natAbs.divisors.card^2 := by nlinarith only [hc]
      _ ≤ _ := Nat.mul_le_mul (by calc
        T+1 = (T+1)^1 := by simp
        _ ≤ (T+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)) (by omega)

theorem box_card (P : Polynomial ℤ) (hd : 3 ≤ P.natDegree) :
    ∃ C : ℕ, ∀ (k : ℤ) (s : Finset Triple),
    (∀ z ∈ s, 0<z.2.1 ∧ 0<z.2.2 ∧ box (iter P 0) z.1 z.2.1 z.2.2 = k) →
    s.card ≤ C*(1+k.natAbs.divisors.card^2) := by
  by_cases hp : 0 < P.leadingCoeff
  · exact positive_card P hd hp
  have hpn : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (fun h => by simp [h] at hd)
  obtain ⟨C,hC⟩ := positive_card (-P) (by simpa using hd) (by rw [Polynomial.leadingCoeff_neg]; omega)
  refine ⟨C,fun k s hs => ?_⟩
  apply (hC (-k) s ?_).trans_eq (by simp)
  intro z hz
  obtain ⟨hu,hv,h⟩ := hs z hz
  refine ⟨hu,hv,?_⟩; rw [←h]; simp [box,iter]; ring

end EqualPair

open Finset Filter
namespace PolyCollisionDivisors
/-- Adapted from goldbach-proofs PR #2468, revision
3d9be84b446f4e30f46b52e1c83dc7e49e4535d9 (Apache-2.0). -/
theorem divisorPower (K : ℕ) (hK : 0<K) :
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
      simp only [Real.norm_eq_abs,Nat.cast_add,Nat.cast_one,abs_of_nonneg (pow_nonneg (by positivity : 0≤(e:ℝ)+1) K),one_mul,pow_succ] at hs
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

private theorem divisor_envelope_for_product (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n m : ℕ, m ≤ n →
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

private def height (P : Polynomial ℤ) : ℕ := ∑ j ∈ P.support, (P.coeff j).natAbs
private theorem eval_bound (P : Polynomial ℤ) (M a : ℕ) (hM : 1 ≤ M) (ha : a ≤ M) :
    (P.eval (a:ℤ)).natAbs ≤ height P*M^P.natDegree := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  refine (Int.natAbs_sum_le _ _).trans ?_
  rw [height, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  simp only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left ha _).trans (Nat.pow_le_pow_right (by omega) (Polynomial.le_natDegree_of_mem_supp _ hj))
theorem bound (P : Polynomial ℤ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M a b c d : ℕ), 1 ≤ M → a ≤ M → b ≤ M → c ≤ M → d ≤ M →
      let K : ℤ := P.eval (a:ℤ) + P.eval (b:ℤ) - (P.eval (c:ℤ) + P.eval (d:ℤ))
      (K.natAbs.divisors.card : ℝ)^2 ≤ C * (M:ℝ)^ε := by
  obtain ⟨k,hk⟩ := exists_nat_gt (2*(P.natDegree:ℝ)/ε)
  have kpos : (0:ℝ) < k := (div_nonneg (by positivity) hε.le).trans_lt hk
  have hk' : 0 < k := by exact_mod_cast kpos
  obtain ⟨A,hA,hf⟩ := divisor_envelope_for_product k hk'
  let H : ℕ := 4 * height P + 1
  let r : ℝ := 1/(k:ℝ)
  have Hr : (0:ℝ) < H := by dsimp [H]; positivity
  have Ar : 0 < A := by linarith
  have hr : 0 ≤ r := by dsimp [r]; positivity
  refine ⟨(A*(H:ℝ)^r)^2, by positivity, ?_⟩
  intro M a b c d hM ha hb hc hd
  dsimp only
  let u := P.eval (a:ℤ) + P.eval (b:ℤ)
  let v := P.eval (c:ℤ) + P.eval (d:ℤ)
  have hab := Int.natAbs_add_le (P.eval (a:ℤ)) (P.eval (b:ℤ))
  have hcd := Int.natAbs_add_le (P.eval (c:ℤ)) (P.eval (d:ℤ))
  have hp : (u-v).natAbs ≤ H * M^P.natDegree := by
    have ht := Int.natAbs_sub_le u v
    dsimp [u,v,H] at *
    nlinarith only [ht,hab,hcd,eval_bound P M a hM ha,eval_bound P M b hM hb,
      eval_bound P M c hM hc,eval_bound P M d hM hd,Nat.zero_le (M^P.natDegree)]
  have hf' := hf _ _ hp
  change (((u-v).natAbs.divisors.card:ℝ)) ≤ A*(((H*M^P.natDegree:ℕ):ℝ))^r at hf'
  rw [Nat.cast_mul,Nat.cast_pow,Real.mul_rpow (by positivity) (by positivity),←Real.rpow_natCast,
    ←Real.rpow_mul (by positivity)] at hf'
  have he : (P.natDegree:ℝ)*r ≤ ε/2 := by
    have hl := (div_lt_iff₀ hε).mp hk
    dsimp [r]
    rw [mul_one_div, div_le_iff₀ kpos]
    linarith
  have hM' : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hE := Real.rpow_le_rpow_of_exponent_le hM' he
  have h2 : ((u-v).natAbs.divisors.card:ℝ) ≤ (A*(H:ℝ)^r)*(M:ℝ)^(ε/2) :=
    hf'.trans (by rw [← mul_assoc]; gcongr)
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) (u-v).natAbs.divisors.card) h2 2
  rw [mul_pow,← Real.rpow_natCast ((M:ℝ)^(ε/2)),←Real.rpow_mul (by positivity)] at hpow
  simpa [show ε/2*(2:ℝ)=ε by ring,u,v] using hpow
end PolyCollisionDivisors


namespace EqualPairOrientation

private theorem perm_two {i j : Fin 4} (h : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by
  classical
  let s := Equiv.swap (0 : Fin 4) i
  have h0 : s 0 = i := Equiv.swap_apply_left _ _
  have h1 : s 1 ≠ i := by
    rw [← h0]
    exact fun e => (by decide : (1 : Fin 4) ≠ 0) (s.injective e)
  refine ⟨s.trans (Equiv.swap (s 1) j), ?_, ?_⟩
  · change Equiv.swap (s 1) j (s 0) = i
    rw [h0, Equiv.swap_apply_of_ne_of_ne h1.symm h]
  · exact Equiv.swap_apply_left _ _

theorem orient (z : (Fin 4 → ℕ) × (Fin 4 → ℕ)) (i j k l : Fin 4)
    (hij : i ≠ j) (hkl : k ≠ l) (hdis : ∀ s t, z.1 s ≠ z.2 t)
    (hs : z.1 i + z.1 j = z.2 k + z.2 l) :
    ∃ (swap : Bool) (σ τ : Equiv.Perm (Fin 4)),
      let x := if swap then z.2 else z.1
      let y := if swap then z.1 else z.2
      x (σ 0) < y (τ 0) ∧ x (σ 0) < y (τ 1) ∧
          x (σ 0) + x (σ 1) = y (τ 0) + y (τ 1) := by
  obtain ⟨a, ha, ha'⟩ := perm_two hij
  obtain ⟨b, hb, hb'⟩ := perm_two hkl
  obtain ⟨ar, har, har'⟩ := perm_two hij.symm
  obtain ⟨br, hbr, hbr'⟩ := perm_two hkl.symm
  have h1 := hdis i k
  have h2 := hdis i l
  have h3 := hdis j k
  have h4 := hdis j l
  by_cases hi : z.1 i ≤ z.1 j
  · by_cases hl : z.1 i < z.2 k ∧ z.1 i < z.2 l
    · exact ⟨false,a,b,by simpa [ha,ha',hb,hb'] using And.intro hl.1 (And.intro hl.2 hs)⟩
    · by_cases hk : z.2 k ≤ z.2 l
      · refine ⟨true,b,a,?_⟩; simp only [Bool.true_eq, ↓reduceIte,hb,hb',ha,ha']; omega
      · refine ⟨true,br,a,?_⟩; simp only [Bool.true_eq, ↓reduceIte,hbr,hbr',ha,ha']; omega
  · by_cases hl : z.1 j < z.2 k ∧ z.1 j < z.2 l
    · refine ⟨false,ar,b,?_⟩; simp [har,har',hb,hb']; omega
    · by_cases hk : z.2 k ≤ z.2 l
      · refine ⟨true,b,a,?_⟩; simp [hb,hb',ha,ha']; omega
      · refine ⟨true,br,a,?_⟩; simp [hbr,hbr',ha,ha']; omega

end EqualPairOrientation

open Finset
namespace PolyEqualSum
abbrev Quad := Fin 4 → ℕ
abbrev Pair := Quad × Quad
abbrev Key := Bool × Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4)
def left (k : Key) (z : Pair) (i : Fin 4) := (if k.1 then z.2 else z.1) (k.2.1 i)
def right (k : Key) (z : Pair) (i : Fin 4) := (if k.1 then z.1 else z.2) (k.2.2 i)
def oriented (k : Key) (z : Pair) : Prop :=
  left k z 0 < right k z 0 ∧ left k z 0 < right k z 1 ∧
    left k z 0 + left k z 1 = right k z 0 + right k z 1
def rest (k : Key) (z : Pair) : Quad :=
  ![left k z 2,left k z 3,right k z 2,right k z 3]
def triple (k : Key) (z : Pair) : EqualPair.Triple :=
  (left k z 0,right k z 0-left k z 0,right k z 1-left k z 0)

private lemma recover (k : Key) (z : Pair) (hz : oriented k z) :
    let t := triple k z
    left k z 0=t.1 ∧ left k z 1=t.1+t.2.1+t.2.2 ∧
      right k z 0=t.1+t.2.1 ∧ right k z 1=t.1+t.2.2 := by
  dsimp only [triple]
  rcases hz with ⟨h1,h2,h3⟩
  exact ⟨rfl,by omega,by omega,by omega⟩

private lemma inj (k : Key) (z z' : Pair) (hz : oriented k z) (hz' : oriented k z')
    (ht : triple k z = triple k z') (hr : rest k z = rest k z') : z=z' := by
  have h := recover k z hz
  rw [ht] at h
  obtain ⟨l0,l1,r0,r1⟩ := h
  obtain ⟨l0',l1',r0',r1'⟩ := recover k z' hz'
  have l : left k z = left k z' := by
    funext i; fin_cases i
    · exact l0.trans l0'.symm
    · exact l1.trans l1'.symm
    · exact congrFun hr 0
    · exact congrFun hr 1
  have r : right k z = right k z' := by
    funext i; fin_cases i
    · exact r0.trans r0'.symm
    · exact r1.trans r1'.symm
    · exact congrFun hr 2
    · exact congrFun hr 3
  obtain ⟨sw,σ,τ⟩ := k
  cases sw
  · exact Prod.ext (funext (fun i => by simpa [left] using congrFun l (σ.symm i)))
       (funext (fun i => by simpa [right] using congrFun r (τ.symm i)))
  · exact Prod.ext (funext (fun i => by simpa [right] using congrFun r (τ.symm i)))
       (funext (fun i => by simpa [left] using congrFun l (σ.symm i)))

private def E (P : Polynomial ℤ) (a : ℕ) := P.eval (a:ℤ)
private def K (P : Polynomial ℤ) (t : Quad) :=
  E P (t 2)+E P (t 3)-(E P (t 0)+E P (t 1))

private lemma box_eq (P : Polynomial ℤ) (k : Key) (z : Pair) (hz : oriented k z)
    (he : ∑ i, E P (z.1 i) = ∑ i, E P (z.2 i)) :
    let t := triple k z
    EqualPair.box (EqualPair.iter P 0) t.1 t.2.1 t.2.2 = K P (rest k z) := by
  have sumEq : ∑ i, E P (left k z i) = ∑ i, E P (right k z i) := by
    obtain ⟨sw,σ,τ⟩ := k
    cases sw <;> simp only [left,right,Bool.false_eq_true,↓reduceIte]
    · exact (Equiv.sum_comp σ (fun i => E P (z.1 i))).trans (he.trans (Equiv.sum_comp τ (fun i => E P (z.2 i))).symm)
    · exact (Equiv.sum_comp σ (fun i => E P (z.2 i))).trans (he.symm.trans (Equiv.sum_comp τ (fun i => E P (z.1 i))).symm)
  obtain ⟨l0,l1,r0,r1⟩ := recover k z hz
  simp only [Fin.sum_univ_four] at sumEq
  change E P ((triple k z).1+(triple k z).2.1+(triple k z).2.2) -
    E P ((triple k z).1+(triple k z).2.1) - E P ((triple k z).1+(triple k z).2.2) +
    E P (left k z 0) =
    E P (right k z 2)+E P (right k z 3)-(E P (left k z 2)+E P (left k z 3))
  rw [←l1,←r0,←r1]
  omega

theorem count (P : Polynomial ℤ) (hd : 3≤P.natDegree) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (M : ℕ) (A : Finset ℕ) (G : Finset Pair),
    2≤M → A ⊆ Icc 1 M →
    (∀ z ∈ G, (∀ i, z.1 i ∈ A) ∧ (∀ i, z.2 i ∈ A) ∧
      (∑ i, E P (z.1 i) = ∑ i, E P (z.2 i)) ∧ ∃ k, oriented k z) →
    (G.card:ℝ) ≤ C*(M:ℝ)^ε*(A.card:ℝ)^4 := by
  classical
  obtain ⟨B,hB⟩ := EqualPair.box_card P hd
  obtain ⟨D,hD,hdiv⟩ := PolyCollisionDivisors.bound P ε hε
  let V := ((B:ℝ)+1)*(1+D)
  refine ⟨((Fintype.card Key:ℝ)+1)*V,by dsimp [V]; positivity,?_⟩
  intro M A G hM hA hG
  let T := Fintype.piFinset (fun _ : Fin 4 => A)
  let keys := (univ : Finset Key) ×ˢ T
  let fiber := fun kt : Key × Quad => G.filter (fun z => oriented kt.1 z ∧ rest kt.1 z=kt.2)
  have cover : G ⊆ keys.biUnion fiber := by
    intro z hz
    obtain ⟨hl,hr,_,k,hk⟩ := hG z hz
    apply mem_biUnion.mpr
    refine ⟨(k,rest k z),mem_product.mpr ⟨mem_univ _,?_⟩,mem_filter.mpr ⟨hz,hk,rfl⟩⟩
    apply Fintype.mem_piFinset.mpr
    intro i
    obtain ⟨sw,σ,τ⟩ := k
    cases sw <;> fin_cases i <;> first | apply hl | apply hr
  have hm1 : (1:ℝ) ≤ (M:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast (show 1≤M by omega)) hε.le
  have fiberBound (kt : Key × Quad) (hkt : kt ∈ keys) :
      ((fiber kt).card:ℝ) ≤ V*(M:ℝ)^ε := by
    obtain ⟨k,t⟩ := kt
    let F := fiber (k,t)
    let s := F.image (triple k)
    have ht (i : Fin 4) : t i ≤ M := (mem_Icc.mp (hA ((Fintype.mem_piFinset.mp (mem_product.mp hkt).2) i))).2
    have hK := hdiv M (t 2) (t 3) (t 0) (t 1) (by omega) (ht 2) (ht 3) (ht 0) (ht 1)
    change ((K P t).natAbs.divisors.card:ℝ)^2 ≤ D*(M:ℝ)^ε at hK
    have hc := hB (K P t) s (by
      intro z hz; obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
      obtain ⟨hyG,hor,hrt⟩ := mem_filter.mp hy
      change rest k y=t at hrt
      refine ⟨Nat.sub_pos_of_lt hor.1,Nat.sub_pos_of_lt hor.2.1,?_⟩
      exact (box_eq P k y hor (hG y hyG).2.2.1).trans (congrArg (K P) hrt))
    have hin : Set.InjOn (triple k) (F:Set Pair) := by
      intro z hz w hw he
      exact inj k z w (mem_filter.mp hz).2.1 (mem_filter.mp hw).2.1 he
        ((mem_filter.mp hz).2.2.trans (mem_filter.mp hw).2.2.symm)
    have heq : s.card = F.card := card_image_of_injOn hin
    rw [heq] at hc
    have hcr : (F.card:ℝ) ≤ (B:ℝ)*(1+((K P t).natAbs.divisors.card:ℝ)^2) := by exact_mod_cast hc
    change (F.card:ℝ) ≤ _
    apply hcr.trans
    have hg : 1+((K P t).natAbs.divisors.card:ℝ)^2 ≤ (1+D)*(M:ℝ)^ε := by linarith only [hm1,hK]
    dsimp [V]
    calc
      _ ≤ (B:ℝ)*((1+D)*(M:ℝ)^ε) := mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg B)
      _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ 1+D by linarith) (zero_le_one.trans hm1)]
  have hsum : ((keys.biUnion fiber).card:ℝ) ≤ ∑ kt ∈ keys, ((fiber kt).card:ℝ) := by
    exact_mod_cast (card_biUnion_le (s:=keys) (t:=fiber))
  calc
    _ ≤ _ := (Nat.cast_le.mpr (card_le_card cover)).trans hsum
    _ ≤ ∑ _ ∈ keys, V*(M:ℝ)^ε := sum_le_sum fiberBound
    _ = (Fintype.card Key:ℝ)*(A.card:ℝ)^4*(V*(M:ℝ)^ε) := by
      simp [keys,T]
    _ ≤ _ := by
      have hnn : 0 ≤ (A.card:ℝ)^4*(V*(M:ℝ)^ε) := by dsimp [V]; positivity
      nlinarith only [hnn]

end PolyEqualSum

theorem Conjectures.Cuts.Taskf45436bd558b4113eea18aa8 :
∀ (x1 : Polynomial ℤ),   (3 : ℕ) ≤ x1.natDegree →     ∀ (x3 : ℝ),       (0 : ℝ) < x3 →         ∃ (x5 : ℝ),           (0 : ℝ) < x5 ∧             ∀ (x6 : ℕ),               (2 : ℕ) ≤ x6 →                 ∀ x8 ⊆ Finset.Icc (1 : ℕ) x6,                   have x10 : Finset (Fin (4 : ℕ) → ℕ) := Fintype.piFinset fun (x10 : Fin (4 : ℕ)) => x8;                   let x11 : (Fin (4 : ℕ) → ℕ) → ℤ := fun (x11 : Fin (4 : ℕ) → ℕ) => ∑ x12 : Fin (4 : ℕ), Polynomial.eval (↑(x11 x12) : ℤ) x1;                   have x12 : Finset ((Fin (4 : ℕ) → ℕ) × (Fin (4 : ℕ) → ℕ)) := {x12 ∈ x10.product x10 | x11 x12.1 = x11 x12.2 ∧ ∀ (x13 : Fin (4 : ℕ) × Fin (4 : ℕ)), x12.1 x13.1 ≠ x12.2 x13.2};                   (↑{x13 ∈ x12 | ∃ (x14 : Fin (4 : ℕ) × Fin (4 : ℕ)) (x15 : Fin (4 : ℕ) × Fin (4 : ℕ)), x14.1 ≠ x14.2 ∧ x15.1 ≠ x15.2 ∧ x13.1 x14.1 + x13.1 x14.2 = x13.2 x15.1 + x13.2 x15.2}.card : ℝ) ≤ x5 * (↑x6 : ℝ) ^ x3 * (↑x8.card : ℝ) ^ (4 : ℕ) := by
  classical
  intro P hd ε hε
  obtain ⟨C,hC,h⟩ := PolyEqualSum.count P hd ε hε
  refine ⟨C,hC,?_⟩
  intro M hM A hA
  apply h M A _ hM hA
  intro z hz
  obtain ⟨hz,⟨i,j⟩,⟨k,l⟩,hij,hkl,hs⟩ := Finset.mem_filter.mp hz
  obtain ⟨hm,he,hdis⟩ := Finset.mem_filter.mp hz
  obtain ⟨hm1,hm2⟩ := Finset.mem_product.mp hm
  refine ⟨Fintype.mem_piFinset.mp hm1,Fintype.mem_piFinset.mp hm2,he,?_⟩
  obtain ⟨sw,σ,τ,hor⟩ := EqualPairOrientation.orient z i j k l hij hkl
    (fun s t => hdis (s,t)) hs
  exact ⟨(sw,σ,τ),hor⟩
