import Mathlib
import Conjectures.Goldbach.BinaryShiftShortMixedEnergy

/-! Count collisions of two binary shifts at the square-root logarithmic exponent scale.
The uniform two-prime sieve and Romanoff order sum are supplied by
Conjectures.Goldbach.BinaryShiftShortMixedEnergy. The divisor expansion below
adapts its BinarySieve.mean argument to a translate of a doubling orbit.
-/
open Finset Real
namespace RomanovCritical
open Goldbach.OrderTail Conjectures.Goldbach.ShiftPairSieve.Foundation.CentralSelberg

def shift (L i j : ℕ) := 2^(i+1) + 2^(L+1)*2^j

def shifts (L : ℕ) := ((range L) ×ˢ (range L)).image (fun w : ℕ × ℕ => shift L w.1 w.2)

theorem shifts_inj (L : ℕ) : Set.InjOn (fun w : ℕ × ℕ => shift L w.1 w.2)
    (↑((range L) ×ˢ (range L)) : Set (ℕ × ℕ)) := by
  rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd h
  have ha := mem_range.mp (mem_product.mp hab).1
  have hc := mem_range.mp (mem_product.mp hcd).1
  have small (i : ℕ) (hi : i<L) : 2^(i+1) < (2:ℕ)^(L+1) :=
    Nat.pow_lt_pow_right (by decide) (by omega)
  dsimp only [shift] at h
  have eqlo := congrArg (fun n : ℕ => n % 2^(L+1)) h
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (small a ha),
    Nat.mod_eq_of_lt (small c hc)] at eqlo
  have eac : a = c := by
    have := (Nat.pow_right_injective (by decide : 2 ≤ 2)) eqlo
    omega
  subst c
  have ebd := Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos (L+1)) (Nat.add_left_cancel h)
  exact Prod.ext rfl (Nat.pow_right_injective (by decide : 2 ≤ 2) ebd)

theorem shifts_card (L : ℕ) : (shifts L).card = L^2 := by
  rw [shifts,card_image_of_injOn (shifts_inj L),card_product,card_range,sq]

theorem shift_small {L i j : ℕ} (hi : i<L) (hj : j<L) :
    shift L i j ≤ 2^(2*L+1) := by
  have a : (2:ℕ)^(i+1) ≤ 2^(2*L) := Nat.pow_le_pow_right (by decide) (by omega)
  have b : (2:ℕ)^(L+1+j) ≤ 2^(2*L) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold shift
  rw [←pow_add,pow_succ (2:ℕ) (2*L)]
  omega

theorem fiber (L A v d : ℕ) (hd : 0 < ord d) :
    (((range L).filter (fun i => 2^(i+1)+A<v)).filter
      (fun i => d ∣ v-(2^(i+1)+A))).card ≤ L/ord d+1 := by
  classical
  let S := ((range L).filter (fun i => 2^(i+1)+A<v)).filter (fun i => d ∣ v-(2^(i+1)+A))
  have same (i : ℕ) (hi : i ∈ S) : (2:ZMod d)^(i+1)+(A:ZMod d) = v := by
    obtain ⟨hm,hdiv⟩ := mem_filter.mp hi
    have eqv := (Nat.modEq_iff_dvd' (mem_filter.mp hm).2.le).mpr hdiv
    have eqc := (ZMod.natCast_eq_natCast_iff _ _ d).mpr eqv
    push_cast at eqc
    exact eqc
  change S.card ≤ _
  rw [←card_range (L/ord d+1)]
  apply card_le_card_of_injOn (f := fun i => i/ord d)
  · intro i hi
    have h := mem_range.mp (mem_filter.mp (mem_filter.mp hi).1).1
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right h.le))
  · intro i hi j hj heq
    have hp := add_right_cancel ((same i hi).trans (same j hj).symm)
    have ho : IsOfFinOrder (2:ZMod d) := orderOf_pos_iff.mp hd
    have he := Nat.ModEq.add_right_cancel' 1 (ho.pow_eq_pow_iff_modEq.mp hp)
    have hmod : i % ord d = j % ord d := he
    have h := Nat.mod_add_div i (ord d)
    change i / ord d = j / ord d at heq
    rw [hmod,heq] at h
    exact h.symm.trans (Nat.mod_add_div j (ord d))

noncomputable def denoms (D : ℕ) := (Icc 1 D).filter (fun d => Squarefree d ∧ 0 < ord d)

theorem divisor_majorant (n D : ℕ) (hn : 0<n) (hD : n≤D) :
    (∏ p ∈ n.primeFactors.filter (fun p => 2<p), (1+1/(p:ℝ))) ≤
      ∑ d ∈ denoms D, if d∣n then 1/(d:ℝ) else 0 := by
  classical
  let P := n.primeFactors.filter (fun p => 2<p)
  let f (a : Finset ℕ) := ∏ p ∈ a, p
  have fact (a : Finset ℕ) (ha : a ∈ P.powerset) : (f a).primeFactors = a := by
    apply Nat.primeFactors_prod
    intro p hp
    exact Nat.prime_of_mem_primeFactors (mem_filter.mp ((mem_powerset.mp ha) hp)).1
  have facts (a : Finset ℕ) (ha : a ∈ P.powerset) : f a ∈ denoms D ∧ f a ∣ n := by
    have hsq : Squarefree (f a) := by
      have eqp : ∏ p ∈ (f a).primeFactors,p = f a := by rw [fact a ha]
      simpa only [eqp] using Nat.squarefree_prod_primeFactors (f a)
    have hdvd : f a ∣ n := (prod_dvd_prod_of_subset a n.primeFactors _ (fun _ hp =>
      (mem_filter.mp ((mem_powerset.mp ha) hp)).1)).trans (Nat.prod_primeFactors_dvd _)
    have hc : Nat.Coprime 2 (f a) := by
      apply Nat.Coprime.prod_right
      intro p hp
      obtain ⟨hpn,hp2⟩ := mem_filter.mp ((mem_powerset.mp ha) hp)
      exact (Nat.coprime_primes Nat.prime_two (Nat.prime_of_mem_primeFactors hpn)).mpr (by omega)
    have hu : IsUnit (2:ZMod (f a)) := (ZMod.isUnit_iff_coprime 2 (f a)).mpr hc
    have : NeZero (f a) := ⟨hsq.ne_zero⟩
    obtain ⟨u,hu⟩ := hu
    have ho : 0 < ord (f a) := by
      unfold ord
      rw [←hu,orderOf_units]
      exact orderOf_pos u
    exact ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hsq.ne_zero,(Nat.le_of_dvd hn hdvd).trans hD⟩,hsq,ho⟩,hdvd⟩
  rw [prod_one_add]
  apply sum_le_sum_of_injOn f
  · intro a ha b hb hab
    exact (fact a ha).symm.trans ((congrArg Nat.primeFactors hab).trans (fact b hb))
  · intro d hd
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hd
    exact (facts a ha).1
  · intro a ha
    simp [(facts a ha).2,f,one_div,prod_inv_distrib]
  · intro d _ _
    split <;> positivity

theorem compare_singular : ∃ K : ℝ, 0<K ∧ ∀ h : ℕ,
    singular h ≤ K * ∏ p ∈ h.primeFactors.filter (fun p => 2<p), (1+1/(p:ℝ)) := by
  unfold singular
  let Z := ∑' n : ℕ, 1/(n:ℝ)^2
  refine ⟨exp (6*Z),exp_pos _,?_⟩
  intro h
  have point (p : ℕ) (hp : p ∈ h.primeFactors.filter (fun p => 2<p)) : 1+1/((p:ℝ)-2) ≤ exp (6/(p:ℝ)^2)*(1+1/(p:ℝ)) := by
    have hpn := (mem_filter.mp hp).2
    have h3 : (3:ℝ) ≤ p := by exact_mod_cast (show 3≤p by omega)
    have hx : (0:ℝ)<p := by linarith
    have hd : 0 < (p:ℝ)-2 := by linarith
    have hgap : 1/((p:ℝ)-2) ≤ 1/(p:ℝ) + 6/(p:ℝ)^2 := by
      field_simp
      nlinarith only [h3]
    have hmul := mul_le_mul_of_nonneg_right (add_one_le_exp (6/(p:ℝ)^2))
      (show 0 ≤ 1+1/(p:ℝ) by positivity)
    nlinarith only [hgap,hmul,show (0:ℝ) ≤ 6/(p:ℝ)^2 * (1/(p:ℝ)) by positivity]
  have hz : (∑ p ∈ h.primeFactors.filter (fun p => 2<p), 1/(p:ℝ)^2) ≤ Z :=
    (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).sum_le_tsum _ (fun _ _ => by positivity)
  calc _ ≤ ∏ p ∈ h.primeFactors.filter (fun p => 2<p), (exp (6/(p:ℝ)^2)*(1+1/(p:ℝ))) := by
             apply prod_le_prod₀ _ point
             intro p hp
             have hpn : 2 < p := (mem_filter.mp hp).2
             have hx : (2:ℝ) < p := by exact_mod_cast hpn
             positivity
       _ = exp (6*(∑ p ∈ h.primeFactors.filter (fun p => 2<p), 1/(p:ℝ)^2))*∏ p ∈ h.primeFactors.filter (fun p => 2<p), (1+1/(p:ℝ)) := by
             rw [prod_mul_distrib,← Real.exp_sum,Finset.mul_sum]
             simp only [mul_one_div]
       _ ≤ _ := by gcongr



theorem harmonic_budget (L : ℕ) :
    ∑ d ∈ denoms (2^(2*L+1)), 1/(d:ℝ) ≤ 2*((L:ℝ)+1) := by
  let D := (2:ℕ)^(2*L+1)
  have hh := harmonic_le_one_add_log D
  simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast] at hh
  have hsub : (∑ d ∈ denoms D, 1/(d:ℝ)) ≤ ∑ d ∈ Icc 1 D, (d:ℝ)⁻¹ := by
    simp only [one_div]
    exact sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => by positivity)
  have he : Real.log D = (2*(L:ℝ)+1)*Real.log 2 := by dsimp [D]; push_cast; rw [Real.log_pow]; push_cast; ring
  rw [he] at hh
  have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  have hh' : (2*(L:ℝ)+1)*Real.log 2 ≤ (2*(L:ℝ)+1)*1 :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  change (∑ d ∈ denoms D, 1/(d:ℝ)) ≤ _
  linarith only [hsub,hh,hh']

/-- The fourth exponent varies and the other three are absorbed in A and v. -/
theorem row_bound : ∃ B : ℝ, 0<B ∧ ∀ L A v : ℕ, 1≤L → v≤2^(2*L+1) →
    (∑ i ∈ (range L).filter (fun i => 2^(i+1)+A < v), singular (v-(2^(i+1)+A))) ≤ B*L := by
  classical
  obtain ⟨K,hK,hcomp⟩ := compare_singular
  obtain ⟨C,hC,hord⟩ := Goldbach.OrderTail.total
  refine ⟨K*(4+C),by positivity,?_⟩
  intro L A v hL hv
  let D := 2^(2*L+1)
  let S := denoms D
  let F := (range L).filter (fun i => 2^(i+1)+A < v)
  let n i := v-(2^(i+1)+A)
  let w (d i : ℕ) : ℝ := if d∣n i then 1/(d:ℝ) else 0
  have point (i : ℕ) (hi : i∈F) : singular (n i) ≤ K*∑ d ∈ S, w d i := by
    apply (hcomp _).trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    apply divisor_majorant
    · exact Nat.sub_pos_of_lt (mem_filter.mp hi).2
    · exact (Nat.sub_le ..).trans hv
  have col (d : ℕ) (hd : d∈S) :
      (∑ i ∈ F, w d i) ≤ 1/(d:ℝ)+(L:ℝ)*(1/((d:ℝ)*(ord d:ℝ))) := by
    have hc := fiber L A v d (mem_filter.mp hd).2.2
    have hc' : (((F.filter (fun i => d∣n i)).card):ℝ) ≤ (L/ord d:ℕ)+1 := by exact_mod_cast hc
    have hf : ((L/ord d:ℕ):ℝ) ≤ (L:ℝ)/(ord d:ℝ) := Nat.cast_div_le
    have ce := mul_le_mul_of_nonneg_right (hc'.trans (add_le_add_left hf 1)) (show (0:ℝ) ≤ 1/(d:ℝ) by positivity)
    simp only [w,←sum_filter,sum_const,nsmul_eq_mul]
    convert ce using 1; ring
  calc
    _ ≤ ∑ i ∈ F, K*∑ d ∈ S, w d i := sum_le_sum point
    _ = K*∑ d ∈ S, ∑ i ∈ F, w d i := by rw [←mul_sum,sum_comm]
    _ ≤ K*∑ d ∈ S, (1/(d:ℝ)+(L:ℝ)*(1/((d:ℝ)*(ord d:ℝ)))) :=
      mul_le_mul_of_nonneg_left (sum_le_sum col) hK.le
    _ ≤ _ := by
      rw [sum_add_distrib,←mul_sum]
      have hh := harmonic_budget L
      have ht := hord S (fun d hd => (mem_filter.mp hd).2)
      have hl : 1 ≤ (L:ℝ) := by exact_mod_cast hL
      have he : (∑ d ∈ S, 1/(d:ℝ))+(L:ℝ)*(∑ d ∈ S,1/((d:ℝ)*(ord d:ℝ))) ≤ (4+C)*L := by
        change ∑ d ∈ S, 1/(d:ℝ) ≤ _ at hh
        nlinarith only [hh,hl,mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg L)]
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left he hK.le

theorem gaps : ∃ B : ℝ, 0<B ∧ ∀ L : ℕ, 1≤L →
    (∑ u ∈ Goldbach.ShortComb.increasing (shifts L), singular (u.2-u.1)) ≤ B*(L:ℝ)^4 := by
  classical
  obtain ⟨B,hB,hr⟩ := row_bound
  refine ⟨B,hB,?_⟩
  intro L hL
  have row (v : ℕ) (hv : v∈shifts L) :
      (∑ e ∈ shifts L, if e<v then singular (v-e) else 0) ≤ B*(L:ℝ)^2 := by
    obtain ⟨⟨c,d⟩,hcd,hev⟩ := mem_image.mp hv
    have hb : v ≤ 2^(2*L+1) := hev ▸ shift_small (mem_range.mp (mem_product.mp hcd).1) (mem_range.mp (mem_product.mp hcd).2)
    change (∑ e ∈ ((range L) ×ˢ (range L)).image (fun w : ℕ×ℕ => shift L w.1 w.2), _) ≤ _
    rw [sum_image (shifts_inj L),sum_product,sum_comm]
    have one (j : ℕ) (_ : j∈range L) : (∑ i ∈ range L, if shift L i j < v then singular (v-shift L i j) else 0) ≤ B*L := by
      have h := hr L (2^(L+1)*2^j) v hL hb
      rw [sum_filter] at h
      apply le_trans (le_of_eq _) h
      apply sum_congr rfl
      intro i _
      unfold shift
      split_ifs <;> rfl
    apply (sum_le_sum one).trans
    simp only [sum_const,card_range,nsmul_eq_mul]
    exact le_of_eq (by ring)
  unfold Goldbach.ShortComb.increasing
  rw [sum_filter,sum_product,sum_comm]
  apply (sum_le_sum row).trans
  simp only [sum_const,nsmul_eq_mul,shifts_card,Nat.cast_pow]
  exact le_of_eq (by ring)


open Filter
open scoped Topology

private theorem theta_bounds : ∃ K : ℕ, ∀ n ≥ K,
    (19/20 : ℝ) * n < Chebyshev.theta n ∧ Chebyshev.theta n < (21/20 : ℝ) * n := by
  have limN : Tendsto (fun n : ℕ ↦ Chebyshev.theta n / (n : ℝ)) atTop (𝓝 1) :=
    Chebyshev.tendsto_theta_div_atTop.comp tendsto_natCast_atTop_atTop
  apply Filter.eventually_atTop.mp
  filter_upwards [limN.eventually_const_lt (show (19/20 : ℝ) < 1 by norm_num),
    limN.eventually_lt_const (show (1 : ℝ) < 21/20 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hlo hhi hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact ⟨(lt_div_iff₀ hn').mp hlo, (div_lt_iff₀ hn').mp hhi⟩

private theorem window_le (a b : ℕ) (hab : a ≤ b) :
    Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) ≤
      (((Finset.Ioc a b).filter Nat.Prime).card : ℝ) * Real.log b := by
  have expand (n : ℕ) : Chebyshev.theta (n : ℝ) =
      ∑ p ∈ Ioc 0 n, (if p.Prime then Real.log (p:ℝ) else 0) := by
    simp [Chebyshev.theta, sum_filter]
  have split := Finset.sum_union (f := fun p : ℕ => if p.Prime then Real.log (p:ℝ) else 0)
    (Finset.Ioc_disjoint_Ioc_of_le (a := 0) (b := a) (c := a) (d := b) le_rfl)
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hab] at split
  have h1 : Chebyshev.theta (b:ℝ) - Chebyshev.theta (a:ℝ) =
      ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ) := by
    rw [expand, expand, split, sum_filter]
    ring
  rw [h1]
  calc ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (p:ℝ)
      ≤ ∑ p ∈ (Ioc a b).filter Nat.Prime, Real.log (b:ℝ) := by
        refine sum_le_sum fun p hp => ?_
        have hp' := mem_filter.mp hp
        have h2 := (mem_Ioc.mp hp'.1)
        exact Real.log_le_log (by exact_mod_cast hp'.2.pos) (by exact_mod_cast h2.2)
    _ = _ := by simp

def primeWindow (X : ℕ) := (Ioc X (X+X/2)).filter Nat.Prime

theorem prime_mass : ∃ N : ℕ, ∀ X ≥ N,
    (X:ℝ) ≤ 8 * ((primeWindow X).card:ℝ)*Real.log X := by
  obtain ⟨K,hK⟩ := theta_bounds
  refine ⟨max K 20,?_⟩
  intro X hX
  have hx : 20≤X := (le_max_right ..).trans hX
  have hx' := hK X ((le_max_left ..).trans hX)
  have hy := hK (X+X/2) (by omega)
  have ht := window_le X (X+X/2) (by omega)
  change _ ≤ ((primeWindow X).card:ℝ)*_ at ht
  have hlog : log ((X+X/2:ℕ):ℝ) ≤ 2*log X := by
    calc _ ≤ log (2*(X:ℝ)) := Real.log_le_log (by positivity) (by exact_mod_cast (show X+X/2≤2*X by omega))
         _ = log 2+log X := Real.log_mul (by norm_num) (by positivity)
         _ ≤ _ := by linarith [Real.log_le_log (by norm_num : (0:ℝ)<2) (show (2:ℝ) ≤ X by exact_mod_cast (show 2≤X by omega))]
  have lower : (X:ℝ)-1 ≤ 2*(X/2:ℕ) := by
    have h : X ≤ 2*(X/2)+1 := by omega
    exact_mod_cast (show (X:ℝ) - 1 ≤ 2*((X/2:ℕ):ℝ) by
      have hh : (X:ℝ) ≤ 2*((X/2:ℕ):ℝ)+1 := by exact_mod_cast h
      linarith)
  push_cast at hy ht hlog
  have m := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (primeWindow X).card)
  have x20 : (20:ℝ)≤X := by exact_mod_cast hx
  linarith only [m,ht,hy.1,hx'.2,lower,x20]

def targets (X : ℕ) := (Ico X (2*X)).filter Odd

theorem shift_even (L i j : ℕ) : Even (shift L i j) := by
  unfold shift
  rw [pow_succ,pow_succ]
  exact ⟨2^i+2^L*2^j,by ring⟩

theorem first (X L : ℕ) (hx : 3≤X) (fits : 2^(2*L+1)+X/2<X) :
    (shifts L).card * (primeWindow X).card ≤
    ∑ m ∈ targets X, ((shifts L).filter (fun s => Nat.Prime (m-s))).card := by
  classical
  have column (s : ℕ) (hs : s∈shifts L) :
      (primeWindow X).card ≤ ((targets X).filter (fun m => Nat.Prime (m-s))).card := by
    obtain ⟨⟨i,j⟩,hij,rfl⟩ := mem_image.mp hs
    have hbound := shift_small (mem_range.mp (mem_product.mp hij).1) (mem_range.mp (mem_product.mp hij).2)
    change shift L i j ≤ 2^(2*L+1) at hbound
    have he := shift_even L i j
    change (primeWindow X).card ≤ ((targets X).filter (fun m => Nat.Prime (m-shift L i j))).card
    apply card_le_card_of_injOn (f := fun p => p+shift L i j)
    · intro p hp
      obtain ⟨hm,hprime⟩ := mem_filter.mp hp
      obtain ⟨hl,hu⟩ := mem_Ioc.mp hm
      change p+shift L i j ∈ (targets X).filter _
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,
        (hprime.odd_of_ne_two (by omega)).add_even he⟩,by simpa using hprime⟩
    · intro p hp q hq heq
      exact Nat.add_right_cancel heq
  calc
    _ = ∑ _s ∈ shifts L, (primeWindow X).card := by simp
    _ ≤ ∑ s ∈ shifts L, ((targets X).filter (fun m => Nat.Prime (m-s))).card := sum_le_sum column
    _ = _ := by
      simp_rw [Finset.card_filter]
      rw [sum_comm]

theorem pair_transfer (X e f : ℕ) (hef : e<f) (hfit : f≤X) :
    (((targets X).filter (fun m => Nat.Prime (m-e) ∧ Nat.Prime (m-f))).card) ≤
    ((Ico ((f-e)+(X-f)) ((f-e)+(X-f)+X)).filter (fun t => Nat.Prime t ∧ Nat.Prime (t-(f-e)))).card := by
  apply card_le_card_of_injOn (fun m => m-e)
  · intro m hm
    obtain ⟨hm,h₁,h₂⟩ := mem_filter.mp hm
    obtain ⟨hl,hu⟩ := mem_Ico.mp (mem_filter.mp hm).1
    change m-e ∈ (Ico _ _).filter _
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,h₁,by rwa [show m-e-(f-e)=m-f by omega]⟩
  · intro m hm n hn heq
    have h1 := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hm).1).1).1
    have h2 := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hn).1).1).1
    change m-e=n-e at heq
    omega

noncomputable def count (_X L m : ℕ) : ℝ := ((shifts L).filter (fun s => Nat.Prime (m-s))).card

theorem second : ∃ B : ℝ, 0<B ∧ ∃ N : ℕ, ∀ X ≥ N, ∀ L : ℕ, 1≤L →
    2^(2*L+1)≤X → (L:ℝ)^2≤log X →
    ∑ m ∈ targets X, (count X L m)^2 ≤ B*X := by
  classical
  obtain ⟨B,hB,hg⟩ := gaps
  obtain ⟨N,hN⟩ := Goldbach.ShortShift.pairs
  refine ⟨1+4*4114*B,by positivity,max N 2,?_⟩
  intro X hX L hL fits scale
  have hlog := Real.log_pos (show (1:ℝ)<X by exact_mod_cast (show 1<X by omega))
  let J := Goldbach.ShortComb.increasing (shifts L)
  let hits (u : ℕ×ℕ) := ((targets X).filter (fun m => Nat.Prime (m-u.1) ∧ Nat.Prime (m-u.2))).card
  have data (s : ℕ) (hs : s∈shifts L) : Even s ∧ s≤X := by
    obtain ⟨⟨i,j⟩,hij,rfl⟩ := mem_image.mp hs
    exact ⟨shift_even _ _ _,(shift_small (mem_range.mp (mem_product.mp hij).1) (mem_range.mp (mem_product.mp hij).2)).trans fits⟩
  have per (u : ℕ×ℕ) (hu : u∈J) : (hits u:ℝ)*(log X)^2 ≤ 4114*X*singular (u.2-u.1) := by
    obtain ⟨hm,hef⟩ := mem_filter.mp hu
    obtain ⟨he,hf⟩ := mem_product.mp hm
    have hdiv : 2∣u.2-u.1 := Nat.dvd_sub (even_iff_two_dvd.mp (data _ hf).1) (even_iff_two_dvd.mp (data _ he).1)
    have hs := hN X ((le_max_left ..).trans hX) (u.2-u.1) (X-u.2) (by omega) hdiv
    apply le_trans _ hs
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast pair_transfer X u.1 u.2 hef (data _ hf).2
  have whole := sum_le_sum per
  rw [←sum_mul,←mul_sum] at whole
  have g := hg L hL
  have x0 : 0 ≤ (X:ℝ) := Nat.cast_nonneg _
  have hsq : (L:ℝ)^4 ≤ (log X)^2 := by
    calc _ = ((L:ℝ)^2)^2 := by ring
         _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) scale 2
  have bound : (∑ u ∈ J,(hits u:ℝ)) ≤ 4114*X*B := by
    apply (le_of_mul_le_mul_right _ (sq_pos_of_pos hlog) : _)
    calc _ ≤ _ := whole
         _ ≤ 4114*X*(B*(L:ℝ)^4) := mul_le_mul_of_nonneg_left g (by positivity)
         _ ≤ 4114*X*(B*(log X)^2) := by gcongr
         _ = _ := by ring
  have nat := Goldbach.ShortComb.energy (targets X) (shifts L) (fun m s => Nat.Prime (m-s))
  have hc : (targets X).card ≤ X := (card_filter_le ..).trans (by simp [two_mul])
  have e : (∑ m ∈ targets X,(count X L m)^2) ≤ ((targets X).card:ℝ) + 4*(∑ u ∈ J,(hits u:ℝ)) := by
    unfold count
    exact_mod_cast nat
  have hc' : ((targets X).card:ℝ) ≤ X := by exact_mod_cast hc
  nlinarith only [e,bound,hc']


theorem scales_eventually : ∃ N : ℕ, ∀ X ≥ N, let L := ⌊sqrt (log (X:ℝ))⌋₊
    1≤L ∧ (L:ℝ)^2≤log X ∧ log X ≤ 4*(L:ℝ)^2 ∧ 2^(2*L+1)+X/2<X := by
  have lim : Tendsto (fun X : ℕ => log (X:ℝ)) atTop atTop := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (lim.eventually_ge_atTop 100)
  refine ⟨max N 3,?_⟩
  intro X hX
  let L := ⌊sqrt (log (X:ℝ))⌋₊
  have ht : 100 ≤ log (X:ℝ) := hN X ((le_max_left ..).trans hX)
  have ht0 : 0 ≤ log (X:ℝ) := by linarith
  have hs := Real.sq_sqrt ht0
  have hsn := Real.sqrt_nonneg (log (X:ℝ))
  have ten : 10 ≤ sqrt (log (X:ℝ)) := by nlinarith
  have hL : 1 ≤ L := Nat.le_floor (by push_cast; linarith)
  have floorlo : (L:ℝ) ≤ sqrt (log (X:ℝ)) := Nat.floor_le hsn
  have floorhi : sqrt (log (X:ℝ)) < (L:ℝ)+1 := Nat.lt_floor_add_one _
  have hLr : 1 ≤ (L:ℝ) := by exact_mod_cast hL
  have hl2 := pow_le_pow_left₀ (Nat.cast_nonneg L) floorlo 2
  have hr2 := pow_le_pow_left₀ hsn (show sqrt (log (X:ℝ))≤2*L by linarith) 2
  have hlog2 := log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
  have hh : (2*(L:ℝ)+2)* log 2 < log X := by
    have upper := mul_le_mul_of_nonneg_left hlog2 (show 0≤2*(L:ℝ)+2 by positivity)
    nlinarith only [upper,hs,ten,floorlo,mul_nonneg (sub_nonneg.mpr ten) hsn]
  have hpow : ((2:ℝ)^(2*L+2)) < X := by
    apply (Real.log_lt_log_iff (by positivity) (by exact_mod_cast (show 0<X by omega))).mp
    rw [Real.log_pow]
    push_cast
    exact hh
  have hn : 2^(2*L+2) < X := by exact_mod_cast hpow
  rw [show 2*L+2=(2*L+1)+1 by omega,pow_succ] at hn
  refine ⟨hL,by linarith only [hs,hl2],by nlinarith only [hs,hr2],?_⟩
  change 2^(2*L+1)+X/2<X
  omega

theorem support : ∃ c : ℝ, 0<c ∧ ∃ N : ℕ, ∀ X ≥ N,
    let L := ⌊sqrt (log (X:ℝ))⌋₊
    c*(X:ℝ) ≤ (((targets X).filter (fun m => 0<count X L m)).card:ℝ) := by
  classical
  obtain ⟨B,hB,N,hsecond⟩ := second
  obtain ⟨P,hpr⟩ := prime_mass
  obtain ⟨Q,hQ⟩ := scales_eventually
  refine ⟨1/(1024*B),by positivity, max 3 (max N (max P Q)),?_⟩
  intro X hX
  let L := ⌊sqrt (log (X:ℝ))⌋₊
  let G := (targets X).filter (fun m => 0 < count X L m)
  have x3 : 3≤X := by omega
  have x0 : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  obtain ⟨hl,lows,highs,fits⟩ := hQ X (by omega)
  change 1≤L at hl
  change 2^(2*L+1)+X/2<X at fits
  have hp := hpr X (by omega)
  have one := first X L x3 fits
  rw [shifts_card] at one
  let A := ∑ m ∈ targets X, count X L m
  have one' : (L:ℝ)^2 * ((primeWindow X).card:ℝ) ≤ A := by
    dsimp only [A,count]
    exact_mod_cast one
  have low : (X:ℝ) ≤ 32*A := by
    change log (X:ℝ) ≤ 4*(L:ℝ)^2 at highs
    have hh := mul_le_mul_of_nonneg_right highs (Nat.cast_nonneg (primeWindow X).card)
    nlinarith only [hp,hh,one']
  have sumG : ∑ m ∈ G, count X L m = A := by
    rw [sum_filter]
    apply sum_congr rfl
    intro m _
    split_ifs with hm
    · rfl
    · have h : 0 ≤ count X L m := Nat.cast_nonneg _
      exact (le_antisymm (le_of_not_gt hm) h).symm
  have cauchy := sq_sum_le_card_mul_sum_sq (s:=G) (f:=fun m => count X L m)
  rw [sumG] at cauchy
  have rest : ∑ m ∈ G, (count X L m)^2 ≤ B*X := by
    apply le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => sq_nonneg _))
    exact hsecond X (by omega) L hl (by omega) lows
  have hi := cauchy.trans (mul_le_mul_of_nonneg_left rest (Nat.cast_nonneg G.card))
  have low2 := pow_le_pow_left₀ x0.le low 2
  have step : (X:ℝ)*X ≤ (1024*B*(G.card:ℝ))*X := by nlinarith only [low2,hi]
  have h' := (le_of_mul_le_mul_right step x0 : (X:ℝ) ≤ 1024*B*(G.card:ℝ))
  change 1/(1024*B)*(X:ℝ) ≤ (G.card:ℝ)
  rw [one_div,←div_eq_inv_mul]
  exact (div_le_iff₀ (by positivity)).mpr (by linarith only [h'])

end RomanovCritical


theorem Conjectures.Goldbach.RomanovCriticalTwoShiftScale : (by
  classical
  exact ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T : ℕ, ∀ X ≥ T, let L := ⌊C*Real.sqrt (Real.log (X:ℝ))⌋₊; let good := fun m : ℕ => Odd m ∧ ∃ a b : ℕ, 1 ≤ a ∧ a < b ∧ b ≤ L ∧ Nat.Prime (m-(2^a+2^b)); c*(X:ℝ) ≤ (((Finset.Ico X (2*X)).filter good).card:ℝ)) := by
  classical
  obtain ⟨c,hc,N,h⟩ := RomanovCritical.support
  refine ⟨c,2,hc,by norm_num,N,?_⟩
  intro X hX
  apply (h X hX).trans
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro m hm
  obtain ⟨ht,hr⟩ := Finset.mem_filter.mp hm
  obtain ⟨hx,ho⟩ := Finset.mem_filter.mp ht
  refine Finset.mem_filter.mpr ⟨hx,ho,?_⟩
  let L := ⌊Real.sqrt (Real.log (X:ℝ))⌋₊
  have positive : 0 < ((RomanovCritical.shifts L).filter (fun s => Nat.Prime (m-s))).card := by
    change (0:ℝ) < (((RomanovCritical.shifts L).filter (fun s => Nat.Prime (m-s))).card:ℝ) at hr
    exact_mod_cast hr
  obtain ⟨s,hs⟩ := Finset.card_pos.mp positive
  obtain ⟨hshift,hp⟩ := Finset.mem_filter.mp hs
  obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp hshift
  obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
  have iL := Finset.mem_range.mp hi
  have jL := Finset.mem_range.mp hj
  refine ⟨i+1,L+1+j,by omega,by omega,?_,?_⟩
  · apply Nat.le_floor
    have realL : (L:ℝ) ≤ Real.sqrt (Real.log (X:ℝ)) := Nat.floor_le (Real.sqrt_nonneg _)
    have en : L+1+j ≤ 2*L := by omega
    have en' : ((L+1+j:ℕ):ℝ) ≤ 2*(L:ℝ) := by exact_mod_cast en
    linarith only [realL,en']
  · simpa only [RomanovCritical.shift,pow_add] using hp
