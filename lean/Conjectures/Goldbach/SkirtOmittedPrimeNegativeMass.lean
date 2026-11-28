import Mathlib
import Conjectures.Goldbach.BinaryShiftOrderTail

/- The annular kernel is bounded from below on the interior lobe with
4/3 ≤ (N+1)t ≤ 5/3. The divisor argument uses the accepted
BinaryShiftOrderTail version of Mertens' reciprocal-prime sum. -/


namespace GoldbachDivisorBand

/-- In the band pd ≤ 2Q each coprime divisor has weight at least 1/(2pQ). -/
theorem divisor_weight {p d Q : ℕ} (hp : 0 < p) (hd : 0 < d) (hQ : 0 < Q)
    (hcp : p.Coprime d) (hband : p*d ≤ 2*Q) :
    1 / (2*(p:ℝ)*Q) ≤ (d.totient:ℝ) / (((p*d).totient:ℝ)^2) := by
  rw [Nat.totient_mul hcp, Nat.cast_mul, mul_pow]
  have ha : (0:ℝ) < p.totient := by exact_mod_cast Nat.totient_pos.mpr hp
  have hb : (0:ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hpa : (p.totient:ℝ) ≤ p := by exact_mod_cast p.totient_le
  have hdb : (d.totient:ℝ) ≤ d := by exact_mod_cast d.totient_le
  have hpd : (p:ℝ)*d ≤ 2*Q := by exact_mod_cast hband
  have he : (p.totient:ℝ)^2*d.totient ≤ 2*p*Q := calc
    _ ≤ (p:ℝ)^2*d := by gcongr
    _ = (p:ℝ)*(p*d) := by ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpd (Nat.cast_nonneg (α:=ℝ) p)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith only [mul_le_mul_of_nonneg_right he hb.le]

open Finset

theorem dvd_omitted_primorial {t p y : ℕ} (ht : Squarefree t) (hp : ¬ p ∣ t)
    (hs : ∀ r ∈ t.primeFactors, r ≤ y) :
    t ∣ ∏ r ∈ (Icc 2 y).filter (fun r => r.Prime ∧ r ≠ p), r := by
  have hsub : t.primeFactors ⊆ (Icc 2 y).filter (fun r => r.Prime ∧ r ≠ p) := by
    intro r hr
    obtain ⟨hprime, hd, _⟩ := Nat.mem_primeFactors.mp hr
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hprime.two_le, hs r hr⟩, hprime,
      fun he => hp (he ▸ hd)⟩
  have h := Finset.prod_dvd_prod_of_subset t.primeFactors _ (fun r : ℕ => r) hsub
  rwa [Nat.prod_primeFactors_of_squarefree ht] at h

/-- A linear count of band divisors combines with a uniform positive kernel bound. -/
theorem mass_of_band_count {p Q : ℕ} (hp : 0 < p) (hQ : 0 < Q)
    (D : Finset ℕ) (mass : ℕ → ℝ) (m δ : ℝ) (hm : 0 ≤ m)
    (hcount : δ*(Q:ℝ) ≤ D.card)
    (hD : ∀ d ∈ D, 0 < d ∧ p.Coprime d ∧ p*d ≤ 2*Q ∧ m ≤ mass (p*d)) :
    δ*m/(2*p) ≤ ∑ d ∈ D, (d.totient:ℝ) / (((p*d).totient:ℝ)^2) * mass (p*d) := by
  have hpos : 0 < (2:ℝ)*p*Q := by positivity
  calc
    _ = δ*(Q:ℝ)*(1/(2*(p:ℝ)*Q)*m) := by field_simp
    _ ≤ (D.card:ℝ)*(1/(2*(p:ℝ)*Q)*m) :=
      mul_le_mul_of_nonneg_right hcount (mul_nonneg (by positivity) hm)
    _ = ∑ _d ∈ D, 1/(2*(p:ℝ)*Q)*m := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hd', hcp, hband, hmass⟩ := hD d hd
      exact mul_le_mul (divisor_weight hp hd' hQ hcp hband) hmass hm (by positivity)

open Filter

def omittedProduct (p y : ℕ) : ℕ :=
  ∏ r ∈ (Icc 2 y).filter (fun r => r.Prime ∧ r ≠ p), r

theorem omittedProduct_pos (p y : ℕ) : 0 < omittedProduct p y :=
  Finset.prod_pos fun _ hr => (mem_filter.mp hr).2.1.pos

theorem omittedProduct_le (p y : ℕ) : omittedProduct p y ≤ 4^y := by
  have hsub : (Icc 2 y).filter (fun r => r.Prime ∧ r ≠ p) ⊆
      (range (y+1)).filter Nat.Prime := by
    intro r hr
    obtain ⟨hry,hprime,_⟩ := mem_filter.mp hr
    exact mem_filter.mpr ⟨mem_range.mpr (by have := (mem_Icc.mp hry).2; omega),hprime⟩
  have hd : omittedProduct p y ∣ primorial y :=
    Finset.prod_dvd_prod_of_subset _ _ (fun r : ℕ => r) hsub
  exact (Nat.le_of_dvd (primorial_pos y) hd).trans (primorial_le_four_pow y)

theorem omittedProduct_tendsto (p : ℕ) :
    Tendsto (omittedProduct p) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨r,hr,hrp⟩ := Nat.exists_infinite_primes (max b (p+1))
  filter_upwards [eventually_ge_atTop r] with y hy
  have hmem : r ∈ (Icc 2 y).filter (fun k => k.Prime ∧ k ≠ p) :=
    mem_filter.mpr ⟨mem_Icc.mpr ⟨hrp.two_le,hy⟩,hrp,by omega⟩
  have hd : r ∣ omittedProduct p y := Finset.dvd_prod_of_mem (fun k : ℕ => k) hmem
  exact le_trans (by omega : b ≤ r) (Nat.le_of_dvd (omittedProduct_pos p y) hd)

def bandScale (p y : ℕ) := (Nat.log 2 (omittedProduct p y + 2))^2

theorem bandScale_upper (p y : ℕ) (hy : 0 < y) : 2*bandScale p y ≤ 32*y^2 := by
  have hpow : 2 ≤ 4^y := by
    calc
      2 ≤ 4^1 := by decide
      _ ≤ 4^y := Nat.pow_le_pow_right (by decide) hy
  have he : 4^y = 2^(2*y) := by rw [pow_mul]; norm_num
  have hb : omittedProduct p y + 2 ≤ 2^(2*y+1) := by
    rw [pow_succ, ←he]
    have := omittedProduct_le p y
    omega
  have hl := Nat.log_mono_right (b:=2) hb
  rw [Nat.log_pow (by decide : 1 < 2)] at hl
  unfold bandScale
  have hc : Nat.log 2 (omittedProduct p y + 2) ≤ 4*y := by omega
  nlinarith [Nat.pow_le_pow_left hc 2]

theorem bandScale_tendsto (p : ℕ) : Tendsto (bandScale p) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [(tendsto_atTop.mp (omittedProduct_tendsto p)) (2^b)] with y hy
  have hl := Nat.le_log_of_pow_le (by decide : 1 < 2)
    (by omega : 2^b ≤ omittedProduct p y + 2)
  unfold bandScale
  nlinarith [Nat.le_self_pow (by decide : 2 ≠ 0) (Nat.log 2 (omittedProduct p y + 2))]

end GoldbachDivisorBand

namespace GoldbachOmittedPrime
open Finset Filter MeasureTheory
open scoped Topology Classical
noncomputable section

def target (p y : ℕ) := ∏ r ∈ (Icc 2 y).filter (fun r => r.Prime ∧ r≠p), r
def grid (N : ℕ) := (Nat.log 2 (N+2))^2
def kernel (N : ℕ) (t : ℝ) := (Real.sin (Real.pi*((N:ℝ)+1)*t)/Real.sin (Real.pi*t))^2
def mass (N q : ℕ) :=
  let lo := (grid N:ℝ)/((q:ℝ)*N)
  2*∫ t in lo..(lo*(N:ℝ)^(1/6:ℝ)), kernel N t
def divisorsBand (p N : ℕ) := N.divisors.filter (fun d => grid N<p*d ∧ p*d≤2*grid N)
private theorem interior_lobe {N : ℕ} {t : ℝ} (hN : 3≤N)
    (hl : 4/(3*((N:ℝ)+1)) ≤ t) (hu : t ≤ 5/(3*((N:ℝ)+1))) :
    (((N:ℝ)+1)/(4*Real.pi))^2 ≤ kernel N t := by
  have hN' : (3:ℝ)≤N := by exact_mod_cast hN
  have hden : 0<3*((N:ℝ)+1) := by positivity
  have hl' := (div_le_iff₀ hden).mp hl
  have hu' := (le_div_iff₀ hden).mp hu
  have ht : 0<t := (div_pos (by norm_num) hden).trans_le hl
  have ht1 : t<1 := hu.trans_lt ((div_lt_one hden).mpr (by linarith))
  have hpi := Real.pi_pos
  let v := Real.pi*((N:ℝ)+1)*t-3*Real.pi/2
  have hv : |v| ≤ Real.pi/3 := by
    rw [abs_le];dsimp [v]
    constructor <;> nlinarith only [mul_le_mul_of_nonneg_left hl' hpi.le,
      mul_le_mul_of_nonneg_left hu' hpi.le,hpi]
  have hcos : (1:ℝ)/2 ≤ Real.cos v := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg v)
      (show Real.pi/3 ≤ Real.pi by linarith) hv
    simpa only [Real.cos_pi_div_three,Real.cos_abs] using h
  have hsin : Real.sin (Real.pi*((N:ℝ)+1)*t) = -Real.cos v := by
    rw [show Real.pi*((N:ℝ)+1)*t = v+Real.pi+Real.pi/2 by dsimp [v];ring,
      Real.sin_add,Real.cos_pi_div_two,Real.sin_pi_div_two,mul_zero,zero_add,mul_one,Real.cos_add_pi]
  have hsp := Real.sin_pos_of_pos_of_lt_pi (mul_pos hpi ht)
    (by simpa only [mul_one] using mul_lt_mul_of_pos_left ht1 hpi)
  have hsu := Real.sin_le (mul_nonneg hpi.le ht.le)
  have hnum : (1:ℝ)/2 ≤ |Real.sin (Real.pi*((N:ℝ)+1)*t)| := by
    rw [hsin,abs_neg,abs_of_nonneg (by linarith : 0≤Real.cos v)];exact hcos
  have hbound : ((N:ℝ)+1)/(4*Real.pi) ≤ |Real.sin (Real.pi*((N:ℝ)+1)*t)/Real.sin (Real.pi*t)| := by
    rw [abs_div,abs_of_pos hsp]
    apply (le_div_iff₀ hsp).mpr
    apply le_trans _ hnum
    have hmul := mul_le_mul_of_nonneg_left hsu (show 0≤(N:ℝ)+1 by positivity)
    have hupper := mul_le_mul_of_nonneg_left hu' hpi.le
    rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<4*Real.pi)]
    nlinarith only [hmul,hupper,hpi]
  simpa only [kernel,sq_abs] using pow_le_pow_left₀ (by positivity) hbound 2

/-- A fixed subinterval of the second lobe lies inside every denominator
annulus in the first dyadic block, with a common lower bound. -/
theorem mass_lower : ∀ᶠ N : ℕ in atTop, ∀ q : ℕ, grid N<q → q≤2*grid N →
    (N:ℝ)/(24*Real.pi^2) ≤ mass N q := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/6)).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop 8,hpow.eventually_ge_atTop (4:ℝ)] with N hn hlarge q hq h2q
  change 4 ≤ (N:ℝ)^(1/6:ℝ) at hlarge
  have hN : (8:ℝ)≤N := by exact_mod_cast hn
  have hp : (0:ℝ)<N := by linarith
  have hq' : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
  have hq1 : (grid N:ℝ)≤q := by exact_mod_cast hq.le
  have hq2 : (q:ℝ)≤2*(grid N:ℝ) := by exact_mod_cast h2q
  let lo := (grid N:ℝ)/((q:ℝ)*N)
  let hi := lo*(N:ℝ)^(1/6:ℝ)
  let a := 4/(3*((N:ℝ)+1))
  let b := 5/(3*((N:ℝ)+1))
  have hden := mul_pos hq' hp
  have hlow : 1/(2*(N:ℝ)) ≤ lo := by
    apply (div_le_div_iff₀ (by positivity) hden).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hq2 hp.le]
  have hhigh : lo≤1/(N:ℝ) := by
    apply (div_le_div_iff₀ hden hp).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hq1 hp.le]
  have hlo : 0<lo := (by positivity : (0:ℝ)<1/(2*(N:ℝ))).trans_le hlow
  have hla : lo≤a := hhigh.trans ((div_le_div_iff₀ hp (by positivity : 0<3*((N:ℝ)+1))).mpr (by linarith))
  have hab : a≤b := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hbh : b≤hi := by
    have hb2 : b≤2/(N:ℝ) := (div_le_div_iff₀ (by positivity) hp).mpr (by linarith)
    apply hb2.trans
    calc
      _ = 1/(2*(N:ℝ))*4 := by ring
      _ ≤ _ := mul_le_mul hlow hlarge (by norm_num) hlo.le
  have hlt : hi<1 := by
    have hroot : (N:ℝ)^(1/6:ℝ)<(N:ℝ) := by
      have h := Real.rpow_lt_rpow_of_exponent_lt (by linarith : (1:ℝ)<N) (by norm_num : (1/6:ℝ)<1)
      simpa only [Real.rpow_one] using h
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_right hhigh (Real.rpow_nonneg hp.le _))
    rw [one_div_mul_eq_div,div_lt_one hp];exact hroot
  have hle := hla.trans (hab.trans hbh)
  have hcont : ContinuousOn (kernel N) (Set.Icc lo hi) := by
    unfold kernel
    apply ContinuousOn.pow
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht
    exact (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (hlo.trans_le ht.1))
      (by simpa only [mul_one] using mul_lt_mul_of_pos_left (ht.2.trans_lt hlt) Real.pi_pos)).ne'
  have hint : IntervalIntegrable (kernel N) volume lo hi := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hle] using hcont
  have habint : IntervalIntegrable (kernel N) volume a b :=
    hint.mono_set (by simpa only [Set.uIcc_of_le hab,Set.uIcc_of_le hle] using Set.Icc_subset_Icc hla hbh)
  let K := (((N:ℝ)+1)/(4*Real.pi))^2
  have hk : ∫ _ in a..b, K ≤ ∫ t in a..b, kernel N t := intervalIntegral.integral_mono_on hab
    intervalIntegrable_const habint (fun t ht => interior_lobe (by omega) ht.1 ht.2)
  have hfull := hk.trans (intervalIntegral.integral_mono_interval hla hab hbh
    (Eventually.of_forall fun t => sq_nonneg _) hint)
  change _ ≤ 2*∫ t in lo..hi, kernel N t
  apply le_trans _ (mul_le_mul_of_nonneg_left hfull (by norm_num : (0:ℝ)≤2))
  rw [intervalIntegral.integral_const,smul_eq_mul]
  have eqarea : 2*((b-a)*K) = ((N:ℝ)+1)/(24*Real.pi^2) := by
    dsimp [a,b,K]
    field_simp [Real.pi_ne_zero,show (N:ℝ)+1 ≠ 0 by positivity]
    ring
  rw [eqarea]
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)


/-- Candidates in a single residue class modulo 30p, indexed by consecutive integers. -/
def candidate (M L i : ℕ) := M*(L+1+i)+1
def hits (M L K q : ℕ) := (range K).filter (fun i => q ∣ candidate M L i)

theorem candidate_coprime (M L i : ℕ) : (candidate M L i).Coprime M := by
  unfold candidate
  rw [Nat.add_comm, Nat.coprime_add_mul_left_left]
  exact Nat.coprime_one_left _

/-- A divisor can hit at most one index in each interval of q consecutive indices. -/
theorem hits_count (M L K q : ℕ) (hq : 0<q) : (hits M L K q).card ≤ K/q+1 := by
  let S := hits M L K q
  have hrem {i j : ℕ} (hi : i∈S) (hj : j∈S) (hij : i≤j) : q ∣ j-i := by
    have hiq := (mem_filter.mp hi).2
    have hjq := (mem_filter.mp hj).2
    have hc : q.Coprime M := Nat.Coprime.of_dvd_left hiq (candidate_coprime ..)
    have h := Nat.dvd_sub hjq hiq
    have he : candidate M L j - candidate M L i = M*(j-i) := by
      obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hij
      simp [candidate,Nat.mul_add,add_assoc,add_comm,add_left_comm]
      omega
    rw [he] at h
    exact hc.dvd_of_dvd_mul_left h
  have hsame {i j : ℕ} (hi : i∈S) (hj : j∈S) (hij : i≤j) (hdiv : i/q=j/q) : i=j := by
    by_contra hne
    have hgap := Nat.le_of_dvd (show 0<j-i by omega) (hrem hi hj hij)
    have hiq := Nat.mod_add_div i q
    have hjq := Nat.mod_add_div j q
    rw [hdiv] at hiq
    have hmi := Nat.mod_lt i hq
    have hmj := Nat.mod_lt j hq
    omega
  have hinj : Set.InjOn (fun i => i/q) (↑S:Set ℕ) := by
    intro i hi j hj he
    rcases le_total i j with h|h
    · exact hsame hi hj h he
    · exact (hsame hj hi h he.symm).symm
  have hsub : S.image (fun i => i/q) ⊆ range (K/q+1) := by
    intro k hk
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp (mem_filter.mp hi).1).le))
  calc
    _ = (S.image (fun i => i/q)).card := (card_image_of_injOn hinj).symm
    _ ≤ (range (K/q+1)).card := card_le_card hsub
    _ = _ := card_range _

theorem hits_count_real (M L K q : ℕ) (hq : 0<q) : ((hits M L K q).card:ℝ) ≤ (K:ℝ)/q+1 := by
  have hq' : (0:ℝ)<q := by exact_mod_cast hq
  have hdiv : ((K/q:ℕ):ℝ) ≤ (K:ℝ)/q := (le_div_iff₀ hq').mpr (by exact_mod_cast Nat.div_mul_le_self K q)
  calc
    _ ≤ ((K/q:ℕ):ℝ)+1 := by exact_mod_cast hits_count M L K q hq
    _ ≤ _ := by linarith

private theorem reciprocal_square_tail (H : ℕ) :
    (∑ j ∈ range H, 1/((j:ℝ)+6)^2) ≤ 1/5-1/((H:ℝ)+5) := by
  induction H with
  | zero => norm_num
  | succ H ih =>
    rw [sum_range_succ,Nat.cast_succ]
    have hpos : (0:ℝ)<(H:ℝ)+5 := by positivity
    have hs : 1/((H:ℝ)+6)^2 ≤ 1/((H:ℝ)+5)-1/((H:ℝ)+6) := by
      field_simp
      nlinarith [Nat.cast_nonneg (α:=ℝ) H]
    rw [show ((H:ℝ)+1)+5=(H:ℝ)+6 by ring]
    linarith only [hs,ih]

theorem square_hit_budget (M L K H : ℕ) :
    (((range H).biUnion (fun j => hits M L K ((j+6)^2))).card:ℝ) ≤ (K:ℝ)/5+H := by
  have hcard := card_biUnion_le (s:=range H) (t:=fun j => hits M L K ((j+6)^2))
  calc
    _ ≤ ∑ j ∈ range H, ((hits M L K ((j+6)^2)).card:ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ j ∈ range H, ((K:ℝ)*(1/((j:ℝ)+6)^2)+1) := by
      refine sum_le_sum fun j _ => ?_
      have h := hits_count_real M L K ((j+6)^2) (by positivity)
      convert h using 1 <;> push_cast <;> ring
    _ = (K:ℝ)*(∑ j ∈ range H, 1/((j:ℝ)+6)^2)+H := by rw [sum_add_distrib,←mul_sum];simp
    _ ≤ _ := by
      have ht := (reciprocal_square_tail H).trans (sub_le_self _ (by positivity))
      linarith only [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α:=ℝ) K)]


open ErdosStraus.PrimeEstimates.Mertens

def largePrimes (y X : ℕ) := (primesUpTo (2*X)).filter fun q => y<q

/-- Across the range from y to 32y² the limiting reciprocal-prime mass is
log 2. We retain the rational upper bound 3/4. -/
theorem large_prime_reciprocals : ∀ᶠ y : ℕ in atTop, ∀ X : ℕ, 2*X ≤ 32*y^2 →
    (∑ q ∈ largePrimes y X, 1/(q:ℝ)) ≤ 3/4 := by
  obtain ⟨C,hC,hM⟩ := mertensSecond
  have hlim : Tendsto (fun y : ℕ => Real.log (y:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [eventually_ge_atTop 2,hlim.eventually_ge_atTop (100*C),
    hlim.eventually_ge_atTop (100*Real.log 32)] with y hy hCsmall h32 X hX
  let Z := 32*y^2
  have hyR : (2:ℝ)≤y := by exact_mod_cast hy
  have hy0 : (0:ℝ)<y := by linarith
  have hYZ : y ≤ Z := by dsimp [Z]; nlinarith
  have hzr : (Z:ℝ) = 32*(y:ℝ)^2 := by dsimp [Z];push_cast;rfl
  let A := Real.log (y:ℝ)
  let B := Real.log (Z:ℝ)
  have hA : 0<A := Real.log_pos (by linarith)
  have hAB : A≤B := Real.log_le_log hy0 (by exact_mod_cast hYZ)
  have hB := hA.trans_le hAB
  have hz : (2:ℝ)≤Z := by exact_mod_cast hy.trans hYZ
  have heq : B = Real.log 32 + 2*A := by
    dsimp [A,B];rw [hzr,Real.log_mul (by norm_num) (by positivity),Real.log_pow];norm_num
  have hdiff : Real.log B-Real.log A ≤ 71/100 := by
    rw [←Real.log_div hB.ne' hA.ne']
    have hb2 : 0 < B/(2*A) := by positivity
    have hfac : B/A=2*(B/(2*A)) := by ring
    rw [hfac,Real.log_mul (by norm_num : (2:ℝ)≠0) hb2.ne']
    have hl := Real.log_le_sub_one_of_pos hb2
    have hratio : B/(2*A) ≤ 201/200 := by
      apply (div_le_iff₀ (by positivity)).mpr
      change 100*Real.log 32 ≤ A at h32
      linarith
    linarith only [hl,hratio,Real.log_two_lt_d9]
  have hlow := hM (y:ℝ) hyR
  have hhigh := hM (Z:ℝ) hz
  rw [Nat.floor_natCast] at hlow hhigh
  have herr₁ : C/A ≤ 1/100 := (div_le_iff₀ hA).mpr (by linarith)
  have herr₂ : C/B ≤ 1/100 := (div_le_div_of_nonneg_left hC.le hA hAB).trans herr₁
  have hsub : largePrimes y X ⊆ primesUpTo Z \ primesUpTo y := by
    intro q hq
    obtain ⟨hi,hyq⟩ := mem_filter.mp hq
    obtain ⟨hp,hqX⟩ := mem_primesUpTo.mp hi
    exact mem_sdiff.mpr ⟨mem_primesUpTo.mpr ⟨hp,hqX.trans hX⟩,fun h => (not_le.mpr hyq) (mem_primesUpTo.mp h).2⟩
  have hsub' : primesUpTo y ⊆ primesUpTo Z := by
    intro q hq;obtain ⟨hp,hqy⟩:=mem_primesUpTo.mp hq;exact mem_primesUpTo.mpr ⟨hp,hqy.trans hYZ⟩
  calc
    _ ≤ ∑ q ∈ primesUpTo Z \ primesUpTo y, 1/(q:ℝ) := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = primeReciprocalSum Z-primeReciprocalSum y := sum_sdiff_eq_sub hsub'
    _ ≤ _ := by
      change |primeReciprocalSum y-(Real.log A+mertensSecondConstant)|≤C/A at hlow
      change |primeReciprocalSum Z-(Real.log B+mertensSecondConstant)|≤C/B at hhigh
      linarith only [(abs_le.mp hlow).1,(abs_le.mp hhigh).2,herr₁,herr₂,hdiff]

private theorem prime_count_and_root (ε : ℝ) (he : 0<ε) : ∀ᶠ z : ℕ in atTop,
    (z.primeCounting:ℝ) + Real.sqrt z + 1 ≤ ε*(z:ℝ) := by
  have hx := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hroot := Real.tendsto_sqrt_atTop.comp hx
  have hlog := Real.tendsto_log_atTop.comp hroot
  filter_upwards [eventually_ge_atTop 2,hx.eventually_ge_atTop (4/ε),hroot.eventually_ge_atTop (4/ε),
    hlog.eventually_ge_atTop (4*Real.log 4/ε)] with z h2 hz hs hl
  change 4/ε ≤ Real.sqrt (z:ℝ) at hs
  change 4*Real.log 4/ε ≤ Real.log (Real.sqrt (z:ℝ)) at hl
  have hzR : (1:ℝ)<z := by exact_mod_cast (show 1<z from h2)
  have hzp := zero_lt_one.trans hzR
  have h4 : 0<Real.log 4 := Real.log_pos (by norm_num)
  have hlogpos : 0<Real.log (Real.sqrt z) := (div_pos (by positivity : (0:ℝ)<4*Real.log 4) he).trans_le hl
  have hπ := Chebyshev.pi_le_log4_mul_div hzR
  rw [Nat.floor_natCast] at hπ
  have hn₁ : Real.log 4*(z:ℝ)/Real.log (Real.sqrt z) ≤ ε*(z:ℝ)/4 := by
    apply (div_le_iff₀ hlogpos).mpr
    have hl' := (div_le_iff₀ he).mp hl
    nlinarith only [mul_le_mul_of_nonneg_right hl' hzp.le]
  have hn₂ : Real.sqrt z ≤ ε*(z:ℝ)/4 := by
    have hs' := (div_le_iff₀ he).mp hs
    have hm := mul_le_mul_of_nonneg_right hs' (Real.sqrt_nonneg (z:ℝ))
    have hh : Real.sqrt z * (Real.sqrt z * ε) = (z:ℝ)*ε := by rw [←mul_assoc,Real.mul_self_sqrt hzp.le]
    nlinarith only [hm,hh]
  have hn₃ : (1:ℝ)≤ε*z/4 := by nlinarith only [(div_le_iff₀ he).mp hz]
  linarith only [hπ,hn₁,hn₂,hn₃]

theorem prime_error_budget (ε : ℝ) (he : 0<ε) : ∀ᶠ X : ℕ in atTop,
    ((primesUpTo (2*X)).card:ℝ) + ((2*X).sqrt:ℝ) + 1 ≤ ε*(X:ℝ) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (prime_count_and_root (ε/2) (by positivity))
  filter_upwards [eventually_ge_atTop N] with X hx
  have h := hN (2*X) (by omega)
  have hc : (primesUpTo (2*X)).card = (2*X).primeCounting := Nat.primesLE_card_eq_primeCounting _
  have hs : (((2*X).sqrt:ℕ):ℝ) ≤ Real.sqrt ((2*X:ℕ):ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' (2*X))
  rw [hc]
  exact (add_le_add (add_le_add (le_refl _) hs) (le_refl 1)).trans (h.trans_eq (by push_cast;ring))


def goodIndices (M L K y : ℕ) := (range K).filter fun i =>
  Squarefree (candidate M L i) ∧ ∀ q ∈ (candidate M L i).primeFactors, q≤y

private theorem prime_excluded {q M L i : ℕ} (hq : q.Prime) (hd : q∣M) : ¬q∣candidate M L i := by
  intro h
  have hc := Nat.Coprime.of_dvd_left h (candidate_coprime M L i)
  have hg : q.gcd M=1 := hc
  rw [Nat.gcd_eq_left hd] at hg
  exact hq.ne_one hg

private theorem candidate_bounds {M X i : ℕ} (hM : 0<M) (hi : i∈range (X/M-1)) :
    X < candidate M (X/M) i ∧ candidate M (X/M) i ≤ 2*X := by
  let L := X/M
  have hi' : i<L-1 := mem_range.mp hi
  have hdiv : M*L≤X := Nat.mul_div_le X M
  have hrem := Nat.mod_add_div X M
  have hlt := Nat.mod_lt X hM
  change X % M+M*L=X at hrem
  change X < M*(L+1+i)+1 ∧ M*(L+1+i)+1 ≤ 2*X
  constructor
  · rw [Nat.mul_add,Nat.mul_add,Nat.mul_one]
    omega
  · have hb : L+1+i+1≤L+L := by omega
    have hh := Nat.mul_le_mul_left M hb
    simp only [Nat.mul_add,Nat.mul_one] at hh ⊢
    omega

private theorem small_prime_divides_thirty {r : ℕ} (hr : r.Prime) (h : r<6) : r∣30 := by
  interval_cases r <;> norm_num at *

private theorem sieve_cover (p X y : ℕ) (hp : p.Prime) :
    let M := 30*p
    let L := X/M
    let K := L-1
    let H := (2*X).sqrt+1
    range K ⊆ goodIndices M L K y ∪ ((largePrimes y X).biUnion (hits M L K) ∪
      (range H).biUnion (fun j => hits M L K ((j+6)^2))) := by
  intro M L K H i hi
  let d := candidate M L i
  have hM : 0<M := Nat.mul_pos (by decide) hp.pos
  have hd : 0<d := Nat.succ_pos _
  have hb : d≤2*X := (candidate_bounds hM hi).2
  by_cases hs : Squarefree d
  · by_cases hy : ∀ q ∈ d.primeFactors, q≤y
    · exact mem_union_left _ (mem_filter.mpr ⟨hi,hs,hy⟩)
    · push_neg at hy
      obtain ⟨q,hq,hyq⟩ := hy
      have hq' := Nat.prime_of_mem_primeFactors hq
      have hqd := Nat.dvd_of_mem_primeFactors hq
      have hqX := (Nat.le_of_dvd hd hqd).trans hb
      have hlarge : q ∈ largePrimes y X := mem_filter.mpr ⟨mem_primesUpTo.mpr ⟨hq',hqX⟩,hyq⟩
      exact mem_union_right _ (mem_union_left _ (mem_biUnion.mpr ⟨q,hlarge,mem_filter.mpr ⟨hi,hqd⟩⟩))
  · rw [Nat.squarefree_iff_prime_squarefree] at hs
    push_neg at hs
    obtain ⟨r,hr,hrsq⟩ := hs
    have hrd : r∣d := (dvd_mul_right r r).trans hrsq
    have hr6 : 6≤r := by
      by_contra! h
      exact prime_excluded hr ((small_prime_divides_thirty hr h).trans (dvd_mul_right 30 p)) hrd
    have hroot : r≤(2*X).sqrt := Nat.le_sqrt'.mpr (by simpa [pow_two] using (Nat.le_of_dvd hd hrsq).trans hb)
    have hj : r-6 ∈ range H := mem_range.mpr (by dsimp [H];omega)
    have heq : ((r-6)+6)^2 = r*r := by rw [Nat.sub_add_cancel hr6,pow_two]
    exact mem_union_right _ (mem_union_right _ (mem_biUnion.mpr ⟨r-6,hj,mem_filter.mpr ⟨hi,heq.symm ▸ hrsq⟩⟩))

private theorem large_hit_budget (M L K y X : ℕ) :
    (((largePrimes y X).biUnion (hits M L K)).card:ℝ) ≤
      (K:ℝ)*(∑ q ∈ largePrimes y X, 1/(q:ℝ))+((primesUpTo (2*X)).card:ℝ) := by
  calc
    _ ≤ ∑ q ∈ largePrimes y X, ((hits M L K q).card:ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ∑ q ∈ largePrimes y X, ((K:ℝ)*(1/(q:ℝ))+1) := by
      refine sum_le_sum fun q hq => ?_
      have hp := (mem_primesUpTo.mp (mem_filter.mp hq).1).1.pos
      simpa only [mul_one_div] using hits_count_real M L K q hp
    _ ≤ _ := by
      rw [sum_add_distrib,←mul_sum]
      apply add_le_add (le_refl _)
      simpa using (Nat.cast_le.mpr (card_le_card (filter_subset (fun q => y<q) (primesUpTo (2*X)))) :
        ((largePrimes y X).card:ℝ) ≤ ((primesUpTo (2*X)).card:ℝ))

private theorem index_budget (p X y : ℕ) (hp : p.Prime) :
    let M := 30*p
    let L := X/M
    let K := L-1
    (K:ℝ) ≤ ((goodIndices M L K y).card:ℝ) +
      (K:ℝ)*(∑ q ∈ largePrimes y X, 1/(q:ℝ)) + (K:ℝ)/5 +
      (((primesUpTo (2*X)).card:ℝ)+((2*X).sqrt:ℝ)+1) := by
  intro M L K
  let G := goodIndices M L K y
  let A := (largePrimes y X).biUnion (hits M L K)
  let B := (range ((2*X).sqrt+1)).biUnion (fun j => hits M L K ((j+6)^2))
  have hn : K ≤ G.card+(A.card+B.card) := calc
    _ = (range K).card := (card_range K).symm
    _ ≤ (G ∪ (A ∪ B)).card := card_le_card (sieve_cover p X y hp)
    _ ≤ _ := (card_union_le ..).trans (Nat.add_le_add (Nat.le_refl _) (card_union_le ..))
  have hr : (K:ℝ) ≤ (G.card:ℝ)+((A.card:ℝ)+(B.card:ℝ)) := by exact_mod_cast hn
  have ha := large_hit_budget M L K y X
  have hb := square_hit_budget M L K ((2*X).sqrt+1)
  change (A.card:ℝ) ≤ _ at ha
  change (B.card:ℝ) ≤ _ at hb
  rw [Nat.cast_add,Nat.cast_one] at hb
  dsimp only [G] at hr
  linarith only [hr,ha,hb]

/-- A positive fraction of the central progression survives both sieves.
The square multiples use at most K/5, and primes greater than y use at most
3K/4, apart from the prime-count and square-root endpoint errors. -/
theorem many_good_indices (p : ℕ) (hp : p.Prime) : ∃ X₀ y₀ : ℕ, ∀ X ≥ X₀, ∀ y ≥ y₀,
    2*X ≤ 32*y^2 →
    (X:ℝ)/(80*(30*p:ℕ)) ≤ ((goodIndices (30*p) (X/(30*p)) (X/(30*p)-1) y).card:ℝ) := by
  let M := 30*p
  have hM : 0<M := Nat.mul_pos (by decide) hp.pos
  have hMR : (0:ℝ)<M := by exact_mod_cast hM
  obtain ⟨T,hT⟩ := eventually_atTop.mp (prime_error_budget (1/(1000*(M:ℝ))) (by positivity))
  obtain ⟨Y,hY⟩ := eventually_atTop.mp large_prime_reciprocals
  refine ⟨max T (4*M),Y,?_⟩
  intro X hX y hy hscale
  have h4 : 4*M≤X := (le_max_right T _).trans hX
  let L := X/M
  let K := L-1
  have hL : 1≤L := (Nat.le_div_iff_mul_le hM).mpr (by omega)
  have hx' : X≤M*K+2*M := by
    have hrem := Nat.mod_add_div X M
    have hsmall := Nat.mod_lt X hM
    have heq : L=K+1 := by dsimp [K];omega
    change X % M + M*L=X at hrem
    rw [heq,Nat.mul_add,Nat.mul_one] at hrem
    omega
  have hratio : (X:ℝ)/(2*(M:ℝ)) ≤ (K:ℝ) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have h₁ : 4*(M:ℝ)≤X := by exact_mod_cast h4
    have h₂ : (X:ℝ)≤(M:ℝ)*K+2*M := by exact_mod_cast hx'
    nlinarith only [h₁,h₂]
  have hcnt := index_budget p X y hp
  dsimp only at hcnt
  change (K:ℝ) ≤ ((goodIndices M L K y).card:ℝ) + (K:ℝ)*(∑ q ∈ largePrimes y X, 1/(q:ℝ)) + (K:ℝ)/5 + _ at hcnt
  have hpr := mul_le_mul_of_nonneg_left (hY y hy X hscale) (Nat.cast_nonneg (α:=ℝ) K)
  have hsmall := hT X ((le_max_left ..).trans hX)
  have hnum : (X:ℝ)/(80*(M:ℝ)) ≤ ((X:ℝ)/(2*M))/20 - (1/(1000*(M:ℝ)))*(X:ℝ) := by
    field_simp [hMR.ne'];nlinarith [Nat.cast_nonneg (α:=ℝ) X]
  exact hnum.trans (by linarith only [hcnt,hpr,hsmall,hratio])

open GoldbachDivisorBand

private theorem excluded_from_target {p y : ℕ} (hp : p.Prime) : ¬p ∣ target p y := by
  intro h
  unfold target at h
  obtain ⟨r,hr,hpr⟩ := (hp.prime.dvd_finsetProd_iff (fun k : ℕ => k)).mp h
  have hd := (mem_filter.mp hr).2
  exact hd.2 ((Nat.prime_dvd_prime_iff_eq hp hd.1).mp hpr).symm

private theorem band_count_from_indices {p y : ℕ} (hp : p.Prime) :
    let N := target p y
    let Q := grid N
    let X := Q/p
    (goodIndices (30*p) (X/(30*p)) (X/(30*p)-1) y).card ≤ (divisorsBand p N).card := by
  intro N Q X
  let M := 30*p
  let G := goodIndices M (X/M) (X/M-1) y
  let f := candidate M (X/M)
  have hM : 0<M := Nat.mul_pos (by decide) hp.pos
  have hn : 0<N := omittedProduct_pos p y
  have hinj : Set.InjOn f (↑G : Set ℕ) := by
    intro i _ j _ he
    have hm : M*(X/M+1+i) = M*(X/M+1+j) := Nat.succ.inj he
    have := Nat.eq_of_mul_eq_mul_left hM hm
    omega
  have hsub : G.image f ⊆ divisorsBand p N := by
    intro d hd
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hd
    obtain ⟨hi',hs,hsm⟩ := mem_filter.mp hi
    have hb := candidate_bounds hM hi'
    have hnop := prime_excluded (L:=X/M) (i:=i) hp (dvd_mul_left p 30)
    have hdiv : f i ∣ N := dvd_omitted_primorial hs hnop hsm
    have hlow : Q < p*f i := by
      have h := (Nat.div_lt_iff_lt_mul hp.pos).mp hb.1
      simpa [Nat.mul_comm] using h
    have hhigh : p*f i ≤ 2*Q := calc
      _ ≤ p*(2*X) := Nat.mul_le_mul_left _ hb.2
      _ = 2*(p*X) := by ring
      _ ≤ 2*Q := Nat.mul_le_mul_left _ (Nat.mul_div_le Q p)
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdiv,hn.ne'⟩,hlow,hhigh⟩
  exact (card_image_of_injOn hinj).symm.le.trans (card_le_card hsub)

private theorem final_lower (p : ℕ) (hp : p.Prime) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ y : ℕ in atTop,
      c*(target p y:ℝ) ≤ ∑ d ∈ divisorsBand p (target p y),
        (d.totient:ℝ)/(((p*d).totient:ℝ)^2)*mass (target p y) (p*d) := by
  let M := 30*p
  let δ : ℝ := 1/(160*(p:ℝ)*M)
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hM : 0<M := Nat.mul_pos (by decide) hp.pos
  have hMR : (0:ℝ)<M := by exact_mod_cast hM
  refine ⟨δ/(2*(p:ℝ)*(24*Real.pi^2)), by dsimp [δ]; positivity, ?_⟩
  obtain ⟨T,Y,hgood⟩ := many_good_indices p hp
  have hmass := (omittedProduct_tendsto p).eventually mass_lower
  filter_upwards [eventually_ge_atTop (max 1 Y),
    (tendsto_atTop.mp (bandScale_tendsto p)) (max (2*p) (T*p)),hmass] with y hy hq hm
  let N := target p y
  let Q := grid N
  let X := Q/p
  change max (2*p) (T*p) ≤ Q at hq
  change ∀ q : ℕ, Q<q → q≤2*Q → (N:ℝ)/(24*Real.pi^2) ≤ mass N q at hm
  have hqpos : 0<Q := by have := hp.pos; omega
  have hxT : T ≤ X := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
  have hxscale : 2*X ≤ 32*y^2 := (Nat.mul_le_mul_left 2 (Nat.div_le_self Q p)).trans
    (bandScale_upper p y (by omega))
  have hcnt := (hgood X hxT y (by omega) hxscale).trans
    (Nat.cast_le.mpr (band_count_from_indices (y:=y) hp))
  have hfloor : Q ≤ 2*p*X := by
    have hrem := Nat.mod_add_div Q p
    have hlt := Nat.mod_lt Q hp.pos
    have h1 : 1 ≤ X := (Nat.le_div_iff_mul_le hp.pos).mpr (by omega)
    have hle : p ≤ p*X := by simpa using Nat.mul_le_mul_left p h1
    change Q % p + p * X = Q at hrem
    rw [Nat.mul_assoc]
    omega
  have hc : δ*(Q:ℝ) ≤ ((divisorsBand p N).card:ℝ) := by
    apply le_trans _ hcnt
    change 1/(160*(p:ℝ)*M)*Q ≤ (X:ℝ)/(80*M)
    have hr : (Q:ℝ) ≤ 2*p*X := by exact_mod_cast hfloor
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hr hMR.le]
  have hsum := mass_of_band_count hp.pos hqpos (divisorsBand p N) (mass N) _ δ
    (show (0:ℝ) ≤ N/(24*Real.pi^2) by positivity) hc (by
      intro d hd
      obtain ⟨hdv,hlo,hhi⟩ := mem_filter.mp hd
      have hdiv := (Nat.mem_divisors.mp hdv).1
      have hpos := Nat.pos_of_mem_divisors hdv
      exact ⟨hpos,hp.coprime_iff_not_dvd.mpr (fun h => excluded_from_target hp (h.trans hdiv)),
        hhi,hm _ hlo hhi⟩)
  convert hsum using 1 <;> ring

end
end GoldbachOmittedPrime

theorem Conjectures.Goldbach.SkirtOmittedPrimeNegativeMass : (by
  classical
  let n := fun (p y : ℕ) => ∏ r ∈ (Finset.Icc 2 y).filter (fun r => Nat.Prime r ∧ r ≠ p), r
  let Q := fun N : ℕ => (Nat.log 2 (N+2))^2
  let mass := fun (N q : ℕ) =>
    let lo := (Q N : ℝ) / ((q:ℝ)*(N:ℝ))
    2 * intervalIntegral (fun t : ℝ => (Real.sin (Real.pi*((N:ℝ)+1)*t) / Real.sin (Real.pi*t))^2) lo (lo*(N:ℝ)^((1:ℝ)/6)) MeasureTheory.volume
  exact ∀ p : ℕ, Nat.Prime p → 3 ≤ p → ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y →
    let N := n p y
    let D := N.divisors.filter (fun d => Q N < p*d ∧ p*d ≤ 2*Q N)
    c*(N:ℝ) ≤ ∑ d ∈ D, ((d.totient:ℝ)/(((p*d).totient:ℝ)^2)) * mass N (p*d)) := by
  classical
  dsimp only
  intro p hp _
  obtain ⟨c,hc,h⟩ := GoldbachOmittedPrime.final_lower p hp
  exact ⟨c,hc,Filter.eventually_atTop.mp h⟩
