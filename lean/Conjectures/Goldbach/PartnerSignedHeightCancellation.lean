import Mathlib
import Conjectures.Goldbach.PartnerPrincipalRowPhase

/-!
Order the primitive partners by conductor. Orthogonality, together with
the verified principal-row phase, gives a signed multiplicative coefficient
at each squarefree conductor. Two distinct prime divisors of m − 1 each
have coefficient −1. Removing them makes the height sum a double finite
difference of the remaining summatory function.

The remaining coefficients are the Dirichlet convolution of 1/n with an
absolutely summable correction. The double finite difference of the harmonic
numbers is bounded and tends to zero, allowing passage to the limit.

The phase identity comes from PR #4355. The estimates for the arithmetic
correction adapt the GoldbachGrahamDiagonal divisor-series argument in
Conjectures.Goldbach.FixedModulusZeroClassSquare.
-/

namespace SignedHeight
open Finset
noncomputable def c (m p : ℕ) : ℝ :=
  if p ∣ m then 0 else if p ∣ m-1 then -1 else 1/((p:ℝ)-2)

noncomputable def raw (m n : ℕ) : ℝ :=
  if Squarefree n then ∏ p ∈ n.primeFactors, c m p else 0
end SignedHeight

namespace SignedHeight
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct
open scoped Classical

noncomputable def row (s : ℕ) : Finset (DirichletCharacter ℂ s) :=
  if h : s ≠ 0 then
    let _ : NeZero s := ⟨h⟩
    univ.filter DirichletCharacter.IsPrimitive
  else ∅

private noncomputable def phaseSum (m s : ℕ) : ℂ :=
  ∑ β ∈ row s, β (m : ZMod s)

set_option maxHeartbeats 650000 in
private theorem phaseSum_divisors (m s : ℕ) [NeZero s] (hc : s.Coprime m) :
    ∑ d ∈ s.divisors, phaseSum m d = if (m:ZMod s) = 1 then (s.totient:ℂ) else 0 := by
  let A := DirichletCharacter ℂ s
  have maps (χ : A) (_ : χ ∈ (univ : Finset A)) : χ.conductor ∈ s.divisors :=
    Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne s⟩
  have inner (d : ℕ) (hd : d ∈ s.divisors) :
      phaseSum m d = ∑ χ ∈ (univ : Finset A) with χ.conductor = d, χ (m:ZMod s) := by
    have hds := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := by rintro rfl; exact NeZero.ne s (Nat.zero_dvd.mp hds)
    let _ : NeZero d := ⟨hd0⟩
    have himg : (row d).image (changeLevel hds) =
        (univ : Finset A).filter (fun χ => χ.conductor = d) := by
      ext χ
      constructor
      · rintro h
        obtain ⟨β,hβ,rfl⟩ := mem_image.mp h
        have hp : β.IsPrimitive := by simpa [row,hd0] using hβ
        exact mem_filter.mpr ⟨mem_univ _,(conductor_changeLevel β hds).trans hp⟩
      · intro hχ
        have he := (mem_filter.mp hχ).2
        subst d
        exact mem_image.mpr ⟨χ.primitiveCharacter, by simpa [row,χ.conductor_ne_zero] using
          χ.primitiveCharacter_isPrimitive, changeLevel_primitiveCharacter χ⟩
    rw [← himg,sum_image (changeLevel_injective hds).injOn]
    unfold phaseSum
    apply sum_congr rfl
    intro β _
    have hcop : IsCoprime (m:ℤ) (s:ℤ) := by
      exact_mod_cast (Nat.isCoprime_iff_coprime.mpr hc.symm)
    simpa using (changeLevel_eq_cast_of_dvd' β hds hcop).symm
  simp_rw [sum_congr rfl inner, sum_fiberwise_of_maps_to maps]
  exact sum_characters_eq ℂ _

private def primePhase (m p : ℕ) : ℂ := if p ∣ m-1 then (p:ℂ)-2 else -1
private def phaseProduct (m s : ℕ) : ℂ := ∏ p ∈ s.primeFactors, primePhase m p

private theorem divisor_expand (s : ℕ) (hs : Squarefree s) (f : ℕ → ℂ) :
    (∑ d ∈ s.divisors, ∏ p ∈ d.primeFactors, f p) = ∏ p ∈ s.primeFactors, (f p+1) := by
  rw [← Nat.divisors_filter_squarefree_of_squarefree hs,
    Nat.sum_divisors_filter_squarefree hs.ne_zero, Nat.factors_eq, prod_add_one]
  apply sum_congr rfl
  intro t ht
  rw [t.prod_val,Function.id_def, Nat.primeFactors_prod (fun p hp =>
    Nat.prime_of_mem_primeFactors ((mem_powerset.mp ht) hp))]

private theorem phaseProduct_divisors (m s : ℕ) [NeZero s] (hm : 0 < m) (hs : Squarefree s) :
    ∑ d ∈ s.divisors, phaseProduct m d = if (m:ZMod s) = 1 then (s.totient:ℂ) else 0 := by
  unfold phaseProduct
  rw [divisor_expand s hs]
  have one_iff : (m:ZMod s)=1 ↔ s ∣ m-1 := by
    rw [← sub_eq_zero, ← ZMod.natCast_eq_zero_iff, Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one]
  simp only [one_iff]
  by_cases hd : s ∣ m-1
  · rw [ite_eq_left hd]
    have hφ : s.totient = ∏ p ∈ s.primeFactors, (p-1) := by
      have h := Nat.totient_mul_prod_primeFactors s
      rw [Nat.prod_primeFactors_of_squarefree hs, mul_comm s] at h
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hs.ne_zero) h
    rw [hφ, Nat.cast_prod]
    apply prod_congr rfl
    intro p hp
    have hd' := (Nat.dvd_of_mem_primeFactors hp).trans hd
    simp only [primePhase,ite_eq_left hd',Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le,Nat.cast_one]
    ring
  · rw [ite_eq_right hd]
    have bad : ∃ p ∈ s.primeFactors, ¬p ∣ m-1 := by
      by_contra! h
      have hn : m-1 ≠ 0 := by rintro hz; simp [hz] at hd
      have sub : s.primeFactors ⊆ (m-1).primeFactors :=
        fun p hp => Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp,h p hp,hn⟩
      apply hd
      rw [← Nat.prod_primeFactors_of_squarefree hs]
      exact (Finset.prod_dvd_prod_of_subset _ _ _ sub).trans (Nat.prod_primeFactors_dvd _)
    obtain ⟨p,hp,hpn⟩ := bad
    exact prod_eq_zero hp (by simp [primePhase,hpn])

private theorem phaseSum_eq (m s : ℕ) (hm : 0 < m) (hs : Squarefree s) (hc : s.Coprime m) :
    phaseSum m s = phaseProduct m s := by
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    let _ : NeZero s := ⟨hs.ne_zero⟩
    have total := (phaseSum_divisors m s hc).trans (phaseProduct_divisors m s hm hs).symm
    have er : ∑ d ∈ s.divisors.erase s, phaseSum m d =
        ∑ d ∈ s.divisors.erase s, phaseProduct m d := by
      apply sum_congr rfl
      intro d hd
      have dd := Nat.dvd_of_mem_divisors (mem_erase.mp hd).2
      exact ih d (lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hs.ne_zero) dd) (mem_erase.mp hd).1)
        (hs.squarefree_of_dvd dd) (Nat.Coprime.of_dvd_left dd hc)
    have ht : s ∈ s.divisors := Nat.mem_divisors.mpr ⟨dvd_refl s,hs.ne_zero⟩
    rw [← sum_erase_add _ _ ht, ← sum_erase_add _ _ ht, er] at total
    exact add_left_cancel total

theorem level_sum (m s : ℕ) [NeZero s] (hm : 0 < m) (he : Even m) :
    (∑ β ∈ row s, series (1 : DirichletCharacter ℂ 1) β m) =
      series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m * (raw m s : ℂ) := by
  let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  have hrow (β : DirichletCharacter ℂ s) (hβ : β ∈ row s) : β.IsPrimitive := by
    simpa [row,NeZero.ne s] using hβ
  have formula (β : DirichletCharacter ℂ s) (hβ : β ∈ row s) :=
    PartnerPrincipalRowPhaseProof.main_theorem s β (hrow β hβ) m hm he
  by_cases good : Squarefree s ∧ s.Coprime m
  · have no (p : ℕ) (hp : p ∈ s.primeFactors) : ¬p ∣ m :=
      (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp)).mp
        (Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_primeFactors hp) good.2)
    have term (p : ℕ) (hp : p ∈ s.primeFactors) :
        (-1:ℂ) * primePhase m p / ((p:ℂ)-2) = (c m p : ℂ) := by
      have p2 : p ≠ 2 := by
        rintro rfl
        exact no 2 hp (even_iff_two_dvd.mp he)
      have hn : (p:ℂ)-2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast p2)
      by_cases hp1 : p ∣ m-1
      · simp [c,primePhase,no p hp,hp1]
        field_simp
        ring
      · simp [c,primePhase,no p hp,hp1]
    let D := ∏ p ∈ s.primeFactors, ((p:ℂ)-2)
    let sign := (-1:ℂ)^s.primeFactors.card
    calc
      _ = ∑ β ∈ row s, (O*sign/D) * β (m:ZMod s) := by
        apply sum_congr rfl
        intro β hβ
        rw [formula β hβ, ite_eq_left good]
        dsimp only [O,sign,D]
        ring
      _ = O*(sign*phaseProduct m s/D) := by
        rw [← mul_sum]
        change O*sign/D*phaseSum m s = _
        rw [phaseSum_eq m s hm good.1 good.2]
        ring
      _ = O*∏ p ∈ s.primeFactors, ((-1:ℂ)*primePhase m p/((p:ℂ)-2)) := by
        rw [prod_div_distrib,prod_mul_distrib,prod_const]
        rfl
      _ = _ := by
        rw [raw,ite_eq_left good.1, Complex.ofReal_prod]
        exact congrArg (O * ·) (prod_congr rfl term)
  · have hraw : raw m s = 0 := by
      by_cases sq : Squarefree s
      · have hc : ¬ s.Coprime m := fun h => good ⟨sq,h⟩
        obtain ⟨p,hp,hps,hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
        rw [raw,ite_eq_left sq]
        exact prod_eq_zero (Nat.mem_primeFactors.mpr ⟨hp,hps,NeZero.ne s⟩) (by simp [c,hpm])
      · simp [raw,sq]
    rw [hraw,Complex.ofReal_zero,mul_zero]
    exact sum_eq_zero fun β hβ => (formula β hβ).trans (ite_eq_right good)

end SignedHeight

namespace HeightCorr

open ArithmeticFunction Finset Filter
open scoped ArithmeticFunction Moebius
noncomputable section

def localCoeff (m p q r : ℕ) : ℝ :=
  if r ∣ m ∨ r=p ∨ r=q then 0 else if r ∣ m-1 then -1 else 1/((r:ℝ)-2)

def harmonic : ArithmeticFunction ℝ :=
  (ArithmeticFunction.zeta : ArithmeticFunction ℝ).pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ)

theorem harmonic_apply (n : ℕ) : harmonic n = (n:ℝ)⁻¹ := by
  by_cases h : n = 0
  · simp [h]
  · simp [harmonic, zeta_apply_ne h, id_apply, one_div]

private def mob : ArithmeticFunction ℝ :=
  (μ : ArithmeticFunction ℝ).pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ)

private def flat (c : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ((μ : ArithmeticFunction ℝ).ppow 2).pmul (prodPrimeFactors c)

private def corr (c : ℕ → ℝ) := flat c * mob

private theorem mob_apply (n : ℕ) : mob n = (moebius n:ℝ)/(n:ℝ) := by simp [mob,id_apply]

private theorem flat_apply (c : ℕ → ℝ) (n : ℕ) :
    flat c n = if Squarefree n then ∏ r ∈ n.primeFactors, c r else 0 := by
  by_cases hn : n=0
  · simp [hn]
  rw [flat, pmul_apply, ppow_apply (by decide : 0 < 2), intCoe_apply, prodPrimeFactors_apply hn]
  by_cases hs : Squarefree n
  · rw [ite_eq_left hs, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree hs, Int.cast_one, one_mul]
  · rw [ite_eq_right hs, moebius_eq_zero_of_not_squarefree hs]; norm_num

private theorem corr_mult (c : ℕ → ℝ) : (corr c).IsMultiplicative := by
  have hμ : (μ : ArithmeticFunction ℝ).IsMultiplicative := isMultiplicative_moebius.intCast
  exact ((hμ.ppow (k:=2)).pmul (IsMultiplicative.prodPrimeFactors c)).mul
    (hμ.pdiv isMultiplicative_id.natCast)

-- The convolution with μ(n)/n and its prime-power evaluation follow the
-- construction in GoldbachGrahamDiagonal, FixedModulusZeroClassSquare.lean.
private theorem distrib_div (f g : ArithmeticFunction ℝ) :
    f.pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ) *
      g.pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ) =
      (f*g).pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ) := by
  ext n
  rw [ArithmeticFunction.mul_apply,pdiv_apply,ArithmeticFunction.mul_apply,sum_div]
  apply sum_congr rfl
  intro m hm
  have h := (Nat.mem_divisorsAntidiagonal.mp hm).1
  simp only [pdiv_apply,natCoe_apply,id_apply,div_mul_div_comm]
  rw [← Nat.cast_mul,h]

private theorem conv_flat (c : ℕ → ℝ) : flat c = harmonic * corr c := by
  have hi : harmonic * mob = 1 := by
    rw [harmonic,mob,distrib_div,coe_zeta_mul_coe_moebius]
    ext n
    by_cases hn : n=1
    · simp [hn,id_apply]
    · simp [ArithmeticFunction.one_apply_ne hn]
  rw [corr, mul_left_comm, hi, mul_one]

private theorem prime_convolution (f g : ArithmeticFunction ℝ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    (f*g) (p^k)=∑ i ∈ range (k+1),f (p^i)*g (p^(k-i)) := by
  classical
  let e : ℕ ↪ ℕ := ⟨(p^·),Nat.pow_right_injective hp.one_lt⟩
  have he : (antidiagonal k).map (e.prodMap e) = (p^k).divisorsAntidiagonal := by
    apply le_antisymm (Nat.antidiagonal_map_subset_divisorsAntidiagonal_pow hp.one_lt k)
    intro m hm
    obtain ⟨hmul,_⟩ := Nat.mem_divisorsAntidiagonal.mp hm
    obtain ⟨i,hi,he1⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro m.2 hmul)
    obtain ⟨j,hj,he2⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro_left m.1 hmul)
    have hk : i+j=k := (Nat.pow_right_injective hp.one_lt) (by
      change p^(i+j)=p^k; rw [pow_add,← he1,← he2,hmul])
    exact mem_map.mpr ⟨(i,j),mem_antidiagonal.mpr hk,Prod.ext he1.symm he2.symm⟩
  rw [ArithmeticFunction.mul_apply,← he,sum_map,Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

private theorem local_values (c : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    corr c (p^k) =
      if k=0 then 1 else if k=1 then c p-1/(p:ℝ)
        else if k=2 then -(c p/(p:ℝ)) else 0 := by
  have h1f : flat c 1 = 1 := by simp [flat_apply]
  have h1g : mob 1 = 1 := by simp [mob_apply]
  have hpf : flat c p = c p := by simp [flat_apply, hp.squarefree, hp.primeFactors]
  have hpg : mob p = -1/(p:ℝ) := by simp [mob_apply,moebius_apply_prime hp]
  have hlf (j : ℕ) (hj : 2 ≤ j) : flat c (p^j) = 0 := by
    rw [flat_apply, ite_eq_right]
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; omega
  have hlg (j : ℕ) (hj : 2 ≤ j) : mob (p^j) = 0 := by
    simp [mob_apply,moebius_apply_prime_pow hp (by omega : j ≠ 0), show j ≠ 1 by omega]
  rw [corr, prime_convolution _ _ hp]
  rcases k with _|_|_|k
  · simp [h1f,h1g]
  · norm_num [sum_range_succ,hpf,hpg,h1f,h1g]
    ring
  · norm_num [sum_range_succ,hpf,hpg,h1f,h1g,hlf 2 (by decide),hlg 2 (by decide)]
    ring
  · simp only [Nat.succ_ne_zero]
    apply sum_eq_zero
    intro i _
    by_cases h : 2 ≤ i
    · rw [hlf _ h, zero_mul]
    · rw [hlg _ (by omega), mul_zero]

private def extra (c : ℕ → ℝ) (r : ℕ) : ℝ := |c r - 1/(r:ℝ)| + |c r/(r:ℝ)|

private theorem summable_extra (m p q : ℕ) (hm : 0 < m) (he : Even m) :
    Summable (extra (localCoeff m p q)) := by
  have hm1 : 0 < m-1 := by obtain ⟨b,hb⟩ := he; omega
  have hsum := (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).mul_left 6
  refine hsum.of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_gt_atTop (m+p+q+4)] with r hr
  have hdm : ¬r ∣ m := fun h => (by omega : ¬ r ≤ m) (Nat.le_of_dvd hm h)
  have hd1 : ¬r ∣ m-1 := fun h => (by omega : ¬ r ≤ m-1) (Nat.le_of_dvd hm1 h)
  have hc : localCoeff m p q r = 1/((r:ℝ)-2) := by
    simp [localCoeff, hdm, hd1, show r ≠ p by omega, show r ≠ q by omega]
  have h4 : (4:ℝ) ≤ r := by exact_mod_cast (by omega : 4 ≤ r)
  have hp : 0 < (r:ℝ) := by linarith
  have hp2 : 0 < (r:ℝ)-2 := by linarith
  have hsub : 1/((r:ℝ)-2)-1/(r:ℝ) = 2/((r:ℝ)*((r:ℝ)-2)) := by
    field_simp; ring
  have hdiv : 1/((r:ℝ)-2)/(r:ℝ) = 1/((r:ℝ)*((r:ℝ)-2)) := by
    field_simp
  simp only [extra, hc, hsub, hdiv, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2/((r:ℝ)*((r:ℝ)-2))),
    abs_of_pos (by positivity : 0 < 1/((r:ℝ)*((r:ℝ)-2))), abs_of_nonneg (by positivity : 0 ≤ 2/((r:ℝ)*((r:ℝ)-2))+1/((r:ℝ)*((r:ℝ)-2)))]
  field_simp
  nlinarith [mul_nonneg hp.le (show 0 ≤ (r:ℝ)-4 by linarith)]

private theorem summable_corr_of_local (c : ℕ → ℝ) (h : Summable (extra c)) :
    Summable (fun n : ℕ => |corr c n|) := by
  classical
  let f (n : ℕ) := |corr c n|
  have hf (n : ℕ) : 0 ≤ f n := abs_nonneg _
  have h1 : f 1 = 1 := by simp [f,(corr_mult c).map_one]
  have hmul {m n : ℕ} (hmn : m.Coprime n) : f (m*n)=f m*f n := by
    simp only [f,(corr_mult c).map_mul_of_coprime hmn,abs_mul]
  have hvanish {p : ℕ} (hp : p.Prime) (k : ℕ) (hK : k ∉ range 3) : f (p^k)=0 := by
    have hk : 3 ≤ k := by simpa only [mem_range, not_lt] using hK
    simp [f,local_values c hp, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
  have hS {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => ‖f (p^k)‖) := by
    apply summable_of_ne_finset_zero (s:=range 3)
    intro k hk
    rw [hvanish hp k hk, norm_zero]
  have hval {p : ℕ} (hp : p.Prime) : (∑' k : ℕ, f (p^k)) = 1+extra c p := by
    rw [tsum_eq_sum (hvanish hp)]
    simp [sum_range_succ, f, local_values c hp, extra]
    ring
  apply summable_of_sum_range_le (c:=Real.exp (∑' r, extra c r)) hf
  intro N
  obtain ⟨_,hT⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum h1 hmul hS N
  have hTS : Summable (fun m : N.smoothNumbers => f m) := hT.summable
  let A := (range N).filter (fun n => n≠0)
  let e : {n : ℕ // n∈A} ↪ N.smoothNumbers :=
    ⟨fun n => ⟨n.val,Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero (mem_filter.mp n.property).2)
          (mem_range.mp (mem_filter.mp n.property).1)⟩,
      fun a b hab => Subtype.ext (congrArg (fun n : N.smoothNumbers => n.val) hab)⟩
  calc
    ∑ n ∈ range N, f n = ∑ n ∈ A, f n := by
      symm
      apply sum_subset (filter_subset _ _)
      intro n hn hn'
      have hn0 : n=0 := by by_contra hn0; exact hn' (mem_filter.mpr ⟨hn,hn0⟩)
      simp [f, hn0]
    _ = ∑ n : {n : ℕ // n∈A}, f n.val := (sum_subtype A (fun _ => Iff.rfl) f)
    _ = ∑ n ∈ (univ : Finset {n : ℕ // n∈A}).map e, f n := by rw [sum_map]; rfl
    _ ≤ ∑' n : N.smoothNumbers, f n := hTS.sum_le_tsum _ (fun _ _ => hf _)
    _ = _ := hT.tsum_eq
    _ ≤ ∏ p ∈ N.primesBelow, Real.exp (extra c p) := by
      apply prod_le_prod₀ (fun _ _ => tsum_nonneg (fun k => hf _))
      intro p hp
      rw [hval (Nat.mem_primesBelow.mp hp).2]
      linarith [Real.add_one_le_exp (extra c p)]
    _ = Real.exp (∑ p ∈ N.primesBelow, extra c p) := (Real.exp_sum _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (h.sum_le_tsum _ (fun r _ => add_nonneg (abs_nonneg _) (abs_nonneg _)))

theorem exists_correction (m p q : ℕ) (hm : 0 < m) (he : Even m) :
    ∃ g : ArithmeticFunction ℝ, Summable (fun n => |g n|) ∧ ∀ n,
      (if Squarefree n then ∏ r ∈ n.primeFactors, localCoeff m p q r else 0) = (harmonic * g) n := by
  let c := localCoeff m p q
  refine ⟨corr c, summable_corr_of_local c (summable_extra m p q hm he), ?_⟩
  intro n
  rw [← conv_flat, flat_apply]

end
end HeightCorr

namespace HeightHarmonic
open Filter Finset
open scoped Topology

private noncomputable def H (n : ℕ) : ℝ := harmonic n

private theorem H_mono : Monotone H := by
  apply monotone_nat_of_le_succ
  intro n
  simp [H, harmonic_succ]
  positivity

private noncomputable def first (p n : ℕ) := H n - H (n/p)

/-- The double finite difference of the harmonic summatory function. -/
noncomputable def kernel (p q n : ℕ) : ℝ :=
  (harmonic n : ℝ) - harmonic (n/p) - harmonic (n/q) + harmonic (n/(p*q))

private theorem kernel_eq (p q n : ℕ) : kernel p q n = first p n - first p (n/q) := by
  simp only [kernel, first, H, Nat.div_div_eq_div_mul, Nat.mul_comm q p]
  ring

private theorem first_bounds (p n : ℕ) (hp : 0 < p) :
    0 ≤ first p n ∧ first p n ≤ 1 + Real.log (p:ℝ) := by
  refine ⟨sub_nonneg.mpr (H_mono (Nat.div_le_self n p)), ?_⟩
  by_cases hz : n=0
  · subst n
    have := Real.log_nonneg (show (1:ℝ) ≤ p by exact_mod_cast hp)
    simp [first,H]; linarith
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hz
  have hdiv : n < (n/p+1)*p := (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
  have hlog := Real.log_le_log hn (show (n:ℝ) ≤ ((n/p+1:ℕ):ℝ)*(p:ℝ) by exact_mod_cast hdiv.le)
  rw [Real.log_mul (by positivity) (by exact_mod_cast hp.ne')] at hlog
  change (harmonic n : ℝ) - harmonic (n/p) ≤ _
  linarith [harmonic_le_one_add_log n, log_add_one_le_harmonic (n/p)]

private theorem first_limit (p : ℕ) (hp : 0 < p) :
    Tendsto (first p) atTop (𝓝 (Real.log p)) := by
  have edges (j : ℕ)
      (herr : Tendsto (fun k : ℕ => H k - Real.log (k+j:ℕ)) atTop (𝓝 Real.eulerMascheroniConstant)) :
      Tendsto (fun k : ℕ => H (p*(k+j)) - H k) atTop (𝓝 (Real.log p)) := by
    have hm : Tendsto (fun k : ℕ => p*(k+j)) atTop atTop := by
      apply tendsto_atTop_mono (f := fun k : ℕ => k) _ tendsto_id
      intro k
      exact (Nat.le_add_right k j).trans (Nat.le_mul_of_pos_left _ hp)
    have lim : Tendsto (fun k : ℕ => (H (p*(k+j)) - Real.log (p*(k+j):ℕ)) -
        (H k - Real.log (k+j:ℕ)) + Real.log p) atTop (𝓝 (Real.log p)) := by
      simpa only [H, Function.comp_apply, sub_self,zero_add] using
        (((Real.tendsto_harmonic_sub_log.comp hm).sub herr).add_const (Real.log p))
    apply lim.congr'
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne') (by positivity)]
    ring
  have lo := edges 0 (by simpa [H] using Real.tendsto_harmonic_sub_log)
  have hi := edges 1 (by simpa [H] using Real.tendsto_harmonic_sub_log_add_one)
  have divlim := Nat.tendsto_div_const_atTop hp.ne'
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (lo.comp divlim) (hi.comp divlim)
  · intro n
    apply sub_le_sub_right
    apply H_mono
    simpa [Nat.mul_comm] using Nat.div_mul_le_self n p
  · intro n
    apply sub_le_sub_right
    apply H_mono
    simpa [Nat.mul_comm] using ((Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self (n/p))).le

theorem kernel_limit (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    Tendsto (kernel p q) atTop (𝓝 0) := by
  have h := first_limit p hp
  change Tendsto (fun n => kernel p q n) atTop (𝓝 0)
  simpa only [kernel_eq,Function.comp_def,sub_self] using h.sub (h.comp (Nat.tendsto_div_const_atTop hq.ne'))

theorem kernel_abs_le (p q n : ℕ) (hp : 0 < p) :
    |kernel p q n| ≤ 1 + Real.log (p:ℝ) := by
  rw [kernel_eq,abs_le]
  obtain ⟨ha,hb⟩ := first_bounds p n hp
  obtain ⟨hc,hd⟩ := first_bounds p (n/q) hp
  constructor <;> linarith

theorem weighted_tsum_limit (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (g : ℕ → ℝ)
    (hg : Summable (fun d => |g d|)) :
    Tendsto (fun Y : ℕ => ∑' d, g d * kernel p q (Y/d)) atTop (𝓝 0) := by
  have lim (d : ℕ) : Tendsto (fun Y : ℕ => g d * kernel p q (Y/d)) atTop (𝓝 0) := by
    by_cases hd : d=0
    · subst d; simp [kernel]
    · simpa only [Function.comp_apply, mul_zero] using
        ((kernel_limit p q hp hq).comp (Nat.tendsto_div_const_atTop hd)).const_mul (g d)
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun Y d : ℕ => g d * kernel p q (Y/d)) (g := fun _ : ℕ => (0:ℝ))
    (hg.mul_right (1+Real.log (p:ℝ))) lim (Eventually.of_forall fun Y d => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul_of_nonneg_left (kernel_abs_le p q (Y/d) hp) (abs_nonneg _))
  simpa only [tsum_zero] using h

theorem weighted_limit (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (g : ℕ → ℝ)
    (hg : Summable (fun d => |g d|)) :
    Tendsto (fun Y : ℕ => ∑ d ∈ Icc 1 Y, g d * kernel p q (Y/d)) atTop (𝓝 0) := by
  apply (weighted_tsum_limit p q hp hq g hg).congr
  intro Y
  apply tsum_eq_sum
  intro d hd
  by_cases dz : d=0
  · subst d; simp [kernel]
  · have hlt : Y<d := by simpa [mem_Icc, Nat.one_le_iff_ne_zero.mpr dz] using hd
    simp [Nat.div_eq_of_lt hlt,kernel]

end HeightHarmonic

namespace SignedHeight
open Finset

private noncomputable def sf (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  if Squarefree n then ∏ l ∈ n.primeFactors, c l else 0
private def mask (p : ℕ) (c : ℕ → ℝ) (l : ℕ) := if l=p then 0 else c l

private theorem mask_off (p n : ℕ) (c : ℕ → ℝ) (h : ¬ p ∣ n) :
    sf (mask p c) n = sf c n := by
  unfold sf
  split_ifs
  · apply prod_congr rfl
    intro l hl
    have he : l ≠ p := by rintro rfl; exact h (Nat.dvd_of_mem_primeFactors hl)
    simp [mask, he]
  · rfl

private theorem mask_on {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) (n : ℕ) (h : p ∣ n) :
    sf (mask p c) n = 0 := by
  by_cases hn : n=0
  · simp [hn,sf]
  unfold sf
  split_ifs with hs
  · apply prod_eq_zero (i := p) (Nat.mem_primeFactors.mpr ⟨hp,h,hn⟩)
    simp [mask]
  · rfl

private theorem peel_point {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) (hc : c p = -1) (n : ℕ) :
    sf c n = sf (mask p c) n - if p ∣ n then sf (mask p c) (n/p) else 0 := by
  by_cases hd : p ∣ n
  · obtain ⟨k, rfl⟩ := hd
    rw [mask_on hp c _ (dvd_mul_right _ _), ite_eq_left (dvd_mul_right p k),
      Nat.mul_div_cancel_left _ hp.pos, zero_sub]
    by_cases hh : p ∣ k
    · rw [mask_on hp c k hh, neg_zero]
      have hsf : ¬ Squarefree (p*k) := fun h => (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul h)) hh
      simp [sf, hsf]
    · rw [mask_off p k c hh]
      have hk : k ≠ 0 := by rintro rfl; exact hh (dvd_zero _)
      have hcop := hp.coprime_iff_not_dvd.mpr hh
      by_cases hs : Squarefree k
      · have hs' := (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree,hs⟩
        have notmem : p ∉ k.primeFactors := fun h => hh (Nat.dvd_of_mem_primeFactors h)
        simp [sf, hs', hs, Nat.primeFactors_mul hp.ne_zero hk, hp.primeFactors, notmem, hc]
      · have hs' : ¬ Squarefree (p*k) := fun h => hs h.of_mul_right
        simp [sf, hs', hs]
  · simp [hd,mask_off p n c hd]

private theorem multiples_sum (p : ℕ) (hp : 0 < p) (Y : ℕ) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 Y, if p ∣ n then f (n/p) else 0) = ∑ k ∈ Icc 1 (Y/p), f k := by
  rw [← sum_filter]
  symm
  apply sum_bij (fun k _ => p*k)
  · intro k hk
    obtain ⟨h1,h2⟩ := mem_Icc.mp hk
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hp h1, by
      simpa only [mul_comm p] using (Nat.le_div_iff_mul_le hp).mp h2⟩, dvd_mul_right _ _⟩
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hp h
  · intro n hn
    obtain ⟨hab,k,rfl⟩ := mem_filter.mp hn
    refine ⟨k,mem_Icc.mpr ⟨?_,(Nat.le_div_iff_mul_le hp).mpr ?_⟩,rfl⟩
    · by_contra! h
      have : k=0 := by omega
      simpa [this] using (mem_Icc.mp hab).1
    · simpa [Nat.mul_comm] using (mem_Icc.mp hab).2
  · intro k _
    simp [Nat.mul_div_cancel_left _ hp]

private def part (f : ℕ → ℝ) (Y : ℕ) := ∑ n ∈ Icc 1 Y, f n

private theorem peel_sum {p : ℕ} (hp : p.Prime) (c : ℕ → ℝ) (hc : c p = -1) (Y : ℕ) :
    part (sf c) Y = part (sf (mask p c)) Y - part (sf (mask p c)) (Y/p) := by
  unfold part
  conv_lhs => arg 2; ext n; rw [peel_point hp c hc n]
  rw [sum_sub_distrib,multiples_sum p hp.pos]

private theorem peel_two {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (c : ℕ → ℝ) (hcp : c p = -1) (hcq : c q = -1) (Y : ℕ) :
    let b := sf (mask q (mask p c))
    part (sf c) Y = part b Y - part b (Y/p) - part b (Y/q) + part b (Y/(p*q)) := by
  intro b
  have eq : mask p c q = -1 := by simp [mask,hne.symm,hcq]
  rw [peel_sum hp c hcp,peel_sum hq _ eq,peel_sum hq _ eq,Nat.div_div_eq_div_mul]
  dsimp only [b]
  ring

end SignedHeight

namespace SignedHeight
open Finset

private theorem partial_convolution (H g : ArithmeticFunction ℝ) (hH : ∀ n : ℕ, H n = (n:ℝ)⁻¹)
    (Y : ℕ) :
    part (fun n => (H*g) n) Y = ∑ d ∈ Icc 1 Y, g d * (harmonic (Y/d) : ℝ) := by
  classical
  have fiber (n : ℕ) (hn : n ∈ Icc 1 Y) :
      (H*g) n = ∑ d ∈ Icc 1 Y, if d ∣ n then g d * ((n/d : ℕ):ℝ)⁻¹ else 0 := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => H a * g b)]
    have he : (Icc 1 Y).filter (fun d => d ∣ n) = n.divisors := by
      ext d
      obtain ⟨hn0,hnY⟩ := mem_Icc.mp hn
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨_,hd⟩
        exact ⟨hd,by omega⟩
      · rintro ⟨hd,_⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn0,(Nat.le_of_dvd hn0 hd).trans hnY⟩,hd⟩
    rw [← sum_filter,he]
    exact sum_congr rfl fun d _ => by rw [hH, mul_comm]
  unfold part
  rw [sum_congr rfl fiber, sum_comm]
  apply sum_congr rfl
  intro d hd
  have hcalc := multiples_sum d (mem_Icc.mp hd).1 Y (fun k => g d * (k:ℝ)⁻¹)
  rw [hcalc,← mul_sum,harmonic_eq_sum_Icc]
  push_cast
  rfl

private theorem extend_partial (g : ℕ → ℝ) (Y d : ℕ) :
    (∑ n ∈ Icc 1 (Y/d), g n*(harmonic ((Y/d)/n):ℝ)) =
      ∑ n ∈ Icc 1 Y, g n*(harmonic ((Y/n)/d):ℝ) := by
  have rearrange (n : ℕ) : (Y/d)/n = (Y/n)/d := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.mul_comm]
  simp_rw [← rearrange]
  apply sum_subset (Icc_subset_Icc_right (Nat.div_le_self _ _))
  intro n hn hnot
  have le := (mem_Icc.mp hn).1
  have lt : Y/d < n := by
    by_contra! hn'
    exact hnot (mem_Icc.mpr ⟨le,hn'⟩)
  simp [Nat.div_eq_of_lt lt, harmonic]

private theorem double_sum (g : ArithmeticFunction ℝ) (H : ArithmeticFunction ℝ)
    (hH : ∀ n, H n = (n:ℝ)⁻¹) (p q Y : ℕ) :
    part (fun n => (H*g) n) Y - part (fun n => (H*g) n) (Y/p) - part (fun n => (H*g) n) (Y/q) + part (fun n => (H*g) n) (Y/(p*q)) =
      ∑ d ∈ Icc 1 Y, g d *
        ((harmonic (Y/d):ℝ) - (harmonic ((Y/d)/p):ℝ) - (harmonic ((Y/d)/q):ℝ)
          + (harmonic ((Y/d)/(p*q)):ℝ)) := by
  simp only [partial_convolution H g hH,extend_partial g Y p,extend_partial g Y q,
    extend_partial g Y (p*q), mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]

end SignedHeight

namespace SignedHeight
open Finset Filter
open scoped Topology

private theorem exceptional_value {p m : ℕ} (hm : 0 < m) (hp : p.Prime) (hd : p ∣ m-1) :
    c m p = -1 := by
  have hn : ¬ p ∣ m := by
    intro h
    have hu := Nat.dvd_sub h hd
    rw [show m-(m-1)=1 by omega] at hu
    exact hp.ne_one (Nat.dvd_one.mp hu)
  simp [c, hn, hd]

theorem raw_limit (m : ℕ) (hm : 0 < m) (he : Even m) (hpr : 2 ≤ (m-1).primeFactors.card) :
    Tendsto (fun Y => ∑ n ∈ Icc 1 Y, raw m n) atTop (𝓝 0) := by
  classical
  obtain ⟨p,q,hp,hq,hne⟩ := one_lt_card_iff.mp hpr
  obtain ⟨pp,pd,_⟩ := Nat.mem_primeFactors.mp hp
  obtain ⟨qp,qd,_⟩ := Nat.mem_primeFactors.mp hq
  obtain ⟨g,hsum,hg⟩ := HeightCorr.exists_correction m p q hm he
  have loc : mask q (mask p (c m)) = HeightCorr.localCoeff m p q := by
    funext l
    by_cases lp : l=p <;> by_cases lq : l=q <;> by_cases lm : l ∣ m <;>
      simp [mask, c, HeightCorr.localCoeff, lp, lq, lm]
  have base : sf (mask q (mask p (c m))) = (fun n => (HeightCorr.harmonic * g) n) := by
    funext n
    rw [loc]
    exact hg n
  apply (HeightHarmonic.weighted_limit p q pp.pos qp.pos g hsum).congr
  intro Y
  symm
  change part (sf (c m)) Y = _
  have h := peel_two pp qp hne (c m) (exceptional_value hm pp pd) (exceptional_value hm qp qd) Y
  dsimp only at h
  rw [base] at h
  exact h.trans (double_sum g HeightCorr.harmonic HeightCorr.harmonic_apply p q Y)

end SignedHeight

open Finset Filter
open scoped Topology
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct

theorem Conjectures.Goldbach.PartnerSignedHeightCancellation : (
by
  classical
  let S := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    ∑' q : ℕ, if hq : q ≠ 0 then
      let _ : NeZero q := ⟨hq⟩
      if h : r ∣ q ∧ s ∣ q then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m:ZMod q))) / (q.totient:ℂ)^2
      else 0
    else 0
  let O := S (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1)
  let P := (1 : DirichletCharacter ℂ 1)
  let B := Σ s : ℕ, DirichletCharacter ℂ s
  let valid := fun b : B => b.1 ≠ 0 ∧ b.2.IsPrimitive
  exact ∀ m : ℕ, 0 < m → Even m → 2 ≤ (m-1).primeFactors.card → ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T, ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ b.1 ≤ Y) ∧ ‖∑ b ∈ F, S P b.2 m‖ ≤ ε
) := by
  classical
  intro S O₀ P B valid m hm he hpr ε hε
  let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  have rlim := SignedHeight.raw_limit m hm he hpr
  have clim : Tendsto (fun Y : ℕ => O * ((∑ n ∈ Icc 1 Y, SignedHeight.raw m n : ℝ):ℂ))
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Complex.ofReal_zero, mul_zero] using
      (Complex.continuous_ofReal.continuousAt.tendsto.comp rlim).const_mul O
  have event : ∀ᶠ Y : ℕ in atTop, ‖O * ((∑ n ∈ Icc 1 Y, SignedHeight.raw m n : ℝ):ℂ)‖ < ε := by
    simpa only [dist_zero_right] using (Metric.tendsto_nhds.mp clim ε hε)
  obtain ⟨T,hT⟩ := eventually_atTop.mp event
  refine ⟨T, ?_⟩
  intro Y hY
  let F := (Icc 1 Y).sigma SignedHeight.row
  refine ⟨F, ?_, ?_⟩
  · rintro ⟨s,χ⟩
    change (Sigma.mk s χ ∈ (Icc 1 Y).sigma SignedHeight.row) ↔ (s ≠ 0 ∧ χ.IsPrimitive) ∧ s ≤ Y
    rw [mem_sigma,mem_Icc]
    by_cases hs : s=0
    · subst s; simp
    · simp [SignedHeight.row, hs, Nat.one_le_iff_ne_zero.mpr hs, and_comm]
  · change ‖∑ b ∈ F, series (1 : DirichletCharacter ℂ 1) b.2 m‖ ≤ ε
    have exactSum : (∑ b ∈ F, series (1 : DirichletCharacter ℂ 1) b.2 m) =
        O * ((∑ s ∈ Icc 1 Y, SignedHeight.raw m s : ℝ):ℂ) := by
      rw [Complex.ofReal_sum, mul_sum]
      unfold F
      rw [sum_sigma]
      apply sum_congr rfl
      intro s hs
      let _ : NeZero s := ⟨by have := (mem_Icc.mp hs).1; omega⟩
      exact SignedHeight.level_sum m s hm he
    rw [exactSum]
    exact (hT Y hY).le
