import Conjectures.Goldbach.TwistedGoldbachCoefficientProduct

/-! A power bound for truncating the generalized Goldbach singular series.
For primitive source characters, weight the coefficients at multiples of
their common level by a positive power of the excess denominator.
The primes dividing the target cost at most a divisor-type factor, while
the factors at all remaining primes have a convergent majorant.
This estimates the tail occurring in (10.21) of Pintz I.
https://arxiv.org/abs/1804.05561 -/

namespace Conjectures.Goldbach.TwistedGoldbachDenominatorTail

open Finset DirichletCharacter Filter Topology
open TwistedGoldbachCoefficientProduct TwistedGoldbachSingularSeries TwistedGoldbachMixedPrincipal
open scoped BigOperators Classical

private noncomputable def majorant (u : ℝ) (p : ℕ) := 1+4*(p:ℝ)^(u-2)

private theorem majorant_ge_one (u : ℝ) (p : ℕ) : 1 ≤ majorant u p :=
  le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg p) _))

private theorem majorant_converges {u : ℝ} (hu : u < 1) : Multipliable (majorant u) :=
  Real.multipliable_one_add_of_summable ((Real.summable_nat_rpow.mpr (by linarith : u-2 < -1)).mul_left 4)

private theorem weighted_atom (L t m : ℕ) (u : ℝ) :
    (t:ℝ)^u * |atom L t (fun p => localWeight m p-1)| =
      atom L t (fun p => (p:ℝ)^u*|localWeight m p-1|) := by
  unfold atom
  split_ifs with h
  · have square : (∏ p ∈ t.primeFactors, (p:ℝ)) = t := by
      rw [← Nat.cast_prod,Nat.prod_primeFactors_of_squarefree h.1]
    rw [Finset.abs_prod,prod_mul_distrib,Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) u,square]
  · simp

private theorem prime_weight {p m : ℕ} (hp : p.Prime) (hm : 0 < m) {u : ℝ} (hu : u ≤ 1) :
    1+(p:ℝ)^u*|localWeight m p-1| ≤
      majorant u p * (if p ∈ m.primeFactors then 3 else 1) := by
  have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h0 : 0 < (p:ℝ) := by linarith
  have h1 : 0 < (p:ℝ)-1 := by linarith
  have nonneg := Real.rpow_nonneg h0.le u
  by_cases hd : p ∣ m
  · have mem := Nat.mem_primeFactors.mpr ⟨hp,hd,hm.ne'⟩
    rw [ite_eq_left mem]
    have atom_eq : localWeight m p-1 = 1/((p:ℝ)-1) := by
      simp only [localWeight,ite_eq_left hd]
      field_simp
      ring
    rw [atom_eq,abs_of_nonneg (by positivity)]
    have hpu : (p:ℝ)^u ≤ (p:ℝ) := by simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ p) hu
    have hrat : (p:ℝ)/((p:ℝ)-1) ≤ 2 := (div_le_iff₀ h1).mpr (by linarith)
    have hw := mul_le_mul_of_nonneg_right hpu (by positivity : 0 ≤ 1/((p:ℝ)-1))
    simp only [mul_one_div] at hw ⊢
    linarith [majorant_ge_one u p]
  · have mem : p ∉ m.primeFactors := fun h => hd (Nat.dvd_of_mem_primeFactors h)
    rw [ite_eq_right mem,mul_one]
    have atom_eq : localWeight m p-1 = -(1/((p:ℝ)-1)^2) := by
      simp only [localWeight,ite_eq_right hd]
      field_simp
      ring
    rw [atom_eq,abs_neg,abs_of_nonneg (by positivity)]
    unfold majorant
    rw [Real.rpow_sub h0,Real.rpow_two]
    apply add_le_add_right
    have denom : 1/((p:ℝ)-1)^2 ≤ 4/(p:ℝ)^2 := by
      rw [div_le_div_iff₀ (sq_pos_of_pos h1) (sq_pos_of_pos h0)]
      nlinarith [mul_nonneg (show 0 ≤ (p:ℝ)-2 by linarith) (show 0 ≤ 3*(p:ℝ)-2 by linarith)]
    calc
      _ ≤ (p:ℝ)^u*(4/(p:ℝ)^2) := mul_le_mul_of_nonneg_left denom nonneg
      _ = _ := by ring

private theorem product_bound (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) {m : ℕ} (hm : 0 < m)
    {u : ℝ} (hu : u < 1) :
    ∏ p ∈ S, (1+(p:ℝ)^u*|localWeight m p-1|) ≤
      (∏' p : ℕ, majorant u p) * 3^m.primeFactors.card := by
  calc
    _ ≤ ∏ p ∈ S, (majorant u p * (if p ∈ m.primeFactors then 3 else 1)) :=
      prod_le_prod₀ (fun p _ => by positivity) (fun p hp => prime_weight (hS p hp) hm hu.le)
    _ = (∏ p ∈ S, majorant u p) * (3:ℝ)^(S ∩ m.primeFactors).card := by
      rw [prod_mul_distrib,prod_ite_mem]
      simp
    _ ≤ _ := mul_le_mul
      ((majorant_converges hu).prod_le_tprod_of_nonneg (fun p _ => zero_le_one.trans (majorant_ge_one u p))
        (fun p _ => majorant_ge_one u p))
      (pow_le_pow_right₀ (by norm_num) (card_le_card inter_subset_right))
      (by positivity) (tprod_nonneg (fun p => zero_le_one.trans (majorant_ge_one u p)))

/-- The number of distinct primes dividing the target only costs an
arbitrarily small power, uniformly in the target. -/
theorem target_factor {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → (3:ℝ)^m.primeFactors.card ≤ C*(m:ℝ)^ε := by
  have limit := (tendsto_rpow_atTop hε).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N,hN⟩ := (tendsto_atTop.1 limit (3:ℝ)).exists_forall_of_atTop
  refine ⟨3^N,by positivity,?_⟩
  intro m hm
  let S := m.primeFactors
  have small (p : ℕ) (hp : p ∈ S) :
      (3:ℝ) ≤ (if p ∈ range N then 3 else 1)*(p:ℝ)^ε := by
    have h := (Nat.prime_of_mem_primeFactors hp).one_le
    have hpow : (1:ℝ) ≤ (p:ℝ)^ε := Real.one_le_rpow (by exact_mod_cast h) hε.le
    by_cases H : p ∈ range N
    · rw [ite_eq_left H]
      linarith
    · rw [ite_eq_right H,one_mul]
      exact hN p (by simpa using H)
  have rad : ∏ p ∈ S, (p:ℝ) ≤ (m:ℝ) := by
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
  calc
    (3:ℝ)^S.card = ∏ _p ∈ S, (3:ℝ) := by simp
    _ ≤ ∏ p ∈ S, ((if p ∈ range N then 3 else 1)*(p:ℝ)^ε) := prod_le_prod₀ (by intros; positivity) small
    _ = (3:ℝ)^(S ∩ range N).card * (∏ p ∈ S, (p:ℝ))^ε := by
      rw [prod_mul_distrib,prod_ite_mem,Real.finsetProd_rpow _ _ (fun p _ => Nat.cast_nonneg p) ε]
      simp
    _ ≤ _ := mul_le_mul (pow_le_pow_right₀ (by norm_num)
        ((card_le_card (inter_subset_right (s₁ := S) (s₂ := range N))).trans_eq (card_range N)))
      (Real.rpow_le_rpow (prod_nonneg (fun p _ => Nat.cast_nonneg p)) rad hε.le)
      (by positivity) (by positivity)

section Estimates
variable {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
  (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m)
include hα hβ hm he

private theorem weighted_divisors (n : ℕ) (hn : n ≠ 0) {u : ℝ} (hu : u < 1) :
    let L := Nat.lcm r s
    ∑ t ∈ n.divisors, (t:ℝ)^u * ‖coefficient α β m (L*t)‖ ≤
      ‖coefficient α β m L‖ * ((∏' p : ℕ, majorant u p) * 3^m.primeFactors.card) := by
  intro L
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  let g (p : ℕ) := (p:ℝ)^u*|localWeight m p-1|
  have eqn : ∀ t ∈ n.divisors, (t:ℝ)^u * ‖coefficient α β m (L*t)‖ = ‖coefficient α β m L‖ * atom L t g := by
    intro t ht
    rw [coefficient_extension hα hβ m hm he t (Nat.pos_of_mem_divisors ht).ne',
      norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_left_comm,weighted_atom]
  rw [sum_congr rfl eqn,← mul_sum,sum_atoms L n hL hn]
  exact mul_le_mul_of_nonneg_left (product_bound _ (fun _ hp => Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1) hm hu) (norm_nonneg _)

private theorem weighted_finite {u : ℝ} (hu : u < 1) (S : Finset ℕ) :
    let L := Nat.lcm r s
    ∑ t ∈ S, (t:ℝ)^u * ‖coefficient α β m (L*t)‖ ≤
      ‖coefficient α β m L‖ * ((∏' p : ℕ, majorant u p) * 3^m.primeFactors.card) := by
  intro L
  let N := (S.sup id).factorial
  have hN : N ≠ 0 := Nat.factorial_ne_zero _
  have cover : S ⊆ insert 0 N.divisors := by
    intro d hd
    by_cases hz : d=0
    · simp [hz]
    · exact mem_insert_of_mem (Nat.mem_divisors.mpr ⟨Nat.dvd_factorial (Nat.pos_of_ne_zero hz) (S.le_sup (f:=id) hd),hN⟩)
  apply (sum_le_sum_of_subset_of_nonneg cover (fun p _ _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (norm_nonneg _))).trans
  simpa [L,N,coefficient] using weighted_divisors hα hβ m hm he N hN hu

theorem weighted_series {u : ℝ} (hu : u < 1) :
    let L := Nat.lcm r s
    let f := fun t : ℕ => (t:ℝ)^u*‖coefficient α β m (L*t)‖
    Summable f ∧ (∑' t : ℕ, f t) ≤
      ‖coefficient α β m L‖ * ((∏' p : ℕ, majorant u p) * 3^m.primeFactors.card) := by
  intro L f
  have nonneg : 0 ≤ f := fun t => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (norm_nonneg _)
  have sums := weighted_finite hα hβ m hm he hu
  exact ⟨summable_of_sum_le nonneg sums,Real.tsum_le_of_sum_le nonneg sums⟩

end Estimates

/-- Rankin's bound for the discarded denominators. Its constant is
independent of both primitive characters, their conductors and the target. -/
theorem uniform_tail {u ε : ℝ} (hu0 : 0 ≤ u) (hu : u < 1) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ∀ T : ℕ, 0<T →
      let L := Nat.lcm r s
      (∑' t : ℕ, if T ≤ t then ‖coefficient α β m (L*t)‖ else 0) ≤
        C * ‖∑' d : ℕ, coefficient α β m d‖ * (m:ℝ)^ε / (T:ℝ)^u := by
  obtain ⟨D,hD,Dm⟩ := target_factor hε
  let P := ∏' p : ℕ, majorant u p
  have Pone : 1 ≤ P := by
    simpa using (majorant_converges hu).prod_le_tprod_of_nonneg (s := (∅:Finset ℕ))
      (fun p _ => zero_le_one.trans (majorant_ge_one u p)) (fun p _ => majorant_ge_one u p)
  refine ⟨4*P*D,by positivity [zero_lt_one.trans_le Pone],?_⟩
  intro r s _ _ α β hα hβ m hm he T hT L
  let c := coefficient α β m
  have positive : 0 < (T:ℝ)^u := Real.rpow_pos_of_pos (by exact_mod_cast hT) u
  have single : ‖c L‖ ≤ ∑' d : ℕ, ‖c d‖ :=
    (summable_coefficients α β m hm).le_tsum L (fun d _ => norm_nonneg _)
  have comp := absolute_euler_product hα hβ m hm he
  have cL : ‖c L‖ ≤ ‖∑' d : ℕ, c d‖*4 :=
    single.trans ((le_of_eq comp).trans (mul_le_mul_of_nonneg_left (correction_product_le_four _) (norm_nonneg _)))
  have ⟨hws,hwb⟩ := weighted_series hα hβ m hm he hu
  let tail (t : ℕ) : ℝ := if T ≤ t then ‖c (L*t)‖ else 0
  have htail (t : ℕ) : (T:ℝ)^u*tail t ≤ (t:ℝ)^u*‖c (L*t)‖ := by
    dsimp [tail]
    split_ifs with ht
    · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg T) (by exact_mod_cast ht) hu0) (norm_nonneg _)
    · rw [mul_zero]
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg t) _) (norm_nonneg _)
  have hs : Summable (fun t : ℕ => (T:ℝ)^u*tail t) := Summable.of_nonneg_of_le
    (fun t => mul_nonneg positive.le (by dsimp [tail]; split_ifs <;> positivity)) htail hws
  have bound := hs.tsum_le_tsum htail hws
  rw [tsum_mul_left] at bound
  apply (le_div_iff₀ positive).mpr
  change (∑' t : ℕ, tail t)*(T:ℝ)^u ≤ _
  rw [mul_comm]
  calc
    _ ≤ ‖c L‖*(P*3^m.primeFactors.card) := bound.trans hwb
    _ ≤ (‖∑' d : ℕ, c d‖*4)*(P*(D*(m:ℝ)^ε)) :=
      mul_le_mul cL (mul_le_mul_of_nonneg_left (Dm m hm) (zero_le_one.trans Pone))
        (mul_nonneg (zero_le_one.trans Pone) (by positivity)) (mul_nonneg (norm_nonneg _) (by norm_num))
    _ = _ := by ring

/-- At excess denominator at least X^δ, the tail saves X^(δ/2)
uniformly for positive even targets at most X. -/
theorem power_cutoff {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m X T : ℕ, 0 < m → Even m → m ≤ X → (X:ℝ)^δ ≤ (T:ℝ) →
      (∑' t : ℕ, if T ≤ t then ‖coefficient α β m (Nat.lcm r s*t)‖ else 0) ≤
        C * ‖∑' d : ℕ, coefficient α β m d‖ / (X:ℝ)^(δ/2) := by
  obtain ⟨C,hC,H⟩ := uniform_tail (by norm_num : 0 ≤ (3/4:ℝ)) (by norm_num) (by linarith : 0 < δ/4)
  refine ⟨C,hC,?_⟩
  intro r s _ _ α β hα hβ m X T hm he hX hT
  have hx : (0:ℝ) < X := by exact_mod_cast hm.trans_le hX
  have ht : (0:ℝ) < T := (Real.rpow_pos_of_pos hx δ).trans_le hT
  have h := H r s α β hα hβ m hm he T (by exact_mod_cast ht)
  have weights : (m:ℝ)^(δ/4) * (X:ℝ)^(δ/2) ≤ (T:ℝ)^(3/4:ℝ) := by
    calc
      _ ≤ (X:ℝ)^(δ/4) * (X:ℝ)^(δ/2) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg m) (by exact_mod_cast hX) (by linarith)) (by positivity)
      _ = ((X:ℝ)^δ)^(3/4:ℝ) := by
        rw [← Real.rpow_add hx,← Real.rpow_mul hx.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (Real.rpow_nonneg hx.le _) hT (by norm_num)
  refine h.trans ((div_le_div_iff₀ (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos hx _)).mpr ?_)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left weights (mul_nonneg hC.le (norm_nonneg _))

end Conjectures.Goldbach.TwistedGoldbachDenominatorTail

set_option maxHeartbeats 1200000 in
open Conjectures.Goldbach.TwistedGoldbachDenominatorTail in
theorem Conjectures.Goldbach.TwistedGoldbachDenominatorTail :
by
  classical
  let c := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m d : ℕ) =>
    if hd : d ≠ 0 then
      let _ : NeZero d := ⟨hd⟩
      if h : r ∣ d ∧ s ∣ d then
        let A := DirichletCharacter.changeLevel h.1 α
        let B := DirichletCharacter.changeLevel h.2 β
        gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
          gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-(m : ZMod d))) / (d.totient : ℂ)^2
      else 0
    else 0
  exact
    (∀ u : ℝ, u < 1 → ∀ (r s : ℕ) [NeZero r] [NeZero s]
      (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s), α.IsPrimitive → β.IsPrimitive →
      ∀ m : ℕ, 0 < m → Even m → let L := Nat.lcm r s
      let a := fun t : ℕ => (t:ℝ)^u * ‖c α β m (L*t)‖
      Summable a ∧ (∑' t : ℕ, a t) ≤ ‖c α β m L‖ *
        ((∏' n : ℕ, (1+4*(n:ℝ)^(u-2))) * 3^m.primeFactors.card)) ∧
    (∀ u ε : ℝ, 0 ≤ u → u < 1 → 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
        α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ∀ T : ℕ, 0 < T →
        (∑' t : ℕ, if T ≤ t then ‖c α β m (Nat.lcm r s*t)‖ else 0) ≤
          C * ‖∑' d : ℕ, c α β m d‖ * (m:ℝ)^ε / (T:ℝ)^u) ∧
    (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 < C ∧
      ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
        α.IsPrimitive → β.IsPrimitive → ∀ m X T : ℕ, 0 < m → Even m → m ≤ X → (X:ℝ)^δ ≤ (T:ℝ) →
        (∑' t : ℕ, if T ≤ t then ‖c α β m (Nat.lcm r s*t)‖ else 0) ≤
          C * ‖∑' d : ℕ, c α β m d‖ / (X:ℝ)^(δ/2)) := by
  exact ⟨fun _ hu _ _ _ _ _ _ hα hβ m hm he => weighted_series hα hβ m hm he hu,
    fun _ _ hu₀ hu hε => uniform_tail hu₀ hu hε,fun _ hδ => power_cutoff hδ⟩
