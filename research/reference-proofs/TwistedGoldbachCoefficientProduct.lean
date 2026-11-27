import Conjectures.Goldbach.TwistedGoldbachMixedPrincipal

/-! Möbius inversion of the finite conductor quotient. At denominators
divisible by the least common multiple of the conductors, the remaining
Euler factors are real and multiplicative away from that common level. -/

namespace Conjectures.Goldbach.TwistedGoldbachCoefficientProduct

open Finset DirichletCharacter TwistedGoldbachConductorRatio
open TwistedGoldbachSingularSeries TwistedGoldbachLocalProduct TwistedGoldbachMixedPrincipal
open scoped BigOperators Classical

noncomputable def atom (L t : ℕ) (g : ℕ → ℝ) : ℝ :=
  if Squarefree t ∧ t.Coprime L then ∏ p ∈ t.primeFactors, g p else 0

theorem sum_atoms (L n : ℕ) (hL : L ≠ 0) (hn : n ≠ 0) (g : ℕ → ℝ) :
    ∑ t ∈ n.divisors, atom L t g = ∏ p ∈ n.primeFactors \ L.primeFactors, (1+g p) := by
  rw [prod_one_add]
  unfold atom
  rw [← sum_filter]
  apply sum_bij (fun d _ => d.primeFactors)
  · intro d hd
    obtain ⟨hm,_,hc⟩ := mem_filter.mp hd
    apply mem_powerset.mpr
    intro p hp
    exact mem_sdiff.mpr ⟨Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hm) hn hp,
      fun h => disjoint_left.mp hc.disjoint_primeFactors hp h⟩
  · intro a ha b hb hab
    rw [← Nat.prod_primeFactors_of_squarefree (mem_filter.mp ha).2.1,
      ← Nat.prod_primeFactors_of_squarefree (mem_filter.mp hb).2.1,hab]
  · intro U hU
    have sub := mem_powerset.mp hU
    have prime (p : ℕ) (hp : p ∈ U) := Nat.prime_of_mem_primeFactors (mem_sdiff.mp (sub hp)).1
    let d := ∏ p ∈ U, p
    have factors : d.primeFactors=U := Nat.primeFactors_prod prime
    have hd : d ≠ 0 := (prod_pos (fun p hp => (prime p hp).pos)).ne'
    have square := Nat.squarefree_prod_primeFactors d
    rw [factors] at square
    have divides : d ∣ n := by
      have h := (Nat.prod_primeFactors_dvd_iff (n := d) hn).mpr
        (by rw [factors]; exact fun p hp => (mem_sdiff.mp (sub hp)).1)
      rwa [factors] at h
    have cop : d.Coprime L := (Nat.disjoint_primeFactors hd hL).mp (by
      rw [factors,disjoint_left]
      exact fun p hp => (mem_sdiff.mp (sub hp)).2)
    exact ⟨d,mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨divides,hn⟩,square,cop⟩,factors⟩
  · intro _ _
    rfl

private theorem eq_of_divisor_sums (f g : ℕ → ℂ)
    (h : ∀ n : ℕ, n ≠ 0 → ∑ d ∈ n.divisors, f d = ∑ d ∈ n.divisors, g d) :
    ∀ n : ℕ, n ≠ 0 → f n=g n := by
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    have ne := Nat.mem_divisors_self n hn
    have rest : ∑ d ∈ n.divisors.erase n, f d = ∑ d ∈ n.divisors.erase n, g d := by
      apply sum_congr rfl
      intro d hd
      have ⟨hneq,hmem⟩ := mem_erase.mp hd
      exact ih d (lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hmem)) hneq)
        (Nat.pos_of_mem_divisors hmem).ne'
    have H := h n hn
    rw [← sum_erase_add _ _ ne,← sum_erase_add _ _ ne,rest] at H
    exact add_left_cancel H

private theorem multiples {M : Type*} [AddCommMonoid M] {L n : ℕ} (hL : L ≠ 0) (hn : n ≠ 0) (f : ℕ → M)
    (outside : ∀ d : ℕ, ¬L ∣ d → f d=0) :
    ∑ d ∈ n.divisors, f (L*d) = ∑ d ∈ (L*n).divisors, f d := by
  let S := (L*n).divisors.filter (fun d => L ∣ d)
  calc
    _ = ∑ d ∈ S, f d := by
      apply sum_bij (fun d _ => L*d)
      · intro d hd
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left L (Nat.dvd_of_mem_divisors hd),
          mul_ne_zero hL hn⟩,dvd_mul_right L d⟩
      · intro a _ b _ h
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hL) h
      · intro d hd
        obtain ⟨hm,k,rfl⟩ := mem_filter.mp hd
        exact ⟨k,Nat.mem_divisors.mpr ⟨Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hL)
          (Nat.dvd_of_mem_divisors hm),hn⟩,rfl⟩
      · intro _ _
        rfl
    _ = _ := sum_subset (filter_subset _ _) (fun d hd hnot =>
      outside d (fun h => hnot (mem_filter.mpr ⟨hd,h⟩)))

private theorem complex_ordinary (q m : ℕ) [NeZero q] :
    normalized (1 : DirichletCharacter ℂ q) 1 m = (ordinaryWeight q m:ℂ) := by
  change (q:ℂ)*J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)/(q.totient:ℂ)^2 = _
  simp only [ordinaryWeight,principal_card,Complex.norm_natCast,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_natCast,Complex.ofReal_pow]

private theorem partial_sums {r s q : ℕ} [NeZero r] [NeZero s] [NeZero q]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (hr : r ∣ q) (hs : s ∣ q) (m : ℕ) (hm : 0 < m) (he : Even m) :
    ∑ d ∈ q.divisors, coefficient α β m d =
      (series α β m / series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m) *
        (ordinaryWeight q m:ℂ) := by
  let O := series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m
  have nz : O ≠ 0 := by
    intro hz
    have h := ordinary_at_least_one m hm he
    change 1 ≤ O.re at h
    rw [hz,Complex.zero_re] at h
    norm_num at h
  have id := conductor_identity hα hβ hr hs m hm
  change series α β m * J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q) = O * _ at id
  rw [← ambient_sum hα hβ hr hs m,← complex_ordinary]
  change (q:ℂ)*J _ _ (m:ZMod q)/(q.totient:ℂ)^2 =
    (series α β m/O)*((q:ℂ)*J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)/(q.totient:ℂ)^2)
  have eqn : J (changeLevel hr α) (changeLevel hs β) (m:ZMod q) =
      (series α β m/O)*J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q) := by
    rw [div_mul_eq_mul_div,eq_div_iff nz,mul_comm]
    exact id.symm
  rw [eqn]
  ring

theorem off_level {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s)
    (m d : ℕ) (h : ¬Nat.lcm r s ∣ d) : coefficient α β m d = 0 := by
  unfold coefficient
  split_ifs with hd hdiv
  · exact False.elim (h (Nat.lcm_dvd hdiv.1 hdiv.2))
  all_goals rfl

private theorem new_weights {L t : ℕ} [NeZero L] [NeZero t] (m : ℕ) :
    ordinaryWeight (L*t) m = ordinaryWeight L m *
      ∏ p ∈ t.primeFactors \ L.primeFactors, localWeight m p := by
  rw [ordinary_product,ordinary_product,Nat.primeFactors_mul (NeZero.ne L) (NeZero.ne t)]
  have seteq : L.primeFactors ∪ t.primeFactors = L.primeFactors ∪ (t.primeFactors \ L.primeFactors) := by
    ext p
    simp only [mem_union,mem_sdiff]
    tauto
  rw [seteq,prod_union]
  exact disjoint_left.mpr (fun p hp h => (mem_sdiff.mp h).2 hp)

section Conductors
variable {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
  (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m)
include hα hβ hm he

/-- At multiples of the least common conductor level, partial sums acquire
exactly the ordinary Euler factors for the newly introduced primes. -/
theorem partial_extension (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    ∑ d ∈ (L*t).divisors, coefficient α β m d =
      coefficient α β m L * ((∏ p ∈ t.primeFactors \ L.primeFactors, localWeight m p : ℝ):ℂ) := by
  intro L
  let _ : NeZero t := ⟨ht⟩
  let _ : NeZero L := ⟨(Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'⟩
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  have base := partial_sums hα hβ hr hs m hm he
  rw [sum_eq_single_of_mem L (Nat.mem_divisors_self L (NeZero.ne L))] at base
  · have h := partial_sums hα hβ (hr.trans (dvd_mul_right L t)) (hs.trans (dvd_mul_right L t)) m hm he
    rw [h,new_weights,Complex.ofReal_mul,← mul_assoc,← base]
  · intro d hd ne
    apply off_level
    intro h
    exact ne (Nat.dvd_antisymm (Nat.dvd_of_mem_divisors hd) h)

/-- Formula for every single coefficient, including every ramified or
nonsquarefree zero. No primitivity condition is imposed on the product of
the two source characters. -/
theorem coefficient_extension (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    coefficient α β m (L*t) =
      coefficient α β m L * (atom L t (fun p => localWeight m p-1):ℂ) := by
  intro L
  let c := coefficient α β m
  let g (p : ℕ) := localWeight m p-1
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  apply eq_of_divisor_sums (fun d => c (L*d)) (fun d => c L * (atom L d g:ℂ)) _ t ht
  intro n hn
  rw [multiples hL hn c (fun d h => off_level α β m d h)]
  have H := partial_extension hα hβ m hm he n hn
  change ∑ d ∈ (L*n).divisors, c d = _ at H
  rw [H,← mul_sum,← Complex.ofReal_sum,sum_atoms _ _ hL hn]
  have eqn : (fun p => 1+g p) = localWeight m := funext (fun p => by dsimp [g]; ring)
  simp only [eqn]
  rfl

theorem absolute_partial (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    ∑ d ∈ (L*t).divisors, ‖coefficient α β m d‖ =
      ‖coefficient α β m L‖ * ∏ p ∈ t.primeFactors \ L.primeFactors, (1+|localWeight m p-1|) := by
  intro L
  let c := coefficient α β m
  let g (p : ℕ) := localWeight m p-1
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  have absatom (d : ℕ) : |atom L d g| = atom L d (fun p => |g p|) := by
    unfold atom
    split_ifs <;> simp [Finset.abs_prod]
  rw [← multiples hL ht (fun d => ‖c d‖) (fun d h => by change ‖coefficient α β m d‖ = 0; rw [off_level α β m d h,norm_zero])]
  change ∑ d ∈ t.divisors, ‖c (L*d)‖ = ‖c L‖*_
  rw [← sum_atoms L t hL ht (fun p => |g p|),mul_sum]
  apply sum_congr rfl
  intro d hd
  have H := coefficient_extension hα hβ m hm he d (Nat.pos_of_mem_divisors hd).ne'
  change c (L*d) = c L * (atom L d g:ℂ) at H
  rw [H,norm_mul,Complex.norm_real,Real.norm_eq_abs,absatom]

end Conductors

open Filter Topology

/-- The ratio of the absolute Euler factor to the signed factor. A prime
dividing the conductor level or the even target contributes one. -/
noncomputable def correction (K p : ℕ) : ℝ :=
  if p.Prime ∧ 2 < p ∧ ¬p ∣ K then 1+2/((p:ℝ)*((p:ℝ)-2)) else 1

theorem correction_one_le (K p : ℕ) : 1 ≤ correction K p := by
  unfold correction
  split_ifs with h
  · have hp : (2:ℝ)<p := by exact_mod_cast h.2.1
    exact le_add_of_nonneg_right (by positivity)
  · rfl

private theorem factor_ratio {L p m : ℕ} (hp : p.Prime) (he : Even m) (hL : ¬p ∣ L) :
    1+|localWeight m p-1| = |localWeight m p| * correction (L*m) p := by
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  have h1 : 0 < (p:ℝ)-1 := by linarith
  by_cases hm : p ∣ m
  · have hm' : p ∣ L*m := hm.trans (dvd_mul_left m L)
    simp only [localWeight,ite_eq_left hm,correction,hm',not_true_eq_false,and_false,ite_false,mul_one]
    have hw : 1 ≤ (p:ℝ)/((p:ℝ)-1) := (le_div_iff₀ h1).mpr (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr hw),abs_of_nonneg (by linarith : 0 ≤ (p:ℝ)/((p:ℝ)-1))]
    ring
  · have pn : 2 < p := by
      have := hp.two_le
      by_contra! bad
      exact hm (show p ∣ m by simpa [show p=2 by omega] using even_iff_two_dvd.mp he)
    have hp2 : (2:ℝ)<p := by exact_mod_cast pn
    have h2 : 0 < (p:ℝ)-2 := by linarith
    have h0 : 0 < (p:ℝ) := by linarith
    have hk : ¬p ∣ L*m := fun H => (hp.dvd_mul.mp H).elim hL hm
    simp only [localWeight,ite_eq_right hm,correction,ite_eq_left (And.intro hp (And.intro pn hk))]
    have hw : (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2 ≤ 1 :=
      (div_le_one (sq_pos_of_pos h1)).mpr (by nlinarith)
    rw [abs_of_nonpos (sub_nonpos.mpr hw),abs_of_nonneg (div_nonneg (mul_nonneg h0.le h2.le) (sq_nonneg _))]
    field_simp [h0.ne',h1.ne',h2.ne']
    ring

theorem finite_ratio {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) (t : ℕ) (ht : t ≠ 0) :
    let L := Nat.lcm r s
    ∑ d ∈ (L*t).divisors, ‖coefficient α β m d‖ =
      ‖∑ d ∈ (L*t).divisors, coefficient α β m d‖ *
        ∏ p ∈ t.primeFactors, correction (L*m) p := by
  intro L
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  have rest : ∏ p ∈ t.primeFactors \ L.primeFactors, correction (L*m) p =
      ∏ p ∈ t.primeFactors, correction (L*m) p := by
    apply prod_subset sdiff_subset
    intro p hp hnot
    have hpL : p ∈ L.primeFactors := by
      by_contra H
      exact hnot (mem_sdiff.mpr ⟨hp,H⟩)
    have hd := (Nat.dvd_of_mem_primeFactors hpL).trans (dvd_mul_right L m)
    simp [correction,hd]
  rw [absolute_partial hα hβ m hm he t ht,partial_extension hα hβ m hm he t ht,
    norm_mul,Complex.norm_real,Real.norm_eq_abs,Finset.abs_prod,← rest,mul_assoc,← prod_mul_distrib]
  congr 1
  apply prod_congr rfl
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors (mem_sdiff.mp hp).1
  exact factor_ratio prime he (fun hd => (mem_sdiff.mp hp).2 (Nat.mem_primeFactors.mpr ⟨prime,hd,hL⟩))

private theorem correction_multipliable (K : ℕ) : Multipliable (correction K) := by
  let g (p : ℕ) := correction K p-1
  have base := (Real.summable_one_div_nat_pow.mpr (by decide : 1<2)).mul_left (6:ℝ)
  have hs : Summable g := base.of_norm_bounded (fun p => by
    have hg : 0 ≤ g p := sub_nonneg.mpr (correction_one_le K p)
    rw [Real.norm_eq_abs,abs_of_nonneg hg]
    dsimp [g,correction]
    split_ifs with h
    · have hp : (3:ℝ) ≤ p := by exact_mod_cast h.2.1
      have hp0 : 0 < (p:ℝ) := by linarith
      have hp2 : 0 < (p:ℝ)-2 := by linarith
      field_simp [hp0.ne',hp2.ne']
      nlinarith [mul_nonneg hp0.le (show 0 ≤ (p:ℝ)-3 by linarith)]
    · rw [sub_self]
      positivity)
  exact (Real.multipliable_one_add_of_summable hs).congr (fun p => by dsimp [g]; ring)

private theorem correction_bound_step {p : ℕ} (hp : 2<p) (K : ℕ) :
    correction K p ≤ (((p:ℝ)-1)^2/((p:ℝ)*((p:ℝ)-2)))^2 := by
  have h : (2:ℝ)<p := by exact_mod_cast hp
  have hd : 0 < (p:ℝ)*((p:ℝ)-2) := mul_pos (by linarith) (by linarith)
  have algebra : ((p:ℝ)-1)^2/((p:ℝ)*((p:ℝ)-2)) = 1+1/((p:ℝ)*((p:ℝ)-2)) := by
    field_simp [hd.ne']
    ring
  rw [algebra]
  have hinv : 0 ≤ 1/((p:ℝ)*((p:ℝ)-2)) := by positivity
  unfold correction
  split_ifs <;> nlinarith [sq_nonneg (1/((p:ℝ)*((p:ℝ)-2))),show 2/((p:ℝ)*((p:ℝ)-2))=2*(1/((p:ℝ)*((p:ℝ)-2))) by ring]

private theorem initial_product (K : ℕ) : ∀ n : ℕ, 2 ≤ n →
    ∏ p ∈ range (n+1), correction K p ≤ (2*((n:ℝ)-1)/(n:ℝ))^2 := by
  intro n hn
  induction n,hn using Nat.le_induction with
  | base => norm_num [prod_range_succ,correction]
  | succ k hk ih =>
    have h : (2:ℝ)≤k := by exact_mod_cast hk
    have hk0 : (k:ℝ) ≠ 0 := by linarith
    have hk1 : (k:ℝ)-1 ≠ 0 := by linarith
    have hks : (k:ℝ)+1 ≠ 0 := by linarith
    rw [prod_range_succ]
    refine (mul_le_mul ih (correction_bound_step (by omega : 2<k+1) K)
      (zero_le_one.trans (correction_one_le K _)) (sq_nonneg _)).trans_eq ?_
    push_cast
    field_simp [hk0,hk1,hks,show (k:ℝ)+1-2 ≠ 0 by linarith]
    ring

theorem correction_product_le_four (K : ℕ) : ∏' p : ℕ, correction K p ≤ 4 := by
  apply le_of_tendsto ((correction_multipliable K).hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1))
  filter_upwards [eventually_ge_atTop 2] with n hn
  apply (initial_product K n hn).trans
  have h : (2:ℝ)≤n := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have ht : 2*((n:ℝ)-1)/(n:ℝ) ≤ 2 := (div_le_iff₀ hn0).mpr (by linarith)
  have hb : 0 ≤ 2*((n:ℝ)-1)/(n:ℝ) := div_nonneg (by linarith) hn0.le
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ 2+2*((n:ℝ)-1)/(n:ℝ) by linarith)]

private theorem abs_limit {r s : ℕ} [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r)
    (β : DirichletCharacter ℂ s) (m : ℕ) (hm : 0 < m) (L : ℕ) (hL : L ≠ 0) :
    Tendsto (fun n : ℕ => ∑ d ∈ (L*n.factorial).divisors, ‖coefficient α β m d‖)
      atTop (𝓝 (∑' d : ℕ, ‖coefficient α β m d‖)) := by
  have hf : Tendsto (fun n : ℕ => insert 0 (L*n.factorial).divisors) atTop atTop := by
    apply tendsto_atTop.2
    intro S
    filter_upwards [eventually_ge_atTop (S.sup id)] with n hn
    intro d hd
    by_cases h : d=0
    · simp [h]
    exact mem_insert_of_mem (Nat.mem_divisors.mpr ⟨(Nat.dvd_factorial (Nat.pos_of_ne_zero h)
      ((S.le_sup (f := id) hd).trans hn)).trans (dvd_mul_left n.factorial L),
      mul_ne_zero hL n.factorial_ne_zero⟩)
  apply ((summable_coefficients α β m hm).hasSum.comp hf).congr'
  filter_upwards with n
  simp [coefficient]

/-- Equality keeps precisely the odd primes outside the two conductors
and the target. It includes singular series which vanish. -/
theorem absolute_euler_product {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m) (he : Even m) :
    ∑' d : ℕ, ‖coefficient α β m d‖ =
      ‖∑' d : ℕ, coefficient α β m d‖ * ∏' p : ℕ, correction (Nat.lcm r s*m) p := by
  let L := Nat.lcm r s
  have hL : L ≠ 0 := (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)).ne'
  let K := L*m
  have h := (partial_limit α β m hm L hL).norm.mul
    ((correction_multipliable K).hasProd.tendsto_prod_nat.comp (tendsto_add_atTop_nat 1))
  refine tendsto_nhds_unique (abs_limit α β m hm L hL) (h.congr' ?_)
  filter_upwards with n
  change ‖∑ d ∈ (L*n.factorial).divisors, coefficient α β m d‖ * (∏ p ∈ range (n+1), correction K p) = _
  rw [finite_ratio hα hβ m hm he n.factorial n.factorial_ne_zero]
  congr 1
  symm
  apply prod_subset
  · intro p hp
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.prime_of_mem_primeFactors hp).dvd_factorial.mp
      (Nat.dvd_of_mem_primeFactors hp)))
  · intro p hp hnot
    by_cases prime : p.Prime
    · exact False.elim (hnot (Nat.mem_primeFactors.mpr ⟨prime,prime.dvd_factorial.mpr
        (Nat.le_of_lt_succ (mem_range.mp hp)),n.factorial_ne_zero⟩))
    · simp [correction,prime]

theorem correction_le_universal (K : ℕ) : ∏' p : ℕ, correction K p ≤ ∏' p : ℕ, correction 1 p := by
  apply le_of_tendsto_of_tendsto' (correction_multipliable K).hasProd.tendsto_prod_nat
    (correction_multipliable 1).hasProd.tendsto_prod_nat
  intro n
  apply Finset.prod_le_prod₀ (fun p _ => zero_le_one.trans (correction_one_le K p))
  intro p _
  by_cases h : p.Prime ∧ 2<p ∧ ¬p ∣ K
  · have h1 : p.Prime ∧ 2<p ∧ ¬p ∣ 1 := ⟨h.1,h.2.1,h.1.not_dvd_one⟩
    simp only [correction,ite_eq_left h,ite_eq_left h1,le_refl]
  · rw [show correction K p = 1 by simp [correction,h]]
    exact correction_one_le 1 p

end Conjectures.Goldbach.TwistedGoldbachCoefficientProduct

set_option maxHeartbeats 1200000 in
open Conjectures.Goldbach.TwistedGoldbachCoefficientProduct in
theorem Conjectures.Goldbach.TwistedGoldbachCoefficientProduct :
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
  let w := fun (m p : ℕ) =>
    if p ∣ m then (p:ℝ)/((p:ℝ)-1) else (p:ℝ)*((p:ℝ)-2)/((p:ℝ)-1)^2
  let b := fun (K p : ℕ) =>
    if p.Prime ∧ 2 < p ∧ ¬p ∣ K then 1+2/((p:ℝ)*((p:ℝ)-2)) else 1
  exact
    (∀ K : ℕ, Multipliable (b K) ∧ (∏' p : ℕ, b K p) ≤ ∏' p : ℕ, b 1 p) ∧
    (∏' p : ℕ, b 1 p) ≤ 4 ∧
    ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
      α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m →
      let L := Nat.lcm r s
      let f := c α β m
      (∀ d : ℕ, ¬L ∣ d → f d = 0) ∧
      (∀ t : ℕ, t ≠ 0 → f (L*t) = f L *
        ((if Squarefree t ∧ t.Coprime L then ∏ p ∈ t.primeFactors, (w m p-1) else 0 : ℝ):ℂ)) ∧
      (∀ t : ℕ, t ≠ 0 → ∑ d ∈ (L*t).divisors, ‖f d‖ =
        ‖∑ d ∈ (L*t).divisors, f d‖ * ∏ p ∈ t.primeFactors, b (L*m) p) ∧
      (∑' d : ℕ, ‖f d‖) = ‖∑' d : ℕ, f d‖ * (∏' p : ℕ, b (L*m) p) ∧
      (∑' d : ℕ, ‖f d‖) ≤ ‖∑' d : ℕ, f d‖ * (∏' p : ℕ, b 1 p) := by
  refine ⟨fun K => ⟨correction_multipliable K,correction_le_universal K⟩,correction_product_le_four 1,?_⟩
  intro r s _ _ α β hα hβ m hm he L f
  refine ⟨fun d => off_level α β m d,coefficient_extension hα hβ m hm he,
    finite_ratio hα hβ m hm he,absolute_euler_product hα hβ m hm he,?_⟩
  change (∑' d : ℕ, ‖Conjectures.Goldbach.TwistedGoldbachSingularSeries.coefficient α β m d‖) ≤ _
  rw [absolute_euler_product hα hβ m hm he]
  exact mul_le_mul_of_nonneg_left (correction_le_universal _) (norm_nonneg _)
