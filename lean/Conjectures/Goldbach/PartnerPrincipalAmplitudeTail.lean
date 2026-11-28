import Mathlib
import Conjectures.Goldbach.PartnerPrincipalRowPhase

section

open Finset Filter
open scoped Topology Classical
noncomputable section
namespace PartnerAmplitude

def height (s : ℕ) := ∏ p ∈ s.primeFactors, (p - 2)

def eligible (s : ℕ) := Squarefree s ∧ s.Coprime 2

private theorem prime_gt_two {s p : ℕ} (hs : s.Coprime 2) (hp : p ∈ s.primeFactors) : 2 < p := by
  have hx := Nat.mem_primeFactors.mp hp
  have h2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.Prime.not_dvd_one Nat.prime_two) (hs ▸ Nat.dvd_gcd hx.2.1 (dvd_refl 2))
  have := hx.1.two_le
  omega

theorem height_pos {s : ℕ} (hs : s.Coprime 2) : 0 < height s := by
  apply Finset.prod_pos
  intro p hp
  have := prime_gt_two hs hp
  omega

theorem level_bound {s : ℕ} (hs : eligible s) : s ≤ 3*(height s)^2 := by
  have h1 (p : ℕ) (hp : p ∈ s.primeFactors.erase 3) : p ≤ (p-2)^2 := by
    have hx := Finset.mem_erase.mp hp
    have g := prime_gt_two hs.2 hx.2
    have g' : 4 ≤ p := by omega
    have eq : p = (p-2) + 2 := by omega
    have hv : 2 ≤ p-2 := by omega
    nlinarith [Nat.mul_le_mul hv (le_refl (p-2))]
  have h2 := Finset.prod_le_prod h1
  rw [Finset.prod_pow] at h2
  calc
    s = ∏ p ∈ s.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hs.1).symm
    _ ≤ 3*(height s)^2 := ?_
  unfold height
  by_cases ht : 3 ∈ s.primeFactors
  · rw [← Finset.mul_prod_erase _ _ ht, ← Finset.mul_prod_erase _ _ ht]
    simpa using Nat.mul_le_mul_left 3 h2
  · rw [Finset.erase_eq_of_notMem ht] at h2
    omega

def mainRow {s : ℕ} (β : DirichletCharacter ℂ s) : ℂ :=
  ∑' q : ℕ, if hq : q ≠ 0 then
    let _ : NeZero q := ⟨hq⟩
    if h : 1 ∣ q ∧ s ∣ q then
      let A := DirichletCharacter.changeLevel h.1 (1 : DirichletCharacter ℂ 1)
      let B := DirichletCharacter.changeLevel h.2 β
      gaussSum A ZMod.stdAddChar * gaussSum B ZMod.stdAddChar *
        gaussSum (A*B)⁻¹ (ZMod.stdAddChar.mulShift (-((2:ℕ):ZMod q))) / (q.totient:ℂ)^2
    else 0
  else 0

def baseNorm := ‖mainRow (1 : DirichletCharacter ℂ 1)‖

theorem norm_row {s : ℕ} [NeZero s] {β : DirichletCharacter ℂ s}
    (hβ : β.IsPrimitive) : ‖mainRow β‖ =
      if eligible s then baseNorm / (height s : ℝ) else 0 := by
  classical
  have he := Conjectures.Goldbach.PartnerPrincipalRowPhase s β hβ 2 (by decide) (by decide)
  by_cases hs : eligible s
  · rw [if_pos hs]
    rw [if_pos (show Squarefree s ∧ s.Coprime 2 from hs)] at he
    change mainRow β = _ at he
    rw [he]
    have eq2 : IsUnit (2 : ZMod s) := by
      exact (ZMod.isUnit_iff_coprime 2 s).mpr hs.2.symm
    have hu : ‖β (2 : ZMod s)‖ = 1 := β.unit_norm_eq_one eq2.unit
    have den : (∏ p ∈ s.primeFactors, ((p : ℂ)-2)) = (height s : ℂ) := by
      simp only [height, Nat.cast_prod]
      apply prod_congr rfl
      intro p hp
      rw [Nat.cast_sub (le_of_lt (prime_gt_two hs.2 hp))]
      norm_num
    rw [den, norm_div, norm_mul, norm_mul, norm_pow]
    simp [hu, baseNorm, mainRow]
  · rw [if_neg hs]
    rw [if_neg (show ¬ (Squarefree s ∧ s.Coprime 2) from hs)] at he
    change mainRow β = 0 at he
    rw [he, norm_zero]

def levels (Y : ℕ) : Finset ℕ :=
  (Icc 1 (3*Y^2)).filter (fun s => eligible s ∧ height s < Y)

theorem mem_levels {s Y : ℕ} : s ∈ levels Y ↔ eligible s ∧ height s < Y := by
  classical
  simp only [levels, mem_filter, mem_Icc, and_iff_right_iff_imp]
  intro h
  exact ⟨Nat.one_le_iff_ne_zero.mpr h.1.1.ne_zero, (level_bound h.1).trans (by gcongr; exact h.2.le)⟩

def partners (Y : ℕ) : Finset (Σ s : ℕ, DirichletCharacter ℂ s) :=
  (levels Y).sigma fun s => univ.filter fun β : DirichletCharacter ℂ s => β.IsPrimitive

theorem mem_partners (Y : ℕ) (b : Σ s : ℕ, DirichletCharacter ℂ s)
    (hO : 0 < baseNorm) :
    b ∈ partners Y ↔ (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧ baseNorm < (Y:ℝ)*‖mainRow b.2‖ := by
  classical
  rcases b with ⟨s, β⟩
  simp only [partners, mem_sigma, mem_levels, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨hs, hlt⟩, hb⟩
    haveI : NeZero s := ⟨hs.1.ne_zero⟩
    refine ⟨⟨hs.1.ne_zero, hb⟩, ?_⟩
    rw [norm_row (s := s) (β := β) hb, if_pos hs, ← mul_div_assoc, lt_div_iff₀ (by exact_mod_cast height_pos hs.2)]
    have hr : (height s:ℝ) < (Y:ℝ) := by exact_mod_cast hlt
    nlinarith
  · rintro ⟨⟨hs0, hb⟩, hlt⟩
    haveI : NeZero s := ⟨hs0⟩
    rw [norm_row (s := s) (β := β) hb] at hlt
    by_cases hs : eligible s
    · rw [if_pos hs, ← mul_div_assoc, lt_div_iff₀ (by exact_mod_cast height_pos hs.2)] at hlt
      refine ⟨⟨hs, ?_⟩, hb⟩
      exact_mod_cast (show (height s:ℝ) < (Y:ℝ) by nlinarith)
    · simp only [if_neg hs, mul_zero] at hlt
      linarith
end PartnerAmplitude

end
end

section

open Finset Filter DirichletCharacter
open scoped Topology
noncomputable section
namespace PartnerAmplitudeConstant
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachMixedPrincipal TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct

def oddPrimes (y:ℕ) : Finset ℕ := (range (y+1)).filter (fun p:ℕ=>p.Prime ∧ 2<p)
def factor (p:ℕ) : ℝ := (1+1/((p:ℝ)-2))*(1-1/(p:ℝ))
def coefficient (y:ℕ) : ℝ := (1/2)*∏p∈oddPrimes y,factor p
def ordinary : ℂ := series (1:DirichletCharacter ℂ 1) (1:DirichletCharacter ℂ 1) 2

theorem mem_oddPrimes {p y:ℕ} : p∈oddPrimes y ↔ p.Prime ∧ 2<p ∧ p≤y := by
  simp only [oddPrimes,mem_filter,mem_range,Nat.lt_succ_iff];tauto

theorem nonzero : 0<‖ordinary‖ := by
  have lo := ordinary_at_least_one 2 (by decide) (by decide)
  have bnd := Complex.re_le_norm ordinary
  change 1≤ordinary.re at lo
  linarith

theorem ordinary_limit : Tendsto (fun n:ℕ=>∏p∈n.factorial.primeFactors,localWeight 2 p) atTop (𝓝 ‖ordinary‖) := by
  let O : DirichletCharacter ℂ 1 := 1
  have lim := (TwistedGoldbachSingularSeries.partial_limit O O 2 (by decide) 1 (by decide)).norm
  apply lim.congr'
  filter_upwards with n
  let q:=n.factorial
  let _ : NeZero q := ⟨n.factorial_ne_zero⟩
  change ‖∑d∈(1*n.factorial).divisors,TwistedGoldbachSingularSeries.coefficient O O 2 d‖=_
  rw [one_mul]
  have amb := TwistedGoldbachSingularSeries.ambient_sum (α:=O) (β:=O) isPrimitive_one_level_one
    isPrimitive_one_level_one (one_dvd q) (one_dvd q) 2
  simp only [O,map_one] at amb
  change ‖∑ d ∈ q.divisors,TwistedGoldbachSingularSeries.coefficient O O 2 d‖=_
  rw [←amb]
  change _ = ∏p∈q.primeFactors,localWeight 2 p
  rw [←ordinary_product]
  simp only [TwistedGoldbachSingularSeries.normalized,norm_div,norm_mul,norm_pow,
    Complex.norm_natCast,ordinaryWeight,J]

theorem finite_inverse {n:ℕ} (hn:2≤n) :
    coefficient n = (∏p∈n.factorial.primeFactors,localWeight 2 p)⁻¹ := by
  have eq : n.factorial.primeFactors=insert 2 (oddPrimes n) := by
    ext p
    simp only [Nat.mem_primeFactors,n.factorial_ne_zero,ne_eq,not_false_eq_true,and_true,mem_insert,mem_oddPrimes]
    constructor
    · rintro ⟨pr,dv⟩
      by_cases two:p=2
      · exact Or.inl two
      · exact Or.inr ⟨pr,lt_of_le_of_ne pr.two_le (Ne.symm two),pr.dvd_factorial.mp dv⟩
    · rintro (rfl|⟨pr,_,py⟩)
      · exact ⟨Nat.prime_two,Nat.prime_two.dvd_factorial.mpr hn⟩
      · exact ⟨pr,pr.dvd_factorial.mpr py⟩
  have nf : 2∉oddPrimes n := fun h=>(mem_oddPrimes.mp h).2.1.false
  rw [eq,prod_insert nf,mul_inv_rev,←Finset.prod_inv_distrib]
  have even : (localWeight 2 2)⁻¹=1/2 := by norm_num [localWeight]
  rw [even,mul_comm,coefficient]
  congr 1
  apply prod_congr rfl
  intro p hp
  have big := (mem_oddPrimes.mp hp).2.1
  have nd : ¬p∣2 := fun d => big.not_ge (Nat.le_of_dvd (by decide) d)
  have pr : (2:ℝ)<p := by exact_mod_cast big
  have pp : (p:ℝ)≠0 := by linarith
  have a : (p:ℝ)-2≠0 := by linarith
  have b : (p:ℝ)-1≠0 := by linarith
  simp only [factor,localWeight,nd,ite_false]
  field_simp
  ring

theorem tendsto_coefficient : Tendsto coefficient atTop (𝓝 (1/‖ordinary‖)) := by
  have lim := ordinary_limit.inv₀ nonzero.ne'
  apply (show Tendsto (fun n:ℕ=>(∏p∈n.factorial.primeFactors,localWeight 2 p)⁻¹)
    atTop (𝓝 (1/‖ordinary‖)) by simpa [one_div] using lim).congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (finite_inverse hn).symm

end PartnerAmplitudeConstant

end
end

section

/-! Primitive character counts for squarefree conductors.
The CRT character equivalence follows `PartnerLevelParseval` (PR 4245).
-/

namespace PartnerAmplitudeCount

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachLocalProduct TwistedGoldbachConductorComponents
open scoped Classical BigOperators

noncomputable section

private def glue {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ}
    {L : ℕ} (e : ZMod L ≃+* ∀ i, ZMod (q i))
    (f : ∀ i, DirichletCharacter ℂ (q i)) : DirichletCharacter ℂ L where
  toFun x := ∏ i, f i (e x i)
  map_one' := by simp
  map_mul' x y := by
    have h : ∀ i, f i (e (x * y) i) = f i (e x i) * f i (e y i) := by
      intro i
      rw [e.map_mul, Pi.mul_apply, map_mul]
    simp only [h, ← Finset.prod_mul_distrib]
  map_nonunit' x hx := by
    by_contra h
    apply hx
    have hall : ∀ i, IsUnit (e x i) := by
      intro i
      by_contra hi
      exact h (Finset.prod_eq_zero (Finset.mem_univ i) (MulChar.map_nonunit (f i) hi))
    simpa using (Pi.isUnit_iff.mpr hall).map e.symm

private def phiEquiv {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ}
    {L : ℕ} (e : ZMod L ≃+* ∀ i, ZMod (q i)) :
    DirichletCharacter ℂ L ≃ ∀ i, DirichletCharacter ℂ (q i) where
  toFun := component e
  invFun := glue e
  left_inv χ := by
    apply MulChar.ext'
    intro x
    exact (reassemble e χ x).symm
  right_inv f := by
    funext i
    apply MulChar.ext'
    intro x
    show ∏ j, f j (e (e.symm (Pi.mulSingle i x)) j) = f i x
    rw [e.apply_symm_apply]
    rw [Finset.prod_eq_single i]
    · rw [Pi.mulSingle_eq_same]
    · intro j _ hji
      rw [Pi.mulSingle_eq_of_ne hji, map_one]
    · intro hi
      exact absurd (Finset.mem_univ i) hi

private theorem component_primitive_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ι → ℕ} [∀ i, NeZero (q i)] {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀ i, ZMod (q i))
    (hd : ∀ i, q i ∣ L) (hc : Pairwise (fun i k => (q i).Coprime (q k)))
    (hprod : ∏ i, q i = L) (χ : DirichletCharacter ℂ L) :
    χ.IsPrimitive ↔ ∀ i, (component e χ i).IsPrimitive := by
  constructor
  · intro hχ i
    change (component e χ i).conductor = q i
    rw [component_conductor e hd hc χ i, hχ]
    exact Nat.gcd_eq_left (hd i)
  · intro hχ
    change χ.conductor = L
    calc
      χ.conductor = ∏ i, (component e χ i).conductor := global_conductor e hd hc χ
      _ = ∏ i, q i := Finset.prod_congr rfl (fun i _ => hχ i)
      _ = L := hprod

private def primitiveEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ι → ℕ} [∀ i, NeZero (q i)] {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀ i, ZMod (q i))
    (hd : ∀ i, q i ∣ L) (hc : Pairwise (fun i k => (q i).Coprime (q k)))
    (hprod : ∏ i, q i = L) :
    {χ : DirichletCharacter ℂ L // χ.IsPrimitive} ≃
      ∀ i, {χ : DirichletCharacter ℂ (q i) // χ.IsPrimitive} where
  toFun χ i := ⟨component e χ.1 i, (component_primitive_iff e hd hc hprod χ.1).mp χ.2 i⟩
  invFun f := ⟨(phiEquiv e).symm (fun i => (f i).1), by
    apply (component_primitive_iff e hd hc hprod _).mpr
    intro i
    have h := congrFun ((phiEquiv e).right_inv (fun i => (f i).1)) i
    change component e ((phiEquiv e).symm (fun i => (f i).1)) i = (f i).1 at h
    rw [h]
    exact (f i).2⟩
  left_inv χ := by
    apply Subtype.ext
    exact (phiEquiv e).left_inv χ.1
  right_inv f := by
    funext i
    apply Subtype.ext
    exact congrFun ((phiEquiv e).right_inv (fun i => (f i).1)) i

theorem prime_primitive_iff {p : ℕ} (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) : χ.IsPrimitive ↔ χ ≠ 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [isPrimitive_def]
  constructor
  · intro hc he
    subst χ
    rw [conductor_one] at hc
    exact hp.ne_one hc.symm
  · intro hχ
    rcases (Nat.dvd_prime hp).mp (conductor_dvd_level χ) with h1 | hprime
    · exact (hχ ((eq_one_iff_conductor_eq_one).mpr h1)).elim
    · exact hprime

theorem prime_count {p : ℕ} (hp : p.Prime) :
    ((Finset.univ : Finset (DirichletCharacter ℂ p)).filter
      (fun χ => χ.IsPrimitive)).card = p - 2 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hset : (Finset.univ : Finset (DirichletCharacter ℂ p)).filter
      (fun χ => χ.IsPrimitive) = Finset.univ.erase 1 := by
    ext χ
    simp only [mem_filter, mem_univ, true_and, mem_erase]
    exact (prime_primitive_iff hp χ).trans (by simp [ne_eq])
  rw [hset, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, card_eq_totient_of_hasEnoughRootsOfUnity ℂ p,
      Nat.totient_prime hp]
  omega

theorem primitive_count_crt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : ι → ℕ} [∀ i, NeZero (q i)] {L : ℕ} [NeZero L]
    (e : ZMod L ≃+* ∀ i, ZMod (q i))
    (hd : ∀ i, q i ∣ L) (hc : Pairwise (fun i k => (q i).Coprime (q k)))
    (hprod : ∏ i, q i = L) :
    ((Finset.univ : Finset (DirichletCharacter ℂ L)).filter
      (fun χ => χ.IsPrimitive)).card =
      ∏ i, ((Finset.univ : Finset (DirichletCharacter ℂ (q i))).filter
        (fun χ => χ.IsPrimitive)).card := by
  classical
  calc
    _ = Fintype.card {χ : DirichletCharacter ℂ L // χ.IsPrimitive} :=
      (Fintype.card_subtype (fun χ : DirichletCharacter ℂ L => χ.IsPrimitive)).symm
    _ = Fintype.card (∀ i, {χ : DirichletCharacter ℂ (q i) // χ.IsPrimitive}) :=
      Fintype.card_congr (primitiveEquiv e hd hc hprod)
    _ = ∏ i, Fintype.card {χ : DirichletCharacter ℂ (q i) // χ.IsPrimitive} :=
      Fintype.card_pi
    _ = _ := Finset.prod_congr rfl (fun i _ =>
      Fintype.card_subtype (fun χ : DirichletCharacter ℂ (q i) => χ.IsPrimitive))

theorem squarefree_count {s : ℕ} (hs0 : s ≠ 0) (hsq : Squarefree s) :
    ((Finset.univ : Finset (DirichletCharacter ℂ s)).filter
      (fun χ => χ.IsPrimitive)).card =
      ∏ p ∈ s.primeFactors, (p - 2) := by
  classical
  letI : NeZero s := ⟨hs0⟩
  let I := ↥s.primeFactors
  haveI (i : I) : NeZero (i : ℕ) :=
    ⟨(Nat.mem_primeFactors.mp i.property).1.ne_zero⟩
  let Q (i : I) : ℕ := (i : ℕ) ^ s.factorization (i : ℕ)
  haveI (i : I) : NeZero (Q i) := ⟨(Nat.ordProj_pos s i).ne'⟩
  let e : ZMod s ≃+* ∀ i : I, ZMod (Q i) := ZMod.equivPi s hs0
  have hfac (i : I) : Q i = (i : ℕ) := by
    have hmem := Nat.mem_primeFactors.mp i.property
    have hge : 1 ≤ s.factorization i :=
      (hmem.1.dvd_iff_one_le_factorization hs0).mp hmem.2.1
    have hle : s.factorization i ≤ 1 :=
      (Nat.squarefree_iff_factorization_le_one hs0).mp hsq i
    dsimp only [Q]
    rw [show s.factorization i = 1 by omega, pow_one]
  let e' : ZMod s ≃+* ∀ i : I, ZMod (i : ℕ) :=
    e.trans (RingEquiv.piCongrRight fun i => ZMod.ringEquivCongr (hfac i))
  have hd (i : I) : (i : ℕ) ∣ s := (Nat.mem_primeFactors.mp i.property).2.1
  have hc : Pairwise (fun i k : I => ((i : ℕ)).Coprime (k : ℕ)) := by
    intro i k hik
    have hne : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Subtype.ext h)
    have hp1 : (i : ℕ).Prime := (Nat.mem_primeFactors.mp i.property).1
    have hp2 : (k : ℕ).Prime := (Nat.mem_primeFactors.mp k.property).1
    exact hp1.coprime_iff_not_dvd.mpr fun hdvd =>
      hne ((Nat.prime_dvd_prime_iff_eq hp1 hp2).mp hdvd)
  have hprod : ∏ i : I, (i : ℕ) = s := by
    rw [Finset.prod_coe_sort s.primeFactors (fun p => p)]
    exact Nat.prod_primeFactors_of_squarefree hsq
  rw [primitive_count_crt e' hd hc hprod]
  rw [Finset.prod_coe_sort s.primeFactors (fun p =>
    ((Finset.univ : Finset (DirichletCharacter ℂ p)).filter
      (fun χ => χ.IsPrimitive)).card)]
  exact Finset.prod_congr rfl (fun p hp =>
    prime_count (Nat.mem_primeFactors.mp hp).1)

end
end PartnerAmplitudeCount

end

section

open Finset Filter
open scoped Topology Classical
noncomputable section
namespace PartnerAmplitudePeriodic

def width (d Y r : ℕ) (w : ℕ → ℝ) : ℕ := ⌈((Y:ℝ)*w r-r)/d⌉₊

def fiber (d Y r : ℕ) (w : ℕ → ℝ) : Finset ℕ :=
  (range (width d Y r w)).image (fun k => r+d*k)

def block (d Y : ℕ) (w : ℕ → ℝ) : Finset ℕ :=
  (range d).biUnion (fun r=>fiber d Y r w)

theorem mem_block {d Y n : ℕ} (hd:0<d) (w:ℕ→ℝ) :
    n∈block d Y w ↔ (n:ℝ)<(Y:ℝ)*w (n % d) := by
  have dh : 0<(d:ℝ) := by exact_mod_cast hd
  simp only [block,mem_biUnion,mem_range,fiber,mem_image,width,Nat.lt_ceil,
    lt_div_iff₀ dh]
  constructor
  · rintro ⟨r,hr,k,hk,rfl⟩
    have mo : (r+d*k) % d=r := by simp [Nat.add_mod,Nat.mod_eq_of_lt hr]
    rw [mo]
    push_cast
    linarith
  · intro h
    refine ⟨n % d,Nat.mod_lt _ hd,n/d,?_,Nat.mod_add_div _ _⟩
    have eq : ((n % d:ℕ):ℝ)+(d:ℝ)*(n/d:ℕ)=n := by exact_mod_cast Nat.mod_add_div n d
    linarith

theorem block_card (d Y : ℕ) (hd:0<d) (w:ℕ→ℝ) :
    (block d Y w).card=∑r∈range d,width d Y r w := by
  classical
  rw [block,Finset.card_biUnion]
  · apply sum_congr rfl
    intro r hr
    rw [fiber,Finset.card_image_of_injective,Finset.card_range]
    intro a b eq
    exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel eq)
  · intro r hr s hs hne
    apply Finset.disjoint_left.mpr
    intro n hnr hns
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hnr
    obtain ⟨l,_,eq⟩ := Finset.mem_image.mp hns
    apply hne
    have := congrArg (fun a:ℕ=>a % d) eq
    simpa [Nat.add_mod,Nat.mod_eq_of_lt (mem_range.mp hr),Nat.mod_eq_of_lt (mem_range.mp hs)] using this.symm

private theorem width_approx {d Y r:ℕ} (hd:0<d) (hr:r<d) (w:ℕ→ℝ) (hw:0≤w r) :
    |(width d Y r w:ℝ) - Y*w r/d| ≤ 1 := by
  have dpos : 0<(d:ℝ) := by exact_mod_cast hd
  have rlt : (r:ℝ)<d := by exact_mod_cast hr
  have hlo := Nat.le_ceil (((Y:ℝ)*w r-r)/d)
  have hu := Nat.ceil_lt_add_one (show 0≤(Y:ℝ)*w r/d by positivity)
  have mu : ⌈((Y:ℝ)*w r-r)/d⌉₊ ≤ ⌈(Y:ℝ)*w r/d⌉₊ := by
    apply Nat.ceil_mono
    gcongr
    exact sub_le_self _ (Nat.cast_nonneg _)
  have m : (width d Y r w:ℝ)≤(⌈(Y:ℝ)*w r/d⌉₊:ℝ) := by exact_mod_cast mu
  rw [abs_le]
  have rd : (r:ℝ)/d≤1 := (div_le_one dpos).mpr rlt.le
  change ((Y:ℝ)*w r-r)/d ≤ (width d Y r w:ℝ) at hlo
  rw [sub_div] at hlo
  constructor <;> linarith

theorem block_limit {d:ℕ} (hd:0<d) (w:ℕ→ℝ) (hw:∀r, 0≤w r) :
    Tendsto (fun Y:ℕ=>((block d Y w).card:ℝ)/Y) atTop (𝓝 ((∑r∈range d,w r)/(d:ℝ))) := by
  have est (Y:ℕ) : |((block d Y w).card:ℝ)-(Y:ℝ)*((∑r∈range d,w r)/(d:ℝ))| ≤ d := by
    rw [block_card d Y hd, Nat.cast_sum,←mul_div_assoc,Finset.mul_sum,Finset.sum_div, ←Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ r ∈ range d, |(width d Y r w:ℝ) - Y*w r/d| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ range d, (1:ℝ) := Finset.sum_le_sum fun r hr=>width_approx hd (mem_range.mp hr) w (hw r)
      _ = _ := by simp
  apply Metric.tendsto_atTop.mpr
  intro ε he
  obtain ⟨N,hN⟩ := exists_nat_gt ((d:ℝ)/ε)
  refine ⟨max 1 N, fun Y hY=>?_⟩
  have y0 : 0<(Y:ℝ) := by exact_mod_cast (show 0<Y by omega)
  have hyN : (N:ℝ)≤Y := by exact_mod_cast (show N≤Y by omega)
  have ee := (div_lt_iff₀ he).mp (hN.trans_le hyN)
  let c := (∑r∈range d,w r)/(d:ℝ)
  change dist (((block d Y w).card:ℝ)/Y) c < ε
  have hh : ((block d Y w).card:ℝ)/Y-c = (((block d Y w).card:ℝ)-Y*c)/Y := by
    field_simp
  rw [Real.dist_eq,hh,abs_div,abs_of_pos y0,div_lt_iff₀ y0]
  simpa [c,mul_comm] using (est Y).trans_lt ee
end PartnerAmplitudePeriodic

end
end

section

open Finset Filter
open scoped Topology Classical
noncomputable section
namespace PartnerAmplitudePeriodic
open PartnerAmplitudeConstant

private theorem range_zmod_sum (n : ℕ) [NeZero n] (g : ℕ → ℝ) :
    (∑ m ∈ range n, g m) = ∑ z : ZMod n, g z.val := by
  rw [← Fin.sum_univ_eq_sum_range g n]
  apply Fintype.sum_equiv (ZMod.finEquiv n).toEquiv
  intro x
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

private theorem crt_product {ι:Type*} [Fintype ι] [DecidableEq ι] (q:ι→ℕ)
    (pos:∀i,0<q i) (cop:Pairwise (Function.onFun Nat.Coprime q)) (f:ι→ℕ→ℝ) :
    (∑ m∈range (∏i,q i), ∏ i,f i (m % q i)) = ∏ i,∑ r∈range (q i),f i r := by
  classical
  let M:=∏i,q i
  have hm : 0<M := prod_pos fun i _=>pos i
  let : NeZero M := ⟨hm.ne'⟩
  let (i:ι) : NeZero (q i) := ⟨(pos i).ne'⟩
  let e : ZMod M ≃+* ((i:ι)→ZMod (q i)) := ZMod.prodEquivPi q cop
  have coord (z:ZMod M) (i:ι) : (e z i).val = z.val % q i := by
    change (ZMod.prodEquivPi q cop z i).val=_
    rw [ZMod.prodEquivPi_apply]
    conv_lhs => rw [←ZMod.natCast_zmod_val z]
    simp only [map_natCast,ZMod.val_natCast]
  calc
    _ = ∑z:ZMod M,∏ i,f i (z.val % q i) := range_zmod_sum M _
    _ = ∑x:((i:ι)→ZMod (q i)),∏i,f i (x i).val := by
      apply Fintype.sum_equiv e.toEquiv
      intro z
      simp [coord]
    _ = ∏i,∑x:ZMod (q i), f i x.val := by
      simpa only [Fintype.piFinset_univ] using
        (Finset.prod_univ_sum (fun i:ι=>(Finset.univ:Finset (ZMod (q i)))) (fun i x=>f i x.val)).symm
    _ = _ := Finset.prod_congr rfl fun i _=>(range_zmod_sum (q i) (f i)).symm

def ratio (K n:ℕ) : ℝ := ∏p∈oddPrimes K, if p∣n then (p:ℝ)/(p-2:ℝ) else 1
def good (K n:ℕ) : Prop := Odd n ∧ ∀p∈oddPrimes K, ¬p^2∣n

private def primes (K:ℕ) := insert 2 (oddPrimes K)
private def modulus (p:ℕ) := p^(if p=2 then 1 else 2)
private def localW (p n:ℕ) : ℝ :=
  if p=2 then (if Odd n then 1 else 0) else
  if p^2∣n then 0 else if p∣n then (p:ℝ)/(p-2:ℝ) else 1
private def M (K:ℕ) := ∏p:(primes K), modulus p
private def weight (K n:ℕ) : ℝ := ∏p:(primes K), localW p n

private theorem prime_at {K p:ℕ} (h:p∈primes K) : p.Prime := by
  rcases mem_insert.mp h with rfl|h
  · exact Nat.prime_two
  · exact (mem_oddPrimes.mp h).1

private theorem mod_pos {K p:ℕ} (hp:p∈primes K) : 0 < modulus p :=
  pow_pos (prime_at hp).pos _

private theorem modulus_pair (K:ℕ) :
    Pairwise (Function.onFun Nat.Coprime (fun p:primes K=>modulus p)) := by
  intro i j ne
  apply Nat.coprime_pow_primes _ _ (prime_at i.property) (prime_at j.property)
  exact fun eq=>ne (Subtype.ext eq)

private theorem M_pos (K:ℕ) : 0<M K := prod_pos fun i _=>mod_pos i.property

private theorem local_period (p n:ℕ) : localW p (n % modulus p)=localW p n := by
  by_cases h:p=2
  · subst p
    simp [localW,modulus,Nat.odd_iff]
  · have dv : p∣p^2 := by simp [pow_two]
    simp [localW,modulus,h,Nat.dvd_iff_mod_eq_zero,Nat.mod_mod_of_dvd _ dv]

private theorem weight_period (K n:ℕ) : weight K (n % M K)=weight K n := by
  apply prod_congr rfl
  intro i _
  have d : modulus i ∣ M K := Finset.dvd_prod_of_mem _ (mem_univ i)
  rw [←local_period i (n % M K),Nat.mod_mod_of_dvd _ d,local_period]

private theorem ratio_nonneg (K n:ℕ) : 0≤ratio K n := by
  apply prod_nonneg
  intro p hp
  have g : (2:ℝ)<p := by exact_mod_cast (mem_oddPrimes.mp hp).2.1
  split_ifs <;> positivity

private theorem weight_eq (K n:ℕ) : weight K n = if good K n then ratio K n else 0 := by
  classical
  have nf : 2∉oddPrimes K := fun h=>(mem_oddPrimes.mp h).2.1.false
  unfold weight
  rw [Finset.prod_coe_sort (f:=fun p:ℕ=>localW p n)]
  rw [primes,prod_insert nf]
  by_cases g : good K n
  · simp only [g,ite_true]
    simp only [localW,↓reduceIte,g.1,one_mul]
    apply prod_congr rfl
    intro p hp
    have ne : p≠2 := by have := (mem_oddPrimes.mp hp).2.1;omega
    simp [ne,g.2 p hp]
  · simp only [g,ite_false]
    by_cases o : Odd n
    · have h : ∃p∈oddPrimes K,p^2∣n := by
        by_contra! hh
        exact g ⟨o,hh⟩
      obtain ⟨p,hp,dv⟩ := h
      apply mul_eq_zero_of_right
      apply prod_eq_zero hp
      have ne : p≠2 := by have := (mem_oddPrimes.mp hp).2.1;omega
      simp [localW,ne,dv]
    · simp [localW,o]

private theorem multiples (a b:ℕ) (ha:0<a) : ((range (a*b)).filter (fun n=>a∣n)).card=b := by
  have eq : (range (a*b)).filter (fun n=>a∣n)=(range b).image (fun k=>a*k) := by
    ext n
    simp only [mem_filter,mem_range,mem_image]
    constructor
    · rintro ⟨lt,⟨k,rfl⟩⟩
      exact ⟨k,Nat.lt_of_mul_lt_mul_left lt,rfl⟩
    · rintro ⟨k,lt,rfl⟩
      exact ⟨Nat.mul_lt_mul_of_pos_left lt ha,dvd_mul_right _ _⟩
  rw [eq,card_image_of_injective]
  · simp
  · exact fun _ _ h=>Nat.eq_of_mul_eq_mul_left ha h

private theorem odd_local {p:ℕ} (hp:2<p) :
    ∑r∈range (modulus p),localW p r=(modulus p:ℝ)*factor p := by
  have ne : p≠2 := by omega
  have hpr : (2:ℝ)<p := by exact_mod_cast hp
  have pp : (p:ℝ)≠0 := by linarith
  have dd : (p:ℝ)-2≠0 := by linarith
  let A := (p:ℝ)/(p-2:ℝ)
  have eq (r:ℕ) : localW p r=1+(if p∣r then A-1 else 0)-(if p^2∣r then A else 0) := by
    have dv : p∣p^2 := by simp [pow_two]
    by_cases h:p^2∣r
    · simp [localW,ne,h,dv.trans h]
    · by_cases h':p∣r <;> simp [localW,ne,h,h',A]
  have cp : ((range (p^2)).filter (fun n=>p∣n)).card=p := by
    simpa [pow_two] using multiples p p (by omega)
  have cs : ((range (p^2)).filter (fun n=>p^2∣n)).card=1 := by
    simpa using multiples (p^2) 1 (by positivity)
  simp only [modulus,ne,ite_false,eq,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    ←Finset.sum_filter,Finset.sum_const,card_range,nsmul_eq_mul,cp,cs,Nat.cast_pow]
  dsimp [A,factor]
  field_simp
  ring

private theorem even_local : ∑ r∈range (modulus 2),localW 2 r=(modulus 2:ℝ)*(1/2) := by
  norm_num [modulus,localW,Finset.sum_range_succ,Nat.odd_iff]
  decide

theorem mean (K:ℕ) : (∑n∈range (M K),weight K n)/(M K:ℝ)=coefficient K := by
  classical
  have sum := crt_product (fun p:primes K=>modulus p) (fun p=>mod_pos p.property)
    (modulus_pair K) (fun p n=>localW p n)
  simp only [local_period] at sum
  change (∑n∈range (M K),weight K n) = _ at sum
  have loc (p:primes K) : ∑r∈range (modulus p),localW p r =
      (modulus p:ℝ)*(if (p:ℕ)=2 then 1/2 else factor p) := by
    by_cases pp:(p:ℕ)=2
    · simp only [pp,ite_true];exact even_local
    · have g := mem_insert.mp p.property
      simp only [pp,ite_false]
      exact odd_local (mem_oddPrimes.mp (g.resolve_left pp)).2.1
  rw [sum]
  simp only [loc,Finset.prod_mul_distrib]
  have pos : (M K:ℝ)≠0 := by exact_mod_cast (M_pos K).ne'
  rw [←Nat.cast_prod]
  change ((M K:ℝ)*_)/(M K:ℝ)=_
  rw [mul_div_cancel_left₀ _ pos,Finset.prod_coe_sort (f:=fun p:ℕ=>if p=2 then (1:ℝ)/2 else factor p)]
  have nf : 2∉oddPrimes K := fun h=>(mem_oddPrimes.mp h).2.1.false
  rw [primes,prod_insert nf]
  simp only [ite_true,coefficient]
  congr 1
  apply prod_congr rfl
  intro p hp
  simp [show p≠2 by have := (mem_oddPrimes.mp hp).2.1;omega]

def levels (K Y:ℕ) : Finset ℕ := block (M K) Y (weight K)

theorem mem_levels {K Y n:ℕ} :
    n∈levels K Y ↔ good K n ∧ (n:ℝ)<(Y:ℝ)*ratio K n := by
  rw [levels,mem_block (M_pos K),weight_period,weight_eq]
  by_cases h:good K n
  · simp [h]
  · simp [h]

theorem tendsto_levels (K:ℕ) :
    Tendsto (fun Y:ℕ=>((levels K Y).card:ℝ)/Y) atTop (𝓝 (coefficient K)) := by
  rw [←mean K]
  apply block_limit (M_pos K)
  intro r
  rw [weight_eq]
  split_ifs
  · exact ratio_nonneg _ _
  · rfl
end PartnerAmplitudePeriodic

end
end

section

open Finset Filter
open scoped Topology Classical
noncomputable section
namespace PartnerAmplitudeFar

def oddFactors (n : ℕ) := n.primeFactors.filter (2 < ·)
def ratio (n : ℕ) : ℝ := ∏ p ∈ oddFactors n, (p:ℝ)/((p:ℝ)-2)
def increment (p : ℕ) : ℝ := ((p:ℝ)/((p:ℝ)-2))^2 - 1
def candidates (M : ℕ) := (range (M+1)).filter (fun p => p.Prime ∧ 2 < p)
def bound : ℝ := Real.exp (24 * ∑' n : ℕ, ((n : ℝ)^2)⁻¹)
theorem bound_pos : 0 < bound := Real.exp_pos _
theorem candidates_ge_three {M p : ℕ} (hp : p ∈ candidates M) : 3 ≤ p :=
  (Finset.mem_filter.mp hp).2.2
theorem oddFactors_subset {M n : ℕ} (hn : n ≤ M) : oddFactors n ⊆ candidates M := by
  intro p hp
  have h := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := Nat.le_of_mem_primeFactors h.1; omega),
    (Nat.mem_primeFactors.mp h.1).1, h.2⟩
theorem increment_nonneg {p:ℕ} (hp:3≤p) : 0 ≤ increment p := by
  have hx : (3:ℝ) ≤ p := by exact_mod_cast hp
  have h : (1:ℝ) ≤ (p:ℝ)/((p:ℝ)-2) := (le_div_iff₀ (by linarith)).mpr (by linarith)
  dsimp [increment]
  nlinarith [sq_nonneg ((p:ℝ)/((p:ℝ)-2)-1)]
private theorem increment_le {p:ℕ} (hp:3≤p) : increment p/(p:ℝ) ≤ 24 * ((p:ℝ)^2)⁻¹ := by
  have hx : (3:ℝ) ≤ p := by exact_mod_cast hp
  have h : 0 < (p:ℝ)-2 := by linarith
  have h' : 0 < (p:ℝ) := by linarith
  unfold increment
  field_simp
  nlinarith [sq_nonneg ((p:ℝ)-3)]
theorem candidates_product (M:ℕ) : (∏ p ∈ candidates M, (1+increment p/(p:ℝ))) ≤ bound := by
  calc
    _ ≤ Real.exp (∑ p ∈ candidates M, increment p/(p:ℝ)) := by
      rw [Real.exp_sum]
      apply Finset.prod_le_prod₀
      · intro p hp
        exact add_nonneg zero_le_one (div_nonneg (increment_nonneg (candidates_ge_three hp)) (Nat.cast_nonneg p))
      · intro p hp
        simpa [add_comm] using Real.add_one_le_exp (increment p/(p:ℝ))
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ∑ p ∈ candidates M, 24 * ((p:ℝ)^2)⁻¹ := sum_le_sum fun p hp => increment_le (candidates_ge_three hp)
        _ ≤ _ := by
          rw [← mul_sum]
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).sum_le_tsum _ (fun _ _ => by positivity)
private def divisorProduct (t : Finset ℕ) : ℕ := ∏ p ∈ t, p

private noncomputable def subsetWeight (t : Finset ℕ) : ℝ := ∏ p ∈ t, increment p

/-- A subset of the odd prime factors contributes only at multiples of its product. -/
private theorem square_le_divisor_sum {n M : ℕ} (hn : n ≤ M) :
    ratio n ^ 2 ≤ ∑ t ∈ (candidates M).powerset,
      if divisorProduct t ∣ n then subsetWeight t else 0 := by
  classical
  let A := oddFactors n
  have hdiv (t : Finset ℕ) (ht : t ∈ A.powerset) : divisorProduct t ∣ n := by
    have hsub : t ⊆ n.primeFactors :=
      (mem_powerset.mp ht).trans (filter_subset _ _)
    exact (Finset.prod_dvd_prod_of_subset t n.primeFactors id hsub).trans n.prod_primeFactors_dvd
  calc
    ratio n ^ 2 = ∏ p ∈ A, (1 + increment p) := by
      unfold ratio
      rw [← Finset.prod_pow]
      apply prod_congr rfl
      intro p _
      dsimp [increment]
      ring
    _ = ∑ t ∈ A.powerset, subsetWeight t := Finset.prod_one_add A
    _ = ∑ t ∈ A.powerset, if divisorProduct t ∣ n then subsetWeight t else 0 := by
      exact sum_congr rfl fun t ht ↦ (ite_eq_left (hdiv t ht)).symm
    _ ≤ _ := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact fun t ht ↦ mem_powerset.mpr ((mem_powerset.mp ht).trans (oddFactors_subset hn))
      · intro t ht _
        split_ifs
        · exact prod_nonneg fun p hp ↦ increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
        · exact le_rfl

private theorem multiples_count (M d : ℕ) : ((Icc 1 M).filter (fun n ↦ d ∣ n)).card = M / d := by
  have sets : (Icc 1 M).filter (fun n ↦ d ∣ n) = (range M.succ).filter (fun n ↦ n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_range]
    omega
  rw [sets, Nat.card_multiples']

/-- Average the expanded factors using the exact count `M / d` of positive multiples. -/
theorem prefix_square (M : ℕ) : (∑ n ∈ Icc 1 M, ratio n ^ 2) ≤ bound*(M : ℝ) := by
  classical
  let P := candidates M
  calc
    (∑ n ∈ Icc 1 M, ratio n ^ 2) ≤ ∑ n ∈ Icc 1 M, ∑ t ∈ P.powerset,
        if divisorProduct t ∣ n then subsetWeight t else 0 :=
      sum_le_sum fun n hn ↦ square_le_divisor_sum (mem_Icc.mp hn).2
    _ = ∑ t ∈ P.powerset, ∑ n ∈ Icc 1 M,
        if divisorProduct t ∣ n then subsetWeight t else 0 := Finset.sum_comm
    _ ≤ ∑ t ∈ P.powerset, (M : ℝ) * (∏ p ∈ t, increment p / (p : ℝ)) := by
      apply sum_le_sum
      intro t ht
      have hw : 0 ≤ subsetWeight t := prod_nonneg fun p hp ↦
        increment_nonneg (candidates_ge_three (mem_powerset.mp ht hp))
      rw [← sum_filter, sum_const, multiples_count, nsmul_eq_mul]
      calc
        _ ≤ ((M : ℝ) / (divisorProduct t : ℝ)) * subsetWeight t :=
          mul_le_mul_of_nonneg_right Nat.cast_div_le hw
        _ = _ := by
          rw [Finset.prod_div_distrib]
          simp only [divisorProduct, Nat.cast_prod, subsetWeight]
          ring
    _ = (M : ℝ) * ∏ p ∈ P, (1 + increment p / (p : ℝ)) := by
      rw [← Finset.mul_sum, Finset.prod_one_add]
    _ ≤ bound * (M : ℝ) := by
      rw [mul_comm bound]
      exact mul_le_mul_of_nonneg_left (candidates_product M) (Nat.cast_nonneg _)



theorem ratio_nonneg (n:ℕ) : 0 ≤ ratio n := by
  apply prod_nonneg
  intro p hp
  have h := (Finset.mem_filter.mp hp).2
  have h' : (2:ℝ)<p := by exact_mod_cast h
  positivity

theorem ratio_height {n:ℕ} (h:PartnerAmplitude.eligible n) :
    ratio n*(PartnerAmplitude.height n : ℝ)=n := by
  have allp : oddFactors n = n.primeFactors := by
    apply Finset.filter_eq_self.mpr
    intro p hp
    have hx := Nat.mem_primeFactors.mp hp
    have nt : p ≠ 2 := by
      rintro rfl
      exact Nat.prime_two.not_dvd_one (h.2 ▸ Nat.dvd_gcd hx.2.1 (dvd_refl 2))
    have := hx.1.two_le
    omega
  unfold ratio PartnerAmplitude.height
  rw [allp, Nat.cast_prod, ←Finset.prod_mul_distrib]
  calc
    _ = ∏p∈n.primeFactors,(p:ℝ) := by
      apply prod_congr rfl
      intro p hp
      have gt := (Finset.mem_filter.mp (show p ∈ oddFactors n by rwa [allp])).2
      have gt' : (2:ℝ)<p := by exact_mod_cast gt
      rw [Nat.cast_sub (le_of_lt gt)]
      push_cast
      field_simp
    _ = _ := by rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree h.1]

def block (A B : ℕ) (Y:ℝ) : Finset ℕ := (Ioc A B).filter (fun n : ℕ => (n:ℝ) < Y * ratio n)

theorem block_two (A:ℕ) (hA:0<A) (Y:ℝ) (hY:0≤Y) :
    ((block A (2*A) Y).card:ℝ) ≤ 2*bound*Y^2/(A:ℝ) := by
  let S := block A (2*A) Y
  have Ap : (0:ℝ)<A := by exact_mod_cast hA
  have SS : S ⊆ Icc 1 (2*A) := by
    intro n hn
    have h := mem_Ioc.mp (mem_filter.mp hn).1
    exact mem_Icc.mpr ⟨by omega,h.2⟩
  have low : (S.card:ℝ)*(A:ℝ)^2 ≤ Y^2 * ∑n∈S,ratio n^2 := by
    rw [mul_sum]
    calc
      _ = ∑_ ∈ S, (A:ℝ)^2 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro n hn
        have lo : (A:ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hn).1).1.le
        have hi := (mem_filter.mp hn).2.le
        calc
          (A:ℝ)^2 ≤ (Y * ratio n)^2 := by exact pow_le_pow_left₀ Ap.le (lo.trans hi) 2
          _ = _ := by ring
  have up : (∑n∈S,ratio n^2) ≤ bound * ((2*A:ℕ):ℝ) :=
    (sum_le_sum_of_subset_of_nonneg SS (by intros; positivity)).trans (prefix_square _)
  have hh := low.trans (mul_le_mul_of_nonneg_left up (sq_nonneg Y))
  push_cast at hh
  apply (le_div_iff₀ Ap).mpr
  apply (le_of_mul_le_mul_right _ Ap)
  change (S.card:ℝ)*(A:ℝ)*(A:ℝ) ≤ _
  nlinarith only [hh]

theorem many_blocks (j A:ℕ) (hA:0<A) (Y:ℝ) (hY:0≤Y) :
    ((block A (2^j*A) Y).card:ℝ) ≤ 4*bound*Y^2/(A:ℝ) := by
  induction j generalizing A with
  | zero =>
    simp only [pow_zero, one_mul, block, Ioc_self, filter_empty, card_empty, Nat.cast_zero]
    exact div_nonneg (by positivity [bound_pos]) (Nat.cast_nonneg _)
  | succ j ih =>
    let M := 2^j*(2*A)
    have sub : block A (2^(j+1)*A) Y ⊆ block A (2*A) Y ∪ block (2*A) M Y := by
      intro n hn
      have h := mem_filter.mp hn
      have b := mem_Ioc.mp h.1
      apply mem_union.mpr
      by_cases small : n ≤ 2*A
      · exact Or.inl (mem_filter.mpr ⟨mem_Ioc.mpr ⟨b.1,small⟩,h.2⟩)
      · exact Or.inr (mem_filter.mpr ⟨mem_Ioc.mpr ⟨by omega,
          by simpa [M,pow_succ,Nat.mul_assoc] using b.2⟩,h.2⟩)
    have cardn := (Finset.card_le_card sub).trans (Finset.card_union_le ..)
    have cardr : ((block A (2^(j+1)*A) Y).card:ℝ) ≤
        ((block A (2*A) Y).card:ℝ) + ((block (2*A) M Y).card:ℝ) := by exact_mod_cast cardn
    have b1 := block_two A hA Y hY
    have b2 := ih (2*A) (by omega)
    change ((block (2*A) M Y).card:ℝ) ≤ _ at b2
    refine (cardr.trans (add_le_add b1 b2)).trans_eq ?_
    push_cast
    ring

theorem far_card {A:ℕ} (hA:0<A) {Y:ℝ} (hY:0≤Y) (S:Finset ℕ)
    (mem : ∀ n∈S, A<n ∧ (n:ℝ)<Y*ratio n) :
    (S.card:ℝ) ≤ 4*bound*Y^2/(A:ℝ) := by
  let M := S.sup id
  have sub : S ⊆ block A (2^M*A) Y := by
    intro n hn
    obtain ⟨lo,hi⟩ := mem n hn
    have top : n ≤ M := Finset.le_sup (f:=id) hn
    have upper : M ≤ 2^M*A :=
      M.lt_two_pow_self.le.trans (Nat.le_mul_of_pos_right _ hA)
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨lo,top.trans upper⟩,hi⟩
  exact (show (S.card:ℝ) ≤ _ by exact_mod_cast Finset.card_le_card sub).trans (many_blocks M A hA Y hY)
end PartnerAmplitudeFar

end
end

section

open Finset
noncomputable section
namespace PartnerAmplitudeNear

def primes (K : ℕ) := (range (K+1)).filter (fun p : ℕ => p.Prime ∧ 2 < p)
def factor (p : ℕ) : ℝ := (p:ℝ)/(p-2)
def ratio (K n : ℕ) : ℝ := ∏ p∈primes K, if p∣n then factor p else 1
def full (n : ℕ) := ratio n n
def squareBad (K n : ℕ) := ∃ p ∈ n.primeFactors, K<p ∧ p^2∣n
instance (K n : ℕ) : Decidable (squareBad K n) :=
  inferInstanceAs (Decidable (∃ p∈n.primeFactors, K<p ∧ p^2∣n))

theorem mem_primes {K p : ℕ} : p∈primes K ↔ p.Prime ∧ 2<p ∧ p≤K := by
  simp only [primes,mem_filter,mem_range,Nat.lt_succ_iff]
  tauto

theorem factor_pos {p : ℕ} (hp : 2<p) : 0<factor p := by
  have pr : (2:ℝ)<p := by exact_mod_cast hp
  exact div_pos (by linarith) (by linarith)

theorem ratio_pos (K n : ℕ) : 0<ratio K n := by
  apply Finset.prod_pos
  intro p hp
  split
  · exact factor_pos (mem_primes.mp hp).2.1
  · exact zero_lt_one

theorem ratio_factors {n : ℕ} (np : 0<n) (K : ℕ) :
    ratio K n = ∏ p∈n.primeFactors.filter (fun p => 2<p ∧ p≤K),factor p := by
  rw [ratio,←prod_filter]
  apply prod_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_filter,mem_primes,Nat.mem_primeFactors]
  have nz : n ≠ 0 := np.ne'
  tauto

theorem positive_cut (K n : ℕ) (np : 0<n) :
    full n = ratio K n * ∏p∈n.primeFactors.filter (fun p => 2<p ∧ K<p),factor p := by
  rw [full,ratio_factors np n,ratio_factors np K]
  let S := n.primeFactors.filter (fun p => 2<p)
  have lhs : n.primeFactors.filter (fun p => 2<p ∧ p≤n) = S := by
    ext p
    simp only [S,mem_filter]
    constructor
    · rintro ⟨h,eq,le⟩;exact ⟨h,eq⟩
    · rintro ⟨h,eq⟩;exact ⟨h,eq,Nat.le_of_dvd np (Nat.mem_primeFactors.mp h).2.1⟩
  rw [lhs,←prod_filter_mul_prod_filter_not S (·≤K) factor]
  simp [S,filter_filter]

theorem log_ratio (K n : ℕ) (np : 0<n) :
    Real.log (full n/ratio K n) = ∑p∈n.primeFactors.filter (fun p => 2<p ∧ K<p),Real.log (factor p) := by
  rw [positive_cut K n np,mul_div_cancel_left₀ _ (ratio_pos K n).ne', Real.log_prod]
  intro p hp
  exact (factor_pos (mem_filter.mp hp).2.1).ne'

theorem log_factor {p : ℕ} (hp : 4≤p) : Real.log (factor p) ≤ 4/(p:ℝ) := by
  have pr : (4:ℝ)≤p := by exact_mod_cast hp
  have p0 : (0:ℝ)<p := by linarith
  have p2 : (0:ℝ)<(p:ℝ)-2 := by linarith
  apply (Real.log_le_sub_one_of_pos (factor_pos (by omega : 2<p))).trans
  unfold factor
  field_simp
  nlinarith only [pr]

private theorem multip_count (X d : ℕ) (dp : 0<d) : ((Icc 1 X).filter (d∣·)).card ≤ X/d := by
  have sub : (Icc 1 X).filter (d∣·) ⊆ (Icc 1 (X/d)).image (·*d) := by
    intro n hn
    obtain ⟨lo,dn⟩ := mem_filter.mp hn
    obtain ⟨np,nx⟩ := mem_Icc.mp lo
    exact mem_image.mpr ⟨n/d,mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd np dn) dp,Nat.div_le_div_right nx⟩,Nat.div_mul_cancel dn⟩
  simpa using (card_le_card sub).trans card_image_le

theorem multip_real (X d : ℕ) (dp : 0<d) :
    (∑n∈Icc 1 X,if d∣n then (1:ℝ) else 0) ≤ (X:ℝ)/d := by
  rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one]
  exact (by exact_mod_cast multip_count X d dp : (((Icc 1 X).filter (d∣·)).card:ℝ) ≤ ((X/d:ℕ):ℝ)).trans Nat.cast_div_le

theorem inv_square_tail {K : ℕ} (kp : 0<K) (X : ℕ) :
    (∑p∈Ioc K X,1/(p:ℝ)^2) ≤ 1/(K:ℝ) := by
  by_cases cut : X<K
  · simp [Ioc_eq_empty_of_le cut.le]
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le (le_of_not_gt cut)
    have tel (h : ℕ) : (∑p∈Ioc K (K+h),1/(p:ℝ)^2) ≤ 1/(K:ℝ)-1/((K:ℝ)+h) := by
      induction h with
      | zero => simp
      | succ h ih =>
        rw [Nat.add_succ,sum_Ioc_succ_top (by omega : K≤K+h)]
        push_cast
        have q : 0<(K:ℝ)+h := add_pos_of_pos_of_nonneg (by exact_mod_cast kp) (Nat.cast_nonneg _)
        have q1 : 0<(K:ℝ)+h+1 := by linarith
        have step : 1/((K:ℝ)+h+1)^2 ≤ 1/((K:ℝ)+h)-1/((K:ℝ)+h+1) := by
          field_simp
          linarith
        rw [←add_assoc (K:ℝ) (h:ℝ) 1]
        linarith only [ih,step]
    exact (tel k).trans (sub_le_self _ (by positivity))

private theorem divisor_majorant (K X n : ℕ) (k3:3≤K) (hn:n∈Icc 1 X) :
    Real.log (full n/ratio K n) ≤ ∑p∈Ioc K X,if p∣n then 4/(p:ℝ) else 0 := by
  obtain ⟨np,nx⟩ := mem_Icc.mp hn
  rw [log_ratio K n np]
  let T := n.primeFactors.filter (fun p=>2<p ∧ K<p)
  have inc : T ⊆ Ioc K X := by
    intro p hp
    obtain ⟨fd,_,lo⟩ := mem_filter.mp hp
    exact mem_Ioc.mpr ⟨lo,(Nat.le_of_dvd np (Nat.mem_primeFactors.mp fd).2.1).trans nx⟩
  calc
    _ ≤ ∑ p∈T,if p∣n then 4/(p:ℝ) else 0 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨fd,_,lo⟩ := mem_filter.mp hp
      rw [ite_eq_left (Nat.mem_primeFactors.mp fd).2.1]
      exact log_factor (by omega)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg inc (fun p hp _ => by split <;> positivity)

private theorem expected (K X : ℕ) (d : ℕ→ℕ) (w : ℕ→ℝ)
    (dpos:∀p∈Ioc K X,0<d p) (wpos:∀p∈Ioc K X,0≤w p) :
    (∑n∈Icc 1 X,∑p∈Ioc K X,if d p∣n then w p else 0) ≤
      ∑p∈Ioc K X,((X:ℝ)/d p)*w p := by
  rw [sum_comm]
  apply sum_le_sum
  intro p hp
  have eq (n) : (if d p∣n then w p else 0) = (if d p∣n then (1:ℝ) else 0)*w p := by split <;> simp
  simp_rw [eq]
  rw [← sum_mul]
  exact mul_le_mul_of_nonneg_right (multip_real X _ (dpos p hp)) (wpos p hp)

theorem square_bad_count {K : ℕ} (kp : 0<K) (X : ℕ) :
    (((Icc 1 X).filter (squareBad K)).card:ℝ) ≤ (X:ℝ)/K := by
  have item (n) (hn : n∈Icc 1 X) : (if squareBad K n then (1:ℝ) else 0) ≤
      ∑p∈Ioc K X,if p^2∣n then (1:ℝ) else 0 := by
    by_cases hit : squareBad K n
    · rw [ite_eq_left hit]
      obtain ⟨p,fd,lo,dv⟩ := hit
      have hp := mem_Ioc.mpr ⟨lo,(Nat.le_of_dvd (mem_Icc.mp hn).1 (Nat.mem_primeFactors.mp fd).2.1).trans (mem_Icc.mp hn).2⟩
      have b := single_le_sum (s:=Ioc K X) (f:=fun p:ℕ=>if p^2∣n then (1:ℝ) else 0)
        (fun p _ => by split <;> norm_num) hp
      simpa [dv] using b
    · rw [ite_eq_right hit]
      exact sum_nonneg (fun _ _ => by split <;> norm_num)
  have h := (sum_le_sum item).trans (expected K X (·^2) (fun _=>1)
    (fun p hp => pow_pos (by have := (mem_Ioc.mp hp).1;omega) _) (fun _ _ => zero_le_one))
  rw [←sum_filter,sum_const,nsmul_eq_mul,mul_one] at h
  apply h.trans
  calc
    _ = (X:ℝ)*∑p∈Ioc K X,1/(p:ℝ)^2 := by simp [mul_sum,div_eq_mul_inv]
    _ ≤ _ := by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (inv_square_tail kp X) (Nat.cast_nonneg X : (0:ℝ)≤X)

theorem log_bad_count {K : ℕ} (k3 : 3≤K) (X : ℕ) {η : ℝ} (ep : 0<η) :
    (((Icc 1 X).filter (fun n=>η<Real.log (full n/ratio K n))).card:ℝ) ≤ 4*(X:ℝ)/((K:ℝ)*η) := by
  have item (n) (hn : n∈Icc 1 X) :
      η*(if η<Real.log (full n/ratio K n) then (1:ℝ) else 0) ≤
      ∑p∈Ioc K X,if p∣n then 4/(p:ℝ) else 0 := by
    split_ifs with h
    · rw [mul_one]
      exact h.le.trans (divisor_majorant K X n k3 hn)
    · rw [mul_zero];exact sum_nonneg fun _ _ => by split <;> positivity
  have h := (sum_le_sum item).trans (expected K X id (fun p=>4/(p:ℝ))
    (fun p hp => by have := (mem_Ioc.mp hp).1;dsimp;omega) (fun _ _ => by positivity))
  rw [←mul_sum,←sum_filter,sum_const,nsmul_eq_mul,mul_one] at h
  have tail : (∑p∈Ioc K X, (X:ℝ)/(id p:ℕ)*(4/(p:ℝ))) ≤ 4*(X:ℝ)/(K:ℝ) := by
    calc
      _ = (4*(X:ℝ))*∑p∈Ioc K X,1/(p:ℝ)^2 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro p _
        dsimp only [id]
        ring
      _ ≤ _ := by simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left (inv_square_tail (by omega : 0<K) X) (by positivity : 0≤4*(X:ℝ))
  apply (le_div_iff₀ (mul_pos (by exact_mod_cast (by omega : 0<K)) ep)).mpr
  have top := (le_div_iff₀ (by exact_mod_cast (by omega : 0<K) : (0:ℝ)<K)).mp (h.trans tail)
  linarith only [top]

theorem bad_count {K : ℕ} (k3 : 3≤K) (X : ℕ) {η : ℝ} (ep : 0<η) :
    (((Icc 1 X).filter (fun n=>squareBad K n ∨ η<Real.log (full n/ratio K n))).card:ℝ) ≤
      (X:ℝ)/K+4*(X:ℝ)/((K:ℝ)*η) := by
  rw [filter_or]
  let l := (Icc 1 X).filter (squareBad K)
  let r := (Icc 1 X).filter (fun n=>η<Real.log (full n/ratio K n))
  have b : ((l∪r).card:ℝ)≤(l.card:ℝ)+r.card := by exact_mod_cast card_union_le l r
  apply b.trans
  exact add_le_add (square_bad_count (by omega) X) (log_bad_count k3 X ep)

end PartnerAmplitudeNear

end
end

section

open Filter
open scoped Topology
noncomputable section
namespace PartnerAmplitudeSqueeze

def error (B:ℝ) (K L:ℕ) (η:ℝ) : ℝ := 4*B/(L:ℝ)+((L:ℝ)/(K:ℝ)+4*(L:ℝ)/((K:ℝ)*η))

private theorem ceil_scale (f:ℕ→ℝ) {c a:ℝ} (ha:0<a)
    (h:Tendsto (fun Y:ℕ=>f Y/(Y:ℝ)) atTop (𝓝 c)) :
    Tendsto (fun Y:ℕ=>f ⌈a*(Y:ℝ)⌉₊/(Y:ℝ)) atTop (𝓝 (c*a)) := by
  have hu : Tendsto (fun Y:ℕ=>⌈a*(Y:ℝ)⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop)
  have hv := (tendsto_nat_ceil_mul_div_atTop ha.le).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply ((h.comp hu).mul hv).congr'
  filter_upwards [hu.eventually_ge_atTop 1] with Y hy
  change f ⌈a*(Y:ℝ)⌉₊/(⌈a*(Y:ℝ)⌉₊:ℝ)*((⌈a*(Y:ℝ)⌉₊:ℝ)/(Y:ℝ))=_
  have hn : (⌈a*(Y:ℝ)⌉₊:ℝ)≠0 := by exact_mod_cast (show ⌈a*(Y:ℝ)⌉₊≠0 by omega)
  field_simp

theorem tendsto_count (A:ℕ→ℝ) (P:ℕ→ℕ→ℝ) (c:ℕ→ℝ) (C B:ℝ) (hB:0<B)
    (hc:Tendsto c atTop (𝓝 C))
    (hp:∀K,Tendsto (fun Y:ℕ=>P K Y/(Y:ℝ)) atTop (𝓝 (c K)))
    (bounds:∀K L Y:ℕ,3≤K→1≤L→1≤Y→∀η:ℝ,0<η→
      P K Y/(Y:ℝ)-error B K L η≤A Y/(Y:ℝ) ∧
      A Y/(Y:ℝ)≤P K ⌈Real.exp η*(Y:ℝ)⌉₊/(Y:ℝ)+error B K L η) :
    Tendsto (fun Y:ℕ=>A Y/(Y:ℝ)) atTop (𝓝 C) := by
  have ri : Tendsto (fun n:ℕ=>(n:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have err : Tendsto (fun n:ℕ=>error B (n^3) n (1/(n:ℝ))) atTop (𝓝 0) := by
    have h := ((ri.const_mul (4*B)).add ((ri.pow 2).add (ri.const_mul 4)))
    simp only [mul_zero,zero_pow (by decide : 2≠0),zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have nz : (n:ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
    simp only [error,Nat.cast_pow]
    field_simp
  have cg : Tendsto (fun n:ℕ=>c (n^3)) atTop (𝓝 C) := hc.comp (tendsto_pow_atTop (by decide : 3≠0))
  have ex : Tendsto (fun n:ℕ=>Real.exp (1/(n:ℝ))) atTop (𝓝 1) := by
    simpa [one_div,Function.comp_def] using (Real.continuous_exp.tendsto 0).comp ri
  have lower := cg.sub err
  have upper := (cg.mul ex).add err
  simp only [mul_one,add_zero,sub_zero] at lower upper
  apply tendsto_order.mpr
  constructor
  · intro z hz
    obtain ⟨n,hn,hh⟩ := ((eventually_ge_atTop (3:ℕ)).and ((tendsto_order.mp lower).1 z hz)).exists
    obtain hb : 3≤n^3 := by nlinarith [Nat.pow_le_pow_left hn 3]
    have pos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have per := (hp (n^3)).sub_const (error B (n^3) n (1/(n:ℝ)))
    filter_upwards [(tendsto_order.mp per).1 z hh,eventually_ge_atTop 1] with Y hY hy
    exact hY.trans_le (bounds (n^3) n Y hb (by omega) hy (1/(n:ℝ)) (by positivity)).1
  · intro z hz
    obtain ⟨n,hn,hh⟩ := ((eventually_ge_atTop (3:ℕ)).and ((tendsto_order.mp upper).2 z hz)).exists
    obtain hb : 3≤n^3 := by nlinarith [Nat.pow_le_pow_left hn 3]
    have pos : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
    have per := (ceil_scale (P (n^3)) (Real.exp_pos (1/(n:ℝ))) (hp (n^3))).add_const
      (error B (n^3) n (1/(n:ℝ)))
    filter_upwards [(tendsto_order.mp per).2 z hh,eventually_ge_atTop 1] with Y hY hy
    exact (bounds (n^3) n Y hb (by omega) hy (1/(n:ℝ)) (by positivity)).2.trans_lt hY
end PartnerAmplitudeSqueeze

end
end

section

open Finset Filter
open scoped Topology Classical
noncomputable section
namespace PartnerAmplitudeComparison

theorem ratio_full {n:ℕ} (hn:0<n) : PartnerAmplitudeFar.ratio n = PartnerAmplitudeNear.full n := by
  rw [PartnerAmplitudeNear.full,PartnerAmplitudeNear.ratio_factors hn]
  unfold PartnerAmplitudeFar.ratio PartnerAmplitudeFar.oddFactors PartnerAmplitudeNear.factor
  apply prod_congr _ (fun _ _=>rfl)
  ext p
  simp only [mem_filter]
  exact ⟨fun ⟨hp,h⟩=>⟨hp,h,Nat.le_of_mem_primeFactors hp⟩,
    fun ⟨hp,h,_⟩=>⟨hp,h⟩⟩

theorem periodic_le_full {n:ℕ} (hn:0<n) (K:ℕ) : PartnerAmplitudePeriodic.ratio K n ≤ PartnerAmplitudeFar.ratio n := by
  rw [ratio_full hn,PartnerAmplitudeNear.positive_cut K n hn]
  change PartnerAmplitudeNear.ratio K n ≤ _
  have factors : 1 ≤ ∏p∈n.primeFactors.filter (fun p=>2<p ∧ K<p),PartnerAmplitudeNear.factor p := by
    apply Finset.one_le_prod₀
    intro p hp
    have h := (Finset.mem_filter.mp hp).2.1
    have hr : (2:ℝ)<p := by exact_mod_cast h
    apply (le_div_iff₀ (by linarith : 0<(p:ℝ)-2)).mpr
    linarith
  exact le_mul_of_one_le_right (PartnerAmplitudeNear.ratio_pos K n).le factors

theorem actual_mem {Y n:ℕ} : n∈PartnerAmplitude.levels Y ↔ PartnerAmplitude.eligible n ∧ (n:ℝ)<Y*PartnerAmplitudeFar.ratio n := by
  rw [PartnerAmplitude.mem_levels]
  constructor
  · rintro ⟨h,hh⟩
    refine ⟨h,?_⟩
    rw [← PartnerAmplitudeFar.ratio_height h, mul_comm (PartnerAmplitudeFar.ratio n)]
    apply mul_lt_mul_of_pos_right (by exact_mod_cast hh)
    rw [ratio_full (Nat.pos_of_ne_zero h.1.ne_zero)]
    exact PartnerAmplitudeNear.ratio_pos _ _
  · rintro ⟨h,hh⟩
    rw [← PartnerAmplitudeFar.ratio_height h, mul_comm (PartnerAmplitudeFar.ratio n)] at hh
    have hp : 0 < PartnerAmplitudeFar.ratio n := by
      rw [ratio_full (Nat.pos_of_ne_zero h.1.ne_zero)]
      exact PartnerAmplitudeNear.ratio_pos _ _
    exact ⟨h,by exact_mod_cast (lt_of_mul_lt_mul_right hh hp.le)⟩

theorem good_of_eligible {n:ℕ} (h:PartnerAmplitude.eligible n) (K:ℕ) : PartnerAmplitudePeriodic.good K n := by
  refine ⟨Nat.coprime_two_right.mp h.2,fun p hp=>?_⟩
  simpa [pow_two] using (Nat.squarefree_iff_prime_squarefree.mp h.1 p
    (PartnerAmplitudeConstant.mem_oddPrimes.mp hp).1)

theorem eligible_of_good {K n:ℕ} (h:PartnerAmplitudePeriodic.good K n) (nb:¬ PartnerAmplitudeNear.squareBad K n) : PartnerAmplitude.eligible n := by
  have nn : n≠0 := by rintro rfl; simpa using h.1
  refine ⟨Nat.squarefree_iff_prime_squarefree.mpr ?_,Nat.coprime_two_right.mpr h.1⟩
  intro p hp hdiv
  have div := (dvd_mul_right p p).trans hdiv
  have p2 : 2 < p := by
    have ht : p ≠ 2 := by
      rintro rfl
      exact Nat.prime_two.not_dvd_one ((Nat.coprime_two_right.mpr h.1) ▸ Nat.dvd_gcd div (dvd_refl 2))
    have := hp.two_le
    omega
  have sq : p^2∣n := by simpa [pow_two] using hdiv
  by_cases small : p≤K
  · exact h.2 p (PartnerAmplitudeConstant.mem_oddPrimes.mpr ⟨hp,p2,small⟩) sq
  · exact nb ⟨p,Nat.mem_primeFactors.mpr ⟨hp,div,nn⟩,by omega,sq⟩

def bad (K n:ℕ) (η:ℝ) := PartnerAmplitudeNear.squareBad K n ∨ η<Real.log (PartnerAmplitudeNear.full n/PartnerAmplitudeNear.ratio K n)

theorem outside_bad {n K:ℕ} (hn:0<n) {η:ℝ} (nb:¬bad K n η) :
    PartnerAmplitudeFar.ratio n ≤ Real.exp η * PartnerAmplitudePeriodic.ratio K n := by
  have h : Real.log (PartnerAmplitudeNear.full n/PartnerAmplitudeNear.ratio K n) ≤ η := le_of_not_gt (fun z=>nb (Or.inr z))
  have pos : 0 < PartnerAmplitudeNear.full n/PartnerAmplitudeNear.ratio K n := div_pos (PartnerAmplitudeNear.ratio_pos n n) (PartnerAmplitudeNear.ratio_pos K n)
  have hl := Real.exp_le_exp.mpr h
  rw [Real.exp_log pos] at hl
  rw [ratio_full hn]
  exact (div_le_iff₀ (PartnerAmplitudeNear.ratio_pos K n)).mp hl

def error (K L:ℕ) (η:ℝ) : ℝ := 4*PartnerAmplitudeFar.bound/(L:ℝ) + ((L:ℝ)/(K:ℝ)+4*(L:ℝ)/((K:ℝ)*η))

theorem comparison (S T:Finset ℕ) {K L Y:ℕ} (hK:3≤K) (hL:1≤L) (hY:1≤Y)
    {η:ℝ} (hη:0<η) (pos : ∀n∈S,0<n ∧ (n:ℝ)<Y*PartnerAmplitudeFar.ratio n)
    (good : ∀n∈S,¬bad K n η → n∈T) :
    (S.card:ℝ)/(Y:ℝ) ≤ (T.card:ℝ)/(Y:ℝ) + error K L η := by
  let E := (Icc 1 (L*Y)).filter (fun n=>bad K n η)
  let U := S.filter (fun n=>L*Y<n)
  have incl : S ⊆ T∪E∪U := by
    intro n hn
    by_cases far : L*Y<n
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hn,far⟩))
    apply mem_union.mpr ∘ Or.inl
    by_cases hb : bad K n η
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_Icc.mpr ⟨(pos n hn).1,by omega⟩,hb⟩))
    · exact mem_union.mpr (Or.inl (good n hn hb))
  have far := PartnerAmplitudeFar.far_card (A:=L*Y) (by positivity) (Y:=(Y:ℝ)) (Nat.cast_nonneg _) U
    (fun n hn=>⟨(mem_filter.mp hn).2,(pos n (mem_filter.mp hn).1).2⟩)
  have eqE : E = (Icc 1 (L*Y)).filter (fun n=>PartnerAmplitudeNear.squareBad K n ∨ η<Real.log (PartnerAmplitudeNear.full n/PartnerAmplitudeNear.ratio K n)) := by
    ext n
    constructor <;> intro hn <;> exact Finset.mem_filter.mpr (Finset.mem_filter.mp hn)
  have near := PartnerAmplitudeNear.bad_count hK (L*Y) hη
  rw [← eqE] at near
  have ca : S.card ≤ T.card+E.card+U.card := calc
    _ ≤ (T∪E∪U).card := card_le_card incl
    _ ≤ (T∪E).card+U.card := card_union_le _ _
    _ ≤ _ := Nat.add_le_add_right (card_union_le _ _) _
  have cr : (S.card:ℝ) ≤ (T.card:ℝ)+(E.card:ℝ)+(U.card:ℝ) := by exact_mod_cast ca
  have lp : (0:ℝ)<L := by exact_mod_cast hL
  have kp : (0:ℝ)<K := by exact_mod_cast (by omega : 0<K)
  have yp : (0:ℝ)<Y := by exact_mod_cast hY
  push_cast at far near
  have er : 4*PartnerAmplitudeFar.bound*(Y:ℝ)^2/((L:ℝ)*Y) + ((L:ℝ)*Y/K+4*((L:ℝ)*Y)/((K:ℝ)*η)) =
      error K L η * Y := by
    unfold error
    field_simp <;> ring
  apply (div_le_iff₀ yp).mpr
  rw [add_mul,div_mul_cancel₀ _ yp.ne']
  linarith only [cr,near,far,er]

theorem bounds (K L Y:ℕ) (hK:3≤K) (hL:1≤L) (hY:1≤Y) (η:ℝ) (hη:0<η) :
    ((PartnerAmplitudePeriodic.levels K Y).card:ℝ)/Y - error K L η ≤ ((PartnerAmplitude.levels Y).card:ℝ)/Y ∧
    ((PartnerAmplitude.levels Y).card:ℝ)/Y ≤ ((PartnerAmplitudePeriodic.levels K ⌈Real.exp η*(Y:ℝ)⌉₊).card:ℝ)/Y+error K L η := by
  constructor
  · apply sub_le_iff_le_add.mpr
    apply comparison _ _ hK hL hY hη
    · intro n hn
      obtain ⟨g,lt⟩ := PartnerAmplitudePeriodic.mem_levels.mp hn
      have np : 0<n := Nat.pos_of_ne_zero fun he=>by
        have od := g.1
        rw [he] at od
        exact (by decide : ¬Odd (0:ℕ)) od
      exact ⟨np,lt.trans_le (mul_le_mul_of_nonneg_left (periodic_le_full np K) (Nat.cast_nonneg _))⟩
    · intro n hn nb
      obtain ⟨g,lt⟩ := PartnerAmplitudePeriodic.mem_levels.mp hn
      have elig := eligible_of_good g (fun v=>nb (Or.inl v))
      exact actual_mem.mpr ⟨elig,lt.trans_le (mul_le_mul_of_nonneg_left
        (periodic_le_full (Nat.pos_of_ne_zero elig.1.ne_zero) K) (Nat.cast_nonneg _))⟩
  · apply comparison _ _ hK hL hY hη
    · intro n hn
      have h := actual_mem.mp hn
      exact ⟨Nat.pos_of_ne_zero h.1.1.ne_zero,h.2⟩
    · intro n hn nb
      obtain ⟨g,lt⟩ := actual_mem.mp hn
      have np := Nat.pos_of_ne_zero g.1.ne_zero
      apply PartnerAmplitudePeriodic.mem_levels.mpr
      refine ⟨good_of_eligible g K,lt.trans_le ?_⟩
      calc
        (Y:ℝ)*PartnerAmplitudeFar.ratio n ≤ (Y:ℝ)*(Real.exp η * PartnerAmplitudePeriodic.ratio K n) :=
          mul_le_mul_of_nonneg_left (outside_bad np nb) (Nat.cast_nonneg _)
        _ = (Real.exp η*(Y:ℝ))*PartnerAmplitudePeriodic.ratio K n := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.le_ceil _) (PartnerAmplitudeNear.ratio_pos K n).le

end PartnerAmplitudeComparison

end
end

section

open Finset Filter
open scoped Topology
noncomputable section
namespace PartnerAmplitudeComparison

theorem unweighted : Tendsto (fun Y:ℕ => ((PartnerAmplitude.levels Y).card:ℝ)/(Y:ℝ))
  atTop (𝓝 (1/PartnerAmplitude.baseNorm)) := by
  apply PartnerAmplitudeSqueeze.tendsto_count _ (fun K Y => ((PartnerAmplitudePeriodic.levels K Y).card:ℝ))
    PartnerAmplitudeConstant.coefficient _ PartnerAmplitudeFar.bound PartnerAmplitudeFar.bound_pos
  · exact PartnerAmplitudeConstant.tendsto_coefficient
  · exact PartnerAmplitudePeriodic.tendsto_levels
  · exact bounds
end PartnerAmplitudeComparison

end
end

section

open Finset Filter
open scoped Topology Classical BigOperators

noncomputable section
namespace PartnerAmplitudeFinish

open PartnerAmplitude

def weighted (Y : ℕ) : ℝ := ∑ s ∈ levels Y, (height s : ℝ)
def count (Y : ℕ) : ℝ := ((levels Y).card : ℝ)

theorem partners_card (Y : ℕ) : ((partners Y).card : ℝ) = weighted Y := by
  classical
  unfold partners weighted
  rw [Finset.card_sigma]
  push_cast
  apply Finset.sum_congr rfl
  intro s hs
  have h : eligible s := (mem_levels.mp hs).1
  rw [PartnerAmplitudeCount.squarefree_count h.1.ne_zero h.1]
  rfl

private theorem levels_mono {a b : ℕ} (hab : a ≤ b) : levels a ⊆ levels b := by
  intro s hs
  rw [mem_levels] at hs ⊢
  exact ⟨hs.1, lt_of_lt_of_le hs.2 hab⟩

private theorem sum_step (h Y : ℕ) (hh : h < Y) :
    (∑ t ∈ Finset.range Y, if h < t + 1 then (1 : ℕ) else 0) = Y - h := by
  induction Y with
  | zero => omega
  | succ Y ih =>
      rw [Finset.sum_range_succ]
      by_cases hy : h < Y
      · rw [ih hy]
        simp only [Nat.lt_add_one_iff, Nat.le_of_lt hy, ↓reduceIte]
        omega
      · have he : h = Y := by omega
        subst h
        have hz : (∑ t ∈ Finset.range Y, if Y < t + 1 then (1 : ℕ) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          have : t < Y := Finset.mem_range.mp ht
          simp [show ¬ Y < t + 1 by omega]
        rw [hz]
        simp

private theorem filter_level {t Y : ℕ} (ht : t < Y) :
    (levels Y).filter (fun s => height s < t + 1) = levels (t + 1) := by
  ext s
  simp only [mem_filter, mem_levels]
  constructor
  · rintro ⟨⟨hs, _⟩, hh⟩
    exact ⟨hs, hh⟩
  · intro hs
    exact ⟨⟨hs.1, lt_of_lt_of_le hs.2 (Nat.succ_le_of_lt ht)⟩, hs.2⟩

private theorem weighted_partial_sum (Y : ℕ) :
    weighted Y + ∑ t ∈ Finset.range Y, count (t + 1) = (Y : ℝ) * count Y := by
  classical
  have hs (s : ℕ) (hsm : s ∈ levels Y) :
      (height s : ℝ) +
      (∑ t ∈ Finset.range Y, if height s < t + 1 then (1 : ℝ) else 0) = (Y : ℝ) := by
    have hlt := (mem_levels.mp hsm).2
    have hsum := sum_step (height s) Y hlt
    have hcast :
        (∑ t ∈ Finset.range Y, if height s < t + 1 then (1 : ℝ) else 0) =
          ((Y - height s : ℕ) : ℝ) := by
      exact_mod_cast hsum
    rw [hcast, Nat.cast_sub (Nat.le_of_lt hlt)]
    ring
  have hsum :
      (∑ s ∈ levels Y, ((height s : ℝ) +
        ∑ t ∈ Finset.range Y, if height s < t + 1 then (1 : ℝ) else 0)) =
          (Y : ℝ) * count Y := by
    calc
      _ = ∑ s ∈ levels Y, (Y : ℝ) :=
        Finset.sum_congr rfl (fun s h => hs s h)
      _ = _ := by simp [count, mul_comm]
  rw [Finset.sum_add_distrib] at hsum
  have hswap :
      (∑ s ∈ levels Y, ∑ t ∈ Finset.range Y,
        if height s < t + 1 then (1 : ℝ) else 0) =
      ∑ t ∈ Finset.range Y, count (t + 1) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    have hte : t < Y := Finset.mem_range.mp ht
    change _ = (((levels (t + 1)).card : ℝ))
    rw [← filter_level hte]
    simp
  rw [hswap] at hsum
  exact hsum

private theorem sum_succ_real (Y : ℕ) :
    (∑ t ∈ Finset.range Y, ((t + 1 : ℕ) : ℝ)) =
      (Y : ℝ) * ((Y : ℝ) + 1) / 2 := by
  induction Y with
  | zero => simp
  | succ Y ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem sum_succ_ratio :
    Tendsto (fun Y : ℕ =>
      (∑ t ∈ Finset.range Y, ((t + 1 : ℕ) : ℝ)) / (Y : ℝ) ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hlim : Tendsto (fun Y : ℕ => (1 + (Y : ℝ)⁻¹) / 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
    convert (tendsto_const_nhds.add
      (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const 2 using 1 <;> ring
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with Y hY
  rw [sum_succ_real]
  have hy : (Y : ℝ) ≠ 0 := by exact_mod_cast (show Y ≠ 0 by omega)
  field_simp

private theorem sum_succ_atTop :
    Tendsto (fun Y : ℕ => ∑ t ∈ Finset.range Y, ((t + 1 : ℕ) : ℝ))
      atTop atTop := by
  apply tendsto_atTop_mono (g := fun Y : ℕ =>
    ∑ t ∈ Finset.range Y, ((t + 1 : ℕ) : ℝ))
    (fun Y => ?_) tendsto_natCast_atTop_atTop
  calc
    (Y : ℝ) = ∑ t ∈ Finset.range Y, (1 : ℝ) := by simp
    _ ≤ ∑ t ∈ Finset.range Y, ((t + 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact_mod_cast Nat.succ_pos t

private theorem sum_linear_asymptotic (N : ℕ → ℝ) (c : ℝ)
    (hN : Tendsto (fun Y : ℕ => N Y / (Y : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun Y : ℕ =>
      (∑ t ∈ Finset.range Y, N (t + 1)) / (Y : ℝ) ^ 2)
      atTop (𝓝 (c / 2)) := by
  let f (t : ℕ) : ℝ := N (t + 1) - c * ((t + 1 : ℕ) : ℝ)
  let g (t : ℕ) : ℝ := ((t + 1 : ℕ) : ℝ)
  have hf0 : Tendsto (fun t => f t / g t) atTop (𝓝 (0 : ℝ)) := by
    have h := (hN.comp (tendsto_add_atTop_nat 1)).sub_const c
    convert h using 1
    · ext t
      dsimp [f, g]
      have ht : (((t + 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero t
      field_simp
    · ring
  have hfo : f =o[atTop] g :=
    (Asymptotics.isLittleO_iff_tendsto (by
      intro t ht
      have hp : 0 < g t := by dsimp [g]; positivity
      exact (ne_of_gt hp ht).elim)).mpr hf0
  have hgs : ∀ t, 0 ≤ g t := by intro t; dsimp [g]; positivity
  have hsum := hfo.sum_range hgs sum_succ_atTop
  have herror : Tendsto (fun Y : ℕ =>
      (∑ t ∈ Finset.range Y, f t) / (Y : ℝ) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
    have hquot := hsum.tendsto_div_nhds_zero
    have hprod := hquot.mul sum_succ_ratio
    have hprod0 : Tendsto (fun Y : ℕ =>
        ((∑ t ∈ Finset.range Y, f t) / (∑ t ∈ Finset.range Y, g t)) *
          ((∑ t ∈ Finset.range Y, ((t + 1 : ℕ) : ℝ)) / (Y : ℝ) ^ 2))
        atTop (𝓝 (0 : ℝ)) := by simpa using hprod
    apply hprod0.congr'
    filter_upwards [eventually_ge_atTop 1] with Y hY
    have hden : (∑ t ∈ Finset.range Y, g t) ≠ 0 := by
      have hle : (Y : ℝ) ≤ ∑ t ∈ Finset.range Y, g t := by
        calc
          (Y : ℝ) = ∑ t ∈ Finset.range Y, (1 : ℝ) := by simp
          _ ≤ ∑ t ∈ Finset.range Y, g t := by
            apply Finset.sum_le_sum
            intro t ht
            dsimp [g]
            exact_mod_cast Nat.succ_pos t
      have hy : (0 : ℝ) < Y := by exact_mod_cast hY
      exact ne_of_gt (lt_of_lt_of_le hy hle)
    dsimp [g] at hden ⊢
    field_simp
  have hmain := (herror.add (sum_succ_ratio.const_mul c))
  convert hmain using 1
  · ext Y
    have hs : (∑ t ∈ Finset.range Y, N (t + 1)) =
        (∑ t ∈ Finset.range Y, f t) +
        c * (∑ t ∈ Finset.range Y, g t) := by
      simp only [f, g, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    rw [hs]
    dsimp [g]
    ring
  · ring

theorem weighted_limit (c : ℝ)
    (hN : Tendsto (fun Y : ℕ => count Y / (Y : ℝ)) atTop (𝓝 c)) :
    Tendsto (fun Y : ℕ => weighted Y / (Y : ℝ) ^ 2)
      atTop (𝓝 (c / 2)) := by
  have hs := sum_linear_asymptotic count c hN
  have hsub := hN.sub hs
  have hsub' : Tendsto (fun Y : ℕ => count Y / (Y : ℝ) -
      (∑ t ∈ Finset.range Y, count (t + 1)) / (Y : ℝ) ^ 2)
      atTop (𝓝 (c / 2)) := by
    convert hsub using 1 <;> ring
  apply hsub'.congr'
  filter_upwards [eventually_ge_atTop 1] with Y hY
  have hy : (Y : ℝ) ≠ 0 := by exact_mod_cast (show Y ≠ 0 by omega)
  have h := weighted_partial_sum Y
  have heq : weighted Y = (Y : ℝ) * count Y -
      ∑ t ∈ Finset.range Y, count (t + 1) := by linarith
  rw [heq]
  field_simp

theorem partners_limit
    (hN : Tendsto (fun Y : ℕ => count Y / (Y : ℝ))
      atTop (𝓝 (1 / baseNorm))) :
    Tendsto (fun Y : ℕ => ((partners Y).card : ℝ) / (Y : ℝ) ^ 2)
      atTop (𝓝 (1 / (2 * baseNorm))) := by
  have hb : baseNorm ≠ 0 := by
    have hnorm : baseNorm = ‖PartnerAmplitudeConstant.ordinary‖ := rfl
    rw [hnorm]
    exact ne_of_gt PartnerAmplitudeConstant.nonzero
  have h := weighted_limit (1 / baseNorm) hN
  have htarget : (1 / baseNorm) / 2 = 1 / (2 * baseNorm) := by
    field_simp
  rw [htarget] at h
  apply h.congr'
  filter_upwards with Y
  rw [partners_card]

theorem conditional_finish
    (hN : Tendsto (fun Y : ℕ => ((levels Y).card : ℝ) / (Y : ℝ))
      atTop (𝓝 (1 / baseNorm))) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T,
      ∃ F : Finset (Σ s : ℕ, DirichletCharacter ℂ s),
        (∀ b, b ∈ F ↔ (b.1 ≠ 0 ∧ b.2.IsPrimitive) ∧
          baseNorm < (Y : ℝ) * ‖mainRow b.2‖) ∧
        |(F.card : ℝ) / (Y : ℝ) ^ 2 - 1 / (2 * baseNorm)| ≤ ε := by
  have hb : 0 < baseNorm := by
    have hnorm : baseNorm = ‖PartnerAmplitudeConstant.ordinary‖ := rfl
    rw [hnorm]
    exact PartnerAmplitudeConstant.nonzero
  have hlim := partners_limit hN
  intro ε hε
  rcases Metric.tendsto_atTop.1 hlim ε hε with ⟨T, hT⟩
  refine ⟨T, fun Y hY => ⟨partners Y, (fun b => mem_partners Y b hb), ?_⟩⟩
  have h := hT Y hY
  simpa [Real.dist_eq] using h.le

end PartnerAmplitudeFinish

end
end

theorem Conjectures.Goldbach.PartnerPrincipalAmplitudeTail :
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
  exact ∀ ε : ℝ, 0 < ε → ∃ T : ℕ, ∀ Y ≥ T, ∃ F : Finset B, (∀ b, b ∈ F ↔ valid b ∧ ‖O 2‖ < (Y:ℝ)*‖S P b.2 2‖) ∧ |(F.card:ℝ)/(Y:ℝ)^2 - 1/(2*‖O 2‖)| ≤ ε := by
  exact PartnerAmplitudeFinish.conditional_finish PartnerAmplitudeComparison.unweighted
