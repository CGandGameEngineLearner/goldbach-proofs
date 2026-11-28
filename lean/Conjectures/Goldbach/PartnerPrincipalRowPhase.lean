import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-!
确定平凡首特征 `1 : DirichletCharacter ℂ 1` 与任意原始搭档 `β : DirichletCharacter ℂ s`
在偶数目标 `m > 0` 处的完整扭曲奇异级数复数值（包括复相位、振幅与严格消失条件）。
复用已合并社区模块 `Conjectures.Goldbach.SharpSingularSeriesRatios` 中的
CRT 乘积分解 `full_product`、`reassemble`、`component_conductor` 与 `mixed_vanishes`。
-/

namespace PartnerPrincipalRowPhaseProof
open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open PrimePowerTwistedGoldbachDensity
open scoped BigOperators Classical

/-- 交换局部 Jacobi 型和 `J` 的两个特征参数。 -/
private theorem swap_J {q : ℕ} [NeZero q] (A B : DirichletCharacter ℂ q) (m : ZMod q) :
    J A B m = J B A m := by
  unfold J
  rw [← Equiv.sum_comp (Equiv.subLeft m) (fun x : ZMod q => A x * B (m - x))]
  simp [mul_comm]

/-- 素模数 `p` 上的非平凡特征全和为零。 -/
private theorem sum_char_eq_zero {p : ℕ} [Fact p.Prime] {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1) :
    (∑ x : ZMod p, χ x) = 0 := by
  have hp : p.Prime := Fact.out
  have : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr hp.ne_one
  have hex : ∃ u : (ZMod p)ˣ, χ (u : ZMod p) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hχ
    apply MulChar.ext
    intro u
    rw [MulChar.one_apply u.isUnit]
    exact hall u
  obtain ⟨u, hu⟩ := hex
  have hu0 : (u : ZMod p) ≠ 0 := by
    intro h0
    have h1 : ((u : ZMod p) * (u⁻¹ : (ZMod p)ˣ)) = 1 := u.mul_inv
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hshift : χ (u : ZMod p) * (∑ x : ZMod p, χ x) = ∑ x : ZMod p, χ x := by
    rw [Finset.mul_sum]
    calc
      (∑ x : ZMod p, χ (u : ZMod p) * χ x) = ∑ x : ZMod p, χ ((u : ZMod p) * x) := by
        apply Finset.sum_congr rfl
        intro x _
        rw [map_mul]
      _ = ∑ x : ZMod p, χ x := Equiv.sum_comp (Equiv.mulLeft₀ (u : ZMod p) hu0) χ
  have h0 : (χ (u : ZMod p) - 1) * (∑ x : ZMod p, χ x) = 0 := by
    linear_combination hshift
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hu)

/-- 素模数 `p` 处，平凡特征与非平凡特征的局部和 `J 1 χ m = - χ m`（含 `m = 0` 时为零）。 -/
private theorem J_one_prime {p : ℕ} [Fact p.Prime] {χ : DirichletCharacter ℂ p} (hχ : χ ≠ 1)
    (m : ZMod p) :
    J (1 : DirichletCharacter ℂ p) χ m = -χ m := by
  have hp : p.Prime := Fact.out
  have : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr hp.ne_one
  unfold J
  have hterm (x : ZMod p) :
      (1 : DirichletCharacter ℂ p) x * χ (m - x) = if x = 0 then 0 else χ (m - x) := by
    by_cases hx : x = 0
    · subst hx
      simp [MulChar.map_zero]
    · have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
      simp [hx, MulChar.one_apply hu]
  simp_rw [hterm]
  have hsplit : (∑ x : ZMod p, if x = 0 then (0 : ℂ) else χ (m - x)) + χ m =
      ∑ x : ZMod p, χ (m - x) := by
    rw [← Finset.add_sum_erase univ (fun x : ZMod p => χ (m - x)) (mem_univ 0)]
    rw [← Finset.add_sum_erase univ (fun x : ZMod p => if x = 0 then (0 : ℂ) else χ (m - x))
      (mem_univ 0)]
    simp only [↓reduceIte, zero_add, sub_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro x hx
    rw [ite_eq_right (Finset.ne_of_mem_erase hx)]
  have htot : (∑ x : ZMod p, χ (m - x)) = 0 :=
    (Equiv.sum_comp (Equiv.subLeft m) χ).trans (sum_char_eq_zero hχ)
  linear_combination hsplit + htot

/-- 素模数 `p` 且 `m ≠ 0` 处，`J 1 1 m = p - 2`。 -/
private theorem J_one_one_prime {p : ℕ} [Fact p.Prime] {m : ZMod p} (hm : m ≠ 0) :
    J (1 : DirichletCharacter ℂ p) 1 m = (p : ℂ) - 2 := by
  have hp : p.Prime := Fact.out
  have : Nontrivial (ZMod p) := ZMod.nontrivial_iff.mpr hp.ne_one
  rw [principal_card]
  have hfilt : univ.filter (admissible m) = (univ.erase (0 : ZMod p)).erase m := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_erase, admissible, isUnit_iff_ne_zero,
      sub_ne_zero, and_true]
    constructor
    · rintro ⟨hx0, hmx⟩
      exact ⟨Ne.symm hmx, hx0⟩
    · rintro ⟨hxm, hx0⟩
      exact ⟨hx0, Ne.symm hxm⟩
  rw [hfilt, card_erase_of_mem (mem_erase.mpr ⟨hm, mem_univ m⟩), card_erase_of_mem (mem_univ 0),
      card_univ, ZMod.card]
  have h2 : 2 ≤ p := hp.two_le
  have hsub : p - 1 - 1 = p - 2 := by omega
  rw [hsub, Nat.cast_sub h2]
  norm_num

/-- 单位特征在 CRT 分量映射下仍为单位特征。 -/
private theorem component_one {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ}
    {L : ℕ} (e : ZMod L ≃+* ∀ i, ZMod (q i)) (i : ι) :
    component e (1 : DirichletCharacter ℂ L) i = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.one_apply u.isUnit]
  let v : ∀ j, ZMod (q j) := Pi.mulSingle i (u : ZMod (q i))
  change (1 : DirichletCharacter ℂ L) (e.symm v) = 1
  have hu : IsUnit (e.symm v) := by
    have hall : ∀ j, IsUnit (v j) := by
      intro j
      dsimp only [v]
      by_cases hj : j = i
      · subst hj
        simpa using u.isUnit
      · rw [Pi.mulSingle_eq_of_ne hj]
        exact isUnit_one
    exact (Pi.isUnit_iff.mpr hall).map e.symm
  exact MulChar.one_apply hu

/-- 当 `q = p` 为素数、特征 `χ` 原始且 `¬ p ∣ m` 时，局部比值等于 `- χ m / (p - 2)`。 -/
private theorem local_ratio_prime {p q : ℕ} [Fact p.Prime] [NeZero q] (hq : q = p)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (m : ℕ) (hpm : ¬ p ∣ m) :
    J (1 : DirichletCharacter ℂ q) χ (m : ZMod q) /
      J (1 : DirichletCharacter ℂ q) 1 (m : ZMod q) =
      ((-1 : ℂ) * χ (m : ZMod q)) / ((p : ℂ) - 2) := by
  subst hq
  have hq_prime : q.Prime := Fact.out
  have hne1 : χ ≠ 1 := by
    rintro rfl
    have hc : (1 : DirichletCharacter ℂ q).conductor = q := hχ
    rw [conductor_one] at hc
    exact hq_prime.ne_one hc.symm
  have hm0 : (m : ZMod q) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m q).mp hpm
  rw [J_one_prime hne1 (m : ZMod q), J_one_one_prime hm0]
  ring

/-- 当 `q = p` 为素数、特征 `χ` 原始且 `p ∣ m` 时，局部和 `J 1 χ m = 0`。 -/
private theorem local_zero_dvd {p q : ℕ} [Fact p.Prime] [NeZero q] (hq : q = p)
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (m : ℕ) (hpm : p ∣ m) :
    J (1 : DirichletCharacter ℂ q) χ (m : ZMod q) = 0 := by
  subst hq
  have hq_prime : q.Prime := Fact.out
  have hne1 : χ ≠ 1 := by
    rintro rfl
    have hc : (1 : DirichletCharacter ℂ q).conductor = q := hχ
    rw [conductor_one] at hc
    exact hq_prime.ne_one hc.symm
  have hm0 : (m : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff m q).mpr hpm
  rw [hm0, J_one_prime hne1 0, MulChar.map_zero, neg_zero]

/-- 当 `q = d * p`（其中 `p ∣ d`）且特征 `χ` 原始时，局部和 `J 1 χ m = 0`。 -/
private theorem local_zero_nonsquarefree {p q : ℕ} [Fact p.Prime] [NeZero q] (e : ℕ)
    (hq : q = p ^ (e + 2)) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (m : ℕ) :
    J (1 : DirichletCharacter ℂ q) χ (m : ZMod q) = 0 := by
  have hp : p.Prime := Fact.out
  let d : ℕ := p ^ (e + 1)
  have hd_pos : 0 < d := pow_pos hp.pos _
  let : NeZero d := ⟨hd_pos.ne'⟩
  have hq_eq : q = d * p := by rw [hq, pow_succ]
  subst hq_eq
  have hsup : ∀ a : ℕ, a.Coprime d → a.Coprime p := fun a ha =>
    ha.coprime_dvd_right (dvd_pow_self p (by omega))
  have h1lift : changeLevel (dvd_mul_right d p) (1 : DirichletCharacter ℂ d) =
      (1 : DirichletCharacter ℂ (d * p)) := by
    simp
  have hz := mixed_vanishes hp.one_lt hsup hχ (1 : DirichletCharacter ℂ d) (m : ZMod (d * p))
  change J χ (changeLevel (dvd_mul_right d p) (1 : DirichletCharacter ℂ d)) (m : ZMod (d * p)) = 0 at hz
  rw [h1lift] at hz
  rw [swap_J, hz]

/-- 主定理：平凡首特征行对任意原始搭档的精确复相位与消失条件。 -/
private theorem main {s : ℕ} [NeZero s] (β : DirichletCharacter ℂ s) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m) :
    series (1 : DirichletCharacter ℂ 1) β m =
      if Squarefree s ∧ s.Coprime m then
        series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
          ((-1 : ℂ) ^ s.primeFactors.card) * β (m : ZMod s) /
          (∏ p ∈ s.primeFactors, ((p : ℂ) - 2))
      else 0 := by
  let I := ↥s.primeFactors
  let Q (i : I) : ℕ := (i : ℕ) ^ s.factorization (i : ℕ)
  let (i : I) : NeZero (Q i) := ⟨(Nat.ordProj_pos s i).ne'⟩
  let e := ZMod.equivPi s (NeZero.ne s)
  have h1prim : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
    change (1 : DirichletCharacter ℂ 1).conductor = 1
    exact conductor_one
  have hfp := full_product e h1prim hβ (one_dvd s) (dvd_refl s) m hm he
  have h1ch : changeLevel (one_dvd s) (1 : DirichletCharacter ℂ 1) =
      (1 : DirichletCharacter ℂ s) := by simp
  have hβch : changeLevel (dvd_refl s) β = β := by simp
  rw [h1ch, hβch] at hfp
  simp_rw [component_one e] at hfp
  have hd : ∀ i : I, Q i ∣ s := fun i => Nat.ordProj_dvd s i
  have hc : Pairwise (fun i k : I => (Q i).Coprime (Q k)) := by
    intro i k hik
    have hne : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Subtype.ext h)
    have hi : (i : ℕ).Prime := (Nat.mem_primeFactors.mp i.property).1
    have hk : (k : ℕ).Prime := (Nat.mem_primeFactors.mp k.property).1
    exact ((Nat.coprime_primes hi hk).mpr hne).pow _ _
  have hBi_prim : ∀ i : I, (component e β i).IsPrimitive := by
    intro i
    change (component e β i).conductor = Q i
    rw [TwistedGoldbachConductorComponents.component_conductor e hd hc β i,
        hβ, Nat.gcd_eq_left (hd i)]
  rw [hfp]
  by_cases hcond : Squarefree s ∧ s.Coprime m
  · rw [ite_eq_left hcond]
    rcases hcond with ⟨hsq, hcop⟩
    have hfac_one : ∀ i : I, s.factorization (i : ℕ) = 1 := by
      intro i
      have hi := Nat.mem_primeFactors.mp i.property
      have hge1 : 1 ≤ s.factorization (i : ℕ) :=
        (hi.1.dvd_iff_one_le_factorization (NeZero.ne s)).mp hi.2.1
      by_contra hne1
      have hge2 : 2 ≤ s.factorization (i : ℕ) := by omega
      have hsqdvd : (i : ℕ) * (i : ℕ) ∣ s := by
        rw [← sq]
        exact (pow_dvd_pow (i : ℕ) hge2).trans (Nat.ordProj_dvd s i)
      exact hi.1.ne_one (Nat.isUnit_iff.mp (hsq (i : ℕ) hsqdvd))
    have hloc (i : I) :
        J (1 : DirichletCharacter ℂ (Q i)) (component e β i) (m : ZMod (Q i)) /
          J (1 : DirichletCharacter ℂ (Q i)) 1 (m : ZMod (Q i)) =
          ((-1 : ℂ) * component e β i (e (m : ZMod s) i)) / (((i : ℕ) : ℂ) - 2) := by
      have hi := Nat.mem_primeFactors.mp i.property
      let : Fact (i : ℕ).Prime := ⟨hi.1⟩
      have hQi : Q i = (i : ℕ) := by dsimp only [Q]; rw [hfac_one i, pow_one]
      have hpm : ¬ (i : ℕ) ∣ m := fun hdv =>
        hi.1.ne_one (Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd hi.2.1 hdv))
      have heval : e (m : ZMod s) i = (m : ZMod (Q i)) := by
        rw [map_natCast]
        rfl
      rw [heval]
      exact local_ratio_prime hQi (hBi_prim i) m hpm
    simp_rw [hloc]
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe, ← reassemble e β (m : ZMod s),
        Finset.prod_coe_sort s.primeFactors (fun p => ((p : ℂ) - 2))]
    ring
  · rw [ite_eq_right hcond]
    have hzero_exists : ∃ i : I,
        J (1 : DirichletCharacter ℂ (Q i)) (component e β i) (m : ZMod (Q i)) = 0 := by
      by_cases hsq : Squarefree s
      · have hncop : ¬ s.Coprime m := fun hc' => hcond ⟨hsq, hc'⟩
        have hgcd_ne : s.gcd m ≠ 1 := hncop
        obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd_ne
        have hps : p ∣ s := hpdvd.trans (Nat.gcd_dvd_left s m)
        have hpm : p ∣ m := hpdvd.trans (Nat.gcd_dvd_right s m)
        have hmem : p ∈ s.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hps, NeZero.ne s⟩
        let i : I := ⟨p, hmem⟩
        let : Fact p.Prime := ⟨hp⟩
        have hge1 : 1 ≤ s.factorization p :=
          (hp.dvd_iff_one_le_factorization (NeZero.ne s)).mp hps
        have hfac1 : s.factorization p = 1 := by
          by_contra hne1
          have hge2 : 2 ≤ s.factorization p := by omega
          have hsqdvd : p * p ∣ s := by
            rw [← sq]
            exact (pow_dvd_pow p hge2).trans (Nat.ordProj_dvd s p)
          exact hp.ne_one (Nat.isUnit_iff.mp (hsq p hsqdvd))
        have hQi : Q i = p := by dsimp only [Q, i]; rw [hfac1, pow_one]
        exact ⟨i, local_zero_dvd hQi (hBi_prim i) m hpm⟩
      · rw [Nat.squarefree_iff_prime_squarefree] at hsq
        push Not at hsq
        obtain ⟨p, hp, hpp_dvd⟩ := hsq
        have hps : p ∣ s := (dvd_mul_right p p).trans hpp_dvd
        have hmem : p ∈ s.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hps, NeZero.ne s⟩
        let i : I := ⟨p, hmem⟩
        let : Fact p.Prime := ⟨hp⟩
        have hge2 : 2 ≤ s.factorization p := by
          have hsq' : p ^ 2 ∣ s := by simpa [sq] using hpp_dvd
          exact (hp.pow_dvd_iff_le_factorization (NeZero.ne s)).mp hsq'
        obtain ⟨k, hk⟩ : ∃ k, s.factorization p = k + 2 := ⟨s.factorization p - 2, by omega⟩
        have hQi : Q i = p ^ (k + 2) := by dsimp only [Q, i]; rw [hk]
        exact ⟨i, local_zero_nonsquarefree k hQi (hBi_prim i) m⟩
    obtain ⟨i, hi0⟩ := hzero_exists
    have hprod0 :
        (∏ j : I,
          J (1 : DirichletCharacter ℂ (Q j)) (component e β j) (m : ZMod (Q j)) /
            J (1 : DirichletCharacter ℂ (Q j)) 1 (m : ZMod (Q j))) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hi0, zero_div]
    rw [hprod0, mul_zero]

end PartnerPrincipalRowPhaseProof

theorem Conjectures.Goldbach.PartnerPrincipalRowPhase :
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
  exact ∀ (s : ℕ) [NeZero s] (β : DirichletCharacter ℂ s), β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → S P β m = if Squarefree s ∧ s.Coprime m then O m * ((-1:ℂ)^s.primeFactors.card) * β (m:ZMod s) / (∏ p ∈ s.primeFactors, ((p:ℂ)-2)) else 0
:= by
  classical
  dsimp only
  intro s inst β hβ m hm he
  exact PartnerPrincipalRowPhaseProof.main β hβ m hm he
