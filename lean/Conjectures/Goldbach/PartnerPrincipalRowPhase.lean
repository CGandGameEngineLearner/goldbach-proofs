import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-! Exact complex evaluation of the principal row `S 1 β m` for every primitive
Dirichlet character `β` of modulus `s` and every positive even target `m`.

Reuses the global CRT factorization (`TwistedGoldbachLocalProduct.full_product`),
conductor factorization (`TwistedGoldbachConductorComponents.global_conductor`),
and mixed prime-power vanishing (`PrimePowerTwistedGoldbachDensity.mixed_vanishes`)
from `Conjectures.Goldbach.SharpSingularSeriesRatios` (PR #4023). -/

namespace PartnerPrincipalRowPhaseProof

open Finset DirichletCharacter
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open TwistedGoldbachConductorRatio TwistedGoldbachLocalProduct
open TwistedGoldbachConductorComponents PrimePowerTwistedGoldbachDensity
open scoped BigOperators Classical

private theorem swap_J {q : ℕ} [NeZero q] (A B : DirichletCharacter ℂ q) (m : ZMod q) :
    J A B m = J B A m := by
  unfold J
  rw [← Equiv.sum_comp (Equiv.subLeft m) (fun x : ZMod q => A x * B (m - x))]
  simp [mul_comm]

private theorem component_isPrimitive {s : ℕ} [NeZero s]
    {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ι → ℕ} [∀ i, NeZero (q i)]
    (e : ZMod s ≃+* ∀ i, ZMod (q i))
    (hd : ∀ i, q i ∣ s) (hc : Pairwise (fun i k => (q i).Coprime (q k)))
    (hprod : ∏ i, q i = s)
    {β : DirichletCharacter ℂ s} (hβ : β.IsPrimitive) (i₀ : ι) :
    (component e β i₀).IsPrimitive := by
  have hle (i : ι) : (component e β i).conductor ≤ q i :=
    Nat.le_of_dvd (NeZero.pos (q i)) (component e β i).conductor_dvd_level
  have hpos (i : ι) : 0 < (component e β i).conductor :=
    Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero (NeZero.ne (q i))
      (component e β i).conductor_dvd_level)
  have heq : ∏ i, (component e β i).conductor = ∏ i, q i := by
    rw [← global_conductor e hd hc β, hβ, hprod]
  by_contra hnot
  have hlt : (component e β i₀).conductor < q i₀ :=
    lt_of_le_of_ne (hle i₀) hnot
  have hprod_lt : (∏ i, (component e β i).conductor) < ∏ i, q i := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀),
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)]
    have hrest_le :
        (∏ i ∈ Finset.univ.erase i₀, (component e β i).conductor) ≤
          ∏ i ∈ Finset.univ.erase i₀, q i :=
      Finset.prod_le_prod' (fun i _ => hle i)
    have hrest_pos : 0 < ∏ i ∈ Finset.univ.erase i₀, (component e β i).conductor :=
      Finset.prod_pos (fun i _ => hpos i)
    exact lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hlt hrest_pos)
      (Nat.mul_le_mul_left (q i₀) hrest_le)
  exact hprod_lt.ne heq

private theorem local_J_one_zero {p : ℕ} [hp : Fact p.Prime]
    {B : DirichletCharacter ℂ p} (hB : B ≠ 1) :
    J (1 : DirichletCharacter ℂ p) B 0 = 0 := by
  unfold J
  have hterm (x : ZMod p) :
      (1 : DirichletCharacter ℂ p) x * B (0 - x) = B (-1) * B x := by
    by_cases hx : x = 0
    · subst hx
      have h0 : ¬ IsUnit (0 : ZMod p) := by
        simpa [isUnit_iff_ne_zero]
      rw [MulChar.map_nonunit _ h0, MulChar.map_nonunit _ h0, zero_mul, mul_zero]
    · have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
      rw [MulChar.one_apply hu, one_mul, zero_sub, ← neg_one_mul x, map_mul]
  calc
    (∑ x : ZMod p, (1 : DirichletCharacter ℂ p) x * B (0 - x))
        = ∑ x : ZMod p, B (-1) * B x := Finset.sum_congr rfl fun x _ => hterm x
    _ = B (-1) * ∑ x : ZMod p, B x := (Finset.mul_sum _ _ _).symm
    _ = B (-1) * 0 := by rw [MulChar.sum_eq_zero_of_ne_one hB]
    _ = 0 := mul_zero _

private theorem local_J_one_prim {p : ℕ} [hp : Fact p.Prime]
    {B : DirichletCharacter ℂ p} (hB : B ≠ 1) {m : ZMod p} (hm : m ≠ 0) :
    J (1 : DirichletCharacter ℂ p) B m = -B m := by
  unfold J
  have h0 : ¬ IsUnit (0 : ZMod p) := by simpa [isUnit_iff_ne_zero]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod p)),
    MulChar.map_nonunit _ h0, zero_mul, zero_add]
  have hrest :
      (∑ x ∈ Finset.univ.erase (0 : ZMod p),
        (1 : DirichletCharacter ℂ p) x * B (m - x)) =
        ∑ x ∈ Finset.univ.erase (0 : ZMod p), B (m - x) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hu : IsUnit x := isUnit_iff_ne_zero.mpr (Finset.ne_of_mem_erase hx)
    rw [MulChar.one_apply hu, one_mul]
  rw [hrest]
  have hfull : (∑ x : ZMod p, B (m - x)) = 0 := by
    have heq : (∑ x : ZMod p, B (Equiv.subLeft m x)) = ∑ y : ZMod p, B y :=
      Equiv.sum_comp (Equiv.subLeft m) (fun y : ZMod p => B y)
    exact heq.trans (MulChar.sum_eq_zero_of_ne_one hB)
  have hsplit := Finset.add_sum_erase Finset.univ (fun x : ZMod p => B (m - x))
    (Finset.mem_univ (0 : ZMod p))
  rw [sub_zero, hfull] at hsplit
  exact eq_neg_of_add_eq_zero_right hsplit

private theorem local_J_one_one {p : ℕ} [hp : Fact p.Prime] {m : ZMod p} (hm : m ≠ 0) :
    J (1 : DirichletCharacter ℂ p) 1 m = (p : ℂ) - 2 := by
  unfold J
  let S := (Finset.univ.erase (0 : ZMod p)).erase m
  have hmem : m ∈ Finset.univ.erase (0 : ZMod p) :=
    Finset.mem_erase.mpr ⟨hm, Finset.mem_univ _⟩
  have hsum : (∑ x : ZMod p, (1 : DirichletCharacter ℂ p) x * (1 : DirichletCharacter ℂ p) (m - x)) =
      ∑ _x ∈ S, (1 : ℂ) := by
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · apply Finset.sum_congr rfl
      intro x hx
      have hxm : x ≠ m := (Finset.mem_erase.mp hx).1
      have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).1
      have hu1 : IsUnit x := isUnit_iff_ne_zero.mpr hx0
      have hu2 : IsUnit (m - x) := isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxm.symm)
      rw [MulChar.one_apply hu1, MulChar.one_apply hu2, mul_one]
    · intro x _ hxS
      by_cases hx0 : x = 0
      · subst hx0
        have h0 : ¬ IsUnit (0 : ZMod p) := by simpa [isUnit_iff_ne_zero]
        rw [MulChar.map_nonunit _ h0, zero_mul]
      · have hxm : x = m := by
          by_contra hne
          exact hxS (Finset.mem_erase.mpr ⟨hne, Finset.mem_erase.mpr ⟨hx0, Finset.mem_univ _⟩⟩)
        subst hxm
        have h0 : ¬ IsUnit (0 : ZMod p) := by simpa [isUnit_iff_ne_zero]
        rw [sub_self, MulChar.map_nonunit _ h0, mul_zero]
  rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : S.card = p - 2 := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem hmem, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card]
    omega
  rw [hcard, Nat.cast_sub hp.out.two_le]
  norm_num

private theorem ne_one_of_isPrimitive_prime {p : ℕ} [hp : Fact p.Prime]
    {B : DirichletCharacter ℂ p} (hB : B.IsPrimitive) : B ≠ 1 := by
  intro h
  subst h
  have hc : (1 : DirichletCharacter ℂ p).conductor = 1 := DirichletCharacter.conductor_one
  have hp2 := hp.out.two_le
  change (1 : DirichletCharacter ℂ p).conductor = p at hB
  omega

theorem main_theorem :
    ∀ (s : ℕ) [NeZero s] (β : DirichletCharacter ℂ s), β.IsPrimitive →
      ∀ m : ℕ, 0 < m → Even m →
        series (1 : DirichletCharacter ℂ 1) β m =
          if Squarefree s ∧ s.Coprime m then
            series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
              ((-1 : ℂ) ^ s.primeFactors.card) * β (m : ZMod s) /
              (∏ p ∈ s.primeFactors, ((p : ℂ) - 2))
          else 0 := by
  classical
  intro s _ β hβ m hm he
  have hsne : s ≠ 0 := NeZero.ne s
  let I := ↥s.primeFactors
  let Q (i : I) : ℕ := (i : ℕ) ^ s.factorization i
  haveI (i : I) : Fact (i : ℕ).Prime := ⟨(Nat.mem_primeFactors.mp i.property).1⟩
  haveI (i : I) : NeZero (i : ℕ) := ⟨(Nat.mem_primeFactors.mp i.property).1.ne_zero⟩
  haveI (i : I) : NeZero (Q i) := ⟨(Nat.ordProj_pos s i).ne'⟩
  let e : ZMod s ≃+* ∀ i : I, ZMod (Q i) := ZMod.equivPi s hsne
  have hd (i : I) : Q i ∣ s := Nat.ordProj_dvd s i
  have hc : Pairwise (fun i k : I => (Q i).Coprime (Q k)) := by
    intro i k hik
    have hne : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Subtype.ext h)
    have hp1 : (i : ℕ).Prime := (Nat.mem_primeFactors.mp i.property).1
    have hp2 : (k : ℕ).Prime := (Nat.mem_primeFactors.mp k.property).1
    exact ((hp1.coprime_iff_not_dvd.mpr fun hdvd =>
      hne ((Nat.prime_dvd_prime_iff_eq hp1 hp2).mp hdvd)).pow_left _).pow_right _
  have hprod : ∏ i : I, Q i = s := by
    rw [Finset.prod_coe_sort s.primeFactors (fun p => p ^ s.factorization p)]
    exact (Nat.prod_primeFactors_pow_factorization hsne).symm
  have hprim (i : I) : (component e β i).IsPrimitive :=
    component_isPrimitive e hd hc hprod hβ i
  have hfp := full_product e
    (show (1 : DirichletCharacter ℂ 1).IsPrimitive from DirichletCharacter.conductor_one)
    hβ (one_dvd s) dvd_rfl m hm he
  simp only [changeLevel_one, component_one, changeLevel_self] at hfp
  by_cases hcond : Squarefree s ∧ s.Coprime m
  · rw [if_pos hcond]
    obtain ⟨hsq, hcop⟩ := hcond
    have hfac (i : I) : Q i = (i : ℕ) := by
      have hmem := Nat.mem_primeFactors.mp i.property
      have hge : 1 ≤ s.factorization i := (hmem.1.dvd_iff_one_le_factorization hsne).mp hmem.2.1
      have hle : s.factorization i ≤ 1 := (Nat.squarefree_iff_factorization_le_one hsne).mp hsq i
      dsimp only [Q]
      rw [show s.factorization i = 1 by omega, pow_one]
    let e' : ZMod s ≃+* ∀ i : I, ZMod (i : ℕ) :=
      e.trans (RingEquiv.piCongrRight fun i => ZMod.ringEquivCongr (hfac i))
    have hd' (i : I) : (i : ℕ) ∣ s := (Nat.mem_primeFactors.mp i.property).2.1
    have hc' : Pairwise (fun i k : I => ((i : ℕ)).Coprime (k : ℕ)) := by
      intro i k hik
      have hne : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Subtype.ext h)
      have hp1 : (i : ℕ).Prime := (Nat.mem_primeFactors.mp i.property).1
      have hp2 : (k : ℕ).Prime := (Nat.mem_primeFactors.mp k.property).1
      exact hp1.coprime_iff_not_dvd.mpr fun hdvd =>
        hne ((Nat.prime_dvd_prime_iff_eq hp1 hp2).mp hdvd)
    have hprod' : ∏ i : I, (i : ℕ) = s := by
      calc (∏ i : I, (i : ℕ)) = ∏ i : I, Q i := Finset.prod_congr rfl fun i _ => (hfac i).symm
        _ = s := hprod
    have hprim' (i : I) : (component e' β i).IsPrimitive :=
      component_isPrimitive e' hd' hc' hprod' hβ i
    have hfp' := full_product e'
      (show (1 : DirichletCharacter ℂ 1).IsPrimitive from DirichletCharacter.conductor_one)
      hβ (one_dvd s) dvd_rfl m hm he
    simp only [changeLevel_one, component_one, changeLevel_self] at hfp'
    rw [hfp']
    have hlocal (i : I) :
        J (1 : DirichletCharacter ℂ (i : ℕ)) (component e' β i) (m : ZMod (i : ℕ)) /
          J (1 : DirichletCharacter ℂ (i : ℕ)) 1 (m : ZMod (i : ℕ)) =
          ((-1 : ℂ) * component e' β i (e' (m : ZMod s) i)) / (((i : ℕ) : ℂ) - 2) := by
      have hm_not_dvd : ¬ (i : ℕ) ∣ m := by
        intro hdvd
        have hp_prime : (i : ℕ).Prime := (Nat.mem_primeFactors.mp i.property).1
        have h1 : (i : ℕ) ∣ Nat.gcd s m := Nat.dvd_gcd (hd' i) hdvd
        rw [hcop.gcd_eq_one] at h1
        exact hp_prime.not_dvd_one h1
      have hm0 : (m : ZMod (i : ℕ)) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m (i : ℕ)).mp hm_not_dvd
      have hne1 : component e' β i ≠ 1 := ne_one_of_isPrimitive_prime (hprim' i)
      have he_m : e' (m : ZMod s) i = (m : ZMod (i : ℕ)) := by
        rw [map_natCast]
        rfl
      rw [local_J_one_prim hne1 hm0, local_J_one_one hm0, he_m]
      ring
    calc
      series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
          ∏ i : I, (J (1 : DirichletCharacter ℂ (i : ℕ)) (component e' β i) (m : ZMod (i : ℕ)) /
            J (1 : DirichletCharacter ℂ (i : ℕ)) 1 (m : ZMod (i : ℕ)))
          = series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
              ∏ i : I, (((-1 : ℂ) * component e' β i (e' (m : ZMod s) i)) /
                (((i : ℕ) : ℂ) - 2)) := by
            congr 1
            exact Finset.prod_congr rfl fun i _ => hlocal i
      _ = series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
            ((∏ i : I, ((-1 : ℂ) * component e' β i (e' (m : ZMod s) i))) /
              (∏ i : I, (((i : ℕ) : ℂ) - 2))) := by
            rw [Finset.prod_div_distrib]
      _ = series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
            ((((-1 : ℂ) ^ s.primeFactors.card) * β (m : ZMod s)) /
              (∏ p ∈ s.primeFactors, ((p : ℂ) - 2))) := by
            congr 1
            rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe,
              ← reassemble e' β (m : ZMod s),
              Finset.prod_coe_sort s.primeFactors (fun p => (p : ℂ) - 2)]
      _ = series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m *
            ((-1 : ℂ) ^ s.primeFactors.card) * β (m : ZMod s) /
            (∏ p ∈ s.primeFactors, ((p : ℂ) - 2)) := by
            rw [← mul_div_assoc, mul_assoc]
  · rw [if_neg hcond, hfp]
    suffices hzero : ∃ i₀ : I,
        J (1 : DirichletCharacter ℂ (Q i₀)) (component e β i₀) (m : ZMod (Q i₀)) = 0 by
      obtain ⟨i₀, hi₀⟩ := hzero
      have hp0 : (∏ i : I,
          (J (1 : DirichletCharacter ℂ (Q i)) (component e β i) (m : ZMod (Q i)) /
            J (1 : DirichletCharacter ℂ (Q i)) 1 (m : ZMod (Q i)))) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ i₀)
        rw [hi₀, zero_div]
      rw [hp0, mul_zero]
    by_cases hsq : Squarefree s
    · have hnotcop : ¬ s.Coprime m := fun h => hcond ⟨hsq, h⟩
      obtain ⟨p, hp_prime, hps, hpm⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnotcop
      have hp_mem : p ∈ s.primeFactors := Nat.mem_primeFactors.mpr ⟨hp_prime, hps, hsne⟩
      let i₀ : I := ⟨p, hp_mem⟩
      have hfac0 : Q i₀ = p := by
        have hge : 1 ≤ s.factorization p := (hp_prime.dvd_iff_one_le_factorization hsne).mp hps
        have hle : s.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hsne).mp hsq p
        dsimp only [Q, i₀]
        rw [show s.factorization p = 1 by omega, pow_one]
      refine ⟨i₀, ?_⟩
      have hprim0 : (component e β i₀).IsPrimitive := hprim i₀
      have hB : ∀ [NeZero (Q i₀)] (B : DirichletCharacter ℂ (Q i₀)), B.IsPrimitive →
          J (1 : DirichletCharacter ℂ (Q i₀)) B (m : ZMod (Q i₀)) = 0 := by
        rw [hfac0]
        intro _ B hBp
        haveI : Fact p.Prime := ⟨hp_prime⟩
        have hm0 : (m : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff m p).mpr hpm
        rw [hm0]
        exact local_J_one_zero (ne_one_of_isPrimitive_prime hBp)
      exact hB (component e β i₀) hprim0
    · have hnotle : ¬ ∀ p, s.factorization p ≤ 1 :=
        mt (Nat.squarefree_iff_factorization_le_one hsne).mpr hsq
      push_neg at hnotle
      obtain ⟨p, hp_gt⟩ := hnotle
      have hp_mem : p ∈ s.primeFactors := by
        rw [← Nat.support_factorization]
        exact Finsupp.mem_support_iff.mpr (by omega)
      have hp_prime : p.Prime := (Nat.mem_primeFactors.mp hp_mem).1
      let i₀ : I := ⟨p, hp_mem⟩
      let k := s.factorization p - 1
      have hk : 1 ≤ k := by dsimp [k]; omega
      have hQeq : Q i₀ = p ^ k * p := by
        dsimp only [Q, i₀, k]
        rw [← pow_succ, show s.factorization p - 1 + 1 = s.factorization p by omega]
      refine ⟨i₀, ?_⟩
      have hprim0 : (component e β i₀).IsPrimitive := hprim i₀
      have hvan : ∀ [NeZero (Q i₀)] (B : DirichletCharacter ℂ (Q i₀)), B.IsPrimitive →
          J (1 : DirichletCharacter ℂ (Q i₀)) B (m : ZMod (Q i₀)) = 0 := by
        rw [hQeq]
        intro _ B hBp
        haveI : NeZero (p ^ k) := ⟨(pow_pos hp_prime.pos k).ne'⟩
        haveI : NeZero p := ⟨hp_prime.ne_zero⟩
        have hsup : ∀ a : ℕ, a.Coprime (p ^ k) → a.Coprime p := fun a ha =>
          ha.coprime_dvd_right (dvd_pow_self p (by omega))
        have hmv := mixed_vanishes hp_prime.one_lt hsup hBp (1 : DirichletCharacter ℂ (p ^ k))
          (m : ZMod (p ^ k * p))
        rw [changeLevel_one] at hmv
        rw [swap_J]
        exact hmv
      exact hvan (component e β i₀) hprim0

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
  exact ∀ (s : ℕ) [NeZero s] (β : DirichletCharacter ℂ s), β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → S P β m = if Squarefree s ∧ s.Coprime m then O m * ((-1:ℂ)^s.primeFactors.card) * β (m:ZMod s) / (∏ p ∈ s.primeFactors, ((p:ℂ)-2)) else 0 := by
  classical
  dsimp only
  exact PartnerPrincipalRowPhaseProof.main_theorem
