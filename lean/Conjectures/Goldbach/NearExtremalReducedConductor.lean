import Mathlib
import Conjectures.Goldbach.SharpSingularSeriesRatios

/-! Localization of large twisted Goldbach singular series by their prime-power Jacobi factors. -/

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open Finset DirichletCharacter Real TwistedGoldbachLocalProduct TwistedGoldbachConductorRatio
open TwistedGoldbachConductorValue TwistedGoldbachConductorComponents TwistedGoldbachExceptionalGap
open B13BilateralVaughanReductionProof
open scoped BigOperators Classical

namespace NearExtremalProof

theorem bad_prime_of_not_dvd {j : ℕ} (hj : 0 < j) (hn : ¬ j ∣ 180) :
    ∃ p : ℕ, p.Prime ∧ p ∣ j ∧
      ((p = 2 ∧ 8 ∣ j) ∨ (p = 3 ∧ 27 ∣ j) ∨ 7 ≤ p ∨ (p = 5 ∧ 25 ∣ j)) := by
  by_contra none
  apply hn
  apply (Nat.factorization_le_iff_dvd hj.ne' (by decide : (180 : ℕ) ≠ 0)).mp
  intro p
  by_contra! large
  have pp : p.Prime := by
    by_contra np
    rw [Nat.factorization_eq_zero_of_not_prime j np] at large
    omega
  have dj : p ∣ j := by
    by_contra nd
    rw [Nat.factorization_eq_zero_of_not_dvd nd] at large
    omega
  apply none
  refine ⟨p, pp, dj, ?_⟩
  by_cases h7 : 7 ≤ p
  · exact Or.inr (Or.inr (Or.inl h7))
  have lb := pp.two_le
  have cases : p=2 ∨ p=3 ∨ p=5 := by
    interval_cases p <;> first | omega | norm_num at pp
  rcases cases with rfl | rfl | rfl
  · left
    refine ⟨rfl, (pp.pow_dvd_iff_le_factorization hj.ne' (k:=3)).mpr ?_⟩
    have lower : 2 ≤ (180:ℕ).factorization 2 := (pp.pow_dvd_iff_le_factorization (by decide : (180:ℕ)≠0)).mp (by decide : 2^2∣180)
    omega
  · right;left
    refine ⟨rfl, (pp.pow_dvd_iff_le_factorization hj.ne' (k:=3)).mpr ?_⟩
    have lower : 2 ≤ (180:ℕ).factorization 3 := (pp.pow_dvd_iff_le_factorization (by decide : (180:ℕ)≠0)).mp (by decide : 3^2∣180)
    omega
  · right;right;right
    refine ⟨rfl, (pp.pow_dvd_iff_le_factorization hj.ne' (k:=2)).mpr ?_⟩
    have lower : 1 ≤ (180:ℕ).factorization 5 := (pp.pow_dvd_iff_le_factorization (by decide : (180:ℕ)≠0)).mp (by decide : 5^1∣180)
    omega

theorem five_dvd_of_dvd_180_not_dvd_36 {j : ℕ} (h : j ∣ 180) (h' : ¬ j ∣ 36) : 5 ∣ j := by
  by_contra off
  have co : j.Coprime 5 := ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr off).symm
  exact h' (co.dvd_of_dvd_mul_right (show j ∣ 36*5 from h))

end NearExtremalProof

namespace NearExtremalProof

open Conjectures.Goldbach.SharpSingularSeriesRatiosProof
open Conjectures.Goldbach.SharpSingularSeriesRatiosProof.TwistedGoldbachLocalProduct
open DirichletCharacter Real TwistedGoldbachConductorRatio

def badPower (p t m : ℕ) : Prop :=
  (p=2 ∧ 8≤t) ∨ (p=3 ∧ 27≤t) ∨ 7≤p ∨ (p=5 ∧ (25≤t ∨ 5∣m))

private theorem prime_large_sqrt {p : ℕ} (hp : 7≤p) :
    sqrt 2*sqrt p ≤ (p:ℝ)-2 := by
  have H : (7:ℝ)≤p := by exact_mod_cast hp
  apply (sq_le_sq₀ (by positivity) (by linarith)).mp
  rw [mul_pow,sq_sqrt (by norm_num : (0:ℝ)≤2),sq_sqrt (Nat.cast_nonneg _)]
  nlinarith only [H,mul_nonneg (show 0≤(p:ℝ)-7 by linarith only [H]) (show 0≤(p:ℝ)+1 by linarith only [H])]

private theorem power_arithmetic {p t m : ℕ} (pt : p≤t) (pp : 2≤p) (he : Even m) (bad : badPower p t m) :
    sqrt 2*(p:ℝ) ≤ (if p∣m then (p:ℝ)-1 else (p:ℝ)-2)*sqrt t := by
  have P : (2:ℝ)≤p := by exact_mod_cast pp
  have T : (p:ℝ)≤t := by exact_mod_cast pt
  have pos : 0≤(if p∣m then (p:ℝ)-1 else (p:ℝ)-2) := by split <;> linarith only [P]
  apply (sq_le_sq₀ (by positivity) (mul_nonneg pos (sqrt_nonneg _))).mp
  rw [mul_pow,mul_pow,sq_sqrt (by norm_num : (0:ℝ)≤2),sq_sqrt (Nat.cast_nonneg _)]
  rcases bad with ⟨rfl,b⟩|⟨rfl,b⟩|b|⟨rfl,b|b⟩
  · rw [ite_eq_left (even_iff_two_dvd.mp he)]
    norm_num;exact_mod_cast b
  · have H : (27:ℝ)≤t := by exact_mod_cast b
    split_ifs <;> norm_num <;> first | omega | linarith only [H]
  · have H : (7:ℝ)≤p := by exact_mod_cast b
    have upper : 2*(p:ℝ)≤((p:ℝ)-2)^2 := by
      nlinarith only [H,mul_nonneg (show 0≤(p:ℝ)-7 by linarith only [H]) (show 0≤(p:ℝ)+1 by linarith only [H])]
    have A := mul_le_mul_of_nonneg_right upper (Nat.cast_nonneg (α:=ℝ) p)
    have B := mul_le_mul_of_nonneg_left T (sq_nonneg ((p:ℝ)-2))
    have C := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (show 0≤(p:ℝ)-2 by linarith only [H])
      (show (p:ℝ)-2≤p-1 by linarith) 2) (Nat.cast_nonneg (α:=ℝ) t)
    split_ifs <;> nlinarith only [A,B,C]
  · have H : (25:ℝ)≤t := by exact_mod_cast b
    split_ifs <;> norm_num <;> first | omega | linarith only [H]
  · rw [ite_eq_left b];norm_num
    have H : (5:ℝ)≤t := by exact_mod_cast pt
    linarith only [H]

theorem power_gap_of_eq {p q : ℕ} [hp : Fact p.Prime] [NeZero q] (n : ℕ)
    (eqn : q=p*p^n) (m : ℕ) (he : Even m) (A B : DirichletCharacter ℂ q)
    (hA : A.IsPrimitive) (hB : B.IsPrimitive) :
    let t := q/(m.gcd q)
    p≤t → badPower p t m →
    sqrt 2*‖J A B (m:ZMod q)‖ ≤ ‖J (1 : DirichletCharacter ℂ q) 1 (m:ZMod q)‖ := by
  subst q
  intro t pt bad
  have top := TwistedGoldbachExceptionalGap.prime_power_bound n m hA hB (hp.out.one_lt.trans_le pt)
  have gap := power_arithmetic pt hp.out.two_le he bad
  have root : 0 < sqrt (t:ℝ) := sqrt_pos.mpr (by exact_mod_cast hp.out.pos.trans_le pt)
  apply le_of_mul_le_mul_right (a:=sqrt (t:ℝ)) _ root
  rw [TwistedGoldbachLocalProduct.ordinary_prime_power n m]
  have upper := mul_le_mul_of_nonneg_left top (sqrt_nonneg 2)
  have lower := mul_le_mul_of_nonneg_left gap (by positivity : 0≤((p^n:ℕ):ℝ))
  change sqrt 2*(‖J A B (m:ZMod (p*p^n))‖*sqrt (t:ℝ)) ≤ sqrt 2*((p*p^n:ℕ):ℝ) at upper
  push_cast at upper lower ⊢
  linarith only [upper,lower]

theorem prime_local_gap {p : ℕ} [Fact p.Prime] (m : ℕ)
    (A B : DirichletCharacter ℂ p) (mp : ¬p∣m) (hab : A≠1 ∨ B≠1) (big : 7≤p) :
    sqrt 2*‖J A B (m:ZMod p)‖ ≤ ‖J (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖ := by
  have nonzero : (m:ZMod p) ≠ 0 := mt (ZMod.natCast_eq_zero_iff m p).mp mp
  have top := SquarefreeTwistedGoldbachDensity.local_norm A B (m:ZMod p)
  have ordinary := SquarefreeTwistedGoldbachDensity.local_norm (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)
  have pair : ¬(A=1 ∧ B=1) := by tauto
  simp only [nonzero,ite_false,pair] at top
  simp only [nonzero,ite_false,and_self,ite_true] at ordinary
  change sqrt 2*‖SquarefreeTwistedGoldbachDensity.localSum A B (m:ZMod p)‖ ≤
    ‖SquarefreeTwistedGoldbachDensity.localSum (1 : DirichletCharacter ℂ p) 1 (m:ZMod p)‖
  rw [top,ordinary]
  split_ifs
  · have H : (7:ℝ)≤p := by exact_mod_cast big
    have S : sqrt 2 ≤ 2 := (sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
    linarith only [H,S]
  · exact prime_large_sqrt big

end NearExtremalProof

namespace NearExtremalProof

private theorem complementary_odd {L r m : ℕ} (rL : r ∣ L) (he : Even m)
    (good : TwistedGoldbachConductorValue.admissible r L)
    (div : L/r ∣ L/(m.gcd L)) : ¬2 ∣ L/r := by
  let a := L/r
  let g := m.gcd L
  let j := L/g
  have ra : r*a=L := Nat.mul_div_cancel' rL
  have gj : g*j=L := Nat.mul_div_cancel' (Nat.gcd_dvd_right m L)
  intro ha
  have cp : Nat.Coprime 2 r := good.2.of_dvd_left ha
  have twoL : 2 ∣ L := ra ▸ ha.trans (dvd_mul_left a r)
  have hdg : 2 ∣ g := Nat.dvd_gcd (even_iff_two_dvd.mp he) twoL
  have bad : 2*2 ∣ L := gj ▸ Nat.mul_dvd_mul hdg (ha.trans div)
  have badA : 2*2 ∣ a := (cp.pow_left 2).dvd_of_dvd_mul_left (ra ▸ bad)
  exact Nat.squarefree_iff_prime_squarefree.mp good.1 2 Nat.prime_two badA

private theorem small_complement {a : ℕ} (h : a ∣ 36) (hs : Squarefree a)
    (odd : ¬2 ∣ a) : a ∣ 3 := by
  have le := Nat.le_of_dvd (by decide : 0 < 36) h
  have hn : ¬ 9 ∣ a := Nat.squarefree_iff_prime_squarefree.mp hs 3 Nat.prime_three
  interval_cases a <;> norm_num at *

theorem not_reduced_36 {r s : ℕ} [NeZero r] [NeZero s] {α : DirichletCharacter ℂ r}
    {β : DirichletCharacter ℂ s} (hα : α.IsPrimitive) (hβ : β.IsPrimitive)
    (m : ℕ) (hm : 0 < m) (he : Even m)
    (out : ¬SharpTwistedGoldbachGap.exceptional α β m) (nz : series α β m ≠ 0) :
    ¬Nat.lcm r s/(m.gcd (Nat.lcm r s)) ∣ 36 := by
  let L := Nat.lcm r s
  let j := L/(m.gcd L)
  let d := (inversePair α β).conductor
  intro h36
  have good : supported r s L d j := (full_support hα hβ m hm he).mp nz
  have hr : r ∣ L := Nat.dvd_lcm_left ..
  have hs : s ∣ L := Nat.dvd_lcm_right ..
  obtain ⟨ra,sa⟩ := TwistedGoldbachConductorSuppression.complementary_dvd hα hβ (m := m) good
  have rj := ra.trans good.2.2.1
  have sj := sa.trans good.2.2.1
  have rsmall := small_complement (rj.trans h36) good.1.1 (complementary_odd hr he good.1 rj)
  have ssmall := small_complement (sj.trans h36) good.2.1.1 (complementary_odd hs he good.2.1 sj)
  have eqr : L/r=s/(r.gcd s) := by
    change (Nat.lcm r s)/r=s/(r.gcd s)
    rw [Nat.lcm_eq_mul_div,Nat.mul_div_assoc _ (Nat.gcd_dvd_right r s),Nat.mul_div_cancel_left _ (NeZero.pos r)]
  have eqs : L/s=r/(r.gcd s) := by
    change (Nat.lcm r s)/s=r/(r.gcd s)
    rw [Nat.lcm_comm,Nat.lcm_eq_mul_div,Nat.mul_div_assoc _ (Nat.gcd_dvd_right s r),
      Nat.mul_div_cancel_left _ (NeZero.pos s),Nat.gcd_comm]
  have splitj : j=Nat.lcm (r/(m.gcd r)) (s/(m.gcd s)) := TwistedGoldbachConductorSuppression.reduced_lcm m
  have hd : ((changeLevel (Nat.dvd_lcm_left r s) α) * (changeLevel (Nat.dvd_lcm_right r s) β)).conductor ∣ 36 := by
    simpa only [d,inversePair,conductor_inv] using good.2.2.1.trans h36
  exact out ⟨(splitj ▸ Nat.dvd_lcm_left ..).trans h36,(splitj ▸ Nat.dvd_lcm_right ..).trans h36,
    eqs ▸ ssmall,eqr ▸ rsmall,hd⟩

end NearExtremalProof

namespace NearExtremalProof

private theorem reduced_prime_part {L p : ℕ} (hp : p.Prime) (hL : L ≠ 0) (m : ℕ) :
    let q := p^L.factorization p
    q/(m.gcd q) = p^(L/(m.gcd L)).factorization p := by
  intro q
  let g := m.gcd L
  have gd : g ∣ L := Nat.gcd_dvd_right ..
  have Q : q ∣ L := Nat.ordProj_dvd L p
  have same : m.gcd q = q.gcd g := by
    change m.gcd q = q.gcd (m.gcd L)
    rw [Nat.gcd_left_comm, Nat.gcd_eq_left Q]
  have gq := prime_part_gcd hp hL gd
  change q.gcd g = p^g.factorization p at gq
  have le := (Nat.factorization_le_iff_dvd
    (Nat.gcd_pos_of_pos_right m (Nat.pos_of_ne_zero hL)).ne' hL).mpr gd p
  rw [same, gq, Nat.factorization_div gd]
  exact Nat.pow_div le hp.pos

private theorem primitive_source_dvd {p L r n : ℕ} (hp : p.Prime)
    (hr : r ∣ L) (good : TwistedGoldbachConductorValue.admissible r L)
    (hd : p^(n+2) ∣ L) : p^(n+2) ∣ r := by
  let a := L/r
  have eqn : r*a=L := Nat.mul_div_cancel' hr
  have hpow : p^(n+2) ∣ r*a := eqn ▸ hd
  by_cases hdpa : p ∣ a
  · have cop : p.Coprime r := good.2.of_dvd_left hdpa
    have all : p^(n+2) ∣ a := (cop.pow_left _).dvd_of_dvd_mul_left hpow
    have bad : p*p ∣ a := (show p*p ∣ p^(n+2) by
      rw [← pow_two]
      exact pow_dvd_pow _ (by omega)).trans all
    exact False.elim (Nat.squarefree_iff_prime_squarefree.mp good.1 p hp bad)
  · exact ((hp.coprime_iff_not_dvd.mpr hdpa).pow_left _).dvd_of_dvd_mul_right hpow

theorem bad_global {r s : ℕ} [NeZero r] [NeZero s]
    {α : DirichletCharacter ℂ r} {β : DirichletCharacter ℂ s}
    (hα : α.IsPrimitive) (hβ : β.IsPrimitive) (m : ℕ) (hm : 0 < m)
    (he : Even m) (p : ℕ) (hp : p.Prime)
    (pj : p ∣ Nat.lcm r s / (m.gcd (Nat.lcm r s)))
    (bad : (p=2 ∧ 8 ∣ Nat.lcm r s / (m.gcd (Nat.lcm r s))) ∨
      (p=3 ∧ 27 ∣ Nat.lcm r s / (m.gcd (Nat.lcm r s))) ∨ 7≤p ∨
      (p=5 ∧ (25 ∣ Nat.lcm r s / (m.gcd (Nat.lcm r s)) ∨ 5∣m))) :
    sqrt 2*‖series α β m‖ ≤
      ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖ := by
  classical
  let L := Nat.lcm r s
  let j := L/(m.gcd L)
  let hr : r ∣ L := Nat.dvd_lcm_left ..
  let hs : s ∣ L := Nat.dvd_lcm_right ..
  let d := (inversePair α β).conductor
  by_cases good : supported r s L d j
  swap
  · have zero := not_ne_iff.mp (mt (full_support hα hβ m hm he).mp good)
    rw [zero, norm_zero, mul_zero]
    positivity
  have lp : 0 < L := Nat.lcm_pos (NeZero.pos r) (NeZero.pos s)
  let _ : NeZero L := ⟨lp.ne'⟩
  have jd : j ∣ L := Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m L)
  have jp : 0 < j := Nat.pos_of_dvd_of_pos jd lp
  let _ : Fact p.Prime := ⟨hp⟩
  have pl : p ∣ L := pj.trans jd
  let i : L.primeFactors := ⟨p, Nat.mem_primeFactors.mpr ⟨hp, pl, lp.ne'⟩⟩
  let (k : L.primeFactors) : NeZero ((k:ℕ)^L.factorization k) :=
    ⟨(Nat.ordProj_pos L k).ne'⟩
  let e := ZMod.equivPi L lp.ne'
  let Q := p^L.factorization p
  let _ : NeZero Q := ⟨(Nat.ordProj_pos L p).ne'⟩
  let A := component e (changeLevel hr α) i
  let B := component e (changeLevel hs β) i
  let t := Q/(m.gcd Q)
  have qpos : 0 < Q := Nat.ordProj_pos ..
  have tpos : 0 < t := Nat.pos_of_dvd_of_pos
    (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m Q)) qpos
  have eqt : t=p^j.factorization p := reduced_prime_part hp lp.ne' m
  have lift (k : ℕ) (H : p^k ∣ j) : p^k ∣ t :=
    eqt ▸ (hp.pow_dvd_iff_dvd_ordProj jp.ne').mp H
  have pt : p ≤ t := Nat.le_of_dvd tpos (by
    simpa using lift 1 (by simpa using pj))
  have out : badPower p t m := by
    rcases bad with ⟨ep,h8⟩ | ⟨ep,h27⟩ | big | ⟨ep,h25 | hm5⟩
    · left
      refine ⟨ep, ?_⟩
      have h : p^3 ∣ t := lift 3 (by simpa [ep] using h8)
      simpa [ep] using Nat.le_of_dvd tpos h
    · right
      left
      refine ⟨ep, ?_⟩
      have h : p^3 ∣ t := lift 3 (by simpa [ep] using h27)
      simpa [ep] using Nat.le_of_dvd tpos h
    · exact .inr (.inr (.inl big))
    · right
      right
      right
      refine ⟨ep, .inl ?_⟩
      have h : p^2 ∣ t := lift 2 (by simpa [ep] using h25)
      simpa [ep] using Nat.le_of_dvd tpos h
    · exact .inr (.inr (.inr ⟨ep, .inr hm5⟩))
  have ha : A.conductor=Q.gcd r := by
    dsimp only [A]
    rw [component_conductor e (fun k : L.primeFactors => Nat.ordProj_dvd L k)
      L.pairwise_coprime_pow_primeFactors_factorization, conductor_changeLevel, hα]
  have hb : B.conductor=Q.gcd s := by
    dsimp only [B]
    rw [component_conductor e (fun k : L.primeFactors => Nat.ordProj_dvd L k)
      L.pairwise_coprime_pow_primeFactors_factorization, conductor_changeLevel, hβ]
  have vpos : 1 ≤ L.factorization p :=
    (hp.dvd_iff_one_le_factorization lp.ne').mp pl
  have loc : sqrt 2*‖J A B (m:ZMod Q)‖ ≤
      ‖J (1 : DirichletCharacter ℂ Q) 1 (m:ZMod Q)‖ := by
    by_cases v : L.factorization p=1
    · have Qp : Q=p := by simp [Q,v]
      let _ : Fact Q.Prime := ⟨Qp ▸ hp⟩
      have tl : t ≤ p := Qp ▸ Nat.div_le_self Q (m.gcd Q)
      have mp : ¬Q ∣ m := by
        intro H
        have te : t=1 := by
          dsimp only [t]
          rw [Nat.gcd_eq_right H, Nat.div_self qpos]
        have := hp.one_lt
        omega
      have large : 7 ≤ Q := by
        rw [Qp]
        rcases out with ⟨hp2,ht⟩ | ⟨hp3,ht⟩ | big | ⟨hp5,ht25 | hm5⟩
        · omega
        · omega
        · exact big
        · omega
        · exact False.elim (mp (by simpa [Qp,hp5] using hm5))
      have neq (χ : DirichletCharacter ℂ Q) (H : χ.conductor=Q) : χ ≠ 1 := by
        intro E
        rw [E, conductor_one] at H
        omega
      apply prime_local_gap m A B mp _ large
      rcases hp.dvd_mul.mp (pl.trans (Nat.lcm_dvd_mul r s)) with pr | ps
      · exact .inl (neq A (ha.trans (Nat.gcd_eq_left (Qp ▸ pr))))
      · exact .inr (neq B (hb.trans (Nat.gcd_eq_left (Qp ▸ ps))))
    · obtain ⟨n,hn⟩ : ∃ n : ℕ, L.factorization p=n+2 :=
        ⟨L.factorization p-2, by omega⟩
      have Qd : p^(n+2) ∣ L := by simpa [hn] using Nat.ordProj_dvd L p
      have Qr : Q ∣ r := by simpa [Q,hn] using primitive_source_dvd hp hr good.1 Qd
      have Qs : Q ∣ s := by simpa [Q,hn] using primitive_source_dvd hp hs good.2.1 Qd
      have eqQ : Q = p*p^(n+1) := by
        dsimp only [Q]
        rw [hn, pow_succ' p (n+1)]
      exact power_gap_of_eq (n+1) eqQ m he A B
        (ha.trans (Nat.gcd_eq_left Qr)) (hb.trans (Nat.gcd_eq_left Qs)) pt out
  have full := single_factor e hα hβ hr hs m hm he i
  let O := ‖series (1 : DirichletCharacter ℂ 1) (1 : DirichletCharacter ℂ 1) m‖
  let V := ‖J A B (m:ZMod Q)‖
  let W := ‖J (1 : DirichletCharacter ℂ Q) 1 (m:ZMod Q)‖
  have wp : 0 < W := norm_pos_iff.mpr (principal_ne_zero Q m he)
  change ‖series α β m‖*W ≤ O*V at full
  change sqrt 2*V ≤ W at loc
  apply le_of_mul_le_mul_right (a := W) <;> try assumption
  change (sqrt 2*‖series α β m‖)*W ≤ O*W
  have h1 := mul_le_mul_of_nonneg_left full (sqrt_nonneg 2)
  have h2 := mul_le_mul_of_nonneg_left loc (show 0 ≤ O from norm_nonneg _)
  nlinarith only [h1,h2]

end NearExtremalProof

theorem Conjectures.Goldbach.NearExtremalReducedConductor :
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
  let X := fun {r s : ℕ} (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s) (m : ℕ) =>
    r/(m.gcd r) ∣ 36 ∧ s/(m.gcd s) ∣ 36 ∧ r/(r.gcd s) ∣ 3 ∧ s/(r.gcd s) ∣ 3 ∧
      ((DirichletCharacter.changeLevel (Nat.dvd_lcm_left r s) α)*
       (DirichletCharacter.changeLevel (Nat.dvd_lcm_right r s) β)).conductor ∣ 36
  exact ∀ (r s : ℕ) [NeZero r] [NeZero s] (α : DirichletCharacter ℂ r) (β : DirichletCharacter ℂ s),
    α.IsPrimitive → β.IsPrimitive → ∀ m : ℕ, 0 < m → Even m → ¬X α β m →
    ‖O m‖ < Real.sqrt 2 * ‖S α β m‖ →
    let j := Nat.lcm r s / Nat.gcd m (Nat.lcm r s)
    5 ∣ j ∧ j ∣ 180 ∧ ¬ 5 ∣ m := by
  classical
  dsimp only
  intro r s _ _ α β hα hβ m hm he outside above
  change ¬SharpTwistedGoldbachGap.exceptional α β m at outside
  let P : DirichletCharacter ℂ 1 := 1
  change ‖series P P m‖ < sqrt 2 * ‖series α β m‖ at above
  let L := Nat.lcm r s
  let j := L/(m.gcd L)
  change 5 ∣ j ∧ j ∣ 180 ∧ ¬5 ∣ m
  have nz : series α β m ≠ 0 := by
    intro e
    rw [e,norm_zero,mul_zero] at above
    exact (norm_nonneg _).not_gt above
  have n36 : ¬j ∣ 36 := NearExtremalProof.not_reduced_36 hα hβ m hm he outside nz
  have jp : 0 < j := Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right m L))
    (Nat.lcm_pos (NeZero.pos r) (NeZero.pos s))
  have exclude (p : ℕ) (hp : p.Prime) (pj : p ∣ j)
      (bad : (p=2 ∧ 8∣j) ∨ (p=3 ∧ 27∣j) ∨ 7≤p ∨ (p=5 ∧ (25∣j ∨ 5∣m))) : False :=
    above.not_ge (NearExtremalProof.bad_global hα hβ m hm he p hp pj bad)
  have small : j ∣ 180 := by
    by_contra no
    obtain ⟨p,hp,pj,bad⟩ := NearExtremalProof.bad_prime_of_not_dvd jp no
    apply exclude p hp pj
    rcases bad with a | b | c | ⟨rfl,d⟩
    · exact .inl a
    · exact .inr (.inl b)
    · exact .inr (.inr (.inl c))
    · exact .inr (.inr (.inr ⟨rfl,.inl d⟩))
  have d5 := NearExtremalProof.five_dvd_of_dvd_180_not_dvd_36 small n36
  exact ⟨d5,small,fun hm5 => exclude 5 (by decide) d5 (.inr (.inr (.inr ⟨rfl,.inr hm5⟩)))⟩
