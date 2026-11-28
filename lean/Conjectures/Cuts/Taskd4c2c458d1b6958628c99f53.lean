import Mathlib
import Conjectures.Goldbach.FareyInitialSieveLower
import Conjectures.Goldbach.FareyCubeSqrtDensityRatio


open Finset Real
open FareyBrun
open ErdosStraus.BrunHooley ErdosStraus.RoughEstimates

namespace FareyPureEndpoint

noncomputable section
open scoped Classical

/- The cofactor residue counts use the CRT lemmas in the initial sieve module. -/
namespace CofactorRemainder

open Conjectures.Goldbach.FareyFullSieveRemainder_aux

/-- Number of forbidden residues at a prime modulus. -/
def primeRootCount (n r : ℕ) : ℕ := if r ∣ n then 1 else 2

private theorem card_root_prime (r n : ℕ) (hr : r.Prime) :
    (Root r n).card = primeRootCount n r := by
  by_cases h : r ∣ n
  · let _ : Fact (Nat.Prime r) := ⟨hr⟩
    let _ : NeZero r := ⟨hr.ne_zero⟩
    have hn : (n : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff n r).2 h
    have hroot : Root r n = {0} := by
      ext x
      simp [mem_Root, hn, mul_eq_zero]
    simp [hroot, primeRootCount, h]
  · simpa [primeRootCount, h] using card_Root_prime r n hr h

private theorem card_root_product (n : ℕ) (s : Finset ℕ)
    (hs : ∀ r ∈ s, r.Prime) :
    (Root (∏ r ∈ s, r) n).card = ∏ r ∈ s, primeRootCount n r := by
  induction s using Finset.induction_on with
  | empty =>
      simp only [prod_empty]
      have hroot : Root 1 n = (univ : Finset (ZMod 1)) := by
        ext x
        simp only [Finset.mem_univ, iff_true, mem_Root]
        rw [Subsingleton.elim x 0, zero_mul]
      simp [hroot]
  | @insert r s hr ih =>
      have hrp := hs r (mem_insert_self r s)
      have hsp : ∀ a ∈ s, Nat.Prime a := fun a ha => hs a (mem_insert_of_mem ha)
      have hpos : 0 < ∏ a ∈ s, a := Finset.prod_pos fun a ha => (hsp a ha).pos
      have hcop : r.Coprime (∏ a ∈ s, a) :=
        Nat.Coprime.prod_right fun a ha =>
          (Nat.coprime_primes hrp (hsp a ha)).2 (fun he => hr (he ▸ ha))
      let _ : NeZero r := ⟨hrp.ne_zero⟩
      let _ : NeZero (∏ a ∈ s, a) := ⟨hpos.ne'⟩
      let _ : NeZero (r * ∏ a ∈ s, a) := ⟨(Nat.mul_pos hrp.pos hpos).ne'⟩
      rw [prod_insert hr, prod_insert hr, card_Root_mul r _ n hcop, card_root_prime r n hrp,
        ih hsp]

theorem card_root_squarefree (d n : ℕ) (hd : Squarefree d) :
    (Root d n).card = ∏ r ∈ d.primeFactors, primeRootCount n r := by
  have h := card_root_product n d.primeFactors fun _ hr => Nat.prime_of_mem_primeFactors hr
  rwa [Nat.prod_primeFactors_of_squarefree hd] at h

/-- Residues of the variable (q) for which ((pq)(n-pq)) vanishes modulo (d). -/
def switchedRoots (d n p : ℕ) [NeZero d] : Finset (ZMod d) :=
  univ.filter fun x => (p : ZMod d) * x ∈ Root d n

theorem card_switchedRoots (d n p : ℕ) [NeZero d] (hp : p.Coprime d) :
    (switchedRoots d n p).card = (Root d n).card := by
  have hunit := ZMod.coe_mul_inv_eq_one p hp
  refine Finset.card_bij' (fun x _ => (p : ZMod d) * x)
    (fun y _ => (p : ZMod d)⁻¹ * y) ?_ ?_ ?_ ?_
  · intro x hx
    exact (mem_filter.mp hx).2
  · intro y hy
    exact mem_filter.mpr ⟨mem_univ _, by rwa [← mul_assoc, hunit, one_mul]⟩
  · intro x _
    rw [← mul_assoc, mul_comm (p : ZMod d)⁻¹ _, hunit, one_mul]
  · intro y _
    rw [← mul_assoc, hunit, one_mul]

/-- The error in counting divisibility of ((pq)(n-pq)) on a cofactor interval
    is at most the number of forbidden residues modulo (d). -/
theorem cofactor_remainder (n p d lo hi : ℕ) (hd : 0 < d)
    (hp : p.Coprime d) (hlh : lo ≤ hi) (hhi : p * hi ≤ n) :
    |(((Icc lo hi).filter fun q => d ∣ (p * q) * (n - p * q)).card : ℝ) -
      ((Root d n).card : ℝ) * ((hi - lo + 1 : ℕ) : ℝ) / (d : ℝ)| ≤
      ((Root d n).card : ℝ) := by
  let _ : NeZero d := ⟨hd.ne'⟩
  let roots := switchedRoots d n p
  let interval := Icc lo hi
  let counted := interval.filter fun q => d ∣ (p * q) * (n - p * q)
  let fiber (x : ZMod d) := (interval.filter fun q => q ≡ x.val [MOD d]).card
  have hmem {q : ℕ} (hq : q ∈ interval) : (q : ZMod d) ∈ roots ↔
      d ∣ (p * q) * (n - p * q) := by
    have hprod := (Nat.mul_le_mul_left p (mem_Icc.mp hq).2).trans hhi
    simpa [roots, switchedRoots, Nat.cast_mul] using (mem_Root_iff d n (p * q) hprod)
  have hfiber {x : ZMod d} (hx : x ∈ roots) :
      (counted.filter fun q : ℕ => (q : ZMod d) = x).card = fiber x := by
    congr 1
    ext q
    have hcast : (q : ZMod d) = x ↔ q ≡ x.val [MOD d] := by
      simpa only [ZMod.natCast_zmod_val] using ZMod.natCast_eq_natCast_iff q x.val d
    simp only [counted, mem_filter, hcast]
    constructor
    · rintro ⟨⟨hq, _⟩, hqmod⟩
      exact ⟨hq, hqmod⟩
    · rintro ⟨hq, hqmod⟩
      exact ⟨⟨hq, (hmem hq).mp ((hcast.mpr hqmod).symm ▸ hx)⟩, hqmod⟩
  have hsplit : counted.card = ∑ x ∈ roots, fiber x := by
    rw [Finset.card_eq_sum_card_fiberwise (s := counted) (t := roots)
      (f := fun q : ℕ => (q : ZMod d))
      (fun q hq => (hmem (mem_filter.mp hq).1).2 (mem_filter.mp hq).2)]
    exact Finset.sum_congr rfl fun _ hx => hfiber hx
  have hmain : (∑ _x ∈ roots, ((hi - lo + 1 : ℕ) : ℝ) / (d : ℝ)) =
      (roots.card : ℝ) * (((hi - lo + 1 : ℕ) : ℝ) / (d : ℝ)) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
  change |(counted.card : ℝ) - _| ≤ _
  rw [← card_switchedRoots d n p hp, ← show roots.card = (switchedRoots d n p).card from rfl,
    hsplit, Nat.cast_sum, mul_div_assoc, ← hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x ∈ roots, |(fiber x : ℝ) - ((hi - lo + 1 : ℕ) : ℝ) / (d : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ roots, (1 : ℝ) := Finset.sum_le_sum fun x _ =>
      card_modEq_Icc d x.val lo hi hd hlh
    _ = roots.card := by simp

/-- Squarefree sieve moduli yield a factor of one at (r mid n) and two at all
    other primes dividing the modulus. -/
theorem cofactor_remainder_squarefree (n p d lo hi : ℕ) (hd : Squarefree d)
    (hp : p.Coprime d) (hlh : lo ≤ hi) (hhi : p * hi ≤ n) :
    |(((Icc lo hi).filter fun q => d ∣ (p * q) * (n - p * q)).card : ℝ) -
      ((∏ r ∈ d.primeFactors, primeRootCount n r : ℕ) : ℝ) *
        ((hi - lo + 1 : ℕ) : ℝ) / (d : ℝ)| ≤
      ((∏ r ∈ d.primeFactors, primeRootCount n r : ℕ) : ℝ) := by
  have h := cofactor_remainder n p d lo hi (Nat.pos_of_ne_zero hd.ne_zero) hp hlh hhi
  rwa [card_root_squarefree d n hd] at h

end CofactorRemainder

open CofactorRemainder

def localDensity (n l : ℕ) : ℝ := (primeRootCount n l : ℝ) / l

def oddLocalProduct (n z : ℕ) : ℝ :=
  ∏ l ∈ good 2 z, (1 - localDensity n l)

def siftCofactors (n p lo hi z : ℕ) : Finset ℕ :=
  (Icc lo hi).filter fun q => ∀ l ∈ good 2 z, ¬ l ∣ (p*q)*(n-p*q)

private lemma rootCount_le (n l : ℕ) : primeRootCount n l ≤ 2 := by
  unfold primeRootCount
  split_ifs <;> omega

private lemma localDensity_le (n l : ℕ) : localDensity n l ≤ 2/(l:ℝ) := by
  exact div_le_div_of_nonneg_right (by exact_mod_cast rootCount_le n l) (by positivity)

private lemma localDensity_nonneg (n l : ℕ) : 0 ≤ localDensity n l := by
  unfold localDensity
  positivity

private theorem cofactor_intersection (n p lo hi : ℕ) (s : Finset ℕ)
    (hs : ∀ l ∈ s, l.Prime) (hc : ∀ l ∈ s, p.Coprime l)
    (hlh : lo ≤ hi) (hhi : p*hi ≤ n) :
    |intersectionCount (Icc lo hi) (fun l q => l ∣ (p*q)*(n-p*q)) s -
        ((hi-lo+1 : ℕ) : ℝ) * ∏ l ∈ s, localDensity n l| ≤
      ((∏ l ∈ s, l : ℕ) : ℝ) := by
  let d := ∏ l ∈ s, l
  have hdSet : d.primeFactors = s := Nat.primeFactors_prod hs
  have hdSq : Squarefree d := by
    simpa only [hdSet] using Nat.squarefree_prod_primeFactors d
  have hdCop : p.Coprime d := Nat.Coprime.prod_right hc
  have hcrt := cofactor_remainder_squarefree n p d lo hi hdSq hdCop hlh hhi
  rw [hdSet] at hcrt
  have hpred (q : ℕ) : (∀ l ∈ s, l ∣ (p*q)*(n-p*q)) ↔ d ∣ (p*q)*(n-p*q) :=
    ⟨Finset.prod_primes_dvd ((p*q)*(n-p*q)) (fun l hl => (hs l hl).prime),
      fun hd l hl => (Finset.dvd_prod_of_mem (fun t : ℕ => t) hl).trans hd⟩
  have hw : (∏ l ∈ s, localDensity n l) = ((∏ l ∈ s, primeRootCount n l : ℕ) : ℝ)/d := by
    simp only [localDensity, prod_div_distrib, Nat.cast_prod, d]
  unfold intersectionCount
  simp_rw [hpred]
  rw [hw, mul_div_assoc', mul_comm ((hi-lo+1 : ℕ) : ℝ)]
  refine hcrt.trans ?_
  exact_mod_cast Finset.prod_le_prod (fun l hl => (rootCount_le n l).trans (hs l hl).two_le)

set_option maxHeartbeats 1200000 in
theorem cofactor_sieve_upper (n p lo hi z K : ℕ) (hp : p.Prime)
    (hz : 2 ≤ z) (hzp : z < p) (hlh : lo ≤ hi) (hhi : p*hi ≤ n) :
    ((siftCofactors n p lo hi z).card : ℝ) ≤
      ((hi-lo+1 : ℕ) : ℝ) * (oddLocalProduct n z * Real.exp (tiltError K)) +
      ((z^(8*(K+2)) : ℕ) : ℝ)^2 := by
  let P := fun j : Fin (blockCount z) => blocks 2 z j.val
  let r := fun j : Fin (blockCount z) => rank K j.val
  let W := z^(8*(K+2))
  let w := localDensity n
  let hit := fun l q : ℕ => l ∣ (p*q)*(n-p*q)
  let bit (q l : ℕ) : ℝ := @ite ℝ (hit l q) (Classical.propDecidable (hit l q)) 1 0
  have hdisj : Pairwise (fun j k => Disjoint (P j) (P k)) := block_disjoint 2 z hz
  have hcover : univ.biUnion P = good 2 z := block_cover 2 z hz
  have hP (j : Fin (blockCount z)) : P j ⊆ good 2 z := fun _ hl => (mem_filter.mp hl).1
  have hs (j : Fin (blockCount z)) (l : ℕ) (hl : l ∈ P j) : l.Prime :=
    blocks_prime 2 z j.val l hl
  have hlt (j : Fin (blockCount z)) (l : ℕ) (hl : l ∈ P j) : z ≥ l :=
    (mem_Icc.mp (mem_filter.mp (mem_filter.mp (hP j hl)).1).1).2
  have hw (j : Fin (blockCount z)) (l : ℕ) (hl : l ∈ P j) : 0 ≤ w l ∧ w l < 1 := by
    have h3 := good_odd (n := 2) (by decide : Even (2 : ℕ)) (hP j hl)
    have hlR : (2 : ℝ) < l := by exact_mod_cast (show 2 < l by omega)
    exact ⟨localDensity_nonneg n l, (localDensity_le n l).trans_lt
      ((div_lt_one (by positivity)).mpr hlR)⟩
  have htail := rank_tail K P w
    (fun j => (Finset.sum_le_sum (fun l _ => localDensity_le n l)).trans (block_mass 2 z j.val hz))
    (fun j l hl => (hw j l hl).1)
    (fun j => (block_euler 2 z j.val (by decide : Even (2 : ℕ)) hz).trans
      (Finset.prod_le_prod₀ (fun l hl => by
        have h3 := good_odd (n := 2) (by decide : Even (2 : ℕ)) (hP j hl)
        have h2 : (2 : ℝ) ≤ l := by exact_mod_cast (show 2 ≤ l by omega)
        exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr h2))
        (fun l _ => sub_le_sub_left (localDensity_le n l) 1)))
  have hbound (f : Fin (blockCount z) → Finset ℕ) (hf : f ∈ choices P (fun j => 2*r j)) :
      selectedProduct f ≤ W := by
    have h := rank_support K P hdisj (by exact_mod_cast (show 1 ≤ z by omega))
      (fun j l hl => (mem_filter.mp hl).2.2) (fun j => 2*r j) (fun j => Nat.le_succ _) hf
    exact_mod_cast h
  have hround (f : Fin (blockCount z) → Finset ℕ) (hf : f ∈ choices P (fun j => 2*r j)) :
      |intersectionCount (Icc lo hi) hit (selected f) -
         ((hi-lo+1 : ℕ) : ℝ) * ∏ j, ∏ l ∈ f j, w l| ≤ (W:ℝ) := by
    have hpr := selected_primes hs hf
    have hcop (l : ℕ) (hl : l ∈ selected f) : p.Coprime l := by
      obtain ⟨j, _, hlj⟩ := mem_biUnion.mp hl
      exact (Nat.coprime_primes hp (hpr l hl)).mpr
        (ne_of_gt ((hlt j l ((mem_choices.mp hf j).1 hlj)).trans_lt hzp))
    have hprod : (∏ l ∈ selected f, w l) = ∏ j, ∏ l ∈ f j, w l := by
      apply prod_biUnion
      intro j _ k _ hjk
      exact (hdisj hjk).mono (mem_choices.mp hf j).1 (mem_choices.mp hf k).1
    rw [←hprod]
    exact (cofactor_intersection n p lo hi (selected f) hpr hcop hlh hhi).trans
      (by exact_mod_cast hbound f hf)
  have hmodel : |(∑ q ∈ Icc lo hi, FareyBrun.box P (bit q) (fun j => 2*r j)) -
      ((hi-lo+1 : ℕ) : ℝ) * FareyBrun.box P w (fun j => 2*r j)| ≤
      (choices P (fun j => 2*r j)).card * (W:ℝ) :=
    box_mean (Icc lo hi) P hit (fun j => 2*r j) w ((hi-lo+1 : ℕ) : ℝ) (W:ℝ) hround
  have hchoices : ((choices P (fun j => 2*r j)).card:ℝ) ≤ W := by
    exact_mod_cast choices_card_le_of_product_le P hs hdisj (fun j => 2*r j) W hbound
  have hfilter : siftCofactors n p lo hi z =
      (Icc lo hi).filter (fun q => ∀ j l, l ∈ P j → ¬ hit l q) := by
    ext q
    simp only [siftCofactors, mem_filter, ← hcover, mem_biUnion, mem_univ, true_and]
    constructor
    · rintro ⟨hi, h⟩
      exact ⟨hi, fun j l hl => h l ⟨j, hl⟩⟩
    · rintro ⟨hi, h⟩
      exact ⟨hi, fun l ⟨j, hl⟩ => h j l hl⟩
  have hcount : ((siftCofactors n p lo hi z).card:ℝ) ≤
      ∑ q ∈ Icc lo hi, FareyBrun.box P (bit q) (fun j => 2*r j) := by
    rw [hfilter, card_filter]
    push_cast
    refine sum_le_sum fun q _ => ?_
    have h := sift_indicator_le_weight P (fun l => hit l q) r
    by_cases hh : ∀ j l, l ∈ P j → ¬ hit l q
    · simpa only [ite_eq_left hh, FareyBrun.box, bit] using h
    · simpa only [ite_eq_right hh, FareyBrun.box, bit] using h
  have hprod := product_truncation_upper P w hw r
  have hprod_nn : 0 ≤ ∏ j, ∏ l ∈ P j, (1-w l) :=
    prod_nonneg (fun j _ => prod_nonneg fun l hl => sub_nonneg.mpr (hw j l hl).2.le)
  have hupper : box P w (fun j => 2*r j) ≤
      oddLocalProduct n z * Real.exp (tiltError K) := by
    have hfactor : (∏ j, ∏ l ∈ P j, (1-w l)) = oddLocalProduct n z := by
      unfold oddLocalProduct
      rw [← hcover, prod_biUnion]
      exact hdisj.set_pairwise _
    rw [← hfactor]
    exact hprod.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htail) hprod_nn)
  have hmain := mul_le_mul_of_nonneg_left hupper (show 0 ≤ ((hi-lo+1 : ℕ):ℝ) by positivity)
  have herr := (abs_le.mp hmodel).2.trans (mul_le_mul_of_nonneg_right hchoices (by positivity))
  change _ ≤ _ + (W:ℝ)^2
  refine hcount.trans ((sub_le_iff_le_add.mp herr).trans ?_)
  simpa only [add_comm, pow_two] using add_le_add_right hmain ((W:ℝ)*W)

abbrev semiprimeAbove (cutoff m : ℕ) : Prop :=
  cutoff < m.minFac ∧ m.minFac.Prime ∧ (m / m.minFac).Prime

def bothSemiprimes (n cutoff : ℕ) : Finset ℕ :=
  (window n).filter fun m => semiprimeAbove cutoff m ∧ semiprimeAbove cutoff (n-m)

def endpointPairs (n cutoff cap : ℕ) : Finset ℕ :=
  (bothSemiprimes n cutoff).filter fun m => cap < m.minFac ∨ cap < (n-m).minFac

def endpointPrimes (n cutoff cap : ℕ) : Finset ℕ :=
  (Ioc (max cutoff cap) n.sqrt).filter Nat.Prime

private lemma mem_window_reflect {n m : ℕ} (hm : m ∈ window n) : n-m ∈ window n := by
  obtain ⟨hl, hh⟩ := mem_Icc.mp hm
  have hl' := (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 3)).mp hl
  have hh' := (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mp hh
  refine mem_Icc.mpr ⟨?_, ?_⟩
  · exact (Nat.div_le_iff_le_mul_add_pred (by decide : 0 < 3)).mpr (by omega)
  · exact (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr (by omega)

private lemma mem_window_le {n m : ℕ} (hm : m ∈ window n) : m ≤ n := by
  have h : m ≤ 2*n/3 := (mem_Icc.mp hm).2
  omega

theorem endpoint_card_le_lanes (n cutoff cap z : ℕ) (hz : z ≤ cutoff) :
    (endpointPairs n cutoff cap).card ≤ 2 *
      ∑ p ∈ endpointPrimes n cutoff cap, (siftCofactors n p 0 (n/p) z).card := by
  let left := (bothSemiprimes n cutoff).filter fun m => cap < m.minFac
  let right := (bothSemiprimes n cutoff).filter fun m => cap < (n-m).minFac
  have hcover : endpointPairs n cutoff cap = left ∪ right := by
    ext m
    simp [endpointPairs, left, right]
    tauto
  have hright : right.card ≤ left.card := by
    refine Finset.card_le_card_of_injOn (fun m => n-m) (fun m hm => ?_) ?_
    · obtain ⟨hboth, hcap⟩ := mem_filter.mp hm
      obtain ⟨hmI, hmA, hmB⟩ := mem_filter.mp hboth
      have hreflect := Nat.sub_sub_self (mem_window_le hmI)
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_window_reflect hmI, hmB, by rwa [hreflect]⟩, hcap⟩
    · intro u hu v hv heq
      have hu' := mem_window_le (mem_filter.mp (mem_filter.mp hu).1).1
      have hv' := mem_window_le (mem_filter.mp (mem_filter.mp hv).1).1
      change n-u = n-v at heq
      omega
  let candidates := (endpointPrimes n cutoff cap).sigma fun p => siftCofactors n p 0 (n/p) z
  have hleft : left.card ≤ candidates.card := by
    refine (card_le_card (s := left) (t := candidates.image fun x => x.1*x.2) ?_).trans card_image_le
    intro m hm
    obtain ⟨hboth, hcap⟩ := mem_filter.mp hm
    obtain ⟨hmI, hmA, hmB⟩ := mem_filter.mp hboth
    let p := m.minFac
    let q := m/p
    have hp : p.Prime := hmA.2.1
    have hq : q.Prime := hmA.2.2
    have hprod : p*q = m := by
      rw [mul_comm]
      exact Nat.div_mul_cancel (Nat.minFac_dvd m)
    have hqdvd : q ∣ m := ⟨p, by simpa [mul_comm] using hprod.symm⟩
    have hpq : p ≤ q := Nat.minFac_le_of_dvd hq.two_le hqdvd
    have hpsq : p ≤ n.sqrt := by
      apply Nat.le_sqrt.mpr
      calc
        p*p ≤ p*q := Nat.mul_le_mul_left _ hpq
        _ = m := hprod
        _ ≤ n := mem_window_le hmI
    have hpBand : p ∈ endpointPrimes n cutoff cap := by
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨max_lt_iff.mpr ⟨hmA.1, hcap⟩, hpsq⟩, hp⟩
    have hqSift : q ∈ siftCofactors n p 0 (n/p) z := by
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, ?_⟩, ?_⟩
      · apply (Nat.le_div_iff_mul_le hp.pos).mpr
        rw [mul_comm, hprod]
        exact mem_window_le hmI
      · intro l hl hdiv
        rw [hprod] at hdiv
        obtain ⟨hl', _⟩ := mem_filter.mp hl
        obtain ⟨hlI, hlp⟩ := mem_filter.mp hl'
        have hlz := (mem_Icc.mp hlI).2.trans hz
        rcases hlp.dvd_mul.mp hdiv with h | h
        · exact (not_le_of_gt (hlz.trans_lt hmA.1)) (Nat.minFac_le_of_dvd hlp.two_le h)
        · exact (not_le_of_gt (hlz.trans_lt hmB.1)) (Nat.minFac_le_of_dvd hlp.two_le h)
    exact mem_image.mpr ⟨⟨p,q⟩, mem_sigma.mpr ⟨hpBand, hqSift⟩, hprod⟩
  rw [hcover, two_mul]
  have hc : candidates.card = ∑ p ∈ endpointPrimes n cutoff cap,
      (siftCofactors n p 0 (n/p) z).card := card_sigma ..
  exact (card_union_le left right).trans (Nat.add_le_add (hleft.trans_eq hc) (hright.trans (hleft.trans_eq hc)))

set_option maxHeartbeats 1200000 in
theorem endpointPairs_upper (n cutoff cap z : ℕ) (hz : 2 ≤ z) (hzcut : z ≤ cutoff) :
    ((endpointPairs n cutoff cap).card : ℝ) ≤
      4*(n:ℝ)*oddLocalProduct n z * Real.exp (tiltError 0) *
        (∑ p ∈ endpointPrimes n cutoff cap, 1/(p:ℝ)) +
      2*(n.sqrt:ℝ)*((z^16 : ℕ) : ℝ)^2 := by
  let S := endpointPrimes n cutoff cap
  let V := oddLocalProduct n z * Real.exp (tiltError 0)
  let W : ℝ := ((z^16 : ℕ) : ℝ)^2
  have hV : 0 ≤ V := by
    unfold V oddLocalProduct
    apply mul_nonneg _ (Real.exp_pos _).le
    apply prod_nonneg
    intro l hl
    have hl2 := (mem_filter.mp (mem_filter.mp hl).1).2.two_le
    exact sub_nonneg.mpr ((localDensity_le n l).trans
      ((div_le_one (by positivity)).mpr (by exact_mod_cast hl2)))
  have hc (p : ℕ) (hp : p ∈ S) : p.Prime ∧ p ≤ n ∧ z < p := by
    obtain ⟨hi, hp⟩ := mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := mem_Ioc.mp hi
    exact ⟨hp, hhi.trans (Nat.sqrt_le_self _), hzcut.trans_lt ((le_max_left _ _).trans_lt hlo)⟩
  have hone (p : ℕ) (hp : p ∈ S) : (((n/p+1 : ℕ) : ℝ)) ≤ 2*((n:ℝ)/p) := by
    have ⟨hprime, hpn, _⟩ := hc p hp
    have hpc : (0:ℝ) < p := by exact_mod_cast hprime.pos
    have hnat : ((n/p:ℕ):ℝ) ≤ (n:ℝ)/p := by
      apply (le_div_iff₀ hpc).mpr
      exact_mod_cast Nat.div_mul_le_self n p
    have hratio : (1:ℝ) ≤ (n:ℝ)/p := by
      apply (le_div_iff₀ hpc).mpr
      simpa only [one_mul] using (show (p:ℝ) ≤ n by exact_mod_cast hpn)
    push_cast
    linarith
  have hsum : (∑ p ∈ S, ((siftCofactors n p 0 (n/p) z).card:ℝ)) ≤
      2*(n:ℝ)*V * (∑ p ∈ S, 1/(p:ℝ)) + (S.card:ℝ)*W := by
    calc
      _ ≤ ∑ p ∈ S, (2*((n:ℝ)/p)*V + W) := by
        refine sum_le_sum fun p hp => ?_
        have ⟨hprime, _, hzp⟩ := hc p hp
        have hu := cofactor_sieve_upper n p 0 (n/p) z 0 hprime hz hzp (Nat.zero_le _)
          (by rw [mul_comm]; exact Nat.div_mul_le_self n p)
        simp only [Nat.sub_zero] at hu
        change _ ≤ ((n/p+1 : ℕ):ℝ)*V + W at hu
        refine hu.trans ?_
        simpa only [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_right (hone p hp) hV) W
      _ = _ := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, mul_sum]
        congr 1
        apply sum_congr rfl
        intro p _
        ring
  have hcard : (S.card : ℝ) ≤ n.sqrt := by
    exact_mod_cast (show S.card ≤ n.sqrt from by
      have hs : S ⊆ Icc 1 n.sqrt := by
        intro p hp
        obtain ⟨hi, hprime⟩ := mem_filter.mp hp
        exact mem_Icc.mpr ⟨hprime.pos, (mem_Ioc.mp hi).2⟩
      have := card_le_card hs
      simpa using this)
  have hw : 0 ≤ W := by positivity
  have ht := mul_le_mul_of_nonneg_right hcard hw
  have he : ((endpointPairs n cutoff cap).card:ℝ) ≤
      2 * ∑ p ∈ S, ((siftCofactors n p 0 (n/p) z).card:ℝ) := by
    exact_mod_cast endpoint_card_le_lanes n cutoff cap z hzcut
  have hfinal := he.trans (mul_le_mul_of_nonneg_left (hsum.trans (add_le_add_right ht _))
    (by norm_num : (0:ℝ) ≤ 2))
  calc
    _ ≤ 2 * (2*(n:ℝ)*V * (∑ p ∈ S, 1/(p:ℝ)) + (n.sqrt:ℝ)*W) := hfinal
    _ = _ := by unfold S V W; ring

private theorem terminal_volume_as_product {n : ℕ} (hn : 0 < n) :
    mainTerm n n.sqrt = ((window n).card:ℝ) *
      ∏ l ∈ n.primeFactors ∪ good n n.sqrt, (1 - localDensity n l) := by
  have hdisj : Disjoint n.primeFactors (good n n.sqrt) := Finset.disjoint_left.mpr
    fun l hl hgood => (mem_filter.mp hgood).2 (Nat.dvd_of_mem_primeFactors hl)
  rw [prod_union hdisj]
  have hT : (∏ l ∈ n.primeFactors, (1-localDensity n l)) =
      ∏ l ∈ n.primeFactors, (1-(l:ℝ)⁻¹) := by
    refine prod_congr rfl fun l hl => ?_
    simp [localDensity, primeRootCount, Nat.dvd_of_mem_primeFactors hl, one_div]
  have hU : (∏ l ∈ good n n.sqrt, (1-localDensity n l)) =
      ∏ l ∈ good n n.sqrt, (1-2/(l:ℝ)) := by
    refine prod_congr rfl fun l hl => ?_
    simp [localDensity, primeRootCount, (mem_filter.mp hl).2]
  have htot : (n.totient:ℝ) =
      (n:ℝ) * ∏ l ∈ n.primeFactors, (1-(l:ℝ)⁻¹) := by
    have h := congrArg (fun a : ℚ => (a : ℝ)) (Nat.totient_eq_mul_prod_factors n)
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_prod, Rat.cast_sub, Rat.cast_one,
      Rat.cast_inv] using h
  have hn' : (n:ℝ) ≠ 0 := by positivity
  rw [hT, hU, mainTerm, scale, htot]
  field_simp [hn']

theorem cofactorDensity_le_terminal (n U : ℕ) (hn : 64 ≤ n) (he : Even n)
    (hU : 2 ≤ U) (hz : 2 ≤ cut n U) :
    (n:ℝ) * oddLocalProduct n (cut n U) ≤
      8 * Real.exp (12*(U:ℝ)) * mainTerm n n.sqrt := by
  let T := n.primeFactors ∪ good n n.sqrt
  let small := insert 2 (good 2 (cut n U))
  let f := fun l : ℕ => 1 - localDensity n l
  have htwo : 2 ∣ n := even_iff_two_dvd.mp he
  have hsmall (l : ℕ) (hl : l.Prime) (hb : l ≤ cut n U) : l ∈ small := by
    by_cases h : l = 2
    · subst l
      exact mem_insert_self _ _
    · have hnd : ¬ l ∣ 2 := by
        intro hd
        exact h (le_antisymm (Nat.le_of_dvd (by decide) hd) hl.two_le)
      exact mem_insert_of_mem (mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_Icc.mpr ⟨hl.two_le, hb⟩, hl⟩, hnd⟩)
  have hsub : small ⊆ T := by
    intro l hl
    rcases mem_insert.mp hl with hl | hl
    · rcases hl with rfl
      exact mem_union_left _ (Nat.mem_primeFactors.mpr ⟨Nat.prime_two, htwo, by omega⟩)
    · obtain ⟨hl', _⟩ := mem_filter.mp hl
      obtain ⟨hlI, hlp⟩ := mem_filter.mp hl'
      by_cases hld : l ∣ n
      · exact mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hlp, hld, by omega⟩)
      · have hly := (mem_Icc.mp hlI).2.trans (cut_le_sqrt n U (by omega) hU)
        exact mem_union_right _ (mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_Icc.mpr ⟨hlp.two_le, hly⟩, hlp⟩, hld⟩)
  have htprime (l : ℕ) (hl : l ∈ T) : l.Prime ∧ l ≤ n := by
    rcases mem_union.mp hl with hl | hl
    · exact ⟨Nat.prime_of_mem_primeFactors hl, Nat.le_of_dvd (by omega)
        (Nat.dvd_of_mem_primeFactors hl)⟩
    · obtain ⟨hl', _⟩ := mem_filter.mp hl
      obtain ⟨hlI, hlp⟩ := mem_filter.mp hl'
      exact ⟨hlp, (mem_Icc.mp hlI).2.trans (Nat.sqrt_le_self n)⟩
  have hbig (l : ℕ) (hl : l ∈ T \ small) : cut n U < l :=
    lt_of_not_ge fun hb => (mem_sdiff.mp hl).2 (hsmall l (htprime l (mem_sdiff.mp hl).1).1 hb)
  have hnR : (0:ℝ) < n := by positivity
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hUR : (0:ℝ) < U := by positivity
  have htail := log_tail_budget (by omega : 0<n) (T \ small) (Real.log n/U) (fun l hl => by
    obtain ⟨hlprime, hln⟩ := htprime l (mem_sdiff.mp hl).1
    refine ⟨hlprime, hln, ?_⟩
    have hpow : (n:ℝ)^(1/(U:ℝ)) < (l:ℝ) := (Nat.floor_lt (by positivity)).mp (hbig l hl)
    have hlogl := Real.log_le_log (Real.rpow_pos_of_pos hnR _) hpow.le
    rw [Real.log_rpow hnR] at hlogl
    simpa [div_eq_mul_inv, mul_comm] using hlogl)
  have hmass : (∑ l ∈ T \ small, 2/(l:ℝ)) ≤ 4*(U:ℝ) := by
    apply (mul_le_mul_iff_left₀ (div_pos hlog hUR)).mp
    calc
      _ ≤ 4 * Real.log n := by simpa only [mul_comm (Real.log n/(U:ℝ))] using htail
      _ = (4*(U:ℝ)) * (Real.log n/(U:ℝ)) := by field_simp [hUR.ne']
  have h3 (l : ℕ) (hl : l ∈ T \ small) : 3 ≤ l := hz.trans_lt (hbig l hl)
  have htailProd : Real.exp (-12*(U:ℝ)) ≤ ∏ l ∈ T \ small, f l := by
    calc
      _ ≤ Real.exp (-3*(∑ l ∈ T \ small, 2/(l:ℝ))) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ ∏ l ∈ T \ small, (1-2/(l:ℝ)) := euler_density_lower _ h3
      _ ≤ _ := by
        apply prod_le_prod₀
        · intro l hl
          have h2 : (2:ℝ) ≤ l := by exact_mod_cast (show 2 ≤ l by have := h3 l hl; omega)
          exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr h2)
        · exact fun l _ => sub_le_sub_left (localDensity_le n l) 1
  have hodd : 0 ≤ oddLocalProduct n (cut n U) := by
    apply prod_nonneg
    intro l hl
    have hlp := (mem_filter.mp (mem_filter.mp hl).1).2
    have hl2 : (2:ℝ) ≤ l := by exact_mod_cast hlp.two_le
    exact sub_nonneg.mpr ((localDensity_le n l).trans ((div_le_one (by positivity)).mpr hl2))
  have hbase : (∏ l ∈ small, f l) = (1/2:ℝ) * oddLocalProduct n (cut n U) := by
    have h2 : 2 ∉ good 2 (cut n U) := fun h => (mem_filter.mp h).2 (dvd_refl _)
    norm_num [small, prod_insert h2, f, localDensity, primeRootCount, htwo, oddLocalProduct]
  have hlocal : Real.exp (-12*(U:ℝ)) * ((1/2:ℝ)*oddLocalProduct n (cut n U)) ≤ ∏ l ∈ T, f l := by
    rw [← prod_sdiff hsub, hbase]
    exact mul_le_mul_of_nonneg_right htailProd (by positivity)
  have hcard : (n:ℝ) ≤ 4*((window n).card:ℝ) := by
    exact_mod_cast (show n ≤ 4*(window n).card from by
      simp only [window, Nat.card_Icc]
      omega)
  have hVol : (n:ℝ) * (Real.exp (-12*(U:ℝ))/8) * oddLocalProduct n (cut n U) ≤ mainTerm n n.sqrt := by
    calc
      _ = ((n:ℝ)/4) * (Real.exp (-12*(U:ℝ)) * ((1/2:ℝ)*oddLocalProduct n (cut n U))) := by ring
      _ ≤ ((window n).card:ℝ) * (∏ l ∈ T, f l) := by
        exact mul_le_mul (by linarith) hlocal (by positivity) (by positivity)
      _ = _ := (terminal_volume_as_product (by omega)).symm
  calc
    _ = ((n:ℝ) * (Real.exp (-12*(U:ℝ))/8) * oddLocalProduct n (cut n U)) *
          (8*Real.exp (12*(U:ℝ))) := by
      rw [show -12*(U:ℝ) = -(12*(U:ℝ)) by ring, Real.exp_neg]
      field_simp [Real.exp_ne_zero]
    _ ≤ mainTerm n n.sqrt * (8*Real.exp (12*(U:ℝ))) :=
      mul_le_mul_of_nonneg_right hVol (by positivity)
    _ = _ := by ring

theorem endpoint_volume_upper (n cutoff cap U : ℕ) (hn : 64 ≤ n) (he : Even n)
    (hU : 2 ≤ U) (hz : 2 ≤ cut n U) (hzcut : cut n U ≤ cutoff) :
    ((endpointPairs n cutoff cap).card : ℝ) ≤
      (32 * Real.exp (12*(U:ℝ)+tiltError 0)) * mainTerm n n.sqrt *
        (∑ p ∈ endpointPrimes n cutoff cap, 1/(p:ℝ)) +
      2*(n.sqrt:ℝ)*((cut n U ^ 16 : ℕ) : ℝ)^2 := by
  have hnorm := cofactorDensity_le_terminal n U hn he hU hz
  have hsum : 0 ≤ ∑ p ∈ endpointPrimes n cutoff cap, 1/(p:ℝ) :=
    sum_nonneg (fun _ _ => by positivity)
  have hfactor : 0 ≤ 4*Real.exp (tiltError 0) *
      (∑ p ∈ endpointPrimes n cutoff cap, 1/(p:ℝ)) := by positivity
  have hmain := mul_le_mul_of_nonneg_right hnorm hfactor
  apply (endpointPairs_upper n cutoff cap (cut n U) hz hzcut).trans
  apply add_le_add_left
  rw [Real.exp_add]
  convert hmain using 1 <;> ring

end

end FareyPureEndpoint


open Finset Filter Real ErdosStraus.PrimeEstimates.Mertens
open scoped Topology

namespace FareyPurePrimeBand

noncomputable section

def primeBandMass (a b : ℕ) : ℝ :=
  ∑ p ∈ (Ioc a b).filter Nat.Prime, 1/(p:ℝ)

private theorem primeBandMass_eq {a b : ℕ} (hab : a ≤ b) :
    primeBandMass a b = primeReciprocalSum b - primeReciprocalSum a := by
  have hsub : primesUpTo a ⊆ primesUpTo b := fun p hp =>
    mem_primesUpTo.mpr ⟨(mem_primesUpTo.mp hp).1, (mem_primesUpTo.mp hp).2.trans hab⟩
  have hset : (Ioc a b).filter Nat.Prime = primesUpTo b \ primesUpTo a := by
    apply Finset.ext
    intro p
    rw [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_sdiff, mem_primesUpTo, mem_primesUpTo]
    constructor
    · rintro ⟨⟨hla, hub⟩, hp⟩
      exact ⟨⟨hp, hub⟩, fun h => (not_le_of_gt hla) h.2⟩
    · rintro ⟨⟨hp, hub⟩, h⟩
      exact ⟨⟨lt_of_not_ge (fun ha => h ⟨hp, ha⟩), hub⟩, hp⟩
  unfold primeBandMass primeReciprocalSum
  rw [hset]
  exact eq_sub_of_add_eq (Finset.sum_sdiff hsub)

theorem primeBandMass_bound :
    ∃ C > (0:ℝ), ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      primeBandMass ⌊a⌋₊ ⌊b⌋₊ ≤ log (log b/log a) + C/log a + C/log b := by
  obtain ⟨C, hC, hM⟩ := mertensSecond
  refine ⟨C, hC, fun a b ha hab => ?_⟩
  have hb := ha.trans hab
  have hla : 0 < log a := log_pos (by linarith)
  have hlb : 0 < log b := log_pos (by linarith)
  have h1 := (abs_le.mp (hM a ha)).1
  have h2 := (abs_le.mp (hM b hb)).2
  rw [primeBandMass_eq (Nat.floor_mono hab), log_div hlb.ne' hla.ne']
  linarith only [h1, h2]

theorem primeBandMass_tendsto_zero (a b : ℕ → ℝ)
    (hdom : ∀ᶠ n in atTop, 2 ≤ a n ∧ a n ≤ b n)
    (ha : Tendsto (fun n => log (a n)) atTop atTop)
    (hb : Tendsto (fun n => log (b n)) atTop atTop)
    (hq : Tendsto (fun n => log (b n)/log (a n)) atTop (𝓝 1)) :
    Tendsto (fun n => primeBandMass ⌊a n⌋₊ ⌊b n⌋₊) atTop (𝓝 0) := by
  obtain ⟨C, _, hbound⟩ := primeBandMass_bound
  have hlog := (continuousAt_log (show (1:ℝ) ≠ 0 by norm_num)).tendsto.comp hq
  have hsum := (hlog.add (tendsto_const_nhds.div_atTop ha : Tendsto
    (fun n => C/log (a n)) atTop (𝓝 0))).add
      (tendsto_const_nhds.div_atTop hb : Tendsto (fun n => C/log (b n)) atTop (𝓝 0))
  have hup : Tendsto (fun n => log (log (b n)/log (a n)) + C/log (a n) + C/log (b n))
      atTop (𝓝 0) := by simpa [Function.comp_def, log_one] using hsum
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · exact Eventually.of_forall fun n => sum_nonneg fun _ _ => by positivity
  · filter_upwards [hdom] with n hn
    exact hbound _ _ hn.1 hn.2

def cofactorCapReal (n : ℕ) : ℝ :=
  exp (log (n:ℝ)/2 - 2*(log (n:ℝ))^(2/3:ℝ))

def cofactorCap (n : ℕ) : ℕ := ⌊cofactorCapReal n⌋₊

private theorem logNatAtTop : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))

private theorem capLogFraction :
    Tendsto (fun n => log (cofactorCapReal n)/log (n:ℝ)) atTop (𝓝 (1/2:ℝ)) := by
  have ht := (tendsto_rpow_neg_atTop (show (0:ℝ) < 1/3 by norm_num)).comp logNatAtTop
  have h : Tendsto (fun n : ℕ => (1/2:ℝ) - 2*(log (n:ℝ))^(-(1/3):ℝ))
      atTop (𝓝 (1/2:ℝ)) := by simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul ht)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hlog : 0 < log (n:ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  rw [cofactorCapReal, log_exp]
  have hp := rpow_sub_one hlog.ne' (2/3:ℝ)
  rw [show (2/3:ℝ)-1 = -(1/3) by norm_num] at hp
  rw [hp]
  field_simp [hlog.ne']

private theorem capLogAtTop : Tendsto (fun n => log (cofactorCapReal n)) atTop atTop := by
  apply tendsto_atTop.2
  intro B
  have hfrac := capLogFraction.eventually (eventually_ge_nhds
    (show (1/4:ℝ) < 1/2 by norm_num))
  have hL := tendsto_atTop.mp logNatAtTop (4*B)
  filter_upwards [hfrac, hL, eventually_ge_atTop 2] with n hfrac hL hn
  have hlog : 0 < log (n:ℝ) := log_pos (by exact_mod_cast (show 1 < n by omega))
  have hh := (le_div_iff₀ hlog).mp hfrac
  linarith

theorem cofactorCap_le_sqrt (n : ℕ) (hn : 1 ≤ n) : cofactorCap n ≤ n.sqrt := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ log (n:ℝ) := log_nonneg (by exact_mod_cast hn)
  have hpow : 0 ≤ (log (n:ℝ))^(2/3:ℝ) := rpow_nonneg hlog _
  have hcap : cofactorCapReal n ≤ GoldbachLateDensity.high n := by
    rw [cofactorCapReal, GoldbachLateDensity.high, rpow_def_of_pos hnR]
    exact exp_le_exp.mpr (by linarith)
  have hfloor : ⌊GoldbachLateDensity.high n⌋₊ = n.sqrt := by
    rw [GoldbachLateDensity.high, ←sqrt_eq_rpow, nat_floor_real_sqrt_eq_nat_sqrt]
  exact (Nat.floor_mono hcap).trans_eq hfloor

theorem cofactorCapBand_tendsto_zero :
    Tendsto (fun n => primeBandMass (cofactorCap n) n.sqrt) atTop (𝓝 0) := by
  have hh : ∀ᶠ n in atTop, log (GoldbachLateDensity.high n) = (1/2:ℝ)*log (n:ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact log_rpow (by exact_mod_cast (show 0 < n by omega)) _
  have hhigh : Tendsto (fun n => log (GoldbachLateDensity.high n)) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [hh, tendsto_atTop.mp logNatAtTop (2*B)] with n hh hL
    linarith
  have hratio0 := (show Tendsto (fun _ : ℕ => (1/2:ℝ)) atTop (𝓝 (1/2:ℝ)) from
    tendsto_const_nhds).div capLogFraction (by norm_num : (1/2:ℝ) ≠ 0)
  have hratio : Tendsto (fun n => log (GoldbachLateDensity.high n)/log (cofactorCapReal n))
      atTop (𝓝 1) := by
    have h : Tendsto (fun n => (1/2:ℝ)/(log (cofactorCapReal n)/log (n:ℝ))) atTop (𝓝 1) := by
      change Tendsto (fun n : ℕ => (1/2:ℝ)/(log (cofactorCapReal n)/log (n:ℝ)))
        atTop (𝓝 ((1/2:ℝ)/(1/2))) at hratio0
      simpa only [div_self (by norm_num : (1/2:ℝ) ≠ 0)] using hratio0
    apply h.congr'
    filter_upwards [hh, eventually_ge_atTop 2, tendsto_atTop.mp capLogAtTop 1] with n hh hn hc
    have hL : (log (n:ℝ)) ≠ 0 := (log_pos (by exact_mod_cast (show 1 < n by omega))).ne'
    have hcap : log (cofactorCapReal n) ≠ 0 := by linarith
    rw [hh]
    field_simp
  have hdom : ∀ᶠ n in atTop, 2 ≤ cofactorCapReal n ∧
      cofactorCapReal n ≤ GoldbachLateDensity.high n := by
    filter_upwards [eventually_ge_atTop 2, tendsto_atTop.mp capLogAtTop (log 2)] with n hn hlog
    have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    constructor
    · have h := exp_le_exp.mpr hlog
      rwa [exp_log (by norm_num : (0:ℝ)<2), exp_log (by unfold cofactorCapReal; positivity)] at h
    · rw [cofactorCapReal, GoldbachLateDensity.high, rpow_def_of_pos hnR]
      have hpow : 0 ≤ (log (n:ℝ))^(2/3:ℝ) := rpow_nonneg
        (log_nonneg (by exact_mod_cast (show 1≤n by omega))) _
      exact exp_le_exp.mpr (by linarith)
  have h := primeBandMass_tendsto_zero _ _ hdom capLogAtTop hhigh hratio
  have hfloor (n : ℕ) : ⌊GoldbachLateDensity.high n⌋₊ = n.sqrt := by
    rw [GoldbachLateDensity.high, ←sqrt_eq_rpow, nat_floor_real_sqrt_eq_nat_sqrt]
  simpa only [cofactorCap, hfloor] using h

end

end FareyPurePrimeBand


open Filter Finset Real
open FareyBrun FareyPureEndpoint FareyPurePrimeBand
open scoped Topology

namespace FareyPureEndpointLimit

noncomputable section

def cubeCut (n : ℕ) : ℕ := ⌊(n:ℝ)^(1/3:ℝ)⌋₊

private theorem rounding_bound (n : ℕ) (hn : 0 < n) :
    2*(n.sqrt:ℝ)*((cut n 256 ^ 16 : ℕ):ℝ)^2 ≤ 2*(n:ℝ)^(5/8:ℝ) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hz : (cut n 256 : ℝ) ≤ (n:ℝ)^(1/256:ℝ) :=
    Nat.floor_le (rpow_nonneg hnR.le _)
  have hw : ((cut n 256 ^ 16 : ℕ):ℝ)^2 ≤ (n:ℝ)^(1/8:ℝ) := by
    calc
      _ = ((cut n 256:ℕ):ℝ)^32 := by push_cast; ring
      _ ≤ ((n:ℝ)^(1/256:ℝ))^32 := pow_le_pow_left₀ (by positivity) hz 32
      _ = _ := by rw [← rpow_natCast, ← rpow_mul hnR.le]; norm_num
  have hs : (n.sqrt:ℝ) ≤ (n:ℝ)^(1/2:ℝ) := by
    rw [← sqrt_eq_rpow, ← nat_floor_real_sqrt_eq_nat_sqrt]
    exact Nat.floor_le (sqrt_nonneg _)
  calc
    _ ≤ 2 * (n:ℝ)^(1/2:ℝ) * (n:ℝ)^(1/8:ℝ) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hw
        (by positivity) (by positivity)
    _ = _ := by rw [mul_assoc, ← rpow_add hnR]; norm_num

set_option maxHeartbeats 1200000 in
theorem endpoint_negligible (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 64 ≤ N ∧ ∀ n : ℕ, N ≤ n → Even n →
      ((endpointPairs n (cubeCut n) (cofactorCap n)).card:ℝ) ≤
        ε * mainTerm n n.sqrt := by
  obtain ⟨c, hc, hfloor⟩ := terminal_floor_power
  let B : ℝ := 32 * exp (12*((256:ℕ):ℝ)+tiltError 0)
  have hB : 0 ≤ B := by unfold B; positivity
  have hlim : Tendsto (fun n => B * primeBandMass (cofactorCap n) n.sqrt) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := B)).mul cofactorCapBand_tendsto_zero
  have hsmall := hlim.eventually (eventually_le_nhds (show (0:ℝ) < ε/2 by positivity))
  have hdecay : Tendsto (fun n : ℕ => (2/c)*(n:ℝ)^(-(1/4):ℝ)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (2/c:ℝ))).mul
      ((tendsto_rpow_neg_atTop (show (0:ℝ)<1/4 by norm_num)).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hround := hdecay.eventually (eventually_le_nhds (show (0:ℝ) < ε/2 by positivity))
  have hnat : Tendsto (fun n => cut n 256) atTop atTop := by
    exact tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (show (0:ℝ)<1/256 by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have hlarge := tendsto_atTop.mp hnat 2
  have heventual : ∀ᶠ n : ℕ in atTop, 64 ≤ n ∧ (Even n →
      ((endpointPairs n (cubeCut n) (cofactorCap n)).card:ℝ) ≤ ε * mainTerm n n.sqrt) := by
    filter_upwards [eventually_ge_atTop 64, hlarge, hsmall, hround] with n hn hz hsmall hround
    refine ⟨hn, fun he => ?_⟩
    have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hzcut : cut n 256 ≤ cubeCut n := by
      apply Nat.floor_mono
      exact rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1≤n by omega)) (by norm_num)
    have hmass : (∑ p ∈ endpointPrimes n (cubeCut n) (cofactorCap n), 1/(p:ℝ)) ≤
        primeBandMass (cofactorCap n) n.sqrt := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hi, hp⟩ := mem_filter.mp hp
        obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hi
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(le_max_right _ _).trans_lt hlo, hhi⟩, hp⟩
      · intro p _ _
        positivity
    have hconst : B * (∑ p ∈ endpointPrimes n (cubeCut n) (cofactorCap n), 1/(p:ℝ)) ≤ ε/2 :=
      (mul_le_mul_of_nonneg_left hmass hB).trans hsmall
    have hrem : 2*(n:ℝ)^(5/8:ℝ) ≤ (ε/2)*mainTerm n n.sqrt := by
      calc
        _ = ((2/c)*(n:ℝ)^(-(1/4):ℝ)) * (c*(n:ℝ)^(7/8:ℝ)) := by
          rw [show ((2/c)*(n:ℝ)^(-(1/4):ℝ))*(c*(n:ℝ)^(7/8:ℝ)) =
              ((2/c)*c)*((n:ℝ)^(-(1/4):ℝ)*(n:ℝ)^(7/8:ℝ)) by ring,
            div_mul_cancel₀ _ hc.ne', ← rpow_add hnR]
          norm_num
        _ ≤ (ε/2)*(c*(n:ℝ)^(7/8:ℝ)) := mul_le_mul_of_nonneg_right hround (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (hfloor n hn he) (by positivity)
    have hupper := endpoint_volume_upper n (cubeCut n) (cofactorCap n) 256 hn he
      (by decide) hz hzcut
    calc
      _ ≤ (B * (∑ p ∈ endpointPrimes n (cubeCut n) (cofactorCap n), 1/(p:ℝ))) *
          mainTerm n n.sqrt + 2*(n.sqrt:ℝ)*((cut n 256 ^ 16 : ℕ):ℝ)^2 := by
        convert hupper using 1
        unfold B
        ring
      _ ≤ (ε/2)*mainTerm n n.sqrt + (ε/2)*mainTerm n n.sqrt :=
        add_le_add (mul_le_mul_of_nonneg_right hconst (mainTerm_nonneg _ _))
          ((rounding_bound n (by omega)).trans hrem)
      _ = _ := by ring
  obtain ⟨N,hN⟩ := eventually_atTop.mp heventual
  exact ⟨max N 64, le_max_right .., fun n hn he => (hN n ((le_max_left ..).trans hn)).2 he⟩

end

end FareyPureEndpointLimit


open Finset
open scoped BigOperators

theorem Conjectures.Cuts.Taskd4c2c458d1b6958628c99f53 : (have x1 : ℕ → Finset ℕ := fun (x1 : ℕ) => Finset.Icc ((x1 + (2 : ℕ)) / (3 : ℕ)) ((2 : ℕ) * x1 / (3 : ℕ)); have x2 : ℕ → Finset ℕ := fun (x2 : ℕ) => Finset.filter Nat.Prime (Finset.Icc (2 : ℕ) x2); have x3 : ℕ → Finset ℕ := fun (x3 : ℕ) => {x4 ∈ x1 x3 | ⌊(↑x3 : ℝ) ^ (1 / 3 : ℝ)⌋₊ < x4.minFac ∧ Nat.Prime x4.minFac ∧ Nat.Prime (x4 / x4.minFac)}; have x4 : ℕ → ℝ := fun (x4 : ℕ) => (↑(x1 x4).card : ℝ) * (↑x4.totient : ℝ) / (↑x4 : ℝ) * ∏ x5 ∈ x2 x4.sqrt with ¬x5 ∣ x4, ((1 : ℝ) - (2 : ℝ) / (↑x5 : ℝ)); have x5 : ℕ → Finset ℕ := fun (x5 : ℕ) => {x6 ∈ x3 x5 | x5 - x6 ∈ x3 x5}; have x6 : ℕ → ℕ := fun (x6 : ℕ) => ⌊Real.exp (Real.log (↑x6 : ℝ) / (2 : ℝ) - (2 : ℝ) * Real.log (↑x6 : ℝ) ^ (2 / 3 : ℝ))⌋₊; ∃ (x7 : ℕ), ∀ (x8 : ℕ), x7 ≤ x8 → Even x8 → (↑{x11 ∈ x5 x8 | x6 x8 < x11.minFac ∨ x6 x8 < (x8 - x11).minFac}.card : ℝ) ≤ (1 / 500 : ℝ) * x4 x8) := by
  obtain ⟨N, _, hN⟩ := FareyPureEndpointLimit.endpoint_negligible (1/500) (by norm_num)
  refine ⟨N, fun n hn he => ?_⟩
  let cutoff := FareyPureEndpointLimit.cubeCut n
  let cap := FareyPurePrimeBand.cofactorCap n
  let semiprimes := (FareyBrun.window n).filter (FareyPureEndpoint.semiprimeAbove cutoff)
  change (((semiprimes.filter (fun m => n-m ∈ semiprimes)).filter
    (fun m => cap < m.minFac ∨ cap < (n-m).minFac)).card:ℝ) ≤
      (1/500:ℝ) * FareyBrun.mainTerm n n.sqrt
  have hset : ((semiprimes.filter (fun m => n-m ∈ semiprimes)).filter
      (fun m => cap < m.minFac ∨ cap < (n-m).minFac)) =
        FareyPureEndpoint.endpointPairs n cutoff cap := by
    apply Finset.ext
    intro m
    simp only [semiprimes, FareyPureEndpoint.endpointPairs, FareyPureEndpoint.bothSemiprimes,
      Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨hwin, hm⟩, _, hreflect⟩, hcap⟩
      exact ⟨⟨hwin, hm, hreflect⟩, hcap⟩
    · rintro ⟨⟨hwin, hm, hreflect⟩, hcap⟩
      exact ⟨⟨⟨hwin, hm⟩, FareyPureEndpoint.mem_window_reflect hwin, hreflect⟩, hcap⟩
  rw [hset]
  exact hN n hn he
