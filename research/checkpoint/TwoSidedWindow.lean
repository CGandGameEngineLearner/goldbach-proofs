import Conjectures.Goldbach.DynFirstMass
import Conjectures.Goldbach.DynPathSecondMoment
import Mathlib

open Finset
namespace Goldbach.TwoSidedWindow
noncomputable section

/-- Number of distinct first coordinates of paths arriving at n. -/
def paths (P Q : Finset ℕ) (n : ℕ) :=
  (P.filter (fun p => p ≤ n ∧ n-p ∈ Q)).card

private theorem mass_le (E P Q : Finset ℕ) : ∑ n ∈ E, paths P Q n ≤ P.card * Q.card := by
  classical
  calc
    _ = ∑ p ∈ P, (E.filter (fun n => p ≤ n ∧ n-p ∈ Q)).card := by
      simp only [paths, Finset.card_filter]
      exact Finset.sum_comm
    _ ≤ ∑ _p ∈ P, Q.card := by
      apply sum_le_sum
      intro p _
      apply card_le_card_of_injOn (fun n => n-p)
      · exact fun n hn => (mem_filter.mp hn).2.2
      · intro n hn m hm h
        have hn' := (mem_filter.mp hn).2.1
        have hm' := (mem_filter.mp hm).2.1
        change n-p=m-p at h
        omega
    _ = _ := by simp

theorem deletion_cost (E P Q U V : Finset ℕ) :
    ∑ n ∈ E, paths P Q n ≤ (∑ n ∈ E, paths (P \ U) (Q \ V) n) +
        U.card * Q.card + P.card * V.card := by
  classical
  have row (n : ℕ) : paths P Q n ≤ paths (P \ U) (Q \ V) n + paths U Q n + paths P V n := by
    let T (P Q : Finset ℕ) := P.filter (fun p => p ≤ n ∧ n-p ∈ Q)
    have hs : T P Q ⊆ (T (P \ U) (Q \ V) ∪ T U Q) ∪ T P V := by
      intro p hp
      obtain ⟨hpP,hpn,hqQ⟩ := mem_filter.mp hp
      by_cases hU : p ∈ U
      · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hU,hpn,hqQ⟩))
      by_cases hV : n-p ∈ V
      · exact mem_union_right _ (mem_filter.mpr ⟨hpP,hpn,hV⟩)
      exact mem_union_left _ (mem_union_left _ (mem_filter.mpr
        ⟨mem_sdiff.mpr ⟨hpP,hU⟩,hpn,mem_sdiff.mpr ⟨hqQ,hV⟩⟩))
    exact (card_le_card hs).trans ((card_union_le ..).trans
      (Nat.add_le_add_right (card_union_le ..) _))
  calc
    _ ≤ ∑ n ∈ E, (paths (P \ U) (Q \ V) n + paths U Q n + paths P V n) := sum_le_sum fun n _ => row n
    _ ≤ _ := by
      simp only [sum_add_distrib]
      have := mass_le E U Q
      have := mass_le E P V
      omega

/-- Both windows contain only primes at least sqrt X. This common estimate
pays for deleting a first prime or a second prime at their own natural scales. -/
theorem window_upper (X B : ℕ) (hX : 16 ≤ X) :
    ((((Icc (Nat.sqrt X) B).filter Nat.Prime).card : ℝ) * Real.log X)
    ≤ (4 * Real.log 4) * B := by
  let s := Nat.sqrt X
  let P := (Icc s B).filter Nat.Prime
  have hs : 4 ≤ s := Nat.le_sqrt.mpr hX
  have hsR : (4:ℝ) ≤ s := by exact_mod_cast hs
  have hXR : 0 < (X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have hpow : X ≤ s^4 := by
    have ht := Nat.lt_succ_sqrt X
    change X < (s+1)*(s+1) at ht
    have h₂ : s+1 ≤ s^2 := by nlinarith
    nlinarith [Nat.mul_le_mul h₂ h₂]
  have hlog := Real.log_le_log hXR (show (X:ℝ) ≤ (s:ℝ)^4 by exact_mod_cast hpow)
  rw [Real.log_pow] at hlog
  have hmass : (P.card:ℝ)*Real.log (s:ℝ) ≤ Real.log 4 * (B:ℝ) := by
    calc
      _ = ∑ _p ∈ P, Real.log (s:ℝ) := by simp [nsmul_eq_mul]
      _ ≤ ∑ p ∈ P, Real.log (p:ℝ) := by
        exact sum_le_sum fun p hp => Real.log_le_log (by linarith) (by exact_mod_cast (mem_Icc.mp (mem_filter.mp hp).1).1)
      _ ≤ ∑ p ∈ B.primesLE, Real.log (p:ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg
        · exact fun p hp => Nat.mem_primesLE.mpr ⟨(mem_Icc.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
        · intro p hp _
          exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
      _ ≤ _ := by rw [← Chebyshev.theta_eq_sum_primesLE_log]; exact Chebyshev.theta_le_log4_mul_x (by positivity)
  change (P.card:ℝ) * Real.log X ≤ _
  push_cast at hlog
  nlinarith only [hmass, mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (α:=ℝ) P.card)]

/-- Rich representations survive simultaneous deletions in both prime windows. -/
theorem two_sided_rich :
    let E := fun X : ℕ => (Icc X (2*X)).filter Even
    let P := fun X : ℕ => (Icc X.sqrt (2*X.sqrt)).filter Nat.Prime
    let M := fun X : ℕ => Real.sqrt X / (Real.log X)^2
    ∃ η c δ : ℝ, 0 < η ∧ 0 < c ∧ 0 < δ ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ U V : Finset ℕ,
      (U.card:ℝ) ≤ η*Real.sqrt X / Real.log X →
      (V.card:ℝ) ≤ η*X / Real.log X →
      δ*X ≤ (((E X).filter (fun n => c*M X ≤
        (((P X \ U).filter (fun p => p ≤ n ∧ (n-p).Prime ∧ n-p ∉ V)).card : ℝ))).card : ℝ) := by
  classical
  intro E P M
  obtain ⟨a,ha,N₁,hmass⟩ := Conjectures.Goldbach.DynFirstMass
  obtain ⟨b,hb,N₂,henergy⟩ := Conjectures.Goldbach.DynPathSecondMoment
  let k : ℝ := 8 * Real.log 4
  have hk : 0 < k := by dsimp [k]; positivity
  refine ⟨a/(4*k),a/8,a^2/(16*b),by positivity,by positivity,by positivity,
    max 16 (max N₁ N₂),?_⟩
  intro X hX U V hU hV
  have h16 : 16 ≤ X := by omega
  have hx : (0:ℝ) < X := by exact_mod_cast (show 0<X by omega)
  let L := Real.log (X:ℝ)
  let R := Real.sqrt (X:ℝ)
  have hL : 0 < L := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hR : 0 < R := Real.sqrt_pos.mpr hx
  have hm : 0 < M X := by dsimp [M]; positivity
  let Q := (Icc X.sqrt (2*X)).filter Nat.Prime
  let H := fun n => ((P X).filter (fun p => p ≤ n ∧ Nat.Prime (n-p))).card
  let J := paths (P X \ U) (Q \ V)
  let G := (E X).filter (fun n => a/8*M X ≤ (J n:ℝ))
  have hs : 4 ≤ X.sqrt := Nat.le_sqrt.mpr h16
  have hs2 := Nat.sqrt_le' X
  have hsR : (X.sqrt:ℝ) ≤ R := (Real.le_sqrt (by positivity) hx.le).mpr (by exact_mod_cast hs2)
  have qmem {n p : ℕ} (hn : n ∈ E X) (hp : p ∈ P X) :
      n-p ∈ Q ↔ (n-p).Prime := by
    have hr := mem_Icc.mp (mem_filter.mp hn).1
    have hw := mem_Icc.mp (mem_filter.mp hp).1
    have h3 : 3*X.sqrt ≤ X := by nlinarith
    exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,h⟩⟩
  have hH {n} (hn : n ∈ E X) : paths (P X) Q n = H n := by
    unfold paths H
    congr 1
    exact filter_congr fun p hp => and_congr_right fun _ => qmem hn hp
  have hJ {n} (hn : n ∈ E X) : J n =
      ((P X \ U).filter (fun p => p ≤ n ∧ (n-p).Prime ∧ n-p ∉ V)).card := by
    dsimp [J,paths]
    congr 1
    exact filter_congr fun p hp => by rw [mem_sdiff, qmem hn (mem_sdiff.mp hp).1]
  have hJle {n} (hn : n ∈ E X) : J n ≤ H n := by
    rw [hJ hn]
    apply card_le_card
    intro p hp
    obtain ⟨hpu,hpn,hprime,_⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨(mem_sdiff.mp hpu).1,hpn,hprime⟩
  have hQ : (Q.card:ℝ) ≤ k*X/L := by
    apply (le_div_iff₀ hL).mpr
    have h := window_upper X (2*X) h16
    push_cast at h
    dsimp [k]; change (Q.card:ℝ)*Real.log X ≤ _; linarith only [h]
  have hP : ((P X).card:ℝ) ≤ k*R/L := by
    apply (le_div_iff₀ hL).mpr
    have h := window_upper X (2*X.sqrt) h16
    push_cast at h
    dsimp [k]; change ((P X).card:ℝ)*Real.log X ≤ _
    linarith only [h,mul_le_mul_of_nonneg_left hsR (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4))]
  have hcost : (U.card:ℝ)*Q.card+((P X).card:ℝ)*V.card ≤ a/2*X*M X := by
    calc
      _ ≤ (a/(4*k)*R/L)*(k*X/L) + (k*R/L)*(a/(4*k)*X/L) :=
        add_le_add (mul_le_mul hU hQ (by positivity) (by positivity))
          (mul_le_mul hP hV (by positivity) (by positivity))
      _ = _ := by dsimp [M,R,L]; field_simp [hk.ne']; ring
  have hcount := deletion_cost (E X) (P X) Q U V
  rw [sum_congr rfl (fun n hn => hH hn)] at hcount
  have hcountR : (∑ n ∈ E X, (H n:ℝ)) ≤ (∑ n ∈ E X, (J n:ℝ)) + (U.card:ℝ)*Q.card + ((P X).card:ℝ)*V.card := by exact_mod_cast hcount
  have hfirst : a*X*M X ≤ ∑ n ∈ E X, (H n:ℝ) := hmass X (by omega)
  have he : (E X).card ≤ 2*X := (card_filter_le ..).trans (by simp; omega)
  have hlow : (∑ n ∈ (E X).filter (fun n => ¬ a/8*M X ≤ (J n:ℝ)), (J n:ℝ)) ≤ a/4*X*M X := by
    let T := (E X).filter (fun n => ¬ a/8*M X ≤ (J n:ℝ))
    calc
      _ ≤ ∑ _n ∈ T, a/8*M X := sum_le_sum fun n hn => le_of_lt (lt_of_not_ge (mem_filter.mp hn).2)
      _ = (T.card:ℝ)*(a/8*M X) := by simp [nsmul_eq_mul]
      _ ≤ (2*(X:ℝ))*(a/8*M X) := mul_le_mul_of_nonneg_right (by exact_mod_cast (card_filter_le ..).trans he) (by positivity)
      _ = _ := by ring
  have hsplit := sum_filter_add_sum_filter_not (E X) (fun n => a/8*M X ≤ (J n:ℝ)) (fun n => (J n:ℝ))
  have hrich : a/4*X*M X ≤ ∑ n ∈ G, (J n:ℝ) := by dsimp only [G]; linarith
  have hCS := sq_sum_le_card_mul_sum_sq (s:=G) (f:=fun n => (J n:ℝ))
  have hmom : (∑ n ∈ G, (J n:ℝ)^2) ≤ b*X*(M X)^2 := by
    calc
      _ ≤ ∑ n ∈ G, (H n:ℝ)^2 := sum_le_sum fun n hn => pow_le_pow_left₀ (by positivity) (by exact_mod_cast hJle (mem_filter.mp hn).1) 2
      _ ≤ ∑ n ∈ E X, (H n:ℝ)^2 := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := henergy X (by omega)
  have htop := (pow_le_pow_left₀ (by positivity) hrich 2).trans (hCS.trans (mul_le_mul_of_nonneg_left hmom (Nat.cast_nonneg (α:=ℝ) G.card)))
  have heq : G = _ := filter_congr (s:=E X) (fun n hn => show (a/8*M X ≤ (J n:ℝ)) ↔ _ by rw [hJ hn])
  rw [← heq]
  apply le_of_mul_le_mul_right (a:=(16*b)*(X:ℝ)*(M X)^2) _ (by positivity)
  calc
    _ = 16*(a/4*X*M X)^2 := by field_simp [hb.ne']; ring
    _ ≤ 16*((G.card:ℝ)*(b*X*(M X)^2)) := by linarith only [htop]
    _ = _ := by ring
end
end Goldbach.TwoSidedWindow

namespace Goldbach.TwoSidedWindow
open Finset Filter
open scoped Topology

/-- A family of representations in which each first prime, second prime and
target is used at most once. The primes occupy disjoint windows for large X. -/
def Compatible (X : ℕ) (T : Finset (ℕ × ℕ)) : Prop :=
  (∀ z ∈ T, z.1 ∈ Icc X.sqrt (2*X.sqrt) ∧ z.1.Prime ∧ z.2.Prime ∧
    z.1+z.2 ∈ Icc X (2*X) ∧ Even (z.1+z.2)) ∧
  Set.InjOn Prod.fst (T : Set (ℕ × ℕ)) ∧ Set.InjOn Prod.snd (T : Set (ℕ × ℕ)) ∧
  Set.InjOn (fun z : ℕ × ℕ => z.1+z.2) (T : Set (ℕ × ℕ))

private theorem extend_inj {T : Finset (ℕ × ℕ)} {z : ℕ × ℕ} {f : ℕ × ℕ → ℕ}
    (hf : Set.InjOn f (T : Set (ℕ × ℕ))) (hnew : f z ∉ T.image f) (hz : z ∉ T) :
    Set.InjOn f ((insert z T : Finset _) : Set (ℕ × ℕ)) := by
  rw [coe_insert, Set.injOn_insert (by exact hz)]
  exact ⟨hf, fun h => hnew (by simpa using h)⟩

/-- A matching of order sqrt(X)/log X with pairwise distinct target sums.
The constant and the threshold do not depend on the requested cardinality. -/
theorem disjoint_representations :
    ∃ κ : ℝ, 0 < κ ∧ ∃ X₀ : ℕ, ∀ X ≥ X₀, ∀ k : ℕ,
      (k:ℝ) ≤ κ*Real.sqrt X/Real.log X →
      ∃ T : Finset (ℕ × ℕ), T.card = k ∧ Compatible X T := by
  classical
  obtain ⟨η,c,δ,hη,hc,hδ,N,hres⟩ := two_sided_rich
  have hlarge := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))).eventually_ge_atTop 1
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp hlarge
  refine ⟨min η δ, lt_min hη hδ, max 16 (max N N₁), ?_⟩
  intro X hX k hk
  have h16 : 16 ≤ X := by omega
  have hx : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hx1 : (1:ℝ)≤X := by exact_mod_cast (show 1≤X by omega)
  let L := Real.log (X:ℝ)
  let R := Real.sqrt (X:ℝ)
  have hl1 : 1 ≤ L := hN₁ X (by omega)
  have hl : 0 < L := by linarith
  have hr : 0 < R := Real.sqrt_pos.mpr hx
  have hrX : R ≤ X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hx.le,by nlinarith [mul_nonneg hx.le (sub_nonneg.mpr hx1)]⟩
  have hsmall : (k:ℝ) ≤ η*R/L := hk.trans (by gcongr; exact min_le_left ..)
  have hbig : (k:ℝ) ≤ η*X/L := hsmall.trans (by gcongr)
  have htgt : (k:ℝ) ≤ δ*X := by
    calc
      _ ≤ min η δ * R/L := hk
      _ ≤ δ*R/L := by gcongr; exact min_le_right ..
      _ ≤ δ*R := div_le_self (by positivity) hl1
      _ ≤ _ := by gcongr
  have build (j : ℕ) (hj : j ≤ k) : ∃ T : Finset (ℕ × ℕ), T.card = j ∧ Compatible X T := by
    induction j with
    | zero => exact ⟨∅,by simp,by simp [Compatible]⟩
    | succ j ih =>
      obtain ⟨T,hT,hz,hp,hq,ht⟩ := ih (by omega)
      let U := T.image Prod.fst
      let V := T.image Prod.snd
      let W := T.image (fun z : ℕ × ℕ => z.1 + z.2)
      have ub : (U.card:ℝ) ≤ η*R/L := le_trans (by exact_mod_cast (card_image_le.trans (hT.le.trans (by omega : j ≤ k)))) hsmall
      have vb : (V.card:ℝ) ≤ η*X/L := le_trans (by exact_mod_cast (card_image_le.trans (hT.le.trans (by omega : j ≤ k)))) hbig
      have hh := hres X (by omega) U V ub vb
      have hw : (W.card:ℝ) < k := by exact_mod_cast (card_image_le.trans_lt (hT.le.trans_lt (by omega : j < k)))
      obtain ⟨n, hn, hnW⟩ := exists_mem_notMem_of_card_lt_card (by exact_mod_cast (hw.trans_le (htgt.trans hh)))
      obtain ⟨hnE,hnJ⟩ := mem_filter.mp hn
      have hpos : 0 < c*(Real.sqrt (X:ℝ)/(Real.log (X:ℝ))^2) := mul_pos hc (div_pos hr (sq_pos_of_pos hl))
      obtain ⟨p,hpJ⟩ := Finset.card_pos.mp (by exact_mod_cast hpos.trans_le hnJ)
      obtain ⟨hpU,hpn,hqP,hqV⟩ := mem_filter.mp hpJ
      obtain ⟨hpP,hpFresh⟩ := mem_sdiff.mp hpU
      obtain ⟨hpI,hpPrime⟩ := mem_filter.mp hpP
      have hsum : p + (n-p) = n := by omega
      let z : ℕ × ℕ := (p,n-p)
      have hnew : z ∉ T := fun h => hpFresh (mem_image_of_mem Prod.fst h)
      refine ⟨insert z T,by rw [card_insert_of_notMem hnew,hT],?_,extend_inj hp hpFresh hnew,
        extend_inj hq hqV hnew,extend_inj ht (by simpa only [z,hsum] using hnW) hnew⟩
      intro v hv
      rcases mem_insert.mp hv with rfl | hv
      · obtain ⟨hi,hev⟩ := mem_filter.mp hnE
        exact ⟨hpI,hpPrime,hqP,hsum ▸ hi,hsum ▸ hev⟩
      · exact hz v hv
  exact build k le_rfl

end Goldbach.TwoSidedWindow

namespace Goldbach.TwoSidedWindow

/-- Distinct first primes give the matching upper bound on the same scale. -/
theorem disjoint_upper {X : ℕ} (hX : 16 ≤ X) {T : Finset (ℕ × ℕ)}
    (hT : Compatible X T) :
    (T.card:ℝ) ≤ (8 * Real.log 4) * Real.sqrt X / Real.log X := by
  have hcard : T.card ≤ ((Icc X.sqrt (2*X.sqrt)).filter Nat.Prime).card :=
    card_le_card_of_injOn Prod.fst (fun z hz => mem_filter.mpr ⟨(hT.1 z hz).1,(hT.1 z hz).2.1⟩) hT.2.1
  have hl : 0 < Real.log (X:ℝ) := Real.log_pos (by exact_mod_cast (show 1<X by omega))
  have hroot : (X.sqrt:ℝ) ≤ Real.sqrt (X:ℝ) :=
    (Real.le_sqrt (by positivity) (by positivity)).mpr (by exact_mod_cast Nat.sqrt_le' X)
  apply (le_div_iff₀ hl).mpr
  have hw := window_upper X (2*X.sqrt) hX
  push_cast at hw
  have h := (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard :
    (T.card:ℝ) ≤ (((Icc X.sqrt (2*X.sqrt)).filter Nat.Prime).card:ℝ)) hl.le).trans hw
  linarith only [h, mul_le_mul_of_nonneg_left hroot (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4))]
end Goldbach.TwoSidedWindow
