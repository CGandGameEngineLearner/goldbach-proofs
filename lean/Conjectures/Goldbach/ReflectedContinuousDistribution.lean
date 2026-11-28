import Mathlib
import Conjectures.Goldbach.ReflectedShiftedPairMoment

-- The mean-square bound and reflected-band model are from the verified proof in #4434.


namespace GoldbachReflectedShiftCRTCore

open Finset
open scoped BigOperators Classical

private theorem sum_natCast_range_eq_zmod {L : ℕ} [NeZero L] (f : ZMod L → ℝ) :
    ∑ n ∈ range L, f (n : ZMod L) = ∑ x : ZMod L, f x := by
  apply sum_bij (s := range L) (t := (univ : Finset (ZMod L))) (fun n _ => (n : ZMod L))
  · simp
  · intro a ha b hb hab
    have hval := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_range.mp ha),
      Nat.mod_eq_of_lt (mem_range.mp hb)] using hval
  · intro x _
    exact ⟨x.val, mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
  · intro n _
    rfl

set_option maxHeartbeats 1600000 in
/-- A complete period of independent prime residues factors, even after
any starting shift. -/
private theorem crt_sum (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    [∀ p : S, NeZero (p : ℕ)] (F : ∀ p : S, ZMod (p : ℕ) → ℝ) (start : ℕ) :
    (∑ n ∈ range (∏ p ∈ S, p), ∏ p : S, F p ((start + n : ℕ) : ZMod (p : ℕ))) =
      ∏ p : S, ∑ x : ZMod (p : ℕ), F p x := by
  let L := ∏ p : S, (p : ℕ)
  have hLpos : 0 < L := prod_pos (fun p _ => (hS p p.property).pos)
  let _ : NeZero L := ⟨hLpos.ne'⟩
  have hc : Pairwise (fun p q : S => (p : ℕ).Coprime (q : ℕ)) := by
    intro p q hpq
    apply (Nat.coprime_primes (hS p p.property) (hS q q.property)).mpr
    exact fun h => hpq (Subtype.ext h)
  let e := ZMod.prodEquivPi (fun p : S => (p : ℕ)) hc
  have comp (n : ℕ) (p : S) : e (n : ZMod L) p = (n : ZMod (p : ℕ)) := by
    dsimp only [e]
    rw [ZMod.prodEquivPi_apply, map_natCast]
  have hL : L = ∏ p ∈ S, p := prod_coe_sort S id
  rw [← hL]
  calc
    _ = ∑ n ∈ range L, ∏ p : S, F p (e (n : ZMod L) p + (start : ZMod (p : ℕ))) := by
      apply sum_congr rfl
      intro n _
      apply prod_congr rfl
      intro p _
      rw [comp, Nat.cast_add, add_comm]
    _ = ∑ n : ZMod L, ∏ p : S, F p (e n p + (start : ZMod (p : ℕ))) :=
      sum_natCast_range_eq_zmod (L := L)
        (fun (n : ZMod L) => ∏ p : S, F p (e n p + (start : ZMod (p : ℕ))))
    _ = ∑ t : ∀ p : S, ZMod (p : ℕ), ∏ p : S, F p (t p + (start : ZMod (p : ℕ))) :=
      Equiv.sum_comp e.toEquiv
        (fun (t : ∀ p : S, ZMod (p : ℕ)) => ∏ p : S, F p (t p + (start : ZMod (p : ℕ))))
    _ = ∏ p : S, ∑ x : ZMod (p : ℕ), F p (x + (start : ZMod (p : ℕ))) :=
      (Fintype.prod_sum (fun (p : S) (x : ZMod (p : ℕ)) =>
        F p (x + (start : ZMod (p : ℕ))))).symm
    _ = _ := by
      apply prod_congr rfl
      intro p _
      exact Equiv.sum_comp (Equiv.addRight (start : ZMod (p : ℕ))) (F p)

/-- Complete blocks contribute their exact mean. The leftover block and
its proposed mean each cost at most its length. -/
private theorem bounded_interval_error (f : ℕ → ℝ) (μ : ℝ) (P : ℕ) (hP : 0 < P)
    (hf : ∀ n, |f n| ≤ 1) (hμ : |μ| ≤ 1)
    (hm : ∀ s, (∑ n ∈ range P, f (s+n)) = (P : ℝ)*μ) (start length : ℕ) :
    |(∑ n ∈ range length, f (start+n)) - (length : ℝ)*μ| ≤ 2*(P : ℝ) := by
  have hblock (k : ℕ) :
      (∑ n ∈ range (k*P), f (start+n)) = ((k*P : ℕ) : ℝ)*μ := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.succ_mul, sum_range_add (fun n => f (start+n)), ih]
        simp_rw [← Nat.add_assoc start (k*P)]
        rw [hm, Nat.cast_add, add_mul]
  let k := length/P
  let r := length % P
  have hL : length = k*P+r := by
    simpa only [k, r, mul_comm P] using (Nat.div_add_mod length P).symm
  have hr : r < P := Nat.mod_lt _ hP
  have hsum : |∑ n ∈ range r, f (start+(k*P+n))| ≤ (r : ℝ) := calc
    _ ≤ ∑ n ∈ range r, |f (start+(k*P+n))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ range r, (1 : ℝ) := sum_le_sum (fun _ _ => hf _)
    _ = _ := by simp
  have hrμ : |(r : ℝ)*μ| ≤ (r : ℝ) := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg r)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hμ (Nat.cast_nonneg r)
  calc
    _ = |(∑ n ∈ range r, f (start+(k*P+n))) - (r : ℝ)*μ| := by
      rw [hL, sum_range_add (fun n => f (start+n)), hblock, Nat.cast_add]
      apply congrArg abs
      ring
    _ ≤ |∑ n ∈ range r, f (start+(k*P+n))| + |(r : ℝ)*μ| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (∑ n ∈ range r, f (start+(k*P+n))) (-((r : ℝ)*μ))
    _ ≤ (r : ℝ) + r := add_le_add hsum hrμ
    _ ≤ _ := by
      have h : (r : ℝ) ≤ (P : ℝ) := by exact_mod_cast hr.le
      linarith only [h]

private theorem sum_Icc_as_range (L U : ℕ) (f : ℕ → ℝ) :
    (∑ u ∈ Icc L U, f u) = ∑ i ∈ range (Icc L U).card, f (L+i) := by
  symm
  apply sum_bij (s := range (Icc L U).card) (t := Icc L U) (fun i _ => L+i)
  · intro i hi
    rw [mem_range, Nat.card_Icc] at hi
    exact mem_Icc.mpr (by omega)
  · intro i _ j _ h
    omega
  · intro u hu
    rw [mem_Icc] at hu
    refine ⟨u-L, ?_, by omega⟩
    rw [mem_range, Nat.card_Icc]
    omega
  · intro i _
    rfl

end GoldbachReflectedShiftCRTCore


namespace GoldbachReflectedEmpirical

open Finset

/-- Compare a residue statistic on an integer interval with its uniform CRT mean. -/
theorem empirical_error (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    [∀ p : S, NeZero (p : ℕ)] (f : (∀ p : S, ZMod (p : ℕ)) → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (L U : ℕ) (hLU : L ≤ U) :
    |(∑ u ∈ Icc L U, f (fun p => (u : ZMod (p : ℕ)))) / ((Icc L U).card : ℝ) -
      (∑ x, f x) / (Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ)| ≤
      2 * ((∏ p ∈ S,p : ℕ) : ℝ) / ((Icc L U).card : ℝ) := by
  let M := ∏ p : S, (p : ℕ)
  have hM : 0 < M := prod_pos (fun p _ => (hS p p.property).pos)
  let : NeZero M := ⟨hM.ne'⟩
  have hcoprime : Pairwise (fun p q : S => (p : ℕ).Coprime (q : ℕ)) := by
    intro p q hne
    apply (Nat.coprime_primes (hS p p.property) (hS q q.property)).mpr
    exact fun he => hne (Subtype.ext he)
  let e := ZMod.prodEquivPi (fun p : S => (p : ℕ)) hcoprime
  let μ := (∑ x, f x) / (Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ)
  let g (u : ℕ) := f (fun p => (u : ZMod (p : ℕ)))
  have hcard : Fintype.card (∀ p : S, ZMod (p : ℕ)) = M := by
    have hc := Fintype.card_congr e.toEquiv
    rw [ZMod.card] at hc
    exact hc.symm
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hμ : |μ| ≤ 1 := by
    dsimp only [μ]
    rw [hcard, abs_div, abs_of_pos hMR]
    apply (div_le_iff₀ hMR).mpr
    rw [one_mul]
    calc
      _ ≤ ∑ x, |f x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : (∀ p : S, ZMod (p : ℕ)), (1 : ℝ) := Finset.sum_le_sum (fun x _ => hf x)
      _ = _ := by simpa using congrArg (fun k : ℕ => (k : ℝ)) hcard
  have hcomp (n : ℕ) (p : S) : e (n : ZMod M) p = (n : ZMod (p : ℕ)) := by
    dsimp only [e]
    rw [ZMod.prodEquivPi_apply, map_natCast]
  have hperiod (s : ℕ) : (∑ n ∈ range M, g (s+n)) = (M : ℝ)*μ := by
    calc
      _ = ∑ n ∈ range M, f (e ((n : ZMod M)+(s : ZMod M))) := by
        apply Finset.sum_congr rfl
        intro n _
        rw [← Nat.cast_add, add_comm n s]
        exact congrArg f (funext fun p => (hcomp (s+n) p).symm)
      _ = ∑ n : ZMod M, f (e (n+(s : ZMod M))) :=
        GoldbachReflectedShiftCRTCore.sum_natCast_range_eq_zmod (L := M)
          (fun n : ZMod M => f (e (n+(s : ZMod M))))
      _ = ∑ n : ZMod M, f (e n) :=
        Equiv.sum_comp (Equiv.addRight (s : ZMod M)) (fun n => f (e n))
      _ = ∑ x, f x := Equiv.sum_comp e.toEquiv f
      _ = (M : ℝ)*μ := by
        dsimp only [μ]
        rw [hcard]
        field_simp [hMR.ne']
  have hb := GoldbachReflectedShiftCRTCore.bounded_interval_error g μ M hM
    (fun _ => hf _) hμ hperiod L (Icc L U).card
  rw [← GoldbachReflectedShiftCRTCore.sum_Icc_as_range] at hb
  have hU : 0 < ((Icc L U).card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr ⟨L, Finset.mem_Icc.mpr ⟨le_rfl,hLU⟩⟩)
  have hprod : M = ∏ p ∈ S,p := Finset.prod_coe_sort S id
  change |(∑ n ∈ Icc L U, g n)/((Icc L U).card : ℝ)-μ| ≤ _
  rw [← hprod]
  have hrewrite : μ * ((Icc L U).card : ℝ) / ((Icc L U).card : ℝ) = μ :=
    mul_div_cancel_right₀ _ hU.ne'
  conv_lhs => rw [← hrewrite]
  rw [← sub_div, abs_div, abs_of_pos hU]
  apply div_le_div_of_nonneg_right _ hU.le
  simpa only [mul_comm μ] using hb

end GoldbachReflectedEmpirical


namespace GoldbachReflectedContinuous

open Finset Filter GoldbachReflectedBand GoldbachReflectedTransfer
open GoldbachReflectedShiftMain GoldbachReflectedShiftTransfer GoldbachReflectedShiftBand
open GoldbachReflectedShiftEuler GoldbachReflectedShiftCRT
open scoped Topology

noncomputable section

theorem twinConstant_pos : 0 < twinConstant := by
  have hfac (p : ℕ) : 0 < GoldbachReflectedEuler.factor p := by
    unfold GoldbachReflectedEuler.factor
    split_ifs with h
    · have hp : (2 : ℝ) < p := by exact_mod_cast h.2
      have hsq : 1 < ((p:ℝ)-1)^2 := by nlinarith only [hp, sq_nonneg ((p:ℝ)-2)]
      have hb := (div_lt_one (show (0:ℝ) < ((p:ℝ)-1)^2 by positivity)).mpr hsq
      linarith only [hb]
    · norm_num
  have ht := GoldbachReflectedEuler.one_sub_tail_le 4 (by decide)
  unfold twinConstant
  rw [GoldbachReflectedEuler.tprod_factor_eq_prefix_mul_tail 4]
  exact mul_pos (Finset.prod_pos (fun p _ => hfac p)) (by norm_num at ht; linarith only [ht])

def residueModel (S : Finset ℕ) (x : ∀ p : S, ZMod (p : ℕ)) : ℝ :=
  (2*twinConstant) * ∏ p : S, (1 + if x p = 0 then 1/(((p:ℕ):ℝ)-2) else 0)

private theorem model_eq_residue (y u : ℕ) (hu : u ≠ 0) :
    model y (2*u) =
      residueModel (primesUpTo y) (fun p => (u : ZMod (p : ℕ))) := by
  classical
  let S := primesUpTo y
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ 2 < p :=
    ⟨(mem_primesUpTo.mp hp).1, (mem_primesUpTo.mp hp).2.1⟩
  have hset : ((2*u).primeFactors.filter (fun p => 2 < p ∧ p ≤ y)) =
      (2*u).primeFactors.filter (fun p => p ∈ S) := by
    apply Finset.filter_congr
    intro p hp
    simp only [S, mem_primesUpTo, Nat.prime_of_mem_primeFactors hp, true_and]
  have hscore : model y (2*u) = (2*twinConstant)*finiteScore S u := by
    unfold model
    rw [finiteScore_eq_primeFactors S hS u hu, hset]
    rfl
  rw [hscore, residueModel]
  congr 1
  rw [finiteScore, ← Finset.prod_coe_sort S]
  apply Finset.prod_congr rfl
  intro p hp
  simp only [ZMod.natCast_eq_zero_iff, boost]

private theorem cast_filter_card {ι : Type*} (s : Finset ι) (f : ι → Prop) [DecidablePred f] :
    ((s.filter f).card : ℝ) = ∑ x ∈ s, if f x then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp

theorem model_window_on_band (y : ℕ) (width α η : ℝ) (hη : 0 < η)
    [∀ p : primesUpTo y, NeZero (p : ℕ)]
    (hFinite : ∀ z : ℝ,
      (((univ : Finset (∀ p : primesUpTo y, ZMod (p : ℕ))).filter
        (fun x => |residueModel (primesUpTo y) x-z| ≤ width)).card : ℝ) ≤
      α * (Fintype.card (∀ p : primesUpTo y, ZMod (p : ℕ)) : ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ z : ℝ,
      (((band N).filter (fun m => |model y m-z| ≤ width)).card : ℝ) ≤
        (α+η)*((band N).card : ℝ) := by
  classical
  let S := primesUpTo y
  have hPrime (p : ℕ) (hp : p ∈ S) : p.Prime := (mem_primesUpTo.mp hp).1
  let M : ℕ := ∏ p ∈ S,p
  have hC : 0 ≤ 2*(M:ℝ) := by positivity
  filter_upwards [eventually_ge_atTop (384 : ℕ),
    eventually_log_power_over_shifted_card_le 0 hC hη] with N hN hError
  intro z
  let F := halfBand N
  let f (x : ∀ p : S, ZMod (p : ℕ)) : ℝ := if |residueModel S x-z| ≤ width then 1 else 0
  have hf (x : ∀ p : S, ZMod (p : ℕ)) : |f x| ≤ 1 := by
    dsimp [f]
    split_ifs <;> norm_num
  have hNpos : 0 < N := by omega
  have hL := lower_le_upper N (by omega)
  have hcardNat : N ≤ 24*F.card := halfBand_card_ge N (by omega)
  have hCard : 0 < (F.card : ℝ) := by exact_mod_cast (show 0 < F.card by omega)
  have hCount :
      (((band N).filter (fun m => |model y m-z| ≤ width)).card : ℝ) =
        ∑ u ∈ F, f (fun p => (u : ZMod (p : ℕ))) := by
    rw [cast_filter_card, sum_band]
    apply Finset.sum_congr rfl
    intro u hu
    have hu0 : u ≠ 0 := by
      have huL := (Finset.mem_Icc.mp hu).1
      dsimp only [lower] at huL
      omega
    rw [model_eq_residue y u hu0]
  have hSamp : 0 < (Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (show Nonempty (∀ p : S, ZMod (p : ℕ)) from ⟨fun _ => 0⟩)
  have hMu : (∑ x, f x) / (Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) ≤ α := by
    apply (div_le_iff₀ hSamp).mpr
    have h' := hFinite z
    rw [cast_filter_card] at h'
    exact h'
  have hex := (abs_le.mp
    (GoldbachReflectedEmpirical.empirical_error S hPrime f hf (lower N) (upper N) hL)).2
  change (∑ u ∈ F, f (fun p => (u : ZMod (p : ℕ)))) / (F.card : ℝ) -
    (∑ x, f x) / (Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) ≤ 2*(M:ℝ)/(F.card:ℝ) at hex
  have hErr : 2*(M:ℝ)/(F.card:ℝ) ≤ η := by
    simpa only [pow_zero, mul_one, shiftedHalfBand, Nat.sub_zero, F, halfBand]
      using hError 0 (by simp)
  rw [hCount, band_card]
  apply (div_le_iff₀ hCard).mp
  linarith only [hex, hMu, hErr]

theorem transfer_window {ι : Type*} (F : Finset ι) (hF : 0 < F.card)
    (f g : ι → ℝ) (δ η κ z : ℝ) (hδ : 0 < δ)
    (hMean : avg F (fun m => (f m-g m)^2) ≤ η*δ^2)
    (hModel : (((F.filter (fun m => |g m-z| ≤ 2*δ)).card : ℝ)) ≤ κ*(F.card:ℝ)) :
    (((F.filter (fun m => |f m-z| ≤ δ)).card : ℝ)) ≤ (η+κ)*(F.card:ℝ) := by
  classical
  let Bad := F.filter (fun m => δ < |f m-g m|)
  let Model := F.filter (fun m => |g m-z| ≤ 2*δ)
  have hBadSub : Bad ⊆ F := Finset.filter_subset _ _
  have hBad : (Bad.card : ℝ) ≤ η*(F.card:ℝ) := by
    have hCard : 0 < (F.card : ℝ) := by exact_mod_cast hF
    have hsq : 0 < δ^2 := pow_pos hδ 2
    apply le_of_mul_le_mul_left _ hsq
    calc
      δ^2 * (Bad.card : ℝ) = ∑ _m ∈ Bad, δ^2 := by simp [nsmul_eq_mul, mul_comm]
      _ ≤ ∑ m ∈ Bad, (f m-g m)^2 := by
        apply Finset.sum_le_sum
        intro m hm
        have hlt := (Finset.mem_filter.mp hm).2.le
        simpa only [sq_abs] using pow_le_pow_left₀ hδ.le hlt 2
      _ ≤ ∑ m ∈ F, (f m-g m)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hBadSub (fun _ _ _ => sq_nonneg _)
      _ ≤ (η*δ^2)*(F.card:ℝ) := (div_le_iff₀ hCard).mp hMean
      _ = _ := by ring
  have hSub : F.filter (fun m => |f m-z| ≤ δ) ⊆ Bad ∪ Model := by
    intro m hm
    obtain ⟨hmem, hclose⟩ := Finset.mem_filter.mp hm
    by_cases h : δ < |f m-g m|
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem,h⟩)
    · apply Finset.mem_union_right _
      apply Finset.mem_filter.mpr
      refine ⟨hmem, ?_⟩
      have hh := abs_sub_le (g m) (f m) z
      rw [abs_sub_comm (g m) (f m)] at hh
      linarith only [hh, hclose, le_of_not_gt h]
  have hcardLead : (((F.filter (fun m => |f m-z| ≤ δ)).card : ℝ)) ≤
      (Bad.card : ℝ) + (Model.card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hSub).trans (Finset.card_union_le Bad Model)
  calc
    _ ≤ _ := hcardLead
    _ ≤ η*(F.card:ℝ)+κ*(F.card:ℝ) := add_le_add hBad hModel
    _ = _ := by ring

end
end GoldbachReflectedContinuous


namespace GoldbachReflectedSperner

open Finset
open scoped BigOperators Classical

private theorem card_antichain_le_choose {ι : Type*} [DecidableEq ι]
    (A : Finset ι) (F : Finset (Finset ι)) (hF : ∀ s ∈ F, s ⊆ A)
    (hanti : IsAntichain (· ⊆ ·) (F : Set (Finset ι))) :
    F.card ≤ A.card.choose (A.card / 2) := by
  let restrict (s : Finset ι) := s.subtype (fun i => i ∈ A)
  let e : A ↪ ι := Function.Embedding.subtype fun i => i ∈ A
  let G := F.image restrict
  have hre (s : Finset ι) (hs : s ∈ F) : (restrict s).map e = s :=
    subtype_map_of_mem (hF s hs)
  have hc : G.card = F.card := by
    apply card_image_of_injOn
    intro s hs t ht he
    rw [← hre s hs, ← hre t ht, he]
  have hg : IsAntichain (· ⊆ ·) (G : Set (Finset A)) := by
    intro s' hs' t' ht' hne hsub
    obtain ⟨s, hs, rfl⟩ := mem_image.mp (mem_coe.mp hs')
    obtain ⟨t, ht, rfl⟩ := mem_image.mp (mem_coe.mp ht')
    apply hanti (mem_coe.mpr hs) (mem_coe.mpr ht) (fun he => hne (congrArg restrict he))
    rw [← hre s hs, ← hre t ht]
    exact map_subset_map.mpr hsub
  have hh := hg.sperner
  simpa only [hc, Fintype.card_coe] using hh

private theorem product_increment {ι : Type*} [DecidableEq ι]
    {A s t : Finset ι} (a : ι → ℝ) (d : ℝ) (hd : 0 < d)
    (ha : ∀ i ∈ A, d ≤ a i) (ht : t ⊆ A) (hst : s ⊆ t) (hne : s ≠ t) :
    (∏ i ∈ s, (1 + a i)) + d ≤ ∏ i ∈ t, (1 + a i) := by
  have hv (i : ι) (hi : i ∈ t) : 1 ≤ 1+a i := by linarith only [hd, ha i (ht hi)]
  obtain ⟨j, hjt, hjs⟩ := Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hst, hne⟩)
  have hone : 1 ≤ ∏ i ∈ s, (1 + a i) := one_le_prod₀ fun i hi => hv i (hst hi)
  have hja : 0 ≤ a j := hd.le.trans (ha j (ht hjt))
  have hj : d ≤ a j * ∏ i ∈ s, (1+a i) :=
    (ha j (ht hjt)).trans (le_mul_of_one_le_right hja hone)
  calc
    _ ≤ (∏ i ∈ s, (1+a i)) + (a j * ∏ i ∈ s, (1+a i)) := add_le_add_right hj _
    _ = ∏ i ∈ insert j s, (1+a i) := by rw [prod_insert hjs]; ring
    _ ≤ _ := prod_le_prod_of_subset_of_one_le₀ (insert_subset hjt hst)
      (fun i hi => zero_le_one.trans (hv i (insert_subset hjt hst hi))) (fun i hi _ => hv i hi)

/-- Positive product increments make any sufficiently narrow score window an
antichain in the active-coordinate cube. -/
theorem small_ball_card_le_choose {ι : Type*} [DecidableEq ι] (A : Finset ι)
    (a : ι → ℝ) (c d z δ : ℝ) (hc : 0 < c) (hd : 0 < d)
    (ha : ∀ i ∈ A, d ≤ a i) (hδ : 2*δ < c*d) :
    (A.powerset.filter (fun s => |c * (∏ i ∈ s, (1+a i)) - z| ≤ δ)).card ≤
      A.card.choose (A.card / 2) := by
  let F := A.powerset.filter (fun s => |c * (∏ i ∈ s, (1+a i)) - z| ≤ δ)
  have hF (s : Finset ι) (hs : s ∈ F) : s ⊆ A := mem_powerset.mp (mem_filter.mp hs).1
  apply card_antichain_le_choose A F hF
  intro s hs t ht hne hst
  have hs' := abs_le.mp (mem_filter.mp (mem_coe.mp hs)).2
  have ht' := abs_le.mp (mem_filter.mp (mem_coe.mp ht)).2
  have hinc := mul_le_mul_of_nonneg_left (product_increment a d hd ha (hF t ht) hst hne) hc.le
  rw [mul_add] at hinc
  linarith only [hs'.1, ht'.2, hinc, hδ]

private noncomputable def central (n : ℕ) : ℝ := (n.centralBinom : ℝ) / (4:ℝ)^n

private theorem central_nonneg (n : ℕ) : 0 ≤ central n := by unfold central; positivity

private theorem central_succ (n : ℕ) :
    central (n+1) = central n * ((2*(n:ℝ)+1)/(2*(n:ℝ)+2)) := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have he : ((n:ℝ)+1) * ((n+1).centralBinom : ℝ) =
      2 * (2*(n:ℝ)+1) * (n.centralBinom : ℝ) := by exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have hce : ((n+1).centralBinom : ℝ) =
      (2 * (2*(n:ℝ)+1) * (n.centralBinom : ℝ)) / ((n:ℝ)+1) :=
    (eq_div_iff hn).mpr (by rw [mul_comm]; exact he)
  simp only [central, hce, pow_succ (4:ℝ) n]
  have hn' : 2*(n:ℝ)+2 ≠ 0 := by positivity
  field_simp [hn, hn']
  ring

private theorem central_sq_le (n : ℕ) :
    (central n)^2 ≤ 1/((n:ℝ)+1) := by
  induction n with
  | zero => norm_num [central, Nat.centralBinom]
  | succ n ih =>
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hr : ((2*(n:ℝ)+1)/(2*(n:ℝ)+2))^2 ≤ ((n:ℝ)+1)/((n:ℝ)+2) := by
      rw [div_pow]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith only [hn0]
    calc
      (central (n+1))^2 = (central n)^2 * ((2*(n:ℝ)+1)/(2*(n:ℝ)+2))^2 := by
        rw [central_succ, mul_pow]
      _ ≤ (1/((n:ℝ)+1)) * (((n:ℝ)+1)/((n:ℝ)+2)) :=
        mul_le_mul ih hr (sq_nonneg _) (by positivity)
      _ = _ := by
        push_cast
        have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
        have hn2 : (n:ℝ)+1+1 ≠ 0 := by positivity
        have hn3 : (n:ℝ)+2 ≠ 0 := by positivity
        field_simp [hn1, hn2, hn3]
        ring

private theorem choose_ratio_le_central (n : ℕ) :
    (n.choose (n/2) : ℝ) / (2:ℝ)^n ≤ central (n/2) := by
  let k := n/2
  have hk : n = 2*k ∨ n = 2*k+1 := by dsimp [k]; omega
  change (n.choose k : ℝ) / (2:ℝ)^n ≤ central k
  rcases hk with hk | hk
  · rw [hk, central, Nat.centralBinom_eq_two_mul_choose, pow_mul]
    norm_num
  · have he := Nat.choose_mul_succ_eq (2*k) k
    have he' : (2*k+1-k : ℕ) = k+1 := by omega
    rw [he'] at he
    have hb : ((2*k+1).choose k : ℝ) * ((k:ℝ)+1) =
        (k.centralBinom : ℝ) * (2*(k:ℝ)+1) := by
      rw [Nat.centralBinom_eq_two_mul_choose]
      exact_mod_cast he.symm
    have hscale : ((2*k+1).choose k : ℝ) ≤ 2*(k.centralBinom : ℝ) := by
      apply le_of_mul_le_mul_right _ (show 0 < (k:ℝ)+1 by positivity)
      rw [hb]
      have hk' : 2*(k:ℝ)+1 ≤ 2*((k:ℝ)+1) := by linarith
      calc
        _ ≤ (k.centralBinom : ℝ) * (2*((k:ℝ)+1)) :=
          mul_le_mul_of_nonneg_left hk' (Nat.cast_nonneg _)
        _ = _ := by ring
    rw [hk, central, pow_succ, pow_mul]
    norm_num
    have hk4 : 0 < (4:ℝ)^k := by positivity
    apply (div_le_div_iff₀ (by positivity) hk4).mpr
    calc
      _ ≤ (2*(k.centralBinom : ℝ)) * (4:ℝ)^k := mul_le_mul_of_nonneg_right hscale hk4.le
      _ = _ := by ring

/-- The maximal Boolean layer has fraction tending to zero, with one threshold
that applies to every larger active set. -/
theorem eventually_choose_ratio_le (η : ℝ) (hη : 0 < η) :
    ∃ M : ℕ, ∀ n ≥ M, (n.choose (n/2) : ℝ) ≤ η * (2:ℝ)^n := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / η^2)
  refine ⟨2*k, fun n hn => ?_⟩
  have hkn : k ≤ n/2 := by omega
  have hknR : (k : ℝ) ≤ ((n/2 : ℕ) : ℝ) := by exact_mod_cast hkn
  have hsmall : 1/(((n/2 : ℕ) : ℝ)+1) ≤ η^2 := by
    have hh : 1/η^2 ≤ ((n/2 : ℕ) : ℝ)+1 := by linarith only [hk, hknR]
    have hpos : 0 < η^2 := by positivity
    have hpos' : 0 < (((n/2 : ℕ) : ℝ)+1) := by positivity
    have hh' := (div_le_iff₀ hpos).mp hh
    exact (div_le_iff₀ hpos').mpr (by rw [mul_comm]; exact hh')
  have hcentral : central (n/2) ≤ η := by
    exact le_of_pow_le_pow_left₀ (by decide) hη.le ((central_sq_le (n/2)).trans hsmall)
  exact (div_le_iff₀ (by positivity)).mp ((choose_ratio_le_central n).trans hcentral)

theorem small_ball_card_le {ι : Type*} [DecidableEq ι] (A : Finset ι)
    (a : ι → ℝ) (c d z δ η : ℝ) (hc : 0 < c) (hd : 0 < d)
    (ha : ∀ i ∈ A, d ≤ a i) (hδ : 2*δ < c*d)
    (hη : (A.card.choose (A.card/2) : ℝ) ≤ η * (2:ℝ)^A.card) :
    ((A.powerset.filter (fun s => |c * (∏ i ∈ s, (1+a i)) - z| ≤ δ)).card : ℝ) ≤
      η * (A.powerset.card : ℝ) := by
  have hchoose := small_ball_card_le_choose A a c d z δ hc hd ha hδ
  have hcast : ((A.powerset.filter (fun s => |c * (∏ i ∈ s, (1+a i)) - z| ≤ δ)).card : ℝ) ≤
    (A.card.choose (A.card/2) : ℝ) := by exact_mod_cast hchoose
  simpa only [card_powerset, Nat.cast_pow, Nat.cast_ofNat] using hcast.trans hη

end GoldbachReflectedSperner


namespace GoldbachReflectedCells

open Finset
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]
variable {R : ι → Type*} [∀ i, Zero (R i)] [∀ i, One (R i)] [∀ i, DecidableEq (R i)]

def active (E : Finset ι) (x : ∀ i, R i) : Finset ι :=
  E.filter fun i => x i = 0 ∨ x i = 1

omit [DecidableEq ι] in
theorem mem_active {E : Finset ι} {x : ∀ i, R i} {i : ι} :
    i ∈ active E x ↔ i ∈ E ∧ (x i = 0 ∨ x i = 1) :=
  mem_filter

def tag (E : Finset ι) (x : ∀ i, R i) : ∀ i, R i :=
  fun i => if i ∈ active E x then 0 else x i

private theorem tag_zero_iff {E : Finset ι} {x : ∀ i, R i} {i : ι} (hi : i ∈ E) :
    tag E x i = 0 ↔ i ∈ active E x := by
  constructor
  · intro ht
    by_contra hn
    have hz : x i = 0 := by simpa [tag, hn] using ht
    exact hn (mem_active.mpr ⟨hi, Or.inl hz⟩)
  · intro ha
    simp [tag, ha]

theorem active_eq_of_tag_eq {E : Finset ι} {x y : ∀ i, R i} (hy : tag E y = tag E x) :
    active E y = active E x := by
  ext i
  by_cases hi : i ∈ E
  · rw [← tag_zero_iff hi, ← tag_zero_iff hi, hy]
  · simp [active, hi]

theorem eq_off_active {E : Finset ι} {x y : ∀ i, R i} (hy : tag E y = tag E x)
    {i : ι} (hi : i ∉ active E x) : y i = x i := by
  simpa [tag, active_eq_of_tag_eq hy, hi] using congrFun hy i

private def zeroes (E : Finset ι) (x y : ∀ i, R i) : Finset ι :=
  (active E x).filter fun i => y i = 0

private def restore (E : Finset ι) (x : ∀ i, R i) (t : Finset ι) : ∀ i, R i :=
  fun i => if i ∈ active E x then (if i ∈ t then 0 else 1) else x i

private theorem restore_active (E : Finset ι) (x : ∀ i, R i) (t : Finset ι) :
    active E (restore E x t) = active E x := by
  ext i
  by_cases hi : i ∈ active E x
  · have he := (mem_active.mp hi).1
    by_cases ht : i ∈ t <;> simp [mem_active, restore, hi, he, ht]
  · have hrestore : restore E x t i = x i := by simp [restore, hi]
    simp only [mem_active, hrestore]

private theorem restore_tag (E : Finset ι) (x : ∀ i, R i) (t : Finset ι) :
    tag E (restore E x t) = tag E x := by
  funext i
  simp only [tag, restore_active, restore]
  split_ifs <;> rfl

/-- The residues with the same tag are parametrized by their sets of
active coordinates assigned zero. -/
def cellEquiv (E : Finset ι) (x : ∀ i, R i) (h01 : ∀ i, (0 : R i) ≠ 1) :
    {y : (i : ι) → R i // tag E y = tag E x} ≃ ↥((active E x).powerset) where
  toFun y := ⟨zeroes E x y, mem_powerset.mpr (filter_subset _ _)⟩
  invFun t := ⟨restore E x t, restore_tag E x t⟩
  left_inv y := by
    apply Subtype.ext
    funext i
    change restore E x (zeroes E x y) i = y.val i
    by_cases hi : i ∈ active E x
    · have hact : i ∈ active E y.val := by simpa only [active_eq_of_tag_eq y.property] using hi
      rcases (mem_active.mp hact).2 with h0 | h1
      · simp [restore, hi, zeroes, h0]
      · simp [restore, hi, zeroes, h1, Ne.symm (h01 i)]
    · simp only [restore, hi, ite_false]
      exact (eq_off_active y.property hi).symm
  right_inv t := by
    apply Subtype.ext
    ext i
    change i ∈ (active E x).filter (fun j => restore E x t.val j = 0) ↔ i ∈ t.val
    rw [mem_filter]
    have ht := mem_powerset.mp t.property
    by_cases hi : i ∈ active E x
    · simp only [restore, hi, ite_true, true_and]
      by_cases ht' : i ∈ t.val <;> simp [ht', Ne.symm (h01 i)]
    · have ht' : i ∉ t.val := fun h => hi (ht h)
      simp [hi, ht']

theorem mem_cellEquiv {E : Finset ι} {x : ∀ i, R i} (h01 : ∀ i, (0 : R i) ≠ 1)
    (y : {y : (i : ι) → R i // tag E y = tag E x}) {i : ι} :
    i ∈ (cellEquiv E x h01 y).val ↔ i ∈ active E x ∧ y.val i = 0 :=
  mem_filter

theorem card_tag_fibre (E : Finset ι) (x : ∀ i, R i) (h01 : ∀ i, (0 : R i) ≠ 1) :
    Nat.card {y : (i : ι) → R i // tag E y = tag E x} = 2 ^ (active E x).card := by
  rw [Nat.card_congr (cellEquiv E x h01), Nat.card_eq_fintype_card, Fintype.card_coe, card_powerset]

section Finite

variable [Fintype ι]

theorem prod_cell_eq {M : Type*} [CommMonoid M]
    (E : Finset ι) (x : ∀ i, R i) (h01 : ∀ i, (0 : R i) ≠ 1)
    (y : {y : (i : ι) → R i // tag E y = tag E x}) (f : ∀ i, R i → M)
    (hf : ∀ i ∈ active E x, f i 1 = 1) :
    (∏ i, f i (y.val i)) =
      (∏ i ∈ univ \ active E x, f i (x i)) *
        ∏ i ∈ (cellEquiv E x h01 y).val, f i 0 := by
  rw [← prod_sdiff (subset_univ (active E x)) (f := fun i => f i (y.val i))]
  congr 1
  · apply prod_congr rfl
    intro i hi
    rw [eq_off_active y.property (mem_sdiff.mp hi).2]
  · symm
    apply prod_subset_one_on_sdiff (mem_powerset.mp (cellEquiv E x h01 y).property)
    · intro i hi
      obtain ⟨ha, hn⟩ := mem_sdiff.mp hi
      have hn₀ : y.val i ≠ 0 := fun h0 => hn ((mem_cellEquiv h01 y).mpr ⟨ha, h0⟩)
      have ha' : i ∈ active E y.val := by simpa only [active_eq_of_tag_eq y.property] using ha
      rw [((mem_active.mp ha').2).resolve_left hn₀, hf i ha]
    · intro i hi
      rw [(mem_cellEquiv h01 y).mp hi |>.2]

theorem prod_zero_indicator_eq {M : Type*} [CommMonoid M]
    (E : Finset ι) (x : ∀ i, R i) (h01 : ∀ i, (0 : R i) ≠ 1)
    (y : {y : (i : ι) → R i // tag E y = tag E x}) (a : ι → M) :
    (∏ i, if y.val i = 0 then a i else 1) =
      (∏ i ∈ univ \ active E x, if x i = 0 then a i else 1) *
        ∏ i ∈ (cellEquiv E x h01 y).val, a i := by
  simpa only [ite_true] using
    prod_cell_eq E x h01 y (fun i r => if r = 0 then a i else 1)
      (fun i _ => ite_eq_right (Ne.symm (h01 i)))

variable [∀ i, Fintype (R i)]

noncomputable def cell (E : Finset ι) (x : ∀ i, R i) : Finset ((i : ι) → R i) := by
  classical
  exact univ.filter fun y => tag E y = tag E x

theorem mem_cell {E : Finset ι} {x y : ∀ i, R i} :
    y ∈ cell E x ↔ tag E y = tag E x := by
  classical
  simp only [cell, mem_filter, mem_univ, true_and]

theorem cell_card (E : Finset ι) (x : ∀ i, R i) (h01 : ∀ i, (0 : R i) ≠ 1) :
    (cell E x).card = 2 ^ (active E x).card := by
  let e : ↥(cell E x) ≃ {y : (i : ι) → R i // tag E y = tag E x} :=
    Equiv.subtypeEquivRight (fun _ => mem_cell)
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, Nat.card_congr e]
  exact card_tag_fibre E x h01

theorem cell_filter_card_eq (E : Finset ι) (x : ∀ i, R i) (h01 : ∀ i, (0 : R i) ≠ 1)
    (P : ((i : ι) → R i) → Prop) (Q : Finset ι → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ y : {y : (i : ι) → R i // tag E y = tag E x},
      P y.val ↔ Q (cellEquiv E x h01 y).val) :
    ((cell E x).filter P).card = ((active E x).powerset.filter Q).card := by
  let e := cellEquiv E x h01
  let lhs (y : (i : ι) → R i) (hy : y ∈ (cell E x).filter P) :
      {y : (i : ι) → R i // tag E y = tag E x} :=
    ⟨y, mem_cell.mp (mem_filter.mp hy).1⟩
  let rhs (t : Finset ι) (ht : t ∈ (active E x).powerset.filter Q) : ↥((active E x).powerset) :=
    ⟨t, (mem_filter.mp ht).1⟩
  refine card_bij' (fun y hy => (e (lhs y hy)).val)
    (fun t ht => (e.symm (rhs t ht)).val) ?_ ?_ ?_ ?_
  · intro y hy
    exact mem_filter.mpr ⟨(e (lhs y hy)).property, (hPQ (lhs y hy)).mp (mem_filter.mp hy).2⟩
  · intro t ht
    refine mem_filter.mpr ⟨mem_cell.mpr (e.symm (rhs t ht)).property, (hPQ _).mpr ?_⟩
    change Q (e (e.symm (rhs t ht))).val
    rw [Equiv.apply_symm_apply]
    exact (mem_filter.mp ht).2
  · intro y hy
    exact congrArg Subtype.val (e.symm_apply_apply (lhs y hy))
  · intro t ht
    exact congrArg Subtype.val (e.apply_symm_apply (rhs t ht))


/-- A uniform bound on each occupied tag fibre gives the same bound
on its union. -/
theorem card_le_of_cellwise (E : Finset ι) (B : Finset ((i : ι) → R i))
    (η : ℝ) (hη : 0 ≤ η)
    (hcell : ∀ x ∈ B, ((cell E x ∩ B).card : ℝ) ≤ η * ((cell E x).card : ℝ)) :
    (B.card : ℝ) ≤ η * (Fintype.card ((i : ι) → R i) : ℝ) := by
  classical
  let U : Finset ((i : ι) → R i) := univ
  let T := B.image (tag E)
  let Tfull := U.image (tag E)
  have hB := card_eq_sum_card_fiberwise (f := tag E) (s := B) (t := T)
    (fun x hx => mem_image_of_mem (tag E) hx)
  have hU := card_eq_sum_card_fiberwise (f := tag E) (s := U) (t := Tfull)
    (fun x hx => mem_image_of_mem (tag E) hx)
  have hsubset : T ⊆ Tfull := image_subset_image (subset_univ B)
  calc
    (B.card : ℝ) = ∑ v ∈ T, ((B.filter (fun x => tag E x = v)).card : ℝ) := by
      exact_mod_cast hB
    _ ≤ ∑ v ∈ T, η * ((U.filter (fun x => tag E x = v)).card : ℝ) := by
      apply sum_le_sum
      intro v hv
      obtain ⟨x, hx, rfl⟩ := mem_image.mp hv
      have hB' : B.filter (fun y => tag E y = tag E x) = cell E x ∩ B := by
        ext y
        simp only [mem_filter, mem_inter, mem_cell, and_comm]
      have hU' : U.filter (fun y => tag E y = tag E x) = cell E x := by
        ext y
        simp only [U, mem_filter, mem_univ, mem_cell, true_and]
      rw [hB', hU']
      exact hcell x hx
    _ = η * ∑ v ∈ T, ((U.filter (fun x => tag E x = v)).card : ℝ) := (mul_sum _ _ _).symm
    _ ≤ η * ∑ v ∈ Tfull, ((U.filter (fun x => tag E x = v)).card : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hη
      exact sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => Nat.cast_nonneg _)
    _ = _ := by rw [← Nat.cast_sum, ← hU, show U.card = _ from card_univ]

end Finite

end GoldbachReflectedCells


namespace GoldbachReflectedActive

open Finset Filter
open scoped BigOperators Topology

noncomputable section

/-- Early coordinates with residues 0 or 1 are the active ones. -/
def activeSet (E S : Finset ℕ) (x : ∀ p : S, ZMod (p : ℕ)) : Finset S :=
  univ.filter (fun p => (p : ℕ) ∈ E ∧ (x p = 0 ∨ x p = 1))

def activeCount (E S : Finset ℕ) (x : ∀ p : S, ZMod (p : ℕ)) : ℕ :=
  (activeSet E S x).card

private def weight (E : Finset ℕ) (p : ℕ) (x : ZMod p) : ℝ :=
  if p ∈ E ∧ (x = 0 ∨ x = 1) then 1 / 2 else 1

private theorem sum_weight (E : Finset ℕ) (p : ℕ) [NeZero p] (hp : 2 < p) :
    (∑ x : ZMod p, weight E p x) = (p : ℝ) * (if p ∈ E then (1 - 1 / (p : ℝ)) else 1) := by
  by_cases h : p ∈ E
  · let _ : Fact (1 < p) := ⟨by omega⟩
    have hne : (0 : ZMod p) ≠ 1 := zero_ne_one
    have hn : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    rw [ite_eq_left h]
    calc
      _ = ∑ x : ZMod p, ((1 : ℝ) - (if x = 0 then 1 / 2 else 0) - (if x = 1 then 1 / 2 else 0)) := by
        apply sum_congr rfl
        intro x _
        by_cases hx : x = 0
        · subst x
          norm_num [weight, h, hne]
        · by_cases hx' : x = 1 <;> norm_num [weight, h, hx, hx']
      _ = (p : ℝ) - 1 / 2 - 1 / 2 := by simp [sum_sub_distrib, ZMod.card]
      _ = _ := by field_simp [hn]; ring
  · simp [weight, h, ZMod.card]

private theorem prod_weight (E S : Finset ℕ) (x : ∀ p : S, ZMod (p : ℕ)) :
    (∏ p : S, weight E p (x p)) = (1 / 2 : ℝ) ^ activeCount E S x := by
  unfold weight activeCount activeSet
  rw [← prod_filter, prod_const]

private theorem weighted_product_total (E S : Finset ℕ) [∀ p : S, NeZero (p : ℕ)]
    (hES : E ⊆ S) (hS : ∀ p ∈ S, 2 < p) :
    (∑ x : ∀ p : S, ZMod (p : ℕ), ∏ p : S, weight E p (x p)) =
      ((Fintype.card (∀ p : S, ZMod (p : ℕ))) : ℝ) * ∏ q ∈ E, (1 - 1 / (q : ℝ)) := by
  classical
  have hE : (∏ p : S, if (p : ℕ) ∈ E then (1 - 1 / (p : ℝ)) else 1) =
      ∏ p ∈ E, (1 - 1 / (p : ℝ)) := by
    rw [prod_coe_sort S (fun p : ℕ => if p ∈ E then (1 - 1 / (p : ℝ)) else 1), ← prod_filter]
    congr 1
    ext p
    exact ⟨fun hp => (mem_filter.mp hp).2, fun hp => mem_filter.mpr ⟨hES hp, hp⟩⟩
  have hc : (∏ p : S, ((p : ℕ) : ℝ)) = (Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) := by
    rw [Fintype.card_pi, Nat.cast_prod]
    simp only [ZMod.card]
  have hLocal (p : S) := sum_weight E (p : ℕ) (hS p p.property)
  rw [← Fintype.prod_sum]
  simp_rw [hLocal, prod_mul_distrib, hc, hE]

/-- The number of low-activity choices is bounded uniformly in the untested coordinates. -/
theorem low_count_card (E S : Finset ℕ) [∀ p : S, NeZero (p : ℕ)]
    (hES : E ⊆ S) (hS : ∀ p ∈ S, 2 < p) (r : ℕ) :
    ((univ.filter (fun x : ∀ p : S, ZMod (p : ℕ) => activeCount E S x < r)).card : ℝ) ≤
      (2 : ℝ) ^ r * (∏ p ∈ E, (1 - 1 / (p : ℝ))) *
        (Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) := by
  classical
  have h_ind (x : ∀ p : S, ZMod (p : ℕ)) :
      (if activeCount E S x < r then (1 : ℝ) else 0) ≤
        (2 : ℝ) ^ r * ∏ p : S, weight E p (x p) := by
    rw [prod_weight]
    by_cases hx : activeCount E S x < r
    · rw [ite_eq_left hx]
      calc
        1 = (2 : ℝ) ^ r * (1 / 2 : ℝ) ^ r := by rw [← mul_pow]; norm_num
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hx.le) (by positivity)
    · rw [ite_eq_right hx]
      positivity
  calc
    _ = ∑ x : ∀ p : S, ZMod (p : ℕ), (if activeCount E S x < r then (1 : ℝ) else 0) := by
      rw [← sum_filter]
      simp
    _ ≤ ∑ x : ∀ p : S, ZMod (p : ℕ), (2 : ℝ) ^ r * ∏ p : S, weight E p (x p) :=
      sum_le_sum (fun x _ => h_ind x)
    _ = _ := by rw [← mul_sum, weighted_product_total E S hES hS]; ring

/-- The same bound expressed as a fraction of the full residue cube. -/
theorem low_count_fraction (E S : Finset ℕ) [∀ p : S, NeZero (p : ℕ)]
    (hES : E ⊆ S) (hS : ∀ p ∈ S, 2 < p) (r : ℕ) :
    ((univ.filter (fun x : ∀ p : S, ZMod (p : ℕ) => activeCount E S x < r)).card : ℝ) /
      (Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) ≤
        (2 : ℝ) ^ r * ∏ p ∈ E, (1 - 1 / (p : ℝ)) := by
  have h : (0 : ℝ) < (Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) := by exact_mod_cast Fintype.card_pos
  exact (div_le_iff₀ h).mpr (low_count_card E S hES hS r)

def earlyPrimes (y : ℕ) : Finset ℕ := (range (y + 1)).filter (fun p => p.Prime ∧ 2 < p)

theorem mem_earlyPrimes {p y : ℕ} : p ∈ earlyPrimes y ↔ p.Prime ∧ 2 < p ∧ p ≤ y := by
  simp [earlyPrimes, and_comm, and_left_comm]

private def primeRecip (p : ℕ) : ℝ := if p.Prime ∧ 2 < p then 1 / (p : ℝ) else 0

private theorem primeRecip_nonneg (p : ℕ) : 0 ≤ primeRecip p := by
  unfold primeRecip
  split_ifs <;> positivity

private theorem primeRecip_diverges :
    Tendsto (fun n : ℕ => ∑ p ∈ range n, primeRecip p) atTop atTop := by
  refine (not_summable_iff_tendsto_nat_atTop_of_nonneg primeRecip_nonneg).mp ?_
  intro hs
  apply not_summable_one_div_on_primes
  refine hs.congr_cofinite ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with p hp
  by_cases h : p.Prime <;> simp [primeRecip, h, show 2 < p by omega, Set.indicator]

/-- The finite product in the low-activity bound can be made arbitrarily small. -/
theorem exists_small_active_bound (r : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ y : ℕ, 3 ≤ y ∧ (2 : ℝ) ^ r * ∏ p ∈ earlyPrimes y, (1 - 1 / (p : ℝ)) ≤ η := by
  have hpos : 0 < (2 : ℝ) ^ r := by positivity
  let L := Real.log ((2 : ℝ) ^ r / η)
  obtain ⟨u, hu⟩ := eventually_atTop.mp ((tendsto_atTop.mp primeRecip_diverges) L)
  let y := max 3 u
  refine ⟨y, le_max_left _ _, ?_⟩
  have hy : u ≤ y + 1 := (le_max_right _ _).trans (Nat.le_succ _)
  have hSum : L ≤ ∑ p ∈ earlyPrimes y, (1 / (p : ℝ)) := by
    simpa [earlyPrimes, sum_filter, primeRecip] using hu (y + 1) hy
  have hprod : (∏ p ∈ earlyPrimes y, (1 - 1 / (p : ℝ))) ≤
      Real.exp (-(∑ p ∈ earlyPrimes y, (1 / (p : ℝ)))) := by
    rw [← sum_neg_distrib, Real.exp_sum]
    apply prod_le_prod₀
    · intro p hp
      have h : (3 : ℝ) ≤ p := by
        exact_mod_cast (show 3 ≤ p from (mem_earlyPrimes.mp hp).2.1)
      apply sub_nonneg.mpr
      apply (div_le_iff₀ (show 0 < (p : ℝ) by linarith)).mpr
      linarith
    · intro p _
      exact Real.one_sub_le_exp_neg _
  calc
    _ ≤ (2 : ℝ) ^ r * Real.exp (-(∑ p ∈ earlyPrimes y, (1 / (p : ℝ)))) :=
      mul_le_mul_of_nonneg_left hprod hpos.le
    _ ≤ (2 : ℝ) ^ r * Real.exp (-L) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hSum)) hpos.le
    _ = η := by
      dsimp [L]
      rw [Real.exp_neg, Real.exp_log (div_pos hpos hη)]
      field_simp [hη.ne', hpos.ne']

end

end GoldbachReflectedActive


namespace GoldbachReflectedHighActive

open Finset GoldbachReflectedCells
open scoped BigOperators Classical

def earlyCoords (E S : Finset ℕ) : Finset S := univ.filter fun p => (p : ℕ) ∈ E

noncomputable def residueScore (S : Finset ℕ) (c : ℝ) (x : ∀ p : S, ZMod (p : ℕ)) : ℝ :=
  c * ∏ p : S, (1 + if x p = 0 then 1 / (((p : ℕ) : ℝ) - 2) else 0)

theorem residueScore_nat (S : Finset ℕ) (c : ℝ) (u : ℕ) :
    residueScore S c (fun p => (u : ZMod (p : ℕ))) =
      c * ∏ p ∈ S, (1 + if p ∣ u then 1 / ((p : ℝ) - 2) else 0) := by
  simp only [residueScore, ZMod.natCast_eq_zero_iff]
  rw [prod_coe_sort S (fun p : ℕ => 1 + if p ∣ u then 1 / ((p : ℝ) - 2) else 0)]

theorem active_eq (E S : Finset ℕ) (x : ∀ p : S, ZMod (p : ℕ)) :
    active (earlyCoords E S) x = GoldbachReflectedActive.activeSet E S x := by
  ext p
  simp [mem_active, earlyCoords, GoldbachReflectedActive.activeSet]

private theorem boost_pos (p : ℕ) (hp : 2 < p) :
    0 < 1 / ((p : ℝ) - 2) := by
  have hp' : (2 : ℝ) < p := by exact_mod_cast hp
  exact one_div_pos.mpr (sub_pos.mpr hp')

/-- In one tag cell, no sufficiently short score window contains more than
the maximal-layer fraction of its active subsets. -/
theorem cell_small_ball_card (E S : Finset ℕ) [∀ p : S, NeZero (p : ℕ)]
    (hS : ∀ p ∈ S, 2 < p) (z : ℕ) (hz : 0 < z) (hE : ∀ p ∈ E, p ≤ z)
    (c center radius η : ℝ) (hc : 0 < c) (hδ : 2*radius < c/(z:ℝ))
    (x : ∀ p : S, ZMod (p : ℕ))
    (hratio : (((active (earlyCoords E S) x).card).choose
      ((active (earlyCoords E S) x).card / 2) : ℝ) ≤
        η * (2:ℝ)^(active (earlyCoords E S) x).card) :
    (((cell (earlyCoords E S) x).filter
        (fun y => |residueScore S c y-center| ≤ radius)).card : ℝ) ≤
      η * ((cell (earlyCoords E S) x).card : ℝ) := by
  let A := active (earlyCoords E S) x
  let a (p : S) : ℝ := 1 / (((p : ℕ) : ℝ) - 2)
  let f (p : S) (u : ZMod (p : ℕ)) : ℝ := 1 + if u = 0 then a p else 0
  let b := c * ∏ p ∈ univ \ A, f p (x p)
  let d : ℝ := 1/(z:ℝ)
  have hd : 0 < d := by unfold d; positivity
  have ha (p : S) (hp : p ∈ A) : d ≤ a p := by
    have hpE : (p : ℕ) ∈ E := by simpa [earlyCoords] using (mem_active.mp hp).1
    have hpz : ((p : ℕ) : ℝ) ≤ z := by exact_mod_cast hE p hpE
    have hp2 : (2 : ℝ) < (p : ℕ) := by exact_mod_cast hS p p.property
    exact one_div_le_one_div_of_le (sub_pos.mpr hp2) (by linarith only [hpz])
  have h01 (p : S) : (0 : ZMod (p : ℕ)) ≠ 1 := by
    let : Fact (1 < (p : ℕ)) := ⟨Nat.lt_trans (by decide) (hS p p.property)⟩
    exact zero_ne_one
  have hf (p : S) (_ : p ∈ A) : f p 1 = 1 := by
    simp [f, Ne.symm (h01 p)]
  have hprod : 1 ≤ ∏ p ∈ univ \ A, f p (x p) := by
    apply one_le_prod₀
    intro p _
    have hapos : 0 < a p := boost_pos p (hS p p.property)
    unfold f
    split_ifs <;> linarith only [hapos]
  have hb : c ≤ b := le_mul_of_one_le_right hc.le hprod
  have hδ' : 2*radius < b*d := by
    calc
      _ < c/(z:ℝ) := hδ
      _ = c*d := by unfold d; ring
      _ ≤ b*d := mul_le_mul_of_nonneg_right hb hd.le
  have hcard := cell_filter_card_eq (earlyCoords E S) x h01
    (fun y => |residueScore S c y-center| ≤ radius)
    (fun t => |b * (∏ p ∈ t, (1+a p)) - center| ≤ radius) (by
      intro y
      have hprod' := prod_cell_eq (earlyCoords E S) x h01 y f hf
      change |c * (∏ p : S, f p (y.val p))-center| ≤ radius ↔ _
      rw [hprod', ← mul_assoc]
      simp only [f]
      rfl)
  rw [hcard, cell_card (earlyCoords E S) x h01, ← card_powerset A]
  exact GoldbachReflectedSperner.small_ball_card_le A a b d center radius η
    (hc.trans_le hb) hd ha hδ' hratio

/-- Summing over cells preserves the same bound on the high-activity part
of the residue cube, uniformly in the score window center. -/
theorem high_count_card (E S : Finset ℕ) [∀ p : S, NeZero (p : ℕ)]
    (hS : ∀ p ∈ S, 2 < p) (z : ℕ) (hz : 0 < z) (hE : ∀ p ∈ E, p ≤ z)
    (c center radius η : ℝ) (hc : 0 < c) (hδ : 2*radius < c/(z:ℝ)) (hη : 0 ≤ η)
    (r : ℕ) (hr : ∀ n ≥ r, (n.choose (n/2) : ℝ) ≤ η*(2:ℝ)^n) :
    ((univ.filter (fun x : ∀ p : S, ZMod (p : ℕ) =>
        r ≤ GoldbachReflectedActive.activeCount E S x ∧
          |residueScore S c x-center| ≤ radius)).card : ℝ) ≤
      η * (Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) := by
  let B : Finset (∀ p : S, ZMod (p : ℕ)) :=
    univ.filter (fun x => r ≤ GoldbachReflectedActive.activeCount E S x ∧
      |residueScore S c x-center| ≤ radius)
  change (B.card : ℝ) ≤ _
  apply card_le_of_cellwise (earlyCoords E S) B η hη
  intro x hx
  have hx' : r ≤ (active (earlyCoords E S) x).card := by
    rw [active_eq]
    exact (mem_filter.mp hx).2.1
  have hcell := cell_small_ball_card E S hS z hz hE c center radius η hc hδ x (hr _ hx')
  refine le_trans ?_ hcell
  apply Nat.cast_le.mpr
  apply card_le_card
  intro y hy
  obtain ⟨hcell', hyB⟩ := mem_inter.mp hy
  exact mem_filter.mpr ⟨hcell', (mem_filter.mp hyB).2.2⟩

end GoldbachReflectedHighActive

namespace GoldbachReflectedContinuous

open Finset Filter GoldbachReflectedBand GoldbachReflectedTransfer
open GoldbachReflectedShiftMain GoldbachReflectedShiftEuler
open GoldbachReflectedActive GoldbachReflectedHighActive
open scoped Topology

theorem uniform_window (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ z : ℝ,
      (((band N).filter (fun m => |normalized N m-z| ≤ δ)).card : ℝ) ≤
        ε*((band N).card : ℝ) := by
  classical
  let θ : ℝ := ε/4
  have hθ : 0 < θ := by dsimp [θ]; positivity
  obtain ⟨r,hr⟩ := GoldbachReflectedSperner.eventually_choose_ratio_le θ hθ
  obtain ⟨z₀,hz₀,hEarly⟩ := exists_small_active_bound r θ hθ
  have hzNat : 0 < z₀ := by omega
  have hzR : 0 < (z₀:ℝ) := by exact_mod_cast hzNat
  let c := 2*twinConstant
  have hc : 0 < c := mul_pos (by norm_num) twinConstant_pos
  let δ := c/(8*(z₀:ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : 2*(2*δ) < c/(z₀:ℝ) := by
    dsimp only [δ]
    field_simp [hzR.ne']
    linarith only [hc]
  let C : ℝ := 48*Real.exp 2+4
  have hC : 0 < C := by dsimp [C]; positivity
  let loss := θ*δ^2
  have hLoss : 0 < loss := by dsimp [loss]; positivity
  obtain ⟨Y,hY⟩ := exists_nat_ge (C/loss)
  let y := max z₀ Y
  have hzY : z₀ ≤ y := le_max_left _ _
  have hy : 3 ≤ y := hz₀.trans hzY
  have hypos : 0 < (y:ℝ) := by exact_mod_cast (show 0 < y by omega)
  have hy1 : 1 ≤ (y:ℝ) := by exact_mod_cast (show 1 ≤ y by omega)
  have hylarge : C/loss ≤ (y:ℝ) := hY.trans (by exact_mod_cast le_max_right z₀ Y)
  have hySquare : (y:ℝ) ≤ (y:ℝ)^2 := by
    nlinarith only [mul_nonneg hypos.le (sub_nonneg.mpr hy1)]
  have hCoeff : C/(y:ℝ)^2 ≤ loss := by
    apply (div_le_iff₀ (by positivity : 0 < (y:ℝ)^2)).mpr
    have h₁ := (div_le_iff₀ hLoss).mp (hylarge.trans hySquare)
    simpa only [mul_comm] using h₁
  let E := earlyPrimes z₀
  let S := primesUpTo y
  have hES : E ⊆ S := by
    intro p hp
    obtain ⟨hpr, htwo, hpz⟩ := mem_earlyPrimes.mp hp
    exact mem_primesUpTo.mpr ⟨hpr, htwo, hpz.trans hzY⟩
  have hE (p : ℕ) (hp : p ∈ E) : p ≤ z₀ := (mem_earlyPrimes.mp hp).2.2
  have hS (p : ℕ) (hp : p ∈ S) : 2 < p := (mem_primesUpTo.mp hp).2.1
  let : ∀ p : S, NeZero (p : ℕ) := fun p => ⟨(by have := hS p p.property; omega)⟩
  have hFinite (z : ℝ) :
      (((univ : Finset (∀ p : S, ZMod (p : ℕ))).filter
        (fun x => |residueModel S x-z| ≤ 2*δ)).card : ℝ) ≤
      (2*θ)*(Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) := by
    let X := (univ : Finset (∀ p : S, ZMod (p : ℕ))).filter
      (fun x => |residueModel S x-z| ≤ 2*δ)
    let low := (univ : Finset (∀ p : S, ZMod (p : ℕ))).filter
      (fun x => activeCount E S x < r)
    let high := (univ : Finset (∀ p : S, ZMod (p : ℕ))).filter
      (fun x => r ≤ activeCount E S x ∧ |residueModel S x-z| ≤ 2*δ)
    have hSub : X ⊆ low ∪ high := by
      intro x hx
      by_cases h : activeCount E S x < r
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨mem_univ _,h⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨mem_univ _, le_of_not_gt h, (Finset.mem_filter.mp hx).2⟩)
    have hLow : (low.card : ℝ) ≤ θ*(Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) :=
      (low_count_card E S hES hS r).trans (mul_le_mul_of_nonneg_right hEarly (by positivity))
    have hHigh : (high.card : ℝ) ≤ θ*(Fintype.card (∀ p : S, ZMod (p : ℕ)) : ℝ) :=
      high_count_card E S hS z₀ hzNat hE c z (2*δ) θ hc hsmall hθ.le r hr
    have hCard : (X.card : ℝ) ≤ (low.card : ℝ)+(high.card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hSub).trans (Finset.card_union_le low high)
    change (X.card : ℝ) ≤ _
    linarith only [hCard, hLow, hHigh]
  refine ⟨δ,hδ,?_⟩
  have H := model_window_on_band y (2*δ) (2*θ) θ hθ hFinite
  filter_upwards [eventually_ge_atTop (384 : ℕ), H,
    GoldbachReflectedMeanSquare.eventual_meanSquare y hy] with N hN hModel hMean
  intro z
  have hBand : 0 < (band N).card := by
    rw [band_card]
    have h := halfBand_card_ge N (by omega)
    omega
  have hMean' : GoldbachReflectedShiftTransfer.avg (band N) (fun m =>
      (normalized N m-model y m)^2) ≤ θ*δ^2 := hMean.trans hCoeff
  have HH := transfer_window (band N) hBand (normalized N) (model y)
    δ θ (2*θ+θ) z hδ hMean' (hModel z)
  rw [show θ+(2*θ+θ)=ε by dsimp [θ]; ring] at HH
  exact HH

end GoldbachReflectedContinuous

theorem Conjectures.Goldbach.ReflectedContinuousDistribution : (
by
  classical
  let e := fun t : ℝ => Complex.exp (((2*Real.pi*t : ℝ) : ℂ)*Complex.I)
  let S := fun (N : ℕ) (t : ℝ) => ∑ p ∈ (Finset.range (N+1)).filter Nat.Prime, (Real.log (p : ℝ) : ℂ) * e ((p : ℝ)*t)
  let arcs := fun N : ℕ => let k := Nat.log 2 (N+2); {t : ℝ | ∃ q a : ℕ, 1 ≤ q ∧ q ≤ k ∧ a ≤ q ∧ Nat.Coprime a q ∧ |t-(a : ℝ)/(q : ℝ)| ≤ ((k^3 : ℕ) : ℝ)/((q : ℝ)*(N : ℝ))}
  let A := fun N m : ℕ => (intervalIntegral ((arcs N).indicator (fun t : ℝ => (S N t)^2 * e (-(m : ℝ)*t))) (0 : ℝ) 1 MeasureTheory.volume).re
  let C₂ := ∏' p : ℕ, if Nat.Prime p ∧ 2 < p then 1 - 1/((p : ℝ)-1)^2 else 1
  let band := fun N m : ℕ => 4*N ≤ 3*m ∧ 2*m ≤ 3*N ∧ Even m
  let R := fun N m : ℕ => A N m / (2*(N:ℝ)-(m:ℝ))
  let B := fun N : ℕ => (Finset.Icc N (2*N)).filter (band N)
  let avg := fun (F : Finset ℕ) (f : ℕ → ℝ) => (∑ m ∈ F, f m)/(F.card:ℝ)
  exact ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N → ∀ z : ℝ,
    (((B N).filter (fun m => |R N m-z| ≤ δ)).card:ℝ) ≤ ε*((B N).card:ℝ)
) := by

  classical
  dsimp only
  intro ε hε
  obtain ⟨δ,hδ,hEv⟩ := GoldbachReflectedContinuous.uniform_window ε hε
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp hEv
  exact ⟨δ,hδ,T,fun N hN z => hT N hN z⟩
