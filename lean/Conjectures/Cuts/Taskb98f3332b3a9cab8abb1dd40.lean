import Mathlib.Combinatorics.Colex
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.BitIndices
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Bits
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Fixed-transition words for the dyadic mean-real-part lemma
A word is encoded from a fair starting bit and a subset of transition gaps.
The lemmas below count completions of prescribed window data, identify the
dyadic phase, and transfer a lower bound from independent flips to fixed-size samples.
Paper derivation and an exact 16-bit rational certificate:
https://github.com/CGandGameEngineLearner/goldbach-proofs/discussions/4202
-/

open Finset
namespace DyadicWords

/-- Bit positions are numbered from the least significant end.
An element of A marks the gap between positions j and j+1. -/
def bitAt (b : Bool) (A : Finset ℕ) : ℕ → Bool
  | 0 => b
  | j+1 => if j ∈ A then !(bitAt b A j) else bitAt b A j

theorem bit_changes (b : Bool) (A : Finset ℕ) (j : ℕ) :
    bitAt b A (j+1) ≠ bitAt b A j ↔ j ∈ A := by
  by_cases h : j ∈ A <;> cases e : bitAt b A j <;> simp [bitAt,h,e]

def ones (B : ℕ) (b : Bool) (A : Finset ℕ) : Finset ℕ :=
  (range (B+1)).filter fun j => bitAt b A j = true

def encode (B : ℕ) (p : Bool × Finset ℕ) : ℕ :=
  ∑ j ∈ ones B p.1 p.2, 2^j

def sample (B r : ℕ) := (univ : Finset Bool) ×ˢ ((range B).powersetCard r)
def family (B r : ℕ) := (sample B r).image (encode B)

/-- All 1000t+1 digits are part of a word, including leading zeroes. -/
theorem encode_lt (B : ℕ) (p : Bool × Finset ℕ) : encode B p < 2^(B+1) := by
  have geometric (n : ℕ) : (∑ j ∈ range n, 2^j) + 1 = (2:ℕ)^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ,pow_succ]; omega
  have bound : encode B p ≤ ∑ j ∈ range (B+1), 2^j :=
    sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have g := geometric (B+1)
  omega

theorem family_grid (B r : ℕ) : family B r ⊆ range (2^(B+1)) := by
  intro x hx
  obtain ⟨p,_,rfl⟩ := mem_image.mp hx
  exact mem_range.mpr (encode_lt B p)

theorem read_bit (B j : ℕ) (p : Bool × Finset ℕ) (hj : j < B+1) :
    (encode B p).testBit j = bitAt p.1 p.2 j := by
  have h : j ∈ (encode B p).bitIndices.toFinset ↔ bitAt p.1 p.2 j = true := by
    simp [encode,ones,hj]
  simp only [List.mem_toFinset,Nat.mem_bitIndices] at h
  cases e : (encode B p).testBit j <;> cases d : bitAt p.1 p.2 j <;> simp_all

/-- The initial bit and the set of differences can be recovered from the word. -/
theorem encode_injective (B r : ℕ) : Set.InjOn (encode B) (sample B r) := by
  rintro ⟨b,A⟩ hp ⟨d,C⟩ hq eqn
  have psub := (mem_powersetCard.mp (mem_product.mp hp).2).1
  have qsub := (mem_powersetCard.mp (mem_product.mp hq).2).1
  have bits (j : ℕ) (hj : j < B+1) : bitAt b A j = bitAt d C j := by
    calc
      _ = (encode B (b,A)).testBit j := (read_bit _ _ _ hj).symm
      _ = (encode B (d,C)).testBit j := congrArg (fun z : ℕ => z.testBit j) eqn
      _ = _ := read_bit _ _ _ hj
  have same : b = d := bits 0 (by omega)
  have eqAC : A=C := by
    ext j
    by_cases h : j<B
    · rw [←bit_changes b A j,←bit_changes d C j,bits j (by omega),bits (j+1) (by omega)]
    · have ha : j ∉ A := fun e => h (mem_range.mp (psub e))
      have hc : j ∉ C := fun e => h (mem_range.mp (qsub e))
      simp [ha,hc]
  rw [same,eqAC]

theorem family_card (B r : ℕ) : (family B r).card = 2*B.choose r := by
  rw [family,card_image_of_injOn (encode_injective B r)]
  simp [sample]

end DyadicWords

namespace DyadicWordCount

/-- Exact multiplicity of any fixed local transition pattern under fixed total weight. -/
theorem pattern_count {α : Type*} [DecidableEq α] (U W S : Finset α) (r : ℕ)
    (hWU : W ⊆ U) (hSW : S ⊆ W) (hr : S.card ≤ r) :
    ((U.powersetCard r).filter (fun A => A ∩ W = S)).card =
      (U.card-W.card).choose (r-S.card) := by
  have hsu : S ⊆ U \ (W \ S) := fun a ha =>
    mem_sdiff.mpr ⟨hWU (hSW ha), fun e => (mem_sdiff.mp e).2 ha⟩
  have eq : (U.powersetCard r).filter (fun A => A ∩ W = S) =
      ((U \ (W \ S)).powersetCard r).filter (S ⊆ ·) := by
    ext A
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨hu, hc⟩, hi⟩
      refine ⟨⟨fun x hx => mem_sdiff.mpr ⟨hu hx, ?_⟩, hc⟩, ?_⟩
      · intro e
        exact (mem_sdiff.mp e).2 (hi ▸ mem_inter.mpr ⟨hx,(mem_sdiff.mp e).1⟩)
      · intro x hx
        exact (mem_inter.mp (hi.symm ▸ hx)).1
    · rintro ⟨⟨hu,hc⟩,hs⟩
      refine ⟨⟨hu.trans sdiff_subset,hc⟩,?_⟩
      ext x
      constructor
      · intro hx
        obtain ⟨ha,hw⟩ := mem_inter.mp hx
        by_contra e
        exact (mem_sdiff.mp (hu ha)).2 (mem_sdiff.mpr ⟨hw,e⟩)
      · intro hx
        exact mem_inter.mpr ⟨hs hx,hSW hx⟩
  rw [eq, card_filter_powersetCard_subset _ _ _ hsu hr,
      card_sdiff_of_subset (sdiff_subset.trans hWU), card_sdiff_of_subset hSW]
  have := card_le_card hWU
  have := card_le_card hSW
  congr 1
  omega

end DyadicWordCount

namespace DyadicWords

theorem bitAt_complement (b : Bool) (A : Finset ℕ) (h : ℕ) :
    bitAt (!b) A h = !(bitAt b A h) := by
  induction h with
  | zero => rfl
  | succ h ih => by_cases e : h ∈ A <;> simp [bitAt,e,ih]

theorem bitAt_involution (b : Bool) (A : Finset ℕ) (h : ℕ) :
    bitAt (bitAt b A h) A h = b := by
  have flip := bitAt_complement false A h
  cases b <;> cases e : bitAt false A h <;> simp_all

/-- The local initial bit and the pattern of prescribed transitions have
exactly this many completions in the global fixed-transition sample. -/
theorem prescribed_window_count (B r h : ℕ) (v : Bool) (W S : Finset ℕ)
    (hW : W ⊆ range B) (hS : S ⊆ W) (hr : S.card ≤ r) :
    ((sample B r).filter (fun p => bitAt p.1 p.2 h = v ∧ p.2 ∩ W = S)).card =
      (B-W.card).choose (r-S.card) := by
  let C := ((range B).powersetCard r).filter fun A => A ∩ W = S
  let tag (A : Finset ℕ) := (bitAt v A h,A)
  have tags : (sample B r).filter (fun p => bitAt p.1 p.2 h = v ∧ p.2 ∩ W = S) =
      C.image tag := by
    ext ⟨b,A⟩
    constructor
    · rintro hp
      obtain ⟨sampled,first,pattern⟩ := mem_filter.mp hp
      refine mem_image.mpr ⟨A,mem_filter.mpr ⟨(mem_product.mp sampled).2,pattern⟩,?_⟩
      exact Prod.ext (by change bitAt v A h = b; rw [←first]; exact bitAt_involution b A h) rfl
    · intro hp
      obtain ⟨A',ha,he⟩ := mem_image.mp hp
      rw [←he]
      obtain ⟨hc,hp⟩ := mem_filter.mp ha
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _,hc⟩, bitAt_involution v A' h,hp⟩
  rw [tags, card_image_of_injective _ (show Function.Injective tag from
    fun a b e => congrArg Prod.snd e)]
  simpa [C] using DyadicWordCount.pattern_count (range B) W S r hW hS hr

end DyadicWords

namespace DyadicWords

def window (k h : ℕ) := k / 2^h % 2^16

theorem window_bit (k h i : ℕ) (hi : i < 16) :
    (window k h).testBit i = k.testBit (i+h) := by
  unfold window
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp [hi]

/-- The real part of a full truncated grid phase is exactly the cosine
indexed by its 16 extracted bits, even when the shift crosses whole periods. -/
theorem window_phase (k j h : ℕ) :
    (Complex.exp (((2*Real.pi*↑⌊(65536:ℝ)*2^j*((k:ℝ)/2^(j+16+h))⌋/65536 : ℝ):ℂ)
       *Complex.I)).re = Real.cos (2*Real.pi*(window k h:ℝ)/65536) := by
  rw [Complex.exp_ofReal_mul_I_re]
  let a := k/2^h
  have phase : (65536:ℝ)*2^j*((k:ℝ)/2^(j+16+h)) = (k:ℝ)/(↑(2^h:ℕ):ℝ) := by
    push_cast
    rw [pow_add, pow_add]
    norm_num
    field_simp
  have floorphase : ⌊(65536:ℝ)*2^j*((k:ℝ)/2^(j+16+h))⌋ = (a:ℤ) := by
    rw [phase,Int.floor_div_natCast,Int.floor_natCast]
    exact (Int.ofNat_ediv_ofNat ..).symm
  have cut : (window k h:ℝ) + 65536*((a/65536:ℕ):ℝ) = (a:ℝ) := by
    exact_mod_cast (Nat.mod_add_div a 65536)
  rw [floorphase]
  push_cast
  convert Real.cos_add_nat_mul_two_pi (2*Real.pi*(window k h:ℝ)/65536) (a/65536) using 2
  linear_combination Real.pi/32768 * cut.symm

end DyadicWords

namespace DyadicWordPopulation

/-- A fixed pattern with a prescribed number of ones and zeroes can be filled
in as an unordered subset or sampled as an ordered list. -/
theorem count_pattern (B r k c : ℕ) (h : r ≤ B) (hk : k ≤ B)
    (hc : c ≤ r) (hck : c ≤ k) (hz : k-c ≤ B-r) :
    (B-k).choose (r-c) * B.descFactorial k =
      B.choose r * r.descFactorial c * (B-r).descFactorial (k-c) := by
  let z := B-r-(k-c)
  have hz' : B-k-(r-c) = z := by dsimp [z]; omega
  have hf : (B-k).choose (r-c) * (r-c).factorial * z.factorial = (B-k).factorial := by
    simpa [hz'] using Nat.choose_mul_factorial_mul_factorial (show r-c ≤ B-k by omega)
  have hr := Nat.factorial_mul_descFactorial hc
  have hz0 : z.factorial * (B-r).descFactorial (k-c) = (B-r).factorial :=
    Nat.factorial_mul_descFactorial hz
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.factorial_pos (r-c)) (Nat.factorial_pos z))
  calc
    _ = ((B-k).choose (r-c) * (r-c).factorial * z.factorial) * B.descFactorial k := by ring
    _ = B.factorial := by rw [hf, Nat.factorial_mul_descFactorial hk]
    _ = B.choose r * r.factorial * (B-r).factorial :=
      (Nat.choose_mul_factorial_mul_factorial h).symm
    _ = _ := by rw [← hr, ← hz0]; ring

/-- The number of ordered samples containing a collision is at most the sum
over pairs of equal positions, with no assumption on the population size. -/
theorem collision_deficit (B m : ℕ) :
    B^(m+1) ≤ B.descFactorial (m+1) + (m+1).choose 2 * B^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have split : B*B.descFactorial (m+1) ≤ B.descFactorial (m+2) + (m+1)*B^(m+1) := by
      calc
        _ ≤ ((B-(m+1))+(m+1))*B.descFactorial (m+1) :=
          Nat.mul_le_mul_right _ (by omega)
        _ = B.descFactorial (m+2) + (m+1)*B.descFactorial (m+1) := by
          rw [Nat.add_mul, Nat.descFactorial_succ B (m+1)]
        _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow B (m+1))) _
    calc
      B^(m+1+1) = B*B^(m+1) := by rw [pow_succ']
      _ ≤ B*(B.descFactorial (m+1) + (m+1).choose 2 * B^m) := Nat.mul_le_mul_left _ ih
      _ = B*B.descFactorial (m+1) + (m+1).choose 2 * B^(m+1) := by rw [pow_succ]; ring
      _ ≤ B.descFactorial (m+2) + (m+1)*B^(m+1) + (m+1).choose 2*B^(m+1) :=
        Nat.add_le_add_right split _
      _ = _ := by
        have hx : (m+1+1).choose 2 = (m+1) + (m+1).choose 2 := by
          rw [Nat.choose_succ_succ (m+1) 1, Nat.choose_one_right]
        rw [hx]; ring

/-- Uniform upper comparison for the multiplicity of every 15-gap pattern. The
with-replacement weight depends only on its number c of changes. -/
theorem pattern_weight_le (t c : ℕ) (ht : 2000 ≤ t) (hc : c ≤ 15) :
    (1000*t-105) * (1000*t-15).choose (85*t-c) * 200^15 ≤
      1000*t * (1000*t).choose (85*t) * (17^c * 183^(15-c)) := by
  let B := 1000*t
  let r := 85*t
  let v := 5*t
  have hb : 105 ≤ B := by dsimp [B]; omega
  have he := count_pattern B r 15 c (by dsimp [r,B]; omega) (by omega)
    (by dsimp [r]; omega) hc (by dsimp [B,r]; omega)
  have hw : (B-15).choose (r-c) * B.descFactorial 15 ≤
      B.choose r * r^c * (B-r)^(15-c) := by
    rw [he]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _))
      (Nat.descFactorial_le_pow _ _)
  have bd := collision_deficit B 14
  change B^15 ≤ B.descFactorial 15 + 105*B^14 at bd
  have hdef : (B-105)*B^14 ≤ B.descFactorial 15 := by
    rw [pow_succ'] at bd
    have hs : B-105+105 = B := Nat.sub_add_cancel hb
    have eqn : (B-105)*B^14+105*B^14 = B*B^14 := by rw [← Nat.add_mul, hs]
    omega
  have lhs := (Nat.mul_le_mul_left ((B-15).choose (r-c)) hdef).trans hw
  have expr : r^c * (B-r)^(15-c) = (17^c*183^(15-c))*v^15 := by
    have h1 : r = 17*v := by dsimp [r,v]; omega
    have h2 : B-r = 183*v := by dsimp [B,r,v]; omega
    rw [h2,h1, mul_pow (17:ℕ) v c, mul_pow (183:ℕ) v (15-c)]
    calc
      _ = (17^c*183^(15-c))*(v^c*v^(15-c)) := by ac_rfl
      _ = _ := by rw [←pow_add,Nat.add_sub_of_le hc]
  have bound : ((B-105)*((B-15).choose (r-c)))*B^14 ≤
      B.choose r*(17^c*183^(15-c))*v^15 := by
    calc
      _ = (B-15).choose (r-c) * ((B-105)*B^14) := by ac_rfl
      _ ≤ B.choose r * r^c * (B-r)^(15-c) := lhs
      _ = _ := by rw [Nat.mul_assoc,expr]; ac_rfl
  have bscaled : B = 200*v := by dsimp [B,v]; omega
  change (B-105) * (B-15).choose (r-c) * 200^15 ≤ B * B.choose r * (17^c * 183^(15-c))
  apply (mul_le_mul_iff_of_pos_right (by dsimp [v]; positivity : 0<v^14)).mp
  calc
    _ = 200 * (((B-105)*(B-15).choose (r-c))*B^14) := by
      conv_rhs => rw [show B^14 = 200^14*v^14 by rw [bscaled,mul_pow]]
      ring
    _ ≤ 200*(B.choose r*(17^c*183^(15-c))*v^15) := Nat.mul_le_mul_left _ bound
    _ = _ := by rw [show v^15 = v^14*v by ring, bscaled]; ring


open Finset

/-- On any 16-bit window the without-replacement mean exceeds 0.74518, as
soon as the independent mean exceeds 0.7452 and the loss weights are dominated
by the falling-factorial comparison. No independence between windows is needed. -/
theorem transfer_local_mean {ι : Type*} (I : Finset ι) (P Q g : ι → ℝ) (B : ℝ)
    (large : 2000000 ≤ B) (hp : ∑ i ∈ I, P i = 1) (hq : ∑ i ∈ I, Q i = 1)
    (dominate : ∀ i ∈ I, (B-105)*P i ≤ B*Q i) (hu : ∀ i ∈ I, g i ≤ 1)
    (independent : (1863/2500:ℝ) < ∑ i ∈ I, Q i*g i) :
    (37259/50000:ℝ) < ∑ i ∈ I, P i*g i := by
  have losses := sum_le_sum (s := I) (fun i hi =>
    mul_le_mul_of_nonneg_right (dominate i hi) (sub_nonneg.mpr (hu i hi)))
  have identity (s : ℝ) (w : ι → ℝ) (H : ∑ i ∈ I, w i = 1) :
      ∑ i ∈ I, s*w i*(1-g i) = s*(1-∑ i ∈ I, w i*g i) := by
    simp only [mul_assoc, ←mul_sum, mul_sub, mul_one, sum_sub_distrib, H]
  rw [identity _ _ hp, identity _ _ hq] at losses
  by_contra! bad
  have h1 := mul_le_mul_of_nonneg_left bad (by linarith : 0 ≤ B-105)
  have h2 := mul_lt_mul_of_pos_left independent (by linarith : 0 < B)
  nlinarith only [large,losses,h1,h2]

/-- Even charging the fifteen padded windows their full worst-case cost does
not consume the 0.745 target at the first permitted length. -/
theorem full_window_margin (N : ℝ) (hn : 2000001 ≤ N) :
    (745/1000:ℝ)*N < (N-15)*(37259/50000:ℝ)-15 := by linarith

end DyadicWordPopulation

namespace DyadicWordPopulation

/-- Mass of one specified 16-bit value in the uniform fixed-size family. -/
noncomputable def fixedMass (t c : ℕ) : ℝ :=
  ((1000*t-15).choose (85*t-c):ℝ) / (2*((1000*t).choose (85*t):ℝ))

/-- Its probability under independent transitions, with a fair first bit. -/
noncomputable def iidMass (c : ℕ) : ℝ := ((17:ℝ)^c*183^(15-c))/(2*200^15)

/-- The pointwise comparison is in the direction needed for the nonnegative
cosine loss. The same factor works for every possible window. -/
theorem mass_comparison (t c : ℕ) (ht : 2000 ≤ t) (hc : c ≤ 15) :
    (1000*(t:ℝ)-105)*fixedMass t c ≤ (1000*(t:ℝ))*iidMass c := by
  have hp : 0 < ((1000*t).choose (85*t) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 85*t ≤ 1000*t by omega)
  have hn : 105 ≤ 1000*t := by omega
  have H := Nat.cast_le (α := ℝ).mpr (pattern_weight_le t c ht hc)
  push_cast [Nat.cast_sub hn] at H
  unfold fixedMass iidMass
  rw [←mul_div_assoc,←mul_div_assoc,div_le_div_iff₀ (by positivity) (by positivity)]
  linarith only [H]

end DyadicWordPopulation

namespace DyadicWords

def gaps (h : ℕ) := Ico h (h+15)

def changes (a : ℕ) := (range 15).filter fun i => a.testBit (i+1) ≠ a.testBit i

def windowChanges (h a : ℕ) := (gaps h).filter fun j => a.testBit (j-h+1) ≠ a.testBit (j-h)

theorem windowChanges_card (h a : ℕ) : (windowChanges h a).card = (changes a).card := by
  have shift : windowChanges h a = (changes a).image (· + h) := by
    ext j
    simp only [windowChanges,changes,gaps,mem_filter,mem_Ico,mem_image,mem_range]
    constructor
    · rintro ⟨⟨lo,hi⟩,flip⟩
      exact ⟨j-h,⟨by omega,flip⟩,by omega⟩
    · rintro ⟨i,⟨hi,flip⟩,rfl⟩
      simpa only [Nat.add_sub_cancel] using
        (show (h ≤ i+h ∧ i+h < h+15) ∧ a.testBit (i+1) ≠ a.testBit i from ⟨by omega,flip⟩)
  rw [shift,card_image_of_injective _ (fun _ _ e => Nat.add_right_cancel e)]

/-- A full 16-bit window has value a iff its initial bit and fifteen changes match a. -/
theorem match_window (B h a : ℕ) (p : Bool × Finset ℕ) (inside : h+15 ≤ B) (ha : a < 2^16) :
    window (encode B p) h = a ↔
      bitAt p.1 p.2 h = a.testBit 0 ∧ p.2 ∩ gaps h = windowChanges h a := by
  have loc (i : ℕ) (hi : i < 16) :
      (window (encode B p) h).testBit i = bitAt p.1 p.2 (i+h) := by
    rw [window_bit _ _ _ hi,read_bit _ _ _ (by omega)]
  constructor
  · intro eqn
    have bit_eq (i : ℕ) (hi : i<16) : bitAt p.1 p.2 (i+h) = a.testBit i :=
      (loc _ hi).symm.trans (congrArg (fun x : ℕ => x.testBit i) eqn)
    refine ⟨by simpa using bit_eq 0 (by decide),?_⟩
    ext j
    by_cases hj : j ∈ gaps h
    · obtain ⟨lo,hi⟩ := mem_Ico.mp hj
      simp only [windowChanges,mem_inter,mem_filter,hj,and_true,true_and]
      have e := bit_eq (j-h) (by omega)
      have f := bit_eq (j-h+1) (by omega)
      rw [show j-h+h=j by omega] at e
      rw [show j-h+1+h=j+1 by omega] at f
      rw [←bit_changes p.1 p.2 j,e,f]
    · simp [windowChanges,hj]
  · rintro ⟨h0,hs⟩
    have eqbits (i : ℕ) (hi : i<16) : bitAt p.1 p.2 (i+h) = a.testBit i := by
      induction i with
      | zero => simpa using h0
      | succ i ih =>
        have e := ih (by omega)
        have mem : i+h ∈ gaps h := mem_Ico.mpr (by omega)
        have m : i+h ∈ p.2 ↔ a.testBit (i+1) ≠ a.testBit i := by
          have := Finset.ext_iff.mp hs (i+h)
          simpa [windowChanges,mem] using this
        rw [show i+1+h = i+h+1 by omega]
        rw [bitAt,e]
        by_cases f : i+h ∈ p.2
        · have diff := m.mp f
          cases aa : a.testBit i <;> cases bb : a.testBit (i+1) <;> simp_all
        · have same : a.testBit (i+1) = a.testBit i := not_ne_iff.mp (fun z => f (m.mpr z))
          simp [f,same]
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i<16
    · exact (loc i hi).trans (eqbits i hi)
    · have powle : (2:ℕ)^16 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
      have hw : window (encode B p) h < 2^16 := Nat.mod_lt _ (by decide)
      rw [Nat.testBit_lt_two_pow (hw.trans_le powle), Nat.testBit_lt_two_pow (ha.trans_le powle)]

end DyadicWords

namespace DyadicWords

/-- Exact law of an actual extracted 16-bit value for a uniform word with exactly r total transitions. -/
theorem value_multiplicity (B r h a : ℕ) (inside : h+15 ≤ B) (ha : a < 2^16)
    (hr : 15 ≤ r) :
    ((sample B r).filter fun p => window (encode B p) h = a).card =
      (B-15).choose (r-(changes a).card) := by
  have hv : (gaps h).card = 15 := by simp [gaps]
  have hw : gaps h ⊆ range B := fun i hi => mem_range.mpr (lt_of_lt_of_le (mem_Ico.mp hi).2 inside)
  have hs : windowChanges h a ⊆ gaps h := filter_subset _ _
  have hcard : (windowChanges h a).card ≤ r := (card_le_card hs).trans (by simpa only [hv] using hr)
  have filters : (sample B r).filter (fun p => window (encode B p) h = a) =
      (sample B r).filter (fun p => bitAt p.1 p.2 h = a.testBit 0 ∧ p.2 ∩ gaps h = windowChanges h a) := by
    exact filter_congr (fun p _ => match_window B h a p inside ha)
  rw [filters,prescribed_window_count B r h _ _ _ hw hs hcard,hv,windowChanges_card]

end DyadicWords

namespace DyadicWords
open DyadicWordPopulation

noncomputable def loss (a : ℕ) := 1 - Real.cos (2*Real.pi*(a:ℝ)/65536)

/-- The one length-independent finite inequality used by the construction. -/
@[irreducible] def lossCertificate : Prop :=
  (∑ a ∈ range 65536, iidMass (changes a).card * loss a) < (637/2500:ℝ)

theorem sample_card (B r : ℕ) : (sample B r).card = 2*B.choose r := by simp [sample]

private theorem loss_margin {b u v : ℝ} (hb : 2000000 ≤ b)
    (hd : (b-105)*u ≤ b*v) (hi : v < 637/2500) : u ≤ 12741/50000 := by
  by_contra! bad
  have a := mul_lt_mul_of_pos_left bad (by linarith only [hb] : 0 < b-105)
  have c := mul_lt_mul_of_pos_left hi (by linarith only [hb] : 0 < b)
  nlinarith only [hb,hd,a,c]

theorem local_loss (cert : lossCertificate) (t h : ℕ) (ht : 2000 ≤ t)
    (inside : h+15 ≤ 1000*t) :
    ∑ p ∈ sample (1000*t) (85*t), loss (window (encode (1000*t) p) h) ≤
      (12741/50000:ℝ)*(sample (1000*t) (85*t)).card := by
  let A := sample (1000*t) (85*t)
  let n : ℝ := A.card
  let f (p : Bool × Finset ℕ) := window (encode (1000*t) p) h
  have choosePos : 0 < ((1000*t).choose (85*t) : ℝ) := by
    exact_mod_cast Nat.choose_pos (show 85*t ≤ 1000*t by omega)
  have hn : n = 2*((1000*t).choose (85*t):ℝ) := by simp [n,A,sample_card]
  have maps (p) (_hp : p ∈ A) : f p ∈ range 65536 := mem_range.mpr (Nat.mod_lt _ (by decide))
  have count (a : ℕ) (ha : a ∈ range 65536) :
      (((A.filter fun p => f p = a).card):ℝ) = n*fixedMass t (changes a).card := by
    rw [value_multiplicity _ _ _ _ inside (mem_range.mp ha) (by omega),hn]
    unfold fixedMass
    field_simp
  have upper (a : ℕ) (ha : a ∈ range 65536) :
      (1000*(t:ℝ)-105)*(fixedMass t (changes a).card*loss a) ≤
        (1000*(t:ℝ))*(iidMass (changes a).card*loss a) := by
    have hc : (changes a).card ≤ 15 := by
      exact (card_le_card (filter_subset _ _)).trans_eq (card_range 15)
    have := mul_le_mul_of_nonneg_right (mass_comparison t _ ht hc)
      (show 0 ≤ loss a from sub_nonneg.mpr (Real.cos_le_one _))
    simpa only [mul_assoc] using this
  have m := sum_le_sum upper
  rw [←mul_sum,←mul_sum] at m
  unfold lossCertificate at cert
  have ht' : (2000:ℝ) ≤ t := by exact_mod_cast ht
  have upperTotal : (∑ a ∈ range 65536, fixedMass t (changes a).card * loss a) ≤
      (12741/50000:ℝ) := by
    generalize (range 65536 : Finset ℕ) = I at m cert ⊢
    exact loss_margin (b := 1000*(t:ℝ))
      (v := ∑ a ∈ I, iidMass (changes a).card * loss a)
      (by linarith only [ht']) m cert
  change ∑ p ∈ A, loss (f p) ≤ _ * n
  calc
    _ = ∑ a ∈ range 65536, (((A.filter fun p => f p=a).card):ℝ)*loss a := by
      simpa only [sum_const,nsmul_eq_mul] using (sum_fiberwise_of_maps_to' maps loss).symm
    _ = n*∑ a ∈ range 65536, fixedMass t (changes a).card * loss a := by
      rw [mul_sum]
      exact sum_congr rfl (fun a ha => by rw [count a ha,mul_assoc])
    _ ≤ _ := by rw [mul_comm _ n]; exact mul_le_mul_of_nonneg_left upperTotal (Nat.cast_nonneg _)

noncomputable def phase (N j k : ℕ) : ℂ :=
  Complex.exp (((2*Real.pi*↑⌊(65536:ℝ)*2^j*((k:ℝ)/2^N)⌋/65536 : ℝ):ℂ)*Complex.I)

/-- Assemble all overlapping full windows and all fifteen padded boundary terms. -/
theorem mean_from_finite_certificate (cert : lossCertificate) (t : ℕ) (ht : 2000 ≤ t) :
    let N := 1000*t+1
    ∃ S ⊆ range (2^N), 2*(1000*t).choose (85*t) ≤ S.card ∧
      (745/1000:ℝ)*N*S.card < ∑ k ∈ S, (∑ j ∈ range N, phase N j k).re := by
  let B := 1000*t
  let r := 85*t
  let N := B+1
  let A := sample B r
  let n : ℝ := A.card
  let y (j : ℕ) := ∑ p ∈ A, (phase N j (encode B p)).re
  have hn : 0<n := by
    dsimp [n,A]
    rw [sample_card]
    exact_mod_cast Nat.mul_pos (by decide : 0<2) (Nat.choose_pos (show r≤B by dsimp [r,B]; omega))
  have full (j : ℕ) (hj : j ∈ range (N-15)) : (37259/50000:ℝ)*n ≤ y j := by
    have jlt := mem_range.mp hj
    let h := N-j-16
    have eqN : N = j+16+h := by dsimp [h]; omega
    have fits : h+15 ≤ B := by dsimp [h,N]; omega
    have e (p) : (phase N j (encode B p)).re =
        1-loss (window (encode B p) h) := by
      unfold phase
      rw [eqN,window_phase]
      unfold loss
      ring
    have est := local_loss cert t h ht fits
    change _ ≤ ∑ p ∈ A, (phase N j (encode B p)).re
    simp_rw [e,sum_sub_distrib,sum_const,nsmul_eq_mul,mul_one]
    change _ ≤ n - _
    change (∑ p ∈ A, loss (window (encode B p) h)) ≤ (12741/50000:ℝ)*n at est
    linarith only [est]
  have tail (j : ℕ) : -n ≤ y j := by
    have term (p : Bool × Finset ℕ) (_hp : p ∈ A) : (-1:ℝ) ≤ (phase N j (encode B p)).re := by
      unfold phase
      rw [Complex.exp_ofReal_mul_I_re]
      exact Real.neg_one_le_cos _
    simpa [n,y] using sum_le_sum term
  have hN : 2000001 ≤ N := by dsimp [N,B]; omega
  have num := full_window_margin (N:ℝ) (by exact_mod_cast hN)
  have addN : N-15+15 = N := by omega
  have total : (745/1000:ℝ)*N*n < ∑ j ∈ range N, y j := by
    have lower0 := sum_le_sum full
    have lower1 := sum_le_sum (s := range 15) (fun j _ => tail (N-15+j))
    simp only [sum_const,nsmul_eq_mul,card_range] at lower0 lower1
    push_cast [Nat.cast_sub (by omega : 15 ≤ N)] at lower0 lower1
    have prod := mul_lt_mul_of_pos_right num hn
    conv_rhs => rw [←addN, sum_range_add]
    linarith only [prod,lower0,lower1]
  refine ⟨family B r,family_grid B r, (family_card B r).ge,?_⟩
  rw [family, sum_image (encode_injective B r)]
  simp_rw [Complex.re_sum]
  rw [sum_comm]
  have nc : ((family B r).card:ℝ) = n := by simp [family_card,n,A,sample_card]
  change (745/1000:ℝ)*N*((family B r).card:ℝ) < ∑ j ∈ range N, y j
  rw [nc]
  exact total

end DyadicWords

/-- The single finite cosine inequality implies the research desk’s exact mean statement. -/
theorem DyadicWords.frozen_mean_from_certificate (h : DyadicWords.lossCertificate) :
    (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x3 * x2⌋ / (65536 : ℝ)) * Complex.I); ∀ (x2 : ℕ),   (2000 : ℕ) ≤ x2 →     have x4 : ℕ := (1000 : ℕ) * x2 + (1 : ℕ);     ∃ x5 ⊆ Finset.range ((2 : ℕ) ^ x4), (2 : ℕ) * ((1000 : ℕ) * x2).choose ((85 : ℕ) * x2) ≤ x5.card ∧ (745 / 1000 : ℝ) * ↑x4 * ↑x5.card < ∑ x6 ∈ x5, (x1 x4 (↑x6 / (2 : ℝ) ^ x4)).re) :=
  fun t ht => DyadicWords.mean_from_finite_certificate h t ht

/-! Two conditional Fourier sums track all 16-bit windows exactly. -/
namespace DyadicTransfer
open DyadicWords DyadicWordPopulation

def factor (b d : Bool) : ℕ := if b ≠ d then 17 else 183

def weight (n a : ℕ) : ℕ :=
  ∏ i ∈ range n, factor (a.testBit (i+1)) (a.testBit i)

noncomputable def mass (n a : ℕ) : ℝ := (weight n a:ℝ)/(2*200^n)

theorem mass_fifteen (a : ℕ) : mass 15 a = iidMass (changes a).card := by
  unfold mass weight factor
  rw [prod_ite]
  let p (i : ℕ) := a.testBit (i+1) ≠ a.testBit i
  have h := card_filter_add_card_filter_not (s := range 15) p
  have hnot : ((range 15).filter (fun i => ¬p i)).card = 15-(changes a).card := by
    change ((range 15).filter p).card + _ = _ at h
    change _ = 15-((range 15).filter p).card
    rw [card_range] at h
    omega
  change ((↑((∏ _i ∈ (range 15).filter p, (17:ℕ)) *
              (∏ _i ∈ (range 15).filter (fun i => ¬p i), (183:ℕ))) : ℝ)/_) = _
  simp only [prod_const,hnot,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rfl

theorem mass_append (n a : ℕ) (b : Bool) :
    mass (n+1) (Nat.bit b a) = mass n a * (factor (a.testBit 0) b : ℝ)/200 := by
  have h : weight (n+1) (Nat.bit b a) = weight n a * factor (a.testBit 0) b := by
    unfold weight
    rw [prod_range_succ']
    simp only [Nat.testBit_bit_succ,Nat.testBit_bit_zero]
  unfold mass
  rw [h,pow_succ]
  push_cast
  ring

theorem sum_bits {M : Type*} [AddCommMonoid M] (f : ℕ → M) (D : ℕ) :
    ∑ k ∈ range (2*D), f k =
      (∑ k ∈ range D, f (Nat.bit false k)) + (∑ k ∈ range D, f (Nat.bit true k)) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [show 2*(D+1) = 2*D+1+1 by omega, sum_range_succ, sum_range_succ, ih,
      sum_range_succ _ D, sum_range_succ _ D]
    simp only [Nat.bit_val, Bool.toNat_false, Bool.toNat_true, Nat.add_zero]
    ac_rfl

noncomputable def cis (x : ℝ) : ℂ := Complex.exp ((x:ℂ)*Complex.I)
noncomputable def wave (x : ℝ) (n a : ℕ) := cis (x*a/2^n)
noncomputable def amp (x : ℝ) (n : ℕ) (b : Bool) : ℂ :=
  ∑ k ∈ range (2^n), (mass n (Nat.bit b k):ℂ)*wave x n (Nat.bit b k)

@[simp] theorem cis_zero : cis 0=1 := by simp [cis]
theorem wave_append (x : ℝ) (n a : ℕ) (b : Bool) :
    wave x (n+1) (Nat.bit b a) = wave x n a * cis (x*b.toNat/2^(n+1)) := by
  unfold wave cis
  rw [←Complex.exp_add,Nat.bit_val,pow_succ]
  congr 1
  push_cast
  field_simp

theorem advance (x : ℝ) (n : ℕ) (b : Bool) :
    amp x (n+1) b = cis (x*b.toNat/2^(n+1)) *
      (((factor false b:ℕ):ℂ)/200*amp x n false +
       ((factor true b:ℕ):ℂ)/200*amp x n true) := by
  let f (a : ℕ) : ℂ := (mass (n+1) (Nat.bit b a):ℂ)*wave x (n+1) (Nat.bit b a)
  change ∑ a ∈ range (2^(n+1)), f a = _
  rw [pow_succ',sum_bits]
  have one (d : Bool) : ∑ k ∈ range (2^n), f (Nat.bit d k) =
      cis (x*b.toNat/2^(n+1)) * (((factor d b:ℕ):ℂ)/200*amp x n d) := by
    rw [amp,mul_sum,mul_sum]
    apply sum_congr rfl
    intro k _
    dsimp only [f]
    rw [mass_append,wave_append,Nat.testBit_bit_zero]
    push_cast
    ring
  rw [one,one,mul_add]

theorem amp_base (x : ℝ) (b : Bool) : amp x 0 b = cis (x*b.toNat)/2 := by
  cases b <;> simp [amp,mass,weight,wave,Nat.bit_val]; ring

theorem zero_amp (n : ℕ) (b : Bool) : amp 0 n b = 1/2 := by
  induction n generalizing b with
  | zero => simp [amp_base]
  | succ n ih => rw [advance,ih,ih]; cases b <;> norm_num [factor]

theorem total (x : ℝ) (n : ℕ) :
    ∑ k ∈ range (2^(n+1)), (mass n k:ℂ)*wave x n k = amp x n false + amp x n true := by
  rw [pow_succ',sum_bits]; rfl

set_option linter.constructorNameAsVariable false in
theorem loss_of_final (good : (1863/2500:ℝ) < (amp Real.pi 15 false + amp Real.pi 15 true).re) :
    lossCertificate := by
  have eqsum (x : ℝ) : ∑ a ∈ range 65536, mass 15 a * Real.cos (x*a/2^15) =
      (amp x 15 false + amp x 15 true).re := by
    have h := congrArg Complex.re (total x 15)
    rw [show (2:ℕ)^(15+1)=65536 by decide] at h
    simpa only [Complex.re_sum,Complex.re_ofReal_mul,wave,cis,Complex.exp_ofReal_mul_I_re] using h
  have unit := eqsum 0
  simp only [zero_mul,zero_div,Real.cos_zero,mul_one,zero_amp] at unit
  norm_num at unit
  have e (a : ℕ) : loss a = 1-Real.cos (Real.pi*a/2^15) := by
    unfold loss
    rw [show (2*Real.pi*(a:ℝ)/65536) = Real.pi*a/2^15 by ring]
  unfold lossCertificate
  simp_rw [←mass_fifteen,e,mul_sub,mul_one]
  rw [sum_sub_distrib]
  have H := congrArg₂ (fun a b : ℝ => a-b) unit (eqsum Real.pi)
  rw [H]
  generalize (amp Real.pi 15 false + amp Real.pi 15 true).re = z at good ⊢
  linarith only [good]

end DyadicTransfer

namespace DyadicIntervals

structure Box where
  lo : ℚ
  hi : ℚ
deriving DecidableEq

def Holds (b : Box) (x : ℝ) : Prop := b.lo ≤ x ∧ x ≤ b.hi
abbrev Wider (c b : Box) := c.lo ≤ b.lo ∧ b.hi ≤ c.hi

theorem widen {b c : Box} {x : ℝ} (h : Holds b x) (hc : Wider c b) : Holds c x :=
  ⟨le_trans (by exact_mod_cast hc.1) h.1,le_trans h.2 (by exact_mod_cast hc.2)⟩

def add (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩
def sub (a b : Box) : Box := ⟨a.lo-b.hi,a.hi-b.lo⟩
def point (q : ℚ) : Box := ⟨q,q⟩
theorem hold_point (q : ℚ) : Holds (point q) (q:ℝ) := ⟨le_rfl,le_rfl⟩

theorem hold_add {a b : Box} {x y : ℝ} (ha : Holds a x) (hb : Holds b y) :
    Holds (add a b) (x+y) := by
  simpa [Holds,add] using And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)

theorem hold_sub {a b : Box} {x y : ℝ} (ha : Holds a x) (hb : Holds b y) :
    Holds (sub a b) (x-y) := by
  simpa [Holds,sub] using And.intro (sub_le_sub ha.1 hb.2) (sub_le_sub ha.2 hb.1)

def mul (a b : Box) : Box :=
  ⟨min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi)),
   max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))⟩

private theorem corner {x y a b c d l u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hlo : (l ≤ a*c ∧ l ≤ a*d) ∧ (l ≤ b*c ∧ l ≤ b*d))
    (hhi : (a*c ≤ u ∧ a*d ≤ u) ∧ (b*c ≤ u ∧ b*d ≤ u)) :
    l ≤ x*y ∧ x*y ≤ u := by
  have lower (z : ℝ) (hc : l ≤ z*c) (hd : l ≤ z*d) : l ≤ z*y := by
    rcases le_total 0 z with e | e
    · exact hc.trans (mul_le_mul_of_nonneg_left hy.1 e)
    · exact hd.trans (mul_le_mul_of_nonpos_left hy.2 e)
  have upper (z : ℝ) (hc : z*c ≤ u) (hd : z*d ≤ u) : z*y ≤ u := by
    rcases le_total 0 z with e | e
    · exact (mul_le_mul_of_nonneg_left hy.2 e).trans hd
    · exact (mul_le_mul_of_nonpos_left hy.1 e).trans hc
  rcases le_total 0 y with e | e
  · exact ⟨(lower a hlo.1.1 hlo.1.2).trans (mul_le_mul_of_nonneg_right hx.1 e),
      (mul_le_mul_of_nonneg_right hx.2 e).trans (upper b hhi.2.1 hhi.2.2)⟩
  · exact ⟨(lower b hlo.2.1 hlo.2.2).trans (mul_le_mul_of_nonpos_right hx.2 e),
      (mul_le_mul_of_nonpos_right hx.1 e).trans (upper a hhi.1.1 hhi.1.2)⟩

theorem hold_mul {a b : Box} {x y : ℝ} (ha : Holds a x) (hb : Holds b y) :
    Holds (mul a b) (x*y) := by
  apply corner ha hb
  · simp only [←le_min_iff]
    simp [mul]
  · simp only [←max_le_iff]
    simp [mul]

structure Rect where
  x : Box
  y : Box

def Rect.Holds (b : Rect) (z : ℂ) := DyadicIntervals.Holds b.x z.re ∧ DyadicIntervals.Holds b.y z.im
abbrev Rect.Wider (c b : Rect) := DyadicIntervals.Wider c.x b.x ∧ DyadicIntervals.Wider c.y b.y
theorem Rect.widen {b c : Rect} {z : ℂ} (h : b.Holds z) (hc : c.Wider b) : c.Holds z :=
  ⟨DyadicIntervals.widen h.1 hc.1, DyadicIntervals.widen h.2 hc.2⟩

def plus (a b : Rect) : Rect := ⟨add a.x b.x,add a.y b.y⟩
def times (a b : Rect) : Rect :=
  ⟨sub (mul a.x b.x) (mul a.y b.y), add (mul a.x b.y) (mul a.y b.x)⟩
def realPoint (q : ℚ) : Rect := ⟨point q,point 0⟩
theorem hold_plus {a b : Rect} {z w : ℂ} (ha : a.Holds z) (hb : b.Holds w) :
    (plus a b).Holds (z+w) := ⟨hold_add ha.1 hb.1,hold_add ha.2 hb.2⟩
theorem hold_times {a b : Rect} {z w : ℂ} (ha : a.Holds z) (hb : b.Holds w) :
    (times a b).Holds (z*w) :=
  ⟨hold_sub (hold_mul ha.1 hb.1) (hold_mul ha.2 hb.2),
   hold_add (hold_mul ha.1 hb.2) (hold_mul ha.2 hb.1)⟩
theorem hold_realPoint (q : ℚ) : (realPoint q).Holds ((q:ℝ):ℂ) := by
  exact ⟨hold_point _,by simp [DyadicIntervals.Holds,realPoint,point]⟩

abbrev HalfOK (p c s : Box) :=
  (0 ≤ c.hi ∧ c.lo^2 ≤ (1+p.lo)/2 ∧ (1+p.hi)/2 ≤ c.hi^2) ∧
  (0 ≤ s.hi ∧ s.lo^2 ≤ (1-p.hi)/2 ∧ (1-p.lo)/2 ≤ s.hi^2)

theorem enclose_half {p c s : Box} {x : ℝ} (pos : 0 ≤ x) (small : x ≤ Real.pi)
    (hx : Holds p (Real.cos x)) (ok : HalfOK p c s) :
    Holds c (Real.cos (x/2)) ∧ Holds s (Real.sin (x/2)) := by
  have hr {b : Box} {y : ℝ} (h : 0 ≤ b.hi) (lo : (b.lo:ℝ)^2 ≤ y) (hi : y ≤ (b.hi:ℝ)^2) :
      Holds b (Real.sqrt y) :=
    ⟨Real.le_sqrt_of_sq_le lo, Real.sqrt_le_iff.mpr ⟨by exact_mod_cast h,hi⟩⟩
  rw [Real.cos_half (by linarith [Real.pi_pos]) small,
      Real.sin_half_eq_sqrt pos (by linarith [Real.pi_pos])]
  constructor
  · apply hr ok.1.1
    · have h : (c.lo:ℝ)^2 ≤ (1+(p.lo:ℝ))/2 := by exact_mod_cast ok.1.2.1
      linarith only [h,hx.1]
    · have h : (1+(p.hi:ℝ))/2 ≤ (c.hi:ℝ)^2 := by exact_mod_cast ok.1.2.2
      linarith only [h,hx.2]
  · apply hr ok.2.1
    · have h : (s.lo:ℝ)^2 ≤ (1-(p.hi:ℝ))/2 := by exact_mod_cast ok.2.2.1
      linarith only [h,hx.2]
    · have h : (1-(p.lo:ℝ))/2 ≤ (s.hi:ℝ)^2 := by exact_mod_cast ok.2.2.2
      linarith only [h,hx.1]

end DyadicIntervals

namespace DyadicTransfer
open DyadicIntervals

noncomputable def angle (n : ℕ) : ℝ := Real.pi / 2^n
noncomputable def rot (n : ℕ) := cis (angle n)

theorem next_rot (n : ℕ) {old new : Rect} (hb : old.Holds (rot n))
    (hc : HalfOK old.x new.x new.y) : new.Holds (rot (n+1)) := by
  have hpi : angle n ≤ Real.pi := by
    unfold angle
    exact div_le_self Real.pi_pos.le (one_le_pow₀ (by norm_num))
  have pos : 0 ≤ angle n := by unfold angle; positivity
  have cosbound : Holds old.x (Real.cos (angle n)) := by
    simpa only [rot,cis,Complex.exp_ofReal_mul_I_re] using hb.1
  have step := enclose_half pos hpi cosbound hc
  have ang : angle (n+1) = angle n/2 := by unfold angle; rw [pow_succ,div_mul_eq_div_div]
  simpa only [Rect.Holds,rot,cis,Complex.exp_ofReal_mul_I_re,Complex.exp_ofReal_mul_I_im,ang] using step

def mix (a b : Rect) (q p : ℚ) := plus (times (realPoint q) a) (times (realPoint p) b)

theorem hold_mix {a b : Rect} {z w : ℂ} (ha : a.Holds z) (hb : b.Holds w) (q p : ℚ) :
    (mix a b q p).Holds (((q:ℝ):ℂ)*z+((p:ℝ):ℂ)*w) :=
  hold_plus (hold_times (hold_realPoint q) ha) (hold_times (hold_realPoint p) hb)

theorem advance_box (n : ℕ) {a b r c d : Rect}
    (states : a.Holds (amp Real.pi n false) ∧ b.Holds (amp Real.pi n true))
    (hr : r.Holds (rot (n+1)))
    (enclose : c.Wider (mix a b (183/200) (17/200)) ∧
      d.Wider (times r (mix a b (17/200) (183/200)))) :
    c.Holds (amp Real.pi (n+1) false) ∧ d.Holds (amp Real.pi (n+1) true) := by
  have ff : factor false false = 183 := rfl
  have tf : factor true false = 17 := rfl
  have ft : factor false true = 17 := rfl
  have tt : factor true true = 183 := rfl
  obtain ⟨ha,hb⟩ := states
  constructor
  · have h := Rect.widen (hold_mix ha hb (183/200) (17/200)) enclose.1
    rw [advance]
    simpa only [Bool.toNat_false,Nat.cast_zero,mul_zero,zero_div,cis_zero,one_mul,ff,tf,Nat.cast_ofNat,
      Rat.cast_div,Rat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_ofNat] using h
  · have h := Rect.widen (hold_times hr (hold_mix ha hb (17/200) (183/200))) enclose.2
    rw [advance]
    simpa only [Bool.toNat_true,Nat.cast_one,mul_one,rot,angle,ft,tt,Nat.cast_ofNat,
      Rat.cast_div,Rat.cast_ofNat,Complex.ofReal_div,Complex.ofReal_ofNat] using h

end DyadicTransfer

namespace DyadicTransfer
open DyadicIntervals

/- The two conditional amplitudes start at +1/2 and -1/2. The endpoint data below
are proposed rational enclosures. Every half-angle, interval product, and outward
rounding inequality is checked in the kernel by the proof of final_boxes. -/
private def u0 : Rect := ⟨⟨1/2, 1/2⟩, ⟨0, 0⟩⟩
private def v0 : Rect := ⟨⟨-1/2, -1/2⟩, ⟨0, 0⟩⟩
private def rotation1 : Rect := ⟨⟨0, 0⟩, ⟨1, 1⟩⟩
private def u1 : Rect := ⟨⟨83/200, 83/200⟩, ⟨0, 0⟩⟩
private def v1 : Rect := ⟨⟨0, 0⟩, ⟨-83/200, -83/200⟩⟩
private def rotation2 : Rect := ⟨⟨1767766952966368811/2500000000000000000, 70710678118654752441/100000000000000000000⟩, ⟨1767766952966368811/2500000000000000000, 70710678118654752441/100000000000000000000⟩⟩
private def u2 : Rect := ⟨⟨15189/40000, 15189/40000⟩, ⟨-1411/40000, -1411/40000⟩⟩
private def v2 : Rect := ⟨⟨14672465709620861131/50000000000000000000, 3668116427405215283/12500000000000000000⟩, ⟨-24356293077970629479/100000000000000000000, -24356293077970629477/100000000000000000000⟩⟩
private def rotation3 : Rect := ⟨⟨23096988312782168903/25000000000000000000, 46193976625564337807/50000000000000000000⟩, ⟨9567085809127244293/25000000000000000000, 38268343236508977173/100000000000000000000⟩⟩
private def u3 : Rect := ⟨⟨4654894583829443299/12500000000000000000, 37239156670635546393/100000000000000000000⟩, ⟨-2648973705813751753/50000000000000000000, -1059589482325500701/20000000000000000000⟩⟩
private def v3 : Rect := ⟨⟨18215965677976345257/50000000000000000000, 910798283898817263/2500000000000000000⟩, ⟨-9356143115176340083/100000000000000000000, -2339035778794085019/25000000000000000000⟩⟩
private def rotation4 : Rect := ⟨⟨6129908002520190307/6250000000000000000, 98078528040323044913/100000000000000000000⟩, ⟨19509032201612826783/100000000000000000000, 9754516100806413393/50000000000000000000⟩⟩
private def u4 : Rect := ⟨⟨37170542518887503641/100000000000000000000, 7434108503777500729/20000000000000000000⟩, ⟨-705361755803644327/12500000000000000000, -5642894046429154613/100000000000000000000⟩⟩
private def v4 : Rect := ⟨⟨586831171621063077/1562500000000000000, 37557194983748036939/100000000000000000000⟩, ⟨-1717145689911212531/100000000000000000000, -1717145689911212517/100000000000000000000⟩⟩
private def rotation5 : Rect := ⟨⟨6219904541701230539/6250000000000000000, 796147781337757509/800000000000000000⟩, ⟨4900857016478030099/50000000000000000000, 9801714032956060201/100000000000000000000⟩⟩
private def u5 : Rect := ⟨⟨37203407978400648969/100000000000000000000, 2325212998650040561/6250000000000000000⟩, ⟨-265460271806256477/5000000000000000000, -5309205436125129533/100000000000000000000⟩⟩
private def v5 : Rect := ⟨⟨37544656534530021579/100000000000000000000, 18772328267265010797/50000000000000000000⟩, ⟨1637068500239937977/100000000000000000000, 327413700047987599/20000000000000000000⟩⟩
private def rotation6 : Rect := ⟨⟨99879545620517239271/100000000000000000000, 12484943202564654909/12500000000000000000⟩, ⟨2453383716370900711/50000000000000000000, 1226691858185450357/25000000000000000000⟩⟩
private def u6 : Rect := ⟨⟨930810352641791141/2500000000000000000, 744648282113432913/2000000000000000000⟩, ⟨-2359386075767049401/50000000000000000000, -589846518941762349/12500000000000000000⟩⟩
private def v6 : Rect := ⟨⟨7483821041490194349/20000000000000000000, 9354776301862742941/25000000000000000000⟩, ⟨2886180214059102117/100000000000000000000, 2886180214059102141/100000000000000000000⟩⟩
private def rotation7 : Rect := ⟨⟨99969881869620422011/100000000000000000000, 24992470467405105503/25000000000000000000⟩, ⟨2454122852291228797/100000000000000000000, 2454122852291228809/100000000000000000000⟩⟩
private def u7 : Rect := ⟨⟨18624141424661444179/50000000000000000000, 3724828284932288837/10000000000000000000⟩, ⟨-162894048018347069/4000000000000000000, -509043900057334589/12500000000000000000⟩⟩
private def v7 : Rect := ⟨⟨1166781402011443371/3125000000000000000, 37337004864366187897/100000000000000000000⟩, ⟨3157006062923300791/100000000000000000000, 3157006062923300823/100000000000000000000⟩⟩
private def rotation8 : Rect := ⟨⟨24998117545978613523/25000000000000000000, 99992470183914454093/100000000000000000000⟩, ⟨1227153828571992599/100000000000000000000, 61357691428599631/5000000000000000000⟩⟩
private def u8 : Rect := ⟨⟨2328489013787598051/6250000000000000000, 37255824220601568831/100000000000000000000⟩, ⟨-3457855833071208637/100000000000000000000, -3457855833071208621/100000000000000000000⟩⟩
private def v8 : Rect := ⟨⟨745909042715972731/2000000000000000000, 37295452135798636579/100000000000000000000⟩, ⟨3000409189597311149/100000000000000000000, 375051148699663899/12500000000000000000⟩⟩
private def rotation9 : Rect := ⟨⟨19999623505652022853/20000000000000000000, 49999058764130057133/50000000000000000000⟩, ⟨613588464915447501/100000000000000000000, 613588464915447543/100000000000000000000⟩⟩
private def u9 : Rect := ⟨⟨9314798148348329893/25000000000000000000, 37259192593393319591/100000000000000000000⟩, ⟨-363612913268048057/12500000000000000000, -727225826536096109/25000000000000000000⟩⟩
private def v9 : Rect := ⟨⟨37276339894764285367/100000000000000000000, 37276339894764285399/100000000000000000000⟩, ⟨2680230438988013447/100000000000000000000, 670057609747003377/25000000000000000000⟩⟩
private def rotation10 : Rect := ⟨⟨1999990587619152343/2000000000000000000, 97655790411091423/97656250000000000⟩, ⟨153397838148298801/50000000000000000000, 76698919074149421/25000000000000000000⟩⟩
private def u10 : Rect := ⟨⟨2328790632125615729/6250000000000000000, 7452130022801970337/20000000000000000000⟩, ⟨-608456734452032659/25000000000000000000, -2433826937808130609/100000000000000000000⟩⟩
private def v10 : Rect := ⟨⟨7453588326821767341/20000000000000000000, 37267941634108836743/100000000000000000000⟩, ⟨2319501420245317113/100000000000000000000, 2319501420245317203/100000000000000000000⟩⟩
private def rotation11 : Rect := ⟨⟨6249992646573136937/6250000000000000000, 49999941172585095497/50000000000000000000⟩, ⟨19174752328559553/12500000000000000000, 613592074513907/400000000000000000⟩⟩
private def u11 : Rect := ⟨⟨37261269893218265391/100000000000000000000, 4657658736652283177/12500000000000000000⟩, ⟨-1014897013686793789/50000000000000000000, -253724253421698443/12500000000000000000⟩⟩
private def v11 : Rect := ⟨⟨37264339717354818079/100000000000000000000, 37264339717354818127/100000000000000000000⟩, ⟨394526717898174641/20000000000000000000, 246579198686359177/12500000000000000000⟩⟩
private def rotation12 : Rect := ⟨⟨19999994117257644383/20000000000000000000, 99999970586288221917/100000000000000000000⟩, ⟨38349515937135047/50000000000000000000, 76699031874270747/100000000000000000000⟩⟩
private def u12 : Rect := ⟨⟨2328845676766867023/6250000000000000000, 37261530828269872397/100000000000000000000⟩, ⟨-422396919985027103/25000000000000000000, -1689587679940108361/100000000000000000000⟩⟩
private def v12 : Rect := ⟨⟨18631407882831885717/50000000000000000000, 4657851970707971437/12500000000000000000⟩, ⟨1661007949562841929/100000000000000000000, 1661007949562842373/100000000000000000000⟩⟩
private def rotation13 : Rect := ⟨⟨49999996323285892557/50000000000000000000, 19999998529314357023/20000000000000000000⟩, ⟨38349518757138921/100000000000000000000, 19174759378570113/50000000000000000000⟩⟩
private def u13 : Rect := ⟨⟨37261640047948353787/100000000000000000000, 18630820023974176911/50000000000000000000⟩, ⟨-702393525716178817/50000000000000000000, -351196762858089387/25000000000000000000⟩⟩
private def v13 : Rect := ⟨⟨3726217603701418807/10000000000000000000, 745243520740283763/2000000000000000000⟩, ⟨43453040265404499/3125000000000000000, 1390497288492944869/100000000000000000000⟩⟩
private def rotation14 : Rect := ⟨⟨4999999908082146469/5000000000000000000, 99999998161642929381/100000000000000000000⟩, ⟨19174759731069643/100000000000000000000, 4793689932767737/25000000000000000000⟩⟩
private def u14 : Rect := ⟨⟨372616856070189497/1000000000000000000, 37261685607018949741/100000000000000000000⟩, ⟨-1167187882538706999/100000000000000000000, -583593941269353421/50000000000000000000⟩⟩
private def v14 : Rect := ⟨⟨745238174549764093/2000000000000000000, 7452381745497640949/20000000000000000000⟩, ⟨290010755598683147/25000000000000000000, 116004302239473391/10000000000000000000⟩⟩
private def rotation15 : Rect := ⟨⟨12499999942551341411/12500000000000000000, 9999999954041073129/10000000000000000000⟩, ⟨9587379909597303/100000000000000000000, 1198422488699989/12500000000000000000⟩⟩
private def u15 : Rect := ⟨⟨3726170457225883637/10000000000000000000, 18630852286129418209/50000000000000000000⟩, ⟨-242343313904841159/25000000000000000000, -969373255619364377/100000000000000000000⟩⟩
private def v15 : Rect := ⟨⟨37261797338504799037/100000000000000000000, 37261797338504799157/100000000000000000000⟩, ⟨193160165997218773/20000000000000000000, 965800829986096063/100000000000000000000⟩⟩

private theorem from_bounds {a b : Rect} {z w : ℂ} (h : a.Holds z ∧ b.Holds w)
    (q : (1863/2500:ℚ) < a.x.lo+b.x.lo) : (1863/2500:ℝ) < (z+w).re := by
  have hq := (Rat.cast_lt (K := ℝ)).mpr q
  push_cast at hq
  exact hq.trans_le (add_le_add h.1.1.1 h.2.1.1)

private theorem final_boxes : u15.Holds (amp Real.pi (14+1) false) ∧ v15.Holds (amp Real.pi (14+1) true) := by
  have r1 : rotation1.Holds (rot 1) := by
    norm_num [Rect.Holds, DyadicIntervals.Holds, rot, angle, cis, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, rotation1, Real.cos_pi_div_two, Real.sin_pi_div_two]
  have h0 : u0.Holds (amp Real.pi 0 false) ∧ v0.Holds (amp Real.pi 0 true) := by
    rw [amp_base,amp_base]
    norm_num [u0,v0,Rect.Holds,DyadicIntervals.Holds,cis,Complex.exp_pi_mul_I]
  have h1 := advance_box 0 (c := u1) (d := v1) h0 r1 (by decide +kernel)
  have r2 := next_rot 1 (new := rotation2) r1 (by decide +kernel)
  have h2 := advance_box 1 (c := u2) (d := v2) h1 r2 (by decide +kernel)
  have r3 := next_rot 2 (new := rotation3) r2 (by decide +kernel)
  have h3 := advance_box 2 (c := u3) (d := v3) h2 r3 (by decide +kernel)
  have r4 := next_rot 3 (new := rotation4) r3 (by decide +kernel)
  have h4 := advance_box 3 (c := u4) (d := v4) h3 r4 (by decide +kernel)
  have r5 := next_rot 4 (new := rotation5) r4 (by decide +kernel)
  have h5 := advance_box 4 (c := u5) (d := v5) h4 r5 (by decide +kernel)
  have r6 := next_rot 5 (new := rotation6) r5 (by decide +kernel)
  have h6 := advance_box 5 (c := u6) (d := v6) h5 r6 (by decide +kernel)
  have r7 := next_rot 6 (new := rotation7) r6 (by decide +kernel)
  have h7 := advance_box 6 (c := u7) (d := v7) h6 r7 (by decide +kernel)
  have r8 := next_rot 7 (new := rotation8) r7 (by decide +kernel)
  have h8 := advance_box 7 (c := u8) (d := v8) h7 r8 (by decide +kernel)
  have r9 := next_rot 8 (new := rotation9) r8 (by decide +kernel)
  have h9 := advance_box 8 (c := u9) (d := v9) h8 r9 (by decide +kernel)
  have r10 := next_rot 9 (new := rotation10) r9 (by decide +kernel)
  have h10 := advance_box 9 (c := u10) (d := v10) h9 r10 (by decide +kernel)
  have r11 := next_rot 10 (new := rotation11) r10 (by decide +kernel)
  have h11 := advance_box 10 (c := u11) (d := v11) h10 r11 (by decide +kernel)
  have r12 := next_rot 11 (new := rotation12) r11 (by decide +kernel)
  have h12 := advance_box 11 (c := u12) (d := v12) h11 r12 (by decide +kernel)
  have r13 := next_rot 12 (new := rotation13) r12 (by decide +kernel)
  have h13 := advance_box 12 (c := u13) (d := v13) h12 r13 (by decide +kernel)
  have r14 := next_rot 13 (new := rotation14) r13 (by decide +kernel)
  have h14 := advance_box 13 (c := u14) (d := v14) h13 r14 (by decide +kernel)
  have r15 := next_rot 14 (new := rotation15) r14 (by decide +kernel)
  have h15 := advance_box 14 (c := u15) (d := v15) h14 r15 (by decide +kernel)
  exact h15

private theorem final_comparison : (1863/2500:ℚ) < u15.x.lo+v15.x.lo := by decide +kernel

attribute [local irreducible] amp

theorem numeric_bound : (1863/2500:ℝ) < (amp Real.pi (14+1) false + amp Real.pi (14+1) true).re :=
  @from_bounds u15 v15 (amp Real.pi (14+1) false) (amp Real.pi (14+1) true) final_boxes final_comparison

theorem certified_loss : DyadicWords.lossCertificate := by
  apply loss_of_final
  simpa only [Nat.reduceAdd] using numeric_bound

end DyadicTransfer

theorem Conjectures.Cuts.Taskb98f3332b3a9cab8abb1dd40 :
    (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x3 * x2⌋ / (65536 : ℝ)) * Complex.I); ∀ (x2 : ℕ),   (2000 : ℕ) ≤ x2 →     have x4 : ℕ := (1000 : ℕ) * x2 + (1 : ℕ);     ∃ x5 ⊆ Finset.range ((2 : ℕ) ^ x4), (2 : ℕ) * ((1000 : ℕ) * x2).choose ((85 : ℕ) * x2) ≤ x5.card ∧ (745 / 1000 : ℝ) * ↑x4 * ↑x5.card < ∑ x6 ∈ x5, (x1 x4 (↑x6 / (2 : ℝ) ^ x4)).re) :=
  DyadicWords.frozen_mean_from_certificate DyadicTransfer.certified_loss
