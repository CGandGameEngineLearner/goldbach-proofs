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
