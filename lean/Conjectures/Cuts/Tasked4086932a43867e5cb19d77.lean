import Mathlib

-- The scaled logarithm upper bound is adapted from the Apache-2.0 proof of
-- Task8f9f08650abf4d04bfa7122e, revision ed0b2428d69a876757ab067a438fcf6afce8e743.
-- Here 16 terms and 14 decimal places suffice for the short prime sum.
namespace MertensFiniteCorrection
open Finset

def scale : ℕ := 10 ^ 14

def roundedUp (u v : ℕ) : ℕ :=
  17 + ∑ i ∈ range 16,
    (2 * scale * (u - v) ^ (2 * i + 1)) / ((2 * i + 1) * (u + v) ^ (2 * i + 1))

theorem log_le_roundedUp (u v : ℕ) (hv : 0 < v) (hvu : v ≤ u) (huv : u ≤ 2 * v) :
    Real.log ((u : ℝ) / (v : ℝ)) ≤ (roundedUp u v : ℝ) / (scale : ℝ) := by
  have hscale : 0 < (scale : ℝ) := by norm_num [scale]
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hvuR : (v : ℝ) ≤ (u : ℝ) := by exact_mod_cast hvu
  have huR := hvR.trans_le hvuR
  have huvR : (u : ℝ) ≤ 2 * (v : ℝ) := by exact_mod_cast huv
  have hpos : 0 < (u : ℝ) + (v : ℝ) := by positivity
  let t : ℝ := ((u : ℝ) - (v : ℝ)) / ((u : ℝ) + (v : ℝ))
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hvuR) hpos.le
  have ht3 : t ≤ 1 / 3 := by
    apply (div_le_iff₀ hpos).2
    linarith only [huvR]
  have ht1 : t < 1 := ht3.trans_lt (by norm_num)
  have htRatio : (1 + t) / (1 - t) = (u : ℝ) / (v : ℝ) := by
    apply (div_eq_div_iff (sub_ne_zero.mpr ht1.ne') hvR.ne').2
    dsimp [t]
    field_simp
    ring
  have htail : 2 * (scale : ℝ) * (t ^ (33 : ℕ) / (1 - t ^ 2)) ≤ 1 := by
    have htSq : t ^ (2 : ℕ) ≤ (1 / 3 : ℝ) ^ (2 : ℕ) := pow_le_pow_left₀ ht0 ht3 2
    have hden : (0 : ℝ) < 1 - (1 / 3 : ℝ) ^ (2 : ℕ) := by norm_num
    have hden_le : 1 - (1 / 3 : ℝ) ^ (2 : ℕ) ≤ 1 - t ^ (2 : ℕ) := by linarith
    calc
      _ ≤ 2 * (scale : ℝ) * ((1 / 3 : ℝ) ^ (33 : ℕ) / (1 - (1 / 3 : ℝ) ^ (2 : ℕ))) := by
        gcongr
      _ ≤ _ := by norm_num [scale]
  let term : ℕ → ℕ := fun i =>
    (2 * scale * (u - v) ^ (2 * i + 1)) / ((2 * i + 1) * (u + v) ^ (2 * i + 1))
  have hround (i : ℕ) :
      2 * (scale : ℝ) * (t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ≤ (term i : ℝ) + 1 := by
    let A : ℕ := 2 * scale * (u - v) ^ (2 * i + 1)
    let B : ℕ := (2 * i + 1) * (u + v) ^ (2 * i + 1)
    have hB : 0 < B := by dsimp [B]; positivity
    have hBR : 0 < (B : ℝ) := by exact_mod_cast hB
    have hf : (A : ℝ) / (B : ℝ) ≤ (term i : ℝ) + 1 := by
      apply (div_le_iff₀ hBR).2
      have h := (Nat.lt_mul_div_succ A hB).le
      simpa [term, A, B, Nat.cast_mul, Nat.cast_add, mul_comm] using
        (show (A : ℝ) ≤ ((B * (A / B + 1) : ℕ) : ℝ) by exact_mod_cast h)
    have heq : 2 * (scale : ℝ) * (t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) =
        (A : ℝ) / (B : ℝ) := by
      dsimp [t, A, B]
      push_cast [Nat.cast_sub hvu]
      rw [div_pow]
      field_simp [hpos.ne']
    exact heq.le.trans hf
  have hsum : 2 * (scale : ℝ) * (∑ i ∈ range 16, t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) ≤
      (∑ i ∈ range 16, (term i : ℝ)) + 16 := by
    rw [mul_sum]
    calc
      _ ≤ ∑ i ∈ range 16, ((term i : ℝ) + 1) := sum_le_sum (fun i _ => hround i)
      _ = _ := by simp [sum_add_distrib]
  have hseries := Real.log_div_le_sum_range_add ht0 ht1 16
  rw [htRatio] at hseries
  have hscaled : Real.log ((u : ℝ) / (v : ℝ)) * (scale : ℝ) ≤
      2 * (scale : ℝ) * (∑ i ∈ range 16, t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)) +
        2 * (scale : ℝ) * (t ^ (33 : ℕ) / (1 - t ^ 2)) := by
    calc
      _ = (2 * (scale : ℝ)) * (1 / 2 * Real.log ((u : ℝ) / (v : ℝ))) := by ring
      _ ≤ _ := by
        rw [← mul_add]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_one] using hseries
  apply (le_div_iff₀ hscale).2
  change _ ≤ ((17 + ∑ i ∈ range 16, term i : ℕ) : ℝ)
  push_cast
  linarith only [hscaled, hsum, htail]

def upper (a b : ℕ) : ℚ := (roundedUp a b : ℚ) / scale
def lower (a b : ℕ) : ℚ := 0.6931471803 - upper (2*b) a

theorem log_bounds (a b : ℕ) (hb : 0 < b) (hlo : b ≤ a) (hhi : a ≤ 2*b) :
    (lower a b : ℝ) ≤ Real.log ((a:ℝ)/b) ∧ Real.log ((a:ℝ)/b) ≤ (upper a b : ℝ) := by
  have bpos : 0 < (b:ℝ) := by exact_mod_cast hb
  have apos : 0 < (a:ℝ) := by exact_mod_cast hb.trans_le hlo
  constructor
  · have u := log_le_roundedUp (2*b) a (by omega) hhi (by omega)
    have ratio : Real.log ((2*b:ℕ)/ (a:ℝ)) = Real.log 2 - Real.log ((a:ℝ)/b) := by
      push_cast
      rw [Real.log_div (by positivity) apos.ne',Real.log_mul (by norm_num) bpos.ne',
        Real.log_div apos.ne' bpos.ne']
      ring
    rw [ratio] at u
    unfold lower upper
    push_cast
    linarith only [Real.log_two_gt_d9,u]
  · unfold upper
    push_cast
    exact log_le_roundedUp a b hb hlo hhi

def lowerTerm (p : ℕ) : ℚ := -upper p (p-1) + 1/(p:ℚ)
    + lower (p^2) (p^2-1)/2 + lower (p^3) (p^3-1)/3
def upperTerm (p : ℕ) : ℚ := -lower p (p-1) + 1/(p:ℚ)
    + upper (p^2) (p^2-1)/2 + upper (p^3) (p^3-1)/3

noncomputable def term (p : ℕ) : ℝ := Real.log (1 - 1/(p:ℝ)) + 1/(p:ℝ) -
  Real.log (1 - 1/(p:ℝ)^2)/2 - Real.log (1 - 1/(p:ℝ)^3)/3

private theorem signed_log_bounds {a : ℕ} (ha : 2 ≤ a) :
    -(upper a (a-1) : ℝ) ≤ Real.log (1 - 1/(a:ℝ)) ∧
    Real.log (1 - 1/(a:ℝ)) ≤ -(lower a (a-1) : ℝ) := by
  have h := log_bounds a (a-1) (by omega) (by omega) (by omega)
  have ar : 1 < (a:ℝ) := by exact_mod_cast (show 1 < a by omega)
  have iden : Real.log (1 - 1/(a:ℝ)) = -Real.log ((a:ℝ)/(a-1:ℕ)) := by
    rw [← Real.log_inv]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ a),Nat.cast_one,inv_div]
    field_simp
  rw [iden]
  exact ⟨neg_le_neg h.2,neg_le_neg h.1⟩

private theorem term_bounds (p : ℕ) (hp : p.Prime) :
    (lowerTerm p : ℝ) ≤ term p ∧ term p ≤ (upperTerm p : ℝ) := by
  have h1 := signed_log_bounds hp.two_le
  have h2 := signed_log_bounds (a:=p^2) (by nlinarith [hp.two_le])
  have p3 : 2^3 ≤ p^3 := Nat.pow_le_pow_left hp.two_le _
  have h3 := signed_log_bounds (a:=p^3) (by omega)
  push_cast at h2 h3
  unfold term lowerTerm upperTerm
  push_cast
  constructor <;> linarith only [h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

def piLo : ℕ := 3141592653589
def piHi : ℕ := 3141592653590
def piDen : ℕ := 6*10^24
private theorem piTerm :
    (lower (piLo^2) piDen : ℝ) ≤ Real.log (Real.pi^2/6) ∧
    Real.log (Real.pi^2/6) ≤ (upper (piHi^2) piDen : ℝ) := by
  have l := (log_bounds (piLo^2) piDen (by decide) (by decide) (by decide)).1
  have u := (log_bounds (piHi^2) piDen (by decide) (by decide) (by decide)).2
  have a : (3141592653589/10^12 : ℝ) < Real.pi := by linarith only [Real.pi_gt_d20]
  have b : Real.pi < (3141592653590/10^12 : ℝ) := by linarith only [Real.pi_lt_d20]
  refine ⟨l.trans (Real.log_le_log (by norm_num [piLo,piDen]) ?_),
    (Real.log_le_log (by positivity) ?_).trans u⟩
  · norm_num [piLo,piDen]
    nlinarith [sq_nonneg (Real.pi-3141592653589/10^12),
      mul_self_le_mul_self (by norm_num) a.le]
  · norm_num [piHi,piDen]
    nlinarith [mul_self_le_mul_self Real.pi_pos.le b.le]

private theorem numerics :
    (-0.25437377 : ℚ) ≤ -(upper (piHi^2) piDen)/2 +
      ∑ p ∈ (range 101).filter Nat.Prime, lowerTerm p ∧
    -(lower (piLo^2) piDen)/2 + ∑ p ∈ (range 101).filter Nat.Prime, upperTerm p
      ≤ (-0.25437368 : ℚ) := by decide +kernel

end MertensFiniteCorrection

open MertensFiniteCorrection Finset in
theorem Conjectures.Cuts.Tasked4086932a43867e5cb19d77 :
    let w := fun p : ℕ => Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ) -
      Real.log (1 - 1 / (p : ℝ)^2)/2 - Real.log (1 - 1 / (p : ℝ)^3)/3
    let c := -(Real.log (Real.pi^2/6)/2) + ∑ p ∈ (range 101).filter Nat.Prime, w p
    (-0.25437377 : ℝ) ≤ c ∧ c ≤ -0.25437368 := by
  change _ ≤ -(Real.log (Real.pi^2/6)/2) + ∑ p ∈ (range 101).filter Nat.Prime, term p ∧ _
  have L := Finset.sum_le_sum (s := (range 101).filter Nat.Prime)
    (fun p hp => (term_bounds p (mem_filter.mp hp).2).1)
  have U := Finset.sum_le_sum (s := (range 101).filter Nat.Prime)
    (fun p hp => (term_bounds p (mem_filter.mp hp).2).2)
  have lo := (Rat.cast_le (K := ℝ)).mpr numerics.1
  have hi := (Rat.cast_le (K := ℝ)).mpr numerics.2
  push_cast at lo hi
  change _ ∧ -(Real.log (Real.pi^2/6)/2) + ∑ p ∈ (range 101).filter Nat.Prime, term p ≤ _
  constructor <;> linarith only [L,U,lo,hi,piTerm.1,piTerm.2]

