import Mathlib

/-!
For a word of length B + 1, choose its initial bit and exactly K of its B
adjacent gaps in which to change bit.  A complete 16-bit window fixes 15
of those choices.  We bound its expected loss (one minus its cosine) and
then sum over all window positions.  The final 15 positions cost at most
one each in the lower bound on the real part.

The fixed-transition construction and the Taylor certificate are due to
Li2O0577 in goldbach-proofs Discussion 4202, linked from PR 4223.
-/

-- Encode the family and bound the multiplicity of each window.
namespace DyadicWord
open Finset

def changes (B k : ℕ) : Finset ℕ :=
  (range B).filter fun i => k.testBit i ≠ k.testBit (i+1)

def family (B K : ℕ) := (range (2^(B+1))).filter fun k => (changes B k).card = K

def bitAt (S : Finset ℕ) (b : Bool) : ℕ → Bool
  | 0 => b
  | i+1 => if i ∈ S then !(bitAt S b i) else bitAt S b i

def pack : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | n+1, f => Nat.bit (f 0) (pack n (fun i => f (i+1)))

private theorem pack_lt (n : ℕ) (f : ℕ → Bool) : pack n f < 2^n := by
  induction n generalizing f with
  | zero => simp [pack]
  | succ n ih =>
    have h := ih (fun i => f (i+1))
    cases h0 : f 0 <;> simp [pack, h0, pow_succ] <;> omega

private theorem pack_bit (n i : ℕ) (f : ℕ → Bool) (hi : i < n) :
    (pack n f).testBit i = f i := by
  induction n generalizing i f with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => simp [pack]
    | succ i => simpa only [pack, Nat.testBit_bit_succ] using ih i (fun l => f (l+1)) (by omega)

private theorem pack_changes (B : ℕ) (S : Finset ℕ) (b : Bool) (hS : S ⊆ range B) :
    changes B (pack (B+1) (bitAt S b)) = S := by
  ext i
  by_cases hi : i < B
  · simp only [changes, mem_filter, mem_range, hi, true_and, pack_bit _ _ _ (by omega : i < B+1),
      pack_bit _ _ _ (by omega : i+1 < B+1)]
    by_cases hh : i ∈ S <;> simp [bitAt, hh]
  · have hn : i ∉ S := fun h => hi (mem_range.mp (hS h))
    simp [changes, hi, hn]

theorem family_lower (B K : ℕ) : 2 * B.choose K ≤ (family B K).card := by
  classical
  let D := (univ : Finset Bool) ×ˢ (range B).powersetCard K
  let f (x : Bool × Finset ℕ) := pack (B+1) (bitAt x.2 x.1)
  have hf {x} (hx : x ∈ D) : x.2 ⊆ range B ∧ x.2.card = K := by
    exact mem_powersetCard.mp (mem_product.mp hx).2
  have hm : Set.MapsTo f D (family B K) := by
    intro x hx
    exact mem_filter.mpr ⟨mem_range.mpr (pack_lt _ _), (congrArg Finset.card (pack_changes B x.2 x.1 (hf hx).1)).trans (hf hx).2⟩
  have hinj : Set.InjOn f D := by
    intro x hx y hy he
    apply Prod.ext
    · simpa only [f, pack_bit _ _ _ (by omega : 0 < B+1), bitAt] using congrArg (fun k : ℕ => k.testBit 0) he
    · simpa only [f, pack_changes B x.2 x.1 (hf hx).1, pack_changes B y.2 y.1 (hf hy).1] using congrArg (changes B) he
  simpa [D, card_product, card_powersetCard] using card_le_card_of_injOn f hm hinj

def window (s k : ℕ) := (k / 2^s) % 65536

theorem window_bit (s k i : ℕ) (hi : i < 16) :
    (window s k).testBit i = k.testBit (s+i) := by
  change ((k / 2^s) % 2^16).testBit i = _
  rw [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]; simp [hi, Nat.add_comm]

end DyadicWord
namespace DyadicWord
open Finset

private theorem local_changes (B s k : ℕ) (hs : s+15 ≤ B) :
    changes B k ∩ Ico s (s+15) =
      (changes 15 (window s k)).image (fun i => s+i) := by
  ext l
  constructor
  · intro hl
    obtain ⟨hc, hp⟩ := mem_inter.mp hl
    obtain ⟨hs₀, hs₁⟩ := mem_Ico.mp hp
    have h := (mem_filter.mp hc).2
    refine mem_image.mpr ⟨l-s, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, by omega⟩
    rw [window_bit _ _ _ (by omega), window_bit _ _ _ (by omega)]
    simpa only [show s + (l-s) = l by omega, show s + (l-s+1) = l+1 by omega] using h
  · intro hl
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hl
    obtain ⟨hir, hd⟩ := mem_filter.mp hi
    have hil := mem_range.mp hir
    rw [window_bit _ _ _ (by omega), window_bit _ _ _ (by omega)] at hd
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), hd⟩,
      mem_Ico.mpr ⟨by omega, by omega⟩⟩

private theorem word_unique (B s k l : ℕ) (hs : s ≤ B)
    (hk : k < 2^(B+1)) (hl : l < 2^(B+1)) (hc : changes B k = changes B l)
    (hb : k.testBit s = l.testBit s) : k = l := by
  have pair (i : ℕ) (hi : i < B) :
      (k.testBit i = l.testBit i) ↔ (k.testBit (i+1) = l.testBit (i+1)) := by
    have h : i ∈ changes B k ↔ i ∈ changes B l := hc ▸ Iff.rfl
    simp only [changes, mem_filter, mem_range, hi, true_and] at h
    have rule : ∀ a b c d : Bool, ((a ≠ c) ↔ (b ≠ d)) → ((a = b) ↔ (c = d)) := by decide
    exact rule _ _ _ _ h
  have first (i : ℕ) (hi : i ≤ B) :
      (k.testBit 0 = l.testBit 0) ↔ (k.testBit i = l.testBit i) := by
    induction i with
    | zero => rfl
    | succ i ih => exact (ih (by omega)).trans (pair i (by omega))
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i ≤ B
  · exact (first i hi).mp ((first s hs).mpr hb)
  · have hpow : 2^(B+1) ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (hk.trans_le hpow), Nat.testBit_lt_two_pow (hl.trans_le hpow)]

theorem fiber_bound (B K s a : ℕ) (hs : s+15 ≤ B) :
    (((family B K).filter (fun k => window s k = a)).card) ≤
      (B-15).choose (K - (changes 15 a).card) := by
  classical
  let I := Ico s (s+15)
  let F := (family B K).filter (fun k => window s k = a)
  let U := (range B \ I).powersetCard (K - (changes 15 a).card)
  have hI : I ⊆ range B := fun i hi => mem_range.mpr ((mem_Ico.mp hi).2.trans_le hs)
  have local_eq {k} (hk : k ∈ F) : changes B k ∩ I = (changes 15 a).image (fun i => s+i) := by
    simpa only [(mem_filter.mp hk).2] using local_changes B s k hs
  have maps : Set.MapsTo (fun k => changes B k \ I) F U := by
    intro k hk
    obtain ⟨hkf, -⟩ := mem_filter.mp hk
    have hh := (mem_filter.mp hkf).2
    apply mem_powersetCard.mpr
    refine ⟨fun i hi => mem_sdiff.mpr ⟨(mem_filter.mp (mem_sdiff.mp hi).1).1, (mem_sdiff.mp hi).2⟩, ?_⟩
    rw [card_sdiff, inter_comm I, local_eq hk, card_image_of_injective _ (by intro x y he; simpa using he), hh]
  have hinj : Set.InjOn (fun k => changes B k \ I) F := by
    intro k hk l hl he
    change changes B k \ I = changes B l \ I at he
    have info {x} (hx : x ∈ F) : x < 2^(B+1) :=
      mem_range.mp (mem_filter.mp (mem_filter.mp hx).1).1
    apply word_unique B s k l (by omega) (info hk) (info hl)
    · calc
        changes B k = _ := (sdiff_union_inter (changes B k) I).symm
        _ = (changes B l \ I) ∪ (changes B l ∩ I) := by rw [he, local_eq hk, local_eq hl]
        _ = _ := sdiff_union_inter _ _
    · have hwin := (mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm
      have hh := congrArg (fun x : ℕ => x.testBit 0) hwin
      simpa only [window_bit _ _ 0 (by decide), Nat.add_zero] using hh
  have hcard := card_le_card_of_injOn _ maps hinj
  simpa [F, U, card_powersetCard, card_sdiff_of_subset hI, I, Nat.card_Ico] using hcard
end DyadicWord

-- Compare sampling 15 gaps without replacement to independent sampling.
namespace GBSampling

private theorem falling_defect (n k : ℕ) :
    n^(k+1) ≤ n.descFactorial (k+1) + (k+1).choose 2 * n^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      n^((k+1)+1) = n^(k+1)*n := pow_succ _ _
      _ ≤ (n.descFactorial (k+1) + (k+1).choose 2 * n^k)*n :=
        Nat.mul_le_mul_right _ ih
      _ = n.descFactorial (k+1+1) + (k+1)*n.descFactorial (k+1) +
          (k+1).choose 2 * n^(k+1) := by
            rw [Nat.add_mul, Nat.descFactorial_mul_self, pow_succ, Nat.mul_assoc]
      _ ≤ n.descFactorial (k+1+1) + (k+1)*n^(k+1) +
          (k+1).choose 2 * n^(k+1) := by
            gcongr
            exact Nat.descFactorial_le_pow _ _
      _ = _ := by rw [Nat.choose_succ_succ (k+1) 1, Nat.choose_one_right]; ring

private theorem pattern_identity {B K m c : ℕ}
    (hK : K ≤ B) (hc : c ≤ K) (hm : c ≤ m) (hf : m-c ≤ B-K) :
    (B-m).choose (K-c) * B.descFactorial m =
    B.choose K * K.descFactorial c * (B-K).descFactorial (m-c) := by
  have hr : K-c ≤ B-m := by omega
  have hrel : B-m-(K-c) = (B-K)-(m-c) := by omega
  apply Nat.eq_of_mul_eq_mul_right
       (Nat.mul_pos (Nat.factorial_pos (K-c)) (Nat.factorial_pos ((B-K)-(m-c))))
  calc
    (B-m).choose (K-c) * B.descFactorial m *
      ((K-c).factorial * ((B-K)-(m-c)).factorial) =
        ((B-m).choose (K-c) * (K-c).factorial * (B-m-(K-c)).factorial) *
          B.descFactorial m := by rw [hrel]; ring
    _ = B.factorial := by
      rw [Nat.choose_mul_factorial_mul_factorial hr, Nat.factorial_mul_descFactorial (by omega)]
    _ = B.choose K * K.descFactorial c * (B-K).descFactorial (m-c) *
          ((K-c).factorial * ((B-K)-(m-c)).factorial) := by
      rw [← Nat.choose_mul_factorial_mul_factorial hK,
          ← Nat.factorial_mul_descFactorial hc, ← Nat.factorial_mul_descFactorial hf]
      ring

private theorem falling15_lower (B : ℕ) (hB : 2000000 ≤ B) :
    (B:ℝ)^15 ≤ (10001/10000:ℝ) * (B.descFactorial 15 : ℝ) := by
  have hi := falling_defect B 14
  change B^15 ≤ B.descFactorial 15 + 105*B^14 at hi
  have h : (B:ℝ)^15 ≤ (B.descFactorial 15 : ℝ) + 105*(B:ℝ)^14 := by
    exact_mod_cast hi
  have hb : (2000000:ℝ) ≤ B := by exact_mod_cast hB
  have hmul := mul_le_mul_of_nonneg_right hb (show (0:ℝ) ≤ (B:ℝ)^14 by positivity)
  nlinarith only [h,hmul]

theorem pattern_probability_le (t c : ℕ) (ht : 2000 ≤ t) (hc : c ≤ 15) :
    (((1000*t-15).choose (85*t-c) : ℕ) : ℝ) / ((1000*t).choose (85*t) : ℝ) ≤
    (10001/10000 : ℝ) * ((17:ℝ)^c * (183:ℝ)^(15-c) / 200^15) := by
  let B := 1000*t
  let K := 85*t
  have hKB : K ≤ B := by dsimp [K,B]; omega
  have hCK : c ≤ K := by dsimp [K]; omega
  have hB : 2000000 ≤ B := by dsimp [B]; omega
  have hFK : 15-c ≤ B-K := by dsimp [B,K]; omega
  have hBpos : (0:ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hpos : (0:ℝ) < B.choose K := by exact_mod_cast Nat.choose_pos hKB
  have hip := pattern_identity hKB hCK hc hFK
  have hi : (((B-15).choose (K-c) : ℕ) : ℝ) * (B.descFactorial 15 : ℝ) =
      (B.choose K : ℝ) * (K.descFactorial c : ℝ) * ((B-K).descFactorial (15-c) : ℝ) := by
    exact_mod_cast hip
  have hu : (K.descFactorial c : ℝ) * ((B-K).descFactorial (15-c) : ℝ) ≤
      (K:ℝ)^c * ((B-K : ℕ):ℝ)^(15-c) := by
    exact_mod_cast Nat.mul_le_mul (Nat.descFactorial_le_pow K c)
      (Nat.descFactorial_le_pow (B-K) (15-c))
  have hKreal : (K:ℝ) = (B:ℝ)*(17/200) := by dsimp [K,B]; push_cast; ring
  have hFreal : ((B-K : ℕ):ℝ) = (B:ℝ)*(183/200) := by
    rw [Nat.cast_sub hKB,hKreal]; ring
  have hscale : (K:ℝ)^c * ((B-K : ℕ):ℝ)^(15-c) =
      (B:ℝ)^15 * ((17:ℝ)^c * (183:ℝ)^(15-c) / 200^15) := by
    rw [hFreal,hKreal, mul_pow,mul_pow, div_pow,div_pow]
    have hn : c + (15-c) = 15 := by omega
    have hpow (z : ℝ) : z^c * z^(15-c) = z^15 := by rw [←pow_add,hn]
    field_simp
    rw [hpow B,hpow 200,mul_comm]
  change _ / (B.choose K : ℝ) ≤ _
  apply (div_le_iff₀ hpos).mpr
  apply (le_of_mul_le_mul_right _ (pow_pos hBpos 15))
  calc
    (((B-15).choose (K-c) : ℕ):ℝ) * (B:ℝ)^15 ≤
        (((B-15).choose (K-c) : ℕ):ℝ) * ((10001/10000 : ℝ) * (B.descFactorial 15 : ℝ)) :=
      mul_le_mul_of_nonneg_left (falling15_lower B hB) (by positivity)
    _ = (10001/10000:ℝ) * ((B.choose K : ℝ) *
          ((K.descFactorial c : ℝ) * ((B-K).descFactorial (15-c) : ℝ))) := by
      linear_combination (10001/10000:ℝ)*hi
    _ ≤ (10001/10000:ℝ) * ((B.choose K : ℝ) *
          ((K:ℝ)^c * ((B-K : ℕ):ℝ)^(15-c))) := by gcongr
    _ = _ := by rw [hscale]; ring

end GBSampling

-- On the dyadic grid the phase of a complete window uses exactly 16 bits.
private noncomputable def gbTerm (N k j : ℕ) : ℝ :=
  (Complex.exp ((2 * Real.pi *
    (⌊(65536 : ℝ) * 2 ^ j * ((k : ℝ) / 2 ^ N)⌋ : ℝ) / 65536 : ℝ) * Complex.I)).re

private lemma gbTerm_ge_neg_one (N k j : ℕ) : -1 ≤ gbTerm N k j := by
  simpa only [gbTerm, Complex.exp_ofReal_mul_I_re] using Real.neg_one_le_cos _

private lemma gbTerm_eq_window (N k j : ℕ) (hj : j + 16 ≤ N) :
    gbTerm N k j =
      Real.cos (2 * Real.pi * (((k / 2 ^ (N - j - 16)) % 65536 : ℕ) : ℝ) / 65536) := by
  let d := N - j - 16
  have hN : N = j + 16 + d := by dsimp [d]; omega
  have hp : (2 : ℝ) ^ N = 2 ^ j * 65536 * 2 ^ d := by
    calc
      (2 : ℝ) ^ N = 2 ^ (j + 16 + d) := congrArg ((2 : ℝ) ^ ·) hN
      _ = _ := by rw [pow_add, pow_add]; norm_num
  have hphase : (65536 : ℝ) * 2 ^ j * ((k : ℝ) / 2 ^ N) = k / ((2 ^ d : ℕ) : ℝ) := by
    push_cast
    rw [hp]
    field_simp
  have hf : ⌊(65536 : ℝ) * 2 ^ j * ((k : ℝ) / 2 ^ N)⌋ = ((k / 2 ^ d : ℕ) : ℤ) := by
    rw [hphase, Int.floor_div_natCast, Int.floor_natCast, Int.natCast_ediv]
  let q := k / 2 ^ d
  have hq : ((q % 65536 : ℕ) : ℝ) + 65536 * ((q / 65536 : ℕ) : ℝ) = q := by
    exact_mod_cast Nat.mod_add_div q 65536
  simp only [gbTerm, Complex.exp_ofReal_mul_I_re, hf, Int.cast_natCast]
  change Real.cos (2 * Real.pi * q / 65536) =
    Real.cos (2 * Real.pi * ((q % 65536 : ℕ) : ℝ) / 65536)
  calc
    _ = Real.cos (2 * Real.pi * ((q % 65536 : ℕ) : ℝ) / 65536 +
          ((q / 65536 : ℕ) : ℝ) * (2 * Real.pi)) := by
      congr 1
      linear_combination -(2 * Real.pi / 65536) * hq
    _ = _ := Real.cos_add_nat_mul_two_pi _ _

-- Fold the angle into [0, π] and bound the cosine by its Taylor polynomial.
namespace DyadicCert

open Finset

/-- Taylor polynomial of cosine through order fifteen. Its odd coefficients vanish. -/
private noncomputable def poly (x : ℝ) : ℝ := 1 - x^2 / 2 + x^4 / 24 - x^6 / 720 + x^8 / 40320 - x^10 / 3628800 + x^12 / 479001600 - x^14 / 87178291200

private theorem taylor_error (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 22/7) :
    poly x - 1/100000 ≤ Real.cos x := by
  rcases hx.eq_or_lt with h | h
  · subst x
    norm_num [poly]
  obtain ⟨z, _, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := Real.cos) (n := 15) h.ne Real.contDiff_cos.contDiffOn
  have H (k : ℕ) : iteratedDerivWithin k Real.cos (Set.uIcc 0 x) 0 = iteratedDeriv k Real.cos 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc h.ne)
      Real.contDiff_cos.contDiffAt Set.left_mem_uIcc
  have E (k : ℕ) : iteratedDeriv (2*k) Real.cos 0 = (-1:ℝ)^k := by
    simp
  have O (k : ℕ) : iteratedDeriv (2*k+1) Real.cos 0 = 0 := by
    simp
  have P : taylorWithinEval Real.cos 15 (Set.uIcc 0 x) 0 x = poly x := by
    rw [taylor_within_apply]
    simp only [H, sub_zero, smul_eq_mul]
    norm_num [Finset.sum_range_succ, Nat.factorial, poly, E 0, O 0, E 1, O 1, E 2, O 2, E 3, O 3, E 4, O 4, E 5, O 5, E 6, O 6, E 7, O 7]; ring
  rw [P, sub_zero] at hz
  have hv := Real.neg_one_le_cos z
  have hp : x^16 ≤ (22/7:ℝ)^16 := by gcongr
  have hm := mul_le_mul_of_nonneg_right hv (show 0 ≤ x^16 by positivity)
  norm_num [Nat.factorial] at hz
  linarith

/-- Fold the angle at π and replace π by the rational upper bound 3927/1250.
The two errors each cost at most 1/100000 in the resulting cosine bound. -/
private theorem loss_approx (a : ℕ) (ha : a < 65536) :
    1 - Real.cos (2*Real.pi*(a:ℝ)/65536) ≤
    1 - poly (3927/1250 * (min a (65536-a):ℕ) / 32768) + 1/50000 := by
  let d := min a (65536-a)
  have hd : d ≤ 32768 := by dsimp [d]; omega
  have hdr : (d:ℝ) ≤ 32768 := by exact_mod_cast hd
  have hd0 : (0:ℝ) ≤ d := by positivity
  have fold : Real.cos (2*Real.pi*(a:ℝ)/65536) = Real.cos (Real.pi*(d:ℝ)/32768) := by
    by_cases h : a ≤ 65536-a
    · dsimp [d]; rw [min_eq_left h]; congr 1; ring
    · dsimp [d]; rw [min_eq_right (by omega), Nat.cast_sub (by omega)]
      rw [← Real.cos_two_pi_sub (2*Real.pi*(a:ℝ)/65536)]
      congr 1
      push_cast
      ring
  rw [fold]
  change _ ≤ 1 - poly (3927/1250*(d:ℝ)/32768) + 1/50000
  have hdif : |Real.pi*(d:ℝ)/32768 - 3927/1250*(d:ℝ)/32768| ≤ 1/100000 := by
    have h₁ := mul_le_mul_of_nonneg_right Real.pi_gt_d6.le hd0
    have h₂ := mul_le_mul_of_nonneg_right Real.pi_lt_d4.le hd0
    rw [abs_le]
    constructor <;> linarith
  have hcos := (abs_le.mp ((Real.abs_cos_sub_cos_le _ _).trans hdif)).1
  have ht := taylor_error (3927/1250*(d:ℝ)/32768) (by positivity) (by linarith)
  linarith

end DyadicCert

-- Clear denominators. The moment table sums the integer polynomial over 16-bit windows.
namespace DyadicCert

open Finset

private def scale : ℕ :=
  24903052539070693948323139191192524233804510735483535360000000000000000000000000000000000000000000000000000000000

/-- Integer form of the cosine loss bound, with the Taylor coefficients in Horner form. -/
private def scaledLoss (a : ℕ) : ℤ :=
  let d : ℤ := (min a (65536 - a) : ℕ)
  let u := d * d
  (498061050781413878966462783823850484676090214709670707200000000000000000000000000000000000000000000000000000 + u * (114452292415289439450323619777015989586702669184185139200000000000000000000000000000000000000000000000000 + u * (-87668819037098838686397656651947409593915735019618304000000000000000000000000000000000000000000 + u * (26861224599928943254567505678707748533199845711675392000000000000000000000000000000000 + u * (-4408995827376817066233246004801993763656938112942080000000000000000000000000 + u * (450297032552329056469584023806698624857941506785280000000000000000 + u * (-31356462415028594190771984892663323056435468697600000000 + u * 1583644070397007908871486760144675141790990417)))))))

private def flips (n a : ℕ) : ℕ :=
  ((range n).filter (fun i => a.testBit i ≠ a.testBit (i+1))).card

private def weight (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | i+1 => (if a.testBit i = a.testBit (i+1) then 183 else 17) * weight a i

private theorem weight_eq (a n : ℕ) :
    weight a n = 17^(flips n a) * 183^(n - flips n a) := by
  induction n with
  | zero => simp [flips, weight]
  | succ n ih =>
    have hb : flips n a ≤ n := by
      dsimp [flips]; exact (card_le_card (filter_subset _ _)).trans_eq (card_range n)
    by_cases h : a.testBit n = a.testBit (n+1)
    · have he : flips (n+1) a = flips n a := by simp [flips, range_add_one, filter_insert, h]
      rw [weight, ite_eq_left h, ih, he, show n+1-flips n a = n-flips n a+1 by omega, pow_succ]
      ring
    · have he : flips (n+1) a = flips n a + 1 := by simp [flips, range_add_one, filter_insert, h]
      rw [weight, ite_eq_right h, ih, he, show n+1-(flips n a+1) = n-flips n a by omega, pow_succ]
      ring

private def certSum : ℕ → ℕ → ℤ
  | 0, a => (weight a 15 : ℤ) * scaledLoss a
  | n+1, a => certSum n a + certSum n (a+2^n)

private theorem certSum_eq (m a : ℕ) :
    certSum m a = ∑ i ∈ range (2^m), (weight (a+i) 15 : ℤ) * scaledLoss (a+i) := by
  induction m generalizing a with
  | zero => simp [certSum]
  | succ n ih =>
    rw [certSum, pow_succ, Nat.mul_two, sum_range_add, ih, ih]
    simp only [Nat.add_assoc]


private theorem wt_congr (n x y : ℕ) (h : ∀ i ≤ n, x.testBit i = y.testBit i) :
    weight x n = weight y n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [weight, h n (by omega), h (n+1) (by omega), ih (fun i hi => h i (by omega))]

private def put (n : ℕ) (b : Bool) (r : ℕ) : ℕ := if b then 2^n+r else r

private theorem put_small (n : ℕ) (b : Bool) (r : ℕ) (hr : r < 2^n) : put n b r < 2^(n+1) := by
  cases b <;> simp [put,pow_succ] <;> omega

private theorem put_bit (n : ℕ) (b : Bool) (r : ℕ) (hr : r < 2^n) : (put n b r).testBit n = b := by
  cases b <;> simp [put, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]

private theorem put_bit_lt (n i : ℕ) (b : Bool) (r : ℕ) (hi : i < n) :
    (put n b r).testBit i = r.testBit i := by
  cases b <;> simp [put, Nat.testBit_two_pow_add_gt hi]

private def edge (b c : Bool) : ℕ := if c = b then 183 else 17

private theorem wt_extend (n : ℕ) (b c : Bool) (r : ℕ) (hr : r < 2^n) :
    weight (put (n+1) b (put n c r)) (n+1) = edge b c * weight (put n c r) n := by
  rw [weight, put_bit_lt _ n _ _ (by omega), put_bit _ c _ hr,
    put_bit _ b _ (put_small n c r hr), ← show edge b c = if c = b then 183 else 17 from rfl]
  rw [wt_congr n (put (n+1) b (put n c r)) (put n c r)
    (fun i hi => put_bit_lt _ _ _ _ (by omega))]

/-- Unnormalized kth moment of the n low bits, conditional on the next bit b.
Splitting at the highest low bit only requires the two moments of shorter words. -/
private def moments (n : ℕ) (b : Bool) (k : ℕ) : ℕ :=
  ∑ r ∈ range (2^n), weight (put n b r) n * r^k

private theorem moments_step (n : ℕ) (b : Bool) (k : ℕ) :
    moments (n+1) b k = edge b false * moments n false k +
      edge b true * ∑ j ∈ range (k+1), k.choose j * (2^n)^(k-j) * moments n true j := by
  unfold moments
  rw [pow_succ, Nat.mul_two, sum_range_add, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro r hr
    have he := wt_extend n b false r (mem_range.mp hr)
    dsimp [put] at he ⊢
    rw [he]; ring
  · calc
      _ = ∑ r ∈ range (2^n), ∑ j ∈ range (k+1),
              edge b true * (k.choose j * (2^n)^(k-j) * (weight (put n true r) n * r^j)) := by
          apply sum_congr rfl
          intro r hr
          have he := wt_extend n b true r (mem_range.mp hr)
          change weight (put (n+1) b (put n true r)) (n+1) * (2^n+r)^k = _
          rw [he, Nat.add_comm (2^n) r, add_pow, mul_sum]
          apply sum_congr rfl
          intro j _
          simp only [Nat.cast_id]
          ring
      _ = _ := by
          rw [sum_comm]
          apply sum_congr rfl
          intro j _
          rw [← mul_sum, ← mul_sum]

/-- Integer certificate indexed by word length, next bit, and moment order.
The base case and every recurrence entry are checked below in the kernel. -/
private def momentTable : Array (Array (Array ℕ)) := #[
  #[#[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
  #[#[200, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17, 17], #[200, 183, 183, 183, 183, 183, 183, 183, 183, 183, 183, 183, 183, 183, 183]],
  #[#[40000, 13022, 32266, 89420, 259726, 768332, 2289526, 6843860, 20488366, 61384892, 184000486, 551699300, 1654499806, 4962309452, 14884554646], #[40000, 106978, 314134, 929380, 2762674, 8237668, 24612874, 73638940, 220518034, 660757108, 1980677914, 5938847500, 17810170594, 53417768548, 160227819754]],
  #[#[8000000, 6921652, 36673964, 227060704, 1499601620, 10189807072, 70158975044, 486161466304, 3379940517140, 23541505318432, 164151812727524, 1145467745643904, 7997537760644660, 55861368709837792, 390312565011155204], #[8000000, 49078348, 331770836, 2269609696, 15635540780, 108189768928, 750769421756, 5220019540096, 36344052993260, 253297499697568, 1766686641941276, 12329545943298496, 86087910635553740, 601321513248618208, 4201570895872185596]],
  #[#[1600000000, 3188994232, 34404750280, 445321702624, 6206466745720, 89450381193952, 1310366621583640, 19356214579739104, 287211663840469240, 4272789136628415712, 63668328083541098200, 949749777274549948384, 14178758031096178949560, 211802282120221505397472, 3165440044478424835582360], #[1600000000, 20811005768, 298734923320, 4350320953376, 63882155334280, 943006950806048, 13968694928137960, 207414512200644896, 3085148262213930760, 45949343178025184288, 685050247006203951400, 10221539983063956643616, 152614541260996902650440, 2279880178268198169002528, 34074268809552551444635240]],
  #[#[320000000000, 1372573042512, 29658950135472, 782336716523712, 22334522584703952, 661071562364912832, 19919449001310359952, 605851767074186684352, 18522637630724122149072, 568021736965025166651072, 17452881244328620311458832, 536960530227140936030342592, 16536205286357469891639930192, 509626621552452098720601707712, 15715498405815091354009862304912], #[320000000000, 8547426957488, 252079421499728, 7551937564513088, 228303702178995248, 6941549603361167168, 211867940906071707248, 6484014532384048528448, 198829838775471222030128, 6106242427368443652676928, 187750792895280232502160368, 5778367372880075072662726208, 177979696037457917472293049008, 5485567053431314277170053908288, 169166536214981472592897851026288]],
  #[#[64000000000000, 570567125056992, 24583098570033696, 1307582919035971200, 75480423452149553376, 4523192728033618783872, 276153836744558144090976, 17027112311343877958167680, 1055677509636452847055324896, 65668100049770228345910137472, 4093504391281183085134364521056, 255545041440240188578407475013760, 15969954824038911124248963576693216, 998849554370237763241974019451129472, 62515532120247677114433351511008503136], #[64000000000000, 3461432874943008, 206707640812852704, 12547887952646793600, 768906549525364533024, 47399805491743360672128, 2933813318671213906955424, 182108663194650980495541120, 11327884276125342950339721504, 705788469849453703045219974528, 44031286349832046728544016125344, 2749818558468259613574844738439040, 171879572399036098102185758167793184, 10751326402701057015506101269580038528, 672930624909308932406373541122707823264]],
  #[#[12800000000000000, 232890142759460672, 20001262868010647744, 2135587662835824045824, 247809929332772840448320, 29870010156614031615418112, 3669527889507550387572674624, 455384171821831009386491519744, 56835790093272652406425145963840, 7117921433452792580582545949103872, 893392799609275986755234464830384704, 112303739086947830458276097686091934464, 14133022353692482530044429077129600612160, 1780151507277384999617715643205309752024832, 224382210882657248280210400403262338432465984], #[12800000000000000, 1392709857240539328, 167298366607107637056, 20435340552174209208576, 2520192177016827331174080, 312708344711155978940997888, 38962076258821317090704650176, 4868823724391673998206869478656, 609758887867586185638444995578560, 76494084788247568862677746595408128, 9609116351923939429281261538933020096, 1208417656325625705859042514610845127936, 152106640483856835949929732677880629250240, 19160856707444491943311901715830935713063168, 2415286416227052012494017887442755438284538816]],
  #[#[2560000000000000000, 94147763698070471552, 16130535035877605522560, 3450403417449594825480704, 802666170047131051217031040, 194018766684635632887487150592, 47806588798102267965002231351680, 11900808081610935368644977173533184, 2979735472410491641434747282835703680, 748673770137312710457342935720063601152, 188532082839803196031403696277083699209600, 47550587628725797182227069098269805451723264, 12006825205720571730462164656096488379496321920, 3034535854981935160447361031108376544964030413312, 767494466103438826151344040266851944682115073806720], #[2560000000000000000, 558652236301929528448, 134579175549861665031040, 32971900881595676161271296, 8156507027339819062931320960, 2030220586240513821692839249408, 507457495536533197925176208225920, 127219360260606846055905841429474816, 31964979012942548136627378700760840320, 8045352055502211370589318630074199438848, 2027747677572762171234506037321996951952000, 511648767759949071551549345796482126202420736, 129222340959101296250269332765899804159264894080, 32662409437156030892934103560792852437920608306688, 8261413988678117703826650375502383386305358860938880]],
  #[#[512000000000000000000, 37867248773879698277632, 12954369680685244731767552, 5546359777551842178844613632, 2583396790571179191421748448512, 1250484702320491766371528873679872, 617073615939338249517517788596218112, 307655337146788872992245647448527219712, 154284213449765810351678682519030246071552, 77643395287825687268082312613520883683556352, 39162876963487573961864904524504447668203606272, 19784721611365386106417871296166392120387867528192, 10006748297805038132361745473192837130248615699752192, 5065856855700298073040350727952351866594086924709010432, 2566470395068646009391352077853723603628841754942588082432], #[512000000000000000000, 223764751226120301722368, 107947993433780193092027648, 52966496813685915913094407168, 26241946813468296537045560914688, 13082192792395299425536777087280128, 6549252527576582609721628307778361088, 3288577639385463570784820014171716441088, 1655004931977830292462445017128964098171648, 834346198147267175768934083694612682501915648, 421208659951055562877237348545171455556911836928, 212883845610034821235765912264963952969998973252608, 107696253641264238543573416336923928907135140892171008, 54526532823692302771709254754649858440319123612472173568, 27625800087134563855858188566182032939971446760826072704768]],
  #[#[102400000000000000000000, 15190155296464029914086912, 10382763705283965280860914176, 8893971328395940190380325447680, 8289735666822562443583580891147776, 8030050229823943249087910365521651712, 7930197495101298140209554818892104766976, 7912793923578083459731270439128910403635200, 7941693444396419731207786374035672760018750976, 7998859152300343036238317204609729341343237629952, 8074846693696349187334943447521082383485654697739776, 8164491707470936567716436809431798742687717030571755520, 8264839796498272376997048370367338304250757389182707826176, 8374116106156518399811189921362270866840822965639500171323392, 8491198540693929643471122106028576923322556924642469339828696576], #[102400000000000000000000, 89565044703535970085913088, 86468275568718560076639092224, 84909271087160934970703434373120, 84191344328327398707093720858202624, 83999005878867134584679578722605324288, 84161135150255972339668643604462395943424, 84578066518912698973381172639135264715929600, 85188686143412505053373480834640959465520935424, 85953733185141586047900689156753622125148142082048, 86846866907720241989809455062714384030311202938714624, 87849713512334356533727933105822732099615019964276193280, 88949026983276277513203849519265465146186138128188456436224, 90135003587001977486436636233242797091170569354478128953284608, 91400242713521932100453150147896754902611025862547517368489101824]],
  #[#[20480000000000000000000000, 6084983379213028965738427392, 8313664139933489502211561933824, 14245646924165952632593084403871744, 26562441599633603400207172597653918720, 51475409868494890759040430687615052541952, 101701569428604590840082861119609327305442304, 203020928168337696363507499642384658626906435584, 407657072065250496049539288997471032098815615472640, 821454296835426836612659676322520280089881688222298112, 1659071343458003763900335135891161218051489110780323881984, 3356115118236916793290776933776767939537675843668394107777024, 6797047142312396498868169493159243852564973156750553777945359360, 13778565640442687475062513274881960503191417197075869685022519324672, 27952080452536262368806965393716233760100643797089422747231703724196864], #[20480000000000000000000000, 35837576620786971034261572608, 69217222505435348916478440190976, 135980796412919065731994567120326656, 269747505211437667594761041163797703680, 538435431664965299590275305394013869314048, 1079300273446898648557659197935369942272490496, 2170007358620176827274046720939841923724893474816, 4372798821505110567175858316407012619908860888181760, 8827092599825102335959624037401656955430338438550949888, 17843645349563762941220106455624988409899457855107900578816, 36111647383098102239891999598769141012772791010935361143525376, 73152072609524989214703453837779142905158174267060616203774807040, 148305852443899259501503893988118208511250013631907348291378417635328, 300879342060152057354559495635067684079091970939850954868312909929511936]],
  #[#[4096000000000000000000000000, 2435822440949362808312578947072, 6653824336098867877542551140976640, 22804897249454961836438042210858409984, 85054488854358346558038196797572044584960, 329699801909063497943780100666745766437036032, 1302986260790662267328185717597934579246987089920, 5202938757648449665537388097678307247673700248920064, 20897785468592742292552265334907742467842077342517688320, 84233965469618587333906470155592787665468407496113695137792, 340304994060077227473924985761501891839798764343413083756288000, 1377019834299957339664761466908382601790761971293992697758854815744, 5578587557466876755563297061392443160125647497768696314363302144686080, 22620857448763849554189700926823653504701522730394977049270807877471281152, 91795348326453392307519042939214651124320591870495432147226114463026652026880], #[4096000000000000000000000000, 14337297559050637191687421052928, 55390364944723586477462529564456960, 217667101103996964039180666022267478016, 863711670543514222778477169630210238679040, 3448592949513211161794800948422685618446163968, 13827646683509501323833366784191235196215173703680, 55611617519675145722004327816882532685757285405351936, 224162383879994442533424697170200049020554086779237959680, 905149611663839135948784925718798380557749088219989759582208, 3660043102611254523692163603990779979661403790374511033795225600, 14816659214998042795359652626472507496006869994634757235617190240256, 60038580061841980864960055235743777141593431469580429831944500385105920, 243479968514383633599561364362823677074804276741843404773118534937392078848, 988095337333526269903843556860306457458225468878035336123951226715896116766720]],
  #[#[819200000000000000000000000000, 974702237197594226179888105213952, 5324186569342021729570306866909458432, 36497074033220066775761482264746382180352, 272259429560343972317550476512141486883459072, 2110878048831759816553043451954952054458357235712, 16685713961356980110982781934047140240477113955356672, 133264753045843067146714354123901257627661075405804060672, 1070604938441617392352909729047864697069975521819157252984832, 8631358349419647491698578555235032310657665019797742126193426432, 69746679591278152652623274482635637162979877988257434892880721088512, 564493594879865090569748473678999685252420720565918669716086656849723392, 4574113326679433170797930518445211596963495232991611739012244632984654139392, 37098450523278624941388075927395171989752743569192615883339754719598041086410752, 301114449658172150629373433880651909480651371660226757045150762904662358420052938752], #[819200000000000000000000000000, 5735364962802405773820111894786048, 44318774954771033116291379927294496768, 348343644670433381587918132532240513384448, 2764686269386955872257933474590735307026608128, 22079097030166537546910203080330603912951163404288, 177072147710004551354973725182727955057430110732054528, 1424394837684432515232522677637118255602306467705764528128, 11483935132779923750380573247449429559639597854419658237882368, 92749530017070832581256128282285013664697596911418578494989549568, 750137896435359257145760289458531749295072726639700545353909599858688, 6073918282618620764152182388385622594047855209771538588263427307271569408, 49228089980907551173396269612531499595964909184737589854211994482646360567808, 399309731370158200262871693920149760519317410741623505494890548403818204251701248, 3241229216581239136032395809878453971090698445304199770053841276738414065060140904448]],
  #[#[163840000000000000000000000000000, 389956782574800641545861425465516032, 4259789932389726014858887741239405715456, 58402540691142839480034108840291838481039360, 871363034604843391492628370215034751088290226176, 13512113667285585042365225536109132158955265903460352, 213623834773524396610086544832055236753254298648613707776, 3412443787840784466370004027988484369681263119916252923985920, 54830865170122710712131955181933367539369173512745162309569273856, 884139710955871175499216326043700301465066327083849182918209108344832, 14289313172907686030535463773497854783140378662646277209217009184661200896, 231309268069316589235488486435077809140644425465510012738656574559877339054080, 3748756549078463195936223337735786057552799129723659581339004269063201598943911936, 60811046141939522233480815361853852737131696065972055572238552705422958804481379827712, 987199123055031560148454552221614874427807246895717503911355924864882815287091284860297216], #[163840000000000000000000000000000, 2294233937425199358454138574534483968, 35457562560303808193967192274436307410944, 557409534622131376934762394504930973743677440, 8848260133604877691894606819361662475566251188224, 141331508817179272755486778264886280992988011771035648, 2267011532943406637644777020238573133521276262904615706624, 36473695492573033383319989444998771641084282543600093545594880, 588147308363305550758472423252318655985990327382821687167769452544, 9500647412219040754096011462233138358552547257511006790320155592327168, 153684042404686829936466045755134348362404609606768151908721708285462421504, 2488873815843230841711028080487829193128679381897973166549387003967655425310720, 40345328701112529863238728206613909853361356041040845992664857336279458946429886464, 654540575024562336375231478064615619481472975822728763227784015602100635662119039500288, 10626320148196595540692134579914746139817292268022187275732013837937948259249303492462813184]],
  #[#[32768000000000000000000000000000000, 155998095667416906496612996627275661312, 3408004808286496453839647343088109973192704, 93449730367225871058239836324259884262752190464, 2788569950326428368234181579309868898675379103416320, 86485338402215518297973411599823856936182861991146094592, 2734677301335050766343803363068500035192184075633452266307584, 87369392238247692442383834396146712345363857804224817642488397824, 2807737497528480086288791192192196246462368952963309037926218951639040, 90550323868374544971497467618549038179232975493184615403459261884164145152, 2926969867903306743315574017810442778628352400764068389864816002902395121188864, 94762776230647433988286400571751045572642082382946341798250039817507599198153539584, 3071636841713905118591933350007952003013246344706907202905725441684087225212476862709760, 99655903570186834527654584811986871849436128466145405877594189641859155058827204729108365312, 3235662942102589077845266828062525258658150373824754389621954318786394325532768609247543024697344], #[32768000000000000000000000000000000, 917710960332583093503387003372724338688, 28367050244769996903490611222116226784772096, 891902135662140713701221037284815869559596711936, 28316414597697387693488233360150991454203714142126080, 904600867873621083830741696174643684214361700963814801408, 29020802048813722369027126009006545445880096654458105272713216, 933841508579000804274868091809742981066362826034818943029355544576, 30117386901415516576188588662301866194135674225391906738342374603407360, 973020931147576870985733093657048419811234959599623577997656493082646478848, 31480063566409682285325662815413582335893425221660274055406783754482797371047936, 1019641681324034065240811358051811573913531275361983859803343169901676630917970722816, 33057946077424425395542277672743669909077254597073952507861605934497356701223431058800640, 1072647730977192842730743379854328470619761102176189353138514022618259137266651157859797106688, 34829031964346374952816876520253433218859442071137242087040457842423802791942889650684883038355456]]]

private def entry (n : ℕ) (b : Bool) (k : ℕ) : ℕ :=
  (((momentTable.getD n #[]).getD b.toNat #[]).getD k 0)

private theorem entry0 : ∀ (b : Bool) (k : Fin 15), entry 0 b k.val = 0^k.val := by decide +kernel

set_option maxHeartbeats 0 in
private theorem entrySucc : ∀ (n : Fin 15) (b : Bool) (k : Fin 15),
    entry (n.val+1) b k.val = edge b false * entry n.val false k.val +
      edge b true * ∑ j ∈ range (k.val+1), k.val.choose j * (2^n.val)^(k.val-j) * entry n.val true j := by
  decide +kernel

private theorem moments_eq_entry (n k : ℕ) (b : Bool) (hn : n ≤ 15) (hk : k < 15) :
    moments n b k = entry n b k := by
  induction n generalizing b k with
  | zero => simpa [moments, weight] using (entry0 b ⟨k,hk⟩).symm
  | succ n ih =>
    rw [moments_step, show entry (n+1) b k = _ from entrySucc ⟨n,by omega⟩ b ⟨k,hk⟩]
    rw [ih k false (by omega) hk]
    congr 2
    apply sum_congr rfl
    intro j hj
    rw [ih j true (by omega) (by have := mem_range.mp hj; omega)]



/-- Coefficients in the low fifteen bits. For a leading one the folded index
is 32768 minus those bits. `poly_entry` checks both polynomial identities. -/
private def coeffs (b : Bool) : Array ℤ :=
  if b then #[49806706933558267578371589075120531886521708220043041491313340247418958787817539570452630586819074745674663723008, -32940858366515421244911421616186840894759038659932121575793218577478063517539623070075214095609478774784, -114440792982226629634323043723803844335449336434119699034029388431661411051742790508521674604648572387328, -1655167900689921634001769749403884328048319643203366022599831539736039329082181856107207187234816, 87829178883788307108292241519256811602555910954431142420130668668722217871990673554618825310208, -11629551571694804600302295284442199577169443696912355972641156338442992738146852548902912, -26217137023371256774985643395392010395732370830096392801427611730629525407508593639424, -27676870617835311211028181519218250257898410268773873639914595566916689993924608, 5340866604140981722706983092087101391126759699048456638945031569578313908224, -24613114231052809767103827678798132805022223306406249173092297670131712, 55802974512346386152274824037280684085733623212965111649630420992, -7952043366412081687844196068373703423216610380974018439151616, 123382201002024364344710748871429730091269148919965155328, -726499884582768172210612294189890010646900435779584, 1583644070397007908871486760144675141790990417]
  else #[498061050781413878966462783823850484676090214709670707200000000000000000000000000000000000000000000000000000, 0, 114452292415289439450323619777015989586702669184185139200000000000000000000000000000000000000000000000000, 0, -87668819037098838686397656651947409593915735019618304000000000000000000000000000000000000000000, 0, 26861224599928943254567505678707748533199845711675392000000000000000000000000000000000, 0, -4408995827376817066233246004801993763656938112942080000000000000000000000000, 0, 450297032552329056469584023806698624857941506785280000000000000000, 0, -31356462415028594190771984892663323056435468697600000000, 0, 1583644070397007908871486760144675141790990417]

private def coeff (b : Bool) (k : ℕ) : ℤ := (coeffs b).getD k 0

private theorem poly_entry (b : Bool) (r : ℕ) (hr : r < 2^15) :
    scaledLoss (put 15 b r) = ∑ j ∈ range 15, coeff b j * (r:ℤ)^j := by
  have hr' : r < 32768 := hr
  cases b
  · have h : r ≤ 65536-r := by omega
    norm_num [put, scaledLoss, min_eq_left h, coeff, coeffs, sum_range_succ]; ring
  · have hd : min (put 15 true r) (65536 - put 15 true r) = 32768-r := by
      change min (32768+r) (65536-(32768+r)) = 32768-r
      omega
    simp only [scaledLoss, hd, Nat.cast_sub (by omega : r ≤ 32768)]
    norm_num [coeff, coeffs, sum_range_succ]; ring

private theorem block_sum (b : Bool) :
    ∑ r ∈ range (2^15), (weight (put 15 b r) 15 : ℤ) * scaledLoss (put 15 b r) =
    ∑ j ∈ range 15, coeff b j * (entry 15 b j : ℤ) := by
  calc
    _ = ∑ r ∈ range (2^15), ∑ j ∈ range 15,
        coeff b j * ((weight (put 15 b r) 15 : ℤ) * (r:ℤ)^j) := by
      apply sum_congr rfl
      intro r hr
      rw [poly_entry b r (mem_range.mp hr), mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [← mul_sum, ← moments_eq_entry 15 j b (by decide) (mem_range.mp hj)]
      simp only [moments, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

set_option maxHeartbeats 0 in
private theorem numerical_via_moments :
    (∑ a ∈ range 65536, (weight a 15 : ℤ) * scaledLoss a) * 10000 < 5096 * (200:ℤ)^15 * (scale:ℤ) := by
  rw [show (65536:ℕ) = 2^15 + 2^15 by decide, sum_range_add]
  change ((∑ r ∈ range (2^15), (weight (put 15 false r) 15 : ℤ) * scaledLoss (put 15 false r)) +
      ∑ r ∈ range (2^15), (weight (put 15 true r) 15 : ℤ) * scaledLoss (put 15 true r)) * 10000 < _
  rw [block_sum, block_sum]
  decide +kernel

private theorem numerical : certSum 16 0 * 10000 < 5096 * (200:ℤ)^15 * (scale:ℤ) := by
  simpa only [certSum_eq, Nat.reducePow, zero_add] using numerical_via_moments

end DyadicCert

-- Transfer the exact integer certificate to the real weighted cosine loss.
namespace DyadicCert
open Finset

private theorem scaledLoss_bound (a : ℕ) (ha : a < 65536) :
    (1 - Real.cos (2*Real.pi*(a:ℝ)/65536)) ≤ (scaledLoss a : ℝ) / (scale : ℝ) := by
  refine (loss_approx a ha).trans_eq ?_
  simp only [scaledLoss, scale, poly]
  push_cast
  ring

theorem iid_window_loss :
    (∑ a ∈ range 65536, (1 - Real.cos (2*Real.pi*(a:ℝ)/65536)) *
      ((17:ℝ)^(((range 15).filter (fun i => a.testBit i ≠ a.testBit (i+1))).card) *
       (183:ℝ)^(15-((range 15).filter (fun i => a.testBit i ≠ a.testBit (i+1))).card))) <
    5096/10000 * (200:ℝ)^15 := by
  have hw (a : ℕ) : (weight a 15 : ℝ) =
      (17:ℝ)^(flips 15 a) * (183:ℝ)^(15-flips 15 a) := by
    rw [weight_eq]; push_cast; rfl
  have hsum : ((certSum 16 0 : ℤ) : ℝ) =
      ∑ a ∈ range 65536, (weight a 15 : ℝ)*(scaledLoss a : ℝ) := by
    rw [certSum_eq, Int.cast_sum]
    norm_num only [Nat.reducePow, zero_add, Int.cast_mul, Int.cast_natCast]
  have hs : (0:ℝ) < scale := by norm_num [scale]
  have hnum : (certSum 16 0 : ℝ)*10000 < 5096*(200:ℝ)^15*(scale:ℝ) := by
    exact_mod_cast numerical
  change ∑ a ∈ range 65536, (1 - Real.cos (2*Real.pi*(a:ℝ)/65536)) *
      ((17:ℝ)^(flips 15 a)*(183:ℝ)^(15-flips 15 a)) < _
  simp_rw [← hw]
  calc
    _ ≤ ∑ a ∈ range 65536, (scaledLoss a : ℝ)/(scale:ℝ)*(weight a 15 : ℝ) :=
      sum_le_sum fun a ha => mul_le_mul_of_nonneg_right
        (scaledLoss_bound a (mem_range.mp ha)) (by positivity)
    _ = (certSum 16 0 : ℝ)/(scale:ℝ) := by
      rw [hsum, Finset.sum_div]
      apply sum_congr rfl
      intro a _
      ring
    _ < _ := (div_lt_iff₀ hs).mpr (by linarith)

end DyadicCert

-- Sum the bounds for complete windows and the final partial windows.
namespace DyadicWord
open Finset

private noncomputable def windowLoss (a : ℕ) : ℝ := 1 - Real.cos (2 * Real.pi * a / 65536)

private noncomputable def windowWeight (a : ℕ) : ℝ :=
  (17:ℝ) ^ (changes 15 a).card * 183 ^ (15 - (changes 15 a).card) / 200^15

private theorem full_window_sum (t j : ℕ) (ht : 2000 ≤ t)
    (hj : j + 16 ≤ 1000*t+1)
    (hcert : ∑ a ∈ range 65536, windowLoss a * windowWeight a ≤ 5097/10000) :
    (7451/10000 : ℝ) * (family (1000*t) (85*t)).card ≤
      ∑ k ∈ family (1000*t) (85*t), gbTerm (1000*t+1) k j := by
  classical
  let B := 1000*t
  let K := 85*t
  let F := family B K
  let s := B+1-j-16
  have hs : s+15 ≤ B := by dsimp [s,B]; omega
  have hC : (0:ℝ) < B.choose K := by
    exact_mod_cast Nat.choose_pos (show K ≤ B by dsimp [K,B]; omega)
  have hcount : 2 * (B.choose K : ℝ) ≤ F.card := by exact_mod_cast family_lower B K
  have hmaps (k : ℕ) (_ : k ∈ F) : window s k ∈ range 65536 :=
    mem_range.mpr (Nat.mod_lt _ (by decide))
  have hfiber (a : ℕ) :
      (((F.filter fun k => window s k = a).card : ℕ) : ℝ) ≤
      ((10001/10000 : ℝ) * (B.choose K : ℝ)) * windowWeight a := by
    have hc : (changes 15 a).card ≤ 15 :=
      (card_filter_le _ _).trans_eq (card_range 15)
    have hpr := (div_le_iff₀ hC).mp (GBSampling.pattern_probability_le t _ ht hc)
    calc
      _ ≤ (((B-15).choose (K-(changes 15 a).card) : ℕ) : ℝ) := by
        exact_mod_cast fiber_bound B K s a hs
      _ ≤ _ := by simpa only [B, K, windowWeight, mul_right_comm] using hpr
  have hpos (a : ℕ) : 0 ≤ windowLoss a := sub_nonneg.mpr (Real.cos_le_one _)
  have hloss : ∑ k ∈ F, windowLoss (window s k) ≤ (2549/10000 : ℝ) * F.card := by
    calc
      _ = ∑ a ∈ range 65536, (((F.filter fun k => window s k = a).card : ℕ) : ℝ) * windowLoss a := by
        simpa only [sum_const, nsmul_eq_mul] using (sum_fiberwise_of_maps_to' hmaps windowLoss).symm
      _ ≤ ∑ a ∈ range 65536, ((10001/10000 : ℝ) * (B.choose K : ℝ)) * (windowLoss a * windowWeight a) := by
        apply sum_le_sum
        intro a ha
        simpa only [mul_assoc, mul_comm (windowWeight a) (windowLoss a)] using
          mul_le_mul_of_nonneg_right (hfiber a) (hpos a)
      _ = _ := (mul_sum _ _ _).symm
      _ ≤ ((10001/10000 : ℝ) * (B.choose K : ℝ)) * (5097/10000) := by gcongr
      _ ≤ _ := by linarith
  have hphase (k : ℕ) : gbTerm (B+1) k j = 1 - windowLoss (window s k) := by
    rw [gbTerm_eq_window _ _ _ hj]
    dsimp [windowLoss, window, s]
    ring
  change _ * (F.card : ℝ) ≤ ∑ k ∈ F, gbTerm (B+1) k j
  simp_rw [hphase]
  rw [sum_sub_distrib]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  linarith

private theorem assemble_dyadic (t : ℕ) (ht : 2000 ≤ t)
    (hcert : ∑ a ∈ range 65536, windowLoss a * windowWeight a ≤ 5097/10000) :
    ∃ F ⊆ range (2^(1000*t+1)), 2 * (1000*t).choose (85*t) ≤ F.card ∧
      (745/1000 : ℝ) * (1000*t+1 : ℕ) * F.card <
        ∑ k ∈ F, ∑ j ∈ range (1000*t+1), gbTerm (1000*t+1) k j := by
  let N := 1000*t+1
  let F := family (1000*t) (85*t)
  have hc := family_lower (1000*t) (85*t)
  refine ⟨F, filter_subset _ _, hc, ?_⟩
  have hF : (0 : ℝ) < F.card := by
    exact_mod_cast (show 0 < F.card from
      (Nat.mul_pos (by decide : 0 < 2) (Nat.choose_pos (by omega : 85*t ≤ 1000*t))).trans_le hc)
  have hn : 2000001 ≤ N := by dsimp [N]; omega
  let G : ℕ → ℝ := fun j => ∑ k ∈ F, gbTerm N k j
  have hmain (j : ℕ) (hj : j ∈ range (N-15)) : (7451/10000 : ℝ) * F.card ≤ G j := by
    exact full_window_sum t j ht (by change j+16 ≤ N; have := mem_range.mp hj; omega) hcert
  have htail (i : ℕ) (_ : i ∈ range 15) : -(F.card : ℝ) ≤ G (N-15+i) := by
    simpa only [sum_const, nsmul_eq_mul, mul_neg, mul_one] using
      (sum_le_sum (s := F) (fun k _ => gbTerm_ge_neg_one N k (N-15+i)))
  have hm := sum_le_sum hmain
  have hh := sum_le_sum htail
  simp only [sum_const, nsmul_eq_mul, card_range, Nat.cast_ofNat] at hm hh
  have hN : (N-15 : ℕ) + 15 = N := by omega
  have hdis : ∑ j ∈ range N, G j =
      (∑ j ∈ range (N-15), G j) + ∑ i ∈ range 15, G (N-15+i) := by
    simpa only [hN] using (sum_range_add G (N-15) 15)
  change _ < ∑ k ∈ F, ∑ j ∈ range N, gbTerm N k j
  rw [sum_comm]
  change (745/1000:ℝ) * (N:ℝ) * F.card < ∑ j ∈ range N, G j
  rw [hdis]
  apply lt_of_lt_of_le _ (add_le_add hm hh)
  rw [Nat.cast_sub (by omega : 15 ≤ N)]
  push_cast
  have hb : (2000001:ℝ) ≤ N := by exact_mod_cast hn
  have hmargin : (745/1000 : ℝ) * N < ((N:ℝ)-15) * (7451/10000) - 15 := by linarith
  convert mul_lt_mul_of_pos_right hmargin hF using 1
  ring

end DyadicWord

theorem Conjectures.Cuts.Taskb98f3332b3a9cab8abb1dd40 : (have x1 : ℕ → ℝ → ℂ := fun (x1 : ℕ) (x2 : ℝ) => ∑ x3 ∈ Finset.range x1, Complex.exp (↑((2 : ℝ) * Real.pi * ↑⌊(65536 : ℝ) * (2 : ℝ) ^ x3 * x2⌋ / (65536 : ℝ)) * Complex.I); ∀ (x2 : ℕ),   (2000 : ℕ) ≤ x2 →     have x4 : ℕ := (1000 : ℕ) * x2 + (1 : ℕ);     ∃ x5 ⊆ Finset.range ((2 : ℕ) ^ x4), (2 : ℕ) * ((1000 : ℕ) * x2).choose ((85 : ℕ) * x2) ≤ x5.card ∧ (745 / 1000 : ℝ) * ↑x4 * ↑x5.card < ∑ x6 ∈ x5, (x1 x4 (↑x6 / (2 : ℝ) ^ x4)).re) := by
  intro expSum t ht
  have hcert : ∑ a ∈ Finset.range 65536, DyadicWord.windowLoss a * DyadicWord.windowWeight a ≤ 5097/10000 := by
    unfold DyadicWord.windowWeight
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, div_le_iff₀ (by positivity)]
    dsimp only [DyadicWord.windowLoss, DyadicWord.changes]
    apply le_trans _ (show (5096/10000:ℝ)*200^15 ≤ (5097/10000)*200^15 by norm_num)
    exact DyadicCert.iid_window_loss.le
  simpa only [expSum, Complex.re_sum, gbTerm] using DyadicWord.assemble_dyadic t ht hcert
