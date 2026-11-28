import Mathlib

open Finset
namespace MertensPrefix
def scale : ℕ := 10^18
noncomputable def exactTerms (p : ℕ) : ℕ → ℝ
 | 0 => 0
 | n+1 => exactTerms p n + 1 / ((n+2:ℕ) * (p:ℝ)^(n+2))
def terms (p : ℕ) : ℕ → ℕ
 | 0 => 0
 | n+1 => terms p n + scale / ((n+2)*p^(n+2))
def errs (p n : ℕ) := n+1+scale/(p^(n+1)*(p-1))
noncomputable def correction (p : ℕ) : ℝ := -Real.log (1-1/(p:ℝ)) - 1/(p:ℝ)
theorem floorBounds (a b : ℕ) (h : 0 < b) :
    ((a/b:ℕ):ℝ) ≤ (a:ℝ)/b ∧ (a:ℝ)/b ≤ (a/b:ℕ)+1 := by
  constructor
  · apply (le_div_iff₀ (by exact_mod_cast h)).2
    exact_mod_cast Nat.div_mul_le_self a b
  · apply (div_le_iff₀ (by exact_mod_cast h)).2
    exact_mod_cast (Nat.lt_div_mul_add h : a < a / b * b + b).le.trans_eq (by ring : a / b * b + b = (a / b + 1) * b)
theorem termsBounds (p n : ℕ) (hp : 2 ≤ p) : (terms p n : ℝ) ≤ scale * exactTerms p n ∧
    (scale:ℝ) * exactTerms p n ≤ (terms p n:ℝ)+n := by
  induction n with
  | zero => simp [terms,exactTerms]
  | succ n ih =>
    have h := floorBounds scale ((n+2)*p^(n+2)) (by positivity)
    simp only [terms,exactTerms,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
      Nat.cast_succ,mul_add,mul_one_div] at *
    constructor <;> linarith
theorem series_eq (p n : ℕ) (hp : 2 ≤ p) :
    (∑ i ∈ range (n+1), ((1/(p:ℝ))^(i+1))/((i:ℝ)+1)) = 1/(p:ℝ) + exactTerms p n := by
  induction n with
  | zero => simp [exactTerms]
  | succ n ih =>
    rw [sum_range_succ,ih]
    simp only [exactTerms,Nat.cast_add,Nat.cast_ofNat,one_div,← inv_pow,mul_inv_rev]
    ring
theorem correction_bounds (p n : ℕ) (hp : 2 ≤ p) :
    (terms p n:ℝ) ≤ (scale:ℝ)*correction p ∧
    (scale:ℝ)*correction p ≤ (terms p n:ℝ) + (errs p n:ℝ) := by
  have hp1 : 1 < (p:ℝ) := by exact_mod_cast (show 1 < p by omega)
  have hp0 : 0 < (p:ℝ) := by linarith
  have hx : |1/(p:ℝ)| < 1 := by rw [abs_of_pos (by positivity)]; exact (div_lt_one hp0).2 hp1
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one hx
  have hlow := sum_le_hasSum (range (n+1)) (fun i _ => by positivity) hs
  have hhigh := Real.abs_log_sub_add_sum_range_le hx (n+1)
  rw [series_eq p n hp] at hlow hhigh
  rw [abs_of_pos (by positivity : 0 < 1/(p:ℝ))] at hhigh
  have he := termsBounds p n hp
  have hpn : 0 < p^(n+1)*(p-1) := Nat.mul_pos (by positivity) (by omega)
  have hfl := (floorBounds scale _ hpn).2
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_sub (by omega : 1 ≤ p),Nat.cast_one] at hfl
  have hre : (1/(p:ℝ))^(n+1+1)/(1-1/(p:ℝ)) = 1/((p:ℝ)^(n+1)*(p-1)) := by
    rw [pow_succ,div_pow]; field_simp <;> ring
  rw [hre,abs_le] at hhigh
  have z : (0:ℝ) ≤ scale := by positivity
  unfold correction errs
  push_cast
  constructor
  · exact he.1.trans (mul_le_mul_of_nonneg_left (by linarith) z)
  · have ht : -Real.log (1-1/(p:ℝ)) - 1/(p:ℝ) ≤ exactTerms p n + 1/((p:ℝ)^(n+1)*(p-1)) := by linarith
    have h := mul_le_mul_of_nonneg_left ht z
    rw [mul_add,mul_one_div] at h
    linarith
end MertensPrefix


open Finset
namespace MertensSieve
private def stripe (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 =>
    let h := q*2^k
    let s := stripe q k
    if h < 16384 then s ||| (s <<< h) else s
private theorem stripe_spec (q k i : ℕ) (hq : 0 < q) (hi : i < 16384) :
    (stripe q k).testBit i = true ↔ i < q*2^k ∧ q ∣ i := by
  induction k generalizing i with
  | zero =>
    simp only [stripe,pow_zero,mul_one,Nat.testBit_one_eq_true_iff_self_eq_zero]
    constructor
    · rintro rfl; simp [hq]
    · rintro ⟨hl,hd⟩
      by_contra hn
      have := Nat.le_of_dvd (by omega : 0 < i) hd
      omega
  | succ k ih =>
    have hd : q ∣ q*2^k := dvd_mul_right _ _
    simp only [stripe,pow_succ,← Nat.mul_assoc]
    split_ifs with h
    · rw [Nat.testBit_or,Nat.testBit_shiftLeft,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,ih _ hi,
        ih _ (by omega : i-q*2^k < 16384)]
      by_cases hl : q*2^k ≤ i
      · rw [Nat.dvd_sub_iff_left hl hd]; omega
      · omega
    · rw [ih _ hi]; omega
private def freeOf (p : ℕ) : ℕ → Bool
  | 0 => true
  | k+1 => freeOf p k && decide (p % (k+2) ≠ 0)
private theorem freeOf_spec (p k : ℕ) : freeOf p k = true ↔ ∀ d, 2 ≤ d → d ≤ k+1 → ¬ d ∣ p := by
  induction k with
  | zero => simp [freeOf]; omega
  | succ k ih =>
    simp only [freeOf, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · intro ⟨h1,h2⟩ d hd hu
      by_cases h : d = k+2
      · subst d; exact fun hh => h2 (Nat.mod_eq_zero_of_dvd hh)
      · exact h1 d hd (by omega)
    · intro h
      exact ⟨fun d hd hu => h d hd (by omega), fun hh => h _ (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hh)⟩
def fastPrime (p : ℕ) : Bool := if p < 1733 then decide (2 ≤ p) && freeOf p (min (p-2) 40) else decide (Nat.Prime p)
theorem fastPrime_iff (p : ℕ) : fastPrime p = true ↔ Nat.Prime p := by
  unfold fastPrime
  split_ifs with hsmall
  · rw [Bool.and_eq_true,decide_eq_true_eq,freeOf_spec]
    constructor
    · rintro ⟨hp,h⟩
      refine Nat.prime_def_le_sqrt.mpr ⟨hp, fun d hd hsq => h d hd ?_⟩
      have hlt : p.sqrt < 42 := Nat.sqrt_lt.mpr (by omega)
      have hsp : p.sqrt < p := Nat.sqrt_lt_self (by omega)
      omega
    · intro hp
      refine ⟨hp.two_le, fun d hd hu hh => ?_⟩
      have := (Nat.dvd_prime hp).mp hh
      omega
  · simp

private def bases := (List.range 1733).filter (fun p => decide (Nat.Prime p))
private def mark (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | q::qs => (stripe q 14 >>> (a % q)) ||| mark a qs
private theorem mark_spec (a j : ℕ) (qs : List ℕ) (hj : j < 8192)
    (hb : ∀ q ∈ qs, 2 ≤ q ∧ q ≤ 1732) :
    (mark a qs).testBit j = true ↔ ∃ q ∈ qs, q ∣ a+j := by
  induction qs with
  | nil => simp [mark]
  | cons q qs ih =>
    have hq := hb q (by simp)
    have hp := Nat.mod_lt a (by omega : 0 < q)
    rw [mark,Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true,stripe_spec _ _ _ (by omega) (by omega),
      ih (fun p hp => hb p (by simp [hp]))]
    have hu : a % q+j < q*2^14 := by norm_num; omega
    have hh : q ∣ a % q + j ↔ q ∣ a+j := by
      rw [Nat.dvd_iff_mod_eq_zero,Nat.dvd_iff_mod_eq_zero,Nat.mod_add_mod]
    norm_num at hu; simp [hu,hh]
def verifiedBases : List ℕ := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997,1009,1013,1019,1021,1031,1033,1039,1049,1051,1061,1063,1069,1087,1091,1093,1097,1103,1109,1117,1123,1129,1151,1153,1163,1171,1181,1187,1193,1201,1213,1217,1223,1229,1231,1237,1249,1259,1277,1279,1283,1289,1291,1297,1301,1303,1307,1319,1321,1327,1361,1367,1373,1381,1399,1409,1423,1427,1429,1433,1439,1447,1451,1453,1459,1471,1481,1483,1487,1489,1493,1499,1511,1523,1531,1543,1549,1553,1559,1567,1571,1579,1583,1597,1601,1607,1609,1613,1619,1621,1627,1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem bases_eq : bases = verifiedBases := by
  have h : bases = (List.range 1733).filter fastPrime := by
    simp only [bases]; congr 1
    funext p
    exact Bool.eq_iff_iff.mpr (by simp [fastPrime_iff])
  rw [h]; decide +kernel
def bits (a : ℕ) := mark a verifiedBases % 2^8192
theorem bits_spec (a j : ℕ) (ha : 1732 < a) (hj : j < 8192) (hN : a+j ≤ 3000000) :
    (bits a).testBit j = false ↔ Nat.Prime (a+j) := by
  have hb : ∀ q ∈ bases, 2 ≤ q ∧ q ≤ 1732 := by
    intro q hq
    simp only [bases,List.mem_filter,List.mem_range,decide_eq_true_eq] at hq
    exact ⟨hq.2.two_le, by omega⟩
  have h := mark_spec a j bases hj hb
  unfold bits
  simp only [Nat.testBit_mod_two_pow, hj, decide_true, Bool.true_and]
  rw [← bases_eq]
  rw [Bool.eq_false_iff]; change (¬ (mark a bases).testBit j = true) ↔ _; rw [h]
  constructor
  · intro hn
    apply Nat.prime_def_le_sqrt.mpr
    refine ⟨by omega, fun d hd hs hdiv => ?_⟩
    have hm := Nat.minFac_prime (show d ≠ 1 by omega)
    have hle := Nat.minFac_le (by omega : 0 < d)
    have hu : (a+j).sqrt < 1733 := Nat.sqrt_lt.mpr (by omega)
    exact hn ⟨_,by simp [bases,hm,show d.minFac < 1733 by omega],dvd_trans (Nat.minFac_dvd d) hdiv⟩
  · rintro hp ⟨q,hq,hd⟩
    have hh := hb q hq
    have hh' := (Nat.dvd_prime hp).mp hd
    omega
end MertensSieve


namespace MertensTree
open Finset
def tree (f : ℕ → ℕ) (a m : ℕ) : ℕ → ℕ
  | 0 => if m.testBit 0 then f a else 0
  | d+1 => if m = 0 then 0 else
    tree f a (m % (2^(2^d))) d + tree f (a+2^d) (m >>> (2^d)) d

theorem tree_spec (f : ℕ → ℕ) (a m d : ℕ) : tree f a m d =
    ∑ j ∈ range (2^d), if m.testBit j then f (a+j) else 0 := by
  induction d generalizing a m with
  | zero => simp [tree]
  | succ d ih =>
    by_cases hm : m = 0
    · subst m; simp [tree]
    rw [tree, if_neg hm, ih, ih, pow_succ, Nat.mul_two, sum_range_add]
    congr 1
    · apply sum_congr rfl; intro j hj
      have hj' := mem_range.mp hj
      simp [Nat.testBit_mod_two_pow, hj']
    · apply sum_congr rfl; intro j hj
      simp [Nat.testBit_shiftRight,Nat.add_assoc]
end MertensTree


open Finset

namespace MertensFold

def depth (p : ℕ) := if p < 32 then 63 else if p < 1000 then 5 else 2

def charge (p : ℕ) (prime : Bool) : ℕ × ℕ :=
  if prime then (MertensPrefix.terms p (depth p), MertensPrefix.errs p (depth p)) else (0,0)

def go (a : ℕ) (isPrime : ℕ → Bool) : ℕ → ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, _, acc => acc
  | k+1, j, acc =>
    let c := charge (a+j) (isPrime j)
    go a isPrime k (j+1) (acc.1+c.1, acc.2+c.2)

def blockFromMask (a w mask : ℕ) : ℕ × ℕ :=
  let live := (mask ^^^ (2^w-1)) % 2^w
  (MertensTree.tree (fun p => MertensPrefix.terms p (depth p)) a live 13,
    MertensTree.tree (fun p => MertensPrefix.errs p (depth p)) a live 13)

def block (a w : ℕ) : ℕ × ℕ :=
  if a = 0 then go a (fun j => MertensSieve.fastPrime (a+j)) w 0 (0,0)
  else blockFromMask a w (MertensSieve.bits a)

noncomputable def term (p : ℕ) : ℝ :=
  if Nat.Prime p then -(Real.log (1-1/(p:ℝ)) + 1/(p:ℝ)) else 0

noncomputable def cumulative (a : ℕ) : ℝ :=
  (MertensPrefix.scale:ℝ) * ∑ p ∈ range a, term p

def B (a b lo err : ℕ) : Prop :=
  (lo:ℝ) ≤ cumulative b - cumulative a ∧ cumulative b - cumulative a ≤ (lo:ℝ) + err

private theorem single (p : ℕ) (flag : Bool) (hf : flag = true ↔ Nat.Prime p) :
    B p (p+1) (charge p flag).1 (charge p flag).2 := by
  have hstep : cumulative (p+1)-cumulative p = (MertensPrefix.scale:ℝ)*term p := by
    simp [cumulative,sum_range_succ,mul_add]
  unfold B
  rw [hstep]
  by_cases hp : Nat.Prime p
  · have hreal : term p = MertensPrefix.correction p := by
      simp [term,hp,MertensPrefix.correction]; ring
    rw [hf.mpr hp,hreal]
    exact MertensPrefix.correction_bounds p (depth p) hp.two_le
  · have he : flag = false := by cases flag <;> simp_all
    simp [term,hp,charge,he]

theorem join {a b c l₁ e₁ l₂ e₂ : ℕ} (h : B a b l₁ e₁) (h' : B b c l₂ e₂) :
    B a c (l₁+l₂) (e₁+e₂) := by
  unfold B at *
  push_cast
  constructor <;> linarith [h.1,h.2,h'.1,h'.2]

private theorem go_spec (a : ℕ) (test : ℕ → Bool) (k j l e : ℕ)
    (hf : ∀ u, j ≤ u → u < j+k → (test u = true ↔ Nat.Prime (a+u)))
    (hacc : B a (a+j) l e) :
    B a (a+(j+k)) (go a test k j (l,e)).1 (go a test k j (l,e)).2 := by
  induction k generalizing j l e with
  | zero => simpa only [Nat.add_zero,go] using hacc
  | succ k ih =>
    have h := single (a+j) (test j) (hf j le_rfl (by omega))
    have hh := join hacc h
    rw [Nat.add_assoc] at hh
    have hnext := ih (j+1) _ _ (fun u h1 h2 => hf u (by omega) (by omega)) hh
    simpa only [go, Nat.add_right_comm j 1 k,Nat.add_assoc] using hnext

private theorem sums_spec (a k : ℕ) (test : ℕ → Bool)
    (hf : ∀ j < k, test j = true ↔ Nat.Prime (a+j)) :
    B a (a+k) (∑ j ∈ range k, (charge (a+j) (test j)).1)
      (∑ j ∈ range k, (charge (a+j) (test j)).2) := by
  induction k with
  | zero => simp [B]
  | succ k ih =>
    rw [sum_range_succ,sum_range_succ]
    exact join (ih (fun j hj => hf j (by omega)))
      (single (a+k) (test k) (hf k (by omega)))

private theorem mask_spec (a w mask : ℕ) (hmask : MertensSieve.bits a = mask)
    (ha : 1732 < a) (hw : w ≤ 8192) (hN : a+w ≤ 3000001) :
    B a (a+w) (blockFromMask a w mask).1 (blockFromMask a w mask).2 := by
  let test := fun j : ℕ => !(mask.testBit j)
  have hf : ∀ j < w, test j = true ↔ Nat.Prime (a+j) := by
    intro j hj
    simpa only [test,← hmask,Bool.not_eq_true'] using
      MertensSieve.bits_spec a j ha (by omega) (by omega)
  let live := (mask ^^^ (2^w-1)) % 2^w
  have eqSum (g : ℕ → ℕ) :
      MertensTree.tree g a live 13 =
        ∑ j ∈ range w, if test j then g (a+j) else 0 := by
    rw [MertensTree.tree_spec, show 2^13=8192 by decide]
    calc
      _ = ∑ j ∈ range w, if live.testBit j then g (a+j) else 0 := by
        symm
        apply sum_subset (range_mono hw)
        intro j hj hnot
        have hj' : ¬ j < w := by simpa using hnot
        simp [live,Nat.testBit_mod_two_pow,hj']
      _ = _ := by
        apply sum_congr rfl
        intro j hj
        have hj' := mem_range.mp hj
        simp [live,test,Nat.testBit_mod_two_pow,Nat.testBit_xor,Nat.testBit_two_pow_sub_one,hj']
  have hg := sums_spec a w test hf
  change B a (a+w) (MertensTree.tree _ a live 13) (MertensTree.tree _ a live 13)
  rw [eqSum,eqSum]
  convert hg using 1
  · apply sum_congr rfl
    intro j hj
    cases hf' : test j <;> simp [charge]
  · apply sum_congr rfl
    intro j hj
    cases hf' : test j <;> simp [charge]

theorem block_of_mask (a w lo err mask : ℕ) (ha : 1732 < a) (hw : w ≤ 8192)
    (hN : a+w ≤ 3000001) (hMask : MertensSieve.bits a = mask)
    (hcert : blockFromMask a w mask = (lo,err)) : B a (a+w) lo err := by
  have h := mask_spec a w mask hMask ha hw hN
  rwa [hcert] at h

theorem segment (a w lo err : ℕ) (ha : a = 0 ∨ 1732 < a) (hw : w ≤ 8192)
    (hN : a+w ≤ 3000001) (hcert : block a w = (lo,err)) :
    B a (a+w) lo err := by
  have h0 : B a (a+0) 0 0 := by simp [B]
  by_cases hz : a=0
  · let f := fun j : ℕ => MertensSieve.fastPrime (a+j)
    have h := go_spec a f w 0 0 0 (by simp [f,MertensSieve.fastPrime_iff]) h0
    change _ at hcert
    simp only [block, hz, ↓reduceIte] at hcert
    subst a
    change go 0 (fun j => MertensSieve.fastPrime (0+j)) w 0 (0,0) = (lo,err) at hcert
    dsimp only [f] at h
    rw [hcert] at h
    simpa only [Nat.zero_add] using h
  · apply block_of_mask a w lo err (MertensSieve.bits a) (by omega) hw hN rfl
    simpa only [block,hz,↓reduceIte] using hcert

theorem bounds {K lo err : ℕ} (h : B 0 (K+1) lo err) :
    (lo:ℝ)/MertensPrefix.scale ≤ ∑ p ∈ range (K+1), term p ∧
    (∑ p ∈ range (K+1), term p) ≤ ((lo:ℝ)+err)/MertensPrefix.scale := by
  simp only [B,cumulative,range_zero,sum_empty,mul_zero,sub_zero] at h
  have hp : (0:ℝ) < MertensPrefix.scale := by norm_num [MertensPrefix.scale]
  exact ⟨(div_le_iff₀ hp).2 (by simpa only [mul_comm] using h.1),
         (le_div_iff₀ hp).2 (by simpa only [mul_comm] using h.2)⟩

theorem finish {lo err : ℕ} (h : B 0 3000001 lo err)
    (hl : 315718430000000000 ≤ lo) (hu : lo+err ≤ 315718450000000000) :
    0.31571843 ≤ ∑ p ∈ range 3000001, term p ∧
      (∑ p ∈ range 3000001, term p) ≤ 0.31571845 := by
  have h1 : (315718430000000000:ℝ) ≤ lo := by exact_mod_cast hl
  have h2 : (lo:ℝ)+err ≤ 315718450000000000 := by exact_mod_cast hu
  simp only [B,cumulative,range_zero,sum_empty,mul_zero,sub_zero] at h
  norm_num [MertensPrefix.scale] at h
  constructor <;> linarith only [h.1,h.2,h1,h2]

end MertensFold

namespace MertensMasks
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask1733 : MertensSieve.bits 1733 = 0xbfffbefffbbffbffafbffbeeffefbfbffbbeffebfffefbbeffebffffefeffafffeffefbffafbbeffefffbffffffffbbfbeffeffbffefbffbefbafffffaebfebeffbefbffefbffffefaefffbbfbfffeffaeffffefffebffbeffefbbffbefeffeefbffeefbfffefbffbfffffbfbfefaffefffebbebffffffafbffbfefeefbffffffefbffffbaffeffafbfebffbbffffbbfffefefbeefbffbefbfbeefeefefbfffbeffebbffeffafffefeffbffffbaffbefeffeffffffffbefffbbffafbbffffffebfefefbfefffffeffefbffeebbffeefbffffbeebfebfeffffbffbfbbefffbfffffbefbfefeebeffeffbefffbffffefafffefffffffbffaffeefbfbffbeffffbaefbffeffeffefbefffffeefffffffaeffefffbbefffbbfbbefeeffffefbbfffefffbbffafbeeffebfebeefefbeffbfbfebeeffffafbfffefffefbfffefffffeffffafffebfeffebfefffbffffffefbbefeffbebbffefbfeffffbfbffffebeffefbfffffbfeffefffbbffbfbeffeefbfbefbbebfebffffffefbbfbfffbffafbefffefeebbffffbfebfebfffafffffeefffbfefaffaffbeffebefffeffffbffbfbfffeefafbfebbfffefefffffffbfefeeffffafffffbefffffefeffbefbebeffbefefbefbfebffbfefafbeffbfffefeefbfbafffffeffbffbfbfebfefeffeffaffbefbffefbbefeffffbbffffbeffffffefffbffbbffffbefffebfebeefafbbffbefefbeffbfbbffffffefaeffffefbfefeefbffeffaebbebfffbfffffffbfefeefbeffffffbbebffbaffffbafbffffefaefbffaefbfbefbefffffffbbffeffbffefbefffebeffefffffeebbfffeffefeffbfbbffefbffffffbefbebffbeeffffbfbffbfffaffafbbefbffeebfefbfbeebffbfefbffeffefbfefffffffbffeeffebeebbfffffbfbfffeefaffffbffbffbeffbefafbafffeffffbefbfbfffbeffebfffffbaefbffeffaffffbefbbeffffaffeffefbfffeffbefeffaffbffffffefefbfebfebeffaffaffafbfefffffeffffaefffbeebfffbffbebffbefffefafffffbebefbaffefffffbffffbbffafbafbbfffefeefffbfebbffeffaffffbeefffbfebefffffbefbfbfefeefbffeebffbfffbefbfbeefbffeffaffbffaffbebeebfefbffbfbffffebaefefffeffffefbfffafffebfebffbbffafbbefbebffffffbffaebffffefeefefbffbbeffebbfffffefffebfeffffefbbffbeffefeefffbbfbfebffffffafbeefffbffbfefefbeffbfbfffeefbfbeefffbfffaefaffeffbffeefeffaffbebbfbeebbefbfbaffbffeffeefefffebffbffffefafbbfbfeffffbfffffeefbfbffbeefffbefbffbeefaefbffefbbebefffffaffeefbefeebfffbfbafffefefbbfffffbfffefeffaefafffebffbfebaffefbfefffbfebfefbfbaefbfbefffffafffebfffefbeffeffaebbefffbfffbfbffbfeffebbeffffbefbefe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask9925 : MertensSieve.bits 9925 = 0xffffefeffefffebfebaffffffefffffebeefbffaffffbfefaffafbffbfeffffbffbffaffbffffbfffafbffffeffebfefefffefbfffffaffeffafffffffbbffeffafffebeeffffbffbffffbfeffefafbefbbfffefbffbffafffefeebbeffffbfbfefefbeeffffbebfffffffeffffbfbffffebbffafbfffbfbffffefffbeffbfbefffefffffefbefeebeffbfffefbebfffbffffbefbbeffffaffefbbfbffffffbffafbffbfffffbfffffbbffbeffeffffffbbebfffeffeefafffebffbffbbffffffefbefefbfffeffbfffffefbeefffffebbffefbeefbffffffeffefaffeffbefffbfffeffffffefbffeeffffafbefffffeebbfffffffffebffbfffbfbefbbffeebaefffffeffffffbeffbfffebffbffffefffbbefbeffebeeffffbffffffffbefefbefbbffefbeffeffaebbffffffffffbbfbbeffebaffeffbffbeffffaffeffbfbfefffbfffbffeeffffefbeffbfbbffbffeffeffbfbeeffebfeffffaffbefbfbfebfefafbbfffefefbfeffffbefbffeffeffeffafbfefffbeffbfbeeffefefffffbffeefffffffbffeffefbbfbfefbfffffefbbfbfebfffbfbffbbefefffefffbbfbbfbefbeefbfbeefffbfffbffeffeefffbeebeffffffebffffffaefafbeefffbfffbffeffbfffeffebfefbfbbfbbeffebfffefffffbefffbaffffbfeffefffffffafbffffefffbfeffffeefffbeefbffffffffbffffbaffbffefbfffeeffffaffafffffffbbffffffebfefefbaffffbaefffbfffeffafffffbfbfefeffffbafbffffefaffaffeebbebfeffffefffefbfbefffefbffeffbffefffefffbfefffbffbfefefbefbfeffffeefbffafffefffbffffffafbbffeeffefbfffffbfbfefeffeffafffffffbbefbfbbfbbffffbeffefbbefffffffbffefbeefffffebaffffbbefbfbeffeffffbafbbfbeeffffffffeffeffefaffeffbfbfeffffbefffbbfffefeffbefeffffbffbefbeeffffbebfeffefbefefffefbebffbfefbfbefbbfbefffefbffeeffefeefeffbffaeffffffbbffefbffffeffefeefefbfebfebffbfffbfbeffffffffaefefbfffffbeebeefffffebffffefaeffffffbbffffbeffaffbeffebefbbffefbeffbffffbbfffffbebbefefbeffefbaffffffffbffbffafffebfefeeffffefffffeffeeffffeefbfbffffffafffffbfbfffbefafbffbbffffbbefffbffbffbeffbffefffebffffefeefbffbffbfbeffeefbfbbfffffefffeffffeebfebfeffffbffaeffffefbbffaffaffbffffbfffffbfefbfbefffefeffaffffffefbffafbfffbebefbfefbfffffffbfefeffbfffefffbeefbffaffffbbffffbbefbffbfbbffefbeefefffffbfbffffffafffeffebffbfefffbaeffffeebffffffbfbffffeffefffbeebfefeffaffefffebbfbefbbffffbffbfffeffeefefbbfbfebefffffbfbbebffbfebefffffaffffffebfffffffefbfffefeffaf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask18117 : MertensSieve.bits 18117 = 0xffeeffffffbaffaffeffbfffefbffefbefbfefeffefffffbebbfbfffbffffffeffeffefeefffbafffeffeffffbfbbebffbeffbffefffefbfffebefffffbfffebefffffbfbbffbefefffefffbfefffbefbfefffbbeffeffefaffefbafffeffffeefffbffffffffffffafbeefbfbfffbffaffffbfffefbfefefbbfffeffebafffffffffefefbbefeffbffffffefbffafbfefbffffbeefbffeffbffefffeffffeebfffefffffeffafbbffeffbffffbaffbfffeffeffffbfbbeffffeffeffbeffefffbbffefffefffffeffefbfbefbffbffffffbfbffbfffefffffbffffbbffefbfefeffbfffefeeffffffbbfffebefbfffbffbebffbffffefeffeffffffffefffffffbbfbfefbffffbefffebfeffffbffeeffefeebbefbfbefbfeffefbffefbbffbefeffeefbffeffffffeffefaffbefbfbeeffefffffebbfbeffeffefffefbefefbafffffbffffffebfefafbffffffeebbffefbbeffefffbaefeffafbffffeffefffffefffbffbfffbffeffffbffffffaffeffffbefbeffbffeebffbfeffffbfffffbfffefaefefffefbfbfffbffbffeffffbffbeffbfbaeffebfebeefbfbfeffffeffaffffbefffefffbefffffefbfebeffffffffefbbffffbbefeffffbfebffbeefeffafbffbfeffffbfbafffebefffffffffebbfffefaffbffffbfeffffaffefffefbefefffffeffefbfeffebfffefbffffffffbbffbfbaebffbffbfffeffffffffeeffffbffaefbffeefbffafffebffbefbbffbffafbbffeffbefbffefffeffffbefeffffbfffeffeffbfbbfbfebfffeefffbbffbffefbfefbffaffbffeffeffffbfeffeffebffffffeebfebfebfefefbaffffffefaefffbbebbefffbfffffffefffbffbeefbfbafffffffbeffffbaefffffffbefefffffbffffbeffbfffebbfbfefbefefbbfffefffbeffefffffbebffffffbfbaebfeffffaffffbbffbfbfefeffffbaffbfbefffefefffffffffebfffefffebffbeebbffbffaffbffeffeffffbffffebffbfffbffbefffffffbffafbfeffeffebfffffbaffffffffaffbffffbbfbeeffffeffaefbefefbbfffffeffbfffefeffefffebffbfffeffffbeeffeffebbffefbeefbeffeffffbfbffbbfffefaffbffeebffbeffaffeffeffbfbefffffafffffbefeffafffffbeffefefffefffbbebffbffbfefeffaffbeffffeffffffffffffefbefffbefbffbeffaffbfffffbeffefbefafbeffbefeebaefffbffbbebefffffffffefffbfefeffefffefbfbfeffefbffbebbfffffaffffbefffebfffeffffffffbebeeffffbffefbfffeefefffffbefffbffbffffffaebffbffffffeffbffffbffffffffbeefbffefffefefbffbffbeffeffbffbfbfefffffeffffefffffefbbffffffeffebfffaefffbfeffeffffeefbfbbefbffeffeeffffbfbbffeffeffefffebbeffebfffeffeebfffeefbefbffbfbfeffeffffefbfebbeb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask26309 : MertensSieve.bits 26309 = 0xbffbbffaffeffffbfefeffffbffffeffebeffbffeffbfbeffaefffbfefbebefffffbffeebffffffbffbffaffbeffebbffffffffffffffeeffffbebffbffffefffffffbeffffeefbfbffbfffeeffffbfbefbffffebfffaffefbfffeebfefaffbfffefeffbfffffbfffffffbeefefbaeffebfebeefefbfffbffeefeffffbfefbfbfefeefffffffbffeefbffbffeffffbeebbffaffefbfeffebfffffffffbfffffbffbfbbfbfebfffeffafffffffbefbfffbfbfebfffeeffefefbfefffbefbbffaffefffebefffefafffffbfffeffffffbbebffffffaefefbbfbffffefffffffaefbffefbfffffffefbffeffeffafbfffbfbeefafffffeebfffffbbefbffbffbfffffaffefbfebfeffffeefafbbeffefffbaffefbaffffffffeefbffeeffffeffbffafbfefffbfffafffffaffffbfefbefefbafbffffebfffefbffbfefeffbeffffffffffffbfffbfbfefffbfebffffffeffffbefffffaffffbfeffebafffffbffbffffbbefefbfffbffffbeffffbfefbffffbaffbffeebffffefeefefffffffffffffffffeebbfbffffeffffeefbebffbffffffefbbfbeebfefbfbbfffffeefaeffffbebbfbfffafffffffbfebfefbffbffbefffbefffffffbefbffffefeefbffffbfffeffeffaffbebfebfeffefefbffffefeffbefffffffbffefbbefeffefbfeffefbefbffffffffefffeffffaefffbfeffefeffeebffffebfffeffffbbfffffbffafffffbffffbeffffbbefbffefffffaffbeffeffffbffbfbeffbeffefefffffaefffbeefbefaffffbffbffbfffefffebffffefbfffffbffbffffbeeffffffffebefbbffbffeefffbfffbffeffffffebeffeffffbeffffffffbffafbffffefeeffffbffbffbefeebffffffefbbfffffeffffbfeffffeffbefefbffbfebfebbffffbfffbfbefbfffbfbeffbfffeffffbfbffbfeffebeffbffbefbffefbfefafbffffefffffefffbbfffffefbaefefffffffbfffeffefffefbeffefefffffbfbbfbfffbeffffeefbffeeffffbffbebffffefbffbfbeffbfffefaefefbffbbebffbbefbffbebffbfebeeffffeefffbefffefffbfffbfbeeffffafbfefbffffffffafffffffbfebfefefbafffffffffffeffbfbfeffffaffffbffbffffffbffaffaffbeffeffefbffffbbfbfffeefffbfffbefefbafffffafffefeffbfffffffbbffffbbefefbbebffbefbbffafbaefffffffeefafffeffffefbfffbffefbffffffafffffffbfebfebfffefffffbebffffefeffefbbfffebfefffffffbefffffefefffffffbfffaefbffbeffebffffffbffefbffbffffffffbfffbfffebbffbffeefbebfffbffbffefbfffefbefffffbebbffffbeffffbfebfebfffaffeffbeffefeffeffffbeffffbffffefafbeebfebefbaffefffffbefefbffffffefbfffeffeeffffbfffffeffeefeffbffffbfeffefbfbeffbfbefbfffbffeffbfbfffeefe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask34501 : MertensSieve.bits 34501 = 0xefbeffbfffefafffffffbffffeffefaffefffffefffffeffbfbbffefbaefbfbeefffffebbefbffbefffbfeffefbfbfffbfbeffafffffeffffbffbaffeffeefbebfeffeffffbfbffffffeffefbfebfeffffbffffbaefffbfffaffeffaefbefffbfffbfbeefbfbfffbffafbffffffeefefffffefbfebffffefeffbfffffffbeffeffbfbbefffbeefafbeefffbffffffefbbfffebefbfffbffbffbffeffbffffffebffbfebefffffefbfefeffffffffbfffeffefbefffbfebbefeffaffefbafffeffefaffbffeefffffffeeffffefbbfbfffbefbfffeffffeffeffeffbefbfffffbefffbbffbffeebeffefbbeffefffbfffbfbbfbffbffffffeffaefffffffffffffaffbfffeffefbfbeffffbfffbffaffbffbfbefbbffbffbfffffeebbffffffffbfffffeefbfbffffffffffffefbefffffeffeefbfffeffffeeffefefbfebffffebbffbffbefbfffffbfffffafbfffeeffffefbbfbfffefffefeffffffefffbbefefbeffbebfebefffffbfbffbfefeffefffefbfbfefbfffffbfbbfbffffffbfbbffbfffffeffefbffbfeffffeffafbbffffffffeffbfbbffffbfeffefffbfebbfbfffaffffbeeffefeffffffffffbfebeebfefeffbfbfeffffaeffffbefffbefbbefeffbfffffffbaffffbbfffffefffefbffbeffffeffaefffbffbfffefbeffbffbeffeffffbffbfbfffbfffebfefefbfebbfbefffefafffebffbfeffffafbfefffffebeefffbfffffffffefffffffffebeebfffbffffffffefffefbffffbfffeebeefffbbffbefeffefffffafbffbfffeefefbeffbffeefffffffbefffffffbffefffefbfbffffffbffeebbffffbbefbffffffffffbfefeffbfbfefefbfffbfffebffbfffaffffffffbffffffeffffbebffffffbefefbfefffbffbfffaffbebbeffebfefeffefbbefeefbffffbfffbeffffbffeffeffffbfefaeffffafffefeebffffffeeffffeffbffffbefffebfefeffbffbffffbfffbeffffeffbfffffeefeffbfffebeffbeffffbeffffffbbffafbbeffebffbfefbffeffbffeffeffefffebbebffbeffeffbfffefeeffefbfbefbfffeffbefefffffbfbffbbffbfbbfbfeffebbfffffeefffbeebfefbfffeffffffffffefbfeffffeffafffffbefbfbefffefefbffbfeffeffefeffffbbfffffeffbffefbffffebfefffbfefbefffffeffffeebbfbeffbefefbffbfffeffbffbffaffffbfefbffbffafbffffefaeffffffbffbefbfffaffffffffffffefbffffffffffffefffbeebfffeeffffffbeebbeffebfffbffffffeffebfefffbbffbefeffeffffbfefffbffbbefbffffbfebffbfefbfffffbeffffefffffffbffbeefeffeffefbbfbfefaffeffbebfffffbbfffffffffeffffaffeffbffffbefffefffbefbffffebafffffbffbfffffeffffbaffbfbfefeffffbfefbfbefbfffaffffbfffefbbffafbfffffffefbeffffbebfe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask42693 : MertensSieve.bits 42693 = 0xffefbfefeffbeffefffffffeffeefbffeffeffffbfffbfffffbffbffffbbffffbffffffbebbefffffffafbbffbffeffbeffffffffebfffeffffbefbfffffbbefffbbfffefeefeffbffffbbffeffafffffffbbefffbffffffeffffbefbfffafbbfbfefefbfefefffebbffeffafffffbebfffffffefffbaffbebffffffbffefbfffeffbffbfbffbbeffebbfffffeffbebffbfffbffefffeffebbfffffbefbffeffbefffffffffbfebfefafbfffffbfffeefffbbfbfffeeffefafffebffffebbfffffbebfffffbfeffffafffefefffffffbffbbebefffefaffeffffbfffaefefbffffeffeffefffbeebffbfefbffafffeffffefbfffffffffbfffefbffaffaffbfffffaefeffbffbebffbeefbfffebffffffffffffaeffeffebfffffbbfbfffeeffffbfbffffebefbbfffffefbbebeffbffeffefffffeebfefffbffbfffeffeefffffebffbfffeffbffbffbfbfffefffffeefbfbfffbeffffffbfebfeffffbffbefffffeffffefbeffffffffeefefbffbbfbefffefbfbffffeffeffefffbeffffbfebfefbffaffffffffaeffffeebfebfffefffffaefffbfefbffeffbfbfeffefbffffbfefbefefbeefbfffffffbfffeffbffaffbfffebeffffbfebffbffffefefbeefbfbfeffffbffefffefffbfffeffffffeffebbefefbbfbfffefbffffffafbfefffffeffffeeffffffffefffffefffbfffeffeffeffbefefffffaffafbbffffffffaffefbbffffbbffffbffbbebfffbffefbbefffbfffeffafffefbfbfeffffffbffbbfbfeffefbffefbbebffffffbffbfffefffffffaffeffbfffebefffffbebfefffffefeffbffffbffbaffbfffefbefefffffffbbebfffeffeffafffffbefffffffeffbfbffbeefbfffffffffffefbfffefbfeffefefbaefffffffffbffbbefbffefffffffbfefbffeefbfbfffeffbfffefffbfebfffeffeeffefeffbffffbefbfeffffffffffbefbffeffbffeffefffeffffaefeffaffbffeefeffffbbffbffeffffffffefbfebfffefffffafbbebffffffffbefffefefffffffffefbffffbbffbfbbefffbffbfefefffefbfbffbfffbfbbffffbfeffefeffeebfffeffeffeffffbfebffbbfffffefbbefeffaefffffffbfbfffbffefbeebffbffbeefbfbffffffeefffffffeffffffefaffbffefbfffffffffffffeffebeebbefeffffffefffbaffeffbfbffbffffffafbbfbfeffebfffbffbeffeffebeeffffefbbffeefaffbfbfeffffefffffafffffbffeffffffffffffefeebaeffffbefffffffeefbffffbffffefeffafffefbffeebfefbffaefffffffafffffeffffbffbefffffefbfefffbfffbfbafbffffffffffffffbfebefffffbfbffbfefffffefffbfffbeffeffeffffbfbfffefffefffbfeffffffbbffaffeffffbeffbffeffbffbefeffbefefbffffebffffffffbbeffebfefefffffeefbffefbfffbfbeffbfbfefaef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask50885 : MertensSieve.bits 50885 = 0xfefbfebffffefaffaffefbffbffbbffffbefffefeebeefeffffffffffffffbfffffffffebfffbfbefffefefbfffbffbefbfbfffeeffffffbfffeffafffffbefbfffefbeffffffbffffffeefffffebfebffbfefbfbfebffbfebbfffffefffefeefffffffffbffffffbefaffefbbfbeeffffafffebbfffeffffaffbfffffefbeefefbffbbffefffffbffeeffffffbbffffbefffebfffefffffbefbfbfeffffefbfebbefefffffbffefbbfbeeffefeffbffbffeefeeffffffffefefbfffbffaffffffebfffffbfefbffffbfefffffffbffefffefefbfefbfffebfffaffffffefffbbffaffbfbfeffffaffffbfebffbeffbffefbbfbffbffbfefeffeefffbffbeefffffffffbeefbffffbefbfeffefaffaffeebfffefffefffbfffbefeebfffffbbefbffffbfefbfffebfefffbeffbfbbfffffeeffffbffafbffffeffffffbfebbfbfefaffeffaefbffeffbefbffefffefeffbefeffbfffffefffffbffbffffffebbffeffaffffffebfeffffbfbbfffeffffbfbfeffebefbeffffffeffebffffffefbeffbffffbfffefffebbeffffaefeffffbffffefbefefbaefbfbefbfffffbffffffeffeefbffefbfefefbafffffbebfebfefbffeffbfffffffbeffeffffbfefffbfffeffefffebffffffbffbfffefefffffbfbaebfffefffffbfffffffbfefbffeffaefbefffffffbfbfffbffffbfefefbfffffbeffeefaffffffeffefeffffbbefffbfefefffffaffbfffffeefeffffbfffeefffffffbffbfbefbfffbfffffbefeefffffffbefbffffbfffafbefffeffffaefffbbffbebfffeefffbaefffffeffffefbefffebeefafffffefbbefffbfffbfbbfbfffefbfefeffffbfffffffefffffeffefffbbffbffbeffeffffeffbfbfffffbfeffefffffebfefefbffffffbfbffbffbbeffffafbbeffffeefeffffbffbefffffbfbeefffbffffffbffaffffbeffefffffeefffbeefbefaffeebffffeffffafffffbffffbbfffffbfffffeffeeffffbfbbeffffeeffffbeffffffbbffeffbfffebfebffffffbebffffffeefefffebfeffebfffeffeeffefeebfefeffffbbffffffefffbbfffefefbbefbffeffffbfffaffefbbfffebffffeffffeefbfffffbffeffeffbffefbeffaffefbfffefbffffffbfbbfffeffffffbbfbbefeffaffeffefbfeffefffffffeeffffeffffffffffbbfbfefafffffffffefeffeffafffffbfbeeffefffbffffeffefaefffbfefbffffbeffffbffffeffebfefbfffffbeffeffffbffeebffffefeffefffefbfbefffffaffbefffbfebfefffbeffbfffebfffeffffffebefffffbfbbefffbffbfefbfffefbfbeffeefffbffbffbfffeefbfbfffbebeffeffeffafbbebefbfffffbffffeffebaffefffffbffffbbffffbefffebfeffefffbaefffffeffefbffeebffffefffffffffbfebffbbffbffffffefeeffffaffefbffffefbffefffebf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask59077 : MertensSieve.bits 59077 = 0xfefffbfffbffaebffffebeffeffeeffebfefeffffbfffffbeffeefefbfeffeffffbfffffeefffbfebbffbfbbffffffefbefffbfebfeffffeffeffefbffffffbffaffbeffefeffeefffbffffffeffbffeffefffefefbfffafffeffefeefbffeffbfbfffffbbefeffffbfffeffbffffbeeffebffbbeffffffffefefffffbfffffffbfffefffffffbffbeefefffffeffffffebbffefbffbbffffbeefeffffffffeffaffffbefbffffebefffffbfffefffbfffbfbafbbfffeffffeffefffefffffffaffaefbebffbfeffffefbbffeeffefeffbffbebfffbefbfbafffebffffeffffbffffffebfefffbbefbffeffeffbffeeffffffbbffefffefbfffebfeffffbfffffeffbffffbbebbffffbeffefbbfbfebfeffffbfbfeffffeebfffbfbeffffffeffffbffeffbebfffeffbffafbfffeefffffffefbfffeffaffffbfffbffffffefefffefffbffbaffffffefbefeefeffbffaffbffefffffffffefffbfefbffffffebffbefffffffbbfffefefffffffffefbfbfffaffffbbfbfffffffefbfbeffffffebfffbffeebffffffbffeffffbfefffbbfffffeefffbefbfeffffeffffffeffffefffefbefffffffffbeeffebfffbffefbbeffefeffeffffbeffbfbfefbefaffffbbfbfebfffeffefbbebfebfeffffbfffefefbefffffbefbffefbbffffbbfffebfeffefaffeffbefefbfefbffeebffbfffeefffffffbefffffffbffaffffbffffffeffffbbffeffbeffffbefbfbffffffafffffffffebaffafffffffbfebeffffbefffffeefeffbfffffbfbfffeffbfffeffefeffbffbfbffffefffbbfffffbefffbefbfefffbefbfeffffbffeffbeffffffbeefffbeefbfbffffffffbefffeffffbfffffffbbffffbbffbfbafffffefffffffffefffbefbeffaffffbffffffaefaffbffffbfffeffbffeefbfbffffefbfbffbbebffbeffefffefbfffefffffffbfbfeffffbeffffbefffffffefffffefbffffefbefffbfffbefefbfefbfbefbbffeefbffffbffffebefbbfffffbfbbffefbbffafbffffefffffefefbffffebfffbefffbbebfffffffefbfbffffefefffffbfbffbfffffffffefffebfeffefefffffbfbfffffffefbfbffbbffffbefffffffffefeffbefffbaeffebfebfffeffbffffffffeffbfffefffbeffaeffffeefbfbfffbffeffbfffebfebfefbfbefbbeffeffffffffffffbffbeffeffeeffffffffefefbfffbffefffefffbfeffffeffbefbffefffffeeffffbffafbffffffbefefffffffffebeffeffbefbffffbaffafbeffffffffeefeffeefffbfffeffbffefbffffefeffffffffbfbfffbffffffefffffeffefbffbfbfffefbbffefbfffbfbefffffafbbfbffffebeefbffffffefffbeeffffbfffffeeffefffffebbffefbafffffaffbfbefbfefeffafbfefeffffffffffffefeffbffffbbeffebfebfefffbfffbfbfefeffffbbefbffeffbe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask67269 : MertensSieve.bits 67269 = 0xfffffefbfffffbaffaffeffbffefbfefefbfffbfffeffefefffefffbffbbefafffeffeffebeffefffefffffeffffffbbffffffffeefeffeebffffffffffffbfffefeefbffffbefbbffeefeefffbffbbefffffeffffbfbfebffbfffaffaefbfbffbfffffffefffffffbffaffeffbffefbeffbffffbbeffebfffeffffbfffeefefffffbebffffffaefffbeefffffffbefbffeefbfbffffeffffffbffbfefaefeffeffbebfefbffbffffffebefffefbffffbbffffbeeffffbfffffeffeffbfbbfffffffbfefffbeffbfbfebfffffbbffffffffbffbffefbfffffbeffeffbeffebefffffbfbefffffeebfefefbffbfefefbfffefbeffffffffbefbffbeffffeffeefffffffbfbfefaffbffffbbfffefbffbffeffffbfffbefffffffffffefefffffffffefefbefffffffbffbfffaffffbaffffbeeffeffffeefffbeeffefbfbffbbefeefbffaffbffffffffbeffffefffffffbbfffffbefbfbffbeffeffbebfeffebbffffbeeffffffffeffffbfbbffefffffffbeeffeffebefffffffbfefffffffffbbffbffeffeefffffefbffffbfefafffebffffebaffbffffffffeebefffffbffffffefaffaffeeffffefbbffbffbffffbefbbffbfbfffbefefffefeffbffbebffbeffefbefffeffebfffeffefffeffffefffffbebbfbefffffbfbfffbffeffffffffeefffffefbffaffeffbfffffbffffbbebfffeffbefeffbebffbfebfffffbbefbebeebfefffffefbfffffaefeffeefffffeffffbffffbbefefbbffeffbffffffefeffeffbffffbfffbffbffafbfebfeffefaffefffebeffeffbffaffbffeefaffffbffffffeffbffefffefffffeffefefffffbffffbbeffffbffbebffbfffefbfebffffeffefefffffbeffebefffffafbffbfefbffffffeffebefffffbfffffbefeeffefeffffbffffefeefefbfffbebfffaefffbefffebfffaefbffbffffbffbeffbffbffffbfefaefbfffffffbfffeffaffffbffbffffeffffaffbffeebeffefffffffbffbafffffaffffffeffefbffefffefefffffffbffffffeffffffffeffffbfffffffffaebfefefbbeffffbfbbfffffaffefbbfbffffffeeffffeeffffffffffffbaffbfbeffeffffbeebffffffbffafbfffbfbfeffffffffefbefffffffaffbfbfefefffffffbfffbffffbfefefbafbfebfffbfffffffffebefffffbffefbbfffefbefefffebffbffbbffeffbffffbefffffbffefffefffbfffffbbfbfefffbeffafbeefffffebbefffffffffbfeffffbffffbffffeffffbffffffebfffefffffbffbfbeebffffffffbfefffbeffffffebffbffbfffbffbeffeffffbffffffefbfbffbeefffbbebbfffffeffbfbfffbffeffbffeffbffbeffefbefffbafbfefeffbffeffbffffbffffffbffffbffbffbeffeffaffbfbffbfefbfbffbffbeefeefffffefbffeebeffaffbfbffffeffffefbbfffffffbfffefffeb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask75461 : MertensSieve.bits 75461 = 0xffebfffeefeffefbffbfffaeffffefffffffffeffffefbffbfefbefbfbeffbebfefbfffffefffebffffffbffbfffffeebfefffbfebbebffbbfffffefffffffffeffffefffefeeffefbfbbffbfffffbffefbefffeffffbfffffbfffffeffbffafbffffffffbfefffffebffbefbeffffbaffffffebafffffbfffffffffefbfffefffbeefeffbffffbbebfeffffafffffbfbefbbffafbeffffffffeffffffefbffeffeffaffbfffffffbefffffbffbeffffeefbfbaffbffeefbffbfbfeffebfefffffffffffffefbfffbffafbfefeebbffffffebbffeffbefaffbfffebfffbffefffefbfbffffeffffbfffffeefeffeffeffbffffbaffeffefbbfffebfefeffbfbfffffffffefbbebbffefbfefefffffffffffbeffffbfffeffefeffffffebffbeefbffbfffffbfbeffaffffffffffbeffbffffbafffefeffbeffffffbffbfffeefffbefbffffebaffbfbaeffeffeffffffbfeffffeefbefaffeffffffffbffefffebffbfefbffefbafffeffebfefffffeffefffbaefaffefbffffebeffbfbbfffffffbfeffffeffbffefffffafffebffffebfffefffffbffffbfffefbfffbeffeffefefffffbfbeffbffbffbebfeffebfffbffeefbffeebefffffffbbffffffefbffffbffbfffefffffaffbfbefbfffffbbfffffffbaffefffefbefffbaffefbeebfefffffefeffeffffffffffffffaebbfffeffefffffebbefeefeffeffbfffebfeffefbffffffffeffefffffffbfffefbbffbffaefffbffbfefeffeefffbfefeffffbbefffbfffeffaffffffefefbefffffbebbfbefffffbfbfffbfffffbffffbbfbfffffffffeffaffffffffeffeffbfffefeebfeffffeefffbfffbffefbefbbebfffffffffefffefefbfefbffffffffeefbffffbfffbffeffbefafffeffebffffefaffeffbfbffbffffffaffbfffffeffffffffbffffbefffffefbbeffffbeffffbfffefeeffffffbfebffbefbbeffffafffeffffefffffbffffbfefeffbffeffbfbfffbefeffffbfffeefffffffbeffffffbbffeffbfffffeffeefffbfeffefffbbffbfbbebffbfebefffffbffbeffffeefbffffbbffeefbefafbfffbefeeffffaffafbfffffbfffbffaffffffffbefeffbfbbfbfffbeffffffbffbfebaffefbafffffeffeffbffffbbffeffeeffffffffefeffeffefffffbeffefbefffbffbffffffaffefbfffffbefbfffffbfebfffffbfefaffbfffeffffeefbffeeffffefffeffffeffffbefbfffaffffbfffffbbeffffbfffeffffaeffffbfbbffefbeffbfbffffeffffaffffbfffbfbfebfffffbfefffffffbffefbffffebeefbffbfffefbffffffffffbaffbfffefbffffbbfbfebfffffffffbfbffffffaefafbbffbfffffeefbfffefffffffbffefffeffffeffefffffeefbefefbfffffbffbfeffebbffefbbffffbeffeffeffafbffffffbefbffeeffebefbeffbfbfffffbffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask83653 : MertensSieve.bits 83653 = 0xeefffbfebbeffffeffbffeeffffefffffbfbffbfffeffffffffbfbfefffffffbfbeebffffffeffefffefffbefffffffbaeffffeffbffbffeefbefeebffffffffbffffefbefbfbffffffeefbefefffffffbeffbffffbbebfebfebefffffafffebffffffffffefffbfeffefeffefbfffffbfffbffefbbefffbfffffbfffbefeffaffffbfefbffffffffeffffbffffefbeffffaffffbffbeffbffaffffbfffbffffffffbffeebbffbffbfffefeefffffffafffffffbaeffffbebffbefffffffffefffffefeffbfbfffbfbffbfefffbafbbffeffbffefffffbefffbfffefffebbfbefffffbfbafbbeffefbefffbbffffbfffbefeffafbfffffbfffeffbeffebfeffefffbbffbfbefffffffffffffffefeffaffaeffffefbfffbfbafbfffffbaffffffefbebeffeffbffeffffbfefbffbffeefffbefbeffbfbfffffffeffefffbfeffffeefefffffefbbffeefbffeffffffffefffefffbbefbefffbbffaffefbfeffffeefefbeefffffeffffbffeffffbfffbefffbfefbefeffbfffffaebbebeeffffbfffffbeffefefffffffffefffbaefbfbfffffffebfffaffffffffffbfffffbfefffbefffffafbffffffffbbffbffeffffbfffffffffaffbeffffeffeffffffebfffeefffbffbfffffffefefffffffffeffefffffefffbfefffffffeffffbffbaffbffeeffebfffbffbffefbfffffbeefefffeffffefffffbfbeeffffffbfffbfbbfffebfffeefbfbbfbffffefaffafbfefffffebbfffffaefbebfffbefaffffbfefefffffffbfefbefffbbffffbfffffbffffefffbeefffbeffeeffffeebffffffaffbfffffbebffffffafffeffebffbbffffbffbffffefeefffffebfffeffeffeffbfbffbfebbffffffffffffefeefbfbefffffefffffffbffbbffeffbffeffbfbfffeeffefffffffffffebffffffbffbfbeffefffffbebffffefeffbffeffbefeffeffffbfefffbfefeffaffeebfeffffbffbffeebbfffefbefefbbffffffefeefffbbfbfeffffbefbffeebffffffbefefffffffffebfefbffbfbfffffffffffffebffffefbffeffffffffefbbefaffafffffeffefffffffbfffefffefbfbffbffffebeffffbbffbebffbeeffffefbffffeffffbfbeeffffffbfffefffebbfbfebfffbffffffeffefaffffffebfffeffbefffffffffbffbbefefbfeffebeffffffffbffbffeffeffefbfebbeffffeffeffeffbeffeffffbffaffbefffbffffffbeffffffffffaffafffffffbfffafffefbfffffeffbffefbffbeffeefbfffefffbeeffffafffffffffefffffffbfbfffeffaffefbbfffefffbbefefbefbfefffbeffaffeffffffebffffffaefbfbffffffffbfffbfbfefaffbffbfbfebfffbffffbefbbefffffffefffffbebefbffffffefbfffffbbffefffffffbeffeffbfbffbfffeeffefffbfeffffefffffbffeeffefffffeffffafffeffeffffffbfe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask91845 : MertensSieve.bits 91845 = 0xffffbfffbffaffffbfefffffffefbfffbeffffeefbffbffffbeefbefefffefbffffbeffffffeffebeebfffeffbffbeffffbffffbffbbfffffeefbfbbfbffffebbfffffeffbfffefffffffbfbffffefeefbffefbbfffebffffffeffffffeffeffffafbfefeffbfffffffbfefefffffeffaebffbfefbffefbbfffffeffeffffbeefffbeffeffffbfefbfbfebfffaffaefbffeebfffeffeffffffebefffffbeffffffffefaffeebffffeffffefbffffebffbefffffefffffeffaffffbfefffbffbfffbffbefbfbeffbffeffbfbbfffebfefefffffbffffbaeffffaffffffeffefbfffffbefefbffffffbffffffffbffefbffffeffffefffffeffbefffffefafffffbffefbeffffbffbbfbffffffffbbfbfebfebaffefffefffffebfefbfffffffffeffffbfffffbffefffffaffffffffeebfffffbafbfefeebfffffbffbfebffffffffbbeffeffefbfffffeffbebeebfffffffffbfffffaffffbfffffbfffeffbfffeffffffbfefaffafbfffffbfefffbffffefeffffffffbfffefffbaefeffbefffbefffffbffffbbffeffffffffefbbffffbafffffaffbfbfefbefeffafbffffffbeffffffbbeffffbfffffffffeffebefffffeeffffffbfeffffeefbfbfefeefbfbffbffbfffefffffefffffefffefafbffffffeefeffefbbfffffeffaffbffbfffebffbfefeffefffffffffeffffbffffbeffbfffffeeffeffebfffbffaffbfffefbefbffffbfefeeffefffffffffbeffaffafbfeffffffbfefbfbeefbeffffffffffffbfffeefeefffbefffeffefeffeffbfbbffffbfffffbbfbbeffffaffeffbeffefeffbffefffffffbffbfefbfffffbfbefbeeffffbebffbeffbffaffefffffeffbffbffffbbefeebbffbfbffffffffbeffefbbefffffffeffafffeffffffbbffefffefffffebeefffbbfbfffeefeefbfffffbffffbbffefffefbffffffffaffffffefeffbefffbfeffebffbaffafffefffffffbefffbfffbebefbefffffaffffbffffffafbffbbeffebfffbfffeffefefffffeffbffbefffffffefffebffffffeefaffbffffbfffbefefffefffffebfefffbbfbbfffefeefffbfebfefeebfffbffffbfffffbfffafffffbfffffafffffbffffbfffaffffbffffffffffefefffffbeffffeffffbaefffffefbffffbeebbebfffbffffffffbfbffbfffffbefbfffffffefefbbffbffffbaffffbeebfebfefffffffbffbfbfeffffbffbebfffeffbefefbeffffbefbffffffffffefefbffffffafbfefffbefffffbeffffffbaefeffffbfeffefeffaffbffbefefffefffbeffbfbeffaffaffeffbebffbbffffffeffeffebfefbffffffffffbbffeffbffbebffffffbffbeffebffbaefefbeefbffefffefbffeffffffeffffbfbeefbebfffbffeffaeffffeffbfffffbfbbfffffbeffffffbfefefffffefbeffffffebeefbfbbfffeffeffffffffefbfffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask100037 : MertensSieve.bits 100037 = 0xfbefbfbfebbfbfffefffffbfbbfffebfffeffbfffeffffeefffbfebbfbfffeffbffffbfefffbbffffbefffefefbfefffbaffbffffffffbffeeffefffbefffffaefffbefbfffbfffffbeffffeffefbbfffeffffbffffffffffffebfffffffefbffeefefffffffffffffffeffffefbbfbfffbffefffffffbeeffffbfbfffbfffefeefffbffbfffffffefffbbfffebfeffefaffeeffffeffeffffffefffbfffaefeffefffefffbbfffffefbbebefffffffbffffefffbafffffbebbfbffbeffffbbeffeffefaefeffeffbebffffffbfffffffffffaefbffffffefffbfffffffebfefefbfefbffefbfffefbbefeffffbfebffbbefbffaeffeffffbfffffaefbfffebeffffbfffffffefaffefbfffbffffffffffffebffbefffefffbefbbffeffbffefffefbfbfffbffbfbfffffffeffefffffffffffebeffbfffefbfffffeffbfbfefbffeefffffffbefbefffffffffbefffefeebfefefbbfbfffffbfffeffefffffffbeefeffbefbebfffeefbfbbfffffffffefefbfebffbfebfffbffbfffffefbfffffbefffffffbfeffffffbfffffffefbfbbffffbffbfffbffbefbffefffefbffffbffbfeffffaffffbbfffffaffeffbeffebfffbffefbefbbefeffaeffffbfbffbfffbfffffeefffbfffeffafbeffbffefffffbffbebffbfffffffffeffffbeffaffefffffbffffbbffaffeffbefffffffffbbebfffffbfffffbbeffeffebfffffbbefbfffebffffffbefbffeffeffefbeebfebfebbffbfffffffbeffbffefffffbfffffaefffffebfefffbfffefffffffffffbffffbbffbeffeffefbfbfffffbefffffbfbeefbefeeffffeffffbffffffbffbffefbffffffaffeffbebbffffffefefffefffbffbfffaffffffffffffefbffeffffffffbefbffffffeffffbfffffbebbfbfebfffefbffffffffbeffffbfffbffefffffafffebffffffeefbffbfffeffeffffbffeefffffefaffffffffffffffefffffaefbffefbbfffffffbbffefbfffffbbfbbfbeffbffffbafffeffffeffbffeefffffebfefffffffbfbffffefeffefffebeffffffffbebfefeeffefffbafbfeffffeffeffbfffefffbafffffafbfebfffbffbfbbeffebffbfefffbeffffbfefeeffffffbffbeefbfffffaeffffffbfefeffffbffffebeefffbbfffefeffeffffbfeffefffbfffbfbbfffefeffefffffeebbffeffaffefbeffbfffeffffeffbfbffbfffbefffbbffbefeffbffffffefbebefbffffffffffeffebbefffbfeffebfefefffffaebbfffefeffffbffbfffffbeffeffbffbefffffefffbefbbffefbffffffffffffefbfffefbffbfebffbfffefffffbefefffffffbbeffffeeffffeffffffefeeffffbfffffffbfebfefffbafbfefeffbffeffbffbffffffefbfbfebffbfffaefffbfeffffefffefbffbfbbffffffefffffefbffeefbffefffebffffeffffefbfffffffeffefefbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask108229 : MertensSieve.bits 108229 = 0xffbfffffbeffbffbfbfeffeffffffffefffbeeffefffbbffffffffeffaffeffbfbfffeffbfffefbebfeffffffffffbefffbfffefffffbebfffbffffffebffffffaffbfbaeffebeeffefbfbffbbffeffaefafbefbfefefbfffffffefffbfffbeffffefbfffeffaefeffffbfefefbfffffbfefffbffffffaffbffffffefefffffbffffffffaffffbefbbebfefafffffbffffbfeffefffbffbfeffffbffffbfebfffefbbeffffbffffbffbeeffffffffebeffeefffffefbfffffeffffffeffeffefbfffffbffbffefbfffeffafffefeefeefefbffffffefffffaffbfbfebfefafffffeeffebefffefbfffefbffffffffffffefbfbefbfffbfffffffbffbffffffefbffffffbffeffbfbffbfffeefeffbffffffefeefffbaeffffffbeefffbffffffefffffefbeefbfffffaffbfffeffeffefbffefbeffbffeffeffefbbfbfffffffffffbeffffbfeffefffbafffebfeffffbfbaffffffffbfffffeffbfffffafffffffbfffffbfeffffafffffeffeefefffffbffefffeffffeffffffffaffbfbafffeffebfffffffffbfbffffffffffefbffeeffffeffeebbebeebbffbfbefbfffeefaffffbffbfebffbaefbffeffffbffbfffbffbffbebeefefffffeffffbfffbffbfffffbfbffbfffbffafffeffffffffffffbbfffffbefffbffffeffffaffefbeebffbfffbffffffffbeffffefffffbffffffeffffffbeffffffffaffeffafbbfffffbefaffbfffefeebeefffbfefbfbfffeffffbfefffbfefeffbfbeffbfffebefffffffbffbffffeffffeefffbeefffffffbeffffefffffafbeffbffeebefffffbfbfebefbfffbfffebfefffffefffffffbfbeffeefffbffbffbeffeefffffffffbeffeffeffeebbffffbfffffbbfbbfffeffffffffeffffffbeefffbefffefffffffafbfefffffebfefbffffbbffffffffefbfffbebfefbffbffffffffeefbffafffffffffeffefeffffbbfbefbaefeffbfffebfffbffeffffffebefbffffffefbfffeeffffaffffbffffffefffffffbbeffefbffefbeffbefeebbefffbfefbfffffaffbffaffffbfffeefbffbffffffffffffffbffffbfffaffbffffbfefeefeffbffeeffefffffffffbffffefffffffeffbffffffffbffefbbfbffbfffbefffffffbfffffeffffbeffffbeffbefbfbfefffbfebaffaffbffbffeefffffffffbfeffffeeffffffffffeffafffffbfffebfeffefefbbffbffffbeeffffaffbfffffeffafffebfefeffbfffffefbbfbffbbeffffffbfefeffbeffffbffbffefffffeffffbfebffffffaffbffbebeffeffbfbefffffeffbffeffefffffeffeffbffffbbebfebbffefbeffbffefbaefefbffffffffbeffffbbebffffefeffbffbffbfffebffffffeffffffefbefbffffffffffbfffbffeeffefeeffefffbaffffffffaeffffbfffefeffefffffaffffbffbbfffffffffefeebfffbfbfffbffef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask116421 : MertensSieve.bits 116421 = 0xffefffffeffbeffffaffefffeffffeeffefbffbffbffeebffffffffffffffbbffafbaffffffefaefbffeffffffebfffbfffefffbeffaffbfffefbfbeffafffffeffbffffbffffffffffeffffeefefbbeffffeffeffbfbffbfffffbfffffbfeffffeefeefffbffbbffffffeffffeebbfbffbefffffeffbefefffefbffbfffefeffaffffffebbffffbfefffbbebffbffffefeffbefbfbffbeeffffaefffffffeffffbffbbfffeffffeffbffffbfeffefefbffbffffeffffffbfffbefefffffbfbeffffbfeffffbffeffbefffffffbfbeefffbfefefffffffbbfffebeffeffbefbfbffffffeffefffefeffafffffbfffefefffffffbfebfffffffffaffaffffbfffeefffffefbfffefaefeffefbfffeefbfffffffffebeebfffffbfffbffffbafffffbffffbefbbffbffffbffbfebaffffffefbfffebfffbffeffffbfffeffefffebfebeebeffbffeeffffffbbffaffefbfeffeffffefbfffbffeffbffffffffffffebfffffbffffffffbeffbffeffbfffffefffffeebfeffebfffbffafbffbefbfffbfbfffbefefbfffefffefbebfffeffffbfffffbfebfefafbfefbefeeffffbfbffbbfbffffffefffffffffefeffaffefbffbfffbfffffffffefffbafffffbfffebefbeeffffefffffffbaefeffaffbfbfeffefbfbffbbffeefbefbfffffffbffbbffeffafffefeeffffaffefbfefffbeffffbbffbffffbfefefbefbffbffffffbfbffffffeffffffffffbbffeffeefbfbffbffffeffffbffbffffbeffbefffffffbffeffbffeffbeffefffbbeffffffffeffffbefbffaffbfffebefffffefbfffeffaffbfbfefffffefafffffffbfeffeffffaffbfbbffeeffefffbfebffbffbfefffbffffebfebfefbffaeffffefbfefbffffbffffefbefafffeffffeffbffeffffffffffbfffeffaffffffeffffffbbffffffffeffbffaebfffffbfffffbeefbffffffffbfbbefffbffffffafffffbebfebbffeffeffbfbefbffffffffffffefbffffffffbbffefbaefbfffeffeffffbffbffbfffebffbffffffefbbfbffffefeffffbbefeefeffffffeffebfffbffefbffbffffefbffeffffffffefffffbfbeefffffefbffaffbffbffeefeffffbffffffffffeffffeefffbeebffffffbebffffeffffafbfffbffffbfffffffeffeffffeefbfbeeffffffffffaffaefffbffffeffffefbffbfefaeffffffbfebefffffaffeffbfbeffbefbffffbbeffefafffffbebffbfffbfffffafffffffffefbfbffffebfeffefbfbafffffffffffffbefbbffefffffefffebfefefffffaffbffbfffffeffeffbfbfebfffbffefbfebfffffbbffffffefbfbfefefffffffbfffeffaefffbefffffeefeffeffbeffffeebbffbfbffffefffbfffefffefbfbfffbefaffffffffffbeffbffbffbfffebeffffbeffffbffffffffffefffbffffffeffaebfffffbfffbfbffbfefffbbefffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask124613 : MertensSieve.bits 124613 = 0xffffffffffaefaffbfffeffebeefeffbffbefffbfefbfbbfbbfffeffffffffffbefeebbffbffbfbffffefffffffafffeffefbffffbffbbefffbfffafffefffbffbbffffbeffbefeefffffffbfffffeeffefbffefffffeefbfffffffbffbfebffffffbfffefffffffeffbffbebefbfffeffbebffffffeffeffafffffffffefffbafbffbfefbffbfffebbefffbfffbffffffebffbfefbffffbfeffffeffffbfffffbffbeefeffaffffffebeefbfffefffffffeffbfbeffffffffeefbfbeeffffffbfffaffffbfefeffbfffffffbffffefbffefffebfefffffffbfbbfffeffffbffafffffbefeeffefffffffbffffffffffffefffbfffaffeffefbbffffbbffefffffffffefffffffbefbefffffefafbbebfebffffffeffbfffffefbfffbfbeefffffefbefeffeffbfbfffbffaffbffffbfebbffefbefffffffbbfffffbffbebeffeffffbffbfebfffbffbfffffbffffbefffffbffbfbeeffefbfbfffbeffffbfffffffbbfbefffeffffafffefefbfffffffeffefffffffffbfefffffefbefeffeefffbffbffffffffbffffffaffafffffbffeebeffffffefffbeebfefeffafbffffefeefefbbffffbfffafffffbfffefffbeffffffeffffeebeefffbfffffffefaffeffeefbfffeffffffffffbebefffefefbffffeffeffefffbffbfefefbaffaffbfbfebfffbffffbfffffbeffeeffffeebffbefffffffffffbeffebffffffefffffeffbefefbaffffffefeffffbbfbffffffbffaffffffebfeffffefbeefbeffeffefbfffebffbeeffeffffffbbebffbeffbffffbbffefffeffffafffefeffaffefffefffbefbffffffbebffbffffffffffefbffeffefffffeffffbefffffbffffbfefeffffffffeefbfbfefbeffffaffbfffffeffffbfffbfbefbfefafbffbfebfefbefefbeffffffebeefbfbbffffffefeffefffffbffefbeffffffefbfffffbffffbbfffffeffbffffbffbfeffffeefaffefbfeffebefffffaffbfffeffffffbeffffbeffbffffbffffebffffffbffeebfffffffffefffffbeffefbffffbfefffffffffffffafbffbffbbfffffffffeffffeefbfbbefffbeffbffbfbffffffeffeffbfffebfeffffbfffffffbbefffffeffffbebbefeffeefffbfeffefffffefffffffffbfefeefffbefbbffffffffbffefffefeebbffbffbfffffefffffbfbffbbffffbfeffffbffbffffbeefbfbbebfefffffffffbbfffefeebefffffaffbfffffbfffffffffefeffbffaffefffffeffbefbffefbbffefbbffeffbfbfebffbeeffffefbfffffffffbffbffbfffebfeffffffbfffeffeffefbfffbfbffbbffbfffefffbfeffffbfbbffbfffefeffffbffbfebffbeefffbfffffffefeffbffaefbefefffffffbfefffffeffefffbffbbebffffffbfffffffbfebfeffffffffffefbfffffbbffffbeffaefaffbefffbfffeefffbbefffbeeffffffbfefffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask132805 : MertensSieve.bits 132805 = 0xfefbefffffffffbfeffffeffeebffffebbfffffafbbffefffeffffbeffebfffeffaffeffffffefaefffbbffffbfebfefbfbfefbffffffefafffefbeffffffffffeeffffeefbffffbafbbeffffeffffbffbffbeffeeffffefffeffefbffeffeffbefffbfefbffefbbfbfffbffffbffbfffffffffaffeeffffffffffeffbfbbeffebfffffbbfffefffbeffbfbffbfefffffefbfffeffefffbffffffbefbfbfefeffefbefffeffffaffffffffbfbfeffefaffffbfffffbfeffffffbfefefbbfffffaffffbfefbffeffeefbfffebeffffbbeffffeefaefbfffefbfffffefffffffffebffbfefeffffffffeffaffeffffbffbffbfffffffeffeffffffffffeffbfbffffefffbeffffbeefbffefbffffeffefefffffaefffffffbfffffbfbbffffffffffbbfffefffbeefeffeffffbffbeefafbbffbffffffefbffeefffffefeffafffefbffffbaffefffebffffeffefffbbfbffffefbfffffffbbebffffffeffefbfebfffbefffbbfffffefbefffffafbffbeffeffffffffbfbeffbfffffeffbefefbfffaffffffffeebfffeffffbbfffffbffbffefbffffffbefffbfefbfbfffffffffbefffbeffbfffffeefbffefbffffffeffffbffbfffbfbefffffefbbefffffefffbefbbffefbbeffebfffeffffbfffffbefffffbffbffffbfefeefbfbefffffefbbffbffaffffffebfefffffffffffefffffffbebbfbeffbffafbffffffffffefefbbfffebfefeffffffebfffffffefefffebffbefbfffafffebfffffffefaffffffefffbaffffffefffbffbeefbfbbfbfeffffaffbfbfefbfffefeefffbaefffbeffeffbfbeefbfbfefbfffffeeffefffbfefffbeffbffeeffefffbfffffbefffffbffbefffffebfefffbfefbffeffffffffafffffffffefefffebffbefbffffffbfbfeffefffffffbffbefffffefffbffbbebfffeeffffffbfeffebfefffbeefbebeefeffbffbfffffefffffbffeffffbfebaffefffebbfffefbffafffffbffeebfffeffbfffeffffaefbffefffeffffeffaffeeffefefffffbffffbffbfffeffeffeffffbfefbffeffaffbfbfefffffffffbbfffffaefefffffbffefbfefbffafffffffbfffeffefffffeffeffbfffffbfbfffaefefffffffbffffffeffeebbeffffffffffffffffefbbffeffffbffffffbeffffefffebffffffafbbeffebefbfffffffebbfffefbefffbfffbfbefbfffbffefbfefefffffeffffffffeebeeffffbefbfbeffffffffbeffebffbbffefffffffbfffffffffeeffffeffbffbfffebfeffffeffeffffffffeffbefaffefbfffeeffefefffebfffffffefffbffbffbfffafffffbffffbeffefffffffbbfbffffefffbffbbfbffffffaffeffbebfffbffffbafbfefeffeffffffeffefffbbffeffeefffffffeefefbeffbffeeffffbffbeffffefffffeffffbbefeebfffeffffbfffefbfffffbafbfffefffefff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask140997 : MertensSieve.bits 140997 = 0xfbfeffebeffbfffffbebfebffbfefeffaeffffefbeffbffefbffffffeefefffebbefefffffbfffefbebefffffeffefffffeffaffffbfffbffffbaffbfffebffffebbfffffbefbfffefffffffbefffffeffefbffeeffeffffbffaffeffffbfeffffbfbbffbefffbefffffbfbffffffafffffbffffffefbffefffffbebefffffbffeebbfbfffbfffffffbffbeffafffffffffefefffeffffeffffffeffeffffbffffffffeffffbbeffffffbfffbffbefbfbeefeffffbbffbfffefbffefffebfefffbfffeffeefbfffffbffbffefbbefffffefffbfffbefffffefafffffffbfefeefbffefffffefbeffbffbfbffbeefbffffbfefffffebeffaffeffffbfffbffbffafffffffbfefefbfeffffffbfffaffffbffffebbefffffeffefeffeefffffebfffffffefefbeefffbffbefffffeffbfffefbfffffbfffeffffaefefffffbfbffffefefbffffeffffbffffbbffbebeffffffffeffffffeffefffbeffbfffefaffeffbffbfffffbefeffafbfffefffffeffbfffefeffbefbfffeffeffffefffffeffffbefffefffbafbfffeffaffaffffbbfffebbffefffebffffffbeffffbfffefffffffefbbffbfbffffefbffaefffffffaffefbfffbebfffeffffbeefffffffaffeffeffffffebbffbffeebfefffbfefbfbbfbfefeffbeffffbfbfeffffeffeffffffffffbbffefbfffbfbeffffffffbefbffefffefffffffffbeffeffeffffbffffefbffffbefbfeffebfffffbfefbeffffeffbffeffffbfebbffffffffbfbfeffeffffffbffbeffbefbffefbffbfefefffffffbbfbffffffeffffbfffeefbefefbffffebffffffbffefffebfffeffbffbffbffeebfffffbbffffffefeffffbffbbfbfeffffbffbefbeffffbffffbffffffeebafffffbffffffffbffffffebfefffffefbfffefffbfffeefbfffefbffffffffeffffffebefffffffffebbefefbfefbffbffffffffbffeffbfbffbffbfefefffebffffeffefefffeffffeebfffbffeffbfbeefaffefbeffbeffffbfffffbeffefffbffffffefffffeefffffffffbbeffffaefefbbfffffffffeffffeffffbfffeefffffebbffefffffffbfeffffffffffffffeffebeefbffeffbfffffffbbefffffebbfffffeeffffffbffbfebfffbffafffffefffffbffafffffefffefffffffffbfebeffafffefbfbefbbefeffffffefffffffefffeffffefbeffffbffbfeffeffefffffffbfbffffeffffffbfffffffefbfbefbfffeefbffeffafbffffffbffbffafffffffbeefeffbfbffbffbfffbffffbfebfffeefbffeffbffffffffbfbfebfffeeffffbfbfeffffeebefffffffbffbfebfefeffafbbffeeffefefbbeffefffbffffffffbffbfeffffaffafffeffffeffffbbfffffeffbeffffffbffbeffffffffbfbbeffffbefefbefffefeffaffeffbfffebfffeeffffffbfefffbefffffbefbeffffeffffbffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask149189 : MertensSieve.bits 149189 = 0xffffbffafffffbefffbbffbffaebffbefbbffaffafbbfffefeefffbffffefefbfffefbffffeffffeefaffeffffbefbffffffbfbbfffffaffffffeffebffbffffffffffefeffbeffffafffefffffffefffefbfbffbbffbfbafbffbfffeffbfbbfffefeeffefffffffffbfffeffbfffebbffffbffffffefffebfffffffffffbfefefbfffeffbffbffffffffeffaeffeffebfeffffffffffffffefbffbfbbfbfeffffeffffbfebfffefffffbfbbffffffffffffffffffffeffffffebbfffffaffafffeffeffefeefffbeeffffffbeffbfbaffbfbeeffffbfbeeffffffbeffeffbeffebfeffeffffafffeffefeffffffeffefeffbffffbfefffbffbaefbffffffffefbfefffbbfbffffeffffbffffbffbfefaffbffffbbefefffeffffbfffffffbaffefffffbffffbfefefbffbfefffffffffbeefbffffffefffbeebffffefeffffbfffbfbfebfffefffefbffefbbfffffbfbfeffebfffffbffffebefffffaffbebffffffbffffbffffefefbffffffbffffbfffbefefffffbffeeffffbffbeffefeffbffbffaffbffffbbffefffebffffffafffffaeffffffbfffbffeffbebefbeefffbfffbfffffeefbffffffffeebeffefffebffffebfefbffffffefffffefffffffffffffbefefbbefffbfffeffefffffffffefeffffbffbbfffeffffffbefffffeefaffaffbffbfffeffefefbeffbeffebffffffbfbffbeffbeffffbeffffffbeefaffbffbfffffffffffffbfffffffffbffeeffffefbfffeffeebbfbfffffffffffffefeefefffffbefbebffffffeffaffffbffffefbfbaeffebfeffffbfbeffbffefffffefbeffffffffeffbffefffebfefbeffffafffffffbbfffffbebffbfffefffffffffebfffaffefbaffbffeefeefffbffffffffffffbffeefbffffbfffeffbfbffbeffbefefbffffffffbfffffbffbfffeffaefffbffffebfebfefffbfffffffebffffffaffffffefaefffbffbffffebefffffeefffbffbbffaffffffffeeffefffbfefbefefbfffbfbefbffffebbeffffbeffefeeffefbfbeffbfbfffbefbffffbfffeefbfffffefbfebffffefffbaffffffffbffeffbeffffefbaefffffeffeffeffffafbeeffeffffefffffffbfffffffefafffffbffeebfffaffbffbebffffffeffbffbefeefaffefffffbffefbffffffefbffbfebfffffbffffefffbfefffffffffbfefffffffefbbfffebbffbffbfbfffeffbefffbefffffeffffffffbfbbffefbeffffbaefffffffbffefbffffebffbfffffffffbfbfffaefafbeefffffeffffbffffbfffffbfefafbeffbefeffefffffffbfefefffffafffefffbfffeffaffbeffffefbefffffaffbfffffbffbffffbbfbfeffffaffeebffffeffffffffffffffebbffffbfffffbfffaffbfbfebfebfffbefafffffffbfffeffffbafbffbeffeefbffffbfefeffbffeffeffbfffeffefaffbfffffefffeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask157381 : MertensSieve.bits 157381 = 0xeffbebfefefbbffbfffffffbfefbefefbefffffffffefbfbbffbfffefbffbffeebfffefbfffffffffbffeeffffbfbffffefeffeffffffefffffffbffefbbffffbfebeeffffffffebffbfffffbfeffffffffffbfffeffeffffffffffafbfeffeffffeffffbbfffffbffefffffbeffffbefffbfeffffffbaeffffbffbeffefffffffffbfffeffbfffffefbffffebbffaffbeffffffbfefbfbefffeffffeffeffbfbffbffbfffaffbebffffefeffbfbfefffffebffffffeeffffeeffffbffefbffbfffbffbffeebbebefffffffffffbfffefeffffbffbfebefbefffffbfbffffefeffbfffeffefeefffffffeffffbeffeffffbeefbefeffeffffffefbeffffbfffffefffffffbaefeffffffffefffefafbfeffffffbbffbffeffbeffebfffffffffffbfefbffffbffbffbeffeffaffffbbfffebfefefffffffffffaffffffffbebfffbefefffebfffffbfeffffeffbeffefefffffbefbfbfefafffffffbbfbffffffaffbfbbffeefbffbfbefbffffefeffefbffbfefefffefffbeefffffebbeffffbeffffefffefbffbffffbefffffafffffffbfffbfffffffffffeebfefefbefbffffefeffeffffffffffffffffbfffffbfeffffbffbffffbeffffffffefbbfbfffbefaffeffbfffffaffbffffffebeefffffffbfbfffffbfffffbbebfefeffaffaffeffffffffbfffffbfffebffbfffbffbfbfffeefaffffbffbbefffbbfffffffbfebeffffffffffbbffffbfefffbffffebeffbffefbffffefffbbfffffeeffeffffeffffffffbfbfefeefffbffffffefbfffbffbefbfbefffefeffefffeffebfffffffeffffffbbffffbafffeffffeffeffeefbfffefefffffeebffbfffbffaffeffbeffefbffaffaffbebfffbffbfbbfffffeffeffffffffbfbfffaffffffeffeffffbffefbeffbffefbfefffbfffffbeefffffffffffffeffbffbffeffbeffffbffefbbfffefffffefffffebbebefffffefffebffbfefefffffafffffffffefbffffbffbffffffaffeefffbefffffbffbebbfbeefbfffffafffefffbeefffbfebbffffffffafbeffffffeffffafbfeffebfffeffffbbfbfffeefbeffffefbfefffbbffeffffffeffebfeffffbfbfffefbffffffffffffefbbffeffbebffbfebeefffffffffbefffeffffbefffbffffffffbeeffffeffefffffbfffefffbbffeffffffefffbbffefbfffffffffbffbffefbfebfebfffbfffffffbffffffffbeffbffeffeefbffefbfefefbbffbffeffbfbffbfffefffffffffefbffeffbffbffefffffbfbafbfeffeffffffbfefffffefeffffbfebbfffefeffeffffffeffffaffefffeffffffffefbfffffbfffeffefefbbfbfffffffffbfffebfffffbeefeffeffbfffffeefbfbfefffbefffffafffffbfbeffeffffffffffbfebfffeffaffbfffffffffffbfbfebfffbffffbbefffffefbeffffefffffeebfffbfffefff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask165573 : MertensSieve.bits 165573 = 0xfffffaffefffefbfbffbbffaffbfbbfffeffeffffbfffffeffeffefbbfbffffffeefbfbfeffffffffffafffffffffffffffffaffbffffffffeffeebfffefbbffefffffffbfebfffafbeffffffefeefffffffffbffbefffffbefffbfffafffffbefbefeeffffffffeffffffffffffbefbbfbeeffffefffffbefffbffffffbfbfeffffeefefffffbefeffbefefbfefffbffbbefefbfeffefeffefffffaffbfffefffffffffffebefbaffbffbfffffefffefbfbffbfefefbfefffbbffffbfffbffffbaefffbfffeffaffeefbffffbffffffeefffbfeffffeffffbbeffefefffffffffffffbfefefbeffffffefeefefbffbfffffbbffbfbbefffffffaefffffefffbefbfeffffbebffbeffeefeffeffffffffbffbffbeffebfeffeffffffbfefeebfffeffbffbfffffaffffbfffffffffeffeffeffffbefffffbfbfebfffefffffffbfffffbfebafffffffbffffffbffbffafffffeebbffefbfffbffffffffbffeeffffffbefffffbffbefefffefbfbeffbffeefefffffeefbebfefefffffffbbeffeffffefffffbefefbfffefbfffffbffffefbffaffffffefbefffbfeffffffbeffffffeffffeefbffafbfebbefffbffffffbefffbffbbffefbbfbbffefbfefeffbffbfffffeffffbffbfebfffeffffbeffbfffefeffffbffbbffffffefbfbeefffbeeffffafffffffbfffbefbfbeffffffefbefefffebfffefffffefffebfefffbeefeffbefbffffbfffbfbfffbffefffffbfbffffefeefbffbffefffffffbfffeffbfffffeefeffffbbffbebefbfffffbfffffbfefafffffaffffbfffeeffffbfbffffeffffbffeefffbfebbffefffffffbfebbffbffeffffffffbefffffeffebefbfffefbffbfffffffffffbffffeffefeffffbefbffbefffeffffeefffffffbffaffefffebfffffffffbfffefefbbfffffbfbfeffffbefafffefffffeffffbffffffffefbfffbfbffffffeffeefefbfefbffffbfffbffeeffffffffffbfbfffbfffeffffefbffbbfffffbefefbfeffffffbfffbfffeffffffffefbffbfbbfbeffaffffffffffffefefffffafbffbffbfffeffffbffffffbefffbffffefefbaffbffeeffffffffffffbefffefffffffbfbffbffffefaefefbfefbffeffefffffffffebfeffefafffffffffebeffeffffffefefffefbffeefffbfefffffffaefbfbffbeefbffffbbfbeffaefefffffbfbefbfffeffffbffbfefffffffffbbefeebaffffbfffbfbfffafffffffffebfffbffffbfefffbfebfefffbffbbfbeefaeffffffbbeffffefffffffffffffbfffbffeffffffeffefefbbefffffffbefafffffffbfffaefefffefffbffbfeffffbffbfffefbffeffefbbfffffffffffbfffeffffbffffbffbbefefffffffbffffefffbeffbffffffefffbbeffffefffffeeffefbffbffffbffffffeffffffebeebaffffffefbffeffffffffefbfeffebfff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask173765 : MertensSieve.bits 173765 = 0xfffbffbbfbeffbffafffebfffffffefffffefffffebfefffbafbffbfefeefbfffefffffebffffffbffffbfebbfffffffffffeeffefffbfeffebfffffffffaffffbfffeffeffaffbfffffeffffffffffffffaefffbeeffffeffbfffffbebfebeffbfffffefffeffffbffffffffbeffffafffffbfbffbfffaffffffffffbfeffffffffffbfffffbffbfffffbffffffffbffaefffbefffffaffffbffffffefffffbffbffffbfffefbefffffffffffefbfffbebefffffbfbefbfffeffbfffffeffffbefffffbffbfbfefffbfefbffefbbfffebeffffbbffbebeffeffbffffffebfffefffffefffffffffeffffeebfffeffbffffbfffbebfefeffeffeebbfbfffbefefbafffffffffffefffefbebefbefffffbffffffefbeffffafffffeebfffbffafbfffeffbffffbfebfebeffbffefffefbfbffffefffbbfbfefeffeefeffffbbffeffaffeffefbfffffbeefffffffbeffefeffffbfeffffeefbffffffefbeffffbfffffbfbbfbfefbfffffefbfefeefeffffffffbffefffffbffbebfeffebbefeffeefffbefffffbffaefbfbeffefffffeefffffffffffffeebfefffffffffbbffbefeefaeffffffbbebffffefbfffeffeffebeffefffffbebffffefffbeefffffffeffafffefbffffbeffeffffffebfebfffbfbfffbffffbbffeffffbfefffbfefffbfebffffebffffffafffeffffefffffbffbffeefbffeffeefbffeebbfffffffffebfffbffbffefbbfffffaffffbbfffffffffffbffafffffffbfffffbffffeffeffffffffefffbefffffbfffefbefefbfffffffebbeffeffffffbbfffffffbfefffbbfffeffffbffeffeffffbfffbefaffffffffefbffffffffbbffeefeffbfffffffffffbfffffbebbfffefbeffffffbfffefbaffffbbffbffffffefefffffffbfebfefaffafffffefbeffffffebffbffffeffffffbfeffeffffaffafbfffefffefaffefbfeffebbefefffffbebffffffbffaeffeffefbffeffeefbffeebeefffbbffffffffeffffbeffbefefbeffbffbfffebefffffefbfffffffebeffffbfebbeffffaefffffebffbfffaffeffaffffbfeffefbfffefffbeffbefeffffbffffffafffffaeffffffbbffeffbfbbffeffbffefffebfeffffeffffffefffffffbffffbbffffbeffeffffbfefbffefffffbfbfebffffffeffefffefbfffefbffbffeffbefffffffeffffbffffffffffffffffeffeffffffbffffebfebefffffbfffffeffbffafffffffbfffbffaffeffbefefffeffffbfbffffefefffffbfffffefbaffeffefffeffffbfffffbefffbeeffefbffeefffbfffbffaffffffffefbffffffffbbeffebfefffbffbfffefbfffefffffbffffbfefaffffbffbfefeffffbafffeffffefffffeffffffeffefefbefffeffffeffbffafbbeffebffffffaffbffeffeefeffffffffeffbefeffefbfffffbeffbffbffbfbffbfffffbaeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask181957 : MertensSieve.bits 181957 = 0xbfffefefffffeefffffffbffbffffbbffffffefefbeffbeffebfffefffeffefffbeeffffbebffffffbeffffafffffffbfefffbfeffffeffeefbffffbfefeffbfffffaefffbeffbfffffbffbfffefbefefffebffbefbbfffffaeffefffbeffaffefffefeebfeffffffbbffffffffbffeebffbfefbfffffbffbfffeffffaffbffbffffffffffffffbeffffafffffafbffbfffbfffffeeffebefbfffbffffbffffefaefffbfebbfffffeffbffbffbffefffffeffbfbbefefbeefffffeffffeffeffefbfffffbfffbffffffefbfbffffffbfbfefffbfffbefbffeffbeffeffffeffbfbfffeffbefbfbbfbfefeffeffeffffffffffffefeffbfbffbffbbefffffffbffffffffffffffffffefeefbfffffbffeffbffbffffbbeffebfefffbefbfeffffbffffbffffffefbfffffbffbffffffeffbffbffbfffefeffbffaebfffffffefffffefffbffbfffbfffefbffffffefafbffffefeffbefefffefbfbefbeffeffaffffffffbfffffeeffffffffefffbafbfffeefeefbfbffffebeebbffbffffbfefeebfffefbfffbfffefbffffffffffbffbffffffeffffffefbefaffbfffeffffffffffbeffffeffaefffbfefbfffebeffeffbfbfffeebfffeffbfffefffbaffeffffbffffffffffffffffebfeffffbffeffffbffffefbffaffffffffbfffffefbfebfffbffbffbefbfbfebfffbffffbbfffffaefefffffffbefbbeffffffbffffefeefffbbefbffefbfffbffafbbfffffbefffbeeffffeeffffefffebfebefffefefffffbffeebfefffbffbbfbeffaeffffffbfeffffefffffbefffffebfefbfbbebbfbffffffbfbeffbfffffeffeffffffefffffffafbbfffffffbbffefbbfbfffffbfffffbfeffefffffffefbeffbefeeffefbfbfffffbfeffefafbefbfffffbefffffaefffffebfefeffffffffeffafffffbffffbfffbefafbffffffffffefffffeffffefbeffbfbfefbfffeffffafffebbfffebffffffefbbfbefffffffbefbffffebfefffbfffbefffffefefffffffffeffffbffeeffeffeffffbffbebffbfffeffbffffbffbfebefffffeeffffefffefbfffffbefefffefffbbfbfffefbbfffffbebffbfefbfffffaffbfffffeefbfffffffffefbffeffeffffffffafffffffffffeebfefbfbffffefffffeffffffbfffefbeefaffffffffffbbffafbaffbfbeffeffbffafffffffffefefbeeffeffefbffeffaffbebfefbffffbbffbffffffffffbffbfffffbfffbfffffffbffffffafffffbfbffbeefffbfffffbfffeffeffeeffffeebefffffbefbffffbfefbffbfffefeffbffeffbeffffffbfffffffebfefffbefffffaeffebffbfefffbbefbfbfffeffeffeffffbfefbffefffebbffeffbffbfbeffffffebfffffffeffebefffffeffeffffbfffeffffbbefffffefefffffaffbfbfffeffafbffbbebfefffffffaffbeffebfffaffefffefffbfe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask190149 : MertensSieve.bits 190149 = 0xefffbfeffeffffeeffffafbfeffffafffffeefffbeffffffffbffbfffeffefbfbfeffffffbbffbffeeffffffffffafbaffbffefbeffefffebbfffffffffffefbfffffbbfffffbefbfbeffeffffffebffbfefbeffffffbbeffffeffeffafffffeebfffbffbfffefffbffffffbfffffeffeffffbbffffffefaffaffbffbebffffffbffaefffbeefeefffbfeffefffbbfffffffffebffbfefffbefffeffefbefffbbfffffeffbffefbfebffffffeffffffffbfbffbefffffbebfffefffefbffeffffbffffffaffffbffbffbfefeffbffbeffffaefffbffffffefffefffbbfffeffefaffffbbfffebffffeffffbefffbfeffffffffffbfbfffffffffefbfffffbbffbffafbfffffbffffffffffefefbeefaffbffffbffffefbfffffbefefffffbfbbefffffffbefbffeebbffffffffaffbefbffefbbffefbffffffffffefeffffbbeffffeffbfbaebffffeffefbffeffffbffffffffffffffbeffefffffffffebffbfffbffeefffbfeffefffbfffbffefbeffefffffffbeffaffeffbfbffffffeefbffbeffeffeffffffbeefffffffaeffffefbbeffffbffeffefbfffeebbffefbfffffffefeefffbffffffefffefbffbfbffffebafffffbffbfbeefffffffffbbfffeffffefbeefbffffbaffbffbefbffffffffeffffbfeffeffffffbfffbefffbfffffbbfbffffffbffbfffeffffffffefbfffefffffffbffefffffffffebbfffffbffffffffbeffffbffbfffefefffffbeffefefbbffaffefffffffbfefffbfefffbffffefbfbafffffffffffbfbeebfebffbeffffffebffbeeffffbfbefbfefffbbffffbfffffbfffbffefffffffbffbaeffffeefffbfefeffffffefbffefffffefbffbbefeffbffffffefbebefbfeffffeffbfffffeffffbffffefffbbfffffffffeffefaffffbfefbfbefffffffffeffffefffefbfbffbfffeefbffbffafbfeffeffffbfbeffffffebbeffffbefbffefffefbffbfbfefffbfefefbefffffffffeffffeffbffffffefaffeebfefffbaffbffeefbfbfefffffffaffffffffafffffffbfffffbfffbfbeeffffffbaffffbaffbffffffffbfbbfbffbeeffffffffebbffeffeffefffeffefeffbefbffffffffefbbefefffefbfbffffefefffefffffeffffbfbbffffffffefffffeebbfffffaffbfbfefffffebffffffeffbfbeeffefaffefffffffbefffffbffffbfffaffbffeebffbfebfefbfffefbebeebeffffffeffffffffffffffeffebfffffffffafffefffffffaffefbbffffffffefffeffeffffaefffbbffffbfeffffbffeffbfbefbefffffeffffbfffffffffffffefeefeffaffffbffffffbefefbffbbffefbbffefbbeffffffffefaffbffffffebfefeffbeffffefbfffbfbaefffffffbefefbfffbffffffffbffffffffffffffefbffbbfffebfeffffbfbfefeffeefffbffbfeffefbffffffffbfffffefffffbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask198341 : MertensSieve.bits 198341 = 0xfbfbfffeffefbeffbefffbffffffbebbfbfffbffeffffbbefffffffffbbfbfebeffbffaffeeffeffefbefbfbafffffefffffffbfffffffffaefeffffbbfbefbeffefffebfefffbbefaffefffffefffffffbbfffffffbfefffbeffffffffbffffbbffffffffeffffbfffffffffaefbfffefbfbffbbffefffffffbeeffefeffbffbffefbbefffbfeffefefbaeffffafbfffffffeffffbffbfbffbfefffffffbffefffefffbfebfefffbfffbffefbfefeeffffbfbefffeffefbffffbfebffbffffffffbbeffffffbfffbfbeeffffffbfffbffaffffffffeffffbeebfefffffffafffefffbffbffffffbffbfffffeffffbfeffebffbbffffbeffffffffeefafffffbeffffeffffbafbbffffffeffffefbbebefffffaffbfbfebfffffffffffbfffeffffffffffffffeffaffbfbeeffffffbeffffffffbfbffbfffffbbefbfbfeffefafffefbfffffeffaffefffffeeffefffbffffeffebfffefffebbefffffffffffeffffffffffefbaeffefffbfeffffffbffbfefbffeffffbffffffffffffffffebfeffffaffafffffefbaffffbfebfebfffaefafffefffbffffffefffefbefeebfffffbfefffffffefffffeffffffffffffffefbffbfffbefbffbffbefefbfffefffebfefffbfffeffaffffbfffeffffbeffffbffffeffffeebbffeeffefffffefffbffbefffffaffbefefffffbffeffbfffeffffeffbfffffeffeffbffffffefffffffefbfefbeffffeefffbbffbfffeffffaffeffffffffbffbffbfffefffbbffffffffffffebeffeffbffbffffbaffeffffbfeffffeeffffbeffefefbfefffbbfbbffeefeffffffffbffeebaffeffefbbeffebfefffbffbffffefeffffbfefbefefffffefbffbffbfefeeffffeffbffffffefbffaebfffefffffaffefffffeffaffefffffffbffffefefffffbffffbefffffffbbffefffffafbfeffffffbbffbffbfffebffbeffffffefffffeffefbffffbbfffebbffbfffffffffebfffefbbfbfeffebeffffbffffffffbfefeffbfbfffffffffbfbfefffbfeffffbffeffffbffffffeffefbbfbeefffffffffffffefffffffbfffbeffffbefffffffbeffffaffbfbefbfeffefbfffffeeffffefffeffffefbbfffffeffbfbefbffbefffffbffefffffffbfffffbffffefeefbefefbbfffffffbeffffffebfeffeffffeffeeffffefffffbffbebbfbfffbefffffebfebfefefffffeffbfbeeffeffffefffeffffaffffbfffbfbffffffffbffffebfebbfffffeefbfffeffefbfbbffffbefffefffbefffefefffffefffffbefffbffffffffbbffeffeffffffebfffffffffefbffffefffffffeffaeffefffffeffffefbbfbeffaefeffffffebfffffffffbfbfebeebbefbfffffffffefeffffffefffbfffeffefffefffbffbeefffbfefffbeeffffbfffeffffeeffffffbffbffbfefafffffaffbffeeffefbffeffffffebf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask206533 : MertensSieve.bits 206533 = 0xbfffffffbfffefbbefbffbfbfffffbbffeffffffebfffeffbffaffbfbfffaffefbefbffbeffffffffbfbfefeffbffbfffffffffeffefffbfffffbfffbeffffbebffffeffefffbfffbefeefffffffffbbfffefbffbfbfebfeffebbffeffeeffffeebbffeffbfffefffbefffffbffbffefbefffffbfbfffffffffbffeffbefefffffffffffffbfefeefffbfebffbfefffffffeefffbeffbfffffffbfefffbeffeffffffffffbfefbfbffffebfeffefeffbffbfffebeffffbfefbfffefbefefbfeffefefffffeffbebffbffffefbffbffbfffffbffefbbffffbffbeffefffffffffffbefefbefffefeebfffbfbeffbfffffeffbffeffffffffffffffffffeffffbefaffffbfffefbfffffffefbfbeffeeffffffffffffbefffffbffbefefbfefffbbfbffffffbffefffefffffffffffffeeffefffffffffbbffbfffebbffffbfffbeffffeffbfbeffffbfffefffffeffffbfefffffffeffffbfeffffefbfebbffffffffaffaefbfbfffffffffefbfeffefeefffffffbefffbbffbfffebfeffffaefffbbffffbffffefffbfebffbfffbffffffffbebefffffeffefffefefbfffffbffffffeeffffeffbefffbefffefbfbffbfffffbeffaffaefffbefbfefffffebffffefffffffeeffffefbaffaffbfffffffbfffffffffbeffffbffefbfebbefffffffeffeefffbffbbffafbffffffeffefffffbfbffbeefffffffffbffbfffbffbffbfffebfffffffffefffffefbbfffffbfbbefffbefffffefffefffbaffbffffffebffbfffffbaffffbfffbefffbeffbefeeffffefffebbffeeffefffbbfbbffeefeeffffffbfffefffefbffbfbfffffbbefbffbefffbfebfefffffffbfffffeefbffefffebeefeffeffffbbfffffbfffffaffbefffbfffeffbffbfbfffafffffefffebfebbffefbfefffbffffeffffefbffbfefeffbffffffefeffeffbffaefbffefbfefbffbffffffebbefefffefbefeffaffeffbefffbffbfffffbfffffffeffffbfbfffffbfefefffffeebffffffaffffffebbffffbfffaffeffffffffbefffffffbfbffbffffffbffffbfefefffffaffbffefbfeffffffbbfffeffffaffefffffefffffeffbebfebeeffffefbafffefefffffefffebbfbffbffffffeefffbfeffffbfbafffefefffffbfbeefbfffeffffffffffbebfefeffbffbfffffefbfefeffeffffffefaefffffebbffefbeffbfbffffffffffefefffffbffeffeffbffaffffffefbffffbffffebfefffffffbebfefeffbffeffbfffffeeffffefbffbbeffffaefaffefbfebfefbefffbfefffffefefffffefbbfffffaffafffffbefefbfffeffefffebffbffffffafbbfffefffffffbffbefeffffffffbeffeffffeefeffeeffffefffffffffebffbeffbefaffeffbfbffffffffffffbebefbbffffbbffffffeffffffffffffbfffffffffffbfebffbbffffbeeffffffffffbfbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask214725 : MertensSieve.bits 214725 = 0xefffffffbefffbefffebfffbfffffbebbfbeffffffffffbfffefbffffffbffffbffbbfffffbeffefffbffffffeeffffefbfffbffbefffffffefffffeffffbfffbffeffbffbeffebfefefbefbfffeeffffefffffbfffffffffffaefffffffaffaffeffbffeebfffffffefbfbfffaffefbffbbfbfebffffffeebfefffffffeffffbfffefffffeffffbbffefbfefffffeffffffbfefefbaefbffffffefbffaefffffffaffffbfffbefffbfffeffaffffffeffefeffefbfefefbfffffffebfebeffffffffffffffffbfefbfbffffeffffeffbffbefbfbfefaefffffebffbfffffffffffffefefbbefaffbffbfffffefffffffffffeffffffffbebffbffbaefeffaeffebfffefffffffbbffeefbffbffeffbfffffeffeffbffbefefbbfffffffffffefffffeffbefffbeffbefefffebfffffffffafffffbfffffeffbfbbfbfffeefeefbfffefbffffbeffbffbffffffffbfffffeffffffeffefefbffbbeffffbffffffffffffffbeffffffffebeeffffffbafbffbeffaefbffefbffffefeffbffffbbfbfefbffeffaffbffffbaefeffffbbefffbfffefbaffffffebfffeffbefbfbffbfefffffffbffeefbefffbffbfffffbbffbffeefffffebfffeffefbfefefffffffffebfefeffeeffffffbffffffbefffffffbfffeffffffbfefffbfffbefbfbffbffbeffeffbffafffefeebfffafbfffbeffffbffffffffbffefffefefbbefffbfeffefffbffffeffeffefffbafbffffffeeffffefbfeffebbffbffbfbffbffffffaffffbbefeefffffffbfffebefbfefffbafffeffefeffbfbefffffffffffffffffbfbffffffefffefbffefffffbffffbffffefbefbffefbbffffbaefefffffbfffffeffffbffffebfefffffffeefffffebeffffffffffbfeffffefbffffffeffeffbfffffbfbefbfeffffefbbefffbeffffbfffffbfffffffffaeffebfffffffffaffffbfeffffffbeffffbfefeffaffeffbfffebaffbffaefffbeebffffffffbfffeffeffefbbffbebffffffefbeffffffffeefbffffffeffeffefffffefbfffffaffbfffefbffffbffffffafbfebffffeffffbfbfeffeffffffbffbbebfffeefbfbffbffbfffbfffffbfffefeebefffffeffbffffffefafffebffffffbffefffeffefffffffbffffbfeffffeeffffbebfffffbfffeffaffffffeffffffbbfffffefffefbfffffffbefffefefffefbfbefbbffbffffbfefffffefffbfffffffffafffffbefffbffbeffeffbefffffffbefbfbfefbfffffeeffffffbbffefffefffbffffffeebefffffbeffffffffefffffffbffeffbfffffffbfefffbbefffbffbfebffbbfffffeffffbeefefffffbebffffeffefeffeffffbeffeffeffbfffffffffefbfbbfffefeffaffffbffffffffbfefffbffbfffffffffffffefbffffbfffffbbfffffefffffbfbfffbffeeffffbffefbbfffebbffbfbbfffefeef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask222917 : MertensSieve.bits 222917 = 0xbffffffbffbffeffeffbffafffebffffefeffbfffebeefffffffffbfffeffaffefffefbfbffbffffffbebbeffffbffeffbfffffeffbffffbfefbffffffffbffefffffffbaffbffbfffffffbefffffbfbbffeeffffbffffffffeebbffeffeeffebffbfffafbffbfefefffeffffbefbefeffbffefffffffffefbefffbeffbeffefeefffbbffbffffffefffbffffebfffaffeffaffffffffbefffffffffffebeeffffbefffbfffeefafbbebffbffbfefbfbbeffeffffffffffafbbffeffeffafbffffefeebfffeffbffbfbffbfffeffbfffffeffbffefbbeffffefffffbfbffffeffeffffffbfffbefeebfefffbeefffbfefeffbffeefffbefbbffffffeffeffffffffffeffbfffffbffefbffffebefffffefbfebfefffbaffeffbefbeffefffffffaeffffefffefbffeebfffefbffffffefffffffbfeffffafbfefefbeeffffbffffbfffaefafffffffbfefeefbfbfffbebfeffffffbfffffbeffeefbffffbbebfffefffffefbfffeffbffbfbafffeffffffffffbfbbffeffbeffffefffeffeffffffbfeffffeeffeffffffbbffffffffffffeffffeeffffefffffbffffffefefffffffffffbffeffbffbfbefffffbfbfebffffebfffafbeeffeffebefffffeebffbfffeefefffebbfbefffffbffbffbfbefbfefbfbffffffffffffffbbfffefffbfefbfffebffbffbfffaffeffbfbefbfffbfffebfffeefeffffffeffffffbfffbffffbfffffffffffbefffffefbafffffffbffffffbffffbaefffbfefbefefffeffeffffffffffefbffffefbefefbefbfeffefefffffffbfffeebfffbffffbfffffbbffffbfebfffefbfffeffefffebffbfeffffefffffefbfffffbfffbfffffeffbffefffebfefbffeffffffefeefbffffbbffbfffffbffffffffbffefbeffefbefffeffefaffbffbffffffeffffbffbffffbfefeffeffffffebfebfffafffeffefffffefefbffbfffffffefeffbebfeffffaffefffffffffebbffefbbefffbfffeeffffffbbffffffffffbfebfffeebaffffffffbfbfebfffffbefffefffbaeffffffffffffbaefefbfefffbfeffffeffaffbefffffefffbffffffefffefeffffbbfffefeffaffefbfeffefbfffffffbfffefffeffffffbffbfffbefeffefbffbfffbefeffffffffeeffefbfbffbffbfefbffffffffbffeffeffbfffefbeffefbffefbffffefffffffffbbfbfffffbfefefbbfbfffffbeffbffbeffeffefeeffffefbfffeeffffafffeffefffffffaffeffbefefbfffbffbffffffefbfffffbfffebfffbffffffffffffefaefafbfffffffffefffffaefbffffffffbffefffebffbffffffeeffefffffffeffeffffffebbffefffffbffeffeffefbffffebfefbffffbffffefffbefffffafbffbeffbffbfbeefffbefbaffeffafbbfffffffffffffbfffeeffffffbbffbfffffaffaffeffffbfebfffbffaffbffefbeffbffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask231109 : MertensSieve.bits 231109 = 0xeffbffeffbffbfbeebffffffefffffbfbbffffbfeffffbfffffffbeffefffeffffffbbeffffffbfffffbfffefbbfffebffffefffbaffffbeffeefeffffffeffefefffffbffbfffebbffefbffbfefefffefeffbffbffffffffbfffeffffffbfffaffbffffbfffeefbfbffbffbfffbeffffefffffeefafffffbfbfefefbfffbfffffbefffbfefefbfefbeffffeffbfbafbfefffffffefbbeffebfffffffffafbffbfefeeffffeebbfbffffffeffffbfeffffbeffffafbffffffefffffffbfefffbbffeffeeffffffbeffafbfeffffffffffbffbffbfffffeffbfbfffbffffffffefffffbffffbfffffffffffffefefffffbeffeffffbffbffbeffefffbbefbffefffffefffefffbfffffbeffaefbfbefffffffffffafffebbffeffbfffffbfbfffeffaffffffffbffffffefeffeebfebfebffffffffffffefbfffffbbebffffeffefefbfefbebfffefffffbeffefffbfffeffffffffeffbffefffffbfbffbbfffffafbfeffeffffefffffbfbffbeefffffffffbeefbfffffeefbfffffefffffffbffbfebfffffffffbffeffbffeffffbbffffbfefefbfefffffffeeffffeffffbffbfffbfffffbfbfffeffaffefbffffeffffffffebfffeebbfffffffbbfffffbfffffbffffbeffafffffffffefffbeffbffeffffbeffeefffbbeffffeefbffffffffbebfffffffffeffffffeffffeffeffffffebfffefffefffffffaffbffffbffbfffeefbffbfffffffffefbffbfbffffeffefbfbffffffeebbffeffaffbebffbfffbffeffbffefffffefbffbbffefffffafbbfbfeffeffffefbfefbefefffffffbfefffbefffffefffefffbfebfffbfffffbebfebfffbffbfffffefbaeffffffbfffffffffffbffffeffffaffbfbafffffefbeffbffbffffbffffefbfbeebbefffbeffeffbfbfeffffbffefbfffbfffffbffefffffbffeffbffeffffffebfffaefbffffffebfffeffbffeffffffffffffffeffffbffbbffffffeffffeebbffefbffffeffffeefeffbfbfffffffefafffffffffeffffeffefffffffffefffbaffbffffffffbffeefbeffebbfffffeefffbffbfffbffbfbfeffffeffffbfeffebfffafffffeefffffffbffafffffffffffeffffffffbfffffafffffeffffbffbeffbffefbfefefbfffffbbfbfefffffefffffebfefffffffaffbfffeffefbffffbfeffefffbfefbffffbbfffeffffffbfefffbffbffffffafbffbefffefaffffbfefffbbefffffeffffffbbffffffffffbfffffffffeffbfffebfffbfffefffffeffefefbffbfebefffffaffffffffefbbffffffffbefffbbffffbbfffefefffefbffbfffebffbaffeffbffffbffffffffffffffbfefefffffefffeffffbffbfffebbfbfeffffbfbbfbbffeeffffffbfeffebfffaffffbfebffbfefffffffbffbfbfebfffbfbeffffbeeffefaffffffeffffbfffffeffffffefffffffffbffffe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask239301 : MertensSieve.bits 239301 = 0xfffffffbffbffbeffeffefffebfeffefbffffbaffffffefefffffbffffbfefeffefbffffefeffbfffffffffeffffffffffbffbffeebffffffffbfffffbefffffbfbfffffbeefafbbefbfbfeffffffffffffbefffefafbfefbefeefffffffbfbfffeebfffefbffffeffffaefffffebbfbffffefeffeffffbffbbffaffefffffeefffffffbffffffffbffbffffbfeffefbffeffaffffffeffefbffffbbeffffbefefbfefbffefbfffbfffebfebffffefffffefffffefffffffefbffffefaefffbffffefffffffaffafffeffffbffaffffffefffffffefbffbffbefbeffffbbfbffffffaffbfffefffbfebeffffffebbfffffaffffffefbebeffefffffeebfffffffeffffafbbfffefbffffffffffbfffeeffffbfbffbfefeefbfffffffffeffffffbeebffffeffffafffffbffffbbffbfffffffbeefbfffffefffffffffefffbbffffffffeefeffeeffebfffaefffffeffffffbefffffbefbffeffeffbfbffbbfffebffffffaefffbfffbefefbfffbefefbfffefffffbffeffeffbfbefbffffefbffbfbbeffebffbfefbffbeffffeffaefbffffffefefbbfffffaffffbffffeffffaffbeffefeffeffffbbffffffffffbfeffeffefbffefffeffffefffffbffefbffffeffffbfbefbffbfeffffeffbffbeffeffffffffffffffebaffffffebfffffbbffbfbfefffffebbefffffefffbefbeefffffffbfbeefefffffeebfeffffaffbfffffbfffffbfffffffbfefffffffffbbffffbefbfffefbefffffffbeefeffefffebfefeffbffeeffffffffffbffffbffbfeffffbffffffffffbbffbfffffbffefbbffffffffffbefbfefeffbeffffffbfffafffefffffefeeffffbffbfbeefeefffbffbfffffffffbfffeffebfeffffbfbbffbffeebefffffbefffbefffefbffeffffffeffffefffffffbeffeefffbfffbfffffeefffffebfefffbfffeffbfffefeffbffeffafffffffffffefffeffebeffbffbffbfbfebffbbffffbeefbefffbfffffbefbbffeffaffbfffffffbffbfffbffffbbfbffbbffbfbbffffffffaefefffffbebfffbeffffeebffffeffffefbfeffeffefeffffffebffffffaffffbeefbefeffbffbffffbfebeeffffefffffbfffffbefeffffffefffbfefffffefffbfebeffaffeffbffefffefffffffbfbeffbffffffefffbeffaffeffbeffeffeffffbffeffffffefbffffbbefbfbffbefffffeffffbfffeffbfbfffbfbfebfffbffffbfffffffefefbffbffbeffffffffeeffeffffffffffbfbfffeebefffffbfffffffbbffbfbafffffffffffefbefffffeeffffbffbfbfffeefeffefffefffbfebafffffefbbfbffffefffbeffbffeeffffffffefffbefffefafbffbfffffbbffffbbfffffefffefbfffebffbfeffffbffffffefeffbffbffeffbfbffbfefffbbfbbeffeffffeffffffeffffeffafbeffffffebbfffffeffbffeefffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask247493 : MertensSieve.bits 247493 = 0xfbffbfbeefeeffffeefffffebfffbffffbffffffbefbfbbffbffeebfefffbfffffbefffffffbffbfeffeffffefffefffffffffffffbebbfbffffefeffeebfebefffffeffeefbefffbfefffbefbfffeefbffffbbffbffefbfefbfbbfffeffebfffbffbffbfbeeffefffffebbfffffbffbfbeeffffefbeffafffefffbffffffffbbffbffffbbffffffeffffffffeffffeffffbffffffaffffffefffbfefffffefbfffefbefefffffffffefffffffbfbfebffffefeffffffffeebfeffffbfffefffbefffffbffffffffbffbfffefbebffbeffffbbefbfffeffffaffeffffbfebefffffbfbbffefffffffbbfbfeffebfefefbffbfefefffefffbffffebfffeffbffaeffffeebeffffffefbffeffbefbfffffbefeffeffefffffbfbefbbefffffffbeffebeffefbffffefffbfffffffeffffffbbffefffffffffffffffffaeffffefffffefbffffeffffbffeffffffffeffbffffbbfbffffeffeffffbebffbefbeefefffffffffebbefffffffffbffbefffffefbbffeeffffbfffffbfffffefffffefbbfffefbfffffbfffefefffffeffffffeffffbefefbffbffbfefeffbfbfffffbfffeffffbbeffffeefbefffffeffffeffbffefffeffefeefbefbfbbffffffffefffffbfffffffffefeffeeffeffffbffafffffbebffffefffbeefbfbfffeefffbfebffffeffffaffffffefffffefffffffbefffffefffbfefffbfffaffaffffffffffbeffffbbefbfbeffeffbfbeefbfffffbefaffefffffefbffffffbefbfffffbfffffefbbfffffaefffffebfebfffaefbffafbffbfefbfffffeffffbffbeffbfbafbfffefffffffbfefffbfebbffafffffffbffffffeffffbbffeffeefefffefbfbefbfefffffebfebffbeffefbfefbefefffffffbfffffbffffffffbfffffffffbfffffffffebfefffffffffbfefeffbffefbfffffffffeffffbffffffffbefffffbffbfbefffffffffffffbffffffefffefbfffffbffeffffbfffefffefafbefbbffefbfffefffebbffffbbffffbffbffffffeffbfbaeffffefbfffbffeffffbfffbffeffeffbeffffbfffffefbffbffbfffffffffbffeefbffffbffffebeffeefffbaffffffffbffeffaefbebffffefffbeffbfffffeffeffefbfffffbffffffeeffffeeffefbffbffbefffffffffbfebbffffbbefeffbffffbffffeffffefffffffbeffbffffffffffffffefbfebbfbfebeffbffbffbefefffefefbbfffffeeffefffbbffbeffffbfffffefffebffbeffeffeefbfbfeffffffbeefffffeffffffbeeffefffbeffbfffffbeffeffffbffefbffffffbefeffbebfffffbfefffbffbffffffaffeffaffbeffffeeffffaffffbfeffefbfbefbfefeffefffffaebfffffffefffbbfffffeffeffeffbeffffefbfffefffebffbfffeffaffbffffbfeffefbffeebfffffffffafffeffffeebaffbffbfffffefbfffaffbfffeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask255685 : MertensSieve.bits 255685 = 0xfebbffefbfffbebfffbfffffffffebffffefefbffffffffffeffffefbbfffffeffaffefbfffefbefffffeeffebeffbffafffffffffffbefefbffbfebffbbffefffffffffffbffffbfefbffeebfeffffbffbffeefeffbfbffbbffffffffeffbfbfeffefbefbfbfffbfffffbffeffffffefffffefeffeffffffefeefffbefffffeffffffffbffbfffffaffffffffbebeffbffeffeeffefffffefafbfffbefffffefffbfffbffeffafffffbebfeffeffffeffbfffffefffffbffbfbbfffeffffaffefbfefeffbfffffffbfefefffefbffefffffefbfffffffebbfbefbeffafbfffffbfeffffafffffbffffbfffffbeebffbfffffffffefffffffbeffffffffbfffffbfffffbfbbffeffeeffffbfffefefbfefffffefffffffaefbffbfffefefbeefffbeffffffefbffeffffffffffbbffbffbebbffffbfffeffbfffffefbfefefbffffeffffeffbffffbfeffefbffffffffffffebfffffffffbfffffeffeffefbfebfffbffbffeebffbffbbffeffbfbfeffffeffffffefffbeffaefefffffffffebfffbfffeffefefbfffffbeeffffffffefbffffbbfffeffffefffffbefeeffffafbbffbffffffffefbfffbefeffefffffaebffbffbfffffbfffffbfeffefffffffffffefbfffffffbfffeebeffaffbfbfffffffeffffffbffffefeffffffffbfffffbefafbfebfffffbfffefbeeffffffbfffffffffbfffffeefefbfeffeffffaffbffffbfffeffbeffffefbfefffbfefffbbfbbebfffbffffbefffffffbfefbffeffbfbfffffffffbebffffefeffbffeffbebfffffffffbfffeffefffffffefbfffffffffeffbebfeffffbefefbafbffffffafffffbfffffffffffffffefffbfefeffbfbefbbfbfefffffffafffffffbfffbfffffbffffbfffefbfffbfbfffbffffbeeffefffbbefbffeefffbffffefbfbeebbfffffeffefbffbffbffbefffffbfbbfffeffffefbefffefefbbffefffeffffefffefaffaffffbfffbefffffeffefefffffbffefffffeffeefffbffbbfbeebeffffffffbefffffffbfbbfffffeebeffffffefbfffffeffffbfefffbfebaeffffefffffffffefbfbffffffffffffbffeebbfffebfffbffeffffbffbfffbffffbffffffefffffbffffbfffaefefffefffbffbbefffffffbebfffeffbfffebffbfffeffbffeefbefeffbffeffbfffebffffffeffefbfeffffeffffbfffbfbefffefefffeffffffffefffbffffefffbfeffffbfbffffffaffeffeeffffffffffbfffeffebffffffbffeffffffffafffffbffbfffffeffbfbbffffffefbffeffaffbeffffefffffeffffbeefbffaffffffeffffbffffffebffffefbffeffefffffefbefffffbffffffffffffffbfbffbfebeffefbfffbffeefeefffffefffbffffefefffebfebffffffeffeebfefffbfffffbaffbffffbfefeffbfbbebffffffffbffffffffbbefffbfeffffeeffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask263877 : MertensSieve.bits 263877 = 0xffbefffbfeffffafbffffeffebffffffbffbfbfffbeffffbffbefeefeffeffffbbffffbfffafffefffffefbffffbfeffffffffefbffaffffbfffbefffffebfffeefffffffefffebfefbffbfbffbffffeffffefffeffffffbbefbfffeffffffffffeffaeffefeffeffbffefbffffffeefefbfffffffebfffeffeffffbffbfefffbfffbefeffbffffffefbefefffefbfbfefffbfffffffffbfffefeffefffffafbffffffaffeffeffffbfefeffeffbffbfbefffffbffbfffefefbbefffbfebbfbffbfffefffefffffffaffbfbefffefffbffffffbfbffffffbefefbffbbfbffbfffaffffffebfefbefeffffbfffffbbefffbfebfefffffefffffebffbffffefaffffffefffbeffffffefbfbfffbfffffefbbfbffffffbffffffffffffffbfbbfffeffefeffffbbeffeffffbffffbffbfeffffbeffffeffffbeffeffffbbffbfbefffffffffeffeffffeffaffbeffffeebbeffffffbfefefbfeffffffffefffffefbffefbfebfefeffefbaffbfffffeffbffeffffffeffffefbefffebfefbfffffaefffbeefffffffeffbefeeffefffbffffeffffaffffbaebffffefaefbffaffbffeefeffffffefffffffeffffbefffffefbfffffffeffffffbfefaffaffbefefbffffffbffffbffffffffbffffffffffffffbffffffffffefbfbffbbffefffeffffffbbfbfeffffbfffeffffeffbfffffffbffffefbffefbffffffeffbfffffffffebfffeffefffefbebefbfefffbefffffeeffffbfbefbfeffffbffeffaffbebeffffffffafbbeffebbefefffebfefefbeffeffefbfeffffaefbffeeffebfeffffbffbebffbeffaffafffeffffeffefffffeffbebffffefbffbfffffeebfefffbbefbffffbfffffbbebfffffffefffffffffffeffeffffeffffbeffbefbffeefbffefbeffeffafbfffffbbfffffafffeffffeefffffffbfbfffffffffbfbfeffebaefbfbfffbefefffffffbbffbffffffffeffffffefffffffaffaffffffebffffffefbfeffffeffeffbebfffeffffffffeebfeffefefffffbfffefffffffffbeffffbefffefeffefbffbeefafffffbebbfffebbffefbfffbfffffeeffffffffefffffffbfbfebfefffbeffbffbefbffffbefffffeffbfbfeffefafbfffffffffffffffffffebefbffffffbfbbefffbaffffffebfffeffbffbffbfbfffffbbefffbbfffeffffffffffaeffffeffffffffeebfeffebeffbfffffbffefffffefbefbfeffefbefffffebffbfffffffffefffefffbbefbffefffebfeffffbffbffffbeefeffbfffffffbfebfffbfffebbfbfefbefefbbfbfffffffefffffffffbfffbefbffbfffebfffeeffffbefffffebfffffffffbfffffbffffbeffffffffbffbffffbffbeefbffbfbffffeffefbffefbfffffffffeffbfffffffbfebffffffaefbffeffeffbfbffbffbefffffafffefbfffffbfffffeebfefefbfffaffbfffef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask272069 : MertensSieve.bits 272069 = 0xfeefbffefbbffbfbffbbffffffffffbfefeffffbaffffffefefffffefbfffeefeffbffeffbfffefefffffbefffffffbffffbeffbfffffbefffffffffbffbeffbffffbffffebfffeffbffffbfefeeffffbefbffeffbefbffeebfeffffbffbffffffebffffffbfbffbfefefbfeffffffffffefffefeffefbfffffffffefffffffffffeffbfbfffbfbefffffffbefbbebfeffffffffeffffffbfffefbfffbeffffeffffffffbffffffefafbffbfebffbfffefbfffbfbeebeffffffffbffeffafffffefffeffebfffbffffbffbffbbefaffffbfeffffaefefbfffffffffaefaffbffffbffffefffffeffffefbfffffbfefbfffefeffffffffffbfefefffffeefbfbfebfffbffeffffffebbffffbbfbfffffbfffbfbffbfeffeffeffffbefffffffeffffffffffbfffbefafbfffffbffbfffefffeffffeebffffffefbbefffffffffbffbbfffffbefffbaffffffffaeffffaffbfffebfffbfffefffbeffbffffffffffffebeffbffffffffeffbfffffffbffffefeeffffbeffebffbfffbfbeefffffffbefefbeffffffffffffffaffbffeffbffbffffffefffbbfffffefffefeeffffeffaffbeffffbffefffffbfbefbaeffffffffebffbbfffffbfffefffbfffffffebfffffffefefbfffffbeebefffffeeffffffbfefffbbffbffffbeffefbbffffffffeffefffebffbffbbefffbbfffffefffeffffefbbfbfeffffeffffbbefefffffbffefffffefffffbfbbffffffebaeffffbfbbfbffbeffefbffffebfefaefbffefffeffffffffffeffbffefffffffbfefbfffffeffeffbfbffbffffefeffefbfeffffbfffffbebfebefffffefbffbfeffffbffaffffffebeebfffffbbffffbeeffffbffeffffbfffaffeffbffffffefbffbfffffbffffbeffffbfffbebefbfffaffffffffffbbfffffbefbfbffbfffffbfeffffeffeefbfbffbffffeffffeffffbbefefbbefaffefbfffffbbeffffffbffbfffbffaffeefffbffbeffffffffbfffeffffbfbbfffffffffffeffeffffffeffffbffeebfeffffbffffbfffffffffeefefffefffffffeffffbefbffbfffbefffbfeffebffbfefbfbfffbfbfffaefffbfeffeffefeffffffefffbffbfeffffbfbbfffffaffeffbeffebfffefffffefffffffbeffffbeffbffeffffffffbffbfbfeffeffffffffffeffaffeffeeffefffffffeffffbfffffbeefffbffffffefffefffffeffffffffffffffffbfbfeffffffbfebffffefaffafffeffffefffffffffefbefffffefeffffbbffefbfffffbfefbebffbbffeffffffebfefaffbffbfffffefbfefbfbfffbfbfffbfffffffffffeebffffffefbfebffffeffffafffffeffbfffffbfbffffffeffffbffffefffbbffeffaeffffffbffffffefffffeeffffffbefbbfbfffaffeffbebbefeeffeffffbffbfffebbefeffffbbfffffaffafbbfbffffffeffbffffffffeffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask280261 : MertensSieve.bits 280261 = 0xffffefbffeffbffefbffffebfefffffffeefbffeffbfffffeffbefffbfffefbbfbfebfffffffffeffffffeffffeffefffefeeffffffbfffbffffffefffffffffbeffeffffffffbffefbbefaffffffefeffeffefbffffffffbfffbffffffeffefeffafffffffffeffffbffeffffbffffefeffeffffffffaffbfffffffffeffeffffffffffefbbffffffffbefefbefffffefbfebfeffefbffaefffbffffffbffbefbfbfefeeffffeffbfbefbffffffaffbffffffffffbbffbefefffffffffffbffffffffffffefffbffffffbfffeffeffeffefbfbfebfffeffeffbfbeffbffefffffbfffefffbeeffffaffffffffefbafffffbefffbefbbefeffaeffffffbeffbffeeffeffebfffffffefffffffeffefffffffffefbffffffffffbffffffbfbfffffffeffffffbffffffeffaffefbfffffbfefeefffbafffffeeffeffffffffffffffffbffffffebffbbfffffffffefefbbefeffffbfeffebfefffffefbeffffaffafffebffbffffffeffaefffbeffeeffffefffffeefbefbfffeffeffffffffffeffffffffbfffffefffeffebafffffffbfffffbefffffbfbffbfffeffbffbfffebeffeffbffbfbffffeffffbfbfffbfffeffffeffefffffffbfeffffafffefffffeffffbebffbefbbffffbeffffbfebaefafbfffbeffefefffffafbfffeffbffffffebbffeffeffbffbffbeffebfffefbeffbffffbfffefbfefbffffbfefeffefffefffffffbfffefffffebeffffbeebbfffffeffbfffeffebeeffffaffefbfffeffbfffffafbfeffffbffffbfffffbfffeefeffeffffffeffffffffeffebffffefbffeefbfbefffffafbffffeffffefffffeffbfffefffffffafbffffebeffffbbebfffeffefffffbfbfeffebfffffbfffbffffffffbfbeffffffeffffffffffffffffbffeffeffbfffffffffffffbbffeffaffffbbffffbeffeefbffaefffbffffffbfffffbfffebeffbffeefffbfffffffffeebbfffefeffeffffbbffefbfffeffefffffeebffffffffffffefbbefbfbafbfeffffffffffeffffbfeffefbfbbfffffffffffffffefbeffffefffffbffbffeebfffafbeffffffeffffffffebbfbffbeffffffeffebfefefffffffffffffbfefffbfffbfffffaefaffffbffbeffffffffbfbfefeeffffbffbffbffefbaffffffefbffffbfefeffaeffffffbbefbfbeffbefffbfeffffaffffffffbffefbfebbefffbaffeffffffebfffbefaffbfbbfffefffffffffffffffffffafbbffffffffeffffbeefffbffbeeffffefbffbefffffafbfefbffffbfffafffffbfbefffffbffeffffffffeffefbfeffffeffbfffffeffffbffbbefeffbefbefeeffefffbbfbffbfffbeffffefbfffffffffaffbfbffffeffefbfbafffefeffffffffbffbffefbbefafbffffeffebeefffffefbfbffbfffffbffbfffffffffaffffffffefffffbffaffbeffffbeffffeffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask288453 : MertensSieve.bits 288453 = 0xffffbffffffffbbebfffaefbfffffffbfebbffeffaefffffffeeffffffffffffffefefbfefbfffffffffffbffbfbeeffffafbefffefeffeffffbfffffbffffefeffeffffbfffbffbfffffbefffbfefbfffeffffeffeffafbeffffffefafffffaebfefefbbefbffbfffffffbfefeffbfbfffffbfffffbbefffffffbffffffffffffffeffbffffbbffeffefffffeefffffffffffffbfffebeeffefbfffffbfffffbefffffefffbefffffbfbefbffbffbfeffffbfffebffbfffffffefffffefbffbffffffebefffffeffaeffffffbfefaffbfffffeebfffffbbfbfffefbfffeffbffffffefeffefbbefbefeffeefbffffbffffffbffffffefffbfebeffeffffffffffffffffbffbffffefbffeffbffffbffbefffffbfbffffffbefbfbffffffefbeeffffaebfffeeffefeffffbbefffbbffbffbfffebfebfefeffffbbfffffbffffffffbfbeffbffefbfeffebfefbfffffefffeffffffffffbefffffffafffffffbbfffffbffbfffefbfffeffffefbefffeffffeeffffbfbffbeffeefffbbfffffffffffffbffffffffbfffffbfefbfbeffeffbfffefffbfffffffffefbffbfeffffbfffffffffefaeffffffffefefbefffffaefffffebfffefbfffbfbefbeffbfffffffffffeffffffefffbeeffffffffeffeffefffffffbffbfffefeeffffbffbefefffeffffbeffffffbfefafbfefffbefbefffffffbbfffffefffffeeffeffefeffbffefffffeefbefaffbfffefffbfffffffeffefffbbffbfbfffffbfefeffffbfffbfffefeffbfbfffffffffafffffeffbefefffffffffebfebfeffeffffeffbefffffefffbbfbfffffffffffbffffebffbfefeffeeffffeeffeffffffbffbffffffbfbfffbeffffeffaffefffeffebffffffbfffffffffffefbbffbfbfffeffefbffbfefffffefffbaffffbfffffffffeebbfbfeffefbfffffffbefbfffbffeeffffffffefeffbfbfffeebfffffbffffffefbaffeffeffffffffaefffffefbfbefbfffbfbbffffffffbfffffeffffbfefefffffaffbeffffbffbfffffbefffffeffffffbbefffffefafbafffffffbaefbffeeffffffffeffffbebbfffeffefefffebfffffbaffeffbffffbeffbffeffbfbbffffbfeffffffffffffffffefbfefffbfefeffefbffffeffffeeffffbefbfffffbfffffeffbebefbaffbffbffbffefbfefbffefffffffffefeffffbffbefbaefffffffffffeffffbfbbfffefefbeefffffffffffeffefffbefffffffbbffeffeefffbfffbfffffffbffffeffefefbfefffbfffbeffffefffeffefeffefbfffffbfeffefbfbfeffffeefaffffffeffffeefeffaffffbfebfebfffafbbfffffffbbffeffbebfebfffeefaffbeffffffbfffafffefbffffffefffffebffbeffbefffbffffffefbfffbfffebfffffffefefbbfffefeebfffffffffffffffbefbffbfbffbfebffffffbeffefffbeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask296645 : MertensSieve.bits 296645 = 0xfbfffefbfffefeffbfbefbffbfefbffefffffbfffffbffbfbffbffffeffeffffffffebeffeefffbefbfeffefeeffffaffffbeeffefbfffebfffeffbefeffffbffffffafffffbffffbefffffffbefbfffefffffefbfebfffffbffffffbfbfeffebbffeffbeffefeeffefffbfffffbffffefbffeffbfffeffffbffbffffbffbfefffbffffefffbfffeffffbbffeffbffafbbffffffebbfffffaeffffefbeffbfffebbfbfefffffffeebfffeefbfffffffbfeffeffffeffafbbeffffeefffbfefbfbefbbffbffefffffffffefffffffbffffffefbfbbffffbffffefafffeffffeeffffeffbebbfbfefbefaffbfffefffbeffefbffbfffefffefbfbeebffffffeffbffbffbfbffbfffffbffbffffffeffffbfffbfffeffffeffeefbebefbbffbffffffffefbfffffbfffffbfffbffeffefbffbffffffffffffffffeffeffffaffbfbeffeffffffffbefefffffafffebbfffffbffffbffbfffffffffffffeffffffffffeffaebffbffffffefbfefbffefbeeffffeffbfffffaffbfffeffffeefffffffbebbffffffffbfbffffefeeffefefbfffbfbfffeffbfbafffffffffffbffffffefeebfffbfbbffbfffefbffefbffffeffffaffefffebffbfffbffffffffbffffbaeffffbfbffffffaeffffbeffefffbbffffffffffbefffefbffbffbffefffeffffeefbefefffffaffffffffeeffefeffefbffffffaffeffbffbfbfffeefefbbeffebffffffbfbfefbeffebfffbfbffffffeefaffeffefffffffffffbffaebfeffffbfffffbfbbffefffefffffffbffffbbffbfbafffebffffefffffffbfbeefeffffffebbfffffbffaffeffffbfeffffefffefffffffbffffbeffbffeffbefeffffbfefefffffefbffbfeffffeefffbffffffffbffffffefbffffefbffbfbffbfebfffaffbfffefffffffbefffbfffffffebffffffbffbefeffefffffaebfffffbffffffafffefeeffffbfbafffffeeffefbfffffbeffffefffffbfffffefffefbffbfbfffffbfefffffefbfbffbfffffbbefffffebfefbffbeffffffffffffbefffffffffeffffffffefefbefffffafffebffffeffffafffffeffbffefffebbebffbfffbffffbfefffbeffefbbffffbffffffffffefffffffbeffffffbfffffbfffaffbfffffeeffffefbbffbffffbbffffbffffefffbfefffbfebfefffbfffaffaefffffffffffffbefbfffffbffefbffbfefefffffaffffbbffefffffbffffbbffeefeffffffeffefefffffaffeefffbffffefffffffbfbffbfffbfbfffffbfffeffefbeefbeffefefffffffffffeffbffefbfffbeffebfeffffbfffeffffbefbffefbffbfffffffffeffffffeffffffbefbbffeffffffffffbffffefeffbfffeffffefffefffbbffbeffeffffffbbfffffffbaffaffffffeffefeffaffffffffffffffffbfebbfbfffeefffffebbffeefeffaffbeffffefbbffefbffbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask304837 : MertensSieve.bits 304837 = 0xffffefbffeffbfbbfffffaefafffffffbffbfffffbefffebfffffffffbffffbefffefffbeffbfffefafffffaefffffffbffffbafffeffefaffffbfebfffffbfefefffffffffeffffbfffffbffefbeefffbffbfffeefbffbfffebffffefaffefffebfefeeffefafbaffffffffefffffffffefffbeffefbfebfffffbbffafbfffbfffffeffffbefbffffffffffffefffeffebfffffffffbefffbbffbfffffffffebbefffffebfffffbaeffffbeffffffffffefbfffffffebeefbffaeffffffffffffffeffffefbffffffbffbffefffffbffbffbeffefbffffbbebffbfffffffffeffffffffbefefbeeffffefffefffbffbffbfffffffffffffefefbeffeffeffbfffeffffeffffbbfffffeffefbfffbefffffffafbbfffeffefeffbfffffbefeebeffbffeefffffffbffffbfffbffffffffbffefbbfbefbffffffffbbeffefeffffbbffbfbeffbfffffeffffbfffaefffffeffffefffffbfbfefffffffbefafbffffffffbeffefffffffffebfefbffffbbefffffffefbfffbebffffffeffefffffffffefafffffffbffffeffffeebffffffbffbffefffebfefffffffefbfffefbffffffefbbffffffefefbfffffbfffbefbffbfffebfffaffffbfeffebfefeeffffeefffffffbffbffffbbfbfffffffffeebfffeeffefaffbfbfeffffbffffffeffffefbfeffffefbfeffebfffbfbbffffbffffefbffbebbfbfefffffffffbffbeebbfffffbffbffffffefafffffbffeefeffffffeffefffffffffbfeffeffffeffffbffffebfffefffffeffbffeeffffbffeffbebfebeffafffffbffffbfefffbffbffffffbfffffbfffffefbbefafbfebffffffbffefffffffbeffffffffffffffeefeefeffeffbefeffefffffffbfefffbfefffbfffffffefffffffbffffbfffbffbfffebffbfffbffbfbeffffffffffffffbfffffefffffbfffebbfffeffffbffbebbfffeffffefbeffffffffbefefbffbffffffeffbffffbffffffbffeffafffefffbefffffaffffffffeffefbeefbebeffbfffffffffeffebfffafbfffbfffefeffffbfebffbffbfffffffebffbfeffffbffffffffeebefffffbefffbeffbefbffeefbfffebeffeffffffeffffbffeffbffbffffbaffeffffffefeffbffffffffffffebfefffbffffefeeffefbfbffbffbeffbeffffefbfebffbfffeffeffbfbfebfffaffffffefffffffffbbefbfbffffffefffebffffebfefeffbeffefffffffbfbfffffffefeffefbffbffbffffffbfffffbffefbfeffffffffffefbeefeffbfffeffffbffffbffbfebfefafffffafffffffffffffbfffffbeffeffbfbeeffeffffbffbfffeffefffffefefbafbffffefeffffbbebbefffffefefbfebffbfefffffffefffefffbfffffbefbffbfefffffffffffffffbbffbffbebfefefffffefffffbffeefaeffffffffebfffeffefbeeffffffbaefffbbffbfffebff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask313029 : MertensSieve.bits 313029 = 0xffffbbefbfffefbffffbfffffffeffffbffeeffffefbfefbffeffbffffffffffffeffebffbbffbffbfffffffbeffbfbbeffefffffffbfffffbfbfffeffffffefffbefbfffeffaffbffffbfffaffffbffffffafffffbeffefefffffffbefbffffeffffbffefffeffebfefffffffffbfeffefffbfebfffeebffffffaffffbeefffffffbfffffeefafffffbefbeffffaffffbeeffebffbfffafffeffefefbffffffefbbfbfffeefffbfffffffeffffaffafbfffffffffffbeffbffeebffffffbfbbebeffffffffbfffffffbeffaffeffbffffbefffffbfbffbfefbefefffeffebefbfffbffbfbbffffffefbfbbffbefefffffeffbffffbffffefffbffbfeffffbffeffbffbffeebfeffffeefffffefeefeffefbbfffffefffffbffffffefffffffafbbfffefaffffbffffefeffbefafffeffefffffffafbefffffeffeffbfbafbfffeffeffeffffffeffefeffeffaffffffffbffffbffffffefbfefffbffbffbffbbfffffeffffffebfefffbbeffebfebeffbffbffbffeeffffafbffbfebeffefffffeffbffffbbfffffefffffffffffffbfffbefffbbffafbaffffffffaffffbfffbffffffeffffbfbbffffffefefbeebffffffaffaffefbfefefffffbfbffbffffffeefeffbebbfffffbeffffbffffffffbffafbfffffbefffefbffbfbffbffffffbfbfebfffefbaffffffffffbfebbefffffffbfffeffefeffbfbffbffffffffbfffffffebfefbfbfffbfffefeffbfbffbffffffeefbffeffffbffbbffbffbfffebefbffffffafffefeffbefeffbeffffffffefffbafbfeffffaffeffeeffefffffffffbefbbffffffffbfffffbebefffffafffefffbfefbffffbffbfffeffbffffbbfffeffffeefbffffbffbfffaffffbbeffefeeffefffffefffbefffffeffeffbffefbfffbffeebffffffbfffffeffbeffeffefffffffbfbeffafffffefbffffeffffbfbfffffbffffffbfbbffffffffaefbffefbffffffbffbffeefffbeeffffeffbfbbfffebeefffffeffefffbeffaffefffeffebfffeffeeffeffeffffffffefffffffeffeffefbbfffffbfffffbeffebffffffffffffbfffefbefffbfffbfbffbfefffffebffffefbfffffeeffffefbfefffbfffffbffffffbfffffbffefbffffffafbfefffbfffffbbfbbffeffffffffffbfefffbbffffbafbfeffeffffefbfffbffefffefbfffffbffeffeffffbfffbebfffffffffafbffbfefffffffbfffffffbaefffbbefbfbefffffefffeffebffffefeffeefbffffffefffbbffffffffeffffbeebbebfefeffefffebfeffeffefefbbfffffeeffffefffffffffffbefffbffffebffbeefbffbffffbfefefffffaffffbeffbefefbffbbefeefbfffffeffbffffffefbffffffffffffffeffbffbefefffffbfbfebfefffbeefefffefbfffefefffffbfbbffffffffffbfebbffeebfffefffffbeffffffffffefb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask321221 : MertensSieve.bits 321221 = 0xffefefbfffffffffbffeffeefeffaeffeffebfefffbfefffffebeffbffeffbfffffbffffbffbfeffefafffffbeffffffbfffeffffffeffffefffffffbfebfffeefbfbfffffffebfefefffefffffebeefffffefffffffeffefffffbffffbfffbffaeffebffffffaffbffffffffbfffffbebffffffeffffffffffbfefeffbffefffebefffefffbfebbfffffbffbfbefbffffefbffffffeffffffffefbfffffffffebeffefbfeffffffbaffbfbefffffffbfffffbbffbffeffeffffbeffffffefeffafffebffbfebbffeffaffffbffffeffffafffefffbfffefffefbefffbfffeffbffffbfffaffbffaefffffeffefbffbebffbeefbffffbfeffebfebefffffffffffffbbefbffafbbfffeffefffbffbbffffffffafbfefffbfffbffffffefbfffffffffffbfbffbffffffffbefbbebeffbfffffffbbebfffbffffbffffefeebbfffffffbffffffffffffbefffffffeefffffffbefefbeffffbafffffefffefaffeeffefffbaffeffaffffffffbeffffbffbfffefeeffffffffffffffffefffebffffffbffeffffffffffffefbfffffffbfffbffeffffbffbeebafffffbeffebffbbffffbeffffffffbfffffbefbffffffefbfbbfffeffffeffafbefffeffeffffffffefbfffffaefefffebbfffefbffeffeebfefefbfffffbffbbffffbfeffffffbffffffaeffffeeffffffbfefffbbefbfbfffeffbfffffffbffffffefbfefffbfebefffffffbffffeffffaffafffeffebeffffbfeffffefffffffffeffebfffbffbfbfffbebfefeefbfbafffffeefeffbffffffefeeffffafffffbfbffffffaffbfbfefeffbefffbfeffffffbfefefffeffefffbeeffffafffffeebffffffeffffffefbefffbefbfffeeffffaffafbbfbfffbefbffffffeffffeffeffbfffebeffffffffffbffbfffbefaffbffffbfffeffbfbffbffbeffeefefffefbffefffffbffffbfffffbffffffefbfffefbbffffbbffffbfffffffffeffffbfffaefefffffbfbfffffffffefbbfbfffffffffffbbeffffbfffffafbfebffbfffeffeffffffebfffffffebbfffffafffffbefffffffaefaffbfffebeffffffffffffffefffffafbfeffffffbeffffffffffffeffefbfbffffefefbbefffffeffffffbfffefbaffffffefbffbffbfffebfffeffbffefbffbfeffffffffffbfffffaffaffeffbffffbfffefffffffffeffffefffebbffefbfffafbfebffbfeffefffbbeffefffffffffbbfffffeeffefefbefffffffffffaffbffbfbfffffffffffbfeffebbefefffeffffefffffafffffffbffffffaffeefffbefbfefbffafffffeefeffbfbffffeffebffffffffbfeffefffffffffbbffeefaeffffbffffbffffefbfbfeffeffebffffffbfffefffbfffbffafbfffefffefafffefbffffffffefffffffffebfffefbfffbffeffbefffbffbbfbfffeffafbbebfeffeffffffffffbfbffbe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask329413 : MertensSieve.bits 329413 = 0xfffffbfffffffffaefeffefbffffebffffffeeffffffbfffbffeffffffebeffefbbffbffeffeffbfbafffefffffffffbaeffeffeffffffffefffffffefffffefbfeffeffffeffbfbfefefffefefbefffefffffffeffffbfebffbfffbfbeffffffebbffffbbeffffeebeefffffffbfffffbffefbffbbffeefbffbfffefffbefbfefbfbffbfffeebeffffbbfbffffffbfffffeffffbfffbefffffeffefeffffffffeffbffffffffffbfebbfbffbaffbffbfffeffffbefbfbffffefeefafffffbffffbfffeffafffffffbfffffffffeeffefffffeffffeefffbffffefffbfeffefeebffffffffbfffffbbffeffbfffffeefeffefbfeffefefffffeffffbffbffbfeffffbffbfbffbffffffeefffbeeffffeffefbffffffaffffffffbeffffbfffffbfffefeffeffeffffffefefbfffffffebfeffeffffbfbeefbfffefeeffffefbbffeefeffefffebbffeffbfffffffbfffffffefaffefffeffffbfffffffffffefbbefbffbebfffffbeeffffbeffefffbeffbfbeffffbfffbfffffffffeffebeffffffebbffefbfffffffffbfffebaffffbfefbfbfffbffefffebffbffffefeffffffefffbfffbfffffffbfefbefbffefffffefbffffffbefffffeffefefbffbfefffffefefffefffbfffeffefbffbfffffffffbffeffffffffeffffbfebbfbfeffeffffefffebeffeffbffbefbffffbfffbfbfffffffefeffffbfffffbefffefffbeebffbffffefaffbefbfbffffefffbfffbfffefeefbfbfffffbffbbffafffeffffefbfffeffeffbfffffefffffbfbfffffbaeffffffbffffefeffafbbfffffeebffffffffbbffeffeffffbfffbefefffffbffeffffffffbffbffbffbfffefbffeffffbffbffbffffffffffeffffbefbffffffffeebefffffffffffeeffffeffeebbefffbefffffefbffbeffffffffffffffffffefefbfffbffeffbffbffffffebffbaffbfbbfffebffbffffffeefffbfffeffefffefffbffffffaffafffffefbfefffbefffeffebfefefbffbffffffafffffbfffeffffeefefffefffbffffffbffeebffffffbffbffffffffeefbffeffafffffeebbefffbbfbfeffefffffffffbbfffffbfffffbfbffffebfffeffaefffbffbeffffbeffffbfefeffbffeefbfffffbffbffbefbefffbffffffbfffeffffbffffbffbbffefffefffbfffffffffbfffffeffbfbffbfeffffaefffbfffaffffffebbffffbfffeffffbfebfffbefefbbfffefeffaffffbffbbffffbfffefbefffffffffffefffffffffefffffffbebbffeeffffefbfffffbffbfffafffebffffebfffbfffffbefeebfefffbbfffffffbfffeffbebffffffbefffffffbefefbeeffffaffffbefffefeffefbbeffffffffffbfbfffefbbffffffffffffffaffeffbeffefffffffefbefbfffffbbefbfbeffffbfebfefffbefbbffffffefbfffefffbfffbffefffebfffffffffbffbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask337605 : MertensSieve.bits 337605 = 0xfbfffeeffefeffbebbffffbeffeffbefffbffbbefffffffbebfffeefbffffbbffefffefbfffffbfbeffaffbffffbfffeffffffffbfffffffffffeffffbbffffffffbfbbffffffebeffffffeffefffffffffbbefffffeffffefffffbffffbefffffafbfefffbfffefbafffeffffeefefffefbffeffbefffbffffebffbeefbfffffffbeefffffffbfffffeffaffbfffefffbfefeffbffbffbffffbfffffbffffffffffefffbbfffffefffffefbefffffffffffbfbfefbffffbeffffffebfffeefbefafbefbfefeebfffeffeebbefeffffffffefbffffffbffffffefffbfffeeffffeffffffffbffbfbbeffffeffeefbffffffffffffffafbeeffebffbfffaffffffffffbfffefffffbffffbeffeffbfbbfffffeffafbbfffebffbbffaffeffffffefefffffffffffeffbffbfffebfebeffffffffeefbffeebbffefffffbefeffbeffffbffffbefffefefbfeffefffbfffffffffbefeffeffbffeffffbffffffeffffbffffeffffefffffffbfeffffafbfffbefeffeffffbbfbffffffeefffffeffffffffefbffbefffbefbfffffffffbfbefffffefffefbffffbefffffefffeffebfffaffffffefefffffeffbebffbffbaeffffbffffbfffafffffefffebefffffbfbefbbfbffffffffbffbfffffbefffffeebfebfebfeffffffffffeffbffffbbebbffffbfffbfffffffbfffbffbffbffbefeffffffffeebffffefbffeffffffefffbefffffbffbeffefbefffbeffbfffeffefffbffffefffbeffbffefffebffbbffffbfffffffffffffffeffbfbeffaffbfbfefbefeeffffffffefbfbfffbffbffbfbffffffeffffbffffffffbbffffbafffefffbfeffffbffffbffffeffffaebbfbeefbefeffeffffbfefffffffbfbfefeebfeffffeffffffffbffefffefbfffffeefefbfefffbfffeffbfbaefffbfffefffffbffffffffeefffffebbfffeffffeffeefbeffefffffffafffefffffefffbfffbefffffeffffffbfeffffbffefffffffffebeefbfbfffffbeffaefeffefbbffffbfffbfffffffbfffbffffffffbffffbfffffbffffebffbeefbffbffffffefeffafffffbffffbffffffbebffbeeffefbffeeffeffefbfffffeffffbffbfeffffffbfffffbfffffffeffffefffffefffefffffffeffbfbfffbfffeffffffbeffbfbfffbffbfffffbffeffeffbffaffbefffbbffbffffbbfffeffffffbfffffbeffffffffbfffffffbfffefffeffffffbfefbffbffffffffbffbffeeffefefbfffbffeffbffffbbffeffbfffffffffffeffffffebefbbffffbffbfffffffeffffeeffeffeffffbfbfebbfffefbffefffffbebfffaffeffeefbfbfebbffbffefbfffefbbefffbffbbebeffeeffffbffffffffffffffffffffefbfeffffbfffffeeffefefffffffbffbaffbfffebbebefffeffffefffffeffefffffbfbfeffffefffffefbfeffefeffbffbefbfffeb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask345797 : MertensSieve.bits 345797 = 0xffffffbfffffbfefeefbffefbffbfebfffffffefffbefbfefffbeffbffffbfeffffffbffbffbeeffffeeffeffebeffbfbffffffffbfeffffffbbfffffeffefffebffbeffbffeffffbfeffefffffffbfffefeefeefffffefffffffbfffffeffffffffafffffbeffeffebfefffbeffffbfffeffeffeefbfffffeffbffffbfffefffffaffbfbffffebfffffbfffbffeffeefbffaeffffffffffbffeeffebffffffbffffbffffffefffffeefffbffbeffeffbffffffefbffffbffbfffeefaffffbbfffeffffaffafbbfffeffebeefefffefbfffefeffffffebbfffeffefeffefffefeffefffffffffffeffbffaffefffefeeffefefbffffefffbfffbffffbffbffffffaffbeffffffbfffffbbfbbfffeffffbfbeffffbeffbffafffebbffffbfffbfffffbefeffbffffffffffbffbfffffbffbffffeffefffbeffffbfeffeffffeffbffeffeefbfbffffebffbafffffffbfefeebfffeffaffffffefbefffffffffbffffefbfffeffefffffeffffafffebefbeefbfbffbffffefaffbfbfffbeffffffffffbfbbeffeffffbfbfffffffefbffefbffbbffffbeefaffbfbffbffffefffbeffffffefeefffffefbfffffaffeffffffeffffbffffffffffbefbbefafbffbffffffeeffffffbbffffffffffffeffefffffefeffeffffbefffffbffbffffbffffeffffffbbffeebfffffffffffbeeffffffbffffefffbbffeffbebbfbefbbfffffffbffffefeefaffbeffefefbffffffbefffffeffefeffefffffffbbfffffeffffffffbffeffbffbffefffffeffbffbfbeffbefbfffffffffffbffafbaffbebeeffefffbefbfffeffbffbfffffffffffefffffffbbfbffbbefbffffffffeffeffeffbeffebffffffbfbbfffffffbfffafffffffffeffefffbafbffffefbfffffffbffbefbfffbfffffffbfefbeffffbfbffffefffffffffbfeffffbefeffefffffffbbffbfbbefbffffbfffffffffbfffffaefbfbeebfebffbeffefffffbffefffffffbfffbffffbfffeffbefbebfffeefeffffbfeffffbffeffffffffffffefffbefffffeffbffbffefbfefeebaffeffafbfffeefffffffbfbbffefffffeffffffefeffefffffbebffbffbfffaffeffbffffffffbffffbffffefeffeffffbbfbfffafffffbefffbeeffffefffffffffffbeffffffbfeffffffffffbfffeffeffeffffaffbffffffefbffbefbfffefeefffbeefbeffffaffafffffffbffffffafbafbfefefffffffbfffffffffaffffbbefffffffbffbffeefbfffeffffbffffffffefffffffbffbffbfffeffbffbffffffebfefaffbffbffffbeffeffffffebefbbffeffffffefffffffefffefbebeefeeffffaebfffeefeffeffefbfeffefbfffffefffebffffffffbeffbefffbfffefffffbebefffefbffefbffbffffffbfbbfffffefffeffffbfffffefffefffbfffbfffebeffefffefffffffbefbfbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask353989 : MertensSieve.bits 353989 = 0xefffefffbbefffffffbfbeffeffeffbebfffffbfffffbfefffbefbeffffbfffbfbfefafffffeebffffffbffffffffbfbeebfffefbfffbffffbbffffffffbfbfffbffafbeffffffffffffffefffeffefeffbfbffbbfbfffeffefbffbbefeffeffaffffffffeffbefaffeffbefeffffffffbfbffffffeefffbaebffffffbfffffbfffffffffffbfffebffffeffffffffeffffeffaffeffaefffbeebfffffffffbefffffffefbfebfffffbaefffbffffebfeffffefffffffffffffffffffffffeeffeffffffbfffeefffffffffbfefffffffaffeffffffffeeffffbfffefffbfffbffffffffffffefffbeffbffeebfefbffefffffeefbfffffeefbeffebbfffffffffffffffffaffffbfffeeffefffbfffbffffbeffffffffffffeffffbffeffffffeffffbffefffffffffffffbfffbefefbfffbffbeffefffffffffbefffefeffefffffbffbeffffaffeffbffffffefeffffbaffffffefefffffaffbfffeffeffffeeffffffbbffbffafbffbffbbffffbffbffffebffffffffbbffefbbefeffffbfefffffffefbffffefffbfefffbbefbfbefffffbffffbffffebafffffaffbebffbfffeffffbfffeffbffefffefbffefbbffbfbefbfeffebffffffefffffefbeefbfffebffffffeffbfffffffbffbbffbffbffbeffebfeffffffffffefffffeffffbbffeffeefaffaefffffffbffefbbeffeffffefffffaeffffffffffefbfffffbeeffffbffffbfffffffefefbeffbffffffffffffefffffffbfffffbffffbfefbefefffefbebffbffffffaefbfffffbffefbefbbebeefffffffbebfffefbbffafbbfbfffffffefefbffffffeffffffffefbfefffffffeffeffffbeebffffffbfffffeffaffbfbffffebfeffffbffaffffbfefffffffbfbffffebbffffbbeffffffbfffbfffffffbfefeefeffbffbffeebfffffffefbfffefffffffffbfebfffbfffffffffeffeffefbffffffefefffffffbfffbfffffefffffffbffbffbaffefffefffffefefffffbffbffeefaffffffffffbffbffffffffbfffefbfffbffbffbfffffaffffbfffffbffffefffffebffffffaefefbfeffefefffefffffffffbfffbffffffffffffebfffbffaeffffeeffffbfffffbffefbefffffbfbffbfffbefffbfefffffffaeffffeffffbfeffffbfbfefffffeffffbfffebffbfefeffeffaefbebfffbffffbefffefffbfefffffffffbfffaffffbbfbfefffbfeffffffffeffffffffffffbfffefffffbfffffffbffbfffaffbefbffeffbefeffafbbfffebfefffbbebfefeffffffffffbffffffaefefffffbfbeefffffffbfbffbfffbffbfbeffbfffffaffeffeffbefffbbfffffbfffffffbeffffffebffbefffffffffffffbfefaffbfbbfffeffffeffbfbeebfffefffefefbeefbefffffffbffaebbffffffffeffffffeffefbffefbbfffefffffefbfffeffffffbaefbfbeffbefff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask362181 : MertensSieve.bits 362181 = 0xfffffffffffffffffffffffffffefffbefffffeefbfbefffffeffbffbffeffeffffbffbfefffbeefffffeffeffefbefbfbbfffebffbffffffeeffffefffeffffffbfefeebeffffffebfffffffffbffbfbffffefbffffffeffebffbfefffffffffffffefffffeefffbfffffffffffbbfffeffffffffffffbfebffffffffffefefffffbffbfffefeffbffefbfefbffffffffbffefbfeffeffffffbeefffbffffeffffafbbffffffffefbfefbfffffffffffeffbfbffffffbffbfffefefffefffffefffffffaffafbfefffffffbefeffeffffffeffffffffebbffefffffeffeefffbffffffbffbfbfefefbfffbffffbfffefbbfffffffbffbffffffefbbfffffffbbffffffefbfbefffffffbfebbffffffefeffffbfffeefeffeffefbbfbfefbeffffbffbfffefefffffffffffffffefefffffffffeffffefbbffbffeefeffbfbbffffffefeefbffffbffbeffeffbffbffbffeffbffaffefffefeffbefffffeffebffbeffbffbfffefffffffeffeeffffffbffffffefbffffeffeffffffffefeebffffffeeffebfffbffaffbffbeffefeffffbfffffbffbafffffeffffffeffffefffefbebffbeefffbfefbffeffeffffbeffbeffefeffeffbebfeffeffffbffffbbffffffffffffefbefeffaefffbefffffffffffbfffffbfbefffffffffffbfffffeefbffeffffbffbafffffaefffbfeffefffbffffffffbaffefffefbffefbfefeffbffffbffbeefbffbeffefeebefffffbefbfffffbeffffefffffefffffaffbeffeffffbffeffffffefeeffffffbffffffffffffbffaffffffeffefbffbefffbfebfffffffffffbfefbffeffffffebffbfffbffffbbfffebfeffffefbbffeebfffeffbebbeffffeffffbbebfffffffefeffefffffefbfffffbeebfffffffefaffffbfffeffefffffbefffbffbfefeffbffbfffeffffefbfffffbfffeefffbeefffbfffeffffbefffebfeffffbfbbeffffefffffeffffffeffffffffffbebbfbffffeffffbfbbfffeffefffbfffbefffbeffffbffbffffffaefffbfefffbffffffbffbfbbffeffbefbfffefffbefffffeffeeffefeffbffaffffbbfffffeffffbfeffffefbbffbffffffeffebfffffbfffffbeefffffffffbbffffffffeffeffbfbfebefffffefbfeffebfffbffffffefeeffffeffbfffffefbeefbffffbffbffffffbfbeffffbfffffffffbfbffffefeefefbefbfefeefbfffffefbfeffffbfffffafbffffffaeffffbebbebfffbffeffeeffffffffefaffefffffffffefbffbffffbeffeefafffffffbffffffffffffbebffbbeffffafffffffbbefefffebfefffbfffbfbefffffffbbffbfffffffffffeffffffffffbeefaffffbeffbffeffffffffefffffeefffffffbfffeffefefffffffffefffffffffffefffbfefbffaffbffbffeffeefbfbeefbfbefffffefbfebfeffffffffffeeffefeffbffbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask370373 : MertensSieve.bits 370373 = 0xfbfbfffeffbffefbfeffffffbbffeffbfffffffbefffffbfffefeffffffffeffffffefbefefffeffebfefbffffffefffbffbbffaffeffbfffffeffefbffbffffffeffffbbfbffbfffeffffbffffffffffffbfffffbffefffffbfbffbbfffefeffeffbfbfeffeffeffffefbfffffbeffffffeffffeffbeffffbeffeffffaefffbeffbefefffffbffefbffbfffffffffffffffefbfffafffefbfbfebffffffefbbfffffbeffffffbffbffffefffbfebfffffbfefefbfffffbffffffbffbfbffffffeffbfffffffffefbffefffebbefffffefaffffffffefbeefffbbfbbefefbfffeffaffffffefeffeffbffbfbffffeffffbebbfffefbffefbeeffffffbfffaffffbfeffffbefafbffffffffffeffffbeffffefffffbffffffffffbfefbfbfffffffffeefbfffffffbfffbffbfffefbffefbffffffafffeffffbffeffbfffeffefaefffbbfbbffffffffbfbffffebfffffffffefffefeffffffffbffbfbeffeefffbfffffffebbffffffefbffffbbffbfbfffbffefffffefbbeffffefbbffaffffffefffbfefafbffffffefbfffbfffebbfbfffefffffffbffffffafffffaebbffefbbffefbfffffffefbefefffffbebeffaefbfbfffffbfefbffeffafffffeebeefffffefffbfeffffefbfefbfbffffffeffaffffbffbfefefbffbfefeffeffeffbeffefffbaefefffeffebffffffffbfffbffffffeffffefbffffffeffffbffffefffbaffffffffffbfefffffffbfbbffeffeeffffbebbfffffffffffbffffbfffbffeffeefffbfeffefffbefbfffeefbffefbfffbebfeffffeffbffbeffefbffbfbeffffffefbfffffffffebffffefffbfffffffffbeffffeefffffffeefffffefffffefeefeffffbfefefffffffffffbefeffffffffefffeffebfffffbbefbffffffffffffefffbfffaefefbbffbfffffeefbfffeffffffffffafffebbfbefbaffbffefbfffffbffffffffbfffeffbffefffffffbffbbfffffbebffffffafffffefffeffffeefbffbffbfbeeffefefbefffffeefbffbffbefffbfebfffeffeffbefefffefefffebbffffffffffffffffbfffbffbffefffefeffeffbfbffffffeefeeffffefbbffefffffffffebffbeeffefafbffffeffffbffffffffffbefbfffeffefbfefffbfffffffffbebfeffefffbfefffbfffeffbffefbfebfebffffffefffffeeffefbfbefbfffffffeffffbfffffffffeffffbffffbffffffefbfffffbefbfefffffffbffeffeffeffffffffeeffffbffbfbfffefbffffffeffffffebbfffffbeffebeffeffbfbbfbfefffffefaffeefbffefffffbffafffffeffaffbfffffffbffbbffaffeffffffebffffffffffffffffffefffffffbffffefbfbbebfffffffefffffeffefeffffffffbffffffffbffffffefbfbeffafffffffbffbeefbeffffffbfefffbfefeffffbfffeffbefbfbffbfebffbaffbffbffbffe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask378565 : MertensSieve.bits 378565 = 0xffbfffbfbbeffffeeffeffffffbbeffefeffafffffbfffeffffefbefffeffffeffeffffbfffffffefafffebfeffffaffafbfffffbeeffffffbaffffbfffbffeffeefbfbffffffffffeffebeefbffaffafffffeffbfffffffbbebffffeffffefbfffffbfffffbbffbffffbeeffffeffffbfffbefbffefbfffeffbffbffffffebffffffefffffffffffaeffffbfbfefffbfefaffbebffbffffefbffbfffefeffeffbffffffffefffefffbeebffbffffffbffffbbefffffffaffbffbeffeffffffbfffffbefffffbffbeffebfebfffefffffbebfeffeffffbffbffeffeffffffeffeffffefffffbefbfffefffffffffbbefffbeefffffffffbefffefbffeefffbfffeefbfffefffffffeffffbbfbffbfefeefffffffbffefffffeffeffbebeefffffffefffffffbbffffbfffbfbfffbffbffefffebfebfeffffaefbffffbfffffbfefbffefffefbfbfeffffefbfffeffbffbeffeffffeffefffefffbbffefbffbfeffffbefeffffbffffefffffffaeffefefbfefbffeffbfbefffffefbffffffeffafffffafbfffefbbffafffffbffefffefefffefbebffffffefbfffffbffffffeffaffffbefffffbfffffbfffffeffffbefbfefffbefffffffffebfffffffffbfbfffefbbffffffefbebfffaefeffffbfeffefbffbffbffffbfffefffffbefffbffffffffbfebbefffbbffffffefbefffffefefbffbbfffebfffefbfefffffffaffefbffbfeffffeffefbbffbffeefefffffbfbbffefffffffbeffffffebffffffffbfffeffbefbffffbffffffbfffffffbbffeffeffafffffffffeffffbfbffffffffffefffbfffbffeefefffffefffeffffaffaffeffffffefbeffffefbffffffffffffbeffefffffefffffebffffffeefeffafffffefbfefffffefffbffffefafffffbffffffffeffbfffefeebbffefffffbefffbeffffbbffffbeffeffefbeebfffffbbffffbbfffeffebfffffffefffbeffaffeffffffeffebfffffffffffffffbeffffefbfefffbfeffffbfbfeffffbefbffefbffffeffefeffffffebfebfffffbaffffbfffbeffffefffffefffffefffefbfffffffffffefbfeffefafffffffbffffffbefffffefffffffbffffbffffebefbeffffbeffffffffbefffbffffffeebfffaffbfbbfffebfffbffffbfffffbaefeffbfffffffbeffaffefffffffffffbffbffbeffffffffffaefffbfffbfffffffbbffeefbffeffeffffbeeffeffffefbfffffbfeffffffbfffffbaffffbbeffebffbbffefffeffffffbfeffffbebffffefeffbfffeffebfffffffffbfbfebefffeffffafbbfffeffffffbfefffbffbfffefbeeffffffffffffffffbfbfebfefffbeffbffeffbffffbeffbefeffffffffbeffffeebfeffffeffbffeefeffeffbfffefeffbffefffffffffffaefefffefffbfffeeffffbeffffefffffbfbffbbefffffffeffbfffefeffbffaf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask386757 : MertensSieve.bits 386757 = 0xfbffbfffffffeffffbfffefffffefeffaebfffffbffffffbffbfbeebeeffffbfffffefffffffbeebffbfffefffffafbffffeffffefbfffbeffefeffffffeffffffffffafffefffffebbefffffffbfbffffffbffffbffbfefeffffbffbfefffbfffeffeefffffefbfffffbfffffeffbffeffbffffbffbfefeffefffefffbfffaffbfffefffffffbfbaefbfffffffffffeffffbfffeffeffbffbefeeffefffbefbbfffeffefeffffbfffefbaefbffefbfebfffeefffffffbfbefffffbffffffffeffaffffbeeffefffffffbffffbfebffbfffbffeffbefffffffefbffbbeffffeefffbefffeffefbefffbaefffbffffffbffeefbfffffaffefbeffffffebbffbfffefffbffffefaffefbbfffebbffffffffbebfffeefffbfffffbffffffefbfffbfffeffffbffbefffffeffffefbffbffbfffbffeffeefbfffffbefffbfffffffefbffffbffbbfbeffefffffafffebfebaffbffbeffefeefefffffeffffbeefbffbfffebfebffbfffeffbeffffefffffbffbffbffffbefffffbfffefffbbffaffbeffefffbfffffbefffeffefffffffeebffbefffefbfffebffbfffefffffbfbbfbeffffffffbfffffefffeffffbfffffffbfffffffebfefffffffffbaefbfbefbfffbffefbffffffeffbfbfefffffebfffbffaffffbffffefffbbfbfffefffefffbffffffefbbefeffffbfebfeffffafffffbebeffffffffffffffeefbefeffffbffffefeffeffffbfeffffbffbfbaffbefffbbffffffebfffefbfffffffffffffffeffffffefffbffbfffffbbebbfbfffbffeffeeffebefbfffafffefbfbefbbffffbfffbfffefeffffbfffffffffbffaffbebffffffeefbfffffffbeebeefffbeffbfffffbfffffffffebfefeffbffeefbefffbbffbfbefbfffffbfffeffbffffbffffefbfbfeffeffefbffffbfefffbffbfffffbbfbffffefefffffffbffbfebafffffbebbffefbfffffbbfffefffbfeffffffffebfffeffeffefffffffffffffbaffbffeefffffffffbbfbffffffefffebbeffefefffffefbffbfefbfffffeffbeffebbffffbffbffffffafffffeebffffffaefbffbffffbffffefffbfeffffeefeeffffefffffffbfffbffaebfffefffefbffffffefffffffffffefbfffffeffeffbffffbfefaefbffbfffffffffffffbffbfffeefbffbfffffffbeffefffffeefffbefffefbffffbfffffbaefefbbfffffefffefaffbfffefffbfefbfffffffffefffffffeebbffeffffffffeebffffffffffffeefffbfffffffffbfbfeffffbffefbfffbefffbfffffbaffffbfffeffbfbfeffffffbfeffffffbffffeffffefbfefffffffbffeffeefffffffbeffffffbffffffeffefffefbfffffeffefbfeffffffbfffffbaffbffeefeffbffeffffffeffffefbefbfffffbfffbffeffbffeebfefffbffffffffbefffffffbbffffffffbffbffffffefffffffefffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask394949 : MertensSieve.bits 394949 = 0xfefffffffbeffffbfffaefefbeffffffffaffbfffffffffebbffffbfffffffffeffefbbfbbfffffbefffbeffffffebaefbffbfffffffffefbffffffffffffffbfffeffefefbafffffbfbfeffebfefbfbfffbffffffffffbfffffbfffbffffbbfbfebfffaffafffefbfbffffefffbfefffbfffafffffeffffffffffffffaebfffffbfffaffffbfffeefbefefbffffffefbefffffaefffbffffefefbfffbffffbefffffbffbffeeffffffffebffffffbfffffffbbfffeffffaffffbffffebfffffffefbffffbfffbffaffffbffbffffffeefffffffffffffefbbffeffeffbfffffbeffefeffafffffbfbffffffffbefbffffefefffffbeffeffffffffffbeffefffbfefeffeefffbfeffeffffeffffffffbffefbffbbfffffbfffffffbffbeeffefffbfffffffffffffffbefffbfffaffbfbffffebffffefbfbfffffbffbeeffffbffffbffffffffbfffffffffeffbffefffeffeffefeffffbfeffffffffffbfbfefefbfefbffefffeffebbeffffeffbfbffbffffffefbffffffbffefffefbfffebfffbfffebffffeffffefbbfffffeffeefffffebffbffbfffbfffebfffffffffffffefbeffefeeffffbfbbfbffffffaffeffbffffbbfffffeeffefffbbefbffefffefffbbfffffbebfefeffffffffbefffffefaffaffbfffffefffffffffffffffffaefbfbffffebffbefffffefffefeffbffaffefbfffffbeeffffbfbbfbfffbffbfbfffffffeffefeffffffefeffeefffbfffbfffffbefffffeffebeffffffffffbffbffffffaffffbfffeffaffeffffffffffbeffaffffbfeffeffefefbbffffffeffffbffeebbfbfffeffffbeffbffefffffeffeefbebfffbffbfbfffbffefbeffefffffbfbefbffffffffbffffefbffeffaeffffffbfefffbbefffbeefbffbffffffefeffbffbffbfffefffbfefffffffbfffeffffeffffbbfbffffffffbaebffffefafffffeffbffefffffffbfeffffffffefafffffbfffebafffffafffffeeffffeffbfffffeebfffffffffffbeffeefbffeffffffffaefefbfffffbefffefffbefbffffffaffffffebfffffbffffffbeffffeffbefbffeffbffefffefffbffbfffefbbefbffbfffffffbaffbffffffffeffffffffffffffffffffffffefffbeefbfffffbffbffffbfefafbbfffeffffeefffbfffbefefbbffefffffffbffffffefbeffbffeffffffffaeffffeeffffffbffbfebefffffeffbffbfbffffefffbafffefefffefffffffffbffbbffbffbfffeffffaffaffffffefffffffbffbefffffffeffeffefbbffefffffafffffffffffbffffffffbfffefeeffffbfffefffbfefbffefffffffbeffbffefffefffffffffbeeffffeeffffbfffffffbeefbffafffffbfffffbefffffffffffffaffefbfefbffeffeffbfbffbffffffeffafffefffbffbeeffffbebbffeeffffefffffbfbffbbffffffefbeffebbfff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask403141 : MertensSieve.bits 403141 = 0xfffffbfffffbffffffbebfefefffffbffeeffffffbfefffbfffbfbeffeffffbffbbfffefeffbfffebbebfffbffffffefffffeffffffbbfffffffffefffffefffbffbeffefbfffffbfebeffbffefffefffbfffbffbfbffffefaefffffffbfffffeffbfffffffbefbfefaffefffefefffffffffebfefefbbfffffbeffebfffbeffffbfffebffffefffbbebffffffbffffffebffffefafffffafffffefbfffffbfffffffeffffeffbefbffffbeffbfbfefffffefeefaffbffbeffffeffbfbeefffffffeefefffeffffeefbffafffebfffffffeffffbffffffeffefeffbefffffffbffefbeffffbfffbefbfbffffefeefffffffefbffbfeffffaffeefbffffffffaffffbbebffffeffffefffffffbfefffbfefffffffefffffbfffeffefbffffbfefbefffbfeffffbfbffbeffbffffbfebfffffffffeffefffefffffefefbfffbffeefbffffbfffffbeffaffaffeffffbfffbefbfbfffbffffffffffbfefffbeffffffffefbffbfefefffffeebbffeffbffeffbfffefffbeeffffffbffffffbffbfbffbfeffefbefafbefffffeefffffffefbbffffffffbffefbffffefefffffbfbfffefffefaffbffbfffffbeffffbefffbfffeefffbfeffefffbeffafbffffffffbeffffbeefbfbffffffeffefbffbeffefffffbffbfbefbfffffffffbeffefaffefbffbfffffffeffffffffeffffbefeffaffbfffffeefbffbfbbffeffbefefffeffebffbbffbffafffffeeffeffffbffffffffbfffffbffbfffffbffffffeffeffeffffbffffffffffbfffffbfefffbffffeffffefbbfffeffffffffffffbfeffeffffafffffeffeffefffebfffffffffbfbaeffebffbfffbffeefbebfffeffffffffbfffffbffffbefffeffffeffeffbfbbffeefffffffffbbffefbfffffffffbfffffbefafffffffffffbefffffeffffefbffffffeffbffefffefafffffbfbfebffffffefffefefffffafbeffffffebfeffffbfffefffbbffeffffbffbfefaffefbaffbfbfffefffffffbbfbffffefffffeffeffebefffffafbbffeffffffffafffffefbeffffffeffffffbaffffbfffffbffbfefefffefbebffbeffbffbffffbffffefffbffffffffffffafffebffffebfefeffffbfeffffaefeffbfbfeffffffffffffffffffffffafbeffbfbffffffffbbeffffffffffffffefffbefffffbfffffffffffffffffefffffffffeffffbebbffefbfefefbffffeffeffffafbbffffbfebefffffeffffffffaffeffffbfffeebfffaffffffefefffefaffeffbefffffffffbbefffbfffefffffffbffffefeefafffeffebfeffefbfffefffffffeffeffeffbeffeffffaffefffffffbbfffffeffffffefeefffbfffbebfffeffeffffffefffbbffbffeffbffeebfeffffffbffbfffbffffffffffbeffffffffffbbfffefbfffffbfbbfffefeffefffffbefeffafffffbffffffffeffffbbfffe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask411333 : MertensSieve.bits 411333 = 0xffefffffbfbeefbfbfefbffefbefffeffffbfffffffbffffeffefffbefbfeffffeffeffffbffffffeffafbffbfefffbefffffffffffffbffffffaebbfffffffffffeefbeffffefffffbefbeffeffffefbffbbeffefbeffffbebffbefbbffbfbffbffbfffeffeffbfffffffbfeffffeebffffffaefffffffffbeffffffffffbfffefffffbffbffbffffbbfffffffbfefefffefafbafbfeffffbffeffbefffbfffffffffbffbfbfefeefeffeffffffeffffefffffbfbeeffffbfbffbbfffebfefffbffffebefbeffbfffffffbfffaffefbfffffbfffeffbfffeffffeffbffbffeebbebffffffbffffbffffefbffbfbeffffffffaeffffbeffeffffbffafffebffbffffefbffeffffbffffffffbafbfffffffefbffefbfffeffbffbffffbffbffbfefffbffbbefeefeffffffefbfbefffefeffffffffffffefffbaffbfffeffffffbeffbffffffffffffffbefefffffaffbeffefffffeffffffffeffffffffffbfffffefffeffffbffffffefaffffffefffbefffffffbffbfffeffaefbffeefffbfffafffffaefbebeebffffffbfffffeffffffffffbfeffffbefefbbffffbfffeffffffffbfbeebfffffffffbfffeffefbfffffffffffbffbffbefffbfefbefaffefbffffffefffffbeffefffffffffbbfffebffbbfffffbffffffefeeffffefbbffeefeffbfbffbbfffebbfffffeffbfbeffbffffbeffbfffeffefefffffbffffbfffeffffbfebffffffffbfffffbffffffffffebfffefffffbfffeffeffebfffbffbefbefefffffaffeffbffeefefffffbfbfffefffffbffefbffbfeffffefbfefffbeeffffbffefffffefffffefbfefffbeebbfffffefbfeffebbefbfbafffffeffaffeffffbbffffffefbffbefffbfffeffffbfffbffffbeefbfffebfffefffefefbfffbefffbfffafffebffffffbefeffbfffeffffeefefbbffffbffffeffffffbffffebeefffbefffefeeffffbffaefffffffefffffffbffffffbffbfffffbfbfebbffefffffbffffbfffffbbffffbefffeffffbebffffefaffffffefffffefffffffeffbfbffffefbffeefbeffffffffffefffeffffbffeffefbfffffffffffffefffffffffffffbeffffffbbffbfbfeffffffbeefffbfffbfbfffaffefffebfffeebeffafffeffffefbfffefffffbffffbfffefbbffffffffaffbfffffffbfeffffbfffffbffefffffbfffffffbffffeffffffffffffbbffbffaffbfbfefbffaffffbbefffffeffffffffffefbeffffbefffffffffffbffeffbffffffffffbbefffffffbffeffeeffffeefffffffbebfefeebfffbffeffbffefbbffeffbfffefefbfffbffaebffbffbeffbfffffbffffbeefffbbffffffffbfffffffffefeffaffeffbffffbffffffbfbaffbeffebbffffbbffbfffffeeffffeebffffefbefefbeffffffebfffffbffbffbeeffffefbffffeffefffffffbfbfefffbfef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask419525 : MertensSieve.bits 419525 = 0xfbffffffeffffffffffffffebffffefbffbffffffffeffefbeeffffffffeffffefbbfbeefaefffbffffebfeffffbfffefbfffebfffffbbffffffebaefffffefffffffeffeffffbfffffffefffbffffebeebfffffbbfffffeffeefffffebffffffeffbffaeffffeeffffbfbbfffeffffffffffbffbfbeffaefffbafbffffebfefbffffffeffffeefbffffbffffffbffffbfebfefffbfffffffffbfffeffffffffffbefffbeffefbffffffefffffbffbfbfefffbfffffffeffffeeffffbffeefffffffafffffffbffffffbffaffeeffeffffffffffffbbfffebfeffffbffffbffffffbfbbffffbfefeefbffaffffbeffeffbfbbfffffffffffffffeffeffffeffffffeffefffffffefbffbffffffbffefffeffebfffeffefffebffffffaffffbafffffefbfefffbffffffeeffefeffefbfebefffffbffeeffffffbfefefffffffffebfffffbfffbeffffbffbffaffffbffbfffffbefffffffbefffffbfffffeefbffafffffbeffefaffeffafbfffffffefaffeffffffebfffefffefbfbffbefffffbffffffffeeffffeefffbfebfeffffbfffffeffeffbffffbfffeefbfffffefffffffffffbfbbfbfffefffffffffebbefffbbffbfbfffffbffbfffefbeffbfbfefeefffbfebffbfffffffffeffbfbffbaffaffefffeffeffffbffffffffffbbffeffbefbfffffbffffbffbfebfefbffafffffbffefbfefffffffbfffefffffffefffefffbefffffaffbefffffffefbefffeffefaeffffbfbbffeffbffeffffffffffbeffffbfffbfbfebeeffffafbfffeefeffeffffbffbefffffffffefbeffefbefbfbfffbefeffbfffffbeffefffbfffeffffffffffbbffbffaeffebfebeefffffffbfffffbefeffffffebeefffffffffbbeffefffffffefffffffbefffffffffefefbbefaffeffffffffffffffbffffbefffffbfffffbffefffefefbfefffbfffeffaffffbbffffbfffefbbfbffffefbffffbfffffffffeefefffebfebfebbefefbefffeffefffffffeffbffefffffffbffffffefbfffbffffffffffbfffbfffffbeffffbfffffffffebffbfefafbafbffffffeefffbbeffeffebfffffffffffbfffffffffefffefeffbffaffbeffffeffbefeffefffeffffeffeffbfbfffeffbfffffbefffffffeffffffffbfffefeefffbbffbffeffaffffbfeffebffffffeffeefffbfeffeffffeffbfffffeffeffbffffbfffffffffaebfffffffffafbbfffebfeffefffbefbfffffffffbfbefbfffffffffffffefffbefffffaffefbffffffeffffbbfffebffbfeffffbfffebffffefffbfffbefeefeffbfbaefbffefffffafbfeffeffffeffffffebffffffbffefffffffffffbefffffeffffffbeefeffffffebfffffffffbeffffeebeffffffeffffeffffffffffbbeffffaffaffefffffeffbfffffffbfefefbffffffffbffffffbffefbafbffbffbaeffffeffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask427717 : MertensSieve.bits 427717 = 0xbffeefefffffaffbfbffffefffffffffbfefbffbffbebffffefffffffbfffefeebeefffbbfffffeffbefafbbeffeffeffffffbffffefffffffbffaffbfbfffaeffffffbffbfefbfffffeffbffffbbefffbeffbfffffafffffffbbebfffeffbfbbfbffffebbffffffffffbfffeefffffffffffefeefffbeffbfbefbaffeffffffefefbfefeffbfbbefefbbffffbffffeffffbfffffaffffbfefbfffffbffbffffffffbffeeffffeffafffffffffeffefefffffbfbfebffffefbffffbbfffebbefffbfefbfffffbffbfbeeffffffbeffefbefffeffefeffbffbffbfffffefffffeebbffffbeffffffffffbfeffffaffffffefffbbffffbffbfffffffffefbefffebffbffffffeeffffffbeeffffbffbfffefbffffbffffebeffaffbffbefbffffbffffffefbffffeffffffffefbefffffffafffefffbfefefffffbeffffeefeefbffeffffbfeffffbffffbbebeefeffefffffbefefbffffffffbfeffffbeffffbefbfbeffeffafffefffffffbffefbbfffebffffffbfbfffbffefffffeffeffbffeffffffffaeffefffffffefbeffbefeffffffffffffebffffefbfffefffffebfefeffaffffbffbfffbfbbfbffbffffefeffeeffffeffeffafffefffbfefbefffbefffefffbeeffffffbfefffbfffffbbfffffffbaffefbafffefffffefffffefbfbeffbefbfbfffbefeffbffffffffbffeeffffbfbffbbeffebbefffffebfffffbaeffffeffffbffffffafffffbffefffffbfbaffffffffeefbfbefffefffbfffffffeffefeffffffffbffffffebeffefbfffffbfffeefefbfffffbfeffffbffeffbfffebfefbffeffffbeffbffbfffeffffefbeffffffffbfbfffbefffbffbbfffefeeffffbffbebffffefeffffffeffebfefbfbbeffefffbeffffbbfbffbfefbffefffebbebfffbffeffafbffffffbffefffffffffffaffeffbfbfffeffbfffffeebffbffbfffffffeffffefbfffbfffeffffffffefffbfefffbfffbffeffaffbfbfffffffffffffffefffffffffffbfbfffeffffffebfeffffeefffffffffbeebfffbfffebfffeffbefaffefbbebfebeffffffebfffffbbeffffefbfffefffffffffebbfbfffeffffbaeffebfffbffbfffffffbfebeffffbffbbfffefeffafbeffbfffebbffeffffbbffeeffefefffffbeffebfffefffffffffffaefbffbfffefffbbefbffefffeffffefffffaffbfbfefeffffbfffffffffbfffffeffbffffffeffffefbffffffffffffbfffffeffbffbfbfefffffebeeffffeffffbfffeffbffffffffeffbefbfbeffffbeeffffffffffffbfebbefbffbfbffffefbffefffebfffffffffeffffbfefffffffefffefffbffffffffbafffffefffffaffffbbeffffffffffeefbeffebbeffffffffffeffbffffffffbebefbbffffbeebffffebfefaffbffffbefffffffbaffffbfeffffffffefffffebefffffffbfffefbbe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask435909 : MertensSieve.bits 435909 = 0xffeffbfffffffbbffefffffbebffbbffffffeffebffffefeffbeffebeebfffbffefffffffffffbffefbfebeeffffbffffbfeffebffffffbffffffeffffefbffbbffffbaffbfbfefffffffeffefffffbffefffefbfbbefbfffeffffefbfefbefffffffffffebfefeffbffefbefbbeffffbffeffffbbebefbfffefbeffffffeffefffbafffebffffefbffefbbfbeffaffffffffffbfffbfffffbfffeffffbefafbeffbfffefeefefbfefbffeffeffffbbfbfffffffffffffefffbfefefffffaebfffffffefbffefffebfebfffeffeffbfbfffffffffafffffffbbffffffefbfbffffffbfbffbffffffbefeffeffbefeffeefbffefbbfbfffeffeffeffffffefeffffffebbfbfebbfffffffbfffefffefffbfefbffffbfeffffffffebfebfffbffaffbffffffffbffefffffeffbefffffffbffffbfffbffbefbffffbfffefbeffbffffbbeffffbffffbfffeffefbffffeffffbfffffffffebfefffffffbffbfffffeffffbefbbfffeffffffffebbfbfeffefffffffbefeebefffffbeffffeffaffeffffbffffebbfffffbeffebffffffbfbfefffffffbffeffffbfeffebfffffffeffefefffffbfbefbffffffaefefffebfeffffffffffffffebfebfffafbeffbfffebeeffffffbffffffaffbfffffffbeefbffbfffffbfbeeffffbfbffffeffefefffffbffbefffbbffffbafbffbffffffbffffffefefbfffffffffbfbfffbffeffffbfefeefeffefffffffbfffbffbfbfffbefeeffffffbffbffbffbeffbfbbefffffefbffeffeefbffffbefffffbfbfffeffeffffbeefbfbfffefffffbfbfffefffffbfbbfffeffebeffeffffffefffbfefeffbffffffffbffeffbeffffeffffffffeffffbfffbffbfbefffefeffbfffffffffeffffbffffffffffffebfffefbbffbefeffeefffffefffbffbfefefffefbffeebfffffffefffffefeffffffeffefffbefffffffbbefffffefbfbffbfeffeffffeffffbfffefbaeffffbffffbffbfffffbbffffbfefeffbffeffffffffeffefffeffefffbeffbffbeffefeffbffbfbfffffffeffffffbfebfffffffffbfffffffffebfffeffefffefffffeffffbefbfffffbffeffffffefffbeffeffeffffbfefffffffffbfffeffbffeffbfffffefbeefffffebfeffeffffffffffbffffffefffbbefbfbfefeefffffebbffffffffffffeffeffebfffffbefbffffffeffffffefbfbeffbffffbeffffbfffeffbfffffffbeefeefffffebfffeffbefbffffffffefffffbffbefffbefbbeffffffffffefffffeffffbfffeffeffbffbfbfeffffffffffefffebfebfefffffefbffefffffafffffbefffbfffbffffbffffebfffafbfffbfffffaefffbbffffbffbfeffffbfffffffffefffbffffffeebfffbfbbeffffefffffbffeffffffffeffbffefbbffffbffffffefbbeffffeffffffffbffeffbefffbfefffffebfffffbfef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask444101 : MertensSieve.bits 444101 = 0xfffbfefffffffbefbffeffeffbffffbfebffffffbffffffffffbbeffffffffefefbfefefffffbffffbefffffaeffeffefaeffffbefffbffffefbfbfffffbeffbffbfffefbfffffbffeffbfbfebfebbeffffefffeffefefffffbfffffefbeffffbbffffbfffefffffffffebffffffbffeffbfffffeffffbefbfffeefafffffaffffffeffffffffffbeffffaeffffbfffffffffffefbeefffffeffefbffbfffffefffefbffffbffffefbffeffeefffbefbafffffbffbebfeffefafbaffbffffbeffffffffbfbffbfffbffeffffffefafffffefffebffbeffffbefffffeeffffffbfefbebefffffbffffbfefeffbffbfbeffbeffefbfffffffbfebefbfeffffaffffbffbbefeffbefffffefefffffeffbffeffaffffbefbbffffffffeffbfbfeffebfffbfbbfbfeffefeffffffffffbffffffbfffeffefffbfefffbfefbfbfffeffffffffffbeefeefbfbfefffffefeffeffffbffffebbefefbffffffffffffffffefffbfffeeffffafbffbfffeffffbfefbffeffeffbfbbffbfffefaffefbfffbfffefaffffffebfefeeffffaffeffbffeffbeffffffbfffffffffbfbaefffffefffffffbffbffffbfffffbbebbfbeffbffefffffbefefffffeffffffefefbfffffbeffbffffbfffffffebbffffbfeffffffffefffffffbffbffffffffffffffffbffffffefffffeffbfbefbbffbffffffefeefbffffffffffffefeffffffffbfbefbfefeffafffebfffeffbfffeffffefbfeffffffbbffeffbffbfbffffeffffbffffffffbefeffbeffffbfffeffebbefffffebffbffffefefbfffffffffaffffbeffffffffeeffffefbfffffffffaffffffefffbeffeffffffefffbbffafbbffbfffefefffffffffffefffffbfbbfbfffffffffffbaffbffeffeefbffeefffbeffffffffeefffbffbefffffbffbffeffffffffbfbfeffffbffeffffbfffeffeffafffebfeffffbfffffbffbfbffffffffffefbfbefffffbffeefffffffffffffeffbffffffffefbeffffffefeffefffefffffffbfffffeeffefffbefffffefffebfebfffffbfeffffeffbffefffefffbeffafffffffbbefffffefaffbffffffffeffefbffbfffffbeffffffeffefffffffefbfffffffebfffffbefbfffffffffbfbefbfffefbfffefffffbfbfeffffafffffbefffffffffbbfbfffffffefefffebffbffffefefbfefbfffffeefffffffbfbffffefffbfefbffefbfffffffffffffffbfffffbfffefffbfefffbbfbfefffffffefffffffbffbbffeffefffefffffffffbefbbfffeffffffffebfebfffefffffbfbbffefffefeffffffefefbbefefbbfffefefffefbfbfebfffffbffffffbfffffeffefffffefbffffefeefffbfffbfffeffffeffeefbfbfebbefffffffbffeefaffefbffffeffffaffffffffffffebaffffffffbffeebeffbfffeffffffffffefffffbebefbfffbffffbbefeeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask452293 : MertensSieve.bits 452293 = 0xfefffbffbfffffffefefbfefbfbefffffeffeffffffffeefefffffbffffbfffbffefbffffefeffbffeffbffffbfffbffbfbbebeffbffbffbfffffeffffffffffffefffffefefbfefffffffbffffffffbeffeffefffbffbffffffbffefffffffffffbffbffefbffffebfffbfbbfbbffefffffffffffffffffaffefffffffbfebbffffbfffbefffffefffbeeffffeffaeffffeeffefefffffbffefffffeefbffeffffffeffebfffffffffbffefffffaffffffffffbfefafbfefbffefbeefbfbaffbfffefeeffffefbffbfffbffefffffffbffbfefaffffffffffbfffeffbfffeffffbffefbffbffbfefeffbffbeffffeebfffffbfebffffffeffffbeffffffeffffffffffbebffffefffbefffffefbbefefffffffffffffffffbffffbffbfefaffbeffffffffffffbbfffffffffffefbeefbfbffbfffefffffbebffffffffbffffffeffbffeffffbfffffffefeffeefffbfefffffffeffffbffffffbffeffbfbeefeffbfbffffeffebffffffffbffbefbffffffefbbffffffffeffbfffffeffeffbfbaeffefffbbfffffbefffbffbffffffafbbffeffeffefffeffeffefbffffffebffbffffeffffafbbffffffefefbffffefeffaffbffbffffbfeffffffbffffebfffeefbfffffffffffeffaffffbffffebbfffffeffbffffffefffbbfffffeebeffffbfebbffffbeffbffaefffbfefbefffbbffffffffeefbffbffbfffefbfffffeffbffeeffffeffffffffeffbfffffffffefeffbffffffeffffffbfffafffffffbfebfffbffffffefffbfefffbfefbfbeeffefefffeffefeffefffffbfffeffffbffeffffbbfffeffffefbffffefffffeffffefbfefffbafffffbffbffffbfffffbaffffbefffeffffefbbffefffffaffbebfeffffbefbffbffbefeffeffffffeffebeffeefeffffbffffefafffffeefbfbfffefffffefbbfbfeffffffbfffffbefffffffffefbffefffffbfbffbfffeebfffffbffbfebffbfffafffffffbfebbffffbfffffbffffefffbbffffffffaffafffffffbeffffffffeffbfffefbfffffafffffffbaffffffefbeffffbffffffebfffffffefefffffbfbfffeefbffffbfffeffbeffffefffffefbfffaffbebffbfffbfffffbfbfefffffffefffffffbfffafffffbebfeffeffffbfbefffeffeffffbfbfefbfffeffeffffffbbffeffbfffffafffffffffeffffeffffffebbffffbffbbfbfffaefbffefffebffffffaffbeffffffbfffffffffffffffeffbffffffeffffffffffafbbffffbfffeffefbfefeeffffefffffbfbffbfefeffafffeffffeefffbeefffbffbfffffffeffffefffffefbfffffffefbfffffeefffffffbfffffffffffeeffeffffffbfefefbfefffffefffbffffffbffffffeffebfffbffffffffeeffffbffeffbfbffffffeffaebfebffffeffffffffffeffbfffffffffefefffefffbfffffffefffffffee := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask460485 : MertensSieve.bits 460485 = 0xffbefefbeffffbbefffbeffeeffffefbfffffbfffeffbebfffeffbffbffbfffefffffffeffffbffbefffffffbbffffffeffefbfffeffebfffffffffbfbbffefffefbffeeffefeebffffffbfbbfbfeffffeffbfbfefffffefffbfeffefffbfffffbaeffebfebfffffffefbffefffffffbfefffffefbefefffefffbfefeffaffefbfefeebfefbffffbbffffffefefbffbbffffbbefbffaebfffffbfefbffeffffbffffffbfffeffffeeffeffffeefffffffefffffafffffeeffefffbffbfffffbeffffbbfffeffffaffffbfffffffffeefefbefffffffffefbfffffffbeeffefffffffffbeffffffffbfffefffbfeffffffbbffeefbeffffffffffefffffaffeffffbfffbfffffbefbefefbfeffffeffffffffbfffffffbfeffffbffeffffffffeeffeffffbfbfeffffbffffbfefbefffbbfffffffffeffffaffbfffefffbfffefffffffbbfbeefeffffbfefbfbfeffffeffefffffffbfffaffefffefefbffffffffffefeffeffeffafffeffffeffffbbfffeffffefffffbffffbfefbffbffffbfffffbefffffffbfeffefbffffffffffffefbffffffefffbffbfffffbbeffffffffefbffaffffbeffeefbffbfffffffffffafffffbffeebaffbfffefffbffbfffeffafbbeffffefffffbebbfbeffbffffbfebfebffbbefeffeffffbffffefffbfffffbeefafffffeebbffeebeffffffffffbffbfffffbfffbfffffeefffbffbbfffffeefeffafffefffffffffbbffbfbffbfeffffbefffffffaffbffffbfffffbfffaffffbfebfffbefbffefffffeffeefffffebffffffaefaffbffffffefeffefffffbffeffeffbfbfefbffeffbffeffffffebffbfffafffefbeffeffffafbfffbffffbeffffbfefbefffffefbfffefffbfffbffefbfefbffeffffffffbffffffeffefbfbfebfeffffbfffffaebbffeffffffffbffbfffffbffffbbfffebeffbefbfbffffeffebfefbffbefbfffefefffffefffffffffffffbfeffffffffffffffebffffffbffffbffffffefbfeffffffbfebffbeffbfbffbfefffbffffffffffffeffffffffbefbfbefffeffffeefbfbeffaffefffffbfffeffefaffeffbeffefffffffbebfefffbfffffbefffebfefefffffeeffefffffefbffffbbffffffffbfbfffffbfffefffffbfbfefffffffeffffbfffeefbeffffbefbfffffeffffffefffffffbefbffefffffeffeeffffffbbfffffeffffbfffffbfffaffffffffffffffffffffeffbffeebfefffffefffbffbfffefbbfffeffefefffffffffefffbffffffbffbfffffaefffffebbffeffefffffbfffffefbbefeffafffffeeffeffffbeffffffbfffbfbffbfffffbbfffffbfffefeffffffffbebfffffffefaffffbbebeeffffaffeffffbefbbffbffffbffffffaffefffeffffefbfefbfffffffffffeffaffefffffefffefffbeefbfbfeffffeffffbfeffffbffbfffffffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask468677 : MertensSieve.bits 468677 = 0xfbffaffffbffffffbffffbfffffbeffbeffffbeffeffffafffffbffbfbefffffbfbbfbbfbffffffffffffffbefbffffffaffbffffffffefbbffbeffffeffefbffbbffffffeffffbffffbffffffefbeefffbffffffffbfffbfffffbeffffffbbeffebefffffbfffebfebbffeffefbfffefffefffffefbefffbbefeffaffffbfffeefbfbfffbffeeffefffbbebffffefefffffeebfebfeffffeffafffebefffefffbfffffffeffffefbffbffffffbffeffefffeffebeefffbffffebfebfffbfffebbfffffeefefbfebffffffbffeffbffbffffffffeffbfbbefffffffefbfebfefefffffbffefffffffffffffbeffffbfefeefbfbefbbfbfffffffffeffbfbffffffafffffbfbfeffefbffeffffffebffffffffbbfbffbfffeffbffffffffaffaffeffbefefffffffbafbffbffffffffbeeffffefffffaffbffffbffbbeffffbfbbfffeffffffbffffeffffbffbffeffffffefbffbfbeffbfbfffefffffeefffbfefbefeffeffffbffbeffbfffebffbfebbffbffbffbffffbeeffffbeffffffffffeffffffeffffaffefbbffffffffffffffbffbffefffefbffeffffbffffffefffebbfbefbbeffffafbfffeffafffffbfbffffffaefffffebfffffbeffbfffefbfbffffefffffffbfbfffaefbfffefbfbffbefffffefffeffefffffffffffffffbeffefffefffffffbfffffafffeffebfffffbfffffbffbfefbffeffffbefffffffbffbfeffffeffaffefbbfffeffffffbbfbfffffffefffffeffebfffaffffbffffffffffefeffeffffffffeffbffbebffffeffffefffebffbfefeffefffeffefeebffffffffffffeeffffffbbfbffbefbbffbfbffffffffbbefbfffffbfbffffefffffffffbfefbffafbfffbefefffffbfffefbefffffefffbffbfeffeffffeffffffebfffbefffbeebffbfefefffffaffbffeeffffbfffefffbeffeffefbfffbefffbfffbffbfffffffbbffaffffffffefffffffffeffebfffaeffffbeffefffffefefffefbfbeffefffffaffffffffeffafffeffeffffeffffffffbfbeffffffffaffbefefbfffffbffbbefffbbfffffefbffbffffffbfbbffffffeffffbffbfbffffeffffefbfebbffffbeffeffaefffbffffffbffbfbfefeffeffefffebfefefbbffeffeebffbfefffffffbffbffefffefffbaffffbfffbffbfbfffbfbeebefffffbffbefeeffffbfffffffffebaeffffbffffbfffeffffffefffbfeffeffffbffffbffbfffbffaffffffefeffffbffbfefefbfffeffeefbfffffbeffffffbbffefffefeffffbbffefffffefbffffeffffaffeffffffefffbffffffeffffbfeffffbffeffffbfebbffbffffbfeffffbffffbbffbffeffeefeffbffbffefffffefffeffefffbefffffbffffffefffffffefbffffeffffffbfefbffefffffffffefffbeebbffeffbfbfeffffeefffbffffefeffefffffaffffbfefbefbfbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask476869 : MertensSieve.bits 476869 = 0xbeffeffefefffffbffbffffffffbfffffbffffffffffffffbffefffffeffffffffffbfefefbffbfffefbfffffbffbfffffffffffbbfffefeebfeffffeffffffffbffbffffffffeebffffffaffbfbffffefbffefffffeefefffffbffbfffffaffffbfffffbfffbffefffffbefeffeffbfffebffffefbefbffffbffbffbefffffeffbfbffffffbffffbfffefffefefffffbfffffbffefbfefffbfebfffafffffbffefbeefbfffefbfbfeffeffffffbffffefbffeffbfbfffffffefffbefbfeffffbffffbbfbfefffbfffffbfefffffebfefeffeffbffffbfefffbeffffffefefffffffbbfbeefeffafffffffbffbbfffffbffbffffffeffffffbfefffffffbffefffffffffffbffeffbefffffeffffafffffeffafffffeffbfbfffbffefffefbfbeffbffbffafbbfffebbffffbbfffefefbefffffeefffffefffffffbffbfbeebeffffbfffffffffeefffbfefbebefbfffbffbfbbfffffbffeffffffeffffbffffbfebbffeffbffeffbfffffffffffffbefffebefffffbffffbffbeefeeffffeffffffffbfffffbffffffeffffffbbffbeffebbefffffefbefffbfffefffebffffffefffffaeffefefbfffbffbefffbffffffeffefbffffeffffbfffeffeffeffffefffffbffefffefefffffbfbeffbffffbffffffffbaefffffffffffeffffbffffbbfbfffeefbffeefbefeffbffeffeefbffefbfffbfbffffeffefaffeffbffbfbfffeefeffbfbffffffeffffffefffbffbfffffbfffbffeffeffeffefbfffefbffffffffffefffbffffffffffffffbbffefbfeffefefbeefefbbffffffffaffafffffbfbfeffffbfbbefbfffefaffeffeffffbffbffffffffffffffffffefbfffffffebfefffbfeffffefbeffbffffbfebfebbffffbaeffffffffffbffeebffbffffffefbffbfebfffefffffbeffefefffefffbefbfefeefffffffffffefffffffffffffffbfefbfffffbeffeffefeffffbfeffffeeffefefffeffeffffeffaffbfffffffbfefbffefffffffbfefeffbffbffffbbffffbbfbfeffefeffaffffffffefbfefbfffffffffffefffffffffeffebbfffffbfbfffffbbffffbefbbffeffeeffffbfbfefeffbffbfbfebfefffbfffefbfffbebfebfffbffeffffbffffffbffefbbfffffbffeffbebfffffffffbfbffffffeffafffffbebfefefbeefbfbbfbfffffffffbfbbfffefffffffffffebffbeffaffffffefbfbfeffffaffeffffbfeffffbffbffbfffebbfffffbffffffffeffbffeeffffffbeffffffefffbfffeffffbeffbfbfffaffaffefbffffebffffffbfbbeffffffffffefbfffffffefffbbfffffefffefbffeebffbfffbefbffeffffffefefffffbffffffeffffffbffffebfffeffeffeeffffefffeffffbffffffefeffefffffffffffbffeffffbfffffffffbffeeffffffbfffbffaebffffefeefffffffffffefeffbffffbbfffe := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask485061 : MertensSieve.bits 485061 = 0xefbffbffafbfefefffefeffbffbfbefbaffafffeffffffbfffefbfffbefeffefffffbffbfffffffffffffbfefeffbffbfffefffbfffffffffbfffeffefaeffffffbfebffbfffffffebffbffbeffaffafffefffbfffffbffbffffffbffbffffbbffffbbfffffffbfefeefbefeffeffffffffffffffbffffbeffefffffeebfffffbfffffffffffffffffffffffffffeffbffffbeffbebefbfffeffeefbfffffbefeffffbffffffbfffffbfffffefbfefbffeefffbffffefefbfeffffffbfefbffbffbffffffefefffebffbefbfffbfffebfeffffffffffafbbfffffaefefbffffefffffffefbefffffffffefbffeeffebeebffffffaffffbeffeffbfffffffbeffefffffffbbfbfeffefefffffffffffafffffbfffebffffffffbfebffffebfefaffeffbefefffffbffeffffbfeffefefffffffffffbffaffffffefeffffffffeffffffffaffffbffbbfbffffffbffaebffbfefaeffffbffffbeffeffffbbefffffffeefffffeffffffbffffffbfffffeeffffffbefbbfffebeffffbfffbeffffbffeffbfbffffffeefbfbefffffffffefffffebffbfffaffeffefffebfffaffffffebfefffbfffaffffbbffeffbefffbbebffffffeffffbfeffffffffffaffaefffbefffffbfffeffffffffffbffeebffbfeffffffffefbfbffffefeffbfbbfffebfffefffffbeffffbefefffffffbfffbffffbefffebffffeffffefbffbfffeefffffefbffeefefffffffffefeffbfffffbfbfefeffefffffbffbfffffeffeffeefffbfffeffffffefbefffffefbffbffffbfefbffefbefbfeffebffffffffbfebefbfefbfbffffffefbffffffbfffffeffbffffffefffbfffefffffaffbebfffeffffffefbfbeefeefafbfffbfffffaffeffbebbfffebbeffffffbfefeefbfffffbfffffffffffeffefbffffffeffafbeffffbefffffffbfeffffffffefafffefffffffbffaffbfbfffeefbffeffefffefefbfefefbffbfefffffefaffefffffffbaffeffffffefffffffffffffbfffefeefafbeffbfffebbfffffefbbeffffbffeffffffffefbbffffbffffefffbffffffbebfffffbbeffffffffffefffffbffbefffbefffefaffffffefefbfffbffefbffffebbffefbfffbffffffffefffffffbeffeeffffefffeffebfeffffffffefefffefffbafbbffeffaeffffefffeffefbffeffbffffbffbfffafbffbfefffffffefbfeffffffbfefaffaffffffefeffafbfefbffeffeffffffffbfffffaffffbfeffebfffbfffffbefffbfffbffbffffbfefeffaefffbffffffefffeffffbfffeffffbffeffbeffffffffffffffebbfbfffffffffefffffefffffaffefffeffeffffbffeffbffffffffefbfefbffffbfffffbfffffbfeffeffffbfffffffbfefffbefbffffefbffbfbffbbffffffffbfffffffffffbffffffffffffebefffffffbbefffffefbfbfeffeffffeffffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask493253 : MertensSieve.bits 493253 = 0xffffbfbfefeffffbfffbfffffafffffeffffbffbfffbffefffffeefbefefbefbbffefffeffffbebfeffffbffeffeffffffffbefaffbeffefffffeffffeefbffeffaffaffffbbefeffefffffbfbffffebfffbffeffffffffeffefbbefffbefffefbfffffffffeffffffbfffbfbffbfffffffffbfbfefeffffbfebffbfffbffbffeeffffeeffffefbffffefeffeeffffbffbffffffefeffaebffffeffeffffaefbffeffffffffbebbfffffbffeffefffeffeffffefffffffbeeffefffbfffbfffffbefffbbfffffeffffffffbfffefffbeffffffffbfbfeffefbfffebbfbeefaffeffeeffefffbeffbffffbffbfeffffffbbffbffeffafffffbffffbfffbffffbefbffffffaffefffffbeffeffffffbeffbffefffffeffffbffffefafffffafbfebeebfeffffbfffffffbbfffffbefbefffffffeffeeffefffbfefbfbfffbfffffefffffafffffefffffffbffbbebffbeffeffbeffffffffffaffbfffffefbbffffffebffbfffbeffffefbfffffbafffffeefffffebefffffbffffffefaefbfffffbeffffbffbffffffefffffffbffafffffffbfffeffffffefffbbffffbfffffbfffaffefffeffefefffffffffefffbeeffefefbeffffffefffffffbfffffeebfffbffbfbfffeffeffffffebffffffeefeffbfbfeffeffefbfbbfffffefffffffbeffbfbfffeefbffefffeffebeffbffbeffeffeffffffbefbffffefffffffffbffbfffbffefbefbfebfefeeffffbfffffffffeffffefbfffeffeeffffeebfffefffffeffffbbefffffefbffaffffffffbffefffffffbeffeefaffefbffffefefffffeefffffeffffffbfffbffefffffbfbfffbeffefffffffffbffffeffffffbbffffffefffffffffbffbefbeefbffbefffbffbffffffbfffefffffffffbbeffffeffbefafbfffffbffffffaffffbfffefbfffffbffffffffbbffffffffffbeffbffbffbffffbffbfffffbfefbfbefbfffbfbfffffbefffeffffffbffffebefffffafbbffeeffefaffffffffefbefffffbffbffffbfefeffaebffffebfffafbafffffffbfffbffffbffffffeefeffeeffefeffeffeffefbfebffbbefffbfffbeffeffefeffffffeffffeffbffbfffeffffeffaffbefffbeefffffffffbbfffffaeffffefffffffbffffffbffffbefbfefffbbfffffefffffefbfffffffffbffefbffffebfefbefbfbbefffbefbfefbffffbbfbfffeefeffffbbffffbafffffbfffebffffeffffffbffffffaffffffefbffffbaffeffbeffefffbfefffffffbeffebfefbffefffffefffffbfffffbffffbeffefffffbefeffbefeffffbfeffefbffffffefffbefbffffffafbffbffffeffffeefffbeffffffffeebbffefffefffffffbffeefeffafffeffffffffefffbfffbefffbfffffbbefbfffffeffbfbfffffffffeffffbeffbffefffffffbaefffffeffffbfffeffffeffeffbffaffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask501445 : MertensSieve.bits 501445 = 0xeffbffffbffbfefeefbefefbffffefeffffffffeffffffefeffeffeeffffeeffffffbbffffffeffeffffeefbeffffbfffffbffbeffffbffffffffffffebfefffbffffefffbfffbfbfeffffffbbffffffffbffeefeefbfbffbffbeefaffffffffbffffbefffffefbffbfeffffbffffffffffbfffefffefffffffeffffbefffebffffffffbaffbfbfeffffbffeefffbfeffefbffffbffbefffffffffeffffefbbffeffffbbfffffeefffffebffbfffbefefbfeffffffbfffbffbffffffeffffffbefbbffeffffffffeeffebfefffffffbfbfefefffeffffaffbeffffbffffffffffbffbeffefbefffebffffefffbfffffbefffefbfffefbfffffeffbfffffbfbeeffffbffeffffffffbffffbafbffffffefffffffbfeffffeffffbffbfebfebfffeffeeffeffefffffffffffffffffeffffeefffffffbffaffaffffbeefbfffffafbffffeffffefffffffbeffbffffbffffeffeffffbfbbefbffeffeffffbeffffffeffefbfbfefffffffbffafffffffbfebbffffbfffbfffeffffeffbebfffeffbffbffeebfffffbeffbffbfffebfeffffffbefffffeffefffffefbbfbeebffffffffbfeffefbffbffffffffeffeffffbfebfffffbfffbffbeffeffffbffbfffffbffffffffffffffffbfefeffefffffbfbffbffffffefbbffffffffffbbfbffffffeefffbbfffffffbfffafffebffffefbefffbbefffbefbeffffffefffbffffefffbfebfefeffeffeffbffbfffeffffaffbffffffebfeffffbffbebeffeffffbafffffffffefbfffeffefffbefffffaffffbfefbefbffefbfffefbeffafffebbffffffffafbfffbffefbbefeffffffefefffefbffeebffffffeeffffaffbffffbfffffffffbffffffffffbefbbefffffffbffaffbfbefffffffbfffbffffbaffffffffffbeffeefffffffffffffbffeffaffffbeeffefffbffbbfbfeffffefffffbfffffeffeffeffbefffffefafbbfffeffffbffffffeffefffbffffffefbfeffefbffefbbffbfbfebfffbfffffffbfeffefbfffffbebfffbffbffafbfffeffbfffffeffbffffffffffbfefbfffffaffaffbefffffffbffafbfffffffffeffffbffffffeffeffbfbfefbfffefaffeffbfbffbffffefffbeffbffffbfffefffebbffefbfefffffffffbffbfefbfbffffffffffefffffefffbffffefffbffffffeffefffffefffebffffffffbffffefffbeffeffbffbffffbeffafffffffffeffefffbbffbfffeffffbfbfebfffefffefbffffffffeefbfffffeffbebffbffffffffbfeffefeffefffefffffffffffffbfffeffffefffffefffebffbfeffffeffffffffeffbffffffefeffeffffffefbebfffbefffbbfffffeffeeffffffbbffefbfffbffffbffffeffffffbffffeffebeefffbfffffbfefffffffffbffbffbaffbfffffffbffffefffbefffefefffefffbffffffffffffbfbfefffffffbffbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask509637 : MertensSieve.bits 509637 = 0xfbefffffffffffffffffbfbeefeefbfffffffffffffffffaffffbeefbefeffefbfffeebfffffffebbebffbeffaffafffffffffefbfbbeffefefbfffffbeffffffffbffeffeffbeffefaffeffefbbfffefbefeffffbffffefffffffffbbebefbeffffbfffffffffbffbffaefffbfebfffbffffbbfffffbefbfffffbfbfefeffbfffeffffffffefffffffbefeefeffeffbeffffeffbffffbafbffbfebfffffbffffebfffeeffffbefffffeffefeffeebfefffbfffbffefbfebfeffffffbbfffffeffbefffffebbffefbbffeffbefffbfefaefbfffffbffffffffbffefffffeeffffffbefffffefffffeffffbfeffefbefffffffbffeffeefffbbfffffeffbffffbeebfeffffeeffffffffefefbeefffbfebffbfffeffbffeffbfbfffbfffffbffffbffbffffffefffffffffffeffffffeffffeefaffefbffffffbffbfffefffbfffffffffeebbffffffffbfffeffffeefbfffffffbffffebffffffffffeffffffffffffffffffbfffeffbefffffffbffefffefbfbefbeffbfbbfffffeffbffeffefbbebefffffbffffffeffeffffafbafffeffffffffffffbfeffffbffafbbefffbffffffffffeffffeeffeffffbffffbfffeefffbfeffffeeffffeffefbffffebbffeffbfffefffbfefffffffbffffbbefffbfeffebfffeefaffffffefeefeffbffeffffffffbefffbeffffbfffeffbffffffebfefffffffffffeffebeffeffbfbbfbffffefbfbbefffffefeffbffffffffeffffffffffffffeeffffaffffffebeffffffffbfbbfbffbfeffffffbbffefbefffffbebbfffffbefeffeffffbffffffffbffffffeebfeffffefbffffefaffffbfffbfbefbeffbffeeffebfeffeffffbffffffebeefffbbfbfffffffffefbffffebfffbeffffbffbefffbefffffeebffffffbffbfbefffeffffeffeffeebfebeeffffffbefbfefffbbefffffffbfffffbffeffbffffffeffffffffeffffeffeffbfffffbfffeffffaffffffffffbfffffffffbffffbfeffffffffefeffffffffbffbfffffeffaffefbffffffafffffbefffffeffefbfffefbfbfffbffbffffbfefefbffffffeffffffffbffbfbffbffffeffffffffebbfffffbffbfbbefffbfefeffffbbffbffffbfefffbeefbfbffffefeffffbbfffffeffbffeefbffffffefeffbfffeffffbefffbfebfefefffefafbfebffffffbffafffffbfffffeeffffbefffbeffeffefffffffffffaffbffbffbfffeffffffffffbffffbbefffbfeffffefbfffbfffffffffebfffbfbeffffffffffffffaebffffefaffefffebffffefffffffffffeffffbefafffffffffffaffffbbfffefffffffbffbfbffbffbfffbfffefbefefbfefffbbffffbffffeffffeffbeffffeffeffaefbeffebfffbfffffbfffeffffffbbffbfbfffeffafffffffbffbbffffbeefffffffeefffbfffbfffffeefbfbfffffbeebefffffbefbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask517829 : MertensSieve.bits 517829 = 0xfffffffffbbfffefeebfefffbfeffffefbfffafffffffbffffefeffffffefeefffffffbfbbfbeeffeffffefbffffefeffffffffbfbeffbffbffffffefeeffefffffebfffffbeeffffbebffffeffefbffaeffebefffffffffefffbfffffffffeefbeffffeffeffbebfffffbbefffbeffbfffffeffffffffffffffbffeffeeffebfffaffafbaffbebeffefffffbeffffeefbeffffffbbfffffaffefffffffffffbffbfffffbeffffaffeffffffffeffffffffbebffffffffffffffffebfebfeffffffffffefffffefffebffffebfffefffebbefffffffefffffbfffefeefffbffbfebfffaefeffffbffffeffffffbbefffbffbeffbfbeefbfffffffffffeffbfffeffffeffeffbffffbbfffffeffbffffbfffeffffffefefffefbfbbfffeffeffeffffffffefeebfeffffafbffffffbeffffeebfffeffafffffbfbfffeebfffffbbfffffefbfefffbfffbffffffefafffeffffffbfeffffffffeffffffffffbefbffffffefefffffffffeffffeffeeffffffffffeffffbfefffbfffeffffffebffbbfffffbfffffffbaffbffeefffbfebfffbfffffbfffffaefeffeffffbffbbffeffaeffebffffefffbffffefffffffefffeffeffffaeffffeffffbfeffffeffbfffffeeffffbfbfebfffffffefffbeffffffefafffffbfbffbeebfffbffbfbfffffbeefffffffbffefffffffbbeffebffbfeffffeffffbeffeffffffffffffefbffffbeffbebfefefffffffbffbeeffffaffeffbffeefbffffbfffbffefffffaffafffefffffffffbffffefffbfefbffaefbfbfffbefbfbffbfffffbfffeffffffebefffefefbaffffffeffefeffbfffefffbfffbfbffbffffffefffffaefbefefffeffffbffbffffffffffbffbbebfffaffeffffffeffebbefffbffffefefffffefffffbffeffeefffffeffffffbfffffbbffbfffffeefffbbfbffbffffffefffebfeffebfffeffffbbfffebfffefffffffffffffffffffbbffefbbffafffeffebfefaefeffbfffffeebfefbffbffffffffeffffffeffffeffffffffffbffffefbffbfbffffffefbbffffbffbfebffffefeffffbfffffbbffbfbaffbfffefeffffbffffffffffefffbeefbfffefffffffeeffffeffbffbfbfffbffffbbfffffbfbfffffbeefffffebffbffbaffeffbffbffffffefffffefbffefffffbfbfebffbeeffffffffffbefffbbffeffeffbfffebfefffffefffffffeffbffffbfebffbfefafbfffbffffffefbffffbffffefaffffffeffffefffffbfffeffffffbbfffffffbfffeebafffffbffbebffbaefeffeffffbfefffffffeffffffffeffbffeffbfbffffffffbfeffeffeffffffffebbffffbfffaffefbffffebffffffffffefffbfffbffbfbffffffeffeffaefffffebfffbffbfbffbefffefafbfeffebfffbfffffaffbffffffeffffbfbfefffbfffeffffbbfbfffefffffeeffefffffffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask526021 : MertensSieve.bits 526021 = 0xbfbbfffffefbffffffefffffeffeffbffeefffbfebbffeffbefbfbeeffffafbbfffffffbeffefffefbfbffffeffffefbfeffefefffffefffffffbfefffbbebfffefffffbffffffefefffffffffeffefefffffefbfffffffeffffffffffffbefbfffffffefffbfeffffbfbfeffffffbeefffbeffffffffaefeffeffbfbefffffaffeffbfffeffffeffffbffffeffefffbfebfffefffffafbbeffefffffffafffffffbffbfffffffffbffeeffffffbffbfeffefaffbffefbffbefffffeffffbbfffefbfffffbeffebffbafffffffffefffbfefafbffffeffeffffffffebbfbfffeefffbffbffbefffffefffebbffefbfffffbeffbeffefeffffffffffbefbbffffbbeffeffffffffffbefffffefeffffffefbfffefeefefbeffffffffffffffbfbfefffffefbfbeffbefefbafffffbefffffffffffffffbffffffeffefffefbffffffefbfbfebffffefeffaffffbbfffffefffffefffefffffeffffffffffffffffffbfffffbefbbefbfffffffbffbeffffbfefffbfeffffffbefffffeefbffffbfeffeffffafffffbfbffffffbffffbeffffffefbefefffffbffffffffbffeffffffefeefbfbeeffffffbfefffffefbffeffaffbfffebfefefffffeffbeffefffffffefbafffffffbfffeffbebbffefbefffffffffffffbbffeffffffefeefffffffbefffbeeffffffbeefffbffbeffaffeffbfffefbefffbeffffffffbefeffffffffefbfffffbffbfefffbeeffffbffbebeffeeffffbefbfffffffffffffbfffffbfffeffbebbfffffffffffffbbeffffbffefffebbefefffefeffeffffbfffbfffffafffffffbfffbffaefffffeffffbfffffffffffaffbfffeffefffffefefbfffbffefbeffffffebffbfffeefefffefffffffafffffeefffffebeefffbefffffffffffafbeefbffffbbffbfffebbffffbfffeffffbffffffaefffbffffffeffaffbffbfbffbfffbffffffffffbfebfffbffbefbfbffffffafbffbffffffffffffbfffffffbfffaffffbbfffeffffffffefffbeffaffbfbfeffffffffffeffeefffbfeffffffbfffbfffffbeffffefbfffffbbfffffefbbffffbfefbffffffffeffaffffffeffefefbafffffffffeffefeffeffefffeffeffffbfbfffffbfefbffeffffffffeefeffeffffffebffffffbffffffffefbbffffbbfbfeffffbefffffeffffffbfffeffffffffefbefffffbfbbfbeffeefffffefbffefbffffffffbfefefffffbffeffffffebbfffffbeffebfffbffefbfffffbfffeffafbeefffffffffffffeefffffffbefbfbefbfffeefffffffffbffbefffefafffffffffffeefffbbfffebefffefefbffffebffbfefaffeefbfbfffeffffbfebffffffbffbffffbfebfffbfffffbeffeffefbfffffefbbefefbffffffffffffffbfefafbffbffffeffffbfbfefffbeefffffffaffffbfffeefffffffbffeebbffaffeffbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask534213 : MertensSieve.bits 534213 = 0xefffffffbfffffffffffbfffffbeffeffffaffbffeffffbffbfefefbfffbffeefeffbfbafbfffeffaffbfbfeffffffbafffffbebbffffbfffbfffffbfffffeffefffffffbffffefbffeffffbfffeefbfbbfffffffbeffbffbefffffefeeffffffbfffefffffeffafbffffebbefafbffbbfffffbffefffffbfbffffeffffffbfeffefaffeffbffffffefeffffbffbbfffeffefbffefffefeffeffffffeffefeefffffffeffbfffffeffefffffbffffbeffeffffffefffffffffffffbefffffefbfbffbffffffbffefbffffebeeffffbffffffffeffbefaffafffffffffffeffbebffbffbfeffffafffebffffefafffffffffefefffffeeffffffffffafbeefbfffebbffffffffbeffffbffaffffbfffefffefffbfffbebefbfefeffbfffebfffefffffbfffeffffefffffffffffefffffffffffbfffffefffffafffeffffbffefbafffffffffefffbffffeffffbffefbfebfffffbfefffbfeffebeefefffffffffffefffffffffefffffebafffffbffffffebffffffffffeffefffffffffbbfbfffaffafbfefffffebefffffeefffbffbffffffffbbfbeffeffefffebbefeeffffffffffbfbffffffefbfffbffffffffffbbfbbeffffffffffefbffffffeffefbefffebfeffefbfbffbffbfffaffaffefffffffffffaffffffefffffefeffbffbefefffffefbbebfffffbeffbffeffffffffbffbffafffffffbfefffffebffffefaefffbfffbfbfebffffffffffebffffffffbafbbffffbaefffffefffbefffffafffffffbfffeffbfffffffffffefffffbefffbfffbefffffefbefffffffbfffefbefeeffffefbbffffffefbfffffbeffefffffeffffffbffbffbbffefffffbffffbffffffeffffffffffffffffffffeffafffffbeffffffbbffbfffffbffffbeffeffffffefeffefffffefbfeffeffefffbfefbffffffffbffbfbbfffffeefefbffbbebfeffffbfffefbffeefbefeffffbffffebfefeffbffffffffaffbffaebffffefbffeffaffffbffbfefbffffbfffeffeffefffefffffffaffffffebfffeeffffbffbffbefeebaffffbfffbfbffffeffffeefffffffbffbfffefbebefbfffffbfefbfbeffbffafffffffffebefffffffbfebffbfffeffafbffffffbeffffbfbfffefbfefffbaffffbfffffffffbfffebfefffffffffbfffeffbffbffefbfefffbfffeffeffffbeefbfffffeffbfffebfffefffebfffffbfffefbffbffbfebeffffffffffffffffffffbfbbfffffeffafffefffbfffbffffffefffffffbefeffbffbffeffeffeffbfbfffeffbffffbbffffffffefffffeefffbeffffffffffbffffefbffbfbfefffffefbfffffefbfebffbfffbffbffffffffffffffbfffffffbfeffffffbfebfebfefaffeffbeffffeefbfffefffffeffffbffffbfffeffffffffbfbfffffbbfffffffbbfffffeffefbffbbeffffbffffffeffeffeffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask542405 : MertensSieve.bits 542405 = 0xffffefffffeffeffbffbefffffeffffaffeffbebffbfffffffffffbfeffffbffeffffffeffffefbbffbfffffeffffffebffffefeefefbfffffbfebfefbffffffffeffaffefffffbfffebffffffaffffffefbeffffffbffffffbefffbfffffbefffeffffffffffffbfffaffaefffbefbeffbfbfffbfffefaffffbfffbfffebfffefffebbffefffefafbffffefffffffefbffbfeffffbffbffbfffffffffffbfbbefffffffefffffaffbfffefeffffbfefffffebaffeffbfffefffffefaffffbfffffffefffbbebfefffffffffbeeffffffbfffefbeefffffefeffbfbeebbffffffffbfbffbfefeefffffffbffbffefbfefbffeffffffefbfffffffbffbffbfefffbfeffebfffaffeffffffebeffeffffbeffbfbefffffbfbffbbfffffbffeffffbffffffbffffbbffbefeffeffeffffffffeffbffffbeffffbfefbffeffbffffbffffffffbbfffffffffefbfffffffffefeffeffffbfffeeffffbfbafffffffbfffefbfefbefffbfffeffffffeffffaffffbbffbfbfefeffffbeffbfbffffefefffeffebefbbffbfffeffefffffffbffaffbffeefaeffffffffeffffeffbfffebffffefeefefbffffffffffffbfffffffbeffeffffbeefbfffffefffffefffefffbffffffeffbefffbbeffffbfffffeffeffefbbfffeffffffffffffffeffffffffffbfbffbfeffffbfbefbfeffffbffbffaefffbffbbffefffffbfffffbffefffffffbffbefffffffffffffffffbfffefbefeefeffffbeffffffefbffffbfeffebefffffbffeffffbefffffaffeffffffefaeffffffbbffefbfffbffafffeffffffffffbffbfbeeffefbffbeffffeffbffffbfffbffffffffafffefffbfebfffbfbffbfffffffffffbffbbeffffeefeffbffffbffffffafbfefbefffffefffbeefffffefbefeffffffffffbfffbfffffffffefffffffffbfffffbfeffffbfbfffeffbffeffffffeffffaffbffefffffeebfffffbefffffeefbffffffffffbfffafffffeffbfbfffbefefbafffefffffefffffefbffeffeffbffafffffffbaeffffbfffffffbfffbffffbbffeffeffffffffffffefbfffffeeffefffbfefbffffbffffeffffffbbfffffefbfffffffffffffffffffffaefffbffffffffbfffffbfffbefbfffffffbeefbffeffaffffffffffffffffbfefeebeeffffffbbffffffffeffffbfeffebbefbffaeffefffbfffbffeebbffeefffffffffffffefbbffeffbfbfebffffeffffefbbefefffffffffebffbffffffefbeffffffffbffffffffbffffbfffffbbffffbeefeffffffebbfbfebefffffbeffefefbbefffbfffbfffffaefefbbfbfffefffeffffffffefffffffeffaffffbffbefffffffbbfbeffaffbffffbfffeffffffffefbfefffffefbfbffbfefffbfffffbbeffffefbbfffffffffffffffffffbbffbfbffbfefbffaefffbffffefefbfffbefffbefffffffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask550597 : MertensSieve.bits 550597 = 0xbeffeffeffffffbfeffffbffffbffffeffffbffeffffbffbffbbffffbffffebeefefffffafbffbeeffeffffffbbefeffeffffffffffffffbfffffbffbfffebfffffffebfeffffbffefbeffffbffbfffeffbfffefeeffffbfbfffbffefffffeffeffbffffbefffffffffffffbfffffbbfbffffffaeffffffbffffffaffeffbfffebffbaffaffefffffefffffbfbfffffbefffffbffffbfffefbfffbffeeffebffffffefbffffeffefbffffbffffffffffefafffffffbfefeffefbffffefeefeffffffffffffffeefffffffffbeffffffffffffffefbfffeffafffefefbeeffffbffbefffbfefffbbfbfffffffffbfbfffbebfefeffffbafbffbeefeffefbfeffefffbbffeffeebbfbffffffbffbffbffeebeffffbbefffbffffeffffbeffffffbbeffffbfffefffffffffbbfffffefffffbfbffbbefefffffeffbebbefeffbffeffbfbffffffeeffffbffffffffbffffbfefffffebfffbfbeffbefffbfffffffffbffeffeffbffffffffffffffbffeefffffebbfffffffffffffbeffffbbfffffffbfefbfbefbfefffffeffffffffffeefffffffeffffffffafffffffbbfffffefffffbfffebffffffbfbffffeffeffefffffffbefefbfeffffeebffffffeffeffffffffffbfffffbfffffbfeffefbfbeeffffeffaffeffffffffffffefeffbfbfffffbbfffffbebbffffffffefbaeffeffffbefaffbffbfbefbfffbffffbbfbffffefefbffffebefbfffbffefffffeefffffffffbbfffffbffffffffbffefbfffbffaffffffffbefffffffbffffffefffbbefffffefbfffffeefffffebfffeffbfbbffffffefefbeffffffebfeffffffbfffffffefbfbffbfeffffaffffffeffebfffeefffffefbfffeffeffffffbffffeffffeffaffbffefbfffffbbffbefffbfffefbfffbffffbeffafbfeffeffefbffeffeefbfffffeffbfbeffbfbefffefbfffffffffefbffbfffffffffefffffffafffffeeffffeffffbbffeffeffbfffeffebfffbffffbaeffffefbfefbfbefffffefffffbfbffbffffffffffffeefffbffbbfffffbffbefeffeffefffebbffffffefaffffbffffebbfffffeffffbfefffffffffbffffefaffffffeffffffbbffbfffebfefeeffffffffffffffffaeffffbfffffeffefffffefffeffffbffbfbbfffebffffefffffefffbfffffffffeffbffefbbffafffffffbefbfffaffffbfeffffeffffbbfbfffefbfefafffffffffffeffefbffffffeefeffffffefbffeffbffafbeeffffeeffffbffbebffffffffffffeffbeffeffefefbbffffbfffbffefbffffeffffbffffbfffbffffbeffffbfffbfbfffeffbffefffeffeffffffffebffbffbfeffffbffffffffbffefffefbfbefffffefbbffffbffbfefffbeeffffeefeffbffaffffffefbfffffffffebfffaffbfffebfeffeffffffbefffffeffeefffbffbffbfffaefbffefbfeffebff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask558789 : MertensSieve.bits 558789 = 0xefbfbfffbfbffffffbfffffffbffffefbfffeffefffffffbfffffbfbffffefffbaffbefeffeeffffbefffbefffeffffffffffffbbefafbafffeffffffffffffffffeffaefaffeeffffefbfffffffffbfffffbffbffffffffefffffffffebbffeffeffffbbeffeffeffffbfffffbeffeffeffffeffbfffffbffbffeffffbeffffffffefffebfebfffafffffbfffeffffffffeffffefbfffaffffffffffbbfffffffffffffbeffbffefffffeffbefefbffbbfbeefffffffafbbfffefbffefbffbfeffebfffffffebbebfffeffffbeefffbfffbffefbfeffebffbeefffffffbfffefbefbfbffffffffbfffafffffffffeffefeffbfffffefffefefbbefffbffffefffbaffffbfffeffbffffffffffbffffffeefffbfffefffffffffffeefafffffbfbbffeffbfffffeffbffeffffffffffffffeffbfffffefbfffffbbefeffeffffbfebeffbfffebbfbefffffffbfefbebffffffaffefbfffeebffffffefbfffeffbffefffefbfffffbefeffffffebfefefffffeefffbffbfffbfffffbffeefffffffeffbeffeffffbffefbfefeefffffffefffffffbbffffbffffffffffffffbeffffffffbfffffbefbfffffeffbfbfffffffffaffefffffbfffebffffffaebfefffffeffffafbfffffbfffffffffbfffffbffefffffffbffffefffbffffffeeffffbffaefffbfffeeffffffbbebfffeffaffeffbfbefbbffefbffbffffefeeffffffbffffffeffbfffefffffefeffffbbefffbfffeffbfbbebfffeefbffbfffebfefefbfffaffafffffffffeffffafffefefffeffffbffffbffbeefefbbffffffffeefaffeeffffefbeefbfbfebffbffffffbffffffefeffeffefffffbfffeffffffbffbfffffffffffbffffebffbfefffbfeffefffbbffbfbeffbffffffffffffffffbfeffffeffeffbffffbeffffffeffffeffbffffffffbffffffffffffffbfbfffffffffbebffffefeffffffffffffffefffffbffffbfeffffeffeefbfbffbbffffffefbffffffeffffffbffffefffffffbfbfefeffeffffffffffffefaefbfbbfffebefbffffffbfffffffffefeffffffebfefffffffeebbffeefbfffffeffbfffffbefffbffbbefefffeffffbfffeffefbffefffeffebfffeeffffeffffffffeffbfbffbffffffaffaffafbffbffbfeffffffbfffefffffffffeffefffffefbffaeffefffffffefbaefbefefbfffbffbebffbfeffefffbeefbffeefaffffffffbfbfefbeffffffbfffefbffffffbfffffefbeffffbeffffbfefeffbfffefbfbfffeefffffffbfbffffffefbfffbfbefbfffeffbebfffffffefbfbefbfeffebeffefbfebffffffbffeffbfbffffffefffffeffffffebfefffbfffffbefffeffffeffffbfffbffbffaebfeffffbeffffefffffeffbfffffbeffefffbfffafffffffffffeeffffbeffffffbfefbfffeffffeffeffefbfffffffebfffffffeb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask566981 : MertensSieve.bits 566981 = 0xffffefffefafbbfffffffbfefffbfeffffefbfffefffffffffebbffeffbeffffefbfffffffffffbfffffffffeeffebfefffffffffffefefbbffbfbbffbffffbfefffbffbbebffffeffffffffffffbbffefffffbefeeffefffffffffbeefbffffffeffffefbbffffffffffffebfefefbbfffeffffffffffbfffeffffaffefbafffffffbfffeffbfffeffffeffbfffebffffffbfffffeefbffeffeffeffffffebffbbffbfbffbbfffeffefeffffbbfffffaeffffaffffbffffffbffbeffffffbfeffffffffffffffffaffefffffffbbffaffeefbebefffefbffeffffffeffffffbbfbffffffaffeffeffffbfeffefffbfefbfffffffffffeffffbfffaffffbfffffbfebefffffffffffffbfffbfffffbffefffffefbffffebefbfffefbffffebffbfffffbfefbefefbeffbffeffffffefffffffffbbfbffbbfffffaebffbeeffffeffaffbefefbfffeffffffebffffefbffbfbfeffeffefffbaffffbffbffffffefffffeefaffbfbffffeffeffffbffbeffffffbfffffbafffefffffefffffffbffefbfffefbbebfefffbbfffffffffffeefffffffbefffffffbfffffeebbefefbefffffffbfebfefbeffffbfbfeffffeefeffbffffbefffefffffefffffffaffefbbffffffffeffbffffffffffffefbfffeffffefffffeffafffeffefffffffbfbfeffffbfffffbffbefffffffafbffbfebffffffffbeffbffefffffbffbefffffeffffeffefbffbfffeffbfffffbebfeffeffffbfffefffbefffffbebfebffbefffffffffefffffffffbeefffbffffefffbefbbfbfefbefffffeffefffbfffefffefbfbfebfffaffafbbffffbafffffffffebefbbffaffbefffbffffffeffffffffffffffffffeffffeffeeffffffbfefeffefffffbfbfffeebfffbfbafbffffebaffefffeffeffffbfffffeffffbffbfffffbeefbfffefeffbfbbfbffbeeffefffffebffbffbfffaffeebffffffbffbfbbffffffffbefefbbfffebefffffffffeffffffbfeffffbfffefffbfffbfbafffffffffffefffffffffffaffffffffffffebbffafbefffffeefeefeffffffebfffeeffffefbffffffaefbffeefbfffffeffbfbbfbbfbfffbfffffffffefefbbffbffefffffefffffbfbfffbffffbbfffffffbffffffbffeffbfbffbfeffefffbfffbfbfefffffffeffffffefeffffbffffffeffeffbfffeffebeffffffffffbbffffbbffefffffffffffbffeffbefffffffeefbfffffbefeebfefbfbfebfffefffffeffefbffffeffffefffefbfbffffefbffbfffeffebbefffffffffbfffaefbfbefffeffeffffbfffefffbffbeffbffeffffbffffffefffefbebeeffffbfffffbefffffffeffffffffeebffffffbefbffffbfffaffbfffffffbeffefbeffbffffffffffbbfffffffffefffbefffffffffffefffffbebffffffffbffffefffbeefffffffbfbefffffbfffebffbffbf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask575173 : MertensSieve.bits 575173 = 0xfffbffaffffffffeffbffbefbfffeffefefffefbfffefeffafffefbfbffbfffffffffbfffefffffffffbfebefbfffffbfebfeffeffefbfffffffbffbffffffbebffffffeffefffeffefefbafffffefbbebffffffaffeffffffefbffffbffffefffbfffffbffbfefffffffaffbffffffeffefbfffefbfbfeffffbffffbffffffffffffaffffbfffffffffffbbffffbaffefbffffefefbeeffffaffffbffffffffbfffbffffffefbffeebffffffaffffffefbeffffeffeffffbfffeefbefffbffffeffeffefffffefbffeffbffaffffffebffbbffffbeffffbffffeffffafffffefffefafffffbefffffffbfffefffbffbbffeffffbbffefffefefffebfefeffbffbfbfefffffffafffffaffbfffffeefffbeebffffefbeffffffffebfeffffafffffbeffefffffffefffeffefffffffbffbfbeffeffaffffbffbfffbefffffefbffefbfffffbaffbffefffefbfffebbffeffbfffffbebbffffbffffffefffefeeffffefffeffffffbfefbffffffffffffefeffffffebeffeefffbbfbffffffaffbfffffffbffffffbffbeffefffbbffefbffffffefffffffffeffebffffffffffebffffffeffffbfefbeffebfffffffffbffeffaefeffffbffffeffffefffffffbeffbeffffefffefefbeffffffeffffeffaefefffebfffffbbffafbffffebeefeefffbafffffefffffbfffefbfffebffffffbfffffefffffbffffbfffffbaefffbbfbffbfffffffffaffffbffffffffffefffbefbfffffbbfffffefffffffbefbffbffffffbffaffffffffbeffffffffeffffeefffbbffbebfffbffeffaffffffffeffeffbfffefeebffffffbffbfffffeffefbeffbefeffbfffffeefffffefbefefbeffbffeffefffffbffbebffffffbfbfeffffffbfefaffafffffffbfffbffffffffeefbffbfbfffbffffffffbffefffffefffefffbfffbeffefefffffffffebffffeffffafbffbfefeeffffbefbfffeffffbffeffbfbfffefffffefbffbfffefffffffffffffbffffffaffbffeffeffefffefffbffbfefafbeefffffffbffbfbeeffffffbffffffaffbfffffbffafffebbffffbffffffbfbffbfefffffffbfffffefffefefffebbfffffbffbffefffeffebbffffbfefffffebffffffeffbfffefbffffffffffbfefaffffffffffffffffffffffbbfffeffefefbbfbbeffffaffefbefbffbfebfeffffeefffffffeefffffebffbeefbffefffeffffeefefffffbfbbefffffffbffaffffffffefffffbefffbefbffffffffffffffbaefbfbfefffbffbeffbffffbffbfffeffefffffffffefeffaffbeffefffbfffffbafffeffffaffffbfeffffffbbefeffefffefffffffbffefffffefbfffffbefbffbeeffefeffffbbfffffbffbfffebfebefffefbffffffffeffbffeffbefffffffeffaffefffefffffffaffbfffffffffefffbfffffffffeefafbffbffbeffbfffffee := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask583365 : MertensSieve.bits 583365 = 0xefffffffbffeffbffffffeffefffbffbfefffbbffbffeffffffffefffffafffeffebfffbffbfffffefffffffffeffeffffafffffefbbffefffffaffbffbefefffffffbffffffffbbffffbbffffffefafffffbfffffffbffffffbefffbeeffeffffffbfffeffefffffaeffffffffffeffaffbefffbfffeffbeffffefbfffffbefffffffffffeffffffffffffefbfffffbfbfefbefffbefffffffbaffefffffffbfebbffbfbffffffffbefffffffbfffeffeefafbbffffbffffefbffffffefefbefffffeeffffffffffffffeffeffffbfffffeeffebffbfffeffffbbffeffbffffbbebfffffffefbffffffefffffffffbbffffffebeffbfbbfffffffffffafffffbffeffeffbfffebffbffffffefffffbffffffefeffffbbffffffefafffefffffffaffbffbefbfffebeffffbbffffbfffbffafffffffffffbffefffffbeffffffffffefffffeebeeffffffbfffeffeefbfffffffbffbfffbfffffffbefbfffffbeefffffffbffffbfefbfffebeffbffbfffffffffffafffffffffefeefefbfeffeffffbfffffeefffffffbefefbffffebffbffffffffbfffefffeffffefffebfefffffffbfbfffeebfffbffffbfefefffefffbbeffeffffbeffffbfbffbfebfffaffbffbffefbffffffefbbfffffbffefffefbffefffffefffebfffeebfefbffffbfffefbfefeffbfffffeffaefffbbffffbfffbffaffbefbfbefffefffffefbfbfffeefeffeeffffffbeffbffffffefffffffffbeffbeffebbffffffffffbfffeffeffbefffffefbefbfbeffbefffbfffffbeebfffeffeeffffffffebeffeffbffbeffebfefbeffffffbffffefeeffffbebfefefbfffeffffffeffffbffbfffefffbffbfffffffebbfffefaffeffefbbfffffafffffffffebefffffbfbafffffeeffffffbfffbffffbaffefffffffbfefeffbffeeffffffffefffffefffffeffffffffefbfbfefaffbfffffbffefbfefbffeffffffeffefeffffffffeffffffffaebffbfefaefffbeefbebfffffffffbfbffbffffefefbeefbefffffffbffefbfffeffbfffffbfffefefbeefeffffbbffffffefffbfeffffffbeffffbefffffefffffbfbfffbfffffeeffffeefffffefbffaffffbfffffffeffffbffffffffbffeffffbffbefbffffffeebfeffefaefbfbbffffbeffeffbfbffbffffffbefbffeffffbeefbffefffffffffeffffaffeffbffffffefffbbefbfbefffefffbbfffffffbeffefbbefbfffffeeffffffbffffeffffffffebfffffbfffeffefbffbefbfeffffaffbffffffffffbffffebfffeffefffffffffffbffffbfffbffeffeffffffffffbfffeffffbeeffffefbfffbffefbfeffefffffffeffffffefbfffffbeffebeffefffffffffeffefbefefffeffffefbffffffefffffeeffefbffffbfebeffbfffffeffffffffbefffbbfbfefeffeffeffbffbfffffeefefbefbfffffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask591557 : MertensSieve.bits 591557 = 0xfefffffbeffebeffeffffbeffffffefbffbfbefbffffffeffbffeffffbefffffbffafffffffffffeffbefbfbffbbffbffbeffeffffeffefbffffefefffffbfbffbfffefffffbffffffffeebbfffffefffffffbfffefffffffffffaffefbbffbefefbbffffffebffffffbffbfbeffbffeffefffffeffffbfefbefffffffffffebeffbffffbbeffeffefafbffffffeffffffffffbffffffeeffffffffeffebfffffbeffbfbffbefffffbffbfbfefbffffffeffffffbbfffffffffefffffffeffbfffffeebfffffbbfbfefffbbfffffbefffbffffefaffffffffffbfefffffffbffffffffefbffffebfeffffeffbeffffefbbffffbffffeffebeeffffffffffffffefeffaebffbfffbefffffefffbeefeeffffbfbffbfffafffffefffffefffffbffeefffbfebbffbfbfffbefeeffffffffffbefffffffafbfefffbfffeffefffffffffefffffffeebbffffffffffffefffbeeffffbffffffffffbbefffbffffefeebfeffffbffffbfffaefbffbfbfeffffbffeffbffbfffefeefffffffbffefffffafbfeffffeffbffbffbefbfbeefffffffefffffffbbffeffffffefffffffffbbffffbffffffefbffffefffffefffffebffbeffeefbfbffbbfffefffffffbffffbffbbfffffafffffeffaffeffbefbffffbeffeffffffefffbaefafbbffbfffffffffffeefffffffbfffffeffbeffffffffffffffefefffefafbfffbffffffffffffffbffeffffffffafbffffebfffffbbefffffffeffffffebfffffffffbffffffebeffbffbffbefffbeffbffbffefbbefefbfffefffffbeffffafffffafffebfefbeffffeefbefeeffefffbaffffffffbffeffefffebefffffaffefbffbfefffffffeffffffebaffffffeffffefffffaffbfffeffeffeffffbffbffeffeeffffefffffffffefafbffbfffeffaffbffbffffffebfefefffffbeffffaeffffbffbfbffffffefffebffbffbaffbffffffefffbfffbfbfefffbfffaefbffeffffbffbbffbffffffffffbfefffbffffffefbfefeffffbfffefffffffbbffffffefbffbffbfffffffffffffbeffbfffffffffffffbbfffefffffffffbbefeebfffffbeffbffeffffffffbfbffbefbeefbffbefffffebfffefffffbebffbeffffffefffffffafffffeebfffeffeffbfffebbffeebfffffbbfbffffefafffffbfbffffffaffbffbfbfeffeffffffbfefbffefbffffffbfbffbfffbeffffeeffefeefbfffffffffffefffffffbbffbefffbbffffffeffeffffaffefbbfffeffefeefeffefffefffbfffbffeffbfffefbffefbfebffffeffffffffebbfffebfefbfbefffeffebbffeffffffefffffefffbaffffbfffffffffeffffbeefefffffbffbffeffeefefffffbfbffffffffffefffbffffeffffffffefefbeffffbfffbefffbffffffffbffbffffefafbbffffffeffffbfffefffbeeffffffbffbfebfffefffffb := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask599749 : MertensSieve.bits 599749 = 0xbebfeffeffffefbffffeffffbefffbbeffffffffffeffffffefffbaffffbefffeffebfffffffffbfbffffffffbfefffffeffffbffefffffefffffbfffffffffffaefffffffffffffbefeffafbffbfebafffffffffefeefffffffbefffbfffeffffbeebbfffebfffeffeebfefffbbffefbefffffffbaeffffffbbebfffbfffffbefffbffffffffbeffbfbeeffffbffffbfffffffefffbeebfefffffffffffefffbeefbffffffffbfffebeffeffbffffbffbeffffbeeffffffffffefbfeffffefffffffbbffffffffeffffbfebfebfffffffffffbbeffffbfffffffffefeffffffffffbfefefffffbfbaffffbfefeefaffefffffefbfefffffefbffeffeffefffefbfbefbeffeffeffffffeffffeffbffffffffffffffbffbffffbffffffffffebfeffefefbaeffffefffffbfbfebffffefbeffffefbffffffbffffffebfefefffffefffffbffeefbffefffffffffffeefeffaeffefffffffbffeefbffffbfffffbeeffffffffffaffffbffbfffaffeffefffffefffefeffbfbfffffbfffffbfffbebffffefefbbfbfefffbefffffbeffffeebfffbffaffffffffeffafffffffbeefbffeffbffffbffbfffeffeffffffffeeffffffffefefbfffbffeffffbfefeffefbbffffbeeffffbffeffffbfefbefffbfffffffeffffbfffffffffffffffffffffffeefbeffffffbfffefbeffefffffffffebfefbfbaefbebeffefffffbebbffeffeefffffebfeffefeffeffbfbffbffffffeffbffbfffffeffffbfefbffffffffefbeeffeffefaffffbfffbffffbfefffbffbffffffeffafffffffffefffffffbfbffffffbfffffefffffffbfefefbffbfffefffffefffebffffffaffbffefffffffbfffffbfebffbfffbefbffffbbfffeffffeffffbbffefbffffffbfbfeffffefffffbefffbeffbffeffeebffffebfefffffffbfbffbeffffbeeffffffffffbfbffffefeffeffeffafffefefffffbffffbfeffffbeffffffbfefeffeefaffeffffbfebfefffffefbeffffeeffffbfffffeffaeffffffbffbefbafffffeffbfbeefffffffffffeffefeffefbfffffffffbefefbfefffffeffffbfbbefbefffffffbfbbfbbffffffeffffeffbfffeffffbffffbfffffbfffafffffffffffaffffffffbffffbffffffefbffbfffbffbffeffffbffffeffffbefffbeeffefbfbfffbfbffbeffbffbffbefeebfffffffffbffffbfffffffefffbffbeffffbafbfefffffffffbbeffebfebfffbffffffffeefaeffffefffefefbbfffffffbfffffffffbfffffbfffffaefefffefffbfffeffbfbffffefffffefeffeffffffeffefffffffbfffefbffafffeffefffbafffffffbbebffffeffffafbbffeefbffefffffbebeffeefffbfffffffebfffffffffffffefeffbfffebfffeffbfffffffbffbeffbfffffbfffebefbffffffbfbffffeffefffbffbffffffbffffbbffffbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask607941 : MertensSieve.bits 607941 = 0xeffefbfbfffffbeeffffbfffffbfffffbeffffffbffffefefffffbffbffffbbffeffffffffeebefffffbeffffefbeffafbbfbfeffefffffffafffefffffffffbeffbfbffffeffffeffffbfffeffeffeebffbefffffeffefbbffeffaffeffbffbfffffaefffffefffbfeffffeffbeffffeeffffffffffbfffffeffbffefffffffbaffffffffbffefbfffbffbffffffffaffffbffffffffbfefefffeffeffffbffafbfffbffffffffffffefffbeefaffeffefffefefbbffbffaffffbeffbefafffffffffefaffffbffbbfffffbffffbefffffffffeffffeeffffffbfeffffffffffeffefffffeebffbffbfffffffffffbffffffffbaffbffefbbffefffeffefefffffbfbffbfeffffffffffbeffeffebfefffffffffffffbffefbffffeffefeffeffeefbffffffffffbbffbefeffffffffbfffffefbeffbffeefffffebfeffffeefffbfeffffffbfffbfbefffffafbffbbebffbefffffffffefffbbeffffefffffffffefeffbffbffefbbffaffbefffbfefeefefbfeffeffffffffffaffffffffeffeffffffffeebffffffefbbffffbfffefbfffffffeffefefffefbeffffbefaffefbffffffbffbffeffbfbeffffffffbfbffffefbefffffebffffefbffffffeffffffffffbffefffeffffffffffbfffffffbeffffbeebffffefeffbffaffbefffffffffbbffffffefbefffffeffefeeffffeffeeffffeebfffffbffbbeffefaefffbffbffbefffefeffeebffbffbeffffbfffbfbeffffffffaefbfffffaffbffffffffefffffefffffbffefffffbffefffeffffeffffbfffbfffffeefafbffbfffffffefffbfffbfbeefefffffbfbfffeefffffffffffffeffbfffffeefffbfffbeffffffffffefbfffeffffffffffbfefbfffebfeffffeffaffefffffefbfffbfffefffffeffefffffeffebefffffbffaffbfffebbefefbefffefffbaffffbffffebeffeffffbbfffefffbeffbffbefffbffffffffbbffbfbeffaffffbffffefffffffeffeffbfbfeffefeffffbffffffffffffbfbbfffffeffeffbfbffffffbffeffaffffbefbfffffbeffffffffbfffffffffeffffbfffffffbfffffffefaffbfffffffffffefbfebbffffbfeffffbffffffffeffefbffffebffffefbfbfffffffefeffffbfefffffffefffffaefbebeeffffbffffffefefbfefefbfffbfffffeffffbefffefffbbefbffbeffebffffefffffefbfffefbefefffeffefefbeffeffbffffbeffbffefbffffffefbefffffbfbbffffbbffffffffffbfebfefffffefbefffffffffbaffbffeffbefbfbffbffbffffffefffffbfbfefbeffffffffefefffefeffbeffffefffffafffebfefffffffffffffbebffffefffbffbffbffffffafbffbfefeefbffaffaffbfbffffffffbafffffeefffffffffffffefbfffbffefffefffbfffafbeffffbfebffffffffffffeeffffbfffebfffffbeffbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask616133 : MertensSieve.bits 616133 = 0xfbebfffffffefbffbfbfefeeffffefbbfbffffffbffeffbefffbffffefefffffbfffebfefbfffffbfffefbefffbeffbffeefbffffffeffebfebfffbffbffffffffbfffffffbbfbfffbffefbaffffbfffaefafffeffefeffeeffffffbffffffbfffffefbfeffffffffffefffffffffefbfbefffefefbbffffffebfefffbeffffbbfbfebfefafffffffffeffefffffffffbfffffffffffffffbffffffffbffafffeffffbefefbeffbffffbfefffbfffbfffffeffeffbfffeffeffffffffeffffeffeeffffffbffffefbffefffffffffefbfffffafffebefbbfffffefbfeffebfffeffbeffffeffaefffffffffffffbfffffafffffffbfffbffeebfffeffefffffeffffffebaffffffffffffebfeffffafbfffeefbffefbffbfffefbfffafbfffffbfeffefffbfffffffffeefffbfeffffeffbffaffffffffeffefffffbffffbfeffefeffbfffeffffaeffffbfbffffffeffaffafbffffffbfffffffffefffbefffffffffffeffeffbfbffbbfbffffffeffffbffbefbbeffffefffeffefffffffbfffebffbbeffffffffffffffffffbbeffffefffefffbfffffbfffbffaffeefbfbfffefffffeffbffeeffffafffffbfffeffffeffffbbefeffffffffeebffbfffbffbffefffffeeffffbfbeffbfbfffbffffbfffffbfebeffeffffbffbffbfffbfffffbeffffeefefffeffefeffbefffbbfbffffeffefbfbeffffffffeffbffaefbfffffeefffbffbfebfffffffffefbffbfffffffffffbfffeeffffffbbffbebffbffffffffffeffeffefffffffbfffefeffbffbebbffefffffbfbfeffebffffffbfffefbeffeffeffffffffefefbbffefbfeffeffffbeffffffbfffffffefbfffffffffffffffffefbfffeffbfffffffbfffeefbfffffaeffefefbfffffffffbfffebeffeffbffffbffffefbfffffffbffbeefffffefbfbfebfefbffbfbffffffeffefffefffffffbffeffaffbefeffbfffffbfffffffffffffffffffbffbbfffffbfbffffffbeffffbfffffeebeefbffbffbfffffeffefffffffffffbfffffafffefefbffffffefffeffebfefefbffbfefffbfffaffeefffffebffffffbfffffeffefffffffbffbffffffffbffffffeefeffafffffffffffbffbfbbfbfffffffefffffffbfbefffefffbfffffbfefeffbffeffbebffffffbfbaffbfbeefeeffffefbbffffffffffffffbfbfffffffffefbfeffefffffffbebbffefbfffeffffbfefffbfffefbbfffebefbfffbfffeffffeeffefeffeebfffffffffaffffffefefbfffaffbffbffffbfeffffbebffbffbfffbffafbffffffeffbfbfefffffeffeffffefbffffefaffefffffffbeebbffeffefffeffefbefffbffffffeeffffffbbfffffffffefeffbfffffffbfefefbbefbeffefeffffbbffffbefffffafffebbffffbeffffffffbefefbfffeffefffeffffbffefbbfbbfffffeffaffeeffebf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask624325 : MertensSieve.bits 624325 = 0xfffaefffbfefffbffbffffffffffffeefeffbfbfebbfffebafffffafffffefbfefbffffbbeffeffffeffffffffefbeffffbefffeffebaffffffeffeffeffffffffebbfbfffffffffefbbffeffaffefffffbebefbbfffffaffffffeffffffffebffbeffbefbffffffebffbfffffbfffffbefffefffbeefffbfeffefafffefbffffbbffaffaefffffeffffeffbfbbfffffeeffffbfffffffbfffbfffebffbfebfffefbffffffffbeffbffeebffbeffeffffffffffffffefffffbfffffeffbefffffffbfffffefffffbfbbebefffffbfbffffefffbbffffbeffffffffffffffeefffbeefeffeffeffffbffffffffffefbffeebbeffffbffffffefaffffffeffefefbfffbfffeffffffffffbffffffffeefffffffbffbfbfffeffffbfffbfffefffffffeeffeffebbffbfffffbffffbeffffffffbfffffbffefbeffffffebfefffbfffffbfebeffffbafbfffeffeefffbfffffbffbbfffffbefbffffbbefffbffbfeffebbffffffefffffffbefafffebffffebffffffefffffeeffffbfbfffbfffeffffeffefbfeffffaffbffffbfebffffffbffffffeffffbffefbfffffffffbfffffefbffffffbefffffefffffffefffffbffffffefbffafbeeffffeffffffffafffefeefffffffefffeffffefffffbfbfebffbafffffaefffffffeffeffbffbebefffffbffffffffffffffbfbffffefffbfffffffffffbefbfefffffffbffffbbfffffbfbffbeffbefffffffffbfffeffefffffbefffffffbffaefbffeefbffbfffffffbffbffffffeefffffffbefaffefffefefffffffffeffefefbbfffffbfbfeffffffffffbfffefffffffbffafbbffefffffefffeffeffeffffffffefbebfffbeffffafbfffeffffffffbffbefffffffbffffbfebffffffefffeffffffffffbfbafffffeeffffeffffffefefffffaffefbfffffbfeffffefbffffefbfffffbfbffbfffeffafbfebffbfffefffffefffffffbfffffbbefbfffefeefffffffbfffffefffffeefffffeffefffbffbfeffefeffffbfebfefefbbffffbfffffffebaefaffafffeffffffffffbefffbffffffeffeffffffffbfffffffffffeeffefffbfffbefeffbefffffffffffffeffbffbfffffffbeffaffeefffbffbffffffeeffffffffffffbffbfffefffffaffeffffbfeffffffbbffbffeeffffffbffbfefffffefbffbfbffffeffefffbfffffffffffffffaffffffffaefffbefbbeffeffffafffffffffffbffeffeffbfffefbeffffffbfffffffffeffeffffffebfffbfbfffffbffbfffffbbffbffefffefbfffefffbffbeffaffffffffeeffffafbfffbfffffbefffffeffffffbfefffbeeffeffffffffffeffffffffffffffbfbbfbfeffffefbefbbfffefbfffffefbbeffebfffffbfffbfffefbffffffffbebefffeffffffffebfffeefeffeffbfbfebfffbfbfffffbfffeffbffffffffffbfffaf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask632517 : MertensSieve.bits 632517 = 0xffffbbfffebbffeffffbfefefffffefbbfffffffffffafffffffbfffbefffbeffffffffeffbfffffffffefbffffffeffffffbbfffffbffbebfebfffafbbfffffefffffffbfebffbffbeffeffbffffffefeffefbbffbfbfebfefffbfffffbfefeeffffffbbfffffffffffeebffbeffffffffffffffffffeffffbfbffbeffaefeffafbfffffbfefbffffffebfeffefbfbfffbffefffefbfffebbffffffffbffbeffffffffffbffffbfefffffefeffffbbfbffffffefbaeffffffffffbffffffeffebfefbfbefffffffffffbfbffffffeefbfffffffbbfbefffefbffbfffffeffbffffffefffffffeeffffbffffbfffeffffffffbfffffffffffaffffbfeffffefbffffffeefeffffffffbefffbfffffffffbfffffeffefffffbfbefffefbfbffffffffffffbffbffbffffbfefffbfffffffefbffffffefffffffefffffafbfebffbfffffbeffffffffeffffbbfbbfffffbffffffffffffffffffffaefffffeffffffbfefffffffeffaffefffffffbaffbffffbffffebbefaffbfbffffeffefffffffbffffbaefffffefffffffbffaffbefffbfeffffbfbbffbfffffaffefffffffbfeffffeffaffbebfeffefbfbefbffffffbffeffffffebffffffbfbeffffbfefffffffeffffbefbfffffffffffffffaefffbfffbffefbfffbffafffffffffefffbffbffffefeefeffffffefeffaffeffbfbfebffffefffffeffffefffffbffbeffffffffffefbfefbebeffffffffbfffffeefffffffffffeffebbffffffffffbeffbffbffbeffefffbbefffbeffbefffffefbfffeffffffffffeffeefffffebfffffffebfebfffbffffbeffffffefaefeffbffffbfffbefefffebffbffbfffeffefffefeefefffffefffffffffefaffffbbfffefffffffbefffbffffefffbbfffffffbbffffffefbfbffbfffffbffbfeffefeffbfbfefffffebfffffbbebbfbefffefefffebbfbffbbffaffffffffffbbefffffffffffebffffffbfffffffbffffffefbffbfffeffffbfffffbfeffffffbaffbfffffaffbffffbfebeffefffffeffbffeffffffffaffbefffbfefefbfffbebffffffafbfffffffefbeffffeefbfffffeffbfbbfbffbeffbffbffffffeffffefffffefffffefbfffffbffbbffefbefffffbefbefffbeefffbffbffbffbeefeffafffefffffffffbefbffbfffefffffffbfffeffbffbfffffbefeffbefbfbfffffffffbeffffffffffeffbffffbaebfefffbfefbffbfffffffffffffffffbffeeffffefbfefffbfffbffaffbffffffffffffffeffbffeebaffefffffbffffbeffffbaffffbffffeffffeffbffffbfffbfbeefffffffeffeffeffbfffffeffbfffeffffffffffbffbffbffefffefffffeffefefbfefbffffffebfffbffbffefffefffffefbfbbfffffeffffffffeeffffffbbfffffeefffbfffbefefffffbfffebbffeffffbffffffeeffffffffef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask640709 : MertensSieve.bits 640709 = 0xffebfffbfbbfffefffffffffbfffffbfffbfffffffbffbfeffffeffefbfffeeffffaffaffbffffffffffbffffffffffffeffffffefffffffeffeeffffffffffbfbafbffffffaffbffefffffeefbffeffaffffbfeffefbffbfbfefefffffffffefffbffbeeffffbeffebffbeffeffbffbffffbfffffbfebfffffffefefffebffffffeffbffafffeffeffffefbffbfffefbaffffbbfffffefbfffffbbfbfefffbfefefffefbfbffffefbffffbbfffefbffeffefffffeffeffeffefffebffffffbfbafffefefbeffffbfefffffffaffffffffffbfefeffeffffffefffbfffbffeebffbfffeffeffeffbfbefffffbfffebfebffffeffffeffbffeeffefefbbefffbfffbefbfbfffffffffeffbffeffffffffeffffffffbfffeffffffbefbffbfefffffffeebffffefbefffbbfffffffffffffffeffffeffaffbfbeffffbfffffffffbffffffebeffbfffebbfbefffefffffffffbeefaffeffaffbffffffffffbbfffffefbffffffbffbffeffbfffffbefffffffeefffffffbefeeffeffffefbffbefffffffbfffbfffffbffbffaffbffeffbffbfbffffeffebeffeffffbffbfffaefbfffffffffebeffffbaeffefffbfffffbfebffbfeffefffbfffbffefbfffefffefffffffffffffefffffefffffffffffbfbffffffeffefbfffffffefbfbeffbfffefeefffbbebffbffffeffffffbfffeffbffaffbfffeffebbefffbeffffffffeefefbfffbffefbfffaffefffefffbfffafffefbfffeffeffffaefffffefbefeffffbffbefbfffaffffffffffbbffbffffbfeffffaefffbbeffefffbffffffefbffffffeeffffbffbfffffeefbfffefffbeffaffafbeffbeffefffffffeebbfffeffffeffffbffffefeefefffffbfbffffffefbbefffbfebfffffffffffffffefffffffbffffefbffffbeebfeffffeffaffbefffbffffffefbfffbffefbfffffbfffbffefffffefbeefffbfefeffffbffffffeeffffffffffffffffaffffffefffffffbffbffeefffbffbbffffffffffffefefffffbffbefeffeffbfbbfbfeffeffeffffeeffffefbfefbfffffbfbfffeefafffeffffefffffeffafbffbfefffffffaffffffffeffffbfeffffffffffffbfefffffffeffffbeffbffeebfefffffffbffffffefffffffbfbffbbffffffeffebffffffffffffffffffeffffffefbefeffbefbffaffffffffbefafffeffefeffffffffafbffffeffffffffebffffffeffeffbffffffefbffeffefbfefefbbffffbfefbebeffbffaffffffeffebfffffffeffeffffeffffffffffbeffbfffffffffebffffffaffffffebefffffbffbfbbffeffeeffffbebfffffbfffbffffffffffbfeffffbffbfbfffefffffbffbffeffbefffffffbfffffbffaffffffefeefbeffffefbfffffffffffffeffffefbbefefbfefffbffbeffbfffefffbefbfeffffffffffefffefbffffffefefbffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask648901 : MertensSieve.bits 648901 = 0xaffbfbfeffebfffeffefffffeeffeffffbfbffbfffbeffffffbffffffffffffbefffbfeffffbfbffbfffeefeefffffffbefffbaffbffefbfffffffffefbaffbfffffeffffffffbfbffffffffbbfbffbffffffefbfffbfffeffefbfffffbffeefaffbfbefbfffefbbfffffefffeffffffffffffbfffefbeffeffbeffffffffefffbfffffbfffbffffffffbfffffeffffbfffbffeefeffffbfffffbfebfffffffffbfffffffffffefffffffbbefffffefbffffffefafbeffffffffeefffbbfffebffbeffbffefbbfffeffffbfffefffbfffffffffbffbfbefffefbffefbffffffeffefbfefbeffffaffefbbfbffffffefffffeffffffffeffbfbfffbfffeffffffbeeffefeffaffbfffffbfffffbffbfbeffffffeffefffffefffbffbeefffbbfffebffbfffefbbffbfffffeeffffbfbfffffffffefbfebfefefbfffbfffeffebfebfffeffbfbffffffffffffbffbefefffeffffffbffffefbffffbfffbefeffffffffefffffeefaffeffffbbfffebaffefffffbffffbfffefffffbffefbfffefbbfbfefefffefefbffbfeffebfffffbbeffebfffffffffffbffbfffeefeffefffeffefbffffffebbffefbffffffbfbbeffffaefffffefffbfffafffffaffffbffbaffbfffeffefffffffbffffffffffffffffbeffffbfffeffbffffffefefbfffffbfffffffebbeffffffffffeffbfffffeebffffffbfffffefffffeffffffffafbffffeffefffbeebfefeefbfffffffbfffeeffefbffffbfffffbffffffbefbebefbbfffffbfffffffbfefbfffffbeffebeffbffeefbfbfefaffffffffbfbefffffffffebbfffeffefbffffffefeefeefffbbfbfebffffffbfbbfffeffffaefeffeffbfffeffffffffefffffffeefffffffbebfffbfffffbefffbffffeffffffbffffffbffffffeffeffffeefefbeeffebfffeffafbfefffffebfffffffebbffffffefefbfffbfffebefffffefffffffbffffffffffffffffefefbfffbefeffefffffaffffffffeeffffffffefffbfffbfbffffffeefeffbffefbbfbfffaffffffebfebfeffffffbbffbfffefbeffffffbbfffffbffeffafffffffbfffbfffeffffefbfefbffffffffeefaffbfffefbefeffffffffbfffebfffffffffffffefffffffeffffffffffbbffeffbfbfefffbbffefbeffffbffffffffbaffffffeffffffffeffefffbffffffbffbfffebfeffffffbfeffefeffffffffbffefffffefbbfffffffffffffffffbfbfffeffbffbfffffffffefbffffbfeffefffffffefffefffbfeffffafbbfffefbffefffeffebefbbefaffffbffbffffefeffeffffffffeefbfbbebffbeffffffffeefbfbfffeffeffffbbebffbbffaffefffffffbaffffbffffebfffefffffffffefffbfffbfbaeffeffffffffffeffffffffbfffffefbbeffffbffffffefbebeefbfffffbfffffffbeeffffffbfefefffefbffefbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask657093 : MertensSieve.bits 657093 = 0xfbffbfffbffbeffefefbefffffafffffeffeffbfbeebffffeffffefffebbfbfeffefbffefffffefbfffefffeffffffffffbffbffffffebbffffffffffbeeffefbffeffffbffffffbfffebbfbfebaffffffeffebeffbefefbbfbfeffeffefeffffbbffffffffbffbfffefffbeffffbffffebfeffeffffffbffbffffffefffebfffeffbfffffffbffbefffeffffffbfefeffaefeffbfbfffffbeffffbfffffbfeffefbfbaefbebffffefffffffbffeffeffeffeeffffffbafffffeffbfffffbfffffefffffeeffffffbffffebefffffbffffffebfebaffafbeffbebfeffefffffffffffffbfffffeffffffebffffffffbffbfeffffbffbfffeffffaffefbffffebffffffefbffbfffffbaffefffffbffffffeffffffbfffeeffefbfffffbebfffffffffeebbebffffeffffafffffffbfffffbbefffbffffefefffebffffffbfffffbeffffeefeffbffeffbfbffffeffffffbfffffbfffbffafbbffefffffbfbeffffffefbffffffffbefffffffeffeebffbffbbffefffffbefffbeffbffffbbfffffbfffffeffffffefafffffffbbfffffbffffbbffbfffefeffffbfefbfffffeffaffbfbffffeffefefbaefffffeffffffbffffffffffefeffffffeffffefffffeffffbeffbfffffffffefefbbfffffffffffefbefffffeefffffffaeffffbffffbfffeefffffeffffeffeffffbfffbefffffffffffffbfbefffefbffefffeffebbffffffffffbfffeefefbaebffffffeffefffffbfbfeffffffbfefffffefeffffbefffebefbfffffffebfffefffefaffbfbbfffeffefffffebbfbffffffffbffffebfffbfffffaffbebeeffffffbaffbfffefeffefbfeffffffffffefffffffffefbffbffaffbfffebfefefffffffbfffeefbffffbfefffbfeffffafffefffbfeffffefbffbfffbefffffebbefefbfffefffeffebfffbffffbffbbefffffeffffbfffefeffbffefbffbffbffffffffbffffebfffeffffbfeffffeeffffaffeefffbfefeffaffefbffffefbfffffbfbfefeffeefffffefbffefffefffbbfffffffffffbfffeffffefbfeffffbffffbffffffbffefbfefffffffeffeebffbffffeffffffffefffffefefbbffbfffffbffbffefbffbfefaffffbfffffbefbfefffbfebffffffeefbffeffbfffffbffffffebfffffffffffbffffeffffbffefbbeffffefbeffaffbefffffebfffffffffbffffbfefffffefbffefffefffbffbffbffbfffafffffbebfefbfffffafffefefbffffffbfbffbffbfffeffbefffbffbbefbfffffffbfeffefbfbfffffffffeffffbfefffbffbfffaffffbfffefffffffbffffefffbfffefffefffbffffffffbfffffbffbbfffffffffebeefffffffeffbfffefafffffeffffbfefbfffffaebfffeeffffbffbfbfffeffbffffbffffefffbfffffbfebffbfefeffeffefffffeffffffffeefbfffffffffffffbbefefffff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask665285 : MertensSieve.bits 665285 = 0xfeffafbbeffebfffbfbafbfefffffffeffbffbffefffefbfffebfffffbeffffbfffbebeffffffffeffffffefeefafffebfffeefbfffffbffffbffffffffbeffbffeefbefffffeffeffffbffafbffffffffbbefbfbbffbebffbfefffbfffffffffbffffffffbffeffaffeffffffffefbfeffffeffffffffefffffbeffffefffffffbbffffffffffffffaffffffefeffffbefbfffeefbffbffffbffffebbffefffeffeffebfffbfbefbbffffbbeffffbefffbfffaffeffbffffbfffeffafffffbebeffeefbfbfefbffffffffbffefbfffffffffbffafffffeffbffeffefffeffffefffffffbbffefffffefbffbfefffffeffffeefffbfffefffffefbbfffffbffbffefffeffffbffeffeefffbfffbffffbbffbfffefeefefffefffbfffeffeffffffebfffeffbfbffffffefbeffffbbffffbfeffefffbffbbfffffbffbffffbffbfffbeffffeffbffeeffffffbffbffffffeefffbfffffbfebfffbfffeffffeefffffffbffbfbefffefffbeffffbfffafffffefbbffeebfffbffeffbffffffffeffbffffbfffbffefbfeffeffffbeffffbfffeffeffefbfbefbffbefffefffffffbfbfefffffffafffffffffffaffafbffffffeffeffffbfffffbbefbfbfeffefffbfffefbaefbfbfffffffffffbbfffffbffffffeffffffbeffeffaefbebfeffeffffffbbffffffeffffffbfffffbffffffffffebfffbffbffeefffbeffeffbffafbffbffffffeffffbfeffebbffbfffffbeffffffffffffffefefbfffffffefbefefbfffaffeffffffeffffefbfffffbfeffffffbbffbfbfeffffffbfffffbeebfffbffffffefeffbffbffffffefffbeeffffbefffbffbfefbfffffffffffbefaffbfffebffbfffffbbebbffeefffffffffbffffffffffffeffbffffffffffffffbffffffffffbffffffefffffffbffffeffefafffffbffffbeffefffffffbfffeeffffeffffbbffeeffffeffbfbbfffffbffeffffffeffffbffffbfffbebffffefeffafffeffffeffefffeffefffbffffffafbbffefffefefbffbffffffffffffefffebeebfffbffbffbefffbfefffbffffefffbaefffffffffbffbaffbfffeffeffeffffffbfefffffffaffeffffbffffffeffbffffffeffebbffffbffbfeffffffffffffffebefffffefbbffffbffffefeffffffeffeffffbffeffffffefaffbffffffffeeffffaffeefbffffbfefffbffbbfffebbefffffffbfbfffffffffafffeffebfffbfffeffffffbefffffaebbfffffbfffffffffffefffffeffffffefffffefeffffffffeeffffffbffbbffefbfffffbbffffbfeffffaffbefbfffffeffbfbbeffffeffaffffffefbfffffafffffefffffffffefffbffffffeffaffefbfeffefffbfffffbbeffffffffeffffbfffffeeffefffbffbfffeefbefefffffbffffbafffffbfffffffbfffeffbfffffffbeffeffbfbfffffffffbfbbeff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask673477 : MertensSieve.bits 673477 = 0xfffffbfffbfbfefbfffeffffffbeffffbfffafffffeefbefffffffafffffbfbfebbfffffffbbeffffeeffffffbfffefffffbffaebffffefeffffffffffbffbfffbffeffbffefffffafffffbeffebefffffbfbfefeebfffbffbffffffeffeffffffffebeffeeffffffbffffefbffffbfffbfbfeffffffffffbfffffefffffefbfffeffbffbffeffbfffebffffffbfbffffebbffeffffffffeffaffbffefbfebffbfefffffefbefffbefffffaebffffffbffeffefffffeefbffeffefffebffffffefbfffbfffffaeffffbffffbffbfffffbbeffeffefeefbfffefffbfebfefbfbbffbfbfffbefefbfffbffeffeffffffebbefefffffeffbfbfeffefffffffbeffffffbbeffffffffefffffefbffafffefffbfffffbffbfffeffbefefbffffefeefaffffffefffbfeffeffffaffffffeffffefbbffbfffffbffaffeeffffffbbffbfffffbffffbfffbffaeffffffffffeffffbffbfefaffffffffbeffffbffbffbfffffeefbffefffffffbefbaefeffbfbfebffffffffffffffbeebeefbffffbbfbeffeefffbfeffefeffffffffbeffebfffbffbffefffefeebeffffbffbbfffffaffefffffffbfeffffffffefffffefeefbfbbfbffbfeffefffffefffffffafffffefffefffbfefffbfffffffffbfffffbefbffffbffffffffbfffffffefffffffbffefffffbfbbffbffffffeffffefffffffbafffffeffbfbffbfffffffffbfffffaffffbbebfffffffffffffebfebffbeffffbffffffffbfffbffefffffeffaffafffffffffffffffffbebbffeffffffffeffbffffbffffffbebbfffffeeffffefffeffefeffbfffefbebffbeffffbefbbfbfefbffbfbffffebffffffefffffbffffffffbfbffbbffefbeefffbfffffbfffeffefffffffffffeefefffeffffffffffffbffffffefffffefbffffffffbeffaffffbbffeffbffeffafffffffffefeffbffffbeffefffffafbfffffffffbfffffbfffeffffbfbbffffffefeefbfbefbffffebffffffaefffbffffffafbfffffffefeefffbbfffebffbbeffffefffefffffffbfbbfffffefffffffffffffffffbffeffefbbefeffeffeffbebfebffffffbffffffeffffbefefffffffbefbfffbffffffffffbefffffbefffbffffffbfbfebbfbfffefffffeffbfbeffaffbfffebfffeeffefffbbfbbffffffffeffffffffffbfeffffeeffeffeffffffbfffffbffbfefbffeebbffefffffeffffbbebfefeffbffafbfebeffbefefffffbffffffffffbfffffffffbffbffeefffffffeffffbffffeffeffffbffbfffffefffffbfbeffbfffffefffffbfffffeefbffeffbfbbffffffffefbfeffebffffffbfbeffffbfffbffbffafffffffffeffffffbffbfffeffbfbffffefffffffbffbfffffffffeffffefbfefefbeffefffffbffffffffffffffffffebfffefbaffffbeefffffffbefbffeeffffefffefffbffbff := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask681669 : MertensSieve.bits 681669 = 0xffbffffbbffffbbefeffbfbfefffffffffbfefffbeffffffffffffeffefeffffbaffbeffffeffbfffffffffeffffffffffbebfffeffbffffbfffeefbffeffefffeffffeefeffffbffbffbeeffffeefffbfffeffffffffbfffffeffbfffefbffeefeefbfbffffefeffefffffbffffbfeffefbffbfffffffbfffeffffbbefffffffffffefffbfffbefffbeffbefeeffeffffeffffbfefeeffffefbbefffffffbfffeffeffffbffbffffbfffffffefffffebbffeffbffbfbeefffbffffeffffbefffffeffeffffefffffeeffffffbefffefffbffffffbffbfbefffffbffeffbffefbbfffffffbbffeffbfffffefffeffeffffbfbefffefefffffffffffbfbfefbffefffffbfbefbfffeffefffefffbfffbfbbfffffffbeefffbffffffeffefffffbfbfeffffaeffffbfffefeffeefffbeebfffeffbefefbfffffbfffaffbffefbbfbfeffeffffffffffeffbffffffffffbfffaffbffbfbfeffebeffffbfeffeffffeffbfbaefbffeeffefafbfffbffffffffbffeebffbfffbffffbeffffffffeefefffeffefffffefafbffffffffbfffafffffffbffffffbfffefffffffbffbfffffffbeffbfffffbeffffeeffefffbefffffffffffffbbefffbeffeefffffefffffebfffffffffffffefeeffffeefffffefaffbffeffffbfebffffffefbfebfebfffafbffbbffeefbfffffbfffffffbfffffffffffbfefffffffbfffffeffefffffbefbfbeffbeffffeffffbfeffffeffefbfefeeffffbffffffffffbeeffffbebfffefffffbffbefffffebfefffffeffeffebefffffaffffbfffeeffffffbffffebfffbfffffffbffffefeffffffeffffbffefbbeffefeffbefbffbfbffbfffeffeffeeffeffeffffffbfffffffeffffeffefffeffeffffeffbebfffeebfefbffffbbffefffffffbffffffffbbeffffeffffbffbeffeffaffbffffbfffffffeffffeeffffbfbfefbfbffbffffffbefffffebfefeffffbfffeebfffefffffffbfffeeffffffbffffffbefffffffbebeeffffbffffffffefffeffffeffbfffffbfffffeffffbeffbffaffbffbffeffaefffbfebfebffbfffefbeffffbffbfefbffbeffebefbeffffffebfffffffffffbefbfffffbffffffffffffeffbffefbafbfefefbfefffffffbeffffeeffffefbfeffffbefffbbfffffefffefbffffbffffffeffffffffffbfefbffeffbfffffffbbffbfffffbeffffeffffbffffffffbfffbfbfefffffffeffffffffffffffffffffbfbffffeffefffbffbffbeefbfffffaffffbefffeffffefffffffbfeffffffffffffbfffbffbfbffffefbffbfbfffbfbffbeefbffffffffeffefffffeefbefffbbffaffeffffbffbfefeffbffbfffffbffffffebbefffffffffffffffbfefbffeffeffffffefeefffbafbffffefbffbfffefffbfffbfffffffffebeffbffefffffbefeffbfffffffbbfbffffffeffeef := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask689861 : MertensSieve.bits 689861 = 0xbffbfffeeffffbefffbefbfffbffefffffeeffefbffefffffffffffbffbfffffffbffffffafffffeebfffffbfebbefefffffffbeffffffffaffbfbbfffffefffffffbbebbfffffefffffeefbeffffbffeffaffbebefffffbfffffbfffffbfffffffbbebfffffffffefbfeffffefffffefffefefbeffbfffefbfbfefbffefffefffbeeffffaffffffefffffefefffffbffeebfffffffebfffefbbffafffefffffffbefffbefffebffffffbffbffffbefffffefbefbbffffffffefffffbffeffbefffbefbfefffffefffffefbffeffbfffffbeffebfefbffffbeefffffffeffbfbeefffbfffffffffffffefffffffefffffffbfebfffffbaffbefeffffffffbffffbffffffffffffffbffbfeffffbfffebefbfffffbbffffffefeffbffefbffffefbfffffbfffeffebfefffbbfffefffbeffffbbeffefefbeffffffffffffefbffbffeffbffffbefffffffbbfffeffefafffffbfffebbffeffeeffeffefbefffbbfffffffbffffffffbffffffeffbffefbffbfebeffeffbffbfffffeefffbaffbfbffffefbfffffffbfffefffffbebbffffffffafffffffffefaffffbfffbfffffeeffffffffffffffffafffefffbfeffefbffffbbfbfefeffffbfebfffffbaffbffefffffffbfffeffffbbefefbeefeffbefbfbeffffffffeebfebffffffffbfffbefeeffffffffffffffffbfffffffbbebfefefffffbefffbffffffefffffbeffffbffffffffffffffeefbffbfbffffebfffeffbefffbffffefffbbebbfffffeefafbefffebffffffeffbffbefffffffaffffffffeebbffffbfefbfffffffffffefbfeffefaefffffefffbefffefffbeffffffffbfffffeffffffffbffffffffffbfebfefeffeffbfffffbefeffbfffeffffeeffffbffffffffbffefbefffffeebfefffffefffffffbffbffffffefffffffeffbfbfefeffbffeffefbbfffeffffffbffbbeffffefffffffbfefffbfffffbafffefefffffffffffbfbeffeffbfbfefbebfebfffbfffefbffefbfffeffaffbefeeffffeffbfffefffffffbffffffeffebefffffeffffbfeffffbfbbfbfffffffefeffefbffbefffffeffffbfebffbbefbffefbffffffaefefffefffbffbfffffbbffffbfebaffeffeefbeffffeffbffefbfffffffffafbfeffffefffffbfffffffbfeffffffbffbfffefffffeffbfffeffffbffefbeefffffeffefefffffbfffffeffbfffffffbeefaffffffebbfffefeffafffffffbfffbffbffeffffffffeeffffffffffefffffeffbffffffebfffaffffffebffffefffffefbffffffeffffffffebffffffefffeffefffffffeffffbbfffefbffffffeffefefffffafffebfffffbfffeffbefbfbffbfeffffeffbfffffeffffbffffffeffeffaffbfffffefffffffffffbfffffbffffbbffbfbfffbffefffefffbffffeffffffffffffbeffffbafbffffefeefffbfebffbeebf := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem mask698053 : MertensSieve.bits 698053 = 0xfffefffefbefeffbfffffafbfefefffefeffbfffffffbfffaffbefffbfefaffefffefbfffeffeffffbffffbfffbffbfbffffefeebeffffffffbebfefbffbffefffffefffffefffffffffffbffbfffefffffffffffffbfffffeffefffffbebffffffefffffeffbeffefbffefffffffffffffffffeffbffefffefeffbffbffffffffeffefbfeffebafffffeffbfbefffeffffbeffffeffbffbffeebffbeefbffffffffbffeefffffffefffffffbaefeffbefffbffbeefffbafbfefffbfffbffbeffffffbeffffbeffbffffffefffbfeffebfebfffafffffbefffbffffffefffefeebefffffbffffbeffffffffeffffffffeffefbbffbebfeffffbfbfefffbefffffefbefffefeffeffbffefbfefffbfffeffbffffffebbefefbffbfefffffefefbffffffffbbefffbfeffeffeffeffffbffffffeffffffbfeffffeffeffaffbfbffbeffbefffbffbffffffffffffffffebffffefbfffffffbfeffffbfbbffbefffffffbfffefffbffffefeffffbbeffefefffffeffbfffefbffafbefbfffefffffeffffffebffbaeffffffffeffffffffffbeffffefffffbfbffffffffffefffffeffffefbeffefffebbffffbfefefbfffbffefffffffbfebfefffbeffffbbfbfffffffffffbfefbfbfebffffffefbffbfefbefbfbeffffffeffffbffbebfffefbfffbffbfffffeebeefefbfebffffffaffeffeffffbffffffbfbbefffbeffffffffafbbffeffefffffeffbfffffffffffefbbffffffffefbefbfffffffffffbffffeffffbfffffeffffbffffffbfbffffeffffeffbffbfbffbfffeffafffefffffebeffafffeffebffffffeffffbbfffebfefeffbeffffefbbfffffaeffebfffbeffffafffeffefffffffbfbffbffffefffffffbebfefffffffaffffbffbffffffeffffffeffffffffffbffeffbffafffefffffffbffeffeefffbffbfefffbefbffffeffefbffffbfeffefefffffbfbfffffffefffbffffefefffffffbbefbffffffefbffeebfefffffefffbfffffbffffffbffbfffffeefbffffffebbffffbafffffbfbffbffbbfffffaffffffffeefefbffbfebffffffbfffffffffebfffefbbffbebffbfefffffffbfffffeffffffffbefefbbffbffffffffffffffffbfffffffffbefffffebfffffbeefffffefffbfeffefffffffffffefeffbffeffffffffeffbffefffebfebeffbfffefffffefbffefbeffbfffffeffffbbefbfffffbffffbbffffbfebfffbfffeffeffffeefbffefbbfffeffefbfffefffbefffffeffeefffbefffefffffffbeffffbefffffffffbfffbffffbbfbfffffffffefffffbeffffffffffbeffffffffffefbfeffefffffffefffeffeffffffffffffbfffffbfefffbbfbbefffbfffbfbffbfffffbfeffffaeffffefbfffbffbffffbfeffffbffeefbffeffaffaffbfffffffffffffbffbffffffffffffffbffffffbefffffe := by rfl
end MertensMasks

namespace MertensCertificate
open MertensFold
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b0 : B 0 1733 315684388066545112 61977157 := segment 0 1733 315684388066545112 61977157 (Or.inl rfl) (by decide) (by decide) (by decide +kernel)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b1733 : B 1733 9925 29125636570929 8028090 := block_of_mask 1733 8192 29125636570929 8028090 _ (by decide) (by decide) (by decide) MertensMasks.mask1733 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b9925 : B 9925 18117 2372414246126 31823 := block_of_mask 9925 8192 2372414246126 31823 _ (by decide) (by decide) (by decide) MertensMasks.mask9925 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b18117 : B 18117 26309 857955451968 5840 := block_of_mask 18117 8192 857955451968 5840 _ (by decide) (by decide) (by decide) MertensMasks.mask18117 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b26309 : B 26309 34501 437660667119 2923 := block_of_mask 26309 8192 437660667119 2923 _ (by decide) (by decide) (by decide) MertensMasks.mask26309 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b34501 : B 34501 42693 263298874111 2331 := block_of_mask 34501 8192 263298874111 2331 _ (by decide) (by decide) (by decide) MertensMasks.mask34501 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b42693 : B 42693 50885 172294407118 2247 := block_of_mask 42693 8192 172294407118 2247 _ (by decide) (by decide) (by decide) MertensMasks.mask42693 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b50885 : B 50885 59077 126551801919 2283 := block_of_mask 50885 8192 126551801919 2283 _ (by decide) (by decide) (by decide) MertensMasks.mask50885 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b59077 : B 59077 67269 91842249504 2190 := block_of_mask 59077 8192 91842249504 2190 _ (by decide) (by decide) (by decide) MertensMasks.mask59077 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b67269 : B 67269 75461 72075070739 2196 := block_of_mask 67269 8192 72075070739 2196 _ (by decide) (by decide) (by decide) MertensMasks.mask67269 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b75461 : B 75461 83653 57806621944 2190 := block_of_mask 75461 8192 57806621944 2190 _ (by decide) (by decide) (by decide) MertensMasks.mask75461 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b83653 : B 83653 91845 46239157963 2133 := block_of_mask 83653 8192 46239157963 2133 _ (by decide) (by decide) (by decide) MertensMasks.mask83653 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b91845 : B 91845 100037 39171378441 2157 := block_of_mask 91845 8192 39171378441 2157 _ (by decide) (by decide) (by decide) MertensMasks.mask91845 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b100037 : B 100037 108229 32475057650 2109 := block_of_mask 100037 8192 32475057650 2109 _ (by decide) (by decide) (by decide) MertensMasks.mask100037 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b108229 : B 108229 116421 27739806786 2097 := block_of_mask 108229 8192 27739806786 2097 _ (by decide) (by decide) (by decide) MertensMasks.mask108229 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b116421 : B 116421 124613 24292347783 2115 := block_of_mask 116421 8192 24292347783 2115 _ (by decide) (by decide) (by decide) MertensMasks.mask116421 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b124613 : B 124613 132805 21027325430 2088 := block_of_mask 124613 8192 21027325430 2088 _ (by decide) (by decide) (by decide) MertensMasks.mask124613 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b132805 : B 132805 140997 18685578466 2100 := block_of_mask 132805 8192 18685578466 2100 _ (by decide) (by decide) (by decide) MertensMasks.mask132805 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b140997 : B 140997 149189 16177504100 2043 := block_of_mask 140997 8192 16177504100 2043 _ (by decide) (by decide) (by decide) MertensMasks.mask140997 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b149189 : B 149189 157381 14805700189 2085 := block_of_mask 149189 8192 14805700189 2085 _ (by decide) (by decide) (by decide) MertensMasks.mask149189 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b157381 : B 157381 165573 12814603288 2004 := block_of_mask 157381 8192 12814603288 2004 _ (by decide) (by decide) (by decide) MertensMasks.mask157381 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b165573 : B 165573 173765 11656426034 2013 := block_of_mask 165573 8192 11656426034 2013 _ (by decide) (by decide) (by decide) MertensMasks.mask165573 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b173765 : B 173765 181957 10694226100 2028 := block_of_mask 173765 8192 10694226100 2028 _ (by decide) (by decide) (by decide) MertensMasks.mask173765 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b181957 : B 181957 190149 9989698300 2073 := block_of_mask 181957 8192 9989698300 2073 _ (by decide) (by decide) (by decide) MertensMasks.mask181957 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b190149 : B 190149 198341 8881053502 2010 := block_of_mask 190149 8192 8881053502 2010 _ (by decide) (by decide) (by decide) MertensMasks.mask190149 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b198341 : B 198341 206533 8125865618 1998 := block_of_mask 198341 8192 8125865618 1998 _ (by decide) (by decide) (by decide) MertensMasks.mask198341 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b206533 : B 206533 214725 7601219234 2022 := block_of_mask 206533 8192 7601219234 2022 _ (by decide) (by decide) (by decide) MertensMasks.mask206533 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b214725 : B 214725 222917 6881304063 1977 := block_of_mask 214725 8192 6881304063 1977 _ (by decide) (by decide) (by decide) MertensMasks.mask214725 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b222917 : B 222917 231109 6617047482 2046 := block_of_mask 222917 8192 6617047482 2046 _ (by decide) (by decide) (by decide) MertensMasks.mask222917 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b231109 : B 231109 239301 5738958312 1905 := block_of_mask 231109 8192 5738958312 1905 _ (by decide) (by decide) (by decide) MertensMasks.mask231109 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b239301 : B 239301 247493 5623474206 1998 := block_of_mask 239301 8192 5623474206 1998 _ (by decide) (by decide) (by decide) MertensMasks.mask239301 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b247493 : B 247493 255685 5279030654 2004 := block_of_mask 247493 8192 5279030654 2004 _ (by decide) (by decide) (by decide) MertensMasks.mask247493 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b255685 : B 255685 263877 4742146580 1920 := block_of_mask 255685 8192 4742146580 1920 _ (by decide) (by decide) (by decide) MertensMasks.mask255685 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b263877 : B 263877 272069 4680626856 2016 := block_of_mask 263877 8192 4680626856 2016 _ (by decide) (by decide) (by decide) MertensMasks.mask263877 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b272069 : B 272069 280261 4223085000 1932 := block_of_mask 272069 8192 4223085000 1932 _ (by decide) (by decide) (by decide) MertensMasks.mask272069 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b280261 : B 280261 288453 3961777977 1920 := block_of_mask 280261 8192 3961777977 1920 _ (by decide) (by decide) (by decide) MertensMasks.mask280261 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b288453 : B 288453 296645 3770966449 1935 := block_of_mask 288453 8192 3770966449 1935 _ (by decide) (by decide) (by decide) MertensMasks.mask288453 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b296645 : B 296645 304837 3608898767 1959 := block_of_mask 296645 8192 3608898767 1959 _ (by decide) (by decide) (by decide) MertensMasks.mask296645 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b304837 : B 304837 313029 3370045257 1929 := block_of_mask 304837 8192 3370045257 1929 _ (by decide) (by decide) (by decide) MertensMasks.mask304837 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b313029 : B 313029 321221 3321662984 2004 := block_of_mask 313029 8192 3321662984 2004 _ (by decide) (by decide) (by decide) MertensMasks.mask313029 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b321221 : B 321221 329413 3085788255 1959 := block_of_mask 321221 8192 3085788255 1959 _ (by decide) (by decide) (by decide) MertensMasks.mask321221 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b329413 : B 329413 337605 2900106173 1935 := block_of_mask 329413 8192 2900106173 1935 _ (by decide) (by decide) (by decide) MertensMasks.mask329413 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b337605 : B 337605 345797 2736650603 1917 := block_of_mask 337605 8192 2736650603 1917 _ (by decide) (by decide) (by decide) MertensMasks.mask337605 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b345797 : B 345797 353989 2651088317 1947 := block_of_mask 345797 8192 2651088317 1947 _ (by decide) (by decide) (by decide) MertensMasks.mask345797 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b353989 : B 353989 362181 2453875078 1887 := block_of_mask 353989 8192 2453875078 1887 _ (by decide) (by decide) (by decide) MertensMasks.mask353989 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b362181 : B 362181 370373 2334918857 1878 := block_of_mask 362181 8192 2334918857 1878 _ (by decide) (by decide) (by decide) MertensMasks.mask362181 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b370373 : B 370373 378565 2271773624 1911 := block_of_mask 370373 8192 2271773624 1911 _ (by decide) (by decide) (by decide) MertensMasks.mask370373 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b378565 : B 378565 386757 2198811876 1932 := block_of_mask 378565 8192 2198811876 1932 _ (by decide) (by decide) (by decide) MertensMasks.mask378565 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b386757 : B 386757 394949 2103582283 1929 := block_of_mask 386757 8192 2103582283 1929 _ (by decide) (by decide) (by decide) MertensMasks.mask386757 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b394949 : B 394949 403141 1947265504 1860 := block_of_mask 394949 8192 1947265504 1860 _ (by decide) (by decide) (by decide) MertensMasks.mask394949 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b403141 : B 403141 411333 1883967685 1875 := block_of_mask 403141 8192 1883967685 1875 _ (by decide) (by decide) (by decide) MertensMasks.mask403141 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b411333 : B 411333 419525 1851308391 1917 := block_of_mask 411333 8192 1851308391 1917 _ (by decide) (by decide) (by decide) MertensMasks.mask411333 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b419525 : B 419525 427717 1739047007 1872 := block_of_mask 419525 8192 1739047007 1872 _ (by decide) (by decide) (by decide) MertensMasks.mask419525 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b427717 : B 427717 435909 1780249506 1992 := block_of_mask 427717 8192 1780249506 1992 _ (by decide) (by decide) (by decide) MertensMasks.mask427717 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b435909 : B 435909 444101 1628728215 1893 := block_of_mask 435909 8192 1628728215 1893 _ (by decide) (by decide) (by decide) MertensMasks.mask435909 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b444101 : B 444101 452293 1547821317 1866 := block_of_mask 444101 8192 1547821317 1866 _ (by decide) (by decide) (by decide) MertensMasks.mask444101 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b452293 : B 452293 460485 1442562688 1803 := block_of_mask 452293 8192 1442562688 1803 _ (by decide) (by decide) (by decide) MertensMasks.mask452293 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b460485 : B 460485 468677 1454454516 1884 := block_of_mask 460485 8192 1454454516 1884 _ (by decide) (by decide) (by decide) MertensMasks.mask460485 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b468677 : B 468677 476869 1449549695 1944 := block_of_mask 468677 8192 1449549695 1944 _ (by decide) (by decide) (by decide) MertensMasks.mask468677 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b476869 : B 476869 485061 1331711919 1848 := block_of_mask 476869 8192 1331711919 1848 _ (by decide) (by decide) (by decide) MertensMasks.mask476869 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b485061 : B 485061 493253 1310062950 1881 := block_of_mask 485061 8192 1310062950 1881 _ (by decide) (by decide) (by decide) MertensMasks.mask485061 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b493253 : B 493253 501445 1295643468 1923 := block_of_mask 493253 8192 1295643468 1923 _ (by decide) (by decide) (by decide) MertensMasks.mask493253 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b501445 : B 501445 509637 1185393744 1818 := block_of_mask 501445 8192 1185393744 1818 _ (by decide) (by decide) (by decide) MertensMasks.mask501445 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b509637 : B 509637 517829 1199063801 1899 := block_of_mask 509637 8192 1199063801 1899 _ (by decide) (by decide) (by decide) MertensMasks.mask509637 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b517829 : B 517829 526021 1150936623 1881 := block_of_mask 517829 8192 1150936623 1881 _ (by decide) (by decide) (by decide) MertensMasks.mask517829 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b526021 : B 526021 534213 1110386542 1872 := block_of_mask 526021 8192 1110386542 1872 _ (by decide) (by decide) (by decide) MertensMasks.mask526021 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b534213 : B 534213 542405 1052461202 1830 := block_of_mask 534213 8192 1052461202 1830 _ (by decide) (by decide) (by decide) MertensMasks.mask534213 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b542405 : B 542405 550597 1021230685 1830 := block_of_mask 542405 8192 1021230685 1830 _ (by decide) (by decide) (by decide) MertensMasks.mask542405 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b550597 : B 550597 558789 999612097 1845 := block_of_mask 550597 8192 999612097 1845 _ (by decide) (by decide) (by decide) MertensMasks.mask550597 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b558789 : B 558789 566981 969127614 1842 := block_of_mask 558789 8192 969127614 1842 _ (by decide) (by decide) (by decide) MertensMasks.mask558789 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b566981 : B 566981 575173 953668922 1866 := block_of_mask 566981 8192 953668922 1866 _ (by decide) (by decide) (by decide) MertensMasks.mask566981 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b575173 : B 575173 583365 931415455 1875 := block_of_mask 575173 8192 931415455 1875 _ (by decide) (by decide) (by decide) MertensMasks.mask575173 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b583365 : B 583365 591557 895696263 1854 := block_of_mask 583365 8192 895696263 1854 _ (by decide) (by decide) (by decide) MertensMasks.mask583365 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b591557 : B 591557 599749 875295639 1863 := block_of_mask 591557 8192 875295639 1863 _ (by decide) (by decide) (by decide) MertensMasks.mask591557 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b599749 : B 599749 607941 847499467 1854 := block_of_mask 599749 8192 847499467 1854 _ (by decide) (by decide) (by decide) MertensMasks.mask599749 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b607941 : B 607941 616133 825006280 1854 := block_of_mask 607941 8192 825006280 1854 _ (by decide) (by decide) (by decide) MertensMasks.mask607941 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b616133 : B 616133 624325 804745340 1857 := block_of_mask 616133 8192 804745340 1857 _ (by decide) (by decide) (by decide) MertensMasks.mask616133 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b624325 : B 624325 632517 755669710 1791 := block_of_mask 624325 8192 755669710 1791 _ (by decide) (by decide) (by decide) MertensMasks.mask624325 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b632517 : B 632517 640709 735443953 1788 := block_of_mask 632517 8192 735443953 1788 _ (by decide) (by decide) (by decide) MertensMasks.mask632517 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b640709 : B 640709 648901 734699392 1833 := block_of_mask 640709 8192 734699392 1833 _ (by decide) (by decide) (by decide) MertensMasks.mask640709 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b648901 : B 648901 657093 717673069 1836 := block_of_mask 648901 8192 717673069 1836 _ (by decide) (by decide) (by decide) MertensMasks.mask648901 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b657093 : B 657093 665285 710119373 1863 := block_of_mask 657093 8192 710119373 1863 _ (by decide) (by decide) (by decide) MertensMasks.mask657093 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b665285 : B 665285 673477 676047257 1818 := block_of_mask 665285 8192 676047257 1818 _ (by decide) (by decide) (by decide) MertensMasks.mask665285 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b673477 : B 673477 681669 666356011 1836 := block_of_mask 673477 8192 666356011 1836 _ (by decide) (by decide) (by decide) MertensMasks.mask673477 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b681669 : B 681669 689861 647460435 1827 := block_of_mask 681669 8192 647460435 1827 _ (by decide) (by decide) (by decide) MertensMasks.mask681669 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b689861 : B 689861 698053 637417235 1842 := block_of_mask 689861 8192 637417235 1842 _ (by decide) (by decide) (by decide) MertensMasks.mask689861 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem b698053 : B 698053 706245 614409148 1818 := block_of_mask 698053 8192 614409148 1818 _ (by decide) (by decide) (by decide) MertensMasks.mask698053 (by rfl)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_0 : B 0 9925 315713513703116041 70005247 := @join 0 1733 9925 315684388066545112 61977157 29125636570929 8028090 b0 b1733
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_9925 : B 9925 26309 3230369698094 37663 := @join 9925 18117 26309 2372414246126 31823 857955451968 5840 b9925 b18117
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_26309 : B 26309 42693 700959541230 5254 := @join 26309 34501 42693 437660667119 2923 263298874111 2331 b26309 b34501
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_42693 : B 42693 59077 298846209037 4530 := @join 42693 50885 59077 172294407118 2247 126551801919 2283 b42693 b50885
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_59077 : B 59077 75461 163917320243 4386 := @join 59077 67269 75461 91842249504 2190 72075070739 2196 b59077 b67269
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_75461 : B 75461 91845 104045779907 4323 := @join 75461 83653 91845 57806621944 2190 46239157963 2133 b75461 b83653
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_91845 : B 91845 108229 71646436091 4266 := @join 91845 100037 108229 39171378441 2157 32475057650 2109 b91845 b100037
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_108229 : B 108229 124613 52032154569 4212 := @join 108229 116421 124613 27739806786 2097 24292347783 2115 b108229 b116421
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_124613 : B 124613 140997 39712903896 4188 := @join 124613 132805 140997 21027325430 2088 18685578466 2100 b124613 b132805
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_140997 : B 140997 157381 30983204289 4128 := @join 140997 149189 157381 16177504100 2043 14805700189 2085 b140997 b149189
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_157381 : B 157381 173765 24471029322 4017 := @join 157381 165573 173765 12814603288 2004 11656426034 2013 b157381 b165573
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_173765 : B 173765 190149 20683924400 4101 := @join 173765 181957 190149 10694226100 2028 9989698300 2073 b173765 b181957
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_190149 : B 190149 206533 17006919120 4008 := @join 190149 198341 206533 8881053502 2010 8125865618 1998 b190149 b198341
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_206533 : B 206533 222917 14482523297 3999 := @join 206533 214725 222917 7601219234 2022 6881304063 1977 b206533 b214725
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_222917 : B 222917 239301 12356005794 3951 := @join 222917 231109 239301 6617047482 2046 5738958312 1905 b222917 b231109
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_239301 : B 239301 255685 10902504860 4002 := @join 239301 247493 255685 5623474206 1998 5279030654 2004 b239301 b247493
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_255685 : B 255685 272069 9422773436 3936 := @join 255685 263877 272069 4742146580 1920 4680626856 2016 b255685 b263877
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_272069 : B 272069 288453 8184862977 3852 := @join 272069 280261 288453 4223085000 1932 3961777977 1920 b272069 b280261
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_288453 : B 288453 304837 7379865216 3894 := @join 288453 296645 304837 3770966449 1935 3608898767 1959 b288453 b296645
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_304837 : B 304837 321221 6691708241 3933 := @join 304837 313029 321221 3370045257 1929 3321662984 2004 b304837 b313029
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_321221 : B 321221 337605 5985894428 3894 := @join 321221 329413 337605 3085788255 1959 2900106173 1935 b321221 b329413
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_337605 : B 337605 353989 5387738920 3864 := @join 337605 345797 353989 2736650603 1917 2651088317 1947 b337605 b345797
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_353989 : B 353989 370373 4788793935 3765 := @join 353989 362181 370373 2453875078 1887 2334918857 1878 b353989 b362181
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_370373 : B 370373 386757 4470585500 3843 := @join 370373 378565 386757 2271773624 1911 2198811876 1932 b370373 b378565
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_386757 : B 386757 403141 4050847787 3789 := @join 386757 394949 403141 2103582283 1929 1947265504 1860 b386757 b394949
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_403141 : B 403141 419525 3735276076 3792 := @join 403141 411333 419525 1883967685 1875 1851308391 1917 b403141 b411333
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_419525 : B 419525 435909 3519296513 3864 := @join 419525 427717 435909 1739047007 1872 1780249506 1992 b419525 b427717
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_435909 : B 435909 452293 3176549532 3759 := @join 435909 444101 452293 1628728215 1893 1547821317 1866 b435909 b444101
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_452293 : B 452293 468677 2897017204 3687 := @join 452293 460485 468677 1442562688 1803 1454454516 1884 b452293 b460485
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_468677 : B 468677 485061 2781261614 3792 := @join 468677 476869 485061 1449549695 1944 1331711919 1848 b468677 b476869
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_485061 : B 485061 501445 2605706418 3804 := @join 485061 493253 501445 1310062950 1881 1295643468 1923 b485061 b493253
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_501445 : B 501445 517829 2384457545 3717 := @join 501445 509637 517829 1185393744 1818 1199063801 1899 b501445 b509637
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_517829 : B 517829 534213 2261323165 3753 := @join 517829 526021 534213 1150936623 1881 1110386542 1872 b517829 b526021
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_534213 : B 534213 550597 2073691887 3660 := @join 534213 542405 550597 1052461202 1830 1021230685 1830 b534213 b542405
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_550597 : B 550597 566981 1968739711 3687 := @join 550597 558789 566981 999612097 1845 969127614 1842 b550597 b558789
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_566981 : B 566981 583365 1885084377 3741 := @join 566981 575173 583365 953668922 1866 931415455 1875 b566981 b575173
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_583365 : B 583365 599749 1770991902 3717 := @join 583365 591557 599749 895696263 1854 875295639 1863 b583365 b591557
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_599749 : B 599749 616133 1672505747 3708 := @join 599749 607941 616133 847499467 1854 825006280 1854 b599749 b607941
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_616133 : B 616133 632517 1560415050 3648 := @join 616133 624325 632517 804745340 1857 755669710 1791 b616133 b624325
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_632517 : B 632517 648901 1470143345 3621 := @join 632517 640709 648901 735443953 1788 734699392 1833 b632517 b640709
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_648901 : B 648901 665285 1427792442 3699 := @join 648901 657093 665285 717673069 1836 710119373 1863 b648901 b657093
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_665285 : B 665285 681669 1342403268 3654 := @join 665285 673477 681669 676047257 1818 666356011 1836 b665285 b673477
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t1_681669 : B 681669 698053 1284877670 3669 := @join 681669 689861 698053 647460435 1827 637417235 1842 b681669 b689861
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_0 : B 0 26309 315716744072814135 70042910 := @join 0 9925 26309 315713513703116041 70005247 3230369698094 37663 t1_0 t1_9925
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_26309 : B 26309 59077 999805750267 9784 := @join 26309 42693 59077 700959541230 5254 298846209037 4530 t1_26309 t1_42693
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_59077 : B 59077 91845 267963100150 8709 := @join 59077 75461 91845 163917320243 4386 104045779907 4323 t1_59077 t1_75461
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_91845 : B 91845 124613 123678590660 8478 := @join 91845 108229 124613 71646436091 4266 52032154569 4212 t1_91845 t1_108229
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_124613 : B 124613 157381 70696108185 8316 := @join 124613 140997 157381 39712903896 4188 30983204289 4128 t1_124613 t1_140997
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_157381 : B 157381 190149 45154953722 8118 := @join 157381 173765 190149 24471029322 4017 20683924400 4101 t1_157381 t1_173765
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_190149 : B 190149 222917 31489442417 8007 := @join 190149 206533 222917 17006919120 4008 14482523297 3999 t1_190149 t1_206533
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_222917 : B 222917 255685 23258510654 7953 := @join 222917 239301 255685 12356005794 3951 10902504860 4002 t1_222917 t1_239301
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_255685 : B 255685 288453 17607636413 7788 := @join 255685 272069 288453 9422773436 3936 8184862977 3852 t1_255685 t1_272069
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_288453 : B 288453 321221 14071573457 7827 := @join 288453 304837 321221 7379865216 3894 6691708241 3933 t1_288453 t1_304837
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_321221 : B 321221 353989 11373633348 7758 := @join 321221 337605 353989 5985894428 3894 5387738920 3864 t1_321221 t1_337605
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_353989 : B 353989 386757 9259379435 7608 := @join 353989 370373 386757 4788793935 3765 4470585500 3843 t1_353989 t1_370373
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_386757 : B 386757 419525 7786123863 7581 := @join 386757 403141 419525 4050847787 3789 3735276076 3792 t1_386757 t1_403141
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_419525 : B 419525 452293 6695846045 7623 := @join 419525 435909 452293 3519296513 3864 3176549532 3759 t1_419525 t1_435909
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_452293 : B 452293 485061 5678278818 7479 := @join 452293 468677 485061 2897017204 3687 2781261614 3792 t1_452293 t1_468677
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_485061 : B 485061 517829 4990163963 7521 := @join 485061 501445 517829 2605706418 3804 2384457545 3717 t1_485061 t1_501445
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_517829 : B 517829 550597 4335015052 7413 := @join 517829 534213 550597 2261323165 3753 2073691887 3660 t1_517829 t1_534213
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_550597 : B 550597 583365 3853824088 7428 := @join 550597 566981 583365 1968739711 3687 1885084377 3741 t1_550597 t1_566981
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_583365 : B 583365 616133 3443497649 7425 := @join 583365 599749 616133 1770991902 3717 1672505747 3708 t1_583365 t1_599749
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_616133 : B 616133 648901 3030558395 7269 := @join 616133 632517 648901 1560415050 3648 1470143345 3621 t1_616133 t1_632517
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_648901 : B 648901 681669 2770195710 7353 := @join 648901 665285 681669 1427792442 3699 1342403268 3654 t1_648901 t1_665285
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t2_681669 : B 681669 706245 1899286818 5487 := @join 681669 698053 706245 1284877670 3669 614409148 1818 t1_681669 b698053
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_0 : B 0 59077 315717743878564402 70052694 := @join 0 26309 59077 315716744072814135 70042910 999805750267 9784 t2_0 t2_26309
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_59077 : B 59077 124613 391641690810 17187 := @join 59077 91845 124613 267963100150 8709 123678590660 8478 t2_59077 t2_91845
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_124613 : B 124613 190149 115851061907 16434 := @join 124613 157381 190149 70696108185 8316 45154953722 8118 t2_124613 t2_157381
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_190149 : B 190149 255685 54747953071 15960 := @join 190149 222917 255685 31489442417 8007 23258510654 7953 t2_190149 t2_222917
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_255685 : B 255685 321221 31679209870 15615 := @join 255685 288453 321221 17607636413 7788 14071573457 7827 t2_255685 t2_288453
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_321221 : B 321221 386757 20633012783 15366 := @join 321221 353989 386757 11373633348 7758 9259379435 7608 t2_321221 t2_353989
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_386757 : B 386757 452293 14481969908 15204 := @join 386757 419525 452293 7786123863 7581 6695846045 7623 t2_386757 t2_419525
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_452293 : B 452293 517829 10668442781 15000 := @join 452293 485061 517829 5678278818 7479 4990163963 7521 t2_452293 t2_485061
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_517829 : B 517829 583365 8188839140 14841 := @join 517829 550597 583365 4335015052 7413 3853824088 7428 t2_517829 t2_550597
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_583365 : B 583365 648901 6474056044 14694 := @join 583365 616133 648901 3443497649 7425 3030558395 7269 t2_583365 t2_616133
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t3_648901 : B 648901 706245 4669482528 12840 := @join 648901 681669 706245 2770195710 7353 1899286818 5487 t2_648901 t2_681669
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t4_0 : B 0 124613 315718135520255212 70069881 := @join 0 59077 124613 315717743878564402 70052694 391641690810 17187 t3_0 t3_59077
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t4_124613 : B 124613 255685 170599014978 32394 := @join 124613 190149 255685 115851061907 16434 54747953071 15960 t3_124613 t3_190149
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t4_255685 : B 255685 386757 52312222653 30981 := @join 255685 321221 386757 31679209870 15615 20633012783 15366 t3_255685 t3_321221
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t4_386757 : B 386757 517829 25150412689 30204 := @join 386757 452293 517829 14481969908 15204 10668442781 15000 t3_386757 t3_452293
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t4_517829 : B 517829 648901 14662895184 29535 := @join 517829 583365 648901 8188839140 14841 6474056044 14694 t3_517829 t3_583365
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t5_0 : B 0 255685 315718306119270190 70102275 := @join 0 124613 255685 315718135520255212 70069881 170599014978 32394 t4_0 t4_124613
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t5_255685 : B 255685 517829 77462635342 61185 := @join 255685 386757 517829 52312222653 30981 25150412689 30204 t4_255685 t4_386757
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t5_517829 : B 517829 706245 19332377712 42375 := @join 517829 648901 706245 14662895184 29535 4669482528 12840 t4_517829 t3_648901
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t6_0 : B 0 517829 315718383581905532 70163460 := @join 0 255685 517829 315718306119270190 70102275 77462635342 61185 t5_0 t5_255685
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem t7_0 : B 0 706245 315718402914283244 70205835 := @join 0 517829 706245 315718383581905532 70163460 19332377712 42375 t6_0 t5_517829
theorem checked : B 0 706245 315718402914283244 70205835 := t7_0
end MertensCertificate

open Filter Real
open scoped Topology
noncomputable section
namespace GammaCertificate

private def c (b : Bool) (t : ℝ) : ℝ :=
  -t/2+t^2/12-(if b then t^4/120 else 0)
private def cp (b : Bool) (t : ℝ) : ℝ :=
  -1/2+t/6-(if b then t^3/30 else 0)
private theorem dc (b : Bool) (t : ℝ) : HasDerivAt (c b) (cp b t) t := by
  have h := hasDerivAt_id t
  cases b
  · convert (((h.neg.div_const 2).add ((h.pow 2).div_const 12)).sub (hasDerivAt_const t (0 : ℝ))) using 1
    · funext x; rfl
    · simp [cp]; ring
  · convert (((h.neg.div_const 2).add ((h.pow 2).div_const 12)).sub ((h.pow 4).div_const 120)) using 1
    · funext x; rfl
    · simp [cp]; ring

private def gap (b : Bool) (t : ℝ) :=
  t/(1+t) - log (1+t) + c b (t/(1+t)) - c b t
private def gp (b : Bool) (t : ℝ) :=
  if b then t^6*(5+5*t+t^2)/(30*(1+t)^5) else -t^4/(6*(1+t)^3)

private theorem dg (b : Bool) (t : ℝ) (ht : 0 ≤ t) : HasDerivAt (gap b) (gp b t) t := by
  have hn : 1+t ≠ 0 := by positivity
  have h := hasDerivAt_id t
  have h1 := h.const_add 1
  have hu := h.div h1 hn
  convert (((hu.sub (h1.log hn)).add ((dc b _).comp t hu)).sub (dc b t)) using 1
  · funext x; rfl
  · cases b <;> simp [gp,cp,Pi.div_apply] <;> field_simp <;> ring

private theorem gsign (t : ℝ) (ht : 0 ≤ t) : gap false t ≤ 0 ∧ 0 ≤ gap true t := by
  have hcont (b : Bool) : ContinuousOn (gap b) (Set.Ici 0) := fun x hx => (dg b x hx).continuousAt.continuousWithinAt
  have hd (b : Bool) (x : ℝ) (hx : x ∈ interior (Set.Ici (0 : ℝ))) :=
    (dg b x (interior_subset hx)).hasDerivWithinAt (s := interior (Set.Ici (0 : ℝ)))
  have ha := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ)) (hcont false) (hd false) (by
    intro x hx; have h : 0 ≤ x := interior_subset hx; change -x^4/(6*(1+x)^3) ≤ 0; exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity))
  have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ)) (hcont true) (hd true) (by
    intro x hx; have h : 0 ≤ x := interior_subset hx; simp only [gp, ↓reduceIte]; positivity)
  exact ⟨by simpa [gap,c] using ha (show (0 : ℝ) ∈ Set.Ici 0 from by simp) ht ht,
    by simpa [gap,c] using hm (show (0 : ℝ) ∈ Set.Ici 0 from by simp) ht ht⟩

private def f (b : Bool) (n : ℕ) : ℝ :=
  (harmonic (n+1) : ℝ)-log (n+1)+c b (1/(n+1))

private theorem diff (b : Bool) (n : ℕ) : f b (n+1) - f b n = gap b (1/(n+1)) := by
  let x : ℝ := n+1
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < x+1 := by positivity
  have hl : log (x+1) - log x = log (1+1/x) := by
    rw [← log_div hy.ne' hx.ne']; congr 1; field_simp
  have hr : (1/x)/(1+1/x) = 1/(x+1) := by field_simp
  simp only [f,gap, harmonic_succ (n+1), Rat.cast_add, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add_one]
  change (↑(harmonic (n+1)) + (x+1)⁻¹ - log (x+1) + c b (1/(x+1))) -
    (↑(harmonic (n+1)) - log x + c b (1/x)) = _
  change _ = (1/x)/(1+1/x)-log (1+1/x)+c b ((1/x)/(1+1/x))-c b (1/x)
  rw [hr, ← hl]; ring

private theorem limf (b : Bool) : Tendsto (f b) atTop (𝓝 eulerMascheroniConstant) := by
  have ha := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hc := ((dc b 0).continuousAt.tendsto).comp hb
  unfold f
  simpa [Function.comp_def,c] using ha.add hc

theorem gamma_bounds : 0.57721565 < eulerMascheroniConstant ∧ eulerMascheroniConstant < 0.57721568 := by
  have hu : Antitone (f false) := antitone_nat_of_succ_le (fun n => by
    exact sub_nonpos.mp ((diff false n).trans_le (gsign _ (by positivity)).1))
  have hl : Monotone (f true) := monotone_nat_of_le_succ (fun n => by
    apply sub_nonneg.mp; rw [diff]; exact (gsign _ (by positivity)).2)
  have ub := hu.le_of_tendsto (limf false) 63
  have lb := hl.ge_of_tendsto (limf true) 63
  have hr : (4.7438909036 : ℝ) < (harmonic 64 : ℝ) ∧ (harmonic 64 : ℝ) < 4.743890904 := by norm_num [harmonic,Finset.sum_range_succ]
  have hlog : log 64 = 6 * log 2 := by
    rw [show (64 : ℝ) = 2^6 by norm_num, log_pow]; norm_num
  norm_num [f,c] at ub lb
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9, hr.1, hr.2]

end GammaCertificate

namespace MertensPrimeTail

theorem correction_bounds {p : ℝ} (hp : 1 < p) :
    0 ≤ -(Real.log (1-1/p) + 1/p) ∧
    -(Real.log (1-1/p) + 1/p) ≤ 1/(2*(p-1)) - 1/(2*p) := by
  have hp0 : 0 < p := by linarith
  have hm : 0 < p-1 := by linarith
  have hz : 1-1/p = (p/(p-1))⁻¹ := by field_simp
  have hx : 1 ≤ p/(p-1) := (le_div_iff₀ hm).2 (by linarith)
  constructor
  · have h := Real.log_le_sub_one_of_pos (show 0 < 1-1/p by rw [hz]; positivity)
    linarith
  · have h := Real.self_le_sinh_iff.mpr (Real.log_nonneg hx)
    rw [Real.sinh_eq, Real.exp_neg, Real.exp_log (by positivity : 0 < p/(p-1))] at h
    rw [hz,Real.log_inv]
    calc
      -(-Real.log (p/(p-1))+1/p) ≤ ((p/(p-1))-(p/(p-1))⁻¹)/2-1/p := by linarith
      _ = _ := by field_simp; ring

end MertensPrimeTail

namespace MertensPrimeTail
noncomputable def after (K i : ℕ) : ℝ :=
  if (K+i+1).Prime then -(Real.log (1-1/(K+i+1:ℝ))+1/(K+i+1:ℝ)) else 0

theorem tail_sum {K : ℕ} (hK : 0 < K) :
    Summable (after K) ∧ (∑' i, after K i) ≤ 1/(2*(K:ℝ)) := by
  let B (i : ℕ) : ℝ := 1/(2*((K:ℝ)+i))
  have hh (i : ℕ) : 0 ≤ after K i ∧ after K i ≤ B i - B (i+1) := by
    have h : (1:ℝ) < K+i+1 := by
      have hk : (0:ℝ) < K := by exact_mod_cast hK
      linarith [Nat.cast_nonneg (α := ℝ) i]
    have hp := correction_bounds h
    have he : (K:ℝ)+i+1-1 = K+i := by ring
    simp only [he] at hp
    simp only [after, B, Nat.cast_add, Nat.cast_one]
    split_ifs
    · exact ⟨hp.1, by simpa only [add_assoc] using hp.2⟩
    · exact ⟨le_rfl, by simpa only [add_assoc] using hp.1.trans hp.2⟩
  have hs (n : ℕ) : ∑ i ∈ Finset.range n, after K i ≤ B 0 - B n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ]; linarith [(hh n).2]
  have bound (n : ℕ) : ∑ i ∈ Finset.range n, after K i ≤ 1/(2*(K:ℝ)) := by
    have hn : 0 ≤ B n := by dsimp [B]; positivity
    simpa [B] using (hs n).trans (sub_le_self _ hn)
  exact ⟨summable_of_sum_range_le (fun i => (hh i).1) bound, Real.tsum_le_of_sum_range_le (fun i => (hh i).1) bound⟩
end MertensPrimeTail


namespace MertensAssembly

noncomputable def correction (n : ℕ) : ℝ :=
  -(Real.log (1-1/(n:ℝ))+1/(n:ℝ))

noncomputable def term (n : ℕ) : ℝ :=
  if n.Prime then correction n else 0

theorem assemble {K : ℕ} {tail : ℕ → ℝ}
    (shift : ∀ i, term (i+(K+1)) = tail i)
    (hs : Summable tail)
    (ht : 0 ≤ ∑' i, tail i)
    (hu : (∑' i, tail i) ≤ 1/(2*(K:ℝ)))
    (hK : 3000000 ≤ K)
    (hp₁ : 0.31571843 ≤ ∑ n ∈ Finset.range (K+1), term n)
    (hp₂ : (∑ n ∈ Finset.range (K+1), term n) ≤ 0.31571845)
    (hg : 0.57721565 < Real.eulerMascheroniConstant ∧ Real.eulerMascheroniConstant < 0.57721568) :
    let x : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1-1/(p:ℝ))+1/(p:ℝ))
    0.261497 ≤ x ∧ x ≤ 0.261498 := by
  have he : (fun i => term (i+(K+1))) = tail := funext shift
  have hfull : Summable term := (summable_nat_add_iff (K+1)).1 (he ▸ hs)
  have hsplit := hfull.sum_add_tsum_nat_add (K+1)
  rw [he] at hsplit
  have hpr : (∑' p : Nat.Primes, correction p) = ∑' n, term n :=
    Nat.Primes.tsum_eq_tsum_ite correction
  have hneg : (∑' p : Nat.Primes, (Real.log (1-1/(p:ℝ))+1/(p:ℝ))) = -(∑' n, term n) := by
    rw [← hpr, ← tsum_neg]
    congr 1; funext p; simp [correction]
  dsimp only
  rw [hneg, ← hsplit]
  have hreal : (3000000 : ℝ) ≤ K := by exact_mod_cast hK
  have hinv : 1/(2*(K:ℝ)) ≤ 1/6000000 := by
    apply one_div_le_one_div_of_le (by norm_num : (0:ℝ)<6000000)
    linarith
  constructor <;> linarith [hg.1,hg.2]

end MertensAssembly
namespace MertensSix
open Finset MertensPrimeTail
private abbrev K := 706244
private noncomputable def S (n : ℕ) : ℝ := 1 / (6*(706238+6*(n:ℝ)))

private theorem alive (n j : ℕ) (hn : j < 6) (hp : Nat.Prime (K+(6*n+j)+1)) : j=2 ∨ j=4 := by
  have h2 : ¬ 2 ∣ (K+(6*n+j)+1) := by
    intro h; have := (Nat.dvd_prime hp).1 h; unfold K at *; omega
  have h3 : ¬ 3 ∣ (K+(6*n+j)+1) := by
    intro h; have := (Nat.dvd_prime hp).1 h; unfold K at *; omega
  unfold K at *; omega

private theorem pos (i : ℕ) : 0 ≤ after K i := by
  simp only [after]; split_ifs
  · apply (correction_bounds _).1
    change (1 : ℝ) < 706244 + (i:ℝ) + 1
    linarith [Nat.cast_nonneg i (α := ℝ)]
  · exact le_rfl

private theorem single (n j : ℕ) : after K (6*n+j) ≤ (S n-S (n+1))/2 := by
  let x : ℝ := 706238+6*(n:ℝ)
  let p : ℝ := (K:ℝ)+(6*(n:ℝ)+j)+1
  have hx : 0 < x := by dsimp [x]; positivity
  have hp : x+6 ≤ p-1 := by dsimp [x,p,K]; linarith [Nat.cast_nonneg j (α:=ℝ)]
  have hp1 : 1 < p := by linarith
  have hh : (S n - S (n+1))/2 = 1/(2*x*(x+6)) := by
    unfold S; push_cast; dsimp [x]; field_simp; ring
  rw [hh]
  simp only [after]
  split_ifs
  · have ht := (correction_bounds hp1).2
    have he : 1/(2*(p-1))-1/(2*p) = 1/(2*(p-1)*p) := by
      field_simp; ring
    rw [he] at ht
    have hab : 1/(2*(p-1)*p) ≤ 1/(2*x*(x+6)) := by
      apply one_div_le_one_div_of_le (by positivity)
      gcongr <;> linarith
    simpa [p] using ht.trans hab
  · positivity

private theorem six (n : ℕ) :
    ∑ j ∈ range 6, after K (6*n+j) ≤ S n - S (n+1) := by
  have hz (j : ℕ) (hj : j<6) (h2 : j≠2) (h4 : j≠4) : after K (6*n+j) = 0 := by
    have h : ¬ (K+(6*n+j)+1).Prime := fun h => (alive n j hj h).elim h2 h4
    simp [after,h]
  rw [show (6:ℕ) = 5+1 by decide, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ, sum_range_succ]
  simp only [range_zero,sum_empty]
  rw [hz 0 (by decide) (by decide) (by decide),hz 1 (by decide) (by decide) (by decide),hz 3 (by decide) (by decide) (by decide),hz 5 (by decide) (by decide) (by decide)]
  linarith [single n 2,single n 4]

theorem tailSix : (∑' i, after K i) ≤ 1/(6*706238) := by
  have h (n : ℕ) : ∑ i ∈ range (6*n), after K i ≤ S 0 - S n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ,sum_range_add]; linarith [six n]
  apply Real.tsum_le_of_sum_range_le pos
  intro n
  have hle : ∑ i ∈ range n, after K i ≤ ∑ i ∈ range (6*n), after K i :=
    sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun i _ _ => pos i)
  have hs : 0 ≤ S n := by unfold S; positivity
  simpa [S] using (hle.trans (h n)).trans (sub_le_self _ hs)


open MertensAssembly
theorem of_prefix
    (hp₁ : (315718402914283244:ℝ)/10^18 ≤ ∑ n ∈ range (K+1), term n)
    (hp₂ : (∑ n ∈ range (K+1), term n) ≤ ((315718402914283244:ℝ)+70205835)/10^18) :
    let x : ℝ := Real.eulerMascheroniConstant + ∑' p : Nat.Primes, (Real.log (1-1/(p:ℝ))+1/(p:ℝ))
    0.261497 ≤ x ∧ x ≤ 0.261498 := by
  have he : (fun i => term (i+(K+1))) = after K := by
    funext i
    simp [term,correction,after,add_comm,add_left_comm]
  have hfull : Summable term := (summable_nat_add_iff (K+1)).1 (he ▸ (tail_sum (K:=K) (by decide)).1)
  have hsplit := hfull.sum_add_tsum_nat_add (K+1)
  rw [he] at hsplit
  have hpr : (∑' p : Nat.Primes, correction p) = ∑' n, term n :=
    Nat.Primes.tsum_eq_tsum_ite correction
  have hneg : (∑' p : Nat.Primes, (Real.log (1-1/(p:ℝ))+1/(p:ℝ))) = -(∑' n, term n) := by
    rw [← hpr, ← tsum_neg]
    congr 1; funext p; simp [correction]
  dsimp only
  rw [hneg, ← hsplit]
  have hp0 : 0 ≤ ∑' i, after K i := tsum_nonneg pos
  have hg := GammaCertificate.gamma_bounds
  constructor <;> linarith [hg.1,hg.2,tailSix]

end MertensSix

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem Conjectures.Cuts.Taskb182870585b8412c8aff946c : (have x1 : ℝ := Real.eulerMascheroniConstant + ∑' (x1 : Nat.Primes), (Real.log ((1 : ℝ) - (1 : ℝ) / ↑↑x1) + (1 : ℝ) / ↑↑x1); 0.261497 ≤ x1 ∧ x1 ≤ 0.261498) := by
  have h := @MertensFold.bounds 706244 315718402914283244 70205835 MertensCertificate.checked
  have term_eq : MertensFold.term = MertensAssembly.term := by
    funext p
    rfl
  simp only [term_eq, MertensPrefix.scale, Nat.cast_pow, Nat.cast_ofNat] at h
  exact MertensSix.of_prefix h.1 h.2
