import Mathlib

/-!
# Even targets above four quintillion

The public finite-range tasks cover offsets 2 through 32,768 above
4,000,000,000,000,000,000. This proposed extension covers the next 114,688
even targets. Large summands share 57 Lucas primality certificates. A bit
sieve checks the small complementary summand for every target.
-/

/-!
Lucas certificates for the large summands in a finite Goldbach interval.
A binary power is checked against an explicit list of reduced residues. The
elaborator constructs the list; the kernel checks its arithmetic and soundness.
-/
namespace PostBoundary262144.Anchors

private def base : ℕ := 4000000000000000000

private def powerTrace (p a : ℕ) : ℕ → ℕ → List ℕ → Bool
  | e, r, [] => e == 0 && r == 1
  | e, r, v :: vs =>
    r == (if e % 2 = 1 then v * v * a else v * v) % p &&
      powerTrace p a (e/2) v vs

private theorem powerTrace_sound (p a e r : ℕ) (vs : List ℕ)
    (h : powerTrace p a e r vs = true) : (a : ZMod p)^e = (r : ZMod p) := by
  induction vs generalizing e r with
  | nil =>
    simp only [powerTrace, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | cons v vs ih =>
    simp only [powerTrace, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hr, ht⟩ := h
    have hv := ih (e/2) v ht
    by_cases hodd : e % 2 = 1
    · rw [if_pos hodd] at hr
      have he : e / 2 + e / 2 + 1 = e := by omega
      calc
        (a : ZMod p)^e = (a : ZMod p)^(e/2) * (a : ZMod p)^(e/2) * a := by
          rw [← pow_add, ← pow_succ, he]
        _ = (r : ZMod p) := by simp [hr, hv]
    · rw [if_neg hodd] at hr
      have he : e / 2 + e / 2 = e := by omega
      calc
        (a : ZMod p)^e = (a : ZMod p)^(e/2) * (a : ZMod p)^(e/2) := by
          rw [← pow_add, he]
        _ = (r : ZMod p) := by simp [hr, hv]

private theorem primeFactor_mem (xs : List ℕ) (hxs : ∀ r ∈ xs, Nat.Prime r)
    {q : ℕ} (hq : q.Prime) (hd : q ∣ xs.prod) : q ∈ xs := by
  induction xs with
  | nil => exact (hq.not_dvd_one hd).elim
  | cons a xs ih =>
    rw [List.prod_cons, hq.dvd_mul] at hd
    rcases hd with ha | ht
    · have heq := (Nat.prime_dvd_prime_iff_eq hq (hxs a (by simp))).mp ha
      simp [heq]
    · exact List.mem_cons_of_mem _ (ih (fun r hr => hxs r (by simp [hr])) ht)

private abbrev Probe := ℕ × ℕ × List ℕ
private structure Record where
  shift : ℕ
  generator : ℕ
  fullTrace : List ℕ
  factors : List Probe

private def Record.large (r : Record) : ℕ := base - r.shift

private def smallPrime (q : ℕ) : Bool :=
  decide (2 ≤ q) && (List.range (q.sqrt + 1)).all (fun d => decide (d < 2 ∨ q % d ≠ 0))

private theorem smallPrime_sound {q : ℕ} (h : smallPrime q = true) : q.Prime := by
  simp only [smallPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  refine Nat.prime_def_le_sqrt.mpr ⟨h.1, ?_⟩
  intro d hd hl hdiv
  have hc := h.2 d (List.mem_range.mpr (by omega))
  exact (hc.resolve_left (by omega)) (Nat.mod_eq_zero_of_dvd hdiv)

private def Record.valid (r : Record) : Bool :=
  let p := r.large
  let a := r.generator
  (r.factors.map Prod.fst).prod == p - 1 &&
    powerTrace p a (p-1) 1 r.fullTrace &&
    r.factors.all (fun (q,v,vs) => smallPrime q && decide (v % p ≠ 1 % p) &&
      powerTrace p a ((p-1)/q) v vs)

private theorem Record.sound (r : Record) (h : r.valid = true) : r.large.Prime := by
  simp only [Record.valid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨hprod,hfull⟩,hprobes⟩ := h
  have hprime : ∀ q ∈ r.factors.map Prod.fst, Nat.Prime q := by
    intro q hm
    obtain ⟨⟨q',v,vs⟩,hi,rfl⟩ := List.mem_map.mp hm
    exact smallPrime_sound (hprobes _ hi).1.1
  refine lucas_primality r.large r.generator ?_ ?_
  · simpa using powerTrace_sound _ _ _ _ _ hfull
  · intro q hq hdiv
    have hmem := primeFactor_mem _ hprime hq (hprod.symm ▸ hdiv)
    obtain ⟨⟨q',v,vs⟩,hi,rfl⟩ := List.mem_map.mp hmem
    obtain ⟨⟨_, hne⟩, hpow⟩ := hprobes _ hi
    rw [powerTrace_sound _ _ _ _ _ hpow]
    intro hbad
    exact hne ((ZMod.natCast_eq_natCast_iff' v 1 r.large).mp (by simpa using hbad))

-- Each list holds the residues for the successive halved exponents.
private def makeTrace (p a e : ℕ) : ℕ × List ℕ := Id.run do
  let mut k := e
  let mut exponents := []
  for _ in [:e.log2+1] do
    if k == 0 then break
    exponents := k :: exponents
    k := k / 2
  let mut v := 1
  let mut vs := []
  for nextExponent in exponents do
    vs := v :: vs
    v := (if nextExponent % 2 = 1 then v*v*a else v*v) % p
  return (v,vs)

open Lean Elab Term in
elab "anchor% " s:num a:num "[" fs:num,* "]" : term => do
  let p := 4000000000000000000 - s.getNat
  let g := a.getNat
  let (_, full) := makeTrace p g (p-1)
  let probes := fs.getElems.toList.map fun f =>
    let q := f.getNat
    let (v,vs) := makeTrace p g ((p-1)/q)
    (q,v,vs)
  return mkAppN (mkConst ``Record.mk) #[toExpr s.getNat, toExpr g, toExpr full, toExpr probes]

set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem prime_2847 : (base - 2847).Prime :=
  Record.sound (anchor% 2847 7 [2, 2, 2, 2, 2, 3, 3, 17, 61, 5393, 15329, 162011]) (by decide +kernel)

private theorem prime_10403 : (base - 10403).Prime :=
  Record.sound (anchor% 10403 2 [2, 2, 13, 4091, 6317, 18803, 158303]) (by decide +kernel)

private theorem prime_8949 : (base - 8949).Prime :=
  Record.sound (anchor% 8949 3 [2, 3, 3, 5, 5, 7, 79, 751, 13789, 1552207]) (by decide +kernel)

private theorem prime_57071 : (base - 57071).Prime :=
  Record.sound (anchor% 57071 6 [2, 2, 2, 2, 11, 31, 449, 1427, 3803, 300877]) (by decide +kernel)

private theorem prime_15077 : (base - 15077).Prime :=
  Record.sound (anchor% 15077 2 [2, 23, 2579, 13127, 17443, 147253]) (by decide +kernel)

private theorem prime_24621 : (base - 24621).Prime :=
  Record.sound (anchor% 24621 2 [2, 3, 11, 11, 727, 4159, 5333, 341687]) (by decide +kernel)

private theorem prime_7199 : (base - 7199).Prime :=
  Record.sound (anchor% 7199 3 [2, 2, 2, 2, 2, 5, 5, 7, 17, 2153, 10529, 1853497]) (by decide +kernel)

private theorem prime_13923 : (base - 13923).Prime :=
  Record.sound (anchor% 13923 5 [2, 2, 3, 47, 113, 149, 1459, 4861, 59393]) (by decide +kernel)

private theorem prime_18117 : (base - 18117).Prime :=
  Record.sound (anchor% 18117 2 [2, 3, 2557, 6421, 8501, 4776451]) (by decide +kernel)

private theorem prime_67583 : (base - 67583).Prime :=
  Record.sound (anchor% 67583 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 17, 53, 773, 1723, 1627573]) (by decide +kernel)

private theorem prime_59751 : (base - 59751).Prime :=
  Record.sound (anchor% 59751 21 [2, 2, 2, 3, 13, 971, 1117, 6899, 1713353]) (by decide +kernel)

private theorem prime_68609 : (base - 68609).Prime :=
  Record.sound (anchor% 68609 14 [2, 5, 1907, 5849, 22367, 1603319]) (by decide +kernel)

private theorem prime_88623 : (base - 88623).Prime :=
  Record.sound (anchor% 88623 15 [2, 2, 2, 2, 3, 7, 41, 151, 8447, 9811, 23203]) (by decide +kernel)

private theorem prime_42857 : (base - 42857).Prime :=
  Record.sound (anchor% 42857 7 [2, 7, 163, 457, 691, 13451, 412663]) (by decide +kernel)

private theorem prime_135221 : (base - 135221).Prime :=
  Record.sound (anchor% 135221 2 [2, 431, 593, 1217, 5531, 1162529]) (by decide +kernel)

private theorem prime_36099 : (base - 36099).Prime :=
  Record.sound (anchor% 36099 2 [2, 2, 3, 5, 5, 17, 23, 127, 839, 1877, 170503]) (by decide +kernel)

private theorem prime_77099 : (base - 77099).Prime :=
  Record.sound (anchor% 77099 2 [2, 2, 5, 5, 149, 1201, 3119, 5869, 12211]) (by decide +kernel)

private theorem prime_137733 : (base - 137733).Prime :=
  Record.sound (anchor% 137733 3 [2, 3, 31, 859, 4799, 16141, 323201]) (by decide +kernel)

private theorem prime_72683 : (base - 72683).Prime :=
  Record.sound (anchor% 72683 2 [2, 2, 17, 67, 113, 1607, 5153, 938257]) (by decide +kernel)

private theorem prime_180381 : (base - 180381).Prime :=
  Record.sound (anchor% 180381 10 [2, 3, 3, 11, 41, 101, 997, 12149, 402767]) (by decide +kernel)

private theorem prime_21647 : (base - 21647).Prime :=
  Record.sound (anchor% 21647 3 [2, 2, 2, 2, 7, 7, 7, 7, 1367, 16217, 4696873]) (by decide +kernel)

private theorem prime_109899 : (base - 109899).Prime :=
  Record.sound (anchor% 109899 6 [2, 2, 3, 5, 5, 19, 73, 193, 23209, 2146093]) (by decide +kernel)

private theorem prime_130751 : (base - 130751).Prime :=
  Record.sound (anchor% 130751 3 [2, 2, 2, 2, 2, 2, 29, 89, 1601, 8377, 1805561]) (by decide +kernel)

private theorem prime_96417 : (base - 96417).Prime :=
  Record.sound (anchor% 96417 5 [2, 3, 181, 1667, 2111, 9479, 110419]) (by decide +kernel)

private theorem prime_154643 : (base - 154643).Prime :=
  Record.sound (anchor% 154643 2 [2, 2, 43, 751, 2503, 3181, 3889261]) (by decide +kernel)

private theorem prime_225219 : (base - 225219).Prime :=
  Record.sound (anchor% 225219 2 [2, 2, 3, 3, 5, 359, 2273, 5519, 4934387]) (by decide +kernel)

private theorem prime_175737 : (base - 175737).Prime :=
  Record.sound (anchor% 175737 3 [2, 3, 3, 13, 13, 17, 149, 587, 20693, 42737]) (by decide +kernel)

private theorem prime_214319 : (base - 214319).Prime :=
  Record.sound (anchor% 214319 6 [2, 2, 2, 2, 5, 1289, 2707, 13421, 1067687]) (by decide +kernel)

private theorem prime_245771 : (base - 245771).Prime :=
  Record.sound (anchor% 245771 2 [2, 2, 193, 1129, 2237, 13873, 147881]) (by decide +kernel)

private theorem prime_223701 : (base - 223701).Prime :=
  Record.sound (anchor% 223701 3 [2, 3, 43, 67, 167, 523, 6581, 402583]) (by decide +kernel)

private theorem prime_197163 : (base - 197163).Prime :=
  Record.sound (anchor% 197163 5 [2, 2, 3, 281, 617, 1163, 7499, 220447]) (by decide +kernel)

private theorem prime_145967 : (base - 145967).Prime :=
  Record.sound (anchor% 145967 5 [2, 2, 2, 2, 7, 13, 631, 2557, 9281, 183461]) (by decide +kernel)

private theorem prime_203699 : (base - 203699).Prime :=
  Record.sound (anchor% 203699 2 [2, 2, 5, 5, 1811, 4363, 11399, 444109]) (by decide +kernel)

private theorem prime_191103 : (base - 191103).Prime :=
  Record.sound (anchor% 191103 17 [2, 2, 2, 2, 2, 2, 2, 3, 7, 13, 137, 1447, 3407, 169483]) (by decide +kernel)

private theorem prime_113963 : (base - 113963).Prime :=
  Record.sound (anchor% 113963 19 [2, 2, 7, 7, 11, 37, 773, 21379, 3034189]) (by decide +kernel)

private theorem prime_90447 : (base - 90447).Prime :=
  Record.sound (anchor% 90447 5 [2, 2, 2, 2, 3, 787, 2953, 24671, 1453429]) (by decide +kernel)

private theorem prime_132663 : (base - 132663).Prime :=
  Record.sound (anchor% 132663 14 [2, 2, 2, 3, 3, 11, 71, 79, 97, 11981, 774791]) (by decide +kernel)

private theorem prime_39647 : (base - 39647).Prime :=
  Record.sound (anchor% 39647 3 [2, 2, 2, 2, 2, 11, 193, 401, 1699, 3449, 25057]) (by decide +kernel)

private theorem prime_188079 : (base - 188079).Prime :=
  Record.sound (anchor% 188079 31 [2, 2, 2, 2, 3, 5, 7, 17, 2687, 15773, 3304607]) (by decide +kernel)

private theorem prime_204491 : (base - 204491).Prime :=
  Record.sound (anchor% 204491 2 [2, 2, 487, 857, 1063, 4021, 560561]) (by decide +kernel)

private theorem prime_113129 : (base - 113129).Prime :=
  Record.sound (anchor% 113129 7 [2, 5, 13, 19, 89, 257, 1201, 4139, 14243]) (by decide +kernel)

private theorem prime_233241 : (base - 233241).Prime :=
  Record.sound (anchor% 233241 3 [2, 3, 163, 173, 199, 233, 293, 1740197]) (by decide +kernel)

private theorem prime_13547 : (base - 13547).Prime :=
  Record.sound (anchor% 13547 2 [2, 2, 31, 47, 97, 419, 8627, 1957469]) (by decide +kernel)

private theorem prime_182783 : (base - 182783).Prime :=
  Record.sound (anchor% 182783 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 13, 19, 37, 37, 5981, 3862921]) (by decide +kernel)

private theorem prime_11217 : (base - 11217).Prime :=
  Record.sound (anchor% 11217 3 [2, 3, 3, 7, 1051, 7793, 13327, 290837]) (by decide +kernel)

private theorem prime_212453 : (base - 212453).Prime :=
  Record.sound (anchor% 212453 2 [2, 7, 7, 79, 89, 1429, 3761, 1080143]) (by decide +kernel)

private theorem prime_143871 : (base - 143871).Prime :=
  Record.sound (anchor% 143871 11 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 19, 31, 83, 139, 14461, 26501]) (by decide +kernel)

private theorem prime_83387 : (base - 83387).Prime :=
  Record.sound (anchor% 83387 2 [2, 2, 7, 7, 7, 23, 97, 1559, 12757, 65707]) (by decide +kernel)

private theorem prime_69849 : (base - 69849).Prime :=
  Record.sound (anchor% 69849 3 [2, 3, 5, 5, 7, 211, 3301, 4283, 1277011]) (by decide +kernel)

private theorem prime_138293 : (base - 138293).Prime :=
  Record.sound (anchor% 138293 2 [2, 317, 401, 2749, 6779, 844279]) (by decide +kernel)

private theorem prime_173901 : (base - 173901).Prime :=
  Record.sound (anchor% 173901 2 [2, 3, 3, 17, 53, 53, 79, 12401, 4750103]) (by decide +kernel)

private theorem prime_65999 : (base - 65999).Prime :=
  Record.sound (anchor% 65999 3 [2, 2, 2, 2, 5, 5, 5, 7, 23, 31, 47, 3019, 2824109]) (by decide +kernel)

private theorem prime_80831 : (base - 80831).Prime :=
  Record.sound (anchor% 80831 6 [2, 2, 2, 2, 2, 2, 11, 241, 827, 16381, 1740301]) (by decide +kernel)

private theorem prime_78273 : (base - 78273).Prime :=
  Record.sound (anchor% 78273 3 [2, 3, 313, 433, 5119, 13913, 69067]) (by decide +kernel)

private theorem prime_6399 : (base - 6399).Prime :=
  Record.sound (anchor% 6399 19 [2, 2, 2, 2, 2, 2, 2, 2, 3, 5, 5, 13, 13, 29, 1667, 4999, 5101]) (by decide +kernel)

private theorem prime_53297 : (base - 53297).Prime :=
  Record.sound (anchor% 53297 5 [2, 5231, 23687, 23773, 678971]) (by decide +kernel)

private theorem prime_59333 : (base - 59333).Prime :=
  Record.sound (anchor% 59333 2 [2, 61, 109, 193, 1621, 9011, 106699]) (by decide +kernel)

/-- A large summand is the published cutoff minus one of these offsets. -/
def offsets : List ℕ :=
  [2847, 10403, 8949, 57071, 15077, 24621, 7199, 13923, 18117, 67583, 59751, 68609, 88623, 42857, 135221, 36099, 77099, 137733, 72683, 180381, 21647, 109899, 130751, 96417, 154643, 225219, 175737, 214319, 245771, 223701, 197163, 145967, 203699, 191103, 113963, 90447, 132663, 39647, 188079, 204491, 113129, 233241, 13547, 182783, 11217, 212453, 143871, 83387, 69849, 138293, 173901, 65999, 80831, 78273, 6399, 53297, 59333]

private def certifiedOffsets : List {s : ℕ // (base-s).Prime} :=
  [⟨2847, prime_2847⟩,
   ⟨10403, prime_10403⟩,
   ⟨8949, prime_8949⟩,
   ⟨57071, prime_57071⟩,
   ⟨15077, prime_15077⟩,
   ⟨24621, prime_24621⟩,
   ⟨7199, prime_7199⟩,
   ⟨13923, prime_13923⟩,
   ⟨18117, prime_18117⟩,
   ⟨67583, prime_67583⟩,
   ⟨59751, prime_59751⟩,
   ⟨68609, prime_68609⟩,
   ⟨88623, prime_88623⟩,
   ⟨42857, prime_42857⟩,
   ⟨135221, prime_135221⟩,
   ⟨36099, prime_36099⟩,
   ⟨77099, prime_77099⟩,
   ⟨137733, prime_137733⟩,
   ⟨72683, prime_72683⟩,
   ⟨180381, prime_180381⟩,
   ⟨21647, prime_21647⟩,
   ⟨109899, prime_109899⟩,
   ⟨130751, prime_130751⟩,
   ⟨96417, prime_96417⟩,
   ⟨154643, prime_154643⟩,
   ⟨225219, prime_225219⟩,
   ⟨175737, prime_175737⟩,
   ⟨214319, prime_214319⟩,
   ⟨245771, prime_245771⟩,
   ⟨223701, prime_223701⟩,
   ⟨197163, prime_197163⟩,
   ⟨145967, prime_145967⟩,
   ⟨203699, prime_203699⟩,
   ⟨191103, prime_191103⟩,
   ⟨113963, prime_113963⟩,
   ⟨90447, prime_90447⟩,
   ⟨132663, prime_132663⟩,
   ⟨39647, prime_39647⟩,
   ⟨188079, prime_188079⟩,
   ⟨204491, prime_204491⟩,
   ⟨113129, prime_113129⟩,
   ⟨233241, prime_233241⟩,
   ⟨13547, prime_13547⟩,
   ⟨182783, prime_182783⟩,
   ⟨11217, prime_11217⟩,
   ⟨212453, prime_212453⟩,
   ⟨143871, prime_143871⟩,
   ⟨83387, prime_83387⟩,
   ⟨69849, prime_69849⟩,
   ⟨138293, prime_138293⟩,
   ⟨173901, prime_173901⟩,
   ⟨65999, prime_65999⟩,
   ⟨80831, prime_80831⟩,
   ⟨78273, prime_78273⟩,
   ⟨6399, prime_6399⟩,
   ⟨53297, prime_53297⟩,
   ⟨59333, prime_59333⟩]

/-- Lucas certificates establish primality of every large summand. -/
theorem anchors_prime (a : ℕ) (ha : a ∈ offsets) : Nat.Prime (4000000000000000000 - a) := by
  have hm : a ∈ certifiedOffsets.map Subtype.val := ha
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hm
  exact s.property


end PostBoundary262144.Anchors

/-! An exact finite Goldbach cover using a checked sieve of bit positions.
A geometric series proposes a mask of multiples. The kernel verifies its
first bit and translation closure, which suffice for the primality proof. -/

namespace PostBoundary262144.Cover

/-- Bits at indices less than `width`. -/
def lowMask (width : ℕ) : ℕ := (1 <<< width) - 1

theorem lowMask_bit (width i : ℕ) : (lowMask width).testBit i = decide (i < width) := by
  simp [lowMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]

/-- A mask passes if it contains zero and shifting a live bit by `step`
preserves it whenever the resulting position is below `width`. -/
def advances (width step bits : ℕ) : Bool :=
  let moved := (bits <<< step) &&& lowMask width
  bits.testBit 0 && ((moved &&& bits) == moved)

theorem multiples_in_mask {width step bits : ℕ} (h : advances width step bits = true)
    (k : ℕ) (hk : step * k < width) : bits.testBit (step * k) = true := by
  simp only [advances, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hz, hs'⟩ := h
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    have hle : step * k ≤ step * (k + 1) := Nat.mul_le_mul_left step (Nat.le_succ k)
    have hprev := ih (lt_of_le_of_lt hle hk)
    have hge : step ≤ step * (k + 1) := by rw [Nat.mul_succ]; omega
    have hsub : step * (k + 1) - step = step * k := by rw [Nat.mul_succ]; omega
    have hm : ((bits <<< step) &&& lowMask width).testBit (step * (k+1)) = true := by
      simp [Nat.testBit_and, Nat.testBit_shiftLeft, lowMask_bit, hk, hge, hsub, hprev]
    have hi := congrArg (fun m : ℕ => m.testBit (step * (k + 1))) hs'
    change ((((bits <<< step) &&& lowMask width) &&& bits).testBit _) =
      (((bits <<< step) &&& lowMask width).testBit _) at hi
    rwa [Nat.testBit_and, hm, Bool.true_and] at hi

def unionBy {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: rest => f a ||| unionBy f rest

theorem unionBy_bit {α : Type} (f : α → ℕ) (xs : List α) (i : ℕ) :
    (unionBy f xs).testBit i = true ↔ ∃ x ∈ xs, (f x).testBit i = true := by
  induction xs with
  | nil => simp [unionBy]
  | cons x xs ih => simp [unionBy, Nat.testBit_or, ih]

/-- The denominator is odd and positive when `d ≥ 2`. The proofs below
only need the checked closure property of this proposed periodic pattern. -/
def period (width d : ℕ) : ℕ :=
  lowMask ((width / d + 1) * d) / lowMask d

def divisors : List ℕ := (List.range 712).map (· + 2)
def width : ℕ := 507916

def survivors : ℕ := lowMask width ^^^ unionBy (period width) divisors

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem periods_checked : divisors.all (fun d => advances width d (period width d)) = true := by
  decide +kernel

theorem survivors_prime {q : ℕ} (hq : 2 ≤ q) (hlt : q < width)
    (hb : survivors.testBit q = true) : Nat.Prime q := by
  by_contra hcomp
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < q) hcomp
  have hlo := (Nat.minFac_prime (by omega : q ≠ 1)).two_le
  have hupper : q.minFac < 714 := by
    by_contra! hlarge
    have hone := Nat.mul_le_mul hlarge hlarge
    rw [pow_two] at hsq
    change q < 507916 at hlt
    omega
  have hd : q.minFac ∈ divisors := by
    apply List.mem_map.mpr
    exact ⟨q.minFac - 2, List.mem_range.mpr (by omega), by omega⟩
  have hcheck := (List.all_eq_true.mp periods_checked) q.minFac hd
  obtain ⟨k, hdiv⟩ := Nat.minFac_dvd q
  have hp := multiples_in_mask hcheck k (by simpa only [← hdiv] using hlt)
  rw [← hdiv] at hp
  have hbad := (unionBy_bit (period width) divisors q).2 ⟨q.minFac, hd, hp⟩
  simp [survivors, Nat.testBit_xor, lowMask_bit, hlt, hbad] at hb

end PostBoundary262144.Cover

/-! A contiguous interval of binary Goldbach representations above 4 × 10¹⁸.
The large summands come from Lucas certificates. The small summands come
from the packed sieve proved sound above. -/

namespace PostBoundary262144.Cover

open PostBoundary262144.Anchors (offsets)

/-- Bit `2*k` selects a certified complement of a large anchor for
the target `4*10^18 + 2 + 2*k`. -/
def targetBits : ℕ := unionBy (fun a => survivors >>> (a + 2)) offsets

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem targets_checked : advances 262144 2 targetBits = true := by
  decide +kernel

private theorem offset_bound {a : ℕ} (h : a ∈ offsets) : a ≤ 245771 := by
  have checked : offsets.all (fun v => decide (v ≤ 245771)) = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked a h)

/-- Every one of the 131,072 even targets strictly above the 2014
cutoff through 4,000,000,000,000,262,144 has an actual prime pair. -/
theorem goldbach_above_four_quintillion (n : ℕ)
    (hb : 4000000000000000000 < n) (ht : n ≤ 4000000000000262144) (he : Even n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  obtain ⟨half, hhalf⟩ := he
  let k := half - 2000000000000000001
  have heq : n = 4000000000000000000 + 2 + 2 * k := by dsimp [k]; omega
  have hpos : 2 * k < 262144 := by omega
  have hbit := multiples_in_mask targets_checked k hpos
  obtain ⟨a, ha, hsmall⟩ := (unionBy_bit _ offsets (2 * k)).1 hbit
  rw [Nat.testBit_shiftRight] at hsmall
  have bound := offset_bound ha
  have hp := PostBoundary262144.Anchors.anchors_prime a ha
  have hq := survivors_prime (q := a + 2 + 2 * k) (by omega)
    (by change _ < 507916; omega) hsmall
  exact ⟨4000000000000000000 - a, a + 2 + 2 * k, hp, hq, by omega⟩

end PostBoundary262144.Cover

/-- Every even target after the public 32,768-offset block through offset 262,144
has a prime-pair representation. -/
theorem Conjectures.Goldbach.FinitePostBoundaryThrough262144 :
    ∀ j : ℕ, 16385 ≤ j → j ≤ 131072 →
      let n : ℕ := 4000000000000000000 + 2 * j
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  intro j hlo hhi
  apply PostBoundary262144.Cover.goldbach_above_four_quintillion
  · omega
  · omega
  · exact ⟨2000000000000000000 + j, by omega⟩
