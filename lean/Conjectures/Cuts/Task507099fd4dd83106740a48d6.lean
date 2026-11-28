import Mathlib

namespace GoldbachPalindromeDigits

/-- Encode a fixed-width vector with the least significant digit first. -/
def encode (d L : ℕ) (f : Fin L → ℕ) : ℕ :=
  ∑ i, f i * d ^ i.val

private theorem encode_succ (d L : ℕ) (f : Fin (L + 1) → ℕ) :
    encode d (L + 1) f = f 0 + encode d L (fun i => f i.succ) * d := by
  simp only [encode, Fin.sum_univ_succ, Fin.val_zero, pow_zero, mul_one,
    Fin.val_succ, pow_succ, ← Nat.mul_assoc, Finset.sum_mul]

theorem encode_lt (d L : ℕ) (f : Fin L → ℕ) (_hd : 2 ≤ d)
    (hf : ∀ i, f i < d) : encode d L f < d ^ L := by
  induction L with
  | zero => simp [encode]
  | succ L ih =>
    rw [encode_succ]
    have htail := ih (fun i => f i.succ) (fun i => hf i.succ)
    calc
      _ < d + encode d L (fun i => f i.succ) * d := Nat.add_lt_add_right (hf 0) _
      _ = (encode d L (fun i => f i.succ) + 1) * d := by ring
      _ ≤ d ^ L * d := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt htail)
      _ = _ := (pow_succ d L).symm

theorem digit_encode (d L : ℕ) (f : Fin L → ℕ) (hd : 2 ≤ d)
    (hf : ∀ i, f i < d) (i : Fin L) : encode d L f / d ^ i.val % d = f i := by
  have hd0 : 0 < d := by omega
  induction L with
  | zero => exact Fin.elim0 i
  | succ L ih =>
    have hdiv : encode d (L + 1) f / d = encode d L (fun j => f j.succ) := by
      rw [encode_succ, Nat.add_mul_div_right _ _ hd0, Nat.div_eq_of_lt (hf 0), zero_add]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [encode_succ, Nat.mod_eq_of_lt (hf 0)]
    · change encode d (L + 1) f / d ^ (j.val + 1) % d = f j.succ
      rw [pow_succ', ← Nat.div_div_eq_div_mul, hdiv]
      exact ih (fun j => f j.succ) (fun j => hf j.succ) j

theorem encode_digits (d L n : ℕ) (hd : 2 ≤ d) (hn : n < d ^ L) :
    encode d L (fun i => n / d ^ i.val % d) = n := by
  have hd0 : 0 < d := by omega
  induction L generalizing n with
  | zero =>
    have hn0 : n = 0 := by simp only [pow_zero] at hn; omega
    simp [encode, hn0]
  | succ L ih =>
    have hdiv : n / d < d ^ L := (Nat.div_lt_iff_lt_mul hd0).2 (by simpa [pow_succ] using hn)
    have htail : (fun i : Fin L => n / d ^ i.succ.val % d) =
        (fun i : Fin L => (n / d) / d ^ i.val % d) := by
      funext i
      rw [Fin.val_succ, pow_succ', Nat.div_div_eq_div_mul]
    rw [encode_succ, htail, ih (n / d) hdiv]
    simpa [Nat.mul_comm] using Nat.mod_add_div n d

end GoldbachPalindromeDigits

namespace GoldbachPalindromeFold

open Finset

def half (L : ℕ) : ℕ := (L+1)/2

theorem half_index_lt {L : ℕ} (j : Fin (half L)) : j.val < L := by
  have hj := j.isLt
  unfold half at hj
  omega

/-- The nearer end of the two positions related by reversal. -/
def fold {L : ℕ} (i : Fin L) : Fin (half L) :=
  ⟨min i.val (L-1-i.val), by
    have hi := i.isLt
    unfold half
    omega⟩

def lowerIndex {L : ℕ} (j : Fin (half L)) : Fin L :=
  ⟨j.val, half_index_lt j⟩

def mirror {L : ℕ} (i : Fin L) : Fin L :=
  ⟨L-1-i.val, by
    have hi := i.isLt
    omega⟩

def weight (d L : ℕ) (j : Fin (half L)) : ℕ :=
  if 2*j.val+1 = L then d^j.val else d^j.val+d^(L-1-j.val)

theorem fold_lowerIndex {L : ℕ} (j : Fin (half L)) : fold (lowerIndex j) = j := by
  apply Fin.ext
  change min j.val (L-1-j.val) = j.val
  have hj := j.isLt
  unfold half at hj
  exact min_eq_left (by omega)

theorem fold_mirror {L : ℕ} (i : Fin L) : fold (mirror i) = fold i := by
  apply Fin.ext
  change min (L-1-i.val) (L-1-(L-1-i.val)) = min i.val (L-1-i.val)
  have hi := i.isLt
  rw [show L-1-(L-1-i.val) = i.val by omega, min_comm]

/-- The center has one position and every other folded index has two. -/
theorem fiber_eq {L : ℕ} (j : Fin (half L)) :
    (univ.filter (fun i : Fin L => fold i = j)) = {lowerIndex j, mirror (lowerIndex j)} := by
  ext i
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hi
    have hf := congrArg Fin.val hi
    change min i.val (L-1-i.val) = j.val at hf
    have hiL := i.isLt
    rcases le_total i.val (L-1-i.val) with h | h
    · left
      apply Fin.ext
      change i.val = j.val
      rwa [min_eq_left h] at hf
    · right
      apply Fin.ext
      change i.val = L-1-j.val
      rw [min_eq_right h] at hf
      omega
  · rintro (rfl | rfl)
    · exact fold_lowerIndex j
    · exact (fold_mirror _).trans (fold_lowerIndex j)

theorem lower_eq_mirror_iff {L : ℕ} (j : Fin (half L)) :
    lowerIndex j = mirror (lowerIndex j) ↔ 2*j.val+1 = L := by
  have hj := half_index_lt j
  constructor
  · intro he
    have hv := congrArg Fin.val he
    change j.val = L-1-j.val at hv
    omega
  · intro he
    apply Fin.ext
    change j.val = L-1-j.val
    omega

theorem sum_fold (d L : ℕ) (f : Fin (half L) → ℕ) :
    (∑ i : Fin L, f (fold i)*d^i.val) = ∑ j : Fin (half L), f j*weight d L j := by
  rw [← Finset.sum_fiberwise univ fold (fun i : Fin L => f (fold i)*d^i.val)]
  apply sum_congr rfl
  intro j _
  calc
    _ = ∑ i ∈ univ.filter (fun i : Fin L => fold i = j), f j*d^i.val := by
      apply sum_congr rfl
      intro i hi
      rw [(mem_filter.mp hi).2]
    _ = _ := by
      rw [← mul_sum, fiber_eq, weight]
      by_cases hj : 2*j.val+1 = L
      · rw [ite_eq_left hj, ← (lower_eq_mirror_iff j).mpr hj]
        simp [lowerIndex]
      · have hne : lowerIndex j ≠ mirror (lowerIndex j) :=
          fun h => hj ((lower_eq_mirror_iff j).mp h)
        rw [ite_eq_right hj, sum_insert (by simpa only [mem_singleton] using hne), sum_singleton]
        rfl

end GoldbachPalindromeFold

theorem Conjectures.Cuts.Task507099fd4dd83106740a48d6 :
    ∀ (d : ℕ), 2 ≤ d → ∀ A ⊆ Finset.range d, ∀ (L : ℕ) (E : Finset ℕ),
      let palindromes := (Finset.range (d ^ L)).filter (fun n => ∀ i < L,
        n / d ^ i % d ∈ A ∧ n / d ^ i % d = n / d ^ (L - 1 - i) % d)
      let K := (L + 1) / 2
      let weight (j : Fin K) :=
        if 2 * j.val + 1 = L then d ^ j.val else d ^ j.val + d ^ (L - 1 - j.val)
      let tuples := Fintype.piFinset (fun _ : Fin K => A)
      let pack (u : Fin K → ℕ) := ∑ j, u j * weight j
      (palindromes.filter (· ∈ E)).card = (tuples.filter (fun u => pack u ∈ E)).card ∧
        palindromes.card = A.card ^ K := by
  classical
  intro d hd A hA L E
  dsimp only
  let P := (Finset.range (d ^ L)).filter (fun n => ∀ i < L,
    n / d ^ i % d ∈ A ∧ n / d ^ i % d = n / d ^ (L - 1 - i) % d)
  let B := Fintype.piFinset (fun _ : Fin (GoldbachPalindromeFold.half L) => A)
  let pack (u : Fin (GoldbachPalindromeFold.half L) → ℕ) :=
    ∑ j, u j * GoldbachPalindromeFold.weight d L j
  let unpack (n : ℕ) (j : Fin (GoldbachPalindromeFold.half L)) := n / d ^ j.val % d
  change ((P.filter (· ∈ E)).card = (B.filter (fun u => pack u ∈ E)).card) ∧
    P.card = A.card ^ GoldbachPalindromeFold.half L

  have packed (u : Fin (GoldbachPalindromeFold.half L) → ℕ) :
      GoldbachPalindromeDigits.encode d L (fun i => u (GoldbachPalindromeFold.fold i)) = pack u :=
    GoldbachPalindromeFold.sum_fold d L u
  have digits_small (u : Fin (GoldbachPalindromeFold.half L) → ℕ) (hu : u ∈ B) :
      ∀ i : Fin L, u (GoldbachPalindromeFold.fold i) < d :=
    fun i => Finset.mem_range.mp (hA (Fintype.mem_piFinset.mp hu (GoldbachPalindromeFold.fold i)))
  have get_packed (u : Fin (GoldbachPalindromeFold.half L) → ℕ) (hu : u ∈ B) (i : Fin L) :
      pack u / d ^ i.val % d = u (GoldbachPalindromeFold.fold i) := by
    rw [← packed u]
    exact GoldbachPalindromeDigits.digit_encode d L _ hd (digits_small u hu) i
  have pack_mem (u : Fin (GoldbachPalindromeFold.half L) → ℕ) (hu : u ∈ B) : pack u ∈ P := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · rw [← packed u]
      exact GoldbachPalindromeDigits.encode_lt d L _ hd (digits_small u hu)
    · intro i hi
      let p : Fin L := ⟨i, hi⟩
      have hLow := get_packed u hu p
      have hHigh := get_packed u hu (GoldbachPalindromeFold.mirror p)
      constructor
      · rw [hLow]
        exact Fintype.mem_piFinset.mp hu (GoldbachPalindromeFold.fold p)
      · exact hLow.trans
          ((congrArg u (GoldbachPalindromeFold.fold_mirror p)).symm.trans hHigh.symm)
  have unpack_mem (n : ℕ) (hn : n ∈ P) : unpack n ∈ B := by
    apply Fintype.mem_piFinset.mpr
    intro j
    exact ((Finset.mem_filter.mp hn).2 j.val (GoldbachPalindromeFold.half_index_lt j)).1
  have unpack_pack (u : Fin (GoldbachPalindromeFold.half L) → ℕ) (hu : u ∈ B) :
      unpack (pack u) = u := by
    funext j
    have h := get_packed u hu (GoldbachPalindromeFold.lowerIndex j)
    rw [GoldbachPalindromeFold.fold_lowerIndex] at h
    simpa only [unpack, GoldbachPalindromeFold.lowerIndex] using h
  have pack_unpack (n : ℕ) (hn : n ∈ P) : pack (unpack n) = n := by
    have hnData := Finset.mem_filter.mp hn
    have hVec :
        (fun i : Fin L => unpack n (GoldbachPalindromeFold.fold i)) =
          fun i : Fin L => n / d ^ i.val % d := by
      funext i
      change n / d ^ min i.val (L - 1 - i.val) % d = n / d ^ i.val % d
      by_cases hlow : i.val ≤ L - 1 - i.val
      · rw [min_eq_left hlow]
      · rw [min_eq_right (by omega : L - 1 - i.val ≤ i.val)]
        exact (hnData.2 i.val i.isLt).2.symm
    rw [← packed (unpack n), hVec]
    exact GoldbachPalindromeDigits.encode_digits d L n hd (Finset.mem_range.mp hnData.1)

  have hAll : B.card = P.card :=
    Finset.card_nbij' pack unpack pack_mem unpack_mem unpack_pack pack_unpack
  have hHits : (B.filter (fun u => pack u ∈ E)).card = (P.filter (· ∈ E)).card := by
    refine Finset.card_nbij' pack unpack ?_ ?_ ?_ ?_
    · intro u hu
      obtain ⟨huB, huE⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨pack_mem u huB, huE⟩
    · intro n hn
      obtain ⟨hnP, hnE⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨unpack_mem n hnP, ?_⟩
      rwa [pack_unpack n hnP]
    · intro u hu
      exact unpack_pack u (Finset.mem_filter.mp hu).1
    · intro n hn
      exact pack_unpack n (Finset.mem_filter.mp hn).1
  exact ⟨hHits.symm, hAll.symm.trans (Fintype.card_piFinset_const A _)⟩
